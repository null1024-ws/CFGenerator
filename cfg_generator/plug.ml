(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2020 stephane.duprat81@gmail.com                        *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)


(* Open two modules so we can use types and functions *)
open Cil_types
open Cabs

(* Define a new module named Pcg *)
module Pcg = 
  Plugin.Register      (* registers a plugin named "pcg" *)
    (struct
       let name = "Project Graph Explorer"
       let shortname = "pcg"
       let help = "generated call graph functions and call graph module"
     end)

(** Register the new Frama-C option "-pcg-f". *)
module FunctionCg =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-f"
       let help = "generate function call graph" 
       let kind = `Tuning  (* Corrected spacing around `Tuning *)
       let arg_name = "fcg-name"
       let default = "fcg.dot"
     end)

module ModuleCg =
  Pcg.Empty_string  (* Takes another module as an argument and returns a new module *)
    (struct
       let option_name = "-pcg-m"
       let help = "generate module call graph" 
       let kind = `Tuning
       let arg_name = "mcg-name"
       let default = "mcg.dot"
     end)

module CgHead =
  Pcg.False
    (struct
       let option_name = "-pcg-head"
       let help = "include headers"
       let kind = `Correctness
     end)


module CgAll =
  Pcg.False
    (struct
       let option_name = "-pcg-all"
       let help = "one cg for each module"
       let kind = `Correctness
     end)

module CgComments_filename =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-funcinfo"
       let help = "count comments per functions"
       let kind= `Tuning
       let arg_name = "comments_file"
       let default ="comments_count.txt"
     end)

module CommentOut =
  Pcg.False
    (struct
       let option_name = "-pcg-comment"
       let help = "comment metrics"
       let kind = `Correctness
     end)

module CgStack_filename =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-stack"
       let help = "stack computation" 
       let kind= `Tuning 
       let arg_name = "stack_file"
       let default ="stack.txt"
     end)

module CgStack_calls_filename =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-stack-calls"
       let help = "add additional calls (resulting from callback through function pointers" 
       let kind= `Tuning 
       let arg_name = "stack_calls_file"
       let default ="stack_calls.txt"
     end)

module CgStack_caller =
  Pcg.True
    (struct
       let option_name = "-pcg-stack-caller"
       let help = "compute only for uncalled function"
       let kind = `Correctness
     end)


let logdeb3 msg =
  Pcg.debug ~level:3 msg

type function_node = {
  fname: string;
  fid : int;
(*  is_def:bool;*)
  fmod:string;
}

type module_node = {
  mname: string;
  mid: int;
  is_header:bool;
}

module StringMap  = Map.Make(String)
module StringSet  = Set.Make(String)
module PairOrd    = struct type t = int * int let compare = compare end
module PairString = struct type t = string * string let compare = compare end
module PairStringSet = Set.Make(PairString)
module PairStringMap = Map.Make(PairString)

type prj_desc = (function_node StringMap.t * module_node StringMap.t * PairStringSet.t * PairStringSet.t)

(* 
 * Function: max_list 
 * Use: Recursively finds the maximum element in a list of integers. 
 * Returns 0 if the list is empty.
 *)
let rec max_list l =
  match l with
    [] -> 0
   |t::q -> max t (max_list q) ;;

let cPT=ref 0

let new_id () =
  cPT := !cPT+1;
  !cPT
(* 
 * Function: is_header 
 * Use: Checks if a given string `n` represents a header file by verifying if 
 * it ends with ".h". Returns true if it is a header file, otherwise false.
 *)
  let is_header n =
    let res = 
      try
        (String.sub n ((String.length n)-2) 2)=".h"
      with Invalid_argument(_) ->
        false
    in
    Pcg.debug ~level:3 "is_header: %s -> %b\n" n res;
    res
  
(* 
 * Function: string_map_filter 
 * Use: Filters a map `m` based on a predicate function `f`. The function `f` 
 * is applied to each key-value pair in the map, and only pairs that satisfy 
 * the predicate are included in the returned map.
 *)
let string_map_filter f m =
  StringMap.fold (fun k e cur_map -> if (f k e) then (StringMap.add k e cur_map) else cur_map) m StringMap.empty
(* 
 * Function: string_map_exists 
 * Use: Checks if a given key `e` exists in the map `m`. Returns true if the 
 * key exists, otherwise false.
 *)
let string_map_exists e m =
  try
    ignore (StringMap.find e m);
    true
  with
      Not_found -> false
(* 
 * Class: c_get_called 
 * Use: Inherits from `Visitor.frama_c_inplace` and is used to track function 
 * calls in a list `called_list`. It adds functions to this list when they are 
 * encountered during the visit.
 *)
class c_get_called =
object (self)
  inherit Visitor.frama_c_inplace as super

  val mutable called_list = []

  method get_called_list() = called_list;
  method add_func_called f =
    called_list<-if (List.exists ((=) f) called_list) then called_list else f::called_list;

  method vinst (i:instr) =
    match i with
        Call(_,{enode=Lval(Var({vorig_name=n}),_)},_,_)      ->
          self#add_func_called n;
          Cil.DoChildren
      | _   -> Cil.DoChildren

end

(*
 * counting comments
 *)

let m_function_comment_nb = ref PairStringMap.empty

let lines_of_string_list sl =
  let ffold (n:int) (s:string)  =
    n + (List.length (String.split_on_char '\n' s))
  in
  List.fold_left ffold 0 sl

let r_lines = ref []
(* 
 * Function: compute_comment_function 
 * Use: Computes the number of lines of comments associated with a function 
 * `fname` within a specified range of lines (`lstart` to `lend`) in the file 
 * located at `filepath`.
 *)
let compute_comment_function (fname:string) (filepath:Filepath.position) lstart lend=
  let ffold ((pos1,pos2):cabsloc) str prev_n =
    if (((Filepath.Normalized.to_pretty_string filepath.pos_path)
         = (Filepath.Normalized.to_pretty_string pos1.pos_path))
        && pos1.pos_lnum>=lstart && pos1.pos_lnum<=lend)
    then
      prev_n + (lines_of_string_list [str])
    else
      prev_n
  in
  Cabshelper.Comments.fold ffold 0

(* 
 * Function: init_empty_list 
 * Use: Recursively creates a list of empty strings with `n` elements.
 * Returns an empty list if `n` is 0.
 *)
let rec init_empty_list n =
  if n=0
  then
    []
  else
    "" :: (init_empty_list (n-1))
(* Function: compute_empty_lines_per_function
 * Use: Reads a file line by line, processing markers and lines to initialize 
 * and update the `r_lines` reference, which stores the lines of the file.
 *)
let compute_empty_lines_per_function (filename:string) =
  r_lines := [""];
  let in_channel = open_in filename in
  try
    let r_last_marker = ref 0 in
    while true do
      let line = input_line in_channel in
      let r = Str.regexp "^# \\([0-9]+\\)" in
      if Str.string_match r line 0
      then
        begin
          r_last_marker :=  (int_of_string (Str.matched_group 1 line));
          r_lines := init_empty_list !r_last_marker;
        end
      else
        (
          r_lines := List.append !r_lines [line]
        )
    done;
  with End_of_file ->
    close_in in_channel

(* Declare a mutable variable to hold function start and end lines *)
let m_function_start_end_lines = ref PairStringMap.empty

(* This class is modified according to your instruction removed comments empty and other things to find the start and end line of function code and run function also modiefed i mentioned *)


class c_globals_function =
object (self)
  inherit Visitor.frama_c_inplace as super
(* Method: vglob
   * Use: Visits global elements, particularly functions in C files, computes
   * the number of empty lines, comment lines, and code lines, and updates 
   * the metrics map.
   *)
   method vglob (g:global) =
    begin
      match g with
        GFun(({svar=vi}),(l1,l2)) ->
        begin
          let filename = Filename.basename (Format.asprintf "%a" Filepath.Normalized.pp_abs l1.pos_path) in
          if (Str.string_match (Str.regexp ".*\\.c$") filename 0)
          then
            (* only for function in .c file *)
            begin
              compute_empty_lines_per_function (Filepath.Normalized.to_pretty_string l1.pos_path) ;
  
              Pcg.debug ~level:3 "Gfun %s ===========>\n" vi.vorig_name;
              List.iter (fun s -> Pcg.debug ~level:4  "%d %s \n" (List.length (String.split_on_char '\n' s)) s) (Globals.get_comments_global g);
  
              let nb_comment_header =
                let function_comments_list = Globals.get_comments_global g
                and max_of_list l = List.fold_left max 0 l
                in
                if (List.length function_comments_list) > 0
                then
                  max_of_list (List.filter (fun n -> Pcg.debug ~level:3 "n %d " n; if n>0 then true else false) (List.map (fun s -> List.length (String.split_on_char '\n' s)) (Globals.get_comments_global g)))
                else
                  0
  
              and nb_lines_function =
                let subarray =
                  try
                    Array.sub (Array.of_list !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1)
                  with Invalid_argument(_) ->
                    Printf.printf "ERROR : %d, %d, %d\n" (List.length !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1);
                    Array.sub (Array.of_list !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1)
                and ffold n s =
                  let res =
                    if (Str.string_match (Str.regexp ".*[a-zA-Z0-9 ;{}]+") s 0) then n+1 else n
                  in
                  Pcg.debug ~level:3 "MATCH %s %d" s res;
                  res;
  
                in
                Array.fold_left ffold 0 subarray
  
              and nb_comments_function =
                compute_comment_function vi.vorig_name l1 l1.pos_lnum l2.pos_lnum
              in
              let nb_total_function = nb_comment_header + nb_lines_function
              and nb_total_comments_function = nb_comment_header + nb_comments_function
              in
              Pcg.debug ~level:3 "%s %d %d total %d (%dc, %d+%d) - %d\n"
                vi.vorig_name l1.pos_lnum l2.pos_lnum nb_total_function nb_total_comments_function nb_comment_header nb_comments_function (nb_total_comments_function*100/nb_total_function);
  
              let module_name = (Filename.basename filename) in
              let m_f = (module_name,vi.vorig_name) in
              m_function_comment_nb := PairStringMap.add m_f (nb_total_function,nb_total_comments_function) !m_function_comment_nb ;
              
              (* Add start and end lines to metrics *)
              m_function_start_end_lines := PairStringMap.add m_f (l1.pos_lnum, l2.pos_lnum) !m_function_start_end_lines;
  
              Cil.DoChildren
            end
          else
            Cil.SkipChildren
        end
  
      | _ -> Cil.SkipChildren
    end ;
  

end

(* 
 * Function: get_called_functions
 * Use: Takes a kernel function `kf` and returns a list of functions called 
 * within it by using the `c_get_called` visitor class.
 *)
let get_called_functions kf =
  match kf.fundec with
      Definition(f,_)   ->
        let v=new c_get_called
        in
          ignore (Visitor.visitFramacFunction (v :>Visitor.frama_c_visitor) f);
          v#get_called_list();
    | _       -> []

(* 
 * Function: add_edge_to_prj
 * Use: Adds an edge between functions and modules in the project descriptor `prj`, 
 * linking function `a` to function `b` and their respective modules.
 *)
let add_edge_to_prj a ((mf,mm,gf,gm):prj_desc) b =
  let new_gf = 
    logdeb3 "add func %s -> %s" a b;
    PairStringSet.add (a,b)  gf
  and new_gm =
    let ma = (StringMap.find a mf).fmod
    and mb = (StringMap.find b mf).fmod
    in
      logdeb3 "add mod %s -> %s" ma mb;
      PairStringSet.add (ma,mb)  gm
  in
    (mf,mm,new_gf,new_gm)
(* 
 * Function: filter_header
 * Use: Filters out header files from the project descriptor `prj`, removing 
 * them from the function and module maps, as well as the edges between them.
 *)

    let filter_header ((mf, mm, gf, gm): prj_desc) =
      let new_mm = string_map_filter (fun _ e -> not e.is_header) mm in
      let new_mf = string_map_filter (fun _ e -> string_map_exists e.fmod new_mm) mf in
      let new_gm = PairStringSet.filter (fun (a,b) -> (string_map_exists a new_mm) && (string_map_exists b new_mm)) gm in
      let new_gf = PairStringSet.filter (fun (a,b) -> (string_map_exists a new_mf) && (string_map_exists b new_mf)) gf in
      (new_mf, new_mm, new_gf, new_gm)
(* 
 * Function: add_func_to_prj
 * Use: Adds a function `fname` to the project descriptor `prj` if it doesn't 
 * already exist, and updates the module descriptor as needed.
 *)
      let add_func_to_prj ((mf,mm,gf,gm):prj_desc) fname =
        Pcg.debug ~level:3 "Adding function to project: %s\n" fname;
        let new_mf, new_mm =
          if not (string_map_exists fname mf) then
            let owner =
              try
                let {Filepath.pos_path=n}, _ = 
                  (let kf = Globals.Functions.find_by_name fname in
                   Kernel_function.get_location kf)
                in Filepath.Normalized.to_pretty_string n
              with Not_found ->
                "UnknownModule"
            in
            let fdesc = {
              fname = fname;
              fid = new_id();
              fmod = owner;
            } in
            let new_mf = StringMap.add fname fdesc mf in
            let new_mm =
              if not (string_map_exists owner mm) then
                let mod_desc = {
                  mname = owner;
                  mid = new_id();
                  is_header = (owner = "UnknownModule") || is_header owner; 
                } in
                StringMap.add owner mod_desc mm
              else mm
            in
            (new_mf, new_mm)
          else
            (mf, mm)
        in
        (new_mf, new_mm, gf, gm)
      
     
(* 
 * Function: compute_prj
 * Use: Computes the project descriptor by iterating over all functions in the 
 * program, adding functions and edges between them based on their relationships.
 *)   
      
      let compute_prj () =
        let ffold kf ((mf,mm,gf,gm) as prj:prj_desc) =
          let name = Kernel_function.get_name kf in
          let called_functions = get_called_functions kf in
          let new_prj = add_func_to_prj prj name in
          let new_prj = List.fold_left add_func_to_prj new_prj called_functions in
          List.fold_left (add_edge_to_prj name) new_prj called_functions
        in
        let init_prj = (StringMap.empty, StringMap.empty, PairStringSet.empty, PairStringSet.empty) in
        Globals.Functions.fold ffold init_prj
    
(* 
 * Function: print_graph_func
 * Use: Generates and prints a function-level graph in DOT format, showing the relationships 
 * between functions and their clusters within the project descriptor `prj`.
 *)

    let print_graph_func fd ((mf,mm,gf,gm):prj_desc) =
      let print_called () =
        let fiter (a,b) =
          if string_map_exists a mf && string_map_exists b mf then
            Printf.fprintf fd "\t%s->%s\n" a b
        in
          PairStringSet.iter fiter gf
    
      and print_cluster_part () =
        let print_cluster n mdesc =
          let filtered_mf = string_map_filter (fun k {fmod=p} -> p = n) mf in
            Printf.fprintf fd "subgraph cluster_%d {\n" mdesc.mid;
            StringMap.iter (fun n d -> Printf.fprintf fd "\t%s;\n" n) filtered_mf;
            Printf.fprintf fd "\tlabel = \"%s\";\n\t}\n" (Filename.chop_extension (Filename.basename n))
        in
          StringMap.iter print_cluster mm
      in
        Printf.fprintf fd "digraph G {\n";
        print_called ();
        print_cluster_part ();
        Printf.fprintf fd "}\n"
        
(* 
 * Function: center_prj_to_mod
 * Use: Centers the project descriptor `prj` around a specific module `m`, 
 * filtering out unrelated functions and modules.
 *)
let center_prj_to_mod  m ((mf,mm,gf,gm):prj_desc)=

  let new_gf = 
    let ffilter (a,b) =
      let ma = (StringMap.find a mf).fmod
      and mb = (StringMap.find b mf).fmod
      in 
        (0 = (compare m ma)) || (0 = (compare m mb))
    in
      PairStringSet.filter ffilter gf
  in
  let new_mm = 
    let ffilter m _ =
      let ffind (a,b) =
        let ma = (StringMap.find a mf).fmod
        and mb = (StringMap.find b mf).fmod
        in 
        (0 = (compare m ma)) || (0 = (compare m mb))
      in
      PairStringSet.exists ffind new_gf
    in
    StringMap.filter ffilter mm
  in 
  let new_mf =
    (* only function that are orig or dest of graph *)
    let ffilter n f =
      PairStringSet.exists (fun (a,b) -> (0 = compare a n) || (0 = compare b n) ) new_gf
    in
    StringMap.filter ffilter mf


  in (new_mf,new_mm,new_gf,gm)

(* 
 * Function: print_graph_mod
 * Use: Generates and prints a module-level graph in DOT format, showing the relationships 
 * between modules within the project descriptor `prj`.
 *)
let print_graph_func_mod  m ((mf,mm,gf,gm):prj_desc)=
  logdeb3 "print_graph_func_mod %s" m;
  let print_called fd=
    let fiter (a,b)=
      Printf.fprintf fd "\t%s->%s\n" a b
    and ffilter (a,b) =
      let ma = (StringMap.find a mf).fmod
      and mb = (StringMap.find b mf).fmod
      in 
        (0 = (compare m ma)) || (0 = (compare m mb))
    in
      PairStringSet.iter fiter (PairStringSet.filter ffilter gf)
      
  and print_cluster_part fd =
    let print_cluster  n mdesc=
      let filtered_mf= string_map_filter (fun k {fmod=p}->p=n) mf
      in
        Printf.fprintf fd "subgraph cluster_%d {\n" mdesc.mid;
        StringMap.iter (fun n d ->Printf.fprintf fd "\t%s;\n" n) filtered_mf;
        Printf.fprintf fd "\tlabel = \"%s\";\n\t}\n" (Filename.chop_extension (Filename.basename n))
    in
(*      StringMap.iter print_cluster mm*)
        print_cluster m (StringMap.find m mm);
  in
    let fd = open_out ((Filename.chop_extension (Filename.basename m)) ^".dot");
    in
    Printf.fprintf fd "digraph G {\n";
    (* Printf.fprintf fd "//size=\"60,40\"; ratio = fill;\n"; *)
    print_called fd;
    print_cluster_part fd;
    Printf.fprintf fd "}\n";
    close_out fd
  
(* 
 * Function: print_graph_mod2
 * Use: Generates and prints a simplified module-level graph in DOT format, focusing on 
 * module names without additional formatting details.
 *)
let print_graph_mod fd ((mf,mm,gf,gm):prj_desc)=

  let print_called()=
    let fiter (a,b)=
      let desc_a=StringMap.find a mm
      and desc_b=StringMap.find b mm
      in
        Printf.fprintf fd "%d->%d\n" desc_a.mid desc_b.mid
    in
      PairStringSet.iter fiter gm

  and print_mod ()=
    let print_one_mod k mod_elt =
      Printf.fprintf fd "\t\"%d\" [shape=diamond, label=\"%s\", style=bold];\n"  mod_elt.mid (Filename.chop_extension (Filename.basename k))
    in
      StringMap.iter print_one_mod mm

  in
    Printf.fprintf fd "digraph G {\n";
    print_mod ();
    print_called();
    Printf.fprintf fd "}\n"
(* 
 * Function: print_graph_mod2
 * Use: Generates and prints a simplified module-level graph in DOT format, focusing on 
 * module names without additional formatting details.
 *)

let print_graph_mod2 fd ((mf,mm,gf,gm) :prj_desc)=

  let print_called()=
    let fiter (a,b)=
      let desc_a=StringMap.find a mm
      and desc_b=StringMap.find b mm
      in
        Printf.fprintf fd "%s->%s\n" 
          (Filename.chop_extension (Filename.basename desc_a.mname))
          (Filename.chop_extension (Filename.basename desc_b.mname))
    in
      PairStringSet.iter fiter gm
  in
    Printf.fprintf fd "digraph G {\n";
    (* Printf.fprintf fd "size=\"6,4\"; ratio = fill;\n"; *)
    print_called();
    Printf.fprintf fd "}\n"

let computingmap = ref StringMap.empty 

(* 
 * Function: parse_stack_size_file
 * Use: Parses a file containing stack sizes for functions and updates the `computingmap` 
 * with the parsed data.
 *)
let parse_stack_size_file prj =
  let parse_line line_str map =
    let reg = Str.regexp "^\\([A-Za-z0-9_]+\\)[ \t]+\\([0-9]+\\)" in
    if (Str.string_match reg line_str 0)
    then
      begin
        let n1 = Str.matched_group 1 line_str
        and n2 = Str.matched_group 2 line_str in
        Pcg.debug ~level:2 "function %s : %s" n1 n2 ;
        StringMap.add n1 (int_of_string n2) map
      end
    else
      begin
        Pcg.warning  "nothing to parse at this line %s" line_str ;
        map
      end
  in
  try
    let filename = CgStack_filename.get () in
    try
      let ref_file = open_in filename
      in
      try
        Pcg.debug ~level:2 "Parsing stack conf file %s\n" filename ;
        while true do
          computingmap := parse_line (input_line ref_file) !computingmap;
        done;      
      with End_of_file -> close_in ref_file
    with 
      Sys_error(str)    -> 
      Pcg.warning "Error opening file %s (%s)\n" filename str 
  with 
    (* no stack file  *)
    Not_found           ->
     Pcg.debug ~level:2 "No stack file set"

let computingset = ref PairStringSet.empty 
(* 
 * Function: parse_stack_call_file
 * Use: Parses a file containing function call relationships and updates the `computingset` 
 * with the parsed data.
 *)
let parse_stack_call_file prj =
  let parse_line line_str set =
    let reg = Str.regexp "^\\([A-Za-z0-9_]+\\)[ \t]+\\([A-Za-z0-9_]+\\)" in
    if (Str.string_match reg line_str 0)
    then
      begin
        let f1 = Str.matched_group 1 line_str
        and f2 = Str.matched_group 2 line_str in
        Pcg.debug ~level:2 "add call %s -> %s" f1 f2 ;
        PairStringSet.add (f1,f2) set
      end
    else
      begin
        Pcg.warning  "nothing to parse at this line %s" line_str ;
        set
      end
  in
  try
    let filename = CgStack_calls_filename.get () in
    try
      let ref_file = open_in filename
      in
      try
        Pcg.debug ~level:2 "Parsing stack calls conf file %s\n" filename ;
        while true do
          computingset := parse_line (input_line ref_file) !computingset;
        done;      
      with End_of_file -> close_in ref_file
    with 
      Sys_error(str)    -> 
      Pcg.warning "Error opening file %s (%s)\n" filename str 
  with 
    (* no stack file  *)
    Not_found           ->
     Pcg.debug ~level:2 "No stack file set"
(* 
 * Function: compute_stack
 * Use: Computes the stack size required for each function in the project by analyzing 
 * function calls and stack sizes from configuration files.
 *)
let compute_stack ((mf,mm,gf,gm)) =
  parse_stack_size_file();
  parse_stack_call_file();
  let stack_size_of_fn (fn:string) =
    try
      StringMap.find fn !computingmap
    with
      Not_found ->
      Pcg.warning "Stack of %s unknown\n" fn;
      0
  in
  let rec max_stack_function str fn=
    let list_of_called_fn = 
      let subset = PairStringSet.filter (fun (x,_) -> 0 = String.compare x fn) (PairStringSet.union gf !computingset)
      in
      let ffold (a,b) p = 
        b :: p
      in
      PairStringSet.fold ffold subset []
    in
    let new_str = Printf.sprintf "%s -> %s (%d) " str fn (stack_size_of_fn fn) in
    Pcg.log "%s\n" new_str;
    (stack_size_of_fn fn) + (max_list (List.map (max_stack_function new_str) list_of_called_fn))
  in
  let fiter k f_elt =
    Pcg.debug "starting: %s\n" k ;
    Pcg.log "COMPUTED STACK FROM: %s : %d\n" k (max_stack_function "" k)
  in
  let func_to_analyse =
    if (CgStack_caller.get())
    then
      StringMap.filter (fun m _ -> not (PairStringSet.exists (fun (_,b) -> m=b) gf)) mf
    else
      mf;
  in
  StringMap.iter fiter func_to_analyse

(*
 * Depth computation
 *)

let m_function_depth = ref StringMap.empty

class c_compute_depth () = object (self)
  inherit Cabsvisit.nopCabsVisitor as super

  val mutable depth = 0
  val mutable max_depth = 0

  method vdef d =
   ( match d with
       |FUNDEF (_,(_,(name,_,_,_)),bl,_,_) ->
         depth     <- -1;
         max_depth <- 0;
         ignore (Cabsvisit.visitCabsBlock (self:>Cabsvisit.cabsVisitor) bl);
         m_function_depth := StringMap.add name max_depth !m_function_depth;
         Pcg.debug ~level:2 "depth %s = %d" name max_depth ;
         SkipChildren
       | _ -> DoChildren
   );

  method vstmt st =
    (
    match st.stmt_node with
      |SWITCH (_, {stmt_node = BLOCK _}, _) -> depth <- depth-1
      |_ -> ()
    );
    DoChildren


  method vblock bl =
    let {blabels = l1; battrs = l2; bstmts = l3} = bl in
    Pcg.debug ~level:3 "block in ->%d,%d" depth max_depth ;
    depth <- depth + 1;
    max_depth <- max max_depth depth ;
    List.iter (fun s -> ignore (Cabsvisit.visitCabsStatement (self:>Cabsvisit.cabsVisitor) s)) l3;
    Pcg.debug ~level:3 "block ou ->%d,%d : %d, %d, %d" depth max_depth (List.length l1) (List.length l2) (List.length l3);
    depth <- depth - 1;
    SkipChildren

(*  method vExitScope () =
    if (depth > 0 ) then
      depth <- depth -1;
    Pcg.debug ~level:3 "block %d,%d <-" depth max_depth ;
*)
end


let compute_depth () =
  let visit_depth ((*fname*)_,_ as file) =
    let visitor = new c_compute_depth () in
    ignore (Cabsvisit.visitCabsFile (visitor:>Cabsvisit.cabsVisitor) file)
  in
  let untyped_files = Ast.UntypedFiles.get () in
  List.iter visit_depth untyped_files

  let run () =

    let fcg_filename = FunctionCg.get()
    and mcg_filename = ModuleCg.get()
    and stack_filename = CgStack_filename.get()
    and comments_filename = CgComments_filename.get()
    in
  
      if (   ((String.length fcg_filename) >0)
          || ((String.length mcg_filename) >0)
          || ((String.length stack_filename) >0)
          || ((String.length comments_filename) >0)
          || (CgAll.get ())
          || (CommentOut.get ()))
      then
        begin
          let cil_type_file = Ast.get() in
          let prj =
            let prj = compute_prj ()
            in
              if (CgHead.get ())
              then
                prj
              else
                filter_header prj
          in
          if (CommentOut.get ())
          then
            (
              ignore (Visitor.visitFramacFile ((new c_globals_function):> Visitor.frama_c_visitor) (Ast.get ()));
              compute_depth ();
              let fiter (m,f) (l,c) =
                let s_depth =
                  try
                    string_of_int (StringMap.find f !m_function_depth)
                  with Not_found -> "unknown"
                in
                Printf.printf "%s;%s;%d;%d;%d;%s\n" m f l c (c*100/l) s_depth ;
              in
              PairStringMap.iter fiter !m_function_comment_nb;
              (* Print function start and end lines *)
              let fiter_start_end (m,f) (start_line, end_line) =
                Printf.printf "%s;%s; %d; %d\n" m f start_line end_line;
              in
              PairStringMap.iter fiter_start_end !m_function_start_end_lines;
            );
          if (CgAll.get ())
          then
            begin
              let (mf,mm,gf,gm) = prj;
              in
              logdeb3 "print all" ;
              (* StringMap.iter (fun m d -> print_graph_func_mod m prj) mm; *)
              let print_graph_func_mod2 m prj =
                let fd = open_out ((Filename.chop_extension (Filename.basename m)) ^".dot")
                in
                print_graph_func fd prj;
                close_out fd
              in
              StringMap.iter (fun m d -> print_graph_func_mod2 m (center_prj_to_mod m prj)) mm;
            end;
          if ((String.length fcg_filename)>0)
            then
              begin
                try
                  let o = open_out fcg_filename in
                    print_graph_func o prj;
                    close_out o
                with e ->
                  Pcg.error
                    "error during output of function callgraph: %s"
                    (Printexc.to_string e)
              end;
            if ((String.length mcg_filename)>0)
            then
              begin
                try
                  let o = open_out mcg_filename in
                    print_graph_mod2 o prj;
                    close_out o
                with e ->
                  Pcg.error
                    "error during output of module callgraph: %s >%s<"
                    (Printexc.to_string e) mcg_filename
              end;
  
            if ((String.length comments_filename)>0)
            then
              begin
                compute_depth ();
                try
                  let o = open_out comments_filename in
                    ignore (Visitor.visitFramacFile ((new c_globals_function):> Visitor.frama_c_visitor) (Ast.get ()));
                
                    (* Write function start and end lines *)
                    let fiter_start_end (m,f) (start_line, end_line) =
                      Printf.fprintf o "%s %s %d %d\n" m f start_line end_line;
                    in
                    PairStringMap.iter fiter_start_end !m_function_start_end_lines;
                    close_out o
                with e ->
                  Pcg.error
                    "error during output of comments count: %s >%s<"
                    (Printexc.to_string e) comments_filename
              end;
  
          if ((String.length stack_filename)>0)
          then
            compute_stack prj;
  
        end
  
  let () = Db.Main.extend run
  
