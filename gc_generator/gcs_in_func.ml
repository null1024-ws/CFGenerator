open Cil_types
open Cil_datatype


module GCC =
  Plugin.Register
  (struct
    let name = "Guarding Conditions Collector"
    let shortname = "GCC"
    let help = "This OCaml plugin can help you obtain guarding conditions in C/C++ programs."
  end)
  
module  FileGCC =
  GCC.Empty_string
    (struct
       let option_name = "-file"
       let help = "specify the target file"
       (* let kind= `Tuning *)
       let arg_name = "file-name"
       (* let default = "target_file" *)
       (* let default ="fcg.dot" *)
     end)
     
module FunctionGCC =
     GCC.Empty_string
     (struct
      let option_name = "-function"
      let help = "specify the target function"
      let arg_name = "function-name"
      (* let default = "target_function" *)
     end)
     
(* module TargetlineGCC =
     GCC.Int
     (struct
      let option_name = "-line"
      let help = "specify the target line"
      let arg_name = "target-line"
      let default = 1
    end) *)
    
module StartlineGCC =
     GCC.Int
     (struct
      let option_name = "-start"
      let help = "specify the start location for analysis"
      let arg_name = "start-line"
      let default = 10
    end)
    
module EndlineGCC =
    GCC.Int
    (struct
     let option_name = "-end"
     let help = "specify the end location for analysis"
     let arg_name = "end-line"
     let default = 11
   end)
   
(* let target_file = FileGCC.get()
let target_function = FunctionGCC.get()
let start_line = StartlineGCC.get()
let end_line = EndlineGCC.get() *)
(* let target_line = TargetlineGCC.get() *)
(* Updated the comparison logic to match locations accurately by normalizing or focusing on line numbers *)

let match_stmt target_location stmt =
  let stmt_location = Format.asprintf "%a" Printer.pp_location (Cil_datatype.Stmt.loc stmt) in
  (* Skip non-executable statements like function declarations or empty lines *)
  match stmt.skind with
  | Instr _ | Return _ | If _ | Loop _ | Switch _ | Block _ ->
      String.equal target_location stmt_location
  | _ ->
      false
(*
  1. Normalized the location comparison to ensure the target location and the statement's location match correctly.
  2. Adjusted the logic in the `find_stmt` function to accurately identify and compare statement locations.
  3. Verified that the `run` function properly utilizes `find_stmt` to locate and print the statements within the specified line range.
*)

let find_stmt f target_location =
  let found = ref false in
  let stmt = List.find_opt (fun stmt ->
    let stmt_location = Filename.basename (Format.asprintf "%a" Printer.pp_location (Cil_datatype.Stmt.loc stmt)) in
    (*Printf.printf "Comparing target location: %s with statement location: %s\n" target_location stmt_location;*)
    match stmt.skind with
    | Instr _ | Return _ | If _ | Loop _ | Switch _ | Block _ ->
        if String.equal target_location stmt_location then (
          found := true;
          true
        ) else
          false
    | _ ->
        Printf.printf "Non-executable statements at %s\n" stmt_location;
        false
  ) f.sbody.bstmts in
  if not !found then
    Printf.printf "No matching executable statement found at %s\n" target_location;
  stmt
    let print_valid_statement f =
      List.iter (fun stmt ->
        match stmt.skind with
        | Instr _ | Return _ | If _  | Switch _ | Block _ ->  (* Only print executable statements *)
            let stmt_desc = Pretty_utils.to_string Printer.pp_stmt stmt in
            Printf.printf "%s\n" stmt_desc
        | _ -> ()  (* Skip non-executable statements *)
      ) f.sbody.bstmts
      
      
      
(* debug function: print all the statements *)
let print_all_statements f =
    List.iter (fun stmt ->
      let stmt_loc = Format.asprintf "%a" Printer.pp_location (Cil_datatype.Stmt.loc stmt) in
      let stmt_desc = Pretty_utils.to_string Printer.pp_stmt stmt in
      Printf.printf "Found statement at %s: %s\n" stmt_loc stmt_desc
    ) f.sbody.bstmts
(*Print valid statements *)



let print_valid_statment f =
  List.iter (fun stmt ->
    let stmt_loc = Format.asprintf "%a" Printer.pp_location (Cil_datatype.Stmt.loc stmt) in
    let stmt_desc = Pretty_utils.to_string Printer.pp_stmt stmt in
    Printf.printf " ------%s--------\n%s\n" stmt_loc stmt_desc
  ) f.sbody.bstmts
  
  
  
let find_stmt_by_number kf =
  match kf.fundec with
  | Definition(f, _) ->
    let stmts = f.sbody.bstmts in
    List.iter (fun stmt ->
      if match_stmt "test.c:4" stmt then
        (Printf.printf "Find the target\n"; Cil_datatype.Stmt.pretty Format.std_formatter stmt)
      else
        Printf.printf "Not found\n"
    ) stmts
  | Declaration _ ->
    Format.printf "No definition found for this function.\n"
    


    
(* let find_start_stmt f = find_stmt f "challenge_RG.c:106"
let find_end_stmt f = find_stmt f "challenge_RG.c:113" *)
(* let find_start_stmt f = find_stmt f (Format.sprintf "%s:%d" target_file start_line)
let find_end_stmt f = find_stmt f (Format.sprintf "%s:%d" target_file end_line) *)

let print_gc_in_path paths_list =
  List.iter (fun path ->
    Printf.printf "Path: ";
    List.iter (fun stmt ->
      match stmt.skind with
      | If _ -> Printf.printf "Statement: %s\n" (Pretty_utils.to_string Printer.pp_stmt stmt)
      | _ -> ()
    ) path;
    Printf.printf "End\n"
  ) paths_list
  
module GCSet = Set.Make(struct
  type t = Stmt.t
  let compare = Stmt.compare
end)

let rec find_paths_on_nodes visited start_node end_node =
  if List.mem start_node visited then []
  else if start_node == end_node then [[start_node]]
  else
    let succs = start_node.succs in
    let new_paths = List.concat_map (fun succ ->
      find_paths_on_nodes (start_node :: visited) succ end_node
    ) succs in
    List.map (fun path -> start_node :: path) new_paths
    |> List.sort_uniq Stdlib.compare
    
    
(* Assume other necessary modules and functions are already defined *)
(* Function to process paths and collect unique guarding conditions *)
let process_all_gc_in_path paths_list =
  List.fold_left (fun acc path ->
    List.fold_left (fun acc stmt ->
      match stmt.skind with
      | If _ -> GCSet.add stmt acc
      | _ -> acc
    ) acc path
  ) GCSet.empty paths_list
(* Run function to find and process guarding conditions *)

let run () =
  let target_file = FileGCC.get() in
  let target_function = FunctionGCC.get() in
  let start_line = StartlineGCC.get() in
  let end_line = EndlineGCC.get() in
  let kf = Globals.Functions.find_def_by_name target_function in
  match kf.fundec with
  | Definition(f, _) -> begin
      let pdg = Pdg.Api.get kf in
      let rec find_next_start_stmt line =
        match find_stmt f (Format.sprintf "%s:%d" target_file line) with
        | Some stmt -> Some stmt
        | None -> if line < end_line then find_next_start_stmt (line + 1) else None
      in
      let rec find_next_end_stmt line =
        match find_stmt f (Format.sprintf "%s:%d" target_file line) with
        | Some stmt ->
          (match stmt.skind with
           | Block _ -> if line > start_line then find_next_end_stmt (line - 1) else None
           | _ -> Some stmt)
        | None -> if line > start_line then find_next_end_stmt (line - 1) else None
      in
      let start_stmt = find_next_start_stmt start_line in
      let end_stmt = find_next_end_stmt end_line in
      let is_valid_stmt stmt =
        match stmt.skind with
        | Instr (Call _) -> false  (* Skip call functions *)
        | Block _ -> false         (* Skip blocks *)
        | _ -> true
      in
      match (start_stmt, end_stmt) with
      | (Some stmt1, Some stmt2) -> begin
          if is_valid_stmt stmt1 && is_valid_stmt stmt2 then
            let start_node = Pdg_types.PdgTypes.Node.stmt (Pdg.Api.find_stmt_node pdg stmt1)
            and end_node = Pdg_types.PdgTypes.Node.stmt (Pdg.Api.find_stmt_node pdg stmt2) in
            match (start_node, end_node) with
            | (Some start_node_stmt, Some end_node_stmt) ->
              let paths = find_paths_on_nodes [] start_node_stmt end_node_stmt in
              let guarding_conditions = process_all_gc_in_path paths in
              (* Print the guarding conditions *)
              GCSet.iter (fun stmt ->
                Format.printf "******%a******%a\n" Printer.pp_location (Cil_datatype.Stmt.loc stmt) Printer.pp_stmt stmt
              ) guarding_conditions
            | _ -> Printf.printf "Failed to get stmt from node\n"
          else
            (* Handle cases where start or end statements are not valid *)
            print_valid_statment f
        end
      | _ -> Printf.printf "Failed to get statement\n"
    end
  | Declaration _ -> Printf.printf "Function not found\n"
  
  
(* Extend the run function as needed *)
let () = Boot.Main.extend run
(*handle multiple targets gcs --> overlap? indepent?*)
(*for each target path? conditions? --> ds to store?   mapping?*)
