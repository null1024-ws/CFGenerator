Obtain GC in Single Function
===

# Usage
```shell
cd gc-in-func
dune build
# build complete, now test this plugin
cd test_code
# remember this plugin can only process the file containing the function embedded in the gcs_in_func.ml. Of course, you can make the function as a parameter of cmdline.
dune exec -- frama-c ./kstring.c
```