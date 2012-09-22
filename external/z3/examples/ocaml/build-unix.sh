#!/bin/bash

OCAMLLIB=$1
 
#ocamlopt -o test_mlapi.exe -ccopt "-I../../ocaml -L../../bin" -I ../../ocaml/ -I /usr/local/lib/ocaml -cclib -lcamlidl -cclib -lz3stubs -cclib -lz3 /usr/local/lib/ocaml/libcamlidl.a z3.cmxa test_mlapi.ml
#ocamlopt -o test_mlapi.exe -ccopt "-I../../ocaml -L../../bin" -I ../../ocaml/ -I /usr/local/lib/ocaml -cclib -lz3 -cclib -lz3stubs /usr/local/lib/ocaml/libcamlidl.a z3.cmxa test_mlapi.ml
#ocamlopt -o test_mlapi.exe -ccopt "-I../../ocaml -L../../bin" -I ../../ocaml/ -cclib -lz3 -cclib -lz3stubs ${OCAMLLIB}/libcamlidl.a z3.cmxa test_mlapi.ml
ocamlopt -dtypes -o test_mlapi -ccopt "-I../../ocaml -L../../bin -L../../lib" -I ../../ocaml/ -cclib -lz3 -cclib -lz3stubs ${OCAMLLIB}/libcamlidl.a z3.cmxa test_mlapi.ml
