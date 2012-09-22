#!/bin/bash

gcc -I../include -I`ocamlc -where` -c z3_stubs.c -c z3_theory_stubs.c
ocamlopt -c z3.mli
ocamlopt -c z3.ml
ar rcs libz3stubs.a z3_stubs.o z3_theory_stubs.o
ranlib libz3stubs.a
ocamlopt -a -o z3.cmxa -cclib -lz3stubs z3.cmx
