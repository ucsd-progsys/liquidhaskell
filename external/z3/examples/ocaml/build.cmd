@echo off

if not exist ..\..\ocaml\z3.cmxa (
        echo "YOU MUST BUILD OCAML API! Go to directory ..\ocaml"
        goto :EOF
)

set XCFLAGS=/nologo /MT /DWIN32

ocamlopt -ccopt "%XCFLAGS%" -o test_mlapi.exe -I ..\..\ocaml ole32.lib %OCAMLLIB%\libcamlidl.lib z3.cmxa test_mlapi.ml
