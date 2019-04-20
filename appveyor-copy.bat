rem Copy runtime DLLs 

echo "" | stack exec -- where libstdc++-6.dll > lib.txt
echo "" | stack exec -- where libgcc_s_seh-1.dll >> lib.txt
echo "" | stack exec -- where libwinpthread-1.dll >> lib.txt

FOR /F %%I IN (lib.txt) DO copy /Y "%%I" .\

del /q lib.txt