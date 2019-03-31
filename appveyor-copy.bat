rem Copy runtime DLLs 

echo "" | stack exec -- where libstdc++-6.dll > lib.txt
echo "" | stack exec -- where libgcc_s_seh-1.dll >> lib.txt
echo "" | stack exec -- where libwinpthread-1.dll >> lib.txt
for /F %i IN (lib.txt) do copy /Y "%i" .\
del /q lib.txt