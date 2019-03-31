rem Copy runtime DLLs 

FOR /F %%I IN ('stack exec -- where libstdc++-6.dll') DO copy /Y "%%I" .\
FOR /F %%I IN ('stack exec -- where libgcc_s_seh-1.dll') DO copy /Y "%%I" .\
FOR /F %%I IN ('stack exec -- where libwinpthread-1.dll') DO copy /Y "%%I" .\
