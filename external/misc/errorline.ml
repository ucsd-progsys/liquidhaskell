type info =
    { mutable  linenum: int;   (* current line number *)
      mutable  linepos: int;   (* char position of beginning of current line *)	
      fileName        : string (* current file name *)
    }
      
let current : info ref = 
  ref 
    { linenum  = 1 ;
      linepos  = 0 ;
      fileName = ""
    }	

let startFile fname =
  current := { linenum  = 1 ;
               linepos  = 0 ;
               fileName = fname}

let startNewline n =
  let i = !current in
  begin
    i.linenum <- i.linenum + 1 ;
    i.linepos <- n
  end

    
let error n msg = 
  let i = !current in
    Printf.eprintf "%s at %s: %d.%d\n" 
      msg i.fileName i.linenum (n - i.linepos)
       
