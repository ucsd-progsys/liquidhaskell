var x:Int; 
var y:Int;
assert (0 <= x); 
assert (x < y); 
push; 
assert (not (0 <= y)); 
check;
pop;
push;
assert (0 <= y); 
check;
pop

