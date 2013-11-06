TODO
====

String Literals
---------------

How to represent the string literal `"xyz"`

1. data SymConst = SL String
   
2. Programmatic: ESym (SL "xyz")
      
3. Printed as "xyz"

4. Parsed EITHER as the encoded symbol OR as "xyz"

5. fixpoint-encoded as a symbol: `constant lit#String#xyz : Str`

Only missing piece: walk over ENTIRE FI and round up ALL the encoded symbols
so fixpoint.native doesn't grumble about unbound symbols. Can hack Subable to
include:

    symconsts :: a -> [SymConst]

and then fill in appropriately. (Or use syb)


