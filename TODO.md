TODO
====

String Literals
---------------

"xyz" ==> ELit fix#lit#xyz :: String

1. Add to `Constant`

    data StrLit   = SL !String
   
2. Programmatic:
        instance Expression StrLit where 
          expr (SL "xyz") = ELit fix#str#xyz : String
        
        construct: 
          expr $ SL "xyz"

3. Parsing
        "xyz"          ~~~> ELit lit#String#xyz
        lit#String#xyz ~~~> ELit lit#String#xyz

4. ToFixpoint 
      > round up ELIT lit#String#xyz and make them 
         constant lit#String#xyz :: String
         
5. Printing/Serializing/PPrint
      > ELIT lit#String#xyz --> "xyz"
