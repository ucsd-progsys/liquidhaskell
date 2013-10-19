module CSV where

-- | Using LiquidHaskell for CSV lists
-- c.f. http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/

data CSV = Csv { headers :: [String]
               , rows    :: [[String]]
               }

{-@ data CSV = Csv { headers :: [String]
                   , rows    :: [{v:[String] | (len v) = (len headers)}]
                   }
  @-}

-- Eeks, we missed the column name.

csvBad1 = Csv ["Date"] 
              [ ["Mon", "1"]
              , ["Tue", "2"]
              , ["Wed", "3"] 
              ]

-- Eeks, we missed a column.

csvBad2 = Csv ["Name", "Age"] 
              [ ["Alice", "32"]
              , ["Bob"        ]
              , ["Cris" , "29"] 
              ]
                      
-- All is well! 

csvGood = Csv ["Id", "Name", "Days"]
              [ ["1", "Jan", "31"]
              , ["2", "Feb", "28"]
              , ["3", "Mar", "31"]
              , ["4", "Apr", "30"] 
              ]
