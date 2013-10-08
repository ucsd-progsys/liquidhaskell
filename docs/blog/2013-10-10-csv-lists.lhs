---
layout: post
title: "CSV Lists"
date: 2013-10-10 16:12
comments: true
external-url:
categories: measures
author: Ranjit Jhala
published: true 
demo: Csv.hs
---

Most demonstrations for verification techniques involve programs with complicated
invariants and properties. However, these methods can often be rather useful for
describing simple but important aspects of APIs or programs with more humble
goals. I saw a rather nice example of using Scala's `Shapeless` library for
preventing off-by-one errors in CSV processing code. Here's the same, short, 
example rephrased for LiquidHaskell.

<!-- more -->

\begin{code}
module CSV where

-- | Using LiquidHaskell for CSV lists
-- c.f. http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/
\end{code}


The Type
--------

Suppose you wanted to represent *tables* as a list of comma-separated values.

For example, here's a table listing the articles and prices at the coffee shop
I'm sitting in right now:

    Item        Price
    ----        -----
    Espresso    2.25
    Macchiato   2.75
    Cappucino   3.35
    Americano   2.25

You might represent this with a simple Haskell data type:

\begin{code}

data CSV = Csv { headers :: [String]
               , rows    :: [[String]]
               }
\end{code}

and now, the above table is just:

\begin{code}
zumbarMenu = Csv [  "Item"     , "Price"]
                 [ ["Espresso" , "2.25" ]  
                 , ["Macchiato", "2.75" ]
                 , ["Cappucino", "3.35" ]
                 , ["Americano", "2.25" ]
                 ]
\end{code}

The Errors 
----------

Our `CSV` type supports tables with an arbitrary number of `headers` and
`rows` but of course, we'd like to ensure that each `row` has data for *each*
header, that is, we don't end up with tables like this one

\begin{code}
-- Eeks, we missed the header name!

csvBad1 = Csv [  "Date" {- ??? -} ] 
              [ ["Mon", "1"]
              , ["Tue", "2"]
              , ["Wed", "3"] 
              ]

\end{code}

or this one, 

\begin{code}
-- Blergh! we missed a column.

csvBad2 = Csv [  "Name" , "Age"  ] 
              [ ["Alice", "32"   ]
              , ["Bob"  {- ??? -}]
              , ["Cris" , "29"   ] 
              ]
\end{code}

Alas, both the above are valid inhabitants of the Haskell `CSV` type, and 
so, sneak past GHC.

The Invariant 
-------------

Thus, we want to *refine* the `CSV` type to specify that the *number* of
elements in each row is *exactly* the same as the   *number* of headers.

To do so, we merely write a refined data type definition:

\begin{code}
{-@ data CSV = Csv { headers :: [String]
                   , rows    :: [{v:[String] | (len v) = (len headers)}]
                   }
  @-}
\end{code}

Here `len` is a *measure* [denoting the length of a list][list-measure].
Thus, `(len headers)` is the number of headers in the table, and the
refinement on the `rows` field states that:

(a) *each* `row` is a list of `String`s, 
(b) with exactly the same number of elements as the number of `headers`.

Thus, we can now have our arbitrary-arity tables, but LiquidHaskell will 
make sure that we don't miss entries here or there.

\begin{code}
-- All is well! 

csvGood = Csv ["Id", "Name", "Days"]
              [ ["1", "Jan", "31"]
              , ["2", "Feb", "28"]
              , ["3", "Mar", "31"]
              , ["4", "Apr", "30"] 
              ]
\end{code}

Bonus Points
------------

How would you modify the specification to prevent table with degenerate entries
like this one?

\begin{code}
deg = Csv [  "Id", "Name", "Days"]
          [ ["1" , "Jan" , "31"]
          , ["2" , "Feb" , ""]
          ]
\end{code}

[shapeless-csv]: http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/
[list-measure]:  /blog/2013/01/31/safely-catching-a-list-by-its-tail.lhs/ 
