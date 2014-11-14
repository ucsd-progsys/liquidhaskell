Todo
----

- CREATE 00_Motivation_Bugs.lhs **TUFTS**
  + sequence, BUGs, 1984, etc.

- CREATE HARDWIRED-RED-BLACK-BST.lhs **TUFTS**

- CREATE 03_Memory.lhs **TUFTS,BOS**
  + and associated demo file, from eseidel's BS demo.

- UPDATE 11_Evaluation.lhs **TUFTS,BOS** 
	+ Add bits about "comments" ---> "types"
  
- UPDATE 09_Laziness.lhs **BOS**
  + use simpler example
  + show SUBTYPING constraints/FALSE
  
- UPDATE 10_Termination.lhs **BOS**
  + mirror sequence in 03_Termination.hs


BOS-Haskell Plan
----------------

* [5]  00_Motivation: "Go Wrong"

* [15]  01_SimpleRefinements (upto VC, Abs) but no Kvar)

* [15] 02_Measures
    + Demo : 00_Refinements.hs (modify score to letter grade)
    + Demo : 01_Elements.hs
	+ Show : RED-BLACK
	
* [10] 03_Memory

* [??] 10_Termination.lhs

* BREAK

* [10]  04_Abstract Refinements
    + Demo : 02_AbstractRefinements.hs (listMax)
	
* [10]  06_Inductive
	+ Describe: foldr
    + Demo:  02_AbstractRefinements.hs (foldr, append, filter)

* [10]  08_Recursive
	+ Describe: list-ord
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)
	+ Show:  GhcListSort.hs 
	+ Describe: tree-ord
	+ Demo:     Stream

* [5] 07_Array
  	+ Describe: Array
  	+ Demo:     KMP

* [3]  11_Evaluation.lhs 

* [2]  12_Conclusion.lhs




Tufts Plan
----------

* [5] 00_Programs_and_Bugs
		+ The first BUG
		+ Morris Worm
		+ SLAMMER
		+ NORTHEAST BlackOut
		+ 2014: GotoFail, HeartBleed, ShellShock.

	    + 1984

	    "In the end we shall make thoughtcrime literally
		 impossible, because there will be no words to express it."

		+ George Orwell, "1984"
	    + NEWSPEAK "++ungood";
		+ HASKELL 	

* [5]  00_Motivation: "Well typed Program Go Wrong"
	    + No heartbleed because, well no one cares. yet.
		
* [10]  01_SimpleRefinements
        + upto VC, Abs
		+ include Kvar 

* [10] 02_Measures 
        + Demo    : 00_Refinements.hs
        + Demo    : 01_Elements.hs

		+ Complex : RED-BLACK Trees
		  HARDWIRE THE BST DEFINITION.
		  TODO: Define, show OK tree, show BAD tree.

* [10] 03_Memory

* [3]  11_Evaluation.lhs 
		+ Add bits about "comments" ---> "types"
		
* [2]  12_Conclusion.lhs



Brown Plan
----------

* [5]  00_Motivation: "Go Wrong"

* [5]  01_SimpleRefinements (upto VC, Abs, but no Kvar)

* [10] 02_Measures [TODO: cut RED-BLACK]
    + Demo : 00_Refinements.hs
    + Demo : 01_Elements.hs

* [5]  04_Abstract Refinements
    + Demo : 02_AbstractRefinements.hs (listMax)
	
* [5]  06_Inductive
	+ Describe: [TODO: CUT ?foldn] foldr
    + Demo:  02_AbstractRefinements.hs (foldr, append, filter)

* [5]  08_Recursive
	+ Describe: list-ord
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)
	+ Show:  GhcListSort.hs 
	+ Describe: tree-ord
	+ Demo:     Stream
 
* [3]  11_Evaluation.lhs 

* [2]  12_Conclusion.lhs



Harvard Plan
------------

* [5] 00_Motivation: "Go Wrong"

* [5] 01_SimpleRefinements (upto VC, Abs, but no Kvar)

* [10] 02_Measures [TODO: cut RED-BLACK]
    + Demo : 00_Refinements.hs (upto "wtAverage")
    + Demo : 01_Elements.hs

* [5] 04_Abstract Refinements
    + Demo : 02_AbstractRefinements.hs (listMax)
	
* [5] 06_Inductive
	+ Describe: [TODO: CUT ?foldn] foldr
    + Demo:  02_AbstractRefinements.hs (foldr, append, filter)

* [5] 08_Recursive
	+ Describe: list-ord
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)

	+ Show:  GhcListSort.hs 
	+ Describe: tree-ord
	+ [TODO: CUT] Demo:     RBTree-Ord
	+ Demo:     Stream

* [TODO: CUT] [5] 07_Array
  [TODO: CUT] 	+ Describe: Array
  [TODO: CUT] 	+ Demo:     KMP
  
* [3] 11_Evaluation.lhs 

* [2] 12_Conclusion.lhs

