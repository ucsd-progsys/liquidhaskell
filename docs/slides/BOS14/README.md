Plan
====

* [5] 00_Motivation: "Go Wrong"

* [5] 01_SimpleRefinements (upto VC, Abs, but no Kvar)
    + Demo : 00_Refinements.hs (upto "wtAverage")

* [10] 02_Measures
    + Show : RBTree-Col-Height.hs
    + Demo : 01_Elements.hs
    ? Show : Eval.hs

* [5] 04_Abstract Refinements
    + Demo : 02_AbstractRefinements.hs (listMax)
	
* [5] 06_Inductive
	+ Describe: ?foldn, foldr
    + Demo:  02_AbstractRefinements.hs (foldr, append, filter)
	
* [5] 08_Recursive
	+ Describe: list-ord
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)
	+ Show:  GhcListSort.hs 

	+ Describe: tree-ord
	+ Demo:     RBTree-Ord
	+ Demo:     stream

* [5] 07_Array
	+ Describe: Array
	+ Demo:     KMP
  
* [3] 11_Evaluation.lhs 

* [2] 12_Conclusion.lhs

----

fix hs/02_AbstractRefinements.hs so that

1. listMax
2. first, `ifoldr`
3. append, filter, insertSort

go back to list-ord

4. demo: insertSort 
5. show: RBTree-Ord
6. demo: stream

---
