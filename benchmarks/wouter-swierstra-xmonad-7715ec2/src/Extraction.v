
Require Import Arith List Program Decidable Sumbool Logic.
Require Import StackSet.
Extraction Language Haskell.

Extract Constant StackSet.FMap "a" "b" => "M.Map a b".
Extract Constant StackSet.empty => "M.empty".
Extract Constant StackSet.insert => "M.insert".
Extract Constant StackSet.remove => "M.delete".
Extract Constant StackSet.r => "Rational".

Extract Inductive unit => "()" [ "()" ].

Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inductive sumbool => "Bool" [ "True" "False" ].
Extract Constant orb => "(||)".
Extract Constant andb => "(&&)".
Extract Constant negb => "not".
Extraction Inline orb negb andb bool_of_sumbool StackSet.beqi StackSet.beqa.

Extract Inductive list => "List" [ "[]" "(:)" ].
Extract Inlined Constant tl => "tail".

(* These don't work yet?*)
(* Extract Constant rev => "reverse". *)
(* Extraction Inline rev. *)
(* filter flat_map splitAt zipWith3 *)
Extract Inlined Constant Datatypes.length => "length".
Extract Inlined Constant Coq.Lists.List.filter => "filter".
Extract Inlined Constant app => "(++)".
Extract Inlined Constant List.map => "map".
Extract Inlined Constant last => "last".
Extraction Inline last.

Extract Inductive option => "Maybe" [ "Just" "Nothing" ].
Extract Constant option_rect => "flip maybe".
Extraction Inline option_rect option_rec.
(* What about maybe option_bind *)

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Constant fst => "fst".
Extract Constant snd => "snd".
Extraction Inline fst snd.

Extraction Inline id proj1_sig sumbool_rec sumbool_rect.
Extraction Inline eq_rect eq_rec eq_rec_r.

Extract Constant eq_nat_dec => "(==)".
Extraction Inline eq_nat_dec.

Extract Inductive Datatypes.nat => "Int" ["0" "succ"]
  "(\fO fS n -> if n==0 then fO () else fS (n-1))".

Extract Inductive StackSet.stackSet => "StackSet" ["StackSet"].
Extract Inductive StackSet.workspace => "Workspace" ["Workspace"].
Extract Inductive StackSet.rationalRect => "RationalRect" ["RationalRect"].
Extract Inductive StackSet.screen => "Screen" ["Screen"].
Extract Inductive StackSet.stack => "Stack" ["Stack"].
Extract Constant StackSet.beqsid => "(==)".
Extract Constant StackSet.eqsid => "(==)".
Extraction Inline StackSet.beqsid StackSet.eqsid.

Extraction "StackSet.hs" 
  StackSet.new 
  StackSet._view StackSet._greedyView
  StackSet.lookupWorkspace
  StackSet.screens StackSet.workspaces
  StackSet.screens StackSet.workspaces  StackSet.allWindows StackSet.currentTag
  StackSet.peek StackSet.index StackSet.integrate StackSet.integrate' StackSet.differentiate
  StackSet.focusUp StackSet.focusDown StackSet.focusUp' StackSet.focusDown' StackSet.focusMaster 
  StackSet._focusWindow
  StackSet._tagMember StackSet._renameTag StackSet._ensureTags StackSet._member 
  StackSet._findTag 
  StackSet.mapWorkspace StackSet.mapLayout
  StackSet._insertUp StackSet._delete StackSet._delete' StackSet.filterStack
  StackSet.swapUp StackSet.swapDown StackSet.swapMaster StackSet.shiftMaster 
  StackSet.modify StackSet.modify' StackSet.float StackSet.sink
  StackSet._shift StackSet._shiftWin.

(* Problems with Haskell extraction:
  - need type classes
  - better support for interfacing with libraries like Data.Map
  - limited control over generated data types (like strictness annotations)
*)