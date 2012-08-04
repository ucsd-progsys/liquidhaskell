Require Import 
 List Program Decidable Sumbool.

Set Implicit Arguments.

Section StackSet_defs.

Require Import Aux.

(*******************************************************************
** Variables corresponding to type classes                        **
*******************************************************************)

Variable (i l a sd : Set).

Variable eqi : forall (x y : i), {x = y} + {x <> y}.
Definition beqi (x y : i) : {b : bool | if b then x = y else x <> y}
  := bool_of_sumbool (eqi x y).

Variable eqa : forall (x y : a), {x = y} + {x <> y}.
Definition beqa (x y : a) : {b : bool | if b then x = y else x <> y}
  := bool_of_sumbool (eqa x y).

Definition eqOption : forall (x y : option a), {x = y} + {x <> y}.
  decide equality; apply eqa.
  Defined.

Definition beqOption (x y : option a) : {b : bool | if b then x = y else x <> y}
  := bool_of_sumbool (eqOption x y).

(*******************************************************************
** Axiomatic assumptions about Data.Map                           **
*******************************************************************)

Axiom FMap : Set -> Set -> Set.
Axiom empty : forall k a, FMap k a.
Axiom insert : forall (k a : Set), k -> a -> FMap k a -> FMap k a.
Axiom remove : forall (k a : Set), k -> FMap k a -> FMap k a.
Axiom r : Set.

(*******************************************************************
** Data types for stacksets                                       **
*******************************************************************)

Definition sid : Set := nat.

Definition eqsid (x y : sid) : {x = y} + {x <> y}.
  decide equality.
  Defined.

Definition beqsid (x y : sid) : {b : bool | if b then x = y else x <> y}
  := bool_of_sumbool (eqsid x y).

Record stack : Set :=
  Stack
    { getUp : list a
    ; getFocus :  a
    ; getDown : list a
    }.

Record workspace : Set :=
  Workspace
    { getTag : i
    ; getLayout : l
    ; getStack : option stack
    }.

Inductive rationalRect : Set :=
  RationalRect : r -> r -> r -> r -> rationalRect.

Record screen : Set :=
  Screen
    { getWorkspace : workspace
    ; getScreen : sid
    ; getScreenDetail : sd
    }.

Record stackSet : Set :=
  StackSet
    { getCurrent : screen
    ; getVisible : list screen
    ; getHidden : list workspace
    ; getFloating : FMap a rationalRect
    }.

(******************************************************************* *)
(* ** Functions from StackSet.hs re-implemented in Coq               ** *)
(* *******************************************************************)

Definition workspaces : stackSet -> list workspace :=
  fun s => (getWorkspace (getCurrent s)) ::
    map (fun x => getWorkspace x) (getVisible s) ++ getHidden s.

Definition new
  (m : l)
  (wids : {wids : list i | wids <> nil })
  (sds  : {sds : list sd | length sds <= length (proj1_sig wids) /\ sds <> nil})
  : stackSet.
    refine (
    let seenUnseen := splitAt (length (proj1_sig sds)) (map (fun i => Workspace i m None) (proj1_sig wids))
    in let zippy := zipWith3 Screen
                      (fst seenUnseen)
                      (seq 0 (length (proj1_sig wids)))
                      (proj1_sig sds)
    in match zippy return (zippy = zipWith3 Screen
                      (fst seenUnseen)
                      (seq 0 (length (proj1_sig wids)))
                      (proj1_sig sds) -> stackSet)  with
         | (cur :: visi) => fun _ => 
               StackSet cur visi (snd seenUnseen) (empty a rationalRect)
         | nil => _
       end _).
    intro H.
    destruct wids as ([ | wid wids] & prf).
    contradiction prf; auto.
    destruct sds as ( [ | sid sids] & (H1 & H2)).  
    contradiction H2; auto.
    unfold seenUnseen in H.
    simpl in H.
    discriminate H.
    unfold zippy; auto.
    Defined.

Definition currentTag : stackSet -> i :=
  fun s => getTag (getWorkspace (getCurrent s)).

Definition _tagMember (x : i) (stckset : stackSet) :
    let tags := map getTag (workspaces stckset)
    in {In x tags} + {~In x tags} :=
    let tags := map getTag (workspaces stckset)
    in In_dec (A := i) eqi x tags.

Definition _view
  (x : i) (s : stackSet) : stackSet :=
  match eqi x (currentTag s) with
    | left eq => s
    | _ => 
      match find (fun y => proj1_sig (beqi x (getTag (getWorkspace y)))) (getVisible s) with
        | Some x =>
          match s with
            StackSet c vs us f => 
              let p x y := proj1_sig (beqsid (getScreen x) (getScreen y)) in
              StackSet x (deleteBy p x vs) us f
          end
        | _ =>
          match find (fun y => proj1_sig (beqi x (getTag y))) (getHidden s) with 
            | Some x =>
              match s with
                | StackSet c vs us f =>
                  let c' := match c with
                              | Screen _ sid sd => Screen x sid sd 
                            end 
                  in let p x y := proj1_sig (beqi (getTag x) (getTag y)) in
                  StackSet c' vs (getWorkspace c :: deleteBy p x us) f
              end
            | None => s
          end
      end
  end.

Definition _greedyView (w : i) (ws : stackSet) : stackSet :=
  let wTag x := proj1_sig (beqi w (getTag x))
  in if existsb wTag (getHidden ws) then _view w ws
     else match find (fun x => wTag (getWorkspace x)) (getVisible ws) with
            | None => ws
            | Some s => match ws with
                          | StackSet c vs us f =>
                            let c' := c
                            in let vs' :=
                              match s with
                                | Screen w sid sd =>
                                  Screen (getWorkspace (getCurrent ws)) sid sd
                                  :: filter (fun x => negb (wTag (getWorkspace x))) vs
                              end
                            in StackSet c' vs' us f
                        end
            end.

Definition lookupWorkspace (sc : sid) (w : stackSet) : option i :=
  let ws := filter (fun w => proj1_sig (beqsid sc (getScreen w)))
                   (getCurrent w :: getVisible w)
  in match ws with
      | nil => None
      | (Screen y _ _ :: _) => Some (getTag y)
    end.

(* Called "with" in StackSet.hs *)
Definition withStack : forall b,
  b -> (stack -> b) -> stackSet -> b :=
  fun b y f s =>
    maybe y f (getStack (getWorkspace (getCurrent s))).

Definition modify :
  option stack -> (stack -> option stack)
  -> stackSet -> stackSet :=
  fun d f s =>
    match s with
      StackSet (Screen (Workspace i l x) sid sd) v h m =>
        StackSet (Screen (Workspace i l (withStack d f s)) sid sd) v h m end.

Definition modify' :
  (stack -> stack) -> stackSet -> stackSet :=
  fun f => modify None (fun x => Some (f x)).

Definition peek : stackSet -> option a :=
  withStack None (fun x => Some (getFocus x)).

Definition integrate : stack -> list a :=
  fun s => match s with
             Stack u x d => rev u ++ x :: d
           end.

Definition integrate' : option stack -> list a :=
  fun s => maybe nil (fun x => integrate x) s.

Definition differentiate : list a -> option stack :=
  fun xs => match xs with
              | nil => None
              | y :: ys => Some (Stack nil y ys)
            end.

(* Called filter in Xmonad *)
Definition filterStack :
  (a -> bool) -> stack -> option stack :=
    fun p s => match s with
                 | Stack ls c rs =>
                   match filter p (c :: rs) with
                     | c' :: rs' => Some (Stack (filter p ls) c' rs')
                     | nil => match filter p ls with
                                | c' :: ls' => Some (Stack ls' c' nil)
                                | nil => None
                              end
                   end
               end.

Definition index : stackSet -> list a :=
  withStack nil (fun x => integrate x).

Definition focusUp' : stack -> stack :=
  fun s => match s with
             | Stack (l :: ls) c rs => Stack ls l (c :: rs)
             | Stack nil c rs => Stack (tail (rev (c :: rs))) (hd c (rev rs)) nil
           end.

Definition swapUp' : stack -> stack :=
  fun s => match s with
             | Stack (l :: ls) c rs => Stack ls c (l :: rs)
             | Stack nil c rs => Stack (rev rs) c nil
           end.

Definition reverseStack : stack -> stack :=
  fun s => match s with
             | Stack ls c rs => Stack rs c ls
           end.

Definition focusUp : stackSet -> stackSet :=
  fun s => modify' (fun x => focusUp' x) s.

Definition focusDown' : stack -> stack :=
  fun s => reverseStack (focusUp' (reverseStack s)).

Definition focusDown : stackSet -> stackSet :=
  fun s => modify' (fun x => focusDown' x) s.

Definition swapUp : stackSet -> stackSet :=
  fun s => modify' (fun x => swapUp' x) s.

Definition swapDown : stackSet -> stackSet
  := fun s => modify' (fun x => reverseStack (swapUp' (reverseStack x))) s.

Definition screens : stackSet -> list screen :=
  fun s => getCurrent s :: getVisible s.

Definition allWindows : stackSet -> list a :=
  fun s => flat_map (fun x => integrate' (getStack x))  (workspaces s).

Definition mapWorkspace : (workspace -> workspace) -> stackSet -> stackSet :=
  fun f s => let updateScreen scr := match scr with
                                       | Screen w s sd => Screen (f w) s sd
                                     end
    in match s with
         | StackSet c v h fl =>
             StackSet (updateScreen c) (map updateScreen v) (map f h) fl
       end.

Definition _findTag : a -> stackSet -> option i :=
  fun x s =>
    let has := fun x opt =>
      match opt with
        | None => false
        | Some (Stack ls c rs) => match In_dec eqa x (c :: ls ++ rs) with
                                    | left _ => true
                                    | right _ => false
                                  end
      end
    in match
      filter (fun w => has x (getStack w)) (workspaces s) with
        | nil => None
        | x :: _ => Some (getTag x)
       end.

Definition _member : a -> stackSet -> bool :=
  fun x s =>
    match _findTag x s with
      | None => false
      | Some _ => true
    end.

Definition _renameTag (old new : i) : stackSet -> stackSet :=
     let rename := fun w => match eqi (getTag w) old with
                              | left _ => Workspace new (getLayout w) (getStack w)
                              | right _ => w
                            end
     in mapWorkspace rename.

Definition shiftMaster : stackSet -> stackSet :=
  modify' (fun c => match c with
                      | Stack nil _ _ => c
                      | Stack ls t rs => Stack nil t (rev ls ++ rs)
                    end).

Definition focusMaster : stackSet -> stackSet.
  refine (
    modify' (fun c => match c with
                        | Stack [] _ _ => c
                        | Stack (l :: ls) c rs =>
                          let revLs := rev (l :: ls) in
                          match revLs return (rev (l :: ls) = revLs -> stack) with
                            | nil => _
                            | x :: xs => fun _ => Stack nil x (xs ++ c :: rs)
                          end _
                      end)).
  intro H; assert (D : l0 :: ls = nil);
    [apply revNil; auto | discriminate D].
  auto.
  Defined.
  
Definition rotate : list a -> list a := fun xs =>
  match xs with
    | nil => nil
    | x :: xs => xs ++ [x]
  end.

Definition swapMaster : stackSet -> stackSet :=
  modify' (fun c => match c with
                      | Stack nil _ _ => c
                      | Stack ls c rs => 
                          let rs' := rotate (rev ls) ++ rs in
                          Stack nil c rs'
                    end).

Definition _insertUp : a -> stackSet -> stackSet :=
  fun x s =>
  if _member x s
    then s
    else modify
      (Some (Stack nil x nil))
      (fun s => match s with
                  | Stack l c r => Some (Stack l x (c :: r))
                end) s.

Definition _ensureTags : l -> list i -> stackSet -> stackSet :=
  fun label allt st =>
    let fix et is rn s :=
      match is , rn return stackSet with
        | nil , _ => s
        | i :: is , rn =>
          match _tagMember i s with
            | left _ => et is rn s
            | right _ =>
              match rn , s with
                | nil , StackSet c v h f =>
                  et is nil (StackSet c v (Workspace i label None :: h) f)
                | (r :: rs) , s => et is rs (_renameTag r i s)
              end
          end
      end
    in et allt
          (removeList eqi (map getTag (workspaces st)) allt) st.


Definition sink : a -> stackSet -> stackSet :=
  fun w s => match s with
               | StackSet c v h f => StackSet c v h (remove w f)
             end.

Definition float : a -> rationalRect -> stackSet -> stackSet :=
  fun w r s => match s with
                 | StackSet c v h f => StackSet c v h (insert w r f)
               end.

Definition _delete' : a -> stackSet -> stackSet :=
   fun w s =>
     let removeFromWorkspace ws :=
       match ws with
         | Workspace i l stk => Workspace i l
             (option_bind stk (filterStack (fun x => negb (proj1_sig (beqa x w)))))
       end
     in let removeFromScreen scr :=
       match scr with
         | Screen ws sid sd => Screen (removeFromWorkspace ws) sid sd
       end
     in match s with
       | StackSet c v h f =>
         StackSet (removeFromScreen c)
         (map removeFromScreen v)
         (map removeFromWorkspace h)
         f
     end.

Definition _delete : a -> stackSet -> stackSet :=
  fun w s => sink w (_delete' w s).
 
Definition _shift : i -> stackSet -> stackSet :=
  fun n s =>
    let curtag := getTag (getWorkspace (getCurrent s))
    in let go w := _view curtag (_insertUp w (_view n (_delete' w s)))
    in  match _tagMember n s , eqi n curtag with
          | left _ , right _ => maybe s go (peek s)
          | _ , _ => s
        end.

Definition findDistance (w : a) (stk: stack) : option nat :=
  match stk with
    | Stack ls t rs => elemIndex eqa w (t :: ls ++ rev rs)
  end.

Definition _focusWindow : a -> stackSet -> stackSet :=
  fun w s =>
    match eqOption (Some w) (peek s) with
      | left p => s
      | right _ =>
        let go := _findTag w s >>= fun n =>
                  withStack None (findDistance w) (_view n s) >>= fun d =>
                  Some (applyN d (_view n s) focusUp)
        in maybe s id go
   end.

Definition onWorkspace (n : i) (f : stackSet -> stackSet) (s : stackSet)
  := _view (currentTag s) (f (_view n s)).

Definition _shiftWin : i -> a -> stackSet -> stackSet :=
  fun n w s =>
  let go from x := onWorkspace n (_insertUp w) (onWorkspace from (_delete' w) x)
  in match _findTag w s with
       | None => s
       | Some from =>
          match _tagMember n s , eqi n from with
            | left p , right q => go from s
            | _ , _ => s
          end
     end.

End StackSet_defs.

Definition mapLayout (a i l l' sd : Set)
  (f : l -> l') (s : stackSet i l a sd) : stackSet i l' a sd
  := match s with
       | StackSet v vs hs m =>
         let fWorkspace := fun w =>
           match w with
             | Workspace t x s => Workspace t (f x) s
           end
           in let fScreen s :=
             match s with
               | Screen ws s sd => Screen (fWorkspace ws) s sd
             end in
             StackSet (fScreen v) (map fScreen vs) (map fWorkspace hs) m
     end.

