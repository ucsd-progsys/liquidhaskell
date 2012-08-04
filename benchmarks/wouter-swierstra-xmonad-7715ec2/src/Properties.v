Require Import Aux List.
Require Import StackSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import ListLemmas.

Variable (i l a b sd : Set).

Definition invariant (i l a sd : Set) (s : StackSet.stackSet i l a sd) : Prop :=
  let visibles := map (fun x => getWorkspace x) (getVisible s) in
  let hiddens := getHidden s in
  let current := getWorkspace (getCurrent s) in
  let findStack := fun x => maybe nil (fun s => s :: nil) (getStack x) in
  let getFocusUpDown := fun t => getFocus t :: getUp t ++ getDown t in
  let ts := flat_map findStack (current :: visibles ++ hiddens) in
  NoDup (flat_map getFocusUpDown ts).

Implicit Arguments invariant.

Theorem prop_empty_I (m : l) (wids : {wids : list i | wids <> nil}) 
  (sds : {sds : list sd | length sds <= length (proj1_sig wids) /\ sds <> nil}) 
  : invariant (new l m wids sds).
  Proof.
    destruct sds as [sds [sdsLength nonNil]]; simpl in sdsLength.
    induction sds as [ | sd sds].
    (* Base case *)
      contradiction nonNil; auto.
    (* Cons case *)
      destruct wids as [wds widsProp]; induction wds as [ | wd wds].
      (* Base case *)
        simpl in *; absurd (S (length sds) <= 0); auto with arith.
      (* Cons case *)
      unfold new, invariant.
      simpl in *.
      rewrite FlatMapApp.
      rewrite FlatMapApp.      
   Admitted.

Theorem prop_empty (m : l) (wids : {wids : list i | wids <> nil}) 
  (sds : {sds : list sd | length sds <= length (proj1_sig wids) /\ sds <> nil}) 
  (eq_a_dec : forall x y, {x = y} + {x <> y}): forall x,
    ~ (eq_true (StackSet._member eq_a_dec x (new l m wids sds))).
  Proof.
    intros x H.
    destruct wids as [[ | wid wids] NotNilWids];
      [now (contradiction NotNilWids) | ].
  destruct sds as [[ | sd sds] [SdsH1 SdsH2]];
      [now (contradiction SdsH2) | ].
  simpl in H.
  Admitted.

Theorem prop_differentiate (xs : list a) :
  match xs with
    | nil => differentiate xs = None
    | x :: xs => differentiate (x :: xs) = Some (Stack nil x xs)
  end.
  destruct xs as [ | x xs]; reflexivity.
  Qed.

Definition hidden_spaces (x : stackSet i l a sd) := map (fun s => getWorkspace s) (getVisible x) ++ getHidden x.

Lemma modify'_getVisible (f : stack a -> stack a) (x : stackSet i l a sd) :
  getVisible (modify' f x) = getVisible x.
  Proof.
  destruct x; destruct getCurrent; destruct getWorkspace.
  reflexivity.
  Qed.

Lemma modify'_getHidden (f : stack a -> stack a) (x : stackSet i l a sd) : 
  getHidden (modify' f x) = getHidden x.
  Proof.
  destruct x; destruct getCurrent; destruct getWorkspace; reflexivity.
  Qed.

Lemma modify'_hidden (f : stack a -> stack a) (x : stackSet i l a sd) : 
  hidden_spaces (modify' f x) = hidden_spaces x.
  Proof.
    unfold hidden_spaces.  
    rewrite (modify'_getHidden f).
    rewrite (modify'_getVisible f).
    reflexivity.
  Qed.

Lemma modify_getHidden (d : option (stack a)) (f : stack a -> option (stack a)) (x : stackSet i l a sd) : 
  getHidden (modify d f x) = getHidden x.
  Proof.
    destruct x; destruct getCurrent; destruct getWorkspace; reflexivity.
  Qed.

Lemma modify_getVisible (d : option (stack a)) (f : stack a -> option (stack a)) (x : stackSet i l a sd) : 
  getVisible (modify d f x) = getVisible x.
  Proof.
    destruct x; destruct getCurrent; destruct getWorkspace; reflexivity.
  Qed.


Lemma modify_hidden (d : option (stack a)) (f : stack a -> option
  (stack a)) (x : stackSet i l a sd) : hidden_spaces (modify d f x) =
  hidden_spaces x.  
  Proof.  
  unfold hidden_spaces.  rewrite (modify_getHidden d f).  rewrite (modify_getVisible d f).
  reflexivity.  Qed.

Theorem prop_focus_down_local (s : stackSet i l a sd) :
  hidden_spaces (focusDown s) = hidden_spaces s.
  Proof.
  unfold focusDown; rewrite modify'_hidden; reflexivity.
  Qed.

Theorem prop_focus_up_local (s : stackSet i l a sd) : 
  hidden_spaces (focusUp s) = hidden_spaces s.
  Proof.
  unfold focusUp; rewrite modify'_hidden; reflexivity.
  Qed.

Theorem prop_focus_master_local (s : stackSet i l a sd) :
  hidden_spaces (focusMaster s) = hidden_spaces s.
  Proof.
    unfold focusMaster; rewrite modify'_hidden; reflexivity.
  Qed.

Lemma stackSet_eq (x y : stackSet i l a sd) :
  (getCurrent x = getCurrent y) ->
  (getVisible x = getVisible y) ->
  (getHidden x = getHidden y) ->
  (getFloating x = getFloating y) ->
  x = y.
  Proof.
    intros H1 H2 H3 H4.
    destruct x. simpl in *.
    rewrite H1, H2, H3, H4.
    destruct y; reflexivity.
  Qed.

Lemma screen_eq (x y : screen i l a sd ) : 
  (getWorkspace x = getWorkspace y) ->
  (getScreen x = getScreen y) ->
  (getScreenDetail x = getScreenDetail y) ->
  x = y.
  Proof.
    intros H1 H2 H3; destruct x; simpl in *; rewrite H1, H2, H3; destruct y; reflexivity.
  Qed.

Lemma workspace_eq (x y : workspace i l a) :
  (getTag x = getTag y) ->
  (getLayout x = getLayout y) ->
  (getStack x = getStack y) ->
  x = y.
  Proof.
    intros H1 H2 H3; destruct x; simpl in *; rewrite H1, H2, H3; destruct y; reflexivity.
  Qed.

Theorem prop_delete_local (s : stackSet i l a sd) (eq_dec : forall x y, {x = y} + {x <> y}) :
  match peek s with
    | None => True
    | Some i => hidden_spaces s = hidden_spaces (_delete eq_dec i s)
  end.
  Proof.
  remember (peek s). 
  destruct o as [x | ]; [ | trivial].
  unfold _delete.
  unfold sink.
  unfold _delete'.
  destruct s.
  destruct getCurrent.
  f_equal.
  destruct getWorkspace.
  apply stackSet_eq.
  simpl in *.
  apply screen_eq.
  simpl.
  apply workspace_eq; try reflexivity.
  destruct getStack.
  unfold peek in Heqo.
  unfold withStack in Heqo.
  simpl in *.
  unfold filterStack.
  unfold getFocus in Heqo.
  destruct s.
  injection Heqo.
  intros Eq.
  rewrite <- Eq in *.
  simpl.
  assert (negb (proj1_sig (beqa eq_dec x x)) = false).
  generalize (beqa eq_dec x x).
  destruct s.
  Admitted.

Theorem prop_swap_master_local (s : stackSet i l a sd) : 
  hidden_spaces s = hidden_spaces (swapMaster s).
  Proof.
    unfold swapMaster; rewrite modify'_hidden; reflexivity.
  Qed.    

Theorem prop_swap_left_local (s : stackSet i l a sd) : 
  hidden_spaces s = hidden_spaces (swapUp s).
  Proof.
    unfold swapUp; rewrite modify'_hidden; reflexivity.
  Qed.    

Theorem prop_swap_right_local (s : stackSet i l a sd) : 
  hidden_spaces s = hidden_spaces (swapDown s).
  Proof.
    unfold swapDown; rewrite modify'_hidden; reflexivity.
  Qed.    

Theorem prop_shift_master_local (s : stackSet i l a sd) : 
  hidden_spaces s = hidden_spaces (shiftMaster s).
  Proof.
    unfold shiftMaster; rewrite modify'_hidden; reflexivity.
  Qed.

Lemma focusUpDown' (s : stack a) :
  focusDown' (focusUp' s) = s.
  Proof.
    destruct s as [[ | l ls] c rs]; try reflexivity.
    unfold StackSet.focusUp'; simpl.
    assert (H : rev (rev rs) = rs); try apply rev_involutive.
    generalize (rev rs) as rrs, H.
    destruct rrs as [ | r rrs].
      (* Base case *)
      intro Eq; rewrite <- Eq; reflexivity.
      (* Inductive case *)
      unfold StackSet.focusDown'; simpl.
      intro Eq; rewrite rev_unit, <- Eq; reflexivity.
  Qed.

Lemma focusDownUp' (s : StackSet.stack a) :
  StackSet.focusUp' (StackSet.focusDown' s) = s.
  Proof.
    destruct s as [ls c [ | r rs]]; unfold StackSet.focusDown'; try reflexivity.
    simpl; f_equal.
    (* Proof that getUp is OK *)
    assert (H : rev ls = rev ls); auto.
    generalize H as Eq.
    generalize (rev ls) at 1 3 4 as rls.
    intros.
    destruct rls as [ | x xs].
      simpl; symmetry; apply revNil; rewrite Eq; reflexivity.
      simpl; rewrite rev_unit; simpl; rewrite revStep, Eq, rev_involutive; reflexivity.
    (* Proof that getFocus is OK *)
    destruct (rev ls) as [ | z zs]; simpl; try rewrite rev_unit; reflexivity.
  Qed.

Lemma modifyId (f : StackSet.stack a -> StackSet.stack a) (s : StackSet.stackSet i l a sd) : 
  (forall xs, f xs = xs) -> StackSet.modify' f s = s.
  Proof.
    intro H; destruct s.
    unfold StackSet.modify', StackSet.modify.
    destruct getCurrent; destruct getWorkspace; destruct getStack; repeat (f_equal). 
    unfold StackSet.withStack.
    simpl; f_equal; apply H; reflexivity.
  Qed.

Lemma modifyComp (f g : StackSet.stack a -> StackSet.stack a) (s : StackSet.stackSet i l a sd) : 
  StackSet.modify' f (StackSet.modify' g s) = StackSet.modify' (fun s => f (g s)) s.
  Proof.
    destruct s; unfold StackSet.modify', StackSet.modify.
    destruct getCurrent; destruct getWorkspace; destruct getStack; repeat (f_equal).
  Qed.

Theorem prop_focus_right (s : StackSet.stackSet i l a sd) :
  StackSet.focusDown (StackSet.focusUp s) = s.
  Proof.
    unfold StackSet.focusUp, StackSet.focusDown.
    rewrite modifyComp, modifyId; [ | intros; rewrite focusUpDown']; reflexivity.
  Qed.

Theorem prop_focus_left (s : StackSet.stackSet i l a sd) :
  StackSet.focusUp (StackSet.focusDown s) = s.
  Proof.
    unfold StackSet.focusUp, StackSet.focusDown.
    rewrite modifyComp, modifyId; auto; intros; rewrite focusDownUp'; reflexivity.
  Qed.

Theorem prop_swap_master_focus (x : StackSet.stackSet i l a sd) :
  StackSet.peek (StackSet.swapMaster x) = StackSet.peek x.
  Proof.
    destruct x; unfold StackSet.peek; unfold StackSet.swapMaster; unfold StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    unfold StackSet.withStack; unfold StackSet.getFocus.
    destruct getStack; simpl; [ destruct s; destruct getUp | ] ; reflexivity.
  Qed.

Theorem prop_swap_left_focus (x : StackSet.stackSet i l a sd) :
  StackSet.peek (StackSet.swapUp x) = StackSet.peek x.
  Proof.
    destruct x; unfold StackSet.peek; unfold StackSet.swapUp; unfold StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    unfold StackSet.withStack; unfold StackSet.getFocus.
    destruct getStack; simpl; [destruct s; destruct getUp | ]; reflexivity.
  Qed.

Theorem prop_swap_right_focus (x : StackSet.stackSet i l a sd) :
  StackSet.peek (StackSet.swapDown x) = StackSet.peek x.
  Proof.
    destruct x; unfold StackSet.peek; unfold StackSet.swapDown; unfold StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    unfold StackSet.withStack; unfold StackSet.getFocus; unfold StackSet.reverseStack.
    destruct getStack; simpl; [destruct s; destruct getDown | ]; simpl; reflexivity.
  Qed.

Theorem prop_swap_master_idempotent (x : StackSet.stackSet i l a sd) : 
  StackSet.swapMaster (StackSet.swapMaster x) = StackSet.swapMaster x.
  Proof.
    destruct x; unfold StackSet.swapMaster, StackSet.modify'.
    destruct getCurrent; destruct getWorkspace.
    destruct getStack as [ stack | ]; [ | reflexivity ].
    destruct stack as [ls c rs]; simpl.
    unfold StackSet.withStack; simpl.
    repeat f_equal.
    destruct ls; auto.
  Qed.


Theorem prop_screens_work (x : stackSet i l a sd) :
  screens x = getCurrent x :: getVisible x.
  Proof.
    destruct x; unfold screens; reflexivity.
  Qed.

Theorem prop_mapWorkspaceId (x : stackSet i l a sd) : 
  mapWorkspace (fun y => y) x = x.
  Proof.
    unfold mapWorkspace.
    destruct x.
    destruct getCurrent.
    rewrite map_id.
    replace (map (fun scr => match scr with
                               | {| getWorkspace := w; getScreen := s; getScreenDetail := sd0 |} =>
                                 {| getWorkspace := w; getScreen := s; getScreenDetail := sd0 |}
                             end)
                 getVisible)
      with getVisible.
    reflexivity.
    induction getVisible; [ reflexivity | ].
    simpl; rewrite <- IHgetVisible; destruct a0; reflexivity.
  Qed.

Require Import Coq.Program.Equality.

Theorem prop_focusMaster_idem (x : StackSet.stackSet i l a sd) :
  StackSet.focusMaster (StackSet.focusMaster x) = StackSet.focusMaster x.
  Proof.
    destruct x.
    unfold StackSet.focusMaster.
    unfold modify', modify, withStack.
    simpl.
    destruct getCurrent; destruct getWorkspace; destruct getStack; try reflexivity.
    destruct s as [ls c rs].
    apply stackSet_eq; try reflexivity.
    apply screen_eq; try reflexivity.
    apply workspace_eq; try reflexivity.
    simpl.
    destruct ls; try reflexivity.
    (* destruct (rev ls ++ a0 :: nil). *)
  Admitted.

Fixpoint concat (a : Set) (xss : list (list a)) : list a :=
  match xss with
    | nil => nil
    | xs :: xss => xs ++ concat a xss
  end.

Lemma PermutationRotate (xs : list a) : Permutation xs (rotate xs).
  induction xs; [constructor | ].
  apply Permutation_cons_app; rewrite app_nil_r; auto.
  Qed.
  

Theorem prop_insert_local (x : stackSet i l a sd) (eq_dec : forall x y, {x = y} + {x <> y}) :
  forall i, ~(eq_true (_member eq_dec i x)) -> hidden_spaces x = hidden_spaces (_insertUp eq_dec i x).
  Proof.
    intros y H.
    unfold _insertUp.
    destruct (_member eq_dec y x).
    reflexivity.
    rewrite modify_hidden.
    reflexivity.
  Qed.

Theorem prop_swap_master_I (s : StackSet.stackSet i l a sd) :
  invariant s -> invariant (swapMaster s).
  Proof.
    intro H; destruct s; destruct getCurrent; destruct getWorkspace; simpl.
    destruct getStack as [ | s]; auto.
    destruct s as [ls c rs]; auto.
    destruct ls as [ | l ls]; auto.
    unfold withStack; unfold invariant in *.
    apply (NoDupPerm _ _ _ H); clear H.
    simpl; constructor.
    do 2 (rewrite app_comm_cons; apply Permutation_app_tail).
    apply (Permutation_trans (l' := (rev ls ++ l :: nil)));
      [ apply Permutation_rev | apply PermutationRotate].
  Qed.

Theorem prop_view_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (_view eq_nat_dec n s).
  Proof.
    unfold _view.
    case (eq_nat_dec n (currentTag s)); auto.
    case (find (fun y  => proj1_sig (beqi eq_nat_dec n (getTag (getWorkspace y))))
         (getVisible s)).
    destruct s.
    intros s H1 H2.
Admitted.

Lemma invariant_lemma : forall (i l a sd : Set) (v v' : list (screen i l a sd)) (h h' : list (workspace i l a)) c f,
  Permutation v v' ->
  Permutation h h' ->
  invariant (StackSet c v h f) ->
  invariant (StackSet c v' h' f).
  Proof.  
    intros i l a sd v v' h h' c f Pv Ph.
    unfold invariant.
    intros I. apply (NoDupPerm _ _ _ I).
    simpl in *.
    apply PermutationFlatMap.
    apply Permutation_app.
    apply Permutation_refl.
    apply PermutationFlatMap.
    apply Permutation_app.
    apply Permutation_map.
    assumption.
    assumption.
  Qed.
Theorem prop_greedyView_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (_greedyView eq_nat_dec n s).
  Proof.
    unfold _greedyView.
    destruct (existsb (fun x => proj1_sig (beqi eq_nat_dec n (getTag x))) (getHidden s)).
    apply prop_view_I.
    destruct (find (fun x => proj1_sig 
                 (beqi eq_nat_dec n (getTag (getWorkspace x))))
                 (getVisible s)); auto.
    destruct s. destruct s0.
    apply invariant_lemma; try apply Permutation_refl.
    simpl.
  Admitted.

Theorem prop_focusUp_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (iterate n (focusUp (i:=nat) (l:=l) (a:=a)(sd:=sd)) s).
  Proof.
    generalize s; induction n; auto; clear s.
    intros s IHs; simpl.
    cut (invariant (focusUp s)).
    intro H; apply (IHn _ H).
    unfold invariant in *; simpl in *.
    rewrite FlatMapApp.
    apply (NoDupPerm _ _ _ IHs).
    rewrite FlatMapApp in *.
    apply (Permutation_app).
    destruct s.
    destruct getCurrent.
    destruct getWorkspace.
    destruct getStack.
    simpl.
    unfold focusUp'.
    destruct s.
    destruct getUp.
    simpl.
    repeat rewrite (app_nil_r).
    destruct getDown.
    apply (Permutation_refl).
    simpl.
    Focus 2.
    repeat rewrite (app_nil_r).
    simpl.
    apply (Permutation_trans (l' := a0 :: getFocus :: getUp ++ getDown)).
    constructor.
    constructor.
    apply (Permutation_cons_app).
    apply Permutation_refl.
    simpl.
    replace (hd getFocus (rev getDown ++ a0 :: nil)
      :: tl ((rev getDown ++ a0 :: nil) ++ getFocus :: nil))
      with
        (((hd getFocus (rev getDown ++ a0 :: nil)
      :: tl ((rev getDown ++ a0 :: nil))) ++ getFocus :: nil)).
    rewrite HdTlNotNil.
    apply Permutation_cons_app.
    rewrite app_nil_r.
    apply Permutation_cons_app.
    rewrite app_nil_r.
    apply Permutation_rev.
    destruct getDown.
      intros F; discriminate F.
      intros F.
      refine (app_cons_not_nil (rev (a1 :: getDown)) nil a0 _).
      symmetry; assumption.
    simpl. f_equal.
    destruct (rev getDown); reflexivity.
    simpl; constructor.
    apply PermutationFlatMap.
    apply PermutationFlatMap.
    apply Permutation_app.
    apply Permutation_map.
    destruct s; destruct getVisible; destruct getCurrent; destruct getWorkspace.
    constructor.
    apply Permutation_refl.
    destruct s; destruct getVisible; destruct getCurrent; destruct getWorkspace.
    apply Permutation_refl.
    apply Permutation_refl.   
Qed.    

Theorem prop_focusDown_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (iterate n (focusDown (i:=nat) (l:=l) (a:=a)(sd:=sd)) s).
  Proof.
    generalize s; induction n; auto; clear s.
    intros s IHs; simpl.
    cut (invariant (focusDown s)).
    intro H; apply (IHn _ H).
    unfold invariant in *; simpl in *.
    rewrite FlatMapApp.
    apply (NoDupPerm _ _ _ IHs).
    rewrite FlatMapApp in *.
    apply (Permutation_app).
    destruct s; destruct getCurrent; destruct getWorkspace; destruct getStack.
    simpl.
    unfold focusDown', focusUp'.
    destruct s.
    destruct getUp.
    simpl.
    repeat rewrite (app_nil_r).
    destruct getDown.
    apply (Permutation_refl).
    simpl.
    constructor.
    repeat rewrite (app_nil_r).
    simpl.
    apply (Permutation_trans (l' := a0 :: getFocus :: getUp ++ getDown)).
    constructor.
    destruct getDown.
    simpl.
    replace (hd getFocus (rev getUp ++ a0 :: nil)
      :: tl ((rev getUp ++ a0 :: nil) ++ getFocus :: nil))
      with
        (((hd getFocus (rev getUp ++ a0 :: nil)
      :: tl ((rev getUp ++ a0 :: nil))) ++ getFocus :: nil)).
    rewrite HdTlNotNil.
    rewrite app_nil_r.
    rewrite <- app_assoc.
    simpl.
    apply Permutation_cons_app.
    apply Permutation_cons_app.
    rewrite app_nil_r.
    apply Permutation_rev.
    destruct getUp.
      intros F; discriminate F.
      intros F.
      refine (app_cons_not_nil (rev (a1 :: getUp)) nil a0 _).
      symmetry; assumption.
    simpl. f_equal.
    destruct (rev getUp); reflexivity.
    simpl. 
    replace (a0 :: getFocus :: getUp ++ a1 :: getDown) with
      ((a0 :: getFocus :: getUp ++ a1 :: nil) ++ getDown).
    replace (a1 :: getFocus :: a0 :: getUp ++ getDown) with
      ((a1 :: getFocus :: a0 :: getUp) ++ getDown).
    apply Permutation_app_tail.
    replace (a1 :: getFocus :: a0 :: getUp) with
      ((a1 :: getFocus :: nil) ++ a0 :: getUp).
    apply Permutation_cons_app.
    simpl.
    apply Permutation_sym. 
    replace (getFocus :: getUp ++ a1 :: nil) with
      ((getFocus :: getUp) ++ (a1 :: nil)).
    apply Permutation_cons_app.
    rewrite app_nil_r.
    apply Permutation_refl.
    reflexivity.
    reflexivity.
    reflexivity.
    simpl.
    f_equal.
    f_equal.
    rewrite <- app_assoc.
    reflexivity.
    constructor.
    apply PermutationFlatMap, PermutationFlatMap. 
    apply Permutation_app. 
    apply Permutation_map.
    destruct s; destruct getVisible; destruct getCurrent; destruct getWorkspace.
    constructor.
    apply Permutation_refl.
    destruct s; destruct getVisible; destruct getCurrent; destruct getWorkspace.
    apply Permutation_refl.
    apply Permutation_refl.   
    Qed.
    

Theorem prop_focusMaster_I (l a sd : Set) (n : nat) (s : StackSet.stackSet nat l a sd) :
  invariant s -> invariant (iterate n (focusMaster (i:=nat) (l:=l) (a:=a)(sd:=sd)) s).
  Proof.
    generalize s; induction n; auto.
    intros st IHs; simpl.
    cut (invariant (focusMaster st)).
    intro H; apply (IHn _ H).
    unfold invariant in *; simpl in *.
  
    rewrite FlatMapApp in *.
    apply (NoDupPerm _ _ _ IHs).
    apply (Permutation_app).
    destruct st.
    destruct getCurrent.
    destruct getWorkspace.
    destruct getStack.
    simpl.
    destruct s0.
    destruct getUp.
    constructor.
    apply (Permutation_refl).
    Admitted.

Ltac destruct_stackset x := destruct x; destruct getCurrent; destruct getWorkspace; destruct getStack.

Theorem prop_mapLayoutId (s : stackSet i l a sd) :
  mapLayout (fun x => x) s = s.
  Proof.
    destruct s; destruct getCurrent; destruct getWorkspace.
    apply stackSet_eq; try reflexivity.
    induction getVisible.
    reflexivity.
    simpl in *.
    destruct a0.
    destruct getWorkspace.
    rewrite IHgetVisible.
    reflexivity.
    simpl.
    induction getHidden; try reflexivity.
    simpl; rewrite IHgetHidden; destruct a0; reflexivity.
  Qed.

Theorem prop_mapLayoutInverse (s : stackSet i nat a sd) :
  mapLayout pred (mapLayout S s) = s.
  Proof.
    destruct s.
    simpl.
    f_equal.
    destruct getCurrent.
    f_equal.
    destruct getWorkspace.
    reflexivity.
    induction getVisible.
    reflexivity.
    destruct a0.
    simpl.
    rewrite IHgetVisible.
    destruct getWorkspace.
    reflexivity.
    induction getHidden; try reflexivity.
    destruct a0; simpl; rewrite IHgetHidden; reflexivity.
  Qed.

Definition predTag (w : workspace nat l a) : workspace nat l a :=
  match w with
    | Workspace t l s => Workspace (pred t) l s
  end.

Definition succTag (w : workspace nat l a) : workspace nat l a :=
  match w with
    | Workspace t l s => Workspace (S t) l s
  end.

Theorem prop_mapWorkspaceInverse (s : stackSet nat l a sd) :
  mapWorkspace predTag (mapWorkspace succTag s) = s.
  Proof.
    destruct s; destruct getCurrent; destruct getWorkspace.
    unfold mapWorkspace.
    f_equal.
    induction getVisible; try reflexivity.
    simpl; destruct a0; rewrite IHgetVisible; unfold predTag; unfold succTag; simpl. 
    destruct getWorkspace. reflexivity.
    induction getHidden; try reflexivity.
    destruct a0.
    simpl. rewrite IHgetHidden.
    reflexivity.
  Qed.

Theorem prop_screens (s : stackSet i l a sd) :
  In (getCurrent s) (screens s).
  Proof.
    destruct s.
    destruct getCurrent; left; reflexivity.
  Qed.

Theorem prop_lookup_current (x : stackSet i l a sd) :
  lookupWorkspace (getScreen (getCurrent x)) x = Some (getTag (getWorkspace (getCurrent x))).
  Proof.
    destruct x.
    destruct getCurrent.
    simpl.
    unfold lookupWorkspace.
    simpl.
    destruct (beqsid getScreen getScreen) as [b T].
    destruct b.
    reflexivity.
    exfalso; apply T; reflexivity.
  Qed.

Theorem prop_lookup_visible (x : stackSet i l a sd) : 
  getVisible x <> nil ->
  (forall (x y : screen i l a sd), getScreen x = getScreen y -> x = y) -> (* the StackSet invariant *)
  match last (map (fun x => Some (getScreen x)) (getVisible x)) None with
    | None => True
    | Some sc =>
      In (lookupWorkspace sc x) (map (fun x => Some (getTag (getWorkspace x))) (getVisible x))
  end.
  Proof.
    remember (last (map (fun x => Some (getScreen x)) (getVisible x)) None).
    destruct y; try trivial.
    intros F; induction getVisible as [ | y ys].
    exfalso; apply F; reflexivity.
    induction ys as [ | z zs].
    left.
    destruct x.
    unfold lookupWorkspace.
    simpl.
    injection Heqy.
    intros Eq.
    rewrite Eq.
    destruct (beqsid (getScreen y) (getScreen getCurrent)) as [b B].
    destruct b; simpl in *.
    rewrite (H _ _ B).
    destruct getCurrent; reflexivity.
    Focus 2.
    intros H.
    right.
    apply IHys.
    assumption.
    discriminate.
    assumption.
    destruct y.
    simpl in *.
    destruct getCurrent.
    simpl in *.
  Admitted.


