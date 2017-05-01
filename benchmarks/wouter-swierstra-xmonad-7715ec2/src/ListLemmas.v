Require Import Aux List.
Require Import Arith.
Require Import Sorting.Permutation.

Lemma NoDupSingle : forall (a : Type) (x : a),
  NoDup (x :: nil).
Proof. constructor; auto; constructor. Qed.

Lemma NoDupCons : forall (a : Type) (xs : list a) (x : a),
  NoDup (x :: xs) -> NoDup xs.
Proof.
  intros a xs x H; induction xs.
  constructor. inversion H; assumption.
Qed.    

Lemma InApp : forall (a : Type) (x : a) (xs ys : list a),
  In x (xs ++ x :: ys).
Proof.
  intros a x xs.
  induction xs.
  simpl; constructor; reflexivity.
  intros ys. right. apply IHxs.
Qed.

Lemma InApp' : forall (a : Type) (x y : a) (xs ys : list a),
  In x (xs ++ ys) -> In x (xs ++ y :: ys).
Proof.
  intros a x y xs ys H.
  generalize dependent ys.
  induction xs.
  right; assumption.
  intros ys H. destruct H as [H | H].
  rewrite H; constructor; reflexivity.
  right; apply IHxs; assumption.
Qed.

Lemma InSuper : forall (a : Type) (x : a) (xs ys : list a),
  In x xs -> In x (xs ++ ys).
Proof.
  intros a x xs ys H.
  generalize dependent ys.
  induction xs as [ | z zs].
  inversion H.
  inversion H.
  constructor; exact H0.
  destruct H as [Eq | Later].
  constructor; exact Eq.
  right. apply (IHzs); auto.
Qed.

Lemma InComm : forall (a : Type) (x : a) (xs ys : list a),
  In x (xs ++ ys) -> In x (ys ++ xs).
Proof.
  intros a x xs ys.
  generalize dependent ys.
  induction xs as [ | z zs].
  intros ys H. simpl;rewrite app_nil_r; intros; assumption.
  intros ys H. destruct H as [H | H].
  rewrite H.
  apply InApp.
  apply InApp'.
  apply IHzs.
  assumption.
Qed.

Lemma NotInComm : forall (a : Type) (x : a) (xs ys : list a),
  ~In x (xs ++ ys) -> ~In x (ys ++ xs).
Proof.
  intros a x xs ys F H.
  induction ys as [ | y ys].
  induction xs as [ | z zs]; auto.
  rewrite app_nil_r in F; simpl in *; contradiction.
  destruct H as [H | H].
  rewrite H in *; apply F, InApp; assumption.
  apply F, InApp', InComm; auto.
Qed.

Lemma NoDupAppAss : forall (a : Type) (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup (ys ++ xs).
Proof.
  intros a xs ys H.
  generalize dependent xs.
  induction ys.
  intros xs H.
  rewrite app_nil_r in H; assumption.
  constructor; 
    [ apply NotInComm, NoDup_remove_2; assumption 
    | apply IHys; apply NoDup_remove_1 in H; assumption].
Qed.

Lemma NoDupPerm : forall (a : Type) (xs ys : list a),
  NoDup xs -> Permutation xs ys -> NoDup ys.
Proof.
  intros a xs ys H1 H2.
  induction H2.
  (* nil *)
  constructor.
  (* skip *)
  constructor. 
  intro F; apply (NoDup_remove_2 nil l x); auto.
  apply (Permutation_in (l:=l'));
    [ apply (Permutation_sym) | ]; auto.
  apply IHPermutation.
  inversion H1; auto.
  (* swap *)
  constructor.
  apply (NoDup_remove_2 (y :: nil) l x); auto.
  apply (NoDup_remove_1 (y :: nil) l x); auto.
  (* trans *)
  apply IHPermutation2,IHPermutation1; auto.
Qed.

Lemma PermAppL : forall (a : Type) (xs ys zs : list a),
  Permutation ys zs -> Permutation (xs ++ ys) (xs ++ zs).
Proof.
  intros a xs ys zs H1.
  generalize dependent ys.
  generalize dependent zs.
  induction xs; [auto | simpl; auto].
Qed.

Lemma PermAppR : forall (a : Type) (xs ys zs : list a),
  Permutation ys zs -> Permutation (ys ++ xs) (zs ++ xs).
Proof.
  intros a xs ys zs H.
  induction xs as [| x xs IHxs].
  do 2 rewrite -> app_nil_r; apply H.
  apply Permutation_add_inside. apply H.
  apply Permutation_refl.  
Qed.

Lemma NoDupConsSwap : forall (a : Type) (xs : list a) (x y : a),
  NoDup (x :: y :: xs) -> NoDup (y :: x :: xs).
Proof.
  intros a xs x y H.
  apply (NoDupPerm _ (x :: y :: xs) (y :: x :: xs)).
  apply H. constructor.
Qed.

Lemma NoDupAppConsR : forall (a : Type) (xs ys : list a) (x : a),
  NoDup (xs ++ x :: ys) -> NoDup (xs ++ ys).
Proof.
  intros a xs ys x H1.
  apply NoDupAppAss.
  apply (NoDupCons _ (ys ++ xs) x).
  rewrite -> app_comm_cons.
  apply NoDupAppAss.
  apply H1.
Qed.

Lemma NoDupAppR : forall (a : Type) (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup ys.
Proof.
  intros a xs ys H1.
  generalize dependent ys.
  induction xs as [| x xs IHxs].
  intros ys H1.
  destruct ys as [| y ys].
  apply H1.
  apply H1.
  intros ys H1.
  simpl in H1.
  apply IHxs.
  apply NoDupCons in H1; apply H1.
Qed.

Lemma NoDupAppL : forall (a : Type) (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup xs.
Proof.
  intros a xs ys H.
  apply NoDupAppAss in H.
  apply (NoDupAppR _ ys xs).
  apply H.
Qed.

Lemma FlatMapApp : forall (a b : Type) (f : a -> list b) (xs ys : list a),
  flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof.
  intros a b f xs.
  induction xs as [| x xs IHxs]. reflexivity.
  intros ys. simpl. rewrite -> IHxs.
  rewrite -> app_ass. reflexivity.
Qed.

Lemma NoDupFlatMapCons : forall (a b : Type) (x : a) (xs : list a) (f : a -> list b),
  NoDup (flat_map f (x :: xs)) -> NoDup (flat_map f xs).
Proof.
  intros a b x xs f H.
  destruct xs as [| y ys ]. constructor.
  apply (NoDupAppR _ (f x) (f y ++ flat_map f ys)).
  assumption.
Qed.

Lemma PermutationFlatMap : forall (a b : Type) (f : a -> list b) (xs ys : list a),
  Permutation xs ys -> Permutation (flat_map f xs) (flat_map f ys).
Proof.
  intros a b f xs ys H.
  induction H.
  constructor.
  simpl. apply Permutation_app_head. apply IHPermutation.
  simpl. do 2 rewrite -> app_assoc.
  apply Permutation_app_tail. apply Permutation_app_comm.
  generalize IHPermutation2.
  generalize IHPermutation1.
  apply Permutation_trans.
Qed.

Lemma NoDupFlatMap : forall (a b : Type) (xs ys : list a) (f : a -> list b),
  NoDup (flat_map f xs) -> Permutation xs ys -> NoDup (flat_map f ys).
Proof.
  intros a b xs ys f H1 H2.
  destruct ys as [| y ys ].
  constructor.
  apply (NoDupPerm _ _ _ H1).
  apply PermutationFlatMap.
  apply H2.
Qed.

Lemma NoDupFlatMapApp : forall (a b : Type) (xs ys : list a) (f : a -> list b),
  NoDup (flat_map f (xs ++ ys)) -> NoDup (flat_map f xs ++ flat_map f ys).
Proof.
  intros a b xs ys f H.
  rewrite <- FlatMapApp.
  apply H.
Qed.

Lemma NoDupAppFlatMap : forall (a b : Type) (xs ys : list a) (f : a -> list b),
  NoDup (flat_map f xs ++ flat_map f ys) -> NoDup (flat_map f (xs ++ ys)).
Proof.
  intros a b xs ys f H.
  rewrite -> FlatMapApp.
  apply H.
Qed.

Lemma NotInCons : forall (a : Type) (x y : a) (ys : list a),
  ~ In x (y :: ys) -> ~ In x ys.
Proof.
  unfold not. 
  intros a x y ys H1 H2.
  apply H1. apply in_cons. apply H2.
Qed.

Lemma NoDupNotIn : forall (a : Type) (x : a) (xs : list a),
  NoDup (x :: xs) -> ~ In x xs.
Proof.
  intros a x xs H1.
  induction xs as [| x' xs IHxs].
  apply in_nil.
  unfold not in *.
  intros H2.
  apply IHxs.
  apply (NoDupCons _ (x :: xs) x').
  apply NoDupConsSwap; apply H1.
Admitted.

Lemma NotInApp : forall (a : Type) (x : a) (xs ys : list a),
  ~In x xs -> ~In x ys -> ~In x (xs ++ ys).
Proof.
  unfold not.
  intros a x xs ys H1 H2 H3.
  induction xs as [| x' xs IHxs ].
  apply H2; apply H3.
  induction ys as [| y ys IHys].
  apply H1. rewrite -> app_nil_r in H3. apply H3.
  apply IHxs.
  apply (NotInCons _ x x' xs). unfold not. apply H1.
Admitted.

Lemma NoDupFlatMapL : forall (a b : Type) (f : a -> list b) (xs : list a),
  NoDup (flat_map f xs) -> NoDup xs.
Proof.
  intros a b f xs H.
  induction xs as [| x xs IHxs ].
  constructor.
  constructor.
Admitted.

Lemma HdTlNotNil (a : Type) (x : a) (xs : list a) : 
  xs <> nil -> hd x xs :: (tl xs) = xs.
Proof.
  intros F; induction xs.
    exfalso; apply F; reflexivity.
    reflexivity.
  Qed.
