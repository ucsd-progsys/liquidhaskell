Require Import List.

Set Implicit Arguments.

Fixpoint splitAt (a : Set) (k : nat) (xs : list a)
  : (list a * list a) :=
  match (k,xs) with
    | (O, xs) => (nil, xs)
    | (S m, nil) => (nil, nil)
    | (S m, y :: ys) => (y :: fst (splitAt m ys), snd (splitAt m ys))
  end.                          

Fixpoint zipWith3 
  (a b c d : Set) 
  (f : a -> b -> c -> d)
  (seens : list a) 
  (sids : list b) 
  (sds : list c)
  : list d
  := match (seens, sids, sds) with
       | (s :: seenTail, sid :: sidTail, sd :: sdTail) => 
           f s sid sd :: zipWith3 f seenTail sidTail sdTail
       | _ => nil
     end.

Definition maybe : forall a b, b -> (a -> b) -> option a -> b :=
  fun a b dflt f opt => match opt with
                          | None => dflt
                          | Some x => f x
                        end.

Definition option_bind {a b : Set} : 
  option a -> (a -> option b) -> option b := fun c f =>
    match c with
      | None => None
      | Some x => f x
    end.

Infix ">>=" := option_bind (at level 80, right associativity).

Fixpoint removeList (a : Set) (eqa : forall (x y : a), {x = y} + {x <> y}) (xs ys : list a) : list a :=
  match ys with
    | nil => xs
    | (z :: zs) => remove eqa z (removeList eqa xs zs)
  end.

Fixpoint iterate (a : Set) (n : nat) (f : a -> a) (x : a) : a :=
  match n with
    | O => x
    | S k => iterate k f (f x)
  end.

Fixpoint deleteBy (a : Set) (p : a -> a -> bool) (x : a) (xs : list a) : list a
  := match xs with
       | nil => nil
       | y :: ys => if p x y then ys else y :: deleteBy p x ys
    end.

Fixpoint applyN (a : Set) (n : nat) (x : a) (f : a -> a) : a :=
 match n with
   | 0 => x
   | S k => applyN k (f x) f
 end.

Fixpoint elemIndex (a : Set) (eqa : forall (x y : a), {x = y} + {x <> y}) (y : a) (xs : list a) : option nat 
  := match xs with
    | nil => None
    | x :: xs => match eqa x y with
                   | left _ => Some 0
                   | right _ => elemIndex eqa y xs >>= fun n => Some (S n)
                 end
     end.

Lemma appendNonNil (a : Set) (x : a) (xs ys : list a) : 
  ys ++ (x :: xs) <> nil.
  induction ys; discriminate.
  Qed.

Lemma revNil (A : Set) (xs : list A) : rev xs = nil -> xs = nil.
  destruct xs as [ | x xs ]; auto.
  intro IH; absurd (rev (x :: xs) = nil); auto.
  simpl; apply appendNonNil.
  Qed.


Lemma revStep (A : Set) (xs : list A) (x : A) : rev xs ++ x :: nil = rev (x :: xs).
  reflexivity.
  Qed.