Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint All T P (l : seq T) :=
  match l with
    | nil => True
    | a :: l' => [/\ P a & All P l']
  end.

Fixpoint All2 T (P : T -> T -> Prop) (l : seq T) :=
  if l is [:: a & l'] then [/\ All (P a) l' & All2 P l']
  else True.

Lemma All2_cons T P (a : T) (l : seq T) :
  All2 P [:: a & l] <-> [/\ All (P a) l & All2 P l].
Proof. by split=> /= => [][]A B; split. Qed.

Lemma All_sub T (P P' : T -> Prop) l :
  All P l -> (forall a, P a -> P' a) -> All P' l.
Proof.
move=> A B; move: A; elim: l=> // a' l' IH /= []C D; split.
by apply: (B _ C).
by apply: IH.
Qed.

Lemma All2_sub T (P P' : T -> T -> Prop) l :
  All2 P l -> (forall a a', P a a' -> P' a a') -> All2 P' l.
Proof.
move=> A B; move: A; elim: l=> // a l' IH /= []C D; split.
by apply: (All_sub C); apply: B.
by apply: (IH D).
Qed.

Lemma All2C T (P : T -> T -> Prop) a b l :
  All2 P (a :: b :: l) -> 
  (forall a b, P a b -> P b a) -> 
  All2 P (b :: a :: l).
Proof.
move=> /= => [][][]A B []C D HC; split=> //.
by split=> //; apply: (HC _ _ A).
Qed.

Lemma All_comp T U (P : T -> Prop) (f : U -> T) l :
  All (P \o f) l <-> All P (map f l).
Proof.
elim: l=> // a' l' IH; split.
by move=> /= []A B; split=> //; rewrite -IH.
by move=> /= []A B; split=> //; rewrite IH.
Qed.

Lemma All_comp2 T U (P : T -> Prop) (f : U -> T) l :
  (All P \o map f) l <-> All P (map f l).
Proof. by []. Qed.

Lemma All_comp3 T U (P : T -> Prop) (f : U -> T) l :
  All (fun a => P (f a)) l <-> All P (map f l).
Proof. 
elim: l=> // a' l' IH; split=> //= [][]A B; split=> //.
by rewrite -IH.
by rewrite IH.
Qed.

Lemma All2_comp T U (P : T -> T -> Prop) (f : U -> T) l :
  All2 (fun a b => P (f a) (f b)) l <-> (All2 P \o map f) l.
Proof.
elim: l=> // a l' IH; split.
move=> /= []A B; split; first by rewrite -All_comp. 
by case: IH; move/(_ B)=> C _; apply: C.
move=> /= []A B; split; first by rewrite All_comp.
by case: IH=> _; move/(_ B).
Qed.

Lemma All2_comp2 T U (P : T -> T -> Prop) (f : U -> T) l :
  (All2 P \o map f) l <-> All2 P (map f l).
Proof. by []. Qed.

Lemma All2_comp3 T U (P : T -> T -> Prop) (f : U -> T) l :
  All2 (fun a b => P (f a) (f b)) l <-> 
  All2 P (map f l).
Proof. by rewrite All2_comp All2_comp2. Qed.



