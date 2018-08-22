Add LoadPath "..".
Require Import ZArith List Orders POrderedType.
Require Import veristar.tactics.

(** Module Ident:
the type of identifiers *)

Module Ident : UsualOrderedType.
  Parameter t: Type.
  Definition eq := @Logic.eq t.
  Definition eq_equiv := @eq_equivalence t.
  Parameter lt : t -> t -> Prop.
  Parameter lt_strorder : StrictOrder lt.
  Parameter lt_compat : Proper (eq==>eq==>iff) lt.
  Parameter compare : forall x y : t, comparison.
  Axiom compare_spec: forall s s' : t, CompSpec eq lt s s' (compare s s').
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
End Ident.

(* Version 1: Use this version if you want proper abstraction
 *)

Parameter minid : Ident.t.
Parameter id2pos: Ident.t -> positive.
Parameter pos2id: positive -> Ident.t.
Axiom pos2id_inj: forall x y, pos2id x = pos2id y -> x = y.
Axiom minid_eq: id2pos minid = 1%positive.
Axiom Ilt_morphism: forall x y, Ident.lt x y -> Plt (id2pos x) (id2pos y).
Parameter another_id: Ident.t -> Ident.t.
(* Note: usually "Ident.lt x (another_var x)", but not always; if you
   are writing an algorithm, make sure by doing the comparison! *)

(* Note that there are NO AXIOMS about the following operators!
 *)

Parameter Z2id: Z -> Ident.t.
Parameter add_id: Ident.t -> Ident.t -> Ident.t.
Parameter mult_id: Ident.t -> Ident.t -> Ident.t.
(*
(*
(* Version 2:  This version is what SHOULD be usable if
   if you want to "Compute" in Coq, but it suffers from bug #2608
   in Coq 8.3pl2.   Until this is fixed, use version 3. *)

Module Ident <: UsualOrderedType := Positive_as_OT.
  Parameter minid: Ident.t.
  Parameter id2pos: Ident.t -> positive.
  Axiom minid_eq: id2pos minid = 1%positive.
  Axiom Ilt_morphism: forall x y, Ident.lt x y -> Plt (id2pos x) (id2pos y).
  Parameter another_id: Ident.t -> Ident.t.
*)

(* Version 3: USE THIS IF YOU WANT TO "Compute" in Coq
    until bug #2608 is fixed.
 *)

Module Ident <: OrderedTypeFull
  with Definition t := positive
  with Definition lt := Plt
  with Definition compare := fun x y => Pcompare x y Eq
  with Definition le := Ple.
 Definition t := positive.
 Definition eq : t -> t -> Prop := @Logic.eq positive.
 Definition eq_equiv: Equivalence eq := @eq_equivalence t. (*apply eq_equivalence. Qed.*)
 Definition lt : t -> t -> Prop := Plt.
 Lemma lt_strorder:  StrictOrder lt. apply Positive_as_OT.lt_strorder. Qed.
 Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  apply Positive_as_OT.lt_compat. Qed.
 Definition compare: t -> t -> comparison := fun x y => Pcompare x y Eq.
 Lemma compare_spec: forall p q : t, CompSpec Logic.eq lt p q (compare p q).
   apply Positive_as_OT.compare_spec. Qed.
 Definition eq_dec: forall x y, {eq x y}+{~eq x y} := positive_eq_dec.
 Definition le : t -> t -> Prop := Ple.
 Lemma le_lteq : forall p q : t, le p q <-> lt p q \/ p = q.
   apply Positive_as_OT.le_lteq. Qed.
End Ident.

Definition minid : Ident.t := xH.
Definition id2pos: Ident.t -> positive := fun x => x.
Lemma minid_eq: id2pos minid = 1%positive.
Proof. reflexivity. Qed.
Lemma Ilt_morphism: forall x y, Ident.lt x y -> Plt (id2pos x) (id2pos y).
Proof. auto. Qed.
Definition another_var: Ident.t -> Ident.t := Psucc.
(* Note: usually "Ident.lt x (another_var x)", but not always; if you
   are writing an algorithm, make sure by doing the comparison! *)

Definition Z2id (z : Z) : Ident.t :=
  match z with
    | Z0 => 1%positive
    | Zpos p => Pplus p 1%positive
    | Zneg _ => (* not quite right, but usable for debugging *) 1%positive
  end.

Definition add_id := Pplus.
*)
(** Lemmas and tactics:
 *)

Lemma minid_min x : Ident.lt x minid -> False.
tapp Ilt_morphism; rewrite minid_eq; case (id2pos x); tinv0.
Qed.

Ltac id_compare x y :=
  destruct (CompSpec2Type (Ident.compare_spec x y)).

Ltac id_comp x y H1 H2 H3 :=
  destruct (CompSpec2Type (Ident.compare_spec x y)) as [H1|H2|H3].

Lemma id2pos_inj x y : id2pos x = id2pos y -> x=y.
introv H; id_comp x y H1 H2 H3; [auto|elimtype False; gen H2|gen H3];
done (tapp Ilt_morphism; rewrite H; tapp Pos.lt_irrefl).
Qed.

Lemma Ilt_irrefl : forall {x}, ~ Ident.lt x x.
Proof. done (case Ident.lt_strorder). Qed.

Lemma Ilt_trans : forall {x y z}, Ident.lt x y -> Ident.lt y z -> Ident.lt x z.
Proof. done (case Ident.lt_strorder). Qed.

Definition Ile x y := Ident.lt x y \/ Ident.eq x y.

Lemma Ile_refl x : Ile x x.
Proof. done (introv; right). Qed.

Hint Resolve Ile_refl.

Lemma Ilt_Zpos i j :
  Ident.lt i j <-> Z.lt (Zpos (id2pos i)) ((Zpos (id2pos j))).
Proof.
split; [tapp Ilt_morphism|tinv H].
generalize (Pcompare_spec (id2pos i) (id2pos j)); rewrite H; tinv H1.
id_comp i j H2 H3 H4; auto; subst.
contradiction (Pos.lt_irrefl _ H1).
gen H4; tapp Ilt_morphism; introv H4.
contradiction (Pos.lt_irrefl _ (Plt_trans _ _ _ H1 H4)).
Qed.

Lemma nat_of_P_id2pos_le x y :
  Ile x y -> nat_of_P (id2pos x) <= nat_of_P (id2pos y).
Proof.
cases (Ident.eq_dec x y) as E; subst; auto; cases E.
introv H1; inverts H1 as H1; [|inverts H1; auto].
gen H1; tapp Ilt_morphism; unfold Plt.
done(rewrite nat_of_P_compare_morphism, <-nat_compare_lt; omega).
Qed.
