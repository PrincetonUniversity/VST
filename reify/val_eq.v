Require Import floyd.proofauto.
Require Import msl.Axioms.
Require Import MirrorShard.Expr.

Definition beq_int (i1 i2 : int) : bool :=
Zeq_bool (Int.intval i1) (Int.intval i2).

Lemma beq_int_true : forall a b, beq_int a b = true -> a = b. 
Proof.
intros.
destruct a, b.
unfold beq_int in *.
simpl in H. 
apply Zeq_bool_eq in H. subst.
replace intrange with intrange0.
auto.
apply proof_irr.
Qed.

Definition beq_long (i1 i2 : int64) : bool :=
Zeq_bool (Int64.intval i1) (Int64.intval i2).

Lemma beq_long_true : forall a b, beq_long a b = true -> a = b. 
Proof.
intros.
destruct a, b.
unfold beq_long in *.
simpl in H. 
apply Zeq_bool_eq in H. subst.
replace intrange with intrange0.
auto.
apply proof_irr.
Qed.


Definition beq_val a b : bool :=
match a,b with
| Vundef, Vundef => true
| Vint i1, Vint i2 => beq_int i1 i2
| Vlong i1, Vlong i2 => beq_long i1 i2
| Vfloat f1, Vfloat f2 => false (* for now*)
| Vptr b1 o1, Vptr b2 o2 => andb (Pos.eqb b1 b2) (beq_int o1 o2)
| _, _ => false
end.  

Lemma beq_val_true : forall a b, beq_val a b = true -> a = b.
Proof.
intros.
destruct a, b; simpl in *; try solve [inv H]; try reflexivity.
apply beq_int_true in H; subst; auto.
apply beq_long_true in H; subst; auto.
rewrite andb_true_iff in H. destruct H.
apply Peqb_true_eq in H; subst; auto.
apply beq_int_true in H0; subst; auto.
Qed.

Definition uncurry_2 {A B C} (f : A -> B -> C) (a : (A * B)) :=
let (a, b) := a
in f a b.

Definition beq_list {A} (f: A -> A -> bool) (l1 : list A) (l2 : list A) :=
let zipped := combine l1 l2 in
let eq := map (uncurry_2 f) zipped in
andb (beq_nat (length l1) (length l2))
(fold_right andb true eq).

Lemma beq_list_true {A} {f: A -> A -> bool} (p : forall (a b: A), f a b = true -> a = b) :
forall l1 l2, beq_list f l1 l2 = true -> l1 = l2.
Proof.
intros.
unfold beq_list in H.
rewrite andb_true_iff in H.
destruct H.
generalize dependent l2.
induction l1, l2; intros; auto; inv H.
simpl in H0.
rewrite andb_true_iff in H0.
destruct H0.
apply p in H.
subst.
erewrite IHl1; auto.
Qed.

Definition list_eqb_type {T : Type} {f : T -> T -> bool} (p : forall a b, f a b = true -> a=b) : Expr.type. 
refine ({| Expr.Impl := list T
     ; Expr.Eqb := beq_list f
     ; Expr.Eqb_correct := beq_list_true p |}).
Defined.
