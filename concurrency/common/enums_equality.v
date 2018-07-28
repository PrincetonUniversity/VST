From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(* given n <= m, returns the list [n-1,...,0] with proofs of < m *)
    Program Fixpoint enum_from n m (pr : le n m) : list (ordinal m) :=
      match n with
        O => nil
      | S n => (@Ordinal m n ltac:(rewrite <-Heq_n in *; apply (introT leP pr)))
                :: @enum_from n m ltac:(rewrite <-Heq_n in *; apply Le.le_Sn_le, pr)
      end.

    Definition enum n := Coq.Lists.List.rev (@enum_from n n (Le.le_refl n)).
Fixpoint countdown (n: nat) := match n with O => nil | S n' => n' :: countdown n' end.

Lemma countdown_rev_iota:  forall n, countdown n = List.rev (iota 0 n).
Proof.
intros.
rewrite <- (List.rev_involutive (countdown n)).
f_equal.
induction n; simpl; auto.
rewrite IHn; clear IHn.
replace n with (n+0) at 2 by apply PeanoNat.Nat.add_0_r.
set (k:=0).
clearbody k.
revert k; induction n; intros; simpl.
f_equal.
f_equal.
rewrite <- IHn.
f_equal. f_equal.
rewrite addSn.
rewrite addnS.
auto.
Qed.

Lemma val_enum: forall n: nat,  [seq val i | i <- enum n] = iota 0 n.
Proof.
intros.
unfold enum.
transitivity (List.map [eta val] (List.rev (enum_from (PeanoNat.Nat.le_refl n)))).
*
induction (List.rev (enum_from (PeanoNat.Nat.le_refl n))).
reflexivity.
simpl.
f_equal; auto.
*
rewrite List.map_rev.
rewrite <- (List.rev_involutive (iota 0 n)).
f_equal.
transitivity (countdown n).
+
simpl.
assert (forall m (P: le n m), 
@eq (list nat)
  (@List.map (ordinal m) nat (fun x : ordinal m => @nat_of_ord m x) (@enum_from n m P))
  (countdown n)); [ | auto].
intro.
induction n; intro; simpl.
auto.
f_equal.
auto.
apply countdown_rev_iota.
Qed.


Lemma ord_enum_enum:
  forall n : nat, @eq (list (ordinal n)) (ord_enum n) (enum n).
Proof.
intros.
assert (map val (ord_enum n) = map val (enum n)).
rewrite val_ord_enum.
rewrite val_enum.
auto.
apply inj_map in H; auto.
apply val_inj.
Qed.
