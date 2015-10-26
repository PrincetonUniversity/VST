Require Import msl.msl_direct.

Definition heap : Type := fpm nat nat.
Instance Join_heap: Join heap := Join_fpm (Join_discrete _).

Instance Perm_heap: Perm_alg heap := Perm_fpm _ (Perm_discrete nat).

Definition mapsto  (x y: nat) : pred heap :=
 fun h => forall z, if eq_dec z x then lookup_fpm h z = Some y else lookup_fpm h z = None.

Inductive lis' : nat -> pred heap :=
| lis_nil : forall p w, (!!(p=0) && emp)%pred w -> lis' p w
| lis_cons: forall p w, (!!(p<>0) && EX r:nat, mapsto p r * lis' r)%pred w -> lis' p w.

Lemma lis'_fold_unfold:
    forall p, lis' p =  (!!(p=0) && emp || !!(p<>0) && EX r:nat, mapsto p r * lis' r)%pred.
Proof.
intros.
apply pred_ext; intros w ?; (inv H; [left | right]; auto).
Qed.

Definition lisfun (Q: nat -> pred heap) (p: nat)  : pred heap:=
  (!!(p=0) && emp || !!(p<>0) && EX r:nat, mapsto p r * Q r)%pred.

Lemma covariant_lisfun: covariant lisfun.
Proof.
apply covariant_orp.
apply covariant_const.
apply covariant_andp.
apply covariant_const.
apply covariant_exp; intro.
apply covariant_sepcon.
apply covariant_const.
apply covariant_const'.
Qed.

Definition lis : nat -> pred heap := corec lisfun.

Lemma lis_fold_unfold:
    forall p, lis p =  (!!(p=0) && emp || !!(p<>0) && EX r:nat, mapsto p r * lis r)%pred.
Proof.
intros.
unfold lis at 1.
rewrite corec_fold_unfold.
reflexivity.
apply covariant_lisfun.
Qed.

