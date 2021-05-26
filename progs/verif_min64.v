(* This file tests:
    forward_for_simple_bound on 64-bit long integers,
    forward load with 64-bit integer array subscript, and
    forward store with 64-bit integer array subscript.
*)

Require Import VST.floyd.proofauto.
Require Import VST.progs.min64.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z.


Theorem fold_min_general:
  forall (al: list Z)(i: Z),
  In i (al) ->
  forall x, List.fold_right Z.min x al <= i.
Proof.
induction al; intros.
inversion H.
destruct H.
subst a.
simpl.
apply Z.le_min_l.
simpl. rewrite Z.le_min_r.
apply IHal.
apply H.
Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
  In i (al) ->
  List.fold_right Z.min (hd 0 al) al <= i.
Proof.
intros.
apply fold_min_general.
apply H.
Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
 intros.
 induction H0.
 simpl. auto.
 simpl.
 unfold Z.min at 1.
 destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y,
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
 intros.
 revert x; induction al; simpl; intros.
 apply Z.min_comm.
 rewrite <- Z.min_assoc. f_equal.
 apply IHal.
Qed.

Lemma is_int_I32_Znth_map_Vint:
 forall i s al,
  0 <= i < Zlength al ->
  is_int I32 s (Znth i (map Vint al)).
Proof.
intros. rewrite Znth_map; auto.
Qed.
#[export] Hint Extern 3 (is_int I32 _ (Znth _ (map Vint _))) =>
  (apply  is_int_I32_Znth_map_Vint; rewrite ?Zlength_map; lia) : core.

Definition minimum_spec :=
 DECLARE _minimum
  WITH a: val, n: Z, al: list Z
  PRE [ tptr tint , tlong ]
    PROP  (1 <= n <= Int64.max_signed; Forall repable_signed al)
    PARAMS (a; Vlong (Int64.repr n))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (fold_right Z.min (hd 0 al) al)))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a).

Definition Gprog : funspecs :=
      ltac:(with_library prog [minimum_spec]).

(* First approach from "Modular Verification for Computer Security",
  proved using forward_for_simple_bound *)

Lemma body_min: semax_body Vprog Gprog f_minimum minimum_spec.
Proof.
start_function.
assert_PROP (Zlength al = n). {
  entailer!. autorewrite with sublist; auto.
}
forward.  (* min = a[0]; *)
forward_for_simple_bound n
  (EX i:Z,
    PROP()
    LOCAL(temp _min (Vint (Int.repr (fold_right Z.min (Znth 0 al) (sublist 0 i al))));
          temp _a a;
          temp _n (Vlong (Int64.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)).
* (* Prove that the precondition implies the loop invariant *)
  entailer!.
* (* Prove that the loop body preserves the loop invariant *)
 forward. (* j = a[i]; *)
 forward. (* a[i] = j; *)
 assert (repable_signed (Znth i al))
     by (apply Forall_Znth; auto; lia).
 assert (repable_signed (fold_right Z.min (Znth 0 al) (sublist 0 i al)))
   by (apply Forall_fold_min;
          [apply Forall_Znth; auto; lia
          |apply Forall_sublist; auto]).
 autorewrite with sublist.
 subst POSTCONDITION; unfold abbreviate.
 rewrite (sublist_split 0 i (i+1)) by lia.
 rewrite (sublist_one i (i+1) al) by lia.
 rewrite fold_min_another.
 replace  (upd_Znth i (map Vint (map Int.repr al)) (Vint (Int.repr (Znth i al))))
  with (map Vint (map Int.repr al))
  by list_solve.
 forward_if.
 +
 forward. (* min = j; *)
 entailer!.
 rewrite Z.min_r; auto; lia.
 +
 forward. (* skip; *)
 entailer!.
 rewrite Z.min_l; auto; lia.
* (* After the loop *)
 forward. (* return *)
 entailer!.
 autorewrite with sublist.
 destruct al; simpl; auto.
Qed.
