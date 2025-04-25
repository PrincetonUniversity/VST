(* This file illustrates two approaches to C verification,
  described in Section III of this paper:

 Modular Verification for Computer Security,
 by Andrew W. Appel, in IEEE Computer Security Foundations conference (CSF'16),
 June 2016.
 http://www.cs.princeton.edu/~appel/papers/modsec.pdf
*)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.min.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
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
  PRE [ tptr tint , tint ]
    PROP  (1 <= n <= Int.max_signed; Forall repable_signed al)
    PARAMS (a; Vint (Int.repr n))
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
assert_PROP (Zlength al = n) by (entailer!; list_solve).
forward.  (* min = a[0]; *)
forward_for_simple_bound n
  (EX i:Z,
    PROP()
    LOCAL(temp _min (Vint (Int.repr (fold_right Z.min (Znth 0 al) (sublist 0 i al))));
          temp _a a;
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)).
* (* Prove that the precondition implies the loop invariant *)
  entailer!!.
* (* Prove that the loop body preserves the loop invariant *)
 forward. (* j = a[i]; *)
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
 forward_if.
 +
 forward. (* min = j; *)
 entailer!!.
 rewrite Z.min_r; auto; lia.
 +
 forward. (* skip; *)
 entailer!!.
 rewrite Z.min_l; auto; lia.
* (* After the loop *)
 forward. (* return *)
 entailer!!.
 autorewrite with sublist.
 destruct al; simpl; auto.
Qed.

(* Demonstration of the same theorem, but using
    forward_for  instead of forward_for_simple_bound *)
Lemma body_min': semax_body Vprog Gprog f_minimum minimum_spec.
Proof.
start_function.
assert_PROP (Zlength al = n) by (entailer!; list_solve).
revert POSTCONDITION;
 replace (hd 0 al) with (Znth 0 al) by (destruct al; reflexivity);
 intro POSTCONDITION.
forward.  (* min = a[0]; *)
pose (Inv d (f: Z->Prop) (i: Z) :=
    PROP(0 <= i <= n; f i)
    LOCAL(temp _min (Vint (Int.repr (fold_right Z.min (Znth 0 al) (sublist 0 (i+d) al))));
          temp _a a; temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)).
forward_for (Inv 0 (fun _ => True%type)) continue: (Inv 1 (Z.gt n)).
*
forward.
Exists 0. unfold Inv; entailer!!.
*
entailer!!.
*
rename a0 into i.
 forward. (* j = a[i]; *)
 assert (repable_signed (Znth i al))
     by (apply Forall_Znth; auto; lia).
 assert (repable_signed (fold_right Z.min (Znth 0 al) (sublist 0 i al)))
   by (apply Forall_fold_min;
          [apply Forall_Znth; auto; lia
          |apply Forall_sublist; auto]).
 autorewrite with sublist.
 apply semax_post_flipped' with (Inv 1 (Z.gt n) i).
 unfold Inv.
 rewrite (sublist_split 0 i (i+1)) by lia.
 rewrite (sublist_one i (i+1) al) by lia.
 rewrite fold_min_another.
 forward_if.
 +
 forward. (* min = j; *)
 entailer!. rewrite Z.min_r; auto; lia.
 +
 forward. (* skip; *)
 entailer!!. rewrite Z.min_l; auto; lia.
 +
Exists i. apply ENTAIL_refl.
*
 rename a0 into i.
 forward.
 Exists (i+1).
 entailer!!.
*
 autorewrite with sublist.
 forward.
Qed.

Definition minimum_spec2 :=
 DECLARE _minimum
  WITH a: val, n: Z, al: list Z
  PRE [ tptr tint , tint ]
    PROP  (1 <= n <= Int.max_signed; Forall repable_signed al)
    PARAMS (a; Vint (Int.repr n))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  POST [ tint ]
   EX j: Z,
    PROP (In j al; Forall (fun x => j<=x) al)
    RETURN (Vint (Int.repr j))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a).


(* Second approach from "Modular Verification for Computer Security",
  proved using forward_for_simple_bound *)
Lemma body_min2: semax_body Vprog Gprog f_minimum minimum_spec2.
Proof.
start_function.
assert_PROP (Zlength al = n) by (entailer!; list_solve).
forward.  (* min = a[0]; *)
forward_for_simple_bound n
  (EX i:Z, EX j:Z,
    PROP(
         In j (sublist 0 (Z.max 1 i) al);
         Forall (Z.le j) (sublist 0 i al))
    LOCAL(
          temp _min (Vint (Int.repr j));
          temp _a a;
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)).
* (* Show that the precondition entails the loop invariant *)
Exists (Znth 0 al).
autorewrite with sublist.
entailer!!.
rewrite sublist_one by lia.
constructor; auto.
* (* Show that the loop body preserves the loop invariant *)
Intros.
forward. (* j = a[i]; *)
assert (repable_signed (Znth i al))
   by (apply Forall_Znth; auto; lia).
assert (repable_signed j)
   by (eapply Forall_forall; [ | eassumption]; apply Forall_sublist; auto).
autorewrite with sublist.
forward_if.
 + (* Then clause *)
 forward. (* min = j; *)
 Exists (Znth i al).
 entailer!!.
 rewrite Z.max_r by lia.
 rewrite (sublist_split 0 i (i+1)) by lia.
 rewrite (sublist_one i (i+1) al) by lia.
 split.
 apply in_app; right; constructor; auto.
 apply Forall_app; split.
 eapply Forall_impl; try apply H4.
 intros; lia.
 constructor; auto. lia.
 + (* Else clause *)
 forward. (* skip; *)
 Exists j.
 entailer!!.
 rewrite Z.max_r by lia.
 split.
 destruct (zlt 1 i).
 rewrite Z.max_r in H3 by lia.
 rewrite (sublist_split 0 i (i+1)) by lia.
 apply in_app; left; auto.
 rewrite Z.max_l in H3 by lia.
 rewrite (sublist_split 0 1 (i+1)) by lia.
 apply in_app; left; auto.
 rewrite (sublist_split 0 i (i+1)) by lia.
 apply Forall_app. split; auto.
 rewrite sublist_one by lia.
 repeat constructor. lia.
* (* After the loop *)
 Intros x.
 autorewrite with sublist in *.
 forward. (* return *)
 Exists x; entailer!.
Qed.
