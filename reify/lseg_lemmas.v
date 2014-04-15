Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import sep.
Require Import functions.
Require Import progs.list_dt.
Import Expr.

Local Open Scope logic.
Import VericSepLogic_Kernel.
Local Notation "a ===> b" := (himp a b) (at level 60).

(* Might not need all of these? *)

(* From Navarro Perez (PLDI'11). *)
(* W1 *)
Lemma null_field_at_false : forall T sh id y,
                              field_at sh T id y nullval ===> inj False.
Proof.
  intros. sep_solve. entailer.
Qed.

Definition NP_W1 := null_field_at_false.

(* W2 *)
Lemma lseg_null_null : forall T ll ls sh y contents,
                         @lseg T ll ls sh contents nullval y ===> inj (y = nullval).
Proof.
  intros. sep_solve.
  rewrite lseg_unroll; entailer.
  apply orp_left; entailer.
  unfold lseg_cons; entailer.
Qed.

Definition NP_W2 := lseg_null_null.

(* W3 *)
(* essentially just a restatement of field_at_conflict *)
Lemma field_at_conflict' : forall T sh id x y z,
                             star (field_at sh T id y x) (field_at sh T id z x) ===> inj False.
Proof.
  intros. sep_solve.
  entailer.
  apply field_at_conflict.
Qed.

Definition NP_W3 := field_at_conflict'.

(* W4 *)
Lemma next_lseg_equal : forall T id ls sh x y z contents,
                          star (field_at sh T id y x) (@lseg T id ls sh contents x z) ===>
                               star (inj (x = z)) (field_at sh T id y x).
Proof.
  intros.
  unfold himp, star, inj.
  entailer.
  rewrite lseg_unroll. entailer.
  rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left.
  - entailer.
  - unfold lseg_cons.
    entailer.
    rewrite sepcon_comm.
    rewrite sepcon_assoc.
    rewrite (sepcon_comm (list_cell ls sh h x)).
    rewrite sepcon_assoc.
    rewrite <- sepcon_assoc.
    eapply derives_trans.
    + apply sepcon_derives; try (apply field_at_conflict).
      apply TT_right.
    + rewrite FF_sepcon.
      apply FF_left.
Qed.

Definition NP_W4 := next_lseg_equal.

Lemma neq_ptr_neq : forall x y, x <> y -> ptr_neq x y.
Proof.
  intros; unfold ptr_neq; unfold not; intro peq; apply ptr_eq_e in peq; tauto.
Qed.

(* Useful in some of the lemmas that follow *)
Lemma FF_elim : forall a b, a |-- FF -> a * b |-- FF.
Proof.
  intros.
  rewrite <- FF_sepcon with (P := TT).
  apply sepcon_derives. assumption.
  apply TT_right.
Qed.

(* W5 *)
Lemma lseg_conflict : forall T id ls sh contents x y z,
                        star (@lseg T id ls sh contents x y) (@lseg T id ls sh contents x z) ===>
                             star (inj (x = y \/ x = z))
                             (star (@lseg T id ls sh contents x y) (@lseg T id ls sh contents x z)).
Proof.
  intros.
  unfold himp, star, inj.
  entailer.
  rewrite lseg_unroll. rewrite lseg_unroll.
  rewrite distrib_orp_sepcon.
  apply orp_left.
  - entailer.
  - rewrite sepcon_comm.
    rewrite distrib_orp_sepcon.
    apply orp_left.
    + entailer.
    + unfold lseg_cons. entailer.
      eapply derives_trans.
      * apply FF_elim. rewrite sepcon_comm. rewrite <- sepcon_assoc.
        apply FF_elim. rewrite <- sepcon_assoc.
        apply FF_elim. rewrite <- sepcon_assoc. rewrite sepcon_comm. rewrite <- sepcon_assoc.
        apply FF_elim. apply field_at_conflict.
      * apply FF_left.
Qed.

Definition NP_W5 := lseg_conflict.

(* Used to simulate Navarro Perez's "Next" for unfolding lemmas
   TODO - use these in well-formedness lemmas also? *)

(* Definition list_next T sh id ls content x y :=
   star (field_at sh (tptr T) id y x) (list_cell ls sh content x) *)

(* U1 *)
Lemma first_field_at_lseg :
  forall T id sh ls h x z,
    star (field_at sh (tptr T) id z x) (list_cell ls sh h x) ===> 
       star (star (inj (x = z)) (field_at sh (tptr T) id z x)) (list_cell ls sh h x) ||
       (@lseg (tptr T) id ls sh (cons h nil) x z).
Proof.
  intros.
  sep_solve.
  destruct (EqDec_val x z).
  - subst.
    apply orp_right1.
    entailer.
  - apply orp_right2.
    rewrite lseg_unroll.
    apply orp_right2.
    unfold lseg_cons.
    rewrite exp_andp2. apply (exp_right h).
    rewrite exp_andp2. apply (exp_right nil).
    rewrite exp_andp2. apply (exp_right z).
    entailer.
Qed.

Definition NP_U1 := first_field_at_lseg.

(* U3-5 = list appending
   "Later"
   |>P is a weaker version of P (P -> |>P). Distributes and stuff.
   Find laws in veric book.

   Proof strategy: weaken induction hypothesis; use "n times later", with universally quantified n*)

(* U2 *)
Lemma next_field_at_lseg :
  forall T id sh ls h contents x y z,
    star (field_at sh (tptr T) id y x) (star (list_cell ls sh h x)
     (@lseg (tptr T) id ls sh contents y z)) ===>
    star (inj (x = z)) (star (field_at sh (tptr T) id y x)
                       (star (list_cell ls sh h x)
                               (@lseg (tptr T) id ls sh contents y z))) ||
    (@lseg (tptr T) id ls sh (cons h contents) x z).
Proof.
intros.
sep_solve.
destruct (EqDec_val x z).
- subst.
  apply orp_right1.
  entailer.
- apply orp_right2.
  rewrite lseg_unroll.
  entailer.
Qed.

Definition NP_U2 := next_field_at_lseg.

(* U3 *)
Lemma lseg_nil_append : forall T id sh ls c1 c2 x y,
      star (@lseg T id ls sh c1 x y) (@lseg T id ls sh c2 y nullval) ===>
      (@lseg T id ls sh (c1 ++ c2) x nullval).
Proof.
intros.
sep_solve.
pose (fun (v : val) => emp) as empred.
assert ( lseg ls sh c1 x y * lseg ls sh c2 y nullval * (empred nullval)
         |-- lseg ls sh (c1 ++ c2) x nullval * (empred nullval)) as lseg_fact'.
- apply list_append.
  intros.
  unfold lseg_cell. entailer.
- unfold empred in lseg_fact'.
  autorewrite with norm in *; try (assumption); try (apply Cveric).
Qed.

Definition NP_U3 := lseg_nil_append.

(* U4 *)
Lemma lseg_next_append : forall T id sh ls c1 c2 h x y z w,
      star (@lseg T id ls sh c1 x y)
           (star (@lseg T id ls sh c2 y z)
                 (star (field_at sh (tptr T) id w z)
                       (list_cell ls sh h z))) ===>
      star (@lseg T id ls sh (c1 ++ c2) x z)
           (star (field_at sh (tptr T) id w z)
                 (list_cell ls sh h z)).
Proof.
intros.
unfold himp, star, inj.
entailer.
Qed.

Definition NP_U4 := lseg_nil_append.

(* U5 *)
Lemma three_lseg_append : forall T id sh ls c1 c2 c3 x y z w,
      star (@lseg T id ls sh c1 x y)
           (star (@lseg T id ls sh c2 y z)
                 (@lseg T id ls sh c3 z w)) ===>
      star (@lseg T id ls sh (c1 ++ c2) x z) (@lseg T id ls sh c3 z w) ||
      star (inj (z = w)) 
           (star (@lseg T id ls sh c1 x y)
           (star (@lseg T id ls sh c2 y z)
                 (@lseg T id ls sh c3 z w))).
Proof.
intros.
sep_solve.
destruct (EqDec_val z w).
- subst. apply orp_right2.
  entailer.
- apply orp_right1.
  entailer.
  rewrite (sepcon_comm (lseg ls sh c3 z w)).
  pose (lpred := fun (z : val) => lseg ls sh c3 z w).
  assert ( lseg ls sh c1 x y * lseg ls sh c2 y z * (lpred z)
           |-- lseg ls sh (c1 ++ c2) x z * (lpred z)) as lseg_fact'.
  + apply list_append.
    intros.
    unfold lseg_cell. unfold lpred.
    entailer.
    rewrite lseg_neq.
    * unfold lseg_cons.
      entailer.
      apply FF_elim.
      rewrite sepcon_comm. rewrite <- sepcon_assoc. apply FF_elim.
      rewrite sepcon_comm. rewrite sepcon_assoc. rewrite sepcon_comm. apply FF_elim.
      apply field_at_conflict.
    * apply neq_ptr_neq; assumption.
  + assumption.
Qed.

Definition NP_U5 := three_lseg_append.

