Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import sep.
Require Import reify_derives.
Require Import functions.
Require Import progs.list_dt.
Import Expr.

Local Open Scope logic.
(* Might not need all of these? *)

(* From Navarro Perez (PLDI'11). *)
(* W1 *)
Lemma null_field_at_false : forall T sh id y,
  field_at sh T id y nullval |-- FF.
Proof.
intros; entailer.
Qed.

(* W2 *)
(* ctype and list link can be discovered from list spec *)
Lemma lseg_null_null : forall T ll ls sh y contents, y <> nullval ->
  @lseg T ll ls sh contents nullval y |-- FF.
intros.
erewrite lseg_unroll.
entailer.
eapply orp_left.
entailer. intuition.
unfold lseg_cons.
entailer.
Qed.

Check field_at_conflict.
(* W3 = field_at_conflict *)

(* W4 - danger; this spec might not quite be right *)
Lemma next_lseg_equal : forall T id ls sh x y z contents, x <> z ->
   field_at sh T id y x * @lseg T id ls sh contents x z |-- FF.
Proof.
intros.
entailer.
erewrite lseg_unroll.
entailer.
erewrite sepcon_comm.
erewrite distrib_orp_sepcon.
eapply orp_left.
entailer.
intuition.
unfold lseg_cons.
entailer.
rewrite sepcon_comm.
rewrite sepcon_assoc.
rewrite (sepcon_comm (list_cell ls sh h x)).
rewrite sepcon_assoc.
rewrite <- sepcon_assoc.
eapply derives_trans.
apply sepcon_derives.
apply field_at_conflict.
apply TT_right.
rewrite FF_sepcon.
apply FF_left.
Qed.

Lemma neq_ptr_neq : forall x y, x <> y -> ptr_neq x y.
Proof.
intros; unfold ptr_neq; unfold not; intro peq; apply ptr_eq_e in peq; tauto.
Qed.

(* W5 - I feel like there should be a more efficient way to do this. *)
(* TODO convert this to using right_is_prop from is_prop_lemma *)
Lemma lseg_conflict : forall T id ls sh contents x y z, (x <> y /\ x <> z) ->
      @lseg T id ls sh contents x y * @lseg T id ls sh contents x z |-- FF.
Proof.
  intros.
  inversion H.
  entailer.
  rewrite lseg_neq. rewrite lseg_neq.
  unfold lseg_cons. normalize. (* SLOW *)
  (* TODO add this to msl *)
  assert (forall a b, a |-- FF -> a * b |-- FF)%logic as FF_elim.
  intros.
  rewrite <- FF_sepcon with (P := TT).
  eapply sepcon_derives. assumption.
  eapply TT_right.
  (* don't even actually end up using the lemma *)
  eapply derives_trans with (field_at sh T id x3 x * field_at sh T id x0 x * TT)%logic.
  (* TT absorbs the separation facts we don't want *)
  cancel.
  apply FF_elim.
  apply field_at_conflict.

  apply neq_ptr_neq; assumption.
  apply neq_ptr_neq; assumption.
Qed.  

(* U3-5 = list appending
   "Later"
   |>P is a weaker version of P (P -> |>P). Distributes and stuff.
   Find laws in veric book.

   Proof strategy: weaken induction hypothesis; use "n times later", with universally quantified n*)

(* U1 *)
Lemma first_field_at_lseg : forall T id sh ls x z,
      x <> z -> exists contents,
      (field_at sh T id z x |-- @lseg T id ls sh contents x z).
Admitted.

(* U3 *)
(*
Lemma lseg_nil_append : forall T id1 id2 sh ls1 ls2 c1 c2 x y,
      @lseg T id1 ls1 sh c1 x y * @lseg T id2 ls2 sh c2 y nullval |--
      @lseg T id1 ls1 sh (c1 ++ c2) x nullval.
Check list_append.
Lemma 
*)

(*Proof.      
intros.
eexists.
rewrite lseg_neq.
SearchAbout lseg_cons.
unfold lseg_cons.
SearchAbout field_at.
 normalize.

SearchAbout (!!(_) && _).

apply neq_ptr_neq in H.
erewrite lseg_neq.
Focus 2.
unfold ptr_neq. unfold not.
erewrite lseg_unroll.
eapply orp_right2.
unfold lseg_cons. entailer.
Check list_append.
Admitted. *)

(* U2 *)
(*Lemma next_lseg_lseg : forall T id sh ls x z,
      x <> z -> *)

(*
Check @lseg.
Lemma first_mapsto_lseg : forall T ll sh ls x z,
      exists contents,
      ((prop (x =/= z)) && (mapsto sh T x z))%logic |-- @lseg T ll ls sh contents x z.

Lemma empty_list_emp : forall T ll ls sh lem x,
      is_pointer_or_null x ->
      @lseg T ll ls sh lem x x |-- emp.
intros.
rewrite lseg_eq.
SearchAbout (_ |-- emp * _).
unfold lseg. unfold lseg'.
SearchAbout lseg.
Locate lseg_nil_eq.
Check lseg.
Check listspec.
Check lseg.
SearchAbout mapsto.
*)

