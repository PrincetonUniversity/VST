Require Import floyd.proofauto.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import sep.
Require Import reify_derives.
Require Import functions.
Require Import progs.list_dt.
Import Expr.

Module SL := SepLemma VericSepLogic Sep.
Module HintModule := ReifyHints.Make VericSepLogic Sep SL. 


(* Begin hints *)

(* From Navarro Perez. I haven't tested these yet. *)
(* lseg x x |-- emp *)
Check @lseg.

(* W1 *)
Check field_at.
Lemma null_field_at_false : forall sh T id y,
  field_at sh T id y nullval |-- FF.
Proof.
intros; entailer.
Qed.

(* W2 *)
Lemma lseg_null_null : forall T ll sh ls y contents, y <> nullval ->
  (@lseg T ll ls sh contents nullval y)%logic |--
     FF.
intros.
SearchAbout lseg.
erewrite lseg_unroll.
entailer.
eapply orp_left.
entailer. intuition.
SearchAbout lseg_cons.
Print lseg_cons.
unfold lseg_cons.
entailer.
Qed.

(* W3 = field_at_conflict *)

(* W4 - danger; this spec might not quite be right *)
Lemma next_lseg_equal : forall T sh id ls x y z contents, x <> z ->
   (field_at sh T id y x * @lseg T id ls sh contents x z |-- FF)%logic.
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

(* talk to qinxiang *)

(* W5 - there's gotta be a better way to do this. *)
Lemma lseg_conflict : forall T sh id ls contents x y z, (x <> y /\ x <> z) ->
      (@lseg T id ls sh contents x y * @lseg T id ls sh contents x z |-- FF)%logic.
Proof.
  intros.
  inversion H.
  entailer.
  rewrite lseg_neq. rewrite lseg_neq.
  unfold lseg_cons. normalize.
  (* TODO add this to msl *)
  assert (forall a b, a |-- FF -> a * b |-- FF)%logic.
  intros.
  rewrite <- FF_sepcon with (P := TT).
  eapply sepcon_derives. assumption.
  eapply TT_right.
  (* don't even actually end up using the lemma *)
  eapply derives_trans with (field_at sh T id x3 x * field_at sh T id x0 x * TT)%logic.
  (* TT absorbs the separation facts we don't want *)
  cancel.
  apply H7.
  apply field_at_conflict.
  

  unfold ptr_neq. unfold not. intros. apply ptr_eq_e in H2. tauto.
  unfold ptr_neq. unfold not. intros. apply ptr_eq_e in H2. tauto.
Qed.  

(* U3-5 = list appending
   "Later"
   |>P is a weaker version of P (P -> |>P). Distributes and stuff.
   Find laws in veric book.

   Proof strategy: weaken induction hypothesis; use "n times later", with universally quantified n

*)

(* U1 *)
Check field_at.
Lemma first_field_at_lseg : forall T id sh ls x z,
      x <> z -> exists contents,
      (field_at sh T id x z |-- @lseg T id ls sh contents x z).
Proof.      
intros.
eexists.
erewrite lseg_unroll.
eapply orp_right2.
unfold lseg_cons. entailer.
Admitted.
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
(* left-hints *)

(* right-hints *)

(* from verif_reverse *)
Lemma eq_ptr_emp_lseg : forall T ll a b sh LS,
        (*(ptr_eq a b -> *)(VericSepLogic_Kernel.himp VericSepLogic_Kernel.emp (@lseg T ll LS sh nil a b)).
Admitted.
(*intros.
entailer!.
Qed. *)
(*assert (dreq := (derives_refl'' _ _ (lseg_nil_eq LS0 sh a b))).
eapply derives_trans.
Focus 2.
apply dreq.
eapply andp_right.
apply prop_right. assumption.
auto.
Qed. *)
(* End hints *)

Axiom PQ : forall n, VericSepLogic_Kernel.himp (P n) (Q n).

Check PQ. Check VericSepLogic_Kernel.himp.

(*Make a tuple here *)
Definition left_hints := (PQ).

Ltac id_this x := assert (exists n, x=n).


(*Uncomment this if you are adding new lemmas and need to see some reified things*)
(*Goal False.
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints types functions preds 
ltac:(fun funcs preds hints => id_this (funcs, preds, hints)). 
Admitted.*)

(*Copied and pasted from above goal.
NOTE: Be sure that you add any predicates/functions
that were added here in functions.v (so if you see anything other than functions and preds
as the first two items of the tuple printed in the above goal, you need to add something
to the appropriate list in functions.v
NOTE2: you might need to change to a form of record notation where you can give the
implicit argument. Do this if you are having type errors
*)

(*Definition left_lemmas: list (Lemma.lemma types.our_types (SL.sepConcl types.our_types)).*)
Definition left_lemmas: list (Lemma.lemma SL.sepConcl).
pose_env. 
HintModule.reify_hints ltac:(fun x => x) tt tt is_const left_hints types functions preds 
ltac:(fun funcs preds hints => apply hints). 
Defined.
 
Axiom QP : forall n,  VericSepLogic_Kernel.himp (Q n) (P n).

Definition right_hints := QP. (*(QP, eq_ptr_emp_lseg).*)

(*Make sure you have already updated any funcs and preds that might have been added by doing
the left rules *)

(*Uncomment this if you are adding new lemmas and need to see some reified things*)
(*Goal False.
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints => id_this (funcs, preds, hints)). *)
(* Admitted. *)

(*Copied from above goal*)
(*Definition right_lemmas : list (Lemma.lemma types.our_types (SL.sepConcl types.our_types)).*)
Definition right_lemmas : list (Lemma.lemma SL.sepConcl).
pose_env.
HintModule.reify_hints ltac:(fun x => x) tt tt is_const right_hints types functions preds 
ltac:(fun funcs preds hints =>  apply hints). 
Defined.
