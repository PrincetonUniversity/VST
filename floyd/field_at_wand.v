Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.stronger.
Require Import VST.floyd.entailer.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.loadstore_field_at.
Require Import VST.floyd.nested_loadstore.

Local Open Scope logic.

Lemma wand_slice_array:
forall {cs: compspecs} lo hi n sh t (al: reptype (tarray t n)) (bl: reptype (tarray t (hi-lo)))
(al' : list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
Zlength al' = n ->
JMeq al al' ->
JMeq bl (sublist lo hi al') ->
data_at sh (tarray t n) al p =
data_at sh (tarray t (hi-lo)) bl (field_address (tarray t n) (ArraySubsc lo :: nil) p) *
(ALL cl:_, EX cl':_, EX dl:_, 
!! (JMeq cl cl' /\ JMeq dl (sublist 0 lo al' ++ cl' ++ sublist hi n al'))
&& (data_at sh (tarray t (hi-lo)) cl (field_address0 (tarray t n) (ArraySubsc lo :: nil) p)
-* data_at sh (tarray t n) dl p)).
Proof.
  intros.
  unfold data_at.
  assert (reptype (tarray t n) = list (reptype t)).
  {
    rewrite reptype_eq.
    auto.
  }
  assert (@JMeq _ al (list (reptype t)) (eq_rect _ (fun x => x) al _ H3)).
  {
    apply JMeq_sym.
    apply (@eq_rect_JMeq _ (reptype (tarray t n))  (list (reptype t)) (fun x => x) al H3).
  }
  rewrite (add_andp _ _ (field_at_local_facts _ _ _ _ _)).
  erewrite field_at_Tarray.
    2: constructor.
    2: reflexivity.
    2: omega.
    2: eassumption.
    Print array_at. Locate split3seg_array_at. Check aggregate_pred.split_array_pred.
  erewrite (split3seg_array_at _ _ _ 0 lo hi n); try omega.
  Focus 2.
    generalize H3.
    revert
    2: generalize H3rewrite <- eq_rect_eq.  
  SearchAbout array_at.
  SearchAbout data_at tarray.
Admitted.

Ltac constr_wand_slice_array_spec t :=
let spec := constr:(forall lo hi n sh 
(al' : list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
data_at sh (tarray t n) al' p =
data_at sh (tarray t (hi-lo)) (sublist lo hi al') (field_address (tarray t n) [ArraySubsc lo] p) *
(ALL cl: list (reptype t),
(data_at sh (tarray t (hi-lo)) cl (field_address0 (tarray t n) [ArraySubsc lo] p) )
-* data_at sh (tarray t n) (sublist 0 lo al' ++ cl ++ sublist hi n al') p)) in
exact spec.

Lemma elim_double_exp: forall (T: Type) (x: T) (y: T -> T) (P: T -> T -> mpred),
  EX x0: T, (EX y0: T,
    (!! (JMeq x x0 /\ JMeq y0 (y x0)) && (P x0 y0))) =
  P x (y x).
Proof.
  intros.
  apply pred_ext.
  + apply exp_left; intros.
    apply exp_left; intros.
    entailer!.
    apply JMeq_eq in H.
    apply JMeq_eq in H0.
    entailer!.
  + apply (exp_right x).
    apply (exp_right (y x)).
    entailer!.
Qed.

Ltac prove_wand_slice_array t :=
  hnf; intros;
  erewrite wand_slice_array by eauto;
  f_equal;
  f_equal; extensionality cl;
  refine (elim_double_exp (list (reptype t)) _ _ _).

Lemma wand_slice_array_tint: ltac:(constr_wand_slice_array_spec tint).
Proof.
  prove_wand_slice_array tint.
Qed.

Lemma wand_slice_array_tptint: ltac:(constr_wand_slice_array_spec (tptr tint)).
Proof.
  prove_wand_slice_array (tptr tint).
Qed.

Lemma wand_slice_array_tatint: ltac:(constr_wand_slice_array_spec (tarray tint 10)).
Proof.
  prove_wand_slice_array (tarray tint 10).
Qed.