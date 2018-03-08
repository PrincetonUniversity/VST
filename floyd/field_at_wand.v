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

Definition array_with_hole {cs: compspecs} sh (t: type) lo hi n (al': list (reptype t)) p :=
!! field_compatible (tarray t n) nil p &&
(ALL cl:reptype (tarray t (hi-lo)), EX cl':list (reptype t), EX dl:reptype (tarray t n), 
!! (JMeq cl cl' /\ JMeq dl (sublist 0 lo al' ++ cl' ++ sublist hi n al'))
&& (data_at sh (tarray t (hi-lo)) cl (field_address0 (tarray t n) (ArraySubsc lo :: nil) p)
-* data_at sh (tarray t n) dl p)).

Lemma array_with_hole_local_facts {cs: compspecs}: forall sh t lo hi n al' p,
array_with_hole sh t lo hi n al' p |-- 
!! (field_compatible (tarray t n) nil p).
Proof.
intros.
unfold array_with_hole. entailer!.
Qed.
Hint Resolve array_with_hole_local_facts : saturate_local.

Lemma wand_slice_array:
forall {cs: compspecs} lo hi n sh t (al: reptype (tarray t n)) (bl: reptype (tarray t (hi-lo)))
(al' : list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
JMeq al al' ->
JMeq bl (sublist lo hi al') ->
Zlength al' = n ->
data_at sh (tarray t n) al p =
data_at sh (tarray t (hi-lo)) bl (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) *
array_with_hole sh t lo hi n al' p.
Proof.
  intros until p.
  intros H H0 H2 H3 H1.
  unfold data_at, array_with_hole.
  assert (forall n, reptype (tarray t n) = list (reptype t)).
  {
    intros.
    rewrite reptype_eq.
    auto.
  }
  apply pred_ext.
  + rewrite (add_andp _ _ (field_at_local_facts _ _ _ _ _)).
    normalize.
    rename H5 into H7, H6 into H8.
    erewrite field_at_Tarray.
      2: constructor.
      2: reflexivity.
      2: omega.
      2: eassumption.
    erewrite (split3seg_array_at' _ _ _ 0 lo hi n); try omega.
      2:change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; omega.
    unfold data_at.
    rewrite (sepcon_comm (array_at _ _ _ _ _ _ _)), sepcon_assoc.
    apply sepcon_derives.
    - apply derives_refl'.
      f_equal.
      rewrite !Z.sub_0_r.
      pose proof fold_reptype_JMeq (tarray t (hi - lo)) (sublist lo hi al').
      pose proof JMeq_trans H3 (JMeq_sym H5).
      apply JMeq_eq in H6; auto.
    - apply allp_right; intros.
      apply (exp_right (unfold_reptype v)).
      apply (exp_right (eq_rect _ (fun x => x) (sublist 0 lo al' ++
             (unfold_reptype v) ++
             sublist hi n al') _ (eq_sym (H4 _)))).
      apply andp_right; [apply prop_right; split |].
      * clear.
        apply JMeq_sym.
        apply (unfold_reptype_JMeq (tarray t (hi - lo)) v).
      * clear.
        apply (eq_rect_JMeq _ _ _ (fun x => x) _ _).
      * apply -> wand_sepcon_adjoint.
        rewrite (add_andp _ _ (field_at_local_facts _ _ _ _ _)).
        normalize.
        rewrite value_fits_eq in H6; simpl in H6.
        destruct H6.
        rewrite Z.max_r in H6 by omega.
        erewrite (field_at_Tarray _ (tarray t n)).
          2: constructor.
          2: reflexivity.
          2: omega.
          2: apply (eq_rect_JMeq _ _ _ (fun x => x) _ _).
        erewrite (split3seg_array_at' _ _ _ 0 lo hi n); try omega.
          2: autorewrite with sublist; unfold tarray; rewrite H6; omega.
        unfold tarray; autorewrite with sublist.
        rewrite H6.
        replace (hi - lo - (hi - lo) + hi) with hi by omega.
        replace (n - lo - (hi - lo) + hi) with n by omega.
        rewrite !sepcon_assoc.
        apply sepcon_derives; [apply derives_refl |].
        rewrite sepcon_comm.
        apply sepcon_derives; [| apply derives_refl].
        unfold data_at.
        apply derives_refl'.
        f_equal.
        autorewrite with sublist.
        rewrite fold_unfold_reptype.
        auto.
  + normalize.
    clear H5.
    rewrite sepcon_comm.
    apply wand_sepcon_adjoint.
    apply (allp_left _ bl); intros.
    apply exp_left; intros.
    apply exp_left; intros.
    normalize.
    apply wand_derives; [apply derives_refl |].
    apply derives_refl'.
    unfold data_at.
    f_equal.
    apply JMeq_eq.
    eapply JMeq_trans; [eassumption |].
    eapply JMeq_trans; [| apply JMeq_sym; eassumption].
    pose proof JMeq_trans (JMeq_sym H5) H3.
    apply JMeq_eq in H7; subst.
    rewrite <- sublist_split by omega.
    rewrite <- sublist_split by omega.
    autorewrite with sublist.
    apply JMeq_refl.
Qed.

Ltac constr_wand_slice_array_spec t :=
let spec := constr:(forall lo hi n sh 
(al' : list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
Zlength al' = n ->
data_at sh (tarray t n) al' p =
data_at sh (tarray t (hi-lo)) (sublist lo hi al') (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) *
(!! (field_compatible (tarray t n) nil p) &&
(ALL cl: list (reptype t),
(data_at sh (tarray t (hi-lo)) cl (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) )
-* data_at sh (tarray t n) (sublist 0 lo al' ++ cl ++ sublist hi n al') p))) in
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
  f_equal; unfold array_with_hole;
  f_equal; f_equal; extensionality cl;
  refine (elim_double_exp (list (reptype t)) _ _ _).

(* Try the following lines with a concrete compspecs. *)
(*
Lemma wand_slice_array_tint: ltac:(constr_wand_slice_array_spec tint).
Proof. prove_wand_slice_array tint. Qed.

Lemma wand_slice_array_tptint: ltac:(constr_wand_slice_array_spec (tptr tint)).
Proof. prove_wand_slice_array (tptr tint). Qed.

Lemma wand_slice_array_tatint: ltac:(constr_wand_slice_array_spec (tarray tint 10)).
Proof. prove_wand_slice_array (tarray tint 10). Qed.
*)
