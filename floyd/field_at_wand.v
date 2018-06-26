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
(ALL cl:reptype (tarray t (hi-lo)),
(data_at sh (tarray t (hi-lo)) cl (field_address0 (tarray t n) (ArraySubsc lo :: nil) p)
-* data_at sh (tarray t n) (sublist 0 lo al' ++ cl ++ sublist hi n al') p)).

Lemma array_with_hole_local_facts {cs: compspecs}: forall sh t lo hi n al' p,
array_with_hole sh t lo hi n al' p |-- 
!! (field_compatible (tarray t n) nil p).
Proof.
intros.
unfold array_with_hole. entailer!.
Qed.
Hint Resolve array_with_hole_local_facts : saturate_local.

Lemma wand_slice_array:
forall {cs: compspecs} lo hi n sh t (al bl: list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
Zlength al = n ->
data_at sh (tarray t n) al p =
data_at sh (tarray t (hi-lo)) (sublist lo hi al) (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) *
array_with_hole sh t lo hi n al p.
Proof.
  intros until p.
  intros H H0 H1.
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
    rename H3 into H7, H4 into H8.
    erewrite field_at_Tarray.
      2: constructor.
      2: reflexivity.
      2: omega.
      2: apply JMeq_refl.
    erewrite (split3seg_array_at' _ _ _ 0 lo hi n); try omega.
      2:etransitivity; [exact H1 | omega].
    unfold data_at.
    rewrite (sepcon_comm (array_at _ _ _ _ _ _ _)), sepcon_assoc.
    apply sepcon_derives.
    - apply derives_refl'.
      f_equal.
      rewrite !Z.sub_0_r.
      auto.
    - apply allp_right; intros v. change (list (reptype t)) in v.
      * apply -> wand_sepcon_adjoint.
        rewrite (add_andp _ _ (field_at_local_facts _ _ _ _ _)).
        normalize.
        rewrite value_fits_eq in H4; simpl in H4.
        destruct H4.
        rewrite Z.max_r in H4 by omega.
        change (@Zlength (reptype t) v = hi - lo) in H4.
        erewrite (field_at_Tarray _ (tarray t n)).
          2: constructor.
          2: reflexivity.
          2: omega.
          2: apply JMeq_refl.
        erewrite (split3seg_array_at' _ _ _ 0 lo hi n); try omega.
        Focus 2. {
          autorewrite with sublist.
          replace n with (lo + (@Zlength (reptype t) v + (n - hi))) at 2 by omega.
          reflexivity.
        } Unfocus.
        change (@reptype cs (@nested_field_type cs (tarray t n) (SUB 0))) with (reptype t).
        unfold tarray; autorewrite with sublist.
        rewrite H4.
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

Ltac wand_slice_array_spec t :=
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

Ltac prove_wand_slice_array :=
  let al := fresh "al" in 
  intros ? ? ? ? al ? ? ? ?;
   erewrite wand_slice_array by eauto;
   f_equal; unfold array_with_hole;
   f_equal; f_equal; extensionality cl;
  match type of al with ?t =>
   refine (elim_double_exp t _ _ _)
  end.

(* Try the following lines with a concrete compspecs. *)
(*
Lemma wand_slice_array_tint: ltac:(wand_slice_array_spec tint).
Proof. prove_wand_slice_array. Qed.

Lemma wand_slice_array_tptint: ltac:(wand_slice_array_spec (tptr tint)).
Proof. prove_wand_slice_array. Qed.

Lemma wand_slice_array_tatint: ltac:(wand_slice_array_spec (tarray tint 10)).
Proof. prove_wand_slice_array. Qed.
*)
