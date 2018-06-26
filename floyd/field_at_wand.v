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
forall {cs: compspecs} lo hi n sh t (al: list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
Zlength al = n ->
data_at sh (tarray t n) al p =
!! (field_compatible (tarray t n) nil p) &&
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
          change (Zlength (sublist 0 lo al ++ v ++ sublist hi n al) = n - 0).
          autorewrite with sublist.
          omega.
        } Unfocus.
        change (array_at sh (tarray t n) nil 0 lo (sublist 0 (lo - 0) al) p *
                array_at sh (tarray t n) nil hi n (sublist (hi - 0) (n - 0) al) p *
                field_at sh (tarray t (hi - lo)) nil v (field_address0 (tarray t n) (SUB lo) p)
                |-- array_at sh (tarray t n) nil 0 lo
                      (sublist 0 (lo - 0) (sublist 0 lo al ++ v ++ sublist hi n al)) p *
                    data_at sh (nested_field_array_type (tarray t n) nil lo hi)
                      (sublist (lo - 0) (hi - 0) (sublist 0 lo al ++ v ++ sublist hi n al))
                      (field_address0 (tarray t n) (SUB lo) p) *
                    array_at sh (tarray t n) nil hi n
                      (sublist (hi - 0) (n - 0) (sublist 0 lo al ++ v ++ sublist hi n al)) p).
        unfold tarray; autorewrite with sublist.
        rewrite H4.
        replace (hi - lo - (hi - lo) + hi) with hi by omega.
        replace (n - lo - (hi - lo) + hi) with n by omega.
        rewrite !sepcon_assoc.
        apply sepcon_derives; [apply derives_refl |].
        rewrite sepcon_comm.
        apply sepcon_derives; [| apply derives_refl].
        autorewrite with sublist.
        apply derives_refl.
  + normalize.
    clear H2.
    rewrite sepcon_comm.
    apply wand_sepcon_adjoint.
    apply (allp_left _ (sublist lo hi al)); intros.
    apply wand_derives; [apply derives_refl |].
    unfold data_at.
    apply derives_refl'.
    f_equal.
    autorewrite with sublist.
    auto.
Qed.
