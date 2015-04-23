Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.rangespec_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(************************************************

Definition of nested_reptype_structlist, field_at, nested_sfieldlist_at

************************************************)

Fixpoint nested_reptype_structlist (t: type) (gfs: list gfield) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons i _ fld' =>
    if (is_Fnil fld')
    then reptype (nested_field_type2 t (StructField i :: gfs))
    else prod (reptype (nested_field_type2 t (StructField i :: gfs))) 
         (nested_reptype_structlist t gfs fld')
  end.

Fixpoint nested_reptype_unionlist (t: type) (gfs: list gfield) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons i _ fld' =>
    if (is_Fnil fld')
    then reptype (nested_field_type2 t (UnionField i :: gfs))
    else sum (reptype (nested_field_type2 t (UnionField i :: gfs)))
         (nested_reptype_unionlist t gfs fld')
  end.

Lemma nested_reptype_lemma: forall t gfs t0, nested_field_type t gfs = Some t0 -> reptype t0 = reptype (nested_field_type2 t gfs).
Proof.
  unfold nested_field_type, nested_field_type2.
  intros.
  destruct (nested_field_rec t gfs) as [(ofs', t')|] eqn:HH.
  + inversion H.
    reflexivity.
  + inversion H.
Defined.

Lemma nested_reptype_structlist_lemma: forall t gfs i f' f a ofs,
  nested_field_rec t gfs = Some (ofs, Tstruct i (fieldlist_app f' f) a) ->
  nested_legal_fieldlist t = true ->
  reptype_structlist f = nested_reptype_structlist t gfs f.
Proof.
  intros.
  assert (nested_field_type2 t gfs = Tstruct i (fieldlist_app f' f) a).
    unfold nested_field_type2. rewrite H. reflexivity.
  eapply (nested_field_type2_nest_pred eq_refl t gfs), nested_pred_atom_pred in H0.
  rewrite H1 in H0; clear H1.
  revert f' H H0; induction f; intros.
  + reflexivity.
  + simpl. pose proof field_type_mid _ _ _ _ H0.
    destruct f.
    - simpl. 
      apply nested_reptype_lemma.
      unfold nested_field_type.
      simpl.
      rewrite H.
      solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 Fnil)); inversion H1.
      reflexivity.
    - destruct (is_Fnil (Fcons i1 t1 f)) eqn:Heq; [simpl in Heq; congruence| clear Heq].
      rewrite (nested_reptype_lemma t (StructField i0 :: gfs) t0).
      rewrite fieldlist_app_Fcons in H0, H.
      rewrite (IHf _ H H0).
      reflexivity.
      * unfold nested_field_type.
        simpl.
        rewrite H.
        solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 (Fcons i1 t1 f)));
        inversion H1; reflexivity.
Defined.

Lemma nested_reptype_structlist_lemma2: forall t gfs i f a,
  nested_field_type2 t gfs = Tstruct i f a ->
  nested_legal_fieldlist t = true ->
  reptype (nested_field_type2 t gfs) = nested_reptype_structlist t gfs f.
Proof.
  intros.
  rewrite H. simpl.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  apply (nested_reptype_structlist_lemma _ _ i Fnil f a ofs); simpl; [|exact H0].
  unfold nested_field_type2 in H.
  unfold nested_field_type.
  valid_nested_field_rec t gfs H; inversion H1.
  subst.
  reflexivity.
Defined.

Lemma nested_reptype_unionlist_lemma: forall t gfs i f' f a ofs,
  nested_field_rec t gfs = Some (ofs, Tunion i (fieldlist_app f' f) a) ->
  nested_legal_fieldlist t = true ->
  reptype_unionlist f = nested_reptype_unionlist t gfs f.
Proof.
  intros.
  assert (nested_field_type2 t gfs = Tunion i (fieldlist_app f' f) a).
    unfold nested_field_type2. rewrite H. reflexivity.
  eapply (nested_field_type2_nest_pred eq_refl t gfs), nested_pred_atom_pred in H0.
  rewrite H1 in H0; clear H1.
  revert f' H H0; induction f; intros.
  + reflexivity.
  + simpl. pose proof field_type_mid _ _ _ _ H0.
    destruct f.
    - simpl. 
      apply nested_reptype_lemma.
      unfold nested_field_type.
      simpl.
      rewrite H.
      solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 Fnil)); inversion H1.
      reflexivity.
    - destruct (is_Fnil (Fcons i1 t1 f)) eqn:Heq; [simpl in Heq; congruence| clear Heq].
      rewrite (nested_reptype_lemma t (UnionField i0 :: gfs) t0).
      rewrite fieldlist_app_Fcons in H0, H.
      rewrite (IHf _ H H0).
      reflexivity.
      * unfold nested_field_type.
        simpl.
        rewrite H.
        solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 (Fcons i1 t1 f)));
        inversion H1; reflexivity.
Defined.

Lemma nested_reptype_unionlist_lemma2: forall t gfs i f a,
  nested_field_type2 t gfs = Tunion i f a ->
  nested_legal_fieldlist t = true ->
  reptype (nested_field_type2 t gfs) = nested_reptype_unionlist t gfs f.
Proof.
  intros.
  rewrite H. simpl.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  apply (nested_reptype_unionlist_lemma _ _ i Fnil f a ofs); simpl; [|exact H0].
  unfold nested_field_type2 in H.
  unfold nested_field_type.
  valid_nested_field_rec t gfs H; inversion H1.
  subst.
  reflexivity.
Defined.

Definition field_at (sh: Share.t) (t: type) (gfs: list gfield) (v: reptype (nested_field_type2 t gfs)) : val -> mpred :=
  (!! (legal_alignas_type t = true)) &&
  (!! (nested_legal_fieldlist t = true)) &&
  (fun p => (!! (size_compatible t p /\ align_compatible t p /\ legal_nested_field t gfs))) 
  && data_at' sh empty_ti (nested_field_type2 t gfs) (nested_field_offset2 t gfs) v.
Arguments field_at sh t gfs v p : simpl never.

Definition field_at_ (sh: Share.t) (t: type) (gfs: list gfield) : val -> mpred :=
  field_at sh t gfs (default_val (nested_field_type2 t gfs)).
Arguments field_at_ sh t gfs p : simpl never.

Fixpoint nested_sfieldlist_at (sh: Share.t) (t1: type) (gfs: list gfield) (flds: fieldlist) (v: nested_reptype_structlist t1 gfs flds) : val -> mpred := 
  match flds as f return (nested_reptype_structlist t1 gfs f -> val -> mpred) with
  | Fnil => fun _ p => (!! isptr p) && emp
  | Fcons i t flds0 =>
    fun (v : nested_reptype_structlist t1 gfs (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          ((if b
            then reptype (nested_field_type2 t1 (StructField i :: gfs))
            else ((reptype (nested_field_type2 t1 (StructField i :: gfs)) *
        nested_reptype_structlist t1 gfs flds0)%type)) -> val -> mpred)
       then
        fun (v0: reptype (nested_field_type2 t1 (StructField i :: gfs))) =>
          withspacer sh (nested_field_offset2 t1 (StructField i :: gfs)
          + sizeof (nested_field_type2 t1 (StructField i :: gfs))) 
          (align (nested_field_offset2 t1 (StructField i :: gfs) + 
          sizeof (nested_field_type2 t1 (StructField i :: gfs)))
          (alignof (nested_field_type2 t1 gfs))) (field_at sh t1 (StructField i :: gfs) v0)
       else
        fun (v0: ((reptype (nested_field_type2 t1 (StructField i :: gfs)) *
        nested_reptype_structlist t1 gfs flds0)%type)) =>
          withspacer sh (nested_field_offset2 t1 (StructField i :: gfs) +
          sizeof (nested_field_type2 t1 (StructField i :: gfs)))
          (align (nested_field_offset2 t1 (StructField i :: gfs) +
          sizeof (nested_field_type2 t1 (StructField i :: gfs))) (alignof_hd flds0))
          (field_at sh t1 (StructField i :: gfs) (fst v0)) *
          (nested_sfieldlist_at sh t1 gfs flds0 (snd v0)))
    v
  end v.

Fixpoint nested_ufieldlist_at (sh: Share.t) (t1: type) (gfs: list gfield) (flds: fieldlist) (v: nested_reptype_unionlist t1 gfs flds) : val -> mpred := 
  match flds as f return (nested_reptype_unionlist t1 gfs f -> val -> mpred) with
  | Fnil => fun _ p => (!! isptr p) && emp
  | Fcons i t flds0 =>
    fun (v : nested_reptype_unionlist t1 gfs (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          ((if b
            then reptype (nested_field_type2 t1 (UnionField i :: gfs))
            else ((reptype (nested_field_type2 t1 (UnionField i :: gfs)) +
        nested_reptype_unionlist t1 gfs flds0)%type)) -> val -> mpred)
       then
         fun (v0: reptype (nested_field_type2 t1 (UnionField i :: gfs))) =>
           withspacer sh (nested_field_offset2 t1 (UnionField i :: gfs) + 
             sizeof (nested_field_type2 t1 (UnionField i :: gfs)))  
             (nested_field_offset2 t1 gfs + sizeof (nested_field_type2 t1 gfs)) 
             (field_at sh t1 (UnionField i :: gfs) v0)
       else
        fun (v0: ((reptype (nested_field_type2 t1 (UnionField i :: gfs)) +
          nested_reptype_unionlist t1 gfs flds0)%type)) =>
        match v0 with
        | inl v0' => withspacer sh (nested_field_offset2 t1 (UnionField i :: gfs) + 
            sizeof (nested_field_type2 t1 (UnionField i :: gfs))) 
            (nested_field_offset2 t1 gfs + sizeof (nested_field_type2 t1 gfs))
            (field_at sh t1 (UnionField i :: gfs) v0')
        | inr v0' => nested_ufieldlist_at sh t1 gfs flds0 v0'
        end)
    v
  end v.

Lemma nested_field_type2_ArraySubsc: forall t gfs i j,
  nested_field_type2 t (ArraySubsc i :: gfs) = nested_field_type2 t (ArraySubsc j :: gfs).
Proof.
  intros.
  unfold nested_field_type2.
  destruct (nested_field_rec t (ArraySubsc i :: gfs)) as [[? ?]|] eqn:?H;
  destruct (nested_field_rec t (ArraySubsc j :: gfs)) as [[? ?]|] eqn:?H; auto.
  + simpl in H, H0.
    destruct (nested_field_rec t gfs) as [[? tt]| ]; destruct tt; inversion H; inversion H0; subst.
    auto.
  + simpl in H, H0.
    destruct (nested_field_rec t gfs) as [[? tt]| ]; destruct tt; inversion H; inversion H0; subst.
  + simpl in H, H0.
    destruct (nested_field_rec t gfs) as [[? tt]| ]; destruct tt; inversion H; inversion H0; subst.
Qed.    

Definition nested_Znth {t: type} {gfs: list gfield} (lo n: Z)
  (v: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))) :
  reptype (nested_field_type2 t (ArraySubsc n :: gfs)) :=
  eq_rect_r reptype (Znth (n - lo) v (default_val _)) (nested_field_type2_ArraySubsc t gfs n 0).

Definition array_at (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z)
  (v: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))) : val -> mpred :=
  (!! (legal_alignas_type t = true)) &&
  (!! (nested_legal_fieldlist t = true)) &&
  (fun p : val =>
    !!(isptr p /\ size_compatible t p /\ align_compatible t p /\
       legal_nested_field t gfs)) &&
  rangespec lo hi 
    (fun i => !! legal_nested_field t (ArraySubsc i :: gfs) &&
    data_at' sh empty_ti (nested_field_type2 t (ArraySubsc i :: gfs))
      (nested_field_offset2 t (ArraySubsc i :: gfs)) (nested_Znth lo i v)).

Definition array_at_ (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z) :=
  array_at sh t gfs lo hi (list_repeat (Z.to_nat (hi-lo)) (default_val (nested_field_type2 t (ArraySubsc 0 :: gfs)))).

Opaque alignof.

Lemma nested_Znth_app_l: forall {t gfs} lo i (ct1 ct2: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))),
  0 <= i - lo < Zlength ct1 ->
  nested_Znth lo i ct1 = nested_Znth lo i (ct1 ++ ct2).
Proof.
  intros.
  unfold nested_Znth.
  f_equal.
  unfold Znth.
  if_tac; [omega |].
  rewrite app_nth1; [reflexivity |].
  destruct H as [_ ?].
  apply Z2Nat.inj_lt in H; [| omega | omega].
  rewrite Zlength_correct in H.
  rewrite Nat2Z.id in H.
  exact H.
Qed.

Lemma nested_Znth_app_r: forall {t gfs} lo i (ct1 ct2: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))),
  i - lo >= Zlength ct1 ->
  nested_Znth (lo + Zlength ct1) i ct2 = nested_Znth lo i (ct1 ++ ct2).
Proof.
  intros.
  unfold nested_Znth.
  f_equal.
  unfold Znth.
  assert (Zlength ct1 >= 0).
  Focus 1. {
    rewrite Zlength_correct.
    pose proof Zle_0_nat (length ct1).
    omega.
  } Unfocus.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite app_nth2.
  + f_equal.
    replace (i - (lo + Zlength ct1)) with (i - lo - Zlength ct1) by omega.
    rewrite Z2Nat.inj_sub by omega.
    rewrite Zlength_correct.
    rewrite Nat2Z.id.
    reflexivity.
  + rewrite <- (Nat2Z.id (length ct1)).
    rewrite <- Zlength_correct.
    apply Z2Nat.inj_le; omega.
Qed.

Lemma field_at_Tarray: forall sh t gfs t0 n a v1 v2,
  nested_field_type2 t gfs = Tarray t0 n a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 = array_at sh t gfs 0 n v2.
Proof.
Opaque nested_field_rec.
  intros.
  unfold field_at, array_at.
  extensionality p.
  simpl.
  revert v1 H0; rewrite H; intros.
  simpl.
  unfold array_at', field_at.
  normalize.
Transparent nested_field_rec.
  assert (forall i, nested_field_rec t (ArraySubsc i :: gfs) =
    Some (nested_field_offset2 t gfs + sizeof t0 * i, t0)).
  Focus 1. {
    unfold nested_field_type2 in H.
    unfold nested_field_offset2.
    valid_nested_field_rec t gfs H.
    intros; simpl.
    rewrite H1; subst.
    reflexivity.
  } Unfocus.
  assert (forall i, JMeq (Znth i v1 (default_val t0)) (nested_Znth 0 i v2)).
  Focus 1. {
    intros.
    unfold nested_Znth.
    generalize (nested_field_type2_ArraySubsc t gfs i 0).
    revert v2 H0.   
    unfold nested_field_type2.
    rewrite (H1 i), (H1 0).
    intros.
    rewrite Z.sub_0_r.
    apply JMeq_sym.
    rewrite eq_rect_r_JMeq, H0.
    reflexivity.
  } Unfocus.
Opaque nested_field_rec.
  apply pred_ext; normalize; apply rangespec_ext_derives; intros.
  + assert (legal_nested_field t (ArraySubsc i :: gfs)).
    Focus 1. {
      apply legal_nested_field_cons_lemma.
      rewrite H.
      auto.
    } Unfocus.
    normalize.
    specialize (H2 i).
    revert H2; generalize (nested_Znth 0 i v2).
    unfold nested_field_type2.
    unfold nested_field_offset2 at 2.
    rewrite (H1 i); intros.
    rewrite <- H2.
    rewrite Z.sub_0_r.
    apply derives_refl.
  + simpl.
    normalize.
    specialize (H2 i).
    revert H2; generalize (nested_Znth 0 i v2).
    unfold nested_field_type2.
    unfold nested_field_offset2 at 1.
    rewrite (H1 i); intros.
    rewrite <- H2.
    rewrite Z.sub_0_r.
    apply derives_refl.
Transparent nested_field_rec.
Qed.

Lemma field_at_Tstruct: forall sh t gfs i f a v1 v2,
  eqb_fieldlist f Fnil = false ->
  nested_field_type2 t gfs = Tstruct i f a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 = nested_sfieldlist_at sh t gfs f v2.
Proof.
  intros until v2.
  intros H H0 H2.
  pose proof I as H1.
  pose proof I as H3.
  unfold field_at.
  unfold nested_field_type2, nested_field_offset2 in *.
  valid_nested_field_rec t gfs H1; inversion H0; clear H5. subst t0.
  revert v1 H2; simpl (reptype (Tstruct i f a)); simpl data_at'; intros.

  destruct f; [inversion H|].
  pose proof nested_field_rec_Tstruct_hd _ _ _ _ _ _ _ _ H4.
  change (Tstruct i (Fcons i0 t0 f) a) with (Tstruct i (fieldlist_app Fnil (Fcons i0 t0 f)) a).
  change (Fcons i0 t0 f) with (fieldlist_app Fnil (Fcons i0 t0 f)) in H, H4.
  remember ofs as ofs0. rewrite Heqofs0 in H4. clear Heqofs0.
  forget Fnil as f'.
  revert ofs0 f' i0 t0 v1 v2 H H0 H2 H4; induction f; intros.
  + simpl.
    unfold field_at.
    revert v1 v2 H2.
    simpl reptype_structlist. simpl nested_reptype_structlist.
    unfold nested_field_offset2, nested_field_type2.
    rewrite H4. rewrite H0.
    intros.
    rewrite H2. extensionality p.
    repeat rewrite withspacer_spacer.
    assert (legal_nested_field t gfs <-> legal_nested_field t (StructField i0 :: gfs)).
    Focus. {
      eapply iff_trans; [| apply iff_sym, legal_nested_field_cons_lemma].
      simpl.
      unfold nested_field_type2; rewrite H4.
      split; [| tauto].
      intros; split; [tauto |].
      rewrite fieldlist_app_field_type_isOK.
      destruct (isOK (field_type i0 f')); simpl; try if_tac; try congruence; reflexivity.
    } Unfocus.
    match goal with
    | |- _ && _ && (?P (?A /\ ?B /\ ?C)) && _ = _ =>
      replace (P (A /\ B /\ C)) with (P (A /\ B /\ legal_nested_field t (StructField i0 :: gfs)))
        by (apply pred_ext; normalize; tauto)
    end.
    apply pred_ext; simpl; normalize.
  + assert (is_Fnil (Fcons i0 t0 f) = false) by reflexivity.
    remember (Fcons i0 t0 f) as f''.
    revert v1 v2 H2.
    simpl reptype_structlist. simpl nested_reptype_structlist.
    simpl sfieldlist_at'. simpl nested_sfieldlist_at.
    rewrite H5; intros.
    clear H3.
    destruct (legal_alignas_type t) eqn:?H.
    Focus 2. {
      unfold field_at.
      extensionality p.
      rewrite H3.
      replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (false = true)) with
        (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
        by (apply pred_ext; normalize; congruence).
      apply pred_ext; normalize; rewrite withspacer_spacer; normalize.
    } Unfocus.
    clear H1.
    destruct (nested_legal_fieldlist t) eqn:?H.
    Focus 2. {
      unfold field_at.
      extensionality p.
      rewrite H1.
      replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (false = true)) with
        (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
        by (apply pred_ext; normalize; congruence).
      apply pred_ext; normalize; rewrite withspacer_spacer; normalize.
    } Unfocus.
    extensionality p.
    assert (Heq_fst: reptype t1 = reptype (nested_field_type2 t (StructField i1 :: gfs))).
      unfold nested_field_type2; rewrite H0; reflexivity.
    assert (Heq_snd: reptype_structlist f'' = nested_reptype_structlist t gfs f'').
      rewrite fieldlist_app_Fcons in H4.
      apply (nested_reptype_structlist_lemma t gfs i _ _ a _ H4 H1).
    assert (H_fst: JMeq (fst v2) (fst v1)).
      revert v1 v2 H2. rewrite Heq_fst, Heq_snd. intros. 
      rewrite H2. reflexivity.
    assert (H_snd: JMeq (snd v1) (snd v2)).
      clear H_fst. revert v1 v2 H2. rewrite Heq_fst, Heq_snd. intros. 
      rewrite H2. reflexivity.
    remember (fst v1) as fst_v1; clear Heqfst_v1.
    remember (snd v1) as snd_v1; clear Heqsnd_v1.
    remember (fst v2) as fst_v2; clear Heqfst_v2.
    remember (snd v2) as snd_v2; clear Heqsnd_v2.
    clear H2 v1 v2.
    revert fst_v2 snd_v2 Heq_fst Heq_snd H_fst H_snd.
    simpl reptype_structlist. simpl nested_reptype_structlist.
    unfold field_at.
    unfold nested_field_offset2, nested_field_type2.
    rewrite H0. intros.
    rewrite H_fst.
    simpl.
    repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    subst f''.
    assert (nested_field_rec t (StructField i0 :: gfs) = 
      Some (align (ofs0 + sizeof t1) (alignof_hd (Fcons i0 t0 f)), t0)); [simpl alignof_hd; apply (nested_field_rec_Tstruct_mid i1 t1 t1 i0 t0 t gfs i f' f a ofs ofs0); assumption|].
    rewrite fieldlist_app_Fcons in *.
    erewrite <- IHf; [| | exact H2 | exact H_snd |exact H4].
    assert (legal_nested_field t gfs <-> legal_nested_field t (StructField i1 :: gfs)).
    Focus. {
      eapply iff_trans; [| apply iff_sym, legal_nested_field_cons_lemma].
      simpl.
      unfold nested_field_type2; rewrite H4.
      split; [| tauto].
      intros; split; [tauto |].
      rewrite fieldlist_app_field_type_isOK.
      rewrite fieldlist_app_field_type_isOK.
      rewrite !orb_true_iff; left; right; simpl.
      if_tac; [reflexivity |congruence].
    } Unfocus.
    match goal with
    | |- _ && _ && (?P (?A /\ ?B /\ ?C)) && _ = _ =>
      replace (P (A /\ B /\ C)) with (P (A /\ B /\ C /\ legal_nested_field t (StructField i1 :: gfs)))
        by (apply pred_ext; normalize; tauto)
    end.
    apply pred_ext; simpl; normalize.

    destruct (eqb_fieldlist
     (fieldlist_app (fieldlist_app f' (Fcons i1 t1 Fnil)) (Fcons i0 t0 f))
     (fieldlist_app f' (Fcons i1 t1 Fnil))) eqn:HH; [|reflexivity].
    apply eqb_fieldlist_true in HH.
    clear -HH.
    induction (fieldlist_app f' (Fcons i1 t1 Fnil)).
    - inversion HH.
    - inversion HH. tauto.  
Qed.

Lemma field_at_Tunion: forall sh t gfs i f a v1 v2,
  eqb_fieldlist f Fnil = false ->
  nested_field_type2 t gfs = Tunion i f a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 = nested_ufieldlist_at sh t gfs f v2.
Proof.
Opaque sizeof.
  intros until v2.
  intros H H0 H2.
  destruct (legal_alignas_type t) eqn:H3.
  Focus 2. {
    clear H0.
    unfold field_at.
    replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (legal_alignas_type t = true))
      with (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
      by (apply pred_ext; normalize; congruence).
    normalize.
    clear v1 H2.
    induction f.
    + simpl. inversion H.
    + extensionality p.
      simpl;
      normalize.
      simpl in v2.
      revert v2; destruct (is_Fnil f) eqn:?; intros; [| destruct v2].
      - rewrite withspacer_spacer.
        unfold field_at.
        replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (legal_alignas_type t = true))
          with (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
          by (apply pred_ext; normalize; congruence).
        normalize.
      - rewrite withspacer_spacer.
        unfold field_at.
        replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (legal_alignas_type t = true))
          with (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
          by (apply pred_ext; normalize; congruence).
        normalize.
      - change (!! False) with FF.
        rewrite <- IHf; [reflexivity|].
        destruct f; inversion Heqb; reflexivity.
  } Unfocus.
  destruct (nested_legal_fieldlist t) eqn:H1.
  Focus 2. {
    clear H0.
    unfold field_at.
    replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (nested_legal_fieldlist t = true))
      with (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
      by (apply pred_ext; normalize; congruence).
    normalize.
    clear v1 H2.
    induction f.
    + simpl. inversion H.
    + extensionality p.
      simpl;
      normalize.
      simpl in v2.
      revert v2; destruct (is_Fnil f) eqn:?; intros; [| destruct v2].
      - rewrite withspacer_spacer.
        unfold field_at.
        replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (nested_legal_fieldlist t = true))
          with (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
          by (apply pred_ext; normalize; congruence).
        normalize.
      - rewrite withspacer_spacer.
        unfold field_at.
        replace (@prop (val -> mpred) (@LiftNatDed val mpred Nveric) (nested_legal_fieldlist t = true))
          with (@FF (val -> mpred) (@LiftNatDed val mpred Nveric))
          by (apply pred_ext; normalize; congruence).
        normalize.
      - change (!! False) with FF.
        rewrite <- IHf; [reflexivity|].
        destruct f; inversion Heqb; reflexivity.
  } Unfocus.
  unfold field_at.
  unfold nested_field_type2, nested_field_offset2 in *.
  valid_nested_field_rec t gfs H1; inversion H0; clear H5. subst t0.
  revert v1 H2 H4.
  simpl reptype; simpl data_at'.
  change f with (fieldlist_app Fnil f) at 4 6.
  generalize Fnil as f';  intros.
  revert f' H4;
  induction f; intros.
  + inversion H.
  + pose proof nested_field_rec_Tunion_mid i0 t0 t gfs i f' f a ofs H3 H1 H4.
    revert v1 v2 H2.
    simpl.
    destruct (is_Fnil f) eqn:?; intros.
    - unfold field_at.
      repeat rewrite withspacer_spacer.
      revert v2 H2.
      simpl nested_reptype_unionlist.
      unfold nested_field_type2, nested_field_offset2 in *.
      rewrite H4, H0; intros. 
      rewrite H2.
      extensionality p.
      assert (legal_nested_field t gfs <-> legal_nested_field t (UnionField i0 :: gfs)).
      Focus. {
        eapply iff_trans; [| apply iff_sym, legal_nested_field_cons_lemma].
        simpl.
        unfold nested_field_type2; rewrite H4.
        split; [| tauto].
        intros; split; [tauto |].
        rewrite fieldlist_app_field_type_isOK.
        destruct (isOK (field_type i0 f')); simpl; try if_tac; try congruence; reflexivity.
      } Unfocus.
      match goal with
      | |- _ && _ && (?P (?A /\ ?B /\ ?C)) && _ = _ =>
        replace (P (A /\ B /\ C)) with (P (A /\ B /\ legal_nested_field t (UnionField i0 :: gfs)))
          by (apply pred_ext; normalize; tauto)
      end.
      apply pred_ext; simpl; normalize.
    - unfold field_at.
      revert v2 H2.
      simpl nested_reptype_unionlist.
      unfold nested_field_type2, nested_field_offset2.
      assert (reptype_unionlist f = nested_reptype_unionlist t gfs f).
        apply (nested_reptype_unionlist_lemma t gfs i (fieldlist_app f' (Fcons i0 t0 Fnil)) f a ofs).
        rewrite <- fieldlist_app_Fcons; auto.
        auto.
      rewrite H0, H4; intros. 
      solve_JMeq_sumtype H5.
      * rewrite H5.
        repeat rewrite withspacer_spacer.
        extensionality p.
        assert (legal_nested_field t gfs <-> legal_nested_field t (UnionField i0 :: gfs)).
        Focus. {
          eapply iff_trans; [| apply iff_sym, legal_nested_field_cons_lemma].
          simpl.
          unfold nested_field_type2; rewrite H4.
          split; [| tauto].
          intros; split; [tauto |].
          rewrite fieldlist_app_field_type_isOK.
          destruct (isOK (field_type i0 f')); simpl; try if_tac; try congruence; reflexivity.
        } Unfocus.
        match goal with
        | |- _ && _ && (?P (?A /\ ?B /\ ?C)) && _ = _ =>
          replace (P (A /\ B /\ C)) with (P (A /\ B /\ legal_nested_field t (UnionField i0 :: gfs)))
            by (apply pred_ext; normalize; tauto)
        end.
        apply pred_ext; simpl; normalize.
      * simpl in IHf. rewrite <- IHf with (v1 := r) (f' := (fieldlist_app f' (Fcons i0 t0 Fnil))); auto.
        rewrite <- fieldlist_app_Fcons. auto.
        destruct f; [inversion Heqb | simpl; auto].
        rewrite <- fieldlist_app_Fcons. auto.
Transparent sizeof.
Qed.

Lemma data_at_field_at: forall sh t, data_at sh t = field_at sh t nil.
Proof.
  intros.
  unfold data_at, field_at.
  extensionality v p; simpl.
  pose proof legal_nested_field_nil_lemma t.
  apply pred_ext; normalize.
Qed.

Lemma data_at__field_at_: forall sh t, data_at_ sh t = field_at_ sh t nil.
Proof.
  intros.
  unfold data_at_, field_at_.
  rewrite data_at_field_at.
  reflexivity.
Qed.

Lemma data_at_field_at_cancel:
  forall sh t v p, data_at sh t v p |-- field_at sh t nil v p.
Proof. intros; rewrite data_at_field_at; auto. Qed.

Lemma field_at_data_at_cancel:
  forall sh t v p, field_at sh t nil v p |-- data_at sh t v p.
Proof. intros; rewrite data_at_field_at; auto. Qed.

Lemma field_at_data_at: forall sh t gfs v p,
  field_at sh t gfs v p =
  data_at sh (nested_field_type2 t gfs) v (field_address t gfs p).
Proof.
  intros.
  unfold field_at.
  unfold field_address.
  if_tac.
  + unfold field_compatible in H.
    destruct H as [? [? [? [? [? ?]]]]].
    unfold data_at.
    simpl.
    rewrite <- at_offset'_eq by (rewrite <- data_at'_offset_zero; reflexivity).
    rewrite <- data_at'_at_offset'; [ |
      apply (nested_field_type2_nest_pred eq_refl), H0 |
      apply nested_field_offset2_type2_divide, H0].
    apply pred_ext; normalize.
    apply andp_right; [| apply derives_refl].
    apply prop_right.
    repeat (try assumption; split).
    - apply (nested_field_type2_nest_pred eq_refl), H1.
    - apply size_compatible_nested_field; assumption.
    - apply align_compatible_nested_field; assumption.
    - apply (nested_field_type2_nest_pred eq_refl), H0.
  + simpl.
    rewrite data_at'_isptr.
    normalize.
    unfold field_compatible in H.
    match goal with
    | |- ?A && _ = _ => replace A with (@FF mpred Nveric) by (apply pred_ext; normalize; tauto)
    end.
    rewrite data_at_isptr.
    simpl.
    change (!!False) with FF.
    normalize.
Qed.

Lemma field_at__data_at_: forall sh t gfs p,
  field_at_ sh t gfs p = 
  data_at_ sh (nested_field_type2 t gfs) (field_address t gfs p).
Proof.
  intros.
  unfold field_at_, data_at_.
  apply field_at_data_at.
Qed.

Lemma lifted_field_at_data_at: forall sh t gfs v p,
  `(field_at sh t gfs) v p =
  `(data_at sh (nested_field_type2 t gfs)) v (`(field_address t gfs) p).
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at_data_at.
Qed.

Lemma lifted_field_at__data_at_: forall sh t gfs p,
  `(field_at_ sh t gfs) p =
  `(data_at_ sh (nested_field_type2 t gfs)) (`(field_address t gfs) p).
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at__data_at_.
Qed.

Lemma field_at_compatible:
  forall sh t path v c,
     field_at sh t path v c |-- !! field_compatible t path c.
Proof.
  intros.
  rewrite field_at_data_at.
  rewrite data_at_isptr.
  unfold field_address.
  if_tac.
  + normalize.
  + normalize.
Qed.

Lemma field_at_compatible':
 forall sh t path v c,
     field_at sh t path v c =
     !! field_compatible t path c && field_at sh t path v c.
Proof.
intros.
apply pred_ext.
apply andp_right.
apply field_at_compatible.
auto.
normalize.
Qed.

Hint Resolve field_at_compatible : saturate_local.

Lemma data_at_compatible: forall sh t v p, data_at sh t v p |-- !! field_compatible t nil p.
Proof. intros.
 rewrite data_at_field_at; apply field_at_compatible.
Qed.
Hint Resolve data_at_compatible : saturate_local.

Lemma data_at__compatible: forall sh t p, data_at_ sh t p |-- !! field_compatible t nil p.
Proof. intros.
 unfold data_at_. apply data_at_compatible.
Qed.
Hint Resolve data_at__compatible : saturate_local.

Lemma field_at_isptr: forall sh t gfs v p,
  field_at sh t gfs v p = (!! isptr p) && field_at sh t gfs v p.
Proof. intros. apply local_facts_isptr. 
 eapply derives_trans; [ apply field_at_compatible | ].
 apply prop_derives; intros [? ?]; auto.
Qed.

Lemma field_at_offset_zero: forall sh t gfs v p,
  field_at sh t gfs v p = field_at sh t gfs v (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at_isptr; normalize.
Qed.

Lemma field_at__compatible: forall sh t gfs p,
  field_at_ sh t gfs p |-- !! field_compatible t gfs p.
Proof.
  intros.
  unfold field_at_.
  apply field_at_compatible.
Qed.
Hint Resolve field_at__compatible : saturate_local.

Lemma field_at__isptr: forall sh t gfs p,
  field_at_ sh t gfs p = (!! isptr p) && field_at_ sh t gfs p.
Proof. intros.
 unfold field_at_. apply field_at_isptr.
Qed.

Lemma field_at__offset_zero: forall sh t gfs p,
  field_at_ sh t gfs p = field_at_ sh t gfs (offset_val Int.zero p).
Proof. intros.
 unfold field_at_.
 apply field_at_offset_zero.
Qed.

Lemma field_at_field_at_: forall sh t gfs v p, 
  field_at sh t gfs v p |-- field_at_ sh t gfs p.
Proof.
  intros.
  destruct p; try (rewrite field_at_isptr, field_at__isptr; normalize; reflexivity).
  unfold field_at_, field_at.
  simpl; fold size_compatible.
  normalize.
  apply data_at'_data_at'_.
  + apply nested_field_type2_nest_pred; [reflexivity|exact H2].
  + pose proof nested_field_offset2_in_range t gfs H1.
    omega.
  + apply nested_field_offset2_type2_divide, H2.
  + eapply Zdivides_trans; [|exact H0].
    apply alignof_nested_field_type2_divide; auto.
Qed.

Hint Rewrite <- field_at_offset_zero: norm.
Hint Rewrite <- field_at__offset_zero: norm.
Hint Rewrite <- field_at_offset_zero: cancel.
Hint Rewrite <- field_at__offset_zero: cancel.

(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 1 (data_at _ _ _ _ |-- field_at _ _ nil _ _) =>
    (apply data_at_field_at_cancel) : cancel.

Hint Extern 1 (field_at _ _ nil _ _ |-- data_at _ _ _ _) =>
    (apply field_at_data_at_cancel) : cancel.

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at_ _ _ _ _) => 
   (apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at ?sh ?t ?gfs ?v _) => 
   (change (field_at sh t gfs v) with (field_at_ sh t gfs);
    apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at ?sh ?t ?gfs ?v _ |-- field_at_ _ _ _ _) => 
   (change (field_at sh t gfs v) with (field_at_ sh t gfs);
    apply derives_refl) : cancel.

(*
Lemma field_at_field_at: forall sh t gfs0 gfs1 v v' p,
  legal_alignas_type t = true ->
  JMeq v v' ->
  field_at sh t (gfs1 ++ gfs0) v p =
  (!! (size_compatible t p)) &&
  (!! (align_compatible t p)) &&
  (!! (legal_nested_field t (gfs1 ++ gfs0))) &&
  at_offset' (field_at sh (nested_field_type2 t gfs0) gfs1 v') (nested_field_offset2 t gfs0) p.
Proof.
  intros.
  rewrite at_offset'_eq; [| rewrite <- field_at_offset_zero; reflexivity].
  unfold field_at.
  simpl.
  revert v' H0.
  rewrite nested_field_type2_nested_field_type2.
  intros.
  rewrite <- H0.
  clear H0 v'.
  rewrite data_at'_at_offset'; 
   [ rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity]
   | apply nested_field_type2_nest_pred; simpl; auto
   | apply nested_field_offset2_type2_divide; auto].
  rewrite data_at'_at_offset' with (pos := (nested_field_offset2 (nested_field_type2 t gfs0) gfs1)); 
   [ rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity]
   | apply nested_field_type2_nest_pred; simpl; auto
   | rewrite <- nested_field_type2_nested_field_type2;
     apply nested_field_offset2_type2_divide; apply nested_field_type2_nest_pred; simpl; auto].
  apply pred_ext; normalize; rewrite <- nested_field_offset2_app; normalize.
  apply andp_right; [apply prop_right | apply derives_refl].
  split; [| split; split]; auto.
  + apply size_compatible_nested_field, H0.
    eapply legal_nested_field_app, H2.
  + apply align_compatible_nested_field, H1; auto.
    eapply legal_nested_field_app, H2.
  + apply legal_nested_field_app', H2.
Qed.
*)

(************************************************

Other lemmas

************************************************)

Lemma lower_andp_val:
  forall (P Q: val->mpred) v, 
  ((P && Q) v) = (P v && Q v).
Proof. reflexivity. Qed.

(*
Lemma mapsto_field_at:
  forall p p'  v' sh t structid fld fields (v: reptype
    (nested_field_lemmas.nested_field_type2 (Tstruct structid fields noattr)
       fld)),
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  p' = (field_address (Tstruct structid fields noattr) fld p) ->
  type_is_volatile t = false -> 
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! (legal_nested_field (Tstruct structid fields noattr) fld))
  && mapsto sh t p' v' = field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  rewrite field_at_data_at.
  remember v as v''; assert (JMeq v'' v) by (subst v; reflexivity); clear Heqv''.
  revert v H5; 
  pattern (nested_field_type2 (Tstruct structid fields noattr) fld) at 1 3.
  rewrite <- H0; intros.
  rewrite <- H1.
  subst t; erewrite by_value_data_at; [|exact H| rewrite H3, H5; reflexivity].
  rewrite H1.
  apply pred_ext; normalize; repeat apply andp_right.
  + apply prop_right; split; [| split].
    - unfold field_address.
      if_tac; [| simpl; auto].
      apply size_compatible_nested_field; tauto.
    - unfold field_address.
      if_tac; [| simpl; auto].
      apply align_compatible_nested_field; tauto.
    - apply (nested_field_type2_nest_pred); eauto.
  + rewrite <- H1. apply derives_refl.
  + unfold field_address.
    if_tac; [| rewrite mapsto_isptr; simpl; normalize].
    unfold field_compatible in H8; destruct H8 as [? [? [? [? ?]]]].
    normalize.
  + rewrite <- H1. apply derives_refl.
Qed.

Lemma mapsto__field_at_:
  forall p p' sh t structid fld fields,
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  p' = (field_address (Tstruct structid fields noattr) fld p) ->
  type_is_volatile t = false -> 
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! legal_nested_field (Tstruct structid fields noattr) fld)
  && mapsto_ sh t p'  = field_at_ sh (Tstruct structid fields noattr) fld p.
Proof.
  intros.
  eapply mapsto_field_at; eauto.
  rewrite <- H0; simpl.
  apply JMeq_sym, by_value_default_val, H.
Qed.

(*
Lemma splice_top_top: Share.splice Tsh Tsh = Tsh.
Proof.
unfold Share.splice.
unfold Share.Lsh, Share.Rsh.
change Share.top with Tsh.
case_eq (Share.split Tsh); intros L R ?.
simpl.
do 2 rewrite Share.rel_top1.
erewrite Share.split_together; eauto.
Qed.
*)

(*
Lemma by_value_access_mode_eq_type_eq: forall t t',
  type_is_by_value t ->
  access_mode t = access_mode t' ->
  t = t'.
Proof.
  intros.
  destruct t; [| destruct i, s, a| destruct s,a |destruct f | | | | | |];
  (destruct t'; [| destruct i, s, a| destruct s,a |destruct f | | | | | |]);
  simpl in *; inversion H0; try tauto.
*)

Lemma mapsto_field_at'':
  forall p p' v' sh ofs t structid fld fields (v: reptype (nested_field_type2 (Tstruct structid fields noattr) fld)),
  access_mode t = access_mode (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  nested_field_offset2 (Tstruct structid fields noattr) fld = ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  tc_val (nested_field_type2 (Tstruct structid fields noattr) fld) v' ->
  type_is_volatile (nested_field_type2 (Tstruct structid fields noattr) fld) = false ->
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p /\  align_compatible (Tstruct structid fields noattr) p /\ legal_nested_field (Tstruct structid fields noattr) fld)) 
  && mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  rewrite field_at_data_at.
  destruct (access_mode t) eqn:HH;
    try (unfold mapsto; rewrite HH; normalize; reflexivity).
  remember v' as v''; assert (JMeq v' v'') by (subst v'; reflexivity); clear Heqv''.
  assert (type_is_by_value t) by (destruct t; inversion HH; simpl; tauto).

  revert v' H6.
  pattern val at 1 2.
  erewrite <- by_value_reptype; [intros|exact H7].
  subst ofs.
(* rewrite <- H1; clear H1. *)
(*  erewrite by_value_data_at; [| exact H7|exact H6]. *)
  admit.
Qed.

Lemma mapsto_field_at':
  forall p p' v' sh ofs t structid fld fields (v: reptype (nested_field_type2 (Tstruct structid fields noattr) fld)),
  access_mode t = access_mode (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  nested_field_offset2 (Tstruct structid fields noattr) fld = ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  tc_val (nested_field_type2 (Tstruct structid fields noattr) fld) v' ->
  type_is_volatile (nested_field_type2 (Tstruct structid fields noattr) fld) = false ->
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  size_compatible (Tstruct structid fields noattr) p ->
  align_compatible (Tstruct structid fields noattr) p ->
  legal_nested_field (Tstruct structid fields noattr) fld -> 
  mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  eapply derives_trans; [ | eapply mapsto_field_at''; eassumption].
  normalize.
Qed.
*)
(*
Lemma field_at_nonvolatile:
  forall sh t fld v v', field_at sh t fld v' v = !!(type_is_volatile t = false) && field_at sh t fld v' v.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_at.
destruct t; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); try apply FF_left.
apply andp_left1.
apply prop_derives.
induction fld; simpl; auto.
Qed.

Lemma field_at__nonvolatile:
  forall sh t fld v, field_at_ sh t fld v = !!(type_is_volatile t = false) && field_at_ sh t fld v.
Proof.
 intros.
apply field_at_nonvolatile.
Qed.
*)

Lemma address_mapsto_overlap:
  forall rsh sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (Memdata.size_chunk ch1) a2 ->
     address_mapsto ch1 v1 rsh sh a1 * address_mapsto ch2 v2 rsh sh a2 |-- FF.
Proof.
 intros.
 apply res_predicates.address_mapsto_overlap.
 auto.
Qed.

Lemma mapsto_conflict:
 forall sh t v v2 v3,
 mapsto sh t v v2 * mapsto sh t v v3 |-- FF.
Proof.
intros.
unfold mapsto.
destruct (access_mode t); normalize.
destruct (type_is_volatile t); normalize.
pose proof (size_chunk_pos m).
destruct v; normalize.
rewrite distrib_orp_sepcon.
apply orp_left; normalize;
try (rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize;
      apply address_mapsto_overlap; split; auto; omega).
(*
rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize; intros;
apply address_mapsto_overlap; split; auto; omega.
*)
(* originally, this proof is neccesary. but it is not now. I don't know why.  - Qinxiang *)
Qed.

Lemma memory_block_conflict: forall sh n m p,
  0 < n <= Int.max_unsigned -> 0 < m <= Int.max_unsigned ->
  memory_block sh (Int.repr n) p * memory_block sh (Int.repr m) p |-- FF.
Proof.
  intros.
  destruct H, H0.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  destruct p; normalize.
  remember (nat_of_Z (Int.unsigned (Int.repr n))) as n' eqn:Hn.
  rewrite Int.unsigned_repr in Hn; [| split; omega].
  rewrite <- (nat_of_Z_eq n) in H; [|omega].
  rewrite <- Hn in H.
  destruct n'; simpl in H; [omega|].

  remember (nat_of_Z (Int.unsigned (Int.repr m))) as m' eqn:Hm.
  rewrite Int.unsigned_repr in Hm; [| split; omega].
  rewrite <- (nat_of_Z_eq m) in H0; [|omega].
  rewrite <- Hm in H0.
  destruct m'; simpl in H0; [omega|].
  simpl.
  unfold mapsto_.
  apply derives_trans with (mapsto sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr (Int.unsigned i)))
     Vundef * mapsto sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr (Int.unsigned i)))
      Vundef * TT).
  cancel.
  apply derives_trans with (FF * TT).
  apply sepcon_derives; [|cancel].
  apply mapsto_conflict.
  normalize.
Qed.

Lemma data_at_conflict: forall sh t v v' p,
  0 < sizeof t < Int.modulus ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives.
    apply data_at_data_at_; assumption.
    apply data_at_data_at_; assumption.
  + destruct (nested_non_volatile_type t) eqn:HH.
    - rewrite data_at__memory_block by (auto; omega).
      normalize.
      apply memory_block_conflict; (unfold Int.max_unsigned; omega).
    - unfold data_at_.
      eapply derives_trans; [apply sepcon_derives; apply data_at_non_volatile|].
      rewrite sepcon_prop_prop.
      rewrite HH.
      normalize.
      inversion H0.
Qed.

Lemma field_at_conflict: forall sh t fld p v v',
  0 < sizeof (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
  field_at sh t fld v p * field_at sh t fld v' p|-- FF.
Proof.
  intros.
  repeat (rewrite field_at_data_at; try assumption).
  repeat rewrite lower_andp_val.
  repeat (rewrite at_offset'_eq; [|rewrite <- data_at_offset_zero; reflexivity]).
  normalize.
  apply data_at_conflict; try assumption.
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  0 < sizeof (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
        field_at_ sh t fld p
        * field_at_ sh t fld p |-- FF.
Proof.
intros.
apply field_at_conflict; assumption.
Qed.

Lemma field_compatible_isptr :
  forall t path p, field_compatible t path p -> isptr p.
Proof.
intros. destruct H; auto.
Qed.

Lemma field_compatible0_isptr :
  forall t path p, field_compatible0 t path p -> isptr p.
Proof.
intros. destruct H; auto.
Qed.

Hint Extern 1 (isptr _) => (eapply field_compatible_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_isptr; eassumption).

Lemma field_compatible_offset_isptr:
forall t path n c, field_compatible t path (offset_val n c) ->
          isptr c.
Proof.
intros.
destruct H as [? _]. destruct c; try contradiction; auto.
Qed.

Lemma field_compatible0_offset_isptr:
forall t path n c, field_compatible t path (offset_val n c) ->
          isptr c.
Proof.
intros.
destruct H as [? _]. destruct c; try contradiction; auto.
Qed.

Hint Extern 1 (isptr _) => (eapply field_compatible_offset_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_offset_isptr; eassumption).

Lemma is_pointer_or_null_field_address_lemma:
 forall t path p,
   is_pointer_or_null (field_address t path p) =
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; apply prop_ext; intuition.
Qed.

Lemma isptr_field_address_lemma:
 forall t path p,
   isptr (field_address t path p) =
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; apply prop_ext; intuition.
Qed.

Hint Rewrite is_pointer_or_null_field_address_lemma : entailer_rewrite.
Hint Rewrite isptr_field_address_lemma : entailer_rewrite.

