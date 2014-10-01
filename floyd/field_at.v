Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.type_id_env.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(************************************************

Definition of nested_reptype_structlist, field_at, nested_sfieldlist_at

************************************************)

Fixpoint nested_reptype_structlist (t: type) (ids: list ident) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons i _ fld' =>
    if (is_Fnil fld')
    then reptype (nested_field_type2 t (i :: ids))
    else prod (reptype (nested_field_type2 t (i :: ids))) (nested_reptype_structlist t ids fld')
  end.

Fixpoint nested_reptype_unionlist (t: type) (ids: list ident) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons i _ fld' =>
    if (is_Fnil fld')
    then reptype (nested_field_type2 t (i :: ids))
    else sum (reptype (nested_field_type2 t (i :: ids))) (nested_reptype_unionlist t ids fld')
  end.

Lemma nested_reptype_lemma: forall t ids t0, nested_field_type t ids = Some t0 -> reptype t0 = reptype (nested_field_type2 t ids).
Proof.
  unfold nested_field_type, nested_field_type2.
  intros.
  destruct (nested_field_rec t ids) as [(ofs', t')|] eqn:HH.
  + inversion H.
    reflexivity.
  + inversion H.
Defined.

Lemma nested_reptype_structlist_lemma: forall t ids i f' f a ofs,
  nested_field_rec t ids = Some (ofs, Tstruct i (fieldlist_app f' f) a) ->
  nested_legal_fieldlist t = true ->
  reptype_structlist f = nested_reptype_structlist t ids f.
Proof.
  intros.
  assert (nested_field_type2 t ids = Tstruct i (fieldlist_app f' f) a).
    unfold nested_field_type2. rewrite H. reflexivity.
  eapply (nested_field_type2_nest_pred eq_refl t ids), nested_pred_atom_pred in H0.
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
      rewrite (nested_reptype_lemma t (i0 :: ids) t0).
      rewrite fieldlist_app_Fcons in H0, H.
      rewrite (IHf _ H H0).
      reflexivity.
      * unfold nested_field_type.
        simpl.
        rewrite H.
        solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 (Fcons i1 t1 f)));
        inversion H1; reflexivity.
Defined.

Lemma nested_reptype_structlist_lemma2: forall t ids i f a,
  nested_field_type2 t ids = Tstruct i f a ->
  nested_legal_fieldlist t = true ->
  reptype (nested_field_type2 t ids) = nested_reptype_structlist t ids f.
Proof.
  intros.
  rewrite H. simpl.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t ids H.
  apply (nested_reptype_structlist_lemma _ _ i Fnil f a ofs); simpl; [|exact H0].
  unfold nested_field_type2 in H.
  unfold nested_field_type.
  valid_nested_field_rec t ids H; inversion H1.
  subst.
  reflexivity.
Defined.

Lemma nested_reptype_unionlist_lemma: forall t ids i f' f a ofs,
  nested_field_rec t ids = Some (ofs, Tunion i (fieldlist_app f' f) a) ->
  nested_legal_fieldlist t = true ->
  reptype_unionlist f = nested_reptype_unionlist t ids f.
Proof.
  intros.
  assert (nested_field_type2 t ids = Tunion i (fieldlist_app f' f) a).
    unfold nested_field_type2. rewrite H. reflexivity.
  eapply (nested_field_type2_nest_pred eq_refl t ids), nested_pred_atom_pred in H0.
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
      rewrite (nested_reptype_lemma t (i0 :: ids) t0).
      rewrite fieldlist_app_Fcons in H0, H.
      rewrite (IHf _ H H0).
      reflexivity.
      * unfold nested_field_type.
        simpl.
        rewrite H.
        solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 (Fcons i1 t1 f)));
        inversion H1; reflexivity.
Defined.

Lemma nested_reptype_unionlist_lemma2: forall t ids i f a,
  nested_field_type2 t ids = Tunion i f a ->
  nested_legal_fieldlist t = true ->
  reptype (nested_field_type2 t ids) = nested_reptype_unionlist t ids f.
Proof.
  intros.
  rewrite H. simpl.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t ids H.
  apply (nested_reptype_unionlist_lemma _ _ i Fnil f a ofs); simpl; [|exact H0].
  unfold nested_field_type2 in H.
  unfold nested_field_type.
  valid_nested_field_rec t ids H; inversion H1.
  subst.
  reflexivity.
Defined.

Definition field_at (sh: Share.t) (t: type) (ids: list ident) (v: reptype (nested_field_type2 t ids)) : val -> mpred := 
  (fun p => (!! (size_compatible t p /\ align_compatible t p /\ isSome (nested_field_rec t ids)))) 
  && data_at' sh empty_ti (nested_field_type2 t ids) (nested_field_offset2 t ids) v.
Arguments field_at sh t ids v p : simpl never.

Definition field_at_ (sh: Share.t) (t: type) (ids: list ident) : val -> mpred :=
  field_at sh t ids (default_val (nested_field_type2 t ids)).
Arguments field_at_ sh t ids p : simpl never.

Fixpoint nested_sfieldlist_at (sh: Share.t) (t1: type) (ids: list ident) (flds: fieldlist) (v: nested_reptype_structlist t1 ids flds) : val -> mpred := 
  match flds as f return (nested_reptype_structlist t1 ids f -> val -> mpred) with
  | Fnil => fun _ p => (!! isptr p) && emp
  | Fcons i t flds0 =>
    fun (v : nested_reptype_structlist t1 ids (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          ((if b
            then reptype (nested_field_type2 t1 (i :: ids))
            else ((reptype (nested_field_type2 t1 (i :: ids)) *
        nested_reptype_structlist t1 ids flds0)%type)) -> val -> mpred)
       then
        fun (v0: reptype (nested_field_type2 t1 (i :: ids))) =>
          withspacer sh (nested_field_offset2 t1 (i :: ids) + sizeof (nested_field_type2 t1 (i :: ids))) 
(align (nested_field_offset2 t1 (i :: ids) + sizeof (nested_field_type2 t1 (i :: ids))) (alignof (nested_field_type2 t1 ids))) (field_at sh t1 (i :: ids) v0)
       else
        fun (v0: ((reptype (nested_field_type2 t1 (i :: ids)) *
        nested_reptype_structlist t1 ids flds0)%type)) =>
          withspacer sh (nested_field_offset2 t1 (i :: ids) + sizeof (nested_field_type2 t1 (i :: ids)))
(align (nested_field_offset2 t1 (i :: ids) + sizeof (nested_field_type2 t1 (i :: ids))) (alignof_hd flds0) ) (field_at sh t1 (i :: ids) (fst v0)) *
          (nested_sfieldlist_at sh t1 ids flds0 (snd v0)))
    v
  end v.

Fixpoint nested_ufieldlist_at (sh: Share.t) (t1: type) (ids: list ident) (flds: fieldlist) (v: nested_reptype_unionlist t1 ids flds) : val -> mpred := 
  match flds as f return (nested_reptype_unionlist t1 ids f -> val -> mpred) with
  | Fnil => fun _ p => (!! isptr p) && emp
  | Fcons i t flds0 =>
    fun (v : nested_reptype_unionlist t1 ids (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          ((if b
            then reptype (nested_field_type2 t1 (i :: ids))
            else ((reptype (nested_field_type2 t1 (i :: ids)) +
        nested_reptype_unionlist t1 ids flds0)%type)) -> val -> mpred)
       then
         fun (v0: reptype (nested_field_type2 t1 (i :: ids))) =>
           withspacer sh (nested_field_offset2 t1 (i :: ids) + 
             sizeof (nested_field_type2 t1 (i :: ids)))  
             (nested_field_offset2 t1 ids + sizeof (nested_field_type2 t1 ids)) 
             (field_at sh t1 (i :: ids) v0)
       else
        fun (v0: ((reptype (nested_field_type2 t1 (i :: ids)) +
          nested_reptype_unionlist t1 ids flds0)%type)) =>
        match v0 with
        | inl v0' => withspacer sh (nested_field_offset2 t1 (i :: ids) + 
            sizeof (nested_field_type2 t1 (i :: ids))) 
            (nested_field_offset2 t1 ids + sizeof (nested_field_type2 t1 ids))
            (field_at sh t1 (i :: ids) v0')
        | inr v0' => nested_ufieldlist_at sh t1 ids flds0 v0'
        end)
    v
  end v.

Lemma eqb_fieldlist_true: forall f1 f2, eqb_fieldlist f1 f2 = true -> f1 = f2.
Proof.
  intros.
  revert f2 H; induction f1; intros; destruct f2; simpl in *.
  + reflexivity.
  + inversion H.
  + inversion H.
  + apply andb_true_iff in H.
    destruct H.
    apply andb_true_iff in H0.
    destruct H0.
    apply IHf1 in H1.
    apply eqb_type_true in H0.
    apply eqb_ident_spec in H.
    subst; reflexivity.
Qed.   

Opaque alignof.

Lemma field_at_Tstruct: forall sh t ids i f a v1 v2,
  eqb_fieldlist f Fnil = false ->
  nested_field_type2 t ids = Tstruct i f a ->
  nested_legal_fieldlist t = true ->
  JMeq v1 v2 ->
  legal_alignas_type t = true ->
  field_at sh t ids v1 = nested_sfieldlist_at sh t ids f v2.
Proof.
  intros.
  unfold field_at.
  unfold nested_field_type2, nested_field_offset2 in *.
  valid_nested_field_rec t ids H1; inversion H0; clear H5. subst t0.
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
    apply pred_ext; simpl; normalize.
  + assert (is_Fnil (Fcons i0 t0 f) = false) by reflexivity.
    remember (Fcons i0 t0 f) as f''.
    revert v1 v2 H2.
    simpl reptype_structlist. simpl nested_reptype_structlist.
    simpl sfieldlist_at'. simpl nested_sfieldlist_at.
    rewrite H5; intros.
    extensionality p.
    assert (Heq_fst: reptype t1 = reptype (nested_field_type2 t (i1 :: ids))).
      unfold nested_field_type2; rewrite H0; reflexivity.
    assert (Heq_snd: reptype_structlist f'' = nested_reptype_structlist t ids f'').
      rewrite fieldlist_app_Fcons in H4.
      apply (nested_reptype_structlist_lemma t ids i _ _ a _ H4 H1).
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
    assert (nested_field_rec t (i0 :: ids) = 
      Some (align (ofs0 + sizeof t1) (alignof_hd (Fcons i0 t0 f)), t0)); [simpl alignof_hd; apply (nested_field_rec_Tstruct_mid i1 t1 t1 i0 t0 t ids i f' f a ofs ofs0); assumption|].
    rewrite fieldlist_app_Fcons in *.
    erewrite <- IHf; [| | exact H2 | exact H_snd |exact H4].
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

Lemma JMeq_sumtype_ll: forall A B C D x y, A = C -> B = D -> 
  (@JMeq (A + B) (inl x) (C + D) (inl y)) ->
  JMeq x y.
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
  reflexivity.
Qed.

Lemma JMeq_sumtype_rr: forall A B C D x y, A = C -> B = D -> 
  (@JMeq (A + B) (inr x) (C + D) (inr y)) ->
  JMeq x y.
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
  reflexivity.
Qed.

Lemma JMeq_sumtype_lr: forall A B C D x y, A = C -> B = D -> ~ (@JMeq (A + B) (inl x) (C + D) (inr y)).
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
Qed.

Lemma JMeq_sumtype_rl: forall A B C D x y, A = C -> B = D -> ~ (@JMeq (A + B) (inr x) (C + D) (inl y)).
Proof.
  unfold not.
  intros.
  subst.
  apply JMeq_eq in H1.
  inversion H1.
Qed.

Ltac solve_JMeq_sumtype H :=
  match type of H with
  | JMeq ?x ?y =>
    destruct x; destruct y;
     [apply JMeq_sumtype_ll in H; auto
     |apply JMeq_sumtype_lr in H; auto; inversion H
     |apply JMeq_sumtype_rl in H; auto; inversion H
     |apply JMeq_sumtype_rr in H; auto]
  end.

Lemma field_at_Tunion: forall sh t ids i f a v1 v2,
  eqb_fieldlist f Fnil = false ->
  nested_field_type2 t ids = Tunion i f a ->
  nested_legal_fieldlist t = true ->
  JMeq v1 v2 ->
  legal_alignas_type t = true ->
  field_at sh t ids v1 = nested_ufieldlist_at sh t ids f v2.
Proof.
Opaque sizeof.
  intros.
  unfold field_at.
  unfold nested_field_type2, nested_field_offset2 in *.
  valid_nested_field_rec t ids H1; inversion H0; clear H5. subst t0.
  revert v1 H2 H4.
  simpl reptype; simpl data_at'.
  change f with (fieldlist_app Fnil f) at 4 7.
  generalize Fnil as f';  intros.
  revert f' H4;
  induction f; intros.
  + inversion H.
  + pose proof nested_field_rec_Tunion_mid i0 t0 t ids i f' f a ofs H3 H1 H4.
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
      apply pred_ext; simpl; normalize.
    - unfold field_at.
      revert v2 H2.
      simpl nested_reptype_unionlist.
      unfold nested_field_type2, nested_field_offset2.
      assert (reptype_unionlist f = nested_reptype_unionlist t ids f).
        apply (nested_reptype_unionlist_lemma t ids i (fieldlist_app f' (Fcons i0 t0 Fnil)) f a ofs).
        rewrite <- fieldlist_app_Fcons; auto.
        auto.
      rewrite H0, H4; intros. 
      solve_JMeq_sumtype H5.
      * rewrite H5.
        repeat rewrite withspacer_spacer.
        extensionality p.
        apply pred_ext; simpl; normalize.
      * simpl in IHf. rewrite <- IHf with (v1 := r) (f' := (fieldlist_app f' (Fcons i0 t0 Fnil))); auto.
        rewrite <- fieldlist_app_Fcons. auto.
        destruct f; [inversion Heqb | simpl; auto].
        rewrite <- fieldlist_app_Fcons. auto.
Qed.

Lemma data_at_field_at: forall sh t, data_at sh t = field_at sh t nil.
Proof.
  intros.
  unfold data_at, field_at.
  extensionality v p; simpl.
  apply pred_ext; normalize.
Qed.

Lemma field_at_data_at: forall sh t ids v p,
  legal_alignas_type t = true ->
  field_at sh t ids v p = 
  (!! (size_compatible t p)) &&  
  (!! (align_compatible t p)) &&
  (!! (isSome (nested_field_rec t ids))) && 
  at_offset' (data_at sh (nested_field_type2 t ids) v) (nested_field_offset2 t ids) p.
Proof.
  intros.
  unfold field_at.
  rewrite <- data_at'_data_at; [simpl |
    apply (nested_field_type2_nest_pred eq_refl), H |
    apply nested_field_offset2_type2_divide, H].
  apply pred_ext; normalize.
  apply andp_right.
  apply prop_right.
  repeat split; try assumption.
  apply size_compatible_nested_field; exact H0.
  apply align_compatible_nested_field; auto.
  apply derives_refl.
Qed.

Lemma field_at__data_at_: forall sh t ids p,
  legal_alignas_type t = true ->
  field_at_ sh t ids p = 
  (!! (size_compatible t p)) &&  
  (!! (align_compatible t p)) &&
  (!! (isSome (nested_field_rec t ids))) && 
  at_offset' (data_at_ sh (nested_field_type2 t ids)) (nested_field_offset2 t ids) p.
Proof.
  intros.
  unfold field_at_, data_at_.
  apply field_at_data_at, H.
Qed.

Lemma lifted_field_at_data_at: forall sh t ids v p,
       legal_alignas_type t = true ->
       `(field_at sh t ids) v p =
       `prop (`(size_compatible t) p) && 
       `prop (`(align_compatible t) p) && 
       `prop (`(isSome (nested_field_rec t ids))) &&
       `(at_offset') (fun rho => (data_at sh (nested_field_type2 t ids)) (v rho))
         `(nested_field_offset2 t ids) p.
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at_data_at, H.
Qed.

Lemma lifted_field_at__data_at_: forall sh t ids p,
       legal_alignas_type t = true ->
       `(field_at_ sh t ids) p =
       `prop (`(size_compatible t) p) && 
       `prop (`(align_compatible t) p) && 
       `prop (`(isSome (nested_field_rec t ids))) &&
       `(at_offset' (data_at_ sh (nested_field_type2 t ids))
         (nested_field_offset2 t ids)) p.
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at__data_at_, H.
Qed.

Lemma nested_field_type2_nested_field_type2: forall t ids0 ids1,
  nested_field_type2 (nested_field_type2 t ids0) ids1 = nested_field_type2 t (ids1 ++ ids0).
Proof.
  intros.
  destruct (isSome_dec (nested_field_rec t (ids1 ++ ids0))).
  + pose proof nested_field_rec_app_isSome _ _ _ i.
    pose proof nested_field_rec_app_isSome' _ _ _ i.
    unfold nested_field_type2 in *.
    valid_nested_field_rec t (ids1 ++ ids0) i.
    valid_nested_field_rec t ids0 H.
    valid_nested_field_rec t1 ids1 H0.
    pose proof nested_field_rec_app _ _ _ _ _ _ _ H2 H3.
    rewrite H1 in H4.
    inversion H4.
    reflexivity.
  + unfold nested_field_type2.
    destruct (nested_field_rec t ids0) as [[? ?]|] eqn:?H.
    - destruct (nested_field_rec t0 ids1) as [[? ?]|] eqn:?H.
      * rewrite (nested_field_rec_app _ _ _ _ _ _ _ H H0). reflexivity.
      * destruct (nested_field_rec t (ids1 ++ ids0)); [simpl in n; tauto |].
        reflexivity.
    - destruct (nested_field_rec t (ids1 ++ ids0)); [simpl in n; tauto |].
      induction ids1.
      * reflexivity.
      * simpl.
        destruct (nested_field_rec Tvoid ids1) as [[? ?]|]; inversion IHids1; reflexivity.
Qed.

Lemma field_at_local_facts: forall sh t ids v p,
  field_at sh t ids v p |-- !! isptr p.
Proof.
  intros.
  unfold field_at. simpl. apply andp_left2.
  apply data_at'_local_facts.
Qed.

Hint Resolve field_at_local_facts : saturate_local.
(*
Hint Extern 2 (@derives _ _ _ _) => 
   simple eapply field_at_local_facts; reflexivity : saturate_local.
*)

Lemma field_at_isptr: forall sh t ids v p,
  field_at sh t ids v p = (!! isptr p) && field_at sh t ids v p.
Proof. intros. apply local_facts_isptr. apply field_at_local_facts. Qed.

Lemma field_at_offset_zero: forall sh t ids v p,
  field_at sh t ids v p = field_at sh t ids v (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero. apply field_at_local_facts. Qed.

Lemma field_at__local_facts: forall sh t ids p,
  field_at_ sh t ids p |-- !! isptr p.
Proof.
  intros.
  unfold field_at_.
  apply field_at_local_facts.
Qed.

Hint Resolve field_at__local_facts : saturate_local.
(*
Hint Extern 2 (@derives _ _ _ _) => 
   simple eapply field_at__local_facts; reflexivity : saturate_local.
*)

Lemma field_at__isptr: forall sh t ids p,
  field_at_ sh t ids p = (!! isptr p) && field_at_ sh t ids p.
Proof. intros. apply local_facts_isptr. apply field_at__local_facts. Qed.

Lemma field_at__offset_zero: forall sh t ids p,
  field_at_ sh t ids p = field_at_ sh t ids (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero. apply field_at__local_facts. Qed.

Lemma field_at_field_at_: forall sh t ids v p, 
  legal_alignas_type t = true -> 
  field_at sh t ids v p |-- field_at_ sh t ids p.
Proof.
  intros.
  destruct p; try (rewrite field_at_isptr, field_at__isptr; normalize; reflexivity).
  unfold field_at_, field_at.
  simpl; fold size_compatible.
  normalize.
  apply data_at'_data_at'_.
  + apply nested_field_type2_nest_pred; [reflexivity|exact H].
  + pose proof nested_field_offset2_in_range t ids H2.
    omega.
  + apply nested_field_offset2_type2_divide, H.
  + eapply Zdivides_trans; [|exact H1].
    apply alignof_nested_field_type2_divide; auto.
Qed.

Hint Rewrite <- field_at_offset_zero: norm.
Hint Rewrite <- field_at__offset_zero: norm.
Hint Rewrite <- field_at_offset_zero: cancel.
Hint Rewrite <- field_at__offset_zero: cancel.

Hint Resolve field_at_field_at_: cancel.

Lemma field_at_field_at: forall sh t ids0 ids1 v v' p,
  legal_alignas_type t = true ->
  JMeq v v' ->
  field_at sh t (ids1 ++ ids0) v p =
  (!! (size_compatible t p)) &&  
  (!! (align_compatible t p)) &&
  (!! (isSome (nested_field_rec t (ids1 ++ ids0)))) && 
  at_offset' (field_at sh (nested_field_type2 t ids0) ids1 v') (nested_field_offset2 t ids0) p.
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
  rewrite data_at'_at_offset' with (pos := (nested_field_offset2 (nested_field_type2 t ids0) ids1)); 
   [ rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity]
   | apply nested_field_type2_nest_pred; simpl; auto
   | rewrite <- nested_field_type2_nested_field_type2;
     apply nested_field_offset2_type2_divide; apply nested_field_type2_nest_pred; simpl; auto].
  apply pred_ext; normalize; rewrite <- nested_field_offset2_app; normalize.
  apply andp_right; [apply prop_right | apply derives_refl].
  repeat split; auto.
  + apply size_compatible_nested_field, H0.
  + apply align_compatible_nested_field, H1; auto.
  + apply nested_field_rec_app_isSome', H2.
Qed.

(************************************************

Other lemmas

************************************************)

Lemma lower_andp_val:
  forall (P Q: val->mpred) v, 
  ((P && Q) v) = (P v && Q v).
Proof. reflexivity. Qed.

Lemma mapsto_field_at:
  forall p p'  v' sh ofs t structid fld fields (v: reptype
    (nested_field_lemmas.nested_field_type2 (Tstruct structid fields noattr)
       fld)),
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  nested_field_offset2 (Tstruct structid fields noattr) fld = ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  type_is_volatile t = false -> 
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! (isSome (nested_field_rec (Tstruct structid fields noattr) fld))) 
  && mapsto sh t p' v' = field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  rewrite field_at_data_at; [|exact H5].
  remember v as v''; assert (JMeq v'' v) by (subst v; reflexivity); clear Heqv''.
  revert v H6; 
  pattern (nested_field_type2 (Tstruct structid fields noattr) fld) at 1 3.
  rewrite <- H0; intros.
  rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
  subst ofs.
  rewrite <- H2.
  subst t; erewrite by_value_data_at; [|exact H| rewrite H4, H6; reflexivity].
  rewrite H2.
  apply pred_ext; normalize; repeat apply andp_right.
  + apply prop_right; split. 
    apply size_compatible_nested_field; tauto.
    apply align_compatible_nested_field; tauto.
  + rewrite <- H2. rewrite <- mapsto_offset_zero.
    cancel.
  + rewrite <- H2. rewrite <- mapsto_offset_zero.
    cancel.
Qed.

Lemma mapsto__field_at_:
  forall p p' sh ofs t structid fld fields,
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  nested_field_offset2 (Tstruct structid fields noattr) fld = ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  type_is_volatile t = false -> 
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! (isSome (nested_field_rec (Tstruct structid fields noattr) fld))) 
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
  (!! (size_compatible (Tstruct structid fields noattr) p /\  align_compatible (Tstruct structid fields noattr) p /\ isSome (nested_field_rec (Tstruct structid fields noattr) fld))) 
  && mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  rewrite field_at_data_at; [| exact H5].
  destruct (access_mode t) eqn:HH;
    try (unfold mapsto; rewrite HH; normalize; reflexivity).
  remember v' as v''; assert (JMeq v' v'') by (subst v'; reflexivity); clear Heqv''.
  assert (type_is_by_value t) by (destruct t; inversion HH; simpl; tauto).

  revert v' H6.
  pattern val at 1 2.
  erewrite <- by_value_reptype; [intros|exact H7].
  rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].  
  subst ofs.
  rewrite <- H1; clear H1.
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
  isSome (nested_field_rec (Tstruct structid fields noattr) fld) -> 
  mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  eapply derives_trans; [ | eapply mapsto_field_at''; eassumption].
  normalize.
Qed.

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
  sizeof t > 0 ->
  legal_alignas_type t = true ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives.
    apply data_at_data_at_; assumption.
    apply data_at_data_at_; assumption.
  + destruct (nested_non_volatile_type t) eqn:HH.
    - rewrite <- memory_block_data_at_; try assumption.
      normalize.
      apply memory_block_conflict; admit. (* can be proved by size_compatible *)
    - unfold data_at_.
      eapply derives_trans; [apply sepcon_derives; apply data_at_non_volatile|].
      rewrite sepcon_prop_prop.
      rewrite HH.
      normalize.
      inversion H1.
Qed.

Lemma field_at_conflict: forall sh t fld p v v',
  sizeof (nested_field_type2 t (fld::nil)) > 0 ->
  legal_alignas_type t = true ->
  field_at sh t (fld::nil) v p * field_at sh t (fld::nil) v' p|-- FF.
Proof.
  intros.
  repeat (rewrite field_at_data_at; try assumption).
  repeat rewrite lower_andp_val.
  repeat (rewrite at_offset'_eq; [|rewrite <- data_at_offset_zero; reflexivity]).
  normalize.
  apply data_at_conflict; try assumption.
  apply nested_field_type2_nest_pred; [
    reflexivity| exact H0].
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  sizeof (nested_field_type2 t (fld::nil)) > 0 ->
  legal_alignas_type t = true ->
        field_at_ sh t (fld::nil) p
        * field_at_ sh t (fld::nil) p |-- FF.
Proof.
intros.
apply field_at_conflict; assumption.
Qed.

