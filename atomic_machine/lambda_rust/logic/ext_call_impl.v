(** Language-generic implementations of the atomic-operation contracts. *)
From iris.proofmode Require Import proofmode.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Set Default Proof Using "Type".

Section language.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr}.
  Local Notation C := (@sqlang_thrd_st _ _ _ _ _ _ _ L).

  Class sq_pointsto_mixin `{!sqHeap L Σ} := {
    sq_compare : Val -> Val -> bool -> iProp Σ;
    sq_pointsto_load m ly l q v :
      sq_heap m -∗ sq_pointsto l q v -∗ ⌜load m l ly = Some v⌝;
    sq_pointsto_store_enabled m ly l v v' :
      sq_heap m -∗ sq_pointsto l 1 v -∗
        ⌜exists m', store m l ly v' = Some m'⌝;
    sq_pointsto_store m ly l v v' m' :
      store m l ly v' = Some m' ->
      sq_heap m -∗ sq_pointsto l 1 v ==∗
        sq_heap m' ∗ sq_pointsto l 1 v';
    sq_pointsto_fp_read ly l q v la :
      la ∈ layout_to_locs l ly -> sq_pointsto l q v ⊢ fp_own la false;
    sq_pointsto_fp_write ly l v la :
      la ∈ layout_to_locs l ly -> sq_pointsto l 1 v ⊢ fp_own la true;
    sq_compare_spec m v v' b :
      sq_heap m -∗ sq_compare v v' b -∗
        ⌜(sqlang_ValEq m v v' <-> b = true) /\
          (sqlang_ValNEq m v v' <-> b = false)⌝
  }.

  Section specs.
    Context `{!sqHeap L Σ, !sq_pointsto_mixin}.

    Definition sc_load_spec (ly : Layout) (l : Loc) : ExtSpec L Σ := {|
      ext_args := Qp * Val;
      ext_pre qv := cconst (sq_pointsto l qv.1 qv.2);
      ext_post qv ov := (⌜ov = Some qv.2⌝ ∗ sq_pointsto l qv.1 qv.2)%I
    |}.

    Definition sc_store_spec (ly : Layout) (l : Loc) (v : Val) : ExtSpec L Σ := {|
      ext_args := Val;
      ext_pre v' := cconst (sq_pointsto l 1 v');
      ext_post _ ov := (⌜ov = None⌝ ∗ sq_pointsto l 1 v)%I
    |}.

    Definition sc_cas_spec (ly : Layout) (l : Loc) (v_exp v_new : Val) : ExtSpec L Σ := {|
      ext_args := Val * bool;
      ext_pre x := cconst (sq_compare x.1 v_exp x.2 ∗
        sq_pointsto l 1 x.1)%I;
      ext_post x ov :=
        (⌜ov = Some (if x.2 then sqlang_true_val else sqlang_false_val)⌝ ∗
         sq_pointsto l 1 (if x.2 then v_new else x.1))%I
    |}.

    Local Instance sc_spawn_pre_ne (e : Expr) :
      NonExpansive (λ W : C -d> iPropO Σ, W (sqlang_expr_to_thrd_st e)).
    Proof. intros n W W' HW. apply HW. Qed.

    Definition sc_spawn_spec (e : Expr) : ExtSpec L Σ := {|
      ext_args := unit;
      ext_pre _ := OfeMor (λ W : C -d> iPropO Σ, W (sqlang_expr_to_thrd_st e));
      ext_post _ ov := ⌜ov = None⌝%I
    |}.

    Global Instance ext_specs : ExtSpecs L Σ | 20 := {| ext_spec := λ op,
      match op with
      | ALoad ly l => sc_load_spec ly l
      | AStore ly l v => sc_store_spec ly l v
      | ACAS ly l v_exp v_new => sc_cas_spec ly l v_exp v_new
      | ASpawn e => sc_spawn_spec e
      end |}.
  End specs.

  Section soundness.
    Context `{!sqHeap L Σ, !sq_pointsto_mixin}.

    Lemma sc_load_sound ly l : ext_call_soundness (sc_load_spec ly l) (ALoad ly l).
    Proof using Type*.
      split.
      - intros e k [q v] W m He. iIntros "Hl Hm".
        iDestruct (sq_pointsto_load _ ly with "Hm Hl") as %Hload.
        iPureIntro. do 4 eexists. eapply SC_Read; [exact He | exact Hload].
      - intros e k [q v] W m evs e' m' o He Hst. iIntros "Hl Hm".
        sqlang_ext_inv He Hst.
        iDestruct (sq_pointsto_load _ ly with "Hm Hl") as %Hv.
        rewrite Hload in Hv. injection Hv as ->.
        iModIntro. iExists (Some v). iFrame. by rewrite Hk.
      - intros e k [q v] W m evs e' m' o ev la w He Hst Hin Hacc. iIntros "Hl".
        sqlang_ext_inv He Hst.
        apply list_elem_of_singleton in Hin as ->. destruct Hacc as [Hla ->].
        by iApply (sq_pointsto_fp_read ly with "Hl").
    Qed.

    Lemma sc_store_sound ly l v :
      ext_call_soundness (sc_store_spec ly l v) (AStore ly l v).
    Proof using Type*.
      split.
      - intros e k v' W m He. iIntros "Hl Hm".
        iDestruct (sq_pointsto_store_enabled _ ly with "Hm Hl") as %(m' & Hstore).
        iPureIntro. do 4 eexists. eapply SC_Write; [exact He | exact Hstore].
      - intros e k v' W m evs e' m' o He Hst. iIntros "Hl Hm".
        sqlang_ext_inv He Hst.
        iMod (sq_pointsto_store _ ly with "Hm Hl") as "[Hm Hl]"; first exact Hstore.
        iModIntro. iExists None. iFrame. by rewrite Hk.
      - intros e k v' W m evs e' m' o ev la w He Hst Hin Hacc. iIntros "Hl".
        sqlang_ext_inv He Hst.
        apply list_elem_of_singleton in Hin as ->. destruct Hacc as [Hla ->].
        by iApply (sq_pointsto_fp_write ly with "Hl").
    Qed.

    Lemma sc_cas_sound ly l v_exp v_new :
      ext_call_soundness (sc_cas_spec ly l v_exp v_new) (ACAS ly l v_exp v_new).
    Proof.
      split.
      - intros e k [v b] W m He. iIntros "[Hcmp Hl] Hm".
        iDestruct (sq_pointsto_load _ ly with "Hm Hl") as %Hload.
        iDestruct (sq_compare_spec with "Hm Hcmp") as %[Heq Hneq].
        destruct b.
        + iDestruct (sq_pointsto_store_enabled _ ly with "Hm Hl") as %(m' & Hstore).
          iPureIntro. do 4 eexists. eapply SC_Cas_Suc;
            [exact He | exact Hload | exact (proj2 Heq eq_refl) | exact Hstore].
        + iPureIntro. do 4 eexists. eapply SC_Cas_Fail;
            [exact He | exact Hload | exact (proj2 Hneq eq_refl)].
      - intros e k [v b] W m evs e' m' o He Hst. iIntros "[Hcmp Hl] Hm".
        sqlang_ext_inv He Hst;
          iDestruct (sq_pointsto_load _ ly with "Hm Hl") as %Hv;
          rewrite Hload in Hv; injection Hv as ->;
          iDestruct (sq_compare_spec with "Hm Hcmp") as %[HcmpEq HcmpNeq].
        + have Hb : b = true := proj1 HcmpEq Heq. subst b.
          iMod (sq_pointsto_store _ ly with "Hm Hl") as "[Hm Hl]"; first exact Hstore.
          iModIntro. iExists (Some sqlang_true_val). iFrame. by rewrite Hk.
        + have Hb : b = false := proj1 HcmpNeq Hneq. subst b.
          iModIntro. iExists (Some sqlang_false_val). iFrame. by rewrite Hk.
      - intros e k [v b] W m evs e' m' o ev la w He Hst Hin Hacc. iIntros "[_ Hl]".
        sqlang_ext_inv He Hst;
          apply list_elem_of_singleton in Hin as ->; destruct Hacc as [Hla ->].
        + by iApply (sq_pointsto_fp_write ly with "Hl").
        + by iApply (sq_pointsto_fp_read ly with "Hl").
    Qed.

    Lemma sc_spawn_sound e_new : ext_call_soundness (sc_spawn_spec e_new) (ASpawn e_new).
    Proof.
      split.
      - intros e k [] W m He. iIntros "Hpre Hm". iPureIntro.
        do 4 eexists. by eapply Spawn.
      - intros e k [] W m evs e' m' o He Hst. iIntros "Hpre Hm".
        sqlang_ext_inv He Hst. iModIntro. iExists None. iFrame. by rewrite Hk.
      - intros e k [] W m evs e' m' o ev la w He Hst Hin Hacc.
        sqlang_ext_inv He Hst. by apply elem_of_nil in Hin.
    Qed.

    Lemma ext_sound op :
      ext_call_soundness (ext_spec (ExtSpecs := ext_specs) op) op.
    Proof.
      destruct op; [apply sc_load_sound | apply sc_store_sound |
        apply sc_cas_sound | apply sc_spawn_sound].
    Qed.

    Global Instance ext_specs_sound : ExtSpecsSound.
    Proof. exact ext_sound. Qed.
  End soundness.

  (** The standard contracts determine when an exposed call is atomic. *)
  Section atomicity.
    Context `{!sqHeap L Σ, !sq_pointsto_mixin}.

    Global Instance sc_load_atomic ly l k
        `{!(forall v, SqIntoVal (k (Some v)) v)} :
        SqAtomicExternal (ALoad ly l) k.
    Proof.
      intros [q v] ov. simpl. iIntros "[-> _]".
      iPureIntro. exists v. apply sq_into_val.
    Qed.

    Global Instance sc_store_atomic ly l v k vret
        `{!SqIntoVal (k None) vret} : SqAtomicExternal (AStore ly l v) k.
    Proof.
      intros v' ov. simpl. iIntros "[-> _]".
      iPureIntro. exists vret. apply sq_into_val.
    Qed.

    Global Instance sc_cas_atomic ly l v_exp v_new k
        `{!(forall v, SqIntoVal (k (Some v)) v)} :
        SqAtomicExternal (ACAS ly l v_exp v_new) k.
    Proof.
      intros [v b] ov. simpl. iIntros "[-> _]".
      iPureIntro. eexists. apply sq_into_val.
    Qed.

    Global Instance sc_spawn_atomic e_new k vret
        `{!SqIntoVal (k None) vret} : SqAtomicExternal (ASpawn e_new) k.
    Proof.
      intros [] ov. simpl. iIntros "->".
      iPureIntro. exists vret. apply sq_into_val.
    Qed.
  End atomicity.

  (** Syntax is supplied by [SqAtExternal] and [SqIntoVal] instances. *)
  Section rules.
    Context `{!sqHeap L Σ, !sq_pointsto_mixin, !invGS Σ}.

    Lemma conc_wp_read_sc E {e k} ly l q v
        `{!SqAtExternal e (ALoad ly l) k, !SqIntoVal (k (Some v)) v,
          !Timeless (sq_pointsto l q v)} :
      {{{ ▷ sq_pointsto l q v }}} EXWP e @ E
      {{{ RET v; sq_pointsto l q v }}}.
    Proof.
      iIntros (Φ) "Hl HΦ".
      pose proof (exwp_ext_call E e (ALoad ly l) k) as Hcall.
      iApply (Hcall (q, v) v (sq_pointsto l q v)
        with "[Hl] HΦ").
      - intros ov. simpl. iIntros "[-> $]". iPureIntro. apply sq_into_val.
      - by iMod "Hl".
    Qed.

    Lemma conc_wp_write_sc E {e k} ly l v v' vret
        `{!SqAtExternal e (AStore ly l v) k, !SqIntoVal (k None) vret,
          !Timeless (sq_pointsto l 1 v')} :
      {{{ ▷ sq_pointsto l 1 v' }}} EXWP e @ E
      {{{ RET vret; sq_pointsto l 1 v }}}.
    Proof.
      iIntros (Φ) "Hl HΦ".
      pose proof (exwp_ext_call E e (AStore ly l v) k) as Hcall.
      iApply (Hcall v' vret (sq_pointsto l 1 v)
        with "[Hl] HΦ").
      - intros ov. simpl. iIntros "[-> $]". iPureIntro. apply sq_into_val.
      - by iMod "Hl".
    Qed.

    Lemma conc_wp_cas {b : bool} E {e k} ly l v_exp v_new v_cur
        `{!SqAtExternal e (ACAS ly l v_exp v_new) k,
          !SqIntoVal (k (Some (if b then sqlang_true_val else sqlang_false_val)))
            (if b then sqlang_true_val else sqlang_false_val),
          !Timeless (sq_compare v_cur v_exp b ∗ sq_pointsto l 1 v_cur)%I} :
      {{{ ▷ (sq_compare v_cur v_exp b ∗ sq_pointsto l 1 v_cur) }}}
        EXWP e @ E
      {{{ RET (if b then sqlang_true_val else sqlang_false_val);
          sq_pointsto l 1 (if b then v_new else v_cur) }}}.
    Proof.
      iIntros (Φ) "Hl HΦ".
      pose proof (exwp_ext_call E e (ACAS ly l v_exp v_new) k) as Hcall.
      iApply (Hcall (v_cur, b)
        (if b then sqlang_true_val else sqlang_false_val)
        (sq_pointsto l 1 (if b then v_new else v_cur)) with "[Hl] HΦ").
      - intros ov. simpl. iIntros "[-> $]". iPureIntro. apply sq_into_val.
      - by iMod "Hl".
    Qed.

    Lemma conc_wp_fork E {e k} e_new vret
        `{!SqAtExternal e (ASpawn e_new) k, !SqIntoVal (k None) vret} :
      {{{ ▷ EXWP (sqlang_expr_to_thrd_st e_new) {{ _, True }} }}}
        EXWP e @ E {{{ RET vret; True }}}.
    Proof.
      iIntros (Φ) "He HΦ".
      pose proof (exwp_ext_call E e (ASpawn e_new) k) as Hcall.
      iApply (Hcall () vret True%I with "[He] HΦ").
      - intros ov. simpl. iIntros "->". iSplit; last done.
        iPureIntro. apply sq_into_val.
      - by iModIntro.
    Qed.
  End rules.

End language.
