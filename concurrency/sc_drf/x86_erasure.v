(** ** X86 permission erasure proof*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.
Require Import compcert.x86.Asm.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.sc_drf.SC_erasure.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module X86CoreErasure.
  Import ValErasure MemErasure event_semantics X86Context.

  Section X86CoreErasure.

    Variable the_program: Asm.program.
    Variable Hsafe : Asm_core.safe_genv (@the_ge the_program).
    Instance X86Sem : Semantics := @X86Context.X86Sem the_program Hsafe.
    Definition reg_erasure (r:PregEq.t) (rs rs' : regset) : Prop :=
      val_erasure (Pregmap.get r rs) (Pregmap.get r rs').
    
    Definition regs_erasure rs rs' : Prop :=
      forall r, reg_erasure r rs rs'.

    Definition core_erasure c c' :=
      match c, c' with
      | State rs  _, State rs' _ =>
        regs_erasure rs rs'
      end.
    
    (* Definition erasedPerm c := *)
    (*   match c with *)
    (*   | State _ mem => *)
    (*     forall (b : block) (ofs : Z) (k : perm_kind), *)
    (*       Mem.valid_block mem b -> (Mem.mem_access mem) !! b ofs k = Some Freeable *)
    (*   end. *)

    
    Lemma regs_erasure_refl:
      forall rs, regs_erasure rs rs.
    Proof with eauto with val_erasure.
      intros rs r;
        unfold reg_erasure...
    Qed.

    Hint Immediate regs_erasure_refl : regs_erasure.
    Hint Immediate val_erasure_list_refl : val_erasure.
    
    Lemma core_erasure_refl:
      forall c,
        core_erasure c c.
    Proof with eauto with val_erasure regs_erasure.
      destruct c; simpl.
      repeat split...
    Qed.

    Hint Immediate core_erasure_refl: regs_erasure.

    Lemma regs_erasure_set:
      forall rs rs' v v' r
        (Hrs_ren: regs_erasure rs rs')
        (Hval: val_erasure v v'),
        regs_erasure (rs # r <- v) (rs' # r <- v').
    Proof.
      intros.
      intros r'.
      unfold reg_erasure.
      do 2 rewrite Pregmap.gsspec.
      destruct (Pregmap.elt_eq r' r); auto.
      eapply Hrs_ren.
    Qed.

    
    Lemma regs_erasure_get:
      forall rs rs' r,
        regs_erasure rs rs' ->
        val_erasure (rs r) (rs' r).
    Proof.
      intros.
      unfold regs_erasure, reg_erasure in *. eauto.
    Qed.

    Hint Resolve regs_erasure_get regs_erasure_refl regs_erasure_set
      : regs_erasure.

    Notation the_ge := (@the_ge the_program).
    (** ** Result about at_external, after_external and initial_core *)

    Lemma get_extcall_arg_erase:
      forall rs rs' m m' l v
        (Hrs: regs_erasure rs rs')
        (Hmem: mem_erasure m m')
        (Harg: get_extcall_arg rs m l = Some v),
      exists v',
        get_extcall_arg rs' m' l = Some v' /\
        val_erasure v v'.
    Proof.
      intros.
      unfold get_extcall_arg in *.
      destruct l.
      - inv Harg.
        unfold regs_erasure in Hrs.
        specialize (Hrs (preg_of r)).
        unfold regs_erasure, reg_erasure in Hrs.
        unfold Pregmap.get in Hrs.
        eexists; now eauto.
      - destruct sl; try discriminate.
        assert (Heq: rs RSP = rs' RSP)
          by (eapply regs_erasure_get with (r := RSP) in Hrs;
              destruct (rs RSP); simpl in Harg; try discriminate;
              simpl in Hrs; auto).
        rewrite <- Heq.
        eapply mem_loadv_erased in Harg;
          now eauto.
    Qed.

    Lemma get_extcall_arguments_erase:
      forall rs rs' m m' ls vs
        (Hrs: regs_erasure rs rs')
        (Hmem: mem_erasure m m')
        (Hargs: get_extcall_arguments rs m ls = Some vs),
      exists vs',
        get_extcall_arguments rs' m' ls = Some vs' /\
        val_erasure_list vs vs'.
    Proof.
      intros rs rs' m m' ls.
      induction ls; intros; simpl in *.
      - inv Hargs; exists [::]; split; eauto with val_erasure.
      - destruct a.
        + destruct (get_extcall_arg rs m r) eqn:Harg; try discriminate.
          destruct (get_extcall_arguments rs m ls) eqn:Hget_args; inv Hargs.
          destruct (IHls _ Hrs Hmem ltac:(reflexivity)) as [vs' [Hget_args' Hvals]].
          rewrite Hget_args'.
          eapply get_extcall_arg_erase in Harg; eauto.
          destruct Harg as [v' [Harg' Hval]].
          exists (v' :: vs').
          rewrite Harg'.
          split;
            eauto with val_erasure.
        + repeat match goal with
                 | [H: match ?Expr with _ => _ end = _ |- _] =>
                   destruct Expr eqn:?
                 end; try discriminate; inv Hargs;
            repeat match goal with
                   | [H: get_extcall_arg rs m _ = _ |- _] =>
                     eapply get_extcall_arg_erase in H; eauto
                   | [H: exists _, _ |- _] => destruct H
                   | [H: _ /\ _ |- _] => destruct H
                   | [H: ?Expr = _ |- context[match ?Expr with _ => _ end]] =>
                     rewrite H
                   end.
          destruct (IHls _ Hrs Hmem ltac:(reflexivity)) as [? [Hargs' ?]].
          rewrite Hargs'.            
          eexists; split;
            now eauto with val_erasure.
    Qed.
    
    Lemma at_external_erase:
      forall rs rs' m m' ef vs
        (Herase: core_erasure (State rs m) (State rs' m'))
        (Hmem_erase: mem_erasure m m')
        (Hat_external: at_external the_ge (State rs m) = Some (ef, vs)),
      exists vs',
        at_external the_ge (State rs' m') = Some (ef, vs') /\
        val_erasure_list vs vs'.
    Proof.
      intros.
      unfold core_erasure in *.
      unfold regs_erasure, reg_erasure, Pregmap.get, at_external in *.
      destruct (rs PC) eqn:Hpc; try discriminate.
      repeat match goal with
               | [H: _ /\ _ |- _] => destruct H
               | [|- match ?Expr with _ => _ end] =>
                 destruct Expr eqn:?
               | [H: match ?Expr with _ => _ end = _ |- _] =>
                 destruct Expr eqn:?; try discriminate
               | [H: Some _ = Some _ |- _] => inversion H; clear H; subst
             end.
      pose proof (Herase PC) as Hregs.
      rewrite Hpc in Hregs.
      simpl in Hregs.
      rewrite <- Hregs.
      eapply get_extcall_arguments_erase in Heqo0; eauto.
      destruct Heqo0 as [vs' [Hget_ext' Hvals]].
      exists vs'.
      split; auto.
      erewrite if_true by reflexivity.
      rewrite Heqo.
      rewrite Hget_ext'.
      reflexivity.
    Qed.
    
    Lemma after_external_erase :
      forall v v' c c' m m' c2
        (HeraseCores: core_erasure c c')
        (HeraseVal: optionval_erasure v v')
        (HeraseMem: mem_erasure m m')
        (Hafter_external: after_external the_ge v c m = Some c2),
      exists (c2' : state),
        after_external the_ge v' c' m' = Some c2' /\
        core_erasure c2 c2'.
    Proof.
      intros.
      unfold after_external, after_external_regset in *.
      simpl in *.
      destruct c; try discriminate.
      unfold core_erasure in HeraseCores.
      destruct c'; try by exfalso.
      destruct (r PC) eqn:?; try discriminate.
      destruct (Ptrofs.eq_dec i Ptrofs.zero) eqn:Hptr; try discriminate.
      destruct (Genv.find_funct_ptr the_ge b) as [[? | ?]|] eqn:Hgenv; try discriminate.
      assert (HPC':= regs_erasure_get PC HeraseCores).
      rewrite Heqv0 in HPC'.
      simpl in HPC'.
      rewrite <- HPC'.
      rewrite Hgenv.
      rewrite Hptr.
      unfold set_pair.
      destruct v;
        inv Hafter_external;
        simpl in HeraseVal;
        destruct v'; try (by exfalso);
          eexists; split; eauto; [destruct (loc_external_result (ef_sig e0))|];
            eauto;
            repeat eapply regs_erasure_set;
            now eauto with regs_erasure val_erasure.
    Qed.

    Lemma make_arguments_nil_erasure:
      forall rs rs2 rs' m m2 m' locs
        (Hregs: regs_erasure rs rs')
        (Hmem: mem_erasure' m m')
        (Hmake: make_arguments rs m locs [::] = Some (rs2, m2)),        
      exists rs2' m2',
        make_arguments rs' m' locs [:: ] = Some (rs2', m2') /\
        regs_erasure rs2 rs2' /\
        mem_erasure' m2 m2'.
    Proof.
      destruct locs; intros.
      - simpl in *.
        inv Hmake.
        do 2 eexists; now eauto.
      - simpl in Hmake.
        discriminate.
    Qed.

    Lemma make_arguments_nil_locs:
      forall rs rs2 rs' m m2 m' locs
        (Hregs: regs_erasure rs rs')
        (Hmem: mem_erasure' m m')
        (Hmake: make_arguments rs m locs [::] = Some (rs2, m2)),
        locs = [::].
    Proof.
      destruct locs; intros; simpl in *;
        [reflexivity | discriminate].
    Qed.

    Lemma make_arg_erasure:
      forall rs rs' m m' r arg arg' rs2 m2
        (Hregs: regs_erasure rs rs')
        (Hmem: mem_erasure' m m')
        (Hargs: val_erasure arg arg')
        (Hmake: make_arg rs m r arg = Some (rs2, m2)),
      exists rs2' m2',
        make_arg rs' m' r arg' = Some (rs2', m2') /\
        regs_erasure rs2 rs2' /\
        mem_erasure' m2 m2'.
    Proof.
      intros.
      unfold make_arg in *.
      destruct r.
      - inv Hmake.
        do 2 eexists; split; eauto.
        split; eauto.
        repeat eapply regs_erasure_set;
          now eauto with regs_erasure val_erasure.
      - destruct (Mem.storev (chunk_of_type ty) m
                             (Val.offset_ptr (rs RSP) (Ptrofs.repr (Stacklayout.fe_ofs_arg +
                                                                    4 * pos))) arg) eqn:Hstore;
          try discriminate.
        inv Hmake.
        assert (Val.offset_ptr (rs' RSP) (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos)) =
                Val.offset_ptr (rs2 RSP) (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos))).
        { destruct (rs2 RSP) eqn:Hrsp; simpl in Hstore; try discriminate.
          eapply regs_erasure_get with (r := RSP) in Hregs.
          rewrite Hrsp in Hregs. inv Hregs.
          reflexivity.
        }
        eapply mem_storev_erased' in Hstore; eauto.
        destruct Hstore as [m2' [Hstore' Hmem']].
        exists rs', m2'.
        rewrite H.
        rewrite Hstore'.
        now eauto.
    Qed.

    Lemma make_arguments_erasure:
      forall rs rs2 rs' m m2 m' locs arg arg'
        (Hregs: regs_erasure rs rs')
        (Hmem: mem_erasure' m m')
        (Hargs: val_erasure arg arg')
        (Hmake: make_arguments rs m locs [:: arg] = Some (rs2, m2)),
      exists rs2' m2',
        make_arguments rs' m' locs [:: arg'] = Some (rs2', m2')/\
        regs_erasure rs2 rs2' /\
        mem_erasure' m2 m2'.
    Proof.
      intros. destruct locs.
      - simpl in *.
        discriminate.
      - simpl in Hmake.
        simpl.
        destruct (make_arguments rs m locs [::]) as [[? ?]|] eqn:Hmake_args; try discriminate.
        assert (Heq := make_arguments_nil_locs _ Hregs Hmem Hmake_args); subst.
        eapply make_arguments_nil_erasure in Hmake_args; eauto.
        destruct Hmake_args as [rs2' [m2' [Hmake_args' [Hregs_erasure' Hmem']]]].
        simpl.
        simpl in Hmake_args'; inv Hmake_args'.
        destruct r.
        eapply make_arg_erasure in Hmake; now eauto.
        destruct (make_arg r0 m0 rhi (Val.hiword arg)) as [[? ?]|] eqn:Hmake_arg1; try discriminate.
        eapply make_arg_erasure with (arg' := Val.hiword arg') in Hmake_arg1; eauto with val_erasure.
        destruct Hmake_arg1 as [rs2'0 [m2'0 [? [? ?]]]].
        eapply make_arg_erasure with (arg' := Val.loword arg') in Hmake; eauto with val_erasure.
        destruct Hmake as [rs2'1 [m2'1 [? [? ?]]]].
        exists rs2'1, m2'1.
        rewrite H.
        now eauto.
    Qed.
        
  Lemma erasure_initial_core:
    forall h v arg v' arg' c m m' m2
      (Hv: val_erasure v v')
      (Harg: val_erasure arg arg')
      (Hmem: mem_erasure m m')
      (Hinit: initial_core semSem h m c m2 v [:: arg]),
      exists c' m2',
        initial_core semSem h m' c' m2' v' [:: arg'] /\
        core_erasure c c' /\
        mem_erasure m2 (erasePerm m2').
  Proof.
    intros.
    unfold initial_core in *; simpl in *.
    destruct Hinit as [Hinit ?].
    inversion Hinit; subst.
    simpl in Hv; subst.
    remember (Mem.alloc m' 0 (3 * size_chunk Mptr)) eqn:Halloc'.
    destruct p.
    symmetry in Halloc'.
    eapply alloc_erasure' with (m := m) (m' := m') in H1; eauto.
    destruct H1 as [Hmem' ?]; subst.
    eapply mem_storev_erased' in H2; eauto with val_erasure.
    destruct H2 as [m2' [Hstore2' Hmem2']].
    eapply mem_storev_erased' in H3; eauto with val_erasure.
    destruct H3 as [m4' [Hstore4' Hmem4']].
    eapply @make_arguments_erasure with (m' := m4') in H4; eauto with regs_erasure.
    destruct H4 as [? [? [? [? ?]]]].
    exists (State x x0), x0.
    split; simpl; split; eauto.
    econstructor; eauto.
    eapply mem_erasure'_erase;
      eauto.
  Qed.    
        
  Lemma halted_erase:
    forall c c' h
      (HeraseCores: core_erasure c c')
      (Hhalted: halted semSem c h),
      halted semSem c' h.
  Proof.
    intros.
    unfold halted in *; simpl in *.
    inversion Hhalted; subst.
    unfold core_erasure in HeraseCores.
    destruct c'.
    econstructor.
    eapply regs_erasure_get with (r := PC) in HeraseCores.
    rewrite H in HeraseCores; auto.
    eapply regs_erasure_get with (r := RAX) in HeraseCores.
    rewrite H0 in HeraseCores; auto.
  Qed.

  Lemma eval_testcond_erasure:
    forall (c : testcond) rs rs'
      (Hrs: regs_erasure rs rs'),
      eval_testcond c rs <> None ->
      eval_testcond c rs = eval_testcond c rs'.
  Proof.
    intros.
    unfold eval_testcond in *.
    destruct c;
      unfold regs_erasure, reg_erasure, Pregmap.get in *;
      repeat match goal with
             | [|- match (?Rs ?R) with _ => _ end = _] =>
               pose proof (Hrs R);
                 destruct (Rs R);
                 match goal with
                 | [H: val_erasure _ _ |- _] =>
                   inv H
                 end
             end; auto; try by exfalso.
  Qed.

  Import TraceErasure.

  Lemma eval_addrmode32_erase:
    forall g a rs rs',
      regs_erasure rs rs' ->
      val_erasure (eval_addrmode32 g a rs) (eval_addrmode32 g a rs').
  Proof.
    intros.
    unfold eval_addrmode32.
    destruct a.
    eapply val_erasure_add.
    destruct base; eauto with val_erasure regs_erasure.
    eapply val_erasure_add;
      match goal with
      |[|-context[match ?Expr with _ => _ end]] =>
       destruct Expr
      end; eauto with val_erasure regs_erasure.
    destruct p.
    destruct (zeq z 1);
      eauto with val_erasure regs_erasure.
  Qed.
  
  Lemma eval_addrmode_erase:
    forall g a rs rs',
      regs_erasure rs rs' ->
      isPointer (eval_addrmode g a rs) ->
      eval_addrmode g a rs = eval_addrmode g a rs'.
  Proof.
    intros. unfold isPointer in *.
    destruct (eval_addrmode g a rs) eqn:?; try by exfalso.
    symmetry.
    unfold eval_addrmode in *.
    assert (Hptr64: Archi.ptr64 = false) by auto.
    rewrite Hptr64 in Heqv.
    rewrite Hptr64.
    unfold eval_addrmode32 in *.
    repeat match goal with
           | [|-context[match ?Expr with _ => _ end]] =>
             destruct Expr
           end;
      eauto with val_erasure regs_erasure.
    eapply val_erasure_add_result with
    (v1 := rs i0) (v2 := Val.add (Val.mul (rs i1) (Vint (Int.repr z))) (Vint (Int.repr z0)));
      eauto with val_erasure regs_erasure.
    eapply val_erasure_add_result with
    (v2 := Val.add (Val.mul (rs i1) (Vint (Int.repr z))) (Genv.symbol_address g i2 i3));
      eauto with val_erasure regs_erasure.
  Qed.

  (* TODO: these two are duplicated, create a separate library for registers*)
  Lemma regset_comm:
    forall (rs: Pregmap.t val) r r' v,
      (rs # r <- v) # r' <- v = (rs # r' <- v) # r <- v.
  Proof.
    intros.
    unfold Pregmap.set.
    extensionality r''.
    destruct (PregEq.eq r'' r'), (PregEq.eq r'' r); auto.
  Qed.

  Lemma undef_regs_comm:
    forall regs rs r,
      undef_regs regs (rs # r <- Vundef) =
      (undef_regs regs rs) # r <- Vundef.
  Proof.
    intros.
    generalize dependent rs.
    induction regs; intros. simpl. auto.
    simpl.
    specialize (IHregs (rs # a <- Vundef)).
    rewrite <- IHregs.
    apply f_equal.
      by rewrite regset_comm.
  Qed.

  Lemma regs_erasure_undef:
    forall regs rs rs',
      regs_erasure rs rs' ->
      regs_erasure (undef_regs regs rs) (undef_regs regs rs').
  Proof.
    induction regs; intros; simpl.
    auto.
    do 2 rewrite undef_regs_comm.
    eapply regs_erasure_set.
    eauto.
    simpl; auto.
  Qed.

  Lemma regs_erasure_set_undef:
    forall rs rs' r,
      regs_erasure rs rs' ->
      regs_erasure rs # r <- Vundef rs'.
  Proof.
    intros.
    unfold regs_erasure, reg_erasure in *.
    intros r'.
    rewrite Pregmap.gsspec.
    destruct (Pregmap.elt_eq r' r); subst;
    simpl; auto.
  Qed.
  
  Hint Resolve regs_erasure_set_undef : regs_erasure.

  Lemma regs_erasure_set_res:
    forall res v v' rs rs'
      (Hregs: regs_erasure rs rs')
      (Hval: val_erasure v v'),
      regs_erasure (set_res res v rs) (set_res res v' rs').
  Proof.
    induction res; intros;
      simpl; eauto with regs_erasure.
    eapply IHres2; eauto with val_erasure.
  Qed.

  Hint Resolve regs_erasure_set_res : regs_erasure.


  Lemma val_erasure_addrmode:
    forall g (a : addrmode) rs rs'
      (Hrs: regs_erasure rs rs'),
      val_erasure (eval_addrmode g a rs) (eval_addrmode g a rs').
  Proof with eauto 10 with val_erasure regs_erasure.
    intros.
    unfold eval_addrmode.
    assert (Hptr64: Archi.ptr64 = false) by auto.
    rewrite Hptr64.
    eapply eval_addrmode32_erase;
      now eauto.
  Qed.

  Lemma compare_ints_erasure:
    forall v1 v2 v1' v2' rs rs' m m'
      (Hval_erasure: val_erasure v1 v1')
      (Hval_erasure': val_erasure v2 v2')
      (Hrs: regs_erasure rs rs')
      (Hmem: mem_erasure m m'),
      regs_erasure (compare_ints v1 v2 rs m)
                   (compare_ints v1' v2' rs' m').
  Proof with eauto 12 using val_erasure_cmpu with regs_erasure val_erasure.
    intros.
    unfold compare_ints...
  Qed.

  Hint Extern 0 (val_erasure Vundef _) => reflexivity : val_erasure.

  Lemma compare_floats_erasure:
    forall v1 v2 v1' v2' rs rs'
      (Hval_erasure: val_erasure v1 v1')
      (Hval_erasure2: val_erasure v2 v2')
      (Hrs: regs_erasure rs rs'),
      regs_erasure (compare_floats v1 v2 rs)
                   (compare_floats v1' v2' rs').
  Proof with eauto 10 using val_erasure_cmpu with regs_erasure val_erasure.
    intros.
    unfold compare_floats.
    destruct v1,v2; inv Hval_erasure; inv Hval_erasure2; simpl;
    eauto 6 with regs_erasure val_erasure;
    try destruct v1'; try destruct v2';
    eauto 6 with regs_erasure val_erasure;
    unfold Val.of_bool;
    repeat rewrite if_negb;
    repeat match goal with
           | [|- context[match ?Expr with | _ => _ end]] =>
             destruct Expr eqn:?
           end...
  Qed.

  Lemma compare_floats32_erasure:
    forall v1 v2 v1' v2' rs rs'
      (Hval_erasure: val_erasure v1 v1')
      (Hval_erasure2: val_erasure v2 v2')
      (Hrs: regs_erasure rs rs'),
      regs_erasure (compare_floats32 v1 v2 rs)
                   (compare_floats32 v1' v2' rs').
  Proof with eauto 10 using val_erasure_cmpu with regs_erasure val_erasure.
    intros.
    unfold compare_floats32.
    destruct v1,v2; inv Hval_erasure; inv Hval_erasure2; simpl;
    eauto 6 with regs_erasure val_erasure;
    try destruct v1'; try destruct v2';
    eauto 6 with regs_erasure val_erasure;
    unfold Val.of_bool;
    repeat rewrite if_negb;
    repeat match goal with
           | [|- context[match ?Expr with | _ => _ end]] =>
             destruct Expr eqn:?
           end...
  Qed.

  Hint Transparent undef_regs: regs_erasure.

    (* TODO: move this to the right place*)
  Lemma get_reg_erasure:
    forall rs rs' r
      (Hregs_erasure: regs_erasure rs rs')
      (Hundef: rs r <> Vundef),
      rs r = rs' r.
  Proof.
    intros.
    unfold regs_erasure, reg_erasure, Pregmap.get, val_erasure in *.
    specialize (Hregs_erasure r).
    destruct (rs r); tauto.
  Qed.

  Lemma erasure_eval_testcond:
    forall c rs rs' b,
      regs_erasure rs rs' ->
      eval_testcond c rs = Some b ->
      eval_testcond c rs' = Some b.
  Proof.
    intros.
    unfold eval_testcond in *.
    destruct c;
    repeat  match goal with
      | [H: match ?Expr with | _ => _ end = _ |- _] =>
        destruct Expr eqn:?
      end; try discriminate;
    repeat  match goal with
            |[H: rs ?R = _ |- _] =>
             erewrite get_reg_erasure  in H by (eauto; congruence);
               rewrite H
            |[H: Some _ = Some _ |- _] =>
             inv H
            end; auto.
  Qed.

  Lemma eval_addrmode64_erase:
    forall g a rs rs',
      regs_erasure rs rs' ->
      val_erasure (eval_addrmode64 g a rs) (eval_addrmode64 g a rs').
  Proof.
    intros.
    unfold eval_addrmode64.
    destruct a.
    eapply val_erasure_addl.
    destruct base; eauto with val_erasure regs_erasure.
    eapply val_erasure_addl;
      match goal with
      |[|-context[match ?Expr with _ => _ end]] =>
       destruct Expr
      end; eauto with val_erasure regs_erasure.
    destruct p.
    destruct (zeq z 1);
      eauto with val_erasure regs_erasure.
  Qed.

  Lemma compare_longs_erasure:
    forall v1 v1' v2 v2' rs rs' m m'
      (Hval1: val_erasure v1 v1')
      (Hval2: val_erasure v2 v2')
      (Hregs: regs_erasure rs rs')
      (Hmem: mem_erasure m m'),
      regs_erasure (compare_longs v1 v2 rs m) (compare_longs v1' v2' rs' m').
  Proof with eauto 10 using val_erasure_cmpu with regs_erasure val_erasure.
    intros.
    unfold compare_longs.
    destruct v1,v2; inv Hval1; inv Hval2; simpl;
      eauto 6 with regs_erasure val_erasure;
      try destruct v1'; try destruct v2';
        eauto 6 with regs_erasure val_erasure;
        unfold Val.of_bool;
        repeat rewrite if_negb;
        repeat match goal with
               | [|- context[match ?Expr with | _ => _ end]] =>
                 destruct Expr eqn:?
               end...
  Qed.

  Hint Resolve compare_ints_erasure compare_floats_erasure compare_longs_erasure
       compare_floats32_erasure val_erasure_addrmode eval_addrmode32_erase
       eval_addrmode64_erase regs_erasure_undef : regs_erasure.
  Hint Extern 0 (val_erasure (undef_regs _ _ # _ <- _ _) _) =>
  eapply regs_erasure_set : regs_erasure.


  Lemma exec_instr_erased:
    forall (fn : function) (i : instruction) (rs rs' rs2: regset)
      (m m' m2 : mem) ev
      (HeraseCores: regs_erasure rs rs')
      (HerasedMem: mem_erasure m m')
      (Hexec_ev: Asm_event.drf_instr the_ge (fn_code fn) i rs m = Some ev)
      (Hexec: exec_instr the_ge fn i rs m = Next rs2 m2),
    exists rs2' m2' ev',
      exec_instr the_ge fn i rs' m' = Next rs2' m2' /\
      Asm_event.drf_instr the_ge (fn_code fn) i rs' m' = Some ev' /\
      regs_erasure rs2 rs2' /\ mem_erasure m2 (erasePerm m2') /\
      mem_event_list_erasure ev ev'.
  Proof.
    intros.
    destruct i eqn:?; simpl in *;
    unfold goto_label in *;
    repeat match goal with
           | [H: context[match eval_testcond ?C rs with _ => _ end] |- _] =>
             destruct (eval_testcond C rs) as [b|] eqn:?
           | [H: eval_testcond ?C rs = Some _ |- _] =>
             erewrite <- eval_testcond_erasure with (rs := rs)
               by (eauto; rewrite H; congruence);
               rewrite H;
               destruct b
           end;
    (* see if this does anything*)
      repeat match goal with
             | [|- match (?Rs ?R) with _ => _ end = _] =>
               pose proof (Hrs R);
                 destruct (Rs R);
                 match goal with
                 | [H: val_erasure _ _ |- _] =>
                   inv H
                 end
             end; auto;
    repeat match goal with
           | [H: match ?Expr with _ => _ end = _ |- _] =>
             destruct Expr eqn:?
           end; try discriminate;
    try match goal with
        | [H: Mem.alloc m 0 ?Sz = _ |- _] =>
          destruct (Mem.alloc m' 0 Sz) as [? ?] eqn:Halloc';
            eapply alloc_erasure' in Halloc'; eauto;
            destruct Halloc'; subst
        | [H: Mem.free _ _ _ _ = _ |- _] =>
          eapply mem_free_erasure' in H; eauto;
          destruct H as [? [? Herasure']];
          eapply mem_erasure'_erase in Herasure'
        end;
    repeat match goal with
           | [H: Mem.store ?Chunk ?M ?B ?Ofs (rs ?R) = _,
                 H1: mem_erasure' ?M ?M2 |- _] =>
             eapply mem_store_erased' with (m' := M2) (v' := rs' R) in H;
               eauto with regs_erasure val_erasure;
               destruct H as [? [? ?]]
           | [H: Mem.loadv _ ?M (Vptr _ _) = _, H2: mem_erasure ?M _ |- _] =>
             eapply mem_loadv_erased in H; eauto;
             destruct H as [? [? ?]]
           end;
    try match goal with
        | [H: exec_store ?G ?CHUNK ?M ?A ?RS ?RS0 _ = _ |- _] =>
          unfold exec_store in *;
            destruct (Mem.storev CHUNK M (eval_addrmode G A RS) (RS RS0)) eqn:?;
                     inv H
        | [H: exec_load ?G ?CHUNK ?M ?A ?RS ?RD = _ |- _] =>
          unfold exec_load in *;
            destruct (Mem.loadv CHUNK M (eval_addrmode G A RS)) eqn:?;
                     inv H
        | [H: Next _ _ = Next _ _ |- _] =>
          inv H
        end;
    try match goal with
        | [H: Mem.loadv _ _ (eval_addrmode ?G ?A rs) = _ |- _] =>
          pose proof (loadv_pointer _ _ _ H);
            erewrite <- eval_addrmode_erase by (eauto);
          eapply mem_loadv_erased with
          (m' := m') (vptr := eval_addrmode G A rs) in H;
            eauto with val_erasure regs_erasure;
            destruct H as [? [? ?]]
        | [H: Mem.storev _ _ (eval_addrmode ?G ?A rs) (rs ?R) = _ |- _] =>
          pose proof (storev_pointer _ _ _ _ H);
            erewrite <- eval_addrmode_erase by (eauto);
            eapply mem_storev_erased with
            (m' := m') (vptr := eval_addrmode G A rs) (v' := rs' R) in H;
            eauto with val_erasure regs_erasure;
            destruct H as [? [? ?]]
        | [H: Val.divs _ _ = _, H2: Val.mods _ _ = _ |- _] =>
          erewrite divs_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1) in H;
            eauto with reg_renamings val_renamings;
            erewrite mods_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1)
              in H2; eauto with reg_renamings val_renamings
        | [H: Val.divu _ _ = _, H2: Val.modu _ _ = _ |- _] =>
          erewrite divu_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1) in H;
            eauto with reg_renamings val_renamings;
            erewrite modu_ren with (v1' := rs' EAX) (v2' := rs' # EDX <- Vundef r1)
              in H2; eauto with reg_renamings val_renamings
        end;
      repeat match goal with
             | [H: Mem.loadbytes ?M _ _ _ = _, H2: mem_erasure ?M _ |- _] =>
               eapply loadbytes_erasure in H; eauto;
               destruct H as [? [? ?]]
             end;
      unfold nextinstr_nf, nextinstr, Vone, Vzero;
      repeat match goal with
             | [H: Val.divu (rs ?R) (rs # ?R2 <- ?V ?R3) = _ |- _] =>
               eapply val_erasure_divu_result with (v1' := rs' R)
                                                   (v2' := rs' # R2 <- V R3) in H;
                 eauto with regs_erasure val_erasure;
                 rewrite H
             | [H: Val.modu (rs ?R) (rs # ?R2 <- ?V ?R3) = _ |- _] =>
               eapply val_erasure_modu_result with (v1' := rs' R)
                                                   (v2' := rs' # R2 <- V R3) in H;
                 eauto with regs_erasure val_erasure;
                 rewrite H
             | [H: Val.divs (rs ?R) (rs # ?R2 <- ?V ?R3) = _ |- _] =>
               eapply val_erasure_divs_result with (v1' := rs' R)
                                                   (v2' := rs' # R2 <- V R3) in H;
                 eauto with regs_erasure val_erasure;
                 rewrite H
             | [H: Val.mods (rs ?R) (rs # ?R2 <- ?V ?R3) = _ |- _] =>
               eapply val_erasure_mods_result with (v1' := rs' R)
                                                   (v2' := rs' # R2 <- V R3) in H;
                 eauto with regs_erasure val_erasure;
                 rewrite H
             | [|- context[eval_testcond ?C rs']] =>
               destruct (eval_testcond C rs') as [[]|] eqn:?
             | [H: eval_addrmode _ _ _ = _, H2: Mem.loadv _ _ _ = _ |- _] =>
               rewrite H in H2
             | [H: eval_addrmode _ _ _ = _, H2: Mem.storev _ _ _ _ = _ |- _] =>
               rewrite H in H2
             | [H: eval_addrmode _ _ _ = _ |- context[eval_addrmode _ _ _]] =>
               rewrite H
             | [H: Mem.loadv _ _ _ = _ |- _] =>
               rewrite H; clear H; eauto
             | [H: Mem.storev _ _ _ _ = _ |- _] =>
               rewrite H; clear H; eauto
             | [H: Mem.loadbytes _ _ _ _ = _ |- _] =>
               rewrite H; clear H
             | [|- _ /\ _] => split; eauto
             | [H: Some _ = Some _ |- _] =>
               inv H
             | [H: rs ?R = _ |- _ ] =>
               erewrite get_reg_erasure in H by (eauto; congruence);
                 try rewrite H; clear H
             | [H: ?Expr = _ |- context[?Expr]] =>
               rewrite H; clear H
             | [|- regs_erasure _ _] =>
               eauto 20 with regs_erasure val_erasure
             | [|- mem_erasure _ (erasePerm _)] =>
               eauto using mem_erasure_idempotent
             | [|- mem_event_list_erasure _ _] =>
               constructor
             | [|- mem_event_erasure _ _ ] => constructor
             | [|- memval_erasure_list _ _] =>
               eauto with val_erasure regs_erasure
             | [|- exists _ _ _, _ ] => try (do 3 eexists; split; [reflexivity|])
             end; try (by exfalso); try assumption.
    destruct (eval_testcond c rs) as [[]|] eqn:Heq; simpl;
    try pose proof (erasure_eval_testcond _ HeraseCores Heq);
    try congruence;
    eauto 8 with regs_erasure val_erasure.
    destruct (eval_testcond c rs) as [[]|] eqn:Heq; simpl;
    try pose proof (erasure_eval_testcond _ HeraseCores Heq);
    try congruence;
    eauto 8 with regs_erasure val_erasure.
    assert (Heval: eval_testcond c rs = None).
    { destruct (eval_testcond c rs) eqn:Heval;
      auto.
      eapply erasure_eval_testcond in Heval; eauto;
      congruence.
    }
    rewrite Heval. simpl.
    now eauto 8 with regs_erasure val_erasure.
    pose proof HeraseCores as HeraseCores'.
    apply regs_erasure_set_undef with (r := RAX) in HeraseCores;
      simpl; auto.
    eapply regs_erasure_set_undef with (r:= RDX) in HeraseCores.
    eapply regs_erasure_get with (r := PC) in HeraseCores.
    rewrite Heqv0 in HeraseCores.
    simpl in HeraseCores.
    erewrite! Pregmap.gso by (intros Hcontra; discriminate).
    rewrite <- HeraseCores.
    do 3 eexists.
    split.
    reflexivity.
    split. reflexivity.
    split.
    repeat (eapply regs_erasure_set; eauto with val_erasure).
    split.
    eapply mem_erasure_idempotent; eauto.
    now eauto using mem_event_list_erasure, mem_event_erasure.
    eapply mem_erasure'_erase;
      now assumption.
  Qed.

  (* Lemma extcall_arg_erasure: *)
  (*   forall m m' loc arg rs rs' ev *)
  (*     (Harg: extcall_arg rs m loc arg) *)
  (*     (Harg_ev: Asm_event.extcall_arg_ev rs m loc arg ev) *)
  (*     (Hmem_obs_eq: mem_erasure m m') *)
  (*     (Hrs : regs_erasure rs rs'), *)
  (*   exists arg' ev', *)
  (*     Asm_event.extcall_arg_ev rs' m' loc arg' ev' /\ *)
  (*     extcall_arg rs' m' loc arg' /\ *)
  (*     val_erasure arg arg' /\ *)
  (*     mem_event_list_erasure ev ev'. *)
  (* Proof with eauto with val_erasure regs_erasure. *)
  (*   intros. *)
  (*   inversion Harg; subst. *)
  (*   - inversion Harg_ev; subst. *)
  (*     exists (rs' (preg_of r)), [::]; *)
  (*     (repeat split); try econstructor... *)
  (*   - inversion Harg_ev; subst. *)
  (*     eapply mem_loadv_erased in H0; eauto. *)
  (*     destruct H0 as [arg' [Hload' Harg_erasure]]. *)
  (*     eapply loadbytes_erasure in H6; eauto. *)
  (*     destruct H6 as [bytes' [Hloadbytes' Hbytes_erasure]]. *)
  (*     rewrite H3 in Hload'. simpl in Hload'. *)
  (*     assert (Val.add (rs' ESP) (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs))) *)
  (*             = Vptr b z) *)
  (*       by (eapply val_erasure_add_result; eauto with val_erasure regs_erasure ). *)
  (*       exists arg', [:: Read b (Int.unsigned z) (size_chunk (chunk_of_type ty)) *)
  (*                 bytes']. *)
  (*     (repeat split); try econstructor... *)
  (*     eapply Mem.loadbytes_load in Hloadbytes'; eauto. *)
  (*     rewrite Hloadbytes' in Hload'. inv Hload'. *)
  (*     reflexivity. *)
  (*     rewrite H. simpl; auto. *)
  (*     econstructor; eauto. *)
  (*     constructor. *)
  (* Qed. *)

  (* Lemma extcall_arg_pair_erasure: *)
  (*   forall m m' loc arg rs rs' ev *)
  (*     (Harg_ev: Asm_event.extcall_arg_pair_ev rs m loc arg ev) *)
  (*     (Hmem_obs_eq: mem_erasure m m') *)
  (*     (Hrs : regs_erasure rs rs'), *)
  (*   exists arg' ev', *)
  (*     Asm_event.extcall_arg_pair_ev rs' m' loc arg' ev' /\ *)
  (*     extcall_arg_pair rs' m' loc arg' /\ *)
  (*     val_erasure arg arg' /\ *)
  (*     mem_event_list_erasure ev ev'. *)
  (* Proof with eauto with val_erasure regs_erasure. *)
  (*   intros. *)
  (*   inv Harg_ev. *)
  (*   - pose proof (Asm_event.extcall_arg_ev_extcall_arg _ _ _ _ _ H). *)
  (*     eapply extcall_arg_erasure in H; eauto. *)
  (*     destruct H as [? [? [? [? [? ?]]]]]. *)
  (*     do 2 eexists; (repeat split); try econstructor... *)
  (*   - pose proof (Asm_event.extcall_arg_ev_extcall_arg _ _ _ _ _ H). *)
  (*     pose proof (Asm_event.extcall_arg_ev_extcall_arg _ _ _ _ _ H0). *)
  (*     eapply extcall_arg_erasure in H; eauto. *)
  (*     eapply extcall_arg_erasure in H0; eauto. *)
  (*     destruct H as [vhi' [T1' [? [? [? ?]]]]]. *)
  (*     destruct H0 as [vlo' [T2' [? [? [? ?]]]]]. *)
  (*     exists (Val.longofwords vhi' vlo'), (T1' ++ T2'). *)
  (*     (repeat split); try econstructor... *)
  (*     eapply mem_event_list_erasure_cat; eauto. *)
  (* Qed. *)

  (* Lemma extcall_arguments_erasure: *)
  (*   forall m m' ef args rs rs' ev *)
  (*     (Hexternal_ev: Asm_event.extcall_arguments_ev rs m (ef_sig ef) args ev) *)
  (*     (Hmem_obs_eq: mem_erasure m m') *)
  (*     (Hrs : regs_erasure rs rs'), *)
  (*   exists args' ev', *)
  (*     Asm_event.extcall_arguments_ev rs' m' (ef_sig ef) args' ev' /\ *)
  (*     extcall_arguments rs' m' (ef_sig ef) args' /\ *)
  (*     val_erasure_list args args' /\ *)
  (*     mem_event_list_erasure ev ev'. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold extcall_arguments, Asm_event.extcall_arguments_ev in *. *)
  (*   generalize dependent ev. *)
  (*   generalize dependent (Conventions1.loc_arguments (ef_sig ef)). *)
  (*   induction args; intros. *)
  (*   - inv Hexternal_ev. *)
  (*     exists [::], [::]. *)
  (*     repeat split; *)
  (*       constructor. *)
  (*   - inv Hexternal_ev. *)
  (*     destruct (IHargs _ _ H6) as (args' & T2' & Hargs_ev & *)
  (*                                     Hls & Hargs_erasure & HT_erasure2). *)
  (*     eapply extcall_arg_pair_erasure in H4; eauto. *)
  (*     destruct H4 as (arg' & T1' & Harg_ev' & Harg' & Harg_erasure' & HT_erasure1). *)
  (*     exists (arg' :: args'), (T1' ++ T2'). *)
  (*     repeat split; try econstructor; eauto. *)
  (*     eapply mem_event_list_erasure_cat; eauto. *)
  (* Qed. *)
  
  Lemma eval_builtin_arg_ev_erasure:
    forall rs rs' sp sp' m m' ba v T
      (Hrs: regs_erasure rs rs')
      (Hsp: val_erasure sp sp')
      (Hmem: mem_erasure m m')
      (Hbuiltin: Asm_event.eval_builtin_arg_ev _ the_ge rs sp m ba v T),
    exists v' T',
      Asm_event.eval_builtin_arg_ev _ the_ge rs' sp' m' ba v' T' /\
      val_erasure v v' /\
      mem_event_list_erasure T T'.
  Proof.
    intros.
    induction Hbuiltin.
    - exists (rs' x), [::].
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - exists (Vint n), [::].
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - exists (Vlong n), [::].
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - exists (Vfloat n), [::].
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - exists (Vsingle n), [::].
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - eapply mem_loadv_erased in H; eauto.
      destruct H as [v' [Hloadv' Hval]].
      eapply loadbytes_erasure in H1; eauto.
      destruct H1 as [bytes' [Hloadbytes' Hmemval]].
      assert (Val.offset_ptr sp' ofs = Val.offset_ptr sp ofs)
        by (unfold Val.offset_ptr in H3;
            destruct sp; try discriminate;
            simpl in Hsp; subst; reflexivity).
      exists v', [:: Read b (Ptrofs.unsigned z) (size_chunk chunk) bytes'].
      split; [econstructor; eauto | split; eauto with val_erasure regs_erasure].
      rewrite H. assumption.
      rewrite H3 in Hloadv'.
      simpl in Hloadv'.
      eapply Mem.load_loadbytes in Hloadv'.
      destruct Hloadv' as [? [Hloadbytes'' Hval_eq]].
      subst.
      rewrite Hloadbytes' in Hloadbytes''.
      inv Hloadbytes''.
      reflexivity.
      rewrite H; assumption.
      do 2 econstructor;
        now eauto.
    - exists (Val.offset_ptr sp' ofs), [::].
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - eapply mem_loadv_erased in H; eauto.
      destruct H as [v' [Hloadv' Hval]].
      eapply loadbytes_erasure in H1; eauto.
      destruct H1 as [bytes' [Hloadbytes' Hmemval]].
      exists v', [:: Read b (Ptrofs.unsigned z) (size_chunk chunk) bytes'].
      split; [econstructor; eauto | split; eauto with val_erasure regs_erasure].
      rewrite H3 in Hloadv'.
      simpl in Hloadv'.
      eapply Mem.load_loadbytes in Hloadv'.
      destruct Hloadv' as [? [Hloadbytes'' Hval_eq]].
      subst.
      rewrite Hloadbytes' in Hloadbytes''.
      inv Hloadbytes''.
      reflexivity.
      do 2 econstructor;
        now eauto.
    - do 2 eexists.
      split;
        [now econstructor |split; eauto with val_erasure regs_erasure; now econstructor].
    - destruct IHHbuiltin1 as [v1' [T1' [? [? ?]]]], IHHbuiltin2 as [v2' [T2' [? [? ?]]]].
      exists (Val.longofwords v1' v2'), (T1' ++ T2').
      split;
        [econstructor; now eauto |].
      split; eauto with val_erasure regs_erasure.
      eapply mem_event_list_erasure_cat; now eauto.
    - destruct IHHbuiltin1 as [v1' [T1' [? [? ?]]]], IHHbuiltin2 as [v2' [T2' [? [? ?]]]].
      exists (if Archi.ptr64 then Val.addl v1' v2' else Val.add v1' v2'), (T1' ++ T2').
      split;
        [econstructor; now eauto |].
      split;
        [destruct Archi.ptr64; now eauto with val_erasure regs_erasure |
         eapply mem_event_list_erasure_cat; now eauto].
  Qed.

  Lemma eval_builtin_args_ev_erasure:
    forall rs rs' sp sp' m m' ba vs T
      (Hrs: regs_erasure rs rs')
      (Hsp: val_erasure sp sp')
      (Hmem: mem_erasure m m')
      (Hbuiltin_ev: Asm_event.eval_builtin_args_ev _ the_ge rs sp m ba vs T),
    exists vs' T',
      Asm_event.eval_builtin_args_ev _ the_ge rs' sp' m' ba vs' T' /\
      val_erasure_list vs vs' /\
      mem_event_list_erasure T T'.
  Proof.
    induction ba; intros.
    - inversion Hbuiltin_ev; subst.
      exists [::], [::].
      repeat split; now econstructor.
    - inversion Hbuiltin_ev; subst.
      eapply eval_builtin_arg_ev_erasure in H1; eauto.
      destruct H1 as [v' [T1' [Hbuiltin' [Hv HT1]]]].
      destruct (IHba vl T2 Hrs Hsp Hmem H4) as [vs' [T2' [Hbuiltins [Hvs HT2']]]].
      exists (v' :: vs'), (T1' ++ T2').
      repeat (split; econstructor; eauto with val_erasure).
      eapply mem_event_list_erasure_cat; assumption.
  Qed.

  Lemma builtin_event_erasure:
    forall ef m1 m1' vs1 vs1' T1
      (Hmem: mem_erasure m1 m1')
      (Hval_erasure: val_erasure_list vs1 vs1')
      (Hbuiltin: Asm_event.builtin_event ef m1 vs1 T1),
    exists T1',
      Asm_event.builtin_event ef m1' vs1' T1' /\
      mem_event_list_erasure T1 T1'.
  Proof.
    intros.
    inv Hbuiltin.
    remember (Mem.alloc m1' (-size_chunk Mptr) (Ptrofs.unsigned n)) eqn:ALLOC'.
    destruct p as [m2'' b2'].
    symmetry in ALLOC'.
    - pose proof ALLOC' as Hmem''.
      eapply alloc_erasure' in Hmem''; eauto.
      destruct Hmem'' as [Hmem'' ?]; subst.
      eapply Mem.storebytes_store in ST; eauto.
      eapply  mem_store_erased' in ST; eauto with val_erasure.
      destruct ST as [m2' [Hstore' Hm']].
      eapply Mem.store_storebytes in Hstore'.
      exists [:: Alloc b2' (- size_chunk Mptr) (Ptrofs.unsigned n);
         Write b2' (- size_chunk Mptr) (encode_val Mptr (Vptrofs n))].
      inv Hval_erasure. inv H3. inv H1.
      now repeat (econstructor; eauto with val_erasure).
    - eapply loadbytes_erasure in LB; eauto.
      destruct LB as [bytes' [Hload' Hbytes']].
      eapply mem_free_erasure' in FR; eauto.
      destruct FR as [m2' [Hfree Hmem']].
      exists
      [:: Read b (Ptrofs.unsigned lo - size_chunk Mptr) (size_chunk Mptr) bytes';
       Free
         [:: (b, Ptrofs.unsigned lo - size_chunk Mptr,
              Ptrofs.unsigned lo + Ptrofs.unsigned sz)]].
      inv Hval_erasure.
      inv H1. inv H3.
      split;
        repeat (econstructor; eauto with val_erasure).
      unfold Vptrofs in *.
      destruct Archi.ptr64; simpl in SZ;
        apply decode_val_erasure with (chunk := Mptr) in Hbytes';
        rewrite <- SZ in Hbytes';
        simpl in Hbytes';
        now auto.
    -  eapply loadbytes_erasure with (m' := m1') in LB; eauto.
       destruct LB as [bytes' [LB' Hbytes]].
       eapply storebytes_erasure in ST; eauto.
       destruct ST as [m2' [ST' Hmem']].
       exists
       [:: Read bsrc (Ptrofs.unsigned osrc) sz bytes';
        Write bdst (Ptrofs.unsigned odst) bytes'].
       inv Hval_erasure.
       inv H1. inv H3. inv H4. inv H1.
       split; repeat (econstructor; eauto with val_erasure).
    - destruct ef; try (now exfalso);
        try (eexists; split; econstructor; eauto with val_erasure);
        try econstructor.
  Qed.

  (* Axiom extsem_erasure: *)
  (*   forall name sg vs1 vs1' t vres m1 m1' m2 *)
  (*     (Hmem: mem_erasure m1 m1') *)
  (*     (Hval_erasure: val_erasure_list vs1 vs1') *)
  (*     (Hextcall: external_functions_sem name sg the_ge vs1 m1 t vres m2), *)
  (*   exists vres' m2', *)
  (*     external_functions_sem name sg the_ge vs1' m1' t vres' m2' /\ *)
  (*     val_erasure vres vres' /\ *)
  (*     mem_erasure m2 (erasePerm m2'). *)

  (* Axiom inline_assembly_erasure: *)
  (*   forall text sg vs1 vs1' t vres m1 m1' m2 *)
  (*     (Hmem: mem_erasure m1 m1') *)
  (*     (Hval_erasure: val_erasure_list vs1 vs1') *)
  (*     (Hextcall: inline_assembly_sem text sg the_ge vs1 m1 t vres m2), *)
  (*   exists vres' m2', *)
  (*     inline_assembly_sem text sg the_ge vs1' m1' t vres' m2' /\ *)
  (*     val_erasure vres vres' /\ *)
  (*     mem_erasure m2 (erasePerm m2'). *)
  
  Lemma external_call_erasure:
    forall ef m1 m1' vs1 vs1' t m2 vres
      (Hef: match ef with
            | EF_memcpy _ _ | EF_malloc | EF_free => True
            | _ => False
            end)
      (Hmem: mem_erasure m1 m1')
      (Hval_erasure: val_erasure_list vs1 vs1')
      (Hextcall: external_call ef the_ge vs1 m1 t vres m2),
    exists vres' m2',
      external_call ef the_ge vs1' m1' t vres' m2' /\
      val_erasure vres vres' /\
      mem_erasure m2 (erasePerm m2').
  Proof.
    intros.
    destruct ef; simpl in *;
      try (exfalso; now eauto).
    - inv Hextcall.
      remember (Mem.alloc m1' (- size_chunk Mptr) (Ptrofs.unsigned sz)).
      destruct p as [m0' b'].
      symmetry in Heqp.
      eapply alloc_erasure' with (m := m1) (m' := m1') in H; eauto.
      destruct H; subst.
      inv Hval_erasure.
      inv H3; inv H5.
      eapply mem_store_erased' in H0; eauto with val_erasure.
      destruct H0 as [m2' [? ?]].
      do 2 eexists.
      split. econstructor; eauto.
      split; eauto using mem_erasure'_erase with val_erasure.
    - inv Hextcall.
      eapply mem_load_erased in H; eauto.
      destruct H as [v' [Hload' Hv']].
      inv Hval_erasure.
      inv H3; inv H5.
      inv Hv'.
      eapply mem_free_erasure' in H1; eauto.
      destruct H1 as [m2' [? ?]].
      do 2 eexists.
      split; [econstructor; eauto|].
      split; eauto using mem_erasure'_erase with val_erasure.
    - inv Hextcall.
      inv Hval_erasure.
      inv H9; inv H11. inv H12. inv H9.
      eapply loadbytes_erasure in H5; eauto.
      destruct H5 as [bytes' [Hload' Hbytes]].
      eapply storebytes_erasure in H6; eauto.
      destruct H6 as [m2' [Hstore' ?]].
      do 2 eexists.
      split; [econstructor; eauto|].
      split; eauto using mem_erasure_idempotent with val_erasure.
  Qed.
  
  Lemma evstep_erase:
    forall c1 c1' c2 ev m1 m1' m2
      (HeraseCores: core_erasure c1 c1')
      (HerasedMem: mem_erasure m1 m1')
      (Hstep: ev_step semSem c1 m1 ev c2 m2),
    exists c2' m2' ev',
      ev_step semSem c1' m1' ev' c2' m2' /\
      core_erasure c2 c2' /\
      mem_erasure m2 (erasePerm m2') /\
      mem_event_list_erasure ev ev'.
  Proof with eauto with val_erasure mem_erasure regs_erasure trace_erasure.
    intros.
    destruct c1 as [rs1 cm1]; simpl in *;
      destruct c1' as [rs1' cm1'].
    inversion Hstep.
    - subst rs m0 m ev c2 m'.
      assert (Hpc' : rs1' PC = Vptr b ofs)
        by (erewrite get_reg_erasure in H1; eauto;
            rewrite H1; discriminate).
      destruct (exec_instr_erased _ _ HeraseCores HerasedMem H9 H4)
        as (rs2' & m2' & ev' & Hexec' & Hexec_ev' & Hrs2 & Hm2 & Hev_erasure).
      exists (State rs2' m2'), m2', ev'.
      repeat match goal with
            | [ |- _ /\ _] =>
              split; simpl; eauto with val_erasure regs_erasure mem_erasure
             end.
      econstructor...
    - subst.
      assert (Hpc' : rs1' PC = Vptr b ofs)
          by (erewrite get_reg_erasure in H1; eauto;
              rewrite H1; discriminate).
      pose proof H4 as Hargs.
      eapply eval_builtin_args_ev_erasure with (sp' := rs1' RSP) in H4...
      destruct H4 as [vargs' [T1' [Hargs_ev [Hargs_erasure Htrace_erasure]]]].
      eapply builtin_event_erasure in H5...
      destruct H5 as [T2' [Hbuiltin  Htrace_erasure2]].
      eapply external_call_erasure in H6; eauto.
      destruct H6 as [vres' [m2' [Hextcall' [Hvres_erasure Hmem2']]]].
      exists (State
           (nextinstr_nf
              (set_res res vres'
                       (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs1'))) m2'),
      m2', (T1' ++ T2').
      split.
      econstructor 2; now eauto.      
      split.
      simpl.
      eapply regs_erasure_set.
      eapply regs_erasure_undef.
      eapply regs_erasure_set_res...
      eauto 15 with val_erasure regs_erasure.
      split;
        now eauto using mem_event_list_erasure_cat.
      unfold Asm_core.safe_genv in Hsafe.
      eapply Asm_event.eval_builtin_args_ev_eval_builtin_args in Hargs.
      pose proof (Hsafe b ofs _ _ _ H2 H3 Hargs H6).
      destruct ef;
        auto;
        destruct H as [? [? ?]];
        now exfalso.
  Qed.

  Instance X86Erasure : CoreErasure.CoreErasure :=
    { core_erasure := core_erasure;
      core_erasure_refl := core_erasure_refl;
      after_external_erase := after_external_erase;
      erasure_initial_core := erasure_initial_core;
      halted_erase := halted_erase;
      evstep_erase := evstep_erase
    }.
  intros.
  simpl in *.
  unfold set_mem in *.
  destruct c, c'.
  eapply at_external_erase;
    now eauto.
    Qed.

  End X86CoreErasure.
End X86CoreErasure.



