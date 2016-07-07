Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

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

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_context.
Require Import concurrency.fineConc_safe.
Require Import Coqlib.
Require Import msl.Coqlib2.


Import dry_context SEM mySchedule DryMachine DryMachine.ThreadPool.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".


(** ** Erasure from FineConc to X86-SC*)
Module X86Erasure.

  Require Import ccc26x86.Asm ccc26x86.Asm_coop.
  Import event_semantics.
  (*TODO: Things here should be abstracted to support similar
  erasures, e.g. for Power, but due to time constraints I am going to
  do it right away for now*)
  
  (**  The erased memory is identical for
       everything but permissions. *)
  Local Notation "a # b" := (PMap.get b a) (at level 1).

  Record erasedMem (m m': mem) :=
    { perm_le:
        forall b ofs k,
          (Mem.mem_access m')#b ofs k = Some Freeable;
      erased_contents:
       (Mem.mem_contents m') = (Mem.mem_contents m);
      erased_nb: Mem.nextblock m = Mem.nextblock m'
    }.

  Definition erased_val v1 v2 : Prop :=
    match v1, v2 with
    | Vundef, _ => True
    | v1, v2 => v1 = v2
    end.
  
  Inductive erased_val_list : seq.seq val -> seq.seq val -> Prop :=
    erased_val_nil : erased_val_list [::] [::]
  | erased_val_cons : forall (v v' : val) (vl vl' : seq.seq val),
      erased_val v v' ->
      erased_val_list vl vl' ->
      erased_val_list (v :: vl) (v' :: vl').
    
  Definition erased_reg (r:PregEq.t) (rs rs' : regset) : Prop :=
    erased_val (Pregmap.get r rs) (Pregmap.get r rs').
  
  Definition erased_regs rs rs' : Prop :=
    forall r, erased_reg r rs rs'.

  Definition erased_loader (l l' : load_frame) : Prop :=
    l = l'.

  Definition erasedCores c c' :=
    match c, c' with
    | State rs loader, State rs' loader' =>
      erased_regs rs rs' /\ erased_loader loader loader'
    | Asm_CallstateIn vf args tys retty, Asm_CallstateIn vf' args' tys' retty' =>
      vf = vf' /\ erased_val_list args args' /\
      tys = tys' /\ retty = retty'
    | Asm_CallstateOut ef vals rs loader, Asm_CallstateOut ef' vals' rs' loader' =>
      ef = ef' /\ erased_val_list vals vals'
      /\ erased_regs rs rs' /\ erased_loader loader loader'
    | _, _ => False
    end.

  Definition erasedCtl c c' : Prop :=
    match c, c' with
    | Kinit vf arg, Kinit vf' arg' =>
      erased_val vf vf' /\ erased_val arg arg'
    | Krun c, Krun c' =>
      erasedCores c c'
    | Kblocked c, Kblocked c' =>
      erasedCores c c'
    | Kresume c arg, Kresume c' arg' =>
      erasedCores c c' /\ erased_val arg arg'
    | _, _  => False
    end.

  Inductive erased_threadPool tp (tp' : ErasedMachine.ThreadPool.t) :=
    | ErasedPool :
        num_threads tp = ErasedMachine.ThreadPool.num_threads tp' ->
        (forall i (cnti: containsThread tp i)
           (cnti': ErasedMachine.ThreadPool.containsThread tp' i),
            erasedCtl (getThreadC cnti)
                      (ErasedMachine.ThreadPool.getThreadC cnti')) ->
        erased_threadPool tp tp'.

  Lemma erased_val_refl:
    forall v, erased_val v v.
  Proof.
    destruct v; simpl; auto.
  Qed.

  Hint Immediate erased_val_refl : erased.
  Hint Constructors erased_val_list : erased.
  
  Lemma erased_val_list_refl:
    forall vs, erased_val_list vs vs.
  Proof with eauto with erased.
    induction vs; simpl...
  Qed.

  Lemma erased_regs_refl:
    forall rs, erased_regs rs rs.
  Proof with eauto with erased.
    intros rs r;
    unfold erased_reg...
  Qed.

  Lemma erased_loader_refl:
    forall loader, erased_loader loader loader.
  Proof.
    unfold erased_loader; auto.
  Qed.
  
  Hint Immediate erased_regs_refl erased_loader_refl
       erased_val_list_refl : erased.

  Lemma erasedCores_refl:
    forall c, erasedCores c c.
  Proof with eauto with erased.
    destruct c; simpl;
    repeat split...
  Qed.

  Hint Immediate erasedCores_refl: erased.
  
  Lemma erasedCtl_refl:
    forall c, erasedCtl c c.
  Proof with eauto with erased.
    destruct c; simpl...
  Qed.
  
  Lemma erased_updLockSet:
    forall tp tp' addr addr' rmap rmap',
      erased_threadPool tp tp' ->
      erased_threadPool (updLockSet tp addr rmap)
                         (ErasedMachine.ThreadPool.updLockSet tp' addr' rmap').
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.
  
  Lemma erased_updThread:
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp' i) c c' pmap pmap',
      erased_threadPool tp tp' ->
      erasedCtl c c' ->
      erased_threadPool (updThread cnti c pmap)
                        (ErasedMachine.ThreadPool.updThread cnti' c' pmap').
  Proof.
    intros.
    inversion H.
    constructor; auto.
    intros.
    destruct (i0 == i) eqn:Heq; move/eqP:Heq=>Heq.
    subst. rewrite gssThreadCode.
    rewrite ErasedMachine.ThreadPool.gssThreadCode; auto.
    rewrite gsoThreadCode; auto.
    rewrite ErasedMachine.ThreadPool.gsoThreadCode; auto.
  Qed.

  Lemma erased_addThread:
    forall tp tp' i (cnti: containsThread tp i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp' i) v arg v' arg' pmap pmap',
      erased_threadPool tp tp' ->
      erased_val v v' ->
      erased_val arg arg' ->
      erased_threadPool (addThread tp v arg pmap)
                        (ErasedMachine.ThreadPool.addThread tp' v arg pmap').
  Proof with eauto with erased.
    intros.
    inversion H.
    constructor.
    unfold addThread, ErasedMachine.ThreadPool.addThread; simpl. rewrite H2; auto.
    intros.
    assert (cnti00 := cntAdd' _ _ _  cnti0).
    assert (cnti0'0 := ErasedMachine.ThreadPool.cntAdd' _ _ _  cnti'0).
    destruct cnti00 as [[cnti00 ?] | Heq];
      destruct cnti0'0 as [[cnti0'0 ?] | ?].
    - erewrite gsoAddCode with (cntj := cnti00) by eauto.
      erewrite ErasedMachine.ThreadPool.gsoAddCode with (cntj := cnti0'0) by eauto.
      eauto.
    - exfalso; subst; apply H4.
      destruct (num_threads tp), (ErasedMachine.ThreadPool.num_threads tp');
        simpl; inversion H2; auto.
    - exfalso; subst; apply H4.
      destruct (num_threads tp), (ErasedMachine.ThreadPool.num_threads tp');
        simpl; inversion H2; auto.
    - subst. erewrite gssAddCode by eauto.
      erewrite ErasedMachine.ThreadPool.gssAddCode; eauto.
      simpl...
  Qed.
  
  Lemma erased_remLockSet:
    forall tp tp' addr addr',
      erased_threadPool tp tp' ->
      erased_threadPool (remLockSet tp addr)
                         (ErasedMachine.ThreadPool.remLockSet tp' addr').
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Lemma mem_load_erased:
    forall chunk m m' b ofs pmap v
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hload: Mem.load chunk (restrPermMap Hlt) b ofs = Some v)
      (Herased: erasedMem m m'),
      Mem.load chunk m' b ofs = Some v.
  Proof.
    intros.
    inversion Herased.
    assert (Hreadable := Mem.load_valid_access _ _ _ _ _ Hload).
    destruct Hreadable.
    assert (Hreadable': Mem.valid_access m' chunk b ofs Readable).
    { split; auto.
      intros ? ?.
      unfold Mem.perm.
      rewrite perm_le0.
      simpl; constructor.
    }
    Transparent Mem.load.
    unfold Mem.load in *.
    destruct (Mem.valid_access_dec m' chunk b ofs Readable);
      try by exfalso.
    destruct (Mem.valid_access_dec (restrPermMap Hlt) chunk b ofs Readable);
      try by discriminate.
    simpl in *.
    rewrite erased_contents0; auto.
    Opaque Mem.load.
  Qed.

  Lemma mem_store_erased:
    forall chunk m m' b ofs pmap v m2
      (Hv: v <> Vundef)
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hstore: Mem.store chunk (restrPermMap Hlt) b ofs v = Some m2)
      (Herased: erasedMem m m'),
    exists m2', Mem.store chunk m' b ofs v = Some m2'
           /\ erasedMem m2 m2'.
  Proof.
    intros.
    destruct Herased.
    assert (Haccess := Mem.store_valid_access_3 _ _ _ _ _ _ Hstore).
    destruct Haccess.
    assert (Haccess' : Mem.valid_access m' chunk b ofs Writable).
    { split; auto.
      intros ? ?.
      unfold Mem.perm.
      rewrite perm_le0.
      simpl; constructor.
    }
    Transparent Mem.store.
    unfold Mem.store in *.
    destruct (Mem.valid_access_dec m' chunk b ofs Writable); try by exfalso.
    destruct (Mem.valid_access_dec (restrPermMap Hlt) chunk b ofs Writable);
      try by discriminate. simpl in Hstore.
    inv Hstore.
    eexists; split; eauto.
    constructor; simpl; auto.
    rewrite <- erased_contents0.
      reflexivity.
    Opaque Mem.store.
  Qed.
  
  Hint Resolve erased_updLockSet erased_updThread
       erased_addThread erased_remLockSet mem_store_erased: erased.

  Lemma erased_val_list_decode:
    forall vals vals' typs,
      erased_val_list vals vals' ->
      erased_val_list (decode_longs typs vals) (decode_longs typs vals').
  Proof.
    intros.
    generalize dependent vals.
    generalize dependent vals'.
    induction typs; intros; simpl;
    first by constructor.
    destruct vals;
      destruct a; inversion H; subst;
      try constructor; eauto.
    destruct vals; inversion H4; subst.
    constructor.
    unfold Val.longofwords.
    destruct v;
      constructor; eauto;
      inv H2; try constructor.
    unfold erased_val in H3.
    destruct v0; subst; auto;
    constructor.
  Qed.

  (** ** Lemmas about erased values*)
  Lemma erased_val_hiword:
    forall v v',
      erased_val v v' ->
      erased_val (Val.hiword v) (Val.hiword v').
  Proof.
    intros;
    destruct v; simpl; inv H; auto.
  Qed.

  Lemma erased_val_loword:
    forall v v',
      erased_val v v' ->
      erased_val (Val.loword v) (Val.loword v').
  Proof.
    intros;
    destruct v; simpl; inv H; auto.
  Qed.

  Lemma erased_regs_set:
    forall rs rs' v v' r
      (Hrs_ren: erased_regs rs rs')
      (Hval: erased_val v v'),
      erased_regs (rs # r <- v) (rs' # r <- v').
  Proof.
    intros.
    intros r'.
    unfold erased_reg.
    do 2 rewrite Pregmap.gsspec.
    destruct (Pregmap.elt_eq r' r); auto.
    eapply Hrs_ren.
  Qed.

  (*NOTE THIS IS DUPLICATED WITH X86_INJ*)
  Lemma set_regs_empty_1:
    forall regs rs,
      set_regs regs [::] rs = rs.
  Proof.
    intros;
    induction regs; by reflexivity.
  Qed.
  
  Hint Resolve erased_val_hiword erased_val_loword erased_regs_set : erased.

  (** ** Result about at_external, after_external and initial_core *)
  Lemma at_external_erase:
    forall c c' (Herase: erasedCores c c'),
      match at_external Sem c, at_external Sem c' with
      | Some (ef, sig, vs), Some (ef', sig', vs') =>
        ef = ef' /\ sig = sig' /\ erased_val_list vs vs'
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros.
    unfold erasedCores in *.
    destruct c, c'; try (by exfalso);
    repeat match goal with
    | [H: _ /\ _ |- _] => destruct H
           end; subst;
    unfold at_external; simpl; auto.
    destruct (BuiltinEffects.observableEF_dec f0); auto.
    split; auto.
    split; auto.
    eapply erased_val_list_decode; eauto.
  Qed.

  Lemma after_external_erase :
    forall v v' c c' c2
      (HeraseCores: erasedCores c c')
      (HeraseVal: erased_val v v')
      (Hafter_external: after_external SEM.Sem (Some v) c = Some c2),
    exists (c2' : state),
      after_external SEM.Sem (Some v') c' = Some c2' /\
      erasedCores c2 c2'.
  Proof.
    intros.
    unfold after_external in *.
    simpl in *.
    unfold Asm_after_external in *.
    destruct c; try discriminate.
    inv Hafter_external.
    unfold erasedCores in HeraseCores.
    destruct c'; try by exfalso.
    destruct HeraseCores as (? & ? & ? &?); subst.
    unfold erased_loader in H2; subst.
    eexists; split; eauto.
    simpl.
    split; [|unfold erased_loader; auto].      
    destruct (loc_external_result (ef_sig f0)) as [|r' regs];
      simpl.
    eapply erased_regs_set; eauto.
    eapply H1.
    destruct (sig_res (ef_sig f0)) as [ty|];
      try destruct ty;
      simpl;
      try do 2 rewrite set_regs_empty_1;
      repeat apply erased_regs_set; eauto;
      try apply H1.
    destruct regs as [|r'' regs'']; simpl;
    eauto with erased.
    do 2 rewrite set_regs_empty_1;
      eauto with erased.
  Qed.

  Lemma erasure_initial_core:
    forall ge v arg v' arg' c
      (Hv: erased_val v v')
      (Harg: erased_val arg arg')
      (Hinit: initial_core SEM.Sem ge v [:: arg] = Some c),
      initial_core ErasedMachine.ThreadPool.SEM.Sem ge v' [:: arg'] = Some c.
  Proof.
    intros.
    unfold initial_core in *; simpl in *.
    unfold  Asm_initial_core in *.
    destruct v; try discriminate.
    inversion Hv; subst.
    destruct (Int.eq_dec i Int.zero); try discriminate.
    destruct (Genv.find_funct_ptr ge b); try discriminate.
    destruct f; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr eqn:?
    end; try discriminate.
    apply andb_true_iff in Heqb0.
    destruct Heqb0.
    apply andb_true_iff in H.
    destruct H.
    unfold val_casted.vals_defined in *.
    destruct arg; (try discriminate);
    inv Harg; rewrite H0 H; simpl;
    auto.
  Qed.


  (** Simulation of synchronization steps between erased states*)

  Lemma syncStep_erase:
    forall ge tp1 tp1' m1 m1' tp2 m2 i ev
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (HerasedMem: erasedMem m1 m1')
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': ErasedMachine.mem_compatible tp1' m1')
      (Hstep: syncStep ge cnti Hcomp1 tp2 m2 ev),
    exists tp2' m2',
      ErasedMachine.syncStep ge cnti' Hcomp1' tp2' m2' ev /\
      erased_threadPool tp2 tp2' /\ erasedMem m2 m2'.
  Proof with eauto with erased.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').      
    inversion Hstep; subst;
    match goal with
    | [H: erasedCtl ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
      rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
    end; try (by exfalso);
    try match goal with
        | [H: Mem.load _ _ _ _ = Some _ |- _] =>
          eapply mem_load_erased in H; eauto
        end;
    try match goal with
        | [H: Mem.store _ _ _ _ _ = Some _ |- _] =>
          eapply mem_store_erased in H; eauto;
          destruct Hstore as [m2' [Hstore HerasedMem']]
        end;
    try match goal with
        | [|- _ <> Vundef] => intro Hcontra; discriminate
        end;
    match goal with
    | [H: at_external _ _ = _, H1: erasedCores _ _ |- _] =>
      pose proof (at_external_erase _ _ H1);
        match goal with
          | [H2: match at_external _ _ with _ => _ end |- _] =>
            rewrite H in H2;
              match goal with
              | [H3: match at_external ?E1 ?E2 with _ => _ end |- _] =>
                destruct (at_external E1 E2) as [[[? ?] ?]|] eqn:?; try by exfalso
              end
        end
    end;
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [H: erased_val_list _ _ |- _] =>
             inv H
           | [H: erased_val (Vptr _ _) _ |- _] => inv H
           end; subst.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m2'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m2'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists (ErasedMachine.ThreadPool.addThread
           (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef))
           (Vptr b ofs) v'0 tt), m1'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto. rewrite Hnum. auto.
      intros j cntj cntj'.
      assert (cntj0 := cntAdd' _ _ _ cntj).
      destruct cntj0 as [[cntj0 ?] | Heq].
      + (* case it's an old thread*)
        erewrite @gsoAddCode with (cntj := cntj0) by eauto.
        assert (cntj00 := cntUpdate' _ _ _ cntj0).
        assert (cntj00': ErasedMachine.ThreadPool.containsThread tp1' j)
          by (unfold containsThread,ErasedMachine.ThreadPool.containsThread;
               rewrite <- Hnum; auto).
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC (Kresume c0 Vundef)
                                                              cnti' cntj00').
        erewrite @ErasedMachine.ThreadPool.gsoAddCode with (cntj := cntj0')
          by eauto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        * subst.
          rewrite gssThreadCode.
          rewrite ErasedMachine.ThreadPool.gssThreadCC.
          simpl; auto.
        * rewrite gsoThreadCode; auto.
          erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj00')
            by eauto.
          inversion HerasePool; eauto.
      + (*case j is the just addded thread *)
        subst.
        erewrite gssAddCode by (unfold latestThread; reflexivity).
        erewrite ErasedMachine.ThreadPool.gssAddCode
          by (unfold ErasedMachine.ThreadPool.latestThread;
               simpl; rewrite Hnum; auto).
        simpl; auto.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m2'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kresume c0 Vundef)), m1'.
      split; [econstructor; eauto | split; eauto].
      constructor. simpl; eauto.
      intros j cntj cntj'.
      rewrite gRemLockSetCode.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        rewrite gssThreadCode.
        rewrite ErasedMachine.ThreadPool.gssThreadCC.
        simpl; auto.
      + rewrite gsoThreadCode; auto.
        assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
        erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
          by eauto.
        inversion HerasePool; eauto.
    - exists tp1', m1'.
      split; [econstructor; eauto | split; eauto].
  Qed.

  Lemma evstep_erase:
    forall ge c1 c1' c2 ev m1 m1' m2
      (HeraseCores: erasedCores c1 c1')
      (HerasedMem: erasedMem m1 m1')
      (Hstep: ev_step SEM.Sem ge c1 m1 ev c2 m2),
    exists c2' m2',
      ev_step ErasedMachine.ThreadPool.SEM.Sem ge c1' m1' ev c2' m2' /\
      erasedCores c2 c2' /\ erasedMem m2 (erasePerm m2').
  Proof.
  Admitted.
  
  Lemma threadStep_erase:
    forall ge tp1 tp1' m1 m1' tp2 m2 i ev
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (HerasedMem: erasedMem m1 m1')
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': ErasedMachine.mem_compatible tp1' m1')
      (Hstep: threadStep ge cnti Hcomp1 tp2 m2 ev),
    exists tp2' m2',
      ErasedMachine.threadStep ge cnti' Hcomp1' tp2' m2' ev /\
      erased_threadPool tp2 tp2' /\ erasedMem m2 (erasePerm m2').
  Proof.
    intros.
    inversion Hstep; subst.
    Admitted.

  Ltac pf_cleanup :=
    repeat match goal with
           | [H1: invariant ?X, H2: invariant ?X |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
               subst H2
           | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M, H2: containsThread ?TP ?M |- _] =>
           assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
             apply cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply cnt_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
             apply cntUpdate' in H2;
               assert (H1 = H2) by (by eapply cnt_irr); subst H2
         end.

  (** ** Result about startStep, resumeStep and suspendStep *)
  
  Lemma startStep_erasure:
  forall ge tp1 tp1' m1 m1' tp2 i
    (HerasePool: erased_threadPool tp1 tp1')
    (cnti: containsThread tp1 i)
    (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
    (HerasedMem: erasedMem m1 m1')
    (Hcomp1: mem_compatible tp1 m1)
    (Hcomp1': ErasedMachine.mem_compatible tp1' m1')
    (Hstep: FineConc.start_thread ge cnti tp2),
  exists tp2',
    X86SC.start_thread ge cnti' tp2' /\
    erased_threadPool tp2 tp2'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
    match goal with
      [H: erasedCtl ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
      rewrite H1 in H; simpl in H;
      destruct Expr2 eqn:?
    end; try (by exfalso).
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [H: erased_val_list _ _ |- _] =>
             inv H
           | [H: erased_val (Vptr _ _) _ |- _] => inv H
           end; subst.
    eapply erasure_initial_core in Hinitial; eauto.
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c_new)).
    split; econstructor; eauto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl. apply erasedCores_refl.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Lemma resumeStep_erasure:
    forall tp1 tp1' tp2 i
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: FineConc.resume_thread cnti tp2),
    exists tp2',
      X86SC.resume_thread cnti' tp2' /\
      erased_threadPool tp2 tp2'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
      match goal with
        [H: erasedCtl ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    destruct Hthreads as [HeraseCores _].
    pose proof (at_external_erase _ _ HeraseCores).
    rewrite Hat_external in H.
    destruct X, p.
    destruct (at_external Sem c0) eqn:Hat_external'; try by exfalso.
    destruct p as [[? ?] ?].
    destruct H as [? [? ?]]; subst.
    eapply after_external_erase with (v' := Vint Int.zero) in Hafter_external;
      eauto with erased.
    destruct Hafter_external as [c2' [Hafter_external' HerasedCores']].
    
    

  Notation fstep := (corestep fine_semantics).
  Notation scstep := (corestep x86_sc_semantics).

  Lemma erasedPool_contains:
    forall tp1 tp1' 
      (HerasedPool: erased_threadPool tp1 tp1') i,
      containsThread tp1 i <-> ErasedMachine.ThreadPool.containsThread tp1' i.
  Proof.
  Admitted.
  
  Lemma sc_erasure:
    forall ge tp1 tp1' i U tr tr' m1 m1' tp2 m2
      (HerasePool: erased_threadPool tp1 tp1')
      (HerasedMem: erasedMem m1 m1')
      (Hfstep: fstep ge (i :: U, tr, tp1) m1 (U, tr', tp2) m2),
    exists tp2' m2',
      scstep ge (i :: U, tr, tp1') m1' (U, tr', tp2') m2' /\
      erased_threadPool tp2 tp2' /\ erasedMem m2 m2'.
  Proof.
    intros.
    inversion Hfstep; simpl in *; subst;
    inv HschedN;
    try match goal with
        | [H: containsThread tp1 ?I |- _ ] =>
          assert (ErasedMachine.ThreadPool.containsThread tp1' I)
            by (eapply erasedPool_contains; eauto)
        end;
    assert (Hcomp1' : ErasedMachine.mem_compatible tp1' m1')
      by (unfold ErasedMachine.mem_compatible; auto).
    - assert (Hstep' := startStep_erasure HerasePool H HerasedMem Hcmpt I Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 1; simpl; eauto.
      split; eauto.
    -
   

      
      
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c)).
    split; econstructor; eauto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl. apply erasedCores_refl.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.
      
    - assert (Htstep' := threadStep_erase HerasePool H HerasedMem Hcomp1' Htstep).
      destruct Htstep' as [tp2' [m2' [Htstep' [HerasePool' HerasedMem']]]].
      exists tp2', (erasePerm m2').
      split.
      eapply X86SC.thread_step; eauto.
      split; eauto.

      Lemma erasedMem_dilute_1:
        forall m m',
          erasedMem m m' ->
          erasedMem (DryMachine.diluteMem m) m'.
      Admitted.

      eapply erasedMem_dilute_1; eauto.
    - admit.
    - assert (Hstep' := syncStep_erase HerasePool H HerasedMem Hcomp1' Htstep).
      destruct Hstep' as [tp2' [m2' [Hstep' [HerasePool' HerasedMem']]]].
      exists tp2', m2'.
      split.
      eapply X86SC.sync_step; eauto.
      split; eauto.
    - admit.
    - assert (~ ErasedMachine.ThreadPool.containsThread tp1' tid).
      { intros Hcontra.
        destruct HerasePool as [Hnum _].
        unfold containsThread, ErasedMachine.ThreadPool.containsThread in *.
        rewrite <- Hnum in Hcontra.
        auto.
      }
      exists tp1', m1'.
      split.
      econstructor 7; simpl; eauto.
      split; eauto.
  Admitted.
        


    Lemma startStep_erasure:
      forall 
    
    assert (X86SC.start_thread ge 
    
  
End X86Erasure.

(** ** Safety for X86-SC semantics *)
Module X86Safe.
  Import Asm Asm_coop event_semantics FineConcSafe Events.

  Definition sc_init f arg := initial_core x86_sc_semantics the_ge f arg.
  
  Notation sc_safe := (X86SC.fsafe the_ge).

  (*TODO: This will be very similar (what an irony) to
  similar_threadPool, but now we need a more invloved relation on
  cores that says that things may be more defined. Do we have one? *)
  
  Inductive erasePool (tpf:FineConc.machine_state) (tpsc:X86SC.machine_state) : Prop :=
  | ErasePool:
        num_threads tpf = ErasedMachine.ThreadPool.num_threads tpsc ->
        (forall i (pffi: containsThread tpf i)
           (pfsci: ErasedMachine.ThreadPool.containsThread tpsc i),
            getThreadC pffi = ErasedMachine.ThreadPool.getThreadC pfsci) ->
        erasePool tpf tpsc.

  (** The initial state of X86SC is an erasure of the initial state of
  the FineConc machine *)
  Lemma init_erasure:
    forall f arg U tpsc tpf
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf)),
      erasePool tpf tpsc.
  Proof.
    intros.
    unfold sc_init, tpf_init in *.
    simpl in *. unfold X86SC.init_machine, FineConc.init_machine in *.
    unfold init_mach, ErasedMachine.init_mach in *.
    simpl in *.
    destruct (Asm_initial_core the_ge f arg); try discriminate.
    destruct init_perm; try discriminate.
    inv HinitSC. inv HinitF.
    unfold initial_machine, ErasedMachine.initial_machine.
    simpl.
    econstructor; simpl; eauto.
  Qed.
    
  (** Erasure from FineConc to X86-SC.*)
  Conjecture x86sc_erasure:
    forall sched f arg U tpsc tpf m trace
      (Hmem: init_mem = Some m)
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf))
      (HsafeF: fsafe tpf m sched trace (size sched).+1),
      sc_safe tpsc (diluteMem m) sched trace (size sched).+1.

  (** Competing Events *)

  Definition sameLocation ev1 ev2 :=
    match location ev1, location ev2 with
    | Some (b1, ofs1, size1), Some (b2, ofs2, size2) =>
      b1 = b2 /\ exists ofs, Intv.In ofs (ofs1, (ofs1 + Z.of_nat size1)%Z) /\
                       Intv.In ofs (ofs2, (ofs2 + Z.of_nat size2)%Z)
    | _,_ => False
    end.
  
  Definition competes (ev1 ev2 : machine_event) : Prop :=
    thread_id ev1 <> thread_id ev2 /\
    sameLocation ev1 ev2 /\
    (is_internal ev1 ->
     is_internal ev2 ->
     action ev1 = Some Write \/ action ev2 = Some Write) /\
    (is_external ev1 \/ is_external ev2 ->
     action ev1 = Some Mklock \/ action ev1 = Some Freelock
     \/ action ev2 = Some Mklock \/ action ev2 = Some Freelock).

  (** Spinlock well synchronized*)
  Definition spinlock_synchronized (tr : X86SC.event_trace) :=
    forall i j ev1 ev2,
      i < j ->
      List.nth_error tr i = Some ev1 ->
      List.nth_error tr j = Some ev2 ->
      competes ev1 ev2 ->
      exists u v eu ev,
        i < u < v < j /\
        List.nth_error tr u = Some eu /\
        List.nth_error tr v = Some ev /\
        action eu = Some Release /\ action ev = Some Acquire /\
        location eu = location ev.

  (** Spinlock clean *)
  Definition spinlock_clean (tr : X86SC.event_trace) :=
    forall i j evi evj,
      i < j ->
      List.nth_error tr i = Some evi ->
      List.nth_error tr j = Some evj ->
      action evi = Some Mklock ->
      (~ exists u evu, i < u < j /\ List.nth_error tr u = Some evu /\
                  action evu = Some Freelock /\ location evu = location evi) ->
      sameLocation evj evi ->
      action evj <> Some Write /\ action evj <> Some Read.
  
End X86Safe.

  
  



