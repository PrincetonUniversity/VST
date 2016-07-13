(** ** Erasure from FineConc to a non-angelic SC machine*)

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
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.memory_lemmas.
Require Import concurrency.dry_context.
Require Import concurrency.fineConc_safe.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

(** ** Erasure of Values*)
Module ValErasure.

  Definition erased_val v1 v2 : Prop :=
    match v1, v2 with
    | Vundef, _ => True
    | v1, v2 => v1 = v2
    end.

  Definition erased_memval mv1 mv2 : Prop :=
    match mv1, mv2 with
    | Undef, _ => True
    | mv1, mv2 => mv1 = mv2
    end.
  
  Inductive erased_val_list : seq.seq val -> seq.seq val -> Prop :=
    erased_val_nil : erased_val_list [::] [::]
  | erased_val_cons : forall (v v' : val) (vl vl' : seq.seq val),
      erased_val v v' ->
      erased_val_list vl vl' ->
      erased_val_list (v :: vl) (v' :: vl').

  Inductive erased_memval_list : seq.seq memval -> seq.seq memval -> Prop :=
    erased_memval_nil : erased_memval_list [::] [::]
  | erased_memval_cons : forall (mv mv' : memval) (mvl mvl' : seq.seq memval),
      erased_memval mv mv' ->
      erased_memval_list mvl mvl' ->
      erased_memval_list (mv :: mvl) (mv' :: mvl').

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

  Lemma erased_val_cmp_bool:
    forall c v1 v1',
      v1 <> Vundef ->
      erased_val v1 v1' ->
      Val.cmp_bool c v1 Vzero = Val.cmp_bool c v1' Vzero.
  Proof.
    intros.
    destruct v1; try congruence.
  Qed.

  Hint Resolve erased_val_hiword erased_val_loword : erased.

End ValErasure.

(** ** Memory Erasure*)
Module MemErasure.

  Import ValErasure.
  
  (** The values of the erased memory may be more defined and its
       permissions are top.*)

  Local Notation "a # b" := (PMap.get b a) (at level 1).

  Record erasedMem (m m': mem) :=
    { perm_le:
        forall b ofs k,
          Mem.valid_block m' b -> 
          (Mem.mem_access m')#b ofs k = Some Freeable;
      erased_contents: forall b ofs,
          erased_memval (ZMap.get ofs ((Mem.mem_contents m) # b))
                        (ZMap.get ofs ((Mem.mem_contents m') # b));
      erased_nb: Mem.nextblock m = Mem.nextblock m'
    }.

  Lemma erasedMem_restr:
    forall m m' pmap (Hlt: permMapLt pmap (getMaxPerm m)),
      erasedMem m m' ->
      erasedMem (restrPermMap Hlt) m'.
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Lemma erasedMem_dilute_1:
    forall m m',
      erasedMem m m' ->
      erasedMem (setMaxPerm m) m'.
  Proof.
    intros.
    inversion H.
    constructor; auto.
  Qed.

  Lemma getN_erasure:
    forall m1 m2 b,
      erasedMem m1 m2 ->
      forall n ofs,
        Mem.range_perm m1 b ofs (ofs + Z_of_nat n) Cur Readable ->
        erased_memval_list
                     (Mem.getN n ofs (m1.(Mem.mem_contents)#b))
                     (Mem.getN n ofs (m2.(Mem.mem_contents)#b)).
  Proof.
    induction n; intros; simpl.
    constructor.
    rewrite inj_S in H0.
    destruct H.
    constructor.
    eapply erased_contents0; eauto.
    apply IHn. red; intros; apply H0; omega.
  Qed.

  Lemma decode_val_erasure:
    forall vl1 vl2 chunk,
      erased_memval_list vl1 vl2 ->
      erased_val (decode_val chunk vl1) (decode_val chunk vl2).
  Proof.
    Admitted.
  
  Lemma mem_load_erased:
    forall chunk m m' b ofs v
      (Hload: Mem.load chunk m b ofs = Some v)
      (Herased: erasedMem m m'),
    exists v',
      Mem.load chunk m' b ofs = Some v' /\
      erased_val v v'.
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
      eapply MemoryLemmas.load_valid_block in Hload.
      unfold Mem.valid_block in *. simpl in *.
      rewrite <- erased_nb0; auto.
    }
    exists (decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs
                                  (m'.(Mem.mem_contents)#b))).
    Transparent Mem.load.
    unfold Mem.load. split.
    apply pred_dec_true; auto.
    exploit Mem.load_result; eauto. intro. rewrite H1.
    apply decode_val_erasure; auto.
    apply getN_erasure; auto.
    rewrite <- size_chunk_conv.
    exploit Mem.load_valid_access; eauto. 
    Opaque Mem.load.
  Qed.

  Lemma inj_bytes_erasure :
    forall (bl : seq.seq byte),
      erased_memval_list (inj_bytes bl) (inj_bytes bl).
  Admitted.

  Lemma inj_value_erasure :
    forall (v1 v2 : val) (q : quantity),
      erased_val v1 v2 ->
      erased_memval_list (inj_value q v1) (inj_value q v2).
  Admitted.

  Lemma repeat_Undef_erasure_self :
    forall (n : nat),
      erased_memval_list (list_repeat n Undef) (list_repeat n Undef).
  Admitted.

  Lemma repeat_Undef_inject_encode_val :
    forall (chunk : memory_chunk) (v : val),
      erased_memval_list (list_repeat (size_chunk_nat chunk) Undef)
                         (encode_val chunk v).
  Admitted.

  Lemma encode_val_erasure:
    forall (v1 v2 : val) (chunk : memory_chunk),
      erased_val v1 v2 ->
      erased_memval_list (encode_val chunk v1)
                   (encode_val chunk v2).
  Proof.
    intros. 
    destruct v1; inversion H; subst; simpl; destruct chunk;
    auto using inj_bytes_erasure,  inj_value_erasure, repeat_Undef_erasure_self,
    repeat_Undef_inject_encode_val.    
    unfold encode_val. destruct v2; apply inj_value_erasure; auto.
    unfold encode_val. destruct v2; apply inj_value_erasure; auto.
  Qed.

  Lemma setN_erasure :
    forall (vl1 vl2 : seq.seq memval),
      erased_memval_list vl1 vl2 ->
      forall (p : Z) (c1 c2 : ZMap.t memval),
        (forall q : Z,
            erased_memval (ZMap.get q c1) (ZMap.get q c2)) ->
        forall q : Z,
          erased_memval (ZMap.get q (Mem.setN vl1 p c1))
                        (ZMap.get q (Mem.setN vl2 p c2)).
  Proof.
    induction 1; intros; simpl.
    auto.
    apply IHerased_memval_list; auto.
    intros. erewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
    rewrite ZMap.gss. auto.
    rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega.
  Qed.
  
  Lemma mem_store_erased:
    forall chunk m m' b ofs v v' m2
      (Hstore: Mem.store chunk m b ofs v = Some m2)
      (Herased: erasedMem m m')
      (Herased_val: erased_val v v') ,
    exists m2', Mem.store chunk m' b ofs v' = Some m2'
           /\ erasedMem m2 m2'.
  Proof.
    intros.
    destruct Herased.
    assert (Haccess := Mem.store_valid_access_3 _ _ _ _ _ _ Hstore).
    assert (Hvalid := Mem.valid_access_valid_block
                        _ _ _ _ (Mem.valid_access_implies
                                   _ _ _ _ _ Nonempty Haccess ltac:(constructor))).
    destruct Haccess.
    assert (Haccess' : Mem.valid_access m' chunk b ofs Writable).
    { split; auto.
      intros ? ?.
      unfold Mem.perm.
      rewrite perm_le0.
      simpl; constructor.
      unfold Mem.valid_block in *. simpl in *.
      rewrite <- erased_nb0; auto.
    }
    destruct (Mem.valid_access_dec m' chunk b ofs Writable); try by exfalso.
    destruct (Mem.valid_access_store _ _ _ _ v' Haccess') as [m2' Hstore'].
    exists m2'. split; auto.
    constructor.
    - intros.
      assert (Heq1 := MemoryLemmas.mem_store_max _ _ _ _ _ _ Hstore' b0 ofs0).
      assert (Heq2 := MemoryLemmas.mem_store_cur _ _ _ _ _ _ Hstore' b0 ofs0).
      do 2 rewrite getMaxPerm_correct in Heq1.
      do 2 rewrite getCurPerm_correct in Heq2.
      unfold permission_at in *.
      eapply Mem.store_valid_block_2 in H1; eauto.
      destruct k;
        [rewrite <- Heq1 | rewrite <- Heq2];
        eauto.
    - intros.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore').
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Hstore).
      rewrite ! PMap.gsspec.
      destruct (peq b0 b). subst b0.
      apply setN_erasure.
      apply encode_val_erasure; auto. intros. eauto.
      eauto.
    - erewrite Mem.nextblock_store with (m1 := m) by eauto.
      erewrite Mem.nextblock_store with (m2 := m2') (m1 := m') by eauto.
      eauto.
  Qed.
  
End MemErasure.

(** Erasure of cores *)
Module Type CoreErasure (SEM: Semantics).
  Import SEM ValErasure MemErasure event_semantics.
  
  Parameter erasedCores : C -> C -> Prop.
  Parameter erasedCores_refl: forall c, erasedCores c c.

  Parameter at_external_erase:
    forall c c' (Herase: erasedCores c c'),
      match at_external Sem c, at_external Sem c' with
      | Some (ef, sig, vs), Some (ef', sig', vs') =>
        ef = ef' /\ sig = sig' /\ erased_val_list vs vs'
      | None, None => True
      | _, _ => False
      end.

  Parameter after_external_erase:
    forall v v' c c' c2
      (HeraseCores: erasedCores c c')
      (HeraseVal: erased_val v v')
      (Hafter_external: after_external SEM.Sem (Some v) c = Some c2),
    exists c2',
      after_external SEM.Sem (Some v') c' = Some c2' /\
      erasedCores c2 c2'.
  
  Parameter erasure_initial_core:
    forall ge v arg v' arg' c
      (Hv: erased_val v v')
      (Harg: erased_val arg arg')
      (Hinit: initial_core Sem ge v [:: arg] = Some c),
      initial_core Sem ge v' [:: arg'] = Some c.
  
  Parameter halted_erase:
    forall c c'
      (HeraseCores: erasedCores c c')
      (Hhalted: halted SEM.Sem c),
      halted SEM.Sem c'.

  Parameter evstep_erase:
    forall ge c1 c1' c2 ev m1 m1' m2
      (HeraseCores: erasedCores c1 c1')
      (HerasedMem: erasedMem m1 m1')
      (Hstep: ev_step Sem ge c1 m1 ev c2 m2),
    exists c2' m2',
      ev_step Sem ge c1' m1' ev c2' m2' /\
      erasedCores c2 c2' /\ erasedMem m2 (erasePerm m2').

  Hint Resolve erasedCores_refl : erased.
  
End CoreErasure.

Module ThreadPoolErasure (SEM: Semantics)
       (Machines: MachinesSig with Module SEM := SEM)
       (CE : CoreErasure SEM).
  Import ValErasure CE
         Machines DryMachine ThreadPool.
  
  Definition erasedCtl c c' : Prop :=
    match c, c' with
    | Kinit vf arg, Kinit vf' arg' =>
      erased_val vf vf' /\ erased_val arg arg'
    | Krun c, Krun c' =>
      erasedCores c c'
    | Kblocked c, Kblocked c' =>
      erasedCores c c'
    | Kresume c arg, Kresume c' arg' =>
      erasedCores c c' /\ arg = arg'
    (*we don't use this and our semantics are strange*)
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

  Lemma erasedPool_contains:
    forall tp1 tp1' 
      (HerasedPool: erased_threadPool tp1 tp1') i,
      containsThread tp1 i <-> ErasedMachine.ThreadPool.containsThread tp1' i.
  Proof.
    intros.
    inversion HerasedPool.
    unfold containsThread, ErasedMachine.ThreadPool.containsThread.
    rewrite H.
    split; auto.
  Qed.

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

  Hint Resolve erased_updLockSet erased_updThread
       erased_addThread erased_remLockSet: erased.

End ThreadPoolErasure.
  
(** ** Erasure from FineConc to SC*)
Module SCErasure (SEM: Semantics)
       (Machines: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machines)
       (CE : CoreErasure SEM).
  Module ThreadPoolErasure := ThreadPoolErasure SEM Machines CE.
  Import ValErasure MemErasure CE ThreadPoolErasure.
  Import Machines DryMachine ThreadPool AsmContext.

  Import event_semantics.
  (** ** Simulation for syncStep, startStep, resumeStep, suspendStep,
  and haltedStep *)
  
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
    Hint Resolve erasedMem_restr : erased.
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
          eapply mem_load_erased in H; eauto with erased;
          destruct Hload as [? [Hload ?]]
        end;
    try match goal with
        | [H: Mem.store _ _ _ _ _ = Some _ |- _] =>
          eapply mem_store_erased in H; eauto with erased;
          destruct Hstore as [m2' [Hstore HerasedMem']]
        end;
    try match goal with
        | [|- _ <> Vundef] => intro Hcontra; discriminate
        end;
    match goal with
    | [H: at_external _ _ = _, H1: erasedCores _ _ |- _] =>
      pose proof (at_external_erase H1);
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
           | [H:erased_val (Vint _) _ |- _] => inv H
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

  Global Ltac pf_cleanup :=
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
  Lemma startStep_erasure:
    forall ge tp1 tp1' tp2 i
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: FineConc.start_thread ge cnti tp2),
    exists tp2',
      SC.start_thread ge cnti' tp2' /\
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
    unfold ErasedMachine.invariant; auto.
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
      SC.resume_thread cnti' tp2' /\
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
    destruct Hthreads as [HeraseCores Heq]. subst v.
    pose proof (at_external_erase HeraseCores).
    rewrite Hat_external in H.
    destruct X, p.
    destruct (at_external SEM.Sem c0) eqn:Hat_external'; try by exfalso.
    destruct p as [[? ?] ?].
    destruct H as [? [? ?]]; subst.
    eapply after_external_erase with (v' := Vint Int.zero) in Hafter_external;
      eauto with erased.
    destruct Hafter_external as [c2' [Hafter_external' HerasedCores']].
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c2')).
    split.
    eapply SC.ResumeThread with (c := c0); simpl in *; eauto.
    unfold ErasedMachine.invariant; auto.
    constructor.
    simpl. auto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.
  
  Lemma suspendStep_erasure:
    forall tp1 tp1' tp2 i
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: FineConc.suspend_thread cnti tp2),
    exists tp2',
      SC.suspend_thread cnti' tp2' /\
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
    pose proof (at_external_erase Hthreads).
    rewrite Hat_external in H.
    destruct X, p.
    destruct (at_external SEM.Sem c0) eqn:Hat_external'; try by exfalso.
    destruct p as [[? ?] ?].
    destruct H as [? [? ?]]; subst.
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Kblocked c0)).
    split.
    eapply SC.SuspendThread with (c := c0); simpl in *; eauto.
    unfold ErasedMachine.invariant; auto.
    constructor.
    simpl. auto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCC.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdateC' _ _ cntj).
      erewrite <- @gsoThreadCC with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Lemma haltStep_erasure:
    forall tp1 tp1' i
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (Hstep: threadHalted cnti),
      ErasedMachine.threadHalted cnti'.
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup.
    rewrite Hcode in Hthreads.
    simpl in Hthreads.
    destruct (ErasedMachine.ThreadPool.getThreadC cnti') eqn:?;
             try by exfalso.
    assert (halted SEM.Sem c0)
      by (eapply halted_erase; eauto).
    econstructor; eauto.
  Qed.

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
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
      match goal with
        [H: erasedCtl ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    eapply erasedMem_restr with (Hlt := Hcomp1 i cnti) in HerasedMem.
    eapply evstep_erase in Hcorestep; eauto.
    destruct Hcorestep as (c2' & m2' & Hevstep' & HerasedCores' & HerasedMem').
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c2')), m2'.
    split; eauto.
    econstructor; eauto.
    split; eauto.
    constructor; eauto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCode.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdate' _ _ _ cntj).
      erewrite  @gsoThreadCode with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Notation fstep := (corestep fine_semantics).
  Notation scstep := (corestep sc_semantics).

  (** A step on the FineConc machine can be matched by a step on the
  SC machine producing the same event *)
  Lemma sc_sim:
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
        | [H: containsThread _ ?I |- _ ] =>
          assert (ErasedMachine.ThreadPool.containsThread tp1' I)
            by (eapply erasedPool_contains; eauto)
        end;
    assert (Hcomp1' : ErasedMachine.mem_compatible tp1' m1')
      by (unfold ErasedMachine.mem_compatible; auto).
    - assert (Hstep' := startStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 1; simpl; eauto.
      split; eauto.
    - assert (Hstep' := resumeStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 2; simpl; eauto.
      split; eauto.
    - assert (Htstep' := threadStep_erase HerasePool H HerasedMem Hcomp1' Htstep).
      destruct Htstep' as [tp2' [m2' [Htstep' [HerasePool' HerasedMem']]]].
      exists tp2', (erasePerm m2').
      split.
      eapply SC.thread_step; eauto.
      split; eauto.
      eapply erasedMem_dilute_1; eauto.
    - assert (Hstep' := suspendStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 4; simpl; eauto.
      split; eauto.
    - assert (Hstep' := syncStep_erase HerasePool H HerasedMem Hcomp1' Htstep).
      destruct Hstep' as [tp2' [m2' [Hstep' [HerasePool' HerasedMem']]]].
      exists tp2', m2'.
      split.
      eapply SC.sync_step; eauto.
      split; eauto.
    - eapply haltStep_erasure with (cnti' := H) in Hhalted; eauto.
      exists tp1', m1';
        split; eauto.
      econstructor 6; simpl; eauto.
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
  Qed.
  
  Notation sc_safe := (SC.fsafe the_ge).
  Notation fsafe := (FineConc.fsafe the_ge).

  Inductive sc_execution :
    SC.MachState -> mem -> SC.MachState -> mem -> Prop :=
  | refl_sc_exec : forall ms (m : mem),
      SC.halted ms ->
      sc_execution ms m ms m
  | step_sc_trans : forall i U U'
                      (tp tp' tp'': SC.machine_state)
                      (tr tr' tr'': SC.event_trace)
                      (m m' m'' : mem),
      SC.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m' ->
      sc_execution (U, tr', tp') m' (U', tr'', tp'') m'' ->
      sc_execution (i :: U,tr,tp) m (U',tr'',tp'') m''.

  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | refl_fine_exec : forall ms (m : mem),
      FineConc.halted ms ->
      fine_execution ms m ms m
  | step_fine_trans : forall i U U'
                        (tp tp' tp'': FineConc.machine_state)
                        (tr tr' tr'': FineConc.event_trace)
                        (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

  (* TODO: Move this lemma. Maybe definitions above it too*)
  Lemma fstep_trace_irr:
    forall U i tp m tp' m' tr tr'
      (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m'),
    forall tr'', exists ev,
        FineConc.MachStep the_ge (i :: U, tr'', tp) m (U, tr'' ++ ev, tp') m'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *; subst; inv HschedN; pf_cleanup.
    - exists [::]; erewrite cats0; econstructor; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 2; simpl; eauto.
    - exists (map [eta Events.internal tid] ev); econstructor 3; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 4; simpl; eauto.
    - exists [:: Events.external tid ev]; econstructor 5; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 6; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 7; simpl; eauto.
  Qed.

  Lemma fsafe_execution:
    forall tpf mf U tr,
      fsafe tpf mf U (size U).+1 ->
      exists tpf' mf' tr',
        fine_execution (U, tr, tpf) mf ([::], tr ++ tr', tpf') mf'.
  Proof.
    intros.
    generalize dependent mf.
    generalize dependent tpf.
    generalize dependent tr.
    induction U; intros.
    do 2 eexists. exists [::].
    erewrite cats0.
    econstructor 1; eauto.
    simpl in *.
    inversion H; subst.
    simpl in H0; by exfalso.
    simpl in *.
    assert (exists ev,
               FineConc.MachStep the_ge ((a :: U), tr, tpf) mf
                                 (U, tr ++ ev, tp') m')
      by (eapply fstep_trace_irr; eauto).
    destruct H0 as [ev Hstep].
    specialize (IHU (tr ++ ev) _ _ H2).
    destruct IHU as (tpf'' & mf'' & tr'' & Hexec).
    rewrite <- catA in Hexec.
    exists tpf'', mf'', (ev ++ tr'').
    econstructor 2; eauto.
  Qed.

  (** The initial state of the SC machine is an erasure of the initial
  state of the FineConc machine*)
 Lemma init_erasure:
    forall f arg U tpsc tpf
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf)),
      erased_threadPool tpf tpsc.
  Proof.
    intros.
    unfold sc_init, tpf_init in *.
    simpl in *. unfold SC.init_machine, FineConc.init_machine in *.
    unfold init_mach, ErasedMachine.init_mach in *.
    simpl in *.
    destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
    destruct init_perm; try discriminate.
    inv HinitSC. inv HinitF.
    unfold initial_machine, ErasedMachine.initial_machine.
    simpl.
    econstructor. simpl; eauto.
    intros. 
    simpl.
    apply erasedCores_refl; auto.
  Qed.

  (** Any execution of the FineConc machine resulting in some trace
    tr' can be matched by an execution of the SC machine with the
    same trace*)
  Lemma execution_sim:
    forall U U' tpf tpf' mf mf' tpsc msc tr tr' 
      (Hexec: fine_execution (U, tr, tpf) mf (U', tr', tpf') mf')
      (HerasedPool: erased_threadPool tpf tpsc)
      (HerasedMem: erasedMem mf msc),
    exists tpsc' msc',
      sc_execution (U, tr, tpsc) msc (U', tr', tpsc') msc' /\
      erased_threadPool tpf' tpsc' /\ erasedMem mf' msc'.
  Proof.
    intros U.
    induction U.
    - intros.
      inversion Hexec; subst.
      exists tpsc, msc.
      split.
      econstructor 1. simpl; auto.
      split; auto.
    - intros.
      inversion Hexec; subst.
      + simpl in H5; by exfalso.
      + eapply sc_sim in H8; eauto.
        destruct H8 as (tpsc0 & msc0 & Hstep0 & HerasedPool0 & HerasedMem0).
        specialize (IHU _ _ _ _ _ _ _ _ _ H9 HerasedPool0 HerasedMem0).
        destruct IHU as (tpsc2' & msc2' & Hsexec & HerasedPool' & HerasedMem').
        exists tpsc2', msc2'.
        split; eauto.
        econstructor; eauto.
  Qed.

  (** Safety of the SC machine*)
  Lemma fsafe_implies_scsafe:
    forall sched tpsc tpf mf msc
      (Hsafe: fsafe tpf mf sched (size sched).+1)
      (HerasedPool: erased_threadPool tpf tpsc)
      (HerasedMem: erasedMem mf msc),
      sc_safe tpsc msc sched (size sched).+1.
  Proof.
    intro sched.
    induction sched as [|i sched]; intros.
    - simpl in *. inversion Hsafe;
        eapply SC.HaltedSafe with (tr := tr);
        simpl; auto.
    - simpl in Hsafe.
      inversion Hsafe; subst.
      simpl in H; by exfalso.
      simpl in *.
      eapply sc_sim in H0; eauto.
      destruct H0 as (tpsc2' & msc2' & Hstep & HerasedPool' & HerasedMem').
      econstructor 3; eauto.
  Qed.
  
  Theorem sc_erasure:
    forall sched f arg U tpsc tpf m
      (Hmem: init_mem = Some m)
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf))
      (HsafeF: fsafe tpf (DryMachine.diluteMem m) sched (size sched).+1),
      sc_safe tpsc (ErasedMachine.diluteMem m) sched (size sched).+1 /\
      (forall tpf' mf' tr,
          fine_execution (sched, [::], tpf) (DryMachine.diluteMem m)
                         ([::], tr, tpf') mf' ->
          exists tpsc' msc',
            sc_execution (sched, [::], tpsc) (ErasedMachine.diluteMem m)
                         ([::], tr, tpsc') msc' /\
            erased_threadPool tpf' tpsc' /\ erasedMem mf' msc').
  Proof.
    intros.
    assert (HpoolErase := init_erasure _ _ HinitSC HinitF).
    assert (HmemErase : erasedMem (diluteMem m) (ErasedMachine.diluteMem m)).
    { econstructor; eauto.
      intros.
      assert (Hvalid: Mem.valid_block m b)
        by (unfold Mem.valid_block, ErasedMachine.diluteMem, erasePerm in *;
             simpl in *; auto).
      assert (Hperm:= erasePerm_V ofs k Hvalid).
      unfold permission_at in Hperm; auto.
    }
    split; first by (eapply fsafe_implies_scsafe; eauto).
    intros.
    eapply execution_sim; eauto.
  Qed.

End SCErasure.

(*TODO: Move to another file*)
(** ** Spinlock well synchronized*)
(*
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
      action evj <> Some Write /\ action evj <> Some Read. *)
  



