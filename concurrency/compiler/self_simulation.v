Require Import Coq.omega.Omega.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Smallstep.


Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.lib.tactics.

Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.setoid_help.
Require Import Coq.Classes.Morphisms.

Set Bullet Behavior "Strict Subproofs".
Set Nested Proofs Allowed.



(*Self simulations say that a program has equivalent executions 
  in equivalent memories. 
  - Equivalent memories: VISIBLE locations are injected 
    one to one (same values and permissions).
  - Equivalent executions: the executions have equivalent memories and
    none visible locations are unchanged (in the execution).  
 *)

Section SelfSim.

  Variable Sem: semantics.
  
  (*Separate state and memory*)
  Variable core: Type.
  Variable state_to_memcore: state Sem -> (core * Mem.mem).
  Variable memcore_to_state: core -> Mem.mem -> state Sem.
  Hypothesis state_to_memcore_correct:
    forall c m, state_to_memcore (memcore_to_state c m) = (c,m).
  Hypothesis memcore_to_state_correct: forall s c m,
   state_to_memcore  s = (c,m) -> s = memcore_to_state c m.
  
  
  (*extension of a mem_injection 
  (slightly stengthens the old inject_separated - LENB: not sure you need the stronger prop*)
  Definition is_ext' (f1:meminj)(nb1 nb1': positive)(f2:meminj)(nb2:positive) : Prop:=
    forall b1 b2 ofs,
      f2 b1 = Some (b2, ofs) ->
      f1 b1 = None -> 
      (ofs = 0 /\ ~ Plt b1 nb1 /\  ~ Plt b2 nb2).
  Definition upd_inj (f:meminj) (b1:block) b2 delt :=
    fun b => if peq b b1 then Some (b2, delt) else f b.
  Inductive is_ext: meminj -> positive -> positive -> meminj -> positive -> Prop :=
  | is_ext_refl: forall j p1 p2, is_ext j p1 p1 j p2 
  | is_ext_step: forall j j' p1 p1' p2',
      is_ext j p1 p1' j' p2' ->
      is_ext j p1 (Pos.succ p1') (upd_inj j' p1' p2' 0) (Pos.succ p2').
  Definition is_ext_mem f m1 m1' f' m2':=
    is_ext f (Mem.nextblock m1) (Mem.nextblock m1') f' (Mem.nextblock m2').
  Lemma is_ext_full:
    forall f f' m m' m2',
      is_ext_mem f m m' f' m2' ->
      Events.injection_full f m ->
      Events.injection_full f' m'.
  Proof.
    unfold is_ext_mem.
    intros * H.
    unfold injection_full,Mem.valid_block.
    remember (Mem.nextblock m) as p1.
    remember (Mem.nextblock m') as p1'.
    remember (Mem.nextblock m2') as p2'.
    clear Heqp1 Heqp1' Heqp2'.
    induction H; eauto.

    intros. unfold upd_inj. match_case.
    eapply IHis_ext; eauto.
    clear - n H1. simpl in H1.
    eapply Plt_succ_inv in H1 as [|]; auto.
    contradiction.
  Qed.
  
  (*The code is also injected*)
  Variable code_inject: meminj -> core -> core -> Prop.
  Variable code_inj_incr: forall c1 mu c2 mu',
      code_inject mu c1 c2 ->
      inject_incr mu mu' ->
      code_inject mu' c1 c2.
  
  (*The current permisions OF THIS THREAD are unchanged! *)
  (*This is slightly stronger than Mem.inject/mi_inj which allows
    permissions to grow (on compilation). *)
  (*also it could be restricted to take only the Cur permissions*)
  (*NEVERMIND... BOTH FOLLOW from Mem.inject!*)
  Definition perm_inject1 (f:meminj)(m1:mem)(m2:mem): Prop:=
    forall b1 b2 delta,
      f b1 = Some (b2, delta) ->
      forall ofs p,
        Mem.perm m1 b1 (ofs ) Cur p  ->
        Mem.perm m2 b2 (ofs + delta) Cur p.
  
  Definition perm_inject2 (f:meminj)(m1:mem)(m2:mem): Prop:=
    forall b1 b2 delta,
      f b1 = Some (b2, delta) ->
      forall ofs p,
        Mem.perm m2 b2 (ofs + delta) Cur p ->
        Mem.perm m1 b1 (ofs ) Cur p \/ ~ Mem.perm m1 b1 ofs Cur Nonempty.



  Record match_mem (f: meminj) (m1:mem) (m2:mem): Prop:=
    { minject: Mem.inject f m1 m2 
      ; pimage: perm_image f (getCurPerm m1) 
      ; ppreimage: perm_surj f (getCurPerm m1) (getCurPerm m2)
    }.
  
  Instance match_mem_proper:
    Proper (Logic.eq ==> mem_equiv ==> mem_equiv ==> iff) match_mem.
  Proof.
    setoid_help.proper_iff.
    setoid_help.proper_intros; subst.
    inv H2; econstructor.
    - rewrite <- H0, <- H1; auto.
    - intros ? **. eapply pimage0; eauto.
      inv H0; rewrite cur_eqv; eauto.
    - intros b2 ofs2.
      inv H1. rewrite <- cur_eqv; intros HH.
      eapply ppreimage0 in HH. normal_hyp.
      inv H0. rewrite cur_eqv0 in H2.
      repeat (eexists; eauto).
  Qed.
  
  Instance proper_match_mem:
    Proper (Logic.eq ==> mem_equiv ==> mem_equiv ==> iff) match_mem.
  Proof.
    setoid_help.proper_iff; setoid_help.proper_intros; subst.
    inversion H2; econstructor.
    - rewrite <- H1, <- H0; assumption.
    - pose proof (cur_eqv _ _ H0).
      unfold Cur_equiv in *.
      rewrite <- H; assumption.
    - inv H0; inv H1.
      unfold Cur_equiv in *.
      rewrite <- cur_eqv, <- cur_eqv0; assumption.
  Qed.
  
  Record match_self (f: meminj) (c1:core) (m1:mem) (c2:core) (m2:mem): Prop:=
    { cinject: code_inject f c1 c2
    ; matchmem: match_mem f m1 m2 
    }.



  Lemma all_order_eq:
    forall a b, (forall p, Mem.perm_order' a p <->  Mem.perm_order' b p) <-> a = b.
  Proof.
    clear.
    intros. destruct a, b; auto.
    4: tauto.
    3: { simpl; split; intros; try congruence.
         specialize (H Nonempty).
         destruct H as [_ HH].
         contradict HH. apply perm_any_N. }
    
    2: { simpl; split; intros; try congruence.
         specialize (H Nonempty).
         destruct H as [ HH _].
         contradict HH. apply perm_any_N. }

    intros; split.
    - intros.
      dup H as H'.
      specialize (H p ); destruct H as [H _].
      specialize (H ltac:(simpl; apply perm_refl)).
      specialize (H' p0); destruct H' as [_ H'].
      specialize (H' ltac:(simpl; apply perm_refl)).
      simpl in *.
      destruct p, p0; inversion H; inversion H'; auto.
    - intros H; invert H; intros; auto. reflexivity.
  Qed.

  Lemma match_source_forward:
    forall mu c1 m1 c2 m2,
      match_self mu c1 m1 c2 m2 ->
      forall mu' m1' m2',
        inject_incr mu mu' ->
        Mem.inject mu' m1' m2' ->
        same_visible m1 m1' ->
        same_visible m2 m2' ->
        match_self mu' c1 m1' c2 m2'.
  Proof.
  intros ? ? ? ? ? MATCH ? ? ? INCR INJ VIS1 VIS2.
  constructor.
  - eapply code_inj_incr; eauto; apply MATCH. 
  - inv MATCH.
    split; trivial.
    * (*perm_image*) (*Easy ... use lemmas to simplify same_visible*)
      intros b1 ofs PERM.
      assert (PERM':Mem.perm m1' b1 ofs Cur Nonempty).
      { apply at_least_Some_perm_Cur; assumption. }
      apply VIS1 in PERM'.
      pose proof (pimage _ _ _ matchmem0 b1 ofs); unfold perm_image in *.
      apply at_least_Some_perm_Cur in PERM'.
      eapply H in PERM'; eauto.
      destruct PERM' as (? & ? & ?).
      do 2 eexists; eapply INCR; eauto.
    * (*Pre_image*) (*Easy ... use lemmas to simplify same_visible*)
      intros b2 ofs_delta PERM.
      assert (PERM':Mem.perm m2' b2 ofs_delta Cur Nonempty).
      { apply at_least_Some_perm_Cur; assumption. }
      apply VIS2 in PERM'.
      pose proof (ppreimage _ _ _ matchmem0 b2 ofs_delta).
      apply at_least_Some_perm_Cur in PERM'.
      eapply H in PERM'; eauto.
      destruct PERM' as (? & ? & ? & ? & ? & ?).
      do 3 eexists; repeat split; try eapply INCR; eauto.
      repeat rewrite getCurPerm_correct in *.
      repeat unfold permission_at in *.
      pose proof (same_cur _ _ VIS1 x x0) as HH1.
      pose proof (same_cur _ _ VIS2 b2 ofs_delta) as HH2.
      unfold Mem.perm in *.
      etransitivity. etransitivity.
      symmetry.
      1,3: eapply all_order_eq.
      eapply HH2.
      eapply HH1.
      eauto.
  Qed.

End SelfSim.
Arguments match_self {core}.

Section SelfSimulation.

  Variable state:Type.
  Variable Sem: semantics.CoreSemantics state mem.
  Variable state_to_memcore: state -> (state * Mem.mem).
  Variable memcore_to_state: state -> Mem.mem -> state.
  Notation get_core s:= (fst (state_to_memcore s)). 
  Notation get_mem s:= (snd (state_to_memcore s)). 


  Import Integers.
  Import Ptrofs.

  
  Definition self_preserves_atx_inj {s m} (Sem:semantics.CoreSemantics s m) match_states:=
    forall (j:meminj) s1 m1 s2 m2,
      match_states j s1 m1 s2 m2 ->
      forall f args,
        at_external Sem s1 m1 = Some (f,args) ->
        exists args',
          at_external Sem s2 m2 = Some (f,args') /\
          Val.inject_list j args args'.
  
 Record self_simulation: Type :=
    { code_inject: meminj -> state -> state -> Prop;
      code_inj_incr: forall c1 mu c2 mu',
          code_inject mu c1 c2 ->
          inject_incr mu mu' ->
          code_inject mu' c1 c2;
      ssim_diagram: forall f t c1 m1 c2 m2,
        match_self code_inject f c1 m1 c2 m2 ->
        forall c1' m1',
          semantics.corestep Sem c1 m1  c1' m1' ->
          exists c2' f' t' m2',
          semantics.corestep Sem c2 m2  c2' m2'  /\
          match_self code_inject f' c1' m1' c2' m2' /\
          inject_incr f f' /\
          is_ext_mem f m1 m1' f' m2' /\
          Events.inject_trace f' t t'
      ; ssim_external: forall c1 c2 m1 m2 j args1 func_name, 
        code_inject j c1 c2 ->
        Mem.inject j m1 m2 ->
        semantics.at_external Sem c1 m1  =  
        Some (func_name, args1) ->
        exists args2,
        Val.inject_list j args1 args2 /\
        semantics.at_external Sem c2 m2 = Some (func_name, args2)
     ; ssim_after_ext:
        forall (f : meminj)
          (c1 c1' : state)
          (m1 : mem)
          (c2 : state)
          (m2 : mem),
          match_self code_inject f c1 m1 c2 m2 ->
          semantics.after_external Sem None c1 m1 = Some c1' ->
          exists (c2' : state),
            semantics.after_external Sem None c2 m2 = Some c2' /\
            match_self code_inject f c1' m1 c2' m2
     ; ssim_halted:
        forall (f : meminj)
          (c1 : state)
          (m1 : mem)
          (c2 : state)
          (m2 : mem) ret ,
          match_self code_inject f c1 m1 c2 m2 ->
          semantics.halted Sem c1 ret ->
          semantics.halted Sem c2 ret
     ; ssim_initial:
         forall (c1 : state)
           (mu: meminj)
           (m1 m2 m1': mem) main1 main2 main_args1 main_args2 h,
           semantics.initial_core Sem h m1 c1 m1' main1 main_args1 ->
           match_mem mu m1 m2 ->
           Forall2 (mem_lemmas.val_inject mu) main_args1 main_args2 ->
           mem_lemmas.val_inject mu main1 main2 ->
           exists c2 m2' mu',
             semantics.initial_core Sem h m2 c2 m2' main2 main_args2 /\
             match_self code_inject mu' c1 m1' c2 m2' /\
             inject_incr mu mu' /\
             is_ext_mem mu m1 m1' mu' m2'
             
      ; ssim_preserves_atx:
          self_preserves_atx_inj Sem (match_self code_inject)
      (* ; ssim_visible_atx:
          atx_only_visible Sem (match_self code_inject) *)
    }. 

 
End SelfSimulation. 



