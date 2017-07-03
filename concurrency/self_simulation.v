Require Import Coq.omega.Omega.
Require Import Clight.
Require Import Events.
Require Import Globalenvs.
Require Import Memory.
Require Import Values.
Require Import Coqlib.

Require Import msl.Coqlib2.

Require veric.Clight_core. Import Clight_core.

Require Import sepcomp.event_semantics.
Require Import sepcomp.semantics.
Require Import sepcomp.mem_lemmas.


Require Import Smallstep.
(*To include once Asm has been repaired:
  Require Import concurrency.x86_context.
  Require Import concurrency.HybridMachine_simulation.*)


(*Require Import concurrency.compiler_correct.*)
Require Import concurrency.CoreSemantics_sum.


(*Self simulations say that a program has equivalent executions 
  in equivalent memories. 
  - Equivalent memories: VISIBLE locations are injected 
    one to one (same values and permissions).
  - Equivalent executions: the executions have equivalent memories and
    none visible locations are unchanged (in the execution).  
 *)

Set Bullet Behavior "Strict Subproofs".

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
  
  
  (*extension of a mem_injection (slightly stengthens the old inject_separated - LENB: not sure you need the stronger prop*)
  Definition is_ext (f1:meminj)(nb1: positive)(f2:meminj)(nb2:positive) : Prop:=
    forall b1 b2 ofs,
      f2 b1 = Some (b2, ofs) ->
      f1 b1 = None -> 
      (ofs = 0 /\ ~ Plt b1 nb1 /\  ~ Plt b2 nb2).
  
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
  Definition perm_inject (f:meminj)(m1:mem)(m2:mem): Prop:=
    forall b1 b2 delta,
      f b1 = Some (b2, delta) ->
      forall ofs p,
        Mem.perm m1 b1 (ofs ) Cur p  <->
        Mem.perm m2 b2 (ofs + delta) Cur p.

  (* The injection maps all visible locations*)
  Definition perm_image (f:meminj)(m1:mem)(m2:mem): Prop:=
    forall b1 ofs,
      Mem.perm m1 b1 ofs Cur Nonempty ->
    exists b2 delta,
      f b1 = Some (b2, delta).

  (* The injection maps to every visible location *)
  Definition perm_preimage (f:meminj)(m1:mem)(m2:mem): Prop:=
    forall b2 ofs_delta,
      Mem.perm m2 b2 ofs_delta Cur Nonempty ->
    exists b1 delta ofs,
      f b1 = Some (b2, delta) /\
      Mem.perm m1 b1 ofs Cur Nonempty /\
  ofs_delta = ofs + delta. 
  

  Record match_self (f: meminj) (c1:core) (m1:mem) (c2:core) (m2:mem): Prop:=
    { cinject: code_inject f c1 c2
    ; minject: Mem.inject f m1 m2            
    ; pinject: perm_inject f m1 m2
    ; pimage: perm_image f m1 m2
    ; ppreimage: perm_preimage f m1 m2
    }.

  (*
  Record match_mem (f: meminj) (m1:mem) (m2:mem): Prop:=
    { minject: Mem.inject f m1 m2            
    ; pinject: perm_inject f m1 m2
    ; pimage: perm_image f m1 m2
    ; ppreimage: perm_preimage f m1 m2
    }.
   *)
  
  Record same_visible (m1 m2: mem):=
    { same_visible12:
        forall b ofs,
          Mem.perm m1 b ofs Cur Nonempty ->
          (forall p, Mem.perm m1 b ofs Cur p <->
                Mem.perm m2 b ofs Cur p) /\
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1))) =
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2)));
      same_visible21:
        forall b ofs,
          Mem.perm m2 b ofs Cur Nonempty ->
          (forall p, Mem.perm m1 b ofs Cur p <->
                Mem.perm m2 b ofs Cur p) /\
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1))) =
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2)));
      }.
            
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
    - assumption.
    - unfold perm_inject; intros.
      inversion MATCH.
      simpl; split; intros.
      + assert (NE: Mem.perm m1' b1 ofs Cur Nonempty)
          by admit. (*easy by transitivity that doenst' exists*)
        assert (NE':= NE).
        eapply same_visible21 in NE'; eauto.
        destruct NE' as [SAME_PERM SAME_CONTENT].
        apply SAME_PERM in H0.
        apply SAME_PERM in NE.
        eapply MATCH in H0.

        eapply same_visible12 with (m2:=m2') in H0; eauto.
        admit. (*by trans *)
        
        eapply pimage0 in NE.
        destruct NE as [? [? HH]].
        assert (HH':= HH).
        eapply INCR in HH'.
        rewrite HH' in H. inversion H; subst.
        assumption.
      + assert (NE: Mem.perm m2' b2 (ofs+delta) Cur Nonempty)
          by admit. (*easy by transitivity that doenst' exists*)
        assert (NE':= NE).
        eapply same_visible21 in NE'; eauto.
        destruct NE' as [SAME_PERM SAME_CONTENT].
        apply SAME_PERM in H0.
        apply SAME_PERM in NE.
        eapply pinject0 in H0.
        
        eapply same_visible12 with (m2:=m1') in H0; eauto.
        admit. (*by trans *)
        
        eapply ppreimage0 in NE.
        destruct NE as [? [? [? [HH1 [HH2 HH3]]]]].
        assert (HH':= HH1).
        eapply INCR in HH'.
        admit. (*With some none overlapping this should follow*)
    - (*pre_image*)
      intros b1 ofs PERM.
      admit. (*Easy ... use lemmas to simplify same_visible*)
    - intros b2 ofs_delta PERM.
      admit. (*Easy ... use lemmas to simplify same_visible*)
  Admitted.

End SelfSim.
Arguments match_self {core}.
Section SelfSimulation.

  Variable Sem: semantics.
  Variable core: Type.
  Variable state_to_memcore: state Sem -> (core * Mem.mem).
  Variable memcore_to_state: core -> Mem.mem -> state Sem.
  Notation get_core s:= (fst (state_to_memcore s)). 
  Notation get_mem s:= (snd (state_to_memcore s)). 
  
 Record self_simulation: Type :=
    { code_inject: meminj -> core -> core -> Prop;
      code_inj_incr: forall c1 mu c2 mu',
          code_inject mu c1 c2 ->
          inject_incr mu mu' ->
          code_inject mu' c1 c2;
      ssim_diagram: forall f t c1 m1 c2 m2,
        match_self code_inject f c1 m1 c2 m2 ->
        forall (g: genvtype Sem) c1' m1',
          step Sem g (memcore_to_state c1 m1)  t (memcore_to_state c1' m1') ->
          exists c2' f' t' m2',
          step Sem g (memcore_to_state c2 m2)  t (memcore_to_state c2' m2')  /\
          match_self code_inject f' c1' m1' c2' m2' /\
          is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) /\
          Events.inject_trace f' t t'
    }. 

End SelfSimulation.        

  
  
  