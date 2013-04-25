Require Import ListSet.
Require Import Coq.Logic.Decidable.

Require Import sepcomp.extspec.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.wf_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.
Require Import sepcomp.extension.
Require Import sepcomp.compile_safe.
Require Import sepcomp.Coqlib2.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

(**  "Compilable" Extensions *)

(*This is an [F,V]-independent definition of meminj_preserves_globals*)
Definition meminj_preserves_globals (globals: (block->Prop)*(block->Prop)) f :=
  (forall b, fst globals b -> f b = Some (b, 0)) /\
  (forall b, snd globals b -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, snd globals b2 -> f b1 = Some (b2, delta) -> b1=b2).

Definition genv2blocks {F V: Type} (ge: Genv.t F V) := 
  (fun b => exists id, Genv.find_symbol ge id = Some b,
   fun b => exists gv, Genv.find_var_info ge b = Some gv).

Section CoreCompatibleDefs. Variables
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: EffectfulSemantics G xT D) (** extended semantics *)
 (esig: ef_ext_spec mem Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, EffectfulSemantics (gT i) (cT i) (dT i)) (** a set of core semantics *)
 (csig: ef_ext_spec mem Z). (** client signature *)

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.
 Variable core_compat: core_compatible ge genv_map E.

 Import Extension.

 Definition owned_valid s m := 
  forall i c, proj_core E i s = Some c -> 
  forall b ofs, effects (csem i) c AllocEffect b ofs -> 
    b < Mem.nextblock m.
  
 Definition owned_disjoint s :=
  forall i j (c: cT i) (d: cT j), 
  i<>j -> 
  proj_core E i s = Some c ->   
  proj_core E j s = Some d ->   
  forall b ofs, effects (csem i) c AllocEffect b ofs -> 
    ~effects (csem j) d AllocEffect b ofs.

 Definition owned_conserving := 
   forall s i (c: cT i),
   proj_core E i s = Some c -> 
   forall b ofs, effects (csem i) c AllocEffect b ofs -> 
     effects esem s AllocEffect b ofs.

 Definition new_effects_aligned :=
   forall s c m s' c' m',
   proj_core E (active E s) s = Some c -> 
   corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   (forall k b ofs, 
    new_effect esem k b ofs s s' <-> 
    new_effect (csem (active E s)) k b ofs c c').

 Lemma guarantee_step': 
   owned_conserving -> 
   new_effects_aligned -> 
   forall (r r': reserve) j j' s c m s' c' m',
   guarantee' esem j r s m ->   
   guarantee' (csem (active E s)) j r c m -> 
   proj_core E (active E s) s = Some c -> 
   corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   proj_core E (active E s) s' = Some c' -> 
   reserve_separated2 r r' j' m -> 
   reserve_valid' r j m -> 
   reserve_incr r r' -> 
   inject_incr j j' -> 
   inject_separated2 j j' m -> 
   effects_valid esem s m -> 
   guarantee' (csem (active E s)) j' r' c' m' -> 
   guarantee' esem j' r' s' m'.
 Proof.
 unfold new_effects_aligned.
 intros OWN EQV; intros until m'. 
 intros H1 H2 H3 H4 H5 H6 H7 H8 H9 INCR SEP EFVAL H9' b ofs VAL RR EF.
 specialize (EQV _ _ _ _ _ _ H3 H4 H5).
 destruct (new_effect_dec esem AllocEffect b ofs s s') as [N|R].
 solve[destruct N as [X Y]; auto].
 unfold new_effect in R.
 assert (effects esem s AllocEffect b ofs \/
         ~effects esem s' AllocEffect b ofs).  
  apply not_and in R.
  destruct R; try solve[left; auto|right; auto].
  apply not_not in H. solve[left; auto].
  destruct (effects_dec esem s AllocEffect b ofs);
   try solve[left; auto|right; auto].
  solve[destruct (effects_dec esem s AllocEffect b ofs);
   try solve[left; auto|right; auto]].
 destruct H; auto.
 eapply effects_forward in H5; eauto.
 solve[destruct H5; auto].
 assert (H10: ~effects esem s AllocEffect b ofs).
  intro CONTRA.
  eapply effects_forward in H5; eauto.
  solve[destruct H5 as [H5 _]; apply H; auto].
 clear R; elimtype False. 
 destruct (effects_dec esem s ModifyEffect b ofs).
 destruct RR as [b0 [delta [JJ' RR']]].
 destruct (reserve_dec r b0 (ofs-delta)).
 case_eq (j b0).
 intros [b' delta'] H11.
 assert (b' = b /\ delta' = delta) as [EQ1 EQ2].
  apply INCR in H11. 
  rewrite H11 in JJ'.
  solve[inv JJ'; auto].
 subst.
 assert (VAL0: Mem.valid_block m b).
  solve[apply (H8 _ _ _ _ s0 H11)].
 unfold guarantee', guarantee in H1.
 apply H10. 
 apply (H1 _ _ VAL0); auto.
 solve[exists b0, delta; split; auto].
 intros NONE.
 unfold inject_separated2 in SEP.
 apply (SEP _ _ _ NONE JJ').
 solve[eapply EFVAL; eauto].
 unfold reserve_separated2 in H6.
 apply (H7 _ _ n RR' _ _ JJ').
 solve[eapply EFVAL; eauto].
 assert (NEW: new_effect esem ModifyEffect b ofs s s').
  solve[split; auto].
 rewrite EQV in NEW.
 destruct NEW as [X Y]. 
 unfold guarantee', guarantee in H9'.
 specialize (H9' _ _ VAL RR Y).
 solve[eapply OWN in H9'; eauto].
 Qed.

 Lemma guarantee_stepN: 
   owned_conserving -> 
   new_effects_aligned -> 
   forall n (r r': reserve) j j' s c m s' c' m',
   guarantee' esem j r s m ->   
   guarantee' (csem (active E s)) j r c m -> 
   proj_core E (active E s) s = Some c -> 
   corestepN (csem (active E s)) (genv_map (active E s)) n c m c' m' -> 
   corestepN esem ge n s m s' m' -> 
   proj_core E (active E s) s' = Some c' -> 
   reserve_separated2 r r' j' m -> 
   reserve_valid' r j m -> 
   reserve_incr r r' -> 
   inject_incr j j' -> 
   inject_separated2 j j' m -> 
   effects_valid esem s m -> 
   guarantee' (csem (active E s)) j' r' c' m' -> 
   guarantee' esem j' r' s' m'.
 Proof.
 intros OWN ALIGN.
 induction n; intros until m'; intros.
 hnf in H2, H3.
 inv H2; inv H3; auto.
 intros b ofs VAL INJ EF.
 unfold guarantee', guarantee in H.
 specialize (H _ ofs VAL).
 apply H; auto.
 destruct INJ as [b0 [delta [X Y]]].
 case_eq (j b0).
 intros [b' delta'] W.
 assert (b=b' /\ delta=delta') as [EQ1 EQ2].
  apply H8 in W.
  rewrite W in X.
  solve[inv X; split; auto].
 subst.
 exists b0, delta'; split; auto.
 destruct (reserve_dec r b0 (ofs-delta')); auto.
 elimtype False.
 unfold reserve_separated2 in H5.
 apply (H5 _ _ n Y _ _ X).
 solve[eapply H10; eauto].
 intros NONE.
 unfold inject_separated2 in H9.
 elimtype False.
 apply (H9 _ _ _ NONE X).
 solve[eapply H10; eauto].
 hnf in H2, H3.
 destruct H2 as [c2 [m2 [STEP STEPN]]].
 destruct H3 as [s2 [m2' [ESTEP ESTEPN]]].
 assert (m2 = m2').
  inv core_compat.
  solve[eapply corestep_pres; eauto].
 subst.
 assert (guarantee' (csem (active E s)) j' r' c2 m2').
  solve[eapply guarantee'_backward_stepN; eauto].
 assert (INTER: guarantee' esem j' r' s2 m2').
  apply guarantee_step' 
   with (s := s) (c := c) (m := m) (r := r) (j := j) (c' := c2); auto.
  inv core_compat.
  exploit corestep_pres; eauto.
  solve[intros [? [? ?]]; auto].
 
 assert (exists (r2: reserve) (j2: meminj), 
  reserve_incr r2 r' /\
  reserve_separated2 r2 r' j' m2' /\
  reserve_valid' r2 j2 m2' /\
  inject_incr j2 j' /\
  inject_separated2 j2 j' m2') as [r2 [j2 [A [B [C [X Y]]]]]].
  admit. (*interpolation lemma*)

 assert (EQ: active E s = active E s2).
  inv core_compat.
  exploit corestep_pres; eauto.
  solve[intros [? ?]; auto].
 forget (active E s) as x; subst.
 specialize (IHn r2 r' j2 j' s2 c2 m2' s' c' m').
 spec IHn. solve[eapply guarantee_decr2; eauto].
 spec IHn. solve[eapply guarantee_decr2; eauto].
 spec IHn. 
  assert (active E s = active E s2). 
   admit. (*extension property*)
  forget (active E s2) as x.
  subst.
  inv core_compat.
  solve[eapply corestep_pres; eauto].
 spec IHn; auto.
 spec IHn; auto.
 spec IHn; auto.
 spec IHn; auto.
 spec IHn; auto.
 spec IHn; auto. 
 spec IHn; auto.
 spec IHn; auto. 
 spec IHn. solve[eapply effects_valid_preserved; eauto].
 apply IHn; auto.
 Qed. 

End CoreCompatibleDefs.

Module CompilabilityInvariant. Section CompilabilityInvariant. 
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
 (** a set of core semantics *)
  (csemS: forall i:nat, EffectfulSemantics (Genv.t (fS i) (vS i)) (cS i) (dS i)) 
 (** a set of core semantics *)
  (csemT: forall i:nat, EffectfulSemantics (Genv.t (fT i) (vT i)) (cT i) (dT i)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (max_cores: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature). (*TODO: SHOULD PERHAPS BE GENERALIZED*)
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> reserve -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, (core_data i) -> (core_data i) -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation zint_invar_after_external := (Extension.zint_invar_after_external).

 Definition core_datas := forall i:nat, core_data i.

 Definition core_ords (max_cores: nat) cd1 cd2 := 
(*exists i, (i < max_cores)%nat /\
  (forall j, (j < i)%nat -> cd1 j=cd2 j) /\ core_ord i (cd1 i) (cd2 i)%nat.*)
  prod_ord' _ core_ord _ _ 
   (data_prod' _ _ _ cd1) (data_prod' _ max_cores max_cores cd2).

 Variable (R: reserve -> meminj -> xS -> mem -> xT -> mem -> Prop).

 Definition allocs_shrink j s1 s2 :=
   forall b1 b2 ofs2 delta, 
   effects esemT s2 AllocEffect b2 ofs2 -> 
   j b1 = Some (b2, delta) -> 
   effects esemS s1 AllocEffect b1 (ofs2-delta).

 Definition match_states (cd: core_datas) (r: reserve) (j: meminj) 
                         (s1: xS) m1 (s2: xT) m2 :=
   owned_valid esemS csemS E_S s1 m1 /\ owned_disjoint esemS csemS E_S s1 /\ 
   owned_valid esemT csemT E_T s2 m2 /\ owned_disjoint esemT csemT E_T s2 /\
   reserve_valid r m1 /\ reserve_valid' r j m2 /\
   core_semantics.effects_valid esemS s1 m1 /\ 
   core_semantics.effects_valid esemT s2 m2 /\
   mem_wd m1 /\ mem_wd m2 /\
   guarantee esemS r s1 m1 /\ guarantee' esemT j r s2 m2 /\
   allocs_shrink j s1 s2 /\
   R r j s1 m1 s2 m2 /\ 
   ACTIVE E_S s1=ACTIVE E_T s2 /\
   (*invariant on active cores*)
   (forall c1, 
     PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
     guarantee (csemS (ACTIVE E_S s1)) r c1 m1 /\
     (exists z: Z, 
       compile_safe (csemS (ACTIVE E_S s1)) (genv_mapS (ACTIVE E_S s1)) z r c1 m1) /\
     exists c2, PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 /\ 
       guarantee' (csemT (ACTIVE E_S s1)) j r c2 m2 /\
       match_state (ACTIVE E_S s1) (cd (ACTIVE E_S s1)) r j c1 m1 c2 m2) /\
   (*invariant on inactive cores*)
   (forall i c1, 
     i <> ACTIVE E_S s1 -> 
     PROJ_CORE E_S i s1 = Some c1 -> 
     exists c2, PROJ_CORE E_T i s2 = Some c2 /\ 
     exists cd0 (r0: reserve) j0 m10 m20,
       guarantee (csemS i) r0 c1 m10 /\
       (exists z: Z, compile_safe (csemS i) (genv_mapS i) z r0 c1 m10) /\
       guarantee' (csemT i) j0 r0 c2 m20 /\
       match_state i cd0 r0 j0 c1 m10 c2 m20).

 Inductive Sig: Type := Make: forall  
 (corestep_rel: forall cd (r r': reserve) j j' s1 c1 m1 c1' m1' s2 c2 m2 c2' m2' s1' s2' n cd', 
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   match_states cd r j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   meminj_preserves_globals_ind (genv2blocks ge_S) j -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   reserve_incr r r' -> 
   reserve_separated r r' j' m1 m2 -> 
   corestep (csemS (ACTIVE E_S s1)) (genv_mapS (ACTIVE E_S s1)) c1 m1 c1' m1' -> 
   corestepN (csemT (ACTIVE E_S s1)) (genv_mapT (ACTIVE E_S s1)) n c2 m2 c2' m2' ->
   corestep esemS ge_S s1 m1 s1' m1' -> 
   corestepN esemT ge_T n s2 m2 s2' m2' -> 
   match_state (ACTIVE E_S s1) cd' r' j' c1' m1' c2' m2' -> 
   guarantee (csemS (ACTIVE E_S s1)) r c1' m1' -> 
   guarantee' (csemT (ACTIVE E_S s1)) j r c2' m2' -> 
   R r' j' s1' m1' s2' m2')

 (after_external_rel: 
   forall cd (r r': reserve) j j' s1 m1 s2 m2 s1' m1' s2' m2' ret1 ret2 ef sig args1,
   match_states cd r j s1 m1 s2 m2 -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   reserve_incr r r' -> 
   reserve_separated r r' j' m1 m2 -> 
   Mem.inject j' m1' m2' -> 
   mem_forward m1 m1'-> 
   mem_forward m2 m2' -> 
   rely esemS r s1' m1 m1' -> 
   rely' esemT j r s2' m2 m2' -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   after_external esemS ret1 s1 = Some s1' -> 
   after_external esemT ret2 s2 = Some s2' -> 
   val_has_type_opt ret1 (ef_sig ef) -> 
   val_has_type_opt ret2 (ef_sig ef) -> 
   val_inject_opt j' ret1 ret2 -> 
   R r' j' s1' m1' s2' m2')   

 (extension_diagram: forall s1 m1 s1' m1' s2 c1 c2 m2 ef sig args1 args2 cd r j,
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   runnable (csemS (ACTIVE E_S s1)) c1=false -> 
   runnable (csemT (ACTIVE E_S s1)) c2=false -> 
   at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
   at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
   match_states cd r j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args (ef_sig ef)) -> 
   corestep esemS ge_S s1 m1 s1' m1' -> 
   guarantee esemS r s1' m1' -> 
   exists s2', exists m2', exists cd', exists r': reserve, exists j',
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     reserve_incr r r' /\
     reserve_separated r r' j' m1 m2 /\
     guarantee' esemT j' r' s2' m2' /\
     match_states cd' r' j' s1' m1' s2' m2' /\
     ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
      corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ords max_cores cd' cd))

 (at_external_match: forall s1 m1 s2 c1 c2 m2 ef sig args1 args2 cd r j,
   ACTIVE E_S s1=ACTIVE E_T s2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   runnable (csemS (ACTIVE E_S s1)) c1=runnable (csemT (ACTIVE E_S s1)) c2 -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
   match_state (ACTIVE E_S s1) cd r j c1 m1 c2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args (ef_sig ef)) -> 
   at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
   at_external esemT s2 = Some (ef, sig, args2))

 (make_initial_core_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 (r: reserve) j sig,
   In (v1, v2, sig) entry_points -> 
   make_initial_core esemS ge_S v1 vals1 = Some s1 -> 
   Mem.inject j m1 m2 -> 
   mem_wd m1 -> 
   mem_wd m2 -> 
   reserve_valid r m1 -> 
   reserve_valid' r j m2 -> 
   Forall2 (val_inject j) vals1 vals2 -> 
   Forall2 Val.has_type vals2 (sig_args sig) -> 
   exists cd, exists s2, 
     make_initial_core esemT ge_T v2 vals2 = Some s2 /\
     match_states cd r j s1 m1 s2 m2)
 
 (safely_halted_step: forall cd r j c1 m1 c2 m2 v1 rty,
   match_states cd r j c1 m1 c2 m2 -> 
   safely_halted esemS c1 = Some v1 -> 
   Val.has_type v1 rty -> 
   exists v2, val_inject j v1 v2 /\
     safely_halted esemT c2 = Some v2 /\ 
     Val.has_type v2 rty /\ 
     Mem.inject j m1 m2)

 (safely_halted_diagram: forall cd r j m1 m1' m2 rv1 s1 s2 s1' c1 c2,
   match_states cd r j s1 m1 s2 m2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   safely_halted (csemS (ACTIVE E_S s1)) c1 = Some rv1 -> 
   corestep esemS ge_S s1 m1 s1' m1' ->  
   guarantee esemS r s1' m1' -> 
   exists rv2, 
     safely_halted (csemT (ACTIVE E_S s1)) c2 = Some rv2 /\
     val_inject j rv1 rv2 /\ 
     exists s2', exists m2', exists cd', exists r': reserve, exists j', 
       inject_incr j j' /\
       Events.inject_separated j j' m1 m2 /\
       reserve_incr r r' /\
       reserve_separated r r' j' m1 m2 /\
       corestep esemT ge_T s2 m2 s2' m2' /\
       match_states cd' r' j' s1' m1' s2' m2' /\
       guarantee' esemT j' r' s2' m2'),
 Sig.

End CompilabilityInvariant. End CompilabilityInvariant.

Definition genvs_domain_eq {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall b, fst (genv2blocks ge1) b <-> fst (genv2blocks ge2) b) /\
  (forall b, snd (genv2blocks ge1) b <-> snd (genv2blocks ge2) b).

Module CompilableExtension. Section CompilableExtension. 
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
 (** a set of core semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) 
 (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (max_cores: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> reserve -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Implicit Arguments match_state [].

 Import Forward_simulation_inj_exposed.

 Record Sig: Type := Make {
   core_datas: Type;
   core_ords: core_datas -> core_datas -> Prop;
   match_states: core_datas -> reserve -> meminj -> xS -> mem -> xT -> mem -> Prop;
   _ : Forward_simulation_inject D_S D_T esemS esemT ge_S ge_T 
          entry_points core_datas match_states core_ords
 }.

End CompilableExtension. End CompilableExtension.

Module EXTENSION_COMPILABILITY. Section EXTENSION_COMPILABILITY.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
  (csemS: forall i:nat, 
    EffectfulSemantics (Genv.t (fS i) (vS i)) (cS i) (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, 
    EffectfulSemantics (Genv.t (fT i) (vT i)) (cT i) (dT i)) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (max_cores: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> reserve -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
 Implicit Arguments match_state [].

 Import Forward_simulation_inj_exposed.
 Import Extension.

 Definition core_datas := forall i:nat, core_data i.

 Variable (R: reserve -> meminj -> xS -> mem -> xT -> mem -> Prop).

 Record Sig: Type := Make {
   _ : (forall i: nat, RelyGuaranteeSimulation.Sig (csemS i) (csemT i) 
         (genv_mapS i) (match_state i)) -> 
       genvs_domain_eq ge_S ge_T -> 
       (forall i: nat, genvs_domain_eq ge_S (genv_mapS i)) -> 
       (forall i: nat, genvs_domain_eq ge_T (genv_mapT i)) -> 
       core_compatible ge_S genv_mapS E_S -> 
       core_compatible ge_T genv_mapT E_T -> 
       owned_conserving esemS csemS E_S ->
       owned_conserving esemT csemT E_T ->
       (forall x, active E_S x < max_cores)%nat ->  
       (forall x, active E_T x < max_cores)%nat ->  
       new_effects_aligned esemT csemT ge_T genv_mapT E_T -> 
       (forall i:nat, Forward_simulation_inject (dS i) (dT i) (csemS i) (csemT i) 
         (genv_mapS i) (genv_mapT i) entry_points 
         (core_data i) (@match_state i) (@core_ord i)) -> 
       CompilabilityInvariant.Sig fS fT vS vT 
         esemS esemT csemS csemT max_cores ge_S ge_T genv_mapS genv_mapT E_S E_T 
         entry_points core_data match_state core_ord R -> 
       CompilableExtension.Sig esemS esemT ge_S ge_T entry_points
 }.

End EXTENSION_COMPILABILITY. End EXTENSION_COMPILABILITY. 
