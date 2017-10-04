(*CompCert imports*)
Require Import Events. (*needed for standard definitions of
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import Memory.
Require Import AST.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.StructuredInjections.
Require Import effect_simulations.
Require Import effect_simulations_lemmas.

Module Type EffectInterpolationAxioms.

Parameter effect_interp_II: forall m1 m2 nu12
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')

                             (ExtIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (SMInjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc (compose_sm nu12 nu23) b = true /\
                                                      pubBlocksSrc (compose_sm nu12 nu23) b = false) m1 m1')
                             (UnchLOOR13: Mem.unchanged_on (local_out_of_reach (compose_sm nu12 nu23) m1) m3 m3')

                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         extBlocksTgt nu12 = extBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true ->
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true ->
                                                    frgnBlocksSrc nu23 b = true))
                             (Norm12: forall b1 b2 d1, extern_of nu12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of nu23 b2 = Some(b3, d2)),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (as_inj nu23') m2' m3' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\
                             sm_inject_separated nu23 nu23' m2 m3 /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              extBlocksTgt nu12' = extBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true ->
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true ->
                                         frgnBlocksSrc nu23' b = true)) /\
                             (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                     exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\
                              Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\
                                                             pubBlocksSrc nu23 b = false) m2 m2' /\
                              Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' (* /\
                              the following fact is not any longer exported, since it can be established
                              outside of interpolation, in the transitivioty proof:
                              Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3'*).

(*The following lemma from mem_interpolation (pre- structured-injection! is used in the proof of
  Lemma initial_inject_split in effect_simulations_trans. Prior to reintegrating global environments,
  thta final two clauses asserted by this lemma were not needed in the proof of initial_inject_split.*)
Parameter interpolate_II_strongHeqMKI: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
                  (Fwd1: mem_forward m1 m1') j23 m3
                  (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                  j' (MInj13': Mem.inject j' m1' m3')
                  (InjIncr: inject_incr (compose_meminj j12 j23) j')
                  (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                  (Unch11': Mem.unchanged_on
                            (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                  (Unch33': Mem.unchanged_on
                        (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3'),
         exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                   (forall b1 b2 d1, j12' b1 = Some(b2,d1) ->
                       j12 b1 = Some(b2,d1) \/
                       exists b3 d, j' b1 = Some(b3,d)) /\
                   (forall b2 b3 d2, j23' b2 = Some(b3,d2) ->
                       j23 b2 = Some(b3,d2) \/
                       exists b1 d, j' b1 = Some(b3,d)) /\
                   inject_incr j12 j12' /\ inject_incr j23 j23' /\
                   Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\
                   Mem.inject j23' m2' m3' /\
                   Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                   inject_separated j12 j12' m1 m2 /\
                   inject_separated j23 j23' m2 m3 /\
                   Mem.unchanged_on (loc_unmapped j23) m2 m2' /\
                   Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                   (forall b1 b2 ofs2, j12' b1 = Some(b2,ofs2) ->
                     (j12 b1 = Some (b2,ofs2)) \/
                     (b1 = Mem.nextblock m1 /\ b2 = Mem.nextblock m2 /\ ofs2 = 0) \/
                     (exists m, (b1 = Mem.nextblock m1 + m /\ b2=Mem.nextblock m2 + m)%positive /\ ofs2=0)) /\
                   (forall b2 b3 ofs3, j23' b2 = Some(b3,ofs3) ->
                     (j23 b2 = Some (b3,ofs3)) \/
                     (b2 = Mem.nextblock m2 /\ j' (Mem.nextblock m1) = Some(b3,ofs3)) \/
                     (exists m, (b2 = Mem.nextblock m2 + m)%positive /\
                            j' ((Mem.nextblock m1+m)%positive) = Some(b3,ofs3))).

End EffectInterpolationAxioms.