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
                                         DomTgt nu12 = DomSrc nu23 /\ 
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
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
                              DomTgt nu12' = DomSrc nu23' /\ 
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true -> 
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true -> 
                                         frgnBlocksSrc nu23' b = true)) /\
                             (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                     exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\ 
                              Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\ 
                                                             pubBlocksSrc nu23 b = false) m2 m2' /\
                              Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' /\
                              Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3'.

(*A variant of interpolation for unstructured injections, needed in 
   effect_simulations_trans.initial_inject_split*)
Parameter interpolate_II_strong: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1'
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
                   Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'. 

(*
Parameter interp: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1' 
                             (Fwd1: mem_forward m1 m1') j23 m3
                             (MInj23 : Mem.inject j23 m2 m3) m3' 
                             (Fwd3: mem_forward m3 m3')
                             j' (MInj13': Mem.inject j' m1' m3')
                             (InjIncr: inject_incr (compose_meminj j12 j23) j')
                             (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                             mu12 mu23
                             (Unch11': Mem.unchanged_on (fun b ofs => locBlocksSrc mu12 b /\ 
                                         loc_unmapped (pub_of (compose_sm mu12 mu23)) b ofs) m1 m1')
                             (HJ12: j12 = shared_of mu12) (HJ23: j23 = shared_of mu23)
                             (Unch33': Mem.unchanged_on (fun b ofs => locBlocksTgt mu23 b /\ 
                                         loc_out_of_reach (pub_of (compose_sm mu12 mu23)) m1 b ofs) m3 m3'),
                 exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                             inject_incr j12 j12' /\ inject_incr j23 j23' /\
                             Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ Mem.inject j23' m2' m3' /\
                             Mem.unchanged_on (fun b ofs => locBlocksTgt mu12 b /\ 
                                               loc_out_of_reach (pub_of mu12) m1 b ofs) m2 m2' /\
(*WAS:                             Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\*)
                             inject_separated j12 j12' m1 m2 /\ inject_separated j23 j23' m2 m3 /\
                             Mem.unchanged_on (fun b ofs => locBlocksSrc mu23 b /\ 
                                                            loc_unmapped (pub_of mu23) b ofs) m2 m2' /\
(*WAS:                             Mem.unchanged_on (loc_unmapped j23) m2 m2' /\ *)
                             Mem.unchanged_on (fun b ofs => locBlocksTgt mu23 b /\
                                        loc_out_of_reach (pub_of mu23) m2 b ofs) m3 m3' 
(*WAS:                             Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\*).      

Parameter effect_interp: forall m1 m2 mu12 (MInj12 : Mem.inject (shared_of mu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') mu23 m3
                             (MInj23 : Mem.inject (shared_of mu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                             j' j12 j23 
                             (MInj13': Mem.inject (join j' (pub_of (compose_sm mu12 mu23))) m1' m3')
                             (InjIncr: inject_incr (compose_meminj j12 j23) j')
                             (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                             (SMV12: sm_valid mu12 m1 m2)
                             (SMV23: sm_valid mu23 m2 m3)
                             (SMWD12: SM_wd mu12) (SMWD23: SM_wd mu23) 
                             (B: locBlocksTgt mu12 = locBlocksSrc mu23)
                             M1 M3
                             (Unch11': Mem.unchanged_on (fun (b : block) (ofs : Z) => ~ M1 b ofs) m1 m1')
                             (HJ12: j12 = foreign_of mu12) (HJ23: j23 = foreign_of mu23)
                             (Unch33': Mem.unchanged_on (fun (b : block) (ofs : Z) => ~ M3 b ofs) m3 m3')
              
                             (unmapped13_M1 : forall b ofs, locBlocksSrc (compose_sm mu12 mu23) b ->
                                loc_unmapped (pub_of (compose_sm mu12 mu23)) b ofs -> ~ M1 b ofs)
                             (HM3 : forall b ofs, locBlocksTgt (compose_sm mu12 mu23) b ->
                                 M3 b ofs -> exists b1 delta,
                                             pub_of (compose_sm mu12 mu23) b1 = Some (b, delta) /\
                                             M1 b1 (ofs - delta))
                        (*     (HMF3 : forall b ofs, ~locBlocksTgt (compose_sm mu12 mu23) b -> M3 b ofs -> 
                                     ((exists b1 delta, foreign_of (compose_sm mu12 mu23) b1 = Some(b,delta) 
                                                         /\ M1 b1 (ofs-delta)) 
                                       \/ (forall b1 delta, foreign_of (compose_sm mu12 mu23) b1 = Some(b,delta) -> 
                                           ~Mem.perm m1 b1 (ofs-delta) Max Nonempty)))
                        *)     (unmapped12_M1 : forall b ofs, locBlocksSrc mu12 b -> 
                                    loc_unmapped (pub_of mu12) b ofs -> ~ M1 b ofs)
                             (PermM1 : forall b ofs, M1 b ofs -> Mem.valid_block m1 b -> 
                                       Mem.perm m1 b ofs Max Nonempty)
                             (PermM3 : forall b ofs, M3 b ofs -> Mem.valid_block m3 b ->
                                       Mem.perm m3 b ofs Max Nonempty),
     exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                             inject_incr j12 j12' /\ inject_incr j23 j23' /\
                             Mem.inject (join j12' (pub_of mu12)) m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (join j23' (pub_of mu23)) m2' m3' /\
                             inject_separated j12 j12' m1 m2 /\ 
                             inject_separated j23 j23' m2 m3 /\
                 exists M2,
                             Mem.unchanged_on (fun (b : block) (ofs : Z) => ~ M2 b ofs) m2 m2' /\
                            (forall b ofs, M2 b ofs -> Mem.valid_block m2 b ->
                                       Mem.perm m2 b ofs Max Nonempty) /\
                            (forall b ofs, locBlocksSrc mu23 b -> loc_unmapped (pub_of mu23) b ofs -> ~ M2 b ofs) /\
                            (forall b ofs, locBlocksTgt mu23 b -> M3 b ofs -> exists b1 delta,
                                           pub_of mu23 b1 = Some (b, delta) /\
                                           M2 b1 (ofs - delta)) /\
                            (forall b ofs, locBlocksTgt mu12 b -> M2 b ofs -> exists b1 delta,
                                           pub_of mu12 b1 = Some (b, delta) /\
                                           M1 b1 (ofs - delta)) (* /\
                            (forall b ofs, ~locBlocksTgt mu12 b -> M2 b ofs -> 
                                     ((exists b1 delta, foreign_of mu12 b1 = Some(b,delta) 
                                                /\ M1 b1 (ofs-delta))
                                      \/ (forall b1 delta, foreign_of mu12 b1 = Some(b,delta) -> 
                                           ~Mem.perm m1 b1 (ofs-delta) Max Nonempty))) /\
                            (forall b ofs, ~locBlocksTgt mu23 b -> M3 b ofs -> 
                                     ((exists b1 delta, foreign_of mu23 b1 = Some(b,delta) 
                                                /\ M2 b1 (ofs-delta))
                                      \/ (forall b1 delta, foreign_of mu23 b1 = Some(b,delta) -> 
                                           ~Mem.perm m2 b1 (ofs-delta) Max Nonempty)))*).
*)   

(*An interpolation without any effects - proven by appealing to CHEAT-memII
  and used to work out the skeleton of the after_external cases
Parameter effect_interp: forall m1 m2 nu12 
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')
                             
                             (InjIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (InjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         DomTgt nu12 = DomSrc nu23 /\ 
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true -> 
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true -> 
                                                    frgnBlocksSrc nu23 b = true)),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (as_inj nu23') m2' m3' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\ 
                             sm_inject_separated nu23 nu23' m2 m3 /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              DomTgt nu12' = DomSrc nu23' /\ 
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true -> 
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true -> 
                                         frgnBlocksSrc nu23' b = true)).
*)

(*Parameter effect_interp_ModEffects: forall m1 m2 nu12 
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')
                             
                             (InjIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (InjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             M1 M3
                             (UnchSrc: Mem.unchanged_on (fun b ofs => ~M1 b ofs) m1 m1') 
                             (UnchTgt: Mem.unchanged_on (fun b ofs => ~M3 b ofs) m3 m3')
                             (PrivSrcNoeffect: forall b ofs,
                                           locBlocksSrc (compose_sm nu12 nu23) b = true -> 
                                           loc_unmapped (pub_of (compose_sm nu12 nu23)) b ofs -> 
                                           ~M1 b ofs)
                             (LocalTgtReverseEffect : forall b ofs, locBlocksTgt (compose_sm nu12 nu23) b = true ->
                                                       M3 b ofs ->
                                   exists b1 delta, pub_of (compose_sm nu12 nu23) b1 = Some (b, delta) /\
                                                    M1 b1 (ofs - delta))
                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         DomTgt nu12 = DomSrc nu23 /\ 
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true -> 
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true -> 
                                                    frgnBlocksSrc nu23 b = true)),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (as_inj nu23') m2' m3' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\ 
                             sm_inject_separated nu23 nu23' m2 m3 /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              DomTgt nu12' = DomSrc nu23' /\ 
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true -> 
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true -> 
                                         frgnBlocksSrc nu23' b = true)) /\
                              exists M2,
                                 Mem.unchanged_on (fun b ofs => ~M2 b ofs) m2 m2' /\
                                 (forall b ofs,
                                           locBlocksSrc nu23 b = true -> 
                                           loc_unmapped (pub_of nu23) b ofs -> 
                                           ~M2 b ofs) /\
                                 (forall b ofs, locBlocksTgt nu12 b = true -> M2 b ofs -> 
                                           exists b1 delta, (pub_of nu12) b1 = Some(b,delta) /\ 
                                                            M1 b1 (ofs-delta)).
*)

End EffectInterpolationAxioms.