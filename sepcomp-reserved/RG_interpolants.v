Require Import Events.
Require Import Memory.
Require Import AST.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
(*CompCert imports*)
(*Add LoadPath "../compcert/lib".
Add LoadPath "../compcert/flocq/Appli".
Add LoadPath "../compcert/flocq/Calc".
Add LoadPath "../compcert/flocq/Core".
Add LoadPath "../compcert/flocq/Prop".
Add LoadPath "../compcert/common".
Add LoadPath "../compcert/cfrontend".
Add LoadPath "..".
Require Import compcert.common.Events. (*needed for standard definitions of 
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import compcert.common.Memory.
Require Import compcert.common.AST.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.Globalenvs.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.*)
(*
Definition reserve_image (*{F1 V1 C1:Type} 
      (Sem: RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))*)
      (j:meminj) (r:reserve'):reserve'.
  eapply Build_reserve' with 
     (sort :=fun b2 => fun ofs => exists b1, exists delta2, j b1 = Some(b2, delta2) /\ r b1 (ofs - delta2)).
   admit. (*TODO -maybe use source-construction?*)
Defined.
*)

Module Type RGInterpolationAxioms.
(*
Parameter interpolate_EE: forall m1 m2 (Ext12: Mem.extends m1 m2) m1' 
            (Fwd1: mem_forward m1 m1') m3 (Ext23: Mem.extends m2 m3) m3' 
            (Fwd3: mem_forward m3 m3') (Ext13' : Mem.extends m1' m3')
            (UnchOn3: mem_unchanged_on (loc_out_of_bounds m1) m3 m3') 
            (WD3': mem_wd m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ Mem.extends m2' m3' /\
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                  (mem_wd m2 -> mem_wd m2').

Parameter interpolate_EI: forall (m1 m2 m1':mem) (Ext12: Mem.extends m1 m2) (Fwd1: mem_forward m1 m1')
                              m3 j (Inj23: Mem.inject j m2 m3) m3' (Fwd3: mem_forward m3 m3') j'
                             (Inj13': Mem.inject j' m1' m3')
                             (UnchOn3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3') 
                             (InjInc: inject_incr j j') (injSep: inject_separated j j' m1 m3)
                             (UnchOn1: mem_unchanged_on (loc_unmapped j) m1 m1') (WD1':mem_wd m1') (WD2: mem_wd m2)
                             (WD3': mem_wd m3'),
       exists m2', mem_forward m2 m2' /\ Mem.extends m1' m2' /\ Mem.inject j' m2' m3' /\ 
                   mem_unchanged_on (loc_out_of_bounds m1) m2 m2' /\
                   mem_unchanged_on (loc_unmapped j) m2 m2' /\
                   (mem_wd m2 -> mem_wd m2').

Parameter interpolate_IE: forall m1 m1' m2 j (Minj12 : Mem.inject j m1 m2) (Fwd1: mem_forward m1 m1') 
                             j' (InjInc: inject_incr j j')  (Sep12 : inject_separated j j' m1 m2) 
                             (UnchLUj: mem_unchanged_on (loc_unmapped j) m1 m1')
                             m3 m3' (Ext23 : Mem.extends m2 m3) (Fwd3: mem_forward m3 m3') 
                             (UnchLOORj1_3: mem_unchanged_on (loc_out_of_reach j m1) m3 m3')
                             (Inj13' : Mem.inject j' m1' m3')
                             (UnchLOOB23_3' : mem_unchanged_on (loc_out_of_bounds m2) m3 m3')
                             (WD2: mem_wd m2) (WD1' : mem_wd m1') (WD3': mem_wd m3'),
                 exists m2',  mem_forward m2 m2' /\ Mem.extends m2' m3' /\ Mem.inject j' m1' m2' /\
                             mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                             (mem_wd m2 -> mem_wd m2').                                         
*)
Parameter interpolate_II: forall {F1 V1 C1 F2 V2 C2:Type}
(Sem1 : EffectfulSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
(Sem2 : EffectfulSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
                             m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1' (Fwd1: mem_forward m1 m1') j23 m3
                             (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                             j' (MInj13': Mem.inject j' m1' m3')
                             (InjIncr: inject_incr (compose_meminj j12 j23) j')
                             (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                             (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3: mem_wd m3) (WD3' : mem_wd m3')
                             (r r': reserve) 
                             (Rinc: reserve_incr r r')
                             (Rsep13: reserve_separated r r' j' m1 m3)
                              
                   RELY1 (RELY1_dec: forall b ofs, {RELY1 b ofs} + {~RELY1 b ofs})
                   (Uniform1: uniform RELY1 j12)
                             (Unch11': mem_unchanged_on RELY1 m1 m1' ) (*RELY1 is rely Sem1 r st1:  (Unch11': rely Sem1 r st1 m1 m1' )*)
                             RELY
                             (Unch33':  mem_unchanged_on RELY m3 m3' )  (*RELY is rely Sem3 (inject_reserve (compose_meminj j12 j23) r) st3 m3 m3')*)                            
(*                             (Unch33': rely Sem1 (inject_reserve (compose_meminj j12 j23) r) st1 m3 m3')*)
(*                             (Unch11': mem_unchanged_on (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                             (Unch33': mem_unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')*),
                 exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                             inject_incr j12 j12' /\ inject_incr j23 j23' /\
                             Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ Mem.inject j23' m2' m3' /\
                             inject_separated j12 j12' m1 m2 /\ inject_separated j23 j23' m2 m3 /\
                             (mem_wd m2 -> mem_wd m2') /\
                             reserve_separated r r' j12' m1 m2 /\
                      exists r23,  r23 = inject_reserve j12 r /\
                      exists (RELY2: block -> Z -> Prop),
                             (forall b1 ofs b2 delta2, j12 b1 = Some(b2,delta2) -> RELY1 b1 ofs -> RELY2 b2 (ofs + delta2)) /\
                             mem_unchanged_on RELY2 m2 m2' (*  RELY2 should probably be rely Sem2 (inject_reserve j12 r) st2 m2 m2' *)
(*                             mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\*)

                             (*again? rely Sem2 r23 st2 m2 m2' /\ *)

(*WAS:                             mem_unchanged_on (loc_unmapped j23) m2 m2' /\ *)
(*WAS:                             rely Sem2 (inject_reserve j23 r23) st2 m3 m3' /\*)
                        (* /\ exists RELY3,
                             mem_unchanged_on RELY3 m3 m3' *) (*RELY33 should probably be rely Sem3 (inject_reserve j23 r23) st3 m3 m3' /\*)

(*WAS:                             mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\*) .                         

End RGInterpolationAxioms.