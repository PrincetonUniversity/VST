(*CompCert imports*)
Require Import Events. (*needed for standard definitions of 
                        mem_unchanged_on,loc_out-of_bounds etc etc*)
Require Import Memory.
Require Import AST.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.

Require Import sepcomp.mem_lemmas.

Module Type MemoryInterpolationAxioms.

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

Parameter interpolate_II: forall m1 m2 j12 (MInj12 : Mem.inject j12 m1 m2) m1' (Fwd1: mem_forward m1 m1') j23 m3
                             (MInj23 : Mem.inject j23 m2 m3) m3' (Fwd3: mem_forward m3 m3')
                             j' (MInj13': Mem.inject j' m1' m3')
                             (InjIncr: inject_incr (compose_meminj j12 j23) j')
                             (InjSep: inject_separated (compose_meminj j12 j23) j' m1 m3)
                             (Unch11': mem_unchanged_on (loc_unmapped (compose_meminj j12 j23)) m1 m1')
                             (Unch33': mem_unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3')
                             (WD1: mem_wd m1) (WD1': mem_wd m1') (WD2: mem_wd m2) (WD3: mem_wd m3) (WD3' : mem_wd m3'),
                 exists m2', exists j12', exists j23', j'=compose_meminj j12' j23' /\
                             inject_incr j12 j12' /\ inject_incr j23 j23' /\
                             Mem.inject j12' m1' m2' /\ mem_forward m2 m2' /\ Mem.inject j23' m2' m3' /\
                             mem_unchanged_on (loc_out_of_reach j12 m1) m2 m2' /\
                             inject_separated j12 j12' m1 m2 /\ inject_separated j23 j23' m2 m3 /\
                             mem_unchanged_on (loc_unmapped j23) m2 m2' /\ 
                             mem_unchanged_on (loc_out_of_reach j23 m2) m3 m3' /\
                             (mem_wd m2 -> mem_wd m2').                                 

End MemoryInterpolationAxioms.