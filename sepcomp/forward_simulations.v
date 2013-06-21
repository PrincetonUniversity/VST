(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.

(** * Here we present a module type which expresses the sort of
   forward simulation lemmas we have available.  The idea is that
   these lemmas would be used in the individual compiler passes and
   the composition lemma would be used to build the main lemma. 

   First, a forward simulation for passes which do not alter the
   memory layout at all. *)

Module Forward_simulation_eq. Section Forward_simulation_equals. 
  Context {M G1 C1 G2 C2:Type}
          {Sem1 : CoreSemantics G1 C1 M}
          {Sem2 : CoreSemantics G2 C2 M}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_equals :=
  { core_data:Type;

    match_core : core_data -> C1 -> C2 -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m st1' m', corestep Sem1 ge1 st1 m st1' m' ->
      forall d st2, match_core d st1 st2 ->
        exists st2', exists d',
          match_core d' st1' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord d' d);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals,
          Forall2 (Val.has_type) vals (sig_args sig) ->
          exists cd, exists c1, exists c2,
            initial_core Sem1 ge1 v1 vals = Some c1 /\
            initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_core cd c1 c2;

    core_halted : forall cd c1 c2 v,
      match_core cd c1 c2 ->
      halted Sem1 c1 = Some v ->
      halted Sem2 c2 = Some v;

    core_at_external : 
      forall d st1 st2 e args ef_sig,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,ef_sig,args) ->
        ( at_external Sem2 st2 = Some (e,ef_sig,args) /\
          Forall2 Val.has_type args (sig_args ef_sig) );

    core_after_external :
      forall d st1 st2 ret e args ef_sig,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,ef_sig,args) ->
        at_external Sem2 st2 = Some (e,ef_sig,args) ->
        Forall2 Val.has_type args (sig_args ef_sig) ->
        Val.has_type ret (proj_sig_res ef_sig) ->
        exists st1', exists st2', exists d',
          after_external Sem1 (Some ret) st1 = Some st1' /\
          after_external Sem2 (Some ret) st2 = Some st2' /\
          match_core d' st1' st2' }.

End Forward_simulation_equals. 

(*Question: Does this declaration take effect after module import?*)
Implicit Arguments Forward_simulation_equals [[M] [G1] [C1] [G2] [C2]]. 

End Forward_simulation_eq.

(** * Next, an axiom for passes that allow the memory to undergo extension. *)
(*As extensions require CompCert memories, such simulations can only be formulated 
for core semantics with (M:=mem)*)

Module Forward_simulation_ext. Section Forward_simulation_extends. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CoreSemantics G1 C1 mem}
          {Sem2 : CoreSemantics G2 C2 mem}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_extends :=
  { core_data : Type;

    match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    (*Matching memories should be well-defined ie not contain values
        with invalid/"dangling" block numbers*)
    match_memwd: forall d c1 m1 c2 m2,  match_state d c1 m1 c2 m2 -> 
      (mem_wd m1 /\ mem_wd m2);

    (*The following axiom could be strengthened to extends m1 m2*)
    match_validblocks: forall d c1 m1 c2 m2,  match_state d c1 m1 c2 m2 -> 
      forall b, Mem.valid_block m1 b <-> Mem.valid_block m2 b;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          mem_wd m1 -> mem_wd m2 ->
          exists cd, exists c1, exists c2,
            initial_core Sem1 ge1 v1 vals = Some c1 /\
            initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2;

    core_halted : 
      forall cd st1 m1 st2 m2 v1,
        match_state cd st1 m1 st2 m2 ->
        halted Sem1 st1 = Some v1 -> val_valid v1 m1 ->
        exists v2, Val.lessdef v1 v2 /\
            halted Sem2 st2 = Some v2 /\
            Mem.extends m1 m2 /\ val_valid v2 m2;

    core_at_external : 
      forall cd st1 m1 st2 m2 e vals1 ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) -> 
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
          at_external Sem2 st2 = Some (e,ef_sig,vals2) /\
          (forall v2, In v2 vals2 -> val_valid v2 m2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) -> 
        at_external Sem2 st2 = Some (e,ef_sig,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args ef_sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Mem.unchanged_on (loc_out_of_bounds m1) m2 m2' -> 
        (*i.e., spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res ef_sig) -> 

        mem_wd m1' -> mem_wd m2' -> val_valid ret1 m1' -> val_valid ret2 m2' ->

        exists st1', exists st2', exists cd',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2' }.
End Forward_simulation_extends.

Implicit Arguments Forward_simulation_extends [[G1] [C1] [G2] [C2]].

End Forward_simulation_ext.

(*The same for CoopCoreSem's - but this can just be obtained by instantiating the
previous definition to 
          {Sem1 : CoopCoreSem G1 C1}
          {Sem2 : CoopCoreSem G2 C2}
Module Coop_forward_simulation_ext. Section Forward_simulation_extends. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CoopCoreSem G1 C1}
          {Sem2 : CoopCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_extends :=
  { core_data : Type;

    match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    (*Matching memories should be well-defined ie not contain values
        with invalid/"dangling" block numbers*)
    match_memwd: forall d c1 m1 c2 m2,  match_state d c1 m1 c2 m2 -> 
      (mem_wd m1 /\ mem_wd m2);

    (*The following axiom could be strengthened to extends m1 m2*)
    match_validblocks: forall d c1 m1 c2 m2,  match_state d c1 m1 c2 m2 -> 
      forall b, Mem.valid_block m1 b <-> Mem.valid_block m2 b;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          mem_wd m1 -> mem_wd m2 ->
          exists cd, exists c1, exists c2,
            initial_core Sem1 ge1 v1 vals = Some c1 /\
            initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2;

    core_halted : 
      forall cd st1 m1 st2 m2 v1,
        match_state cd st1 m1 st2 m2 ->
        halted Sem1 st1 = Some v1 -> val_valid v1 m1 ->
        exists v2, Val.lessdef v1 v2 /\
            halted Sem2 st2 = Some v2 /\
            Mem.extends m1 m2 /\ val_valid v2 m2;

    core_at_external : 
      forall cd st1 m1 st2 m2 e vals1 ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) -> 
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
          at_external Sem2 st2 = Some (e,ef_sig,vals2) /\
          (forall v2, In v2 vals2 -> val_valid v2 m2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) -> 
        at_external Sem2 st2 = Some (e,ef_sig,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args ef_sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Mem.unchanged_on (loc_out_of_bounds m1) m2 m2' -> 
        (*i.e., spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res ef_sig) -> 

        mem_wd m1' -> mem_wd m2' -> val_valid ret1 m1' -> val_valid ret2 m2' ->

        exists st1', exists st2', exists cd',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2' }.
End Forward_simulation_extends.

Implicit Arguments Forward_simulation_extends [[G1] [C1] [G2] [C2]].

End Coop_forward_simulation_ext.
*)

(** An axiom for passes that use memory injections. *)
(*Again, we specialize (M:=mem), and also G1:=Genv F1 V1, due to
the typing constraint of meminj_preserves_globals ge1 j
in the at_external clause*)


Module Forward_simulation_inj. Section Forward_simulation_inject. 
  Context {F1 V1 C1 G2 C2:Type}
          {Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem}
          {Sem2 : CoreSemantics G2 C2 mem}
          {ge1: Genv.t F1 V1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_inject := 
  { core_data : Type;
    match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    (*Matching memories should be well-defined ie not contain values
        with invalid/"dangling" block numbers*)
    match_memwd: forall d j c1 m1 c2 m2,  match_state d j c1 m1 c2 m2 -> 
               (mem_wd m1 /\ mem_wd m2);

    (*The following axiom could be strengthened to inject j m1 m2*)
    match_validblocks: forall d j c1 m1 c2 m2,  match_state d j c1 m1 c2 m2 -> 
          forall b1 b2 ofs, j b1 = Some(b2,ofs) -> 
               (Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2);

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          mem_wd m1 -> mem_wd m2 ->
          (*Is this line needed?? (forall w1 w2 sigg, In (w1,w2,sigg)
           entry_points -> val_inject j w1 w2) ->*) Forall2
           (val_inject j) vals1 vals2 ->

          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state cd j c1 m1 c2 m2;

    core_halted : forall cd j c1 m1 c2 m2 v1,
      match_state cd j c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->
      val_valid v1 m1 ->
      exists v2, val_inject j v1 v2 /\
        halted Sem2 c2 = Some v2 /\
        Mem.inject j m1 m2 /\ val_valid v2 m2;

    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1 ef_sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ 
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
          at_external Sem2 st2 = Some (e,ef_sig,vals2) /\
          (forall v2, In v2 vals2 -> val_valid v2 m2));

    core_after_external :
      forall cd j j' st1 st2 m1 e vals1 ret1 m1' m2 m2' ret2 ef_sig,
        Mem.inject j m1 m2->
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        (forall v1, In v1 vals1 -> val_valid v1 m1) ->
        meminj_preserves_globals ge1 j -> 

        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         Mem.unchanged_on (loc_unmapped j) m1 m1' ->
         mem_forward m2 m2' -> 
         Mem.unchanged_on (loc_out_of_reach j m1) m2 m2' ->
         Val.has_type ret2 (proj_sig_res ef_sig) -> 

        mem_wd m1' -> mem_wd m2' -> val_valid ret1 m1' -> val_valid ret2 m2' ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'
    }.

End Forward_simulation_inject. 

Implicit Arguments Forward_simulation_inject [[F1] [V1] [C1] [G2] [C2]].

End Forward_simulation_inj.

Module Forward_simulation.
Section Core_sim.
Context {F1 V1 C1 F2 V2 C2:Type}
        (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
        (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem).

Inductive core_sim G1 G2 entrypoints:Type :=
  core_sim_eq: forall (R:@Forward_simulation_eq.Forward_simulation_equals 
                    mem _ _ _ _ Sem1 Sem2 G1 G2 entrypoints),
          core_sim G1 G2 entrypoints
| core_sim_ext: forall (R:@Forward_simulation_ext.Forward_simulation_extends
                    _ _ _ _ Sem1 Sem2 G1 G2 entrypoints),
          core_sim G1 G2 entrypoints
| core_sim_inj: forall (R:@Forward_simulation_inj.Forward_simulation_inject
                    _ _ _ _ _ Sem1 Sem2 G1 G2 entrypoints),
          core_sim G1 G2 entrypoints.
End Core_sim.

Section Coop_sim.
Context {F1 V1 C1 F2 V2 C2:Type}
        (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
        (Sem2 : CoopCoreSem (Genv.t F2 V2) C2).

Inductive coop_sim G1 G2 entrypoints:Type :=
  coop_sim_eq: forall (R:@Forward_simulation_eq.Forward_simulation_equals 
                    mem _ _ _ _ Sem1 Sem2 G1 G2 entrypoints),
          coop_sim G1 G2 entrypoints
| coop_sim_ext: forall (R:@Forward_simulation_ext.Forward_simulation_extends
                    _ _ _ _ Sem1 Sem2 G1 G2 entrypoints),
          coop_sim G1 G2 entrypoints
| coop_sim_inj: forall (R:@Forward_simulation_inj.Forward_simulation_inject
                    _ _ _ _ _ Sem1 Sem2 G1 G2 entrypoints),
          coop_sim G1 G2 entrypoints.
End Coop_sim.

End Forward_simulation.
