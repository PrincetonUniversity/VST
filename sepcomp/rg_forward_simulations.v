Require Import Coqlib.
Require Import ListSet.
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import AST.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.rg_semantics.
Require Import sepcomp.forward_simulations.


Module RGForward_simulation_ext. 
Section RGForward_simulation_extends. 
  Context {G1 C1 G2 C2:Type}
          {Sem1: RelyGuaranteeSemantics G1 C1}
          {Sem2: RelyGuaranteeSemantics  G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record RGForward_simulation_extends := 
  { core_data : Type;

    match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          Mem.unchanged_on (fun b ofs => 
            (*I'm not sure whether this should be ~private_block st1 or
               ~private_block st2.  Perhaps it doesn't matter if we know that 
               private_block st2 -> private_block st1 over extension passes. *)
            loc_out_of_bounds m1 b ofs /\ ~private_block Sem1 st1 b) m2 m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            initial_core Sem1 ge1 v1 vals = Some c1 /\
            initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2;

    core_halted : 
      forall cd st1 m1 st2 m2 v1,
        match_state cd st1 m1 st2 m2 ->
        halted Sem1 st1 = Some v1 ->
        exists v2, Val.lessdef v1 v2 /\
            halted Sem2 st2 = Some v2 /\
            Mem.extends m1 m2;

    core_at_external : 
      forall cd st1 m1 st2 m2 e vals1 ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
          at_external Sem2 st2 = Some (e,ef_sig,vals2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        at_external Sem2 st2 = Some (e,ef_sig,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args ef_sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Mem.unchanged_on (fun b ofs => 
          loc_out_of_bounds m1 b ofs /\ private_block Sem1 st1 b) m2 m2' -> 
       (*i.e., spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res ef_sig) -> 

        exists st1', exists st2', exists cd',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2' }.

End RGForward_simulation_extends.

Implicit Arguments RGForward_simulation_extends [[G1] [C1] [G2] [C2]].

End RGForward_simulation_ext.

Module RGForward_simulation_inj. Section RGForward_simulation_inject. 
  Context {F1 V1 C1 G2 C2:Type}
          {Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1}
          {Sem2 : RelyGuaranteeSemantics G2 C2}
          {ge1: Genv.t F1 V1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record RGForward_simulation_inject := 
  { core_data : Type;
    match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;
    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          Mem.unchanged_on (fun b ofs => 
            loc_unmapped j b ofs /\ ~private_block Sem1 st1 b) m1 m1' /\
          Mem.unchanged_on (fun b ofs => 
            loc_out_of_reach j m1 b ofs /\ ~private_block Sem2 st2 b) m2 m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          Forall2 (val_inject j) vals1 vals2 ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state cd j c1 m1 c2 m2;

    core_halted : forall cd j c1 m1 c2 m2 v1 rty,
      match_state cd j c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->
      Val.has_type v1 rty -> 
      exists v2, val_inject j v1 v2 /\
          halted Sem2 c2 = Some v2 /\
          Val.has_type v2 rty /\
          Mem.inject j m1 m2;

    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1 sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ 
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,sig,vals2));

    core_after_external :
      forall cd j j' st1 st2 m1 e vals1 ret1 m1' m2 m2' ret2 sig,
        Mem.inject j m1 m2->
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        meminj_preserves_globals ge1 j -> 

        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject_opt j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         Mem.unchanged_on (fun b ofs => 
           loc_unmapped j b ofs /\ private_block Sem1 st1 b) m1 m1' ->
         mem_forward m2 m2' -> 
         Mem.unchanged_on (fun b ofs => 
           loc_out_of_reach j m1 b ofs /\ private_block Sem2 st2 b) m2 m2' ->
         val_has_type_opt' ret1 (proj_sig_res (ef_sig e)) -> 
         val_has_type_opt' ret2 (proj_sig_res (ef_sig e)) -> 

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2' }.

End RGForward_simulation_inject. 

Implicit Arguments RGForward_simulation_inject [[F1][V1] [C1] [G2] [C2]].

End RGForward_simulation_inj.
(* A variation of Forward_simulation_inj that exposes core_data and match_state *)

Module RGForward_simulation_inj_exposed. Section RGForward_simulation_inject. 
  Context {F1 V1 C1 G2 C2:Type}
          {Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1}
          {Sem2 : RelyGuaranteeSemantics G2 C2}

          {ge1: Genv.t F1 V1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}
          {core_data : Type}
          {match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop}
          {core_ord : core_data -> core_data -> Prop}.

  Record RGForward_simulation_inject := 
  { core_ord_wf : well_founded core_ord;
    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          Mem.unchanged_on (fun b ofs => 
            loc_unmapped j b ofs /\ ~private_block Sem1 st1 b) m1 m1' /\
          Mem.unchanged_on (fun b ofs => 
            loc_out_of_reach j m1 b ofs /\ ~private_block Sem2 st2 b) m2 m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
           Forall2 (val_inject j) vals1 vals2 ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state cd j c1 m1 c2 m2;

    core_halted : forall cd j c1 m1 c2 m2 v1 rty,
      match_state cd j c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->
      Val.has_type v1 rty -> 
      exists v2, val_inject j v1 v2 /\
        halted Sem2 c2 = Some v2 /\
        Val.has_type v2 rty /\
        Mem.inject j m1 m2;

    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1 sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ 
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,sig,vals2));

    core_after_external :
      forall cd j j' st1 st2 m1 e vals1 ret1 m1' m2 m2' ret2 sig,
        Mem.inject j m1 m2->
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        meminj_preserves_globals ge1 j -> 

        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject_opt j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         Mem.unchanged_on (fun b ofs => 
           loc_unmapped j b ofs /\ private_block Sem1 st1 b) m1 m1' ->
         mem_forward m2 m2' -> 
         Mem.unchanged_on (fun b ofs => 
           loc_out_of_reach j m1 b ofs /\ private_block Sem2 st2 b) m2 m2' ->
         val_has_type_opt' ret1 (proj_sig_res (ef_sig e)) -> 
         val_has_type_opt' ret2 (proj_sig_res (ef_sig e)) -> 

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'
    }.

End RGForward_simulation_inject. 

Implicit Arguments RGForward_simulation_inject [[F1][V1] [C1] [G2] [C2]].

End RGForward_simulation_inj_exposed.

Lemma RGForward_simulation_inj_exposed_hidden: 
  forall (F1 V1 C1 G2 C2: Type) 
   (csemS: RelyGuaranteeSemantics (Genv.t F1 V1) C1)
   (csemT: RelyGuaranteeSemantics G2 C2) ge1 ge2 
   entry_points core_data match_state core_ord,
  RGForward_simulation_inj_exposed.RGForward_simulation_inject csemS csemT ge1 ge2
    entry_points core_data match_state core_ord -> 
  RGForward_simulation_inj.RGForward_simulation_inject csemS csemT ge1 ge2 entry_points.
Proof.
intros until core_ord; intros []; intros.
solve[eapply @RGForward_simulation_inj.Build_RGForward_simulation_inject 
 with (core_data := core_data) (match_state := match_state); eauto].
Qed.

Lemma RGForward_simulation_inj_hidden_exposed:
  forall (F1 V1 C1 G2 C2: Type) 
   (csemS: RelyGuaranteeSemantics (Genv.t F1 V1) C1)
   (csemT: RelyGuaranteeSemantics G2 C2) ge1 ge2 entry_points,
  RGForward_simulation_inj.RGForward_simulation_inject csemS csemT ge1 ge2 entry_points -> 
  {core_data: Type & 
  {match_state: core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop &
  {core_ord: core_data -> core_data -> Prop & 
    RGForward_simulation_inj_exposed.RGForward_simulation_inject csemS csemT ge1 ge2
    entry_points core_data match_state core_ord}}}.
Proof.
intros until entry_points; intros []; intros.
solve[eexists; eexists; eexists;
 eapply @RGForward_simulation_inj_exposed.Build_RGForward_simulation_inject; eauto].
Qed.

Set Implicit Arguments.

Definition runnable {G C M} (csem: CoreSemantics G C M) (c: C) :=
  match at_external csem c, halted csem c with 
  | None, None => true
  | _, _ => false
  end.

Local Open Scope Z_scope.

(*This is an [F,V]-independent definition of meminj_preserves_globals*)
Definition meminj_preserves_globals_ind (globals: (block->Prop)*(block->Prop)) f :=
  (forall b, fst globals b -> f b = Some (b, 0)) /\
  (forall b, snd globals b -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, snd globals b2 -> f b1 = Some (b2, delta) -> b1=b2).

Definition genv2blocks {F V: Type} (ge: Genv.t F V) := 
  (fun b => exists id, Genv.find_symbol ge id = Some b,
   fun b => exists gv, Genv.find_var_info ge b = Some gv).

(** RelyGuarantee Simulations *)

Module RelyGuaranteeSimulation. Section RelyGuaranteeSimulation.
 Variables (F1 V1 C1 G2 C2: Type).
 Variables 
  (sourceC: RelyGuaranteeSemantics (Genv.t F1 V1) C1)
  (targetC: RelyGuaranteeSemantics G2 C2) 
  (ge1: Genv.t F1 V1) (ge2: G2) 
  (entry_points: list (val * val * signature))
  (core_data: Type)
  (match_state: core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop).

 Import RGForward_simulation_inj_exposed.

 Inductive Sig: Type := Make: forall
  (match_state_runnable: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> 
    runnable sourceC c1 = runnable targetC c2)

  (match_state_inj: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)

  (match_state_preserves_globals: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> 
    meminj_preserves_globals ge1 j),
  Sig.

End RelyGuaranteeSimulation. End RelyGuaranteeSimulation.

Module StableRelyGuaranteeSimulation. Section StableRelyGuaranteeSimulation.
 Variables (F1 V1 C1 INIT1 G2 C2 INIT2: Type).
 Variables 
  (sourceC: RelyGuaranteeSemantics (Genv.t F1 V1) C1)
  (targetC: RelyGuaranteeSemantics G2 C2) 
  (ge1: Genv.t F1 V1) (ge2: G2) 
  (entry_points: list (val * val * signature))
  (core_data: Type)
  (match_state: core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop).

 Import RGForward_simulation_inj_exposed.

 Inductive Sig: Type := Make: forall
  (match_state_runnable: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> 
    runnable sourceC c1 = runnable targetC c2)

  (match_state_inj: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)

  (match_state_preserves_globals: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> 
    meminj_preserves_globals ge1 j)

  (stable: forall (ge1: Genv.t F1 V1) cdC m1 m1' f f' m2 m2' c1 c2,
    (** Rely *)
    Mem.inject f m1 m2 -> 
    meminj_preserves_globals_ind (genv2blocks ge1) f -> 
    Mem.inject f' m1' m2' -> 
    Mem.unchanged_on (fun b ofs => 
      loc_unmapped f b ofs /\ private_block sourceC c1 b) m1 m1' ->
    Mem.unchanged_on (fun b ofs => 
      loc_out_of_reach f m1 b ofs /\ private_block targetC c2 b) m2 m2' ->
    inject_incr f f' -> 
    inject_separated f f' m1 m2 -> 

    (** Match is stable *)
    match_state cdC f c1 m1 c2 m2 -> 
    match_state cdC f' c1 m1' c2 m2'),
  Sig.

End StableRelyGuaranteeSimulation. End StableRelyGuaranteeSimulation.

