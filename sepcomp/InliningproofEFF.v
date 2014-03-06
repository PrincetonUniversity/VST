Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import sepcomp.Inlining.
Require Import sepcomp.Inliningspec.
Require Import RTL.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.
Require Import CminorSel_coop.
Require Import RTL_eff.
Require Import RTL_coop.

Load Santiago_tactics.

Variable SrcProg: RTL.program.
Variable TrgProg: RTL.program.
Let SrcGe : RTL.genv := Genv.globalenv SrcProg.
Let TrgGe : RTL.genv := Genv.globalenv TrgProg.

(*LENB: GFP as in selectionproofEFF*)
Definition globalfunction_ptr_inject (j:meminj):=
  forall b f, Genv.find_funct_ptr SrcGe b = Some f -> 
              j b = Some(b,0) /\ isGlobalBlock SrcGe b = true. 

(*The new match_states*)
Inductive match_states (j:meminj): RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_state:
      forall f s k sp e m tm cs tf ns rs (*map ncont nexits ngoto nret rret*) sp'
        (*(MWF: map_wf map)*)
        (*(TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)*)
        (*(TF: tr_fun tf map f ngoto nret rret)*)
        (*(TK: tr_cont j tf.(fn_code) map k ncont nexits ngoto nret rret cs)*)
        (*(ME: match_env j map e nil rs)*)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm)
        (*(*NEW:*) (SP: sp_preserved j sp sp')*),
      match_states j (RTL_State f s k sp e) m
                     (RTL_State cs tf sp' ns rs) tm
  | match_callstate:
      forall f args targs k m tm cs tf
        (*(TF: transl_fundef f = OK tf)*)
        (*(MS: match_stacks j k cs)*)
        (*(LD: Val.lessdef_list args targs)*)
        (*(AINJ: val_list_inject j args targs)*)
        (*(MEXT: Mem.extends m tm)*)
        (*(MINJ: Mem.inject j m tm)*),
      match_states j (RTL_Callstate f args k) m
                     (RTL_Callstate cs tf targs) tm
  | match_returnstate:
      forall v tv k m tm cs
        (*(MS: match_stacks j k cs)*)
        (*(LD: Val.lessdef v tv)*)
         (*(VINJ: val_inject j v tv)*)
        (*(MEXT: Mem.extends m tm)*)
        (*(MINJ: Mem.inject j m tm)*),
      match_states j (RTL_Returnstate v k) m
                     (RTL_Returnstate cs tv) tm.

Print restrict.
Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals SrcGe (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.


(** The simulation proof *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs SrcProg)))
         entrypoints
         (entry_points_ok : 
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints -> 
              exists b f1 f2, 
                v1 = Vptr b Int.zero 
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr SrcGe b = Some f1
                /\ Genv.find_funct_ptr TrgGe b = Some f2)
         (init_mem: exists m0, Genv.init_mem SrcProg = Some m0),
SM_simulation.SM_simulation_inject rtl_eff_sem
   rtl_eff_sem SrcGe TrgGe entrypoints.

intros.
eapply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf.
Lemma genvs_domain_eq_implication: (exists m0:mem, Genv.init_mem SrcProg = Some m0) -> 
genvs_domain_eq SrcGe TrgGe.
Admitted.
apply genvs_domain_eq_implication; auto.
Lemma match_correspondance: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
     (m1 : mem) (c2 : RTL_core) (m2 : mem), MATCH d mu c1 m1 c2 m2 -> SM_wd mu.
Admitted.
eapply match_correspondance.
Lemma match_to_reach: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
     (m1 : mem) (c2 : RTL_core) (m2 : mem),
   MATCH d mu c1 m1 c2 m2 -> REACH_closed m1 (vis mu).
Admitted.
apply match_to_reach.





Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.

Inductive match_states (j:meminj): CMinSel_core -> mem -> RTL_core -> mem -> Prop :=
  | match_state:
      forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret sp'
        (MWF: map_wf map)
        (TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
        (TF: tr_fun tf map f ngoto nret rret)
        (TK: tr_cont j tf.(fn_code) map k ncont nexits ngoto nret rret cs)
        (ME: match_env j map e nil rs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm)
        (*NEW:*) (SP: sp_preserved j sp sp'),
      match_states j (CMinSel_State f s k sp e) m
                     (RTL_State cs tf sp' ns rs) tm
  | match_callstate:
      forall f args targs k m tm cs tf
        (TF: transl_fundef f = OK tf)
        (MS: match_stacks j k cs)
        (*(LD: Val.lessdef_list args targs)*)
        (AINJ: val_list_inject j args targs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm),
      match_states j (CMinSel_Callstate f args k) m
                     (RTL_Callstate cs tf targs) tm
  | match_returnstate:
      forall v tv k m tm cs
        (MS: match_stacks j k cs)
        (*(LD: Val.lessdef v tv)*)
         (VINJ: val_inject j v tv)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm),
      match_states j (CMinSel_Returnstate v k) m
                     (RTL_Returnstate cs tv) tm.



Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Print effstep.
Print rtl_eff_sem.
Print vis.
Print locBlocksSrc.

Variable tprog: RTL.program.
Let tge : RTL.genv := Genv.globalenv tprog.
Print genv.

Lemma MATCH_effcore_diagram: forall 
         st1 m1 st1' m1' (U1 : block -> Z -> bool) ge'
         (CS: effstep rtl_eff_sem ge' U1 st1 m1 st1' m1') (* unpacks the effect step. RTL_effstep. *)
         st2 mu m2 
         (UHyp: forall b z, U1 b z = true -> 
                Mem.valid_block m1 b -> vis mu b = true) (* Proof that allocated valid blocks are visible in the source*)
         (*(MTCH: MATCH st1 mu st1 m1 st2 m2)*),
exists st2' m2' mu', exists U2 : block -> Z -> bool,
  (effstep_plus rtl_eff_sem tge U2 st2 m2 st2' m2' \/
      effstep_star rtl_eff_sem tge U2 st2 m2 st2' m2' (*/\ lt_state st1' st1*))
 /\ intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m2 /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  (*MATCH st1' mu' st1' m1' st2' m2' /\ *)
     (forall (b : block) (ofs : Z),
      U2 b ofs = true ->
      Mem.valid_block m2 b /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1)%Z = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
(*New script*)
intros st1 m1 st1' m1' U1 ge' CS. intros. 
eexists. exists m2, mu, EmptyEffect.
split.
right.






intros st1 m1 st1' m1' U1 ge'. CS.

induction CS; intros; eexists. (*12 Cases*)

(*Case: skip seq*)
exists m2, mu. 
exists EmptyEffect.
split.
right.
unfold vis in UHyp.
unfold effstep_star; exists O; simpl.
reflexivity.

split. 
apply intern_incr_refl.

split.
apply sm_inject_separated_same_sminj.

split.
Lemma sm_locally_allocated_refl: forall mu m1 m2, sm_locally_allocated mu mu m1 m2 m1 m2.
Admitted.
apply sm_locally_allocated_refl.
intros. unfold EmptyEffect in H0.
contradict H0; auto.

(*Case: skip block*)
exists m2, mu.
exists EmptyEffect. (*This should change*)
split. 
right.
unfold effstep_star; exists O; simpl.
reflexivity.

split.
apply intern_incr_refl.

split.
apply sm_inject_separated_same_sminj.

split.
apply sm_locally_allocated_refl.

intros. unfold EmptyEffect in H1.
contradict H1; auto.

(*Case: skip return*)
exists m2, mu.
exists EmptyEffect. (*This should change*)
split. 
right.
unfold effstep_star; exists O; simpl.
reflexivity.

split.
apply intern_incr_refl.

split.
apply sm_inject_separated_same_sminj.

split.
apply sm_locally_allocated_refl.

intros. unfold EmptyEffect in H2.
contradict H2; auto.

(*assign*)

exists m2, mu.

exists EmptyEffect. (*This should change*)
split. 
right.
unfold effstep_star. exists O. simpl.
reflexivity.

split.
apply intern_incr_refl.

split.
apply sm_inject_separated_same_sminj.


split. admit.

intros. unfold EmptyEffect in H2.
contradict H2; auto.




split_allsplit.

eexists.
eexists.
eexists.
eexists.
eexists.
split. (* effste*)
unfold effstep_plus.
unfold effstep_star.
(*Lemma about effstepN.*)

Focus 2. split.
(*intern_incr
unfold intern_incr.*)

Focus 2. split.
unfold sm_inject_separated.

Focus 2. split.
unfold sm_locally_allocated.
