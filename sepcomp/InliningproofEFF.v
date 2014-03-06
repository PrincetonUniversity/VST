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

Load Santiago_tactics.

(*Definition MATCH (d:CMinSel_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.*)

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
