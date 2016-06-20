(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import pos.
Require Import rc_semantics.
Require Import nucular_semantics.
Require Import compcert_linking. Import Modsem.
Require Import simulations. Import SM_simulation.
Require Import semantics_lemmas.

(** The (deterministic) context [C]. Assumptions on [C] are: 
- [sim_C]: C self-simulates ([C <= C]) (cf. Definition 2, pg. 10). 
- [det_C]: C is deterministic (cf. Definition 2, pg. 10). This is true,
      e.g., of all Clight and assembly contexts. 
- [rclosed_C] restricts to reach-closed contexts (cf. linking/rc_semantics.v).
- [nuke_C] restricts contexts to those that store only valid blocks.  This is
      footnote 5 on pg. 9 of the paper (one reviewer suggested we describe this
      condition in a bit more detail in the paper; we tend to agree and plan to
      do so in the final version). It turns out that this condition holds of all
      assembly contexts; see backend/Asm_nucular.v for the proof. 
- [domeq_C]: The global environment attached to the [C] module semantics 
      has the same domain (set of blocks marked "global") as [ge_top]. *)

Module Ctx. 
Record t (ge_top : ge_ty) : Type := {
    C : Modsem.t
  ; sim_C : SM_simulation_inject C.(sem) C.(sem) C.(ge) C.(ge)
  ; rclosed_C : RCSem.t (sem C) (ge C)
  ; valid_C : Nuke_sem.t (sem C)
  ; det_C : corestep_fun (sem C)
  ; domeq_C : genvs_domain_eq ge_top (ge C)
  ; symbols_up_C: forall id b,
     Genv.find_symbol (ge C) id = Some b ->
     Genv.find_symbol ge_top id = Some b
  ; gvars_included_C: forall b,
     gvars_included (Genv.find_var_info (ge C) b) (Genv.find_var_info ge_top b)
  }.
End Ctx.

(** Every Clight program (up to a few syntactic restrictions: no repeated function 
 definitions, function temporary id's disjoint from parameter names) is a valid 
 program context. *)

Require Import Clight.
Require Import Clight_coop.
Require Import Clight_eff.
Require Import Clight_lemmas.
Require Import Clight_self_simulates.
Require Import safe_clight_rc. 
Require Import clight_nucular. Import CLIGHT_NUKE.

Notation Clight_prog := (AST.program fundef Ctypes.type).

Definition mk_Clight_Modsem hf (p : Clight_prog) :=
  @Modsem.mk fundef Ctypes.type (Genv.globalenv p) CL_core (CL_eff_sem1 hf).

Section Clight_Ctx.
Variable is_i64_helper_empty_trace : (* The following should be provable but isn't, 
                                        due to a misspecification of i64_helpers 
                                        (they should all have empty trace)! *)
  forall F V hf ef (ge : Genv.t F V) name sg vargs m t vres m',
  I64Helpers.is_I64_helper hf name sg ->
  external_call ef ge vargs m t vres m' -> 
  t = E0.

Program Definition mk_Clight_Ctx hf (p : Clight_prog)
           (R: list_norepet (map fst (prog_defs p)))
           (DISJ: forall vf f, Genv.find_funct (Genv.globalenv p) vf = Some (Internal f) -> 
                  list_disjoint (var_names (fn_params f)) (var_names (fn_temps f)))
           (ge_top : ge_ty) (pf : genvs_domain_eq ge_top (Genv.globalenv p)) :=
  @Ctx.Build_t ge_top (mk_Clight_Modsem hf p) _ _ _ _ pf.
Next Obligation.
apply Clight_self_simulates.transl_program_correct; auto.
Qed.
Next Obligation.
apply Clight_RC.
Qed.
Next Obligation.
apply Clight_Nuke.
Qed.
Next Obligation.
intros m *; simpl; intros H H2.
eapply clight_corestep_fun in H; eauto; inv H; auto.
Qed.

End Clight_Ctx.