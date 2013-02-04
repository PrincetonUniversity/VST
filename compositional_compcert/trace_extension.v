Load loadpath.
Require Import compositional_compcert.core_semantics.
Require Import compositional_compcert.forward_simulations.
Require Import compositional_compcert.rg_forward_simulations.
Require Import compositional_compcert.step_lemmas.
Require Import compositional_compcert.extspec.
Require Import compositional_compcert.extension.
Require Import compositional_compcert.extension_simulations.
Require Import compositional_compcert.extension_proof.
Require Import compositional_compcert.Coqlib2.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Coqlib.

Set Implicit Arguments.

Section CompCertExecution.
Context {G C M D Z:Type}.
Context (Hcore:CoreSemantics G C M D).
Variable (Hspec:external_specification M external_function Z).

Variable ge : G.

Inductive compcert_stepN: nat -> Z -> C -> M -> Z -> C -> M -> Prop :=
| compcert_step0: forall z c m, compcert_stepN 0 z c m z c m
| compcert_step_core: forall n z c m c'' m'' z' c' m',
   corestep Hcore ge c m c'' m'' -> 
   compcert_stepN n z c'' m'' z' c' m' -> 
   compcert_stepN (S n) z c m z' c' m'
| compcert_step_external: forall n z c m z'' c'' m'' z' c' m' ef sig args ret x,
   at_external Hcore c = Some (ef, sig, args) -> 
   ext_spec_pre Hspec ef x (sig_args sig) args z m ->
   after_external Hcore ret c = Some c'' -> 
   ext_spec_post Hspec ef x (sig_res sig) ret z'' m'' -> 
   compcert_stepN n z c'' m'' z' c' m' -> 
   compcert_stepN (S n) z c m z' c' m'.
  
End CompCertExecution.

Section TraceExtension.
 Variables (fT vT cT dT Z: Type) (initial_z: Z)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT) (csig: ef_ext_spec mem Z).

 Local Open Scope nat_scope.

 Definition cores := @const nat _ csemT.

 Inductive trace_corestate: Type := 
  mkTraceCoreState: forall (z: Z) (c: cT) (tr: trace), trace_corestate.

 Definition z_of (s: trace_corestate) :=
  match s with mkTraceCoreState z _ _ => z end.

 Definition core_of (s: trace_corestate) :=
  match s with mkTraceCoreState _ c _ => c end.

 Definition trace_of (s: trace_corestate) :=
  match s with mkTraceCoreState _ _ tr => tr end.

 Definition trace_initial_mem := initial_mem csemT.

 Definition trace_make_initial_core ge v args := 
  match make_initial_core csemT ge v args with
  | Some c => Some (mkTraceCoreState initial_z c nil)
  | None => None 
  end. 

 Definition trace_at_external (s: trace_corestate):
  option (external_function * signature * list val) := None.

 Definition trace_after_external (rv: option val) (s: trace_corestate): 
  option trace_corestate := None.

 Definition trace_safely_halted (s: trace_corestate) :=
  safely_halted csemT (core_of s).

 Definition ef_id (ef: external_function): option ident :=
  match ef with 
  | EF_external id _ => Some id
  | EF_builtin id _ => Some id
  | EF_inline_asm id => Some id 
  | _ => None
  end. 

 Inductive trace_corestep: Genv.t fT vT -> 
  trace_corestate -> mem -> trace_corestate -> mem -> Prop :=
 | trace_corestep_step: forall ge z c tr m c' m',
    corestep csemT ge c m c' m' -> 
    trace_corestep ge (mkTraceCoreState z c tr) m (mkTraceCoreState z c' tr) m'
 (*NOTE: probably also need to handle external functions with void return type here*)
 | trace_corestep_external: forall ge z c m tr z' c' m' ef sig args evargs ret evret tyret x id,
    at_external csemT c = Some (ef, sig, args) -> 
    ext_spec_pre csig ef x (sig_args (ef_sig ef)) args z m ->
    eventval_list_match ge evargs (sig_args (ef_sig ef)) args -> 
    after_external csemT (Some ret) c = Some c' -> 
    ext_spec_post csig ef x (sig_res sig) (Some ret) z' m' -> 
    sig_res sig = Some tyret -> 
    eventval_match ge evret tyret ret -> 
    ef_id ef = Some id -> 
    trace_corestep ge 
     (mkTraceCoreState z c tr) m 
     (mkTraceCoreState z' c' (Event_syscall id evargs evret :: tr)) m' .

 Program Definition trace_core_semantics :=
  Build_CoreSemantics _ _ _ _
   trace_initial_mem
   trace_make_initial_core
   trace_at_external
   trace_after_external
   trace_safely_halted
   trace_corestep 
   _ _ _ _.
 Next Obligation.
 inv H; unfold trace_safely_halted; simpl.
 solve[apply corestep_not_halted in H0; auto].
 exploit (@at_external_halted_excl (Genv.t fT vT)); intros.
 destruct H; eauto.
 solve[rewrite H in H0; congruence].
 Qed.

 Definition proj_core (i: nat) (s: trace_corestate): option cT := 
  if eq_nat_dec i 0 then Some (core_of s) else None.
 Definition active := fun _:trace_corestate => 0.
 Definition runnable := fun (s: trace_corestate) => 
  match at_external csemT (core_of s), safely_halted csemT (core_of s) with 
  | None, None => true
  | _, _ => false
  end.
 Definition proj_zint := z_of.
 Definition proj_zext := fun z: Z => tt.
 Definition zmult := fun (z: Z) (_:unit) => z.

 Definition handled (ef: external_function) := 
  forall s c sig args,
  proj_core (active s) s = Some c -> 
  at_external csemT c = Some (ef, sig, args) -> 
  trace_at_external s = None.

 Variable empty_sig: ef_ext_spec mem unit. (*TODO*)
 Variable linkable_empty_csig: linkable proj_zext handled csig empty_sig.

 Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.

 Obligation Tactic := 
  autounfold with null_unfold; intros; 
   try solve [eexists; eauto|congruence].

 Program Definition trace_extension := @Extension.Make _ _ _ _ _ _ _
  trace_core_semantics empty_sig 
  (@const nat _ (Genv.t fT vT)) (@const nat _ dT)  (@const nat _ cT)
  cores csig (const 1) proj_core _ active _ proj_zint proj_zext zmult 
  _ _ _ _.
 Next Obligation. 
  if_tac; auto. rewrite H0 in H. unfold const in *. elimtype False; omega. 
 Qed.
 Next Obligation. 
  if_tac; exists (core_of s); auto. 
  elimtype False; apply H; auto. 
 Qed.
 Next Obligation. destruct zext; auto. Qed.
 Next Obligation. simpl in *; unfold trace_after_external in *; congruence. Qed.
 Next Obligation.
  apply linkable_empty_csig.
 Qed.

End TraceExtension.
