Require Import compcert.lib.Axioms.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.

Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.extspec.
Require Import sepcomp.mem_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Event.

Record t : Type := 
  mk { pre_mem  : mem
     ; post_mem : mem
     ; args : list val
     ; rv   : option val }.

End Event.

Module TraceSemantics. Section trace_semantics.

Context {G C Z : Type}.

Variable z_init : Z.
Variable sem : @CoopCoreSem G C.
Variable spec : ext_spec Z.

Definition yielded c :=
  exists ef sig args, at_external sem c = Some (ef, sig, args) 
  \/ exists rv, halted sem c = Some rv.

Inductive step : G -> (Z*list Event.t*C) -> mem -> (Z*list Event.t*C) -> mem -> Prop :=
| trace_step :
  forall ge tr z c m c' m',
  corestep_plus sem ge c m c' m' -> 
  yielded c' -> 
  step ge (z,tr,c) m (z,tr,c') m'
| trace_extern : 
  forall ge tr z c m z' c' m' ef sig args rv x,
  at_external sem c = Some (ef, sig, args) -> 
  Mem.unchanged_on (fun b ofs => REACH m (getBlocks args) b=false) m m' ->   
  mem_forward m m' -> 
  ext_spec_pre spec ef x (sig_args sig) args z m -> 
  ext_spec_post spec ef x (sig_res sig) (Some rv) z' m' -> 
  after_external sem (Some rv) c = Some c' -> 
  step ge (z,tr,c) m (z',Event.mk m m' args (Some rv) :: tr,c') m'.

Definition initial_core (ge : G) (v : val) (vs : list val) 
  : option (Z*list Event.t*C) := 
  match initial_core sem ge v vs with 
    | Some c => Some (z_init, nil, c)
    | None => None
  end.

Definition halted (c : Z*list Event.t*C) := halted sem (snd c).

Program Definition coresem : CoreSemantics G (Z*list Event.t*C) mem :=
  @Build_CoreSemantics G (Z*list Event.t*C) mem 
  initial_core
  (fun _ => None)
  (fun _ _ => None)
  halted 
  step
  _ _ _ _.
Next Obligation.
destruct H.
destruct H as [n H].
hnf in H.
destruct H as [c2 [m2 [H1 H2]]].
apply corestep_not_halted in H1.
unfold halted.
solve[auto].
solve[destruct (at_external_halted_excl sem c1); try congruence; auto].
Qed.

Program Definition coopsem : CoopCoreSem G (Z*list Event.t*C) :=
  @Build_CoopCoreSem G (Z*list Event.t*C) coresem _.
Next Obligation.
destruct CS; auto.
destruct H as [n H].
hnf in H.
destruct H as [c2 [m2 [H1 H2]]].
apply corestep_fwd in H1.
apply corestepN_fwd in H2.
solve[eapply mem_forward_trans; eauto].
Qed.

End trace_semantics. End TraceSemantics.
