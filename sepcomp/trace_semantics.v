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
Require Import sepcomp.effect_safety.
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

Variable sem : @EffectSem G C.
Variable Hspec : ext_spec Z.
Variable Espec : effect_spec.

Inductive effstep : 
  G -> 
  (block -> BinNums.Z -> bool) -> 
  (list Event.t*C) -> mem -> (list Event.t*C) -> mem -> Prop :=
| trace_stepplus :
  forall ge U tr c m c' m',
  effstep_plus sem ge U c m c' m' -> 
  effstep ge U (tr,c) m (tr,c') m'
| trace_extstep : 
  forall ge U tr c m c' m' ef sig args rv,
  at_external sem c = Some (ef, sig, args) -> 
  (forall b ofs, Mem.valid_block m b -> Espec ef args m b ofs=true -> U b ofs=true) -> 
  Mem.unchanged_on (fun b ofs => U b ofs = false) m m' ->   
  mem_forward m m' -> 
  after_external sem rv c = Some c' -> 
  effstep ge U (tr,c) m (Event.mk m m' args rv :: tr,c') m'.

Definition step ge c m c' m' := exists U, effstep ge U c m c' m'.

Definition initial_core (ge : G) (v : val) (vs : list val) : option (list Event.t*C) := 
  match initial_core sem ge v vs with 
    | Some c => Some (nil, c)
    | None => None
  end.

Definition halted (c : list Event.t*C) := halted sem (snd c).

Program Definition coresem : CoreSemantics G (list Event.t*C) mem :=
  @Build_CoreSemantics G (list Event.t*C) mem 
  initial_core
  (fun _ => None)
  (fun _ _ => None)
  halted 
  step
  _ _ _ _.
Next Obligation.
destruct H.
destruct H.
destruct H as [n H].
hnf in H.
destruct H as [c2 [m2 [H1 H2]]].
apply effax1 in H1.
destruct H1 as [H1 ?].
apply corestep_not_halted in H1.
unfold halted.
solve[auto].
solve[destruct (at_external_halted_excl sem c1); try congruence; auto].
Qed.

Program Definition coopsem : CoopCoreSem G (list Event.t*C) :=
  @Build_CoopCoreSem G (list Event.t*C) coresem _.
Next Obligation.
destruct CS.
destruct H; auto.
destruct H as [n H].
hnf in H.
destruct H as [c2 [m2 [H1 H2]]].
apply effstep_fwd in H1.
apply effstepN_fwd in H2.
solve[eapply mem_forward_trans; eauto].
Qed.

Lemma effstep_sub_val : 
  forall g U V c m c' m',
  (forall b ofs, Mem.valid_block m b ->  U b ofs = true -> V b ofs = true) ->
  effstep g U c m c' m' -> effstep g V c m c' m'.
Proof.
intros.
destruct H0.
constructor.
solve[eapply effstep_plus_sub_val; eauto].
econstructor; eauto.
apply unch_on_validblock with (V := fun b ofs => U b ofs=false); auto.
intros.
case_eq (U b ofs); auto.
intros A.
generalize (H _ _ H5 A); congruence.
Qed.

Program Definition effsem : @EffectSem G (list Event.t*C) :=
  @Build_EffectSem G (list Event.t*C) coopsem effstep _ _ effstep_sub_val.
Next Obligation.
destruct H.
split; auto.
exists U.
constructor; auto.
destruct H as [n H].
solve[apply effstepN_unchanged in H; auto].
constructor; auto.
exists U.
solve[eapply trace_extstep; eauto].
Qed.

End trace_semantics. End TraceSemantics.
