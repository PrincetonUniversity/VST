Require Import sepcomp.compcert. Import CompcertAll.

Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.mem_wd.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.reach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition oval_valid (ov : option val) (m : mem) :=
  match ov with
    | None => True
    | Some v => val_valid v m
  end.

Module Nuke. Section nucular_semantics.

Variable F V C : Type.

Variable csem : CoreSemantics (Genv.t F V) C mem.

Record nucular_semantics : Type :=
{ I : C -> mem -> Prop

; wmd_initial : 
    forall ge m v args c,
    valid_genv ge m -> 
    mem_wd m -> 
    initial_core csem ge v args = Some c -> 
    I c m

; wmd_corestep : 
    forall ge c m c' m',
    corestep csem ge c m c' m' -> 
    valid_genv ge m ->
    I c m -> 
    I c' m'

; wmd_at_external :
    forall (ge : Genv.t F V) c m ef dep_sig args,
    I c m -> 
    at_external csem c = Some (ef,dep_sig,args) -> 
    let reach_set := REACH m (fun b => 
      (isGlobalBlock ge b || getBlocks args b)) in 
    (*THIS condition is probably derivable from the next one:*)
    (forall b, reach_set b=true -> Mem.valid_block m b) 
    /\ mem_wd m

; wmd_after_external :
    forall c m ov c' m',
    I c m -> 
    after_external csem ov c = Some c' -> 
    oval_valid ov m' -> 
    mem_forward m m' -> 
    I c' m' 

; wmd_halted : 
    forall c m v,
    I c m -> 
    halted csem c = Some v -> 
    val_valid v m }.

End nucular_semantics.

Lemma val_valid_fwd v m m' : 
  val_valid v m -> 
  mem_forward m m' -> 
  val_valid v m'.
Proof. solve[destruct v; auto; simpl; intros H H2; apply H2; auto]. Qed.

Lemma valid_genv_fwd F V (ge : Genv.t F V) m m' :
  valid_genv ge m -> 
  mem_forward m m' -> 
  valid_genv ge m'.
Proof.
intros H fwd id b fnd.
cut (val_valid (Vptr b Int.zero) m). 
+ intros H2; apply (val_valid_fwd H2 fwd).
+ specialize (H id b fnd); auto.
Qed.

Lemma valid_genv_step F V C (ge : Genv.t F V) 
    (csem : CoopCoreSem (Genv.t F V) C) c m c' m' : 
  valid_genv ge m -> 
  corestep csem ge c m c' m' -> 
  valid_genv ge m'.
Proof.
intros H step; apply corestep_fwd in step; eapply valid_genv_fwd; eauto.
Qed.

Lemma valid_genv_stepN F V C (ge : Genv.t F V) 
    (csem : CoopCoreSem (Genv.t F V) C) c m c' m' n : 
  valid_genv ge m -> 
  corestepN csem ge n c m c' m' -> 
  valid_genv ge m'.
Proof.
intros H stepn; apply corestepN_fwd in stepn; eapply valid_genv_fwd; eauto.
Qed.

Section nucular_semantics_lemmas.

Variable F V C : Type.

Variable csem : CoopCoreSem (Genv.t F V) C.

Variable nuke : nucular_semantics csem.

Variable ge : Genv.t F V.

Lemma nucular_stepN c m (H : nuke.(I) c m) c' m' n : 
  valid_genv ge m -> 
  corestepN csem ge n c m c' m' -> 
  nuke.(I) c' m'.
Proof.
revert c m H; induction n; simpl.
solve[intros ? ? ? ?; inversion 1; subst; auto].
intros c m H H2 [c2 [m2 [H3 H4]]].
apply (IHn c2 m2); auto.
solve[eapply wmd_corestep in H3; eauto].
solve[apply (valid_genv_step H2 H3)].
Qed.

End nucular_semantics_lemmas. 

End Nuke.