Require Import compcert. Import CompcertAll.

Require Import core_semantics.
Require Import core_semantics_lemmas.
Require Import mem_wd.
Require Import mem_lemmas.
Require Import reach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition oval_valid (ov : option val) (m : mem) :=
  match ov with
    | None => True
    | Some v => val_valid v m
  end.

Lemma valid_genv_isGlobal F V (ge : Genv.t F V) m b : 
  valid_genv ge m -> 
  isGlobalBlock ge b=true -> 
  Mem.valid_block m b.
Proof.
intros H H2.
apply H; auto.
Qed.

Lemma mem_wd_reach m : 
  mem_wd m -> 
  forall b, 
  REACH m (fun b => valid_block_dec m b) b=true -> 
  Mem.valid_block m b.
Proof. 
intros H b H2.
rewrite REACHAX in H2.
destruct H2 as [L H3].
revert b H3; induction L; simpl.
intros b; inversion 1; subst.
revert H0; case_eq (valid_block_dec m b); auto.
intros. inversion H1.
intros b; inversion 1; subst.
specialize (IHL b' H2).
assert (A: Mem.flat_inj (Mem.nextblock m) b' = Some (b',0)).
{ unfold Mem.flat_inj.
  case_eq (plt b' (Mem.nextblock m)); intros p _; auto.
  elimtype False; apply p; apply IHL. }
destruct H; specialize (mi_memval _ _ _ _ A H4).
rewrite H6 in mi_memval; inversion mi_memval; subst.
revert H1; unfold Mem.flat_inj.
case_eq (plt b (Mem.nextblock m)); auto.
intros p _; inversion 1.
Qed.

Lemma mem_wd_reach_globargs F V (ge : Genv.t F V) vs m : 
  mem_wd m -> 
  Forall (fun v => val_valid v m) vs -> 
  valid_genv ge m -> 
  forall b, 
    REACH m (fun b => 
      (isGlobalBlock ge b || getBlocks vs b)) b=true -> 
    Mem.valid_block m b.
Proof. 
intros H H1 H2 b H3.
rewrite REACHAX in H3.
destruct H3 as [L H3].
revert b H3; induction L; simpl.
intros b; inversion 1; subst.
rewrite orb_true_iff in H0.
destruct H0.
eapply valid_genv_isGlobal; eauto.
rewrite getBlocks_char in H0.
destruct H0.
clear - H1 H0.
induction vs. inversion H0.
inversion H1; subst. 
inversion H0; subst.
apply H3. apply IHvs; auto. 
intros b; inversion 1; subst.
specialize (IHL b' H5).
destruct H.
assert (A: Mem.flat_inj (Mem.nextblock m) b' = Some (b',0)).
{ unfold Mem.flat_inj.
  case_eq (plt b' (Mem.nextblock m)); intros p _; auto.
  elimtype False; apply p; apply IHL. }
specialize (mi_memval _ _ _ _ A H6).
rewrite H8 in mi_memval.
inversion mi_memval; subst.
unfold Mem.flat_inj in H4.
generalize H4.
case_eq (plt b (Mem.nextblock m)); auto.
intros p _; inversion 1.
Qed.

Module Nuke_sem. Section nucular_semantics.

Variable F V C : Type.

Variable csem : CoreSemantics (Genv.t F V) C mem.

(* A "nucular" semantics is a core semantics that preserves the "WMD"
   property as an execution invariant. "WMD m" (formally, [mem_wd m],
   but the former is easier to say) asserts that the memory [m]
   contains no invalid pointers. An invalid pointer [Vptr b ofs] is one
   for which b is an invalid block in [m]. *)

Record t : Type :=
{ (* An invariant on core states and memories, instantiatable by the 
     person proving that [csem] is a nucular semantics. *) 
I : C -> mem -> Prop

(* It should be possible to establish the invariant initially, assuming
   valid arguments, a valid global environment, and a valid initial 
   memory. *) 
; wmd_initial : 
    forall ge m v args c,
    Forall (fun v => val_valid v m) args -> 
    valid_genv ge m -> 
    mem_wd m -> 
    initial_core csem ge v args = Some c -> 
    I c m

(* Coresteps preserve the invariant. *) 
; wmd_corestep : 
    forall ge c m c' m',
    corestep csem ge c m c' m' -> 
    valid_genv ge m ->
    I c m -> 
    I c' m'

(* When at_external, the arguments and memory passed to the environment
   must both be valid. *) 
; wmd_at_external :
    forall (ge : Genv.t F V) c m ef dep_sig args,
    I c m -> 
    at_external csem c = Some (ef,dep_sig,args) -> 
    Forall (fun v => val_valid v m) args /\ mem_wd m

(* It's possible to reestablish the invariant when external calls return, 
   assuming that we're passed a valid return memory in the fwd relation 
   w/r/t m, and we're passed a valid return value. *) 
; wmd_after_external :
    forall c m ov c' m',
    I c m -> 
    after_external csem ov c = Some c' -> 
    oval_valid ov m' -> 
    mem_forward m m' -> 
    mem_wd m' -> 
    I c' m' 

(* We halt with a valid return value and valid memory. *)
; wmd_halted : 
    forall c m v,
    I c m -> 
    halted csem c = Some v -> 
    val_valid v m /\ mem_wd m }.

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
intros H fwd. inv H; constructor; intros.
{ cut (val_valid (Vptr b Int.zero) m). 
+ intros H2; apply (val_valid_fwd H2 fwd).
+ eauto. }
{ cut (val_valid (Vptr b Int.zero) m). 
+ intros H2; apply (val_valid_fwd H2 fwd).
+ eauto. }
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

Variable nuke : t csem.

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

End Nuke_sem.