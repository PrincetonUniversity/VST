Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import msl.Axioms.

Require Import compcert. Import CompcertCommon.

Require Import linking.sepcomp. Import SepComp.
Require Import sepcomp.arguments.

Require Import linking.core_semantics_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Reach-closed semantics extend effect semantics w/:                       *)
(*   1) args: the arguments passed to initial_core at initialization        *)
(*   2) rets: the list of values returned to the core at inter. points      *)
(*   3) locs: the set of blocks allocated by this core, together            *)
(*            with blocks leaked by the environment at previous             *)
(*            interaction points                                            *)
(*                                                                          *)
(* We say that the /reachable set/ of a reach-closed configuration          *)
(*   <(c,args,rets,locs), m>                                                *)
(* in global env. ge is                                                     *)
(*   REACH m                                                                *)
(*     (globalBlocks ge                                                     *)
(*     \cup blocksOf args                                                   *)
(*     \cup blocksOf rets                                                   *)
(*     \cup locs)                                                           *)
(*                                                                          *)
(* RC semantics are /reach closed/ in the sense that whenever               *)
(*   effstep rcsem ge U (c,args,rets,locs) m                                *)
(*                      (c',args,rets,locs\cup freshlocs m m') m'           *)
(* then                                                                     *)
(*   U is a subset of the reachable set of <(c,args,rets,locs),m>.          *)
(*                                                                          *)
(* That is, a reach-closed core only writes to blocks that it               *)
(* allocated or which were revealed to it by interaction at an external     *)
(* call point.                                                              *)

Module RC. Section rc.

Variables F V C : Type.

Variable sem : @EffectSem (Genv.t F V) C.

Record state : Type := 
  mk { core :> C
     ; args : list val
     ; rets : list val
     ; locs : block -> bool }.

Definition updC (c : C) (st : state) :=
  match st with
    | mk _ args rets locs => mk c args rets locs 
  end.

Definition upd_locs locs (st : state) :=
  match st with
    | mk c args rets _ => mk c args rets locs 
  end.

Definition initial_core ge v vs := 
  match initial_core sem ge v vs with
    | Some c => Some (mk c vs nil (fun _ => false))
    | None => None
  end.

Lemma initial_core_args ge v vs c : 
  initial_core ge v vs = Some c -> 
  args c = vs.
Proof.
unfold initial_core.
case_eq (core_semantics.initial_core sem ge v vs).
solve[intros c0 H; inversion 1; subst; simpl; auto].
solve[intros _; inversion 1].
Qed.

Lemma initial_core_rets ge v vs c : 
  initial_core ge v vs = Some c -> 
  rets c = nil.
Proof.
unfold initial_core.
case_eq (core_semantics.initial_core sem ge v vs).
solve[intros c0 H; inversion 1; subst; simpl; auto].
solve[intros _; inversion 1].
Qed.

Lemma initial_core_locs ge v vs c : 
  initial_core ge v vs = Some c -> 
  locs c = (fun _ : block => false).
Proof.
unfold initial_core.
case_eq (core_semantics.initial_core sem ge v vs).
solve[intros c0 H; inversion 1; subst; simpl; auto].
solve[intros _; inversion 1].
Qed.

Definition at_external c := 
  match at_external sem (core c) with
    | None => None 
    | Some (ef,dep_sig,args) => 
      if vals_def args then Some (ef,dep_sig,args) else None
  end.

Arguments at_external /.

Definition after_external ov c :=
  match after_external sem ov (core c) with
    | Some c' => 
      match ov with 
        | Some v => Some (mk c' (args c) (v :: rets c) (locs c))
        | None => Some (mk c' (args c) (rets c) (locs c))
      end
    | None => None
  end.

Definition halted c := halted sem (core c).

Arguments halted /.

Definition roots F V (ge : Genv.t F V) (c : state) := 
  fun b => isGlobalBlock ge b
        || getBlocks (args c) b
        || getBlocks (rets c) b
        || locs c b.

Lemma roots_domains_eq 
    F1 F2 V1 V2 (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2) c b : 
  genvs_domain_eq ge1 ge2 -> 
  roots ge1 c b=true -> 
  roots ge2 c b=true.
Proof.
unfold roots; intros A.
case_eq (isGlobalBlock ge2 b); simpl; auto.
intros B. cut (isGlobalBlock ge1 b=false). intros ->; auto.
erewrite genvs_domain_eq_isGlobal; eauto.
Qed.

Definition reach_set (ge : Genv.t F V) (c : state) (m : mem) := 
  REACH m (roots ge c).

Definition effstep ge U c m c' m' :=
  effstep sem ge U (core c) m (core c') m' 
  /\ (forall b ofs, U b ofs=true -> reach_set ge c m b=true)
  /\ args c'=args c
  /\ rets c'=rets c
  /\ locs c' = fun b => locs c b 
                     || StructuredInjections.freshloc m m' b
                     || reach_set ge c m b.

Arguments effstep /.

Definition corestep ge c m c' m' := 
  exists U, effstep ge U c m c' m'.

Arguments corestep /.

Lemma getBlocks_app l1 l2 : 
  getBlocks (l1 ++ l2) 
  = fun b => getBlocks l1 b || getBlocks l2 b.
Proof.
induction l1; simpl; auto.
extensionality b.
do 2 rewrite getBlocksD.
destruct a; try solve[rewrite IHl1; auto].
rewrite IHl1; auto.
rewrite orb_assoc; auto.
Qed.

Lemma after_external_rc_basis (ge : Genv.t F V) v (c c' : state) :
  after_external (Some v) c = Some c' -> 
  roots ge c' = (fun b => getBlocks (v :: nil) b || roots ge c b).
Proof.
unfold after_external; case (core_semantics.after_external _ _).
intros ?; inversion 1; subst; unfold roots; simpl.
extensionality b.
rewrite <-(orb_comm (getBlocks (v :: rets c) b)).
symmetry.
rewrite <-(orb_assoc (isGlobalBlock ge b)).
rewrite (orb_comm (isGlobalBlock ge b)).
rewrite (orb_comm (getBlocks (args c) b)).
rewrite <-(orb_assoc (getBlocks (rets c) b)).
rewrite <-(orb_assoc (getBlocks (rets c) b)).
rewrite <-orb_assoc.
rewrite orb_assoc.
change
   ((fun b => getBlocks (v :: nil) b || getBlocks (rets c) b) b
   || (getBlocks (args c) b || (isGlobalBlock ge b || locs c b)) =
   getBlocks (v :: rets c) b || (isGlobalBlock ge b || getBlocks (args c) b)
   || locs c b).
rewrite <-getBlocks_app; simpl.
rewrite <-orb_assoc.
symmetry.
rewrite (orb_comm (isGlobalBlock ge b)).
rewrite <-orb_assoc; auto.
inversion 1.
Qed.
  
Program Definition coresem : CoreSemantics (Genv.t F V) state mem :=
  Build_CoreSemantics _ _ _
    initial_core
    at_external
    after_external
    halted
    corestep _ _ _.
Next Obligation. 
destruct (effax1 H0) as [X Y].
case_eq (core_semantics.at_external sem q); auto; intros [[ef dep_sig] args] H5.
destruct (vals_def args); auto.
apply corestep_not_at_external in X; rewrite X in H5; congruence.
Qed.
Next Obligation. 
destruct (effax1 H0) as [X Y].
revert X; apply corestep_not_halted; auto.
Qed.
Next Obligation. 
case_eq (at_external_halted_excl sem (core q)); auto; intros e _. 
case_eq (core_semantics.at_external sem q); auto; intros [[ef dep_sig] args] H5.
destruct (vals_def args); auto.
rewrite e in H5; congruence.
Qed.

Program Definition coopsem : CoopCoreSem (Genv.t F V) state :=
  Build_CoopCoreSem _ _ coresem _.
Next Obligation. 
destruct (effax1 H) as [X Y].
revert X; apply corestep_fwd. 
Qed.

Lemma my_effax1 M ge c m c' m' :
  effstep ge M c m c' m' ->
  corestep ge c m c' m'  
  /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
Proof.
destruct 1 as [H [H2 [H3 [H4 H5]]]]; split.
exists M; split; auto.
apply effax1 in H. destruct H; auto.
Qed.

Lemma my_effax2 ge c m c' m' :
  corestep ge c m c' m' -> 
  exists M, effstep ge M c m c' m'.
Proof. destruct 1 as [M ?]; exists M; auto. Qed.

Lemma my_effstep_valid M ge c m c' m' :
  effstep ge M c m c' m' ->
  forall b z, M b z = true -> Mem.valid_block m b.
Proof.
destruct 1 as [H [H2 [H3 [H4 H5]]]].
intros b ofs. eapply effstep_valid; eauto.
Qed.

Definition effsem : @Effsem.t (Genv.t F V) state := 
  Effsem.Build_t _ _ coopsem effstep my_effax1 my_effax2 my_effstep_valid.

End rc. End RC.
