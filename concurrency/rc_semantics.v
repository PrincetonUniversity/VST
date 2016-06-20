Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import Axioms.

Require Import concurrency.compcert_imports. Import CompcertCommon.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.arguments.
Require Import sepcomp.structured_injections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Reach-Closed Semantics *)

(** Reach-closed semantics extend effect semantics by tracking 
- the arguments passed to initial_core at initialization; 
- the list of values returned to the core at inter. points;
- the set of blocks allocated by this coe, together
  with blocks reachable at previous interaction points. *)
(** The blocks are tracked in new local state called [locs], 
    attached to the core states of the underlying semantics. *)

(** We say that the /reachable set/ of a reach-closed configuration [(c,locs),
     m] in global env. [ge] is [REACH m (globalBlocks ge \cup locs)].  RC
     semantics are /reach closed/ in the sense that whenever [effstep rcsem ge U
     (c,locs) m (c',locs\cup freshlocs m m') m'] then [U] is a subset of the
     reachable set of [(c,locs),m].  That is, a reach-closed core only writes to
     blocks that it allocated or which were revealed to it by interaction at an
     external call point. *)

Module RC. Section rc.

Variables F V C : Type.

Variable sem : @EffectSem (Genv.t F V) C.

(** ** Reach-closed States *)

Record state : Type := 
  mk { core :> C
     ; locs : block -> bool }.

Definition updC (c : C) (st : state) :=
  match st with
    | mk _ locs => mk c locs 
  end.

Definition upd_locs locs (st : state) :=
  match st with
    | mk c _ => mk c locs 
  end.

Definition initial_core ge v vs := 
  match initial_core sem ge v vs with
    | Some c => Some (mk c (getBlocks vs))
    | None => None
  end.

Lemma initial_core_locs ge v vs c : 
  initial_core ge v vs = Some c -> 
  locs c = getBlocks vs.
Proof.
unfold initial_core.
case_eq (semantics.initial_core sem ge v vs).
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
        | Some v => Some (mk c' (fun b => getBlocks (v::nil) b || locs c b))
        | None => Some (mk c' (locs c))
      end
    | None => None
  end.

Definition halted c := 
  match halted sem (core c) with
    | Some rv => if vals_def (rv::nil) then Some rv else None
    | None => None
  end.

Arguments halted /.

Definition roots F V (ge : Genv.t F V) (c : state) := 
  fun b => isGlobalBlock ge b || locs c b.

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

(** ** Reach-Closed Step Relation *)

Definition effstep ge U c m c' m' :=
  effstep sem ge U (core c) m (core c') m' 
  /\ (forall b ofs, U b ofs=true -> reach_set ge c m b=true)
  /\ locs c' = REACH m' (fun b => freshloc m m' b || reach_set ge c m b).

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
unfold after_external; case (semantics.after_external _ _).
intros ?; inversion 1; subst; unfold roots; simpl.
extensionality b.
rewrite (orb_assoc (getBlocks (v :: nil) b)).
symmetry.
rewrite (orb_comm (getBlocks (v :: nil) b)).
rewrite (orb_assoc (isGlobalBlock ge b)); auto.
inversion 1.
Qed.

(** ** Reach-Closed Interaction Semantics *)
  
Program Definition coresem : CoreSemantics (Genv.t F V) state mem :=
  Build_CoreSemantics _ _ _
    initial_core
    at_external
    after_external
    halted
    corestep _ _ _.
Next Obligation. 
destruct (effax1 H0) as [X Y].
case_eq (semantics.at_external sem q); auto; intros [[ef dep_sig] args] H5.
destruct (vals_def args); auto.
apply corestep_not_at_external in X; rewrite X in H5; congruence.
Qed.
Next Obligation. 
destruct (effax1 H0) as [X Y].
case_eq (semantics.halted sem q). intros v.
apply corestep_not_halted in X. rewrite X; inversion 1.
auto.
Qed.
Next Obligation. 
case_eq (at_external_halted_excl sem (core q)); auto; intros e _. 
case_eq (semantics.at_external sem q); auto; intros [[ef dep_sig] args] H5.
destruct (vals_def args); auto.
rewrite e in H5; congruence.
rewrite e; auto.
Qed.

Program Definition memsem : MemSem (Genv.t F V) state :=
  Build_MemSem _ _ coresem _.
Next Obligation. 
destruct (effax1 H) as [X Y].
revert X; apply corestep_mem. 
Qed.

(** ** Reach-Closed Effect Semantics *)

Lemma my_effax1 M ge c m c' m' :
  effstep ge M c m c' m' ->
  corestep ge c m c' m'  
  /\ Mem.unchanged_on (fun b ofs => M b ofs = false) m m'.
Proof.
destruct 1 as [H [H2 H3]]; split.
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
destruct 1 as [H [H2 H3]].
intros b ofs. eapply effstep_valid; eauto.
Qed.

Lemma my_effstep_perm :
  forall (M : block -> Z -> bool) 
         ge c (m : mem) c' (m' : mem),
    effstep ge M c m c' m' ->
    forall (b : block) (z : Z),
      M b z = true -> Mem.perm m b z Cur Writable.
Proof.
  intros until m'.
  destruct 1 as [H [H1 H2]].
  eapply effstep_perm; eauto.
Qed.  

Definition effsem : @EffectSem (Genv.t F V) state :=
  Build_EffectSem _ _ memsem effstep my_effax1 my_effax2 my_effstep_perm.

End rc. End RC.

Module RCSem. Section RCSem.
          
Variables F V C : Type.

Variable sem : @EffectSem (Genv.t F V) C.

Variable ge : Genv.t F V.

Let rcsem := RC.effsem sem.
      
Record t : Type := {
  I : C -> mem -> (block -> bool) -> Prop

; init_ax : 
  forall v vs c m,
  initial_core sem ge v vs = Some c -> 
  I c m (getBlocks vs)

; step_ax : 
  forall c m c' m' B,
  I c m B -> 
  corestep sem ge c m c' m' ->
  let B'  := REACH m' (fun b => freshloc m m' b || RC.reach_set ge (RC.mk c B) m b) in
  let c'' := RC.mk c' B' in corestep rcsem ge (RC.mk c B) m c'' m' /\ I c' m' B'

; atext_ax :
  forall c m B ef sg vs,
  I c B m -> 
  at_external sem c = Some (ef,sg,vs) ->
  vals_def vs = true

; aftext_ax :
  forall c m B ef sg vs ov c' m',
  I c m B ->
  at_external sem c = Some (ef,sg,vs) -> 
  after_external sem ov c = Some c' -> 
  I c' m' (fun b => match ov with None => B b
                      | Some v => getBlocks (v::nil) b || B b
                    end)

; halted_ax : 
  forall c m B v,
  I c m B -> 
  halted sem c = Some v -> 
  vals_def (v :: nil) = true
}.

End RCSem. End RCSem.
