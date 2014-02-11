Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import compcert. Import CompcertCommon.

Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.core_semantics_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Reach-closed semantics extend effect semantics w/:                     *)
(*   1) args: the arguments passed to initial_core at initialization      *)
(*   2) rets: the list of values returned to the core at inter. points    *)
(*   3) locs: the set of blocks allocated by this core                    *)
(*                                                                        *)
(* We say that the /reachable set/ of a reach-closed configuration        *)
(*   <(c,args,rets,locs), m>                                              *)
(* in global env. ge is                                                   *)
(*   REACH m                                                              *)
(*     (globalBlocks ge                                                   *)
(*     \cup blocksOf args                                                 *)
(*     \cup blocksOf rets                                                 *)
(*     \cup locs)                                                         *)
(*                                                                        *)
(* RC semantics are /reach closed/ in the sense that whenever             *)
(*   effstep rcsem ge U (c,args,rets,locs) m                              *)
(*                      (c',args,rets,locs\cup newBlocks m m') m'         *)
(* then                                                                   *)
(*   U is a subset of the reachable set of <(c,args,rets,locs),m>.        *)
(*                                                                        *)
(* That is, a reach-closed core only writes to blocks that it             *)
(* allocated or which were revealed to it by interaction at an external   *)
(* call point.                                                            *)

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

Definition initial_core ge v vs := 
  match initial_core sem ge v vs with
    | Some c => Some (mk c vs nil (fun _ => false))
    | None => None
  end.

Definition at_external c := at_external sem (core c).

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

Definition newBlocks (m m' : mem) := 
  fun b => (Pos.leb (Mem.nextblock m) b && Pos.ltb b (Mem.nextblock m')).

Definition effstep ge U c m c' m' :=
  effstep sem ge U (core c) m (core c') m' 
  /\ (forall b ofs, 
      U b ofs=true -> 
      REACH m (fun b => 
        isGlobalBlock ge b
        || getBlocks (args c++rets c) b 
        || locs c b) b=true)
  /\ args c'=args c
  /\ rets c'=rets c
  /\ locs c' = fun b => locs c b || newBlocks m m' b.

Arguments effstep /.

Definition corestep ge c m c' m' := 
  exists U, effstep ge U c m c' m'.

Arguments corestep /.

Lemma after_at_external_excl ov (c c' : state) :
  after_external ov c = Some c' -> 
  at_external c' = None.
Proof.
intros H.
case_eq (after_at_external_excl sem ov (core c) (core c')); auto.
revert H; unfold after_external.
case (core_semantics.after_external sem ov (core c)).
intros ?; case ov. intros v. inversion 1; auto. inversion 1; auto.
inversion 1.
Qed.
  
Program Definition coresem : CoreSemantics (Genv.t F V) state mem :=
  Build_CoreSemantics _ _ _
    initial_core
    at_external
    after_external
    halted
    corestep _ _ _ after_at_external_excl.
Next Obligation. 
destruct (effax1 _ _ _ _ _ _ _ H0) as [X Y].
revert X; apply corestep_not_at_external; auto. 
Qed.
Next Obligation. 
destruct (effax1 _ _ _ _ _ _ _ H0) as [X Y].
revert X; apply corestep_not_halted; auto.
Qed.
Next Obligation. case_eq (at_external_halted_excl sem (core q)); auto. Qed.

Program Definition coopsem : CoopCoreSem (Genv.t F V) state :=
  Build_CoopCoreSem _ _ coresem _.
Next Obligation. 
destruct (effax1 _ _ _ _ _ _ _ H) as [X Y].
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

Definition reach_set (ge : Genv.t F V) (c : state) (m : Mem.mem) :=
  REACH m (fun b => isGlobalBlock ge b
                 || getBlocks (args c) b
                 || getBlocks (rets c) b
                 || locs c b).

End rc. End RC.
