Require Import Omega.
Require Import Coq.Classes.Morphisms.

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Events.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.EventsAux.

Require Import VST.concurrency.common.permissions. Import permissions.

Require Import VST.msl.Coqlib2.
Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.mem_equiv.

Import BinInt.
Import List.
Import Relation_Definitions.
Import RelationClasses.


Set Bullet Behavior "Strict Subproofs".


(** *Monotonicity (inject_incr)*)
Class Inject_Monotonic {A:Type}(R: meminj -> relation A):=
  monotonicity: forall j j' a1 a2,
    R j a1 a2 ->
    inject_incr j j' ->
    R j' a1 a2.

Ltac emonotonicity:=
  try (unfold Inject_Monotonic);
  eapply monotonicity.


Instance list_map_rel_monotonicity:
  forall {A} {R: meminj -> relation A},
    Inject_Monotonic R ->
    Inject_Monotonic (fun j => Forall2 (R j)).
Proof.
  intros ? ? ? j j' vals1.
  induction vals1; intros.
  - inversion H0; subst. constructor.
  - inversion H0; subst. constructor; auto.
    + emonotonicity; eauto.
Qed.

Lemma list_map_rel_monotonicity':
  forall {A} {R: meminj -> relation A},
    (forall j j' vals1 vals2,
        R j vals1 vals2 ->
        inject_incr j j' ->
        R j' vals1 vals2) ->
    forall j j' vals1 vals2,
      (Forall2 (R j)) vals1 vals2 ->
      inject_incr j j' ->
      (Forall2 (R j')) vals1 vals2.
Proof.
  intros ? ? ? j j' vals1.
  eapply list_map_rel_monotonicity.
  unfold Inject_Monotonic. eapply H.
Qed.
Instance memval_inject_monotonic:
  Inject_Monotonic memval_inject:=
  memval_inject_incr.
Instance list_memval_inject_monotonic:
  Inject_Monotonic list_memval_inject.
Proof.
  eapply list_map_rel_monotonicity.
  emonotonicity.
Qed.
Instance inject_hi_low_monotonic:
  Inject_Monotonic inject_hi_low.
Proof. intros ???? H H0.
       inversion H; subst.
       econstructor. apply H0; auto.
Qed.
Instance list_inject_hi_low_monotonic:
  Inject_Monotonic list_inject_hi_low.
Proof. eapply list_map_rel_monotonicity; emonotonicity. Qed.

Instance inject_mem_effect_monotonic:
  Inject_Monotonic Events.inject_mem_effect.
Proof.
  intros ??????.
  inversion H; subst;
    econstructor; eauto.
  - emonotonicity; eassumption.
  - emonotonicity; eassumption.
Qed.
Instance list_inject_mem_effect_monotonic :
  Inject_Monotonic Events.list_inject_mem_effect.
Proof.
  emonotonicity.
Qed.


(** *strict_injection_evolution *)

Inductive injection_evolution_effect:
  meminj -> meminj ->
  Events.mem_effect -> Events.mem_effect -> Prop:=
|EffEvolWrite: forall b1 b2 ofs1 ofs2 mvs1 mvs2 j,
    Events.inject_mem_effect
      j
      (common.Events.Write b1 ofs1 mvs1)
      (common.Events.Write b2 ofs2 mvs2) ->
    injection_evolution_effect
      j j
      (common.Events.Write b1 ofs1 mvs1)
      (common.Events.Write b2 ofs2 mvs2)
|EffEvolAlloc: forall j j' (b1 b2:block) ofs1 ofs1',
    j b1 = None -> (* Do we need this? *)
    j' = (fun b => if eq_block b b1 then
                  Some (b2, 0%Z) else j b) ->
    injection_evolution_effect
      j j'
      (common.Events.Alloc b1 ofs1 ofs1')
      (common.Events.Alloc b2 ofs1 ofs1')
|EffEvolFree: forall  j ls1 ls2,
    Events.inject_mem_effect j
                             (common.Events.Free ls1)
                             (common.Events.Free ls2) ->
    injection_evolution_effect
      j j
      (common.Events.Free ls1)
      (common.Events.Free ls2).

Inductive strict_injection_evolution:
  meminj -> meminj ->
  list Events.mem_effect -> list Events.mem_effect -> Prop:=
| EvolutionNil: forall j,
    strict_injection_evolution j j nil nil
| EvolutionCons: forall j j' j'' ev1 ev2 ls1 ls2,
    injection_evolution_effect j j' ev1 ev2 ->
    strict_injection_evolution j' j'' ls1 ls2 ->
    strict_injection_evolution
      j j''
      (ev1::ls1) (ev2::ls2).

Lemma evolution_inject_effect:
  forall j j' ev1 ev2,
    injection_evolution_effect j j' ev1 ev2 ->
    Events.inject_mem_effect j' ev1 ev2.
Proof.
  intros. inversion H; subst; eauto.
  (*replace (Alloc b2 ofs1 ofs1') with (Alloc b2 (ofs1 + 0) (ofs1' + 0)). *)
  econstructor; destruct (eq_block b1 b1); eauto.
  contradict n; reflexivity.
  (*f_equal; Omega.omega.*)
Qed.
Lemma effect_evolution_incr:
  forall j j' ev1 ev2,
    injection_evolution_effect j j' ev1 ev2 ->
    inject_incr j j'.
Proof.
  intros. inversion H; subst;
            try eapply inject_incr_refl.
  intros b1' b2' delt HH.
  destruct (eq_block b1' b1); auto.
  + subst. congruence.
Qed.
Lemma evolution_inject_incr:
  forall j j' lev1 lev2,
    strict_injection_evolution j j' lev1 lev2 ->
    inject_incr j j'.
Proof.
  intros j j' lev1; revert j j'.
  induction lev1; intros.
  - inversion H; subst.
    eapply inject_incr_refl.
  - inversion H; subst.
    eapply (inject_incr_trans _ j'0).
    + eapply effect_evolution_incr; eassumption.
    + eapply IHlev1.
      eauto.
Qed.

Lemma evolution_list_inject_mem:
  forall j j' lev1 lev2,
    strict_injection_evolution j j' lev1 lev2 ->
    Events.list_inject_mem_effect j' lev1 lev2.
Proof.
  intros j j' lev1; revert j j'.
  induction lev1; intros.
  - inversion H; subst. econstructor.
  - inversion H; subst. econstructor.
    + eapply evolution_inject_effect in H4.
      eapply inject_mem_effect_monotonic; try eassumption.
      eapply evolution_inject_incr; eassumption.
    + eapply IHlev1; eauto.
Qed.


(** *Lessdef*)
Instance Forall2_preorder {A} (R: relation A) {Pre: PreOrder R}:
  PreOrder (Forall2 R).
Proof. constructor.
       - intros ls; induction ls; econstructor; auto.
         reflexivity.
       - intros ls1.
         induction ls1; intros. 
         + inversion H; subst; inversion H0; subst. constructor.
         + inversion H; subst; inversion H0; subst. constructor; eauto.
           etransitivity; eauto.
Qed.


Inductive memval_lessdef: relation memval:=
| MvUndefLessDef : forall mv, memval_lessdef Undef mv 
| MvBytelLessDef : forall b, memval_lessdef (Byte b) (Byte b)
| MvReflLessDef : forall v v' q n,
    Val.lessdef v v' ->
    memval_lessdef (Fragment v q n) (Fragment v' q n).
Instance memval_lessdef_preorder: PreOrder memval_lessdef.
Proof. constructor.
       - intros x; destruct x; econstructor. apply Val.lessdef_refl.
       - intros x y z ? ?.
         inversion H; subst; inversion H0; subst; econstructor.
         eapply Val.lessdef_trans; eassumption.
Qed.

Inductive effect_lessdef:
  relation Events.mem_effect:=
| EvWriteLessDef:
    forall b ofs mvs mvs',
      (Forall2 memval_lessdef) mvs mvs' ->
      effect_lessdef (common.Events.Write b ofs mvs)
                     (common.Events.Write b ofs mvs')
| EvReflLessDef: forall eff,  effect_lessdef eff eff.
Instance effect_lessdef_preorder: PreOrder effect_lessdef.
Proof. constructor.
       - intros x; destruct x; econstructor. reflexivity.
       - intros x y z ? ?.
         inversion H; subst; inversion H0; subst; econstructor; try eassumption.
         + etransitivity; eassumption.
Qed.

Definition effects_lessdef:
  relation (list Events.mem_effect):=
  Forall2 effect_lessdef.


(** *Consecutive*)
Inductive consecutive: block -> list Events.mem_effect -> Prop:=
| consecutiveNil: forall nb,
    consecutive nb nil
| consecutiveWrite: forall nb b ofs mvals lev',
    (b <= nb)%positive -> (* needed?*)
    consecutive nb lev' ->
    consecutive nb ((common.Events.Write b ofs mvals):: lev')
| consecutiveAlloc: forall nb b ofs mvals lev',
    (b = nb)%positive -> (* needed?*)
    consecutive (Pos.succ nb) lev' ->
    consecutive nb ((common.Events.Alloc b ofs mvals):: lev')
| consecutiveFree: forall nb lsbzz lev',
    (Forall (fun x => (fst (fst x)) < nb)%positive lsbzz) ->
    consecutive nb lev' ->
    consecutive nb ((common.Events.Free lsbzz):: lev').
Lemma consecutive_monotonic:
  forall nb lev0 lev,
    effects_lessdef lev0 lev ->
    consecutive nb lev ->
    consecutive nb lev0.
Proof.
  intros nb lev0. revert nb.
  induction lev0; intros.
  - econstructor.
  - inversion H; subst.
    inversion H0; subst;
      inversion H3; subst;
        econstructor; eauto.
Qed.

(** *Section Diagrams *) 
Record diagram
       (nb: block) (j j': meminj)
       (lev1 lev2: list Events.mem_effect):=
  { Dincr: inject_incr j j'
    ; Dinj: Events.list_inject_mem_effect j' lev1 lev2
    ; Dconsec: consecutive nb lev2
  }.

Record principled_diagram
       (nb: block) (j j': meminj)
       (lev1 lev2: list Events.mem_effect):=
  { PDevol: strict_injection_evolution j j' lev1 lev2
    ; PDinj_str: Events.list_inject_mem_effect_strong j' lev1 lev2
    ; PDconsec: consecutive nb lev2
  }.

Inductive principled_diagram':
  block -> meminj -> meminj -> list Events.mem_effect -> Prop :=
|build_pd': forall  nb j j0 lev1 lev20,
    principled_diagram nb j j0 lev1 lev20 ->
    principled_diagram' nb j j0 lev1.
Inductive diagram':
  block -> meminj -> meminj -> list Events.mem_effect -> Prop :=
|build_d': forall nb j j' lev1 lev2,
    diagram nb j j' lev1 lev2 ->
    diagram' nb j j' lev1.





(** *Principaled Effects and values*)
Lemma principaled_val_exists:
  forall j v1 v2,
    Val.inject j v1 v2 ->
    exists v20,
      inject_strong j v1 v20 /\
      Val.lessdef v20 v2.
Proof.
  intros. induction H;
            try (eexists; split; econstructor); eassumption.
Qed.
Lemma principaled_memval_exists:
  forall j mv1 mv2,
    memval_inject j mv1 mv2 ->
    exists mv20,
      memval_inject_strong j mv1 mv20 /\
      memval_lessdef mv20 mv2.
Proof.
  intros. induction H;
            try solve[eexists; split; econstructor].
  - eapply principaled_val_exists in H.
    destruct H as (v20&?&?).
    eexists; split. econstructor; eassumption.
    econstructor; eauto.
Qed.
Lemma principaled_memvals_exists:
  forall j mv1 mv2,
    list_memval_inject j mv1 mv2 ->
    exists mv20,
      list_memval_inject_strong j mv1 mv20 /\
      Forall2 memval_lessdef mv20 mv2.
Proof.
  intros. induction H; subst.
  - exists nil; split; econstructor.
  - destruct (principaled_memval_exists _ _ _ H) as (v20&?&?).
    destruct IHForall2 as (mv20&?&?).
    exists (v20::mv20); split. constructor; eassumption.
    econstructor; eauto.
Qed.
Lemma principaled_effect_exists:
  forall j eff1 eff2,
    Events.inject_mem_effect j eff1 eff2 ->
    exists eff20,
      Events.inject_mem_effect_strong j eff1 eff20 /\
      effect_lessdef eff20 eff2.
Proof.
  intros. inversion H; subst;
            try solve[eexists; split; econstructor; eauto].
  + destruct (principaled_memvals_exists _ _ _ H1) as (mv20&?&?).
    eexists; split. econstructor; eauto.
    econstructor; eassumption.
Qed.
Lemma principaled_effects_exists:
  forall j lev1 lev2,
    Events.list_inject_mem_effect j lev1 lev2 ->
    exists lev20,
      Events.list_inject_mem_effect_strong j lev1 lev20 /\
      effects_lessdef lev20 lev2.
Proof.
  intros j lev1 lev2; revert j lev1.
  induction lev2; intros.
  - inversion H; subst.
    exists nil; split; econstructor.
  - inversion H; subst; clear H.
    destruct (principaled_effect_exists _ _ _ H3) as (eff20&?&?).
    destruct (IHlev2 _ _ H4) as (lev20&?&?).
    eexists; split.
    + econstructor; eassumption.
    + econstructor; eassumption.
Qed.

Lemma memval_inject_weaken:
  forall j1 j2 a b b0,
    inject_incr j1 j2 ->
    memval_inject_strong j2 a b ->
    memval_inject j1 a b0 ->
    memval_inject j1 a b.
Proof.
  intros.
  inv H0; inv H1; econstructor.
  inv H2; inv H6; econstructor; eauto.
  eapply H in H3 as HH. rewrite HH in H0; inv H0.
  assumption.
Qed.
Lemma list_memval_inject_relax:
  forall vals1 vals2 vals2' j1 j2,
    list_memval_inject j1 vals1 vals2' ->
    list_memval_inject_strong j2 vals1 vals2 ->
    inject_incr j1 j2 ->
    list_memval_inject j1 vals1 vals2.
  induction vals1.
  ++ intros; inv H0; econstructor.
  ++ intros. inv H0; inv H. 
     econstructor; eauto.
     eapply memval_inject_weaken; eauto.
     eapply IHvals1; eauto.
Qed.

Lemma principaled_injection_exists:
  forall j j' lev1 lev2 lev20,
    strict_injection_evolution j j' lev1 lev2 ->
    Events.list_inject_mem_effect_strong j' lev1 lev20 ->
    effects_lessdef lev20 lev2 ->
    strict_injection_evolution j j' lev1 lev20.
Proof.
  intros j j' lev1; revert j j'.
  induction lev1; intros.
  - inversion H0; inversion H; subst. econstructor.
  - inversion H0; inversion H; subst; inversion H1; 
      subst; clear H0 H H1.
    econstructor; eauto.
    + eapply evolution_inject_incr in H13 as Hincr.
      clear H13 H6.

      inv H4; inv H11; inv H7.
      * inv H8.
        assert (delt = delt0) by omega; subst delt0. clear H7.
        repeat econstructor; eauto.
        eapply list_memval_inject_relax; eauto.     
      * inv H8.
        repeat econstructor; eauto.
      * econstructor; eauto.
      * econstructor; eauto.
Qed.

Lemma principled_diagram_exists:
  forall nb j j' lev1 lev2,
    strict_injection_evolution j j' lev1 lev2 ->
    consecutive nb lev2 ->
    exists lev20,
      principled_diagram nb j j' lev1 lev20 /\
      effects_lessdef lev20 lev2.
Proof.
  intros.
  pose proof (evolution_list_inject_mem _ _ _ _ H).
  destruct (principaled_effects_exists _ _ _ H1) as (lev20 & HH & Horder).
  exists lev20.
  econstructor; repeat split.
  - eapply principaled_injection_exists; eauto.
  - eauto.
  - 
    eapply consecutive_monotonic; eassumption.
  - assumption.
Qed.
Lemma principled_diagram_exists':
  forall (nb : block) (j j' : meminj) (lev1 lev2 : list Events.mem_effect),
    strict_injection_evolution j j' lev1 lev2 ->
    consecutive nb lev2 ->
    principled_diagram' nb j j' lev1.
Proof.
  intros.
  edestruct principled_diagram_exists as (?&?&?); eauto.
  econstructor; eauto.
Qed.
Lemma consecutive_head:
  forall nb ev ls,
    consecutive nb (ev :: ls) ->
    consecutive nb (ev :: nil).
Proof. intros. inversion H; subst;
                 econstructor; auto; constructor.
Qed.
Definition nextblock_eff (nb:block) (ev:mem_effect):=
  match ev with
  | Write _ _ _ => nb
  | Alloc _ _ _ => Pos.succ nb
  | Free _ => nb
  end.
Lemma consecutive_tail:
  forall nb ev ls,
    consecutive nb (ev :: ls) ->
    consecutive (nextblock_eff nb ev ) (ls).
Proof. intros. inversion H; subst; simpl; auto. Qed.


Lemma inject_lessdef:
  forall j' j0 : meminj,
    inject_incr j0 j' ->
    forall v1 v3 v2 : val,
      Val.inject j' v1 v2 ->
      inject_strong j0 v1 v3 -> Val.lessdef v3 v2.
Proof.
  intros j' j0 Hincr v1 v3 v2 H0 H1.
  inversion H0; subst;
    inversion H1; subst;
      try solve[constructor].
  - apply Hincr in H4.
    rewrite H4 in H; inversion H; subst.
    constructor.
Qed.
Lemma inject_memval_lessdef:
  forall (a : memval) (j' j0 : meminj),
    inject_incr j0 j' ->
    forall b b0 : memval,
      memval_inject j' a b ->
      memval_inject_strong j0 a b0 -> memval_lessdef b0 b.
Proof.
  intros a j' j0 H b b0 H4 H5.
  inversion H4; subst;
    inversion H5; subst;
      try solve[constructor].
  - constructor.
    eapply inject_lessdef; eassumption.
Qed.
Lemma list_inject_memval_lessdef:
  forall (j' j0 : meminj) (mvs1 mvs2 : list memval),
    inject_incr j0 j' ->
    forall vals2 : list memval,
      list_memval_inject j' mvs1 vals2 ->
      list_memval_inject_strong j0 mvs1 mvs2 ->
      Forall2 memval_lessdef mvs2 vals2.
Proof.
  intros j' j0 mvs1. revert j' j0.
  induction mvs1; intros.
  - inversion H0; subst;
      inversion H1; subst;
        constructor.
  - inversion H0; subst;
      inversion H1; subst;
        try solve[econstructor; eauto].
    econstructor.
    
    +eapply inject_memval_lessdef; eassumption.
    + eapply IHmvs1; eassumption.
Qed.

Lemma list_inject_hi_low_lessdef:
  forall j0 j ls1 ls2 ls20,
    inject_incr j0 j ->
    list_inject_hi_low j0 ls1 ls20 ->
    list_inject_hi_low j ls1 ls2 ->
    ls20 = ls2.
Proof.
  intros j0 j ls1; revert j0 j.
  induction ls1; intros.
  - inversion H0; subst;
      inversion H1; subst; auto.
  - inversion H0; subst;
      inversion H1; subst; auto.
    f_equal.
    + clear - H4 H5 H.
      inversion H4; subst;
        inversion H5; subst.
      apply H in H0; rewrite H0 in H7.
      inversion H7; subst. reflexivity.
    + eapply IHls1; eassumption.
Qed.

Lemma incr_inject_strong:
  forall (j0 j0' : meminj) v1 v2,
    inject_incr j0 j0' ->
    inject_strong j0' v1 v2 ->
    Val.inject j0 v1 v2 ->
    inject_strong j0 v1 v2.
Proof.
  intros.
  inversion H0; subst;
    inversion H1; subst;
      econstructor; eauto.
Qed.
Lemma incr_memval_inject_strong:
  forall (j0 j0' : meminj) (val1 val2 : memval),
    inject_incr j0 j0' ->
    memval_inject_strong j0' val1 val2 ->
    memval_inject j0 val1 val2 ->
    memval_inject_strong j0 val1 val2.
Proof.
  intros.
  inversion H0; subst;
    inversion H1; subst;
      econstructor; eauto.
  eapply incr_inject_strong; eassumption.
Qed.
Lemma incr_list_memval_inject_strong:
  forall (j0 j0' : meminj) (vals1 vals2 : list memval),
    inject_incr j0 j0' ->
    list_memval_inject_strong j0' vals1 vals2 ->
    list_memval_inject j0 vals1 vals2 -> list_memval_inject_strong j0 vals1 vals2.
Proof.
  intros j0 j0' vals1; revert j0 j0'.
  induction vals1; intros j0 j0' vals2 H0 H3 H11.
  - inversion H3; subst;
      inversion H11; subst;
        econstructor; eauto.
  - inversion H3; subst;
      inversion H11; subst;
        econstructor; eauto.
    
    eapply incr_memval_inject_strong; eassumption.
    eapply IHvals1; eauto.
Qed.
(*j0 is the strict evolution of j.
  so j' has to also be j0<j'.
 *)
(* simpl_incr defines an injection that increases only, with 0 ofsets *)
Definition simpl_incr (f1 f2 : meminj):=
  forall (b b' : block) (delta : Z),
    f2 b = Some (b', delta) ->
    f1 b = None -> delta = 0%Z.

  Lemma evolution_injection_lessdef:
  forall j j' j0 ev1 ev2 ev20 nb,
    inject_incr j j' ->
    injection_evolution_effect j j0 ev1 ev2 ->
    inject_mem_effect_strong j0 ev1 ev2 ->
    inject_mem_effect j' ev1 ev20 ->
    consecutive nb (ev2 :: nil) ->
    consecutive nb (ev20 :: nil) ->
    effect_lessdef ev2 ev20.
Proof.
  intros
    ??????? Hincr Hevol Hinj_str Hinject Hconsec Hconsec'.
  inversion Hevol; subst; clear Hevol; 
    inversion Hinject; subst; clear Hinject.
  - inversion Hinj_str; subst.
    apply Hincr in H2.
    rewrite H2 in H4; inversion H4; subst.
    econstructor.
    eapply list_inject_memval_lessdef; eassumption.

  - inversion Hconsec; subst.
    inversion Hconsec'; subst.
    inversion Hinj_str; subst.
    match_case in H1. inversion H1; subst.
    (*rewrite (Hsimpl_incr b1 nb delt); auto.
    repeat match goal with
             | [|- context[(?x + 0)%Z]] => replace (x + 0)%Z with x by Omega.omega
             | [|- context[(0 + ?x)%Z]] => replace (0 + x)%Z with x by Omega.omega
           end. *)
    econstructor.
  - inversion H; subst.
    inversion Hinj_str; subst.
    eapply list_inject_hi_low_lessdef in H1; eauto.
    subst; econstructor.
Qed.
Lemma incr_inject_mem_effect_strong:
  forall j0 j0' ev1 ev2,
    inject_mem_effect_strong j0' ev1 ev2 ->
    inject_incr j0 j0' ->
    inject_mem_effect j0 ev1 ev2 ->
    inject_mem_effect_strong j0 ev1 ev2.
Proof.
  intros.
  inversion H; subst;
    inversion H1; subst;
      econstructor; eauto.
  - apply H0 in H6;
      rewrite H2 in H6;
      inversion H6; subst.
    eapply incr_list_memval_inject_strong; eassumption.
Qed.


Lemma principled_diagram_correct:
  forall nb j j' j0 lev1 lev2 lev20,
    principled_diagram nb j j0 lev1 lev20 ->
    diagram nb j j' lev1 lev2 ->
    inject_incr j0 j' /\  effects_lessdef lev20 lev2.
Proof.
  intros nb j j' j0 lev1; revert nb j j' j0 .
  induction lev1; intros.
  - inversion H as [Hevol Hinj_str Hconsec];
      inversion H0 as [Hincr  Hinj Hconsec'].
    inversion Hevol; inversion Hinj; subst.
    split; auto. reflexivity.
  -  inversion H as [Hevol Hinj_str Hconsec];
       inversion H0 as [Hincr  Hinj Hconsec'].
     inversion Hevol; subst. inversion Hinj; subst.
     inversion Hinj_str; subst.

     assert (Hincr0: inject_incr j'0 j0).
     { eapply evolution_inject_incr; eassumption. }
     
     assert (Hpdiagram: principled_diagram (nextblock_eff nb ev2) j'0 j0 lev1 ls2).
     { econstructor; eauto.
       eapply consecutive_tail; eassumption. }
     
     assert (Hdiagram: diagram (nextblock_eff nb y) j'0 j' lev1 l').
     {  econstructor; try eassumption.
        - clear - Hincr H5 H3 Hconsec' Hconsec.
          (*    H5 : injection_evolution_effect j j'0 a ev2
                H10 : inject_mem_effect j' a y *)             
          inversion H5; subst; eauto.
          inversion H3; subst.
          intros ????.
          if_tac in H0; subst; auto.
          + inversion H0; subst.
            inversion Hconsec'; subst.
            inversion Hconsec; subst.
            auto.
        - eapply consecutive_tail. eassumption.
     }

     assert (Hlessdef: effect_lessdef ev2 y).
     { 
       eapply (evolution_injection_lessdef j j'); try eassumption.
       * eapply incr_inject_mem_effect_strong; try eassumption.
         inversion H5; subst; eauto.
         -- eapply evolution_inject_effect; eassumption.
       * eapply consecutive_head; eauto.
       * eapply consecutive_head; eauto. }
     
     replace (nextblock_eff nb y) with (nextblock_eff nb ev2) in Hdiagram by
         (inversion Hlessdef; reflexivity).
     
     edestruct (IHlev1 _ _ _ _ _ _ Hpdiagram Hdiagram) as (Hincr'&Hlessdef').
     split.
     + assumption.
     + econstructor; auto.
Qed.

Lemma principled_diagram_correct':
  forall (nb : block)
    (j j' j0 : meminj)
    (lev1: list Events.mem_effect),
    principled_diagram' nb j j0 lev1 ->
    diagram' nb j j' lev1 ->
    inject_incr j0 j'.
Proof.
  intros * H1 H2; inversion H1; inversion H2;subst; 
    eapply principled_diagram_correct; eassumption.
Qed.



  
  Record same_visible (m1 m2: mem):=
    { same_cur:
        forall b ofs p,
          (Mem.perm m1 b ofs Cur p <->
                Mem.perm m2 b ofs Cur p);
      same_visible12:
        forall b ofs,
          Mem.perm m1 b ofs Cur Readable ->
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1))) =
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2)));
      same_visible21:
        forall b ofs,
          Mem.perm m2 b ofs Cur Readable ->
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1))) =
          (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m2)));
    }.
  Instance same_vis_equiv: (Equivalence same_visible).
  Proof.
    econstructor.
    - intros ?; econstructor;
        intros; reflexivity.
    - intros ???. inv H.
      econstructor; intros; symmetry; eauto.
    - intros ??? H1 H2. inv H1; inv H2.
      econstructor; intros; try now (etransitivity; eauto).
      + etransitivity.
        * eapply same_visible22; (eapply same_cur0; eauto).
        * eapply same_visible14; (eapply same_cur0; eauto).
      + etransitivity.
        * eapply same_visible13; (eapply same_cur0, same_cur1; eauto).
        * eapply same_visible23; eauto.
  Qed.
Instance range_perm_visible:
  Proper (same_visible ==> Logic.eq ==> Logic.eq ==> Logic.eq ==>
                       trieq Cur ==> Logic.eq ==> iff)
         Mem.range_perm.
Proof.
  unfold Mem.range_perm.
  setoid_help.proper_iff; setoid_help.proper_intros; subst.
  inversion H3; subst; eapply H; auto.
Qed.
  Instance valid_acccess_visible:
    Proper (same_visible ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           Mem.valid_access.
  Proof.
    unfold Mem.valid_access.
    setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
    unfold Mem.valid_access in *.
    rewrite <- H; auto.
  Qed.
  Lemma same_visible_range:
    forall m1 m2,
      (forall (b : block) (ofs : Z),
          Mem.perm m1 b ofs Cur Readable ->
          ZMap.get ofs (Mem.mem_contents m1) !! b =
          ZMap.get ofs (Mem.mem_contents m2) !! b) ->
      forall ofs b x, 
        Mem.range_perm m1 b ofs (ofs + x) Cur Readable ->
        Mem.getN (Z.to_nat x) ofs (Mem.mem_contents m1) !! b =
        Mem.getN (Z.to_nat x) ofs (Mem.mem_contents m2) !! b.
  Proof.
    unfold Mem.range_perm. intros. 
    destruct x; simpl; auto.
    rewrite <- (Pos2Nat.id p) in H0.
    remember (Pos.to_nat p) as n eqn:HH; clear HH.
    destruct n; try reflexivity.
    revert  b ofs H0. induction n.
    - simpl. intros. f_equal. apply H. apply H0. omega.
    - intros.
      simpl; f_equal; eauto.
      + eapply H. apply H0. clear.
        remember ( Z.pos (Pos.of_nat (S (S n)))) as P.
        assert (0 < P)%Z.
        { subst. reflexivity. }
        omega.                        
      + eapply IHn. intros.
        eapply H0.
        replace (Z.pos (Pos.of_nat (S (S n))))%Z
          with (1 + Z.pos (Pos.of_nat (S n)))%Z.
        2:{ do 2 rewrite <- Pos.of_nat_succ.
            do 2 rewrite Zpos_P_of_succ_nat.
            rewrite Nat2Z.inj_succ. omega. }
        omega.
  Qed.
  Instance load_Proper_visible:
    Proper (Logic.eq ==> same_visible ==> Logic.eq ==> Logic.eq  ==> Logic.eq) Mem.load.
  Proof.
    setoid_help.proper_intros; subst.
    Transparent Mem.load.
    unfold Mem.load.
    do 2 match_case;
    try match goal with
          [H: ~ _ |- _ ]=>
          exfalso; apply H;
            first [ rewrite <- H0| rewrite H0]; auto
        end.
    do 2 f_equal.
    unfold Mem.valid_access in *.
    destruct v, v0.
    unfold size_chunk_nat.
    eapply same_visible_range; eauto.
    eapply H0.
  Qed.

Instance loadv_visible:
  Proper (Logic.eq ==> same_visible ==> Logic.eq ==> Logic.eq) Mem.loadv.
Proof.
  setoid_help.proper_intros; subst.
  destruct y1; simpl; auto.
  rewrite H0; reflexivity.
Qed.
   



(** *mem_interference with mem_effect *)
Section MemInterference.
  Inductive mem_effect_interf: mem -> mem_effect -> mem -> Prop:=
  | Write_interf: forall m m' m'' b ofs mvs,
      forall other_perm Hlt Hlt',
        permMapsDisjoint (getCurPerm m) other_perm ->
        Mem.storebytes (@restrPermMap other_perm m Hlt') b ofs mvs = Some m' ->
        m'' = (@restrPermMap (getCurPerm m) m' Hlt) ->
        mvs <> nil ->
        mem_effect_interf m (Write b ofs mvs) m''
  | Alloc_interf: forall m m' m'' lo hi nb Hlt,
      Mem.alloc m lo hi = (m', nb) ->
      m'' = (@restrPermMap (getCurPerm m) m' Hlt) ->
      mem_effect_interf m (Alloc nb lo hi) m''
  | Free_interf: forall m m' m'' ls,
      forall other_perm Hlt Hlt',
        permMapsDisjoint (getCurPerm m) other_perm ->
        Mem.free_list (@restrPermMap other_perm m Hlt') ls = Some m' ->
        Forall (fun bzz=> snd (fst bzz) < snd bzz) ls ->
        m'' = (@restrPermMap (getCurPerm m) m' Hlt) ->
      mem_effect_interf m (Free ls) m''.
           
  
  Inductive mem_interference: mem -> list Events.mem_effect -> mem -> Prop:=
  | Nil_mem_interference: forall m, mem_interference m nil m
  | Build_mem_interference: forall m m' m'' ev lev,
      mem_effect_interf m ev m' ->
      mem_interference m' lev m'' ->
      mem_interference m (ev::lev) m''.
  (* OLD_mem_interference:= Mem.unchanged_on (loc_readable_cur m) m *)

  Lemma mem_interference_one:
    forall m m' ev, 
      mem_effect_interf m ev m' ->
      mem_interference m (ev::nil) m'.
  Proof. intros; econstructor; [eauto| econstructor].
  Qed.

  Lemma mem_interference_trans:
    forall lev lev' m m' m'', 
      mem_interference m lev m' ->
      mem_interference m' lev' m'' ->
      mem_interference m (lev ++ lev') m''.
  Proof.
    induction lev.
    - simpl; intros.
      inversion H; subst; auto.
    - simpl; intros.
      inversion H; subst; auto.
      econstructor; eauto.
  Qed.
  Lemma mem_eq:
    forall m1 m2,
      Mem.mem_contents m1 = Mem.mem_contents m2 ->
      Mem.mem_access m1 = Mem.mem_access m2 ->
      Mem.nextblock m1 = Mem.nextblock m2 ->
      m1 = m2.
  Proof.
    intros.
    destruct m1; destruct m2; simpl in *.
    dependent_rewrite H.
    dependent_rewrite H0.
    dependent_rewrite H1.
    f_equal; apply lib.Axioms.proof_irr.
  Qed.
    
  Lemma mem_effect_interf_determ:
    forall eff m m1' m2',
      mem_effect_interf m eff m1' -> 
      mem_effect_interf m eff m2' ->
      m1' = m2'.
  Proof.
    intros. inv H; inv H0.
    - (* WRITE *)
      eapply mem_eq.
      + simpl. etransitivity; [|symmetry].
        * eapply Mem.storebytes_mem_contents in H2; eauto.
        * eapply Mem.storebytes_mem_contents in H8;
            simpl in *; eauto.
      + eapply Mem.storebytes_access in H2; eauto;
          eapply Mem.storebytes_access in H8.
        clear - H2 H8.
        unfold Mem.mem_access in *; simpl in *.
        simpl; f_equal.
        * extensionality n;
            extensionality ofs.
          do 2 rewrite Clight_bounds.Mem_canonical_useful; auto.
        * destruct m';
            destruct m'0; subst; simpl in *.
          unfold PTree.map.
          do 2 rewrite Coqlib3.xmap_compose; auto.   
      + simpl. etransitivity; [|symmetry].
           * eapply Mem.nextblock_storebytes in H2; eauto.
           *  eapply Mem.nextblock_storebytes in H8;
                simpl in *; eauto.
    - (* ALLOC *)  
      rewrite H1 in H6; inv H6.
      eapply restr_proof_irr.
    - eapply mem_eq.
      + Set Nested Proofs Allowed.
        Lemma free_contents_eq:
              forall b z0 z m m',
                Mem.free m b z0 z = Some m' ->
                Mem.mem_contents m =
                Mem.mem_contents m'.
            Proof.
              intros. Transparent Mem.free.
              unfold Mem.free in H.
              match_case in H. inv H.
              reflexivity.
            Qed.

            Lemma PMap_map_set:
                    forall A B (f: A -> B) t p a,
                      PMap.map f (PMap.set p a t) =
                      PMap.set p (f a) (PMap.map f t).
                  Proof.
                    induction t; unfold PMap.set, PMap.map; simpl.
                    intros p a0; f_equal; revert p a0; 
                    induction b; simpl.
                    - intros; simpl; f_equal.
                      induction p; simpl; f_equal; eauto.
                    - intros; simpl; f_equal.
                      induction p; simpl; f_equal; eauto.
                  Qed.
                  
                Lemma free_max_eq:
                  forall  m1 m2 m1' m2' b lo hi,
                    getMaxPerm  m1 = getMaxPerm  m2 ->
                    Mem.free m1 b lo hi = Some m1' ->
                    Mem.free m2 b lo hi = Some m2' ->
                    getMaxPerm  m1' = getMaxPerm  m2'.
                Proof.
                  intros.
                  Transparent Mem.free.
                  unfold Mem.free in *;
                    match_case in H0;
                    match_case in H1.
                  inv H0; inv H1.
                  assert (HH: forall b ofs, (Mem.mem_access m1) !! b ofs Max =
                                   (Mem.mem_access m2) !! b ofs Max).
                  { intros; repeat rewrite_getPerm; rewrite H; reflexivity. }
                  clear r r0 Heqs Heqs0. (* if lo>= hi those are rivial*)
                  unfold getMaxPerm in *.
                  unfold Mem.mem_access.
                  destruct m1; destruct m2; simpl in *.
                  revert HH H; clear.
                  intros.
                  
                  do 2 rewrite PMap_map_set; eauto.
                  rewrite H; auto. f_equal.
                  extensionality ofs; rewrite HH; eauto.
                Qed.
            Lemma free_list_max_eq:
              forall ls m1 m2 m1' m2',
              getMaxPerm  m1 = getMaxPerm  m2 ->
              Mem.free_list m1 ls = Some m1' ->
              Mem.free_list m2 ls = Some m2' ->
              getMaxPerm  m1' = getMaxPerm  m2'.
            Proof.
              induction ls.
              - intros. inv H0; inv H1; auto.
              - intros. simpl in H0; simpl in H1.
                repeat match_case in H0; subst.
                repeat match_case in H1; subst.
                eapply IHls; try eapply H0; try eapply H1.
                
                eapply free_max_eq; eauto.
            Qed.
            Lemma free_list_contents_eq:
              forall ls m m',
                Mem.free_list m ls = Some m' ->
                Mem.mem_contents m =
                Mem.mem_contents m'.
            Proof.
              induction ls.
              - intros * HH; inversion HH; auto.
              - intros; simpl in *.
                do 3 match_case in H; subst.
                eapply IHls in H. rewrite <- H.
                eapply free_contents_eq; eauto.
            Qed.
            simpl.
            eapply free_list_contents_eq in H2;
            eapply free_list_contents_eq in H5; simpl in *.
            etransitivity; try eassumption; symmetry; auto.
      + simpl; f_equal.
        * extensionality n;
            extensionality ofs.
          do 2 rewrite Clight_bounds.Mem_canonical_useful; auto.
        * remember (
              fun (b : positive) (f : Z -> perm_kind -> option permission) (ofs : Z)=>
                f ofs Max)
            as f1.
          remember (
              fun (b : positive) (f : Z -> perm_kind -> option permission) (ofs : Z)
                (k : perm_kind) =>
                match k with
                | Max => f ofs Max
                | Cur => (getCurPerm m) !! b ofs
                end ) as f3.
          remember (
              fun (b : positive) (f : Z -> option permission) (ofs : Z)
                (k : perm_kind) =>
                match k with
                | Max => f ofs
                | Cur => (getCurPerm m) !! b ofs
                end ) as f2.
          assert (f3 = (fun (p0 : positive) f => f2 p0 (f1 p0 f))).
          { subst; reflexivity. }
          rewrite H.
          unfold PTree.map. rewrite <- Coqlib3.xmap_compose.
          symmetry; rewrite <- Coqlib3.xmap_compose.
          f_equal.
          assert (HH: getMaxPerm m'0 = getMaxPerm m').
          { eapply free_list_max_eq; try eassumption.
            do 2 rewrite restr_Max_eq; reflexivity. }
          subst f1. 
          inv HH. do 2 rewrite Coqlib3.map_map1 in H8.
          unfold PTree.map in *.
          eauto.
      + simpl. etransitivity; [|symmetry].
        * eapply mem_lemmas.nextblock_freelist in H2; eauto.
        *  eapply mem_lemmas.nextblock_freelist in H5;
             simpl in *; eauto.
  Qed.
  Lemma mem_interference_determ:
    forall lev m m1' m2',
      mem_interference m lev m1' -> 
      mem_interference m lev m2' ->
      m1' = m2'.
  Proof.
    intros lev; induction lev; intros.
    - inversion H; subst;
        inversion H0; subst; reflexivity.
    - inversion H; subst; inversion H0; subst.
      pose proof (mem_effect_interf_determ
                    _ _ _ _
                    H4 H5); subst.
      eapply IHlev; eassumption.
  Qed.
  Record same_visible' m1 m2:=
    {HH1: Cur_equiv m1 m2;
     HH2: forall (b : block) (ofs : Z),
         Mem.perm m1 b ofs Cur Readable ->
         ZMap.get ofs (Mem.mem_contents m1) !! b =
         ZMap.get ofs (Mem.mem_contents m2) !! b }.
  Lemma same_visible_alternative:
    forall m1 m2,
      same_visible m1 m2 <->
      same_visible' m1 m2.
  Proof.
    split; intros; inv H.
    - constructor; eauto.
      + intros b; extensionality ofs.
        unfold Mem.perm in *.
        
        assert (HH: forall op,
                   Mem.perm_order'' ((Mem.mem_access m1) !! b ofs Cur) op <->
                   Mem.perm_order'' ((Mem.mem_access m2) !! b ofs Cur) op).
        { intros; split; simpl; intros;
            destruct op; eauto; try eapply event_semantics.po_None;
              erewrite <- mem_lemmas.po_oo in *; eapply same_cur0; auto. }
        repeat rewrite_getPerm.
        dup HH as HH'.
        specialize (HH ((getCurPerm m1) !! b ofs));
          destruct HH as [HH _].
        exploit HH; try apply po_refl; 
          clear HH; intros HH.
        specialize (HH' ((getCurPerm m2) !! b ofs));
          destruct HH' as [_ HH'].
        exploit HH'; try apply po_refl; 
          clear HH'; intros HH'.
        match goal with |- ?lhs = ?rhs =>
                        destruct lhs; destruct rhs;
                          inv HH; inv HH'; eauto
        end.
    - econstructor; eauto.
      + intros; rewrite HH3; reflexivity.
      + intros * HH; rewrite <- HH3 in HH; eauto.
  Qed.
  
    Lemma mem_effect_interf_visible:
      forall m m' lev, mem_effect_interf m lev m' ->
                  same_visible m m'.
    Proof.
        intros; eapply same_visible_alternative.
        inv H.
      - econstructor.
        + symmetry.  eapply getCur_restr.
        + intros.
          pose proof (Mem.storebytes_range_perm _ _ _ _ _ H1) as Hwritable.
          eapply Mem.storebytes_mem_contents in H1.
          rewrite  restr_content_equiv, H1.
          destruct (peq b b0); swap 1 2.
          * rewrite PMap.gso; eauto.
          * subst; rewrite PMap.gss.
            destruct (Memory.range_dec ofs ofs0 (ofs + Z.of_nat (Datatypes.length mvs)));
              swap 1 2.
            -- rewrite Mem.setN_outside; eauto. apply juicy_mem.range_inv0; auto.
            -- eapply perm_range_perm in a; eauto.
               (* same location is readable and writable, 
                  in two permissions that are disjoint ->
                  contradiction
                *)
               exfalso; specialize (H0 b0 ofs0).
               destruct H0 as (P & HH).
               clear - HH H a.
               unfold Mem.perm in *.
               repeat rewrite_getPerm.
               rewrite getCur_restr in a.
               
               unfold Mem.perm_order' in *.
                 repeat match_case in H;
                   repeat match_case in a;
                   try inv a;
                   try inv H;
                   inv HH.
                 
      - econstructor.
        + symmetry.  eapply getCur_restr.
        + intros b0 ofs HH.
          destruct (peq b0 nb); swap 1 2.
          * exploit mem_lemmas.AllocContentsOther1; eauto.
            simpl; intros ->; reflexivity.
          * subst. eapply Mem.alloc_result in H0; subst.
            unfold Mem.perm in *.
            rewrite Mem.nextblock_noaccess in HH. inv HH.
            apply Plt_strict.
      - eapply free_list_contents_eq in H1.
        econstructor.
        + symmetry.  eapply getCur_restr.
        + intros. simpl in *. 
          rewrite H1; eauto.
    Qed.
  Lemma interference_same_visible:
  forall m m' lev, mem_interference m lev m' ->
              same_visible m m'.
Proof.
  intros; induction H.
  - reflexivity.
  - etransitivity; eauto.
    eapply mem_effect_interf_visible; eauto.
Qed.
    
End MemInterference.

Inductive nextblock_event: block -> Events.mem_effect -> block -> Prop:=
| Write_nb: forall nb b ofs mvs,
    (b <= nb)%positive ->
    nextblock_event nb (Write b ofs mvs) nb
  | Alloc_nb: forall nb lo hi,
      nextblock_event nb (Alloc nb lo hi) (Pos.succ nb)
  | Free_nb: forall nb ls,
      Forall (fun x : positive * Z * Z => (fst (fst x) < nb)%positive) ls ->
             nextblock_event nb (Free ls) nb.
Inductive consecutive_until: block -> list Events.mem_effect -> block -> Prop:=
| consecutive_refl: forall b, consecutive_until b nil b
| consecutive_cons: forall b b' b'' ev ls,
    nextblock_event b ev b' -> 
    consecutive_until b' ls b'' -> 
    consecutive_until b (ev::ls) b''.                                          
Lemma consecutive_until_cat:
  forall lev lev' b b' b'',
    consecutive_until b lev b' ->
    consecutive_until b' lev' b'' ->
    consecutive_until b (lev ++ lev') b''.
Proof.
  induction lev.
  - intros. inv H; simpl. eauto.
  - intros. simpl. inv H.
    econstructor; eauto.
Qed.
Lemma consecutive_until_consecutive:
  forall lev b b',
    consecutive_until b lev b' ->
    consecutive b lev.
Proof.
  induction lev.
  - intros. inv H; simpl. constructor.
  - intros. inv H; simpl. 
    inv H3.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
Qed.
Lemma strict_inj_evolution_cat:
  forall j j' j'' lev1 lev1' lev2 lev2' nb nb' nb'',
    strict_injection_evolution j j' lev1 lev2 ->
    strict_injection_evolution j' j'' lev1' lev2' ->
    consecutive_until nb lev2 nb' ->
    consecutive_until nb' lev2' nb'' ->
    strict_injection_evolution j j'' (lev1++lev1') (lev2++lev2').
Proof.
  intros j j' j'' lev1; revert j j' j''; induction lev1.
  - intros. inv H. simpl; eauto.
  - intros. inv H. simpl; eauto.
    inv H1.
    econstructor; eauto.
Qed.

Lemma free_lt_nextblock:
  forall b lo hi m1 m2,
    Mem.free m1 b lo hi = Some m2 ->
    (lo < hi) ->
    (b < Mem.nextblock m1)%positive.
Proof.
  intros.
  eapply Mem.perm_valid_block; eauto.
  eapply Mem.free_range_perm; eauto.
  split; try eassumption; reflexivity.
Qed.
Lemma free_list_lt_nextblock:
  forall ls m1 m2,
    Mem.free_list m1 ls = Some m2 ->
    Forall (fun bzz => snd (fst bzz) < snd bzz) ls ->
    Forall (fun x => (fst (fst x) < Mem.nextblock m1)%positive) ls.
Proof.
  induction ls.
  - intros. inv H. constructor.
  - intros.
    simpl in H. repeat match_case in H; subst.
    constructor; eauto.
    + eapply free_lt_nextblock; eauto.
      inv H0; eauto.
    + erewrite <- Mem.nextblock_free; eauto.
      eapply IHls; eauto.
      inv H0; eauto.
Qed.
Lemma mem_effect_interf_consecutive: forall ev m m',
    mem_effect_interf m ev m' ->
    nextblock_event (Mem.nextblock m) ev (Mem.nextblock m').
Proof.
  intros. inv H. 
  - simpl.
    assert (Mem.valid_block m b).
    { apply Mem.storebytes_range_perm in H1.
      eapply perm_range_perm in H1; swap 1 2.
      - split. simpl; reflexivity. simpl.
        destruct mvs; try now contradict H3; auto.
        simpl; rewrite Zpos_P_of_succ_nat; omega. 
      - destruct (mem_lemmas.valid_block_dec m b); eauto.
        unfold Mem.valid_block in n. eapply Mem.nextblock_noaccess in n.
        apply Mem.perm_cur_max in H1.
        rewrite restr_Max_equiv in H1.
        hnf in H1; rewrite n in H1.
        inv H1. }
    eapply Mem.nextblock_storebytes in H1; simpl in H1.
    rewrite H1; econstructor.
    unfold Mem.valid_block in *.
    apply Plt_Ple; assumption.
  - simpl.
    erewrite
      (Mem.alloc_result _ _ _ _ nb); eauto.
    apply Mem.nextblock_alloc in H0; subst.
    rewrite H0. econstructor.
  - simpl. erewrite (mem_lemmas.nextblock_freelist _ _ _ H1); simpl.
    econstructor.
    replace (Mem.nextblock m) with
        (Mem.nextblock (restrPermMap Hlt')) by reflexivity.
    eapply free_list_lt_nextblock; eauto.
Qed.

Lemma interference_consecutive_until: forall lev m m',
    mem_interference m lev m' ->
    consecutive_until (Mem.nextblock m) lev (Mem.nextblock m').
Proof.
  induction lev.
  - intros. inv H. constructor.
  - intros. inv H. econstructor.
    2: eapply IHlev; eauto.
    eapply mem_effect_interf_consecutive; eauto.
Qed.

        
Lemma interference_consecutive: forall m lev m',
    mem_interference m lev m' ->
    consecutive (Mem.nextblock m) lev.
Proof.
  intros.
  eapply consecutive_until_consecutive, interference_consecutive_until.
  eauto.
Qed.




