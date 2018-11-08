
Require Import compcert.common.Events.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Import BinInt.
Import List.
Import Relation_Definitions.
Import RelationClasses.



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
    Inject_Monotonic (fun j => list_map_rel (R j)).
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
      (list_map_rel (R j)) vals1 vals2 ->
      inject_incr j j' ->
      (list_map_rel (R j')) vals1 vals2.
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
  econstructor.
  destruct (eq_block b1 b1); eauto.
  contradict n; reflexivity.
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
Instance list_map_rel_preorder {A} (R: relation A) {Pre: PreOrder R}:
  PreOrder (list_map_rel R).
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
      (list_map_rel memval_lessdef) mvs mvs' ->
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
  Events.list_map_rel effect_lessdef.


(** *Consecutive*)
Inductive consecutive: block -> list Events.mem_effect -> Prop:=
| consecutiveNil: forall nb,
    consecutive nb nil
| consecutiveWrite: forall nb b ofs mvals lev',
    (b <= nb)%positive -> (* needed?*)
    consecutive nb lev' ->
    consecutive nb ((common.Events.Write b ofs mvals):: lev')
| consecutiveAlloc: forall nb b ofs mvals lev',
    (b <= nb)%positive -> (* needed?*)
    consecutive (Pos.succ nb) lev' ->
    consecutive nb ((common.Events.Alloc b ofs mvals):: lev')
| consecutiveFree: forall nb lsbzz lev',
    (Forall (fun x => (fst (fst x)) <= nb)%positive lsbzz) ->
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
Definition diagram
           (nb: block) (j j': meminj)
           (lev1 lev2: list Events.mem_effect):=
  inject_incr j j' /\
  Events.list_inject_mem_effect j' lev1 lev2 /\
  consecutive nb lev2.

Definition principled_diagram
           (nb: block) (j j': meminj)
           (lev1 lev2: list Events.mem_effect):=
  strict_injection_evolution j j' lev1 lev2 /\
  Events.list_inject_mem_effect_strong j' lev1 lev2 /\
  consecutive nb lev2.



(** *Principaled Effects and values*)
Lemma principaled_val_exists:
  forall j v1 v2,
    Val.inject j v1 v2 ->
    exists v20,
      Events.inject_strong j v1 v20 /\
      Val.lessdef v20 v2.
Proof.
  intros. induction H;
    try (eexists; split; econstructor); eassumption.
Qed.
Lemma principaled_memval_exists:
  forall j mv1 mv2,
    memval_inject j mv1 mv2 ->
    exists mv20,
      Events.memval_inject_strong j mv1 mv20 /\
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
    Events.list_memval_inject j mv1 mv2 ->
    exists mv20,
      Events.list_memval_inject_strong j mv1 mv20 /\
      Events.list_map_rel memval_lessdef mv20 mv2.
Proof.
  intros. induction H; subst.
  - exists nil; split; econstructor.
  - destruct (principaled_memval_exists _ _ _ H) as (v20&?&?).
    destruct IHlist_map_rel as (mv20&?&?).
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
          subst.
        econstructor; eauto.
        + 


          admit. (*  injection_evolution_effect j j'0 a ev2 
                                     effect_lessdef b ev2
                                     injection_evolution_effect j j'0 a b*) 
    Admitted.

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
  - 
    eapply principaled_injection_exists; eauto.
  - eauto.
  - 
    eapply consecutive_monotonic; eassumption.
  - assumption.
Qed.

(*
Lemma principaled_diagrsam_effects_exists:
  forall nb j j' lev1 lev2,
    diagram nb j j' lev1 lev2 ->
    exists lev20,
      Events.list_inject_mem_effect_strong j' lev1 lev20.
Proof.
  
  
  
  
  
  
  
  
  Lemma principled_diagram_correct:
    forall nb j j' j0 lev1 lev2 lev20,
      principled_diagram nb j j0 lev1 lev20 ->
      diagram nb j j' lev1 lev2 ->
      inject_incr j0 j' /\ events_more_defined lev2 lev20.
  Admitted.

  Lemma principled_diagram_exists:
    forall nb j j' lev1 lev2,
      diagram nb j j' lev1 lev2 ->
      exists j0 lev20,
        principled_diagram nb j j0 lev1 lev20.
  Admitted.*)
  