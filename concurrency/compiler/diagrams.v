
Require Import compcert.common.Events.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Require Import VST.msl.Coqlib2.

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
    (b = nb)%positive -> (* needed?*)
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
      list_map_rel memval_lessdef mvs2 vals2.
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
     inversion Hevol; inversion Hinj; subst.
     inversion Hinj_str; subst.

     assert (Hincr0: inject_incr j'0 j0).
     { eapply evolution_inject_incr; eassumption. }
     
     assert (Hpdiagram: principled_diagram (nextblock_eff nb ev2) j'0 j0 lev1 ls2).
     { econstructor; eauto.
       eapply consecutive_tail; eassumption. }

     assert (Hdiagram: diagram (nextblock_eff nb b) j'0 j' lev1 l2).
     {  econstructor; try eassumption.
        - clear - Hincr H5 H10 Hconsec' Hconsec.
          inversion H5; subst; eauto.
          inversion H10; subst.
          intros ????.
          if_tac in H0; subst; auto.
          + inversion H0; subst.
            inversion Hconsec'; subst.
            inversion Hconsec; subst.
            auto.
        - eapply consecutive_tail; eassumption.
     }

     assert (Hlessdef: effect_lessdef ev2 b).
     { 
       eapply (evolution_injection_lessdef j j'); try eassumption.
       * eapply incr_inject_mem_effect_strong; try eassumption.
         inversion H5; subst; eauto.
         -- eapply evolution_inject_effect; eassumption.
       * eapply consecutive_head; eauto.
       * eapply consecutive_head; eauto. }
     
     replace (nextblock_eff nb b) with (nextblock_eff nb ev2) in Hdiagram by
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
  Admitted.



(** *mem_interference with mem_effect *)
Section MemInterference.
  Definition mem_effect_forward: mem -> Events.mem_effect -> mem -> Prop.
  (* Definition mem_effect_forward m ev m':= 
         execute ev in m, without checking for permissions.
   *)
  Admitted.
  
  Inductive mem_interference: mem -> list Events.mem_effect -> mem -> Prop:=
  | Nil_mem_interference: forall m, mem_interference m nil m
  | Build_mem_interference: forall m m' m'' ev lev,
      mem_effect_forward m ev m' ->
      mem_interference m' lev m'' ->
      mem_interference m (ev::lev) m''.
  (* OLD_mem_interference:= Mem.unchanged_on (loc_readable_cur m) m *)

  Lemma mem_interference_one:
    forall m m' ev, 
      mem_effect_forward m ev m' ->
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

  Lemma mem_effect_forward_determ:
    forall eff m m1' m2',
      mem_effect_forward m eff m1' -> 
      mem_effect_forward m eff m2' ->
      m1' = m2'.
  Proof.
    intros. 
  Admitted.
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
      pose proof (mem_effect_forward_determ
                    _ _ _ _
                    H4 H5); subst.
      eapply IHlev; eassumption.
  Qed.

  
Lemma interference_same_visible:
  forall m m' lev, mem_interference m lev m' ->
              same_visible m m'.
Admitted.

End MemInterference.


Definition consecutive_until: block -> list Events.mem_effect -> block -> Prop.
Admitted.
Lemma consecutive_until_cat:
  forall lev lev' b b' b'',
    consecutive_until b lev b' ->
    consecutive_until b' lev' b'' ->
    consecutive_until b (lev ++ lev') b''.
Proof.
Admitted.
Lemma consecutive_until_consecutive:
  forall lev b b',
    consecutive_until b lev b' ->
    consecutive b lev.
Proof.
Admitted.

Lemma strict_inj_evolution_cat:
  forall j j' j'' lev1 lev1' lev2 lev2' nb nb' nb'',
    strict_injection_evolution j j' lev1 lev2 ->
    strict_injection_evolution j' j'' lev1' lev2' ->
    consecutive_until nb lev2 nb' ->
    consecutive_until nb' lev2' nb'' ->
    strict_injection_evolution j j'' (lev1++lev1') (lev2++lev2').
Proof.
Admitted.

Lemma interference_consecutive: forall m lev m',
    mem_interference m lev m' ->
    consecutive (Mem.nextblock m) lev.
Proof.
  intros. induction lev; try econstructor.
Admitted.
Lemma interference_consecutive_until:
  forall {m lev m'},
    mem_interference m lev m' ->
    consecutive_until (Mem.nextblock m) lev (Mem.nextblock m').
Proof. Admitted.




