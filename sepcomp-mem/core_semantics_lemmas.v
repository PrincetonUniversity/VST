Require Import Coq.Logic.Decidable.

(*CompCert imports*)
Require Import sepcomp.Events.
Require Import sepcomp.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import sepcomp.Globalenvs.
Require Import compcert.lib.Axioms.

Require Import sepcomp.Coqlib2.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.

Section CoopCoreSemLemmas.
Context {G C D: Type}.
Variable coopsem: CoopCoreSem G C D.

Lemma corestepN_fwd: forall ge c m c' m' n,
  corestepN coopsem ge n c m c' m' -> 
  mem_forward m m'.
Proof.
intros until n; revert c m.
induction n; simpl; auto.
inversion 1; apply mem_forward_refl; auto.
intros c m [c2 [m2 [? ?]]].
apply mem_forward_trans with (m2 := m2).
apply corestep_fwd in H; auto.
eapply IHn; eauto.
Qed.

Lemma corestepN_memwd: forall ge c m c' m' n,
  corestepN coopsem ge n c m c' m' -> 
  mem_wd m -> 
  mem_wd m'.
Proof.
intros until n; revert c m.
induction n; simpl; auto.
inversion 1; auto.
intros c m [c2 [m2 [? ?]]] H1.
apply corestep_wdmem in H; auto.
eapply IHn; eauto.
Qed.

End CoopCoreSemLemmas.

Lemma inject_separated_incr_fwd: 
  forall j j' m1 m2 j'' m2'
    (InjSep : inject_separated j j' m1 m2)
    (InjSep' : inject_separated j' j'' m1 m2')
    (InjIncr' : inject_incr j' j'')
    (Fwd: mem_forward m2 m2'),
    inject_separated j j'' m1 m2.
Proof.
intros. intros b. intros. remember (j' b) as z. 
destruct z; apply eq_sym in Heqz.
destruct p. specialize (InjIncr' _ _ _ Heqz). 
rewrite InjIncr' in H0. inv H0.
apply (InjSep _ _ _ H Heqz). 
destruct (InjSep' _ _ _ Heqz H0).
split. trivial.
intros N. apply H2. eapply Fwd. apply N.
Qed.

Lemma inject_separated_incr_fwd2: 
  forall j0 j j' m10 m20 m1 m2,
  inject_incr j j' -> 
  inject_separated j j' m1 m2 -> 
  inject_incr j0 j -> 
  mem_forward m10 m1 -> 
  inject_separated j0 j m10 m20 -> 
  mem_forward m20 m2 -> 
  inject_separated j0 j' m10 m20.
Proof.
intros until m2; intros H1 H2 H3 H4 H5 H6.
apply (@inject_separated_incr_fwd j0 j m10 m20 j' m2); auto.
unfold inject_separated.
intros b1 b2 delta H7 H8.
unfold inject_separated in H2, H5.
specialize (H2 b1 b2 delta H7 H8).
destruct H2 as [H21 H22].
unfold mem_forward in H4, H6.
specialize (H4 b1).
specialize (H6 b2).
split; intros CONTRA.
solve[destruct (H4 CONTRA); auto].
apply H22; auto.
Qed.

Lemma external_call_mem_forward:
  forall (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem),
    external_call ef ge vargs m1 t vres m2 -> mem_forward m1 m2.
Proof.
intros.
intros b Hb.
split; intros. eapply external_call_valid_block; eauto.
split.
intros.
eapply external_call_max_perm; eauto.
admit. (*must add another condition to external_call semantics*)
Qed.

Lemma forward_nextblock: forall m m',
  mem_forward m m' -> 
  (Mem.nextblock m <= Mem.nextblock m')%Z.
Proof.
intros m m' H1.
unfold mem_forward in H1.
unfold Mem.valid_block in H1.
destruct (Z_le_dec (Mem.nextblock m) (Mem.nextblock m')); auto.
assert (H2: (Mem.nextblock m' < Mem.nextblock m)%Z) by omega.
destruct (H1 (Mem.nextblock m')); auto.
omega.
Qed.

Section EffectfulSemanticsLemmas.
Context {G C D: Type}.
Variable (efsem: EffectfulSemantics G C D).

Definition new_effect k b ofs c c' :=
  ~effects efsem c k b ofs /\ effects efsem c' k b ofs.

Lemma new_effect_dec: 
  forall k b ofs c c',
  {new_effect k b ofs c c'}+{~new_effect k b ofs c c'}.
Proof.
intros k b ofs c c'.
unfold new_effect.
destruct (effects_dec efsem c k b ofs).
right.
intros [CONTRA _].
auto.
destruct (effects_dec efsem c' k b ofs).
left.
split; auto.
right.
intros [C1 C2].
auto.
Qed.

Lemma effects_new: forall b ofs ge c m c' m',
  ~effects efsem c AllocEffect b ofs -> 
  corestep efsem ge c m c' m' -> 
  effects efsem c' AllocEffect b ofs -> 
  Mem.nextblock m <= b < Mem.nextblock m'.
Proof.
intros until m'; intros H1 H2 H3.
eapply (effects_backward_alloc _ b ofs) in H2; eauto.
rewrite H2 in H3.
destruct H3; auto.
solve[elimtype False; auto].
Qed.

Lemma effects_new2: forall b ofs ge c m c' m',
  corestep efsem ge c m c' m' -> 
  effects_valid efsem c m -> 
  (new_effect AllocEffect b ofs c c' <-> 
    Mem.nextblock m <= b < Mem.nextblock m').
Proof.
intros until m'; intros H1 VAL.
eapply (effects_backward_alloc _ b ofs) in H1.
unfold new_effect.
rewrite H1.
split; intros.
destruct H; destruct H0; auto.
elimtype False; auto.
split; auto.
intros CONTRA.
apply VAL in CONTRA.
unfold Mem.valid_block in CONTRA.
omega.
Qed.

Lemma effects_forwardN: forall b ofs ge n c m c' m' k,
  corestepN efsem ge n c m c' m' -> 
  effects efsem c k b ofs -> 
  effects efsem c' k b ofs.
Proof.
intros until k; revert c m.
induction n; simpl; intros.
solve[inv H; auto].
destruct H as [c2 [m2 [STEP STEPN]]].
eapply effects_forward in STEP; eauto.
destruct STEP as [EF UNCH].
solve[eapply IHn; eauto].
Qed.
  
Lemma effects_newN: forall b ofs ge n c m c' m',
  ~effects efsem c AllocEffect b ofs -> 
  corestepN efsem ge n c m c' m' -> 
  effects efsem c' AllocEffect b ofs -> 
  Mem.nextblock m <= b < Mem.nextblock m'.
Proof.
intros until m'; revert c m; induction n; auto.
intros c m H1 H2 H3.
simpl in H2.
inv H2.
solve[elimtype False; auto].
intros c m H1 H2 H3.
simpl in H2.
destruct H2 as [c2 [m2 [STEP STEPN]]].
destruct (effects_dec efsem c2 AllocEffect b ofs).
eapply (effects_new b ofs) in STEP; eauto.
apply corestepN_fwd in STEPN.
apply forward_nextblock in STEPN.
omega.
cut (Mem.nextblock m2 <= b < Mem.nextblock m'). intro H4.
apply corestep_fwd in STEP.
apply forward_nextblock in STEP.
omega.
solve[eapply IHn with (m := m2); eauto].
Qed.

Lemma effects_backward_allocN: 
  forall b ofs ge n c m c' m',
  corestepN efsem ge n c m c' m' -> 
  (effects efsem c' AllocEffect b ofs <-> 
   effects efsem c AllocEffect b ofs \/
   Mem.nextblock m <= b < Mem.nextblock m').
Proof.
induction n; simpl; intros until m'; intro H1.
inv H1.
split; auto.
intros [H|H]; auto.
destruct H; omega.
destruct H1 as [c2 [m2 [STEP STEPN]]].
assert (H:
  effects efsem c' AllocEffect b ofs <->
  effects efsem c2 AllocEffect b ofs \/
  Mem.nextblock m2 <= b < Mem.nextblock m').
 solve[apply IHn; hnf; auto].
rewrite H.
rewrite effects_backward_alloc; eauto.
split; [intros [[X|X]|X]|].
solve[left; auto].
destruct X; right; split; auto.
solve[apply corestepN_fwd in STEPN; apply STEPN; auto].
destruct X; right; split; auto.
assert (Mem.nextblock m <= Mem.nextblock m2).
 apply corestep_fwd in STEP.
 solve[apply forward_nextblock; auto].
omega.
intros [X|X].
left; auto.
destruct X.
destruct (Z_lt_dec b (Mem.nextblock m2)).
left; right; split; auto.
assert (Mem.nextblock m2 <= b) by omega.
solve[right; split; auto].
Qed.

Notation reserve_type := (block -> Z -> Prop).

Record reserve := {sort :> reserve_type;
                   _ : forall b ofs, {sort b ofs}+{~sort b ofs}}.

Lemma reserve_dec: 
  forall r: reserve, 
  forall b ofs, {r b ofs}+{~r b ofs}.
Proof. destruct r; auto. Qed.

Definition inject_reserve (f: meminj) (r: reserve_type): reserve_type :=
  fun b ofs => exists b0 delta, 
    f b0 = Some (b, delta) /\ r b0 (ofs-delta).

Parameter inject_reserve_ : meminj -> reserve -> reserve.
Axiom inject_reserve_AX : forall f r, sort (inject_reserve_ f r) = inject_reserve f r.

Definition reserve_incr_tp (r1 r2: reserve_type) :=
  forall b ofs, r1 b ofs -> r2 b ofs.

Definition reserve_incr (r1 r2: reserve_type) := 
  forall b ofs, r1 b ofs -> r2 b ofs.

Lemma reserve_incr_refl: forall r, reserve_incr r r.
Proof. intros r b; auto. Qed.

Lemma reserve_incr_trans: forall r1 r2 r3,
   reserve_incr r1 r2 -> reserve_incr r2 r3 -> reserve_incr r1 r3.
Proof. intros. intros b. intros. apply H0. apply H. apply H1. Qed.

Definition uniform (r:reserve_type) (j: meminj) := 
  forall b b2 delta b' delta',
    j b = Some (b2,delta) -> j b' = Some(b2, delta') ->
    forall ofs, r b ofs = r b' (ofs + delta - delta').

Definition reserve_valid (r: reserve_type) (m: mem) :=
  forall b ofs, r b ofs -> Mem.valid_block m b.

Lemma reserve_incr_mono: 
  forall j j'
  (Inc : inject_incr j j') m1 m2
  (Sep : inject_separated j j' m1 m2) r
  (RV : reserve_valid r m1) r'
  (Rinc : reserve_incr_tp (inject_reserve j r) r'),
    reserve_incr_tp (inject_reserve j' r) r'.
Proof. intros. intros b; intros. apply Rinc. 
  destruct H as [b1 [delta [HJ HR]]].
  exists b1. exists delta. split; trivial. 
  remember (j b1) as q.
  destruct q; apply eq_sym in Heqq. 
  destruct p. rewrite (Inc _ _ _ Heqq) in HJ. apply HJ.
  exfalso. specialize (RV _ _ HR). 
  destruct (Sep _ _ _ Heqq HJ). apply (H RV).
Qed.

Lemma inject_reserve_incr: forall r rr (R: reserve_incr r rr) j,
  reserve_incr_tp (inject_reserve j r) (inject_reserve j rr).
Proof. 
  intros. intros b; intros. 
  destruct H as [b1 [delta [J H]]].
  exists b1. exists delta. specialize (R _ _ H).
  auto.
Qed.

Definition reserve_valid' (r: reserve_type) (f: meminj) (m: mem) :=
  forall b ofs b0 delta,
  r b0 (ofs-delta) -> 
  f b0 = Some (b, delta) -> 
  Mem.valid_block m b.

Definition reserve_separated (r r': reserve_type) (f': meminj) (m1 m2: mem) :=
  forall b1 ofs, 
    ~r b1 ofs -> r' b1 ofs -> 
    ~Mem.valid_block m1 b1 /\ 
    (forall delta b2, f' b1 = Some (b2, delta) -> ~Mem.valid_block m2 b2).

Definition reserve_separated1 (r r': reserve_type) m := 
  forall b ofs, ~r b ofs -> r' b ofs -> ~Mem.valid_block m b.

Definition reserve_separated2 (r r': reserve_type) (f': meminj) m :=
  forall b1 ofs, ~r b1 ofs -> r' b1 ofs -> 
    forall delta b2, f' b1 = Some (b2, delta) -> ~Mem.valid_block m b2.

Lemma reserve_separated_same: forall r j m1 m2,
    reserve_separated r r j m1 m2.
Proof. intros r j m1 m2 b; intros. contradiction. Qed.

(*requires decidability of r?*)
Lemma reserve_separated_trans: 
  forall r0 (r r': reserve) j j' m1 m2 m1' m2',
  inject_incr j j' -> 
  inject_separated j j' m1' m2' -> 
  mem_forward m1 m1' -> 
  mem_forward m2 m2' -> 
  reserve_separated r0 r j m1 m2 -> 
  reserve_separated r r' j' m1' m2' -> 
  reserve_separated r0 r' j' m1 m2.
Proof.
intros until m2'; unfold reserve_separated; 
 intros INCR SEP F1 F2 H1 H2.
intros until ofs; intros H3 H4.
split; [intros CONTRA|intros delta b2 J CONTRA].
destruct (reserve_dec r b1 ofs) as [X|X].
specialize (H1 _ _ H3 X).
solve[destruct H1; auto].
specialize (H2 _ _ X H4).
destruct H2 as [H2 ?].
solve[apply H2; apply F1; auto].
destruct (reserve_dec r b1 ofs) as [X|X].
unfold inject_separated in SEP.
specialize (H1 _ _ H3 X).
destruct H1 as [A B].
case_eq (j b1).
intros [? ? Y].
generalize Y as Y'; intro.
apply INCR in Y.
rewrite Y in J; inv J.
solve[specialize (B _ _ Y'); auto].
intros Y.
eapply SEP in Y; eauto.
destruct Y as [_ Y].
apply Y.
solve[apply F2; auto].
specialize (H2 _ _ X H4).
destruct H2 as [_ H2].
apply H2 in J; apply J.
solve[apply F2; auto].
Qed.

(** A core "relies" on the environment to leave unchanged those
 locations that are globally reserved and alloc'd by this core. *)

Definition rely (c: C) (m m': mem) := 
  mem_unchanged_on (fun b ofs => 
    reserved m b ofs /\ effects efsem c AllocEffect b ofs) m m'.

Definition rely' (j: meminj) (c: C) (m1 m2 m2': mem) := 
  mem_unchanged_on (fun b ofs => 
    effects efsem c AllocEffect b ofs /\
    exists b0 delta, 
      j b0 = Some (b, delta) /\ 
      reserved m1 b0 (ofs-delta)) m2 m2'.

(** A core "guarantees" not to touch those locations that are globally
 reserved and not alloc'd by this core. *)

Definition guarantee (r: reserve_type) (c: C) (m: mem) :=
  forall b ofs, 
  Mem.valid_block m b -> 
  r b ofs -> 
  effects efsem c ModifyEffect b ofs -> 
  effects efsem c AllocEffect b ofs.

Definition guarantee' (f: meminj) (r: reserve_type) := 
  guarantee (inject_reserve f r).

Lemma guarantee_backward_step: 
  forall ge r c m c' m',
  guarantee r c' m' -> 
  corestep efsem ge c m c' m' -> 
  guarantee r c m.
Proof.
intros until m'; intros G' STEP.
generalize STEP as STEP'; intro.
apply corestep_fwd in STEP.
intros b ofs VAL R EF.
destruct (STEP _ VAL) as [VAL' _].
specialize (G' b ofs VAL' R).
eapply effects_forward in EF; eauto.
specialize (G' EF).
eapply effects_backward_alloc in STEP'.
rewrite STEP' in G'.
destruct G'; auto.
elimtype False.
destruct H.
unfold Mem.valid_block in VAL.
omegaContradiction.
Qed.

Lemma guarantee_backward_stepN: 
  forall ge r c m c' m' n,
  guarantee r c' m' -> 
  corestepN efsem ge n c m c' m' -> 
  guarantee r c m.
Proof.
intros until n; intros G' STEP.
revert c m STEP.
induction n; [solve[intros c m STEP; hnf in STEP; inv STEP; auto]|].
intros c m STEP; hnf in STEP. 
destruct STEP as [c2 [m2 [STEP STEPN]]].
specialize (IHn _ _ STEPN).
solve[eapply guarantee_backward_step in IHn; eauto].
Qed.

Lemma guarantee'_backward_stepN: 
  forall ge j r c m c' m' n,
  guarantee' j r c' m' -> 
  corestepN efsem ge n c m c' m' -> 
  guarantee' j r c m.
Proof.
intros until n; intros G' STEP.
revert c m STEP.
induction n; [solve[intros c m STEP; hnf in STEP; inv STEP; auto]|].
intros c m STEP; hnf in STEP. 
destruct STEP as [c2 [m2 [STEP STEPN]]].
specialize (IHn _ _ STEPN).
solve[eapply guarantee_backward_step in IHn; eauto].
Qed.

Lemma guarantee_incr: 
  forall (r r': reserve) c m,
  guarantee r c m -> 
  reserve_incr r r' -> 
  reserve_separated1 r r' m -> 
  guarantee r' c m.
Proof.
intros until m; intros G1 R1 SEP b ofs VAL R2 EF.
destruct (reserve_dec r b ofs) as [RES|NRES].
solve[apply (G1 _ _ VAL RES EF)].
solve[specialize (SEP _ _ NRES R2); congruence].
Qed.

Definition inject_separated2 (j j': meminj) m :=
  forall (b1 b2: block) delta,
  j b1 = None ->
  j' b1 = Some (b2, delta) ->
  ~ Mem.valid_block m b2.

Lemma guarantee_incr': 
  forall j j' (r r': reserve) c m,
  guarantee (inject_reserve j r) c m -> 
  inject_incr j j' -> 
  inject_separated2 j j' m -> 
  reserve_incr r r' -> 
  reserve_separated2 r r' j' m -> 
  guarantee (inject_reserve j' r') c m.
Proof.
intros until m; intros G1 INCR INJSEP R1 SEP b ofs VAL R2 EF.
destruct R2 as [b2 [delta2 [H1 H2]]].
destruct (reserve_dec r b2 (ofs-delta2)) as [RES|NRES].
case_eq (j b2).
intros [b2' delta'] SOME.
generalize SOME as SOME'; intro.
apply INCR in SOME.
rewrite SOME in H1; inv H1.
eapply G1; eauto.
solve[exists b2, delta2; split; auto].
intros NONE.
exploit INJSEP; eauto.
solve[intros CONTRA; contradiction].
specialize (SEP _ _ NRES H2 _ _ H1).
contradiction.
Qed.

Lemma guarantee_decr:
  forall (r r': reserve) c m,
  guarantee r' c m -> 
  reserve_incr r r' -> 
  guarantee r c m.
Proof. intros until m; intros G1 R1 b ofs VAL R2 EFM; auto. Qed.

Lemma guarantee_decr2:
  forall (r r': reserve) j j' c m,
  guarantee (inject_reserve j' r') c m -> 
  reserve_incr r r' -> 
  inject_incr j j' -> 
  guarantee (inject_reserve j r) c m.
Proof. 
intros until m; intros G1 R1 INCR b ofs VAL R2 EFM.
assert (R2': inject_reserve j' r' b ofs).
 destruct R2 as [b0 [delta [X Y]]].
 exists b0, delta.
 solve[split; auto].
apply (G1 _ _ VAL R2' EFM).
Qed.

Lemma guarantee_incr_alloc: 
  forall ge (r r2: reserve) c m c2 m2 c' m' n,
  guarantee r c' m' -> 
  reserve_valid r2 m2 -> 
  reserve_separated1 r r2 m -> 
  corestep efsem ge c m c2 m2 -> 
  corestepN efsem ge n c2 m2 c' m' ->
  guarantee r2 c' m'.
Proof.
intros until n; intros G1 R1 SEP STEP STEPN b' ofs' VAL R2 EFM.
assert (G0: guarantee r c m).
 eapply guarantee_backward_stepN; eauto.
 instantiate (1 := S n); hnf.
 solve[exists c2, m2; split; eauto].
specialize (R1 _ _ R2).
specialize (G1 _ ofs' VAL).
destruct (reserve_dec r b' ofs') as [RT|RF].
solve[apply (G1 RT EFM)].
specialize (SEP _ _ RF R2).
assert (effects efsem c2 AllocEffect b' ofs').
 rewrite effects_backward_alloc; eauto.
 unfold Mem.valid_block in R1, SEP. 
 solve[right; omega].
solve[eapply effects_forwardN; eauto].
Qed.

Lemma guarantee_incr_allocN: 
  forall ge (r r': reserve) c m c' m' n,
  guarantee r c' m' -> 
  reserve_valid r m -> 
  reserve_separated1 r r' m -> 
  corestepN efsem ge n c m c' m' ->
  guarantee r' c' m'.
Proof.
intros until n; intros G1 R1 SEP STEPN.
revert r c m R1 SEP STEPN G1.
induction n.
simpl.
intros until m; intros H1 H2; inversion 1; intros G1; subst.
intros b' ofs' VAL R2 EF.
destruct (reserve_dec r b' ofs').
apply G1; auto.
specialize (H2 _ _ n R2).
solve[elimtype False; auto].
intros.
simpl in STEPN.
destruct STEPN as [c2 [m2 [STEP STEPN]]].
 assert (exists (r2: reserve),
  reserve_separated1 r r2 m /\
  reserve_separated1 r2 r' m2 /\
  reserve_valid r2 m2) as [r2 [H2 [H3 H4]]].
 set (r2 := fun b ofs => 
   if Z_lt_dec b (Mem.nextblock m) then r b ofs
     else if Z_lt_dec b (Mem.nextblock m2) then True
     else False).
 assert (DEC: forall b ofs, {r2 b ofs}+{~r2 b ofs}).
   intros b ofs.
   unfold r2.
   destruct (Z_lt_dec b (Mem.nextblock m)).
   apply reserve_dec.
   destruct (Z_lt_dec b (Mem.nextblock m2)).
   left; auto.
   right; auto.
 exists (Build_reserve r2 DEC).
 split.
 simpl.
 intros b ofs H1.
 unfold r2.
 solve[destruct (Z_lt_dec b (Mem.nextblock m)); auto].
 split.
 intros b ofs H1.
 unfold r2 in H1.
 simpl in H1.
 destruct (Z_lt_dec b (Mem.nextblock m)).
 intros; intros CONTRA.
 solve[eapply SEP; eauto].
 destruct (Z_lt_dec b (Mem.nextblock m2)).
 elimtype False; auto.
 solve[auto].
 simpl.
 unfold r2.
 intros b ofs.
 destruct (Z_lt_dec b (Mem.nextblock m)). 
 apply corestep_fwd in STEP.
 intros H1.
 solve[apply STEP; auto].
 destruct (Z_lt_dec b (Mem.nextblock m2)); auto.
 solve[intros; elimtype False; auto].
apply (IHn r2 c2 m2 H4 H3 STEPN).
solve[eapply guarantee_incr_alloc; eauto].
Qed.

Definition inject_valid j m1 m2 := 
  forall b1 b2 (delta: Z), 
  j b1 = Some (b2, delta) -> 
  Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2.

Definition inject_valid1 j m1 :=
  forall b1 (b2: block) (delta: Z), 
  j b1 = Some (b2, delta) -> 
  Mem.valid_block m1 b1.

Definition inject_valid2 j m2 := 
  forall (b1: block) b2 (delta: Z), 
  j b1 = Some (b2, delta) -> 
  Mem.valid_block m2 b2.

Lemma inject_reserve_eq: 
  forall j j2 r m1 m2,
  reserve_valid r m1 -> 
  inject_valid j m1 m2 -> 
  inject_incr j j2 -> 
  inject_separated j j2 m1 m2 -> 
  inject_reserve j r = inject_reserve j2 r.
Proof.
intros.
extensionality b.
extensionality ofs.
apply prop_ext.
unfold inject_reserve.
split; intros [b0 [delta [H3 H4]]].
solve[exists b0, delta; split; auto].
case_eq (j b0).
intros [x y] SOME.
generalize SOME as SOME'; intro.
apply H1 in SOME; auto.
rewrite SOME in H3; inv H3.
solve[exists b0, delta; split; auto].
intros NONE.
specialize (H2 _ _ _ NONE H3).
destruct H2 as [H2 H5].
apply H in H4.
solve[elimtype False; auto].
Qed.

Lemma guarantee_incr_alloc': 
  forall ge j j2 (r r2: reserve) c mleft m c2 m2 c' m' n,
  inject_incr j j2 -> 
  inject_separated j j2 mleft m -> 
  guarantee (inject_reserve j r) c' m' -> 
  reserve_separated r r2 j2 mleft m -> 
  corestep efsem ge c m c2 m2 -> 
  corestepN efsem ge n c2 m2 c' m' ->
  guarantee (inject_reserve j2 r2) c' m'.
Proof.
intros until n; intros INCR INJSEP G1 SEP STEP STEPN b' ofs' VAL R2 EFM.
assert (G0: guarantee (inject_reserve j r) c m).
 eapply guarantee_backward_stepN; eauto.
 instantiate (1 := S n); hnf.
 solve[exists c2, m2; split; eauto].
specialize (G1 _ ofs' VAL).
destruct R2 as [b0 [delta0 [X Y]]].
destruct (reserve_dec r b0 (ofs'-delta0)) as [RT|RF].
case_eq (j b0); [intros [b2 delta2] EQ|].
assert (b' = b2) as ->.
 apply INCR in EQ.
 solve[rewrite EQ in X; inv X; auto].
assert (EQ': delta0 = delta2).
 apply INCR in EQ.
 solve[rewrite EQ in X; inv X; auto].
subst delta0.
apply G1; auto.
solve[exists b0, delta2; split; auto].
intros NONE.
destruct (INJSEP _ _ _ NONE X) as [Z W].
rewrite effects_backward_allocN.
right.
split; eauto.
instantiate (1 := m).
unfold Mem.valid_block in W.
omega.
instantiate (1 := c).
instantiate (1 := S n).
instantiate (1 := ge).
auto.
hnf.
exists c2, m2; split; auto.
generalize SEP as SEP'; intro.
specialize (SEP _ _ RF Y).
rewrite effects_backward_allocN; eauto.
rewrite effects_backward_alloc; eauto.
rewrite or_assoc.
cut (Mem.nextblock m <= b' < Mem.nextblock m').
intros [? ?].
destruct (Z_lt_dec b' (Mem.nextblock m2)).
right; left; split; omega.
right; right; split; omega.
split; auto.
destruct SEP as [_ SEP].
specialize (SEP _ _ X).
unfold Mem.valid_block in SEP.
omega.
Qed.

Lemma guarantee_incr_allocN': 
  forall ge j j' (r r': reserve) c mleft m c' m' n,
  inject_incr j j' -> 
  inject_separated j j' mleft m -> 
  guarantee (inject_reserve j r) c' m' -> 
  reserve_incr r r' -> 
  reserve_separated r r' j' mleft m -> 
  corestepN efsem ge n c m c' m' ->
  guarantee (inject_reserve j' r') c' m'.
Proof.
intros until n; intros INCR INJSEP G1 RINCR SEP STEPN. 
destruct n.
simpl in STEPN; inv STEPN.
eapply guarantee_incr'; eauto.
intros b b' delta NONE SOME.
solve[exploit INJSEP; eauto; intros [_ ?]; auto].
intros b ofs ? ? ? ? ?.
solve[exploit SEP; eauto; intros [? H3]; eapply H3; eauto].
intros b' ofs' VAL R2 EFM.
assert (G0: guarantee (inject_reserve j r) c m).
 solve[eapply guarantee_backward_stepN; eauto].
specialize (G1 _ ofs' VAL).
destruct R2 as [b0 [delta0 [X Y]]].
destruct (reserve_dec r b0 (ofs'-delta0)) as [RT|RF].
case_eq (j b0); [intros [b2 delta2] EQ|].
assert (b' = b2) as ->.
 apply INCR in EQ.
 solve[rewrite EQ in X; inv X; auto].
assert (EQ': delta0 = delta2).
 apply INCR in EQ.
 solve[rewrite EQ in X; inv X; auto].
subst delta0.
apply G1; auto.
solve[exists b0, delta2; split; auto].
intros NONE.
destruct (INJSEP _ _ _ NONE X) as [Z W].
rewrite effects_backward_allocN.
right.
split; eauto.
instantiate (1 := m).
unfold Mem.valid_block in W.
omega.
instantiate (1 := c).
instantiate (1 := S n).
instantiate (1 := ge).
auto.
specialize (SEP _ _ RF Y).
destruct SEP as [_ SEP].
specialize (SEP _ _ X).
rewrite effects_backward_allocN; eauto.
unfold Mem.valid_block in SEP.
solve[right; split; auto; omega].
Qed.

Lemma guarantee_incr_alloc1: 
  forall ge (r r': reserve) c m c' m',
  guarantee r c' m' -> 
  reserve_valid r' m' -> 
  reserve_separated1 r r' m -> 
  corestep efsem ge c m c' m' -> 
  guarantee r' c' m'.
Proof.
intros.
eapply guarantee_incr_alloc; eauto.
instantiate (1 := O).
solve[hnf; auto].
Qed.

Lemma guarantee_incr_alloc1': 
  forall ge j j' (r r': reserve) c mleft m c' m',
  inject_incr j j' -> 
  inject_separated j j' mleft m -> 
  guarantee (inject_reserve j r) c' m' -> 
  reserve_incr r r' -> 
  reserve_separated r r' j' mleft m -> 
  corestep efsem ge c m c' m' -> 
  guarantee (inject_reserve j' r') c' m'.
Proof.
intros.
eapply guarantee_incr_alloc'; eauto.
instantiate (1 := O).
solve[hnf; auto].
Qed.

Lemma alloc_mod_alloc: 
  forall b ofs ge c m c' m' r,
  corestep efsem ge c m c' m' -> 
  guarantee r c' m' -> 
  r b ofs -> 
  Mem.valid_block m' b -> 
  ~effects efsem c AllocEffect b ofs -> 
  effects efsem c' ModifyEffect b ofs -> 
  effects efsem c' AllocEffect b ofs.
Proof.
intros until r.
intros STEP GR RR VAL NA EFM.
apply (GR _ ofs VAL RR EFM).
Qed.

Lemma rely_same_effects: 
  forall c c' m m',
  rely c m m' -> 
  (forall k b ofs, effects efsem c k b ofs <-> effects efsem c' k b ofs) -> 
  rely c' m m'.
Proof.
intros until m'; intros RELY EFSAME.
unfold rely in RELY|-*.
apply mem_unchanged_on_sub with (Q := 
  (fun b ofs => reserved m b ofs /\ effects efsem c AllocEffect b ofs)); auto.
intros b ofs [? ?]; split; auto.
solve[rewrite EFSAME; auto].
Qed.

Lemma effects_valid_after_ext: 
  forall c c' m m' rv e sig args,
  effects_valid efsem c m -> 
  at_external efsem c = Some (e, sig, args) -> 
  after_external efsem rv c = Some c' -> 
  mem_forward m m' -> 
  effects_valid efsem c' m'.
Proof.
intros until args; intros EV AT AFT FW.
intros b ofs k EF.
apply FW.
eapply EV; eauto.
rewrite <-effects_external in EF; eauto.
Qed.

Lemma reserved_separated: 
  forall m m' b ofs,
  mem_forward m m' -> 
  ~reserved m b ofs ->
  reserved m' b ofs -> 
  Mem.nextblock m <= b < Mem.nextblock m'.
Proof.
intros until ofs; intros H1 H2 H3.
destruct (Z_lt_dec b (Mem.nextblock m)); auto.
(*old block*)
destruct (H1 b) as [A [B E]]; auto.
destruct H3 as [p H3].
erewrite <-E in H3.
exfalso.
apply H2.
exists p; auto.
(*new block*)
split.
omega.
destruct H3 as [p H3].
apply Mem.perm_valid_block in H3; auto.
Qed.

Lemma effects_guarantee_after_ext: 
  forall c c' m m' rv e sig args,
  effects_guarantee efsem c m -> 
  effects_valid efsem c m -> 
  at_external efsem c = Some (e, sig, args) -> 
  after_external efsem rv c = Some c' -> 
  mem_forward m m' -> 
  effects_guarantee efsem c' m'.
Proof.
intros until args; intros GR EFVAL AT AFT FW b ofs VALID EF.
destruct (reserved_dec m b ofs).
rewrite <-effects_external; eauto.
rewrite <-effects_external in EF; eauto.
exploit reserved_separated; eauto.
intros [? ?].
rewrite <-effects_external; eauto.
rewrite <-effects_external in EF; eauto.
apply EFVAL in EF.
exfalso. unfold Mem.valid_block in EF. omega.
Qed.

Lemma effects_guarantee_preservedN: 
  forall ge c c' m m' n,
  effects_guarantee efsem c m -> 
  corestepN efsem ge n c m c' m' -> 
  effects_guarantee efsem c' m'.
Proof.
intros until n; revert c m.
induction n.
simpl.
intros.
inv H0; auto.
intros c m H1; simpl; intros [c2 [m2 [STEP STEPN]]].
apply (IHn c2 m2); auto.
eapply effects_guarantee_preserved; eauto.
Qed.

Lemma guarantee_after_ext: 
  forall (r r': reserve) c c' m m' rv e sig args,
  guarantee r c m -> 
  effects_valid efsem c m -> 
  at_external efsem c = Some (e, sig, args) -> 
  after_external efsem rv c = Some c' -> 
  mem_forward m m' -> 
  reserve_incr r r' -> 
  reserve_separated1 r r' m -> 
  reserve_valid r m ->
  guarantee r' c' m'.
Proof.
intros until args; intros GR EFVAL AT AFT FW INCR SEP VALID.
intros b ofs VAL R EF.
rewrite <-effects_external; eauto.
rewrite <-effects_external in EF; eauto.
destruct (reserve_dec r b ofs).
apply GR; auto.
specialize (SEP b ofs).
solve[eapply VALID; eauto].
specialize (SEP _ _ n R).
solve[apply EFVAL in EF; elimtype False; auto].
Qed.

Lemma guarantee_after_ext': 
  forall (r r': reserve) c c' m m' rv e sig args,
  guarantee r c m -> 
  effects_valid efsem c m -> 
  at_external efsem c = Some (e, sig, args) -> 
  after_external efsem rv c = Some c' -> 
  mem_forward m m' -> 
  reserve_incr r r' -> 
  reserve_separated1 r r' m -> 
  reserve_valid r m ->
  guarantee r c' m'.
Proof.
intros.
cut (guarantee r' c' m'). intro H7.
solve[eapply guarantee_decr; eauto].
solve[eapply guarantee_after_ext; eauto].
Qed.

Lemma guarantee'_after_ext: 
  forall (r r': reserve) j j' c c' m m' rv e sig args,
  guarantee' j r c m -> 
  effects_valid efsem c m -> 
  at_external efsem c = Some (e, sig, args) -> 
  after_external efsem rv c = Some c' -> 
  mem_forward m m' -> 
  reserve_incr r r' -> 
  reserve_separated2 r r' j' m -> 
  reserve_valid' r j m ->
  inject_incr j j' -> 
  inject_separated2 j j' m -> 
  guarantee' j' r' c' m'.
Proof.
intros until args; intros GR EFVAL AT AFT FW INCR SEP VALID INJINCR INJSEP.
intros b ofs VAL R EF.
rewrite <-effects_external; eauto.
rewrite <-effects_external in EF; eauto.
destruct R as [b0 [delta [R1 R2]]].
destruct (reserve_dec r b0 (ofs-delta)).
case_eq (j b0); [intros [b' delta'] EQ|].
assert (EQ': j b0 = Some (b, delta)).
 generalize EQ as EQ'; intro.
 apply INJINCR in EQ.
 rewrite EQ in R1.
 solve[inv R1; auto].
apply GR; auto.
specialize (SEP b ofs).
solve[eapply VALID; eauto].
solve[exists b0; exists delta; split; auto].
intros NONE.
specialize (INJSEP _ _ _ NONE R1).
elimtype False.
apply INJSEP.
solve[eapply EFVAL; eauto].
specialize (SEP _ _ n R2 _ _ R1).
solve[apply EFVAL in EF; elimtype False; auto].
Qed.

End EffectfulSemanticsLemmas.

Section ReserveLemmas.
Context {G1 C1 D1 G2 C2 D2: Type}.
Variables 
  (efsem1: EffectfulSemantics G1 C1 D2) 
  (efsem2: EffectfulSemantics G2 C2 D2).

(*This is slightly weird.*)
Lemma guarantee_left_mono: 
  forall (r1: reserve) (r2: reserve) c1 c2 f m1 m2
  (INJ: Mem.inject f m1 m2)
  (ALLOC_COVAR: forall b b0 delta ofs0,
    effects efsem1 c1 AllocEffect b0 ofs0 -> 
    f b0 = Some (b, delta) -> 
    effects efsem2 c2 AllocEffect b (ofs0 + delta))
  (RESERVED_CONTRAVAR: forall b ofs,
    r2 b ofs -> exists b0 delta, f b0 = Some (b, delta) /\ r1 b0 (ofs-delta))
  (RESERVED_ALLOCATED: forall b b0 delta ofs0,
    r1 b0 ofs0 -> 
    ~effects efsem1 c1 ModifyEffect b0 ofs0 -> 
    f b0 = Some (b, delta) -> 
    r2 b (ofs0 + delta) -> 
    effects efsem2 c2 ModifyEffect b (ofs0 + delta) -> 
    effects efsem2 c2 AllocEffect b (ofs0 + delta)),
  guarantee efsem1 r1 c1 m1 -> 
  guarantee efsem2 r2 c2 m2.
Proof.
intros until m2.
unfold guarantee; intros INJ CO CONTRA RA H1 b ofs VAL R2 EM.
destruct (CONTRA _ _ R2) as [b0 [delta [CONTRA1 CONTRA2]]].
generalize CONTRA1 as CONTRA1'; intro.
eapply Mem.valid_block_inject_1 in CONTRA1; eauto.
specialize (H1 _ _ CONTRA1 CONTRA2).
assert (EQ: ofs = ofs - delta + delta) by omega.
destruct (effects_dec efsem1 c1 ModifyEffect b0 (ofs-delta)) as [EF|NEF].
specialize (H1 EF).
specialize (CO _ _ _ _ H1 CONTRA1').
solve[rewrite EQ; auto].
rewrite EQ in R2, EM.
specialize (RA _ _ _ _ CONTRA2 NEF CONTRA1' R2 EM).
solve[rewrite EQ; auto].
Qed.

End ReserveLemmas.
