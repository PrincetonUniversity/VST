(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import sepcomp.mem_lemmas.

(** A "core semantics represents" a fairly traditional, sequential,
   small step semantics of computation.  They are designed to
   cooperate with "extensions" which give semantics to primtive
   constructs not defined by the extensible semantics (e.g., external
   function calls).

   The [G] type parameter is the type of global environments, the type
   [C] is the type of core states, and the type [E] is the type of
   extension requests.  The [at_external] function gives a way to
   determine when the sequential execution is blocked on an extension
   call, and to extract the data necessary to execute the call.
   [after_external] give a way to inject the extension call results
   back into the sequential state so execution can continue.  The type
   parameter [D] stands for the type of initialization data, eg list
   (ident * globvar V).

   [make_initial_core] produces the core state corresponding
   to an entry point of the program/module.  The arguments are the
   program's genv, a pointer to the function to run, and
   the arguments for that function.

   The [safely_halted] predicate indicates when a program state
   has reached a halted state, and what it's exit code/return value is
   when it has reached such a state.

   [corestep] is the fundamental small-step relation for
   the sequential semantics.

   The remaining properties give basic sanity properties which constrain
   the behavior of programs.
    1) a state cannot be both blocked on an extension call
        and also step,
    2) a state cannot both step and be halted
    3) a state cannot both be halted and blocked on an external call
    4) after external calls, cores are back in a "runnable" state
       (NOTE: this axiom may be removed at some point) *)

Record CoreSemantics {G C M D:Type}: Type :=
  { initial_mem: G -> M -> D -> Prop;
    make_initial_core : G -> val -> list val -> option C;
    at_external : C -> option (external_function * signature * list val);
    after_external : option val -> C -> option C;
    safely_halted : C -> option val; 
    corestep : G -> C -> M -> C -> M -> Prop;

    corestep_not_at_external: forall ge m q m' q', 
      corestep ge q m q' m' -> at_external q = None;
    corestep_not_halted: forall ge m q m' q', 
      corestep ge q m q' m' -> safely_halted q = None;
    at_external_halted_excl: forall q, 
      at_external q = None \/ safely_halted q = None;
    after_at_external_excl : forall retv q q',
      after_external retv q = Some q' -> at_external q' = None
  }.

Implicit Arguments CoreSemantics [].

(**  Multistepping *)

Section corestepN.
  Context {G C M E D:Type} (Sem:CoreSemantics G C M D) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
      | O => fun c m c' m' => (c,m) = (c',m')
      | S k => fun c1 m1 c3 m3 => exists c2, exists m2,
        corestep Sem ge c1 m1 c2 m2 /\
        corestepN k c2 m2 c3 m3
    end.

  Lemma corestepN_add : forall n m c1 m1 c3 m3,
    corestepN (n+m) c1 m1 c3 m3 <->
    exists c2, exists m2,
      corestepN n c1 m1 c2 m2 /\
      corestepN m c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m x x0 c3 m3).
    apply H in H2. 
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m x1 x2 c3 m3). 
    eauto.
  Qed.

  Definition corestep_plus c m c' m' :=
    exists n, corestepN (S n) c m c' m'.

  Definition corestep_star c m c' m' :=
    exists n, corestepN n c m c' m'.

  Lemma corestep_plus_star : forall c1 c2 m1 m2,
    corestep_plus c1 m1 c2 m2 -> corestep_star c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma corestep_plus_trans : forall c1 c2 c3 m1 m2 m3,
    corestep_plus c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 -> 
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add (S n1) (S n2) c1 m1 c3 m3) as [_ H].
    eexists. apply H. exists c2. exists m2. split; assumption.
  Qed.

  Lemma corestep_star_plus_trans : forall c1 c2 c3 m1 m2 m3,
    corestep_star c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 -> 
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add n1 (S n2) c1 m1 c3 m3) as [_ H]. 
    rewrite <- plus_n_Sm in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_plus_star_trans: forall c1 c2 c3 m1 m2 m3,
    corestep_plus c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 -> 
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add (S n1) n2 c1 m1 c3 m3) as [_ H]. 
    rewrite plus_Sn_m in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_star_trans: forall c1 c2 c3 m1 m2 m3, 
    corestep_star c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 -> 
    corestep_star c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add n1 n2 c1 m1 c3 m3) as [_ H]. 
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_plus_one: forall c m c' m',
    corestep  Sem ge c m c' m' -> corestep_plus c m c' m'.
  Proof. intros. unfold corestep_plus, corestepN. simpl.
    exists O. exists c'. exists m'. eauto. 
  Qed.

  Lemma corestep_plus_two: forall c m c' m' c'' m'',
    corestep  Sem ge c m c' m' -> corestep  Sem ge c' m' c'' m'' -> 
    corestep_plus c m c'' m''.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. 
    exists c''. exists m''. split; trivial. reflexivity.
  Qed.

  Lemma corestep_star_zero: forall c m, corestep_star  c m c m.
  Proof. intros. exists O. reflexivity. Qed.

  Lemma corestep_star_one: forall c m c' m',
    corestep  Sem ge c m c' m' -> corestep_star c m c' m'.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. reflexivity. 
  Qed.

  Lemma corestep_plus_split: forall c m c' m',
    corestep_plus c m c' m' ->
    exists c'', exists m'', corestep  Sem ge c m c'' m'' /\ 
      corestep_star c'' m'' c' m'.
  Proof. intros.
    destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*. 
    exists c2. exists m2. split. assumption. exists n. assumption.  
  Qed.

End corestepN.

(** "Cooperating" semantics impose additional constraints; in particular, 
   they require that the memories produced by coresteps contain no dangling 
   pointers. *)

Record CoopCoreSem {G C D} :=
  { coopsem :> CoreSemantics G C mem D;
    corestep_fwd : forall g c m c' m' (CS: corestep coopsem g c m c' m'), 
      mem_forward m m';
    corestep_wdmem: forall g c m c' m' (CS: corestep coopsem g c m c' m'), 
      mem_wd m -> mem_wd m';
    initmem_wd: forall g m d, initial_mem coopsem g m d -> mem_wd m }.

Implicit Arguments CoopCoreSem [].

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
eapply external_call_max_perm; eauto.
Qed.

Inductive effect_kind: Type := AllocEffect | ModifyEffect.

Record EffectfulSemantics {G C D} :=
  { csem :> CoopCoreSem G C D;
    effects: C -> effect_kind -> block -> Z -> Prop;
    effects_dec: forall c k b ofs, 
      {effects c k b ofs}+{~effects c k b ofs};
    effects_initial: forall b ofs ge v vs c k,
      make_initial_core csem ge v vs = Some c -> 
      ~effects c k b ofs;
    effects_forward: forall b ofs ge c m c' m' k,
      corestep csem ge c m c' m' -> 
      effects c k b ofs -> 
      effects c' k b ofs /\
      mem_unchanged_on (fun b' ofs' => ~effects c' ModifyEffect b' ofs') m m';
    effects_backward_alloc: forall b ofs ge c m c' m',
      corestep csem ge c m c' m' -> 
      (effects c' AllocEffect b ofs <->
        effects c AllocEffect b ofs \/ 
        Mem.nextblock m <= b < Mem.nextblock m'); (*b newly allocated*)
    effects_external: forall b ofs c c' k retv ef sig args,
      at_external csem c = Some (ef, sig, args) -> 
      after_external csem retv c = Some c' -> 
      (effects c k b ofs <-> effects c' k b ofs)}.

Implicit Arguments EffectfulSemantics [].

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

Definition effects_valid c m := 
  forall b ofs k, 
  effects efsem c k b ofs -> 
  Mem.valid_block m b.

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

Definition reserve := block -> Z -> Prop.

Record reserve' := {sort :> block -> Z -> Prop;
                    _ : forall b ofs, {sort b ofs}+{~sort b ofs}}.

Lemma reserve_dec: 
  forall r: reserve', 
  forall b ofs, {r b ofs}+{~r b ofs}.
Proof. destruct r; auto. Qed.

Definition inject_reserve (f: meminj) (r: reserve): reserve :=
  fun b ofs => exists b0 delta, 
    f b0 = Some (b, delta) /\ r b0 (ofs-delta).

Definition inject_reserve' (f: meminj) (r: reserve'): reserve'.
  destruct r as [res Hres]. 
  apply (Build_reserve' (inject_reserve f res)).
  intros. 
Admitted. (*TODO*) 

Definition reserve_incr (r1 r2: reserve) :=
  forall b ofs, r1 b ofs -> r2 b ofs.

Lemma reserve_incr_trans: forall r1 r2 r3,
   reserve_incr r1 r2 -> reserve_incr r2 r3 -> reserve_incr r1 r3.
Proof. intros. intros b. intros. apply H0. apply H. apply H1. Qed.

Definition reserve_valid (r: reserve) (m: mem) :=
  forall b ofs, r b ofs -> Mem.valid_block m b.

Definition reserve_valid_right (r: reserve) (f: meminj) (m: mem) :=
  reserve_valid (inject_reserve f r) m.

Lemma reserve_valid_right_unpack: 
  forall r f m,
  reserve_valid_right r f m -> 
  forall b b2 delta ofs, r b ofs -> f b = Some (b2, delta) -> Mem.valid_block m b2.
Proof.
unfold reserve_valid_right, inject_reserve, reserve_valid.
intros r f m H1 b b2 delta ofs R F.
specialize (H1 b2 (ofs+delta)).
apply H1.
exists b, delta.
split; auto.
assert (ofs + delta - delta = ofs) as -> by omega; auto.
Qed.

Definition reserve_separated1 (r r': reserve) m := 
  forall b ofs, ~r b ofs -> r' b ofs -> ~Mem.valid_block m b.

Definition reserve_separated (r r': reserve) (f': meminj) (m1 m2: mem) :=
  forall b1 ofs, 
    ~r b1 ofs -> r' b1 ofs -> 
    ~Mem.valid_block m1 b1 /\ 
    (forall delta b2, f' b1 = Some (b2, delta) -> ~Mem.valid_block m2 b2).

(*requires decidability of r?*)
Lemma reserve_separated_trans: 
  forall r0 (r r': reserve') j j' m1 m2 m1' m2',
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

Definition rely (r: reserve) (c: C) (m m': mem) := 
  mem_unchanged_on (fun b ofs => 
    r b ofs /\ effects efsem c AllocEffect b ofs) m m'.

(** A core "guarantees" not to touch those locations that are globally
 reserved and not alloc'd by this core. *)

Definition guarantee (r: reserve) (c: C) (m: mem) :=
  forall b ofs, 
  Mem.valid_block m b -> 
  r b ofs -> 
  effects efsem c ModifyEffect b ofs -> 
  effects efsem c AllocEffect b ofs.

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
destruct EF as [EF _].
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

Lemma guarantee_incr: 
  forall (r r': reserve') c m,
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

Lemma guarantee_decr:
  forall r r' c m,
  guarantee r' c m -> 
  reserve_incr r r' -> 
  guarantee r c m.
Proof. intros until m; intros G1 R1 b ofs VAL R2 EFM; auto. Qed.

Lemma guarantee_decr2:
  forall r r' j j' c m,
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
  forall ge (r r2: reserve') c m c2 m2 c' m' n,
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

(*BEGIN DEPRECATED
(** Guarantee transitivity theorems *)

Lemma guarantee_trans:
  forall m2 m2' m3 m3' f1 (r1: reserve) f2 (r2: reserve) c1 c2,
  (forall b0 b delta ofs0, 
     guarantee_left efsem1 r1 c1 b0 ofs0 -> f1 b0 = Some (b, delta) -> 
     guarantee_left efsem2 r2 c2 b (ofs0 + delta)) -> 
  mem_unchanged_on (guarantee_right efsem1 f1 r1 c1) m2 m2' -> 
  mem_unchanged_on (guarantee_right efsem2 f2 r2 c2) m3 m3' -> 
  mem_unchanged_on (guarantee_right efsem1 (compose_meminj f1 f2) r1 c1) m3 m3'.
Proof.

Lemma guarantee_right_trans:
  forall m2 m2' m3 m3' f1 (r1: reserve) f2 (r2: reserve) c1 c2,
  (forall b0 b delta ofs0, 
     guarantee_left efsem1 r1 c1 b0 ofs0 -> f1 b0 = Some (b, delta) -> 
     guarantee_left efsem2 r2 c2 b (ofs0 + delta)) -> 
  mem_unchanged_on (guarantee_right efsem1 f1 r1 c1) m2 m2' -> 
  mem_unchanged_on (guarantee_right efsem2 f2 r2 c2) m3 m3' -> 
  mem_unchanged_on (guarantee_right efsem1 (compose_meminj f1 f2) r1 c1) m3 m3'.
Proof.
intros until c2; intros H0 H1 H2.
apply mem_unchanged_on_sub with (Q := guarantee_right efsem2 f2 r2 c2); auto.
intros b ofs H4.
unfold guarantee_right in H4|-*.
destruct H4 as [b0 [delta [H4 H5]]].
unfold compose_meminj in H4.
case_eq (f1 b0).
intros [b1 delta1] Heq1.
rewrite Heq1 in H4.
exists b1.
case_eq (f2 b1).
intros [b2 delta2] Heq2.
rewrite Heq2 in H4.
inv H4.
exists delta2.
split; auto.
specialize (H0 _ _ _ _ H5 Heq1).
solve[assert (ofs - (delta1+delta2) + delta1 = ofs - delta2) as <- by omega; auto].
intros Heq; rewrite Heq in H4; congruence.
intros Heq; rewrite Heq in H4; congruence.
Qed.

Lemma guarantee_right_trans_EI:
  forall m2 m2' m3 m3' (r1: reserve) f2 (r2: reserve) c1 c2,
  (forall b0 ofs0, 
    guarantee_left efsem1 r1 c1 b0 ofs0 -> 
    guarantee_left efsem2 r2 c2 b0 ofs0) -> 
  mem_unchanged_on (guarantee_right efsem1 inject_id r1 c1) m2 m2' -> 
  mem_unchanged_on (guarantee_right efsem2 f2 r2 c2) m3 m3' -> 
  mem_unchanged_on (guarantee_right efsem1 f2 r1 c1) m3 m3'.
Proof.
intros.
specialize (guarantee_right_trans m2 m2' m3 m3' inject_id r1 f2 r2 c1 c2); intros H2.
destruct H2; auto.
intros until ofs0; intros H2 H3.
unfold inject_id in H3; inv H3.
solve[assert (ofs0+0 = ofs0) as -> by omega; auto].
assert (f2 = compose_meminj inject_id f2) as Heq.
 unfold inject_id, compose_meminj; hnf.
 extensionality b.
 destruct (f2 b); auto.
 solve[destruct p; auto].
solve[rewrite Heq; split; intros; auto].
Qed.

Lemma guarantee_right_trans_IE:
  forall m2 m2' m3 m3' f1 (r1: reserve) (r2: reserve) c1 c2,
  (forall b0 b delta ofs0, 
     guarantee_left efsem1 r1 c1 b0 ofs0 -> f1 b0 = Some (b, delta) -> 
     guarantee_left efsem2 r2 c2 b (ofs0 + delta)) -> 
  mem_unchanged_on (guarantee_right efsem1 f1 r1 c1) m2 m2' -> 
  mem_unchanged_on (guarantee_right efsem2 inject_id r2 c2) m3 m3' -> 
  mem_unchanged_on (guarantee_right efsem1 f1 r1 c1) m3 m3'.
Proof.
intros.
specialize (guarantee_right_trans m2 m2' m3 m3' f1 r1 inject_id r2 c1 c2); intros H2.
destruct H2; auto.
assert (f1 = compose_meminj f1 inject_id) as Heq.
 unfold inject_id, compose_meminj; hnf.
 extensionality b.
 destruct (f1 b); auto.
 destruct p; auto.
 solve[do 2 f_equal; auto; omega].
solve[rewrite Heq; split; intros; auto].
Qed.

Lemma guarantee_right_trans_EE:
  forall m2 m2' m3 m3' (r1: reserve) (r2: reserve) c1 c2,
  (forall b0 ofs0, 
    guarantee_left efsem1 r1 c1 b0 ofs0 -> 
    guarantee_left efsem2 r2 c2 b0 ofs0) -> 
  mem_unchanged_on (guarantee_right efsem1 inject_id r1 c1) m2 m2' -> 
  mem_unchanged_on (guarantee_right efsem2 inject_id r2 c2) m3 m3' -> 
  mem_unchanged_on (guarantee_right efsem1 inject_id r1 c1) m3 m3'.
Proof.
intros.
specialize (guarantee_right_trans m2 m2' m3 m3' inject_id r1 inject_id r2 c1 c2); intros H2.
destruct H2; auto.
intros until ofs0; intros H2 H3.
unfold inject_id in H3; inv H3.
solve[assert (ofs0+0 = ofs0) as -> by omega; auto].
assert (inject_id = compose_meminj inject_id inject_id) as Heq.
 unfold inject_id, compose_meminj; hnf.
 extensionality b.
 solve[f_equal; auto; omega].
solve[rewrite Heq; split; intros; auto].
Qed.

End ReserveLemmas.

Definition blockmap := block -> Z -> bool.

Section RelyGuaranteeSemanticsFunctor.
Context {G C D: Type}.
Variable csem: CoopCoreSem G C D.

Definition rg_step (ge: G) (x: blockmap*C) (m: mem) (x': blockmap*C) (m': mem) :=
  match x, x' with (f, c), (f', c') => 
    corestep csem ge c m c' m' /\
    (forall b ofs, f' b ofs=true -> f b ofs=true \/ Mem.nextblock m <= b < Mem.nextblock m')
  end.

Program Definition RelyGuaranteeCoreSem: CoreSemantics G (blockmap*C) mem D :=
  Build_CoreSemantics G (blockmap*C) mem D 
    (*initial mem*)
    (initial_mem csem)
    (*make_initial_core*)
    (fun ge v vs => match make_initial_core csem ge v vs with
                    | Some c => Some (fun _ _ => false, c)
                    | None => None
                    end)
    (*at_external*)
    (fun x => at_external csem (snd x))
    (*after_external*)
    (fun retv x => match after_external csem retv (snd x) with
                   | Some c => Some (fst x, c)
                   | None => None
                   end)
    (*safely_halted*)
    (fun x => safely_halted csem (snd x))
    (*corestep*)
    rg_step
    _ _ _ _.
Next Obligation.
destruct H as [H1 H2]; apply corestep_not_at_external in H1; auto.
Qed.
Next Obligation.
destruct H as [H1 H2]; apply corestep_not_halted in H1; auto.
Qed.
Next Obligation. apply (at_external_halted_excl csem c). Qed.
Next Obligation. 
simpl in H.
case_eq (after_external csem retv c0); intros. 
rewrite H0 in H; inv H.
apply after_at_external_excl in H0; auto.
rewrite H0 in H; congruence.
Qed.

Lemma rg_csem:
  forall ge c f m c' f' m',
  corestep RelyGuaranteeCoreSem ge (f, c) m (f', c') m' -> 
  corestep csem ge c m c' m'.
Proof.
intros until m'; intros H1.
inv H1.
auto.
Qed.

Program Definition RelyGuaranteeCoopSem: CoopCoreSem G (blockmap*C) D :=
  Build_CoopCoreSem G (blockmap*C) D 
    RelyGuaranteeCoreSem _ _ _.
Next Obligation.
inv CS.
apply corestep_fwd in H; auto.
Qed.
Next Obligation.
inv CS.
apply corestep_wdmem in H0; auto.
Qed.
Next Obligation.
apply initmem_wd in H.
auto.
Qed.

Program Definition Efsemantics: RelyGuaranteeSemantics G (blockmap*C) D :=
  Build_RelyGuaranteeSemantics G (blockmap*C) D
   RelyGuaranteeCoopSem
   (fun x b ofs => fst x b ofs = true) _ _ _ _.
Next Obligation.
simpl.
destruct (b0 b).
left; auto.
right; auto.
Qed.
Next Obligation. 
simpl.
destruct (make_initial_core csem ge v vs).
inv H; auto.
congruence.
Qed.
Next Obligation. 
destruct H; auto. Qed.
Next Obligation. 
simpl in *|-*; destruct (after_external csem retv c); try solve[congruence].
Qed.

End RelyGuaranteeSemanticsFunctor.
END DEPRECATED*)