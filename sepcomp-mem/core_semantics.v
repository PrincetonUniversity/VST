(*CompCert imports*)
(*Require Import compcert.common.Events.*)
Require Import sepcomp.Events.
(*Require Import compcert.common.Memory.*)
Require Import sepcomp.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
(*Require Import compcert.common.Globalenvs.*)
Require Import sepcomp.Globalenvs.
Require Import compcert.lib.Axioms.

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

Inductive effect_kind: Type := AllocEffect | ModifyEffect.

Local Notation "a # b" := (ZMap.get b a) (at level 1).

Definition reserved (m: mem) b ofs := exists p, Mem.perm m b ofs Res p.

Lemma reserved_dec: 
  forall m b ofs, 
  {reserved m b ofs}+{~reserved m b ofs}.
Proof.
intros.
unfold reserved.
destruct (Mem.perm_dec m b ofs Res Nonempty).
left.
exists Nonempty; auto.
right.
intros [p CONTRA].
apply n.
eapply Mem.perm_implies; eauto.
eauto with mem.
Qed.

Record EffectfulSemantics {G C D} := { 
  csem :> CoopCoreSem G C D;
  effects: C -> effect_kind -> block -> Z -> Prop;

  effects_dec: 
    forall c k b ofs, 
      {effects c k b ofs}+{~effects c k b ofs};

  effects_initial: 
    forall b ofs ge v vs c k,
      make_initial_core csem ge v vs = Some c -> 
      ~effects c k b ofs;

  effects_forward: 
    forall ge c m c' m',
      corestep csem ge c m c' m' -> 
      (forall k b ofs, effects c k b ofs -> effects c' k b ofs) /\
      mem_unchanged_on (fun b' ofs' => ~effects c' ModifyEffect b' ofs') m m';
  
  effects_backward_alloc: 
    forall b ofs ge c m c' m',
      corestep csem ge c m c' m' -> 
      (effects c' AllocEffect b ofs <->
        effects c AllocEffect b ofs \/ 
        Mem.nextblock m <= b < Mem.nextblock m'); (*b newly allocated*)

  effects_external: 
    forall b ofs c c' k retv ef sig args,
      at_external csem c = Some (ef, sig, args) -> 
      after_external csem retv c = Some c' -> 
      (effects c k b ofs <-> effects c' k b ofs); 
  
  effects_valid c m :=   
    forall b ofs k, effects c k b ofs -> Mem.valid_block m b;
  effects_valid_preserved: 
    forall ge c m c' m', 
      corestep csem ge c m c' m' -> 
      effects_valid c m -> 
      effects_valid c' m'; 

  effects_guarantee c m :=
    forall b ofs, 
      reserved m b ofs -> 
      effects c ModifyEffect b ofs -> 
      effects c AllocEffect b ofs;
  effects_guarantee_preserved:
    forall ge c m c' m',
      corestep csem ge c m c' m' -> 
      effects_guarantee c m -> 
      effects_guarantee c' m'
}.

Implicit Arguments EffectfulSemantics [].
    
