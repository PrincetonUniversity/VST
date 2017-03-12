(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import sepcomp.mem_lemmas.

(** * Core semantics *)

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

Definition val_has_type_opt' (v: option val) (ty: typ) :=
 match v with
 | None => True
 | Some v' => Val.has_type v' ty
 end.

Definition val_has_type_opt (v: option val) (sig: signature) :=
  val_has_type_opt' v (proj_sig_res sig).

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
   back into the sequential state so execution can continue.

(* Previsouly, we had additionally

   a) a type parameter [D] that stood for the type of initialization
       data, eg list (ident * globvar V).

   b) a clause [initial_mem] that characterized memories
      suitable at module entry.

But we eliminated these, since these constructs refer to PROGRAMS,
not CORES.

*)

   [initial_core] that produces the core state
      corresponding to an entry point of a module.
      The arguments are the genv, a pointer to the
      function to run, and the arguments for that function.

   The [halted] predicate indicates when a program state
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

Record CoreSemantics {G C M (*D only needed in initial_mem*):Type}: Type :=
  { (*Removed: is a propert of programs, not of cores
      initial_mem: G -> M -> D -> Prop;*)
    initial_core : G -> val -> list val -> option C;
    at_external : C -> option (external_function * signature * list val);
    after_external : option val -> C -> option C;
    halted : C -> option val;
    corestep : G -> C -> M -> C -> M -> Prop;

    corestep_not_at_external: forall ge m q m' q',
      corestep ge q m q' m' -> at_external q = None;
    corestep_not_halted: forall ge m q m' q',
      corestep ge q m q' m' -> halted q = None;
    at_external_halted_excl: forall q,
      at_external q = None \/ halted q = None;
    after_at_external_excl : forall retv q q',
      after_external retv q = Some q' -> at_external q' = None
  }.

Implicit Arguments CoreSemantics [].

(**  Multistepping *)

Section corestepN.
  Context {G C M E:Type} (Sem:CoreSemantics G C M) (ge:G).

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

Record CoopCoreSem {G C} :=
  { coopsem :> CoreSemantics G C mem;
    corestep_fwd : forall g c m c' m' (CS: corestep coopsem g c m c' m'),
      mem_forward m m'
(*;
    corestep_wdmem: forall g c m c' m' (CS: corestep coopsem g c m c' m'),
      mem_wd m -> mem_wd m'*)
   (*Doesn't make sense any longer: initial_mem is a property of program, not cores;
    initmem_wd: forall g m d, initial_mem coopsem g m d -> mem_wd m*)
}.

Implicit Arguments CoopCoreSem [].

Section CoopCoreSemLemmas.
Context {G C: Type}.
Variable coopsem: CoopCoreSem G C.

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

Lemma corestep_star_fwd: forall g c m c' m'
  (CS:corestep_star coopsem g c m c' m'),
  mem_forward m m'.
Proof.
  intros. destruct CS.
  eapply corestepN_fwd.
  apply H.
Qed.

Lemma corestep_plus_fwd: forall g c m c' m'
  (CS:corestep_plus coopsem g c m c' m'),
  mem_forward m m'.
Proof.
   intros. destruct CS.
   eapply corestepN_fwd.
   apply H.
Qed.

End CoopCoreSemLemmas.

