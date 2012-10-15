Add LoadPath "/home/jsseven/Downloads/ssreflect-1.3pl2" as Ssreflect.
Add LoadPath "/home/jsseven/Downloads/ssreflect-1.3pl2/theories" as Ssreflect.
Add LoadPath "/home/jsseven/Downloads/ssreflect-1.3pl2/src" as Ssreflect.

Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
(*Require Import Arith Bool List.*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* 
   This file defines a symbolic execution procedure that integrates a
   fully-automatic program analysis with human-guided proof
   exploration in Coq.

   This is achieved by splitting the analysis problem into two stages: 

   - First, we symbolically execute the program wrt. a decidable
   abstraction (eg, boolean predicates or symbolic heaps as in shape
   analysis via Separation Logic).  This is the [check] stage.

       For each assertion in the program, [check] may either succeed
   or fail.  If it succeeds, it replaces the assertion with an
   assumption of the asserted fact and continues checking the rest of
   the program.  This transformation (which communicates facts proved
   by [check] to the second stage) is justified by [check]'s
   correctness.

       If [check] fails to solve a /syntactic/ assertion, it replaces
   the failed assertion with its /semantic/ encoding, given a
   user-supplied interpretation of the atomic propositions occuring in
   the formula. In order to support this operation, the language of
   formulas contains a special constructor for injecting arbitrary
   semantic predicates.

       If [check] encounters a previously injected semantic assertion
   during symbolic execution, it continues checking the program,
   leaving the assertion unchanged. 

       When [check] completes, each assertion in the transformed
   program will be either (a) a semantic assertion; or (b) an
   assumption.

   - In the second stage, called inspection, we generate a
   characteristic Coq proposition for the program through a process
   similar to the (forward) symbolic execution of the first stage.
   The truth of this proposition, proved by the user, implies the
   safety of the program produced by [check], and by extension and 
   the correctness of [check], the safety of the original program.
*)

Section var.
Variable var : eqType. (*var is an arbitrary type with equality*)

(*formulas*)

Inductive binop : Type := Band | Bor | Bimpl.

Inductive atom : Type :=
| A : var -> atom.

Inductive fm {D : Type} : Type :=
| Ftrue
| Ffalse
| Fatom : atom -> fm
| Fbinop : binop -> fm -> fm -> fm
| Fnot : fm -> fm
(*semantic assertions, predicates on program states D*)
| Fp : forall (p : D -> Prop), fm.

Implicit Arguments fm [].

Notation Fand := (Fbinop Band).
Notation For := (Fbinop Bor).
Notation Fimpl := (Fbinop Bimpl).

Fixpoint fm_eq {D : Type} (f1 f2 : fm D) :=
  match f1, f2 with
    | Ftrue, Ftrue => true
    | Ffalse, Ffalse => true
    | Fatom (A n), Fatom (A m) => n == m
    | Fnot f1', Fnot f2' => fm_eq f1' f2'
    | Fp p, Fp q => false
    | _, _ => false
  end.

(*interpretation of formulas*)

Section interp.
Variable D : Type.

Definition atom_interp := atom -> D -> Prop.

Definition binop_interp (op : binop) := 
  match op with
    | Band => and
    | Bor => or
    | Bimpl => fun p q => p -> q
  end.

Fixpoint fm_interp (I : atom_interp) (f : fm D) (d : D) :=
  match f with
    | Ftrue => True
    | Ffalse => False
    | Fatom l => I l d
    | Fbinop op f1 f2 => 
        binop_interp op (fm_interp I f1 d) (fm_interp I f2 d)
    | Fnot f => ~ fm_interp I f d
    | Fp p => p d
  end.

Definition fm_implies I p q d := fm_interp I p d -> fm_interp I q d.

End interp.

(******************************************************************************)
(** Syntax of a simple guarded command language *)

Inductive expr : Type :=
| Eprim : var -> expr
| Ebinop : binop -> expr -> expr -> expr
| Enot : expr -> expr.

Inductive com {D : Type} : Type :=
| Cskip : com
(*assume statements can be used to simulate the behavior of primitive commands*)
| Cassume : fm D -> com
| Cassert : fm D -> com
| Cseq : com -> com -> com
| Cifte : expr -> com -> com -> com.
(*alternatively, we can simulate Cifte with nondet and assume, as in 

    Cifte e c1 c2  =  Cnondet (Cassume (expr2assn e); c1) 
                              (Cassume (expr2assn (negate e)); c2 *)

Implicit Arguments com [].

Inductive cont {D : Type} := 
| Kseq : com D -> cont -> cont
| Ksafe : cont.

Implicit Arguments cont [].

(******************************************************************************)
(** Semantics of the guarded command language *)

Section expr2assn.
Variable D : Type.

Definition binop2assn (op : binop) :=
  match op with
    | Band => @Fbinop D Band
    | Bor => Fbinop Bor
    | Bimpl => Fbinop Bimpl
  end.

Definition negate (e : expr) :=
  match e with
    | Enot e' => e'
    | _ => Enot e
  end.

Fixpoint expr2assn (e : expr) :=
  match e with
    | Eprim n => Fatom (A n)
    | Ebinop op e1 e2 => 
        binop2assn op (expr2assn e1) (expr2assn e2)
    | Enot e => Fnot (expr2assn e)
  end.

End expr2assn.

Implicit Arguments expr2assn [D].
(** general properties of step relations *)

Section step.
Variable (state : Type).

Notation cont := (@cont state).

Variable (step : state -> cont -> state -> cont -> Prop).

Inductive step_star : state -> cont -> state -> cont -> Prop :=
| step_star_refl s k : step_star s k s k
| step_star_step s k s2 k2 s' k' : 
    step s k s2 k2 -> step_star s2 k2 s' k' ->
    step_star s k s' k'.

Inductive stepN : nat -> state -> cont -> state -> cont -> Prop :=
| stepO s k : stepN O s k s k
| stepS s k s2 k2 s' k' n : 
    step s k s2 k2 -> stepN n s2 k2 s' k' -> 
    stepN (S n) s k s' k'.

Lemma step_star_stepN s k s' k' : 
  step_star s k s' k' <-> exists n, stepN n s k s' k'.
Proof.
split=>[|[n H1]].
- elim=>{s k s' k'}=>[s k|s k s2 k2 s' k' H1 H2 [n H3]]; 
[by exists O; apply: stepO|by exists (n.+1); apply: (stepS H1 H3)].
- elim: H1=>{s k s' k'}=>[s k|s k s2 k2 s' k' n' H1 H2 H3]; 
[by apply: step_star_refl|by apply: (step_star_step H1 H3)]. 
Qed.

Definition safe s k := forall s2 k2, 
  step_star s k s2 k2 -> exists s', exists k', step s2 k2 s' k'.

Definition safeN s k := forall s2 k2 n,
  stepN n s k s2 k2 -> exists s', exists k', step s2 k2 s' k'.

Lemma safe_safeN s k : safe s k <-> safeN s k.
Proof.
rewrite/safe/safeN; split=>H1 s2 k2.
- move=>n H2; case: (H1 s2 k2); first by apply/step_star_stepN; exists n.
by move=>s' [k' H3]; exists s'; exists k'.
- move/step_star_stepN=>[n' H2]; case: (H1 _ _ _ H2)=>s' [k' H3].
by exists s'; exists k'.
Qed.

Lemma safety_induction R s k : 
  (forall s k, R s k -> exists s', exists k', step s k s' k') ->
  (forall s k s' k', R s k -> step s k s' k' -> R s' k') ->
  R s k -> safe s k.
Proof.
move=>H1 H2 H3; rewrite/safe=>s2 k2/step_star_stepN=>[[n H4]].
move: s k s2 k2 H3 H4; induction n=>s k s2 k2 H3 H4. 
- by inversion H4; subst; apply: H1=>//.
- by inversion H4; subst=>{H4}; apply: (IHn s1 k1 s2 k2 (H2 _ _ _ _ H3 H0)). 
Qed.

End step.

(** simulations *)

Section simulation.
Variables (state cont : Type) 
          (R : state -> cont -> state -> cont -> Prop)
          (S T : state -> cont -> state -> cont -> Prop)
          (rank : state -> cont -> nat).

(** T simulates S *)

Definition simulates :=
  forall s1 k1 s1' k1' s2 k2, 
    R s1 k1 s2 k2 -> S s1 k1 s1' k1' -> 
    exists s2', exists k2', T s2 k2 s2' k2' /\ R s1' k1' s2' k2'.

(** T wf-simulates S, with ranking function [rank] *)

Definition wf_simulates :=
  forall s1 k1 s1' k1' s2 k2, 
    R s1 k1 s2 k2 -> S s1 k1 s1' k1' -> 
    (exists s2', exists k2', T s2 k2 s2' k2' /\ R s1' k1' s2' k2') \/
    (rank s1' k1' < rank s1 k1).

Require Import Wf_nat.

Lemma wf_simulates_steps s1 k1 s1' k1' s2 k2 : 
  wf_simulates -> 
  R s1 k1 s2 k2 -> S s1 k1 s1' k1' -> 
  exists s2', exists k2', T s2 k2 s2' k2' /\ R s1' k1' s2' k2'.
Proof.
move=>H1 H2 H3; move: H1; move/(_ s1 k1 s1' k1' s2 k2 H2 H3). 
move=>[[s2'][k2'][H4]H5|//]. by exists s2'; exists k2'.
induction (rank s1 k1)=>//.


pose P := (fun n => 
  forall s1 k1 s1' k1' s2 k2,
  (forall s1 k1 s1' k1' s2 k2, 
    R s1 k1 s2 k2 -> S s1 k1 s1' k1' -> 
    (exists s2', exists k2', T s2 k2 s2' k2' /\ R s1' k1' s2' k2') \/
    (rank s1' k1' < n)) ->
  R s1 k1 s2 k2 -> S s1 k1 s1' k1' -> 
  exists s2', exists k2', T s2 k2 s2' k2' /\ R s1' k1' s2' k2').
generalize (well_founded_ind lt_wf P). 

Print well_founded_ind.

Check lt_wf.

apply: (well_founded_ind .
admit.


move/(_ s1 k1 s1' k1').
induction (rank s1 k1). admit.


pose (rank s1 k1) as n.

move/(_ s1 k1).
induction (rank s1 k1). admit.
move=>H1 H2 H3.


induction (rank s1 k1).

move=>[[s2'][k2'][H4]H5|]. by exists s2'; exists k2'.
move=>H4. unfold n in *.

End wf_simulation.

Section wf_simulation2.
Variables (state cont : Type)
          (R : state -> cont -> state -> cont -> Prop)
          (step1 step2 : state -> cont -> state -> cont -> Prop)
          (rank : state -> cont -> nat).

Lemma wf_simulation_steps : 
  wf_simulates R step1 step2 rank -> 
  forall s1 k1 s1' k1' s2 k2, 
    R s1 k1 s2 k2 -> step1 

Section gcl_step.
Variable state : Type.
Variable I : atom_interp state.

Notation fm := (@fm state).
Notation com := (@com state).
Notation cont := (@cont state).

Inductive step : state -> cont -> state -> cont -> Prop :=
| step_Ksafe : forall s, step s Ksafe s Ksafe
| step_Cskip : forall s k, step s (Kseq Cskip k) s k
| step_Cassume : forall s k f, (*do I need excluded mid. to make this work?*)
    ~ fm_interp I f s -> step s (Kseq (Cassume f) k) s Ksafe
| step_Cassert : forall s f k, 
    fm_interp I f s -> step s (Kseq (Cassert f) k) s k
| step_Cseq : forall s k c1 c2, 
    step s (Kseq (Cseq c1 c2) k) s (Kseq c1 (Kseq c2 k))
| step_Cifte_left : forall s k e c1 c2, 
    fm_interp I (expr2assn e) s -> 
    step s (Kseq (Cifte e c1 c2) k) s (Kseq c1 k)
| step_Cifte_right : forall s k e c1 c2, 
    fm_interp I (expr2assn (negate e)) s -> 
    step s (Kseq (Cifte e c1 c2) k) s (Kseq c2 k).

End gcl_step.

Section oracle.
Variable D : Type.

Notation fm := (@fm D).
Notation com := (@com D).

(*just a placeholder: can replace this ad hoc function with a simple 
  dpll or resolution prover*)

Fixpoint oracle n (f : fm) := 
  match n with O => false | S n' => 
  match f with
    | Fimpl (Fand (Fnot f1) f2) f3 => fm_eq f1 f2
    | Fimpl (Fand f1 f2) f3 => 
        oracle n' (Fimpl f1 f3) || oracle n' (Fimpl f2 f3)
    | Fimpl f1 f2 => fm_eq f1 f2
    | Ftrue => true
    | _ => false
  end end.

Definition oracle0 := oracle 100.

End oracle.

(*stage 1*)

Section check.
Variable D : Type.

Notation fm := (@fm D).
Notation com := (@com D).

(*alien formulas contain semantic assertions [Fp p]*)

Fixpoint alien (f : fm) :=
  match f with
    | Ftrue | Ffalse | Fatom _ => false
    | Fbinop op f1 f2 => alien f1 || alien f2
    | Fnot f' => alien f'
    | Fp _ => true
  end.

Definition incon (f : fm) := oracle0 (Fimpl f Ffalse).

(*the symbolic evaluator*)

Variable I : atom_interp D.

Fixpoint check (p : fm) (c : com) (cont : fm -> com -> com) :=
  if incon p then Cskip else (*we replace inconsistent branches with skip*)
  match c with
    | Cskip => cont p Cskip
    | Cassume f => cont (Fand f p) (Cassume f)
    | Cassert f => 
        if alien f then cont p (Cassert f)
        else (if oracle0 (Fimpl p f) then cont f (Cassume f) 
              else cont p (Cassert (Fp (fm_implies I p f))))
    | Cseq c1 c2 => 
        check p c1 (fun p' c1' => check p' c2 (fun p'' c2' => 
            cont p'' (Cseq c1' c2')))
(*need to think about this rule...*)
    | Cifte e c1 c2 => 
        let: c1' := check (Fand (expr2assn e) p) c1 (fun _ c => c) in
          let: c2' := check (Fand (expr2assn (negate e)) p) c2 (fun _ c => c) in
            cont p (Cifte e c1' c2')
  end.

Definition check0 p c := check p c (fun _ c => c).

End check.

(*stage 2*)

Section inspect.
Variables (D : Type) (I : atom_interp D).

Notation fm := (@fm D).
Notation com := (@com D).

Fixpoint inspect (p : fm) (c : com) (d : D) (cont : fm -> Prop) :=
  match c with
    | Cskip => cont p 
    | Cassume f => cont (Fand f p)
    | Cassert f => fm_implies I p f d /\ cont p
    | Cseq c1 c2 => inspect p c1 d (fun p' => inspect p' c2 d cont)
    | Cifte e c1 c2 => 
        inspect (Fand (expr2assn e) p) c1 d cont /\
        inspect (Fand (expr2assn (negate e)) p) c2 d cont
  end.

Definition inspect0 p c := forall d, inspect p c d (fun _ => True).

End inspect.

Definition inspect1 {D} (I : atom_interp D) p prog := 
  inspect0 I p (check0 I p prog).

End var.

(*example*)

Require Import Arith.

Notation p0 := (Fatom (A 0)).
Notation p1 := (Fatom (A 1)).
Notation p2 := (Fatom (A 2)).
Notation p3 := (Fatom (A 3)).

(*an interpretation of the boolean predicates p0 .. p3*)

Definition I : atom_interp nat_eqType (nat * nat) :=
  fun a d => match d with (x, y) =>
    match a with
      | A 0 => (x = 1)
      | A 1 => (y = x)
      | A 2 => (y = 1)
      | A 3 => (y = 0)
      | _ => False
    end end.

(* Symbolic execution of the boolean abstraction of the program below
   yields a spurious counterexample to the assertion (y = 1), for pre-
   condition (x = 1).  

[[
   Original program:
     if (x = 1):
         y := x
     else:
         y := 0;
     assert (y = 1)

   expressed as a boolean program over the atoms p0, p1, p2, p3 under I:
     if p0: 
         p1
     else:
         p3
     assert (p2)
]]

*)

Definition prog :=
  (Cseq (Cifte (Eprim 0) (Cassume p1)
                         (Cassume p3))
        (@Cassert _ (nat*nat) p2)).

Compute check0 I p0 prog.

Goal inspect1 I p0 prog. 
vm_compute; firstorder; destruct x as (x, y); subst x; auto.
Qed.

(*an example of a program that doesn't require inspection; note that 
  the goal can be solved just using the firstorder tactic*)

Definition prog' :=
  (Cseq (Cifte (Eprim 0) (Cassume p1)
                         (Cassume p3))
        (@Cassert _ (nat*nat) p1)).

Goal inspect1 I p0 prog'. vm_compute; firstorder. Qed.

(*

A slightly more complicated program with a nested conditional:

[[
   Original program:
     if (x = 1):
         y := x;
         if (y = 1):
             y := 0
         else: 
             skip
     else:
         y := 0;
     assert (y = 1)

   expressed as a boolean program over the atoms p0, p1, p2, p3 under I:
     if p0: 
         p1
         if p2:
             p3
         else:
             skip
     else:
         p3
     assert (p2)
]]

*)

Definition prog2 :=
  (Cseq (Cifte (Eprim 0) 
               (Cseq (Cassume p1)
                     (Cifte (Eprim 2)
                            (Cassume p3)
                            (@Cskip _ (nat*nat))))
               (Cassume p3))
        (@Cassert _ (nat*nat) p3)).

Goal inspect1 I (Ftrue _) prog2.
vm_compute; firstorder; destruct x as (x, y); subst x; auto.
specialize (H H1); exfalso; auto.
Qed.




