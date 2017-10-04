Load loadpath.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import VST.msl.base msl.sepalg VST.msl.sepalg_generators msl.Axioms
               VST.msl.predicates_sa.
Require Import veristar.datatypes veristar.clauses veristar.model_type veristar.list_denote.

(** The abstract separation logic model, parameterized by a separation logic
   implementation, VeriStarLogic *)

Module Type VERISTAR_MODEL.
Declare Module VeriStarLogic : VERISTAR_LOGIC.
Import VeriStarLogic.

Inductive lseg : val -> val -> heap -> Prop :=
| lseg_nil : forall x s, identity s -> nil_or_loc x -> lseg x x s
| lseg_cons : forall x x' y s h0 h1 z,
  x<>y -> val2loc x = Some x' ->
  rawnext x' z h0 -> lseg z y h1 -> join h0 h1 s ->
  lseg x y s.

Axiom rawnext2rawnext' : forall {x y h}, rawnext x y h -> rawnext' x y h.

Notation stack := env.

Instance Join_stack : Join stack := Join_equiv stack.
Instance Perm_stack : Perm_alg stack := Perm_equiv stack.
Instance Sep_stack : Sep_alg stack := Sep_equiv stack.
Instance Canc_stack : Canc_alg stack := Canc_equiv stack.

Definition stack_get (s : stack) (x : option var) : val :=
  match x with
  | Some i => env_get s i
  | None => empty_val
  end.

Definition upd_stack (x : var) (v : val) (s : stack) : stack :=
 env_set x v s.

Axiom stack_nil : forall s : stack, stack_get s None = empty_val.

(*Definition empstack : stack := empty_env.
Axiom emp_stack : forall (x : option var), stack_get empstack x = empty_val.*)

Inductive state := State: forall (s: stack) (h: heap), state.

Definition stk (st : state) := match st with State s h => s end.

Definition hp  (st : state) := match st with State s h => h end.

Instance Join_state : Join state :=
   fun (s1 s2 s3 : state) =>
    join (stk s1) (stk s2) (stk s3) /\ join (hp s1) (hp s2) (hp s3).

Definition state_bij: bijection (heap * stack) state.
Proof.
apply (Bijection _ _
             (fun w => State (snd w) (fst w) )
             (fun w => (hp w, stk w))); intros; destruct x; auto.
Defined.

Axiom join_state_eq:
  Join_state = Join_bij _ _ _ state_bij.

Declare Instance Perm_state: Perm_alg state.
Declare Instance Sep_state: Sep_alg state.
Declare Instance Canc_state: Canc_alg state.

Definition expr_denote (e : expr) (s : state) : val :=
  match e with Nil => nil_val | Var x => stack_get (stk s) (Some x) end.

Definition var_eq (x y : expr) (s : state) := expr_denote x s = expr_denote y s.
Hint Unfold var_eq : spred.
Infix "===" := var_eq (at level 35, no associativity).

Axiom var_eq_refl : forall x s, (x === x) s.

Axiom var_eq_trans : forall x y z s, (x === y) s -> (y === z) s -> (x === z) s.

Axiom var_eq_sym : forall x y s, (x === y) s -> (y === x) s.

Axiom var_eq_sym' : forall x y, (x === y) = (y === x).

Notation spred := (state -> Prop).

Definition neg (P : spred) : spred := fun s : state => ~P s.
Hint Unfold neg : spred.

Axiom empstate_empheap: forall (s:state), emp s <-> emp (hp s).

Definition pn_atom_denote (a : pn_atom) : spred :=
  match a with Equ e1 e2 => e1 === e2 | Nequ e1 e2 => neg (e1 === e2) end.

Definition pure_atom_denote (a : pure_atom) : spred :=
  match a with Eqv e1 e2 => e1 === e2 end.

Definition space_atom_denote (a : space_atom) : spred :=
  match a with
  | Next x y =>
      fun s => match val2loc (expr_denote x s) with
      | Some l' =>  rawnext l' (expr_denote y s) (hp s)
                          /\ nil_or_loc (expr_denote y s)
      | None => False
      end
  | Lseg x y =>
      fun s => lseg (expr_denote x s) (expr_denote y s) (hp s)
  end.

Definition space_denote (sigma : list space_atom) : spred :=
  list_denote space_atom_denote sepcon emp sigma.

Definition clause_denote (c : clause) : spred := fun s : state =>
  match c with
  | PureClause p p' _ _ =>
      list_denote pure_atom_denote (@andp state) TT p s ->
      list_denote pure_atom_denote (@orp state) FF p' s
  | NegSpaceClause p space p' =>
      list_denote pure_atom_denote (@andp state) (space_denote space) p s ->
      list_denote pure_atom_denote (@orp state) FF p' s
  | PosSpaceClause p p' space' =>
      list_denote pure_atom_denote (@andp state) TT p s ->
      list_denote pure_atom_denote (@orp state) (space_denote space') p' s
  end.

Definition assertion_denote (f : assertion) : spred :=
  match f with Assertion pi space =>
    let sd := space_denote space in
    list_denote pn_atom_denote (@andp state) sd pi
  end.

Definition entailment_denote (e : entailment) : Prop :=
  match e with
  | Entailment F G => assertion_denote F |-- assertion_denote G
  end.

Axiom var_nil_or_loc : forall (z : var) (e : env), nil_or_loc (env_get e z).

End VERISTAR_MODEL.

(* implementation *)

Module VeriStarModel (VSLog : VERISTAR_LOGIC) : VERISTAR_MODEL
  with Module VeriStarLogic := VSLog.

Module VeriStarLogic := VSLog. Import VSLog.

Inductive lseg : val -> val -> heap -> Prop :=
| lseg_nil : forall x s, identity s -> nil_or_loc x -> lseg x x s
| lseg_cons : forall x x' y s h0 h1 z,
  x<>y -> val2loc x = Some x' ->
  rawnext x' z h0 -> lseg z y h1 -> join h0 h1 s ->
  lseg x y s.

Lemma rawnext2rawnext' : forall {x y h}, rawnext x y h -> rawnext' x y h.
Proof.
intros; destruct (join_ex_units h) as [eh ?]; exists h; split; eauto.
apply join_sub_refl.
Qed.

Lemma var_nil_or_loc : forall (z : var) (e : env), nil_or_loc (env_get e z).
Proof.
intros; remember (env_get e z) as v.
generalize vars_defined_locs as H1; intro.
spec H1 z e. destruct H1 as [v' [H2 H3]].
solve[subst; auto].
Qed.

Notation stack := env.

Instance Join_stack : Join stack := Join_equiv stack.
Instance Perm_stack : Perm_alg stack := Perm_equiv stack.
Instance Sep_stack : Sep_alg stack := Sep_equiv stack.
Instance Canc_stack : Canc_alg stack := Canc_equiv stack.

Definition stack_get (s: stack) (x: option var) : val :=
  match x with
  | Some i => env_get s i
  | None => empty_val
  end.

Definition upd_stack (x : var) (v : val) (s : stack) : stack :=
  env_set x v s.

Lemma stack_nil : forall s : stack, stack_get s None = empty_val.
Proof. reflexivity. Qed.

(*Definition empstack : stack := empty_env.

Lemma emp_stack : forall (x : option var), stack_get empstack x = empty_val.
Proof. unfold stack_get; intros. destruct x; auto. apply env_gempty. Qed.*)

Inductive state := State: forall (s: stack) (h: heap), state.

Definition stk (st : state) := match st with State s h => s end.

Definition hp  (st : state) := match st with State s h => h end.

Instance Join_state : Join state :=
   fun (s1 s2 s3 : state) =>
    join (stk s1) (stk s2) (stk s3) /\ join (hp s1) (hp s2) (hp s3).

Definition state_bij: bijection (heap * stack) state.
Proof.
apply (Bijection _ _
             (fun w => State (snd w) (fst w) )
             (fun w => (hp w, stk w))); intros; destruct x; auto.
Defined.

Lemma join_state_eq:
  Join_state = Join_bij _ _ _ state_bij.
Proof.
extensionality w1 w2 w3; simpl.
destruct w1; destruct w2; destruct w3; simpl.
apply prop_ext; split; intros [? ?]; split; auto.
Qed.

Instance Perm_state: Perm_alg state.
  Proof. rewrite join_state_eq;
     apply Perm_bij; auto with typeclass_instances.
  Qed.

Instance Sep_state: Sep_alg state.
  Proof. rewrite join_state_eq;
     apply Sep_bij; auto with typeclass_instances.
  Defined.

Instance Canc_state: Canc_alg state.
  Proof. rewrite join_state_eq;
     apply Canc_bij; auto with typeclass_instances.
  Qed.

Definition expr_denote (e : expr) (s : state) : val :=
  match e with Nil => nil_val | Var x => stack_get (stk s) (Some x) end.

Definition var_eq (x y : expr) (s : state) := expr_denote x s = expr_denote y s.
Hint Unfold var_eq : spred.

Infix "===" := var_eq (at level 35, no associativity).

Lemma var_eq_refl : forall x s, (x === x) s.
Proof. unfold var_eq; intros; auto. Qed.

Lemma var_eq_trans : forall x y z s, (x === y) s -> (y === z) s -> (x === z) s.
Proof. unfold var_eq; intros. transitivity (expr_denote y s); auto. Qed.

Lemma var_eq_sym : forall x y s, (x === y) s -> (y === x) s.
Proof. unfold var_eq; intros. auto. Qed.

Lemma var_eq_sym' : forall x y, (x === y) = (y === x).
Proof. intros; extensionality s; apply prop_ext; split; apply var_eq_sym. Qed.

Notation spred := (state -> Prop).

Lemma empstate_empheap : forall (s:state), emp s <-> emp (hp s).
Proof.
intros; rewrite identity_unit_equiv; unfold unit_for; simpl.
rewrite identity_unit_equiv; unfold unit_for; simpl.
unfold join, Join_state; intuition; constructor; auto.
Qed.

Definition neg (P : spred) : spred := fun s : state => ~P s.
Hint Unfold neg : spred.

Definition pn_atom_denote (a : pn_atom) : spred :=
  match a with Equ e1 e2 => e1 === e2 | Nequ e1 e2 => neg (e1 === e2) end.

Definition pure_atom_denote (a : pure_atom) : spred :=
  match a with Eqv e1 e2 => e1 === e2 end.

Definition space_atom_denote (a : space_atom) : spred :=
  match a with
  | Next x y =>
      fun s => match val2loc (expr_denote x s) with
      | Some l' =>  rawnext l' (expr_denote y s) (hp s)
                          /\ nil_or_loc (expr_denote y s)
      | None => False
      end
  | Lseg x y =>
      fun s => lseg (expr_denote x s) (expr_denote y s) (hp s)
  end.

Definition space_denote (sigma : list space_atom) : spred :=
  list_denote space_atom_denote sepcon emp sigma.

Definition clause_denote (c : clause) : spred := fun s : state =>
  match c with
  | PureClause p p' _ _ =>
      list_denote pure_atom_denote (@andp state) TT p s ->
      list_denote pure_atom_denote (@orp state) FF p' s
  | NegSpaceClause p space p' =>
      list_denote pure_atom_denote (@andp state) (space_denote space) p s ->
      list_denote pure_atom_denote (@orp state) FF p' s
  | PosSpaceClause p p' space' =>
      list_denote pure_atom_denote (@andp state) TT p s ->
      list_denote pure_atom_denote (@orp state) (space_denote space') p' s
  end.

Definition assertion_denote (f : assertion) : spred :=
  match f with Assertion pi space =>
    let sd := space_denote space in
    list_denote pn_atom_denote (@andp state) sd pi
  end.

Definition entailment_denote (e : entailment) : Prop :=
  match e with
  | Entailment F G => assertion_denote F |-- assertion_denote G
  end.

End VeriStarModel.

