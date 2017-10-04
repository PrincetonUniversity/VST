(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

(* Coq development: using indirection theory to model types in l-calculus *)

(* lam_ref_tcb.v: Trusted Computing Base; note: does *not* require knot. *)

(* We use these to get some basic decidability properties on nat *)
Require Export EqNat.
(* We don't actually use any of these axioms in this file, but it's good style to say at
    the start which axioms we will use in the soundness proofs. *)
Require Import msl.Extensionality.

(* Definition of the machine *)

(* Variables *)
Definition var_t : Type := nat.

(* Addresses *)
Definition addr : Type := nat.

(* Expressions and values *)
Inductive expr : Type :=
 | Nat : forall n : nat, expr
 | Prim : forall (f:nat -> expr) (e:expr), expr
 | Var : forall n : var_t, expr
 | Loc : forall l : addr, expr
 | Lam : forall e : expr, expr (* de Bruijn notation *)
 | App : forall e1 e2 : expr, expr
 | New : forall e : expr, expr
 | Deref : forall e : expr, expr
 | Update : forall e1 e2 e3 : expr, expr. (* [e1] := e2 ; e3 *)

(* No vars greater than n in e *)
Fixpoint closed' (n : nat) (e : expr) : Prop :=
  match e with
   | Var n' => n' < n
   | Prim f e => closed' n e
   | Lam e => closed' (n + 1) e
   | Nat _ => True
   | Loc _ => True
   | App e1 e2 => closed' n e1 /\ closed' n e2
   | New e => closed' n e
   | Deref e => closed' n e
   | Update e1 e2 e3 => closed' n e1 /\ closed' n e2 /\ closed' n e3
  end.

Definition closed (e : expr) : Prop :=
  closed' 0 e.

(* We need a definition for values in the TCB so that we can define
    call-by-value semantics; also, memories only store values. *)
Definition openValue (e:expr) : Prop :=
  match e with
   | Nat _ => True
   | Loc _ => True
   | Lam _ => True
   | _ => False
  end.

Definition isValue (e : expr) : Prop :=
  closed e /\ openValue e.

Definition value : Type :=
  {v : expr | isValue v}.

(* Coerce *)
Definition val_to_exp : value -> expr :=
  @projT1 expr isValue.
Definition exp_to_val (e : expr) (H : isValue e) : value :=
  existT isValue e H.

(* A memory that explicitly tracks the boundry between used and fresh memory. *)
Definition mem : Type :=
  (nat * (addr -> value))%type.

(* Our memories permit three operations: new, deref, and update *)
Definition new (m : mem) (v : value) : (mem * addr) :=
  match m with (n, m') =>
    ((S n, fun a => if beq_nat a n then v else m' a), n)
  end.

Definition deref (m : mem) (a : addr) : value :=
  (snd m) a.

Definition update (m : mem) (a : addr) (v : value) : mem :=
  match m with (n, m') =>
    (n, fun a' => if beq_nat a a' then v else m' a')
  end.

Definition state : Type :=
  (mem * expr)%type.

(* Here we greatly simplify because of limitations to closed Lambda terms. *)
Fixpoint subst (var : var_t) (v : value) (e : expr) : expr :=
  match e with
   | Nat n => Nat n
   | Prim f e => Prim f (subst var v e)
   | Loc l => Loc l
   | Var var' => if (beq_nat var var') then val_to_exp v else Var var'
   | Lam e => Lam (subst (var + 1) v e)
   | App e1 e2 => App (subst var v e1) (subst var v e2)
   | New e => New (subst var v e)
   | Deref e => Deref (subst var v e)
   | Update e1 e2 e3 => Update (subst var v e1) (subst var v e2) (subst var v e3)
  end.

Inductive step : state -> state -> Prop :=
(* App -- standard call-by-value *)
 | st_App1 : forall m e1 e2 m' e1',
     step (m, e1) (m', e1') ->
     step (m, App e1 e2) (m', App e1' e2)
 | st_App2 : forall m e1 e2 m' e2',
     step (m, e2) (m', e2') ->
     step (m, App (Lam e1) e2) (m', App (Lam e1) e2')
 | st_App3 : forall m e1 e2,
     forall (H : isValue e2),
     step (m, App (Lam e1) e2) (m, subst 0 (exp_to_val e2 H) e1)
(* Allocation *)
 | st_New1 : forall m e m' e',
     step (m, e) (m', e') ->
     step (m, New e) (m', New e')
 | st_New2 : forall m e m' l,
     forall (H : isValue e),
     new m (exp_to_val e H) = (m', l) ->
     step (m, New e) (m', Loc l)
(* Dereference *)
 | st_Deref1 : forall m e m' e',
     step (m, e) (m', e') ->
     step (m, Deref e) (m', Deref e')
 | st_Deref2 : forall m l v,
     deref m l = v ->
     step (m, Deref (Loc l)) (m, val_to_exp v)
(* Update *)
 | st_Upd1 : forall m e1 e2 e3 m' e1',
     step (m, e1) (m', e1') ->
     step (m, Update e1 e2 e3) (m', Update e1' e2 e3)
 | st_Upd2 : forall m l e2 e3 m' e2',
     step (m, e2) (m', e2') ->
     step (m, Update (Loc l) e2 e3) (m', Update (Loc l) e2' e3)
 | st_Upd3 : forall m l e2 e3 m',
     forall (H : isValue e2),
     update m l (exp_to_val e2 H) = m' ->
     step (m, Update (Loc l) e2 e3) (m', e3)
(* Primitive *)
 | st_Prim1 : forall m m' e e' f,
     step (m, e) (m', e') ->
     step (m, Prim f e) (m', Prim f e')
 | st_Prim2 : forall m n f,
     isValue (f n) ->
     step (m, Prim f (Nat n)) (m, f n).

(* Reflexive, transitive closure of stepping *)

Inductive stepstar : state -> state -> Prop :=
  | step_refl : forall st, stepstar st st
  | step_trans: forall st1 st2 st3,
       stepstar st1 st2 ->
       stepstar st2 st3 ->
       stepstar st1 st3
  | step1 : forall st st',
       step st st' ->
       stepstar st st'.

(* Statement of safety policy *)
Definition can_step (st : state) : Prop :=
  exists st', step st st'.

Definition at_value (st : state) : Prop :=
  isValue (snd st).

Definition safe (st : state) : Prop :=
  forall st',
    stepstar st st' ->
    can_step st' \/ at_value st'.

Definition safe_prog (e:expr) : Prop :=
  forall m, safe (m, e).

(* End TCB *)

