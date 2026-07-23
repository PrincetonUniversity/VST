(**
  A Rocq 9 port of the syntax-only part of the POPL'18 lambda-Rust core
  language.

  Upstream:
    https://gitlab.mpi-sws.org/iris/lambda-rust
    commit eec05e0aa61e2e8346ab380d0930bbaca4cc1a31
    theories/lang/lang.v

  This file deliberately contains no operational semantics.  Both the
  frozen reference semantics and the new event semantics should use these
  definitions, so their equivalence proof does not need a syntactic
  translation.

  The upstream license is reproduced in LICENSE.lambda-rust.
*)

From Stdlib Require Import ZArith List String Bool.
From stdpp Require Import base strings list proof_irrel.

Import ListNotations.
Open Scope Z_scope.

Set Default Proof Using "Type".

(** Locations. *)

Definition block : Set := positive.
Definition loc : Set := (block * Z)%type.

Declare Scope lambda_rust_loc_scope.
Delimit Scope lambda_rust_loc_scope with L.
Bind Scope lambda_rust_loc_scope with loc.
Open Scope lambda_rust_loc_scope.

(** Expressions and values. *)

Inductive base_lit : Set :=
| LitPoison
| LitLoc (l : loc)
| LitInt (n : Z).

Inductive bin_op : Set :=
| PlusOp
| MinusOp
| LeOp
| EqOp
| OffsetOp.

(**
  [Na1Ord] and [Na2Ord] are retained because they occur in the reference
  semantics.  Source programs use [Na1Ord]; [Na2Ord] is an administrative
  state reached after the first half of a non-atomic access.
*)
Inductive order : Set :=
| ScOrd
| Na1Ord
| Na2Ord.

Inductive binder : Set :=
| BAnon
| BNamed (x : string).

Definition cons_binder (mx : binder) (xs : list string) : list string :=
  match mx with
  | BAnon => xs
  | BNamed x => x :: xs
  end.

Fixpoint app_binder (mxs : list binder) (xs : list string) : list string :=
  match mxs with
  | [] => xs
  | mx :: mxs => cons_binder mx (app_binder mxs xs)
  end.

Global Instance binder_eq_dec : EqDecision binder.
Proof. solve_decision. Defined.

Inductive expr : Type :=
| Var (x : string)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| App (e : expr) (el : list expr)
| Read (o : order) (e : expr)
| Write (o : order) (e1 e2 : expr)
| CAS (e0 e1 e2 : expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| Case (e : expr) (el : list expr)
| Fork (e : expr).

Fixpoint is_closed (xs : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ xs)
  | Lit _ => true
  | Rec f xl e => is_closed (cons_binder f (app_binder xl xs)) e
  | BinOp _ e1 e2
  | Write _ e1 e2
  | Free e1 e2 =>
      is_closed xs e1 && is_closed xs e2
  | App e el
  | Case e el =>
      is_closed xs e && forallb (is_closed xs) el
  | Read _ e
  | Alloc e
  | Fork e =>
      is_closed xs e
  | CAS e0 e1 e2 =>
      is_closed xs e0 && is_closed xs e1 && is_closed xs e2
  end.

Class Closed (xs : list string) (e : expr) : Prop :=
  closed : is_closed xs e.

Global Instance closed_proof_irrel xs e : ProofIrrel (Closed xs e).
Proof. unfold Closed. apply _. Qed.

Global Instance closed_decision xs e : Decision (Closed xs e).
Proof. unfold Closed. apply _. Defined.

Inductive val : Type :=
| LitV (l : base_lit)
| RecV (f : binder) (xl : list binder) (e : expr)
    (Hclosed : Closed (cons_binder f (app_binder xl [])) e).

Arguments RecV _ _ _ {_}.

Definition of_val (v : val) : expr :=
  match v with
  | LitV l => Lit l
  | RecV f xl e => Rec f xl e
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Lit l => Some (LitV l)
  | Rec f xl e =>
      match decide (Closed (cons_binder f (app_binder xl [])) e) with
      | left Hclosed => Some (RecV f xl e)
      | right _ => None
      end
  | _ => None
  end.

(** Evaluation contexts. *)

Inductive ectx_item : Type :=
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (el : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| ReadCtx (o : order)
| WriteLCtx (o : order) (e2 : expr)
| WriteRCtx (o : order) (v1 : val)
| CasLCtx (e1 e2 : expr)
| CasMCtx (v0 : val) (e2 : expr)
| CasRCtx (v0 v1 : val)
| AllocCtx
| FreeLCtx (e2 : expr)
| FreeRCtx (v1 : val)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx el => App e el
  | AppRCtx v vl el => App (of_val v) (map of_val vl ++ e :: el)
  | ReadCtx o => Read o e
  | WriteLCtx o e2 => Write o e e2
  | WriteRCtx o v1 => Write o (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | AllocCtx => Alloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | CaseCtx el => Case e el
  end.

Definition ectx := list ectx_item.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | [] => e
  | Ki :: K => fill K (fill_item Ki e)
  end.

(** Substitution. *)

Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
      Rec f xl
        (if bool_decide (BNamed x <> f /\ BNamed x ∉ xl)
         then subst x es e
         else e)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | App e el => App (subst x es e) (map (subst x es) el)
  | Read o e => Read o (subst x es e)
  | Write o e1 e2 => Write o (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  end.

Definition subst' (mx : binder) (es : expr) : expr -> expr :=
  match mx with
  | BNamed x => subst x es
  | BAnon => id
  end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr)
    : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x :: xl, es :: esl => subst' x es <$> subst_l xl esl e
  | _, _ => None
  end.

(** Operations shared by both semantics. *)

Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : base_lit :=
  LitInt (Z_of_bool b).

Definition shift_loc (l : loc) (z : Z) : loc :=
  (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : lambda_rust_loc_scope.

Definition stuck_term : expr :=
  App (Lit (LitInt 0)) [].

(** Basic facts used by the reference port and future adapters. *)

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v as [l | f xl e Hclosed]; simpl.
  - reflexivity.
  - destruct (decide (Closed (cons_binder f (app_binder xl [])) e))
      as [Hclosed' | Hnot].
    + f_equal. f_equal. apply proof_irrel.
    + contradiction.
Qed.

Lemma shift_loc_assoc l n n' :
  (l +ₗ n +ₗ n')%L = (l +ₗ (n + n'))%L.
Proof. destruct l as [b ofs]. unfold shift_loc. simpl. now rewrite Z.add_assoc. Qed.

Lemma shift_loc_0 l : (l +ₗ 0)%L = l.
Proof. destruct l as [b ofs]. unfold shift_loc. simpl. now rewrite Z.add_0_r. Qed.
