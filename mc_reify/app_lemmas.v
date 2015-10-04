Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.ExprDsimul.
Import ExprDenote.

Section Expr.

  Context {typ : Type}
          {func : Type}.
  Context {RT : RType typ}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym func}.
Locate exprD'.
Check exprD'.
  Instance Expr_expr : @Expr typ _ (@expr typ func) :=
  { exprD' := fun tus tvs e t => @exprD' _ _ _ _ _ tus tvs t e
  ; wf_Expr_acc := @wf_expr_acc typ func
(*  ; mentionsAny := mentionsAny *)
  }.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

Lemma exprD'_App_L_rw
: forall tus tvs td t e1 e2 e1D e2D,
    typeof_expr tus tvs e1 = Some (typ2 td t) ->
    exprD' tus tvs (typ2 td t) e1 = Some e1D ->
    exprD' tus tvs td e2 = Some e2D ->
    exprD' tus tvs t (App e1 e2) = Some (exprT_App e1D e2D).
Proof.
  admit.
Qed.


Lemma exprD'_App_R_rw
: forall tus tvs td t e1 e2 e1D e2D,
    typeof_expr tus tvs e2 = Some td ->
    exprD' tus tvs td e2 = Some e2D ->
    exprD' tus tvs (typ2 td t) e1 = Some e1D ->
    exprD' tus tvs t (App e1 e2) = Some (exprT_App e1D e2D).
Proof.
  admit.
Qed.

End Expr.

