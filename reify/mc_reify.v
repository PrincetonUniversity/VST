Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.ExprCore.
Require Import mctypes.



Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Declare Patterns patterns_vst_typ := typ.
Reify Declare Patterns patterns_vst := (ExprCore.expr typ func).

Reify Declare Syntax reify_vst_typ :=
  { (@Patterns.CPatterns _ patterns_vst_typ (@Patterns.CFail typ)) }.
Reify Declare Syntax reify_vst :=
  { (@Patterns.CPatterns _ patterns_vst
    (@Patterns.CApp _ (@ExprCore.App typ func)
    (@Patterns.CAbs (expr typ func) reify_vst_typ (@ExprCore.Abs typ func)
    (@Patterns.CVar (expr typ func) (@ExprCore.Var typ func)
    (@Patterns.CFail (expr typ func))))))
}.

Reify Pattern patterns_vst_typ += (!!Values.val) => tyval.
Reify Pattern patterns_vst_typ += (@RImpl (?0) (?1)) => 
       (fun (a b : Patterns.function reify_vst_typ) => tyArr a b). 
Reify Pattern patterns_vst_typ += (!!list_dt.listspec @ ?!0 @ ?!1 ) =>
       (fun (a : id Ctypes.type) (b : id AST.ident) => tylistspec a b).
Reify Pattern patterns_vst_typ += (!!AST.ident) => tyident.
Reify Pattern patterns_vst_typ += (!!expr.environ) => tyenviron.
Reify Pattern patterns_vst_typ += (!!shares.share) => tyshare.
Reify Pattern patterns_vst_typ += (!!list @ ?0) =>
       (fun (a : Patterns.function reify_vst_typ) => tylist a).
Reify Pattern patterns_vst_typ += (!!expr.mpred) => tympred.

Reify Pattern patterns_vst += (!!expr.eval_id) => (Inj (typ:=typ) feval_id). 
Reify Pattern patterns_vst += (!!seplog.derives) => (Inj (typ := typ) fderives).
Reify Pattern patterns_vst += (!!@map @ ?0) => (fun (a : function reify_vst_typ) => Inj (typ := typ) (fmap a)).
Reify Pattern patterns_vst += (!!Values.Vint) => (Inj (typ := typ) fVint).
Reify Pattern patterns_vst += (!!seplog.sepcon) => (Inj (typ := typ) fstar).
Reify Pattern patterns_vst += (!!seplog.emp) => (Inj (typ := typ) femp).


Ltac reify_typ trm :=
  let k e :=
      pose e
  in
  reify_expr reify_vst_typ k [ True ] [ trm ].

Ltac reify_vst :=
match goal with
[ |- ?trm ] =>
  let k e :=
      pose e
  in
  reify_expr reify_vst k [ True ] [ trm ]
end.

Goal True.
reify_typ (Values.val -> Values.val).

Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import reverse_defs.
Local Open Scope logic.
Goal forall rho, (eval_id _t rho) = (eval_id _p rho) ->
lseg LS Share.top (map Vint nil) (eval_id _t rho) nullval * emp |--
lseg LS Share.top (map Vint nil) (eval_id _p rho) nullval * emp.
unfold nullval.
reify_vst.
