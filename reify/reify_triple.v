Require Import floyd.proofauto.
Require Import reverse_defs.
Require Import MirrorShard.Expr.
Require Import sep.
Require Import wrapExpr.
Require Import types.
Require Import reify_derives.
Require Import MirrorShard.ReifyExpr MirrorShard.ReifySepExpr.

Local Open Scope logic.

Existing Instance NullExtension.Espec.

Record Triple := mkTriple
{ Tdelta : tycontext;
  Tprop : list expr;
  Tlocal : list expr;
  Tsep : list Sep.sexpr;
  Tcommand : statement;
  Tpost : ret_assert
}.

Section denotation.

Variable functions : functions our_types.
Variable preds : Sep.predicates our_types.
Variable uvars : Expr.env our_types.


Definition reflect_prop e := force_Opt (exprD functions uvars nil e tvProp) False.
Definition False' (_ : environ) := False.
Definition reflect_local (e: expr) :=  (force_Opt (exprD functions uvars nil e (Expr.tvType 17)) False').

Definition s_reflect := Sep.sexprD functions preds uvars nil.

Definition reflect_Tprop l :=
map reflect_prop l.

Definition reflect_Tlocal l :=
map reflect_local l.

Definition reflect_Tsep l := 
map (fun e => `(s_reflect e)) l.

Definition PreD t :=
PROPx (reflect_Tprop (Tprop t)) 
      ( LOCALx (reflect_Tlocal (Tlocal t)) 
               (SEPx (reflect_Tsep (Tsep t)))).

Definition TripleD t :=
  semax (Tdelta t) (PreD t) (Tcommand t) ((Tpost t)).

End denotation.
                
(*shouldn't need these, can probably do this as part of reification*)
Ltac change_eqs' l :=
try
match l with
| ?H :: ?T => match H with
                | `(eq ?l) (eval_id ?r) => change H with (functions.lift_eq l r)
              end; change_eqs' T
end.

Ltac change_eqs :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] => change_eqs Q
end.

Ltac is_const := false.


Ltac reify_exprs isConst es types funcs uvars vars k :=
  match es with
    | tt => k uvars funcs (@nil expr)
    | nil => idtac "nill"; idtac k; k uvars funcs (@nil expr)
    | (?e, ?es) =>
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
          let res := constr:(e :: es) in
          k uvars funcs res))
    | ?e :: ?es => idtac "consc";
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        idtac "cons"; reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
  let res := constr:(e :: es) in
          k uvars funcs res))
  end.


Ltac reify_props types funcs uvars vars k := 
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_exprs is_const P types funcs uvars (@nil bool) k
end. 

Ltac reify_props_change types funcs uvars vars  :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_props types funcs uvars vars 
ltac:(fun uvars funcs res =>idtac "replace"; 
 change P with 
(reflect_Tprop funcs uvars res))
end.

Ltac reify_locals' types funcs uvars vars k l :=
match l with
| nil => k uvars funcs (@nil expr)
| (`(eq ?e) (eval_id ?v))::?T => 
  reify_expr ltac:(is_const) e types funcs uvars vars ltac:(
    fun uvars' funcs' e_r => reify_expr ltac:(is_const) v types funcs' uvars' vars 
  ltac:(
        fun uvars'' funcs'' v_r => 
          reify_locals' types funcs'' uvars'' vars ltac:(
            fun uvars''' funcs''' rest_r => 
              let res := constr:((Func 55%nat (e_r :: v_r :: nil)) :: rest_r) in
              k uvars''' funcs''' res) T))
end. 
      
Ltac reify_locals types funcs uvars vars k :=
match goal with
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_locals' types funcs uvars vars k Q
end.

Ltac reify_locals_change types funcs uvars vars  :=
match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
reify_locals types funcs uvars vars 
ltac:(fun uvars funcs res =>idtac "replace"; 
 replace Q with 
(reflect_Tlocal funcs uvars res))
end.

Lemma triple : forall p contents sh q r,
exists POSTCONDITION,
semax Delta
     (PROP  (p = q)
      LOCAL  (`(eq p) (eval_id _p); `(eq q) (eval_id r))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) POSTCONDITION.
intros. eexists. pose_env. 
let uv := get_uenv types in 
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in
reify_locals_change types functions uenv uenv. 
ltac:(fun a b c => id_this (a, b, c)).

let uv := get_uenv types in 
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in
(*reify_expr is_const (p=q) types funcs uvars (@nil bool) ltac:(fun a b c => idtac "called").*)
reify_props_change types funcs uenv (@nil bool). 
replace ((p=q) :: nil) with ( Equal (tvType 4) (Func 55%nat nil) (Func 56%nat nil) :: nil).

match goal with 
[ |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _] =>
end.

change (`(eq p) (eval_id _p)) with (lift_eq p _p).
intros. eexists.
