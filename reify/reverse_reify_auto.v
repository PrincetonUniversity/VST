Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import wrapExpr.
Require Import reify_derives.
Require Import MirrorShard.ReifySepExpr.
Require Import MirrorShard.ReifyExpr.
Require Import reverse_defs.
Local Open Scope logic.

Import funcs.
Import all_types.

Ltac pose_env :=
pose (functions := functions);
pose (types := all_types);
pose (preds := sep_predicates).

Definition p (d:nat) : mpred:= emp.

Goal emp |-- emp.
pose_env.
reify_derives.
Admitted.

Goal p O |-- emp.
pose_env.
reify_derives.
simpl.
Admitted.

Lemma distribute_lift : forall {A B} (a:B->A) (b:B),
`(a b) = `a `b.
auto.
Qed.

Definition to_reify {P} (p: P) := p.

Lemma can_tag : forall {P} (p:P), p = to_reify p.
auto.
Qed.

Ltac tag H P:=
match P with 
|  to_reify _ => fail 1
|  _ => match type of P with
        | Prop => rewrite (can_tag P) in H
        | _ => fail 2
        end
end.

Ltac tag_reify := 
repeat
match goal with 
  [ H : ?P  |- _] => tag H P
end.

Ltac reify_tagged uenv funcs k:=
let types := get_types in
let rec reify_t uvars funcs k' :=
    idtac "reify_t";
    match goal with
      | [ H : to_reify ?E |- _] => unfold to_reify in H; reify_expr is_const E types funcs uvars nil
                                    ltac:(fun uvars' funcs' r' => reify_t uvars' funcs'
                                              ltac:(fun uvars'' funcs'' r'' =>
                                                      let r''' := constr:(r':: r'') in
                                                      k' uvars'' funcs'' r'''
  ))  
      | _ => k' uvars funcs (@nil (Expr.expr all_types))
    end
in
reify_t uenv funcs k.


Ltac revert_reify k :=
(fun uenv funcs es =>
try
let types := get_types in
let rec rr es' :=
match es' with
| ?h :: ?t => cut (force_Opt (@Expr.exprD types funcs uenv nil h Expr.tvProp)False); 
   [rr t | simpl; try assumption]
| nil => k uenv funcs es
end
in 
rr es).

Ltac collect_imp := 
let rec ci P :=
match P with
| force_Opt (Expr.exprD _ _ _ ?e _) _ -> ?B => 
let Bb := ci B in
constr:(e :: Bb)
| _ => constr:(@nil (Expr.expr all_types))
end
in
match goal with 
[ |- ?G] => ci G
end.

Ltac get_derives :=
let rec gd P :=
match P with
| ?A -> ?B => gd B
| Sep.sexprD _ _ _ _ ?L |-- Sep.sexprD _ _ _ _ ?R => constr:(L, R)
end
in
match goal with 
[ |- ?G] => gd G
end.

Ltac make_goal types funcs preds uenv := 
let ci := collect_imp in
let gd := get_derives in
constr:(goalD types funcs preds uenv nil (ci, (gd))).


Ltac finish_reify funcs preds uenv :=
let types:= get_types in
let g := make_goal types funcs preds uenv in
match goal with
[ |- ?P ] => try replace P with g; [ | try reflexivity]
end.

Ltac revert_cont preds ls rs ls_r rs_r :=
fun uenv funcs es =>
replace_reify_s2 ls funcs preds uenv ls_r;
replace_reify_s2 rs funcs preds uenv rs_r;
finish_reify funcs preds uenv.

Ltac reify_derives2 :=
prepare_reify;
ready_reify; 
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in
match goal with
[ |- ?ls |-- ?rs ] =>
tag_reify;
ReifySepM.reify_sexpr is_const ls types funcs tt tt preds uenv nil 
ltac:(fun uenv' funcs' preds' ls_r => 
      ReifySepM.reify_sexpr is_const rs types funcs' tt tt  preds' uenv' nil 
        ltac:(fun uenv'' funcs'' preds'' rs_r =>
            reify_tagged uenv'' funcs'' ltac:(revert_reify ltac:(revert_cont preds'' ls rs ls_r rs_r))))
end;
try finish_reify.


Goal forall n contents,
`(map Vint contents) = n.
intros.
fold_dependent.
repeat rewrite distribute_lift.
Admitted.


Goal forall (rho:environ), True -> True -> 
   emp |-- emp.
Proof.
intros.
pose_env.
prepare_reify.
reify_derives2.
Admitted.

Goal True -> p O |-- emp.
intros.
pose_env.
reify_derives2.
Admitted.



Goal forall rho sh contents, 
True ->
(lseg LS sh (map Vint contents) (eval_id _p rho) nullval * emp) |-- emp.
Proof.
intros.
pose (types := all_types).
pose (funcs := functions).
pose (predicates := predicates).
reify_derives2.
Admitted.


Goal forall rho ,
   (!!(eval_id _t rho = eval_id _p rho) && emp) |-- emp.
Proof.
intros.
pose_env. 
reify_derives.
Admitted.


Goal forall sh contents rho,
True -> !!True &&
   (!!(eval_id _t rho = eval_id _p rho /\
       eval_id _s rho = Vint (Int.repr 0) /\ True) && 
   (lseg LS sh (map Vint contents) (eval_id _p rho) nullval * emp)) |-- emp.
Proof.
intros.
pose_env.
reify_derives2.

Lemma while_entail1 :
  name _t ->
  name _p ->
  name _s ->
  name _h ->
  forall (sh : share) (contents : list int),
   PROP  ()
   LOCAL 
   (tc_environ
      Delta;
   `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list))
);
   `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
   SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
   |-- PROP  ()
       LOCAL 
       (`(eq (Vint (Int.sub (sum_int contents) (sum_int contents))))
          (eval_id _s))
       SEP  (TT; `(lseg LS sh (map Vint contents)) (eval_id _t) `nullval).
Proof.
intros.
go_lower0.
pose (functions := (functions ++ (more_funcs rho contents sh))).
pose (types := all_types).
pose (preds := sep_predicates ++ predicates).
reify_derives.
(* these are broken by new tactics
reify_assumption H3 tc_environ_r.
reify_derives left_side right_side.*)
Admitted.