Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import wrapExpr.
Require Import MirrorShard.ReifySepExpr.
Require Import MirrorShard.ReifyExpr.
Require Import preproc.
Local Open Scope logic.


Module ReifySepM := ReifySepExpr VericSepLogic Sep.

Definition all_funcs (*:  list (Expr.signature our_types) *):= functions.our_functions nil.
Definition all_preds (*: list (Sep.predicate our_types) *) := functions.sep_predicates nil.

Ltac pose_env :=
pose (types := all_types_r nil);
pose (functions := all_funcs);
pose (preds := all_preds).

(*Tactics for reifying derives and hypothesis *)

Lemma convert_inj : forall S Q, !!S && Q  = (!!S && emp) * Q.
intros.
apply pred_ext.
 entailer!. 
entailer!.
Qed.

(*When prepare_reify is finished, all !!s should be in the form
!!P && emp * ... so that they can be converted to SepExpr.Inj 
this tactic is likely incomplete*)

Ltac fold_inj :=
repeat match goal with 
[ |- context[!!(?P) && emp]] => 
change (!!P && emp) with (VericSepLogic_Kernel.inj P)
end.


Ltac fold_seplog := 
fold_inj;
repeat fold VericSepLogic_Kernel.star (*VericSepLogic.star*)
VericSepLogic_Kernel.emp (*VericSepLogic.emp*)
VericSepLogic_Kernel.inj (*VericSepLogic.inj*)
VericSepLogic_Kernel.ex. (*VericSepLogic.ex.*)

Definition folded {A} (a:A) := True.

Ltac fold_lseg := 
match goal with 
[ |- context[lseg ?t _ _ _ _]] => let ls := fresh "lseg_" in pose (ls := lseg t);
fold ls; assert (folded ls) by apply I
end.

Ltac fold_map :=
match goal with
[ |- context[ map ?a _ ]] => let mp := fresh "map_" in pose (mp := map a); fold mp; assert (folded mp) by apply I
end.

Ltac fold_dependent :=
try fold_lseg; try fold_map.

Ltac unfold_dependent :=
repeat
match goal with
[ H : folded ?X |- _] => unfold X in *; clear X; clear H
end.

Definition TT' := !!True.

Lemma changeTT' : forall (a b c : mpred) ,
(a |-- b * (c * TT')) -> (a |-- b * (c * !!True)). 
auto.
Qed.

Ltac prepare_reify :=
autorewrite with gather_prop;
match goal with 
| [ |- !!?X && _ |-- !!?Y && _] => rewrite (convert_inj X); rewrite (convert_inj Y)
| [ |- !!?X && _ |-- !!?Y && _] => rewrite (convert_inj X); rewrite (convert_inj Y)
| [ |- !!?X && _ |-- _] => rewrite (convert_inj X)
| [ |- _ |-- !!?X && _] => rewrite (convert_inj X)
| [ |- _ |-- _] => idtac
end;
try apply changeTT';
fold_seplog;
(*fold_dependent;*)
fold TT.


(*Turns a reified derives into a reified goal with no assumptions, 
sort of a base case for rev_reify *)
Ltac start_goalD :=
match goal with 
[ |- derivesD ?t ?f ?p ?e ?v ?d] => 
replace (derivesD t f p e v d) with (goalD t f p e v (nil, d)) by reflexivity
end.

(*Pulls down any reified assumptions and puts them into 
a goal *)
Ltac rev_reify :=
repeat match goal with
| [ H : force_Opt (Expr.exprD ?f ?e ?v ?P ?ty) False |- goalD ?t ?f ?p ?e ?v (?l, ?d) ] => revert H; 
replace (force_Opt (Expr.exprD f e v P ty) False ->
goalD t f p e v (l, d)) with
(goalD t f p e v (P::l, d)) by reflexivity
end.

Ltac id_this n:= assert (exists x, n=x); [ eexists | ].

Ltac get_types :=
match goal with 
| [ H := ?X : (list Expr.type) |- _] => X
end.

Ltac clear_types :=
match goal with 
| [ H := ?X : (list Expr.type) |- _] => unfold H in *; clear H
end.

Ltac get_funcs t := 
match goal with
[ _ := ?X : list (Expr.signature t) |- _ ] => X end.

Ltac clear_funcs t :=
match goal with 
| [ H := ?X : (list (Expr.signature t)) |- _] => unfold H in *; clear H
end.

Ltac get_predicates t :=
match goal with
[ _ := ?X : list (Sep.predicate t) |- _] => X end.

Ltac clear_predicates t :=
match goal with 
| [ H := ?X : (list (Sep.predicate t)) |- _] => unfold H in *; clear H
end.

Ltac get_uenv t := 
match goal with 
| [ _ := ?X : Expr.env t |- _ ] => X
| [ _ := ?X : list (sigT (Expr.tvarD t)) |- _ ] => X
| [ _ : _ |- _ ] => constr:(@nil (sigT (Expr.tvarD t)))
end.

Ltac clear_uenv t :=
try 
match goal with 
| [ H := ?X : Expr.env t |- _ ] => unfold H in *; clear H
| [ H := ?X : list (sigT (Expr.tvarD t)) |- _ ] => unfold H in *; clear H
end.


Ltac clear_all :=
let t := get_types in
clear_predicates t;
clear_funcs t;
clear_uenv t.

Ltac abbreviate_goal :=
match goal with
[ |- goalD _ ?f ?p ?u _ _] => 
clear_all;
abbreviate f as funcs;
abbreviate p as preds;
abbreviate u as uenv
end.

Ltac replace_reify_e H v r :=
let types := get_types in
let funcs := get_funcs types in
let uenv := get_uenv types in
replace v with 
(force_Opt (@Expr.exprD types funcs uenv nil r Expr.tvProp)False) in H; [ | try reflexivity]. 

Ltac reflect_sexpr types evars :=
let reflect_sexpr' uvars funcs sfuncs s :=
constr:(Sep.sexprD types funcs sfuncs uvars evars s) in
reflect_sexpr'.

Ltac reify_assumption H r:=
match goal with
[ H : ?X |- _] => replace_reify_e H X r
end.

Ltac replace_reify_s e r :=
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in 
replace e with
(@Sep.sexprD types funcs preds uenv  nil r); [ | try reflexivity ].

Ltac replace_reify_derives_l l funcs preds uenv l_r r :=
let types := get_types in 
replace (l |-- r) with 
(@Sep.sexprD types funcs preds uenv nil l_r |-- r); [ | try reflexivity].

Ltac replace_reify_s2 e funcs preds uenv r :=
let types := get_types in
replace e with
(@Sep.sexprD types funcs preds uenv  nil r); [ | try reflexivity ].

Ltac ready_reify :=
match goal with
| [ |- context[!! _]] => fail 100 "goal still has !!"
| _ => idtac
end.

Ltac is_const e := 
match type of e with
| type => constr:(true)
| ident => constr:(true)
| _ => 
  match e with 
  | nil => constr:(true)
  | !!True => constr:(true)
  | 0 => constr:(true)
  | False => true
  | _ => constr:(false)
  end
end.

Ltac unfold_VericSepLogic := unfold VericSepLogic.star, 
VericSepLogic.inj, VericSepLogic.emp, VericSepLogic_Kernel.star,
VericSepLogic_Kernel.inj, VericSepLogic_Kernel.emp in *.

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
|  folded _ => fail 1
|  name _ => fail 1
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
      | _ => k' uvars funcs (@nil Expr.expr)
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
| _ => constr:(@nil Expr.expr)
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
idtac "rc replace_reify 1";
replace_reify_derives_l ls funcs preds uenv ls_r rs;
idtac "rc replace_reify 2"; 
replace_reify_s2 rs funcs preds uenv rs_r;
idtac "rc finishing reify";
try (finish_reify funcs preds uenv).

Ltac reify_derives :=
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
      idtac "reify_right"; ReifySepM.reify_sexpr is_const rs types funcs' tt tt  preds' uenv' nil 
        ltac:(fun uenv'' funcs'' preds'' rs_r =>
            idtac "reify_tagged"; reify_tagged uenv'' funcs'' ltac:(revert_reify ltac:(revert_cont preds'' ls rs ls_r rs_r))))
end;
abbreviate_goal;
unfold_dependent;
lift_and_goal.