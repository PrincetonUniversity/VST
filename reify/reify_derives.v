Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Require Import wrapExpr.
Require Import MirrorShard.ReifySepExpr.
Require Import MirrorShard.ReifyExpr.
Local Open Scope logic.

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
repeat fold VericSepLogic_Kernel.star VericSepLogic.star
VericSepLogic_Kernel.emp VericSepLogic.emp
VericSepLogic_Kernel.inj VericSepLogic.inj
VericSepLogic_Kernel.ex VericSepLogic.ex.

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

Ltac prepare_reify :=
autorewrite with gather_prop;
match goal with 
| [ |- !!?X && _ |-- !!?Y && _] => rewrite (convert_inj X); rewrite (convert_inj Y)
| [ |- !!?X && _ |-- _] => rewrite (convert_inj X)
| [ |- _ |-- _] => idtac
end;
fold_seplog;
fold_dependent.


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


Ltac finish_reify :=
match goal with 
[ |- @Sep.sexprD ?t ?f ?p ?e ?v ?le |-- Sep.sexprD ?f ?p ?e ?v ?re ] => 
  replace (Sep.sexprD f p e v le |-- Sep.sexprD f p e v re) with 
  (derivesD t f p e v (le, re)) by reflexivity end;
start_goalD;
rev_reify;
abbreviate_goal;
unfold_dependent.



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

Ltac replace_reify_s2 e funcs preds uenv r :=
let types := get_types in
replace e with
(@Sep.sexprD types funcs preds uenv  nil r); [ | try reflexivity ].

Module ReifySepM := ReifySepExpr VericSepLogic Sep.

Ltac ready_reify :=
match goal with
| [ |- context[!! _]] => fail 100 "goal still has !!"
| _ => idtac
end.

Ltac reify_derives :=
prepare_reify;
ready_reify; 
let types := get_types in
let funcs := get_funcs types in
let preds := get_predicates types in 
let uenv := get_uenv types in
match goal with
[ |- ?ls |-- ?rs ] => 
ReifySepM.reify_sexpr is_const ls types funcs tt tt
preds uenv nil 
ltac:(fun uenv' funcs' preds' ls_r => 
ReifySepM.reify_sexpr is_const rs types funcs' tt tt
preds' uenv' nil ltac:(fun uenv'' funcs'' preds'' rs_r =>
replace_reify_s2 ls funcs'' preds'' uenv'' ls_r;
replace_reify_s2 rs funcs'' preds'' uenv'' rs_r)) 
end;
try finish_reify.

Ltac is_const e := 
match type of e with
| type => constr:(true)
| ident => constr:(true)
| _ => 
  match e with 
  | nil => constr:(true)
  | nullval => constr:(true)
  | !!True => constr:(true)
  | 0 => constr:(true)
  | True => true
  | False => true
  | _ => constr:(false)
  end
end.


Ltac unfold_VericSepLogic := unfold VericSepLogic.star, 
VericSepLogic.inj, VericSepLogic.emp, VericSepLogic_Kernel.star,
VericSepLogic_Kernel.inj, VericSepLogic_Kernel.emp.
