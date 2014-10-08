Require Import reify.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import reverse_defs.
Require Import mccancel.
(*Require Import MirrorCore.STac.STac.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.RTac.
Require Import funcs.
Import MirrorCore.Lambda.Expr.*)
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.ModularFunc.ReifyLemma.
Require Import MirrorCore.Lambda.ExprUnify_simul.

Local Open Scope logic.

Existing Instance NullExtension.Espec.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Definition lift_eq_val2  (a b : environ -> val) : environ -> Prop := `eq a b.
Definition lift_eq_val a (b : environ -> val) : environ -> Prop := `(eq a) b.
Definition sp (s : mpred) : environ -> mpred:= `s.

Ltac replace_lift :=
repeat
match goal with
| [ |- context [`eq ?A ?B]] => change (`eq A B) with (lift_eq_val2 A B)
| [ |- context [`(eq ?A) ?B]] => change (`(eq A) B) with (lift_eq_val A B)
end;
repeat
match goal with
| [ |- context [`?S]] => change (`S) with (sp S)
end.

Require Import floyd.local2ptree.

Ltac do_local2ptree := eapply semax_pre0; [ eapply local2ptree_soundness; repeat constructor | ].

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).
Definition skip_lemma : my_lemma.
reify_lemma reify_vst 
@SeparationLogicSoundness.SoundSeparationLogic.CSL.semax_skip.
Defined.

Let EAPPLY :=
  @EApply.EAPPLY typ (ExprCore.expr typ func) subst _ _ SS SU ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ _ SS SU 3
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func)
(*                lem (apply_to_all tac)*).

  Let APPLY :=
    @Apply.APPLY typ (ExprCore.expr typ func) subst _ _ SS SU
           ExprLift.vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ _ SS SU 3
                         tus tvs n s e1 e2 t)
           (@ExprSubst.instantiate typ func)
          (* lem (apply_to_all tac)*).


Definition seq_lemma : my_lemma.
reify_lemma reify_vst 
semax_seq'.
Defined.
Check semax_seq.
Goal forall (Delta : tycontext) (R : ret_assert) 
         (P Q : environ -> mpred) (h t : statement),
       semax Delta P h (overridePost Q R) ->
       semax (update_tycon Delta h) Q t R -> semax Delta P (Ssequence h t) R.
Proof.
intros until t. Check semax.
reify_vst (semax Delta P h (overridePost Q R)).
reify_expr_tac.

Definition forward_setx_closed_now_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_vst forward_setx_closed_now.
Defined.


Lemma triple : forall p contents sh,
semax Delta2
     (PROP  ()
      LOCAL  (`(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) 
(normal_ret_assert (PROP  ()
      LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _w); 
      `(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))).
Proof.
intros.
do_local2ptree.
replace_lift.
eapply semax_seq.
reify_expr_tac.
reify_vst (semax Delta2
     (PROP  ()
      (LOCALx
         (LocalD (PTree.set _p p (PTree.empty val))
            (PTree.empty (type * val)) [tc_environ Delta2])
         SEP  (`(lseg LS sh contents p nullval))))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip)
     (normal_ret_assert
        (PROP  ()
         LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _w);
         `(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval))))).
reify_expr_tac.


Goal forall sh i cts contents t0 y, 
exists a, exists b, exists c,
   PROP  ()
   LOCAL  (tc_environ Delta; `(eq t0) (eval_id _t);
   `(eq (Vint (Int.sub (sum_int contents) (sum_int (i :: cts)))))
     (eval_id _s))
   SEP 
   (`(field_at sh t_struct_list (_head :: nil) (Vint i))
      (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(field_at sh t_struct_list (_tail :: nil)
       (valinject (nested_field_type2 t_struct_list (_tail :: nil)) y))
     (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(lseg LS sh (map Vint cts)) `y `nullval; TT)
   |-- local
         (tc_lvalue Delta
            (Efield (Ederef (Etempvar _t (tptr t_struct_list)) t_struct_list)
               _head tint)) && local `(tc_val tint a) &&
       (`(field_at b t_struct_list (_head :: nil) c)
          (eval_lvalue
             (Ederef (Etempvar _t (tptr t_struct_list)) t_struct_list)) * TT).
Proof.
intros.
eexists. eexists. eexists.
Admitted.

Instance x : RSym func := _.
Print x.

Definition RSym_sym fs := SymSum.RSym_sum
  (SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) RSym_ilfunc) RSym_bilfunc)
  RSym_Func'.

Definition Expr_expr_fs fs: ExprI.Expr _ (ExprCore.expr typ func) := @ExprD.Expr_expr typ func _ _ (RSym_sym fs).
Definition Expr_ok_fs fs: @ExprI.ExprOk typ RType_typ (ExprCore.expr typ func) (Expr_expr_fs fs) := ExprD.ExprOk_expr.

Check @exprD.

Definition reflect ft (tus tvs : env) e (ty : typ)
 := @exprD _ _ _ (Expr_expr_fs ft) tus tvs e ty.

Ltac do_reflect := 
cbv [reflect exprD exprD' Expr_expr_fs ExprD.Expr_expr
ExprDsimul.ExprDenote.exprD'
ExprDsimul.ExprDenote.OpenT
ExprDsimul.ExprDenote.Open_GetVAs
ExprDsimul.ExprDenote.Open_GetUAs
ExprDsimul.ExprDenote.Open_UseU
ExprDsimul.ExprDenote.Open_UseV
ExprDsimul.ExprDenote.func_simul
ExprDsimul.ExprDenote.funcAs
ExprDsimul.ExprDenote.Open_App
ExprDsimul.ExprDenote.Open_Inj
ExprDsimul.ExprDenote.Open_Abs
ExprDsimul.ExprDenote.Rcast_val
ExprDsimul.ExprDenote.Rcast
type_cast
nth_error_get_hlist_nth
FMapPositive.PositiveMap.find
ResType.OpenT
split_env
Monad.bind
Monad.ret
OptionMonad.Monad_option
elem_ctor
TypesI.typD
typD

symD

Relim

typeof_sym

RSym_sym
Rsym
SymSum.RSym_sum
SymEnv.RSym_func
SymEnv.func_typeof_sym
SymEnv.funcD
typeof_func_opt
SymEnv.ftype
RSym_bilfunc
RSym_Func'
RSym_ilfunc

BILogicFunc.RSym_bilfunc
BILogicFunc.typeof_bilfunc
BILogicFunc.funcD
bilops
ilops

ILogicFunc.fEntails
ILogicFunc.ILogicFuncExpr
ILogicFunc.ILogicFuncSumR
ILogicFunc.ILogicFuncSumL
ILogicFunc.BaseFuncInst
ILogic.ILogicOps_Prop
ILogicOps_mpred

BILogicFunc.mkEmp
BILogicFunc.fEmp
BILogicFunc.BILogicFuncSumL
BILogicFunc.BILogicFuncSumR
BILogicFunc.BaseFuncInst
BILogic.empSP
BILogic.sepSP
BILogic.wandSP

ModularFunc.ILogicFunc.RSym_ilfunc
ModularFunc.ILogicFunc.typeof_func
ModularFunc.ILogicFunc.funcD

typ2_match
typ2_cast
typ2
Typ2_tyArr
typ0_cast
typ0_match
typ0
Typ0_tyProp

HList.hlist_hd
HList.hlist_tl

typeof_func
typeof_const
typeof_z_op 
typeof_int_op 
typeof_value 
typeof_eval 
typeof_other 
typeof_sep 
typeof_lst 
typeof_triple

RType_typ

typ_eq_dec typ_rec typ_rect
False_ind False_rect True_ind True_rect
eq_ind eq_rec eq_rect
eq_sym sumbool_rec sumbool_rect
 eq_rec_r
f_equal

eqb_ident eqb_type 

funcD
tripleD

find
constD 
z_opD 
int_opD 
valueD 
evalD 
otherD 
sepD 
lstD ]. 

Goal forall sh contents p,
`(lseg LS sh (map Vint contents) p nullval) |--
`(lseg LS sh (map Vint contents) p nullval)
(*emp |-- emp*).
intros.
reify_vst (contents).
(*replace_lift. go_lower0.
reify_expr_tac.*)
assert (exists n, Some n = reflect tbl nil nil e (tylist tyint)).
eexists. unfold e. unfold tbl. 
do_reflect. 


SearchAbout find.
cbv.


cbv [eqb_ident].
unfold 
simpl. unfold RType_typ. 
simpl.
do_reflect. simpl. unfold BILogicFunc.mkEmp.
simpl. unfold reflect, exprD, exprD'. 
simpl. do_reflect. 
Goal forall (sh : share) (contents : list int) (p : val),
   PROP  ()
   LOCAL  (tc_environ Delta; `(eq p) (eval_id _t);
   `(eq (Vint (Int.repr 0))) (eval_id _s); `(eq p) (eval_id _p))
   SEP  (`(lseg LS sh (map Vint contents) p nullval))
   |-- PROP  ()
       LOCAL  (`(eq p) (eval_id _t);
       `(eq (Vint (Int.sub (sum_int contents) (sum_int contents))))
         (eval_id _s))
       SEP  (TT; `(lseg LS sh (map Vint contents) p nullval)).
intros.
replace_lift. go_lower0.
reify_expr_tac. Check reflect.
assert (exists v, v = reflect tbl nil nil e).
unfold e. eexists.
do_reflect. 

pose (c := cancel e).
unfold e in c.
compute in c.

Check exprD'.
reify_vst rho.
Eval compute in (reflect tbl0 nil nil e0 tyenviron).
assert (exists v, (reflect tbl0 nil nil e0 tyenviron = v)).
unfold e0.

simpl.
unfold typ_eq_dec.
cbv [typ_eq_dec typ_rec typ_rect].

Locate f1. simpl.

cbv [reflect exprD' Expr_expr_fs ExprD.Expr_expr
ExprDsimul.ExprDenote.exprD'
ExprDsimul.ExprDenote.OpenT
ExprDsimul.ExprDenote.Open_GetVAs
ExprDsimul.ExprDenote.Open_GetUAs
ExprDsimul.ExprDenote.Open_UseU
ExprDsimul.ExprDenote.Open_UseV
ExprDsimul.ExprDenote.func_simul
ExprDsimul.ExprDenote.funcAs
ExprDsimul.ExprDenote.Open_App
ExprDsimul.ExprDenote.Open_Inj
ExprDsimul.ExprDenote.Open_Abs
ExprDsimul.ExprDenote.Rcast_val
Monad.bind
Monad.ret
nth_error_get_hlist_nth
OptionMonad.Monad_option
TypesI.typD
type_cast
ResType.OpenT
typeof_sym
RSym_sym
typD
RType_typ
eq_sym
typ2_cast
typ2_match
Typ2_tyArr
HList.hlist_hd
HList.hlist_tl
typ_eq_dec typ_rec typ_rect
SymSum.RSym_sum
SymEnv.RSym_func
RSym_ilfunc
typeof_sym
SymEnv.func_typeof_sym
RSym_bilfunc
ModularFunc.ILogicFunc.RSym_ilfunc
ModularFunc.ILogicFunc.typeof_func
SymEnv.func_typeof_sym
SymEnv.ftype
BILogicFunc.RSym_bilfunc
RSym_Func'
BILogicFunc.typeof_bilfunc
BILogicFunc.mkEmp
FMapPositive.PositiveMap.find
typeof_func_opt].
Locate type_eq_dec.
unfold type_eq_dec.
Eval cbv in (reflect tbl0 nil nil e0 tyZ).
Check reflect.
Print RSym_env.
Print fs.
Locate fs.
Goal forall m n: nat, Some n = Some m -> False.
intros. congruence.

Check exprD'.
Eval vm_compute in reflect e.
assert (exists n, reflect e = n).
eexists. unfold reflect.
cbv in (reflect e).
simpl.
simpl. clear e.
unfold exprD'.
simpl.
Time Compute (cancel e).
reify_vst ( PROP  ()
   LOCAL  (tc_environ Delta; lift_eq_val p (eval_id _t);
   lift_eq_val (Vint (Int.repr 0)) (eval_id _s); lift_eq_val p (eval_id _p))
   SEP  (sp (lseg LS sh (map Vint contents) p nullval))
   |-- PROP  ()
       LOCAL  (lift_eq_val p (eval_id _t);
       lift_eq_val (Vint (Int.sub (sum_int contents) (sum_int contents)))
         (eval_id _s))
       SEP  (TT; sp (lseg LS sh (map Vint contents) p nullval))
).
reify_expr_tac.

Goal forall (sh : share) (contents : list val),
  writable_share sh ->
  forall (cts1 cts2 : list val) (w v : val),
    isptr v ->
   exists (a : Share.t) (b : val),
     PROP  (contents = (*rev*) cts1 ++ cts2)
     LOCAL  (tc_environ Delta2; `(eq w) (eval_id _w); 
     `(eq v) (eval_id _v))
     SEP  (`(lseg LS sh cts1 w nullval); `(lseg LS sh cts2 v nullval))
     |-- local (tc_expr Delta2 (Etempvar _v (tptr t_struct_list))) &&
         (`(field_at a t_struct_list (_tail::nil) b)
            (eval_expr (Etempvar _v (tptr t_struct_list))) * TT).
Proof.
intros. eexists. eexists. go_lower0.
reify_expr_tac.
Abort.

Goal forall n v, `(eq v) (eval_id _v) = n.
 intros.
Abort.
(* reify_expr_tac.*)


Existing Instance NullExtension.Espec.

Goal forall p contents sh,
semax Delta2
     (PROP  ()
      LOCAL  (`(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) 
(normal_ret_assert (PROP  ()
      LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _w); 
      `(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))).
intros.
replace_lift. 
reify_expr_tac. 
Abort.

Goal
  forall (sh : share) (contents : list int),
  PROP  ()
  LOCAL  (tc_environ Delta;
         `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list)));
         `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
  SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
          |-- EX  cts : list int,
  PROP  ()
  LOCAL 
        (`(eq (Vint (Int.sub (sum_int contents) (sum_int cts)))) (eval_id _s))
  SEP  (TT; `(lseg LS sh (map Vint cts)) (eval_id _t) `nullval).
Proof.
intros. 
replace_lift. 
Abort.


Goal
 forall (i : int) (cts : list int) (t0 y : val) (sh : share)
     (contents : list int),
   exists a, exists b,
   PROP  ()
   LOCAL  (tc_environ Delta; `(eq t0) (eval_id _t);
   `(eq (Vint (Int.sub (sum_int contents) (sum_int (i :: cts)))))
     (eval_id _s))
   SEP 
   (`(field_at sh t_struct_list _head (Vint i))
      (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(field_at sh t_struct_list _tail y)
     (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(lseg LS sh (map Vint cts)) `y `nullval; TT)
   |-- local (tc_expr Delta (Etempvar _t (tptr t_struct_list))) &&
       (`(field_at a t_struct_list _head b)
          (eval_expr (Etempvar _t (tptr t_struct_list))) * TT).
Proof.
intros. 
eexists. eexists.
go_lower0.