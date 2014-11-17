Require Import reify.
Require Import floyd.proofauto.
(*Require Import progs.list_dt.*)
Require Import reverse_defs.
Require Import set_reif.
(*Require Import MirrorCore.STac.STac.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.RTac.
*)
Require Import func_defs.
Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.RTac.Intro.
Import MirrorCore.RTac.Repeat.
Import MirrorCore.RTac.Then.
Import MirrorCore.RTac.Try.
Import MirrorCore.RTac.First.
Import MirrorCore.RTac.Fail.
Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import local2list.
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

Locate localD.
Lemma LocalD_to_localD : forall P R t l X,
PROPx (P) (LOCALx (LocalD t l X) (SEPx (R))) |--
PROPx (P) (LOCALx (localD t l) (SEPx (R))).
Proof.
intros. entailer.
apply prop_right.
unfold localD. 
repeat rewrite LocalD_app_eq in *.
unfold LocalD_app in *.
repeat rewrite fold_right_conj in *.
intuition. simpl. apply I.
Qed.

Ltac do_local2ptree := eapply semax_pre0; [ eapply local2ptree_soundness; repeat constructor | ]; eapply semax_pre0; [ apply LocalD_to_localD | ].

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).


Lemma semax_seq_reif c1 c2 : forall  (Espec : OracleKind) 
         (P : environ -> mpred)  (P' : environ -> mpred)
          (Q : ret_assert) (Delta : tycontext) ,
       @semax Espec Delta P c1 (normal_ret_assert P') ->
       @semax Espec (update_tycon Delta c1) P' c2 Q ->
       @semax Espec Delta P (Ssequence c1 c2) Q.
intros.
eapply semax_seq'; eauto.
Qed.


Definition skip_lemma : my_lemma.
reify_lemma reify_vst 
@semax_skip.
Defined. 

Definition seq_lemma (s1 s2: statement)  : my_lemma.
reify_lemma reify_vst (semax_seq_reif s1 s2).
Defined.

Definition set_lemma (id : positive) (e : Clight.expr) (t : PTree.t (type * bool))
         (v : PTree.t type) (r : type) : my_lemma.
reify_lemma reify_vst (semax_set_localD id e t v r).
Defined.

Definition initialized_temp (id : positive) (t : PTree.t (type * bool)) :=
match (t ! id) with
| Some (ty, _) =>
  PTree.set id (ty, true) t
| None => t
end.


Fixpoint update_temp (t : PTree.t (type * bool)) (s : statement) :=
 match s with
 | Sskip | Scontinue | Sbreak => t
 | Sassign e1 e2 => t (*already there?*)
 | Sset id e2 => (initialized_temp id t)
 | Ssequence s1 s2 => let t' := update_temp t s1 in
                      update_temp t' s2
 | Sifthenelse b s1 s2 => join_te (update_temp t s1) (update_temp t s2)
 | Sloop _ _ => t
 | Sswitch e ls => update_temp_labeled t ls
 | Scall (Some id) _ _ => (initialized_temp id t)
 | _ => t  (* et cetera *)
end
with update_temp_labeled (t : PTree.t (type * bool)) (ls : labeled_statements) :=
       match ls with
         | LSnil => t
         | LScons _ s ls' =>
           join_te (update_temp t s) (update_temp_labeled t ls')
       end.
 Check update_tycon.

Lemma initialized_temp_eq : forall t v r g i,
initialized i (t, v, r, g) = (initialized_temp i t, v, r, g).
Proof.
intros.
unfold initialized, temp_types, initialized_temp. simpl. destruct (t ! i); auto.
destruct p; auto.
Qed.

Lemma update_temp_eq : forall t v r g s,
update_tycon (t, v, r, g) s = ((update_temp t s), v, r, g)
with
update_temp_labeled_eq : forall t v r g s,
join_tycon_labeled s (t, v, r, g) = ((update_temp_labeled t s), v, r, g).
Proof.
intros. 
destruct s; intros;
simpl; try rewrite initialized_temp_eq; try reflexivity.
destruct o; try rewrite initialized_temp_eq; auto.
repeat rewrite update_temp_eq. reflexivity.
unfold join_tycon. 
repeat rewrite update_temp_eq. reflexivity.
repeat rewrite update_temp_labeled_eq. reflexivity.

intros.
destruct s; intros; simpl; try reflexivity.
unfold join_tycon. repeat rewrite update_temp_eq.
rewrite update_temp_labeled_eq. reflexivity.
Qed.

Definition update_tycon_tac (e : expr typ func) (args : list (expr typ func))
	: expr typ func :=
match e with
    | (Inj (inr (Smx (fupdate_tycon)))) => 
      match args with
          | [App (Inj (inr (Smx (ftycontext t v r)))) g; (Inj (inr (Smx (fstatement s))))] => 
            App (Inj (inr (Smx (ftycontext (update_temp t s) v r)))) g
          | _ =>  AppN.apps e args
      end
    | _ => AppN.apps e args
end.

Definition SIMPL_DELTA : rtac typ (ExprCore.expr typ func) subst:=
SIMPLIFY (fun _ _ =>beta_all update_tycon_tac nil nil).

Definition INTROS := (REPEAT 10 (INTRO typ func subst)).

Definition APPLY_SKIP :=  (APPLY typ func subst skip_lemma).


Definition run_tac (t: rtac typ (ExprCore.expr typ func) subst) e := 
  t CTop (SubstI.empty (expr := ExprCore.expr typ func)) e.

Definition APPLY_SEQ' s1 s2 := (EAPPLY typ func subst (seq_lemma s1 s2)).

Definition APPLY_SEQ_SKIP s1 s2:= (THEN  (EAPPLY typ func subst (seq_lemma s1 s2)) (THEN (INSTANTIATE typ func subst) (TRY APPLY_SKIP))).

Definition APPLY_SEQ s1 s2 := (THEN (APPLY_SEQ' s1 s2) SIMPL_DELTA).

Definition APPLY_SET' id e t v r:=
EAPPLY typ func subst (set_lemma id e t v r ).


Fixpoint get_delta_statement (e : expr typ func)  :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) 
                     (App (Inj (inr (Smx (ftycontext t v r)))) g)) _) 
           (Inj (inr (Smx (fstatement s))))) _ => Some ((t,v,r), s)
| App _ e 
| Abs _ e => get_delta_statement e
| _ => None
end.

Definition RSym_sym fs := SymSum.RSym_sum
  (SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) RSym_ilfunc) RSym_bilfunc)
  RSym_Func'.


Definition Expr_expr_fs fs: ExprI.Expr _ (ExprCore.expr typ func) := @ExprD.Expr_expr typ func _ _ (RSym_sym fs).
Definition Expr_ok_fs fs: @ExprI.ExprOk typ RType_typ (ExprCore.expr typ func) (Expr_expr_fs fs) := ExprD.ExprOk_expr.

Definition reflect ft (tus tvs : env) e (ty : typ)
 := @exprD _ _ _ (Expr_expr_fs ft) tus tvs e ty.


Definition REFLEXIVITYSTAC : Core.stac typ (expr typ func) subst :=
fun tus tvs s lst e => 
match e with 
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match @exprUnify subst typ func _ _ _ SS SU 10 
                   tus tvs 0 s l r ty with
    | Some s => STac.Core.Solved nil nil s 
    | None =>  STac.Core.Fail
  end
| _ => STac.Core.Fail
end.

Definition REFLEXIVITY :=
STAC_no_hyps (@ExprSubst.instantiate typ func) REFLEXIVITYSTAC. 
  

Definition REFLEXIVITY_BOOL tbl : rtac typ (expr typ func) subst := 
fun c s e => (
match e with
| (App (App (Inj (inr (Other (feq tybool)))) l) r) =>
  match reflect tbl nil nil l tybool, reflect tbl nil nil r tybool with
  | Some v1, Some v2 => if @RelDec.rel_dec _ eq _ v1 v2 then Solved s else Fail
  | _, _ => Fail
  end
| _ => Fail
end).

Definition SYMEXE_STEP tbl : rtac typ (expr typ func) subst := 
fun c s e => (
match (get_delta_statement e) with
| Some ((t, v, r) , st) =>  
    match st with 
      | Sskip => APPLY_SKIP c s e
      | Ssequence s1 s2 => APPLY_SEQ s1 s2 c s e
      | Sset id exp => THEN (APPLY_SET' id exp t v r ) 
                            (TRY (FIRST [REFLEXIVITY_BOOL tbl;
                                    REFLEXIVITY])) c s e
      | _ => Fail
    end
| None => FIRST [(REFLEXIVITY_BOOL tbl)] c s e 
end).


Definition SYMEXE_TAC tbl := THEN INTROS (REPEAT 1000 (SYMEXE_STEP tbl)).

Definition symexe e tbl:=
run_tac (SYMEXE_TAC tbl) e .

Lemma skip_triple : forall p e,
@semax e empty_tycontext
     p
      Sskip 
     (normal_ret_assert p).
Proof. unfold empty_tycontext. 
Time reify_expr_tac.
Time Eval vm_compute in  (symexe e tbl).
Abort.

Fixpoint lots_of_skips n :=
match n with 
| O => Sskip
| S n' => Ssequence Sskip (lots_of_skips n')
end.

Lemma seq_triple : forall p es,
@semax es empty_tycontext p (Ssequence Sskip Sskip) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
reify_expr_tac.
Time Eval vm_compute in  (symexe e tbl).
Abort.

Lemma seq_triple_lots : forall p es,
@semax es empty_tycontext p (lots_of_skips 10) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
reify_expr_tac. 
Time Eval vm_compute in (symexe e tbl).
Abort.

Ltac pull_sep_lift R :=
match R with
| ((`?H) :: ?T) => let rest := pull_sep_lift T in constr:(cons H rest)
| (@nil _) => constr:(@nil mpred)
end.

Ltac extract_sep_lift_semax :=
  match goal with
      [ |- semax _ (*(PROP (?P1) (LOCALx ?Q1 SEP (?R1)))*) 
                 (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ 
                 (normal_ret_assert (PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2))))] =>
      let R1' := pull_sep_lift R1 in
      let R2' := pull_sep_lift R2 in
      try (change (PROPx (P1) (LOCALx Q1 (SEPx (R1)))) 
      with (assertD nil Q1 R1'));
      try  (change (PROPx (P2) (LOCALx Q2 (SEPx (R2)))) 
      with (assertD nil Q2 R2'))
end.


Lemma local2list_soundness' : forall (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (T1 : list (ident * val))
         (T2 : list (ident * (type * val))),
       local2list Q T1 T2 nil ->
       PROPx P (LOCALx Q (SEPx R)) =
       PROPx P (LOCALx (locallistD T1 T2) (SEPx R)).
Proof.
intros. apply local2list_soundness; auto.
Qed.

Ltac do_local2list := erewrite local2list_soundness'; [ | repeat constructor].



Fixpoint extract_semax (e : expr typ func) : expr typ func :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) _) _) _) _ => e
| App _ e 
| Abs _ e => extract_semax e
| _ => Inj (inr (Value fVundef))
end.

Fixpoint replace_semax (e : expr typ func) (s : expr typ func) : expr typ func :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) _) _) _) _ =>  s
| App i e => App i (replace_semax e s) 
| Abs i e => Abs i (replace_semax e s)
| _ => Inj (inr (Value fVundef))
end.

Goal forall n (p : ident) (e1 e2: val), n = [(_p, (Tvoid, e1)); (_p, (Tvoid, e2))].
intros. reify_vst [(_p, (Tvoid, e1))(*; (_p, (Tvoid, e2))*)].

Goal forall n (p : ident) (e1 e2: val), n = [(_p, e1); (_p,  e2)].
intros. 
 reify_vst [(_p, e1); (_p, e2)].

Goal forall n, n = [_p].
reify_vst [(_p, _p); (_p, _p)].

 
Definition and_eq (v1 v2 p: expr typ func) t  : expr typ func :=
App (App (Inj (inr (Other fand))) (App (App (Inj (inr (Other (feq t)))) v1) v2)) p.

Definition _w : ident := 16%positive.

Fixpoint lots_of_sets' n p :=
match n with 
| O => (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
| S n' => Ssequence (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) (lots_of_sets' n' (Psucc p))
end.

Definition lots_of_sets n := lots_of_sets' n 1%positive.



Goal
forall  (contents : list val), exists PO, 
   (semax
     Delta2
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))         
     (normal_ret_assert PO)).
intros. unfold Delta2. change PTree.tree with PTree.t.
Time reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
eexists.
Time repeat forward; eauto.
Time Qed.


Definition reflect_prop' tbl e:= match
reflect_prop tbl e with 
| Some p => p
| None => False
end.

Goal
forall  (contents : list val), exists PO, 
   (semax
     (temp_types Delta, PTree.empty type, Tvoid,
     PTree.empty global_spec)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                Sskip)
     (normal_ret_assert PO)).
intros.

Time reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
eexists.
Time repeat forward; eauto.
Time Qed.

Fixpoint lots_temps' n p :=
match n with 
| O => PTree.set p (tptr t_struct_list, true) (PTree.empty _)
| S n' =>  PTree.set p (tptr t_struct_list, true) (lots_temps' n' (Psucc p))
end.

Definition lots_temps (n : nat) : PTree.t (type * bool) := lots_temps' (S n) (1%positive).

Goal
forall  (contents : list val), exists PO, 
   (semax
      (lots_temps 50, PTree.empty type, Tvoid,
     PTree.empty global_spec)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (lots_of_sets 50)
     (normal_ret_assert PO)).
intros.
Time reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
clear e.
eexists. 
unfold assertD. unfold localD, LocalD, PTree.fold, PTree.xfold, lots_temps, lots_of_sets. simpl.
simplify_Delta.
Time repeat forward; eauto.
Qed.



Lemma set_triple :
forall (contents : list val) E ,
@semax E empty_tycontext (*Delta2*) 
     (PROP  ()
      LOCAL  ((*`(eq p) (eval_id _p)*))  SEP  ((*`(lseg LS sh contents p nullval)))*)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) Sskip) 
(normal_ret_assert (PROP  ()
      LOCAL  ((*`(eq (Vint (Int.repr 0))) (eval_id _w); 
      `(eq p) (eval_id _p)*))  SEP  ((*`(lseg LS sh contents p nullval)*)))).
Proof.
intros.
do_local2ptree.
extract_sep_lift_semax.
unfold empty_tycontext. 
(*simpl (PTree.set _p p (PTree.empty val)).
revert sh p contents E.*)
reify_expr_tac.
Eval vm_compute in symexe e.
Time Eval vm_compute in run_tac (THEN (THEN INTROS (APPLY_SEQ' (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) Sskip)) (INSTANTIATE typ func subst)) e.
Time Eval vm_compute in  run_tac (SYMEXE_TAC) e.





Lemma skip_triple_2 :forall p contents sh,
semax Delta2
     (PROP  ()
      LOCAL  (`(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))
     Sskip 
     (normal_ret_assert (PROP  ()
      LOCAL  (`(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))).
Proof.
intros.
extract_sep_lift_semax.
replace_lift.
revert sh contents.
reify_expr_tac.



intros.
do_local2ptree.
extract_sep_lift_semax.
replace_lift.
reify_expr_tac.
Time Eval vm_compute in run_tac (symexe_tac e) e.
revert p contents sh. intro p.
reify_vst (
forall  (contents : list (elemtype LS)) (sh : share),
   semax Delta2
     (PROP  ()
      (LOCALx
         (LocalD (PTree.set _p p (PTree.empty val))
            (PTree.empty (type * val)) [])
         SEP  (sp (lseg LS sh contents p nullval))))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip)
     (normal_ret_assert
        (PROP  ()
         LOCAL  (lift_eq_val p (eval_id _p))
         SEP  (sp (lseg LS sh contents p nullval))))).
reify_expr_tac.
reify_vst ((PROP  ()
      (LOCALx
         (LocalD (PTree.set _p p (PTree.empty val))
            (PTree.empty (type * val)) [])
         SEP  (sp (lseg LS sh contents p nullval))))).
reify_vst (LocalD (PTree.set _p p (PTree.empty val))
            (PTree.empty (type * val)) []).

reify_vst (forall n , n = (PTree.empty val)).
PTree.set _p p (PTree.empty val)).
         (LocalD (PTree.set _p p (PTree.empty val))
            (PTree.empty (type * val)) [])).
reify_vst (forall (p : val) (contents : list (elemtype LS)) (sh : share),
   semax Delta2
             (PROP  ()
         LOCAL  (lift_eq_val p (eval_id _p))
         SEP  (sp (lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip)
     (normal_ret_assert
        (PROP  ()
         LOCAL  (lift_eq_val p (eval_id _p))
         SEP  (sp (lseg LS sh contents p nullval))))).
reify_expr_tac.

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
typeof_data 
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
dataD ]. 

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