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
Require Import MirrorCore.RTac.RTac.
Check ExprUVar.
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
         (v : PTree.t type) (r : type) (gt : PTree.t type): my_lemma.
reify_lemma reify_vst (semax_set_localD id e t v r gt).
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

Lemma initialized_temp_eq : forall t v r gt gs i,
initialized i (mk_tycontext t v r gt gs) = mk_tycontext (initialized_temp i t) v r gt gs.
Proof.
intros.
unfold initialized, temp_types, initialized_temp. simpl. destruct (t ! i); auto.
destruct p; auto.
Qed.

Lemma update_temp_eq : forall t v r gt gs s,
update_tycon (mk_tycontext t v r gt gs) s = (mk_tycontext (update_temp t s) v r gt gs)
with
update_temp_labeled_eq : forall t v r gt gs s,
join_tycon_labeled s (mk_tycontext t v r gt gs) = (mk_tycontext (update_temp_labeled t s) v r gt gs).
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
          | [App (Inj (inr (Smx (ftycontext t v r gt)))) gs; (Inj (inr (Smx (fstatement s))))] => 
            App (Inj (inr (Smx (ftycontext (update_temp t s) v r gt)))) gs
          | _ =>  AppN.apps e args
      end
    | _ => AppN.apps e args
end.

Instance MA : MentionsAny (expr typ func) := {
  mentionsAny := ExprCore.mentionsAny
}.

Definition THEN' (r1 r2 : rtac typ (expr typ func)) := THEN r1 (runOnGoals r2).

Definition THEN (r1 r2 : rtac typ (expr typ func)) := 
  THEN' r1 (THEN' (INSTANTIATE typ func) r2).

Definition SIMPL_DELTA : rtac typ (ExprCore.expr typ func) :=
SIMPLIFY (fun _ _ _ _=>beta_all update_tycon_tac nil nil).

Definition INTROS := (REPEAT 10 (INTRO typ func)).

Definition APPLY_SKIP :=  (APPLY typ func  skip_lemma).

Definition run_tac (t: rtac typ (ExprCore.expr typ func)) e := 
  t nil nil 0%nat 0%nat (CTop nil nil) (ctx_empty (expr := expr typ func)) e.

Definition run_tac_intros e :=
run_tac (THEN INTROS e).

Definition APPLY_SEQ' s1 s2 := (EAPPLY typ func (seq_lemma s1 s2)).

(*
Definition APPLY_SEQ_SKIP s1 s2:= (THEN  (EAPPLY typ func (seq_lemma s1 s2)) (THEN (INSTANTIATE typ func) (runOnGoals (TRY APPLY_SKIP)))).*)

Definition APPLY_SEQ s1 s2 := THEN (APPLY_SEQ' s1 s2) (SIMPL_DELTA).


Definition APPLY_SET' id e t v r gt:=
EAPPLY typ func  (set_lemma id e t v r gt).


Fixpoint get_delta_statement (e : expr typ func)  :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) 
                     (App (Inj (inr (Smx (ftycontext t v r gt)))) gs)) _) 
           (Inj (inr (Smx (fstatement s))))) _ => Some ((t,v,r,gt), s)
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


Definition REFLEXIVITYTAC : rtac typ (expr typ func) :=
fun tus tvs n m c s e => 
match e with 
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 s l r ty
(*@exprUnify subst typ func _ _ _ SS SU 10 
                   tus tvs 0 s l r ty *) with
    | Some s => RTac.Core.Solved s 
    | None =>  RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Definition REFLEXIVITY := REFLEXIVITYTAC.
(*
STAC_no_hyps (@ExprSubst.instantiate typ func) REFLEXIVITYSTAC. *)
  

Definition REFLEXIVITY_BOOL tbl : rtac typ (expr typ func) := 
   fun tus tvs lus lvs c s e =>(
match e with
| (App (App (Inj (inr (Other (feq tybool)))) l) r) =>
  match reflect tbl nil nil l tybool, reflect tbl nil nil r tybool with
  | Some v1, Some v2 => if @RelDec.rel_dec _ eq _ v1 v2 then Solved s else Fail
  | _, _ => Fail
  end
| _ => Fail
end).

Definition SYMEXE_STEP (tbl: SymEnv.functions RType_typ)
: rtac typ (expr typ func)  := 
   fun tus tvs lus lvs c s e =>
  (
match (get_delta_statement e) with
| Some ((t, v, r, gt) , st) =>  
    match st with 
      | Sskip => APPLY_SKIP tus tvs lus lvs c s e
      | Ssequence s1 s2 => APPLY_SEQ s1 s2 tus tvs lus lvs c s e
      | Sset id exp => THEN (APPLY_SET' id exp t v r gt) 
                             (TRY (FIRST [REFLEXIVITY_BOOL tbl;
                                    REFLEXIVITY])) tus tvs lus lvs c s e
      | _ => Fail
    end
| None => Fail
end).


Definition SYMEXE_TAC tbl := THEN INTROS (REPEAT 1000 (SYMEXE_STEP tbl)).

Definition SYMEXE1_TAC tbl := THEN INTROS (SYMEXE_STEP tbl).

Definition rreflexivity e :=
run_tac (REFLEXIVITY) e.

Definition symexe e tbl:=
run_tac (SYMEXE_TAC tbl) e .

Definition symexe1 e tbl :=
run_tac (SYMEXE1_TAC tbl) e.

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
Print seq_lemma.
Lemma seq_triple : forall p es,
@semax es empty_tycontext p (Ssequence Sskip Sskip) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
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

(*
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
*)


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

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Check semax_set_localD.

Axiom simple_set_d : forall id e t v r gt gs E R ls  vs P,
(assertD [] (*(localD (my_set id vl ls) vs)*) [] R) = P ->
 @semax E (mk_tycontext t v r gt gs) (assertD [] (localD ls vs) R)
         (Sset id e)
         (normal_ret_assert P).


Definition set_lemma_simple (id : positive) (e : Clight.expr) (t : PTree.t (type * bool))
         (v : PTree.t type) (r : type) (gt : PTree.t type): my_lemma.
reify_lemma reify_vst (simple_set_d id e t v r gt).
Defined.

Print set_lemma_simple.

Definition test_lemma :=
  @lemmaD typ (expr typ func) RType_typ Expr_expr (expr typ func)
          (fun tus tvs e => exprD' tus tvs typrop e)
          _
          nil nil.

(*Goal forall (id : positive) (e : Clight.expr) (t : PTree.t (type * bool))
  (v : PTree.t type) (r : type) (gt : PTree.t type), False.
intros.
Eval vm_compute in test_lemma (set_lemma_simple id e t v r gt).*)

Definition EAPPLY_SET_simple id e t v r gt:=
EAPPLY typ func  (set_lemma_simple id e t v r gt).



Goal
forall  (contents : list val), exists (PO : environ -> mpred), 
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))         
     (normal_ret_assert PO)).
intros.
unfold empty_tycontext, Delta, remove_global_spec. change PTree.tree with PTree.t.
reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
Time Eval vm_compute in run_tac_intros (THEN (THEN (APPLY_SET' _p 
              (Econst_int (Int.repr 0) tint)
              (PTree.empty (type * bool))
              (PTree.empty type)
              Tvoid
              (PTree.empty type)) (INSTANTIATE typ func)) (TRY REFLEXIVITYTAC)) e .

Lemma bad_ax : forall A: Prop, A -> A /\ (True /\ A).
auto.
Qed.

Definition bad_ax_lemma : my_lemma.
reify_lemma reify_vst bad_ax.
Defined.

Definition EAPPLY_bad_ax :=
EAPPLY typ func bad_ax_lemma.


Goal exists A, True /\ A.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS (EAPPLY_bad_ax)) e.

eapply bad_ax.

Time Eval vm_compute in run_tac_intros ((EAPPLY_SET_simple _p 
              (Econst_int (Int.repr 0) tint)
              (PTree.empty (type * bool))
              (PTree.empty type)
              Tvoid
              (PTree.empty type))) e .
Print set_lemma.
(*Time Eval vm_compute in rreflexivity e. *)
Time Eval vm_compute in symexe e tbl. 
Abort.


Definition reflect_prop' tbl e:= match
reflect_prop tbl e with 
| Some p => p
| None => False
end.

Goal
forall  (contents : list val), exists PO, 
   (semax
     (remove_global_spec Delta)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                Sskip)
     (normal_ret_assert PO)).
intros.
unfold remove_global_spec,Delta.
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
     (mk_tycontext (lots_temps 50) (PTree.empty type) Tvoid
     (PTree.empty type) (PTree.empty funspec))
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (lots_of_sets 50)
     (normal_ret_assert PO)).
intros.
Time reify_expr_tac.
Time Eval vm_compute in symexe e tbl.
clear e. (*
eexists. 
unfold assertD. unfold localD, LocalD, PTree.fold, PTree.xfold, lots_temps, lots_of_sets. simpl.
simplify_Delta.
Time repeat forward; eauto.
Qed.*)
Abort.


