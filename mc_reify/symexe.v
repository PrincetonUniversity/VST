Require Export reify.
Import floyd.proofauto.
Require Export bool_funcs.
Require Import set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export funcs.
Require Import types.
Require Export reflexivity_tacs.

Local Open Scope logic.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.


Ltac do_local2ptree := eapply semax_pre0; [ eapply local2ptree_soundness; repeat constructor | ]; eapply semax_pre0; [ apply LocalD_to_localD | ].

Lemma semax_seq_reif c1 c2 : forall  (Espec : OracleKind) 
         (P : environ -> mpred)  (P' : environ -> mpred)
          (Q : ret_assert) (Delta : tycontext) ,
       @semax Espec Delta P c1 (normal_ret_assert P') ->
       @semax Espec (update_tycon Delta c1) P' c2 Q ->
       @semax Espec Delta P (Ssequence c1 c2) Q.
intros.
eapply semax_seq'; eauto.
Qed.

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).

Fixpoint get_delta_statement (e : expr typ func)  :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) 
                     (App (Inj (inr (Smx (ftycontext t v r gt)))) gs)) _) 
           (Inj (inr (Smx (fstatement s))))) _ => Some ((t,v,r,gt), s)
| App _ e 
| Abs _ e => get_delta_statement e
| _ => None
end.

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

Definition APPLY_SEQ s1 s2 := THEN (APPLY_SEQ' s1 s2) (SIMPL_DELTA).

Definition APPLY_SET' id e t v r gt:=
EAPPLY typ func  (set_lemma id e t v r gt).

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

Definition test_lemma :=
  @lemmaD typ (expr typ func) RType_typ ExprD.Expr_expr (expr typ func)
          (fun tus tvs e => ExprDsimul.ExprDenote.exprD' tus tvs typrop e)
          _
          nil nil.


Require Import MirrorCharge.RTac.Cancellation.



Fixpoint is_pure (e : expr typ func) := 
match e with 
| App e1 e2 => is_pure e1
| (Inj (inr (Sep fprop))) => true
| _ => false
end.

Definition CANCEL e := run_tac (THEN INTROS (CANCELLATION typ func tympred is_pure)) e.
Locate data_at.

Parameter f : nat -> nat.

Goal f = f.
reify_expr_tac.
(* App(App (Inj (inr (Other (feq (tyArr tynat tynat))))) (Ext 1%positive))
         (Ext 1%positive) *)
Eval vm_compute in run_tac (THEN INTROS REFLEXIVITY) e.
(*     = Solved (TopSubst (expr typ func) [] []) *)
Abort.

Goal forall n, f n = f n.
reify_expr_tac.
(*App (ILogicFunc.fForall tynat typrop)
         (Abs tynat
            (App
               (App (Inj (inr (Other (feq tynat))))
                  (App (Ext 1%positive) (ExprCore.Var 0%nat)))
               (App (Ext 1%positive) (ExprCore.Var 0%nat)))) *)
Eval vm_compute in run_tac (THEN INTROS REFLEXIVITY) e.
(*    = Fail *)
Abort.


Goal forall sh, data_at T tint |-- data_at sh tint.
intros.
reify_expr_tac.
Eval vm_compute in CANCEL e.
Abort.

Goal forall P Q b,  !!b && P * Q |-- !!b && Q * P .
reify_expr_tac.
Eval vm_compute in .

Goal forall (sh : share), sh = sh.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS REFLEXIVITYTAC) e.


Goal forall sh ty v1 v2, mapsto sh ty v1 v2 = mapsto sh ty v1 v2.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS REFLEXIVITYTAC) e.
Eval vm_compute in run_tac (THEN INTROS (CANCELLATION typ func tympred is_pure)) e.


