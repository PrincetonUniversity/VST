Require Import MirrorShard.CancelTacBedrock.
Require Import MirrorShard.Expr MirrorShard.SepExpr.
Require Import MirrorShard.SepHeap MirrorShard.SepCancel.
Require Import MirrorShard.SepLemma.
Require Import sep.
Require Import FMapInterface.
Require Import SimpleInstantiation.
Require Import MirrorShard.ExprUnifySynGenRec.
Require Import wrapExpr.
Require Import Provers.
Require Import reify_derives.

Module SH := SepHeap.Make VericSepLogic Sep.
Module SL := SepLemma VericSepLogic Sep.
Module FM := FMapList.Make NatMap.Ordered_nat.
Module SUBST := SimpleInstantiation.Make FM.
Module UNIFY := ExprUnifySynGenRec.Make SUBST.
Module UNF := Unfolder.Make VericSepLogic Sep SH SUBST UNIFY SL.

Module CancelModule := CancelTacBedrock.Make VericSepLogic Sep SH SL SUBST UNIFY UNF.

Definition reflect_e types functions meta_env var_env :=
fun h => force_Opt (@Expr.exprD types functions meta_env var_env h Expr.tvProp) False.

Lemma goalD_unfold :
forall types funcs preds meta_env hyps l r,
(Expr.AllProvable funcs meta_env nil hyps -> 
derivesD types funcs preds meta_env nil (l, r)) -> goalD types funcs preds meta_env nil ((hyps, (l, r))). 
intros. generalize dependent hyps.
induction hyps; intros.
unfold goalD. simpl. simpl in H.
apply H. auto.
simpl.
intros.
simpl in H.
assert ((AllProvable funcs meta_env nil hyps ->
            derivesD types funcs preds meta_env nil (l, r))).
simpl. 
intros.
apply H. split.
unfold Expr.Provable. destruct (Expr.exprD funcs meta_env nil a Expr.tvProp);
auto.
apply H1.
intuition.
simpl in *.
destruct hyps. auto.
assumption.
Qed.


Lemma ApplyCancelSep_with_eq_goal 
(boundf boundb : nat) (types : list Expr.type) :
      forall (meta_env : Expr.env types) (hyps : Expr.exprs types) preds funcs prover hintsFwd hintsBwd,
      forall (l r : Sep.sexpr types) res,
      forall (WTR : Sep.WellTyped_sexpr (Expr.typeof_funcs funcs) (Sep.typeof_preds preds) (Expr.typeof_env meta_env) nil r = true),
       UNF.hintSideD funcs preds hintsFwd ->
       UNF.hintSideD funcs preds hintsBwd ->
       Prover.ProverT_correct prover funcs ->
      CancelModule.canceller (Sep.typeof_preds preds) hintsFwd hintsBwd prover boundf boundb (Expr.typeof_env meta_env) hyps l r = Some res ->
      match res with
        | {| CancelModule.AllExt := new_vars
           ; CancelModule.ExExt  := new_uvars
           ; CancelModule.Lhs    := lhs'
           ; CancelModule.Rhs    := rhs'
           ; CancelModule.Subst  := subst
          |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (CancelModule.INS.existsSubst funcs subst meta_env var_env (length meta_env) new_uvars
            (fun meta_ext : Expr.env types =>
              SUBST.Subst_equations_to funcs meta_ext var_env subst 0 meta_env /\
              let meta_env := meta_ext in
                (Expr.AllProvable_and funcs meta_env var_env
                  (VericSepLogic.himp  
                    (Sep.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap (SH.impures lhs') nil (SH.other lhs'))))
                    (Sep.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
      end ->
      goalD types funcs preds meta_env nil ((hyps, (l, r))).
Proof.
intros.
apply goalD_unfold.
intros.
simpl.
eapply CancelModule.ApplyCancelSep_with_eq.
apply H.
apply H0.
apply X.
apply Expr.typeof_funcs_WellTyped_funcs.
reflexivity. 
apply H3.
auto.
apply H1.
auto.
Qed.

Ltac mirror_cancel boundf boundb prover prover_proof leftr rightr:=
eapply (ApplyCancelSep_with_eq_goal boundf boundb _ _ _ _ _ prover leftr rightr); auto; try solve[ constructor]; try apply prover_proof.

Ltac mirror_cancel_default :=
let types := get_types in 
eapply (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _ (Provers.trivialProver types) nil nil); auto; try solve[ constructor]; try apply trivialProver_correct.