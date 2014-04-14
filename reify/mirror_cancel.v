Require Import MirrorShard.CancelTacBedrock.
Require Export MirrorShard.Expr MirrorShard.SepExpr.
Require Import MirrorShard.SepHeap MirrorShard.SepCancel.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Export sep.
Require Import FMapInterface.
Require Import SimpleInstantiation.
Require Import MirrorShard.ExprUnifySynGenRec.
Require Export wrapExpr.
Require Import Prover.
Require Import MirrorShard.provers.ReflexivityProver.
Require Export reify_derives.
Require Import symmetry_prover.
Require Import seplog.
Require Import hints.
Require Import congruence_prover.

Module SH := SepHeap.Make VericSepLogic Sep.
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
      forall (meta_env : Expr.env types) (hyps : Expr.exprs) preds funcs prover hintsFwd hintsBwd,
      forall (l r : Sep.sexpr) res,
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

Lemma derives_emp : seplog.derives seplog.emp  seplog.emp.
apply seplog.derives_refl.
Proof.
Qed.

Ltac mirror_cancel boundf boundb prover prover_proof leftr rightr:=
eapply (ApplyCancelSep_with_eq_goal boundf boundb _ _ _ _ _ prover leftr rightr); auto; try solve[ constructor]; try apply prover_proof.

Section typed.
  Variable ts : list Expr.type.
  Variable fs : functions ts.
  Variable user_comp : func -> bool.

Require Import computation_prover.

Definition vst_prover : ProverT :=
    composite_ProverT ( composite_ProverT (composite_ProverT reflexivityProver symmetryProver)
                                          (computationProver fs user_comp))
                      (VST_CONGRUENCE_PROVER.congruenceProver).

  Definition vstProver_correct : ProverT_correct vst_prover fs.
  Proof.
   repeat eapply composite_ProverT_correct; 
      auto using reflexivityProver_correct, symmetryProver_correct, computationProver_correct,
      VST_CONGRUENCE_PROVER.congruenceProver_correct.
  Qed.
End typed.

Definition user_comp : func -> bool := fun _ => false.

Ltac e_vm_compute_left :=
match goal with 
| |- ?X = Some _ => match eval vm_compute in X with 
                   | Some ?Y => exact (@eq_refl _ (Some Y) (*<: (Some Y) = (Some Y)*))
                   end
| |- ?X = _ => let comp := eval vm_compute in X in exact (@eq_refl _ X)
end.


Ltac mirror_cancel_default :=
let types := get_types in 
let funcs := get_funcs types in
(* ensure hints/lemmas are processed as tuples correctly *)
(* TODO figure out if there are issue with processing singletons *)
let left_hints := eval hnf in left_hints in
let right_hints := eval hnf in right_hints in
eapply (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _ (vst_prover types funcs user_comp) left_lemmas right_lemmas); 
[ reflexivity
| HintModule.prove left_hints
| HintModule.prove right_hints
| apply vstProver_correct
| first [e_vm_compute_left | fail "Canceler failed"]
| repeat (split; try assumption; try apply I; try apply derives_emp)].
