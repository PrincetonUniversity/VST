Require Import MirrorShard.CancelTacBedrock.
Require Export MirrorShard.Expr MirrorShard.SepExpr.
Require Import MirrorShard.SepHeap MirrorShard.SepCancel.
Require Import MirrorShard.SepLemma.
Require Import MirrorShard.ReifyHints.
Require Import MirrorShard.Env.
Require Export sep.
Require Import FMapInterface.
Require Import MirrorShard.ExprUnifySynGenRec.
Require Export wrapExpr.
Require Import Prover.
Require Import MirrorShard.provers.ReflexivityProver.
Require Import SimpleInstantiation.
Require Export reify_derives.
Require Import symmetry_prover.
Require Import computation_prover.
Require Import seplog.
Require Import hints.
Require Import types.
Require Import functions.

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

Lemma derives_emp : seplog.derives seplog.emp  seplog.emp.
apply seplog.derives_refl.
Proof.
Qed.

Ltac mirror_cancel boundf boundb prover prover_proof leftr rightr:=
eapply (ApplyCancelSep_with_eq_goal boundf boundb _ _ _ _ _ prover leftr rightr); auto; try solve[ constructor]; try apply prover_proof.

(* like all_types_r, but without applying repr (confusingly)
     maybe this should be defined elsewhere? maybe all_types_r
     should be defined in terms of this? *)
Definition all_types_repr := listToRepr our_types EmptySet_type.

Import ListNotations.
Section typed.
  Variable ts : list Expr.type.
  Let ours_ts := all_types_r ts.


  (* we can instantiate types, but not yet functions *)
  Variable repr_fs :
    forall ts' : list Expr.type,
      list (Expr.signature (all_types_r ts')).

  Let fs_inst := 
    (repr (listToRepr (repr_fs ts)
                      (Default_signature ours_ts)) nil).

  Definition vst_prover : ProverT ours_ts :=
    fold_right (@composite_ProverT ours_ts)
               (@reflexivityProver ours_ts)
               [(@symmetryProver ours_ts);
                (@computationProver all_types_repr repr_fs ts)].

  Variable fs : functions ours_ts.

  Definition vstProver_correct : ProverT_correct vst_prover fs_inst.
  Proof.
    repeat (eapply composite_ProverT_correct;
            eauto using reflexivityProver_correct,
                       symmetryProver_correct,
                       (computationProver_correct all_types_repr repr_fs ts)).
  Qed.
End typed.

(* Check (forall types funcs, vstProver_correct types *)

Check vstProver_correct.

Ltac mirror_cancel_default :=
let types := get_types in 
let funcs := get_funcs in
eapply (ApplyCancelSep_with_eq_goal 100 100 _ _ _ _ _ (vst_prover types) left_lemmas right_lemmas); 
[ reflexivity
| HintModule.prove left_hints
| HintModule.prove right_hints
| apply vstProver_correct (*types (constr: (fun ts' => repr ( ))))*)
| reflexivity
| try (split; [try apply I | try apply derives_emp])].
