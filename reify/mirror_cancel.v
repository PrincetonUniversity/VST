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
Require Import preproc.
Require Import congruence_prover.
Require Import floyd.proofauto.

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


Lemma solve_emp_tt : emp |-- TT.
entailer!.
Qed.

Lemma prove_TT' : forall P, P |-- TT'.
intros.
entailer!.
Qed.

Ltac cleanup_cancel :=
intros;
try match goal with
 | |-  _ /\ _ => split; cleanup_cancel
 | |- _ = _ => reflexivity
 | |- _ |-- TT' => apply prove_TT'
 | |- _ |-- TT'' => apply prove_TT'
 | |- _ |-- prop True => apply prove_TT'
 | |- emp |-- emp => exact derives_emp
 | |- True => exact I
 | |- _ => assumption
end.

Ltac get_types_name :=
match goal with 
| [ H := _ : (list Expr.type) |- _] => H
end.

Ltac get_funcs_name t := 
match goal with
| [ X := _ : list (Expr.signature t) |- _ ] => X
 end.

Ltac get_predicates_name t :=
match goal with
[ X := _ : list (Sep.predicate t) |- _] => X end.

Ltac get_uenv_name t := 
match goal with 
| [ X := _ : Expr.env t |- _ ] => X
| [ X := _ : list (sigT (Expr.tvarD t)) |- _ ] => X
end.

(*If you are getting huge terms when the canceller is done, this is the place
to look first. Try adding any functions you see in that term to this
whitelist*)
Ltac our_cbv :=
let types' := get_types in
let types := get_types_name in
let funcs := get_funcs_name types' in
let preds := get_predicates_name types' in 
let uenv := get_uenv_name types' in
cbv [
exprD functionTypeD applyD
forallEach AllProvable_impl AllProvable_gen AllProvable_and projT1 projT2 Provable lookupAs
nth_error equiv_dec length fold_right tvarD Impl_ EqDec_tvar eq_nat_dec
CancelModule.INS.existsSubst
SUBST.Subst_equations_to SUBST.Subst_lookup SUBST.subst_lookup
FM.find FM.Raw.find FM.this
Basics.impl Impl Exc
Sep.sexprD Sep.SDenotation Sep.SDomain Denotation Domain Range 
SH.sheapD SH.pures SepHeap.FM.fold SepHeap.FM.Raw.fold SH.starred SepHeap.FM.this
SH.other SH.impures
NatMap.Ordered_nat.compare  NatMap.Ordered_nat.eq nat_compare EqDec_tvar tvar_rec tvar_rect Range
VericSepLogic.himp  VericSepLogic.inj VericSepLogic.star VericSepLogic_Kernel.emp VericSepLogic.hprop
sumbool_rec sumbool_rect nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym f_equal
funcs preds types uenv abbreviate value

functions.two_power_nat_signature functions.O_signature functions.force_ptr_signature
functions.app_val_signature functions.int_max_unsigned_signature functions.and_signature
functions.align_signature functions.cons_val_signature functions.int_sub_signature 
functions.Vint_signature functions.map_Vint_signature functions.typed_true_signature 
functions.int_add_signature functions.S_signature functions.Z_lt_signature
functions.Z_le_signature functions.Z_gt_signature functions.Z_ge_signature
functions.Zpos_signature functions.Zneg_signature functions.Z0_signature
functions.xI_signature functions.xO_signature functions.xH_signature functions.int_lt_signature
functions.int_ltu_signature functions.int_mul_signature functions.int_neg_signature 
functions.Z_add_signature functions.Z_sub_signature functions.Z_mul_signature
functions.Z_div_signature functions.Z_mod_signature functions.Z_max_signature
functions.Z_opp_signature functions.Ceq_signature functions.Cne_signature
functions.Clt_signature functions.Cle_signature functions.Cgt_signature
functions.Cge_signature functions.int_cmp_signature functions.int_cmpu_signature
functions.int_repr_signature functions.int_signed_signature functions.int_unsigned_signature
functions.nullval_signature functions.tptr_signature functions.nil_val_signature
functions.reverse_t_struct_list_signature functions.reverse__tail_signature
functions.True_signature functions.eval_id_signature

types.tycontext_tv 
types.c_expr_tv types.c_type_tv types.environ_tv types.val_tv types.share_tv 
types.ident_tv types.list_val_tv types.list_int_tv types.int_tv types.Z_tv
types.nat_tv types.positive_tv types.bool_tv types.comparison_tv types.tc_assert_tv 
types.our_types 

types.tycontext_type
types.c_expr_type types.c_type_type types.environ_type types.val_type types.share_type 
types.ident_type types.list_val_type types.list_int_type  types.int_type types.Z_type
types.nat_type types.positive_type types.bool_type types.comparison_type
types.tc_assert_type
types.no_eqb_type 

Env.repr Env.listToRepr].

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
| first [simpl (Sep.typeof_preds); simpl (typeof_env); e_vm_compute_left | fail "Canceler failed"]
| our_cbv; cleanup_cancel].

Ltac rcancel := try (pose_env; reify_derives; mirror_cancel_default; try (simpl; clear_all)). 
