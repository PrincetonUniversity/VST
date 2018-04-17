Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.forward_lemmas VST.floyd.call_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.globals_lemmas.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Local Open Scope logic.

Lemma rel_lvalue_var {cs: compspecs}:
 forall (P: mpred) i t v rho,
 v = eval_var i t rho ->
 isptr v ->
 P |-- rel_lvalue (Evar i t) v rho.
Proof.
intros.
destruct v; try contradiction.
unfold eval_var in H.
destruct (Map.get (ve_of rho) i) eqn:?.
destruct p.
destruct (eqb_type t t0) eqn:?.
apply eqb_type_true in Heqb1; subst.
inv H.
apply rel_lvalue_local.
apply prop_right; auto.
inv H.
destruct (ge_of rho i) eqn:?; inv H.
apply rel_lvalue_global.
apply prop_right; split; auto.
Qed.

Lemma isptr_not_Vundef:
  forall v, isptr v -> v <> Vundef.
Proof.
intros. intro; subst; inv H.
Qed.

Lemma eval_id_get:
  forall rho i v, eval_id i rho = v -> v <> Vundef -> Map.get (te_of rho) i = Some v.
Proof.
intros.
unfold eval_id in H.
destruct (Map.get (te_of rho) i).
f_equal; assumption.
subst. contradiction H0; auto.
Qed.

Ltac instantiate_Vptr :=
  match goal with
  | H:isptr (eval_id ?i ?rho), A:name ?i
    |- _ =>
        let b := fresh "b_" A in
        let z := fresh "z_" A in
        let J := fresh "H_" A in
        destruct (eval_id i rho) as [| | | | | b z] eqn:J; try contradiction H;
         clear H; symmetry in J; rename J into H
  | H:isptr (eval_id ?i ?rho)
    |- _ =>
        let b := fresh "b_"  in
        let z := fresh "z_"  in
        let J := fresh "H_"  in
        destruct (eval_id i rho) as [| | | | | b z] eqn:J; try contradiction H;
         clear H; symmetry in J; rename J into H
  end.

Ltac solve_nth_error :=
match goal with |- @nth_error ?T (?A::_) ?n = Some ?B =>
 first [unify n O; unfold nth_error, value; repeat f_equal; reflexivity
        | let b := fresh "n" in evar (b:nat);  unify n (S b);
          unfold nth_error; fold (@nth_error  T); solve_nth_error
        ]
end.

Ltac rewrite_eval_id :=
 repeat match goal with H: ?v = (eval_id ?i ?rho) |- context [ (eval_id ?i ?rho) ] =>
    rewrite <- H
 end.

Lemma rel_expr_nested_load {cs: compspecs}:
  forall sh p t_root v e lr efs tts gfs P rho,
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type2 t_root gfs) = true ->
  P |-- rel_LR e lr p rho && efield_denote efs gfs rho && (data_at sh t_root v p * TT) ->
  P |-- rel_expr (nested_efield e efs tts) (repinject _ (proj_reptype t_root gfs v)) rho.
Abort. (* not needed *)

Lemma sc_semax_load_store:  forall {Espec: OracleKind} {CS: compspecs},
 forall p (Delta: tycontext) t_root e lr efs tts gfs e2 sh v0 v2 P P',
  writable_share sh ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type2 t_root gfs) = true ->
  P |-- !! (tc_val (nested_field_type2 t_root gfs) (repinject _ v2))
           && rel_lvalue e p
           && rel_expr (Ecast e2 (typeof (nested_efield e efs tts))) (repinject _ v2)
           && (`(data_at sh t_root v0 p) * P') ->
  semax Delta (|> P) (Sassign (nested_efield e efs tts) e2)
          (normal_ret_assert (`(data_at sh t_root (upd_reptype t_root gfs v0 v2) p) * P')).
Abort.

Lemma rel_expr_array_load: True.
Proof. auto. Qed.

Ltac rel_expr :=
first [
   simple eapply rel_expr_array_load; [reflexivity | reflexivity | apply Coq.Init.Logic.I
   | repeat apply andp_right; [rel_expr | rel_expr | rewrite_eval_id; cancel | entailer.. ]]
 | simple apply rel_expr_tempvar;  apply eval_id_get; [solve [eauto] | congruence ]
 | simple eapply rel_expr_cast; [rel_expr | try (simpl; rewrite_eval_id; reflexivity) ]
 | simple eapply rel_expr_unop; [rel_expr | try (simpl; rewrite_eval_id; reflexivity) ]
 | simple eapply rel_expr_binop; [rel_expr | rel_expr | try (simpl; rewrite_eval_id; reflexivity) ]
 | simple apply rel_expr_const_int
 | simple apply rel_expr_const_float
 | simple apply rel_expr_const_single
 | simple apply rel_expr_const_long
 | simple apply rel_lvalue_var; [ eassumption | assumption]
(*
 | simple eapply rel_lvalue_local
 | simple eapply rel_lvalue_global
*)
 | simple eapply rel_lvalue_deref; [rel_expr ]
 | simple eapply rel_lvalue_field_struct; [ reflexivity | reflexivity | rel_expr ]
 | simple eapply rel_expr_lvalue_By_value; [ reflexivity | rel_expr | rewrite_eval_id; cancel | ]
 | simple eapply rel_expr_lvalue_By_reference; [ reflexivity | rel_expr ]
(* | match goal with |- in_range _ _ _ => hnf; omega end *)
 | idtac
 ].


Ltac forward_nl :=
 hoist_later_in_pre;
 first
 [ simple eapply semax_seq';
   [simple eapply semax_loadstore_array;
       [ reflexivity | apply Coq.Init.Logic.I | reflexivity | reflexivity| reflexivity
       | entailer; repeat instantiate_Vptr; repeat apply andp_right;
               rel_expr
       | try solve_nth_error | auto | auto | hnf; try omega ]
    | unfold replace_nth; simpl valinject; abbreviate_semax ]
 | eapply semax_post_flipped';
   [simple eapply semax_loadstore_array;
       [ reflexivity | apply Coq.Init.Logic.I | reflexivity | reflexivity| reflexivity
       | entailer; repeat instantiate_Vptr; repeat apply andp_right;
               rel_expr
       | try solve_nth_error | auto | auto | hnf; try omega ]
    |  ]
 | simple eapply semax_seq';
    [eapply semax_set_forward_nl;
      [reflexivity | entailer; repeat instantiate_Vptr; rel_expr | try apply Coq.Init.Logic.I ]
      | let old := fresh "old" in apply exp_left; intro old;
        autorewrite with subst; try rewrite insert_local; abbreviate_semax
     ]
 | eapply semax_post_flipped';
    [eapply semax_set_forward_nl;
      [reflexivity | entailer; repeat instantiate_Vptr; rel_expr | try apply Coq.Init.Logic.I ]
      | let old := fresh "old" in apply exp_left; intro old;
        autorewrite with subst; try rewrite insert_local
     ]
  ].

