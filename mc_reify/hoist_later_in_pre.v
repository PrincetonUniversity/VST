Require Import floyd.proofauto.
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Require Export mc_reify.reify.
Require Export mc_reify.bool_funcs.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
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
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
Require Import mc_reify.typ_eq.
Require Import mc_reify.rtac_base.

(************************************************

Lemmas for rtac version of hoist_later_in_pre

************************************************)

Fixpoint rstrip_1_later_sep (R: expr typ func) : expr typ func :=
  match R with
  | Inj (inr (Data (fnil tympred))) => Inj (inr (Data (fnil tympred)))
  | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
    match hd with
    | App (Inj (inr (Smx flater))) hd0 => App (App (Inj (inr (Data (fcons tympred)))) hd0) (rstrip_1_later_sep tl)
    | _ => App (App (Inj (inr (Data (fcons tympred)))) hd) (rstrip_1_later_sep tl)
    end
  | _ => Inj (inr (Data (fnil tympred)))
  end.

Lemma SEPx_map_liftx: forall R, SEPx (map liftx R) = liftx (fold_right sepcon emp R).
Proof.
  intros.
  extensionality rho.
  unfold_lift; simpl.
  induction R.
  + reflexivity.
  + simpl.
    rewrite <- IHR.
    unfold SEPx.
    simpl.
    reflexivity.
Qed.

Lemma hoist_later_in_pre_aux:
    forall temp var ret gt s
      gs P T1 T2 R R' Post,
  forall {Espec: OracleKind},
      fold_right sepcon emp R |-- |> (fold_right sepcon emp R') ->
      semax (mk_tycontext temp var ret gt gs) (|> (assertD P (localD T1 T2) R')) s (normal_ret_assert Post) ->
      semax (mk_tycontext temp var ret gt gs) (assertD P (localD T1 T2) R) s (normal_ret_assert Post).
Proof.
  intros.
  eapply semax_pre0; [| exact H0].
  unfold assertD.
  apply PROP_later_derives.
  apply LOCAL_later_derives.
  rewrite !SEPx_map_liftx.
  intro.
  unfold_lift; simpl.
  exact H.
Qed.

Lemma fold_right_sepcon_later_derives: forall P P' Q Q' R,
  P |-- |> P' ->
  fold_right sepcon emp Q |-- |> (fold_right sepcon emp Q') ->
  (fold_right sepcon emp (P' :: Q')) = R ->
  fold_right sepcon emp (P :: Q) |-- |> R.
Proof.
  intros.
  subst.
  simpl.
  rewrite later_sepcon.
  apply sepcon_derives; auto.
Qed.

Lemma mpred_now_later: forall (P: mpred), P |-- |> P.
Proof.
  apply now_later.
Qed.

Lemma mpred_derives_refl: forall (P: mpred), P |-- P.
Proof.
  apply derives_refl.
Qed.

(************************************************

Reified Lemmas

************************************************)

Definition reify_hlip_base (temp : PTree.t (type * bool)) (var : PTree.t type)
         (ret : type) (gt : PTree.t type) (s : statement) : my_lemma.
reify_lemma reify_vst (hoist_later_in_pre_aux temp var ret gt s).
Defined.

(* Print reify_hlip_base. *)

Definition reify_hlip_ind : my_lemma.
reify_lemma reify_vst (fold_right_sepcon_later_derives).
Defined.

(* Print reify_hlip_ind. *)

Definition reify_now_later : my_lemma.
reify_lemma reify_vst mpred_now_later.
Defined.

(* Print reify_now_later. *)

Definition reify_derives_refl : my_lemma.
reify_lemma reify_vst mpred_derives_refl.
Defined.

(* Print reify_derives_refl. *)

Section tbled.

Variable tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Fixpoint solve_strip_1_later (R: expr typ func) : rtac typ (expr typ func) :=
  match R with
  | Inj (inr (Data (fnil tympred))) => EAPPLY typ func reify_now_later
  | App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
    let solve_head :=
    match hd with
    | App (Inj (inr (Smx flater))) _ => EAPPLY typ func reify_derives_refl
    | _ => EAPPLY typ func reify_now_later
    end in
    THEN (EAPPLY typ func reify_hlip_ind)
     (THEN (TRY (REFLEXIVITY tbl))
           (FIRST [solve_head; solve_strip_1_later tl]))
  | _ => FAIL
  end.

End tbled.

Require Import mc_reify.reverse_defs.
Require Import symexe.
Require Import mc_reify.func_defs.
Require Import mc_reify.denote_tac.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Lemma skip_triple : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
      Sskip 
     (normal_ret_assert (|> assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
intros.
unfold empty_tycontext.

(*
eapply hoist_later_in_pre_aux.
(*instantiate (1:= [data_at sh (tptr tint) (default_val (tptr tint)) (force_ptr v)]).*)
reify_expr_tac.
Eval vm_compute in 
(run_tac (THEN INTROS (EAPPLY typ func reify_hlip_ind)) e0).


eapply fold_right_sepcon_later_derives.
*)
reify_expr_tac.
(*
Eval vm_compute in
(run_tac (THEN (EAPPLY typ func (reify_hlip_base PTree.Leaf PTree.Leaf Tvoid PTree.Leaf Sskip))
         (THEN INTROS (TRY (EAPPLY typ func reify_hlip_ind)))) e0).
*)
Eval vm_compute in
(run_tac (THEN (EAPPLY typ func (reify_hlip_base PTree.Leaf PTree.Leaf Tvoid PTree.Leaf Sskip))
               (TRY (solve_strip_1_later tbl
                   (App
                      (App (Inj (inr (Data (fcons tympred))))
                         (App
                            (App
                               (App (Inj (inr (Sep (fdata_at (tptr tint)))))
                                  (Ext 3%positive)) 
                               (Ext 4%positive))
                            (App (Inj (inr (Other fforce_ptr)))
                               (Ext 5%positive))))
                      (Inj (inr (Data (fnil tympred)))))))) e0).

