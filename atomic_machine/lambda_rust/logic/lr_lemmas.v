(** Facts about the lambda-Rust semantics of [sq_sem.v] and its steps on the
    atomic machine: evaluation contexts around redexes, the shape of
    sequential steps and external calls, and the locations a step touches. *)

From lrust.lang Require Import tactics.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** * Evaluation contexts around a redex *)

Local Lemma fill_decompose K K' e r :
  redex_shape r -> to_val r = None -> to_val e = None ->
  fill K e = fill K' r -> exists K'', K' = K'' ++ K /\ e = fill K'' r.
Proof.
  intros Hr Hvr Hve. revert K'. induction K as [ | Ki K IH ] using rev_ind; intros K' Hfill.
  - exists K'. by rewrite app_nil_r.
  - destruct K' as [ | Kj K' _ ] using rev_ind.
    + exfalso. rewrite fill_app in Hfill. simpl in Hfill.
      destruct (Hr Ki (fill K e) (eq_sym Hfill)) as [v Hv]. by rewrite fill_not_val in Hv.
    + rewrite !fill_app in Hfill. simpl in Hfill.
      pose proof (fill_item_no_val_inj Ki Kj _ _ (fill_not_val K e Hve)
                    (fill_not_val K' r Hvr) Hfill) as <-.
      apply (inj (fill_item Ki)) in Hfill.
      destruct (IH K' Hfill) as (K'' & -> & ->). exists K''. by rewrite assoc.
Qed.

(** A step of a thread whose expression has redex shape happens at its head. *)

Lemma lr_step_head e m T e' m' :
  redex_shape e -> lr_step e m T e' m' -> lr_head_step e m T e' m'.
Proof.
  intros Hr Hstep. inversion Hstep as [K e1 ? ? e2 ? Hh He]; subst.
  destruct (fill_redex_shape_inv K e1 _ Hr (lr_head_step_not_val _ _ _ _ _ Hh) eq_refl)
    as (-> & _). exact Hh.
Qed.

Lemma lr_external_head e op k :
  redex_shape e -> lr_external e op k -> lr_head_external e op k.
Proof.
  intros Hr Hext. inversion Hext as [K e1 ? k1 Hh He]; subst.
  destruct (fill_redex_shape_inv K e1 _ Hr (lr_head_external_not_val _ _ _ Hh) eq_refl)
    as (-> & _). exact Hh.
Qed.

(** Discharges [redex_shape] side conditions of [lr_step_head] and
    [lr_external_head]. *)
Ltac solve_redex_shape :=
  let Ki := fresh "Ki" in let e' := fresh "e'" in let Heq := fresh "Heq" in
  intros Ki e' Heq; destruct Ki; simpl in Heq; simplify_eq; rewrite /= ?to_of_val; by eauto.

(** * Steps and external calls under evaluation contexts *)

Lemma lr_external_fill K e op k :
  lr_external e op k -> exists k',
    lr_external (fill K e) op k' /\ forall ov, k' ov = fill K (k ov).
Proof.
  intros H. destruct H as [K' e op k Hh].
  exists (fun ov => fill (K' ++ K) (k ov)).
  rewrite -fill_app. split; [by constructor | intro ov; by rewrite fill_app].
Qed.

Lemma lr_external_fill_inv K e op k :
  to_val e = None -> lr_external (fill K e) op k ->
  exists k', lr_external e op k' /\ forall ov, k ov = fill K (k' ov).
Proof.
  intros Hv He. inversion He as [K' r op' kr Hh Heq]; subst.
  destruct (fill_decompose K K' e r (lr_head_external_redex_shape _ _ _ Hh)
    (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
  exists (fun ov => fill K'' (kr ov)). split; first by constructor.
  intro ov. by rewrite fill_app.
Qed.

Lemma lr_step_fill_inv K e m T e2 m2 :
  to_val e = None -> lr_step (fill K e) m T e2 m2 ->
  exists e2', e2 = fill K e2' /\ lr_step e m T e2' m2.
Proof.
  intros Hv Hs. inversion Hs as [K' r m0 T0 r' m0' Hh Heq]; subst.
  destruct (fill_decompose K K' e r (lr_head_step_redex_shape _ _ _ _ _ Hh)
    (lr_head_step_not_val _ _ _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
  exists (fill K'' r'). split; [by rewrite fill_app | by constructor].
Qed.

(** * Literal comparisons *)

Lemma lr_lit_eq_int (m : lr_mem) z1 z2 : sq_mem.lit_eq m (LitInt z1) (LitInt z2) -> z1 = z2.
Proof. by inversion 1. Qed.

Lemma lr_lit_neq_int z1 z2 : lit_neq (LitInt z1) (LitInt z2) -> z1 ≠ z2.
Proof. by inversion 1. Qed.
