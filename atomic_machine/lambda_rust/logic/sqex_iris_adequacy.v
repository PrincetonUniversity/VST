(** [at_sem_adequate] is Iris's notion of [adequate] plus race freedom.
    This file proves that [at_sem_adequate] implies [adequate] for at_step.
*)

From stdpp Require Import relations.
From iris.program_logic Require Import language adequacy.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance ext_specs.

(** ** The machine as an Iris language *)

Definition am_prim_step (e : sq_expr) (m : lr_mem) (κ : list (am_event loc))
    (e' : sq_expr) (m' : lr_mem) (efs : list sq_expr) : Prop :=
  exists o, at_step e m κ e' m' o /\ efs = option_list o.

Lemma am_lang_mixin : LanguageMixin (of_val : sq_val -> sq_expr) to_val am_prim_step.
Proof.
  split.
  - apply to_of_val.
  - apply of_to_val.
  - intros e m κ e' m' efs (o & Hst & _).
    inversion Hst; subst; [by eapply lr_step_not_val | by eapply lr_external_not_val ..].
Qed.

(** Not canonical: [sq_lang] is the canonical language of these types. *)
Definition am_lang : language := Language am_lang_mixin.

(** ** Iris executions are machine executions *)

Lemma map_seq_step {A} (t1 t2 : list A) e1 e2 :
  map_seq 0 (t1 ++ e2 :: t2) =@{gmap nat A}
    <[length t1 := e2]> (map_seq 0 (t1 ++ e1 :: t2)).
Proof.
  rewrite insert_map_seq_0; last (rewrite length_app /=; lia).
  f_equal. rewrite insert_app_r_alt; last done. by rewrite Nat.sub_diag.
Qed.

Lemma am_lang_step_am_step (ρ1 ρ2 : cfg am_lang) :
  erased_step ρ1 ρ2 ->
  am_step_any (AMCfg (map_seq 0 ρ1.1 : sqex_tpool) ρ1.2)
    (AMCfg (map_seq 0 ρ2.1 : sqex_tpool) ρ2.2).
Proof.
  intros [κ [e1 σ1 e2 σ2 efs t1 t2 -> -> Hps]].
  destruct Hps as (o & Hst & ->). exists (length t1), κ. simpl.
  have Hget : (map_seq 0 (t1 ++ e1 :: t2) : gmap nat sq_expr) !! length t1 = Some e1.
  { rewrite lookup_map_seq_0. by apply list_lookup_middle. }
  destruct o as [c_new|]; simpl.
  - (* The forked thread is appended, i.e. gets the least unused index. *)
    rewrite app_comm_cons (assoc_L app) map_seq_snoc (map_seq_step t1 t2 e1 e2) /=.
    eapply AMStepSpawn; [exact Hget | exact Hst | | ].
    + apply (lookup_map_seq_None (M := gmap nat)). rewrite !length_app /=.
      unfold sq_expr in *. lia.
    + intros k Hk. rewrite (lookup_map_seq_0 (M := gmap nat)). apply lookup_lt_is_Some_2.
      move: Hk. rewrite !length_app /=. unfold sq_expr in *. lia.
  - rewrite app_nil_r (map_seq_step t1 t2 e1 e2).
    by eapply AMStep.
Qed.

Lemma am_lang_steps_am_steps (ρ1 ρ2 : cfg am_lang) :
  rtc erased_step ρ1 ρ2 ->
  am_steps (AMCfg (map_seq 0 ρ1.1 : sqex_tpool) ρ1.2)
    (AMCfg (map_seq 0 ρ2.1 : sqex_tpool) ρ2.2).
Proof.
  induction 1 as [|ρ1 ρ2 ρ3 Hstep _ IH]; first apply rtc_refl.
  eapply rtc_l; [by apply am_lang_step_am_step | exact IH].
Qed.

(** ** Adequacy *)

Lemma at_sem_adequate_iris (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  at_sem_adequate [e] [φ] m -> adequate (Λ := am_lang) NotStuck e m (fun v _ => φ v).
Proof.
  intros Hadeq. split.
  - intros t2 σ2 v2 Hsteps.
    apply am_lang_steps_am_steps in Hsteps.
    destruct (Hadeq _ _ Hsteps) as (_ & _ & Hpost).
    eapply (Hpost 0%nat (of_val v2));
      [by rewrite (lookup_map_seq_0 (M := gmap nat)) | apply to_of_val | done].
  - intros t2 σ2 e2 _ Hsteps Hin.
    apply am_lang_steps_am_steps in Hsteps.
    destruct (Hadeq _ _ Hsteps) as (_ & Hsafe & _).
    apply list_elem_of_lookup in Hin as [i Hi].
    destruct (Hsafe i e2) as [Hfinal | (evs & c' & m' & oc & Hst)].
    { by rewrite (lookup_map_seq_0 (M := gmap nat)). }
    + left. exact Hfinal.
    + right. exists evs, c', m', (option_list oc). by exists oc.
Qed.

Lemma sqex_iris_adequacy Σ `{!lrSqGpreS Σ} (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ}, ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  adequate (Λ := am_lang) NotStuck e m (fun v _ => φ v).
Proof. intros Hwp. apply at_sem_adequate_iris. by apply (sqex_adequacy Σ). Qed.
