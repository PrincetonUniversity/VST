(** [at_sem_adequate] is Iris's notion of [adequate] plus race freedom.
    This file proves that [at_sem_adequate] implies [adequate] for at_step.
    FIXME is this useful?
*)

From stdpp Require Import relations.
From iris.program_logic Require Export language adequacy.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.sqex_adequacy.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Section language.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr}.
  Local Notation C := (@sqlang_thrd_st _ _ _ _ _ _ _ L).

(** ** The machine as an Iris language *)

(** Iris requires a canonical embedding of values. These operations are
    supplied only to this adapter; EXWP and machine adequacy use final results
    directly and do not require such an embedding. *)
Context (of_val : Val -> C)
  (final_of_val : forall v, sqlang_is_final (of_val v) = Some v)
  (of_final : forall e v, sqlang_is_final e = Some v -> of_val v = e).

Definition am_prim_step (e : C) (m : Mem) (κ : list (am_event Loc))
    (e' : C) (m' : Mem) (efs : list C) : Prop :=
  exists o, at_step e m κ e' m' o /\ efs = option_list o.

Lemma am_lang_mixin : LanguageMixin of_val sqlang_is_final am_prim_step.
Proof using final_of_val of_final.
  split.
  - apply final_of_val.
  - apply of_final.
  - intros e m κ e' m' efs (o & Hst & _).
    pose proof (sqlang_external_not_final e m) as Hext.
    inversion Hst; subst; [by eapply sqlang_step_not_final | by eapply Hext ..].
Qed.

(** The concrete language supplies its canonical Iris language instance. *)
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
  am_step_any (AMCfg (map_seq 0 ρ1.1 : am_tpool) ρ1.2)
    (AMCfg (map_seq 0 ρ2.1 : am_tpool) ρ2.2).
Proof.
  intros [κ [e1 σ1 e2 σ2 efs t1 t2 -> -> Hps]].
  destruct Hps as (o & Hst & ->). exists (length t1), κ. simpl.
  have Hget : (map_seq 0 (t1 ++ e1 :: t2) : gmap nat C) !! length t1 = Some e1.
  { rewrite lookup_map_seq_0. by apply list_lookup_middle. }
  destruct o as [e_new|]; simpl.
  - (* The forked thread is appended, i.e. gets the least unused index. *)
    rewrite app_comm_cons (assoc_L app) map_seq_snoc (map_seq_step t1 t2 e1 e2) /=.
    eapply AMStepSpawn; [exact Hget | exact Hst | | ].
    + apply (lookup_map_seq_None (M := gmap nat)). rewrite !length_app /=.
      lia.
    + intros k Hk. rewrite (lookup_map_seq_0 (M := gmap nat)). apply lookup_lt_is_Some_2.
      move: Hk. rewrite !length_app /=. lia.
  - rewrite app_nil_r (map_seq_step t1 t2 e1 e2).
    by eapply AMStep.
Qed.

Lemma am_lang_steps_am_steps (ρ1 ρ2 : cfg am_lang) :
  rtc erased_step ρ1 ρ2 ->
  am_steps (AMCfg (map_seq 0 ρ1.1 : am_tpool) ρ1.2)
    (AMCfg (map_seq 0 ρ2.1 : am_tpool) ρ2.2).
Proof.
  induction 1 as [|ρ1 ρ2 ρ3 Hstep _ IH]; first apply rtc_refl.
  eapply rtc_l; [by apply am_lang_step_am_step | exact IH].
Qed.

(** ** Adequacy *)

Lemma at_sem_adequate_iris (e : C) (φ : Val -> Prop) (m : Mem) :
  at_sem_adequate [e] [φ] m -> adequate (Λ := am_lang) NotStuck e m (fun v _ => φ v).
Proof.
  intros Hadeq. split.
  - intros t2 σ2 v2 Hsteps.
    apply am_lang_steps_am_steps in Hsteps.
    destruct (Hadeq _ _ Hsteps) as (_ & _ & Hpost).
    eapply (Hpost 0%nat (of_val v2));
      [by rewrite (lookup_map_seq_0 (M := gmap nat)) | apply final_of_val | done].
  - intros t2 σ2 e2 _ Hsteps Hin.
    apply am_lang_steps_am_steps in Hsteps.
    destruct (Hadeq _ _ Hsteps) as (_ & Hsafe & _).
    apply list_elem_of_lookup in Hin as [i Hi].
    destruct (Hsafe i e2) as [Hfinal | (evs & e' & m' & oc & Hst)].
    { by rewrite (lookup_map_seq_0 (M := gmap nat)). }
    + left. exact Hfinal.
    + right. exists evs, e', m', (option_list oc). by exists oc.
Qed.

End language.
