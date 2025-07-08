(* adapted from iris_heap_lang/proofmode.v *)
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From compcert.common Require Import Values.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.veric Require Import mpred seplog juicy_base Clight_base Clight_core mapsto_memory_block env tycontext lifting_expr lifting.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.floyd Require Import functional_base.

Ltac reshape_seq :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ (Ssequence ?s _) ?Q) => iApply wp_seq; reshape_seq
  | _ => idtac
  end.

Lemma tac_wp_expr_eval `{!VSTGS OK_ty Σ} Δ OK_spec ge E f Q e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (wp OK_spec ge E f e' Q) →
  envs_entails Δ (wp OK_spec ge E f e Q).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?OK_spec ?ge ?E ?f ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.


(* This works, but there are almost no Clight steps that meet the definition of PureExec.
Lemma wp_pure_step_later `{!VSTGS OK_ty Σ} OK_spec ge E f s1 s2 φ n Q :
  PureExec ge φ n s1 s2 →
  φ →
  (bi_laterN(PROP := monpred.monPredI _ _) n (wp OK_spec ge E f s2 Q) ⊢ wp OK_spec ge E f s1 Q).
Proof.
  intros Hexec ?; induction Hexec; [done | | done].
  rewrite /= IHp /wp. (* simpl; rewrite IHp; unfold wp. *)
  iIntros "H" (???) "L Hk".
  rewrite /assert_safe /=.
  do 4 (iApply embed_forall; iIntros (?)).
  iIntros "Hρ %%".
  iApply juicy_extspec.jsafe_local_step.
  { apply Hstep. }
  iSpecialize ("H" with "[//]").
  rewrite !bi.later_wand.
  iSpecialize ("H" with "L Hk").
  iPoseProof (embed_later with "H") as "H".
  iApply ("H" with "[Hρ]"); try done.
  rewrite embed_later; iIntros "!>".
  iApply "Hρ".
Qed.

Lemma tac_wp_pure `{!VSTGS OK_ty Σ} Δ Δ' OK_spec ge E f e1 e2 φ n Q :
  PureExec ge φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (wp OK_spec ge E f e2 Q) →
  envs_entails Δ (wp OK_spec ge E f e1 Q).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' wp_pure_step_later //.
Qed.

(* We'll probably need another wp_pure lemma for wp_expr. *)*)

Definition ob_cond `{!VSTGS OK_ty Σ} {A B} P (Q : A → B → assert) := λ x : A, ∃ y, <affine> ⌜P x y⌝ ∗ Q x y.

Definition ob_cond1 `{!VSTGS OK_ty Σ} {A} P (Q : A → assert) := λ x : A, <affine> ⌜P x⌝ ∗ Q x.

Ltac ob_cond_tac :=
  lazymatch goal with
  | |- envs_entails ?Δ (ob_cond ?P _ _) =>
      iExists _; iSplit; [iPureIntro; try done | simpl align; cbv match]
  | |- envs_entails ?Δ (ob_cond1 ?P _ _) =>
      iSplit; [iPureIntro; try done | cbv match]
  | _ => fail "no such ob"
  end.

(* maybe seal *)
Definition ob_check `{!VSTGS OK_ty Σ} (R : Prop) (P Q : assert) := <affine> ⌜R⌝ ∗ ▷ <absorb> P ∧ Q.

(* Not sure we need this.
Definition ob_check_ex `{!VSTGS OK_ty Σ} {A} R P (Q : assert) := (▷ ∃ x : A, <absorb> P x ∧ ⌜R x⌝) ∧ Q.*)

#[export] Hint Rewrite Ptrofs.repr_signed : ints.
#[export] Hint Rewrite Ptrofs.repr_unsigned : ints.
#[export] Hint Rewrite Int.repr_signed : ints.
#[export] Hint Rewrite Int.repr_unsigned : ints.
#[export] Hint Rewrite Ptrofs.signed_repr using rep_lia : ints.
#[export] Hint Rewrite Ptrofs.unsigned_repr using rep_lia : ints.
#[export] Hint Rewrite Int.signed_repr using rep_lia : ints.
#[export] Hint Rewrite Int.unsigned_repr using rep_lia : ints.

Ltac simplify_ofs := rewrite /= ?Ptrofs.repr_unsigned.

Ltac ob_check_tac := simplify_ofs;
  lazymatch goal with
(*  | |- envs_entails ?Δ (ob_check_ex(A := ?A) _ ?P _) =>
      iSplit; [iNext; let x := fresh "x" in evar (x : A); let i := fresh "i" in evar (i : ident.ident);
        let b := fresh "b" in evar (b : bool);
        let H := fresh "H" in assert (envs_lookup i Δ = Some (b, P)) as H;
        [subst b i; iAssumptionCore || fail "cannot find" P |
         clear H; clear b; lazymatch goal with i := ?s : ident.ident |- _ => clear i; iExists x; subst x; iSplit; [iApply s | iPureIntro; try by auto] end]
      |]*)
  | |- envs_entails ?Δ (ob_check _ ?P _) =>
      iSplit; [| iSplit; [iNext; let i := fresh "i" in evar (i : ident.ident);
        let b := fresh "b" in evar (b : bool);
        let H := fresh "H" in assert (envs_lookup i Δ = Some (b, P)) as H;
        [subst b i; iAssumptionCore || fail "cannot find" P |
         clear H; clear b; lazymatch goal with i := ?s : ident.ident |- _ => clear i; iApply s end]
      |]]; first (iPureIntro; try by auto)
  | _ => fail "no such ob"
  end.

Definition ob_replace `{!VSTGS OK_ty Σ} R (P P' Q : assert) := <affine> ⌜R⌝ ∗ ▷ (P ∗ (P' -∗ Q)).

(*Definition ob_replace_ex `{!VSTGS OK_ty Σ} {A} P R P' (Q : assert) := ▷ (∃ x : A, P x ∗ <affine> ⌜R x⌝ ∗ (P' x -∗ Q)).*)

Ltac ob_replace_tac := simplify_ofs;
  lazymatch goal with
(*  | |- envs_entails ?Δ (ob_replace_ex(A := ?A) ?P _ _ _) =>
      iNext; let x := fresh "x" in evar (x : A); let i := fresh "i" in evar (i : ident.ident);
        let H := fresh "H" in assert (envs_lookup i Δ = Some (false, P x)) as H;
        [subst i x; iAssumptionCore || fail "cannot find" P |
         clear H; clear x; lazymatch goal with i := ?s : ident.ident |- _ => clear i; iFrame s; iSplit; [iPureIntro; try by auto | iIntros s] end]*)
  | |- envs_entails ?Δ (ob_replace _ ?P _ _) =>
      iSplit; [| iNext; let i := fresh "i" in evar (i : ident.ident);
        let H := fresh "H" in assert (envs_lookup i Δ = Some (false, P)) as H;
        [subst i; iAssumptionCore || fail "cannot find" P |
         clear H; lazymatch goal with i := ?s : ident.ident |- _ => clear i; iFrame s; iIntros s end]];
        first (iPureIntro; try by auto)
  | _ => fail "no such ob"
  end.

Lemma tac_wp_consti_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vint v)) → envs_entails Δ (wp_expr ge E f (Econst_int v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_int. Qed.
Lemma tac_wp_constf_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vfloat v)) → envs_entails Δ (wp_expr ge E f (Econst_float v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_float. Qed.
Lemma tac_wp_consts_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vsingle v)) → envs_entails Δ (wp_expr ge E f (Econst_single v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_single. Qed.
Lemma tac_wp_constl_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vlong v)) → envs_entails Δ (wp_expr ge E f (Econst_long v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_long. Qed.

Lemma tac_wp_consti `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vint v)) → envs_entails Δ (wp_expr ge E f (Econst_int v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_int_fupd. Qed.
Lemma tac_wp_constf `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vfloat v)) → envs_entails Δ (wp_expr ge E f (Econst_float v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_float_fupd. Qed.
Lemma tac_wp_consts `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vsingle v)) → envs_entails Δ (wp_expr ge E f (Econst_single v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_single_fupd. Qed.
Lemma tac_wp_constl `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vlong v)) → envs_entails Δ (wp_expr ge E f (Econst_long v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_long_fupd. Qed.

Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, fupd ?E _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (ob_cond _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (ob_cond _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (ob_cond _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (ob_cond _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, ob_replace _ _ _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, ob_replace _ _ _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, ob_replace _ _ _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, ob_replace _ _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, wp_binop _ _ _ _ _ _ _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, wp_binop _ _ _ _ _ _ _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, wp_binop _ _ _ _ _ _ _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, wp_binop _ _ _ _ _ _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, wp_unop _ _ _ _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, wp_unop _ _ _ _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, wp_unop _ _ _ _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, wp_unop _ _ _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) _) =>
      eapply tac_wp_consti
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) _) =>
      eapply tac_wp_constf
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) _) =>
      eapply tac_wp_consts
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) _) =>
      eapply tac_wp_constl
  end.

Tactic Notation "wp_const" := wp_value_head.
Tactic Notation "wp_sizeof" := iApply wp_sizeof.
Tactic Notation "wp_alignof" := iApply wp_alignof.
Tactic Notation "wp_binop" := iApply wp_binop_rule.
Tactic Notation "wp_unop" := iApply wp_unop_rule.

Ltac wp_finish0 :=
  repeat (wp_value_head || ob_cond_tac || ob_check_tac || ob_replace_tac);
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Tactic Notation "wp_binop_post" :=
  lazymatch goal with
  | |- envs_entails ?Δ (wp_binop _ _ _ _ _ _ _ _) =>
      iApply wp_binop_sc; [try fast_done | iSplit; [try done | wp_finish0]]
  | _ => fail "no such wp_binop"
  end.

Tactic Notation "wp_unop_post" :=
  lazymatch goal with
  | |- envs_entails ?Δ (wp_unop _ _ _ _ _) =>
      iApply wp_unop_sc; [try fast_done | iSplit; [try done | wp_finish0]]
  | _ => fail "no such wp_unop"
  end.

Ltac wp_finish :=
  repeat (wp_value_head || ob_cond_tac || ob_check_tac || ob_replace_tac);
  try wp_binop_post;
  try wp_unop_post;
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Lemma tac_wp_load `{!VSTGS OK_ty Σ} Δ ge E f e q v (Q : val → assert) :
  envs_entails Δ (wp_lvalue ge E f e (λ '(bl, o),
    ob_check (readable_share q /\ v ≠ Vundef) ⎡mapsto q (typeof e) (Vptr bl (Ptrofs.repr o)) v⎤ (Q v))) →
  envs_entails Δ (wp_expr ge E f e Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_expr_mapsto.
  apply wp_lvalue_mono.
  iIntros ((?, ?)) "(% & H) !>".
  iExists q, v; iSplit; first done.
  iSplit; first by rewrite bi.and_elim_l embed_later embed_absorbingly.
  iModIntro; by rewrite bi.and_elim_r.
Qed.

Lemma tac_wp_deref `{!VSTGS OK_ty Σ} Δ ge E f e ty Q :
  envs_entails Δ (wp_expr ge E f e (ob_cond (λ v l, match v with Vptr b o => l = (b, Ptrofs.unsigned o) | _ => False%type end) (λ _, Q))) →
  envs_entails Δ (wp_lvalue ge E f (Ederef e ty) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_deref.
  apply wp_expr_mono; intros.
  iIntros "(%x & H) !>"; iDestruct "H" as "(%H & ?)".
  destruct v; try contradiction; subst; by iFrame.
Qed.

Lemma tac_wp_field `{!VSTGS OK_ty Σ} Δ ge E f e i ty Q :
  envs_entails Δ (wp_expr ge E f e (ob_cond (λ v l, match v with Vptr b o =>
    match typeof e with
    | Tstruct id _ => match (genv_cenv ge !! id)%maps with Some co => match field_offset ge i (co_members co) with Errors.OK (delta, Full) =>
        l = (b, Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr delta))) | _ => False%type end | _ => False%type end
    | Tunion id _ => match (genv_cenv ge !! id)%maps with Some co => match union_field_offset ge i (co_members co) with Errors.OK (delta, Full) =>
        l = (b, Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr delta))) | _ => False%type end | _ => False%type end
    | _ => False%type
    end | _ => False%type end) (λ _, Q))) →
  envs_entails Δ (wp_lvalue ge E f (Efield e i ty) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_lvalue_field.
  apply wp_expr_mono; intros.
  iIntros "(%x & H) !>"; iDestruct "H" as "(%H & ?)".
  destruct v; try contradiction; iExists _, _; iSplit; first done.
  destruct (typeof e); try contradiction; destruct (genv_cenv ge !! i1)%maps; try contradiction.
  - destruct (field_offset (genv_cenv ge) i (co_members c)) as [(?, [])|] eqn: Hoff; try contradiction; subst; eauto with iFrame.
  - destruct (union_field_offset (genv_cenv ge) i (co_members c)) as [(?, [])|] eqn: Hoff; try contradiction; subst; eauto with iFrame.
Qed.

Lemma tac_wp_cast `{!VSTGS OK_ty Σ} Δ ge E f e ty Q :
  cast_pointer_to_bool (typeof e) ty = false →
  envs_entails Δ (wp_expr ge E f e (ob_cond (λ v v', Cop2.tc_val (typeof e) v /\ Clight_Cop2.sem_cast (typeof e) ty v = Some v') (λ _, Q))) →
  envs_entails Δ (wp_expr ge E f (Ecast e ty) Q).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite Hi -wp_cast; last done.
  apply wp_expr_mono; intros.
  by iIntros "(% & (% & %) & $)".
Qed.

Tactic Notation "wp_load" :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_load
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_deref" :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    eapply tac_wp_load;
    first
      [eapply tac_wp_deref
      |fail 1 "wp_deref: cannot find 'Ederef' in" e];
    wp_finish
  | |- envs_entails _ (wp_lvalue _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_deref
      |fail 1 "wp_deref: cannot find 'Ederef' in" e];
    wp_finish
  | _ => fail "wp_deref: not a 'wp'"
  end.

Tactic Notation "wp_addrof" :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    first
      [iApply wp_addrof
      |fail 1 "wp_addrof: cannot find 'Eaddrof' in" e];
    wp_finish
  | _ => fail "wp_addrof: not a 'wp'"
  end.

Tactic Notation "wp_field" :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    eapply tac_wp_load;
    first
      [eapply tac_wp_field
      |fail 1 "wp_field: cannot find 'Efield' in" e];
    try (iApply wp_expr_ptr; first by auto); wp_finish
  | |- envs_entails _ (wp_lvalue _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_field
      |fail 1 "wp_field: cannot find 'Efield' in" e];
    try (iApply wp_expr_ptr; first by auto); wp_finish
  | _ => fail "wp_field: not a 'wp'"
  end.

Tactic Notation "wp_cast" :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_cast
      |fail 1 "wp_cast: cannot find 'Ecast' in" e];
    [fast_done || fail 1 "wp_cast: pointer-to-bool cast"
    |rewrite /typeof; wp_finish]
  | _ => fail "wp_cast: not a 'wp'"
  end.

(* use ob_cond for valid_val? *)
Lemma tac_wp_if `{!VSTGS OK_ty Σ} Δ OK_spec ge E f e s1 s2 Q :
  envs_entails Δ (wp_expr ge E f e (ob_cond (λ v b, Cop2.bool_val (typeof e) v = Some b)
    (λ v b, ▷ (⎡valid_val v⎤ ∧ if b then wp OK_spec ge E f s1 Q else wp OK_spec ge E f s2 Q)))) →
  envs_entails Δ (wp OK_spec ge E f (Sifthenelse e s1 s2) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_if.
  apply wp_expr_mono; intros.
  iIntros "(%x & H) !> !>"; iDestruct "H" as "(%H & ?)".
  iSplit; first (by rewrite bi.and_elim_l); rewrite bi.and_elim_r; by iFrame.
Qed.

Lemma tac_wp_switch `{!VSTGS OK_ty Σ} Δ OK_spec ge E f e ls Q :
  envs_entails Δ (wp_expr ge E f e (ob_cond (λ v i, sem_switch_arg v (typeof e) = Some i)
    (λ v i, ▷ (wp OK_spec ge E f (seq_of_labeled_statement (select_switch i ls)) (Clight_seplog.switch_ret_assert Q))))) →
  envs_entails Δ (wp OK_spec ge E f (Sswitch e ls) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_switch.
  apply wp_expr_mono; intros.
  iIntros "(%x & H) !>"; iDestruct "H" as "(%H & $)"; done.
Qed.

Tactic Notation "wp_if" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; eapply tac_wp_if
      |fail 1 "wp_if: cannot find 'if' in" e];
     wp_finish
  | _ => fail "wp_if: not a 'wp'"
  end.

Tactic Notation "wp_switch" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; eapply tac_wp_switch
      |fail 1 "wp_switch: cannot find 'switch' in" e];
     simpl seq_of_labeled_statement; wp_finish
  | _ => fail "wp_switch: not a 'wp'"
  end.

(*Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    let e := eval simpl in e in
    unify e efoc;
      eapply (tac_wp_pure _ _ _ _ _ _ e);
      [tc_solve                       (* PureExec *)
      |try fast_done    (* The pure condition for PureExec --
         handles trivial goals *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ]
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.
Tactic Notation "wp_pure" :=
  wp_pure _.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].*)



#[global] Opaque temp.

Lemma tac_wp_store `{!VSTGS OK_ty Σ} Δ OK_spec ge E f e1 e2 q v Q :
  envs_entails Δ (wp_expr ge E f (Ecast e2 (typeof e1)) (ob_cond1 (λ v2, Cop2.tc_val' (typeof e1) v2) (λ v2,
    wp_lvalue ge E f e1 (λ '(b, o), let v1 := Vptr b (Ptrofs.repr o) in
    ob_replace (writable0_share q) ⎡mapsto q (typeof e1) v1 v⎤ ⎡mapsto q (typeof e1) v1 v2⎤ (RA_normal Q))))) →
  envs_entails Δ (wp OK_spec ge E f (Sassign e1 e2) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_store.
  apply wp_expr_mono.
  intros ?; rewrite -fupd_intro /ob_cond1 /ob_replace.
  iIntros "(% & H)"; iSplit; first done.
  iApply (wp_lvalue_mono with "H").
  iIntros ((?, ?)) "(% & ? & H) !>".
  iExists q; iSplit; first done.
  iSplitR "H".
  { by rewrite mapsto_mapsto_. }
  iIntros "!> ?"; by iApply "H".
Qed.

Lemma tac_wp_temp `{!VSTGS OK_ty Σ} Δ ge E f i x v t Q :
  envs_lookup i Δ = Some (false, temp x v) →
  envs_entails Δ (Q v) →
  envs_entails Δ (wp_expr ge E f (Etempvar x t) Q).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -wp_tempvar_local.
  rewrite envs_lookup_split //; simpl.
  by rewrite Hi.
Qed.

(*Lemma tac_wp_set `{!VSTGS OK_ty Σ} Δ Δ' OK_spec ge E f i x e v0 Q :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, temp x v0) →
  envs_entails Δ (wp_expr ge E f e (λ v,
    of_envs Δ ∧
    match envs_simple_replace i false (Esnoc Enil i (temp x v)) Δ' with
    | Some Δ'' => ⌜envs_entails Δ'' (RA_normal Q)⌝
    | None => False
    end)) →
  envs_entails Δ (wp OK_spec ge E f (Sset x e) Q).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite Hi -wp_set.
  apply wp_expr_mono.
  intros ?.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | iIntros "(_ & [])" ].
  apply bi.pure_elim_r; intros HQ.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  iIntros "($ & H) !> !> ?".
  iApply HQ; iApply "H"; iFrame.
Qed.*)

Lemma tac_wp_set `{!VSTGS OK_ty Σ} Δ OK_spec ge E f x e v0 Q :
  envs_entails Δ (wp_expr ge E f e (λ v,
    ob_replace True (temp x v0) (temp x v) (RA_normal Q))) →
  envs_entails Δ (wp OK_spec ge E f (Sset x e) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_set.
  apply wp_expr_mono.
  iIntros (?) "(_ & $ & H) !> !> ? !>"; by iApply "H".
Qed.

Lemma tac_wp_lvar `{!VSTGS OK_ty Σ} Δ ge E f i x b t Q :
  envs_lookup i Δ = Some (false, lvar x t b) →
  envs_entails Δ (Q (b, 0)) →
  envs_entails Δ (wp_lvalue ge E f (Evar x t) Q).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -wp_var_local.
  rewrite envs_lookup_split //; simpl.
  by rewrite Hi.
Qed.

Lemma tac_wp_gvar `{!VSTGS OK_ty Σ} Δ ge E f i x b t Q :
  ¬ In x (map fst (fn_vars f)) →
  envs_lookup i Δ = Some (false, ⎡gvar x b⎤) →
  envs_entails Δ (Q (b, 0)) →
  envs_entails Δ (wp_lvalue ge E f (Evar x t) Q).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -wp_var_global //.
  rewrite envs_lookup_split //; simpl.
  by rewrite Hi.
Qed.

Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp _ _ _ _ _ _) =>
            reshape_seq; tac_suc H
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).

Tactic Notation "wp_apply" open_constr(lem) "as" constr(pat) :=
  wp_apply lem; last iIntros pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Tactic Notation "wp_skip" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; iApply wp_skip
      |fail 1 "wp_skip: cannot find 'Sskip' in" e];
    [pm_reduce; wp_finish]
  | _ => fail "wp_skip: not a 'wp'"
  end.

Tactic Notation "wp_label" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; iApply wp_label
      |fail 1 "wp_label: cannot find 'Slabel' in" e];
    [pm_reduce; wp_finish]
  | _ => fail "wp_label: not a 'wp'"
  end.

Tactic Notation "wp_loop" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; iApply wp_loop
      |fail 1 "wp_loop: cannot find 'Sloop' in" e];
    [iNext; pm_reduce; wp_finish]
  | _ => fail "wp_loop: not a 'wp'"
  end.

Tactic Notation "wp_break" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; iApply wp_break
      |fail 1 "wp_break: cannot find 'Sbreak' in" e];
    [pm_reduce; wp_finish]
  | _ => fail "wp_break: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; eapply tac_wp_store
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [wp_cast]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_temp" :=
  let solve_temp _ :=
    let i := match goal with |- _ = Some (_, temp ?i _) => i end in
    iAssumptionCore || fail "wp_store: cannot find temp" i in
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_temp
      |fail 1 "wp_temp: cannot find 'Etempvar' in" e];
    [solve_temp ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_temp: not a 'wp'"
  end.

Tactic Notation "wp_set" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; eapply tac_wp_set
      |fail 1 "wp_set: cannot find 'Sset' in" e];
    [pm_reduce; wp_finish]
  | _ => fail "wp_set: not a 'wp'"
  end.

Tactic Notation "wp_lvar" :=
  let solve_lvar _ :=
    let i := match goal with |- _ = Some (_, lvar ?i _ _) => i end in
    iAssumptionCore || fail "wp_lvar: cannot find lvar" i in
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    eapply tac_wp_load;
    first
      [eapply tac_wp_lvar
      |fail 1 "wp_lvar: cannot find 'Evar' in" e];
    [solve_lvar ()
    |pm_reduce; wp_finish]
  | |- envs_entails _ (wp_lvalue _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_lvar
      |fail 1 "wp_lvar: cannot find 'Evar' in" e];
    [solve_lvar ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_lvar: not a 'wp'"
  end.

Tactic Notation "wp_gvar" :=
  let solve_gvar _ :=
    let i := match goal with |- _ = Some (_, ⎡gvar ?i _⎤) => i end in
    iAssumptionCore || fail "wp_gvar: cannot find gvar" i in
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    eapply tac_wp_load;
    first
      [eapply tac_wp_gvar
      |fail 1 "wp_gvar: cannot find 'Evar' in" e];
    [try congruence
    |solve_gvar ()
    |pm_reduce; wp_finish]
  | |- envs_entails _ (wp_lvalue _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_gvar
      |fail 1 "wp_gvar: cannot find 'Evar' in" e];
    [try congruence
    |solve_gvar ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_gvar: not a 'wp'"
  end.

Tactic Notation "wp_var" := (wp_lvar || wp_gvar).

Tactic Notation "wp_return" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ (Sreturn (Some _)) ?Q) =>
    iApply wp_return; rewrite /wp_expr_opt /option_map; wp_cast
  | |- envs_entails _ (wp _ _ ?E _ (Sreturn None) ?Q) =>
    iApply wp_return; wp_finish
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    fail 1 "wp_set: cannot find 'Sreturn' in" e
  | _ => fail "wp_return: not a 'wp'"
  end.
  