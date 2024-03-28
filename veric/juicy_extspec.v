From iris.bi Require Export derived_connectives.
Require Import VST.veric.juicy_base.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.shares.
Require Import iris_ora.logic.ghost_map.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.external_state.

Require Import VST.veric.tycontext.

Local Open Scope nat_scope.

(*! The void ext_spec *)
Definition void_spec T : external_specification mem external_function T :=
    Build_external_specification
      mem external_function T
      (fun ef => False%type)
      (fun ef Hef ge tys vl m z => False%type)
      (fun ef Hef ge ty vl m z => False%type)
      (fun rv m z => False%type).

Section upd_exit.
  Context {Z : Type}.
  Variable spec : ext_spec Z.

  Definition upd_exit' (Q_exit : option val -> Z -> mem -> Prop) :=
  {| ext_spec_type := ext_spec_type spec
   ; ext_spec_pre := ext_spec_pre spec
   ; ext_spec_post := ext_spec_post spec
   ; ext_spec_exit := Q_exit |}.

  Definition upd_exit (ef : external_function) (x : ext_spec_type spec ef) ge :=
    upd_exit' (ext_spec_post spec ef x ge (sig_res (ef_sig ef))).

End upd_exit.

Section mpred.

Context {Σ : gFunctors}.

Section juicy_safety.
  Context {G C Z:Type}.
  Context {genv_symb: G -> injective_PTree Values.block}.
  Context (Hcore:@CoreSemantics C mem).
  Variable (Hspec : ext_spec Z).
  Variable ge : G.

  Context `{!gen_heapGS share address resource Σ} `{!externalGS Z Σ} `{!invGS_gen hlc Σ}.

(* The closest match to the Iris approach would be for auth_heap to hold the true full CompCert mem,
   and to run the underlying semantics without any permissions. But that's a poor fit for VST's approach
   to soundness. Instead, our "authoritative" state is still just the current thread's view of the state. *)

Definition state_interp m z := mem_auth m ∗ ext_auth z.

(* We could bring this more in line with weakestpre, but weakestpre doesn't give us control over the
   masks, so we can't restrict updates around steps. *)
Program Definition jsafe_pre
    (jsafe : coPset -d> Z -d> C -d> iPropO Σ) : coPset -d> Z -d> C -d> iPropO Σ := λ E z c,
  |={E}=> ∀ m, state_interp m z -∗
      (∃ i, ⌜halted Hcore c i ∧ ext_spec_exit Hspec (Some (Vint i)) z m⌝) ∨
      (|={E}=> ∃ c' m', ⌜corestep Hcore c m c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c') ∨
      (∃ e args x, ⌜at_external Hcore c m = Some (e, args) ∧ ext_spec_pre Hspec e x (genv_symb ge) (sig_args (ef_sig e)) args z m⌝ ∧
         ▷ (∀ ret m' z', ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
          ⌜ext_spec_post Hspec e x (genv_symb ge) (sig_res (ef_sig e)) ret z' m'⌝ → |={E}=>
          ∃ c', ⌜after_external Hcore ret c m' = Some c'⌝ ∧ state_interp m' z' ∗ jsafe E z' c')).

Local Instance jsafe_pre_contractive : Contractive jsafe_pre.
Proof.
  rewrite /jsafe_pre => n jsafe jsafe' Hsafe E z c.
  do 13 f_equiv.
  - f_contractive; repeat f_equiv. apply Hsafe.
  - f_contractive; repeat f_equiv. apply Hsafe.
Qed.

Local Definition jsafe_def : coPset -> Z -> C -> iProp Σ := fixpoint jsafe_pre.
Local Definition jsafe_aux : seal (@jsafe_def). Proof. by eexists. Qed.
Definition jsafe := jsafe_aux.(unseal).
Local Lemma jsafe_unseal : jsafe = jsafe_def.
Proof. rewrite -jsafe_aux.(seal_eq) //. Qed.

(* basic facts following iris.program_logic.weakestpre *)
Lemma jsafe_unfold E z c : jsafe E z c ⊣⊢ jsafe_pre jsafe E z c.
Proof. rewrite jsafe_unseal. apply (fixpoint_unfold jsafe_pre). Qed.

Lemma fupd_jsafe E z c : (|={E}=> jsafe E z c) ⊢ jsafe E z c.
Proof.
  rewrite jsafe_unfold /jsafe_pre. iIntros ">$".
Qed.

Lemma jsafe_mask_mono E1 E2 z c : E1 ⊆ E2 → jsafe E1 z c ⊢ jsafe E2 z c.
Proof.
  iIntros (?) "H". iLöb as "IH" forall (z c).
  rewrite !jsafe_unfold /jsafe_pre.
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done; iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (?) "?"; iDestruct ("H" with "[$]") as "[H | [H | H]]".
  - by iLeft.
  - iRight; iLeft.
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done; iMod "H"; iMod "Hclose" as "_".
    iDestruct "H" as (???) "[??]"; iIntros "!>".
    iExists _, _; iSplit; first done.
    iFrame; by iApply "IH".
  - iRight; iRight.
    iDestruct "H" as (????) "H".
    iExists _, _, _; iSplit; first done.
    iIntros "!>" (????) "Hext".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done; iMod ("H" with "[%] Hext") as "H'"; first done; iMod "Hclose" as "_".
    iIntros "!>".
    iDestruct "H'" as (??) "[??]"; iExists _; iFrame "%"; iFrame.
    by iApply "IH".
Qed.

(** Proofmode class instances *)
Section proofmode_classes.
  Implicit Types P Q : iProp Σ.

  Global Instance is_except_0_jsafe E z c : IsExcept0 (jsafe E z c).
  Proof. by rewrite /IsExcept0 -{2}fupd_jsafe -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_jsafe p P E z c :
    ElimModal Logic.True p false (|==> P) P (jsafe E z c) (jsafe E z c).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_jsafe.
  Qed.

  Global Instance elim_modal_fupd_jsafe p P E z c :
    ElimModal Logic.True p false (|={E}=> P) P (jsafe E z c) (jsafe E z c).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_jsafe.
  Qed.

  Global Instance add_modal_fupd_jsafe P E z c :
    AddModal (|={E}=> P) P (jsafe E z c).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_jsafe. Qed.

End proofmode_classes.

Lemma jsafe_local_step:
  forall E ora s1 s2,
  (forall m, corestep Hcore s1 m s2 m) ->
  ▷jsafe E ora s2 ⊢
  jsafe E ora s1.
Proof.
  intros ?????; iIntros "H".
  rewrite (jsafe_unfold _ _ s1) /jsafe_pre.
  iIntros "!>" (?) "?".
  iRight; iLeft.
  iIntros "!>".
  iExists _, _; iSplit; first done.
  by iFrame.
Qed.

Definition jstep E z c c' := ∀ m, state_interp m z ={E}=∗ ∃ m', ⌜corestep Hcore c m c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c'.

Definition jstep_ex E z c := ∀ m, state_interp m z ={E}=∗ ∃ c' m', ⌜corestep Hcore c m c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c'.

Lemma jstep_exists : forall E z c c', jstep E z c c' ⊢ jstep_ex E z c.
Proof.
  intros; rewrite /jstep /jstep_ex.
  iIntros "H" (?) "?".
  iMod ("H" with "[$]") as (??) "?"; eauto.
Qed.

Lemma jstep_mono : forall E z c1 c2 c', (forall m m', corestep Hcore c1 m c' m' -> corestep Hcore c2 m c' m') ->
  jstep E z c1 c' ⊢ jstep E z c2 c'.
Proof.
  intros; rewrite /jstep.
  iIntros "H" (?) "?".
  iMod ("H" with "[$]") as (??) "?"; eauto 6.
Qed.

Lemma jsafe_step:
  forall c E z,
  jstep_ex E z c ⊢ jsafe E z c.
Proof.
  intros; iIntros "H".
  rewrite jsafe_unfold /jsafe_pre /jstep_ex.
  iIntros "!>" (m) "?"; iRight; iLeft.
  iMod ("H" with "[$]") as (???) "[??]".
  iIntros "!>"; iExists _, _; iSplit; first done.
  by iFrame.
Qed.

Lemma jsafe_step_forward_ex:
  forall c E z
    (Hhalt : forall i, ~halted Hcore c i) (Hext : forall m, at_external Hcore c m = None),
    jsafe E z c ⊢ jstep_ex E z c.
Proof.
  intros; iIntros "H".
  rewrite jsafe_unfold /jsafe_pre.
  rewrite /jstep_ex; iIntros (m1) "?".
  iMod ("H" with "[$]") as "[H | [H | H]]".
  { iDestruct "H" as (??) "?"; exfalso; eapply Hhalt; eauto. }
  iMod "H" as (???) "H".
  iIntros "!>"; iExists _, _; iSplit; auto.
  { iDestruct "H" as (??? (H & ?)) "?".
    by rewrite Hext in H. }
Qed.

Lemma jsafe_step_forward:
  forall c c1 E z (Hc1 : forall m c' m', corestep Hcore c m c' m' -> c' = c1)
    (Hhalt : forall i, ~halted Hcore c i) (Hext : forall m, at_external Hcore c m = None),
    jsafe E z c ⊢ |={E}=> jstep E z c c1.
Proof.
  intros; iIntros "H".
  rewrite jsafe_unfold /jsafe_pre.
  iMod "H".
  rewrite /jstep; iIntros "!>" (m1) "?".
  iDestruct ("H" with "[$]") as "[H | [H | H]]".
  { iDestruct "H" as (??) "?"; exfalso; eapply Hhalt; eauto. }
  iMod "H" as (?? Hstep) "H".
  rewrite -(Hc1 _ _ _ Hstep).
  iIntros "!>"; iExists _; iSplit; done.
  { iDestruct "H" as (??? (H & ?)) "?".
    by rewrite Hext in H. }
Qed.

(*  Lemma jsafe_corestepN_forward:
    corestep_fun Hcore ->
    forall z c m c' m' n n0,
      semantics_lemmas.corestepN (juicy_core_sem Hcore) ge n0 c m c' m' ->
      jsafeN_ (n + S n0) z c m ->
      jm_bupd (jsafeN_ n z c') m'.
  Proof.
    intros.
    revert c m c' m' n H0 H1.
    induction n0; intros; auto.
    simpl in H0; inv H0.
    apply jm_bupd_intro.
    eapply jsafe_downward in H1; eauto. lia.
    simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
    assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by lia.
    rewrite Heq in H1.
    eapply jsafe_corestep_forward in H1; eauto.
    specialize (H1 nil); spec H1.
    { eexists; simpl; erewrite <- ghost_core.
      apply join_comm, core_unit. }
    destruct H1 as (? & ? & ? & ?).
    eapply (IHn0 _ _ _ _ n).
  Qed.

  Lemma jsafe_step'_back2 :
    forall
      {ora st m st' m'},
      jstep Hcore st m st' m' ->
      jsafeN_ ora st' m' ->
      jsafeN_ ora st m.
  Proof.
    intros.
    eapply jsafe_corestep_backward; eauto.
  Qed.

  Lemma jsafe_corestepN_backward:
    forall z c m c' m' n0,
      semantics_lemmas.corestepN (juicy_core_sem Hcore) n0 c m c' m' ->
      jsafeN_ z c' m' ->
      jsafeN_ z c m.
  Proof.
    simpl; intros.
    revert c m c' m' H H0.
    induction n0; intros; auto.
    simpl in H; inv H; auto.
    simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
    specialize (IHn0 _ _ _ _ STEPN H0).
    solve[eapply jsafe_step'_back2; eauto].
  Qed.*)

  Lemma convergent_controls_jsafe :
    forall q1 q2
      (Hat_ext : forall m, at_external Hcore q1 m = at_external Hcore q2 m)
      (Hafter_ext : forall ret m q', after_external Hcore ret q1 m = Some q' ->
                                     after_external Hcore ret q2 m = Some q')
      (Hhalted : halted Hcore q1 = semantics.halted Hcore q2)
      (Hstep : forall m q' m', corestep Hcore q1 m q' m' ->
                             corestep Hcore q2 m q' m'),
      (forall E z, jsafe E z q1 ⊢ jsafe E z q2).
  Proof.
    intros.
    iIntros "H".
    rewrite !jsafe_unfold /jsafe_pre.
    iMod "H"; iIntros "!>" (?) "?"; iDestruct ("H" with "[$]") as "[H | [H | H]]".
    - rewrite Hhalted; auto.
    - iRight; iLeft.
      iMod "H" as (?? H) "H".
      apply Hstep in H; eauto.
    - rewrite Hat_ext; iDestruct "H" as (????) "H".
      iRight; iRight; iExists _, _, _; iSplit; first done.
      iNext; iIntros (????) "Hpost".
      iMod ("H" with "[%] Hpost") as (? Hafter) "Hpost"; first done.
      apply Hafter_ext in Hafter; eauto.
  Qed.

End juicy_safety.

End mpred.
