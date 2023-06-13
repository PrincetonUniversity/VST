From iris.bi Require Export derived_connectives.
Require Import VST.veric.juicy_base.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.shares.
(*Require Import VST.veric.juicy_safety.*)
Require Import VST.veric.ghost_map.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.external_state.

Require Import VST.veric.tycontext.

Local Open Scope nat_scope.

Section mpred.

Context {Σ : gFunctors}.

(* predicates on juicy memories *)
Global Instance mem_inhabited : Inhabited Memory.mem := {| inhabitant := Mem.empty |}.
Definition mem_index : biIndex := {| bi_index_type := mem |}.

Definition jmpred := monPred mem_index (iPropI Σ).

(* Should this include coherence? *)
Record juicy_mem := { level : nat; m_dry : mem; m_phi : iResUR Σ }.

Definition jm_mono (P : juicy_mem -> Prop) := forall jm n2 x2, P jm -> m_phi jm ≼ₒ{level jm} x2 ->
  n2 <= level jm -> P {| level := n2; m_dry := m_dry jm; m_phi := x2 |}.

Definition jmpred_of P (Hmono : jm_mono P) : jmpred.
Proof.
  unshelve eexists.
  intros m; unshelve eexists.
  exact (λ n phi, P {| level := n; m_dry := m; m_phi := phi |} ).
  - simpl; intros.
    eapply Hmono in H; eauto.
  - apply _.
Defined.

Record juicy_ext_spec (Z: Type) := {
  JE_spec :> external_specification juicy_mem external_function Z;
  JE_pre_mono: forall e t ge_s typs args z, jm_mono (ext_spec_pre JE_spec e t ge_s typs args z);
  JE_post_mono: forall e t ge_s tret rv z, jm_mono (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_exit_mono: forall rv z, jm_mono (ext_spec_exit JE_spec rv z)
}.

Definition ext_mpred_pre Z JE_spec e t ge_s typs args z : jmpred := jmpred_of _ (JE_pre_mono Z JE_spec e t ge_s typs args z).
Definition ext_mpred_post Z JE_spec e t ge_s tret rv z : jmpred := jmpred_of _ (JE_post_mono Z JE_spec e t ge_s tret rv z).
Definition ext_mpred_exit Z JE_spec rv z : jmpred := jmpred_of _ (JE_exit_mono Z JE_spec rv z).

Class OracleKind := {
  OK_ty : Type;
  OK_spec: juicy_ext_spec OK_ty
}.

(*! The void ext_spec *)
Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False%type)
      (fun ef Hef ge tys vl m z => False%type)
      (fun ef Hef ge ty vl m z => False%type)
      (fun rv m z => False%type).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros ???; contradiction.
Defined.

(*Definition j_initial_core {C} (csem: @CoreSemantics C mem)
     (n: nat) (m: juicy_mem) (q: C) (m': juicy_mem) (v: val) (args: list val) 
     : Prop :=
  m' = m /\
  semantics.initial_core csem n (m_dry m) q (m_dry m') v args.

Definition j_at_external {C} (csem: @CoreSemantics C mem)
   (q: C) (jm: juicy_mem) : option (external_function * list val) :=
   semantics.at_external csem q (m_dry jm).

Definition j_after_external {C} (csem: @CoreSemantics C mem)
    (ret: option val) (q: C) (jm: juicy_mem) :=
   semantics.after_external csem ret q (m_dry jm).

(*Definition jstep {C} (csem: @CoreSemantics C mem)
  (q: C) (q': C) (jm': juicy_mem) (jm : juicy_mem) : Prop :=
 corestep csem q (m_dry jm) q' (m_dry jm') /\
 resource_decay (level jm') (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
 level jm = S (level jm') (*/\
  Really, what we want is "nothing has changed in the rmap except the changes related to the mem ops".
  We can state this by indexing into the rmap, but...
 ghost_of (m_phi jm') = ghost_approx jm' (ghost_of (m_phi jm))*).*)

(*Definition jstep {C} (csem: @CoreSemantics C mem)
  (q: C) (q': C) (jm': juicy_mem) (jm : juicy_mem) : Prop :=
 corestep csem q (m_dry jm) q' (m_dry jm').*)

Definition j_halted {C} (csem: @CoreSemantics C mem)
       (c: C) (i: int): Prop :=
     halted csem c i.

(*Lemma jstep_not_at_external {C} (csem: @CoreSemantics C mem):
  forall m q m' q', jstep csem q m q' m' -> at_external csem q (m_dry m) = None.
Proof.
  intros.
  destruct H as (? & ? & ? & ?). eapply corestep_not_at_external; eauto.
Qed.

Lemma jstep_not_halted  {C} (csem: @CoreSemantics C mem):
  forall m q m' q' i, jstep csem q m q' m' -> ~j_halted csem q i.
Proof.
  intros. destruct H as (? & ? & ? & ?). eapply corestep_not_halted; eauto.
Qed.

Definition juicy_core_sem
  {C} (csem: @CoreSemantics C mem) :
   @CoreSemantics C juicy_mem :=
  @Build_CoreSemantics _ juicy_mem
    (j_initial_core csem)
    (j_at_external csem)
    (j_after_external csem)
    (j_halted csem)
    (jstep csem)
    (jstep_not_halted csem)
    (jstep_not_at_external csem)
(*  (j_at_external_halted_excl csem)*).
*)*)

Section upd_exit.
  Context {Z : Type}.
  Variable spec : juicy_ext_spec Z.

  Definition upd_exit' (Q_exit : option val -> Z -> juicy_mem -> Prop) :=
  {| ext_spec_type := ext_spec_type spec
   ; ext_spec_pre := ext_spec_pre spec
   ; ext_spec_post := ext_spec_post spec
   ; ext_spec_exit := Q_exit |}.

  Definition upd_exit'' (ef : external_function) (x : ext_spec_type spec ef) ge :=
    upd_exit' (ext_spec_post spec ef x ge (sig_res (ef_sig ef))).

  Program Definition upd_exit {ef : external_function} (x : ext_spec_type spec ef) ge
   : juicy_ext_spec Z :=
    Build_juicy_ext_spec _ (upd_exit'' _ x ge) _ _ _.
  Next Obligation. intros. eapply JE_pre_mono; eauto. Qed.
  Next Obligation. intros. eapply JE_post_mono; eauto. Qed.
  Next Obligation. intros. eapply JE_post_mono; eauto. Qed.
End upd_exit.

Local Obligation Tactic := Tactics.program_simpl.

Section juicy_safety.
  Context {G C Z:Type}.
  Context {genv_symb: G -> injective_PTree Values.block}.
  Context (Hcore:@CoreSemantics C mem).
  Variable (Hspec : juicy_ext_spec Z).
  Variable ge : G.

  Context `{!heapGS Σ} `{!externalGS Z Σ}.

(* The closest match to the Iris approach would be for auth_heap to hold the true full CompCert mem,
   and to run the underlying semantics without any permissions. But that's a poor fit for VST's approach
   to soundness. Instead, our "authoritative" state is still just the current thread's view of the state. *)

Definition state_interp m z := mem_auth m ∗ ext_auth z.

Program Definition jsafe_pre
    (jsafe : coPset -d> Z -d> C -d> iPropO Σ) : coPset -d> Z -d> C -d> iPropO Σ := λ E z c,
  |={E}=> ∀ m, state_interp m z -∗
      (∃ i, ⌜halted Hcore c i⌝ ∧ monPred_at (ext_mpred_exit Z Hspec (Some (Vint i)) z) m) ∨
      (|={E}=> ∃ c' m', ⌜corestep Hcore c m c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c') ∨
      (∃ e args x, ⌜at_external Hcore c m = Some (e, args)⌝ ∧ monPred_at (ext_mpred_pre Z Hspec e x (genv_symb ge) (sig_args (ef_sig e)) args z) m ∗
         ▷ (∀ ret m' z', ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
          (monPred_at (ext_mpred_post Z Hspec e x (genv_symb ge) (sig_res (ef_sig e)) ret z') m' ={E}=∗
          ∃ c', ⌜after_external Hcore ret c m' = Some c'⌝ ∧ state_interp m' z' ∗ jsafe E z' c'))).

Local Instance jsafe_pre_contractive : Contractive jsafe_pre.
Proof.
  rewrite /jsafe_pre => n jsafe jsafe' Hsafe E z c.
  do 13 f_equiv.
  - f_contractive; repeat f_equiv. apply Hsafe.
  - f_equiv. f_contractive; repeat f_equiv. apply Hsafe.
Qed.

(*Local Definition jsafe_def : Wp (iProp Σ) C (option val) stuckness :=
  λ s : stuckness, fixpoint (jsafe_pre s).
It's possible that we could massage this into Iris's WP framework, but it would involve moving the oracle
quantification into the definition of safety and passing ext_spec_exit as an argument.
*) 
Local Definition jsafe_def : coPset -> Z -> C -> mpred := fixpoint jsafe_pre.
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
  iMod (fupd_mask_subseteq E1) as "Hclose"; iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (?) "?"; iDestruct ("H" with "[$]") as "[H | [H | H]]".
  - by iLeft.
  - iRight; iLeft.
    iMod (fupd_mask_subseteq E1) as "Hclose"; iMod "H"; iMod "Hclose" as "_".
    iDestruct "H" as (???) "[??]"; iIntros "!>".
    iExists _, _; iSplit; first done.
    iFrame; by iApply "IH".
  - iRight; iRight.
    iDestruct "H" as (????) "[Hext H]".
    iExists _, _, _; iSplit; first done; iFrame "Hext".
    iIntros "!>" (????) "Hext".
    iMod (fupd_mask_subseteq E1) as "Hclose"; iMod ("H" with "[%] Hext") as "H'"; first done; iMod "Hclose" as "_".
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

Definition jstep E z c c' : mpred := ∀ m, state_interp m z ={E}=∗ ∃ m', ⌜corestep Hcore c m c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c'.

Definition jstep_ex E z c : mpred := ∀ m, state_interp m z ={E}=∗ ∃ c' m', ⌜corestep Hcore c m c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c'.

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
  { iDestruct "H" as (????) "?".
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
  { iDestruct "H" as (????) "?".
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
      iDestruct "H" as "[$ H]"; iNext.
      iIntros (????) "Hpost".
      iMod ("H" with "[%] Hpost") as (? Hafter) "Hpost"; first done.
      apply Hafter_ext in Hafter; eauto.
  Qed.

End juicy_safety.

(*Lemma juicy_core_sem_preserves_corestep_fun
  {C} (csem: @CoreSemantics C mem) :
  corestep_fun csem ->
  corestep_fun (juicy_core_sem csem).
Proof.
  intros determinism jm q jm1 q1 jm2 q2 step1 step2.
  destruct step1 as [step1 [[ll1 rd1] [l1 g1]]].
  destruct step2 as [step2 [[ll2 rd2] [l2 g2]]].
  pose proof determinism _ _ _ _ _ _ step1 step2 as E.
  injection E as <- E; f_equal.
  apply juicy_mem_ext; auto.
  assert (El: level jm1 = level jm2) by (clear -l1 l2; lia).
  apply rmap_ext. now do 2 rewrite <-level_juice_level_phi; auto.
  intros l.
  specialize (rd1 l); specialize (rd2 l).
  rewrite level_juice_level_phi in *.
  destruct jm  as [m  phi  jmc  jmacc  jmma  jmall ].
  destruct jm1 as [m1 phi1 jmc1 jmacc1 jmma1 jmall1].
  destruct jm2 as [m2 phi2 jmc2 jmacc2 jmma2 jmall2].
  simpl in *.
  subst m2; rename m1 into m'.
  destruct rd1 as [jmno [E1 | [[sh1 [rsh1 [v1 [v1' [E1 E1']]]]] | [[pos1 [v1 E1]] | [v1 [pp1 [E1 E1']]]]]]];
  destruct rd2 as [_    [E2 | [[sh2 [rsh2 [v2 [v2' [E2 E2']]]]] | [[pos2 [v2 E2]] | [v2 [pp2 [E2 E2']]]]]]];
  try pose proof jmno pos1 as phino; try pose proof (jmno pos2) as phino; clear jmno;
    remember (phi  @ l) as x ;
    remember (phi1 @ l) as x1;
    remember (phi2 @ l) as x2;
    subst.

  - (* phi1: same   | phi2: same   *)
    congruence.

  - (* phi1: same   | phi2: update *)
    rewrite <- E1, El.
    rewrite El in E1.
    rewrite E1 in E2.
    destruct (jmc1 _ _ _ _ _ E2).
    destruct (jmc2 _ _ _ _ _ E2').
    congruence.

  - (* phi1: same   | phi2: alloc  *)
    exfalso.
    rewrite phino in E1. simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc2 l).
    rewrite E2 in jmacc2.
    simpl in jmacc2.
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: same   | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: update | phi2: same   *)
    rewrite <- E2, <-El.
    rewrite <-El in E2.
    rewrite E2 in E1.
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E1).
    congruence.

  - (* phi1: update | phi2: update *)
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E2').
    rewrite E1', E2'.
    destruct (phi@l); inv E1; inv E2.
    f_equal. apply proof_irr.
  - (* phi1: update | phi2: alloc  *)
    rewrite phino in E1.
    simpl in E1.
    inversion E1.

  - (* phi1: update | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence.  
  - (* phi1: alloc  | phi2: same   *)
    exfalso.
    rewrite phino in E2. simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc1 l).
    rewrite E1 in jmacc1.
    simpl in jmacc1.
    rewrite jmacc2 in jmacc1.
    clear -jmacc1.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial. 
  - (* phi1: alloc  | phi2: update *)
    rewrite phino in E2.
    simpl in E2.
    inversion E2.

  - (* phi1: alloc  | phi2: alloc  *)
    destruct (jmc1 _ _ _ _ _ E1).
    destruct (jmc2 _ _ _ _ _ E2).
    congruence.

  - (* phi1: alloc  | phi2: free   *)
    congruence.

  - (* phi2: free   | phi2: same   *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial.  
  - (* phi2: free   | phi2: update *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1 rsh2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence.
  - (* phi2: free   | phi2: alloc  *)
    congruence.

  - (* phi2: free   | phi2: free   *)
    congruence.
  - congruence.
Qed.*)

End mpred.
