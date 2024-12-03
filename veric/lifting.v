(* A core wp-based separation logic for Clight, in the Iris style. Maybe VeriC can be built on top of this? *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Cop2.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.external_state.
Require Import VST.veric.tycontext.
Require Import VST.veric.env.
Require Import VST.veric.lifting_expr.

Open Scope maps.

Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree Values.block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.

Class VSTGS OK_ty Σ :=
  { VST_heapGS :: heapGS Σ;
    VST_envGS :: envGS Σ;
    VST_extGS :: externalGS OK_ty Σ }.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty) (ge : genv).

Lemma make_tycontext_v_lookup : forall tys id t,
  make_tycontext_v tys !! id = Some t -> In (id, t) tys.
Proof.
  intros ???; induction tys; simpl.
  - rewrite PTree.gempty //.
  - destruct a as (i, ?).
    destruct (eq_dec id i).
    + subst; rewrite PTree.gss.
      inversion 1; auto.
    + rewrite PTree.gso //; auto.
Qed.

Lemma make_tycontext_v_sound : forall tys id t, list_norepet (map fst tys) ->
  make_tycontext_v tys !! id = Some t <-> In (id, t) tys.
Proof.
  intros; split; first apply make_tycontext_v_lookup.
  induction tys; simpl; first done.
  intros [-> | ?].
  - apply PTree.gss.
  - destruct a; inv H.
    rewrite PTree.gso; auto.
    intros ->.
    contradiction H3; rewrite in_map_iff; eexists (_, _); eauto.
Qed.

Definition match_venv (ve: venviron) (vars: list (ident * type)) :=
 forall id, match lookup id ve with Some (b,t) => In (id,t) vars | _ => True end.

Lemma typecheck_var_match_venv : forall ve tys,
  typecheck_var_environ ve (make_tycontext_v tys) → match_venv ve tys.
Proof.
  unfold typecheck_var_environ, match_venv; intros.
  destruct (lookup id ve) as [(?, ty)|] eqn: Hid; last done.
  destruct (H id ty) as [_ Hty].
  apply make_tycontext_v_lookup, Hty; eauto.
Qed.

Definition jsafeN :=
  jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge.

Definition cont_to_state f ve te ctl :=
  match ctl with
  | Kseq s ctl' => Some (State f s ctl' ve te)
  | Kloop1 body incr ctl' => Some (State f Sskip (Kloop1 body incr ctl') ve te)
  | Kloop2 body incr ctl' => Some (State f (Sloop body incr) ctl' ve te)
  | Kcall id' f' ve' te' k' => Some (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
  | Kstop => Some (State f (Sreturn None) Kstop ve te)
  | _ => None
  end.

Fixpoint stack_depth k :=
  match k with
  | Kcall _ _ _ _ k' => S (stack_depth k')
  | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' => stack_depth k'
  | Kstop => O
  end.

Definition stack_depth' k := match k with Some k' => stack_depth k' | None => O end.

Fixpoint cont_to_stack k :=
  match k with
  | Kcall _ _ ve te k' => (ve, te) :: cont_to_stack k'
  | Kseq _ k' | Kloop1 _ _ k' | Kloop2 _ _ k' | Kswitch k' => cont_to_stack k'
  | Kstop => []
  end.

Fixpoint stack_matches ρ le n : Prop :=
  match le, n with
  | [], O => True
  | (ve, te) :: le', S n' => env_matches (env_to_environ ρ n') ge ve te ∧
      stack_matches ρ le' n'
  | _, _ => False
  end.

Definition stack_matches' (ρ: env_state) ve te (ctl: option cont) : Prop :=
  match ctl with None => True
  | Some k => env_matches (env_to_environ ρ (stack_depth k)) ge ve te ∧
              stack_matches ρ (cont_to_stack k) (stack_depth k) ∧
              ∀ n, (stack_depth k < n)%nat → lookup n ρ.2 = None end.

Definition make_env {A} (ve : PTree.t A) : gmap ident A :=
  PTree.fold (fun e i v => <[i := v]>e) ve empty.

Lemma make_env_spec : forall {A} (ve : PTree.t A) i, lookup i (make_env ve) = PTree.get i ve.
Proof.
  intros; unfold make_env.
  eapply PTree_Properties.fold_ind.
  - intros; rewrite H //.
  - intros ?????? Hrem.
    destruct (eq_dec i k).
    + subst; rewrite lookup_insert //.
    + rewrite lookup_insert_ne //.
      rewrite PTree.gro // in Hrem.
Qed.

Definition assert_safe (E: coPset) (f: function) (ctl: option cont) : mpred :=
  ∀ ora ρ ve te,
       env_auth ρ -∗
       ⌜stack_matches' ρ ve te ctl⌝ →
       (* this is the only tycontext piece we actually need *)
       ⌜typecheck_var_environ (make_env ve) (make_tycontext_v f.(fn_vars))⌝ →
       match option_bind _ _ (cont_to_state f ve te) ctl with
       | Some c => jsafeN E ora c
       | None => |={E}=> False
       end.

Global Instance assert_safe_absorbing E f ctl : Absorbing (assert_safe E f ctl).
Proof.
  rewrite /assert_safe.
  repeat (apply bi.forall_absorbing; intros).
  apply bi.wand_absorbing_r.
  apply bi.impl_absorbing; try apply _.
  apply bi.impl_absorbing; try apply _.
  destruct (option_bind _ _ _ _); apply _.
Qed.

Lemma assert_safe_mono E1 E2 f ctl: E1 ⊆ E2 ->
  assert_safe E1 f ctl ⊢ assert_safe E2 f ctl.
Proof.
  rewrite /assert_safe; intros.
  iIntros "H" (????) "?%%"; iSpecialize ("H" with "[$] [//] [//]").
  destruct option_bind.
  - by iApply jsafe_mask_mono.
  - iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
Qed.

Lemma fupd_assert_safe : forall E f k,
  (|={E}=> assert_safe E f k) ⊢ assert_safe E f k.
Proof.
  intros; iIntros "H" (????) "?%%".
  iSpecialize ("H" with "[$] [//] [//]").
  destruct option_bind; by iMod "H".
Qed.

Global Instance elim_modal_fupd_assert_safe p P E f c :
  ElimModal Logic.True p false (|={E}=> P) P (assert_safe E f c) (assert_safe E f c).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_assert_safe.
Qed.

Fixpoint break_cont (k: cont) :=
match k with
| Kseq _ k' => break_cont k'
| Kloop1 _ _ k' => Some k'
| Kloop2 _ _ k' => Some k'
| Kswitch k' => Some k'
| _ => None
end.

Fixpoint continue_cont (k: cont) :=
match k with
| Kseq _ k' => continue_cont k'
| Kloop1 s1 s2 k' => Some (Kseq s2 (Kloop2 s1 s2 k'))
| Kswitch k' => continue_cont k'
| _ => None
end.

Definition guarded E f k Q :=
  (RA_normal Q (stack_depth k) -∗ assert_safe E f (Some k)) ∧
  (RA_break Q (stack_depth k) -∗ assert_safe E f (break_cont k)) ∧
  (RA_continue Q (stack_depth k) -∗ assert_safe E f (continue_cont k)) ∧
  (RA_return Q None (stack_depth k) -∗ assert_safe E f (Some (Kseq (Sreturn None) (call_cont k)))) ∧
  (∀ e, wp_expr ge E e (λ v, RA_return Q (Some v)) (stack_depth k) -∗
          assert_safe E f (Some (Kseq (Sreturn (Some e)) (call_cont k)))).

Lemma fupd_guarded : forall E f k Q, (|={E}=> guarded E f k Q) ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "H"; repeat iSplit.
  - iMod "H" as "($ & _)".
  - iMod "H" as "(_ & $ & _)".
  - iMod "H" as "(_ & _ & $ & _)".
  - iMod "H" as "(_ & _ & _ & $ & _)".
  - iMod "H" as "(_ & _ & _ & _ & $)".
Qed.

Global Instance elim_modal_fupd_guarded p P E f k Q :
  ElimModal Logic.True p false (|={E}=> P) P (guarded E f k Q) (guarded E f k Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_guarded.
Qed.

Lemma guarded_strong_mono : forall E f k Q Q',
   ((RA_normal Q (stack_depth k) ={E}=∗ RA_normal Q' (stack_depth k)) ∧
    (RA_break Q (stack_depth k) ={E}=∗ RA_break Q' (stack_depth k)) ∧
    (RA_continue Q (stack_depth k) ={E}=∗ RA_continue Q' (stack_depth k)) ∧
    (∀ v, RA_return Q v (stack_depth k) ={E}=∗ RA_return Q' v (stack_depth k))) ∗
  guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "(Hconseq & H)".
  repeat iSplit; [by iIntros "Q"; iMod ("Hconseq" with "Q") as "Q"; iApply ("H" with "Q")..|].
  iIntros (e) "He".
  iPoseProof (monPred_in_entails with "[Hconseq He]") as "He"; first apply wp_expr_strong_mono.
  { monPred.unseal; iFrame.
    iIntros (? n [=]); subst; iDestruct "Hconseq" as "(_ & _ & _ & H)"; iApply "H". }
  by iApply "H".
Qed.

Lemma guarded_conseq_frame : forall E f k P Q Q'
  (Hnormal : P ∗ RA_normal Q (stack_depth k) ⊢ |={E}=> RA_normal Q' (stack_depth k))
  (Hbreak : P ∗ RA_break Q (stack_depth k) ⊢ |={E}=> RA_break Q' (stack_depth k))
  (Hcontinue : P ∗ RA_continue Q (stack_depth k) ⊢ |={E}=> RA_continue Q' (stack_depth k))
  (Hreturn : ∀ v, P ∗ RA_return Q v (stack_depth k) ⊢ |={E}=> RA_return Q' v (stack_depth k)),
  P ∗ guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "(P & ?)"; iApply guarded_strong_mono; iFrame.
  repeat iSplit; iIntros.
  - iApply Hnormal; iFrame.
  - iApply Hbreak; iFrame.
  - iApply Hcontinue; iFrame.
  - iApply Hreturn; iFrame.
Qed.

Lemma guarded_conseq : forall E f k Q Q'
  (Hnormal : RA_normal Q (stack_depth k) ⊢ |={E}=> RA_normal Q' (stack_depth k))
  (Hbreak : RA_break Q (stack_depth k) ⊢ |={E}=> RA_break Q' (stack_depth k))
  (Hcontinue : RA_continue Q (stack_depth k) ⊢ |={E}=> RA_continue Q' (stack_depth k))
  (Hreturn : ∀ v, RA_return Q v (stack_depth k) ⊢ |={E}=> RA_return Q' v (stack_depth k)),
  guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros; etrans; last apply (guarded_conseq_frame _ _ _ emp); intros; rewrite ?embed_emp bi.emp_sep //.
Qed.

Global Instance guarded_proper : forall E f k, Proper (equiv ==> equiv) (guarded E f k).
Proof.
  intros ????? (H1 & H2 & H3 & H4); rewrite /guarded.
  inv H1; inv H2; inv H3.
  repeat (f_equiv; first by f_equiv).
  pose proof (H4 None) as H5; inv H5.
  f_equiv; first by f_equiv.
  do 6 f_equiv; done.
Qed.

Lemma guarded_normal : forall E f k P,
  guarded E f k (normal_ret_assert P) ⊣⊢ (P (stack_depth k) -∗ assert_safe E f (Some k)).
Proof.
  intros.
  iSplit.
  { iIntros "H"; by iDestruct "H" as "[? _]". }
  iIntros "H"; iSplit; first by iApply "H".
  repeat (iSplit; first by simpl; monPred.unseal; iIntros "[]").
  iIntros (?) "He".
  rewrite /wp_expr.
  iIntros (????) "?%%".
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  repeat monPred.unseal.
  iMod ("He" with "[%] Hm [%] [$]") as ">(% & ? & ? & ? & [])"; done.
Qed.

Definition wp E s (Q : ret_assert) : assert :=
    ∀ E' f k, ⌜E ⊆ E'⌝ → <affine> (* should use monPred_in here *) assert_of (λ n, ⌜n = stack_depth k⌝) -∗ (* ▷ *) ⎡guarded E' f k Q⎤ -∗ ⎡assert_safe E' f (Some (Kseq s k))⎤.
(* ▷ would make sense here, but removing Kseq isn't always a step: for instance, Sskip Kstop is a synonym
   for (Sreturn None) Kstop rather than stepping to it. *)

Lemma fupd_wp E s Q : (|={E}=> wp E s Q) ⊢ wp E s Q.
Proof.
  rewrite /wp.
  iIntros "H" (????) "??".
  iApply fupd_assert_safe. iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  by rewrite embed_fupd; iMod "H"; iMod "Hclose"; iApply ("H" with "[%] [$]").
Qed.

Global Instance elim_modal_fupd_wp p P E k Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp E k Q) (wp E k Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp.
Qed.

Global Instance is_except_0_wp E s Q : IsExcept0 (wp E s Q).
Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

Lemma wp_mask_mono : forall E E' s Q (HE : E ⊆ E'),
  wp E s Q ⊢ wp E' s Q.
Proof.
  rewrite /wp; intros.
  iIntros "H" (????); iApply "H".
  iPureIntro; set_solver.
Qed.

Lemma wp_strong_mono : forall E s Q Q',
  ((RA_normal Q ={E}=∗ RA_normal Q') ∧
   (RA_break Q ={E}=∗ RA_break Q') ∧
   (RA_continue Q ={E}=∗ RA_continue Q') ∧
   (∀ v, RA_return Q v ={E}=∗ RA_return Q' v)) ∗
  wp E s Q ⊢ wp E s Q'.
Proof.
  split => n; rewrite /wp; monPred.unseal.
  iIntros "(Hconseq & H)" (???? <- ?? [=]) "Hn % <- HG"; subst j.
  rewrite monPred_at_affinely; iDestruct "Hn" as %->.
  iApply "H"; [rewrite ?monPred_at_affinely; done..|].
  iApply guarded_strong_mono; iFrame.
  repeat iSplit.
  - iIntros "?"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
    iDestruct "Hconseq" as "(H & _)"; iMod ("H" with "[//] [$]").
    by iMod "Hclose".
  - iIntros "?"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
    iDestruct "Hconseq" as "(_ & H & _)"; iMod ("H" with "[//] [$]").
    by iMod "Hclose".
  - iIntros "?"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
    iDestruct "Hconseq" as "(_ & _ & H & _)"; iMod ("H" with "[//] [$]").
    by iMod "Hclose".
  - iIntros (?) "?"; iMod (fupd_mask_subseteq E) as "Hclose"; first done.
    iDestruct "Hconseq" as "(_ & _ & _ & H)"; iMod ("H" with "[//] [$]").
    by iMod "Hclose".
Qed.

Lemma wp_frame : forall E s Q R, R ∗ wp E s Q ⊢ wp E s (frame_ret_assert Q R).
Proof.
  split => n; rewrite /wp; monPred.unseal.
  iIntros "(R & H)" (???? <- ?? [=]) "Hn % <- G"; subst.
  rewrite monPred_at_affinely; iDestruct "Hn" as %->.
  iApply "H"; [rewrite ?monPred_at_affinely //..|].
  iApply (guarded_conseq_frame _ _ _ (R _)); last (by iFrame);
    destruct Q; simpl; intros; monPred.unseal; iIntros "($ & $)"; done.
Qed.

Lemma wp_conseq : forall E s Q Q'
  (Hnormal : RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, RA_return Q v ⊢ |={E}=> RA_return Q' v),
  wp E s Q ⊢ wp E s Q'.
Proof.
  intros; rewrite /wp.
  iIntros "H" (????) "? HG".
  rewrite guarded_conseq; first by iApply ("H" with "[%] [$]").
  - rewrite Hnormal; monPred.unseal; by apply fupd_mask_mono.
  - rewrite Hbreak; monPred.unseal; by apply fupd_mask_mono.
  - rewrite Hcontinue; monPred.unseal; by apply fupd_mask_mono.
  - intros; rewrite Hreturn; monPred.unseal; by apply fupd_mask_mono.
Qed.

Global Instance wp_proper E s : Proper (equiv ==> equiv) (wp E s).
Proof.
  solve_proper.
Qed.

Lemma wp_seq : forall E s1 s2 Q, wp E s1 (overridePost (wp E s2 Q) Q) ⊢ wp E (Ssequence s1 s2) Q.
Proof.
  intros; rewrite /wp.
  iIntros "H %%%% Hn Hk" (????) "?%%".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[//] [Hn] [Hk] [$] [%] [%]"); [done | | done..].
  iSplit; last by iDestruct ("Hk") as "[_ $]".
  iStopProof; split => n; monPred.unseal.
  iIntros "Hk H"; iApply "H"; auto.
  rewrite monPred_at_affinely //.
Qed.

Definition valid_val v :=
  match v with Vptr _ _ => expr.valid_pointer v | _ => True end.

Definition valid_val0 m v : Prop :=
  match v with Vptr b o => valid_pointer m b (Ptrofs.intval o) = true | _ => True end.

Lemma valid_val_mem : forall m v, mem_auth m ∗ valid_val v ⊢ ⌜valid_val0 m v⌝.
Proof.
  iIntros (??) "(Hm & Hv)"; destruct v; try done.
  iApply expr_lemmas4.valid_pointer_dry0; iFrame.
Qed.

Lemma bool_val_valid : forall m v t b, valid_val0 m v -> Cop2.bool_val t v = Some b -> Cop.bool_val v t m = Some b.
Proof.
  rewrite /Cop2.bool_val /Cop.bool_val.
  intros; destruct t; try done; simpl.
  - destruct i; done.
  - destruct v; try done.
    simpl in *.
    simple_if_tac; try done.
    rewrite /weak_valid_pointer H //.
  - destruct f; done.
  - destruct (Cop2.eqb_type _ _); try done.
    rewrite /Cop2.bool_val_p in H0.
    simple_if_tac.
    + destruct v; try done.
      rewrite /weak_valid_pointer H //.
    + destruct v; try done.
      rewrite /weak_valid_pointer H //.
Qed.

Lemma wp_if: forall E e s1 s2 R,
  wp_expr ge E e (λ v, ⎡valid_val v⎤ ∧ ∃ b, ⌜Cop2.bool_val (typeof e) v = Some b⌝ ∧ ▷ if b then wp E s1 R else wp E s2 R)
  ⊢ wp E (Sifthenelse e s1 s2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%%% ? Hk" (????) "? (% & %) %".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(% & ? & Hm & Hr & H)".
  iMod "Hclose" as "_".
  iDestruct (valid_val_mem with "[Hm H]") as %?.
  { rewrite bi.and_elim_l; iFrame. }
  rewrite bi.and_elim_r; iDestruct "H" as (b ?) "H".
  rewrite embed_fupd; iIntros "!>"; iExists _, m.
  iStopProof; split => ?; monPred.unseal; rewrite !monPred_at_affinely.
  iIntros "(% & ? & ? & % & ? & Hr & H)"; subst.
  iSplit.
  { iPureIntro.
    econstructor; eauto.
    apply bool_val_valid; eauto. }
  iFrame.
  destruct b; simpl; iNext; iApply ("H" with "[%] [%] [%] [] [%] [-Hr] Hr"); rewrite ?monPred_at_affinely; done.
Qed.

(* see also semax_lemmas.derives_skip *)
Lemma safe_skip : forall E ora f k ρ ve te
  (Hty : typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f)))
  (Henv : stack_matches' ρ ve te (Some k)),
  env_auth ρ ∗ assert_safe E f (Some k) ⊢
  jsafeN E ora (State f Sskip k ve te).
Proof.
  intros; iIntros "(Hr & H)".
  rewrite /assert_safe.
  iSpecialize ("H" with "Hr [%] [%]"); [done..|].
  destruct k as [ | s ctl' | | | |]; try done; try solve [iApply (jsafe_local_step with "H"); constructor].
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iMod "H" as "[]".
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

Lemma wp_skip: forall E R, RA_normal R ⊢ wp E Sskip R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%%% ? Hk" (????) "?%%".
  iDestruct "Hk" as "[Hk _]".
  iStopProof; split => ?; monPred.unseal; rewrite monPred_at_affinely.
  iIntros "(? & -> & Hk & ?)".
  by iApply safe_skip; last by iFrame; iApply "Hk".
Qed.

Lemma env_to_environ_set : forall ρ n i v, let rho := env_to_environ ρ n in
  env_to_environ (set_temp ρ n i v) n = (ge_of rho, ve_of rho,
    match (snd ρ !! n)%stdpp with Some _ => <[i := v]> (te_of rho) | None => te_of rho end).
Proof.
  intros; subst rho; rewrite /env_to_environ /set_temp.
  destruct ρ as (?, s); simpl; destruct (s !! n)%stdpp as [(?, ?)|] eqn: Hs; simpl.
  - rewrite lookup_insert //.
  - rewrite Hs //.
Qed.

Lemma env_to_environ_set' : forall ρ n n' i v, n' ≠ n →
  env_to_environ (set_temp ρ n i v) n' = env_to_environ ρ n'.
Proof.
  intros; rewrite /env_to_environ /set_temp.
  destruct ρ as (?, s); simpl; destruct (s !! n)%stdpp as [(?, ?)|] eqn: Hs; simpl.
  - rewrite lookup_insert_ne //.
  - done.
Qed.

Lemma stack_matches_set : forall ρ le n n' i v, (n <= n')%nat →
  stack_matches ρ le n → stack_matches (set_temp ρ n' i v) le n.
Proof.
  induction le as [|(?, ?)]; destruct n; simpl; try done.
  intros ???? (? & ?).
  split; first by rewrite env_to_environ_set' //; lia.
  apply IHle; [lia | done].
Qed.

(* We need a temp assertion so we know that the frame doesn't have a value for
   the variable we're setting. On entering a function, we can initialize all
   its temps to Vundef. *)
Lemma wp_set: forall E i e R,
  wp_expr ge E e (λ v, ▷ (∃ v0, temp i v0) ∗ ▷ (temp i v -∗ RA_normal R)) ⊢ wp E (Sset i e) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%%% ? Hk" (????) "Hr (%Henv & %Hstack) %".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm Hr") as ">(% & ? & Hm & Hr & H)".
  rewrite embed_fupd; iMod "Hclose" as "_"; iIntros "!>".
  iStopProof; split => ?; monPred.unseal; rewrite !monPred_at_affinely.
  iIntros "(-> & Hk & Ho & % & Hm & Hr & H)".
  iExists _, _; iSplit.
  { iPureIntro; constructor; eauto. }
  iFrame "Hm Ho"; iNext.
  iDestruct "H" as "((% & Ht) & H)".
  iDestruct (temp_e with "[$Hr $Ht]") as %Hi.
  iMod (temp_update with "[$Hr $Ht]") as "(? & ?)".
  iSpecialize ("H" with "[//] [$]").
  iDestruct "Hk" as "[Hk _]".
  iApply safe_skip; last by iFrame; iApply "Hk".
  - done.
  - destruct Hstack as (? & Hover); split3.
    + rewrite env_to_environ_set.
      destruct Henv as (? & ? & ?); split3; auto; simpl.
      rewrite /env_to_environ in Hi.
      intros id; destruct (snd ρ !! stack_depth k)%stdpp as [(?, ?)|].
      destruct (eq_dec id i).
      * subst; rewrite PTree.gss lookup_insert //.
      * rewrite PTree.gso // lookup_insert_ne //.
      * rewrite lookup_empty // in Hi.
    + apply stack_matches_set; auto.
    + intros; rewrite /set_temp in Hover |- *.
      destruct ρ as (?, s), (s !! stack_depth k)%stdpp as [(?, ?)|]; auto.
      rewrite lookup_insert_ne; auto; lia.
Qed.

(*Lemma mapsto_can_store : forall sh t ch b o v v' m (Hwrite : writable0_share sh) (Hch : access_mode t = By_value ch),
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ ⌜∃ m', Mem.store ch m b (Ptrofs.unsigned o) v' = Some m'⌝.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; by iApply (mapsto_can_store with "[$]").
Qed.

(* Usually we store at the same type consistently, but this describes the more
   general case where we don't. *)
Lemma mapsto_store': forall t t' m ch ch' v v' sh b o m' (Hsh : writable0_share sh)
  (Hch : access_mode t = By_value ch) (Hch' : access_mode t' = By_value ch')
  (Hdec : decode_encode_val_ok ch ch') (Ht' : type_is_volatile t' = false)
  (Halign : (align_chunk ch' | Ptrofs.unsigned o)%Z) (Htc : tc_val' t' (decode_val ch' (encode_val ch v'))),
  Mem.store ch m b (Ptrofs.unsigned o) v' = Some m' ->
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ |==> mem_auth m' ∗ ∃ v'', ⌜decode_encode_val v' ch ch' v''⌝ ∧ mapsto sh t' (Vptr b o) v''.
Proof.
  intros; rewrite /mapsto Hch Hch' Ht'.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> !if_true by auto.
  setoid_rewrite if_true; last auto.
  assert (forall v'', decode_encode_val v' ch ch' v'' -> tc_val' t' v'') as Htc'.
  { intros ? Hv''; eapply decode_encode_val_fun in Hv''; last apply decode_encode_val_general; subst; auto. }
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; (iMod (mapsto_store' _ _ _ _ v' with "[$]") as "[$ (% & %Hv'' & H)]"; [done..|]; iIntros "!>";
    iExists _; iSplit; first done; destruct (eq_dec v'' Vundef); [iRight | specialize (Htc' _ Hv'' n); iLeft]; eauto).
Qed.

Definition numeric_type (t: type) : bool :=
match t with
| Tint IBool _ _ => false
| Tint _ _ _ => true
| Tlong _ _ => true
| Tfloat _ _ => true
| _ => false
end.

Lemma decode_encode_tc: forall t t' ch ch' v
  (Hnumeric : numeric_type t && numeric_type t' = true)
  (Hch : access_mode t = By_value ch) (Hch' : access_mode t' = By_value ch')
  (Hdec : decode_encode_val_ok ch ch') (Htc : tc_val' t v), tc_val' t' (decode_val ch' (encode_val ch v)).
Proof.
  intros; intros Hv.
  destruct ch, ch'; try contradiction Hdec;
        destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv Hch;
        destruct t' as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv Hch';
        destruct v; simpl in *; subst; try contradiction; specialize (Htc ltac:(discriminate));
        try apply I;
        rewrite /decode_val ?proj_inj_bytes;
        match goal with
        | |- context [Int.sign_ext ?n] => apply (expr_lemmas3.sign_ext_range' n); compute; split; congruence
        | |- context [Int.zero_ext ?n] => apply (expr_lemmas3.zero_ext_range' n); compute; split; congruence
        | |- _ => idtac
        end; done.
Qed.

(* This is only really useful for unions. *)
Lemma wp_store': forall E f e1 e2 t2 ch1 ch2 R
  (Hnumeric : numeric_type (typeof e1) && numeric_type t2 = true)
  (Hch1 : access_mode (typeof e1) = By_value ch1)
  (Hch2 : access_mode t2 = By_value ch2),
  decode_encode_val_ok ch1 ch2 →
  wp_expr ge E (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue ge E e1 (λ '(b, o), let v1 := Vptr b (Ptrofs.repr o) in
    ∃ sh, ⌜writable0_share sh⌝ ∧ ▷ (mapsto_ sh (typeof e1) v1 ∧ mapsto_ sh t2 v1) ∗
    ▷ ((∃ v', ⌜decode_encode_val v2 ch1 ch2 v'⌝ ∧ mapsto sh t2 v1 v') ={E}=∗ RA_normal R)))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "? %Henv %".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(%v2 & %He2 & Hm & ? & % & H)".
  iMod ("H" with "Hm [$]") as ">(%b & %o & % & Hm & ? & H)".
  iDestruct "H" as (sh ?) "(Hp & H)".
  rewrite Ptrofs.repr_unsigned.
  iDestruct (add_and _ (▷ ⌜type_is_volatile t2 = false ∧ (align_chunk ch2 | Ptrofs.unsigned o)%Z⌝) with "Hp") as "(Hp & >(% & %))".
  { iIntros "(_ & H) !>".
    rewrite /mapsto_ /mapsto Hch2.
    destruct (type_is_volatile t2); first done.
    rewrite -> if_true by auto.
    iDestruct "H" as "[(% & H) | (% & % & H)]"; rewrite address_mapsto_align; iDestruct "H" as "[_ %]"; done. }
  iCombine "Hm Hp" as "Hp"; iDestruct (add_and _ (▷ ⌜∃ m' : Memory.mem, store ch1 m b (Ptrofs.unsigned o) v2 = Some m'⌝) with "Hp") as "((Hm & Hp) & >(% & %Hstore))".
  { iIntros "(? & ? & _) !>"; iApply mapsto_can_store; eauto; iFrame. }
  iMod "Hclose" as "_"; iIntros "!>".
  specialize (He2 _ _ Henv); inv He2.
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iNext; rewrite bi.and_elim_l; iMod (mapsto_store' _ t2 with "[$]") as "(? & Hp)"; [try done..|].
  { eapply decode_encode_tc; eauto. }
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hp").
  iMod "Hclose" as "_"; iFrame.
  by iApply safe_skip; last by iFrame; iDestruct "Hk" as "[Hk _]"; iApply "Hk".
  { inv H7. }
Qed.

(* This is the more common case. *)
Lemma mapsto_store: forall t m ch v v' sh b o m' (Hsh : writable0_share sh)
  (Htc : tc_val' t v') (Hch : access_mode t = By_value ch),
  Mem.store ch m b (Ptrofs.unsigned o) v' = Some m' ->
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ |==> mem_auth m' ∗ mapsto sh t (Vptr b o) v'.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> !if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; (iMod (mapsto_store _ _ _ v' with "[$]") as "[$ H]"; [done..|];
    destruct (eq_dec v' Vundef); [iRight | specialize (Htc n); iLeft]; eauto).
Qed.

Lemma wp_store: forall E f e1 e2 R,
  wp_expr ge E (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue ge E e1 (λ '(b, o), let v1 := Vptr b (Ptrofs.repr o) in
    ∃ sh, ⌜writable0_share sh⌝ ∧ ▷ mapsto_ sh (typeof e1) v1 ∗
    ▷ (mapsto sh (typeof e1) v1 v2 ={E}=∗ RA_normal R)))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "? %Henv %".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(%v2 & %He2 & Hm & ? & % & H)".
  iMod ("H" with "Hm [$]") as ">(%b & %o & % & Hm & ? & H)".
  iDestruct "H" as (sh ?) "(Hp & H)".
  rewrite Ptrofs.repr_unsigned.
  iDestruct (add_and _ (▷ ⌜∃ ch : memory_chunk, access_mode (typeof e1) = By_value ch⌝) with "Hp") as "(Hp & >(% & %))".
  { apply bi.later_mono; rewrite /mapsto_ mapsto_pure_facts; apply bi.pure_mono; tauto. }
  iCombine "Hm Hp" as "Hp"; iDestruct (add_and _ (▷ ⌜∃ m' : Memory.mem, store ch m b (Ptrofs.unsigned o) v2 = Some m'⌝) with "Hp") as "((Hm & Hp) & >(% & %Hstore))".
  { iIntros "(? & ?) !>"; iApply mapsto_can_store; eauto; iFrame. }
  iMod "Hclose" as "_"; iIntros "!>".
  specialize (He2 _ _ Henv); inv He2.
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iNext; iMod (mapsto_store with "[$]") as "(? & Hp)"; [done..|].
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hp").
  iMod "Hclose" as "_"; iFrame.
  by iApply safe_skip; last by iFrame; iDestruct "Hk" as "[Hk _]"; iApply "Hk".
  { inv H5. }
Qed.

Definition control_as_safex c1 k1 c2 k2 :=
    forall E (ora : OK_ty) f (ve : env) (te : temp_env),
        jsafeN E ora (State f c1 k1 ve te) ⊢
          jsafeN E ora (State f c2 k2 ve te).

Definition control_as_safe ctl1 ctl2 :=
 match ctl1, ctl2 with
 | Kseq c1 k1, Kseq c2 k2 =>
                   control_as_safex c1 k1 c2 k2
 | Kseq c1 k1, Kloop1 _ _ _ =>
                   control_as_safex c1 k1 Sskip ctl2
 | Kseq c1 k1, Kloop2 body incr k2 =>
                   control_as_safex c1 k1 (Sloop body incr) k2
 | Kseq c1 k1, Kstop =>
                   control_as_safex c1 k1 (Sreturn None) Kstop
 | Kseq c1 k1, Kcall _ _ _ _ _ =>
                   control_as_safex c1 k1 (Sreturn None) ctl2
 | Kseq _ _, _ =>
                   False%type
 | Kloop1 _ _ _, Kseq c2 k2 =>
                   control_as_safex Sskip ctl1 c2 k2
 | Kloop1 _ _ _, Kloop1 _ _ _ =>
                   control_as_safex Sskip ctl1 Sskip ctl2
 | Kloop1 _ _ _, Kloop2 body incr k2 =>
                   control_as_safex Sskip ctl1 (Sloop body incr) k2
 | Kloop1 _ _ _, _ =>
                   False%type
 | Kloop2 b1 i1 k1, Kseq c2 k2 =>
                   control_as_safex (Sloop b1 i1) k1 c2 k2
 | Kloop2 b1 i1 k1, Kloop1 _ _ _ =>
                   control_as_safex (Sloop b1 i1) k1 Sskip ctl2
 | Kloop2 b1 i1 k1, Kloop2 b2 i2 k2 =>
                   control_as_safex (Sloop b1 i1) k1 (Sloop b2 i2) k2
 | Kloop2 _ _ _, _ =>
                   False%type
 | Kstop, Kseq c2 k2 =>
                   control_as_safex (Sreturn None) Kstop c2 k2
 | Kcall _ _ _ _ _, Kseq c2 k2 =>
                   control_as_safex (Sreturn None) ctl1 c2 k2

  | _, _ => ctl1 = ctl2
   end.

Lemma assert_safe_adj:
  forall E f k k',
     control_as_safe k k' ->
     assert_safe E f (Some k) ⊢
     assert_safe E f (Some k').
Proof.
  intros.
  rewrite /assert_safe.
  iIntros "H" (????); simpl.
  destruct k as [ | s ctl' | | | |] eqn:Hk; try contradiction;
  destruct k' as [ | s2 ctl2' | | | |] eqn:Hk'; try contradiction;
  try discriminate; rewrite /= -?H; iApply ("H" $! ora); auto.
Qed.

Lemma wp_loop: forall E f s1 s2 R,
  ▷ wp E f s1 (loop1_ret_assert (wp E f s2 (loop2_ret_assert (wp E f (Sloop s1 s2) R) R)) R) ⊢ wp E f (Sloop s1 s2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%%".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[%] [Hk] [$]"); [done | | done..].
  iAssert (guarded E' f k R -∗
    guarded E' f (Kloop2 s1 s2 k) (loop2_ret_assert (wp E f (Sloop s1 s2) R) R))%I as "H2".
  { iIntros "Hk"; iSplit; [|iSplit; [|iSplit]].
    + by iIntros "H"; iApply "H".
    + iDestruct ("Hk") as "[$ _]".
    + iIntros "[]".
    + iDestruct ("Hk") as "(_ & _ & _ & $)". }
  iSplit; [|iSplit; [|iSplit]].
  - iIntros "H"; iApply assert_safe_adj; last by iApply "H"; first done; iApply "H2".
    rewrite /control_as_safe /control_as_safex; intros.
    iIntros "H"; iApply (jsafe_local_step with "H"); constructor; auto.
  - iDestruct ("Hk") as "[$ _]".
  - iIntros "H"; iApply "H"; first done.
    by iApply "H2".
  - iDestruct ("Hk") as "(_ & _ & _ & $)".
Qed.

Lemma wp_switch: forall E f e ls R,
  wp_expr ge E e (λ v, ∃ i, ⌜sem_switch_arg v (typeof e) = Some i⌝ ∧
    wp E f (seq_of_labeled_statement (select_switch i ls)) (switch_ret_assert R)) ⊢
  wp E f (Sswitch e ls) R.
Proof.
  intros; rewrite /wp /=.
  iIntros "H %%% Hk" (????) "?%%".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(% & % & Hm & ? & % & % & H)".
  iMod "Hclose" as "_"; iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame; iNext.
  iApply ("H" with "[%] [Hk] [$]"); try done.
  iSplit; [|iSplit; [|iSplit]].
  - iIntros "[]".
  - iDestruct ("Hk") as "[$ _]".
  - iDestruct ("Hk") as "(_ & _ & $ & _)".
  - iDestruct ("Hk") as "(_ & _ & _ & $)".
Qed.

Lemma wp_continue: forall E f R,
  RA_continue R ⊢ wp E f Scontinue R.
Proof.
  intros; rewrite /wp /=.
  iIntros "H %%% Hk".
  iDestruct "Hk" as "(_ & _ & Hk & _)".
  iSpecialize ("Hk" with "H").
  iIntros (????) "?%%"; iSpecialize ("Hk" with "[$] [%] [%]"); [done..|].
  destruct (continue_cont k) eqn:Hcont; simpl; last by iMod "Hk" as "[]".
  rename c into k'.
  assert (exists s c, k' = Kseq s c) as (? & ? & Hcase).
  { induction k; inv Hcont; eauto. }
  rewrite Hcase.
  iInduction k as [| | | | |] "IHk" forall (k' Hcont Hcase); try discriminate.
  - iApply jsafe_local_step.
    { constructor. }
    iApply ("IHk" with "[%] [%] Hk"); eauto.
  - inv Hcont.
    iApply jsafe_local_step.
    { intros; apply step_skip_or_continue_loop1; auto. }
    iApply "Hk".
  - iApply jsafe_local_step.
    { apply step_continue_switch. }
    iApply ("IHk" with "[%] [%] Hk"); eauto.
Qed.

Lemma wp_break: forall E f R,
  RA_break R ⊢ wp E f Sbreak R.
Proof.
  intros; rewrite /wp /=.
  iIntros "H %%% Hk".
  iDestruct "Hk" as "(_ & Hk & _)".
  iSpecialize ("Hk" with "H").
  iIntros (????) "?%%"; iSpecialize ("Hk" with "[$] [%] [%]"); [done..|].
  destruct (break_cont k) eqn: Hcont; simpl; last by iMod "Hk" as "[]".
  destruct c; simpl; try iMod "Hk" as "[]".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
  - rename c into k'.
    iInduction k as [| s' | s1 s2 | s1 s2 | |] "IHk" forall (s k' Hcont); try discriminate.
    + iApply jsafe_local_step.
      { constructor. }
      by iApply ("IHk" with "[%] Hk").
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { intros; apply step_skip_break_switch; auto. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext.
      iApply (convergent_controls_jsafe with "Hk"); simpl; try congruence.
      by inversion 1; constructor.
Qed.*)

(* function calls *)
(* It would be nice to decompose this into repeated wp_expr, but it includes typecasts. *)
Definition wp_exprs E es ts Φ : assert :=
  ∀ m rho, ⎡mem_auth m⎤ -∗ ⎡env_auth rho⎤ ={E}=∗
         ∃ vs, <affine> assert_of (λ n, ⌜forall ve te,
            env_matches (env_to_environ rho n) ge ve te ->
            Clight.eval_exprlist ge ve te m es ts vs (*/\ typeof e = t /\ tc_val t v*)⌝) ∗
         ⎡mem_auth m⎤ ∗ ⎡env_auth rho⎤ ∗ Φ vs.

Lemma alloc_vars_lookup :
forall ge id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e !! i = None) ->
Clight.alloc_variables ge (e) m1 l ve m2 ->
(exists v, e !! id = Some v) ->
ve !! id = e !! id.
Proof.
intros.
generalize dependent e.
revert ve m1 m2.

induction l; intros.
inv H1. auto.

inv H1. simpl in *. inv H.
destruct H2.
assert (id <> id0).
intro. subst.  specialize (H0 id0). spec H0. auto. rewrite H // in H0.
eapply IHl in H10.
rewrite Maps.PTree.gso in H10; auto.
auto. intros. rewrite Maps.PTree.gsspec. if_tac. subst. tauto.
apply H0. auto.
rewrite Maps.PTree.gso; auto. eauto.
Qed.

Lemma alloc_vars_lemma : forall ge id ty l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve !! i = None),
list_norepet (map fst l) ->
Clight.alloc_variables ge ve m1 l ve' m2 ->
(In (id, ty) l ->
exists v, ve' !! id = Some (v, ty)).
Proof.
  intros.
  generalize dependent ve.
  revert m1 m2.
  induction l; intros; first done.
  destruct a; simpl in *.
  destruct H1 as [[=] | H1].
  - subst. inv H0. inv H. apply alloc_vars_lookup with (id := id) in H9; auto.
    rewrite H9. rewrite Maps.PTree.gss. eauto.
    { intros. destruct (peq i id); first by subst; tauto. rewrite Maps.PTree.gso; eauto. }
    { rewrite Maps.PTree.gss; eauto. }
  - inv H0. inv H. apply IHl in H10; auto.
    intros. rewrite Maps.PTree.gsspec. if_tac; last eauto. subst; done.
Qed.

Lemma alloc_vars_match_venv_gen: forall ge ve m l0 l ve' m',
  match_venv (make_env ve) l0 ->
  Clight.alloc_variables ge ve m l ve' m' ->
  match_venv (make_env ve') (l0 ++ l).
Proof.
  intros.
  generalize dependent l0; induction H0; intros.
  { rewrite app_nil_r //. }
  specialize (IHalloc_variables (l0 ++ [(id, ty)])).
  rewrite -assoc in IHalloc_variables; apply IHalloc_variables.
  rewrite /match_venv in H1 |- *; intros i; specialize (H1 i).
  rewrite !make_env_spec in H1 |- *.
  destruct (eq_dec i id).
  - subst; rewrite Maps.PTree.gss in_app; simpl; auto.
  - rewrite Maps.PTree.gso //.
    destruct (Maps.PTree.get i e) as [(?, ?)|]; first rewrite in_app; simpl; auto.
Qed.

Lemma alloc_vars_match_venv: forall ge m l ve' m',
  Clight.alloc_variables ge empty_env m l ve' m' ->
  match_venv (make_env ve') l.
Proof.
  intros; eapply (alloc_vars_match_venv_gen _ _ _ []) in H; auto.
  rewrite /match_venv; intros; rewrite make_env_spec.
  rewrite Maps.PTree.gempty //.
Qed.

Lemma alloc_vars_typecheck_environ : forall m l ve' m',
  list_norepet (map fst l) ->
  Clight.alloc_variables ge empty_env m l ve' m' ->
  typecheck_var_environ (make_env ve') (make_tycontext_v l).
Proof.
  intros ????? Halloc.
  rewrite /typecheck_var_environ /=; intros.
  rewrite make_tycontext_v_sound //.
  rewrite /Map.get make_env_spec.
  split.
  + intros; eapply alloc_vars_lemma; eauto.
    intros; apply Maps.PTree.gempty.
  + intros (? & Hi); apply alloc_vars_match_venv in Halloc.
    rewrite /match_venv in Halloc.
    specialize (Halloc id); rewrite make_env_spec Hi // in Halloc.
Qed.

Lemma alloc_block:
 forall m n m' b (Halloc : Mem.alloc m 0 n = (m', b))
   (Hn : 0 <= n < Ptrofs.modulus),
   mem_auth m ⊢ |==> mem_auth m' ∗ memory_block Share.top n (Vptr b Ptrofs.zero).
Proof.
  intros.
  iIntros "Hm"; iMod (mapsto_alloc_bytes with "Hm") as "($ & H)"; first done; iIntros "!>".
  rewrite /memory_block Ptrofs.unsigned_zero.
  iSplit; first by iPureIntro; lia.
  rewrite Z.sub_0_r memory_block'_eq; [| lia..].
  rewrite /memory_block'_alt if_true; last auto.
  rewrite /VALspec_range Nat2Z.id.
  iApply (big_sepL_mono with "H"); intros.
  rewrite address_mapsto_VALspec_range /= VALspec1 //.
Qed.

Definition var_sizes_ok (cenv: composite_env) (vars: list (ident*type)) :=
   Forall (fun var : ident * type => @sizeof cenv (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type): assert :=
  ⌜(sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  ∃ b, lvar (fst idt) (snd idt) b ∗ ⎡memory_block sh (sizeof (snd idt)) (Vptr b Ptrofs.zero)⎤.

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) (args: list val) : assert :=
  ([∗ list] idt ∈ fn_vars f, var_block' Share.top cenv idt) ∗
  ([∗ list] idt;v ∈ (fn_params f ++ fn_temps f);(args ++ repeat Vundef (length (fn_temps f))), temp (fst idt) v).

Definition stackframe_of1 f lb lv : assert := ⌜length lb = length (fn_vars f)⌝ ∧ assert_of (λ n,
  let ve := list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))) in
  let te := list_to_map (zip (map fst (fn_params f) ++ map fst (fn_temps f)) (lv ++ repeat Vundef (length (fn_temps f)))) in
  stack_frag n (/ pos_to_Qp (Pos.of_nat (size ve + size te)))%Qp 1%Qp ve te) ∗
  ([∗ list] idt;b ∈ fn_vars f;lb, ⎡memory_block Share.top (@sizeof (genv_cenv ge) (snd idt)) (Vptr b Ptrofs.zero)⎤).

Lemma monPred_at_big_sepL2 : forall {I : biIndex} {PROP : bi} {A B} (Φ : A → B → monPred I PROP) (l1 : list A) (l2 : list B) n,
  (([∗ list] a1;a2 ∈ l1;l2, Φ a1 a2) n) ⊣⊢ ([∗ list] a1;a2 ∈ l1;l2, Φ a1 a2 n).
Proof.
  induction l1; destruct l2; simpl; intros; monPred.unseal; try done.
  rewrite IHl1 //.
Qed.

(* We need env_auth to take this the other way, since otherwise lvars/temps might
   have the wrong fraction. *)
Lemma stackframe_of_eq1 : forall f lb lv,
  length (fn_vars f) + length (fn_params f) + length (fn_temps f) ≠ 0 →
  list_norepet (map fst (fn_vars f)) →
  length (fn_params f) = length lv → list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) →
  stackframe_of1 f lb lv ⊢
  ([∗ list] '(i,t);b ∈ fn_vars f;lb, lvar i t b) ∗
  ([∗ list] idt;v ∈ (fn_params f ++ fn_temps f);(lv ++ repeat Vundef (length (fn_temps f))), temp (fst idt) v) ∗
  ([∗ list] idt;b ∈ fn_vars f;lb, ⎡memory_block Share.top (@sizeof (genv_cenv ge) (snd idt)) (Vptr b Ptrofs.zero)⎤).
Proof.
  intros.
  iIntros "(% & ? & $)".
  iStopProof; split => n; monPred.unseal; rewrite !monPred_at_big_sepL2 /=.
  erewrite big_sepL2_proper'; [|try done..]. setoid_rewrite lvars_equiv; [|done..].
  2: { by intros ? (?, ?) ?. }
  erewrite big_sepL2_proper'; [|try done..]. setoid_rewrite <-(big_sepL2_fmap_l fst).
  setoid_rewrite temps_equiv.
  4: { intros ? (?, ?) ?; simpl; done. }
  destruct (decide _), (decide _).
  - rewrite map_length app_length in e0; lia.
  - rewrite bi.emp_sep; rewrite -bi.exist_intro; f_equiv.
    admit. admit. admit.
  - rewrite bi.sep_emp; rewrite -bi.exist_intro; f_equiv.
    admit. admit.
  - iIntros "H"; rewrite bi.sep_exist_l; iExists _; rewrite bi.sep_exist_r; iExists _.
    iApply stack_frag_split.
Admitted.

(*Lemma stackframe_of_eq' : forall f lv
  (Hsize: Forall (fun var => @Ctypes.sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
  length (fn_vars f) + length (fn_params f) + length (fn_temps f) ≠ 0 →
  (∃ lb, stackframe_of1 f lb lv) ⊣⊢ stackframe_of' (genv_cenv ge) f lv.
Proof.*)

Definition freeable_blocks: list (Values.block * BinInt.Z * BinInt.Z) -> mpred :=
  fold_right (fun bb a =>
                        match bb with (b,lo,hi) =>
                                          VALspec_range (hi-lo) Share.top (b,lo) ∗ a
                        end)
                    emp.

Lemma build_call_temp_env:
  forall f vl,
     length (fn_params f) = length vl ->
  exists te,  bind_parameter_temps (fn_params f) vl
                     (create_undef_temps (fn_temps f)) = Some te.
Proof.
 intros.
 forget (create_undef_temps (fn_temps f)) as rho.
 revert rho vl H; induction (fn_params f); destruct vl; intros; inv H; try congruence.
 exists rho; reflexivity.
 destruct a; simpl.
 apply IHl. auto.
Qed.

Lemma make_env_set : forall {A} t i (v : A), make_env (PTree.set i v t) = <[i := v]> (make_env t).
Proof.
  intros; apply map_eq; intros k.
  destruct (eq_dec k i).
  - subst; rewrite make_env_spec PTree.gss lookup_insert //.
  - rewrite lookup_insert_ne // !make_env_spec PTree.gso //.
Qed.

Lemma create_undef_map : forall temps, make_env (create_undef_temps temps) = list_to_map (zip (map fst temps) (repeat Vundef (length temps))).
Proof.
  induction temps as [|(?, ?)]; simpl; first done.
  rewrite make_env_set IHtemps //.
Qed.

Lemma bind_temps_map : forall params temps vl te, length params = length vl ->
  list_norepet (map fst params) ->
  bind_parameter_temps params vl (create_undef_temps temps) = Some te ->
  make_env te = list_to_map (zip (map fst params ++ map fst temps) (vl ++ repeat Vundef (length temps))).
Proof.
  intros.
  rewrite zip_with_app; last by rewrite map_length.
  rewrite list_to_map_app -create_undef_map.
  forget (create_undef_temps temps) as e.
  generalize dependent e; generalize dependent vl; induction params as [|(?, ?)]; destruct vl; inversion 1; simpl.
  - inversion 1; rewrite left_id //.
  - inv H0.
    intros ? ->%IHparams; [|done..].
    rewrite make_env_set -insert_union_l -insert_union_r //.
    apply not_elem_of_list_to_map_1.
    rewrite fst_zip.
    rewrite elem_of_list_In //.
    { rewrite map_length; lia. }
Qed.

Lemma bind_parameter_temps_inv : forall params args t te,
  bind_parameter_temps params args t = Some te -> length params = length args.
Proof.
  induction params as [|(?, ?)]; simpl.
  - destruct args; done.
  - destruct args; first done.
    intros ?? ->%IHparams; done.
Qed.

Lemma alloc_stackframe:
  forall m ρ n f args te
      (COMPLETE: Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f))
      (Hsize: Forall (fun var => @Ctypes.sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
      list_norepet (map fst (fn_vars f)) ->
      list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) ->
      bind_parameter_temps (fn_params f) args
                     (create_undef_temps (fn_temps f)) = Some te ->
      (snd ρ !! (S n) = None)%stdpp ->
      mem_auth m ∗ env_auth ρ ⊢ |==> ∃ m' ve lb, ⌜Clight.alloc_variables ge empty_env m (fn_vars f) ve m' ∧
        typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f))⌝ ∧
        mem_auth m' ∗ env_auth (alloc_vars (make_env ve) (make_env te) (S n) ρ) ∗ stackframe_of1 f lb args (S n).
Proof.
  intros.
  cut (mem_auth m ∗ env_auth ρ ⊢ |==> ∃ (m' : Memory.mem) (ve : env) lb,
    ⌜(∀i, sub_option (empty_env !! i)%maps (ve !! i)%maps) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ mem_auth m' ∗ env_auth (alloc_vars (make_env ve) (make_env te) (S n) ρ) ∗ stackframe_of1 f lb args (S n)).
  { intros Hgen; rewrite Hgen; iIntros ">(% & % & % & (% & %) & ?) !>".
    iExists _, _; iFrame; iPureIntro; split3; split; eauto.
    eapply alloc_vars_typecheck_environ; eauto. }
  cut (mem_auth m ⊢ |==> ∃ (m' : Memory.mem) ve (lb : list Values.block),
    ⌜length (fn_vars f) = length lb ∧ make_env ve = list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))) ∪ make_env empty_env ∧ (∀i, sub_option (empty_env !! i)%maps (ve !! i)%maps) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ mem_auth m' ∗ [∗ list] idt;b∈fn_vars f;lb, memory_block Share.top (@sizeof (genv_cenv ge) (snd idt)) (Vptr b Ptrofs.zero)).
  { intros ->; iIntros "(>(% & % & % & (%Hlen & %Hve & % & %) & ? & Hblocks) & Hr)".
    rewrite right_id in Hve.
    iExists m', ve, lb; iFrame.
    pose proof (bind_parameter_temps_inv _ _ _ _ H1) as Hargs.
    rewrite Hve; iMod (env_alloc with "Hr") as "($ & Hvars)"; try done.
    iModIntro; iSplit; first done.
    rewrite /stackframe_of1; monPred.unseal; rewrite !monPred_at_big_sepL2.
    erewrite bind_temps_map; try apply H1; try done; first by iFrame.
    + by eapply list_norepet_append_left. }
  forget (fn_vars f) as vars. clear dependent f.
  assert (forall i, In i (map fst vars) -> empty_env !! i = None) as Hout.
  { intros; apply PTree.gempty. }
  forget empty_env as ve0.
  revert ve0 m Hout Hsize; induction vars; intros; simpl; iIntros "Hm".
  - iExists m, ve0, []; simpl; iFrame; iPureIntro.
    split; auto; split; auto; split3.
    + rewrite left_id //.
    + intros; apply sub_option_refl.
    + constructor.
  - destruct a as (id, ty).
    destruct (Mem.alloc m 0 (@sizeof (genv_cenv ge) ty)) as (m', b) eqn: Halloc.
    inv COMPLETE; inv Hsize; inv H.
    iMod (alloc_block with "Hm") as "(Hm & block)"; first done.
    { pose proof @sizeof_pos (genv_cenv ge) ty; unfold sizeof, Ptrofs.max_unsigned in *; simpl in *; lia. }
    unshelve iMod (IHvars _ _ (Maps.PTree.set id (b,ty) ve0) with "Hm") as (??? (? & Hve & Hsub & ?)) "(Hm & ?)"; try done.
    { intros i; destruct (eq_dec i id); first by subst.
      rewrite PTree.gso //; intros; apply Hout; simpl; auto. }
    iIntros "!>"; iExists _, _, (b :: lb); simpl; iFrame.
    iPureIntro; split; last done; split; first auto; split3.
    + setoid_rewrite Hve; rewrite make_env_set -insert_union_l -insert_union_r //.
      apply not_elem_of_list_to_map_1.
      rewrite fst_zip.
      rewrite elem_of_list_In //.
      { rewrite zip_with_length_l_eq; rewrite map_length; lia. }
    + intros i; specialize (Hsub i).
      destruct (eq_dec i id); last by rewrite Maps.PTree.gso in Hsub.
      subst; rewrite Hout //; simpl; auto.
    + econstructor; eauto.
Qed.

(*Definition maybe_retval (Q: assert) retty ret :=
 assert_of (match ret with
 | Some id => fun rho => ⌜tc_val' retty (eval_id id rho)⌝ ∧ Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => ∃ v: val, ⌜tc_val' retty v⌝ ∧ Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end).*)

Lemma stackframe_blocks_freeable : forall lv lb ve,
  length lv = length lb -> list_norepet (map fst lv) ->
  list_to_map (zip (map fst lv) (zip lb (map snd lv))) = make_env ve ->
  ([∗ list] idt;b ∈ lv;lb, ⌜Ptrofs.unsigned Ptrofs.zero + @sizeof (genv_cenv ge) idt.2 < Ptrofs.modulus⌝
     ∧ memory_block' Share.top (Z.to_nat (@sizeof (genv_cenv ge) idt.2)) b (Ptrofs.unsigned Ptrofs.zero)) ⊢
  freeable_blocks (blocks_of_env ge ve).
Proof.
  induction lv as [|(i, t)]; destruct lb; inversion 1; clear H; simpl; intros Hno Heq; inv Hno.
  - rewrite /blocks_of_env.
    destruct (PTree.elements ve) as [|(i, v)] eqn: Hve; simpl; first done.
    assert (ve !! i = Some v) as Hi by (apply PTree.elements_complete; rewrite Hve; simpl; auto).
    rewrite -make_env_spec -Heq lookup_empty // in Hi.
  - assert (ve !! i = Some (b, t)).
    { rewrite -make_env_spec -Heq lookup_insert //. }
    destruct (@Maps.PTree.elements_remove _ i (b,t) ve H) as [l1 [l2 [Hel Hrem]]].
    rewrite /freeable_blocks /blocks_of_env Hel map_app /=.
    trans (freeable_blocks ((b,0,@Ctypes.sizeof ge t) :: (map (block_of_binding ge) (l1 ++ l2)))).
    2:{ clear.
        induction l1; simpl; try auto.
        destruct a as [id' [hi lo]]. simpl in *.
        iIntros "(? & $ & ?)"; rewrite -IHl1; iFrame. }
    iIntros "((% & H) & Hrest)".
    rewrite memory_block'_eq.
    2: rewrite Ptrofs.unsigned_zero; lia.
    2:{ rewrite Z2Nat.id; try lia.
        pose proof (@sizeof_pos (genv_cenv ge) t); lia. }
    unfold memory_block'_alt.
    rewrite -> if_true by apply readable_share_top.
    rewrite Z2Nat.id.
    2: { pose proof (@sizeof_pos (genv_cenv ge) t); lia. }
    rewrite /= Z.sub_0_r Ptrofs.unsigned_zero; iFrame "H".
    rewrite -Hrem; iApply IHlv; try done.
    apply map_eq; intros k; rewrite make_env_spec; destruct (eq_dec k i).
    + subst; rewrite PTree.grs.
      apply not_elem_of_list_to_map_1.
      rewrite fst_zip.
      rewrite elem_of_list_In //.
      { rewrite zip_with_length_l_eq; rewrite map_length; lia. }
    + rewrite PTree.gro // -make_env_spec -Heq lookup_insert_ne //.
Qed.

Lemma env_matches_make_ve : forall rho ve te, env_matches rho ge ve te -> ve_of rho = make_env ve.
Proof.
  intros ??? (_ & H & _).
  apply map_eq; intros.
  rewrite make_env_spec //.
Qed.

Lemma free_stackframe :
  forall f m ve te lb lv ρ n
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f)))
  (MATCH: env_matches (env_to_environ ρ n) ge ve te),
   mem_auth m ∗ env_auth ρ ∗ stackframe_of1 f lb lv n ⊢
   |==> ∃ m2, ⌜free_list m (blocks_of_env ge ve) = Some m2⌝ ∧ mem_auth m2 ∗ env_auth (ρ.1, delete n ρ.2).
Proof.
  intros.
  rewrite /stackframe_of1; monPred.unseal; rewrite !monPred_at_big_sepL2 /=.
  iIntros "(Hm & Hρ & %Hlen & Hfrag & Hblocks)".
  iDestruct (stack_frag_e_1 with "[$Hρ $Hfrag]") as %(Hve & _).
  apply env_matches_make_ve in MATCH; rewrite MATCH in Hve.
  iMod (env_dealloc with "[$Hρ $Hfrag]") as "$".
  rewrite stackframe_blocks_freeable //.
  forget (blocks_of_env ge ve) as el.
  iInduction el as [|] "IHel" forall (m); first eauto.
  destruct a as ((id, b), t); simpl.
  iDestruct "Hblocks" as "(H & Hblocks)".
  iDestruct (juicy_mem_lemmas.VALspec_range_can_free with "[$Hm $H]") as %(m' & ?).
  rewrite /= Zplus_minus in H; rewrite H.
  iMod (juicy_mem_lemmas.VALspec_range_free with "[$Hm $H]") as "Hm"; first done.
  iApply ("IHel" with "Hm Hblocks").
Qed.

(*Lemma wp_call: forall E f0 i e es R,
  wp_expr ge E e (λ v, ∃ f, ⌜exists b, v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
    classify_fun (typeof e) =
    fun_case_f (type_of_params (fn_params f)) (fn_return f) (fn_callconv f) /\
    Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst f.(fn_params) ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok (genv_cenv ge) (f.(fn_vars))⌝ ∧
    wp_exprs es (type_of_params (fn_params f)) (λ vs, ⌜length vs = length f.(fn_params)⌝ ∧ ▷ assert_of (λ rho,
      ∀ rho', stackframe_of' (genv_cenv ge) f rho' -∗ ▷
      wp E f f.(fn_body) (frame_ret_assert (function_body_ret_assert f.(fn_return) (⎡RA_normal R (set_opttemp i v rho)⎤)) (stackframe_of' (genv_cenv ge) f)) rho'))) ⊢
  wp E f0 (Scall i e es) R.
Print step_returnstate.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H %%% Hk" (??? -> ?).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr /wp_exprs.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[%] Hm") as ">(% & %He & Hm & %f & %Hb & H)"; first done.
  destruct Hb as (b & -> & Hb & ? & ? & ? & ? & ?).
  iDestruct ("H" with "[%] Hm") as (vs Hes) "(Hm & % & H)"; first done.
  iMod "Hclose" as "_"; iIntros "!>".
  specialize (He _ _ eq_refl).
  specialize (Hes _ _ _ eq_refl).
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  destruct (build_call_temp_env f vs) as (le & ?); first done.
  iMod (alloc_stackframe with "Hm") as (m' ve' (? & ?)) "(Hm & Hstack)"; [done..|].
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto.
    * eapply list_norepet_append_left; eauto.
    * apply list_norepet_append_inv; auto. }
  iFrame.
  iApply ("H" with "[$] [%] [Hk]"); [done | | done..].
  iIntros "!>" (rho'); simpl; iSplit.
  - destruct f.(fn_return) eqn: Hretty; monPred.unseal; [|iIntros "([] & _)"..].
    iIntros "(Hret & Hstack)".
    iIntros (??? -> ?); simpl.
    iApply jsafe_step.
    rewrite /jstep_ex.
    iIntros (?) "(Hm & Ho)".
    iMod (free_stackframe with "[$Hm $Hstack]") as (m'' ?) "Hm"; [done..|].
    iIntros "!>".
    iExists _, _; iSplit.
    { iPureIntro; econstructor; eauto. }
    iFrame.
    iNext.
    iApply jsafe_local_step.
    { intros; constructor. }
    iNext.
    simpl.
    iApply safe_skip; last iApply "Hk"; try done.
    destruct i; simpl.
    + rewrite /construct_rho /get_result1 /globals_only /= /globals_only /env_set /=.
    Search globals_only.
Qed.*)

Definition up1 (P : assert) : assert := assert_of (λ n, P (S n)).
Definition down1 (P : assert) : assert := assert_of (λ n, match n with | S n' => P n' | O => False end).

Lemma ge_of_env : forall ρ n, ge_of (env_to_environ ρ n) = ρ.1.
Proof.
  intros; rewrite /env_to_environ.
  destruct (ρ.2 !! n)%stdpp as [(?, ?)|]; done.
Qed.

Lemma env_to_environ_alloc' : forall ρ ve te n n', n' ≠ n → env_to_environ (alloc_vars ve te n ρ) n' = env_to_environ ρ n'.
Proof.
  intros; rewrite /env_to_environ /alloc_vars lookup_insert_ne //.
Qed.

Lemma stack_matches_alloc : forall ρ le n n' ve te, (n <= n')%nat →
  stack_matches ρ le n → stack_matches (alloc_vars ve te n' ρ) le n.
Proof.
  induction le as [|(?, ?)]; destruct n; simpl; try done.
  intros ???? (? & ?).
  split; first by rewrite env_to_environ_alloc' //; lia.
  apply IHle; [lia | done].
Qed.

Lemma stack_matches'_alloc : forall ρ ve te k ve' te' s i f, stack_matches' ρ ve te (Some k) →
  stack_matches' (alloc_vars (make_env ve') (make_env te') (S (stack_depth k)) ρ) ve' te' (Some (Kseq s (Kcall i f ve te k))).
Proof.
  intros.
  destruct H as (Henv & Hstack & Htop); split3.
  - rewrite env_to_environ_alloc; split.
    + destruct Henv as (Hge & _).
      rewrite ge_of_env in Hge; auto.
    + split; simpl; intros; rewrite make_env_spec //.
  - split.
    + rewrite env_to_environ_alloc' //.
    + apply stack_matches_alloc; auto.
  - simpl; intros.
    rewrite lookup_insert_ne; last lia.
    apply Htop; lia.
Qed.

Lemma stack_matches_dealloc : forall ρ le n n', (n <= n')%nat →
  stack_matches ρ le n → stack_matches (ρ.1, delete n' ρ.2) le n.
Proof.
  induction le as [|(?, ?)]; destruct n; simpl; try done.
  intros ?? (? & ?).
  split; first by rewrite env_to_environ_dealloc //; lia.
  apply IHle; [lia | done].
Qed.

Lemma stack_matches'_dealloc : forall ρ ve te k ve' te' i f, stack_matches' ρ ve te (Some (Kcall i f ve' te' k)) →
  stack_matches' (ρ.1, delete (S (stack_depth k)) ρ.2) ve' te' (Some k).
Proof.
  intros.
  destruct H as (Henv & (Henv' & Hstack) & Htop); split3.
  - rewrite env_to_environ_dealloc //.
  - apply stack_matches_dealloc; auto.
  - simpl; intros.
    destruct (eq_dec n (S (stack_depth k))).
    + subst; apply lookup_delete.
    + rewrite lookup_delete_ne //.
      apply Htop; simpl; lia.
Qed.

Lemma wp_call: forall E e es R,
  wp_expr ge E e (λ v, ∃ f, ⌜exists b, v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
    classify_fun (typeof e) =
    fun_case_f (type_of_params (fn_params f)) (fn_return f) (fn_callconv f) /\
    Forall (fun it => complete_type (genv_cenv ge) (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst f.(fn_params) ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok (genv_cenv ge) (f.(fn_vars))⌝ ∧
    wp_exprs E es (type_of_params (fn_params f)) (λ vs, ⌜length vs = length f.(fn_params)⌝ ∧
       ▷ up1 (∀ lb, stackframe_of1 f lb vs -∗ ▷ wp E f.(fn_body) (normal_ret_assert ((∃ vs, stackframe_of1 f lb vs) ∗ down1 (RA_normal R)))))) ⊢
  wp E (Scall None e es) R.
Proof.
  intros; rewrite /wp.
  iIntros "H % %f0 %% Hn Hk" (????) "Hr (%Hmatch & %Hstack & %Htop) %".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr /wp_exprs /=.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm Hr") as ">(% & He & Hm & Hr & %f & %Hb & H)"; [done..|].
  destruct Hb as (b & -> & Hb & ? & ? & ? & ? & ?).
  iMod ("H" with "Hm Hr") as (vs) "(Hes & Hm & Hr & % & H)"; [done..|].
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iStopProof; split => n; monPred.unseal; rewrite !monPred_at_affinely.
  iIntros "(-> & Hk & ? & %He & %Hes & ? & Hr & H)".
  specialize (He _ _ Hmatch).
  specialize (Hes _ _ Hmatch).
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros "!>" (?) "(Hm & Ho)".
  destruct (build_call_temp_env f vs) as (le & ?); first done.
  iMod (alloc_stackframe _ _ (stack_depth k) with "[$Hm $Hr]") as (m' ve' lb (? & ?)) "(Hm & Hr & Hstack)"; [try done..|].
  { auto. }
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto.
    * eapply list_norepet_append_left; eauto.
    * apply list_norepet_append_inv; auto. }
  iFrame.
  iApply ("H" with "[//] [$] [//] [//] [//] [] [//] [Hk] [$Hr //] [%]").
  { rewrite monPred_at_affinely; done. }
  2: { by apply stack_matches'_alloc. }
  2: { done. }
  rewrite guarded_normal /=.
  iIntros "!> ((% & ?) & HR)".
  iIntros (????) "Hr (%Henv' & %Hstack') %".
  iApply jsafe_step.
  rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  iMod (free_stackframe with "[$]") as (m'' ?) "(Hm & ?)"; [done..|].
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_local_step.
  { intros; constructor. }
  iIntros "!> !>"; simpl.
  iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
  * done.
  * eapply stack_matches'_dealloc; split; eauto.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros; simpl; auto.
Qed.

(*Lemma wp_return_Some: forall E e R,
  wp_expr ge E e (λ v, RA_return R (Some v)) ⊢ wp E (Sreturn (Some e)) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%%% ? Hk" (????) "?%%".
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn (Some e)) (call_cont k) ve te)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end.
    rewrite call_cont_idem; econstructor; eauto. }
  iDestruct "Hk" as "(_ & _ & _ & _ & Hk)".
  rewrite wp_expr_mask_mono //.
  iSpecialize ("Hk" with "H").
  by iApply "Hk".
Qed.

Lemma wp_return_None: forall E f R,
  RA_return R None ⊢ wp E f (Sreturn None) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H %%% Hk" (??? -> ?).
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn None) (call_cont k) ve te)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end.
    rewrite call_cont_idem; econstructor; eauto. }
  iDestruct ("Hk" $! _) as "(_ & _ & _ & Hk & _)".
  by iApply ("Hk" with "H").
Qed.*)

Lemma safe_return : forall E f rho ora ve te (Hmatch : match_venv (make_env ve) f.(fn_vars)),
  f.(fn_vars) = [] → env_auth rho ∗ (∀ m, state_interp m ora -∗ ⌜∃ i, ext_spec_exit OK_spec (Some (Vint i)) ora m⌝) ⊢ jsafeN E ora (State f (Sreturn None) Kstop ve te).
Proof.
  intros.
  iIntros "(Hr & H)".
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & ?)".
  rewrite H in Hmatch.
  iIntros "!>"; iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    rewrite /blocks_of_env.
    destruct (PTree.elements ve) as [|(id, (?, ?))] eqn: Hel; first done.
    specialize (Hmatch id); rewrite make_env_spec in Hmatch.
    erewrite PTree.elements_complete in Hmatch; last by rewrite Hel; simpl; auto.
    done. }
  iFrame.
  rewrite jsafe_unfold /jsafe_pre.
  iIntros "!> !> !>" (?) "?"; iLeft.
  iDestruct ("H" with "[$]") as %(? & ?).
  iExists _; simpl; eauto.
Qed.

Lemma guarded_stop : forall E f (P : assert),
  f.(fn_vars) = [] →
  (P O -∗ ∀ m z, state_interp m z -∗ ⌜∃ i, ext_spec_exit OK_spec (Some (Vint i)) z m⌝) ⊢
  guarded E f Kstop (function_body_ret_assert Tvoid P).
Proof.
  intros; iIntros "H".
  iSplit.
  - iIntros "?"; rewrite /assert_safe /=.
    iIntros (????) "? (% & _) %".
    iApply safe_return; try done.
    { by apply typecheck_var_match_venv. }
    iFrame; iIntros; by iApply ("H" with "[$]").
  - do 2 (iSplit; first by simpl; monPred.unseal; iIntros "[]").
    iSplit.
    + iIntros "?"; rewrite /assert_safe /=.
      iIntros (????) "?%%".
      iApply safe_return; try done.
      { by apply typecheck_var_match_venv. }
      iFrame; iIntros; by iApply ("H" with "[$]").
    + iIntros "% He" (????) "Hr %%".
      iApply jsafe_step.
      rewrite /wp_expr /jstep_ex.
      iIntros (?) "(Hm & ?)".
      do 2 monPred.unseal.
      iMod ("He" with "[%] Hm [%] Hr") as ">(% & ? & ? & ? & [] & ?)"; done.
Qed.

End mpred.

(* adequacy: copied from veric/SequentialClight *)
Require Import VST.veric.external_state.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.semantics.

Class VSTGpreS (Z : Type) Σ := {
  VSTGpreS_inv :: invGpreS Σ;
  VSTGpreS_heap :: gen_heapGpreS share address resource Σ;
  VSTGpreS_funspec :: inG Σ (gmap_view.gmap_viewR address (@funspecO' Σ));
  VSTGpreS_env :: inG Σ (ora.prodR (ext_order.inclR (lib.gmap_view.gmap_viewR ident (agree.agreeR (leibnizO Values.block))))
    (ext_order.inclR (iris.algebra.auth.authR (iris.algebra.gmap.gmapUR nat (fixed_fracR frameR)))));
  VSTGpreS_ext :: inG Σ (excl_authR (leibnizO Z))
}.

Definition VSTΣ Z : gFunctors :=
  #[invΣ; gen_heapΣ share address resource; GFunctor (gmap_view.gmap_viewRF address funspecOF');
    (*GFunctor (prodRF () ());*) GFunctor (excl_authR (leibnizO Z)) ].
Global Instance subG_VSTGpreS {Z Σ} : subG (VSTΣ Z) Σ → VSTGpreS Z Σ.
Proof. (*solve_inG. Qed.*) Admitted.

Lemma init_VST: forall Z `{!VSTGpreS Z Σ} (z : Z) ge,
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS Z Σ,
    let H : VSTGS Z Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ env_auth (ge, ∅) ∗ has_ext z) ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (own_alloc(A := ora.prodR (ext_order.inclR (lib.gmap_view.gmap_viewR ident (agree.agreeR (leibnizO Values.block))))
    (ext_order.inclR (iris.algebra.auth.authR (iris.algebra.gmap.gmapUR nat (fixed_fracR frameR)))))
    (lib.gmap_view.gmap_view_auth (DfracOwn 1) (to_agree <$> ge), ● ∅)) as (γe) "?".
  { apply pair_valid; split.
    * apply lib.gmap_view.gmap_view_auth_valid.
    * by apply auth_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iIntros "!>" (?); iExists (GenHeapGS _ _ _ _ γh γm), (FunspecG _ _ γf), (EnvGS _ _ γe), _.
  rewrite /state_interp /mem_auth /funspec_auth /env_auth fmap_empty /=; iFrame.
  iSplit; [|done]. iPureIntro. apply juicy_mem.empty_coherent.
Qed.

Global Instance stepN_absorbing {PROP : bi} `{!BiFUpd PROP} n E1 E2 (P : PROP) `{!Absorbing P}: Absorbing (|={E1}[E2]▷=>^n P).
Proof.
  induction n; apply _.
Qed.

Lemma adequacy: forall `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} ge z q m n,
  state_interp m z ∗ jsafeN OK_spec ge ⊤ z q ⊢
  |={⊤}[∅]▷=>^n ⌜dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge n z q m⌝.
Proof.
  intros.
  iIntros "(S & Hsafe)".
  iLöb as "IH" forall (m z q n).
  destruct n as [|n]; simpl.
  { iPureIntro. constructor. }
  rewrite [in (environments.Esnoc _ "Hsafe" _)]/jsafeN jsafe_unfold /jsafe_pre.
  iMod ("Hsafe" with "S") as "[Hsafe_halt | [Hsafe_core | Hsafe_ext]]".
  - iDestruct "Hsafe_halt" as %(ret & Hhalt & Hexit).
    iApply step_fupd_intro; first done; iApply step_fupdN_intro; first done.
    iPureIntro; eapply safeN_halted; eauto.
  - iMod "Hsafe_core" as "(%c' & %m' & % & Hsafe)".
    iApply fupd_mask_intro; first done.
    iIntros "Hclose !>"; iMod "Hclose" as "_".
    iMod "Hsafe" as "(? & ?)"; iModIntro.
    iSpecialize ("IH" with "[$] [$]").
    iApply (step_fupdN_mono with "IH").
    iPureIntro. eapply safeN_step; eauto.
  - iDestruct "Hsafe_ext" as (ef args w (at_external & Hpre)) "Hpost".
    iAssert (|={⊤}[∅]▷=>^(S n) ⌜(∀ (ret : option val) m' z' n',
      Val.has_type_list args (sig_args (ef_sig ef))
      → Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef))
        → n' ≤ n
            → ext_spec_post OK_spec ef w
                (genv_symb_injective ge) (sig_res (ef_sig ef)) ret z' m'
              → ∃ q',
                  (after_external (cl_core_sem ge) ret q m' = Some q'
                   ∧ dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge n' z' q' m'))⌝) with "[-]" as "Hdry".
      2: { iApply (step_fupdN_mono with "Hdry"); iPureIntro; intros; eapply safeN_external; eauto. }
      iApply step_fupdN_mono; first by do 8 setoid_rewrite bi.pure_forall.
      repeat (setoid_rewrite step_fupdN_plain_forall; last done; [|apply _..]).
      iIntros (ret m' z' n' ????).
      iApply fupd_mask_intro; first done.
      iIntros "Hclose !>"; iMod "Hclose" as "_".
      iMod ("Hpost" with "[%] [%]") as (??) "(S & Hsafe)"; [done..|].
      iSpecialize ("IH" with "[$] [$]").
      iModIntro; iApply step_fupdN_le; [done..|].
      iApply (step_fupdN_mono with "IH"); eauto.
Qed.

Definition ext_spec_entails {M E Z} (es1 es2 : external_specification M E Z) :=
  (forall e x1 p tys args z m, ext_spec_pre es1 e x1 p tys args z m ->
     exists x2, ext_spec_pre es2 e x2 p tys args z m /\
       forall ty ret z' m', ext_spec_post es2 e x2 p ty ret z' m' ->
                            ext_spec_post es1 e x1 p ty ret z' m') /\
  (forall v z m, ext_spec_exit es1 v z m -> ext_spec_exit es2 v z m).

Lemma ext_spec_entails_refl : forall {M E Z} (es : external_specification M E Z), ext_spec_entails es es.
Proof.
  intros; split; eauto.
Qed.

Theorem ext_spec_entails_safe : forall {G C M Z} {genv_symb} Hcore es1 es2 ge n z c m
  (Hes : ext_spec_entails es1 es2),
  @step_lemmas.dry_safeN G C M Z genv_symb Hcore es1 ge n z c m -> @step_lemmas.dry_safeN G C M Z genv_symb Hcore es2 ge n z c m.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros.
  inv H.
  - constructor.
  - eapply step_lemmas.safeN_step; eauto.
    eapply IHn; eauto.
  - destruct Hes as (Hes & ?).
    apply Hes in H1 as (x2 & ? & ?).
    eapply step_lemmas.safeN_external; eauto; intros.
    edestruct H2 as (c' & ? & ?); eauto.
    exists c'; split; auto.
    eapply IHn; eauto; [lia | by split].
  - destruct Hes.
    eapply step_lemmas.safeN_halted; eauto.
Qed.

Definition init_stack (ge : genv) ve te : env_state := (make_env (Genv.genv_symb ge), {[O := (make_env ve, make_env te)]}).

Lemma init_stack_matches : forall ge ve te, stack_matches' ge (init_stack ge ve te) ve te (Some Kstop).
Proof.
  split3; simpl.
  - rewrite /init_stack /env_to_environ lookup_insert /=.
    split3; simpl; intros; rewrite make_env_spec //.
  - done.
  - intros; rewrite lookup_insert_ne //; lia.
Qed.

Lemma wp_adequacy: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
  ge m z f s (R : forall `{!VSTGS OK_ty Σ}, assert) ve te (Hf : f.(fn_vars) = [])
  (EXIT: forall `{!VSTGS OK_ty Σ}, ⊢ (R O -∗ ∀ m z, state_interp m z -∗ ⌜∃ i, ext_spec_exit Espec (Some (Vint i)) z m⌝)),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    <affine> monPred_in(I := stack_index) 0 ∗ ⎡state_interp m z⎤ ∗ ⌜typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f))⌝ ∧ ⎡env_auth (init_stack ge ve te)⎤ ∗ wp Espec ge ⊤ s (function_body_ret_assert Tvoid R)) →
       (forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (State f s Kstop ve te) m (*∧ φ*)) (* note that this includes ext_spec_exit if the program halts *).
Proof.
  intros.
(*  assert (forall n, @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (State f s Kstop ve te) m ∧ φ) as H'; last (split; [eapply H' | apply (H' 0)]; eauto). *)
  (*intros n;*)
  eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc'(Σ := Σ) _ (S n) O); [apply _..|].
  simpl; intros. apply (embed_emp_valid_inj(PROP2 := monPred stack_index _)). iIntros "_".
  iMod (H Hinv) as (????) "?".
  iStopProof.
  rewrite /wp; split => l; monPred.unseal.
  iIntros "(I & S & % & E & H)".
  iApply step_fupd_intro; first done.
  iNext.
  set (HH := Build_VSTGS _ _ _ _ _).
  iApply step_fupdN_mono.
  { apply bi.pure_mono, (ext_spec_entails_safe _ (Espec HH)); auto. }
  iApply (adequacy(VSTGS0 := HH)(OK_spec := Espec HH)).
  iFrame.
  iApply ("H" with "[//] [//] [//] [I] [//] [] E").
  { rewrite !monPred_at_affinely; iDestruct "I" as %?; done. }
  iApply guarded_stop; auto.
  iApply EXIT.
  { iPureIntro; apply init_stack_matches. }
  { done. }
Qed.
