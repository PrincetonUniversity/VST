(* A core wp-based separation logic for Clight, in the Iris style. Maybe VeriC can be built on top of this? *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
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
Require Import VST.veric.valid_pointer.
Require Import VST.veric.env.
Require Import VST.veric.expr.
Require Import VST.veric.simple_mapsto.
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

Definition jsafeN :=
  jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge.

(* Could this just be (State f Sskip ctl ve te)? *)
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

(* cont_safe *)
Definition assert_safe (E: coPset) (f: function) (ctl: option cont) : assert :=
  ∀ ora ρ ve te,
       ⎡env_auth ρ⎤ -∗
       ⌜stack_matches' ρ ve te ctl⌝ →
       (* this is the only tycontext piece we actually need *)
       ⌜typecheck_var_environ (make_env ve) (make_tycontext_v f.(fn_vars))⌝ →
       match ctl with
       | Some k => stack_level (stack_depth k) -∗
           match cont_to_state f ve te k with
           | Some c => ⎡jsafeN E ora c⎤
           | None => |={E}=> False
           end
       | None => |={E}=> False
       end.

Lemma assert_safe_mono E1 E2 f ctl: E1 ⊆ E2 ->
  assert_safe E1 f ctl ⊢ assert_safe E2 f ctl.
Proof.
  rewrite /assert_safe; intros.
  do 11 f_equiv.
  destruct ctl; last by iIntros "H"; iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
  f_equiv.
  destruct (cont_to_state _ _ _ _); last by iIntros "H"; iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
  f_equiv.
  by iApply jsafe_mask_mono.
Qed.

Lemma fupd_assert_safe : forall E f k,
  (|={E}=> assert_safe E f k) ⊢ assert_safe E f k.
Proof.
  intros; iIntros "H" (????) "?%%".
  iSpecialize ("H" with "[$] [//] [//]").
  destruct k; last by iMod "H".
  iIntros "?"; iSpecialize ("H" with "[$]").
  destruct (cont_to_state _ _ _ _); last by iMod "H".
  rewrite -embed_fupd; iModIntro; by iMod "H".
Qed.

Global Instance elim_modal_fupd_assert_safe p P E f c :
  ElimModal Logic.True p false (|={E}=> P) P (assert_safe E f c) (assert_safe E f c).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_assert_safe.
Qed.

Definition wp_expr_opt E f oe (Q : option val → assert) :=
  match oe with
  | Some e => wp_expr ge E f e (λ v, Q (Some v))
  | None => Q None
  end.

Global Instance wp_expr_opt_proper E f oe : Proper (pointwise_relation _ equiv ==> equiv) (wp_expr_opt E f oe).
Proof. destruct oe; solve_proper. Qed.

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
  (RA_normal Q -∗ assert_safe E f (Some k)) ∧
  (RA_break Q -∗ assert_safe E f (break_cont k)) ∧
  (RA_continue Q -∗ assert_safe E f (continue_cont k)) ∧
  (∀ ret, wp_expr_opt E f (option_map (λ e, Ecast e f.(fn_return)) ret) (λ vl, RA_return Q vl) -∗
          assert_safe E f (Some (Kseq (Sreturn ret) (call_cont k)))).

Lemma fupd_guarded : forall E f k Q, (|={E}=> guarded E f k Q) ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "H"; repeat iSplit.
  - iMod "H" as "($ & _)".
  - iMod "H" as "(_ & $ & _)".
  - iMod "H" as "(_ & _ & $ & _)".
  - iMod "H" as "(_ & _ & _ & $)".
Qed.

Global Instance elim_modal_fupd_guarded p P E f k Q :
  ElimModal Logic.True p false (|={E}=> P) P (guarded E f k Q) (guarded E f k Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_guarded.
Qed.

Lemma guarded_strong_mono : forall E f k Q Q',
   ((RA_normal Q ={E}=∗ RA_normal Q') ∧
    (RA_break Q ={E}=∗ RA_break Q') ∧
    (RA_continue Q ={E}=∗ RA_continue Q') ∧
    (∀ v, RA_return Q v ={E}=∗ RA_return Q' v)) ∗
  guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros.
  iIntros "(Hconseq & H)".
  repeat iSplit; [by iIntros "Q"; iMod ("Hconseq" with "Q") as "Q"; iApply ("H" with "Q")..|].
  iIntros ([|]) "Q"; simpl.
  - iPoseProof (wp_expr_strong_mono with "[Hconseq Q]") as "?".
    { iSplitR "Q"; last done.
      iIntros (?); iDestruct "Hconseq" as "(_ & _ & _ & H)"; iApply "H". }
    by iApply "H".
  - iDestruct "Hconseq" as "(_ & _ & _ & Hconseq)"; iMod ("Hconseq" with "Q") as "Q"; by iApply "H".
Qed.

Lemma guarded_conseq_frame : forall E f k P Q Q'
  (Hnormal : P ∗ RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : P ∗ RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : P ∗ RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, P ∗ RA_return Q v ⊢ |={E}=> RA_return Q' v),
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
  (Hnormal : RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, RA_return Q v ⊢ |={E}=> RA_return Q' v),
  guarded E f k Q' ⊢ guarded E f k Q.
Proof.
  intros; etrans; last apply (guarded_conseq_frame _ _ _ emp); intros; rewrite ?embed_emp bi.emp_sep //.
Qed.

Global Instance guarded_proper : forall E f k, Proper (equiv ==> equiv) (guarded E f k).
Proof.
  intros ????? (H1 & H2 & H3 & H4); rewrite /guarded.
  inv H1; inv H2; inv H3.
  repeat (f_equiv; first by f_equiv).
  do 5 f_equiv; done.
Qed.

Lemma guarded_normal : forall E f k P,
  guarded E f k (normal_ret_assert P) ⊣⊢ (P -∗ assert_safe E f (Some k)).
Proof.
  intros.
  iSplit.
  { iIntros "H"; by iDestruct "H" as "[? _]". }
  iIntros "H"; iSplit; first by iApply "H".
  repeat (iSplit; first by iIntros "[]").
  iIntros (?) "Hret"; simpl.
  destruct ret; simpl; last by iDestruct "Hret" as "[]".
  rewrite /wp_expr.
  iIntros (????) "?%%?".
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & Ho)".
  iMod ("Hret" with "Hm [$]") as ">(% & ? & ? & ? & [])"; done.
Qed.

(*Lemma guarded_frame : forall E f k P (Q : assert),
  guarded E f k (frame_ret_assert P Q) ⊣⊢ (Q (stack_depth k) -∗ guarded E f k P).
Proof.
  intros; iSplit; iIntros "H"; rewrite /guarded /=; monPred.unseal.
  - iIntros "Q"; iSplit; [|iSplit; [|iSplit]].
    + iIntros "?"; iDestruct "H" as "(H & _)"; iApply "H"; iFrame.
    + iIntros "?"; iDestruct "H" as "(_ & H & _)"; iApply "H"; iFrame.
    + iIntros "?"; iDestruct "H" as "(_ & _ & H & _)"; iApply "H"; iFrame.
    + iIntros (?) "Hret"; iDestruct "H" as "(_ & _ & _ & H)"; iApply "H".
      destruct ret; simpl; last by iFrame.
      iApply (monPred_in_entails with "[Hret Q]"); first apply wp_expr_strong_mono.
      monPred.unseal; iFrame.
      iIntros (?? [=]); subst; iFrame; auto.
  - iSplit; [|iSplit; [|iSplit]].
    + iIntros "(? & Q)"; iDestruct ("H" with "Q") as "(H & _)"; by iApply "H".
    + iIntros "(? & Q)"; iDestruct ("H" with "Q") as "(_ & H & _)"; by iApply "H".
    + iIntros "(? & Q)"; iDestruct ("H" with "Q") as "(_ & _ & H & _)"; by iApply "H".
    + iIntros (?) "Hret".
      destruct ret; simpl; last by iDestruct "Hret" as "(? & Q)"; iDestruct ("H" with "Q") as "(_ & _ & _ & H)"; iApply "H".
      rewrite /wp_expr; monPred.unseal; iMod "Hret".
      iIntros (????) "?%%".
      rewrite /= /jsafeN jsafe_unfold.
      iIntros "!>" (?) "(? & ?)".
      iMod ("Hret" with "[//] [$] [//] [$]") as (?) "(? & ? & ? & ? & Q)".
This doesn't quite work because there isn't a fupd in jsafe after the quantifiers. *)

(* f is used for only one purpose: for the return type for return statements. *)
Definition wp E f s (Q : ret_assert) : assert :=
    ∀ E' k, ⌜E ⊆ E'⌝ → (* ▷ *) guarded E' f k Q -∗ assert_safe E' f (Some (Kseq s k)).
(* ▷ would make sense here, but removing Kseq isn't always a step: for instance, Sskip Kstop is a synonym
   for (Sreturn None) Kstop rather than stepping to it. *)

Lemma fupd_wp E f s Q : (|={E}=> wp E f s Q) ⊢ wp E f s Q.
Proof.
  rewrite /wp.
  iIntros "H" (???) "?".
  iApply fupd_assert_safe. iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  by iMod "H"; iMod "Hclose"; iApply ("H" with "[%] [$]").
Qed.

Global Instance elim_modal_fupd_wp p P E f k Q :
  ElimModal Logic.True p false (|={E}=> P) P (wp E f k Q) (wp E f k Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r fupd_wp.
Qed.

Global Instance is_except_0_wp E f s Q : IsExcept0 (wp E f s Q).
Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

Lemma wp_mask_mono : forall E E' f s Q (HE : E ⊆ E'),
  wp E f s Q ⊢ wp E' f s Q.
Proof.
  rewrite /wp; intros.
  iIntros "H" (???); iApply "H".
  iPureIntro; set_solver.
Qed.

Lemma wp_strong_mono : forall E f s Q Q',
  ((RA_normal Q ={E}=∗ RA_normal Q') ∧
   (RA_break Q ={E}=∗ RA_break Q') ∧
   (RA_continue Q ={E}=∗ RA_continue Q') ∧
   (∀ v, RA_return Q v ={E}=∗ RA_return Q' v)) ∗
  wp E f s Q ⊢ wp E f s Q'.
Proof.
  rewrite /wp; intros.
  iIntros "(Hconseq & H)" (???) "HG".
  iApply "H"; first done.
  iApply guarded_strong_mono; iFrame.
  repeat iSplit; iIntros; (iApply fupd_mask_mono; first done).
  - iDestruct "Hconseq" as "(H & _)"; by iApply "H".
  - iDestruct "Hconseq" as "(_ & H & _)"; by iApply "H".
  - iDestruct "Hconseq" as "(_ & _ & H & _)"; by iApply "H".
  - iDestruct "Hconseq" as "(_ & _ & _ & H)"; by iApply "H".
Qed.

Lemma wp_frame : forall E f s Q R, R ∗ wp E f s Q ⊢ wp E f s (frame_ret_assert Q R).
Proof.
  rewrite /wp; intros.
  iIntros "(R & H)" (???) "G".
  iApply "H"; first done.
  iApply (guarded_conseq_frame _ _ _ R); last (by iFrame); last iIntros (?);
    destruct Q; simpl; iIntros "($ & $)"; done.
Qed.

Lemma wp_conseq : forall E f s Q Q'
  (Hnormal : RA_normal Q ⊢ |={E}=> RA_normal Q')
  (Hbreak : RA_break Q ⊢ |={E}=> RA_break Q')
  (Hcontinue : RA_continue Q ⊢ |={E}=> RA_continue Q')
  (Hreturn : ∀ v, RA_return Q v ⊢ |={E}=> RA_return Q' v),
  wp E f s Q ⊢ wp E f s Q'.
Proof.
  intros; rewrite /wp.
  iIntros "H" (???) "HG".
  rewrite guarded_conseq; first by iApply ("H" with "[%] [$]").
  - rewrite Hnormal; by apply fupd_mask_mono.
  - rewrite Hbreak; by apply fupd_mask_mono.
  - rewrite Hcontinue; by apply fupd_mask_mono.
  - intros; rewrite Hreturn; by apply fupd_mask_mono.
Qed.

Global Instance wp_proper E f s : Proper (equiv ==> equiv) (wp E f s).
Proof.
  solve_proper.
Qed.

Lemma wp_label : forall E f l s Q, wp E f s Q ⊢ wp E f (Slabel l s) Q.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%%?".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[//] [Hk] [$] [%] [%]"); done.
Qed.

Lemma wp_seq : forall E f s1 s2 Q, wp E f s1 (overridePost (wp E f s2 Q) Q) ⊢ wp E f (Ssequence s1 s2) Q.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%%?".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[//] [Hk] [$] [%] [%]"); [|done..].
  iSplit; last by iDestruct ("Hk") as "[_ $]".
  by iIntros "H"; iApply "H".
Qed.

Definition valid_val v :=
  match v with Vptr _ _ => expr.weak_valid_pointer v | _ => True end.

Global Instance valid_val_absorbing p : Absorbing (valid_val p).
Proof. unfold valid_val. apply _. Qed.

Definition valid_val0 m v : Prop :=
  match v with Vptr b o => Mem.weak_valid_pointer m b (Ptrofs.intval o) = true | _ => True end.

Lemma valid_val_mem : forall m v, mem_auth m ∗ valid_val v ⊢ ⌜valid_val0 m v⌝.
Proof.
  iIntros (??) "(Hm & Hv)"; destruct v; try done.
  iApply weak_valid_pointer_dry; iFrame.
Qed.

Lemma bool_val_valid : forall m v t b, valid_val0 m v -> Cop2.bool_val t v = Some b -> Cop.bool_val v t m = Some b.
Proof.
  rewrite /Cop2.bool_val /Cop.bool_val.
  intros; destruct t; [done | | | | | done..].
  - replace (classify_bool _) with bool_case_i; first by destruct v.
    by destruct i.
  - destruct v; [done..|].
    simpl in *.
    simple_if_tac; try done.
    rewrite H //.
  - destruct f; done.
  - simpl; destruct (Cop2.eqb_type _ _); try done.
    rewrite /Cop2.bool_val_p in H0.
    simple_if_tac.
    + destruct v; try done.
      rewrite H //.
    + destruct v; try done.
      rewrite H //.
Qed.

Lemma wp_if: forall E f e s1 s2 R,
  wp_expr ge E f e (λ v, ▷ (⎡valid_val v⎤ ∧ ∃ b, ⌜Cop2.bool_val (typeof e) v = Some b⌝ ∧ if b then wp E f s1 R else wp E f s2 R))
  ⊢ wp E f (Sifthenelse e s1 s2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "? (% & %) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(% & He & Hm & Hr & H)".
  iMod "Hclose" as "_".
  iCombine "Hm H" as "H".
  iDestruct (add_and _ (▷ ⌜valid_val0 m v⌝) with "H") as "((Hm & H) & >%)".
  { iIntros "(? & ? & _) !>"; iPoseProof (valid_val_mem with "[$]") as "%"; done. }
  rewrite bi.and_elim_r; iDestruct "H" as (b) "H".
  rewrite bi.later_and; iDestruct "H" as "(>% & H)".
  rewrite embed_fupd; iIntros "!>"; iExists _, m.
  iPoseProof (env_match_intro with "Hd") as "#?"; first done.
  iDestruct ("He" with "[$]") as %He.
  pose proof (typecheck_var_match_venv _ _ Hty).
  iSplit.
  { iPureIntro.
    econstructor; eauto.
    apply bool_val_valid; eauto. }
  iFrame.
  iNext.
  rewrite embed_fupd; iModIntro.
  destruct b; simpl; by iApply ("H" with "[//] Hk Hr").
Qed.

Lemma safe_skip : forall E ora f k ρ ve te
  (Hty : typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f)))
  (Henv : stack_matches' ρ ve te (Some k)),
  env_auth ρ ∗ assert_safe E f (Some k) (stack_depth k) ⊢
  jsafeN E ora (State f Sskip k ve te).
Proof.
  intros; iIntros "(Hr & H)".
  rewrite /assert_safe /stack_level; monPred.unseal.
  iSpecialize ("H" with "[%] Hr [%] [%] [%] [%] [%]"); [done..|].
  rewrite monPred_at_affinely; iSpecialize ("H" with "[//]").
  destruct k as [ | s ctl' | | | |]; try done; try solve [iApply (jsafe_local_step with "H"); constructor].
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iMod "H" as "[]".
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

Lemma wp_skip: forall E f R, RA_normal R ⊢ wp E f Sskip R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%%?".
  iDestruct "Hk" as "[Hk _]".
  iApply safe_skip; [done..|].
  iSpecialize ("Hk" with "H").
  by iPoseProof (stack_level_embed with "[$] Hk") as "$".
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

Lemma stack_matches'_set : forall ρ ve te k i v,
  stack_matches' ρ ve te k → (ρ.2 !! stack_depth' k ≠ None)%stdpp →
  stack_matches' (set_temp ρ (stack_depth' k) i v) ve (PTree.set i v te) k.
Proof.
  intros.
  destruct k; auto.
  destruct H as (Henv & ? & Hover); split3.
  - rewrite env_to_environ_set.
    destruct Henv as (? & ? & ?); split3; auto; simpl in *.
    intros id; destruct (snd ρ !! stack_depth c)%stdpp as [(?, ?)|]; last done.
    destruct (eq_dec id i).
    + subst; rewrite PTree.gss lookup_insert //.
    + rewrite PTree.gso // lookup_insert_ne //.
  - apply stack_matches_set; auto.
  - intros; rewrite /set_temp in Hover |- *.
    destruct ρ as (?, s); simpl in *; destruct (s !! stack_depth c)%stdpp as [(?, ?)|]; auto.
    rewrite lookup_insert_ne; auto; lia.
Qed.

(* We need a temp assertion so we know that the frame doesn't have a value for
   the variable we're setting. On entering a function, we can initialize all
   its temps to Vundef. *)
Lemma wp_set: forall E f i e R,
  wp_expr ge E f e (λ v, ▷ ((∃ v0, temp i v0) ∗ (temp i v ={E}=∗ RA_normal R))) ⊢ wp E f (Sset i e) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "Hr (%Henv & %Hstack) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm Hr") as ">(% & He & Hm & Hr & H)".
  rewrite embed_fupd; iMod "Hclose" as "_"; iIntros "!>".
  iPoseProof (env_match_intro with "Hd") as "#?"; first done.
  iDestruct ("He" with "[$]") as %He.
  pose proof (typecheck_var_match_venv _ _ Hty).
  iExists _, _; iSplit.
  { iPureIntro; constructor; eauto. }
  iFrame "Hm Ho"; iNext.
  iDestruct "H" as "((% & Ht) & H)".
  iPoseProof (stack_level_embed with "Hd Ht") as "Ht".
  iDestruct (temp_e with "[$Hr $Ht]") as %Hi.
  iMod (temp_update with "[$Hr $Ht]") as "(? & Ht)".
  iPoseProof (stack_level_elim with "Hd Ht") as "?".
  iSpecialize ("H" with "[$]").
  rewrite embed_fupd.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod "H"; iMod "Hclose" as "_"; iIntros "!>".
  iDestruct "Hk" as "[Hk _]".
  iApply safe_skip.
  - done.
  - eapply (stack_matches'_set _ _ _ (Some k)); first by split.
    intros X; rewrite /env_to_environ X lookup_empty in Hi; done.
  - iSpecialize ("Hk" with "H").
    by iPoseProof (stack_level_embed with "Hd Hk") as "$".
Qed.

Lemma mapsto_can_store : forall sh t ch b o v v' m (Hwrite : writable0_share sh) (Hch : access_mode t = By_value ch),
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ ⌜∃ m', Mem.store ch m b (Ptrofs.unsigned o) v' = Some m'⌝.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> if_true by auto.
  iDestruct "H" as "(% & ?)"; by iApply (mapsto_can_store with "[$]").
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
  iDestruct "H" as "(% & ?)"; iMod (mapsto_store' _ _ _ _ v' with "[$]") as "[$ (% & %Hv'' & H)]"; [done..|]; iIntros "!>".
  iExists _; iSplit; first done; eauto.
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
        | |- context [Int.sign_ext ?n] => apply (sign_ext_range' n); compute; split; congruence
        | |- context [Int.zero_ext ?n] => apply (zero_ext_range' n); compute; split; congruence
        | |- _ => idtac
        end; done.
Qed.

(* This is only really useful for unions. *)
Lemma wp_store': forall E f e1 e2 t2 ch1 ch2 R
  (Hnumeric : numeric_type (typeof e1) && numeric_type t2 = true)
  (Hch1 : access_mode (typeof e1) = By_value ch1)
  (Hch2 : access_mode t2 = By_value ch2),
  decode_encode_val_ok ch1 ch2 →
  wp_expr ge E f (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue ge E f e1 (λ '(b, o), let v1 := Vptr b o in
    ∃ sh, ⌜writable0_share sh⌝ ∧ ▷ (⎡mapsto_ sh (typeof e1) v1 ∧ mapsto_ sh t2 v1⎤ ∗
    ((∃ v', ⌜decode_encode_val v2 ch1 ch2 v'⌝ ∧ ⎡mapsto sh t2 v1 v'⎤) ={E}=∗ RA_normal R))))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "? (%Henv & %) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(%v2 & He2 & Hm & ? & % & H)".
  iMod ("H" with "Hm [$]") as ">(%b & %o & He1 & Hm & ? & H)".
  iDestruct "H" as (sh ?) "(Hp & H)".
  iDestruct (add_and _ (▷ ⌜type_is_volatile t2 = false ∧ (align_chunk ch2 | Ptrofs.unsigned o)%Z⌝) with "Hp") as "(Hp & >(% & %))".
  { iIntros "(_ & H) !>".
    rewrite /mapsto_ /mapsto Hch2.
    iDestruct "H" as (?) "H".
    destruct (type_is_volatile t2); first by rewrite embed_pure.
    rewrite -> if_true by auto.
    iDestruct "H" as "(% & H)"; rewrite address_mapsto_align; iDestruct "H" as "[_ %]"; done. }
  iCombine "Hm Hp" as "Hp"; iDestruct (add_and _ (▷ ⌜∃ m' : Memory.mem, store ch1 m b (Ptrofs.unsigned o) v2 = Some m'⌝) with "Hp") as "((Hm & Hp) & >(% & %Hstore))".
  { iIntros "(? & H & _) !>". iDestruct "H" as (?) "?". rewrite -embed_pure; iApply mapsto_can_store; eauto; iFrame. }
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iPoseProof (env_match_intro with "Hd") as "#?"; first done.
  iDestruct ("He1" with "[$]") as %He1; iDestruct ("He2" with "[$]") as %He2.
  pose proof (typecheck_var_match_venv _ _ Hty) as Hmatch.
  specialize (He2 Hmatch); inv He2.
  2: { inv H6. }
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iNext; rewrite bi.and_elim_l.
  iDestruct "Hp" as (?) "Hp".
  iMod (mapsto_store' _ t2 with "[$]") as "(? & Hp)"; [try done..|].
  { eapply decode_encode_tc; eauto. }
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[Hp]").
  { iDestruct "Hp" as (?) "(% & $)"; auto. }
  iMod "Hclose" as "_"; iFrame.
  iApply safe_skip; [done..|].
  iFrame; iDestruct "Hk" as "[Hk _]".
  rewrite embed_fupd; iModIntro; iApply (stack_level_embed with "Hd"); by iApply "Hk".
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
  iDestruct "H" as "(% & ?)"; (iMod (mapsto_store _ _ _ v' with "[$]") as "[$ H]"; [done..|];
    eauto).
Qed.

Lemma wp_store: forall E f e1 e2 R,
  wp_expr ge E f (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue ge E f e1 (λ '(b, o), let v1 := Vptr b o in
    ∃ sh, ⌜writable0_share sh⌝ ∧ ▷ (⎡mapsto_ sh (typeof e1) v1⎤ ∗
    (⎡mapsto sh (typeof e1) v1 v2⎤ ={E}=∗ RA_normal R))))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "? (%Henv & %) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(%v2 & He2 & Hm & ? & % & H)".
  iMod ("H" with "Hm [$]") as ">(%b & %o & He1 & Hm & ? & H)".
  iDestruct "H" as (sh ?) "(Hp & H)".
  rewrite /mapsto_ embed_exist bi.later_exist_except_0; iMod "Hp" as (?) "Hp".
  iDestruct (add_and _ (▷ ⌜∃ ch : memory_chunk, access_mode (typeof e1) = By_value ch⌝) with "Hp") as "(Hp & >(% & %))".
  { apply bi.later_mono; rewrite /mapsto_ mapsto_pure_facts embed_pure; apply bi.pure_mono; tauto. }
  iCombine "Hm Hp" as "Hp"; iDestruct (add_and _ (▷ ⌜∃ m' : Memory.mem, store ch m b (Ptrofs.unsigned o) v2 = Some m'⌝) with "Hp") as "((Hm & Hp) & >(% & %Hstore))".
  { iIntros "(? & ?) !>"; rewrite -embed_pure; iApply mapsto_can_store; eauto; iFrame. }
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iPoseProof (env_match_intro with "Hd") as "#?"; first done.
  iDestruct ("He1" with "[$]") as %He1; iDestruct ("He2" with "[$]") as %He2.
  pose proof (typecheck_var_match_venv _ _ Hty) as Hmatch.
  specialize (He2 Hmatch); inv He2.
  2: { inv H4. }
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iNext; iMod (mapsto_store with "[$]") as "(? & Hp)"; [done..|].
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hp").
  iMod "Hclose" as "_"; iFrame.
  iApply safe_skip; [done..|].
  iFrame; iDestruct "Hk" as "[Hk _]".
  rewrite embed_fupd; iModIntro; iApply (stack_level_embed with "Hd"); by iApply "Hk".
Qed.

Lemma wp_loop: forall E f s1 s2 R,
  ▷ wp E f s1 (loop1_ret_assert (wp E f s2 (loop2_ret_assert (wp E f (Sloop s1 s2) R) R)) R) ⊢ wp E f (Sloop s1 s2) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%% #?".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[//] [Hk] [$] [%] [%]"); [|done..].
  iAssert (guarded E' f k R -∗
    guarded E' f (Kloop2 s1 s2 k) (loop2_ret_assert (wp E f (Sloop s1 s2) R) R))%I as "H2".
  { iIntros "Hk"; iSplit; [|iSplit; [|iSplit]].
    + simpl; iIntros "H".
      by iApply ("H" with "[//] [$]").
    + iDestruct "Hk" as "[$ _]".
    + simpl; iIntros "[]".
    + iDestruct "Hk" as "(_ & _ & _ & $)". }
  iSplit; [|iSplit; [|iSplit]].
  - simpl; iIntros "H" (????) "?%%?"; iApply jsafe_local_step.
    { constructor; auto. }
    iNext; iApply ("H" $! _ (Kloop2 s1 s2 k) with "[//] [Hk] [$] [//] [//] [$]").
    by iApply "H2".
  - iDestruct ("Hk") as "[$ _]".
  - simpl; iIntros "H"; iApply "H"; first done.
    by iApply "H2".
  - iDestruct "Hk" as "(_ & _ & _ & $)".
Qed.

Lemma wp_switch: forall E f e ls R,
  wp_expr ge E f e (λ v, ∃ i, ⌜sem_switch_arg v (typeof e) = Some i⌝ ∧
    ▷ wp E f (seq_of_labeled_statement (select_switch i ls)) (switch_ret_assert R)) ⊢
  wp E f (Sswitch e ls) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "? (%Henv & %) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm [$]") as ">(% & He & Hm & ? & % & % & H)".
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iPoseProof (env_match_intro with "Hd") as "?"; first done.
  iDestruct ("He" with "[$]") as %?.
  pose proof (typecheck_var_match_venv _ _ Hty).
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame; iNext.
  rewrite embed_fupd; iModIntro.
  iApply ("H" with "[//] [Hk] [$]"); try done.
  iSplit; [|iSplit; [|iSplit]].
  - iIntros "[]".
  - iDestruct ("Hk") as "($ & _)".
  - iDestruct ("Hk") as "(_ & _ & $ & _)".
  - iDestruct ("Hk") as "(_ & _ & _ & $)".
Qed.

Lemma stack_matches_continue : forall ρ ve te k, stack_matches' ρ ve te (Some k) →
  stack_matches' ρ ve te (continue_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Lemma wp_continue: forall E f R,
  RA_continue R ⊢ wp E f Scontinue R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%% #?".
  iDestruct "Hk" as "(_ & _ & Hk & _)".
  iSpecialize ("Hk" with "H").
  iSpecialize ("Hk" $! ora with "[$] [%] [//]").
  { by apply stack_matches_continue. }
  destruct (continue_cont k) eqn:Hcont; simpl; last by iApply fupd_jsafe; iMod "Hk" as "[]".
  rename c into k'.
  assert (exists s c, k' = Kseq s c) as (? & ? & Hcase).
  { induction k; inv Hcont; eauto. }
  rewrite Hcase.
  iInduction k as [| | | | |] "IHk" forall (k' Hcont Hcase); try discriminate.
  - iApply jsafe_local_step.
    { constructor. }
    iNext; by iApply "IHk".
  - inv Hcont.
    iApply jsafe_local_step.
    { intros; apply step_skip_or_continue_loop1; auto. }
    iNext; by iApply "Hk".
  - iApply jsafe_local_step.
    { apply step_continue_switch. }
    iNext; by iApply "IHk".
Qed.

Lemma stack_matches_break : forall ρ ve te k, stack_matches' ρ ve te (Some k) →
  stack_matches' ρ ve te (break_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Lemma break_cont_depth : forall k k', break_cont k = Some k' →
  stack_depth k' = stack_depth k.
Proof.
  induction k; simpl; auto; congruence.
Qed.

Lemma wp_break: forall E f R,
  RA_break R ⊢ wp E f Sbreak R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%% #?".
  iDestruct "Hk" as "(_ & Hk & _)".
  iSpecialize ("Hk" with "H").
  iSpecialize ("Hk" $! ora with "[$] [%] [//]").
  { by apply stack_matches_break. }
  destruct (break_cont k) eqn: Hcont; simpl; last by iApply fupd_jsafe; iMod "Hk" as "[]".
  rewrite (break_cont_depth _ _ Hcont); iSpecialize ("Hk" with "[//]").
  destruct c; simpl.
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iNext; iApply ("IHk" with "[%] [%] [$] Hk"). constructor.
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
      iNext; by iApply ("IHk" with "[%] [%] [$] Hk").
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      do 2 iNext; iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      do 2 iNext; iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { intros; apply step_skip_break_switch; auto. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      do 2 iNext; iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iNext; iApply ("IHk" with "[%] [%] [$] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext; iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext; iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext; iApply "Hk".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iNext; iApply ("IHk" with "[%] [%] [$] Hk"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      do 2 iNext; iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      do 2 iNext; iApply "Hk".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      do 2 iNext; iApply "Hk".
  - iStopProof; split => ?; monPred.unseal; iIntros "(? & >[])".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iNext; iApply ("IHk" with "[%] [%] [$] Hk"). constructor.
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
Qed.

(* function calls *)
(* It would be nice to decompose this into repeated wp_expr, but it includes typecasts. *)
Definition wp_exprs E f es ts Φ : assert :=
  ∀ m rho, ⎡mem_auth m⎤ -∗ ⎡env_auth rho⎤ ={E}=∗
         ∃ vs, <affine> (∀ ve te, env_match rho ge ve te -∗
            ⌜match_venv (make_env ve) (fn_vars f) ->
            Clight.eval_exprlist ge ve te m es ts vs (*/\ typeof e = t /\ tc_val t v*)⌝) ∗
         ⎡mem_auth m⎤ ∗ ⎡env_auth rho⎤ ∗ Φ vs.

Lemma wp_exprs_intro : forall E f es ts Φ,
  match es, ts with
  | [], [] => Φ []
  | e :: es', t :: ts' => wp_expr ge E f (Ecast e t) (λ v,
      wp_exprs E f es' ts' (λ lv, Φ (v :: lv)))
  | _, _ => False
  end ⊢ wp_exprs E f es ts Φ.
Proof.
  intros; destruct es, ts; simpl; try iIntros "[]".
  - iIntros "?" (??) "?? !>"; iFrame.
    iIntros "!>" (??) "?%"; iPureIntro; constructor.
  - iIntros "H" (??) "??".
    iMod ("H" with "[$] [$]") as ">(% & He & ? & ? & H)".
    iDestruct ("H" with "[$] [$]") as ">(% & Hes & $ & $ & $)".
    iIntros "!> !>" (??) "#?".
    iDestruct ("He" with "[$]") as %He; iDestruct ("Hes" with "[$]") as %Hes; iPureIntro.
    intros Hmatch; specialize (He Hmatch); inv He.
    econstructor; eauto.
    { inv H. }
Qed.

Lemma wp_exprs_strong_mono : forall E f es ts P1 P2, (∀ v, P1 v ={E}=∗ P2 v) ∗ wp_exprs E f es ts P1 ⊢ wp_exprs E f es ts P2.
Proof.
  intros; rewrite /wp_exprs.
  iIntros "(HP & H)" (??) "??".
  iMod ("H" with "[$] [$]") as (?) "(? & ? & ? & H)".
  iMod ("HP" with "H").
  iIntros "!>"; iExists _; iFrame.
Qed.

Lemma wp_exprs_mono : forall E es ts f P1 P2, (∀ v, P1 v ⊢ |={E}=> P2 v) → wp_exprs E f es ts P1 ⊢ wp_exprs E f es ts P2.
Proof.
  intros; iIntros; iApply wp_exprs_strong_mono; iFrame.
  by iIntros (?) "?"; iApply H.
Qed.

Global Instance wp_exprs_proper E f es ts : Proper (pointwise_relation _ base.equiv ==> base.equiv) (wp_exprs E f es ts).
Proof. solve_proper. Qed.

Lemma wp_exprs_mask_mono : forall E E' f es ts P, E ⊆ E' → wp_exprs E f es ts P ⊢ wp_exprs E' f es ts P.
Proof.
  intros; rewrite /wp_exprs.
  iIntros "H" (??) "??".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[$] [$]") as "H"; iMod "Hclose".
  iApply "H".
Qed.

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
  iIntros "Hm"; iMod (juicy_mem.mapsto_alloc with "Hm") as "($ & H)"; first done; iIntros "!>".
  rewrite /memory_block Ptrofs.unsigned_zero.
  iSplit; first by iPureIntro; lia.
  rewrite Z.sub_0_r memory_block'_eq; [| lia..].
  rewrite /memory_block'_alt if_true; auto.
Qed.

Definition var_sizes_ok (cenv: composite_env) (vars: list (ident*type)) :=
   Forall (fun var : ident * type => @Ctypes.sizeof cenv (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type): assert :=
  ⌜(Ctypes.sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  ∃ b, lvar (fst idt) (snd idt) b ∗ ⎡memory_block sh (Ctypes.sizeof (snd idt)) (Vptr b Ptrofs.zero)⎤.

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) (lv: list val) : assert :=
  ([∗ list] idt ∈ fn_vars f, var_block' Share.top cenv idt) ∗
  ([∗ list] idt;v ∈ (fn_params f ++ fn_temps f);lv, temp (fst idt) v).

Definition stackframe_of1 f lb lv : assert := assert_of (λ n,
  <affine> ⌜length lv = (length (fn_params f) + length (fn_temps f))%nat⌝ ∗
  let ve := list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))) in
  let te := list_to_map (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv) in
  stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size ve + size te)))%Qp 1%Qp ve te) ∗
  ([∗ list] idt;b ∈ fn_vars f;lb, ⎡memory_block Share.top (@Ctypes.sizeof (genv_cenv ge) (snd idt)) (Vptr b Ptrofs.zero)⎤).

Definition stack_size f := (length (fn_vars f) + length (fn_params f) + length (fn_temps f))%nat.

Definition stack_frac f := (/ pos_to_Qp (Pos.of_nat (1 + stack_size f)))%Qp.

Definition stack_retainer f := assert_of (λ n, stack_frag n (stack_frac f) (stack_frac f) ∅ ∅).

Lemma monPred_at_big_sepL2 : forall {I : biIndex} {PROP : bi} {A B} (Φ : A → B → monPred I PROP) (l1 : list A) (l2 : list B) n,
  (([∗ list] a1;a2 ∈ l1;l2, Φ a1 a2) n) ⊣⊢ ([∗ list] a1;a2 ∈ l1;l2, Φ a1 a2 n).
Proof.
  induction l1; destruct l2; simpl; intros; monPred.unseal; try done.
  rewrite IHl1 //.
Qed.

Lemma pure_equiv : forall {PROP : bi} (P Q : PROP) R, (P ⊢ ⌜R⌝) → (Q ⊢ ⌜R⌝) → (R → (P ⊣⊢ Q)) → (P ⊣⊢ Q).
Proof.
  intros; iSplit; iIntros "H"; iAssert ⌜R⌝ as %?.
  - by iApply H.
  - by rewrite H1.
  - by iApply H0.
  - by rewrite -H1.
Qed.

Lemma stackframe_of_eq1 : forall f lb lv,
  list_norepet (map fst (fn_vars f)) →
  list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) →
  stackframe_of1 f lb lv ⊢ stack_retainer f ∗
  ([∗ list] '(i,t);b ∈ fn_vars f;lb, lvar i t b) ∗
  ([∗ list] idt;v ∈ (fn_params f ++ fn_temps f);lv, temp (fst idt) v) ∗
  ([∗ list] idt;b ∈ fn_vars f;lb, ⎡memory_block Share.top (@Ctypes.sizeof (genv_cenv ge) (snd idt)) (Vptr b Ptrofs.zero)⎤).
Proof.
  intros.
  iIntros "(? & Hblocks)".
  iDestruct (big_sepL2_length with "Hblocks") as %?; iFrame "Hblocks".
  iStopProof; split => n; monPred.unseal; rewrite !monPred_at_big_sepL2 /=.
  erewrite big_sepL2_proper'; [|try done..]. setoid_rewrite lvars_equiv; [|done..].
  2: { by intros ? (?, ?) ?. }
  iIntros "(%Hlv & H)".
  erewrite big_sepL2_proper'; [|try done..]. setoid_rewrite <-(big_sepL2_fmap_l fst).
  setoid_rewrite temps_equiv.
  4: { intros ? (?, ?) ?; simpl; done. }
  assert (length (map fst (fn_vars f)) = length (zip lb (map snd (fn_vars f)))) as Heq1.
  { rewrite length_zip_with_l_eq map_length //. }
  assert (length (map fst (fn_params f) ++ map fst (fn_temps f)) = length lv) as Heq2.
  { rewrite !app_length !map_length Hlv //. }
  assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv).*1).
  { rewrite -norepet_NoDup fst_zip //. by rewrite Heq2. }
  assert (NoDup (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))).*1).
  { rewrite -norepet_NoDup fst_zip //. by rewrite Heq1. }
  rewrite !map_size_list_to_map //.
  rewrite !length_zip_with_l_eq // map_length // app_length !map_length.
  rewrite Nat.add_assoc; change (Qp.inv _) with (stack_frac f).
  destruct (decide (stack_size f = 0%nat)).
  - unfold stack_frac, stack_size in *.
    if_tac; last by lia.
    rewrite app_length; if_tac; last by lia.
    destruct (fn_vars f); simpl in *; last done.
    destruct (fn_params f); simpl in *; last done.
    destruct (fn_temps f); simpl in *; last done.
    rewrite Qp.inv_1 !bi.sep_emp; by iFrame.
  - rewrite /stack_frac Nat2Pos.inj_succ // Pplus_one_succ_l -pos_to_Qp_add.
    set (q := (1 + _)%Qp).
    rewrite -(Qp.mul_inv_r q).
    destruct (q - 1)%Qp eqn: Hq.
    apply Qp.sub_Some in Hq; rewrite {2} Hq Qp.mul_add_distr_r -frac_op.
    rewrite -{1}(map_empty_union (list_to_map _)) -{1}(map_empty_union (list_to_map (zip (_ ++ _) _))) stack_frag_split.
    rewrite Qp.mul_1_l; iStopProof; f_equiv.
    unfold q in Hq; apply Qp.add_inj_r in Hq; subst.
    if_tac; if_tac.
    + rewrite /stack_size in n0; rewrite -> app_length in *; lia.
    + destruct (fn_vars f) eqn: Hvars; last done.
      rewrite fmap_app bi.emp_sep -(bi.exist_intro _) /=; f_equiv; last done.
      rewrite /stack_size Hvars app_length; done.
    + rewrite -> app_length in *.
      destruct (fn_params f) eqn: Hparams; last done.
      destruct (fn_temps f) eqn: Htemps; last done.
      rewrite bi.sep_emp -(bi.exist_intro _) /=; f_equiv.
      rewrite /stack_size Hparams Htemps /= !Nat.add_0_r; done.
    + rewrite -> app_length in *.
      rewrite /stack_size -Nat.add_assoc Nat2Pos.inj_add // -pos_to_Qp_add Qp.mul_add_distr_r -frac_op.
      iIntros "H"; rewrite bi.sep_exist_l; iExists _; rewrite bi.sep_exist_r; iExists _.
      iApply stack_frag_split.
      { apply map_disjoint_empty_r. }
      { apply map_disjoint_empty_l. }
      rewrite right_id left_id fmap_app //.
    + apply map_disjoint_empty_l.
    + apply map_disjoint_empty_l.
    + apply Qp.sub_None, Qp.not_add_le_l in Hq; done.
  - rewrite fmap_app !app_length !length_fmap Hlv //.
  - rewrite fmap_app //.
Qed.

Lemma var_blocks_eq: forall lv,
  ([∗ list] idt ∈ lv, var_block' Share.top ge idt) ⊣⊢
  ∃ lb, ([∗ list] '(i, t);b ∈ lv;lb, lvar i t b) ∗
        ([∗ list] idt;b ∈ lv;lb, ⎡ memory_block Share.top (@Ctypes.sizeof ge idt.2) (Vptr b Ptrofs.zero) ⎤).
Proof.
  induction lv as [|(i, t) lv IH]; simpl.
  - iSplit.
    + iIntros "_"; iExists []; simpl; auto.
    + iIntros "(% & ?)"; destruct lb; simpl; auto.
  - rewrite IH /var_block'; iSplit.
    + iIntros "((% & % & ? & ?) & % & ? & ?)"; iExists (b :: lb); simpl; iFrame.
    + iIntros "(% & H)"; destruct lb; simpl; first iDestruct "H" as "([] & ?)".
      iDestruct "H" as "(($ & $) & (% & $) & $)".
      iPureIntro; rewrite !Ptrofs.unsigned_zero !Z.add_0_l in H |- *.
      split3; auto; rewrite /Ptrofs.max_unsigned; lia.
Qed.

Lemma stackframe_of_eq1' : forall f lb lv,
  list_norepet (map fst (fn_vars f)) →
  list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) →
  stackframe_of1 f lb lv ⊢
  stack_retainer f ∗ stackframe_of' (genv_cenv ge) f lv.
Proof.
  intros; rewrite stackframe_of_eq1 //; iIntros "($ & Hvars & $ & Hblocks)".
  rewrite var_blocks_eq; iFrame.
Qed.

Lemma stackframe_of_eq' : forall f lv, list_norepet (map fst (fn_vars f)) →
  list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) →
  stack_retainer f ∗ stackframe_of' (genv_cenv ge) f lv ⊢
  ∃ lb, stackframe_of1 f lb lv.
Proof.
  intros; rewrite /stackframe_of' /stackframe_of1 var_blocks_eq.
  iIntros "(Hret & (% & Hvars & Hblocks) & Htemps)"; iExists lb; iFrame "Hblocks".
  iDestruct (big_sepL2_length with "Hvars") as %Hlb.
  iDestruct (big_sepL2_length with "Htemps") as %Hparams.
  iStopProof; split => n; simpl; monPred.unseal; rewrite !monPred_at_big_sepL2.
  erewrite big_sepL2_proper'; [|try done..]. setoid_rewrite lvars_equiv; [|done..].
  2: { by intros ? (?, ?) ?. }
  erewrite big_sepL2_proper'; [|try done..]. setoid_rewrite <-(big_sepL2_fmap_l fst).
  setoid_rewrite temps_equiv.
  4: { intros ? (?, ?) ?; simpl; done. }
  assert (length (map fst (fn_vars f)) = length (zip lb (map snd (fn_vars f)))) as Heq1.
  { rewrite length_zip_with_l_eq map_length //. }
  rewrite app_length in Hparams.
  assert (length (map fst (fn_params f) ++ map fst (fn_temps f)) = length lv) as Heq2.
  { rewrite -map_app !map_length app_length //. }
  assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv).*1).
  { rewrite -norepet_NoDup fst_zip //. by rewrite Heq2. }
  assert (NoDup (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))).*1).
  { rewrite -norepet_NoDup fst_zip //. by rewrite Heq1. }
  iIntros "(Hret & Hvars & Htemps)"; iSplit; first done; iAssert (stack_frag n (stack_frac f) (pos_to_Qp (Pos.of_nat (1 + length (fn_vars f))%nat) * stack_frac f)%Qp (list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f))))) ∅)
    with "[Hret Hvars]" as "Hvars".
  - destruct (decide _).
    { rewrite e.
      destruct (fn_vars f); last done.
      rewrite Qp.mul_1_l; iFrame. }
    iDestruct "Hvars" as (q) "Hvars".
    iDestruct (stack_frag_join with "[$Hret $Hvars]") as ((<- & _)) "Hvars".
    rewrite !left_id Nat2Pos.inj_succ // Pplus_one_succ_l -pos_to_Qp_add Qp.mul_add_distr_r Qp.mul_1_l; done.
  - rewrite !map_size_list_to_map //.
    rewrite !length_zip_with_l_eq // map_length // app_length !map_length.
    rewrite Nat.add_assoc; change (Qp.inv _) with (stack_frac f).
    destruct (decide _).
    { rewrite app_length in e.
      rewrite {2}/stack_frac /stack_size.
      destruct (fn_params f); last done.
      destruct (fn_temps f); last done; simpl.
      rewrite !Nat.add_0_r Qp.mul_inv_r; iFrame. }
    iDestruct "Htemps" as (q) "Htemps".
    iDestruct (stack_frag_join with "[$Hvars $Htemps]") as ((<- & _)) "Hvars".
    rewrite -> app_length in *.
    rewrite left_id right_id -Qp.mul_add_distr_r pos_to_Qp_add -Nat2Pos.inj_add // -Nat.add_assoc (Nat.add_assoc (length _)) Qp.mul_inv_r.
    rewrite fmap_app; done.
  - rewrite length_fmap //.
  - rewrite fmap_app //.
Qed.

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
      (snd ρ !! n = None)%stdpp ->
      mem_auth m ∗ env_auth ρ ⊢ |==> ∃ m' ve lb, ⌜Clight.alloc_variables ge empty_env m (fn_vars f) ve m' ∧
        typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f))⌝ ∧
        mem_auth m' ∗ env_auth (alloc_vars (make_env ve) (make_env te) n ρ) ∗
        stackframe_of1 f lb (args ++ repeat Vundef (length (fn_temps f))) n.
Proof.
  intros.
  cut (mem_auth m ∗ env_auth ρ ⊢ |==> ∃ (m' : Memory.mem) (ve : env) lb,
    ⌜(∀i, sub_option (empty_env !! i)%maps (ve !! i)%maps) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ mem_auth m' ∗ env_auth (alloc_vars (make_env ve) (make_env te) n ρ) ∗ stackframe_of1 f lb (args ++ repeat Vundef (length (fn_temps f))) n).
  { intros Hgen; rewrite Hgen; iIntros ">(% & % & % & (% & %) & ?) !>".
    iExists _, _; iFrame; iPureIntro; split3; split; eauto.
    eapply alloc_vars_typecheck_environ; eauto. }
  cut (mem_auth m ⊢ |==> ∃ (m' : Memory.mem) ve (lb : list Values.block),
    ⌜length (fn_vars f) = length lb ∧ make_env ve = list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))) ∪ make_env empty_env ∧ (∀i, sub_option (empty_env !! i)%maps (ve !! i)%maps) ∧ alloc_variables ge empty_env m (fn_vars f) ve m'⌝
    ∧ mem_auth m' ∗ [∗ list] idt;b∈fn_vars f;lb, memory_block Share.top (@Ctypes.sizeof (genv_cenv ge) (snd idt)) (Vptr b Ptrofs.zero)).
  { intros ->; iIntros "(>(% & % & % & (%Hlen & %Hve & % & %) & ? & Hblocks) & Hr)".
    rewrite right_id in Hve.
    iExists m', ve, lb; iFrame.
    pose proof (bind_parameter_temps_inv _ _ _ _ H1) as Hargs.
    rewrite Hve; iMod (env_alloc with "Hr") as "($ & Hvars)"; try done.
    iModIntro; iSplit; first done.
    rewrite /stackframe_of1; monPred.unseal; rewrite !monPred_at_big_sepL2.
    erewrite bind_temps_map; try apply H1; try done.
    + iFrame. iPureIntro; rewrite app_length repeat_length Hargs //.
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
    destruct (Mem.alloc m 0 (@Ctypes.sizeof (genv_cenv ge) ty)) as (m', b) eqn: Halloc.
    inv COMPLETE; inv Hsize; inv H.
    iMod (alloc_block with "Hm") as "(Hm & block)"; first done.
    { pose proof @Ctypes.sizeof_pos (genv_cenv ge) ty; unfold sizeof, Ptrofs.max_unsigned in *; simpl in *; lia. }
    unshelve iMod (IHvars _ _ (Maps.PTree.set id (b,ty) ve0) with "Hm") as (??? (? & Hve & Hsub & ?)) "(Hm & ?)"; try done.
    { intros i; destruct (eq_dec i id); first by subst.
      rewrite PTree.gso //; intros; apply Hout; simpl; auto. }
    iIntros "!>"; iExists _, _, (b :: lb); simpl; iFrame.
    iPureIntro; split; last done; split; first auto; split3.
    + setoid_rewrite Hve; rewrite make_env_set -insert_union_l -insert_union_r //.
      apply not_elem_of_list_to_map_1.
      rewrite fst_zip.
      rewrite elem_of_list_In //.
      { rewrite length_zip_with_l_eq; rewrite map_length; lia. }
    + intros i; specialize (Hsub i).
      destruct (eq_dec i id); last by rewrite Maps.PTree.gso in Hsub.
      subst; rewrite Hout //; simpl; auto.
    + econstructor; eauto.
Qed.

Lemma stackframe_blocks_freeable : forall lv lb ve,
  length lv = length lb -> list_norepet (map fst lv) ->
  list_to_map (zip (map fst lv) (zip lb (map snd lv))) = make_env ve ->
  ([∗ list] idt;b ∈ lv;lb, ⌜Ptrofs.unsigned Ptrofs.zero + @Ctypes.sizeof (genv_cenv ge) idt.2 < Ptrofs.modulus⌝
     ∧ memory_block' Share.top (Z.to_nat (@Ctypes.sizeof (genv_cenv ge) idt.2)) b (Ptrofs.unsigned Ptrofs.zero)) ⊢
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
        pose proof (@Ctypes.sizeof_pos (genv_cenv ge) t); lia. }
    unfold memory_block'_alt.
    rewrite -> if_true by apply readable_share_top.
    rewrite /= Z.sub_0_r Ptrofs.unsigned_zero; iSplitL "H".
    { iApply (big_sepL_mono with "H"); intros.
      iIntros "$". }
    rewrite -Hrem; iApply IHlv; try done.
    apply map_eq; intros k; rewrite make_env_spec; destruct (eq_dec k i).
    + subst; rewrite PTree.grs.
      apply not_elem_of_list_to_map_1.
      rewrite fst_zip.
      rewrite elem_of_list_In //.
      { rewrite length_zip_with_l_eq; rewrite map_length; lia. }
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
  iIntros "(Hm & Hρ & (%Hlen & Hfrag) & Hblocks)".
  iDestruct (big_sepL2_length with "Hblocks") as %?.
  iDestruct (stack_frag_e_1 with "[$Hρ $Hfrag]") as %(Hve & _).
  apply env_matches_make_ve in MATCH; rewrite MATCH in Hve.
  iMod (env_dealloc with "[$Hρ $Hfrag]") as "$".
  rewrite stackframe_blocks_freeable //.
  forget (blocks_of_env ge ve) as el.
  iInduction el as [|] "IHel" forall (m); first eauto.
  destruct a as ((id, b), t); simpl.
  iDestruct "Hblocks" as "(H & Hblocks)".
  iDestruct (juicy_mem_lemmas.VALspec_range_can_free with "[$Hm $H]") as %(m' & Hfree).
  rewrite /= Zplus_minus in Hfree; rewrite Hfree.
  iMod (juicy_mem_lemmas.VALspec_range_free with "[$Hm $H]") as "Hm"; first done.
  iApply ("IHel" with "Hm Hblocks").
Qed.

Definition up1 (P : assert) : assert := assert_of (λ n, P (S n)).
Definition down1 (P : assert) : assert := assert_of (λ n, match n with | S n' => P n' | O => False end).

Global Instance up1_nonexpansive : NonExpansive up1.
Proof. split => ? /=. apply H. Qed.

Global Instance down1_nonexpansive : NonExpansive down1.
Proof. split => l /=.
  destruct l; first done. apply H. Qed.

Global Instance up1_proper : Proper (equiv ==> equiv) up1.
Proof. split => ? /=. apply H. Qed.

Global Instance down1_proper : Proper (equiv ==> equiv) down1.
Proof. split => l /=.
  destruct l; first done. apply H. Qed.

Lemma up1_mono : forall P Q, (P ⊢ Q) -> up1 P ⊢ up1 Q.
Proof. split => n; apply H. Qed.

Lemma down1_mono : forall P Q, (P ⊢ Q) -> down1 P ⊢ down1 Q.
Proof. split => n /=. destruct n; first done. apply H. Qed.

Lemma up1_plain : forall P, Plain P -> Absorbing P -> up1 P ⊣⊢ P.
Proof.
  intros.
  rewrite -(plain_plainly P).
  split => n /=; rewrite !monPred_at_plainly //.
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

Lemma guarded_frame_ret0 : forall E f k ty (Q : option val → assert) R
  (Hret : ∀ ve te, cont_to_state f ve te k = Some (State f (Sreturn None) k ve te))
  (Hk : call_cont k = k),
  (∀ ret, wp_expr_opt E f (option_map (λ e, Ecast e f.(fn_return)) ret) (λ vl, (⌜match vl with Some v => tc_val ty v | None => ty = Tvoid end⌝ ∧ Q vl) ∗ R) -∗
        assert_safe E f (Some (Kseq (Sreturn ret) k))) ⊢
  guarded E f k (frame_ret_assert (function_body_ret_assert ty Q) R).
Proof.
  intros.
  iIntros "H"; rewrite /guarded /= /bind_ret.
  iSplit.
  - iSpecialize ("H" $! None); iStopProof; f_equiv.
    rewrite /assert_safe; do 12 f_equiv.
    rewrite Hret //.
  - repeat (iSplit; first by iIntros "([] & ?)").
    rewrite Hk //.
Qed.

Lemma guarded_frame_ret : forall E f i f0 ve te k ty (Q : option val → assert) R,
  (∀ ret, wp_expr_opt E f (option_map (λ e, Ecast e f.(fn_return)) ret) (λ vl, (⌜match vl with Some v => tc_val ty v | None => ty = Tvoid end⌝ ∧ Q vl) ∗ R) -∗
        assert_safe E f (Some (Kseq (Sreturn ret) (Kcall i f0 ve te k)))) ⊢
  guarded E f (Kcall i f0 ve te k) (frame_ret_assert (function_body_ret_assert ty Q) R).
Proof.
  intros; by apply (guarded_frame_ret0 _ _ (Kcall _ _ _ _ _)).
Qed.

Lemma eval_exprlist_length : forall ge ve te m es ts vs,
  Clight.eval_exprlist ge ve te m es ts vs -> length es = length ts /\ length vs = length ts.
Proof.
  induction 1; auto; simpl.
  by destruct IHeval_exprlist as [-> ->].
Qed.

Definition set_temp_opt ret vl R :=
  match ret with
  | Some id => (∃ v0, temp id v0) ∗ (temp id (val_lemmas.force_val vl) -∗ R)
  | _ => R
  end.

(* Under most circumstances stack_retainer can be framed out, but we might need it
   to do whole-stackframe reasoning. *)
Definition internal_call_assert E f args ret R := up1 (stack_retainer f -∗ stackframe_of' ge f (args  ++ repeat Vundef (length f.(fn_temps))) -∗
  ▷ wp E f f.(fn_body) (frame_ret_assert (function_body_ret_assert f.(fn_return)
      (λ vl, down1 (set_temp_opt ret vl R)))
      (stack_retainer f ∗ ∃ vs, stackframe_of' ge f vs)))%I.

Lemma internal_call_assert_mask_mono : forall E1 E2 f args ret R, E1 ⊆ E2 →
  internal_call_assert E1 f args ret R ⊢ internal_call_assert E2 f args ret R.
Proof.
  unfold internal_call_assert; intros; apply up1_mono.
  do 3 f_equiv.
  by apply wp_mask_mono.
Qed.

(* This property usually won't be proven directly by the caller, but rather to
   prove a separation logic spec for each specific external function. *)
Definition external_call_assert E f vs i R :=
  |={E}=> ∀ m z, ⎡state_interp m z⎤ -∗ ∃ x, ⌜ef_inline f = false ∧
      ext_spec_pre OK_spec f x (genv_symb_injective ge) (map proj_xtype (sig_args (ef_sig f))) vs z m⌝ ∧
      ▷ ∀ ret m' z', ⌜Val.has_type_list vs (map proj_xtype (sig_args (ef_sig f)))
                   ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig f))⌝
                  → ⌜ext_spec_post OK_spec f x (genv_symb_injective ge) (sig_res (ef_sig f)) ret z' m'⌝ →
              |={E}=> ⎡state_interp m' z'⎤ ∗ set_temp_opt i ret R.

Lemma external_call_assert_mask_mono : forall E1 E2 f args ret R, E1 ⊆ E2 →
  external_call_assert E1 f args ret R ⊢ external_call_assert E2 f args ret R.
Proof.
  unfold external_call_assert; intros.
  rewrite -(fupd_mask_mono _ _ _ H); do 18 f_equiv.
  by apply fupd_mask_mono.
Qed.

Definition call_assert E f args ret R :=
  match f with
  | Internal f => internal_call_assert E f args ret R
  | External f tys retty cc => external_call_assert E f args ret R
  end.

Lemma call_assert_mask_mono : forall E1 E2 f args ret R, E1 ⊆ E2 →
  call_assert E1 f args ret R ⊢ call_assert E2 f args ret R.
Proof.
  unfold call_assert; intros.
  destruct f; [apply internal_call_assert_mask_mono | apply external_call_assert_mask_mono]; done.
Qed.

Definition fundef_wf f (vs : list val) : Prop := match f with
  | Internal f => Forall (λ it : ident * type, complete_type ge it.2 = true) (fn_vars f) /\
      list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) /\
      list_norepet (map fst (fn_vars f)) /\
      var_sizes_ok ge (fn_vars f) /\ length vs = length (fn_params f)
  | _ => True end.

Lemma call_safe : forall E f0 k ve te ρ ora f vs i R
  (Hstack : stack_matches' ρ ve te (Some k))
  (Htc : typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f0)))
  (Hf : fundef_wf f vs),
⊢ stack_level (stack_depth k) -∗ guarded E f0 k R -∗ ⎡ env_auth ρ ⎤ -∗
  call_assert E f vs i (RA_normal R) -∗
  ⎡ |={E}=> jsafeN E ora (Callstate f vs (Kcall i f0 ve te k)) ⎤.
Proof.
  intros; iIntros "#Hd Hk Hr H".
  destruct f; simpl.
  - (* internal *)
    iApply jsafe_step.
    rewrite /jstep_ex.
    rewrite embed_fupd; iIntros "!>" (?) "(Hm & Ho)".
    destruct Hf as (? & ? & ? & ? & ?).
    destruct (build_call_temp_env f vs) as (le & ?); first done.
    destruct Hstack as (Hmatch & Hstack & Htop).
    iMod (alloc_stackframe _ _ (S (stack_depth k)) with "[$Hm $Hr]") as (m' ve' lb (? & ?)) "(Hm & Hr & Hstack)"; [try done..|].
    { auto. }
    rewrite embed_fupd; iIntros "!>".
    iExists _, _; iSplit.
    { iPureIntro; econstructor; eauto.
      econstructor; eauto.
      * eapply list_norepet_append_left; eauto.
      * apply list_norepet_append_inv; auto. }
    iFrame.
    iDestruct "Hd" as "-#?"; iClear "#".
    iStopProof; split => ?; rewrite /internal_call_assert /wp /assert_safe /stack_level; monPred.unseal; rewrite !monPred_at_affinely.
    iIntros "(Hk & H & Hr & Hstack & %Hn)"; inv Hn.
    iPoseProof (monPred_in_entails with "Hstack") as "Hstack"; first by apply stackframe_of_eq1'.
    rewrite monPred_at_sep; iDestruct "Hstack" as "(? & ?)".
    iApply ("H" with "[//] [$] [//] [$] [//] [//] [//] [Hk] [//] [$Hr //] [//] [%] [//] [//] [//]").
    2: { by apply (stack_matches'_alloc _ _ _ _ _ _ (fn_body f) i f). }
    2: { by rewrite monPred_at_affinely. }
    rewrite -guarded_frame_ret /=.
    rewrite /guarded {5}/assert_safe /stack_level; monPred.unseal.
    iIntros "!>" (ret ? [=]) "Hret".
    iIntros (??????) "Hr %% (%Henv' & %Hstack') %% %Hty' %% _".
    unfold sqsubseteq in *; subst.
    iApply jsafe_step; rewrite /jstep_ex.
    iIntros (?) "(Hm & Ho)".
    unfold set_temp_opt; destruct ret; simpl.
    + rewrite /wp_expr; monPred.unseal.
      iMod ("Hret" with "[//] [$] [//] [$]") as ">(% & Hret & ? & ? & (% & H) & (Hstack & %vs' & Hstack'))".
      iPoseProof (monPred_in_entails with "[Hstack Hstack']") as "Hstack"; first by apply (stackframe_of_eq' f vs').
      { rewrite monPred_at_sep; iFrame. }
      rewrite monPred_at_exist; iDestruct "Hstack" as (?) "Hstack".
      iMod (free_stackframe with "[$]") as (m'' ?) "(Hm & ?)"; [done..|].
      rewrite monPred_at_affinely; iDestruct "Hret" as %Hret.
      pose proof (typecheck_var_match_venv _ _ Hty') as Hmatch'.
      specialize (Hret _ _ _ eq_refl Henv' Hmatch'); inv Hret.
      2: { inv H9. }
      iIntros "!>".
      iExists _, _; iSplit.
      { iPureIntro; econstructor; eauto. }
      iFrame.
      iNext.
      iApply jsafe_local_step.
      { intros; constructor. }
      iIntros "!> !>"; simpl.
      destruct i; simpl.
      * iDestruct "H" as "((% & Hi) & H)".
        iDestruct (temp_e with "[$]") as %Hi.
        iMod (temp_update with "[$]") as "(? & ?)".
        iDestruct ("H" with "[//] [$]") as "H".
        iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
        { done. }
        apply (stack_matches'_set _ _ _ (Some k)); first by eapply stack_matches'_dealloc with (i := Some i)(f := f); split; eauto.
        rewrite /env_to_environ in Hi; simpl in *.
        destruct (delete _ _ !! _)%stdpp; done.
      * iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
        { done. }
        eapply stack_matches'_dealloc with (i := None)(f := f); split; eauto.
    + monPred.unseal.
      iDestruct "Hret" as "((%Hvoid & H) & (Hstack & %vs' & Hstack'))".
      iPoseProof (monPred_in_entails with "[Hstack Hstack']") as "Hstack"; first by apply (stackframe_of_eq' f vs').
      { rewrite monPred_at_sep; iFrame. }
      rewrite monPred_at_exist; iDestruct "Hstack" as (?) "Hstack".
      iMod (free_stackframe with "[$]") as (m'' ?) "(Hm & ?)"; [done..|].
      iIntros "!>".
      iExists _, _; iSplit.
      { iPureIntro; econstructor; eauto. }
      iFrame.
      iNext.
      iApply jsafe_local_step.
      { intros; constructor. }
      iIntros "!> !>"; simpl.
      destruct i; simpl.
      * iDestruct "H" as "((% & Hi) & H)".
        iDestruct (temp_e with "[$]") as %Hi.
        iMod (temp_update with "[$]") as "(? & ?)".
        iDestruct ("H" with "[//] [$]") as "H".
        iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
        { done. }
        apply (stack_matches'_set _ _ _ (Some k)); first by eapply stack_matches'_dealloc with (i := Some i)(f := f); split; eauto.
        rewrite /env_to_environ in Hi; simpl in *.
        destruct (delete _ _ !! _)%stdpp; done.
      * iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
        { done. }
        eapply stack_matches'_dealloc with (i := None)(f := f); split; eauto.
  - (* external *)
  iMod "H".
  rewrite /jsafeN jsafe_unfold /jsafe_pre.
  rewrite !embed_fupd; iIntros "!> !>" (?) "Hm".
  iDestruct ("H" with "Hm") as (? (Hinline & ?)) "H".
  iRight; iRight.
  iExists _, _, _; iSplit.
  { iPureIntro; rewrite /= Hinline; eauto. }
  iNext; iIntros (?????).
  rewrite embed_fupd.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "[//] [//]") as "($ & H)".
  iMod "Hclose" as "_"; iIntros "!>".
  iExists _; iSplit; first done.
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  destruct i; simpl.
  + iDestruct "H" as "((% & Hi) & H)".
    iPoseProof (stack_level_embed with "Hd Hi") as "Hi".
    iDestruct (temp_e with "[$]") as %Hi.
    rewrite -fupd_jsafe.
    iMod (temp_update with "[$]") as "(? & ?)".
    iPoseProof (stack_level_elim with "Hd [$]") as "Hi".
    iSpecialize ("H" with "Hi").
    iPoseProof (stack_level_embed with "Hd H") as "H".
    iPoseProof (stack_level_embed with "Hd Hk") as "Hk".
    iModIntro.
    rewrite /guarded; monPred.unseal.
    iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
    * done.
    * apply (stack_matches'_set _ _ _ (Some k)); first done.
      rewrite /env_to_environ in Hi; simpl in *.
      destruct (ρ.2 !! _)%stdpp; done.
  + by iApply safe_skip; last by (iFrame; iApply (stack_level_embed with "Hd"); iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
Qed.

Lemma wp_call: forall E f0 i e es tys retty cc R,
  classify_fun (typeof e) = fun_case_f tys retty cc →
  wp_expr ge E f0 e (λ v,
    wp_exprs E f0 es tys
    (λ vs, ∃ f, <affine> ⌜exists b, v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some f /\
       type_of_fundef f = Tfunction tys retty cc /\ fundef_wf f vs⌝ ∗
       ▷ call_assert E f vs i (RA_normal R))) ⊢
  wp E f0 (Scall i e es) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "Hr (%Hmatch & %Hstack & %Htop) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr /wp_exprs /=.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm Hr") as ">(% & He & Hm & Hr & H)"; [done..|].
  iMod ("H" with "Hm Hr") as (vs) "(Hes & Hm & Hr & H)"; [done..|].
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iPoseProof (env_match_intro with "Hd") as "#?"; first done.
  iDestruct ("He" with "[$]") as %He; iDestruct ("Hes" with "[$]") as %Hes.
  pose proof (typecheck_var_match_venv _ _ Hty).
  assert (length vs = length tys).
  { apply eval_exprlist_length in Hes as (_ & Hlen); done. }
  iDestruct ("H") as (? (? & -> & ? & ? & ?)) "H".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply (call_safe with "Hd Hk Hr [H]"); [done..|].
  by iApply call_assert_mask_mono.
Qed.

(* not sure we'll ever use this *)
Lemma wp_extcall_inline: forall E f0 i e es tys retty cc R,
  classify_fun (typeof e) = fun_case_f tys retty cc →
  wp_expr ge E f0 e (λ v, ∃ f, ⌜exists b, v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some (External f tys retty cc) /\
    ef_inline f && ef_deterministic f = true⌝ ∧
    wp_exprs E f0 es tys (λ vs,
       ∀ m, ⎡mem_auth m⎤ ={E}=∗ ∃ t ret m', ⌜Events.external_call f ge vs m t ret m'⌝ ∧
         ▷ |={E}=> ⎡mem_auth m'⎤ ∗ set_temp_opt i (Some ret) (RA_normal R))) ⊢
  wp E f0 (Scall i e es) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "Hr (%Hmatch & %Hstack & %Htop) %Hty #Hd".
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr /wp_exprs /=.
  iIntros (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm Hr") as ">(% & He & Hm & Hr & %f & %Hb & H)"; [done..|].
  destruct Hb as (b & -> & Hb & ?).
  iMod ("H" with "Hm Hr") as (vs) "(Hes & Hm & Hr & H)"; [done..|].
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iPoseProof (env_match_intro with "Hd") as "#?"; first done.
  iDestruct ("He" with "[$]") as %He; iDestruct ("Hes" with "[$]") as %Hes.
  pose proof (typecheck_var_match_venv _ _ Hty).
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iFrame.
  iNext.
  iApply jsafe_step.
  rewrite /jstep_ex.
  rewrite embed_fupd; iIntros "!>" (?) "(Hm & Ho)".
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod ("H" with "Hm") as (????) "H".
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto. }
  iNext.
  iMod (fupd_mask_subseteq E) as "Hclose"; first done.
  iMod "H" as "($ & H)"; iFrame.
  iMod "Hclose" as "_"; rewrite embed_fupd; iIntros "!>".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  destruct i; simpl.
  + iDestruct "H" as "((% & Hi) & H)".
    iPoseProof (stack_level_embed with "Hd Hi") as "Hi".
    iDestruct (temp_e with "[$]") as %Hi.
    rewrite -fupd_jsafe.
    iMod (temp_update with "[$]") as "(? & ?)".
    iPoseProof (stack_level_elim with "Hd [$]") as "Hi".
    iSpecialize ("H" with "Hi").
    iPoseProof (stack_level_embed with "Hd H") as "H".
    iPoseProof (stack_level_embed with "Hd Hk") as "Hk".
    iModIntro.
    rewrite /guarded; monPred.unseal.
    iApply safe_skip; last by (iFrame; iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
    * done.
    * apply (stack_matches'_set _ _ _ (Some k)); first by split.
      rewrite /env_to_environ in Hi; simpl in *.
      destruct (ρ.2 !! _)%stdpp; done.
  + by iApply safe_skip; last by (iFrame; iApply (stack_level_embed with "Hd"); iDestruct "Hk" as "(Hk & _)"; iApply "Hk").
Qed.

(* should be unifiable with the regular call, but the handling of the initial
   stack is a bit different *)
Definition initial_internal_call_assert E f args R : assert := (stack_retainer f -∗ stackframe_of' ge f (args  ++ repeat Vundef (length f.(fn_temps))) -∗
  ▷ wp E f f.(fn_body) (frame_ret_assert (function_body_ret_assert f.(fn_return)
      (λ vl, R))
      (stack_retainer f ∗ ∃ vs, stackframe_of' ge f vs)))%I.

Definition initial_call_assert E f args R :=
  match f with
  | Internal f => initial_internal_call_assert E f args R
  | External f tys retty cc => external_call_assert E f args None R
  end.

Lemma call_safe_stop : forall E ρ ora f vs (R : assert)
  (Hge : ∀ i : ident, Genv.find_symbol ge i = (ρ.1 !! i)%stdpp)
  (Hstack : ∀ i : nat, (ρ.2 !! i)%stdpp = None)
  (Hexit : ∀ m ora, state_interp m ora -∗ R O -∗ ⌜∃ i, ext_spec_exit OK_spec (Some (Vint i)) ora m⌝)
  (Hf : fundef_wf f vs),
⊢ stack_level O -∗ ⎡ env_auth ρ ⎤ -∗
  initial_call_assert E f vs R -∗
  ⎡ jsafeN E ora (Callstate f vs Kstop) ⎤.
Proof.
  intros; iIntros "#Hd Hr H".
  destruct f; simpl.
  - (* internal *)
    iApply jsafe_step.
    rewrite /jstep_ex.
    iIntros (?) "(Hm & Ho)".
    destruct Hf as (? & ? & ? & ? & ?).
    destruct (build_call_temp_env f vs) as (le & ?); first done.
    iMod (alloc_stackframe _ _ O with "[$Hm $Hr]") as (m' ve' lb (? & ?)) "(Hm & Hr & Hstack)"; [try done..|].
    rewrite embed_fupd; iIntros "!>".
    iExists _, _; iSplit.
    { iPureIntro; econstructor; eauto.
      econstructor; eauto.
      * eapply list_norepet_append_left; eauto.
      * apply list_norepet_append_inv; auto. }
    iFrame.
    iDestruct "Hd" as "-#?"; iClear "#".
    iStopProof; split => ?; rewrite /initial_internal_call_assert /wp /assert_safe /stack_level; monPred.unseal; rewrite !monPred_at_affinely.
    iIntros "(H & Hr & Hstack & %Hi)"; inv Hi.
    iPoseProof (monPred_in_entails with "Hstack") as "Hstack"; first by apply stackframe_of_eq1'.
    rewrite monPred_at_sep; iDestruct "Hstack" as "(? & ?)".
    iApply ("H" with "[//] [$] [//] [$] [//] [//] [//] [] [//] [$Hr //] [//] [%] [//] [//] [//]").
    2: { simpl; split3; auto.
         * rewrite env_to_environ_alloc; split; auto.
           split; intros; rewrite make_env_spec //.
         * intros; rewrite lookup_insert_ne; last lia; done. }
    2: { rewrite monPred_at_affinely; done. }
    rewrite -guarded_frame_ret0 //=.
    rewrite /assert_safe; monPred.unseal.
    iIntros "!>" (ret ??) "Hret".
    iIntros (??????) "Hr %% (%Henv' & %Hstack') %% %Hty' %% _".
    unfold sqsubseteq in *; subst.
    iApply jsafe_step; rewrite /jstep_ex.
    iIntros (?) "(Hm & Ho)".
    destruct ret; simpl.
    + rewrite /wp_expr; monPred.unseal.
      iMod ("Hret" with "[//] [$] [//] [$]") as ">(% & Hret & ? & ? & (% & H) & (Hstack & %vs' & Hstack'))".
      iPoseProof (monPred_in_entails with "[Hstack Hstack']") as "Hstack"; first by apply (stackframe_of_eq' f vs').
      { rewrite monPred_at_sep; iFrame. }
      rewrite monPred_at_exist; iDestruct "Hstack" as (?) "Hstack".
      iMod (free_stackframe with "[$]") as (m'' ?) "(Hm & ?)"; [done..|].
      rewrite monPred_at_affinely; iDestruct "Hret" as %Hret.
      pose proof (typecheck_var_match_venv _ _ Hty') as Hmatch'.
      specialize (Hret _ _ _ eq_refl Henv' Hmatch'); inv Hret.
      2: { inv H9. }
      iIntros "!>".
      iExists _, _; iSplit.
      { iPureIntro; econstructor; eauto. }
      iFrame.
      iNext.
      rewrite jsafe_unfold /jsafe_pre.
      iIntros "!> !>" (?) "?"; iLeft.
      iDestruct (Hexit with "[$] [$]") as %(? & ?).
      by iExists _.
    + iDestruct "Hret" as "((%Hvoid & H) & (Hstack & %vs' & Hstack'))".
      iPoseProof (monPred_in_entails with "[Hstack Hstack']") as "Hstack"; first by apply (stackframe_of_eq' f vs').
      { rewrite monPred_at_sep; iFrame. }
      rewrite monPred_at_exist; iDestruct "Hstack" as (?) "Hstack".
      iMod (free_stackframe with "[$]") as (m'' ?) "(Hm & ?)"; [done..|].
      iIntros "!>".
      iExists _, _; iSplit.
      { iPureIntro; econstructor; eauto. }
      iFrame.
      iNext.
      rewrite jsafe_unfold /jsafe_pre.
      iIntros "!> !>" (?) "?"; iLeft.
      iDestruct (Hexit with "[$] [$]") as %(? & ?).
      by iExists _.
  - (* external *)
    iApply fupd_jsafe.
    iMod "H".
    rewrite /jsafeN jsafe_unfold /jsafe_pre.
    rewrite !embed_fupd; iIntros "!> !>" (?) "Hm".
    iDestruct ("H" with "Hm") as (? (Hinline & ?)) "H".
    iRight; iRight.
    iExists _, _, _; iSplit.
    { iPureIntro; rewrite /= Hinline; eauto. }
    iNext; iIntros (?????).
    rewrite embed_fupd.
    iMod (fupd_mask_subseteq E) as "Hclose"; first done.
    iMod ("H" with "[//] [//]") as "($ & H)".
    iMod "Hclose" as "_"; iIntros "!>".
    iExists _; iSplit; first done.
    iPoseProof (stack_level_embed with "Hd H") as "H".
    rewrite jsafe_unfold /jsafe_pre.
    iIntros "!> !>" (?) "?"; iLeft.
    iDestruct (Hexit with "[$] [$]") as %(? & ?).
    by iExists _.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros; simpl; auto.
Qed.

Lemma stack_matches_call : forall ρ ve te k, stack_matches' ρ ve te (Some k) →
  stack_matches' ρ ve te (Some (call_cont k)).
Proof.
  induction k; simpl; auto.
Qed.

Lemma wp_expr_opt_mask_mono : forall E E' f e R, E ⊆ E' → wp_expr_opt E f e R ⊢ wp_expr_opt E' f e R.
Proof.
  intros; destruct e; auto; simpl.
  by apply wp_expr_mask_mono.
Qed.

Lemma call_cont_depth : forall k,
  stack_depth (call_cont k) = stack_depth k.
Proof.
  induction k; auto.
Qed.

Lemma wp_return: forall E f ret R,
  wp_expr_opt E f (option_map (λ e, Ecast e (fn_return f)) ret) (RA_return R) ⊢ wp E f (Sreturn ret) R.
Proof.
  intros; rewrite /wp.
  iIntros "H %%% Hk" (????) "?%%?".
  iApply (convergent_controls_jsafe _ _ _ (State f (Sreturn ret) (call_cont k) ve te)); try done.
  { inversion 1; subst; try match goal with H : _ \/ _ |- _ => destruct H; done end;
      rewrite call_cont_idem; econstructor; eauto. }
  iDestruct "Hk" as "(_ & _ & _ & Hk)".
  rewrite wp_expr_opt_mask_mono //.
  iApply ("Hk" with "H [$]"); try done.
  - iPureIntro; by apply stack_matches_call.
  - rewrite /= call_cont_depth //.
Qed.

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

Definition exit_ret_assert R : assert := ((RA_break R -∗ False) ∧ (RA_continue R -∗ False) ∧
  (∀ v, (RA_normal R ∨ RA_return R v) -∗ ∀ m z, ⎡state_interp m z⎤ -∗ ⌜∃ i, ext_spec_exit OK_spec (Some (Vint i)) z m⌝)).

Lemma guarded_stop : forall E f R,
  f.(fn_vars) = [] →
  exit_ret_assert R ⊢ guarded E f Kstop R.
Proof.
  intros; iIntros "H".
  iSplit.
  - rewrite /assert_safe /=; iIntros "R".
    iIntros (????) "? (% & _) %?".
    iApply safe_return; try done.
    { by apply typecheck_var_match_venv. }
    iFrame; iIntros (?) "?"; iDestruct "H" as "(_ & _ & H)".
    rewrite embed_pure.
    iApply ("H" $! None with "[R] [$]"); auto.
  - simpl; iSplit.
    { iDestruct "H" as "(H & _)".
      iIntros "?"; iDestruct ("H" with "[$]") as "[]". }
    iSplit.
    { iDestruct "H" as "(_ & H & _)".
      iIntros "?"; iDestruct ("H" with "[$]") as "[]". }
    iIntros ([|]); simpl.
    + iIntros "He" (????) "Hr (% & %) %Hmatch #Hd".
      iApply jsafe_step.
      rewrite /wp_expr /jstep_ex.
      iIntros (?) "(Hm & ?)".
      rewrite /bind_ret /=.
      iPoseProof (env_match_intro with "Hd") as "#?"; first done.
      iMod ("He" with "Hm Hr") as ">(% & He & ? & ? & ?)"; [done..|].
      iDestruct ("He" with "[$]") as %He.
      apply typecheck_var_match_venv in Hmatch.
      exploit He; eauto; intros Hcast.
      rewrite H in Hmatch.
      inv Hcast.
      rewrite embed_fupd.
      iIntros "!>"; iExists _, _; iSplit.
      { iPureIntro; econstructor; eauto.
        rewrite /blocks_of_env.
        destruct (PTree.elements ve) as [|(id, (?, ?))] eqn: Hel; first done.
        specialize (Hmatch id); rewrite make_env_spec in Hmatch.
        erewrite PTree.elements_complete in Hmatch; last by rewrite Hel; simpl; auto.
        done. }
      iFrame.
      iNext.
      rewrite embed_fupd; iModIntro.
      rewrite jsafe_unfold /jsafe_pre embed_fupd.
      iIntros "!>" (?) "S"; iLeft.
      iDestruct ("H" with "[-S] S") as %(? & ?); auto.
      iExists _; simpl; eauto.
      { inv H2. }
    + rewrite /assert_safe /=; iIntros "?".
      iIntros (????) "?%%?".
      iApply safe_return; try done.
      { by apply typecheck_var_match_venv. }
      iFrame; iIntros (?) "S".
      rewrite embed_pure; iApply ("H" with "[-S] S"); auto.
Qed.

(* {{P}} f {{Q}} *)
Definition fun_triple (P : list val → assert) f Q : assert :=
  □ ∀ args, ⌜tc_vals (map snd (fn_params f)) args⌝ → P args -∗ stack_retainer f -∗ stackframe_of' ge f (args ++ repeat Vundef (length (fn_temps f))) -∗
    wp ⊤ f (fn_body f) (frame_ret_assert (function_body_ret_assert (fn_return f) Q) (stack_retainer f ∗ ∃ lv, stackframe_of' ge f lv)).

End mpred.

Lemma tc_vals_length: forall tys vs, tc_vals tys vs -> length tys = length vs.
Proof.
induction tys; destruct vs; simpl; intros; auto; try contradiction.
destruct H; auto.
Qed.

Lemma tc_vals_Vundef {args ids} (TC:tc_vals ids args): Forall (fun v : val => v <> Vundef) args.
Proof.
generalize dependent ids. induction args; intros. constructor.
destruct ids; simpl in TC. contradiction. destruct TC.
constructor; eauto. intros N; subst. apply (tc_val_Vundef _ H).
Qed.

(* adequacy *)
Require Import VST.veric.external_state.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.semantics.
Import Address.

Class VSTGpreS (Z : Type) Σ := {
  VSTGpreS_inv :: invGpreS Σ;
  VSTGpreS_heap :: gen_heapGpreS share address resource Σ;
  VSTGpreS_funspec :: inG Σ (gmap_view.gmap_viewR address (@funspecO' Σ));
  VSTGpreS_env :: inG Σ envR;
  VSTGpreS_ext :: inG Σ (excl_authR (leibnizO Z))
}.

Definition VSTΣ Z : gFunctors :=
  #[invΣ; gen_heapΣ share address resource; GFunctor (gmap_view.gmap_viewRF address funspecOF');
    GFunctor envR; GFunctor (excl_authR (leibnizO Z)) ].
Global Instance subG_VSTGpreS {Z Σ} : subG (VSTΣ Z) Σ → VSTGpreS Z Σ.
Proof. solve_inG. Qed.

Lemma own_gvars : forall `{!heapGS Σ} `{!envGS Σ} ge, own(inG0 := envGS_inG) env_name ([^ op map] i↦b ∈ ge, lib.gmap_view.gmap_view_frag i DfracDiscarded (to_agree b), ε) ⊢
  [∗ map] i↦b∈ge, gvar i b.
Proof.
  induction ge as [|i x m ? IH] using map_ind.
  - rewrite !big_opM_empty.
    apply own_increasing_affine, _.
  - rewrite !big_opM_insert // pair_op_1 own_op IH //.
Qed.

Lemma init_VST: forall Z `{!VSTGpreS Z Σ} (z : Z) ge,
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS Z Σ,
    let H : VSTGS Z Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    (state_interp Mem.empty z ∗ env_auth (ge, ∅) ∗ ([∗ map] i↦b∈ge, gvar i b) ∗ funspec_auth ∅ ∗ has_ext z) ∗
    ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (own_alloc(A := envR) ((lib.gmap_view.gmap_view_auth DfracDiscarded (to_agree <$> ge), ● ∅) ⋅
    (([^op map] i↦b∈ge, lib.gmap_view.gmap_view_frag i DfracDiscarded (to_agree b)), ε))) as (γe) "He".
  { apply pair_valid; split.
    * rewrite -big_opM_view_frag; apply view_both_dfrac_valid.
      split; first done; intros ????.
      assert (((λ x, (DfracDiscarded, to_agree x)) <$> ge) !! i ≡ Some x) as Hi.
      { rewrite -(gmap.big_opM_singletons (_ <$> _)) big_opM_fmap H //. }
      rewrite lookup_fmap in Hi.
      destruct x, (ge !! i) eqn: Hgei; inv Hi.
      destruct H2 as ([=] & Hc); simpl in *; subst.
      eexists _, DfracDiscarded.
      rewrite lookup_fmap Hgei; split; first done; split; first done.
      apply @Some_includedN_mono, pair_includedN; split.
      { by exists DfracDiscarded. }
      { by rewrite Hc. }
    * rewrite /= right_id; by apply auth_auth_valid. }
  rewrite own_op; iDestruct "He" as "(? & Hg)".
  iMod (ext_alloc z) as (?) "(? & ?)".
  iIntros "!>" (?); iExists (GenHeapGS _ _ _ _ γh γm), (FunspecG _ _ γf), (EnvGS _ _ γe), _.
  rewrite /state_interp /mem_auth /funspec_auth /env_auth fmap_empty /= -own_gvars; iFrame.
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
      Val.has_type_list args (map proj_xtype (sig_args (ef_sig ef)))
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
    split3; simpl; intros; rewrite /Map.get /gmap_to_fun make_env_spec //.
  - done.
  - intros; rewrite lookup_insert_ne //; lia.
Qed.

Lemma wp_adequacy_call: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
  (ge : genv) m z f vs (R : forall `{!VSTGS OK_ty Σ}, assert)
  (Hwf : fundef_wf ge f vs)
  (EXIT: forall `{!VSTGS OK_ty Σ}, ⊢ (R O -∗ ∀ m z, state_interp m z -∗ ⌜∃ i, ext_spec_exit Espec (Some (Vint i)) z m⌝)),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    stack_level 0 ∗ ⎡state_interp m z⎤ ∗ ⎡env_auth (make_env (Genv.genv_symb ge), ∅)⎤ ∗ initial_call_assert Espec ge ⊤ f vs R) →
       (forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (Callstate f vs Kstop) m (*∧ φ*)) (* note that this includes ext_spec_exit if the program halts *).
Proof.
  intros.
  eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc'(Σ := Σ) _ (S n) O); [apply _..|].
  simpl; intros. apply (embed_emp_valid_inj(PROP2 := monPred stack_index _)). iIntros "_".
  iMod (H Hinv) as (????) "(? & ? & E & ?)".
  iPoseProof (call_safe_stop with "[$] [E] [$]") as "Hsafe"; try done.
  { intros; rewrite make_env_spec //. }
  { done. }
  { iIntros; by iApply (EXIT with "[$]"). }
  iStopProof; split => ?; monPred.unseal.
  rewrite -step_fupd_intro // -bi.later_intro.
  set (HH := Build_VSTGS _ _ _ _ _).
  rewrite -step_fupdN_mono; last by apply bi.pure_mono, (ext_spec_entails_safe _ (Espec _)).
  apply (adequacy(VSTGS0 := HH)(OK_spec := Espec HH)).
Qed.

(* This is a "whole-program" adequacy theorem; we may also want a per-function one. *)
Lemma wp_adequacy: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
  ge m z f s (R : forall `{!VSTGS OK_ty Σ}, ret_assert) ve te (Hf : f.(fn_vars) = [])
  (EXIT: forall `{!VSTGS OK_ty Σ}, ⊢ exit_ret_assert Espec R),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    stack_level 0 ∗ ⎡state_interp m z⎤ ∗ ⌜typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f))⌝ ∧ ⎡env_auth (init_stack ge ve te)⎤ ∗ wp Espec ge ⊤ f s R) →
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
  rewrite /wp /assert_safe; split => l; monPred.unseal.
  iIntros "(#L & S & % & E & H)".
  iApply step_fupd_intro; first done.
  iNext.
  set (HH := Build_VSTGS _ _ _ _ _).
  iApply step_fupdN_mono.
  { apply bi.pure_mono, (ext_spec_entails_safe _ (Espec HH)); auto. }
  iApply (adequacy(VSTGS0 := HH)(OK_spec := Espec HH)).
  iFrame.
  iApply ("H" with "[//] [//] [//] [] [//] E [//] [%] [//] [//] [//]").
  rewrite -guarded_stop // -EXIT monPred_at_emp //.
  { apply init_stack_matches. }
  { done. }
Qed.
