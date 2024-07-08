(* A core wp-based separation logic for Clight, in the Iris style. Maybe VeriC can be built on top of this? *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax.
Require Import VST.veric.semax_straight.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty).

Definition assert_safe
     (E: coPset) (f: function) (ctl: contx) rho : iProp Σ :=
       ∀ ora ge ve te,
       ⌜rho = construct_rho (filter_genv ge) ve te⌝ →
       match ctl with
       | Stuck => |={E}=> False
       | Cont (Kseq s ctl') => 
             jsafeN OK_spec ge E ora (State f s ctl' ve te)
       | Cont (Kloop1 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f Sskip (Kloop1 body incr ctl') ve te)
       | Cont (Kloop2 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f (Sloop body incr) ctl' ve te)
       | Cont (Kcall id' f' ve' te' k') => 
             jsafeN OK_spec ge E ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
       | Cont Kstop =>
             jsafeN OK_spec ge E ora (State f (Sreturn None) Kstop ve te)
       | Cont _ => |={E}=> False
       | Ret None ctl' =>
                jsafeN OK_spec ge E ora (State f (Sreturn None) ctl' ve te)
       | Ret (Some v) ctl' => ∀ e, (∀ m, juicy_mem.mem_auth m -∗ ⌜∃ v', Clight.eval_expr ge ve te m e v' ∧ Cop.sem_cast v' (typeof e) (fn_return f) m = Some v⌝) →
              (* Could we replace these with eval_expr and lose the memory dependence?
                 Right now, the only difference is that e must only access pointers that are valid in the current rmap.
                 But typechecking will also guarantee that. *)
              jsafeN OK_spec ge E ora (State f (Sreturn (Some e)) ctl' ve te)
       end.

Definition wp E f s (Q : assert) : assert := assert_of (λ rho,
    ∀ k, ((* ▷ *) (∀ rho, Q rho -∗ assert_safe E f (Cont k) rho)) -∗ assert_safe E f (Cont (Kseq s k)) rho).
(* ▷ would make sense here, but removing Kseq isn't always a step: for instance, Sskip Kstop is a synonym
   for (Sreturn None) Kstop rather than stepping to it. *)

Definition wp_expr e Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ v, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ v.

Definition wp_lvalue e Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ b o, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_lvalue ge ve te m e b o Full (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ (Vptr b o).

Global Instance local_absorbing `{!heapGS Σ} l : Absorbing (local l).
Proof.
  rewrite /local; apply monPred_absorbing, _.
Qed.

Global Instance local_persistent `{!heapGS Σ} l : Persistent (local l).
Proof.
  rewrite /local; apply monPred_persistent, _.
Qed.

Lemma wp_seq : forall E f s1 s2 Q, wp E f s1 (wp E f s2 Q) ⊢ wp E f (Ssequence s1 s2) Q.
Proof.
  intros; rewrite /wp; split => rho.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_local_step.
  { intros; constructor. }
  iApply ("H" with "[Hk]"); last done.
  by iIntros "% H"; iApply "H".
Qed.

Definition valid_val v :=
  match v with Vptr _ _ => expr.valid_pointer v | _ => True end.

Definition valid_val0 m v : Prop :=
  match v with Vptr b o => valid_pointer m b (Ptrofs.intval o) = true | _ => True end.

Lemma valid_val_mem : forall m v, juicy_mem.mem_auth m ∗ valid_val v ⊢ ⌜valid_val0 m v⌝.
Proof.
  iIntros (??) "(Hm & Hv)"; destruct v; try done.
  iApply expr_lemmas4.valid_pointer_dry0; iFrame.
Qed.

Lemma bool_val_valid : forall m v t b, valid_val0 m v -> Cop2.bool_val t v = Some b -> bool_val v t m = Some b.
Proof.
  rewrite /Cop2.bool_val /bool_val.
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

Lemma wp_if: forall E f e s1 s2 R,
  wp_expr e (λ v, ⎡valid_val v⎤ ∧ ∃ b, ⌜Cop2.bool_val (typeof e) v = Some b⌝ ∧ if b then wp E f s1 R else wp E f s2 R)
  ⊢ wp E f (Sifthenelse e s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (??) "(Hm & H)"; first done.
  iDestruct (valid_val_mem with "[Hm H]") as %?.
  { rewrite bi.and_elim_l; iFrame. }
  rewrite bi.and_elim_r; iDestruct "H" as (b ?) "H".
  iIntros "!>"; iExists _, m.
  iSplit.
  { iPureIntro.
    econstructor; eauto.
    apply bool_val_valid; eauto. }
  iFrame.
  destruct b; simpl; iNext; iApply ("H" with "[-]"); done.
Qed.

(* see also semax_lemmas.derives_skip *)
Lemma safe_skip : forall E ora f k ge ve te,
  assert_safe E f (exit_cont EK_normal None k) (construct_rho (filter_genv ge) ve te) ⊢
  jsafeN OK_spec ge E ora (State f Sskip k ve te).
Proof.
  intros; iIntros "H".
  rewrite /assert_safe.
  iSpecialize ("H" with "[%]"); first done.
  destruct k as [ | s ctl' | | | |]; try done; try solve [iApply (jsafe_local_step with "H"); constructor].
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iMod "H" as "[]".
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

Lemma wp_skip: forall E f R, R ⊢ wp E f Sskip R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (???? ->).
  iSpecialize ("Hk" with "H").
  by iApply safe_skip.
Qed.

Lemma wp_set: forall E f i e (R : assert),
  wp_expr e (λ v, assert_of (subst i (liftx v) R)) ⊢ wp E f (Sset i e) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (??) "(Hm & H)"; first done.
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; constructor; eauto. }
  iFrame.
  iNext.
  iApply safe_skip; iApply "Hk".
  rewrite /subst /env_set /construct_rho /= expr_lemmas.map_ptree_rel //.
Qed.

Lemma wp_store: forall E f e1 e2 R,
  wp_lvalue e1 (λ v1, ∃ sh, ⌜writable0_share sh⌝ ∧ ⎡mapsto_ sh (typeof e1) v1⎤ ∗
    wp_expr (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ (⎡mapsto sh (typeof e1) v1 v2⎤ ={E}=∗ R)))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (b o ?) "(Hm & H)"; first done.
  iDestruct "H" as (sh ?) "(Hp & H)".
  iDestruct ("H" with "[%] Hm") as (? He2) "(Hm & % & H)"; first done.
  iDestruct (mapsto_pure_facts with "Hp") as %((? & ?) & ?).
  iDestruct (mapsto_can_store with "[$Hm Hp]") as %(? & ?); [done.. |].
  iMod (mapsto_store with "[$Hm $Hp]") as "(Hm & Hp)"; [done.. |].
  iMod ("H" with "[%] Hp"); first done.
  iIntros "!>".
  specialize (He2 _ _ _ eq_refl); inv He2.
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iFrame.
  iNext.
  iApply safe_skip; iApply "Hk"; done.
  { inv H5. }
Qed.

Lemma wp_loop: forall E f s1 s2 R,
  ▷ wp E f s1 (▷ wp E f s2 (wp E f (Sloop s1 s2) R)) ⊢ wp E f (Sloop s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  monPred.unseal.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[Hk]"); last done.
  iIntros "% H" (???? ->).
  iApply jsafe_local_step.
  { intros; constructor; auto. }
  iNext.
  iApply ("H" with "[Hk]"); last done.
  iIntros "% H" (???? ->).
  by iApply ("H" with "Hk").
Qed.

End mpred.
