(*Require Import iris.bi.lib.fixpoint_banach.*)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.Clight_lemmas.
Require Import VST.msl.eq_dec.

Import Ctypes.

Lemma no_dups_swap:
  forall F V a b c, @no_dups F V (a++b) c -> @no_dups F V (b++a) c.
Proof.
unfold no_dups; intros.
rewrite -> map_app in *.
forget (map (@fst _ _) b) as bb.
forget (map (@fst _ _) a) as aa.
forget (map (var_name V) c) as cc.
clear - H.
destruct (list_norepet_append_inv _ _ _ H) as [? [? ?]].
apply list_norepet_append; auto.
apply list_norepet_append_commut; auto.
clear - H2.
unfold Coqlib.list_disjoint in *.
intros; apply H2; auto.
clear - H.
rewrite -> in_app in *.
tauto.
Qed.

Lemma join_sub_share_top: forall sh, sepalg.join_sub Share.top sh -> sh = Share.top.
Proof.
intros.
generalize (top_correct' sh); intro.
apply sepalg.join_sub_antisym; auto.
Qed.


Lemma nat_of_Z_minus_le : forall z a b,
  b <= a ->
  (Z.to_nat (z - a) <= Z.to_nat (z - b))%nat.
Proof.
  intros.
  apply inj_le_rev.
  do 2 rewrite Z_to_nat_max.
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-a)).
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-b)).
  lia.
  lia.
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-b)); lia.
Qed.

Lemma subst_set : forall {A} id v (P : environ -> A) v' rho
  (Hid : (te_of rho !! id)%stdpp = Some v),
  subst id (λ _ : environ, eval_id id rho) P (env_set rho id v') = P rho.
Proof.
  intros; destruct rho as ((?, ?), ?); rewrite /subst /env_set /=; unfold_lift.
  rewrite insert_insert insert_id //.
  by rewrite /eval_id Hid.
Qed.

Section SemaxContext.

Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty}.

Lemma guard_environ_put_te':
 forall Delta f rho id v t,
 guard_environ Delta f rho  ->
 (temp_types Delta) !! id = Some t -> tc_val' t v ->
 guard_environ Delta f (env_set rho id v).
Proof.
  intros.
  destruct H as (? & ? & ?); split3; auto.
  - apply typecheck_environ_put_te; auto.
    intros ? Hid; rewrite Hid in H0; inv H0; done.
  - intros ??; destruct (eq_dec i id); subst; eauto.
    rewrite /= lookup_insert_ne //; eauto.
Qed.

Lemma typecheck_environ_sub:
  forall Delta Delta', tycontext_sub Delta Delta' ->
   forall rho,
   typecheck_environ Delta' rho -> typecheck_environ Delta rho.
Proof.
intros ?? [? [? [? [? Hs]]]] ?  [? [? ?]].
split; [ | split].
* clear - H H3.
 hnf; intros.
 specialize (H id); rewrite H0 in H.
 destruct ((temp_types Delta') !! id) eqn:?H; try contradiction.
 destruct H; subst.
 specialize (H3 id ty H1).
 destruct H3 as [v [? ?]].
 exists v; split; auto.
* clear - H0 H4.
  red in H4|-*.
 intros id ty. specialize (H4 id ty). rewrite <- H4.
 rewrite H0. clear; tauto.
* clear - H2 H5.
 hnf; intros. eapply H5.
 specialize (H2 id). hnf in H2. rewrite H in H2. eauto.
Qed.

Lemma typecheck_environ_set : forall Delta rho id t v, typecheck_environ Delta rho ->
  temp_types Delta !! id = Some t -> tc_val' t v ->
  typecheck_environ Delta (env_set rho id v).
Proof.
  intros ????? (? & ? & ?) ??; split3; auto.
  intros i ? Ht; destruct (eq_dec i id).
  + subst i; rewrite lookup_insert; exists v; split; eauto.
    assert (ty = t) by congruence; subst; auto.
  + rewrite lookup_insert_ne; auto.
Qed.

Lemma semax_unfold {CS: compspecs} E Delta P c R :
  semax OK_spec E Delta P c R ↔ forall (psi: Clight.genv) Delta' CS'
          (TS: tycontext_sub Delta Delta')
          (HGG: cenv_sub (@cenv_cs CS) (@cenv_cs CS') /\ cenv_sub (@cenv_cs CS') (genv_cenv psi)),
    ⊢ ⎡funassert Delta' psi⎤ -∗ believe(CS := CS') OK_spec Delta' psi Delta' -∗ ∀ f rho, <affine> ⌜guard_environ Delta' f rho⌝ -∗
      curr_env psi f rho -∗ ⎡P rho⎤ -∗ wp OK_spec psi E f c (Clight_seplog.frame_ret_assert (env_ret_assert Delta' psi f R) ⎡funassert Delta' psi⎤).
Proof.
rewrite /semax semax_fold_unfold.
split; intros.
+ iIntros "F B"; iApply (H with "[%] F B"); auto.
+ iIntros (??? (? & ?)) "!> F B"; iApply (H with "F B"); auto.
Qed.

Lemma frame_normal : forall R P, RA_normal (frame_ret_assert R P) = (RA_normal R ∗ P).
Proof. by destruct R. Qed.

Lemma derives_skip:
  forall {CS: compspecs} p E Delta (R: ret_assert),
      (p ⊢ proj_ret_assert R EK_normal None) ->
        semax OK_spec E Delta p Clight.Sskip R.
Proof.
intros.
rewrite semax_unfold.
intros psi Delta' CS' ??.
iIntros "? _" (?? (? & ?)) "??".
iApply wp_skip; simpl; iFrame.
rewrite H /=.
rewrite monPred_at_and bi.and_elim_r; auto.
Qed.

Fixpoint list_drop (A: Type) (n: nat) (l: list A) {struct n} : list A :=
  match n with O => l | S i => match l with nil => nil | _ :: l' => list_drop A i l' end end.
Arguments list_drop [A] _ _.

Definition straightline (c: Clight.statement) :=
 forall ge f ve te k m f' ve' te' c' k' m',
        cl_step ge (State f c k ve te) m (State f' c' k' ve' te') m' -> (c'=Sskip /\ k=k').

Lemma straightline_assign: forall e0 e, straightline (Clight.Sassign e0 e).
Proof.
unfold straightline; intros.
inv H; auto.
destruct H13; inv H; auto.
destruct H13; inv H; auto.
Qed.

Global Instance believe_external_absorbing gx v fsig cc A E P Q : Absorbing (believe_external OK_spec gx v fsig cc A E P Q).
Proof.
  rewrite /believe_external.
  destruct (Genv.find_funct _ _) as [[|]|]; apply _.
Qed.

  (* will be in fixpoint_banach once we bump Iris *)
  Lemma fixpoint_plain `{!BiPlainly PROP} {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Plain (F Φ x))) →
    ∀ x, Plain (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, emp%I); apply _.
    - done.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_Plain; solve_proper.
  Qed.

  Lemma fixpoint_absorbing {PROP : bi} {A} (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, True%I); apply _.
    - done.
    - apply limit_preserving_forall=> x.
      apply bi.limit_preserving_entails; solve_proper.
  Qed.

  Lemma fixpoint_plain_absorbing `{!BiPlainly PROP} {A}
      (F : (A -d> PROP) → A -d> PROP) `{!Contractive F} :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Absorbing (Φ x)) →
          (∀ x, Plain (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Absorbing (fixpoint F x).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros Φ1 Φ2 HΦ ??. by rewrite -(HΦ _).
    - exists (λ _, True%I); split; apply _.
    - naive_solver.
    - apply limit_preserving_forall=> x.
      apply limit_preserving_and; apply bi.limit_preserving_entails; solve_proper.
  Qed.

Lemma semax'_plain_absorbing CS E Delta P c R : Plain (semax'(CS := CS) OK_spec E Delta P c R) ∧ Absorbing (semax' OK_spec E Delta P c R).
Proof.
  apply fixpoint_plain_absorbing; intros; rewrite /semax_; destruct x; split; apply _.
Qed.

Global Instance semax'_plain CS E Delta P c R : Plain (semax'(CS := CS) OK_spec E Delta P c R).
Proof. apply semax'_plain_absorbing. Qed.

Global Instance semax'_absorbing CS E Delta P c R : Absorbing (semax'(CS := CS) OK_spec E Delta P c R).
Proof. apply semax'_plain_absorbing. Qed.

Lemma extract_exists_pre_later {CS: compspecs}:
  forall (A : Type) (Q: assert) (P : A -> assert) c E Delta (R: ret_assert),
  (forall x, semax OK_spec E Delta (Q ∧ ▷ P x) c R) ->
   semax OK_spec E Delta (Q ∧ ▷ ∃ x, P x) c R.
Proof.
intros.
rewrite semax_unfold; intros.
iIntros "??" (???) "? Pre".
rewrite monPred_at_and monPred_at_later monPred_at_exist.
rewrite bi.later_exist_except_0 (bi.except_0_intro Q) monPred_at_except_0 -bi.except_0_and bi.and_exist_l.
iMod "Pre" as (x) "Pre"; specialize (H x).
rewrite semax_unfold in H; iApply (H with "[$] [$] [//] [$]"); eauto.
by rewrite monPred_at_and monPred_at_later.
Qed.

Lemma extract_exists_pre {CS: compspecs}:
  forall  (A : Type) (P : A -> assert) c E Delta (R: ret_assert),
  (forall x, semax OK_spec E Delta (P x) c R) ->
   semax OK_spec E Delta (∃ x, P x) c R.
Proof.
intros.
rewrite semax_unfold; intros.
iIntros "??" (???) "? Pre".
rewrite monPred_at_exist; iDestruct "Pre" as (x) "Pre"; specialize (H x).
rewrite semax_unfold in H; iApply (H with "[$] [$] [//] [$]"); eauto.
Qed.

Definition G0: funspecs(Σ := Σ) := nil.

Definition empty_genv prog_pub cenv: Clight.genv :=
   Build_genv (Genv.globalenv (AST.mkprogram (F:=Clight.fundef)(V:=type) nil prog_pub (1%positive))) cenv.

Lemma empty_program_ok {CS: compspecs}: forall Delta ge,
    glob_specs Delta = Maps.PTree.empty _ ->
    ⊢ believe OK_spec Delta ge Delta.
Proof.
intros Delta ge H.
rewrite /believe.
iIntros (??????? (? & Hge & ?)).
rewrite H in Hge; setoid_rewrite Maps.PTree.gempty in Hge; discriminate.
Qed.

Definition all_assertions_computable  :=
  forall psi E f (Q: mpred),
     exists k,  assert_safe OK_spec psi E f k = Q.
(* This is not generally true, but could be made true by adding an "assert" operator
  to the programming language
 *)

(*Lemma guard_environ_sub:
  forall {Delta Delta' f rho},
   tycontext_sub Delta Delta' ->
   guard_environ Delta' f rho ->
   guard_environ Delta f rho.
Proof.
intros.
destruct H0; split; auto.
eapply typecheck_environ_sub; eauto.
destruct f; auto.
destruct H1; split; auto.
destruct H as [? [? [? ?]]]. rewrite H4; auto.
Qed.*)

Local Notation assert := (@assert Σ).

Lemma proj_frame_ret_assert:
 forall (R: ret_assert) (F: assert) ek vl,
  proj_ret_assert (frame_ret_assert R F) ek vl ⊣⊢
  (proj_ret_assert R ek vl ∗ F).
Proof.
  intros; rewrite proj_frame comm //.
Qed.

Lemma env_ret_assert_proper Delta ge f : Proper (base.equiv ==> base.equiv) (env_ret_assert Delta ge f).
Proof.
  intros ???; rewrite /env_ret_assert.
  do 3 f_equiv.
  split3; last split; simpl; intros; f_equiv; apply H.
Qed.

(*Lemma semax_extensionality0 {CS: compspecs} {OK_spec: OracleKind}:
       True ⊢
      ALL Delta:tycontext, ALL Delta':tycontext,
      ALL P:assert, ALL P':assert,
      ALL c: statement, ALL R:ret_assert, ALL R':ret_assert,
       ((!! tycontext_sub E Delta Delta'
       &&  (ALL ek: exitkind, ALL  vl : option val, ALL rho: environ,
               (proj_ret_assert R ek vl rho >=> proj_ret_assert R' ek vl rho))
      && (ALL rho:environ, P' rho >=> P rho)  && semax' OK_spec Delta P c R) >=> semax' OK_spec Delta' P' c R').
Proof.
apply loeb.
intros w ? Delta Delta' P P' c R R'.
intros w1 ? ? w2 ? Hext [[[? ?] ?] ?].
do 3 red in H2.
rewrite semax_fold_unfold; rewrite semax_fold_unfold in H5.
intros gx Delta'' CS'.
apply prop_imp_i. intros [TS HGG].
intros ? w3 ? Hext3 ?.
specialize (H5 gx Delta'' CS' _ _ (necR_refl _) (ext_refl _)
 (conj (tycontext_sub_trans _ _ _ H2 TS) HGG)
                  _ _ H6 Hext3 H7).

intros k F f ? w4 Hw4 Hext4 [? ?].
specialize (H5 k F f _ w4 Hw4 Hext4).
assert ((rguard OK_spec gx Delta'' f (frame_ret_assert R F) k) w4).
do 9 intro. intros Hext' ?.
apply (H9 b b0 b1 b2 y H10 _ _ H11 Hext').
destruct H12; split; auto; clear H13.
pose proof I.
destruct H12; split; auto.
rewrite proj_frame_ret_assert in H14|-*.
clear H12 H13.
revert a'2 a'' H11 Hext' H14.
apply sepcon_subp' with (level w2).
apply H3.
auto.
apply necR_level in H6.
apply necR_level in Hw4.
apply ext_level in Hext3, Hext4.
eapply Nat.le_trans; try eassumption.
eapply Nat.le_trans; try eassumption.
rewrite Hext3; setoid_rewrite <- Hext4; auto.

specialize (H5 (conj H8 H10)). clear H8 H9 H10.
do 7 intro. intros Hext' ?.
apply (H5 b b0 y H8 _ _ H9 Hext').
destruct H10; split; auto.
destruct H10; split; auto.
clear H10 H11.
revert a'2 a'' H9 Hext' H12.
apply sepcon_subp' with (level w2); auto.
apply necR_level in H6.
apply necR_level in Hw4.
apply ext_level in Hext3, Hext4.
eapply Nat.le_trans; try eassumption.
eapply Nat.le_trans; try eassumption.
rewrite Hext3; setoid_rewrite <- Hext4; auto.
Qed.

Lemma semax_extensionality1 {CS: compspecs} {OK_spec: OracleKind}:
  forall Delta Delta' (P P': assert) c (R R': ret_assert) ,
       tycontext_sub E Delta Delta' ->
       ((ALL ek: exitkind, ALL  vl : option val, ALL rho: environ,
          (proj_ret_assert R ek vl rho >=> proj_ret_assert R' ek vl rho))
      && (ALL rho:environ, P' rho >=> P rho)  && (semax' OK_spec Delta P c R) |-- semax' OK_spec Delta' P' c R').
Proof.
intros.
intros n ?.
apply (semax_extensionality0 n I Delta Delta' P P' c R R' _ (Nat.le_refl _) _ _ (necR_refl _) (ext_refl _)).
destruct H0;
split; auto.
destruct H0;
split; auto.
split; auto.
Qed.*)

Lemma frame_ret_comm : forall R P Q,
  base.equiv (Clight_seplog.frame_ret_assert (Clight_seplog.frame_ret_assert R P) Q)
  (Clight_seplog.frame_ret_assert (Clight_seplog.frame_ret_assert R Q) P).
Proof.
  split; [|split3]; destruct R; simpl; intros; rewrite -!assoc (bi.sep_comm P Q) //.
Qed.

Lemma env_ret_frame : forall Delta ge f R F,
  base.equiv (env_ret_assert Delta ge f (frame_ret_assert R ⎡F⎤)) (Clight_seplog.frame_ret_assert (env_ret_assert Delta ge f R) ⎡F⎤).
Proof.
  intros; destruct R; rewrite /frame_ret_assert /env_ret_assert /Clight_seplog.frame_ret_assert /Clight_seplog.existential_ret_assert /=.
  split3; last split; simpl.
  - rewrite bi.sep_exist_r; do 2 f_equiv.
    rewrite monPred_at_sep monPred_at_embed.
    iSplit; iIntros "(($ & $) & $)".
  - rewrite bi.sep_exist_r; do 2 f_equiv.
    rewrite monPred_at_sep monPred_at_embed.
    iSplit; iIntros "(($ & $) & $)".
  - rewrite bi.sep_exist_r; do 2 f_equiv.
    rewrite monPred_at_sep monPred_at_embed.
    iSplit; iIntros "(($ & $) & $)".
  - intros; rewrite bi.sep_exist_r; do 2 f_equiv.
    rewrite monPred_at_sep monPred_at_embed.
    iSplit; iIntros "(($ & $) & $)".
Qed.

Lemma semax_frame {CS: compspecs} :  forall E Delta P s R F,
  semax OK_spec E Delta P s R ->
  semax OK_spec E Delta (P ∗ ⎡F⎤) s (frame_ret_assert R ⎡F⎤).
Proof.
  intros until F; rewrite !semax_unfold; intros.
  iIntros "??" (???) "? Pre".
  rewrite monPred_at_sep; iDestruct "Pre" as "(? & ?)".
  rewrite env_ret_frame.
  rewrite frame_ret_comm; iApply wp_frame.
  rewrite monPred_at_embed; iFrame.
  by iApply (H with "[$] [$] [//] [$]").
Qed.

Fixpoint filter_seq (k: cont) : cont :=
 match k with
  | Kseq s  k1 => filter_seq k1
  | _ => k
  end.

Fixpoint app_cont (k1 k2: cont) : cont :=
 match k1 with
 | Kstop => k2
 | Kseq c k1' => Kseq c (app_cont k1' k2)
 | Kloop1 c1 c2 k1' => Kloop1 c1 c2 (app_cont k1' k2)
 | Kloop2 c1 c2 k1' => Kloop2 c1 c2 (app_cont k1' k2)
 | Kswitch k1' => Kswitch (app_cont k1' k2)
 | Kcall i f ve te k1' => Kcall i f ve te (app_cont k1' k2)
 end.

Lemma cons_app: forall x y,
  Kseq x y = app_cont (Kseq x Kstop) y.
Proof. auto. Qed.

Lemma cons_app': forall x y z,
      Kseq x (app_cont y z) = app_cont (Kseq x y) z.
Proof. auto. Qed.

Fixpoint length_cont (k: cont) :=
match k with
| Kstop => O
| Kseq _ k' => S (length_cont k')
| Kloop1 _ _ k' =>  S (length_cont k')
| Kloop2 _ _ k' =>  S (length_cont k')
| Kswitch k' =>  S (length_cont k')
| Kcall _ _ _ _ k' =>  S (length_cont k')
end.

Lemma app_cont_length: forall k1 k2,
  length_cont (app_cont k1 k2) = (length_cont k1 + length_cont k2)%nat.
Proof.
induction k1; simpl; intros; auto.
Qed.

Lemma cat_prefix_empty:
   forall prefix ctl, ctl =  app_cont prefix ctl -> prefix = Kstop.
Proof.
intros.
pose proof (app_cont_length prefix ctl).
rewrite <- H in H0.
assert (length_cont prefix = O) by lia.
clear - H1.
destruct prefix; inv H1; auto.
Qed.

Definition true_expr : Clight.expr := Clight.Econst_int Int.one (Tint I32 Signed noattr).

Lemma filter_seq_call_cont:
  forall ctl1 ctl2, filter_seq ctl1 = filter_seq ctl2 -> call_cont ctl1 = call_cont ctl2.
Proof.
  intros ? ? H0.
  revert ctl2 H0; induction ctl1; simpl; intros; auto;
  revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
Qed.

Lemma call_cont_app_nil:
  forall l k, call_cont l = Kstop -> call_cont (app_cont l k) = call_cont k.
Proof.
 intros l k; revert k; induction l; simpl; intros;
   try destruct a; simpl in *; try congruence; auto.
Qed.

Lemma call_cont_app_cons:
  forall l, call_cont l <> Kstop ->
    forall k, call_cont (app_cont l k) = app_cont (call_cont l)  k.
Proof.
  induction l; simpl; intros; try congruence; auto.
Qed.

Section extensions.

Lemma safe_loop_skip:
  forall ge E ora f ve te k,
    ⊢ jsafeN OK_spec ge E ora
           (State f (Sloop Clight.Sskip Clight.Sskip) k ve te).
Proof.
  intros.
  iIntros; iLöb as "IH".
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext; iApply jsafe_local_step.
  { intros; constructor; auto. }
  iNext; iApply jsafe_local_step.
  { intros; constructor. }
  done.
Qed.

Local Open Scope nat_scope.

Fixpoint prebreak_cont (k: cont) : cont :=
  match k with
  | Kloop1 s e3 k' => k
  | Kseq s k' => prebreak_cont k'
  | Kloop2 s e3 k' => k
  | Kswitch k' => k
  | _ =>  Kstop (* stuck *)
  end.

Lemma prebreak_cont_is: forall k,
  match (prebreak_cont k) with
  | Kloop1 _ _ _ => True
  | Kloop2 _ _ _ => True
  | Kswitch _ => True
  | Kstop => True
  | _ => False
  end.
Proof.
induction k; simpl; auto.
Qed.

Lemma app_cont_ass: forall j k l,
  app_cont (app_cont j k) l = app_cont j (app_cont k l).
Proof.
intros.
induction j; simpl; f_equal; auto.
Qed.

Lemma find_label_prefix:
  forall lbl s ctl s' k, find_label lbl s ctl = Some (s',k) ->
     exists j, Kseq s' k = app_cont j ctl
with
  find_label_ls_prefix:
  forall lbl s ctl s' k, find_label_ls lbl s ctl = Some (s',k) ->
     exists j, Kseq s' k = app_cont j ctl.
Proof.
-
 intros.
  clear find_label_prefix.
  revert ctl k H; induction s; simpl; intros; try congruence.
 + revert H; case_eq (find_label lbl s1 (Kseq s2 ctl)); intros; [inv H0 | auto ].
    destruct (IHs1 _ _ H) as [j ?].
    exists (app_cont j (Kseq s2 Kstop)); rewrite app_cont_ass; auto.
  + revert H; case_eq (find_label lbl s1 ctl); intros; [inv H0 | auto ]; auto.
  + destruct (find_label lbl s1 (Kloop1 s1 s2 ctl)) eqn:H0; inv H.
      apply IHs1 in H0. destruct H0 as [j ?]. exists (app_cont j (Kloop1 s1 s2 Kstop)).
      rewrite app_cont_ass. auto.
      apply IHs2 in H2. destruct H2 as [j ?].
      exists (app_cont j (Kloop2 s1 s2 Kstop)). rewrite app_cont_ass; auto.
  + destruct (find_label_ls_prefix _ _ _ _ _ H) as [j ?].
      exists (app_cont j (Kswitch Kstop)); rewrite app_cont_ass; auto.
  +
  if_tac in H. subst l. inv H.
  exists (Kseq s' Kstop); auto.
  apply IHs; auto.
-
 induction s; simpl; intros. inv H.
 destruct (find_label lbl s (Kseq (seq_of_labeled_statement s0) ctl)) eqn:?H.
 inv H.
 destruct (find_label_prefix _ _ _ _ _ H0) as [j ?].
 exists (app_cont j (Kseq (seq_of_labeled_statement s0) Kstop)).
 rewrite app_cont_ass; auto.
 auto.
Qed.

Lemma find_label_None:
  forall lbl s ctl, find_label lbl s ctl = None -> forall ctl', find_label lbl s ctl' = None
with
  find_label_ls_None:
  forall lbl s ctl, find_label_ls lbl s ctl = None ->  forall ctl', find_label_ls lbl s ctl' = None.
Proof.
clear find_label_None; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 try (rewrite (IHs1 _ H); eauto).
 eauto.
 destruct (ident_eq lbl l). inv H. eapply IHs; eauto.

clear find_label_ls_None; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 try (rewrite (IHs1 _ H); eauto).
 eauto.
 rewrite (find_label_None _ _ _ H). eauto.
Qed.

(* Lemma guard_safe_adj':
 forall
   psi E Delta f P c1 k1 c2 k2,
  (forall E ora ve te,
     jsafeN OK_spec psi E ora (State f c1 k1 ve te) ⊢
     jsafeN OK_spec psi E ora (State f c2 k2 ve te)) ->
  guard' OK_spec psi E Delta f P (Kseq c1 k1) ⊢ guard' OK_spec psi E Delta f P (Kseq c2 k2).
Proof.
intros.
unfold guard', _guard.
iIntros "#H" (??) "!> P".
iSpecialize ("H" with "P").
rewrite /assert_safe.
iIntros (??); rewrite -H; iApply "H"; auto.
Qed. *)

Lemma semax_Delta_subsumption {CS: compspecs}:
  forall E Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     semax OK_spec E Delta P c R -> semax OK_spec E Delta' P c R.
Proof.
intros.
unfold semax in *.
rewrite -semax_mono; eauto.
Qed.

End extensions.

Definition Cnot (e: Clight.expr) : Clight.expr :=
   Clight.Eunop Cop.Onotbool e type_bool.

(* Mutually recursive induction scheme for [statement] and [labeled_statements] *)
Section statement_rect.
  Variable P : statement -> Type.
  Variable Q : labeled_statements -> Type.
  Variable f : P Sskip.
  Variable f0 : forall e e0 : expr, P (Sassign e e0).
  Variable f1 : forall (i : ident) (e : expr), P (Sset i e).
  Variable f2 : forall (o : option ident) (e : expr) (l : list expr), P (Scall o e l).
  Variable f3 : forall (o : option ident) (e : external_function) (t : list type) (l : list expr), P (Sbuiltin o e t l).
  Variable f4 : forall s : statement, P s -> forall s0 : statement, P s0 -> P (Ssequence s s0).
  Variable f5 : forall (e : expr) (s : statement), P s -> forall s0 : statement, P s0 -> P (Sifthenelse e s s0).
  Variable f6 : forall s : statement, P s -> forall s0 : statement, P s0 -> P (Sloop s s0).
  Variable f7 : P Sbreak.
  Variable f8 : P Scontinue.
  Variable f9 : forall o : option expr, P (Sreturn o).
  Variable f10 : forall (e : expr) (l : labeled_statements), Q l -> P (Sswitch e l).
  Variable f11 : forall (l : label) (s : statement), P s -> P (Slabel l s).
  Variable f12 : forall l : label, P (Sgoto l).
  Variable f13 : Q LSnil.
  Variable f14 : forall (o : option Z) (s : statement) (l : labeled_statements), P s -> Q l -> Q (LScons o s l).

  Fixpoint statement_rect (s : statement) : P s :=
  match s as s0 return (P s0) with
  | Sskip => f
  | Sassign e e0 => f0 e e0
  | Sset i e => f1 i e
  | Scall o e l => f2 o e l
  | Sbuiltin o e t l => f3 o e t l
  | Ssequence s0 s1 => f4 s0 (statement_rect s0) s1 (statement_rect s1)
  | Sifthenelse e s0 s1 => f5 e s0 (statement_rect s0) s1 (statement_rect s1)
  | Sloop s0 s1 => f6 s0 (statement_rect s0) s1 (statement_rect s1)
  | Sbreak => f7
  | Scontinue => f8
  | Sreturn o => f9 o
  | Sswitch e l => f10 e l (labeled_statements_rect l)
  | Slabel l s0 => f11 l s0 (statement_rect s0)
  | Sgoto l => f12 l
  end
  with labeled_statements_rect (l : labeled_statements) : Q l :=
  match l as l0 return (Q l0) with
  | LSnil => f13
  | LScons o s l0 => f14 o s l0 (statement_rect s) (labeled_statements_rect l0)
  end.
End statement_rect.

(* Equality is decidable on statements *)
Section eq_dec.
  Local Ltac t := hnf; decide equality; auto.

  Let eq_dec_type := type_eq.
  Let eq_dec_float := Float.eq_dec.
  Let eq_dec_float32 := Float32.eq_dec.
  Let eq_dec_int := Int.eq_dec.
  Let eq_dec_int64 := Int64.eq_dec.
  Let eq_dec_ident := ident_eq.
  Let eq_dec_signature := signature_eq.
  Let eq_dec_attr : EqDec attr. repeat t. Defined.
  Let eq_dec_signedness : EqDec signedness. t. Defined.
  Let eq_dec_intsize : EqDec intsize. t. Defined.
  Let eq_dec_floatsize : EqDec floatsize. t. Defined.
  Let eq_dec_Z : EqDec Z. repeat t. Defined.
  Let eq_dec_calling_convention : EqDec calling_convention. repeat t. Defined.
  Lemma eq_dec_external_function : EqDec external_function. repeat t. Defined.
  Let eq_dec_option_ident := Coqlib.option_eq (ident_eq).
  Let eq_dec_option_Z : EqDec (option Z). repeat t. Defined.
  Let eq_dec_typelist : EqDec (list type). repeat t. Defined.

  Lemma eq_dec_expr : EqDec expr.
  Proof. repeat t. Defined.

  Let eq_dec_expr := eq_dec_expr.
  Let eq_dec_option_expr : EqDec (option expr). repeat t. Defined.
  Let eq_dec_list_expr : EqDec (list expr). repeat t. Defined.

  Local Ltac eq_dec a a' :=
    let H := fresh in
    assert (H : {a = a'} + {a <> a'} ) by (auto; repeat (decide equality ; auto));
    destruct H; [subst; auto | try (right; congruence)].

  Lemma eq_dec_statement : forall s s' : statement, { s = s' } + { s <> s' }.
  Proof.
    apply
      (statement_rect
         (fun s => forall s', { s = s' } + { s <> s' } )
         (fun l => forall l', { l = l' } + { l <> l' } ));
      try (intros until s'; destruct s'); intros;
      try (destruct l');
      try solve [right; congruence | left; reflexivity];
      repeat
        match goal with
        | |- context [ ?x ?a          = ?x ?b          ] => eq_dec a b
        | |- context [ ?x ?y ?a       = ?x ?y ?b       ] => eq_dec a b
        | |- context [ ?x ?a _        = ?x ?b _        ] => eq_dec a b
        | |- context [ ?x ?y ?z ?a    = ?x ?y ?z ?b    ] => eq_dec a b
        | |- context [ ?x ?y ?a _     = ?x ?y ?b _     ] => eq_dec a b
        | |- context [ ?x ?a _  _     = ?x ?b _  _     ] => eq_dec a b
        | |- context [ ?x ?y ?z ?t ?a = ?x ?y ?z ?t ?b ] => eq_dec a b
        | |- context [ ?x ?y ?z ?a _  = ?x ?y ?z ?b _  ] => eq_dec a b
        | |- context [ ?x ?y ?a _  _  = ?x ?y ?b _  _  ] => eq_dec a b
        | |- context [ ?x ?a _  _  _  = ?x ?b _  _  _  ] => eq_dec a b
        end.
  Defined.

  Lemma eq_dec_labeled_statements : forall l l' : labeled_statements, { l = l' } + { l <> l' }.
  Proof.
    decide equality.
    apply eq_dec_statement.
  Defined.

End eq_dec.

#[export] Instance EqDec_statement: EqDec statement := eq_dec_statement.
#[export] Instance EqDec_external_function: EqDec external_function := eq_dec_external_function.

Lemma closed_Slabel l c F: closed_wrt_modvars (Slabel l c) F = closed_wrt_modvars c F.
Proof. unfold closed_wrt_modvars. rewrite modifiedvars_Slabel. trivial. Qed.

Lemma closed_Sifthenelse b c1 c2 F: closed_wrt_modvars (Sifthenelse b c1 c2) F <-> closed_wrt_modvars c1 F /\ closed_wrt_modvars c2 F.
Proof.
  unfold closed_wrt_modvars.
  pose proof modifiedvars_Sifthenelse b c1 c2.
  pose proof modifiedvars_computable c1 as TC.
  forget (modifiedvars (Sifthenelse b c1 c2)) as S.
  forget (modifiedvars c1) as S1.
  forget (modifiedvars c2) as S2.
  clear b c1 c2.
  unfold closed_wrt_vars.
  split; [intros; split; intros | intros [? ?]; intros].
  + apply H0.
    intros.
    specialize (H1 i).
    specialize (H i).
    clear - H H1.
    tauto.
  + apply H0.
    intros.
    specialize (H1 i).
    specialize (H i).
    clear - H H1.
    tauto.
  + specialize (TC (te_of rho) te').
    destruct TC as [te'' [? ?]].
    transitivity (F (mkEnviron (ge_of rho) (ve_of rho) te'')).
    - apply H1.
      clear H0 H1.
      intros.
      specialize (H3 i).
      specialize (H i).
      specialize (H2 i).
      specialize (H4 i).
      destruct H2 as [|H0]; [| rewrite -H0 in H4]; tauto.
    - change (mkEnviron (ge_of rho) (ve_of rho) te') with (mkEnviron (ge_of (mkEnviron (ge_of rho) (ve_of rho) te'')) (ve_of (mkEnviron (ge_of rho) (ve_of rho) te'')) te').
      change te'' with (te_of (mkEnviron (ge_of rho) (ve_of rho) te'')) in H3, H4, H2.
      forget (mkEnviron (ge_of rho) (ve_of rho) te'') as rho'.
      apply H0.
      clear H0 H1 H2 H3 H te''.
      intros.
      specialize (H4 i).
      destruct H4; [auto | right; auto].
Qed.

Lemma closed_Sloop c1 c2 F: closed_wrt_modvars (Sloop c1 c2) F <-> closed_wrt_modvars c1 F /\ closed_wrt_modvars c2 F.
Proof.
  unfold closed_wrt_modvars.
  pose proof modifiedvars_Sloop c1 c2.
  pose proof modifiedvars_computable c1 as TC.
  forget (modifiedvars (Sloop c1 c2)) as S.
  forget (modifiedvars c1) as S1.
  forget (modifiedvars c2) as S2.
  clear c1 c2.
  unfold closed_wrt_vars.
  split; [intros; split; intros | intros [? ?]; intros].
  + apply H0.
    intros.
    specialize (H1 i).
    specialize (H i).
    clear - H H1.
    tauto.
  + apply H0.
    intros.
    specialize (H1 i).
    specialize (H i).
    clear - H H1.
    tauto.
  + specialize (TC (te_of rho) te').
    destruct TC as [te'' [? ?]].
    transitivity (F (mkEnviron (ge_of rho) (ve_of rho) te'')).
    - apply H1.
      clear H0 H1.
      intros.
      specialize (H3 i).
      specialize (H i).
      specialize (H2 i).
      specialize (H4 i).
      destruct H2; [| rewrite -H0 in H4]; tauto.
    - change (mkEnviron (ge_of rho) (ve_of rho) te') with (mkEnviron (ge_of (mkEnviron (ge_of rho) (ve_of rho) te'')) (ve_of (mkEnviron (ge_of rho) (ve_of rho) te'')) te').
      change te'' with (te_of (mkEnviron (ge_of rho) (ve_of rho) te'')) in H3, H4, H2.
      forget (mkEnviron (ge_of rho) (ve_of rho) te'') as rho'.
      apply H0.
      clear H0 H1 H2 H3 H te''.
      intros.
      specialize (H4 i).
      destruct H4; [auto | right; auto].
Qed.

Lemma closed_Ssequence c1 c2 F: closed_wrt_modvars (Ssequence c1 c2) F <-> closed_wrt_modvars c1 F /\ closed_wrt_modvars c2 F.
Proof.
  unfold closed_wrt_modvars.
  pose proof modifiedvars_Ssequence c1 c2.
  pose proof modifiedvars_computable c1 as TC.
  forget (modifiedvars (Ssequence c1 c2)) as S.
  forget (modifiedvars c1) as S1.
  forget (modifiedvars c2) as S2.
  clear c1 c2.
  unfold closed_wrt_vars.
  split; [intros; split; intros | intros [? ?]; intros].
  + apply H0.
    intros.
    specialize (H1 i).
    specialize (H i).
    clear - H H1.
    tauto.
  + apply H0.
    intros.
    specialize (H1 i).
    specialize (H i).
    clear - H H1.
    tauto.
  + specialize (TC (te_of rho) te').
    destruct TC as [te'' [? ?]].
    transitivity (F (mkEnviron (ge_of rho) (ve_of rho) te'')).
    - apply H1.
      clear H0 H1.
      intros.
      specialize (H3 i).
      specialize (H i).
      specialize (H2 i).
      specialize (H4 i).
      destruct H2; [| rewrite -H0 in H4]; tauto.
    - change (mkEnviron (ge_of rho) (ve_of rho) te') with (mkEnviron (ge_of (mkEnviron (ge_of rho) (ve_of rho) te'')) (ve_of (mkEnviron (ge_of rho) (ve_of rho) te'')) te').
      change te'' with (te_of (mkEnviron (ge_of rho) (ve_of rho) te'')) in H3, H4, H2.
      forget (mkEnviron (ge_of rho) (ve_of rho) te'') as rho'.
      apply H0.
      clear H0 H1 H2 H3 H te''.
      intros.
      specialize (H4 i).
      destruct H4; [auto | right; auto].
Qed.

Lemma closed_Sswitch e sl F:
  closed_wrt_modvars (Sswitch e sl) F ->
  (forall n, closed_wrt_modvars (seq_of_labeled_statement (select_switch (Int.unsigned n) sl)) F).
Proof.
  intros.
  unfold closed_wrt_modvars, closed_wrt_vars in *.
  intros.
  apply H.
  intros.
  specialize (H0 i); destruct H0; auto.
  left.
  eapply modifiedvars_Sswitch; eauto.
Qed.

Lemma semax_Slabel {cs:compspecs}
       E (Gamma:tycontext) (P:assert) (c:statement) (Q:ret_assert) l:
semax(CS := cs) OK_spec E Gamma P c Q -> semax(CS := cs) OK_spec E Gamma P (Slabel l c) Q.
Proof.
rewrite !semax_unfold; intros.
iIntros "F B" (???) "E P"; iApply wp_label; by iApply (H with "F B [//] E P").
Qed.

Lemma assert_safe_jsafe: forall ge E f ve te c k ora ρ, typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f)) ->
   stack_matches' ge ρ ve te (Some (Kseq c k)) ->
  env_auth ρ ∗ assert_safe OK_spec ge E f (Some (Kseq c k)) ⊢
  jsafeN OK_spec ge E ora (State f c k ve te).
Proof.
  intros; rewrite /assert_safe.
  iIntros "(? & H)"; iApply ("H" with "[$]"); auto.
Qed.

Lemma assert_safe_jsafe': forall ge E f ve te k ora ρ, typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f)) ->
    stack_matches' ge ρ ve te (Some k) ->
  env_auth ρ ∗ assert_safe OK_spec ge E f (Some k) ⊢
  jsafeN OK_spec ge E ora (State f Sskip k ve te).
Proof.
  intros; rewrite /assert_safe.
  iIntros "(? & H)"; iSpecialize ("H" with "[$] [//] [//]").
  destruct k; try iMod "H" as "[]"; try done.
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iApply jsafe_step.
    rewrite /jstep_ex.
    iIntros (m) "? !>".
    iExists _, m; iFrame; iPureIntro; split; auto; constructor.
  - iApply jsafe_step.
    rewrite /jstep.
    iIntros (m) "? !>".
    iExists _, m; iFrame; iPureIntro; split; auto; constructor.
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

End SemaxContext.
