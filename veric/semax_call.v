Require Import Coq.Logic.FunctionalExtensionality.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.semax_conseq.
Import LiftNotation.

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs}.

Lemma tc_environ_make_args':
 forall argsig retsig bl rho Delta
   (Htc : tc_environ Delta rho),
  tc_exprlist Delta (snd (split argsig)) bl rho
  ⊢ ⌜tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig)
         (eval_exprlist (snd (split argsig)) bl rho) rho)⌝.
Proof.
  intros.
  rewrite /tc_environ /tc_exprlist /=.
  revert bl; induction argsig; destruct bl as [ | b bl]; simpl; intros; unfold_lift.
  * iPureIntro; intros _; split3; hnf; try split; intros; try rewrite /funsig_tycontext ?Maps.PTree.gempty // in H |- *.
    destruct H as [? H]; inv H.
  * iPureIntro; done.
  * destruct a as [i ti]; simpl.
    destruct (split argsig) eqn:?; simpl.
    unfold_lift; iPureIntro; inversion 1.
  * destruct a as [i ti]; simpl.
    destruct (split argsig) eqn:?; simpl.
    specialize (IHargsig bl).
    rewrite /typecheck_expr; fold typecheck_expr.
    rewrite !denote_tc_assert_andp.
    unfold_lift.
    rewrite IHargsig; clear IHargsig.
    iIntros "(H & (%Ht & % & %))".
    unfold typecheck_environ; simpl.
    rewrite tc_val_sem_cast //.
    iDestruct "H" as %?%tc_val_tc_val'; iPureIntro.
    split3; auto.
    unfold typecheck_temp_environ; intros ?? Hset.
    destruct (ident_eq i id).
    - subst.
      rewrite Maps.PTree.gss in Hset; inv Hset.
      rewrite lookup_insert; eauto.
    - rewrite lookup_insert_ne //.
      apply (Ht id ty).
      rewrite Maps.PTree.gso // in Hset.
Qed.

(* Scall *)

Definition substopt {A} (ret: option ident) (v: environ -> val) (P: environ -> A)  : environ -> A :=
   match ret with
   | Some id => subst id v P
   | None => P
   end.

Lemma fst_split {T1 T2}: forall vl: list (T1*T2), fst (split vl) = map fst vl.
Proof. induction vl; try destruct a; simpl; auto.
  rewrite <- IHvl; clear IHvl.
 destruct (split vl); simpl in *; auto.
Qed.

Lemma snd_split {T1 T2}: forall vl: list (T1*T2), snd (split vl) = map snd vl.
Proof. induction vl; try destruct a; simpl; auto.
  rewrite <- IHvl; clear IHvl.
 destruct (split vl); simpl in *; auto.
Qed.

Lemma bind_parameter_temps_excludes :
forall l1 l2 t id t1,
~In id (map fst l1) ->
(bind_parameter_temps l1 l2 t) = Some t1 ->
t1 !! id = t !! id.
Proof.
induction l1;
intros.
simpl in *. destruct l2; inv H0. auto.
simpl in H0. destruct a. destruct l2; inv H0.
specialize (IHl1 l2 (Maps.PTree.set i v t) id t1).
simpl in H. intuition. rewrite Maps.PTree.gsspec in H3.
destruct (peq id i). subst; tauto. auto.
Qed.

Lemma pass_params_ni :
  forall  l2
     (te' : temp_env) (id : positive) te l,
   bind_parameter_temps l2 l (te) = Some te' ->
   (In id (map fst l2) -> False) ->
   lookup id (make_env te') = te !! id.
Proof.
intros. eapply bind_parameter_temps_excludes in H; eauto.
by rewrite make_env_spec.
Qed.

Lemma bind_exists_te : forall l1 l2 t1 t2 te,
bind_parameter_temps l1 l2 t1 = Some te ->
exists te2, bind_parameter_temps l1 l2 t2 = Some te2.
Proof.
induction l1; intros.
+ simpl in H. destruct l2; inv H. simpl. eauto.
+ destruct a. simpl in *. destruct l2; inv H. eapply IHl1.
  apply H1.
Qed.


Lemma smaller_temps_exists2 : forall l1 l2 t1 t2 te te2 i,
bind_parameter_temps l1 l2 t1 = Some te ->
bind_parameter_temps l1 l2 t2 = Some te2 ->
t1 !! i = t2 !! i ->
te !! i = te2 !! i.
Proof.
induction l1; intros; simpl in *; try destruct a; destruct l2; inv H.
apply H1.
eapply IHl1; eauto.
repeat rewrite Maps.PTree.gsspec. destruct (peq i i0); auto.
Qed.


Lemma smaller_temps_exists' : forall l l1 te te' id i t,
bind_parameter_temps l l1 (Maps.PTree.set id Vundef t) = Some te ->
i <> id ->
(bind_parameter_temps l l1 t = Some te') -> te' !! i = te !! i.
Proof.
induction l; intros.
- simpl in *. destruct l1; inv H. rewrite Maps.PTree.gso; auto.
- simpl in *. destruct a. destruct l1; inv H.
  eapply smaller_temps_exists2; eauto.
  intros. repeat rewrite Maps.PTree.gsspec. destruct (peq i i0); auto.
  destruct (peq i id). subst. tauto. auto.
Qed.

Lemma smaller_temps_exists'' : forall l l1 te id i t,
bind_parameter_temps l l1 (Maps.PTree.set id Vundef t)=  Some te ->
i <> id ->
exists te', (bind_parameter_temps l l1 t = Some te').
Proof.
intros.
eapply bind_exists_te; eauto.
Qed.

Lemma smaller_temps_exists : forall l l1 te id i t,
bind_parameter_temps l l1 (Maps.PTree.set id Vundef t) = Some te ->
i <> id -> 
exists te', (bind_parameter_temps l l1 t = Some te' /\ te' !! i = te !! i).
Proof.
intros. destruct (smaller_temps_exists'' _ _ _ _ _ _ H H0) as [x ?].
exists x. split. auto.
eapply smaller_temps_exists'; eauto.
Qed.

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with
 | None => True%type
 | Some i => match (temp_types Delta) !! i with Some t' => t=t' | _ => False%type end
 end.

Definition maybe_retval (Q: option val -> mpred) retty ret :=
 assert_of (match ret with
 | Some id => fun rho => ⌜tc_val' retty (eval_id id rho)⌝ ∧ Q (Some (eval_id id rho))
 | None =>
    match retty with
    | Tvoid => (fun rho => Q None)
    | _ => fun rho => ∃ v: val, ⌜tc_val' retty v⌝ ∧ Q (Some v)
    end
 end).

Lemma believe_exists_fundef:
  forall {CS}
    {b : block} {id_fun : ident} {psi : genv} {Delta : tycontext}
    {fspec: funspec}
  (H3: (glob_specs Delta) !! id_fun = Some fspec),
  believe(CS := CS) OK_spec Delta psi ∗ ⎡gvar id_fun b⎤ ⊢
  ⌜∃ f : Clight.fundef,
   Genv.find_funct_ptr (genv_genv psi) b = Some f /\
   type_of_fundef f = type_of_funspec fspec⌝.
Proof.
  intros.
  destruct fspec as [[params retty] cc A E P Q].
  simpl.
  iIntros "(Believe & g)".
  iSpecialize ("Believe" with "[g]").
  { iIntros "!>"; iExists id_fun; iFrame; eauto. }
  iDestruct "Believe" as "[BE|BI]".
  - iStopProof. rewrite -embed_pure; apply embed_mono.
    rewrite /believe_external /=.
    if_tac; last done.
    iIntros "BE".
    destruct (Genv.find_funct_ptr psi b) eqn: Hf; last done.
    iExists _; iSplit; first done.
    destruct f as [ | ef sigargs sigret c'']; first done.
    iDestruct "BE" as ((Es & -> & ASD & _)) "(#? & _)"; inv Es; done.
  - iDestruct "BI" as (b' fu (? & WOB & ? & ? & ? & ? & [=] & ?)) "_"; iPureIntro.
    assert (b' = b) by congruence. subst b'.
    eexists; split; first done; simpl.
    unfold type_of_function; subst; done.
Qed.

(* up to seplog *)
Lemma gvar_agree : forall i b1 b2, ⊢ gvar i b1 -∗ gvar i b2 -∗ ⌜b1 = b2⌝.
Proof.
  intros; iIntros "H1 H2".
  by iDestruct (own_valid_2 with "H1 H2") as %((_ & ?%to_agree_op_inv)%lib.gmap_view.gmap_view_frag_op_valid & _).
Qed.

Lemma tc_vals_length: forall tys vs, tc_vals tys vs -> length tys = length vs.
Proof.
induction tys; destruct vs; simpl; intros; auto; try contradiction.
destruct H; auto.
Qed.

Lemma tc_vals_HaveTyps : forall tys vs, tc_vals tys vs -> argsHaveTyps vs tys.
Proof.
  intros ??; revert tys; induction vs; destruct tys; simpl; try done.
  - constructor.
  - intros (? & ?); constructor; last by apply IHvs.
    intros; by apply tc_val_has_type.
Qed.

Lemma internal_eq_app : forall `{BiInternalEq PROP} (P Q : PROP), ⊢ □ (P ≡ Q) -∗ P -∗ Q.
Proof.
  intros.
  iIntros "H P".
  by iRewrite -"H".
Qed.

Lemma semax_call_si:
  forall E Delta (A: TypeTree) (Ef : dtfr (MaskTT A))
   (P : dtfr (ArgsTT A))
   (Q : dtfr (AssertTT A))
   (x : dtfr A)
   F ret argsig retsig cc a bl
   (Hsub : Ef x ⊆ E) 
   (TCF : Cop.classify_fun (typeof a) = Cop.fun_case_f argsig retsig cc)
   (TC5 : retsig = Tvoid -> ret = None)
   (TC7 : tc_fn_return Delta ret retsig),
  semax OK_spec E Delta
       (▷(tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
           (assert_of (fun rho => func_ptr_si (mk_funspec (argsig,retsig) cc A Ef P Q) (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros.
  rewrite semax_unfold; intros.
  destruct HGG.
  iIntros "E F #B" (f0 (TC' & ?)) "Pre".
  rewrite monPred_at_and monPred_at_sep !monPred_at_later monPred_at_and monPred_at_sep /=.
  iAssert ⎡func_ptr_si (mk_funspec (argsig, retsig) cc A Ef P Q) (eval_expr(CS := CS) a rho)⎤ as "#fp".
  { iDestruct "Pre" as "(_ & $ & _)". }
  iDestruct "fp" as (? Ha ?) "(sub & func)".
  iCombine "sub func F" as "F".
  iDestruct (add_and _ (∃ id, ⎡gvar id b⎤ ∗ ▷ ∃ fA fE fP fQ gP gQ, ⌜(gs = mk_funspec (argsig, retsig) cc fA fE gP gQ) /\ (glob_specs Delta' !! id)%maps = Some (mk_funspec (argsig, retsig) cc fA fE fP fQ)⌝ ∗
    fP ≡ gP ∗ fQ ≡ gQ) with "F") as "(F & % & #g & (% & % & % & % & % & % & >%Hid & #HP & #HQ))".
  { iIntros "(sub & #func & F)".
    destruct gs; iDestruct "F" as "(A & D)"; iDestruct ("D" with "[func]") as (?) "(g & % & %Hfs)".
    { by iExists _, _, _, _. }
    iDestruct ("A" with "[//]") as (?) "(#g' & #f')".
    iDestruct (gvar_agree with "g g'") as %<-.
    iDestruct (func_at_agree with "func f'") as (????????) "H".
    iFrame; iNext.
    iDestruct "H" as (([=] & ->)) "H"; subst.
    iDestruct "sub" as ((-> & ->)) "sub".
    repeat match goal with H : existT _ _ = existT _ _ |- _ => apply inj_pair2 in H end; subst.
    iExists _, _, _, _, _, _; iSplit; first done.
    iDestruct "H" as "(HP & HQ)".
    iRewrite "HP"; iRewrite "HQ"; done. }
  destruct Hid as (-> & Hid).
  iDestruct "F" as "(_ & _ & F)".
  iDestruct "sub" as "(_ & sub)".
  iSpecialize ("B" with "[g]").
  { iIntros "!>"; iExists id; iFrame "g"; eauto. }
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iDestruct "B" as "[BE|BI]".
  - iApply wp_extcall.
    iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
    iSplit; first by rewrite !bi.and_elim_l; auto.
    iIntros "E" (?).
    rewrite /believe_external Ha Genv.find_funct_find_funct_ptr.
    destruct (Genv.find_funct_ptr psi b) as [[|]|] eqn: Hb; try by rewrite embed_pure.
    iDestruct "BE" as (([=] & -> & Hsig & Hinline)) "(BE & TCPost)"; subst.
    iExists _, _, _, _; iSplit; first by iPureIntro; eauto.
    iApply (wp_tc_exprlist(CS := CS) with "E"); [done..|].
    iSplit; first by rewrite bi.and_elim_l bi.and_elim_r; auto.
    rewrite /semax_external.
    iIntros "E" (TCargs) "!>".
    iDestruct "Pre" as "(_ & _ & Frame & Pre)".
    iMod (fupd_mask_subseteq (Ef x)) as "Hclose"; first done.
    iMod ("sub" with "[$Pre]") as (fx F0 ?) "((F0 & Pre) & #Post)".
    { iPureIntro. by split; first apply tc_vals_HaveTyps. }
    iMod (fupd_mask_subseteq (fE fx)) as "Hclose'"; first done.
    iMod ("BE" $! _ _ emp with "[Pre]") as "Hext".
    { iStopProof; split => ?; monPred.unseal.
      rewrite monPred_at_intuitionistically /=; iIntros "(#(_ & _ & _ & HP & _) & Pre)".
      rewrite bi.sep_emp.
      rewrite ofe_morO_equivI; iSpecialize ("HP" $! fx).
      rewrite discrete_fun_equivI; iSpecialize ("HP" $! (eval_exprlist l bl rho)).
      iSplit; last by iApply (internal_eq_app with "[] Pre"); iApply (internal_eq_sym with "HP").
      iPureIntro.
      rewrite Hsig /= map_proj_xtype_argtype.
      forget (eval_exprlist(CS := CS) l bl rho) as args.
      clear - TCargs.
      generalize dependent l; induction args; destruct l; simpl; auto.
      intros (? & ?); split; auto.
      by apply tc_val_has_type. }
    iMod "Hclose'" as "_"; iMod "Hclose" as "_"; iIntros "!>" (??) "Hm".
    iDestruct ("Hext" with "Hm") as (??) "Hext".
    destruct Hinline; last done.
    iExists _; iSplit; first done.
    rewrite Hsig; iIntros "!>" (??? (? & Hretty) ?).
    iMod (fupd_mask_subseteq (fE fx)) as "Hclose"; first by set_solver.
    iMod ("Hext" with "[//]") as "($ & Q & _)".
    iMod "Hclose" as "_"; iIntros "!>".
    simpl in *.
    iDestruct ("TCPost" with "[$Q]") as %TCret.
    { iPureIntro; destruct (rettype_of_type t); done. }
    iClear "HP".
    rewrite ofe_morO_equivI; iSpecialize ("HQ" $! fx).
    rewrite discrete_fun_equivI; iSpecialize ("HQ" $! (make_ext_rval (rettype_of_type t) ret0)).
    iRewrite "HQ" in "Q".
    iPoseProof ("Post" with "[$F0 $Q]") as "Q".
    rewrite /tc_fn_return in TC7; destruct ret; simpl.
    + destruct (temp_types Delta !! i) eqn: Hi; inv TC7.
      iDestruct (curr_env_set_temp with "E") as "($ & E)"; [done..|].
      iIntros "Hi"; iSpecialize ("E" with "Hi"); iFrame.
      assert (exists ret', ret0 = Some ret' /\ tc_val t0 ret') as (v & -> & ?).
      { destruct t0; simpl in TCret; first (by specialize (TC5 eq_refl)); destruct ret0; try done; eauto. }
      iSplit.
      * rewrite monPred_at_exist /maybe_retval.
        apply TC in Hi as (? & ? & ?).
        iExists (eval_id i rho).
        rewrite monPred_at_sep /=. setoid_rewrite subst_set; last done.
        rewrite eval_id_same.
        replace (make_ext_rval _ _) with (Some v).
        2: { destruct t0; try destruct i0, s; try destruct f; try (specialize (TC5 eq_refl)); first done; destruct v; done. }
        iFrame; iPureIntro; by split; first apply tc_val_tc_val'.
      * iPureIntro.
        destruct TS as (TS & _); specialize (TS i). rewrite Hi in TS.
        destruct (temp_types Delta' !! i) eqn: ?; inv TS.
        eapply typecheck_environ_set; eauto.
        apply tc_val_tc_val'; auto.
    + iFrame.
      iSplit; last done.
      rewrite monPred_at_exist; iExists Vundef; rewrite monPred_at_sep /=; iFrame.
      destruct (eq_dec t Tvoid); subst; first done.
      iAssert (⎡∃ v : val, ⌜tc_val' t v⌝ ∧ Q x (Some v)⎤) with "[Q]" as "?"; last by destruct t; iFrame.
      destruct ret0; try by destruct t.
      iExists v; iSplit; first by iPureIntro; apply tc_val_tc_val'; destruct t.
      rewrite /make_ext_rval.
      destruct t; try destruct i, s; try destruct f; try (specialize (TC5 eq_refl)); iFrame; first done; destruct v; contradiction.
  - iApply wp_call.
    iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
    iSplit; first by rewrite !bi.and_elim_l; auto.
    iIntros "E" (?).
    iDestruct "BI" as (?? (Ha' & ? & Hcomplete & ? & ? & Hvars & [=] & <-)) "BI".
    rewrite Ha' in Ha; inv Ha.
    iExists f; iSplit.
    { iPureIntro; exists b; split3; auto; split3; auto.
      { eapply Forall_impl; first apply Hcomplete.
        intros; by apply complete_type_cenv_sub. }
      split3; auto.
      { rewrite /var_sizes_ok !Forall_forall in Hcomplete Hvars |- *.
        intros; rewrite cenv_sub_sizeof //; auto. } }
    iApply (wp_tc_exprlist(CS := CS) with "E"); [done..|].
    iSplit; first by rewrite bi.and_elim_l bi.and_elim_r; auto.
    iIntros "E" (TCargs).
    exploit tc_vals_length; first done; intros Hlen; rewrite -Hlen map_length; iSplit; first done.
    iSpecialize ("BI" $! psi with "[//]").
    iNext.
    iStopProof; split => n; simpl.
    rewrite !monPred_at_sep -assert_of_eq
      monPred_at_big_sepM monPred_at_intuitionistically monPred_at_affinely !monPred_at_and
      !monPred_at_embed monPred_at_pure !monPred_at_internal_eq monPred_at_wand.
    iIntros "(#(sub & func & g & HP & HQ & BI) & Pre & F & E)" (? [=]) "stack".
    rewrite monPred_at_later; iNext.
    rewrite monPred_at_plainly.
    iSpecialize ("BI" $! j); rewrite monPred_at_forall.
    iDestruct "Pre" as "(_ & _ & Frame & Pre)".
    rewrite -fupd_wp monPred_at_fupd.
    iMod (fupd_mask_subseteq (Ef x)) as "Hclose"; first done.
    iMod ("sub" with "[$Pre]") as (fx F0 ?) "((F0 & Pre) & #Post)".
    { iPureIntro. by split; first apply tc_vals_HaveTyps. }
    iSpecialize ("BI" $! fx).
    rewrite monPred_at_wand.
    iSpecialize ("BI" with "[//] [stack Pre]").
    { rewrite /bind_args /close_precondition monPred_at_sep monPred_at_and monPred_at_exist.
      rewrite map_length in Hlen.
      subst; iSplit.
      + rewrite monPred_at_absorbingly /tc_formals monPred_at_exist.
        iExists (eval_exprlist(CS := CS) (type_of_params (fn_params f)) bl rho).
        rewrite monPred_at_and monPred_at_pure !monPred_at_big_sepL2 big_sepL2_fmap_l.
        iDestruct "stack" as "(_ & temps)".
        iDestruct (big_sepL2_app_inv with "temps") as "($ & _)"; first auto.
        iPureIntro; auto.
      + rewrite ofe_morO_equivI; iSpecialize ("HP" $! fx).
        rewrite discrete_fun_equivI; iSpecialize ("HP" $! (eval_exprlist (map snd (fn_params f)) bl rho)).
        iExists _; rewrite monPred_at_and !monPred_at_sep monPred_at_embed monPred_at_pure /type_of_params; subst; iFrame.
        iSplit.
        { iPureIntro.
          clear - TCargs.
          fold (type_of_params (fn_params f)).
          forget (type_of_params (fn_params f)) as tys.
          forget (eval_exprlist tys bl rho) as vals.
          generalize dependent tys; induction vals; destruct tys; try done; simpl.
          intros (? & ?); constructor; eauto.
          intros ->; by apply tc_val_Vundef in H. }
        Fail iRewrite "HP".
        iApply (internal_eq_app with "[] Pre").
        by iApply (internal_eq_sym with "HP"). }
    iMod "Hclose" as "_"; iModIntro.
    subst.
    iApply (monPred_in_entails with "[-]"); first apply wp_mask_mono.
    { by etrans. }
    iApply (monPred_in_entails with "[-]"); first apply wp_strong_mono.
    rewrite monPred_at_sep; iFrame "BI".
    iClear "HP sub"; rewrite /= /Clight_seplog.bind_ret; monPred.unseal.
    iSplit.
    + iIntros (? [=]) "((%Hvoid & Q) & stack)".
      rewrite ofe_morO_equivI; iSpecialize ("HQ" $! fx).
      rewrite discrete_fun_equivI; iSpecialize ("HQ" $! None).
      iRewrite "HQ" in "Q".
      iPoseProof ("Post" with "[$F0 $Q]") as "Q".
      iIntros "!>"; iFrame "stack".
      iSplit; first done.
      specialize (TC5 Hvoid); subst; simpl.
      iFrame.
      iSplitL "Q".
      * iExists Vundef; by rewrite Hvoid.
      * rewrite monPred_at_affinely /=; iSplit; first done.
        rewrite /curr_env /= !monPred_at_sep monPred_at_affinely monPred_at_big_sepM monPred_at_pure -assert_of_eq /=.
        setoid_rewrite monPred_at_embed; done.
    + do 2 (iSplit; first iIntros (??) "([] & ?)").
      iIntros (r ? [=]) "((%Hr & Q) & stack)".
      rewrite ofe_morO_equivI; iSpecialize ("HQ" $! fx).
      rewrite discrete_fun_equivI; iSpecialize ("HQ" $! r).
      iRewrite "HQ" in "Q".
      iPoseProof ("Post" with "[$F0 $Q]") as "Q".
      iIntros "!>"; iFrame "stack".
      iSplit; first done.
      destruct ret; subst; simpl.
      * simpl in TC7.
        destruct (temp_types Delta !! i) eqn: Hi; last done.
        iDestruct (monPred_in_entails with "[E]") as "E"; first by eapply curr_env_set_temp.
        { rewrite /curr_env !monPred_at_sep monPred_at_big_sepM monPred_at_affinely -assert_of_eq; monPred.unseal; done. }
        rewrite monPred_at_sep monPred_at_exist monPred_at_forall; iDestruct "E" as "($ & E)".
        iIntros (??) "Hi".
        iSpecialize ("E" $! (force_val r)); rewrite monPred_at_wand; iSpecialize ("E" with "[//] Hi"); iFrame.
        destruct r; last by specialize (TC5 Hr).
        rewrite monPred_at_affinely /=; iSplit.
        ++ apply TC in Hi as (? & ? & ?).
           iExists (eval_id i rho); setoid_rewrite subst_set; last done.
           rewrite eval_id_same.
           iFrame; iPureIntro; by split; first apply tc_val_tc_val'.
        ++ iPureIntro.
           destruct TS as (TS & _); specialize (TS i). rewrite Hi in TS.
           destruct (temp_types Delta' !! i) eqn: ?; inv TS.
           eapply typecheck_environ_set; eauto.
           apply tc_val_tc_val'; auto.
      * iFrame.
        iSplitL "Q".
        ++ iExists Vundef; destruct r.
           ** destruct (fn_return f); try done; iFrame; iPureIntro; by split; first apply tc_val_tc_val'.
           ** by rewrite Hr.
        ++ rewrite monPred_at_affinely /=; iSplit; first done.
           rewrite /curr_env /= !monPred_at_sep monPred_at_affinely monPred_at_big_sepM monPred_at_pure -assert_of_eq /=.
           setoid_rewrite monPred_at_embed; done.
Qed.

(* We need the explicit frame because it might contain typechecking information. *)
Lemma semax_call:
  forall E Delta (A: TypeTree) (Ef : dtfr (MaskTT A))
  (P : dtfr (ArgsTT A))
  (Q : dtfr (AssertTT A))
  (x : dtfr A)
  F ret argsig retsig cc a bl
  (Hsub : Ef x ⊆ E)
  (TCF : Cop.classify_fun (typeof a) = Cop.fun_case_f argsig retsig cc)
  (TC5 : retsig = Tvoid -> ret = None)
  (TC7 : tc_fn_return Delta ret retsig),
  semax OK_spec E Delta
       ((▷(tc_expr Delta a ∧ tc_exprlist Delta argsig bl))  ∧
           (assert_of (fun rho => func_ptr (mk_funspec (argsig,retsig) cc A Ef P Q) (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros.
  eapply semax_pre, semax_call_si; [|done..].
  iIntros "(_ & ?)"; iStopProof; do 2 f_equiv; last done.
  split => n; apply func_ptr_fun_ptr_si.
Qed.

Definition cast_expropt {CS} (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr(CS := CS) (Ecast e' t))  | None => `None end.

Lemma tc_expropt_char {CS'} Delta e t: tc_expropt (CS := CS') Delta e t =
                                      match e with None => ⌜t=Tvoid⌝
                                              | Some e' => tc_expr(CS := CS') Delta (Ecast e' t)
                                      end.
Proof. reflexivity. Qed.

Lemma RA_return_castexpropt_cenv_sub {CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ ⌜@cast_expropt CS ret t rho = @cast_expropt CS' ret t rho⌝.
Proof.
  rewrite /tc_expropt /tc_expr; destruct ret; simpl.
  + unfold_lift. rewrite /typecheck_expr; fold typecheck_expr.
    rewrite denote_tc_assert_andp (typecheck_expr_sound_cenv_sub CSUB) //.
    iIntros "(-> & _)"; done.
  + iIntros; iPureIntro; done.
Qed.

Lemma tc_expropt_cenv_sub {CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ tc_expropt (CS := CS') Delta ret t rho.
Proof.
  rewrite !tc_expropt_char.
  pose proof (tc_expr_cenv_sub CSUB).
  destruct ret; trivial; auto.
Qed.

Lemma tc_expropt_cspecs_sub {CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ tc_expropt (CS := CS') Delta ret t rho.
Proof.
  destruct CSUB as [CSUB _].
  apply tc_expropt_cenv_sub; done.
Qed.

Lemma tc_expropt_sub {CS'} Delta Delta' rho (TS:tycontext_sub Delta Delta') (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS') Delta ret t rho ⊢ tc_expropt (CS := CS') Delta' ret t rho.
Proof.
  rewrite !tc_expropt_char.
  specialize (tc_expr_sub _ _ _ TS); intros.
  destruct ret; [ eapply H; assumption | trivial].
Qed.

Lemma semax_return:
   forall E Delta R ret,
      semax OK_spec E Delta
                (tc_expropt Delta ret (ret_type Delta) ∧
                             assert_of (`(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ)))
                (Sreturn ret)
                R.
Proof.
  intros.
  rewrite semax_unfold; intros.
  destruct HGG as [CSUB HGG].
  replace (ret_type Delta) with (ret_type Delta')
    by (destruct TS as [_ [_ [? _]]]; auto).
  iIntros "E F #?" (? (TC' & Hret)) "H".
  iApply wp_return.
  rewrite -Hret.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expropt(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite bi.and_elim_l.
  iIntros "E" (?).
  rewrite bi.and_elim_r /=; unfold_lift.
  iFrame; iSplit; last done.
  destruct ret; auto.
Qed.

End mpred.
