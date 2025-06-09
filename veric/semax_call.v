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

(*Lemma semax_call_typecheck_environ:
  forall (Delta : tycontext) (args: list val) (psi : genv)
           m (b : block) (f : function)
     (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
     (H17' : list_norepet (map fst (fn_vars f)))
     (H16 : Genv.find_funct_ptr psi b = Some (Internal f))
     (ve' : env) m' (te' : temp_env)
     (H15 : alloc_variables psi empty_env m (fn_vars f) ve' m')
     (TC5: typecheck_glob_environ psi (glob_types Delta))
     (TC8 : tc_vals (snd (split (fn_params f))) args)
     (H21 : bind_parameter_temps (fn_params f) args
              (create_undef_temps (fn_temps f)) = Some te'),
   typecheck_environ (func_tycontext' f Delta)
      (ge_of psi, ve', te').
Proof.
  intros.
  pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
  split3; auto.
  - unfold typecheck_temp_environ; simpl; intros ?? H.
    apply func_tycontext_t_sound in H; auto.
    clear - H21 H TC8 H17.
    destruct (in_dec (EqDec_prod _ _ _ _) (id, ty) (fn_params f)).
    + forget (create_undef_temps (fn_temps f)) as temps.
      rewrite snd_split in TC8.
      generalize dependent temps. generalize dependent args. generalize dependent te'.
      induction (fn_params f); intros; first done.
      destruct a; simpl in *.
      destruct args; first done.
      destruct TC8 as [TC8' TC8].
      clear H; destruct i as [H | H].
      * inv H.
        rewrite -> (pass_params_ni _ _ id _ _ H21)
           by (inv H17; contradict H1; apply in_app; auto).
        rewrite Maps.PTree.gss.
        apply tc_val_tc_val' in TC8'; eauto.
      * inv H17; eauto.
    + destruct H as [? | H]; first done.
      apply list_norepet_app in H17 as (? & ? & Hdisj).
      rewrite -> (pass_params_ni _ _ id _ _ H21).
      2: { intros; contradiction (Hdisj id id); auto.
          rewrite in_map_iff; exists (id, ty); auto. }
      clear - H; forget (fn_temps f) as temps; induction temps; first done.
      destruct a; simpl in *.
      destruct (eq_dec i id).
      * subst; rewrite Maps.PTree.gss; eauto.
        eexists; split; eauto; apply tc_val'_Vundef.
      * rewrite Maps.PTree.gso //.
        destruct H; [by inv H | eauto].
  - rewrite /typecheck_var_environ /=; intros.
    rewrite (func_tycontext_v_sound (fn_vars f) id ty); auto.
    rewrite /Map.get /make_venv.
    split.
    + intros; eapply alloc_vars_lemma; eauto.
      intros; apply Maps.PTree.gempty.
    + intros (? & H); apply alloc_vars_match_venv in H15.
      rewrite /match_venv /make_venv in H15.
      specialize (H15 id); rewrite H // in H15.
Qed.*)

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
  (Hsub : cenv_sub (@cenv_cs CS) psi)
  (Findb : Genv.find_symbol (genv_genv psi) id_fun = Some b)
  (H3: (glob_specs Delta) !! id_fun = Some fspec),
  believe(CS := CS) OK_spec Delta psi Delta ⊢
  ⌜∃ f : Clight.fundef,
   Genv.find_funct_ptr (genv_genv psi) b = Some f /\
   type_of_fundef f = type_of_funspec fspec /\ forall vals, length vals = length (fst (typesig_of_funspec fspec)) -> fundef_wf psi f vals⌝.
Proof.
  intros.
  destruct fspec as [[params retty] cc A E P Q].
  simpl.
  iIntros "Believe".
  iSpecialize ("Believe" with "[%]").
  { exists id_fun; eauto. }
  iDestruct "Believe" as "[BE|BI]".
  - rewrite /believe_external /=.
    if_tac; last done.
    destruct (Genv.find_funct_ptr psi b) eqn: Hf; last by rewrite embed_pure.
    iExists _; iSplit; first done.
    destruct f as [ | ef sigargs sigret c'']; first by rewrite embed_pure.
    iDestruct "BE" as ((Es & -> & ASD & _)) "(#? & _)"; inv Es; done.
  - iDestruct "BI" as (b' fu (? & WOB & ? & ? & ? & ? & [=] & ?)) "_"; iPureIntro.
    assert (b' = b) by congruence. subst b'.
    eexists; split; first done; simpl.
    unfold type_of_function; subst; split; first done.
    rewrite map_length; intros; intuition.
    + by eapply Forall_impl; last by intros ?; apply complete_type_cenv_sub.
    + pose proof (proj2 (Forall_and _ _) (conj H0 H4)) as Hall.
      eapply Forall_impl; first apply Hall.
      intros ? (? & ?); rewrite cenv_sub_sizeof //.
Qed.

Lemma tc_eval_exprlist:
  forall {CS'} Delta tys bl rho,
    typecheck_environ Delta rho ->
    tc_exprlist(CS := CS') Delta tys bl rho ⊢
    ⌜tc_vals tys (eval_exprlist tys bl rho)⌝.
Proof.
induction tys; destruct bl; simpl in *; intros; auto.
unfold tc_exprlist in *; simpl.
unfold typecheck_expr; fold typecheck_expr.
rewrite !denote_tc_assert_andp IHtys // tc_val_sem_cast //.
unfold_lift; auto.
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

(*Lemma make_args_close_precondition:
  forall bodyparams args ge tx ve' te' (P : list val -> mpred),
    list_norepet (map fst bodyparams) ->
    bind_parameter_temps bodyparams args tx = Some te' ->
    Forall (fun v : val => v <> Vundef) args ->
    P args
   ⊢ close_precondition (map fst bodyparams) P (ge, ve', te').
Proof.
intros *. intros LNR BP VUNDEF.
iIntros "P"; iExists args; iFrame; iPureIntro; repeat (split; auto).
clear - LNR BP VUNDEF.
generalize dependent te'. generalize dependent tx. generalize dependent args.
induction bodyparams; simpl; intros; destruct args; inv BP; simpl; auto.
+ destruct a; discriminate.
+ destruct a. inv LNR. inv VUNDEF. simpl. erewrite <- IHbodyparams by eauto.
  f_equal.
  rewrite (pass_params_ni _ _ _ _ _ H0 H2) Maps.PTree.gss //.
Qed.*)

(* up to extend_tc? *)
Definition globals_auth ge := own(inG0 := envGS_inG) env_name (lib.gmap_view.gmap_view_auth dfrac.DfracDiscarded (to_agree <$> ge), ε).

Lemma curr_env_ge : forall ge f rho, curr_env ge f rho ⊢ curr_env ge f rho ∗
   <affine> ⌜∀ i : ident, Map.get (ge_of rho) i = Genv.find_symbol ge i⌝ ∗ ⎡globals_auth (make_env (Genv.genv_symb ge))⎤.
Proof.
  intros; iIntros "((% & %) & #$ & $)"; auto.
Qed.

Lemma var_blocks_eq : forall {CS} (ge : genv) lv rho
  (Hcomplete : Forall (λ it : ident * type, complete_type (@cenv_cs CS) it.2 = true) lv)
  (Hsub : cenv_sub (@cenv_cs CS) ge)
  (Hlookup : ∀ n i t, (lv !! n)%stdpp = Some (i, t) → ∃ b : block, eval_lvar i t rho = Vptr b Ptrofs.zero),
  ([∗ list] idt ∈ lv, var_block Share.top idt rho) ⊣⊢
  ∃ lb, <affine> ⌜∀ n i t b, (lv !! n)%stdpp = Some (i, t) → (lb !! n)%stdpp = Some b → eval_lvar i t rho = Vptr b Ptrofs.zero⌝ ∗
  ([∗ list] idt;b ∈ lv;lb, memory_block Share.top (@Ctypes.sizeof ge idt.2) (Vptr b Ptrofs.zero)).
Proof.
  induction lv as [|(i, t) lv IH]; simpl; intros.
  - iSplit.
    + iIntros "_"; iExists []; simpl; auto.
    + iIntros "(% & ?)"; destruct lb; simpl; auto.
  - inv Hcomplete.
    rewrite IH // /var_block.
    monPred.unseal; iSplit.
    + iIntros "((% & ?) & % & % & ?)".
      edestruct (Hlookup O) as (b & Heval); first done.
      rewrite Heval -(cenv_sub_sizeof Hsub) //.
      iExists (b :: lb); simpl; iFrame.
      iPureIntro; intros [|]; simpl; eauto.
      inversion 1; inversion 1; subst; done.
    + iIntros "(% & % & H)"; destruct lb; simpl; first iDestruct "H" as "[]".
      rewrite (H O _ _ _ eq_refl eq_refl) /= -(cenv_sub_sizeof Hsub) //.
      iDestruct "H" as "((%Hlt & $) & $)".
      iPureIntro; split.
      * rewrite !Ptrofs.unsigned_zero !Z.add_0_l in Hlt |- *.
        split3; auto; rewrite /Ptrofs.max_unsigned; lia.
      * intros n; apply (H (S n)).
    + intros n; apply (Hlookup (S n)).
Qed.

Lemma stackframe_of_eq : forall {CS : compspecs} (ge : genv) f0 f rho0 k lv n
  (Hcomplete : Forall (λ it : ident * type, complete_type cenv_cs it.2 = true) (fn_vars f))
  (Hsub : cenv_sub cenv_cs ge),
  list_norepet (map fst (fn_vars f)) ->
  list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) ->
  curr_env ge f0 rho0 k ∗ stack_retainer f n ∗ stackframe_of' ge f lv n ⊢ curr_env ge f0 rho0 k ∗ 
  ∃ rho, <affine> ⌜ge_of rho = ge_of rho0 /\ (exists lb, length lb = length (fn_vars f) /\ ve_of rho = (list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))))) /\
    te_of rho = list_to_map (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv)⌝ ∗
  curr_env ge f rho n ∗ stackframe_of f rho.
Proof.
  intros; iIntros "(Hcurr & H)".
  iDestruct (monPred_in_entails with "Hcurr") as "Hcurr"; first by apply curr_env_ge.
  monPred.unseal; rewrite monPred_at_affinely; iDestruct "Hcurr" as "($ & %Hge & Hge)".
  iDestruct (monPred_in_entails with "[H]") as "H"; first by apply stackframe_of_eq'.
  { rewrite monPred_at_sep //. }
  rewrite monPred_at_exist; iDestruct "H" as (lb) "H".
  rewrite /stackframe_of1; monPred.unseal.
  iDestruct "H" as "((%Hlv & stack) & blocks)".
  rewrite monPred_at_big_sepL2.
  iDestruct (big_sepL2_length with "blocks") as %Hlen.
  iExists (ge_of rho0, _, _); iSplit.
  { iPureIntro; simpl; split3; eauto. }
  assert (length (map fst (fn_vars f)) = length (zip lb (map snd (fn_vars f)))) as Heq1.
  { rewrite length_zip_with_l_eq map_length //. }
  assert (length (map fst (fn_params f) ++ map fst (fn_temps f)) = length lv) as Heq2.
  { rewrite !app_length !map_length Hlv //. }
  assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv).*1).
  { rewrite -norepet_NoDup fst_zip //. by rewrite Heq2. }
  assert (NoDup (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))).*1).
  { rewrite -norepet_NoDup fst_zip //. by rewrite Heq1. }
  iSplitL "Hge stack".
  - rewrite /curr_env -assert_of_eq; monPred.unseal; rewrite monPred_at_affinely.
    iSplit; last iFrame.
    { iPureIntro; split; auto.
      rewrite /stack_size.
      destruct (fn_vars f); last done.
      destruct (fn_params f); last done.
      destruct (fn_temps f); done. }
    rewrite !map_size_list_to_map //.
    rewrite !length_zip_with_l_eq // map_length // app_length !map_length.
    rewrite Nat.add_assoc //.
  - rewrite /stackframe_of monPred_at_big_sepL /=.
    rewrite var_blocks_eq //.
    + iExists lb; iFrame; iPureIntro.
      rewrite /eval_lvar /=.
      intros ???? Hn Hb.
      setoid_rewrite elem_of_list_to_map_1; [|try done..].
      2: { rewrite elem_of_zip_gen /=.
           exists n0; rewrite list_lookup_fmap Hn; split; auto.
           rewrite lookup_zip_with Hb /= list_lookup_fmap Hn //. }
      rewrite /= eqb_type_refl //.
    + rewrite /eval_lvar /=.
      intros ??? Hn.
      pose proof (lookup_lt_Some _ _ _ Hn) as Hlt'.
      rewrite Hlen in Hlt'.
      apply lookup_lt_is_Some_2 in Hlt' as (? & Hb).
      setoid_rewrite elem_of_list_to_map_1; [|try done..].
      2: { rewrite elem_of_zip_gen /=.
           exists n0; rewrite list_lookup_fmap Hn; split; auto.
           rewrite lookup_zip_with Hb /= list_lookup_fmap Hn //. }
      eexists; rewrite /= eqb_type_refl //.
Qed.

Lemma make_tycontext_t_sound : forall tys1 tys2 id t, list_norepet (map fst tys1 ++ map fst tys2) ->
  make_tycontext_t tys1 tys2 !! id = Some t <-> In (id, t) (tys1 ++ tys2).
Proof.
  intros; split; first apply make_context_t_get'.
  induction tys1; simpl in *.
  - induction tys2; simpl; first done.
    intros [-> | ?].
    + apply PTree.gss.
    + destruct a; inv H.
      rewrite PTree.gso; auto.
      intros ->.
      contradiction H3; rewrite in_map_iff; eexists (_, _); eauto.
  - intros [-> | ?].
    + apply PTree.gss.
    + destruct a; inv H.
      rewrite PTree.gso; auto.
      intros ->.
      contradiction H3; rewrite -map_app in_map_iff; eexists (_, _); eauto.
Qed.

Lemma stackframe_of_eq' : forall {CS : compspecs} (ge : genv) Delta f rho n
  (Htc : guard_environ (func_tycontext' f Delta) f rho)
  (Hcomplete : Forall (λ it : ident * type, complete_type cenv_cs it.2 = true) (fn_vars f))
  (Hsub : cenv_sub cenv_cs ge),
  list_norepet (map fst (fn_vars f)) ->
  list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) ->
  curr_env ge f rho n ∗ stackframe_of f rho ⊢
  stack_retainer f n ∗ ∃ lv, stackframe_of' ge f lv n.
Proof.
  intros; trans (∃ lv lb, stackframe_of1 ge f lb lv n).
  - rewrite /curr_env /stackframe_of /stackframe_of1 -assert_of_eq /=; monPred.unseal.
    rewrite monPred_at_affinely; iIntros "(((% & %) & _ & stack) & H)".
    set (lv := map (λ '(i, t), force_val (lookup i (te_of rho))) (fn_params f ++ fn_temps f)).
    set (lb := map (λ '(i, t), match lookup i (ve_of rho) with Some (b, _) => b | _ => 1%positive end) (fn_vars f)).
    iExists lv, lb.
    iSplitL "stack".
    + iSplit; first by rewrite map_length app_length.
      assert (length (map fst (fn_vars f)) = length (zip lb (map snd (fn_vars f)))) as Heq1.
      { rewrite length_zip_with_l_eq /lb !map_length //. }
      assert (length (map fst (fn_params f) ++ map fst (fn_temps f)) = length lv) as Heq2.
      { rewrite !app_length /lv !map_length app_length //. }
      assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv).*1).
      { rewrite -norepet_NoDup fst_zip //. by rewrite Heq2. }
      assert (NoDup (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))).*1).
      { rewrite -norepet_NoDup fst_zip //. by rewrite Heq1. }
      iStopProof; f_equiv.
      * rewrite !map_size_list_to_map //.
        rewrite !length_zip_with_l_eq // /lb !map_length // app_length !map_length.
        rewrite Nat.add_assoc //.
      * apply map_eq; intros.
        destruct Htc as ((_ & Htc & _) & _); specialize (Htc i).
        setoid_rewrite make_tycontext_v_sound in Htc; last done.
        destruct (ve_of rho !! i)%stdpp as [(?, ?)|] eqn: Hve; rewrite Hve.
        -- edestruct Htc as (_ & Htc'); spec Htc'; first eauto.
           symmetry; apply elem_of_list_to_map; first done.
           apply elem_of_list_In, elem_of_list_lookup_1 in Htc' as (j & Hi).
           apply elem_of_zip_gen; exists j; rewrite list_lookup_fmap Hi; split; first done.
           rewrite lookup_zip_with /lb !list_lookup_fmap Hi /= Hve //.
        -- symmetry; apply not_elem_of_list_to_map_1.
           intros ((?, ?) & -> & (? & ((?, ?) & ? & Hin%elem_of_list_In)%elem_of_list_lookup_2%elem_of_list_fmap & ?)%elem_of_zip_gen)%elem_of_list_fmap; simpl in *; subst.
           apply Htc in Hin as (? & ?); done.
      * apply map_eq; intros.
        destruct Htc as ((Htc & _) & Hf & _); specialize (Htc i); specialize (Hf i); simpl in *.
        unfold isSome in Hf.
        setoid_rewrite make_tycontext_t_sound in Htc; last done.
        setoid_rewrite make_tycontext_t_sound in Hf; last done.
        destruct (te_of rho !! i)%stdpp eqn: Hte; rewrite Hte.
        -- destruct (Hf _ Hte) as (? & Hi).
           symmetry; apply elem_of_list_to_map; first done.
           apply elem_of_list_In, elem_of_list_lookup_1 in Hi as (j & Hi).
           apply elem_of_zip_gen; exists j; rewrite -map_app list_lookup_fmap Hi; split; first done.
           rewrite /lv list_lookup_fmap Hi /= Hte //.
        -- symmetry; apply not_elem_of_list_to_map_1.
           intros ((?, ?) & -> & (? & Hin%elem_of_list_lookup_2 & ?)%elem_of_zip_gen)%elem_of_list_fmap; simpl in *; subst.
           rewrite -map_app in Hin; apply elem_of_list_fmap in Hin as ((?, ?) & -> & Hin%elem_of_list_In).
           apply Htc in Hin as (? & ? & ?); done.
    + rewrite monPred_at_big_sepL monPred_at_big_sepL2 var_blocks_eq //.
      setoid_rewrite monPred_at_embed.
      iDestruct "H" as (lb1 Hlb1) "H"; simpl.
      iDestruct (big_sepL2_length with "H") as %Hlen.
      assert (lb1 = lb) as ->; last done.
      { eapply list_eq_same_length; eauto; unfold lb.
        { rewrite map_length //. }
        intros ?????.
        rewrite list_lookup_fmap.
        destruct (fn_vars f !! i)%stdpp as [(?, ?)|] eqn: Hf; inversion 1.
        eapply Hlb1 in Hf; last done.
        rewrite /eval_lvar in Hf.
        destruct (ve_of rho !! i0)%stdpp as [(?, ?)|]; last done.
        destruct (eqb_type t t0); inv Hf; done. }
      intros ??? Hf; rewrite /eval_lvar.
      destruct Htc as ((_ & Htc & _) & _).
      specialize (Htc i t); simpl in Htc.
      rewrite make_tycontext_v_sound // in Htc.
      apply elem_of_list_lookup_2, elem_of_list_In, Htc in Hf as (? & ->).
      rewrite eqb_type_refl; eauto.
  - iIntros "(% & % & H)".
    iDestruct (monPred_in_entails with "H") as "H"; first by apply stackframe_of_eq1'.
    rewrite monPred_at_sep; iDestruct "H" as "($ & $)".
Qed.

Lemma stackframe_of'_curr_env : forall {CS : compspecs} (ge : genv) f lv n
  (Hcomplete : Forall (λ it : ident * type, complete_type cenv_cs it.2 = true) (fn_vars f))
  (Hsub : cenv_sub cenv_cs ge),
  list_norepet (map fst (fn_vars f)) ->
  list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) ->
  globals_auth (make_env (Genv.genv_symb ge)) ∗
  stack_retainer f n ∗ stackframe_of' ge f lv n ⊢ ∃ lb, <affine> ⌜length lb = length (fn_vars f)⌝ ∗
  let rho := (Genv.find_symbol ge, list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))),
    list_to_map (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv)) in curr_env ge f rho n ∗ stackframe_of f rho.
Proof.
  intros; trans (globals_auth (make_env (Genv.genv_symb ge)) ∗ ∃ lb, stackframe_of1 ge f lb lv n).
  - iIntros "($ & H)".
    iDestruct (monPred_in_entails with "[H]") as "H"; first by apply lifting.stackframe_of_eq'.
    { rewrite monPred_at_sep; iFrame. }
    by monPred.unseal.
  - iIntros "(Hge & % & H)"; iExists lb.
    rewrite /curr_env /stackframe_of /stackframe_of1 -assert_of_eq /=; monPred.unseal.
    rewrite monPred_at_embed; iFrame "Hge".
    rewrite monPred_at_affinely; iDestruct "H" as "((% & stack) & H)".
    rewrite monPred_at_big_sepL2; iDestruct (big_sepL2_length with "H") as %Hlen; iSplit; first done.
    assert (length (map fst (fn_vars f)) = length (zip lb (map snd (fn_vars f)))) as Heq1.
    { rewrite length_zip_with_l_eq !map_length //. }
    assert (length (map fst (fn_params f) ++ map fst (fn_temps f)) = length lv) as Heq2.
    { rewrite !app_length !map_length //. }
    assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f)) lv).*1).
    { rewrite -norepet_NoDup fst_zip //. by rewrite Heq2. }
    assert (NoDup (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))).*1).
    { rewrite -norepet_NoDup fst_zip //. by rewrite Heq1. }
    iSplitL "stack".
    + iSplit.
      { iPureIntro; split; last by intros.
        unfold stack_size.
        destruct (fn_params f); simpl; last lia.
        destruct (fn_temps f); simpl; last lia; done. }
      iStopProof; f_equiv; try done.
      rewrite !map_size_list_to_map //.
      rewrite !length_zip_with_l_eq // !map_length // app_length !map_length.
      rewrite Nat.add_assoc //.
    + rewrite monPred_at_big_sepL var_blocks_eq // /eval_lvar /=.
      iExists lb; setoid_rewrite monPred_at_embed; iFrame.
      iPureIntro.
      * intros ???? Hn Hb; setoid_rewrite elem_of_list_to_map_1; [|try done..].
        2: { rewrite elem_of_zip_gen /=.
            exists n0; rewrite list_lookup_fmap Hn; split; auto.
            rewrite lookup_zip_with Hb /= list_lookup_fmap Hn //. }
        rewrite /= eqb_type_refl //.
      * intros ??? Hn.
        pose proof (lookup_lt_Some _ _ _ Hn) as Hlt'.
        rewrite Hlen in Hlt'.
        apply lookup_lt_is_Some_2 in Hlt' as (? & Hb).
        setoid_rewrite elem_of_list_to_map_1; [|try done..].
        2: { rewrite elem_of_zip_gen /=.
             exists n0; rewrite list_lookup_fmap Hn; split; auto.
             rewrite lookup_zip_with Hb /= list_lookup_fmap Hn //. }
        eexists; rewrite /= eqb_type_refl //.
Qed.

Lemma tc_vals_Vundef {args ids} (TC:tc_vals ids args): Forall (fun v : val => v <> Vundef) args.
Proof.
generalize dependent ids. induction args; intros. constructor.
destruct ids; simpl in TC. contradiction. destruct TC.
constructor; eauto. intros N; subst. apply (tc_val_Vundef _ H).
Qed.

Lemma tc_vals_lookup {args ids} (TC:tc_vals ids args):
  forall n i v, lookup n ids = Some i -> lookup n args = Some v -> tc_val i v.
Proof.
  generalize dependent ids; induction args; destruct ids; simpl; try done.
  intros (? & ?); destruct n; simpl.
  - inversion 1; inversion 1; by subst.
  - eauto.
Qed.

Lemma repeat_lookup : forall {A} (x : A) m n, lookup n (repeat x m) =
  if decide (n < m)%nat then Some x else None.
Proof.
  induction m; simpl.
  - apply lookup_nil.
  - destruct n; simpl; first done.
    rewrite IHm; repeat if_tac; try done; lia.
Qed.

Lemma bind_ret_eq : forall vl t Q, bind_ret vl t Q ⊣⊢
  <affine> ⌜match vl with Some v => tc_val t v | None => t = Tvoid end⌝ ∗ ⎡Q vl⎤.
Proof.
  intros; rewrite /bind_ret; destruct vl; simpl.
  - iSplit; iIntros "($ & $)".
  - destruct t; [|rewrite bi.pure_False // bi.affinely_False bi.sep_False //..].
    rewrite bi.pure_True // bi.affinely_True_emp bi.emp_sep //.
Qed.

(*Lemma semax_call_aux0 {CS'}
  E (Delta : tycontext) (psi : genv) (ora : OK_ty) (b : block) (id : ident) cc
  A0 P (x : dtfr A0) A nE deltaP deltaQ retty clientparams
  (F0 : assert) F (ret : option ident) (curf: function) args
  (R : ret_assert) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)

  (Spec: (glob_specs Delta)!!id = Some (mk_funspec (clientparams, retty) cc A nE deltaP deltaQ))
  (FindSymb: Genv.find_symbol psi id = Some b)
  (TCRet: tc_fn_return Delta ret retty)
  (GuardEnv: guard_environ Delta curf rho)
  (Hretty: retty=Tvoid -> ret=None)
  (Closed: closed_wrt_vars (thisvar ret) F0)
  (CSUB: cenv_sub (@cenv_cs CS') (genv_cenv psi))
  (Hrho: rho = construct_rho (filter_genv psi) vx tx)
  (ff : Clight.fundef) (H16 : Genv.find_funct psi (Vptr b Ptrofs.zero) = Some ff)
  (H16' : type_of_fundef ff = type_of_funspec (mk_funspec (clientparams, retty) cc A nE deltaP deltaQ))
  (TC8 : tc_vals clientparams args)
  ctl (Hcont : call_cont ctl = ctl)
  (Hctl : ∀ ret0 z', assert_safe OK_spec psi E curf vx (set_opttemp ret (force_val ret0) tx)
             (exit_cont EK_normal None k)  (construct_rho (filter_genv psi) vx (set_opttemp ret (force_val ret0) tx)) ⊢
    jsafeN OK_spec psi E z' (Returnstate (force_val ret0) ctl)):
  □ believe OK_spec Delta psi Delta -∗
  ▷ (F0 rho ∗ F rho ∗ P x (ge_of rho, args) -∗
     funassert Delta rho -∗
     □ ■ (F rho ∗ P x (ge_of rho, args) ={E}=∗
                          ∃ (x1 : dtfr A) (F1 : assert),
                            ⌜nE x1 ⊆ E⌝ ∧ (F1 rho ∗ deltaP x1 (ge_of rho, args))
                            ∧ (∀ rho' : environ,
                                 ■ ((∃ old:val, substopt ret (`old) F1 rho' ∗ maybe_retval (assert_of (deltaQ x1)) retty ret rho') -∗
                                    RA_normal R rho'))) -∗
  <affine> rguard OK_spec psi E Delta curf (frame_ret_assert R F0) k -∗
  jsafeN OK_spec psi E ora (Callstate ff args ctl)).
Proof.
Qed.*)

Lemma make_te_lookup : forall (params : list (ident * type)) l args lv (te : tenviron)
  (Hnodup : NoDup (zip (map fst params ++ l) (args ++ lv)).*1)
  (Hlen : length params = length args)
  (Hte : te = list_to_map (zip (map fst params ++ l) (args ++ lv)))
  n i t (Hn : lookup n params = Some (i, t)),
  exists v, lookup n args = Some v /\ lookup i te = Some v.
Proof.
  intros.
  pose proof (lookup_lt_Some _ _ _ Hn) as Hlt.
  rewrite Hlen in Hlt.
  apply lookup_lt_is_Some_2 in Hlt as (? & ?).
  eexists; split; first done.
  rewrite Hte.
  apply elem_of_list_to_map; first done.
  apply elem_of_zip_gen.
  exists n; erewrite !lookup_app_l_Some; try done.
  rewrite list_lookup_fmap Hn //.
Qed.

Lemma make_env_guard_environ : forall Delta f args lb rho
  (Hparams : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
  (Hvars : list_norepet (map fst (fn_vars f)))
  (Hlb : length lb = length (fn_vars f))
  (Htc : tc_vals (map snd (fn_params f)) args)
  (Hge : typecheck_glob_environ (ge_of rho) (glob_types Delta))
  (Hve : ve_of rho = list_to_map (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))))
  (Hte : te_of rho = list_to_map (zip (map fst (fn_params f) ++ map fst (fn_temps f))
            (args ++ repeat Vundef (length (fn_temps f))))),
  guard_environ (func_tycontext' f Delta) f rho.
Proof.
  intros; pose proof (tc_vals_length _ _ Htc) as Hlen; rewrite map_length in Hlen.
  assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f))
    (args ++ repeat Vundef (length (fn_temps f)))).*1).
  { rewrite -norepet_NoDup fst_zip //.
    rewrite !app_length !map_length Hlen repeat_length //. }
  split3; last done.
  split3; try done.
  + intros ?? Hi%make_context_t_get'.
    apply in_app_iff in Hi as [Hi | Hi].
    * apply elem_of_list_In, elem_of_list_lookup_1 in Hi as (? & Hi).
      edestruct make_te_lookup as (? & ? & ->); [done..|].
      eexists; split; first done.
      eapply tc_val_tc_val', tc_vals_lookup; eauto.
      rewrite list_lookup_fmap Hi //.
    * apply elem_of_list_In, elem_of_list_lookup_1 in Hi as (i & Hi).
      pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
      exists Vundef; split; last by intros ?.
      rewrite Hte; apply elem_of_list_to_map; first done.
      apply elem_of_zip_gen.
      exists (length (fn_params f) + i)%nat.
      rewrite !lookup_app_r; rewrite -?Hlen ?map_length; try lia.
      rewrite !Nat.add_sub' list_lookup_fmap Hi; split; first done.
      rewrite repeat_lookup if_true //.
  + intros ??; rewrite make_tycontext_v_sound //.
    assert (NoDup (zip (map fst (fn_vars f)) (zip lb (map snd (fn_vars f)))).*1).
    { rewrite -norepet_NoDup fst_zip // length_zip_with_l_eq map_length //; lia. }
    rewrite Hve; split.
    * intros Hi.
      apply elem_of_list_In, elem_of_list_lookup_1 in Hi as (i & Hi).
      pose proof (lookup_lt_Some _ _ _ Hi) as Hb.
      rewrite -Hlb in Hb; apply lookup_lt_is_Some_2 in Hb as (? & Hb).
      eexists; apply elem_of_list_to_map; first done.
      apply elem_of_zip_gen.
      exists i; rewrite lookup_zip_with Hb /= !list_lookup_fmap Hi //.
    * intros (? & Hi%elem_of_list_to_map); last done.
      apply elem_of_zip_gen in Hi as (i & Hi & Hb).
      rewrite lookup_zip_with in Hb; apply bind_Some in Hb as (? & ? & Hb).
      rewrite !list_lookup_fmap in Hi Hb.
      apply bind_Some in Hb as (? & Hb & [=]); subst.
      apply elem_of_list_In, (elem_of_list_lookup_2 _ i).
      destruct (lookup i (fn_vars f)) as [(?, ?)|] eqn: Hl; inv Hi; inv Hb; done.
  + rewrite Hte /=.
    setoid_rewrite make_tycontext_t_sound; last done.
    intros ?? Hi%elem_of_list_to_map; last done.
    apply elem_of_zip_gen in Hi as (? & Hi%elem_of_list_lookup_2%elem_of_list_In & _).
    rewrite -map_app in Hi; apply in_map_iff in Hi as ((?, ?) & [=] & ?); subst; eauto.
Qed.

Lemma make_te_lookup_args : forall (params : list (ident * type)) l args lv (te : tenviron)
  (Hnodup : NoDup (zip (map fst params ++ l) (args ++ lv)).*1)
  (Hlen : length params = length args)
  (Hte : te = list_to_map (zip (map fst params ++ l) (args ++ lv))),
  map (λ i : ident, (te !! i)%stdpp) (map fst params) =
  map Some args.
Proof.
  intros; rewrite map_map; eapply list_eq_same_length; eauto.
  { rewrite !map_length //. }
  intros ????.
  rewrite !list_lookup_fmap; destruct (lookup i params) as [(?, ?)|] eqn: Hi; inversion 1; subst.
  eapply make_te_lookup in Hi as (? & He & ->); [|done..].
  rewrite He; inversion 1; done.
Qed.

Lemma tc_formals_args : forall params l lv args rho
  (Hnodup : NoDup (zip (map fst params ++ l) (args ++ lv)).*1)
  (H : tc_vals (map snd params) args)
  (Hrho : te_of rho = list_to_map (zip (map fst params ++ l) (args ++ lv))),
  tc_formals params rho.
Proof.
  intros; rewrite /tc_formals.
  match goal with H: tc_vals _ ?A |- tc_vals _ ?B => replace B with A; auto end.
  assert (length params = length args).
  { apply tc_vals_length in H; rewrite map_length // in H. }
  eapply list_eq_same_length; eauto.
  { rewrite map_length //. }
  intros ?????.
  rewrite list_lookup_fmap; destruct (lookup i params) as [(?, ?)|] eqn: Hi; inversion 1; subst.
  rewrite /eval_id.
  eapply make_te_lookup in Hi as (? & ? & ->); [|done..]; simpl; congruence.
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
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros.
  rewrite semax_unfold; intros.
  destruct HGG.
  iIntros "F #B" (f0 ? (TC' & ?)) "E Pre".
  rewrite monPred_at_and monPred_at_sep !monPred_at_later monPred_at_and monPred_at_sep /=.
  iAssert ⎡func_ptr_si (mk_funspec (argsig, retsig) cc A Ef P Q) (eval_expr(CS := CS) a rho)⎤ as "#fp".
  { iDestruct "Pre" as "(_ & $ & _)". }
  iDestruct "fp" as (? Ha ?) "(sub & func)".
  iCombine "sub func F" as "F".
  iDestruct (add_and _ (∃ id, <affine> ⌜Genv.find_symbol psi id = Some b⌝ ∗ ▷ ∃ fA fE fP fQ gP gQ, ⌜(gs = mk_funspec (argsig, retsig) cc fA fE gP gQ) /\ (glob_specs Delta' !! id)%maps = Some (mk_funspec (argsig, retsig) cc fA fE fP fQ)⌝ ∗
    fP ≡ gP ∗ fQ ≡ gQ) with "F") as "(F & % & %g & (% & % & % & % & % & % & >%Hid & #HP & #HQ))".
  { iIntros "(sub & #func & F)".
    destruct gs; iDestruct "F" as "(A & D)"; iDestruct ("D" with "[func]") as (?) "(%g & % & %Hfs)".
    { by iExists _, _, _, _. }
    iDestruct ("A" with "[//]") as (?) "(%g' & #f')".
    rewrite g' in g; inv g.
    iDestruct (func_at_agree with "func f'") as (????????) "H".
    iExists _; iSplit; first done; iNext.
    iDestruct "H" as (([=] & ->)) "H"; subst.
    iDestruct "sub" as ((-> & ->)) "sub".
    repeat match goal with H : existT _ _ = existT _ _ |- _ => apply inj_pair2 in H end; subst.
    iExists _, _, _, _, _, _; iSplit; first done.
    iDestruct "H" as "(HP & HQ)".
    iRewrite "HP"; iRewrite "HQ"; done. }
  destruct Hid as (-> & Hid).
  iDestruct "F" as "(_ & _ & F)".
  iDestruct "sub" as "(_ & sub)".
  iPoseProof ("B" with "[%]") as "B'".
  { exists id; eauto. }
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply wp_call.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite !bi.and_elim_l; auto.
  iIntros "E" (?).
  iExists _, _, _; iSplit; first done.
  iApply (wp_tc_exprlist(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite bi.and_elim_l bi.and_elim_r; auto.
  iIntros "E" (TCargs Hlen).
  iDestruct "B'" as "[BE|BI]".
  - rewrite /believe_external Ha Genv.find_funct_find_funct_ptr.
    destruct (Genv.find_funct_ptr psi b) as [[|]|] eqn: Hb; try by rewrite embed_pure.
    iDestruct "BE" as (([=] & -> & Hsig & Hinline)) "(BE & TCPost)"; subst.
    iExists _; iSplit; first iPureIntro.
    { eexists; split; first done; split3; eauto; done. }
    rewrite /= /semax_external /external_call_assert.
    iNext.
    iDestruct "Pre" as "(_ & _ & Frame & Pre)".
    iMod (fupd_mask_subseteq (Ef x)) as "Hclose"; first done.
    iMod ("sub" with "[$Pre]") as (fx F0 ?) "((F0 & Pre) & #Post)".
    { iPureIntro. by split; first apply tc_vals_HaveTyps. }
    iMod (fupd_mask_subseteq (fE fx)) as "Hclose'"; first done.
    iDestruct (curr_env_ge_eq with "E") as %Hpsi.
    iMod ("BE" $! psi _ emp with "[Pre]") as "Hext".
    { iStopProof; split => ?; monPred.unseal.
      rewrite monPred_at_intuitionistically /=; iIntros "(#(_ & _ & _ & HP & _) & Pre)".
      rewrite bi.sep_emp -Hpsi.
      rewrite ofe_morO_equivI; iSpecialize ("HP" $! fx).
      rewrite discrete_fun_equivI; iSpecialize ("HP" $! (ge_of rho, eval_exprlist l bl rho)).
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
        eapply guard_environ_put_te'; eauto; first by split.
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
  - iDestruct "BI" as (?? (Ha' & ? & Hcomplete & ? & ? & Hvars & [=] & <-)) "BI".
    rewrite Ha' in Ha; inv Ha.
    iExists _; iSplit.
    { iPureIntro; exists b; split3; eauto; split3; auto.
      { eapply Forall_impl; first apply Hcomplete.
        intros; by apply complete_type_cenv_sub. }
      split3; auto; split.
      { rewrite /var_sizes_ok !Forall_forall in Hcomplete Hvars |- *.
        intros; rewrite cenv_sub_sizeof //; auto. }
      { rewrite Hlen map_length //. } }
    iSpecialize ("BI" with "[%] [%]").
    { intros; apply tycontext_sub_refl. }
    { apply cenv_sub_refl. }
    iNext.
    rewrite /= /internal_call_assert.
    iStopProof; split => n; simpl.
    rewrite !monPred_at_sep -assert_of_eq
      monPred_at_intuitionistically monPred_at_affinely !monPred_at_and
      !monPred_at_embed monPred_at_pure !monPred_at_internal_eq monPred_at_wand monPred_at_forall.
    iIntros "(#(B & sub & func & HP & HQ & BI) & Pre & F & E)" (? [=]) "stack0".
    rewrite monPred_at_wand.
    iIntros (? [=]) "stack".
    rewrite monPred_at_later; iNext.
    iDestruct "Pre" as "(_ & _ & Frame & Pre)".
    rewrite -fupd_wp monPred_at_fupd.
    iMod (fupd_mask_subseteq (Ef x)) as "Hclose"; first done.
    iMod ("sub" with "[$Pre]") as (fx F0 ?) "((F0 & Pre) & #Post)".
    { iPureIntro. by split; first apply tc_vals_HaveTyps. }
    iSpecialize ("BI" $! fx).
    rewrite semax_fold_unfold; monPred.unseal.
    iSpecialize ("BI" with "[//] [%]").
    { split3; eauto; [apply tycontext_sub_refl | apply cenv_sub_refl]. }
    subst; iDestruct (stackframe_of_eq with "[E stack0 stack]") as "(E & % & %Hrho & E' & stack)"; [done..| |].
    { iFrame.
      rewrite /curr_env; monPred.unseal.
      rewrite monPred_at_affinely -assert_of_eq; iFrame. }
    iSpecialize ("BI" $! (S n) with "[//] F [//] [B] [//]").
    { rewrite -(plain_plainly (believe _ _ _ _)) !monPred_at_plainly //. }
    assert (NoDup (zip (map fst (fn_params f) ++ map fst (fn_temps f))
        (eval_exprlist(CS := CS) (type_of_params (fn_params f)) bl rho ++ repeat Vundef (length (fn_temps f)))).*1).
    { rewrite -norepet_NoDup fst_zip //.
      rewrite map_length in Hlen; rewrite !app_length !map_length Hlen repeat_length //. }
    assert (forall n i t, lookup n (fn_params f) = Some (i, t) ->
        exists v, lookup n (eval_exprlist(CS := CS) (type_of_params (fn_params f)) bl rho) = Some v /\
          lookup i (te_of rho0) = Some v) as Hte.
    { destruct Hrho as (_ & _ & ?); eapply make_te_lookup; eauto.
      rewrite map_length // in Hlen. }
    iSpecialize ("BI" with "[] [//] E'").
    { destruct Hrho as (Hge0 & (lb & Hlb & Hve0) & Hte0).
      rewrite monPred_at_affinely; iPureIntro; eapply make_env_guard_environ; eauto.
      rewrite Hge0; apply TC'. }
    iSpecialize ("BI" with "[//] [stack Pre]").
    { iFrame.
      rewrite /bind_args monPred_at_and /=; iSplit.
      + iPureIntro.
        eapply tc_formals_args; eauto; apply Hrho.
      + rewrite ofe_morO_equivI; iSpecialize ("HP" $! fx).
        rewrite discrete_fun_equivI; iSpecialize ("HP" $! (ge_of rho, eval_exprlist (map snd (fn_params f)) bl rho)).
        Fail iRewrite -"HP" in "Pre".
        iPoseProof (internal_eq_app with "[HP] Pre") as "Pre".
        { by iApply (internal_eq_sym with "HP"). }
        replace (ge_of rho) with (ge_of rho0) by apply Hrho.
        iFrame; iPureIntro.
        split; last done; split.
        * eapply make_te_lookup_args; eauto; last apply Hrho.
          rewrite map_length // in Hlen.
        * by eapply tc_vals_Vundef. }
    iMod "Hclose" as "_"; iModIntro.
    subst.
    iApply (monPred_in_entails with "[-]"); first apply wp_mask_mono.
    { by etrans. }
    iApply (monPred_in_entails with "[-]"); first apply wp_strong_mono.
    rewrite monPred_at_sep; iFrame "BI".
    iClear "HP sub"; rewrite /= /Clight_seplog.bind_ret; monPred.unseal.
    iSplit.
    + iIntros (? [=]) "((%rho' & (Q & stack) & Htc & E') & F)".
      rewrite monPred_at_affinely; iDestruct "Htc" as %Htc.
      destruct (fn_return f) eqn: Hret; [|done..].
      simpl.
      rewrite ofe_morO_equivI; iSpecialize ("HQ" $! fx).
      rewrite discrete_fun_equivI; iSpecialize ("HQ" $! None).
      iRewrite "HQ" in "Q".
      iPoseProof ("Post" with "[$F0 $Q]") as "Q".
      iIntros "!>".
      iDestruct (stackframe_of_eq' with "[$E' $stack]") as "$"; [done..|].
      iSplit; first done.
      specialize (TC5 eq_refl); subst; simpl.
      iFrame.
      iSplit; first by iExists Vundef.
      rewrite monPred_at_affinely //.
    + do 2 (iSplit; first iIntros (??) "((% & ([] & ?) & ?) & ?)").
      iIntros (r ? [=]) "((%rho' & (Q & stack) & Htc & E') & F)".
      rewrite monPred_at_affinely; iDestruct "Htc" as %Htc.
      rewrite bind_ret_eq; monPred.unseal; rewrite monPred_at_affinely. iDestruct "Q" as (Hr) "Q".
      rewrite ofe_morO_equivI; iSpecialize ("HQ" $! fx).
      rewrite discrete_fun_equivI; iSpecialize ("HQ" $! r).
      iRewrite "HQ" in "Q".
      iPoseProof ("Post" with "[$F0 $Q]") as "Q".
      iDestruct (stackframe_of_eq' with "[$E' $stack]") as "$"; [done..|].
      iIntros "!>"; iSplit; first done.
      destruct ret; subst; simpl.
      * simpl in TC7.
        destruct (temp_types Delta !! i) eqn: Hi; last done.
        iDestruct (monPred_in_entails with "E") as "E"; first by eapply curr_env_set_temp.
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
           eapply guard_environ_put_te'; eauto; first by split.
           apply tc_val_tc_val'; auto.
      * iFrame.
        iSplitL "Q".
        ++ iExists Vundef; destruct r.
           ** destruct (fn_return f); try done; iFrame; iPureIntro; by split; first apply tc_val_tc_val'.
           ** by rewrite Hr.
        ++ rewrite monPred_at_affinely //.
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
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
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
  iIntros "F #?" (?? (TC' & ? & Hret)) "E H".
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
