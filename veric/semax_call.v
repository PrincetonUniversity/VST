Require Import Coq.Logic.FunctionalExtensionality.
Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
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
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.
Import LiftNotation.
Local Open Scope pred.

Lemma TTL3 l: typelist_of_type_list (Clight_core.typelist2list l) = l.
Proof. induction l; simpl; trivial. f_equal; trivial . Qed.

Lemma age_later {A} {agA : ageable A}: forall {w w1 w2} (AGE: age w w1) (L: laterR w w2), w1=w2 \/ laterR w1 w2.
Proof. intros. induction L.
+ unfold age in *. rewrite AGE in H. left; inv H; trivial.
+ right. destruct (IHL1 AGE); subst. apply L2. eapply t_trans; eassumption.
Qed.

Lemma tc_val_sem_cast':
  forall {cs: compspecs} t2 e2 rho Delta,
      @typecheck_environ Delta rho ->
      @denote_tc_assert cs (@typecheck_expr cs Delta e2) rho
     &&  @denote_tc_assert cs (@isCastResultType cs (typeof e2) t2  e2) rho 
     |-- !! @tc_val t2 (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))).
Proof.
intros.
intro phi.
intros [? ?].
eapply expr_lemmas.tc_val_sem_cast; eauto.
Qed.

Lemma typecheck_expr_sound' {cs: compspecs} :
  forall Delta rho e,
    @typecheck_environ Delta rho ->
    @tc_expr cs Delta e rho |-- !! @tc_val (typeof e) (eval_expr e rho).
Proof.
intros.
intros ? ?.
simpl.
eapply expr_lemmas4.typecheck_expr_sound; eauto.
Qed.

Lemma tc_environ_make_args':
 forall {CS: compspecs} argsig retsig bl rho Delta,
   tc_environ Delta rho ->
  tc_exprlist Delta (snd (split argsig)) bl rho
  |-- !! tc_environ (funsig_tycontext (argsig, retsig)) (make_args (map fst argsig)
         (eval_exprlist (snd (split argsig)) bl rho) rho).
Proof.
intros. rename H into H2.
unfold tc_environ.
simpl.
unfold tc_exprlist.
revert bl; induction argsig; destruct bl as [ | b bl]; simpl; intros; unfold_lift.
* hnf; intros. clear H.
  split3; hnf; intros; try (simpl in *; rewrite PTree.gempty in H; inv H).
  rewrite PTree.gempty. split; intro. inv H. destruct H. inv H.
* apply prop_derives; intros. inv H.
* destruct a as [i ti]; simpl.
  destruct (split argsig) eqn:?.
  simpl.
  unfold_lift; apply prop_derives; intros; inv H.
* destruct a as [i ti]; simpl.
  destruct (split argsig) eqn:?.
  specialize (IHargsig bl).
  simpl denote_tc_assert.
  rewrite !denote_tc_assert_andp.
  simpl andp.
  unfold_lift.
  apply derives_trans with
   (denote_tc_assert (typecheck_expr Delta b) rho &&
   denote_tc_assert (isCastResultType (typeof b) ti b) rho &&
   (!! typecheck_environ (funsig_tycontext (argsig, retsig))
                    (make_args (map fst argsig)
                       (eval_exprlist l0 bl rho) rho))).
  apply andp_derives; auto.
  clear IHargsig.
  simpl. unfold_lift.
  normalize.
  destruct H as [? [? ?]].
  unfold typecheck_environ; simpl.
  match goal with |- ?A |-- ?B => apply derives_trans with
      (!! tc_val' ti (force_val (sem_cast (typeof b) ti (eval_expr b rho))) && A)
  end.
  + apply andp_right; auto.
    clear - H2.
    apply derives_trans with (!! (tc_val (typeof b) (eval_expr b rho)) &&
     !! (tc_val ti (force_val (sem_cast (typeof b) ti (eval_expr b rho))))).
    - apply andp_right.
      eapply derives_trans; [ | eapply typecheck_expr_sound']; eauto.
      apply andp_left1. apply derives_refl.
      pose proof expr_lemmas.tc_val_sem_cast.
      apply tc_val_sem_cast'; auto.
    - apply andp_left2.
      apply prop_derives.
      unfold tc_val'.
      intros; auto.
  + normalize. rename H3 into H8.
    hnf; intros. simpl.
    split3; auto.
    unfold typecheck_temp_environ; intros.
    destruct (ident_eq i id).
    - subst.
      rewrite PTree.gss in H4. inv H4.
      rewrite Map.gss.
      eexists; split; eauto.
    - rewrite Map.gso by auto.
      apply (H id ty).
      rewrite PTree.gso in H4 by auto.
      simpl. auto.
Qed.

(* Scall *)

Lemma age_twin' {A B} `{HA: ageable A} `{HB: ageable B}:
  forall (x: A) (y: B) (x': A),
       level x = level y -> age x x' ->
       exists y', level x' = level y' /\ age y y'.
Proof.
intros x y x' H0 H1.
unfold fashionR in *.
destruct (age1_levelS _ _ H1) as [n ?].
rewrite H0 in H.
destruct (levelS_age1 _ _ H) as [y' ?].
exists y'; split.
apply age_level in H2.
apply age_level in H1.
congruence.
auto.
Qed.

Lemma later_twin' {A B} `{HA: ageable A} `{HB: ageable B}:
  forall (x: A) (y: B) (x': A),
       level x = level y -> laterR x x' ->
       exists y', level x' = level y' /\ laterR y y'.
Proof.
intros x y x' H0 H1.
revert y H0; induction H1; intros.
destruct (age_twin' _ _ _ H0 H) as [y' [? ?]].
exists y'; split; auto.
specialize (IHclos_trans1 _ H0).
destruct IHclos_trans1 as [y2 [? ?]].
specialize (IHclos_trans2 _ H).
destruct IHclos_trans2 as [u [? ?]].
exists u; split; auto.
apply t_trans with y2; auto.
Qed.

Lemma later_twin {A} `{ageable A}:
   forall phi1 phi2 phi1',
     level phi1 = level phi2 ->
     laterR phi1 phi1' ->
     exists phi2', level phi1' = level phi2' /\ laterR phi2 phi2'.
Proof.
intros.
eapply later_twin'; eauto.
Qed.

Lemma someP_inj:  forall A P Q, SomeP A P = SomeP A Q -> P=Q.
Proof. intros. injection H; intro. apply inj_pair2 in H0. auto. Qed.

Lemma function_pointer_aux:
  forall A P P' Q Q' (w: rmap),
    args_super_non_expansive P ->
    super_non_expansive Q ->
    args_super_non_expansive P' ->
    super_non_expansive Q' ->
   SomeP (SpecArgsTT A) (fmap (fpi _) (approx (level w)) (approx (level w)) (packPQ P Q)) =
   SomeP (SpecArgsTT A) (fmap (fpi _) (approx (level w)) (approx (level w)) (packPQ P' Q')) ->
   ( (forall ts x vl, (! |> (P' ts x vl <=> P ts x vl)) w) /\
     (forall ts x vl, (! |> (Q' ts x vl <=> Q ts x vl)) w)).
Proof.
  intros ? ? ? ? ? ? NEP NEQ NEP' NEQ' H.
  apply someP_inj in H.
  unfold packPQ in H; simpl in H.
  split; intros.
  + apply equal_f_dep with ts in H.
    apply equal_f with x in H.
    apply equal_f_dep with true in H.
    apply equal_f with vl in H.
    simpl in H.
    rewrite @later_fash; auto with typeclass_instances.
    intros ? ? m' ?.
    assert (forall m'', necR m' m'' -> (level m'' < level w)%nat).
    {
      intros.
      clear - H0 H1 H2; hnf in H1.
      apply laterR_level in H1.
      apply necR_level in H2; simpl in *.
      lia.
    }
    split; intros m'' ? ?.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEP.
      apply H.
      rewrite <- NEP'.
      apply approx_lt; auto.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEP'.
      apply H.
      rewrite <- NEP.
      apply approx_lt; auto.
  + apply equal_f_dep with ts in H.
    apply equal_f with x in H.
    apply equal_f_dep with false in H.
    apply equal_f with vl in H.
    simpl in H.
    rewrite @later_fash; auto with typeclass_instances; intros ? ? m' ?.
    assert (forall m'', necR m' m'' -> (level m'' < level w)%nat).
    {
      intros.
      clear - H0 H1 H2; hnf in H1.
      apply laterR_level in H1.
      apply necR_level in H2; simpl in *.
      lia.
    }
    split; intros m'' ? ?.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEQ.
      apply H.
      rewrite <- NEQ'.
     apply approx_lt; auto.
    - apply f_equal with (f:= fun x => app_pred x m'') in H.
      apply prop_unext in H.
      apply approx_p with (level w).
      rewrite NEQ'.
      apply H.
      rewrite <- NEQ.
     apply approx_lt; auto.
Qed.

Import JuicyMemOps.

Fixpoint alloc_juicy_variables (ge: genv) (rho: env) (jm: juicy_mem) (vl: list (ident*type)) : env * juicy_mem :=
 match vl with
 | nil => (rho,jm)
 | (id,ty)::vars => match JuicyMemOps.juicy_mem_alloc jm 0 (@Ctypes.sizeof ge ty) with
                              (m1,b1) => alloc_juicy_variables ge (PTree.set id (b1,ty) rho) m1 vars
                           end
 end.

Lemma juicy_mem_alloc_core:
  forall jm lo hi jm' b, JuicyMemOps.juicy_mem_alloc jm lo hi = (jm', b) ->
    core (m_phi jm) = core (m_phi jm').
Proof.
 unfold JuicyMemOps.juicy_mem_alloc, after_alloc; intros.
 inv H.
 simpl.
 apply rmap_ext.
 repeat rewrite level_core. rewrite level_make_rmap. auto.
 intro loc.
 repeat rewrite <- core_resource_at.
 rewrite resource_at_make_rmap.
 unfold after_alloc'.
 if_tac; auto.
 destruct loc as [b z].
 simpl in H.
 rewrite core_YES.
 rewrite juicy_mem_alloc_cohere. rewrite core_NO; auto.
 simpl. destruct H.
 revert H; case_eq (alloc (m_dry jm) lo hi); intros.
 simpl in *. subst b0. apply alloc_result in H. subst b; lia.
 rewrite <- (core_ghost_of (proj1_sig _)), ghost_of_make_rmap, core_ghost_of; auto.
Qed.

Lemma alloc_juicy_variables_e:
  forall ge rho jm vl rho' jm',
    alloc_juicy_variables ge rho jm vl = (rho', jm') ->
  Clight.alloc_variables ge rho (m_dry jm) vl rho' (m_dry jm')
   /\ level jm = level jm'
   /\ core (m_phi jm) = core (m_phi jm').
Proof.
 intros.
 revert rho jm H; induction vl; intros.
 inv H. split; auto. constructor.
 unfold alloc_juicy_variables in H; fold alloc_juicy_variables in H.
 destruct a as [id ty].
 revert H; case_eq (JuicyMemOps.juicy_mem_alloc jm 0 (@Ctypes.sizeof ge ty)); intros jm1 b1 ? ?.
 specialize (IHvl (PTree.set id (b1,ty) rho) jm1 H0).
 destruct IHvl as [? [? ?]]; split3; auto.
 apply alloc_variables_cons  with  (m_dry jm1) b1; auto.
 apply JuicyMemOps.juicy_mem_alloc_succeeds in H. auto.
 apply JuicyMemOps.juicy_mem_alloc_level in H.
 congruence.
 rewrite <- H3.
 eapply  juicy_mem_alloc_core; eauto.
Qed.


Lemma alloc_juicy_variables_match_venv:
  forall ge jm vl ve' jm',
     alloc_juicy_variables ge empty_env jm vl = (ve',jm') ->
     match_venv (make_venv ve') vl.
Proof.
intros.
  intro i.
 unfold make_venv.
  destruct (ve' ! i) as [[? ?] | ] eqn:?; auto.
  assert (H0: (exists b, empty_env ! i = Some (b,t)) \/ In (i,t) vl).
2: destruct H0; auto; destruct H0; rewrite PTree.gempty in H0; inv H0.
 forget empty_env as e.
  revert jm e H; induction vl; simpl; intros.
  inv H.
  left; eexists; eauto.
  destruct a.
  apply IHvl in H; clear IHvl.
 destruct (ident_eq i0 i). subst i0.
 destruct H; auto. destruct H as [b' ?].
 rewrite PTree.gss in H. inv H. right. auto.
 destruct H; auto. left. destruct H as [b' ?].
 rewrite PTree.gso in H by auto. eauto.
Qed.

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

Lemma resource_decay_funassert:
  forall G rho b w w',
         necR (core w) (core w') ->
         resource_decay b w w' ->
         app_pred (funassert G rho) w ->
         app_pred (funassert G rho) w'.
Proof.
unfold resource_decay, funassert; intros until w'; intro CORE; intros.
destruct H. 
destruct H0.
split; [clear H2 | clear H0].
+ intros id fs w2 Hw2 H3.
  specialize (H0 id fs). cbv beta in H0.
  specialize (H0 _ (necR_refl _) H3).
  destruct H0 as [loc [? ?]].
  exists loc; split; auto.
  destruct fs as [f cc A a a0].
  simpl in H2|-*.
  pose proof (necR_resource_at (core w) (core w') (loc,0)
         (PURE (FUN f cc) (SomeP (SpecArgsTT A) (packPQ a a0))) CORE).
  pose proof (necR_resource_at _ _ (loc,0)
         (PURE (FUN f cc) (SomeP (SpecArgsTT A) (packPQ a a0))) Hw2).
  apply H5.
  clear - H4 H2.
  repeat rewrite <- core_resource_at in *.
  spec H4. rewrite H2.  rewrite core_PURE.  simpl.  rewrite level_core; reflexivity.
  destruct (w' @ (loc,0)).
  rewrite core_NO in H4; inv H4.
  rewrite core_YES in H4; inv H4.
  rewrite core_PURE in H4; inv H4. rewrite level_core; reflexivity.
+
intros loc sig cc w2 Hw2 H6.
specialize (H2 loc sig cc _ (necR_refl _)).
spec H2.
{ clear - Hw2 CORE H6. simpl in *.
  destruct H6 as [pp H6].
  rewrite <- resource_at_approx.
  case_eq (w @ (loc,0)); intros.
  + assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
     - rewrite <- core_resource_at.
       simpl; erewrite <- core_NO; f_equal; eassumption.
     - pose proof (necR_resource_at _ _ _ _ CORE H0).
       pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
       rewrite <- core_resource_at in H2; rewrite H6 in H2;
       rewrite core_PURE in H2; inv H2.
  + assert (core w @ (loc,0) = resource_fmap (approx (level (core w))) (approx (level (core w))) (NO _ bot_unreadable)).
    - rewrite <- core_resource_at.
      simpl; erewrite <- core_YES; f_equal; eassumption.
    - pose proof (necR_resource_at _ _ _ _ CORE H0).
      pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
      rewrite <- core_resource_at in H2; rewrite H6 in H2;
      rewrite core_PURE in H2; inv H2.
  + pose proof (resource_at_approx w (loc,0)).
    pattern (w @ (loc,0)) at 1 in H0; rewrite H in H0.
    symmetry in H0.
    assert (core (w @ (loc,0)) = core (resource_fmap (approx (level w)) (approx (level w))
       (PURE k p))) by (f_equal; auto).
    rewrite core_resource_at in H1.
    assert (core w @ (loc,0) =
        resource_fmap (approx (level (core w))) (approx (level (core w)))
         (PURE k p)).
    - rewrite H1.  simpl. rewrite level_core; rewrite core_PURE; auto.
    - pose proof (necR_resource_at _ _ _ _ CORE H2).
      assert (w' @ (loc,0) = resource_fmap
         (approx (level w')) (approx (level w')) (PURE k p)).
      * rewrite <- core_resource_at in H3. rewrite level_core in H3.
        destruct (w' @ (loc,0)).
        ++ rewrite core_NO in H3; inv H3.
        ++ rewrite core_YES in H3; inv H3.
        ++ rewrite core_PURE in H3; inv H3.
           reflexivity.
      * pose proof (necR_resource_at _ _ _ _ Hw2 H4).
        inversion2 H6 H5.
        exists p. reflexivity. }
destruct H2 as [id [? ?]].
exists id. split; auto.
Qed. 

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
t1 ! id = t ! id.
Proof.
induction l1;
intros.
simpl in *. destruct l2; inv H0. auto.
simpl in H0. destruct a. destruct l2; inv H0.
specialize (IHl1 l2 (PTree.set i v t) id t1).
simpl in H. intuition. rewrite PTree.gsspec in H3.
destruct (peq id i). subst; tauto. auto.
Qed.

Lemma pass_params_ni :
  forall  l2
     (te' : temp_env) (id : positive) te l,
   bind_parameter_temps l2 l (te) = Some te' ->
   (In id (map fst l2) -> False) ->
   Map.get (make_tenv te') id = te ! id.
Proof.
intros. eapply bind_parameter_temps_excludes in H.
unfold make_tenv, Map.get.
apply H. intuition.
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
t1 ! i = t2 ! i ->
te ! i = te2 ! i.
Proof.
induction l1; intros; simpl in *; try destruct a; destruct l2; inv H; inv H0.
apply H1.
eapply IHl1. apply H3. apply H2.
repeat rewrite PTree.gsspec. destruct (peq i i0); auto.
Qed.


Lemma smaller_temps_exists' : forall l l1 te te' id i t,
bind_parameter_temps l l1 (PTree.set id Vundef t)=  Some te ->
i <> id ->
(bind_parameter_temps l l1 t = Some te') -> te' ! i = te ! i.
Proof.
induction l; intros.
simpl in *. destruct l1; inv H. inv H1. rewrite PTree.gso; auto.

simpl in *. destruct a. destruct l1; inv H.
eapply smaller_temps_exists2. apply H1. apply H3.
intros. repeat rewrite PTree.gsspec. destruct (peq i i0); auto.
destruct (peq i id). subst. tauto. auto.
Qed.

Lemma smaller_temps_exists'' : forall l l1 te id i t,
bind_parameter_temps l l1 (PTree.set id Vundef t)=  Some te ->
i <> id ->
exists te', (bind_parameter_temps l l1 t = Some te').
Proof.
intros.
eapply bind_exists_te; eauto.
Qed.

Lemma smaller_temps_exists : forall l l1 te id i t,
bind_parameter_temps l l1 (PTree.set id Vundef t)=  Some te ->
i <> id ->
exists te', (bind_parameter_temps l l1 t = Some te' /\ te' ! i = te ! i).
Proof.
intros. copy H. eapply smaller_temps_exists'' in H; eauto.
destruct H. exists x. split. auto.
eapply smaller_temps_exists'; eauto.
Qed.


Lemma alloc_vars_lookup :
forall ge id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e ! i = None) ->
Clight.alloc_variables ge (e) m1 l ve m2 ->
(exists v, e ! id = Some v) ->
ve ! id = e ! id.
Proof.
intros.
generalize dependent e.
revert ve m1 m2.

induction l; intros.
inv H1. auto.

inv H1. simpl in *. inv H.
destruct H2.
assert (id <> id0).
intro. subst.  specialize (H0 id0). spec H0. auto. congruence.
eapply IHl in H10.
rewrite PTree.gso in H10; auto.
auto. intros. rewrite PTree.gsspec. if_tac. subst. tauto.
apply H0. auto.
rewrite PTree.gso; auto. eauto.
Qed.

Lemma alloc_vars_lemma : forall ge id l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve ! i = None),
list_norepet (map fst l) ->

Clight.alloc_variables ge ve m1 l ve' m2 ->
(In id (map fst l) ->
exists v, ve' ! id = Some v).
Proof.
intros.
generalize dependent ve.
revert m1 m2.
induction l; intros. inv H1.
simpl in *. destruct a; simpl in *.
destruct H1. subst. inv H0. inv H.  apply alloc_vars_lookup with (id := id) in H9; auto.
rewrite H9. rewrite PTree.gss. eauto. intros.
destruct (peq i id). subst. tauto. rewrite PTree.gso; auto.
rewrite PTree.gss; eauto.

inv H0. apply IHl in H10; auto. inv H; auto.
intros. rewrite PTree.gsspec. if_tac. subst. inv H. tauto.
auto.
Qed.

Lemma semax_call_typecheck_environ:
  forall (Delta : tycontext) (args: list val) (psi : genv)
           (jm : juicy_mem) (b : block) (f : function)
     (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
     (H17' : list_norepet (map fst (fn_vars f)))
     (H16 : Genv.find_funct_ptr psi b = Some (Internal f))
     (ve' : env) (jm' : juicy_mem) (te' : temp_env)
     (H15 : alloc_variables psi empty_env (m_dry jm) (fn_vars f) ve' (m_dry jm'))
     (TC5: typecheck_glob_environ (filter_genv psi) (glob_types Delta))
   (H : forall (b : ident) (b0 : funspec) (a' : rmap),
    necR (m_phi jm') a' ->
    (glob_specs Delta) ! b = Some b0 ->
    exists b1 : block,
        filter_genv psi b = Some b1 /\
        func_at b0 (b1,0) a')
   (TC8 : tc_vals (snd (split (fn_params f))) args)
   (H21 : bind_parameter_temps (fn_params f) args
              (create_undef_temps (fn_temps f)) = Some te'),
   typecheck_environ (func_tycontext' f Delta)
      (construct_rho (filter_genv psi) ve' te').
Proof. assert (H1:= True).
 intros.
 pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).

unfold typecheck_environ. repeat rewrite andb_true_iff.
split3.
*
clear H H1 H15.
unfold typecheck_temp_environ in *. intros. simpl.
unfold temp_types in *. simpl in *.
apply func_tycontext_t_sound in H; auto.
 clear - H21 H TC8 H17.

destruct H. (*in params*)
forget (create_undef_temps (fn_temps f)) as temps.
rewrite snd_split in TC8.
generalize dependent temps.
generalize dependent args. generalize dependent te'.
{  induction (fn_params f); intros.
   + inv H.
   + destruct args. inv TC8. destruct a. simpl in *.
       destruct TC8 as [TC8' TC8].
       destruct H.
      - clear IHl. 
        inv H.
        rewrite (pass_params_ni _ _ id _ _ H21)
           by (inv H17; contradict H1; apply in_app; auto).
        rewrite PTree.gss.
        eexists.  split. reflexivity. apply tc_val_tc_val'.
        auto.
      - inv H17.
        assert (i <> id). intro. subst.
        apply H2. apply in_or_app. left. apply in_map with (f := fst) in H. apply H.
        eapply IHl; eauto.
}

(*In temps*)
apply list_norepet_app in H17. destruct H17 as [? [? ?]].
generalize dependent (fn_params f). generalize dependent args.
generalize dependent te'.

induction (fn_temps f); intros.
inv H.

simpl in *. destruct H. destruct a. inv H. simpl in *.
clear IHl. exists Vundef. simpl in *. split; [| hnf; congruence]. inv H1.
eapply pass_params_ni with (id := id) in H21; auto.
rewrite PTree.gss in *. auto.
intros.
unfold list_disjoint in *. eapply H2. eauto. left. auto. auto.

destruct a.
destruct (peq id i). subst.
apply pass_params_ni with (id := i) in H21.
rewrite PTree.gss in *. exists Vundef. split; [auto | hnf; congruence].
intros. unfold list_disjoint in *. intuition.
eapply H2. eauto. left. auto. auto.

apply smaller_temps_exists with (i := id) in H21.
destruct H21.  destruct H3.
eapply IHl in H3; auto.
destruct H3. destruct H3.
exists x0. split. unfold Map.get in *.
unfold make_tenv in *. rewrite <- H4. auto. auto.
inv H1; auto. unfold list_disjoint in *. intros.
apply H2. auto. right. auto. auto.
*

simpl in *.
unfold typecheck_var_environ in *. intros.
simpl in *. unfold typecheck_var_environ in *.
unfold func_tycontext' in *. unfold var_types in *.
simpl in *.
rewrite (func_tycontext_v_sound (fn_vars f) id ty); auto.
transitivity ((exists b, empty_env ! id = Some (b,ty) )\/ In (id,ty) (fn_vars f)).
clear; intuition. destruct H0. unfold empty_env in H.
rewrite PTree.gempty in H; inv H.
generalize dependent (m_dry jm).
clear - H17'.
assert (forall id, empty_env ! id <> None -> ~ In id (map fst (fn_vars f))).
intros. unfold empty_env in H. rewrite PTree.gempty in H. contradiction H; auto.
generalize dependent empty_env.
unfold Map.get, make_venv.
induction (fn_vars f); intros.
inv H15.
destruct (ve' ! id); intuition.
inv H15.
inv H17'.
specialize (IHl H3); clear H3.
specialize (IHl (PTree.set id0 (b1,ty0) e)).
spec IHl.
intros id' H8; specialize (H id').
destruct (ident_eq id0 id'). subst. auto.
rewrite PTree.gso  in H8 by auto.
specialize (H H8). contradict H.
right; auto.
specialize (IHl _ H7).
clear - H H2 IHl.
destruct (ident_eq id0 id). subst id0.
rewrite PTree.gss in IHl.
split; intro.
destruct H0.
destruct H0. specialize (H id).
destruct (e!id); try discriminate.
inv H0.
spec H; [congruence | ].
contradiction H. left; auto.
destruct H0. inv H0.
apply IHl. left; eauto.
contradiction H2. apply in_map with (f:=fst) in H0. apply H0.
rewrite <- IHl in H0.
destruct H0.
destruct H0. inv H0. right; left; auto.
contradiction H2.
apply in_map with (f:=fst) in H0. auto.
rewrite PTree.gso in IHl by auto.
rewrite <- IHl.
intuition. inv H5. inv H0. tauto.
apply H4 in H0. apply H1; auto.
*
unfold ge_of in *. simpl in *. auto.
Qed.

Lemma free_juicy_mem_level:
  forall jm m b lo hi H, level (free_juicy_mem jm m b lo hi H) = level jm.
Proof.
 intros;  simpl;  unfold inflate_free; simpl.
 rewrite level_make_rmap. auto.
Qed.

Lemma free_juicy_mem_ghost:
  forall jm m b lo hi H,
    ghost_of (m_phi (free_juicy_mem jm m b lo hi H)) = ghost_of (m_phi jm).
Proof.
 intros;  simpl;  unfold inflate_free; simpl.
 rewrite ghost_of_make_rmap. auto.
Qed.

Lemma free_list_free:
  forall m b lo hi l' m',
       free_list m ((b,lo,hi)::l') = Some m' ->
         {m2 | free m b lo hi = Some m2 /\ free_list m2 l' = Some m'}.
Proof.
simpl; intros.
 destruct (free m b lo hi). eauto. inv H.
Qed.

Definition freeable_blocks: list (block * BinInt.Z * BinInt.Z) -> mpred :=
  fold_right (fun (bb: block*BinInt.Z * BinInt.Z) a => 
                        match bb with (b,lo,hi) => 
                                          sepcon (VALspec_range (hi-lo) Share.top (b,lo)) a
                        end)
                    emp.

Inductive free_list_juicy_mem:
      forall  (jm: juicy_mem) (bl: list (block * BinInt.Z * BinInt.Z))
                                         (jm': juicy_mem), Prop :=
| FLJM_nil: forall jm, free_list_juicy_mem jm nil jm
| FLJM_cons: forall jm b lo hi bl jm2 jm'
                          (H: free (m_dry jm) b lo hi = Some (m_dry jm2))
                          (H0 : forall ofs : Z,
                        lo <= ofs < hi ->
                        perm_of_res (m_phi jm @ (b, ofs)) = Some Freeable),
                          free_juicy_mem jm (m_dry jm2) b lo hi H = jm2 ->
                          free_list_juicy_mem jm2 bl jm' ->
                          free_list_juicy_mem jm ((b,lo,hi)::bl) jm'.

Lemma perm_of_res_val : forall r, perm_of_res r = Some Freeable ->
  exists v pp, r = YES Share.top readable_share_top (VAL v) pp.
Proof.
  destruct r; simpl; try if_tac; try discriminate.
  destruct k; try discriminate.
  unfold perm_of_sh.
  repeat if_tac; try discriminate.
  subst; intro; do 2 eexists; f_equal.
  apply proof_irr.
Qed.

Lemma free_list_juicy_mem_i:
  forall jm bl m' F,
   free_list (m_dry jm) bl = Some m' ->
   app_pred (freeable_blocks bl * F) (m_phi jm) ->
   exists jm', free_list_juicy_mem jm bl jm'
                  /\ m_dry jm' = m'
                  /\ level jm = level jm'.
Proof.
intros jm bl; revert jm; induction bl; intros.
*
 inv H; exists jm; split3; auto. constructor.
*
 simpl freeable_blocks in H0. destruct a as [[b lo] hi].
 rewrite sepcon_assoc in H0.
 destruct (free_list_free _ _ _ _ _ _ H) as [m2 [? ?]].
 generalize H0; intro H0'.
 destruct H0 as [phi1 [phi2 [? [? H6]]]].

 assert (H10:= @juicy_free_lemma' jm b lo hi m2 phi1 _ _ H1 H0' H3 H0).
 match type of H10 with m_phi ?A = _ => set (jm2:=A) in H10 end; subst.

 specialize (IHbl  jm2 m' F H2 H6).
 destruct IHbl as [jm' [? [? ?]]].
 exists jm'; split3; auto.
 apply (FLJM_cons jm b lo hi bl jm2 jm' H1
   (juicy_free_aux_lemma (m_phi jm) b lo hi (freeable_blocks bl * F) H0') (eq_refl _) H4).
 rewrite <- H7.
 unfold jm2.
 symmetry; apply free_juicy_mem_level.
Qed.

Lemma free_juicy_mem_ext:
  forall jm1 jm2 b lo hi m1 m2 H1 H2,
      jm1=jm2 -> m1=m2 ->
     free_juicy_mem jm1 m1 b lo hi H1 = free_juicy_mem jm2 m2 b lo hi H2.
Proof.
intros. subst. proof_irr. auto.
Qed.


Lemma free_list_juicy_mem_lem:
  forall P jm bl jm',
     free_list_juicy_mem jm bl jm' ->
     app_pred (freeable_blocks bl * P) (m_phi jm) ->
     app_pred P (m_phi jm').
Proof.
 intros.
 revert H0; induction H; simpl freeable_blocks.
 intros.  rewrite emp_sepcon in H0; auto.
 rename H0 into H99. rename H1 into H0; rename H2 into H1.
 intro.
 rewrite sepcon_assoc in H2.
 generalize H2; intro H2'.
 destruct H2 as [phi1 [phi2 [? [? ?]]]].
 apply IHfree_list_juicy_mem.
 pose proof  (@juicy_free_lemma' jm b lo hi _ phi1 _ _ H H2' H3 H2).
 match type of H5 with m_phi ?A = _ => set (jm3 := A) in H5 end.
 replace jm2 with jm3 by (subst jm3; rewrite <- H0; apply free_juicy_mem_ext; auto).
 subst; auto.
Qed.

Lemma xelements_app:
 forall A (rho: PTree.t A) i al bl,
    PTree.xelements rho i al ++ bl = PTree.xelements rho i (al++bl).
Proof.
 induction rho; simpl; intros; auto.
 destruct o; simpl.
 rewrite IHrho1. simpl. rewrite IHrho2; auto.
 rewrite IHrho1. simpl. rewrite IHrho2; auto.
Qed.

Lemma PTree_elements_remove: forall {A} (T: PTree.tree A) i e,
  In e (PTree.elements (PTree.remove i T)) ->
  In e (PTree.elements T) /\ fst e <> i.
Proof.
  intros.
  destruct e as [i0 v0].
  apply PTree.elements_complete in H.
  destruct (peq i0 i).
  + subst.
    rewrite PTree.grs in H.
    inversion H.
  + rewrite PTree.gro in H by auto.
    split; [| simpl; auto].
    apply PTree.elements_correct.
    auto.
Qed.

Lemma stackframe_of_freeable_blocks {CS}:
  forall Delta f rho ge ve,
      cenv_sub (@cenv_cs CS) (genv_cenv ge) ->
      Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f) ->
      list_norepet (map fst (fn_vars f)) ->
      ve_of rho = make_venv ve ->
      guard_environ (func_tycontext' f Delta) f rho ->
       stackframe_of f rho |-- freeable_blocks (blocks_of_env ge ve).
Proof.
  intros until ve.
  intros HGG COMPLETE.
 intros.
 destruct H1. destruct H2 as [H7 _].
 unfold stackframe_of.
 unfold func_tycontext' in H1.
 unfold typecheck_environ in H1.
 destruct H1 as [_ [?  _]].
 rewrite H0 in H1.
 unfold make_venv in H1.
 unfold var_types in H1.
 simpl in H1. unfold make_tycontext_v in H1.
 unfold blocks_of_env.
match goal with |- ?A |-- _ =>
 replace A
  with (fold_right (@sepcon _ _ _ _ _) emp
            (map (fun idt : ident * type => var_block Share.top idt rho)
            (fn_vars f)))
end.
 2: clear; induction (fn_vars f); simpl; f_equal; auto.
 unfold var_block. unfold eval_lvar. simpl.
  rewrite H0. unfold make_venv. forget (ge_of rho) as ZZ. rewrite H0 in H7; clear rho H0.
 revert ve H1 H7; induction (fn_vars f); simpl; intros.
 case_eq (PTree.elements ve); simpl; intros; auto.
 destruct p as [id ?].
 pose proof (PTree.elements_complete ve id p). rewrite H0 in H2. simpl in H2.
 specialize (H7 id). unfold make_venv in H7. rewrite H2 in H7; auto.
 destruct p; inv H7.
 inv H.
 destruct a as [id ty]. simpl in *.
 simpl in COMPLETE. inversion COMPLETE; subst.
 clear COMPLETE; rename H5 into COMPLETE; rename H2 into COMPLETE_HD.
 specialize (IHl COMPLETE H4 (PTree.remove id ve)).
 assert (exists b, ve ! id = Some (b,ty)). {
  specialize (H1 id ty).
  rewrite PTree.gss in H1. destruct H1 as [[b ?] _]; auto. exists b; apply H.
 }
 destruct H as [b H].
 destruct (@PTree.elements_remove _ id (b,ty) ve H) as [l1 [l2 [? ?]]].
 rewrite H0.
 rewrite map_app. simpl map.
 apply derives_trans with (freeable_blocks ((b,0,@Ctypes.sizeof ge ty) ::  (map (block_of_binding ge) (l1 ++ l2)))).
 2:{
   clear.
   induction l1; simpl; try auto.
   destruct a as [id' [hi lo]]. simpl. rewrite <- sepcon_assoc. 
   rewrite (sepcon_comm (VALspec_range (@Ctypes.sizeof ge ty - 0) Share.top (b, 0))).
   rewrite sepcon_assoc. apply sepcon_derives; auto.
 }
 unfold freeable_blocks; simpl. rewrite <- H2.
 apply sepcon_derives.
 unfold Map.get. rewrite H. rewrite eqb_type_refl.
 unfold memory_block. normalize. {
  rename H6 into H99.
 normalize. (* don't know why we cannot do normalize at first *)
 rewrite memory_block'_eq.
 2: rewrite Ptrofs.unsigned_zero; lia.
 2:{
 rewrite Ptrofs.unsigned_zero. rewrite Zplus_0_r.
 rewrite Z2Nat.id.
 change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99.
 lia.
 unfold sizeof.
 pose proof (sizeof_pos ty); lia.
}
 rewrite Z.sub_0_r.
 unfold memory_block'_alt.
 rewrite if_true by apply readable_share_top.
 rewrite Z2Nat.id.
 + rewrite (cenv_sub_sizeof HGG); auto.
 + unfold sizeof; pose proof (sizeof_pos ty); lia.
}
 eapply derives_trans; [ | apply IHl]; clear IHl.
 clear - H3.
 induction l; simpl; auto.
 destruct a as [id' ty']. simpl in *.
 apply sepcon_derives; auto.
 replace (Map.get (fun id0 : positive => (PTree.remove id ve) ! id0) id')
   with (Map.get (fun id0 : positive => ve ! id0) id'); auto.
 unfold Map.get.
 rewrite PTree.gro; auto.
 intros id' ty'; specialize (H1 id' ty').
 {split; intro.
 - destruct H1 as [H1 _].
   assert (id<>id').
   intro; subst id'.
   clear - H3 H5; induction l; simpl in *. rewrite PTree.gempty in H5; inv H5.
   destruct a; simpl in *.
   rewrite PTree.gso in H5. auto. auto.
   destruct H1 as [v ?].
   rewrite PTree.gso; auto.
   exists v. unfold Map.get. rewrite PTree.gro; auto.
 - unfold Map.get in H1,H5.
   assert (id<>id').
     clear - H5; destruct H5. intro; subst. rewrite PTree.grs in H. inv H.
   rewrite PTree.gro in H5 by auto.
   rewrite <- H1 in H5. rewrite PTree.gso in H5 by auto. auto.
 }
 hnf; intros.
 destruct (make_venv (PTree.remove id ve) id0) eqn:H5; auto.
 destruct p.
 unfold make_venv in H5.
 destruct (peq id id0).
 subst.  rewrite PTree.grs in H5. inv H5.
 rewrite PTree.gro in H5 by auto.
 specialize (H7 id0). unfold make_venv in H7. rewrite H5 in H7.
 destruct H7; auto. inv H6; congruence.
Qed.
(*
Definition maybe_retval (Q: environ -> mpred) retty ret :=
 match ret with
 | Some id => fun rho => Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.*)

Definition maybe_retval (Q: assert) retty ret :=
 match ret with
 | Some id => fun rho => !!(tc_val' retty (eval_id id rho)) && Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, !!(tc_val' retty v) && Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.

Lemma VALspec_range_free:
  forall n b phi1 jm,
  app_pred (VALspec_range n Share.top (b, 0)) phi1 ->
  join_sub phi1 (m_phi jm) ->
  {m' | free (m_dry jm) b 0 n = Some m' }.
Proof.
intros.
apply range_perm_free.
destruct H0 as [phi2 H0].
hnf; intros.
pose proof (juicy_mem_access jm (b,ofs)).
hnf. unfold access_at in H2. simpl in H2.
destruct H as [H _]; specialize (H (b,ofs)).
hnf in H.
rewrite if_true in H by (split; auto; lia).
destruct H as [v ?].
apply (resource_at_join _ _ _ (b,ofs)) in  H0.
destruct H.
hnf in H.
rewrite H in H0.
rewrite H2.
inv H0; simpl; apply join_top in RJ; subst sh3; rewrite perm_of_freeable; constructor.
Qed.

Lemma Forall_filter: forall {A} P (l: list A) f, Forall P l -> Forall P (filter f l).
Proof.
  intros.
  induction l.
  + constructor.
  + inversion H; subst.
    apply IHl in H3.
    simpl.
    simple_if_tac.
    - constructor; auto.
    - auto.
Qed.

Lemma can_free_list {CS}:
  forall Delta F f jm ge ve te
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f)))
  (COMPLETE: Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f))
  (HGG: cenv_sub (@cenv_cs CS) (genv_cenv ge)),
   guard_environ (func_tycontext' f Delta) f
        (construct_rho (filter_genv ge) ve te) ->
    (F * stackframe_of f (construct_rho (filter_genv ge)ve te))%pred (m_phi jm) ->
   exists m2, free_list (m_dry jm) (blocks_of_env ge ve) = Some m2.
Proof.
  intros.
  destruct H0 as [? [? [? [_ ?]]]].
  unfold stackframe_of in H1.
  unfold blocks_of_env in *.
  destruct H as [_ [H _]]; clear - NOREP COMPLETE HGG H H0 H1. simpl in H.
  pose (F vl := (fold_right
          (fun (P Q : environ -> pred rmap) (rho : environ) => P rho * Q rho)
          (fun _ : environ => emp)
          (map (fun idt : ident * type => var_block Share.top idt) vl))).
  change ((F (fn_vars f)  (construct_rho (filter_genv ge) ve te)) x0) in H1.
  assert (forall id b t, In (id,(b,t)) (PTree.elements ve) ->
                In (id,t) (fn_vars f)). {
   intros.
    apply PTree.elements_complete in  H2.
    specialize (H id); unfold make_venv in H; rewrite H2 in H.
     apply H.
  }
  clear H.
  assert (Hve: forall i bt, In (i,bt) (PTree.elements ve) -> ve ! i = Some bt)
    by apply PTree.elements_complete.
  assert (NOREPe: list_norepet (map (@fst _ _) (PTree.elements ve)))
    by apply PTree.elements_keys_norepet.
  forget (PTree.elements ve) as el.
  rename x0 into phi.
  assert (join_sub phi (m_phi jm)).
  econstructor; eauto.
  clear H0.
  forget (fn_vars f) as vl.
  revert vl phi jm H H1 H2 Hve NOREP NOREPe COMPLETE; induction el; intros;
    [ solve [simpl; eauto] | ].
  simpl in H2.
  destruct a as [id [b t]]. simpl in NOREPe,H2|-*.
  assert (H2': In (id,t) vl) by (apply H2 with b; auto).
  specialize (IHel (filter (fun idt => negb (eqb_ident (fst idt) id)) vl)).
  replace (F vl (construct_rho (filter_genv ge) ve te))
    with  (var_block Share.top (id,t) (construct_rho (filter_genv ge) ve te)
    * F (filter (fun idt => negb (eqb_ident (fst idt) id)) vl) (construct_rho (filter_genv ge) ve te)) in H1.
  2:{
    clear - H2' NOREP.
    induction vl; inv H2'.
    simpl in NOREP.
    inv NOREP.
    unfold F; simpl fold_right.
    f_equal.
    f_equal.
    f_equal.
    replace (eqb_ident id id) with true
      by (symmetry; apply (eqb_ident_spec id id); auto).
    simpl.
    clear - H1.
    induction vl; simpl; auto.
    replace (negb (eqb_ident (fst a) id)) with true.
    f_equal.
    apply IHvl.
    contradict H1. right; auto.
    pose proof (eqb_ident_spec (fst a) id).
    destruct (eqb_ident (fst a) id) eqn:?; auto.
    elimtype False; apply H1. left. rewrite <- H; auto.
    transitivity
     (var_block Share.top a (construct_rho (filter_genv ge) ve te) *
         F vl (construct_rho (filter_genv ge) ve te)); [ | reflexivity].
    inv NOREP.
    rewrite <- IHvl; auto.
    repeat rewrite <- sepcon_assoc.
    simpl filter.
    replace (eqb_ident (fst a) id) with false.
    simpl.
    unfold F at 1.
    simpl.
    symmetry;
    rewrite (sepcon_comm (var_block _ _ _ )).
    repeat rewrite sepcon_assoc.
    reflexivity.
    pose proof (eqb_ident_spec (fst a) id).
    destruct (eqb_ident (fst a) id); auto.
    assert (fst a = id) by (apply H0; auto).
    subst id.
    contradiction H2.
    replace (fst a) with (fst (fst a, t)) by reflexivity.
    apply in_map; auto.
  }
  pose (H0:=True).
  destruct H1 as [phi1 [phi2 [? [? ?]]]].
  unfold var_block in H3.
  normalize in H3.
  simpl in H3.
  assert (0 <= sizeof t) by (unfold sizeof; pose proof (sizeof_pos t); lia).
  simpl in H5.
  unfold eval_lvar, Map.get in H3. simpl in H3.
  unfold make_venv in H3.
  rewrite (Hve id (b,t)) in H3 by (left; auto).
  rewrite eqb_type_refl in H3.
  simpl in H3; destruct H3 as [H99 H3].
  rewrite memory_block'_eq in H3;
  try rewrite Ptrofs.unsigned_zero; try lia.
  2:{
   rewrite Z.add_0_r; rewrite Z2Nat.id by lia. change (Ptrofs.unsigned Ptrofs.zero) with 0 in H99; lia.
  }
  unfold memory_block'_alt in H3.
  rewrite Ptrofs.unsigned_zero in H3.
  rewrite Z2Nat.id in H3 by lia.
  rewrite if_true in H3 by apply readable_share_top.
  assert (join_sub phi1 (m_phi jm)) as H7
   by ( apply join_sub_trans with phi; auto; eexists; eauto).
  destruct (VALspec_range_free _ _ _ _ H3 H7)
   as [m3 ?H].
  assert (VR: app_pred (VALspec_range (sizeof t-0) Share.top (b, 0) * TT) (m_phi jm)).
    clear - H3 H7. destruct H7.
  rewrite Z.sub_0_r; exists phi1; exists x; split3; auto.
  pose (jm3 := free_juicy_mem _ _ _ _ _ H8 ).
  destruct H as [phix H].
  destruct (join_assoc H1 H) as [phi3 []].
  assert (phi3 = m_phi jm3).
  { subst jm3; symmetry; eapply juicy_free_lemma'; eauto.
    rewrite Z.sub_0_r; auto.
  }
  subst phi3.  assert (join_sub phi2 (m_phi jm3)) as Hphi2 by (eexists; eauto).
  destruct (IHel phi2 jm3 Hphi2) as [m4 ?]; auto; clear IHel.
  + intros.
    specialize (H2 id0 b0 t0).
    spec H2; [ auto |].
    assert (id0 <> id).
    {
      clear - NOREPe H11.
      inv NOREPe. intro; subst.
      apply H1. change id with (fst (id,(b0,t0))); apply in_map; auto.
    }
    clear - H2 H12.
    induction vl; simpl in *; auto.
    destruct H2. subst a. simpl.
    replace (eqb_ident id0 id) with false; simpl; auto.
    pose proof (eqb_ident_spec id0 id); destruct (eqb_ident id0 id); simpl in *; auto.
    contradiction H12; apply H; auto.
    pose proof (eqb_ident_spec (fst a) id); destruct (eqb_ident (fst a) id); simpl in *; auto.
  + intros; eapply Hve; eauto.
    right; auto.
  + clear - NOREP.
    induction vl; simpl; auto.
    pose proof (eqb_ident_spec (fst a) id); destruct (eqb_ident (fst a) id); simpl in *; auto.
    assert (fst a = id) by ( apply H; auto); subst.
    apply IHvl; inv NOREP; auto.
    inv NOREP.
    constructor; auto.
    clear - H2.
    contradict H2.
    induction vl; simpl in *; auto.
    destruct (eqb_ident (fst a0) id); simpl in *; auto.
    destruct H2; auto.
  + inv NOREPe; auto.
  + apply Forall_filter; auto.
  + pose proof (proj1 (Forall_forall _ _) COMPLETE (id, t) H2').
    simpl in H11.
    exists m4.
    rewrite (cenv_sub_sizeof HGG) by auto.
    unfold sizeof in H8; rewrite H8; auto.
Qed.

Lemma age_juicy_mem_i:
  forall jm jm', m_dry jm = m_dry jm' ->
        age (m_phi jm) (m_phi jm') ->
       age jm jm'.
Proof.
intros.
hnf in H0 |-*.
unfold age1; simpl.
apply age1_juicy_mem_unpack'; auto.
Qed.

Lemma free_juicy_mem_resource_decay:
  forall jm b lo hi m' jm'
     (H : free (m_dry jm) b lo hi = Some m')
     (H0 : forall ofs : Z,  lo <= ofs < hi ->
             perm_of_res (m_phi jm @ (b, ofs)) = Some Freeable),
    free_juicy_mem jm m' b lo hi H = jm' ->
    resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
intros.
 subst jm'. simpl.
 apply (inflate_free_resource_decay _ _ _ _ _ H H0).
Qed.

Lemma free_list_resource_decay:
  forall bl jm jm',
  free_list_juicy_mem jm bl jm' ->
  resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
induction 1; intros.
apply resource_decay_refl; intros.
apply (juicy_mem_alloc_cohere jm l H).
apply resource_decay_trans with (nextblock (m_dry jm)) (m_phi jm2).
apply Pos.le_refl.
eapply free_juicy_mem_resource_decay; eauto.
rewrite <- (nextblock_free _ _ _ _ _ H).
apply IHfree_list_juicy_mem.
Qed.

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with
 | None => True
 | Some i => match (temp_types Delta) ! i with Some t' => t=t' | _ => False end
 end.

Lemma derives_refl' {A: Type}  `{ageable A}:
    forall P Q: pred A, P=Q -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

 Lemma free_juicy_mem_core:
  forall jm m b lo hi H
   (H0 : forall ofs : Z,
     lo <= ofs < hi -> perm_of_res (m_phi jm @ (b, ofs)) = Some Freeable),
   core (m_phi (free_juicy_mem jm m b lo hi H)) = core (m_phi jm).
Proof.
 intros.
 apply rmap_ext.
 do 2  rewrite level_core.
 apply free_juicy_mem_level.
 intros.
 repeat rewrite <- core_resource_at.
 simpl. unfold inflate_free; simpl;  rewrite resource_at_make_rmap.
 destruct (m_phi jm @ l) eqn:?; auto.
 if_tac; rewrite !core_NO; auto.
 if_tac. rewrite core_YES, core_NO; auto. rewrite !core_YES; auto.
 if_tac; auto.
 destruct l; destruct H1; subst. specialize (H0 z).
 spec H0; [lia | ]. rewrite Heqr in H0. inv H0.
 rewrite !ghost_of_core, free_juicy_mem_ghost; auto.
Qed.

Lemma same_glob_funassert':
  forall Delta1 Delta2 rho rho',
     (forall id, (glob_specs Delta1) ! id = (glob_specs Delta2) ! id) ->
      ge_of rho = ge_of rho' ->
              funassert Delta1 rho = funassert Delta2 rho'.
Proof.
assert (forall Delta Delta' rho rho',
             (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id) ->
             ge_of rho = ge_of rho' ->
             funassert Delta rho |-- funassert Delta' rho').
+ intros.
  unfold funassert.
  intros w [? ?]; split.
  - clear H2; intro id. rewrite <- (H id), <- H0; auto.
  - intros loc sig cc w' Hw' H4; destruct (H2 loc sig cc w' Hw' H4)  as [id H3].
    exists id; rewrite <- (H id), <- H0; auto.
+ intros.
  apply pred_ext; apply H; intros; auto.
Qed.

Definition thisvar (ret: option ident) (i : ident) : Prop :=
 match ret with None => False | Some x => x=i end.

Lemma closed_wrt_modvars_Scall:
  forall ret a bl, closed_wrt_modvars (Scall ret a bl) = closed_wrt_vars (thisvar ret).
Proof.
intros.
unfold closed_wrt_modvars.
extensionality F.
f_equal.
 extensionality i; unfold modifiedvars; simpl.
 unfold isSome, idset0, insert_idset; destruct ret; simpl; auto.
 destruct (ident_eq i0 i).
 subst. rewrite PTree.gss. apply prop_ext; split; auto.
 rewrite PTree.gso by auto. rewrite PTree.gempty.
 apply prop_ext; split ;intro; try contradiction.
 rewrite PTree.gempty. auto.
Qed.

Lemma assert_safe_jmupd_for_external_call {Espec psi curf vx ret ret0 tx k z' m'}
      (AS: assert_safe Espec psi curf vx (set_opttemp ret (force_val ret0) tx) 
         (Cont k) (construct_rho (filter_genv psi) vx (set_opttemp ret (force_val ret0) tx)) (m_phi m')):
  jm_bupd z' (jsafeN OK_spec psi (level m') z' (Returnstate (force_val ret0) (Kcall ret curf vx tx k))) m'.
Proof.
(* this proof is like assert_safe_jsafe *)
intros gh JS J.
destruct (AS _ J) as (? & ? & ? & Hl & Hr & ? & Hsafe); subst.
simpl in Hsafe.
destruct (juicy_mem_resource _ _ Hr) as (jm' & ? & ?); subst.
exists jm'; repeat split; auto.
rewrite level_juice_level_phi, <- Hl.
hnf in Hsafe.
specialize (Hsafe z' jm').
spec Hsafe. {
    eapply joins_comm, join_sub_joins_trans, joins_comm, H.
    destruct JS.
    change (Some (ghost_PCM.ext_ref z', NoneP) :: nil) with
      (own.ghost_approx (m_phi m') (Some (ghost_PCM.ext_ref z', NoneP) :: nil)).
    eexists; apply ghost_fmap_join; eauto.
  }
do 2 (spec Hsafe; [auto|]).
destruct (gt_dec (level (m_phi jm')) O).
2: replace (level (m_phi jm')) with O by lia; constructor.
spec Hsafe; [auto | clear - Hsafe].
destruct k; try contradiction.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  change (level (m_phi jm')) with (level jm') in Hsafe.
  destruct (level jm'). constructor.
  inv Hsafe; [ | discriminate | contradiction].
  destruct H1.
  inv H0.
  econstructor.
  split. eapply step_skip_call; eauto. hnf; auto. auto. auto.
-
  eapply jsafeN_local_step. constructor.
  hnf; auto. eauto.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  change (level (m_phi jm')) with (level jm') in Hsafe.
  destruct (level jm'). constructor.
  inv Hsafe; [ | discriminate | contradiction].
  destruct H1.
  inv H0.
  econstructor.
  split. eapply step_skip_call; eauto. hnf; auto. auto. auto.
Qed.

Lemma semax_call_external: forall 
 (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
 (A : TypeTree) 
 (P : forall ts : list Type,  (dependent_type_functor_rec ts (ArgsTT A)) mpred)
 (Q : forall ts : list Type,  (dependent_type_functor_rec ts (AssertTT A)) mpred)
 (NEP : args_super_non_expansive P) (NEQ' : super_non_expansive Q)
 (ts : list Type)
 (x : (dependent_type_functor_rec ts A) mpred)
 (F : environ -> pred rmap) (F0 : assert)
 (ret : option ident) (curf : function) (fsig : typesig) (cc : calling_convention)
 (R : ret_assert) (psi : genv) (vx : env) (tx : temp_env) 
 (k : cont) (rho : environ) (ora : OK_ty) (b : block) (jm : juicy_mem)
 (Hora : (ext_compat ora) (m_phi jm)) 
 (TCret : tc_fn_return Delta ret (snd fsig)) 
 (TC3 : guard_environ Delta curf rho)
 (TC5 : snd fsig = Tvoid -> ret = None)
 (H : closed_wrt_vars (thisvar ret) F0)
(* (HGG : cenv_sub cenv_cs psi) *)
 (H0 : rho = construct_rho (filter_genv psi) vx tx) 
 (H1 : (rguard Espec psi Delta curf (frame_ret_assert R F0) k) (level (m_phi jm)))
 (H4 : (funassert Delta rho) (m_phi jm)) 
(* (Prog_OK : (believe Espec Delta psi Delta) (level jm)) *)
 (args : list val) 
 (H14 : (F0 rho * F rho *
              P ts x (ge_of rho, args))%pred
              (m_phi jm))
 (H5 : (believe_external Espec psi (Vptr b Ptrofs.zero) fsig cc A P Q) (S (level jm)))
 (ff : Clight.fundef)
 (H16 : Genv.find_funct psi (Vptr b Ptrofs.zero) = Some ff)
(* (H16' : type_of_fundef ff =
       Tfunction (type_of_params (fst fsig)) (snd fsig) cc)*)
 (TC8 : tc_vals (fst fsig) args)
 (Hargs : Datatypes.length (fst fsig) = Datatypes.length args),
 let ctl := Kcall ret curf vx tx k : cont in
 forall (HR : (ALL rho' : environ,
      |> ! ((EX old : val,
             substopt ret (`old) F rho' *
             maybe_retval (Q ts x) (snd fsig) ret rho') >=>
            RA_normal R rho')) (m_phi jm)),
 jsafeN OK_spec psi (level jm) ora (Callstate ff args ctl) jm.
Proof.
intros.
destruct TC3 as [TC3 TC3'].
rename H5 into H15.
unfold believe_external in H15.
rewrite H16 in H15.
destruct ff; try contradiction H15.

destruct H15 as [[H5 H15] Hretty]. hnf in H5.
destruct H5 as [H5 [H5' [Eef Hinline]]]. subst c.
inversion H5. destruct fsig0 as [params retty].
injection H2; clear H2; intros H8 H7. subst t0.
rename t into tys. subst rho.
destruct (age1 jm) as  [jm' |] eqn:Hage.
2:{ rewrite (proj1 (age1_level0 jm) Hage). constructor. }
specialize (H15 psi ts x (level jm)).
spec H15. apply age_laterR. constructor. 
specialize (H15
  (F0 (construct_rho (filter_genv psi) vx tx) *
          F (construct_rho (filter_genv psi) vx tx))
   (typlist_of_typelist tys) args jm).
spec H15; [ clear; lia | ].
specialize (H15 _ (necR_refl _)).
spec H15.
{ clear - Eef Hargs H14 TC8. 
  assert (AP: app_pred ((P ts x (filter_genv psi, args) *
    (F0 (construct_rho (filter_genv psi) vx tx) *
     F (construct_rho (filter_genv psi) vx tx)))) (m_phi jm)).
  { rewrite sepcon_comm.
    eapply sepcon_derives; try apply H14; auto.
  }
  clear - Eef TC8 AP.
  simpl.
  split.
  { (* typechecking arguments *)
    rewrite Eef; simpl.
    clear - TC8. rewrite TTL2.
    revert args TC8; induction params; destruct args; intros; try discriminate; auto.
    inv TC8.
    split; auto.
    apply tc_val_has_type; auto.
  }
  apply AP.
} 
clear H14 TC8. simpl fst in *. simpl snd in *.
destruct H15 as [x' H15].
clear H5.
destruct H15 as [H5 H15].
specialize (H15 (rettype_of_type retty)).
do 3 red in H15.
destruct Hinline as [Hinline|Hempty].
2:{
elimtype False; clear - Hempty x.
eapply Hempty. eassumption.
}
assert (Hty: typelist_of_type_list params = tys) by (rewrite H7, TTL3; trivial).
rewrite (age_level _ _ Hage).
eapply jsafeN_external with (x0 := x'); eauto.

+ (*1/3*)
  simpl.
  rewrite Hinline.
  reflexivity.

+ (*2/3*)
  rewrite Eef. subst tys. apply H5; auto.

+ (*clear - Hretty Eef H15. intros. 
   eapply (sp_entry_point_external_aux Q ts x); try eassumption; trivial.
   clear - H15. simpl; intros. simpl in H15.
   destruct (H15 b b0 _ H _ H0 H1) as [r1 [r2 [JR [R1 R2]]]].
   exists r1, r2; split3; trivial. *)

assert (H2 := I). assert (H3 := I). simpl.
intros.
eexists; split; [ reflexivity |].

pose (tx' := match ret,ret0 with
                   | Some id, Some v => PTree.set id v tx
                   | _, _ => tx
                   end).

specialize (H15 ret0 z').
change ((ext_spec_post' Espec e x' (genv_symb_injective psi) (rettype_of_type retty) ret0 z' >=>
        juicy_mem_op
          (Q ts x (make_ext_rval  (filter_genv psi) (rettype_of_type retty) ret0) *
              (F0 (construct_rho (filter_genv psi) vx tx) *
               F (construct_rho (filter_genv psi) vx tx)))) (level jm)) in H15.
apply (pred_nec_hereditary _ _ (level m')) in H15.
 2:{ clear - H6. destruct H6 as [? [? ?]]. apply nec_nat. lia. }
apply (pred_nec_hereditary _ _ (level m')) in H15;
 [ | apply nec_nat; lia].
rewrite Eef in *.
specialize (H15 m' (le_refl _) _ (necR_refl _) H8).
assert (LAT: laterM (level (m_phi jm)) (level jm')). { simpl; apply laterR_level'. constructor. apply age_jm_phi. apply Hage. }
apply (pred_nec_hereditary _ _ _ (laterR_necR LAT)) in H1.

specialize (H1 EK_normal None tx' vx (m_phi m')).
assert (LATER: laterM (m_phi jm) (m_phi jm')). { clear - Hage. apply age_laterR. apply age1_juicy_mem_Some in Hage; trivial. }

spec H1.
{ clear - Hage H6.
  destruct H6 as [? [? ?]]. apply age_level in Hage.
  rewrite <- level_juice_level_phi. lia.
}
rewrite proj_frame_ret_assert in H1.
simpl proj_ret_assert in H1. hnf in H1. 

assert (H1' : forall a' : rmap,
     necR (m_phi m') a' ->
     (!! guard_environ Delta curf (construct_rho (filter_genv psi) vx tx') &&
      seplog.sepcon (fun rho0 => EX old:val, (*!! tc_ret retty ret rho0 &&*) substopt ret (`old) F rho0 * maybe_retval (Q ts x) retty ret rho0) F0 (construct_rho (filter_genv psi) vx tx') &&
      funassert Delta (construct_rho (filter_genv psi) vx tx')) a' ->
     (assert_safe Espec psi curf vx tx' (exit_cont EK_normal None k) (construct_rho (filter_genv psi) vx tx')) a').
{ intros a' NEC Ha'. apply (H1 _ NEC); clear H1.
  destruct Ha' as [HX HY].
  split; trivial. clear HY. destruct HX as [HA HB]. split; trivial. clear HA.
  destruct HB as [a1 [a2 [J [A1 A2]]]]. exists a1, a2; split; [trivial | split ;[| trivial]].
  split. hnf; auto.
  destruct (nec_join4 _ _ _ _ J NEC) as [a1' [a2' [J' [NA1 NA2]]]].
  eapply HR; try eassumption.
  apply join_level in J'; destruct J' as [J' _]; rewrite J'.
  rewrite <- 2 level_juice_level_phi. destruct H6 as [? [? ?]]; subst. clear - H0. simpl in H0. simpl. lia. }
clear H1; rename H1' into H1. clear R HR.

simpl exit_cont in H1.
do 3 red in H5.
specialize (H1 _ (necR_refl _)).

assert (Htc: tc_option_val retty ret0).
{ clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 Hage.
  destruct H15 as [phi1 [phi2 [Ha [Hb Hc]]]].
  specialize (Hretty ts x ret0 phi1).
  spec Hretty.
  { apply join_level in Ha. destruct Ha as [? ?].
    rewrite H. cut ((level jm > level jm')%nat). intros.
    simpl. unfold natLevel. do 2 rewrite <-level_juice_level_phi.
    destruct H6 as [? [? ?]].  lia.
    apply age_level in Hage. lia.
  }
  specialize (Hretty phi1).
  spec Hretty. apply rt_refl.
  spec Hretty. split. apply Hb. apply Hretty0.
  simpl in Hretty. auto.
}
spec H1.
{ clear H1. clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 H8 Hage TC3' tx' Htc H H4.
  split; [split; [split |] |].
  * (*1/4*) 
    clear - TC3 Htc TCret Hretty0.
    destruct ret. 2: subst tx'; trivial. 
    destruct ret0; subst tx'. 2: trivial.
    unfold construct_rho in TC3. simpl in *.
    apply (typecheck_environ_put_te _ _ _ _ i v) in TC3.
    + unfold construct_rho in *; rewrite map_ptree_rel in *; trivial.
    + intros. rewrite H in TCret; subst. red; intros; trivial.
        clear - Hretty0 Htc H0. hnf in Htc. destruct t; auto.
        hnf in Hretty0. destruct v; try contradiction.
  * (*2/4*) clear - TC3' tx'. auto.
  * (*3/4*)
    do 3 red in H15.
    rewrite (sepcon_comm (F0 _)) in H15.
    rewrite <- sepcon_assoc in H15.
    assert (H15': ((!!tc_option_val retty ret0 && Q ts x (make_ext_rval (filter_genv psi) (rettype_of_type retty)ret0)) *
       F (construct_rho (filter_genv psi) vx tx) *
       F0 (construct_rho (filter_genv psi) vx tx))%pred (m_phi m')).
    { rewrite sepcon_assoc in H15|-*.
      destruct H15 as [w1 [w2 [H1 [H10 H12]]]]; exists w1; exists w2; split3; auto.
      clear - H1 H6 H10  Hage Hretty Hretty0.
      specialize (Hretty ts x ret0 w1).
      spec Hretty. {
        destruct H6 as [? [? ?]].
        repeat rewrite <- level_juice_level_phi.
        apply age_level in Hage. rewrite Hage.
        apply join_level in H1. destruct H1.
        rewrite H1.
        change (S (S (level jm')) >= level m')%nat.
        lia.
      }
      split.
      + apply Hretty; auto. split; auto.
      + auto. }
    clear H15.
    revert Htc.
    normalize in H15'.
    do 2 red in H1.
    intros Htc.
    rewrite (sepcon_comm (Q _ _ _)) in H15'.
    unfold seplog.sepcon, seplog.LiftSepLog .
    rewrite <- exp_sepcon1.
    eapply sepcon_derives; [apply sepcon_derives | | apply H15']; clear H15'.
    + (* F *)
      destruct TC3 as [TC3 _].
      hnf in TC3; simpl in TC3.
      hnf in TCret.
      apply exp_right with match ret with
       | Some id =>
           match tx ! id with
           | Some old => old
           | None => Vundef
           end
       | None => Vundef
       end. 
(*      apply andp_right.
      { intros ? ?; simpl. clear - Hretty0 tx' TC3 TCret H1.
        simpl in Hretty0.
        destruct ret.
        2:{ clear TC3. destruct retty; simpl in *; trivial. exfalso.
            destruct ret0; try contradiction. simpl in *.
        { specialize (TC3 i). destruct ((temp_types Delta) ! i); [ subst | contradiction].
          destruct (TC3 _ (eq_refl _)) as [u [? ?]]; clear TC3.
          unfold make_tenv, Map.get in H.
          destruct ret0; simpl in *; unfold make_tenv, Map.get.
          - destruct t; simpl in *; trivial. unfold eval_id, Map.get; simpl.
            apply (binop_lemmas3.tc_val_PM_Tint i0 s a) in H1. simpl in H1.  unfold binop_lemmas3.tc_val_PM in H1.
            * exists i; split; trivial. rewrite PTree.gss; simpl; trivial.
              red in H1.
            * red   red. simpl. discriminate.  simpl.
        destruct ret0; simpl in *. destruct retty; simpl in *; try contradiction.
          .
        - destruct retty; simpl in *; trivial. eexists i; split; trivial.
          destruct ret0; simpl in *. 
          red in Hretty0.   . red in H1.  red. destruct retty; simpl in*.  destruct ret; simpl in *.
        + destruct ((temp_types Delta) ! i) as [ti|] eqn:H29; try contradiction.
          specialize (TC3 _ _ H29).
          destruct TC3 as [v [? ?]]. unfold make_tenv, Map.get in H3; rewrite H3. subst ti; trivial.
        + intros ?; congruence. }*)
      unfold tx' in *; clear tx'.
      destruct ret; auto.
      destruct ((temp_types Delta) ! i) as [ti|] eqn:H29; try contradiction.
      specialize (TC3 _ _ H29).
      destruct TC3 as [v [? ?]].

      unfold substopt, subst.
      apply derives_refl'.
      f_equal.
      unfold env_set, construct_rho.
      simpl. f_equal.
      unfold Map.set,Map.get, make_tenv in (*H9*)H2 |- *; rewrite (*H9*)H2.
      destruct (type_eq retty Tvoid).
      spec TC5; auto. inv TC5.
      extensionality j.
      if_tac. subst j. auto.
      destruct ret0; auto.
      rewrite PTree.gso; auto.
    + (* Q *)
      destruct (type_eq retty Tvoid).
      --
      subst retty. unfold maybe_retval.
      hnf in H1.
      spec TC5; auto; subst tx' ret.
      destruct ret0; try contradiction; apply derives_refl.
      --
      destruct ret0; hnf in (*H1*)H; simpl in (*H1*)H.
      assert (tc_val retty v).
      { destruct retty; try congruence; auto. }
      clear H1.
      unfold maybe_retval.
      destruct ret.
      - apply andp_right. 
        { clear - n H2. subst tx'.  intros ? ? ?; unfold eval_id; simpl.
          unfold make_tenv, Map.get; simpl. rewrite PTree.gss. apply H2. } 
        apply derives_refl'; f_equal.
        unfold tx'.
        unfold make_ext_rval, get_result1; simpl.
        unfold ret_temp, eval_id, env_set; simpl.
        f_equal.
        unfold Map.get, make_tenv; simpl. 
        rewrite PTree.gss. simpl force_val. clear - Hretty0 n Htc. unfold rettype_of_type.
        destruct retty as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];  try reflexivity; try congruence;
        destruct v; try contradiction.
      - apply derives_trans with
          (EX v0 : val, !! tc_val' retty v0 && Q ts x (mkEnviron (filter_genv psi) (Map.empty (block * type)) (Map.set 1 v0 (Map.empty val)))).
        apply exp_right with v. apply andp_right. { intros ? ? ?.  trivial. }
        unfold make_args, make_ext_rval; simpl.
        unfold env_set, globals_only; simpl.
        clear - Hretty0 Htc n.
        destruct retty as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];  try congruence;
        destruct v; try contradiction; apply derives_refl.
        destruct retty; try congruence; apply derives_refl.
      - repeat match goal with| _ => destruct retty; try contradiction
            | _ => congruence (* 8.5 *)
        end.
    + clear - H.
      apply derives_refl'. apply H; intros.
      unfold tx'; clear.
      unfold thisvar; simpl.
      destruct ret; simpl; auto.
      destruct (ident_eq i0 i).
      subst; auto.
      right.
      unfold Map.get, make_tenv.
      destruct ret0; auto.
      rewrite PTree.gso by auto.
      auto. 
  * (*4/4*)
    clear - H6 H4.
    destruct H6 as (?&?&?).
    destruct H4.
    split.
    + intros id fs ???.
      specialize (H2 id fs (m_phi jm) (necR_refl _)).    spec H2; auto.
      destruct H2 as [b [? ?]].
      destruct H1 as [H1 H1'].
      specialize (H1 (b,0)).
      unfold func_at in H6. destruct fs; simpl in *. 
      rewrite H6 in H1.
      apply (necR_PURE (m_phi m') a') in H1; eauto.
      exists b. split; auto. rewrite H1. simpl.
      f_equal. f_equal.
      assert (Hlev1: (level (m_phi m') >= level a')%nat).
      { apply necR_level in H4; auto. }
      extensionality ts x.
      extensionality b0 rho.
      rewrite !fmap_app.
      match goal with
      | |- ?A (?B (?C ?D)) = _ => change (A (B (C D))) with ((A oo B oo C) D)
      end.
      rewrite approx_oo_approx' by lia.
      rewrite approx_oo_approx' by lia.
      rewrite approx'_oo_approx by lia.
      rewrite approx'_oo_approx by lia.
      auto.
    + intros b sig cc ???.
      specialize (H3 b sig cc (m_phi jm)).
      specialize (H3 (necR_refl _)); spec H3; auto.
      destruct H1 as [H1 H1'].
      specialize (H1' (b,0)).
      simpl in *.
      destruct H5 as [b0 ?].
      destruct (m_phi m' @ (b,0)) eqn:?.
      eapply necR_NOx in Heqr; try apply H4. inversion2 H5 Heqr.
      eapply necR_YES in Heqr; try apply H4. inversion2 H5 Heqr.
      destruct H1' as [pp ?].
      rewrite H6.
      exists pp.
      assert (H9 := necR_PURE _ _ _ _ _ H4 Heqr).
      rewrite H5 in H9. inv H9.
      f_equal.
      pose proof (resource_at_approx (m_phi jm) (b,0)).
      rewrite H6 in H; simpl in H.
      injection H; intro. symmetry in H7. apply H7.
  }

clear - H6 Htc TCret TC5 tx' H1.
destruct H6 as (AA&BB&CC).
subst n'.
rewrite level_juice_level_phi.
change (jm_bupd z'
  (jsafeN OK_spec psi (level m') z'
     (Returnstate (force_val ret0) (Kcall ret curf vx tx k))) m').
replace tx' with (set_opttemp ret (force_val ret0) tx) in H1.
2:{ subst tx'.
  clear - Htc TCret TC5. hnf in Htc, TCret.
 destruct ret0, ret; simpl; auto.
 destruct ((temp_types Delta) ! i); try contradiction.
 destruct retty; try contradiction. spec TC5; auto. inv TC5.
}
clear - H1.
apply assert_safe_jmupd_for_external_call; trivial.
Qed.
(*+ (*1/3*){ clear H15.
assert (app_pred ((P ts x
      (make_args (map fst params) args (tycontext.empty_environ psi)) *
    (F0 (construct_rho (filter_genv psi) vx tx) *
     F (construct_rho (filter_genv psi) vx tx)))) (m_phi jm)). {
rewrite sepcon_comm.
eapply sepcon_derives; try apply H14; auto.
apply derives_refl'. f_equal.
simpl.
clear - H7 Hlen Hargs.
simpl in Hlen, Hargs.
rewrite fst_split in H7,Hlen.
revert args tys H7 Hlen Hargs; induction params; destruct args, tys; simpl; intros; auto; try discriminate.
f_equal.
eapply IHparams; eauto.
injection H7; auto.
}
simpl.
rewrite fst_split.
split.
{ (* typechecking arguments *)
  rewrite Eef; simpl.
  clear - TC8. simpl in TC8. rewrite snd_split in TC8.
  revert args TC8; induction params; destruct args; intros; try discriminate; auto.
  inv TC8.
  simpl in TC8. destruct TC8.
  destruct a. simpl in *. split; auto.
  apply tc_val_has_type; auto.
}
apply H0.
}
clear H14.
destruct H15 as [x' H15].
clear H5.
destruct H15 as [H5 H15].
specialize (H15 (opttyp_of_type retty)).
do 3 red in H15.
destruct Hinline as [Hinline|Hempty].
2:{
elimtype False; clear - Hempty x.
eapply Hempty. eassumption.
}
assert (Hty: type_of_params params = tys).
{ clear -H7 Hlen.
  rewrite H7. clear H7. revert tys Hlen. induction params.
  simpl. destruct tys; auto. inversion 1.
  intros; simpl. destruct a. case_eq (split params). intros l1 l2 Heq. simpl.
  destruct tys; auto. simpl. rewrite Heq in IHparams. rewrite IHparams; auto.
  simpl in Hlen|-*. rewrite Heq in Hlen. inv Hlen. rewrite Heq. auto. }
rewrite (age_level _ _ Hage).
eapply jsafeN_external with (x0 := x'); eauto.
simpl.
rewrite Hinline.
reflexivity.
rewrite Eef. subst tys. apply H5; auto.
assert (H2 := I). assert (H3 := I).
intros.
specialize (H15 ret0 z').
change ((ext_spec_post' Espec e x' (genv_symb_injective psi) (opttyp_of_type retty) ret0 z' >=>
        juicy_mem_op
          (Q ts x (make_ext_rval  (filter_genv psi) ret0) *
              (F0 (construct_rho (filter_genv psi) vx tx) *
               F (construct_rho (filter_genv psi) vx tx)))) (level jm)) in H15.
apply (pred_nec_hereditary _ _ (level m')) in H15.
 2:{ clear - H6. destruct H6 as [? [? ?]]. apply nec_nat. lia. }
apply (pred_nec_hereditary _ _ (level m')) in H15;
 [ | apply nec_nat; lia].
rewrite Eef in *.
specialize (H15 m' (le_refl _) _ (necR_refl _) H8).

pose (tx' := match ret,ret0 with
                   | Some id, Some v => PTree.set id v tx
                   | _, _ => tx
                   end). 
assert (LAT: laterM (level (m_phi jm)) (level jm')). { simpl; apply laterR_level'. constructor. apply age_jm_phi. apply Hage. }
apply (pred_nec_hereditary _ _ _ (laterR_necR LAT)) in H1.

specialize (H1 EK_normal None tx' vx (m_phi m')).
assert (LATER: laterM (m_phi jm) (m_phi jm')). { clear - Hage. apply age_laterR. apply age1_juicy_mem_Some in Hage; trivial. }

spec H1.
{ clear - Hage H6.
  destruct H6 as [? [? ?]]. apply age_level in Hage.
  rewrite <- level_juice_level_phi. lia.
}
rewrite proj_frame_ret_assert in H1.
simpl proj_ret_assert in H1. hnf in H1. 

assert (H1' : forall a' : rmap,
     necR (m_phi m') a' ->
     (!! guard_environ Delta curf (construct_rho (filter_genv psi) vx tx') &&
      seplog.sepcon (fun rho0 => EX old:val, substopt ret old F rho0 * maybe_retval (Q ts x) retty ret rho0) F0 (construct_rho (filter_genv psi) vx tx') &&
      funassert Delta (construct_rho (filter_genv psi) vx tx')) a' ->
     (assert_safe Espec psi curf vx tx' (exit_cont EK_normal None k) (construct_rho (filter_genv psi) vx tx')) a').
{ intros a' NEC Ha'. apply (H1 _ NEC); clear H1.
  destruct Ha' as [HX HY].
  split; trivial. clear HY. destruct HX as [HA HB]. split; trivial. clear HA.
  destruct HB as [a1 [a2 [J [A1 A2]]]]. exists a1, a2; split; [trivial | split ;[| trivial]].
  split. hnf; auto.
  destruct (nec_join4 _ _ _ _ J NEC) as [a1' [a2' [J' [NA1 NA2]]]].
  eapply HR; try eassumption.
  apply join_level in J'; destruct J' as [J' _]; rewrite J'.
  rewrite <- 2 level_juice_level_phi. destruct H6 as [? [? ?]]; subst. lia. } 
clear H1; rename H1' into H1. clear R HR.

simpl exit_cont in H1.
do 3 red in H5.
specialize (H1 _ (necR_refl _)).

assert (Htc: tc_option_val retty ret0).
{clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 Hage.
 destruct H15 as [phi1 [phi2 [Ha [Hb Hc]]]].
 specialize (Hretty ts x ret0 phi1).
 spec Hretty.
 { apply join_level in Ha. destruct Ha as [? ?].
   rewrite H. cut ((level jm > level jm')%nat). intros.
   simpl. unfold natLevel. do 2 rewrite <-level_juice_level_phi.
   destruct H6 as [? [? ?]].  lia.
   apply age_level in Hage. lia.
 }
 specialize (Hretty phi1).
 spec Hretty. apply rt_refl.
 spec Hretty. split. apply Hb. apply Hretty0.
 simpl in Hretty. auto.
}
spec H1. { clear H1.
split; [split; [split |] |].
*
 split.
 2:{
 clear - TC3.
 destruct TC3; simpl in *.
 destruct ret; try apply H0.
 }
 simpl.
 destruct TC3 as [TC3 _].
 destruct ret; try apply TC3. {
 clear - TCret TC3 H0 TC5 H15 Hretty Hretty0 H6 H8 Hage.
 simpl in TCret.
 destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
 subst retty.
 unfold tx' in *; clear tx'. simpl in TC3.
 assert (Hu: exists u, opttyp_of_type t = Some u).
 { clear - TC5; destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   try (eexists; reflexivity).
   spec TC5; [auto | congruence].
 }
 destruct Hu as [u Hu]. (*rewrite Hu in *.*) clear TC5.
 destruct H15 as [phi1 [phi2 [Ha [Hb Hc]]]].
 specialize (Hretty ts x ret0 phi1).
 spec Hretty.
 { apply join_level in Ha. destruct Ha as [? ?].
   rewrite H. cut ((level jm > level jm')%nat). intros.
   simpl. unfold natLevel. do 2 rewrite <-level_juice_level_phi. destruct H6; lia.
   apply age_level in Hage. lia.
 }
 specialize (Hretty phi1).
 spec Hretty. apply rt_refl. spec Hretty. split. apply Hb. apply Hretty0. simpl in Hretty.
 unfold typecheck_temp_environ. intros id ty Hty.
 destruct (ident_eq i id).
 + subst i.
 rewrite Heqo in Hty.
 destruct ret0; auto.
 inversion Hty. subst t. simpl.
 exists v. split. rewrite <-map_ptree_rel, Map.gss; auto.
 assert (ty <> Tvoid). { destruct ty; try inv Hu; intros C; congruence. }
 assert (tc_val ty v). { destruct ty; auto. }
 apply tc_val_tc_val'; auto.
 inversion Hty. subst t. simpl.
 assert (ty = Tvoid). { destruct ty; auto; inv Hretty. } subst ty.
 simpl in Hu. inv Hu.
 + destruct ret0.
 rewrite <-map_ptree_rel, Map.gso; auto.
 assert (t = Tvoid). { destruct t; auto; inv Hretty. } subst t.
 simpl in Hu. inv Hu.
}
*
 auto.
*
do 3 red in H15.
rewrite (sepcon_comm (F0 _)) in H15.
rewrite <- sepcon_assoc in H15.
assert (H15': ((!!tc_option_val retty ret0 && Q ts x (make_ext_rval (filter_genv psi) ret0)) *
       F (construct_rho (filter_genv psi) vx tx) *
       F0 (construct_rho (filter_genv psi) vx tx))%pred (m_phi m')). {
rewrite sepcon_assoc in H15|-*.
destruct H15 as [w1 [w2 [H1 [H10 H12]]]]; exists w1; exists w2; split3; auto.
clear - H1 H6 H10  Hage Hretty Hretty0.
specialize (Hretty ts x ret0 w1).
spec Hretty. {
 destruct H6 as [? [? ?]].
 repeat rewrite <- level_juice_level_phi.
 apply age_level in Hage. rewrite Hage.
 apply join_level in H1. destruct H1.
 rewrite H1.
 change (S (S (level jm')) >= level m')%nat.
 lia.
}
split.
apply Hretty; auto. split; auto.
auto.
}
clear H15.
revert Htc.
normalize in H15'.
do 2 red in H1.
intros Htc.
rewrite (sepcon_comm (Q _ _ _)) in H15'.
unfold seplog.sepcon, seplog.LiftSepLog .
rewrite <- exp_sepcon1.
eapply sepcon_derives; [apply sepcon_derives | | apply H15']; clear H15'.
+ (* F *)
  destruct TC3 as [TC3 _].
  hnf in TC3; simpl in TC3.
 hnf in TCret.
apply exp_right with
  match ret with
       | Some id =>
           match tx ! id with
           | Some old => old
           | None => Vundef
           end
       | None => Vundef
       end.
unfold substopt.
unfold tx' in *; clear tx'.
destruct ret; auto.
destruct ((temp_types Delta) ! i) as [ti|] eqn:H29; try contradiction.
specialize (TC3 _ _ H29).
destruct TC3 as [v [? ?]].
unfold subst.
apply derives_refl'.
f_equal.
unfold env_set, construct_rho.
simpl. f_equal.
unfold Map.set,Map.get, make_tenv in H9 |- *; rewrite H9.
destruct (type_eq retty Tvoid).
spec TC5; auto. inv TC5.
extensionality j.
if_tac. subst j. auto.
destruct ret0; auto.
rewrite PTree.gso; auto.
+ (* Q *)
destruct (type_eq retty Tvoid).
subst retty. unfold maybe_retval.
hnf in H1.
destruct ret0; try contradiction.
simpl make_ext_rval.
spec TC5; auto. unfold tx' in *; subst ret.
apply derives_refl.
destruct ret0; hnf in H1; simpl in H1.
assert (tc_val retty v).
destruct retty; try congruence; auto.
clear H1.
unfold maybe_retval.
destruct ret.
 apply derives_refl'; f_equal.
unfold tx'.
unfold make_ext_rval, get_result1; simpl.
unfold ret_temp, eval_id, env_set; simpl.
f_equal.
unfold Map.get, make_tenv; simpl.
rewrite PTree.gss; reflexivity.
apply derives_trans with
  (EX  v0 : val, Q ts x (make_args (ret_temp :: nil) (v0 :: nil) (construct_rho (filter_genv psi) vx tx'))).
apply exp_right with v.
unfold make_args, make_ext_rval; simpl.
unfold env_set, globals_only; simpl.
apply derives_refl.
destruct retty; try congruence.
repeat match goal with
| _ => destruct retty; try contradiction
| _ => congruence (* 8.5 *)
end.
+
clear - H.
apply derives_refl'; apply H; intros.
unfold tx'; clear.
unfold thisvar; simpl.
destruct ret; simpl; auto.
destruct (ident_eq i0 i).
subst; auto.
right.
unfold Map.get, make_tenv.
destruct ret0; auto.
rewrite PTree.gso by auto.
auto. 
*
assert (H4': (funassert Delta (construct_rho (filter_genv psi) vx tx)) (m_phi m')).
{ clear - H6 H4.
  destruct H6 as (?&?&?).
  destruct H4.
  split.
  * intros id fs ???.
    specialize (H2 id fs (m_phi jm) (necR_refl _)).    spec H2; auto.
    destruct H2 as [b [? ?]].
    destruct H1 as [H1 H1'].
    specialize (H1 (b,0)).
    unfold func_at in H6. destruct fs; simpl in *.
    rewrite H6 in H1.
    apply (necR_PURE (m_phi m') a') in H1; eauto.
    exists b. split; auto. rewrite H1. simpl.
    f_equal. f_equal.
    assert (Hlev1: (level (m_phi m') >= level a')%nat).
    { apply necR_level in H4; auto. }
    extensionality ts x.
    extensionality b0 rho.
    rewrite !fmap_app.
    match goal with
    | |- ?A (?B (?C ?D)) = _ => change (A (B (C D))) with ((A oo B oo C) D)
    end.
    rewrite approx_oo_approx' by lia.
    rewrite approx_oo_approx' by lia.
    rewrite approx'_oo_approx by lia.
    rewrite approx'_oo_approx by lia.
    auto.
  * intros b sig cc ???.
    specialize (H3 b sig cc (m_phi jm)).
    specialize (H3 (necR_refl _)); spec H3; auto.
    destruct H1 as [H1 H1'].
    specialize (H1' (b,0)).
    simpl in *.
    destruct H5 as [b0 ?].
    destruct (m_phi m' @ (b,0)) eqn:?.
    eapply necR_NOx in Heqr; try apply H4. inversion2 H5 Heqr.
    eapply necR_YES in Heqr; try apply H4. inversion2 H5 Heqr.
    destruct H1' as [pp ?].
    rewrite H6.
    exists pp.
    assert (H9 := necR_PURE _ _ _ _ _ H4 Heqr).
    rewrite H5 in H9. inv H9.
    f_equal.
    pose proof (resource_at_approx (m_phi jm) (b,0)).
    rewrite H6 in H; simpl in H.
    injection H; intro. symmetry in H7. apply H7.
  }
match type of H4' with ?A => match goal with |- ?B => replace B with A; auto end end.
}

exists (Returnstate (force_val ret0) (Kcall ret curf vx tx k)).
split.
unfold cl_after_external.
revert Htc TC5.
destruct (type_eq retty Tvoid).
+ subst retty. simpl. destruct ret0; try solve[inversion 1].
  intros _. intros X; spec X; auto.
+ intros Hret0.
  assert (Hv: exists v, ret0 = Some v).
  { revert Hret0.
    destruct retty; destruct ret0; simpl;
      try solve[intros _; eexists; eauto]; try inversion 1.
    exfalso; auto. }
  revert TCret.
  unfold tc_fn_return.
  destruct Hv as [v Hv]. rewrite Hv.
  destruct ret; auto.
+
destruct H6 as (?&?&?).
subst n'.
rewrite level_juice_level_phi.
change (jm_bupd z'
  (jsafeN OK_spec psi (level m') z'
     (Returnstate (force_val ret0) (Kcall ret curf vx tx k))) m').
replace tx' with (set_opttemp ret (force_val ret0) tx) in H1.
2:{ subst tx'.
  clear - Htc TCret TC5. hnf in Htc, TCret.
 destruct ret0, ret; simpl; auto.
 destruct ((temp_types Delta) ! i); try contradiction.
 destruct retty; try contradiction. spec TC5; auto. inv TC5.
}
clear tx'.
(* this proof is like assert_safe_jsafe *)
clear - H1.
repeat intro.
destruct (H1 _ H0) as (? & ? & ? & Hl & Hr & ? & Hsafe); subst.
simpl in Hsafe.
destruct (juicy_mem_resource _ _ Hr) as (jm' & ? & ?); subst.
exists jm'; repeat split; auto.
rewrite level_juice_level_phi, <- Hl.
hnf in Hsafe.
specialize (Hsafe z' jm').
spec Hsafe. {
    eapply joins_comm, join_sub_joins_trans, joins_comm, H2.
    destruct H.
    change (Some (ghost_PCM.ext_ref z', NoneP) :: nil) with
      (own.ghost_approx (m_phi m') (Some (ghost_PCM.ext_ref z', NoneP) :: nil)).
    eexists; apply ghost_fmap_join; eauto.
  }
  do 2 (spec Hsafe; [auto|]).
  destruct (gt_dec (level (m_phi jm')) O).
2:   replace (level (m_phi jm')) with O by lia; constructor.
  spec Hsafe; [auto |].
  destruct k; try contradiction.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  change (level (m_phi jm')) with (level jm') in Hsafe.
  destruct (level jm'). constructor.
  inv Hsafe; [ | discriminate | contradiction].
  destruct H6.
  inv H5.
  econstructor.
  split. eapply step_skip_call; eauto. hnf; auto. auto. auto.
-
  eapply jsafeN_local_step. constructor.
  hnf; auto. eauto.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
-
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  change (level (m_phi jm')) with (level jm') in Hsafe.
  destruct (level jm'). constructor.
  inv Hsafe; [ | discriminate | contradiction].
  destruct H6.
  inv H5.
  econstructor.
  split. eapply step_skip_call; eauto. hnf; auto. auto. auto.
Qed.
*)
Lemma alloc_juicy_variables_age:
  forall {ge rho jm jm1 vl rho' jm' jm1'},
   age jm jm1 -> age jm' jm1' ->
   alloc_juicy_variables ge rho jm vl = (rho', jm') ->
   alloc_juicy_variables ge rho jm1 vl = (rho', jm1').
Proof.
  intros.
  revert jm jm1 H rho H1.
  induction vl; intros.
  {
    simpl in *; inv H1.
    hnf in H0,H. congruence.
  }
  destruct a.
  simpl in H1|-*.
  eapply IHvl; [| rewrite <- (age_jm_dry H); eassumption].
  apply age_juicy_mem_i; [simpl; rewrite (age_jm_dry H); auto |].
  simpl.
  apply rmap_age_i.
  {
    unfold after_alloc; simpl. repeat rewrite level_make_rmap.
    apply age_level. apply age_jm_phi; auto.
  }
  intro. unfold resource_fmap; simpl.
  unfold after_alloc; simpl.
  do 2  rewrite resource_at_make_rmap.
  unfold after_alloc'.
  if_tac; [rewrite if_true | rewrite if_false].
  + f_equal.
  + rewrite <- (age_jm_dry H); assumption.
  + clear H1.
    destruct (m_phi jm @ l) eqn:?.
    - symmetry;  eapply necR_NOx; try apply Heqr.
      constructor 1. apply age_jm_phi; auto.
    - symmetry.
      rewrite level_make_rmap.
      eapply necR_YES. constructor 1. eapply age_jm_phi. eassumption.
      auto.
    - rewrite level_make_rmap.
      symmetry.
      eapply necR_PURE. constructor 1. eapply age_jm_phi. eassumption.  auto.
  + rewrite <- (age_jm_dry H); assumption.
  + unfold after_alloc; rewrite !ghost_of_make_rmap, level_make_rmap.
    symmetry; apply age1_ghost_of, age_jm_phi; auto.
Qed.

Lemma alloc_juicy_variables_resource_decay:
  forall ge rho jm vl rho' jm',
    alloc_juicy_variables ge rho jm vl = (rho', jm') ->
    resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
    (nextblock (m_dry jm) <= nextblock (m_dry jm'))%positive.
Proof.
 intros.
 revert rho jm H; induction vl; intros.
 inv H. split. apply resource_decay_refl.
   apply juicy_mem_alloc_cohere. apply Pos.le_refl.
 destruct a as [id ty].
 unfold alloc_juicy_variables in H; fold alloc_juicy_variables in H.
 revert H; case_eq (juicy_mem_alloc jm 0 (@Ctypes.sizeof ge ty)); intros jm1 b1 ? ?.
 pose proof (juicy_mem_alloc_succeeds _ _ _ _ _ H).
 specialize (IHvl _ _ H0).
 symmetry in H1; pose proof (nextblock_alloc _ _ _ _ _ H1).
 destruct IHvl.
 split; [ |  rewrite H2 in H4; lia].
 eapply resource_decay_trans; try eassumption.
 rewrite H2; lia.
 clear - H H1.
 pose proof (juicy_mem_alloc_level _ _ _ _ _ H).
 unfold resource_decay.
 split. repeat rewrite <- level_juice_level_phi; rewrite H0; auto.
 intro loc.
 split.
 apply juicy_mem_alloc_cohere.
 rewrite (juicy_mem_alloc_at _ _ _ _ _ H).
 rewrite Z.sub_0_r.
 destruct loc as [b z]. simpl in *.
 if_tac. destruct H2; subst b1.
 right. right. left. split. apply alloc_result in H1; subst b; lia.
 eauto.
 rewrite <- H0. left. apply resource_at_approx.
Qed.

(*
bind_parameter_temps params args (create_undef_temps (fn_temps f)) = Some te' ->
alloc_juicy_variables psi empty_env jmx (fn_vars f) = (ve', jm'') ->
P ts x
  (make_args (map fst (fst fsig)) args (construct_rho (filter_genv psi) vx tx))
|-- close_precondition (map fst (fst fsig)) (map fst params) 
      (P ts x) (construct_rho (filter_genv psi) ve' te')
*)

Lemma ge_of_make_args:  
    forall s a rho, ge_of (make_args s a rho) = ge_of rho.
Proof.
induction s; intros.
 destruct a; auto.
 simpl in *. destruct a0; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Lemma ve_of_make_args:  
    forall s a rho, length s = length a -> ve_of (make_args s a rho) = (Map.empty (block * type)).
Proof.
induction s; intros.
 destruct a; inv H; auto.
 simpl in *. destruct a0; inv H; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.
(*Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).*)

Fixpoint make_args' (il: list ident) (vl: list val)  : tenviron :=
  match il, vl with
  | i::il', v::vl' => Map.set i v (make_args' il' vl') 
  | _, _ => Map.empty _
  end.

Lemma make_args_eq:  forall il vl, length il = length vl ->
    forall rho,
    make_args il vl rho = mkEnviron (ge_of rho) (Map.empty _) (make_args' il vl).
Proof.
induction il; destruct vl; intros; inv H; simpl.
auto.
unfold env_set.
rewrite IHil; auto.
Qed.

Lemma make_args_close_precondition:
  forall bodyparams args ge tx ve' te' P,
    list_norepet (map fst bodyparams) ->
    bind_parameter_temps bodyparams args tx = Some te' ->
    Forall (fun v : val => v <> Vundef) args ->
    P (filter_genv ge, args)
   |-- close_precondition (map fst bodyparams) P
           (construct_rho (filter_genv ge) ve' te').
Proof.
intros *. intros LNR BP VUNDEF.
intros phi ?.
exists args. split; simpl; trivial.
clear - LNR BP VUNDEF.
generalize dependent te'. generalize dependent tx. generalize dependent args.
induction bodyparams; simpl; intros; destruct args; inv BP; simpl.
+ split; auto.
+ destruct a; discriminate.
+ destruct a. inv LNR. inv VUNDEF. simpl. destruct (IHbodyparams H3 _ H5 _ _ H0) as [X Y]; clear IHbodyparams.
  rewrite X; simpl; clear X; split.
  - f_equal.
(*    specialize (bind_parameter_temps_excludes _ _ _ _ _ H2 H0); intros Q.*)
    rewrite (pass_params_ni _ _ _ _ _ H0 H2), PTree.gss; trivial.
  - constructor; trivial.
Qed.
(* 
Lemma make_args_close_precondition:
  forall specparams bodyparams args ge ve te m tx ve' te' m' P vars,
    length specparams = length bodyparams ->
    list_norepet specparams ->
    list_norepet (map fst bodyparams) ->
    bind_parameter_temps bodyparams args tx = Some te' ->
    alloc_juicy_variables ge empty_env m vars = (ve', m') ->
    P (make_args specparams args (construct_rho (filter_genv ge) ve te))
   |-- close_precondition specparams (map fst bodyparams) P
           (construct_rho (filter_genv ge) ve' te').
Proof.
intros *. intros Hlen Hno. intros.
intros phi ?.
exists (Map.empty (block * type)).
pose (f := fix f (s b: list ident) :=
          match s,b with
          | s1::sr, b1::br => PTree.set s1 (force_val (te' ! b1)) (f sr br)
          | _, _ => empty_tenv
           end).
pose (e := f specparams (map fst bodyparams) : temp_env).
exists (fun i => e!i).
split; intros.
*
unfold Map.get.
simpl.
unfold make_tenv.
subst e.
clear - Hno H0 H3 H4.
rename specparams into s.
forget bodyparams as b.
revert args tx s b Hno H0 H3 H4; induction n; intros.
destruct s; inv H3. destruct b; inv H4. simpl in H0. destruct p, args. inv H0.
simpl. rewrite PTree.gss.
clear - H0. {
  assert ((PTree.set i0 v tx) ! i0 <> None).
  rewrite PTree.gss. congruence.
  forget (PTree.set i0 v tx) as te.
  revert args te te' H H0; induction b as [|[??]]; intros; destruct args; inv H0; auto.
  destruct (te' ! i0); try contradiction; auto.
   apply IHb in H2; auto.
  destruct (ident_eq i0 i). subst. rewrite PTree.gss. clear; congruence.
  rewrite PTree.gso; auto.
}
destruct s; inv H3. destruct b; inv H4.
inv Hno.
simpl.
destruct p.
destruct args; inv H0.
simpl.
rewrite PTree.gso.
eapply IHn; eauto.
contradict H4.
subst i0.
clear - H1.
eapply nth_error_In; eauto.
*
 simpl.
 replace (mkEnviron (filter_genv ge) (Map.empty (block * type)) (fun i : positive => e ! i))
   with  (make_args specparams args (construct_rho (filter_genv ge) ve te)); auto.
 clear - Hlen Hno H H0.
 rewrite make_args_eq.
2:{ rewrite Hlen. clear - H0.
    revert args tx H0; induction bodyparams as [|[??]]; intros; destruct args; inv H0; simpl; auto.
    f_equal; eauto.
 }
  f_equal.
  subst e.  
  assert (length bodyparams = length args). {
   clear - H0.
   revert tx te' args H0; induction bodyparams as [|[??]]; intros; destruct args;inv H0; simpl; f_equal; eauto.
  }
  revert bodyparams args tx H0 H H1 Hno Hlen; induction specparams; intros.
  destruct bodyparams; inv Hlen.
  destruct args; inv H1.
  extensionality j.
  simpl. unfold empty_tenv.
  rewrite PTree.gempty.
  reflexivity.
  destruct bodyparams as [|[? ?]]; inv Hlen.
  destruct args; inv H1.
  inv Hno. inv H.
  simpl. 
  simpl in H0.
   rewrite (IHspecparams bodyparams args (PTree.set i v tx)) by auto.
  extensionality j.
  unfold Map.set. if_tac. subst a. rewrite PTree.gss.
   clear - H0 H7.
  assert ((PTree.set i v tx) ! i = Some v).
  apply PTree.gss.
  forget (PTree.set i v tx) as te.
  revert args te H H0 H7; induction bodyparams as [|[??]]; intros; destruct args; inv H0.
  rewrite H. auto.
  apply IHbodyparams in H2; auto.
  rewrite PTree.gso; auto.
   contradict H7. left; auto.
  contradict H7. right; auto.
  rewrite PTree.gso; auto.
Qed.*)

Lemma after_alloc_block:
 forall phi n F b (Hno : forall ofs : Z, phi @ (b, ofs) = NO Share.bot bot_unreadable),
   app_pred F phi ->
   0 <= n < Ptrofs.modulus ->
   app_pred (F * memory_block Share.top n (Vptr b Ptrofs.zero)) (after_alloc 0 n b phi Hno).
Proof.
intros. rename H0 into Hn.
unfold after_alloc.
match goal with |- context [proj1_sig ?A] => destruct A; simpl proj1_sig end.
rename x into phi2.
destruct a as (? & ? & Hg).
unfold after_alloc' in H1.
destruct (allocate phi
    (fun loc : address =>
      if adr_range_dec (b, 0) (n - 0) loc
      then YES Share.top readable_share_top (VAL Undef) NoneP
      else core (phi @ loc)) (core (ghost_of phi2)))
  as [phi3 [phi4  [? [? Hg']]]].
* extensionality loc; unfold compose.
  if_tac. unfold resource_fmap. rewrite preds_fmap_NoneP. reflexivity.
  repeat rewrite core_resource_at.
  rewrite <- level_core.
  apply resource_at_approx.
*
 intros.
 simpl; if_tac.
 exists (YES Share.top readable_share_top (VAL Undef) NoneP).
 destruct l as [b0 ofs]; destruct H2.
 subst; rewrite Hno; constructor.
 apply join_unit1; auto.
 exists (phi @ l).
 apply join_comm.
 apply core_unit.
*
rewrite ghost_core; auto.
*
rewrite <- Hg; eexists; apply join_comm, core_unit.
*
assert (phi4 = phi2). {
 apply rmap_ext. apply join_level in H2. destruct H2; lia.
 intro loc; apply (resource_at_join _ _ _ loc) in H2.
 rewrite H3 in H2; rewrite H1.
 if_tac.
 inv H2; apply YES_ext; apply (join_top _ _ (join_comm RJ)).
 apply join_comm in H2.
 apply core_identity in H2. auto.
 apply ghost_of_join in H2.
 rewrite Hg' in H2.
 apply join_comm, core_identity in H2; congruence.
}
subst phi4.
exists phi, phi3; split3; auto.
split.
do 3 red.
rewrite Ptrofs.unsigned_zero.
lia.
rewrite Ptrofs.unsigned_zero.
rewrite memory_block'_eq; try lia.
unfold memory_block'_alt.
rewrite if_true by apply readable_share_top.
split.
intro loc. hnf.
rewrite Z2Nat.id by lia.
if_tac.
exists Undef.
exists readable_share_top.
hnf.
rewrite H3.
rewrite Z.sub_0_r.
rewrite if_true by auto.
rewrite preds_fmap_NoneP.
f_equal.
unfold noat. simpl.
rewrite H3.
rewrite Z.sub_0_r.
rewrite if_false by auto.
apply core_identity.
simpl; rewrite Hg'; apply core_identity.
Qed.

Lemma juicy_mem_alloc_block:
 forall jm n jm2 b F,
   juicy_mem_alloc jm 0 n = (jm2, b) ->
   app_pred F (m_phi jm)  ->
   0 <= n < Ptrofs.modulus ->
   app_pred (F * memory_block Share.top n (Vptr b Ptrofs.zero)) (m_phi jm2).
Proof.
intros.
inv H; simpl m_phi.
apply after_alloc_block; auto.
Qed.

Lemma alloc_juicy_variables_lem2 {CS}:
  forall jm f (ge: genv) ve te jm' (F: pred rmap)
      (HGG: cenv_sub (@cenv_cs CS) (genv_cenv ge))
      (COMPLETE: Forall (fun it => complete_type cenv_cs (snd it) = true) (fn_vars f))
      (Hsize: Forall (fun var => @Ctypes.sizeof ge (snd var) <= Ptrofs.max_unsigned) (fn_vars f)),
      list_norepet (map fst (fn_vars f)) ->
      alloc_juicy_variables ge empty_env jm (fn_vars f) = (ve, jm') ->
      app_pred F (m_phi jm) ->
      app_pred (F * stackframe_of f (construct_rho (filter_genv ge) ve te)) (m_phi jm').
Proof.
intros.
unfold stackframe_of.
forget (fn_vars f) as vars. clear f.
forget empty_env as ve0.
revert F ve0 jm Hsize H0 H1; induction vars; intros.
simpl in H0. inv H0.
simpl fold_right. rewrite sepcon_emp; auto.
inv Hsize. rename H4 into Hsize'; rename H5 into Hsize.
simpl fold_right.
unfold alloc_juicy_variables in H0; fold alloc_juicy_variables in H0.
destruct a as [id ty].
destruct (juicy_mem_alloc jm 0 (@Ctypes.sizeof ge ty)) eqn:?H.
rewrite <- sepcon_assoc.
inv H.
simpl in COMPLETE; inversion COMPLETE; subst.
rename H7 into COMPLETE'.
rename H4 into COMPLETE_HD.
eapply IHvars; eauto. clear IHvars.
pose proof I.
unfold var_block, eval_lvar.
simpl sizeof; simpl typeof.
simpl Map.get. simpl ge_of.
assert (Map.get (make_venv ve) id = Some (b,ty)). {
 clear - H0 H5.
 unfold Map.get, make_venv.
 assert ((PTree.set id (b,ty) ve0) ! id = Some (b,ty)) by (apply PTree.gss).
 forget (PTree.set id (b, ty) ve0) as ve1.
 rewrite <- H; clear H.
 revert ve1 j H0 H5; induction vars; intros.
 inv H0; auto.
 unfold alloc_juicy_variables in H0; fold alloc_juicy_variables in H0.
 destruct a as [id' ty'].
 destruct (juicy_mem_alloc j 0 (@Ctypes.sizeof ge ty')) eqn:?H.
 rewrite (IHvars _ _ H0).
 rewrite PTree.gso; auto. contradict H5. subst; left; auto.
 contradict H5; right; auto.
}
rewrite H3. rewrite eqb_type_refl.
simpl in Hsize'. unfold sizeof.
rewrite <- (cenv_sub_sizeof HGG); auto.
rewrite prop_true_andp by auto.
assert (0 <= @Ctypes.sizeof ge ty <= Ptrofs.max_unsigned) by (pose proof (@Ctypes.sizeof_pos ge ty); lia).
simpl.
forget (@Ctypes.sizeof ge ty) as n.
clear - H2 H1 H4.
eapply juicy_mem_alloc_block; eauto.
unfold Ptrofs.max_unsigned in H4; lia.
Qed.

Lemma free_list_juicy_mem_ghost: forall m l m', free_list_juicy_mem m l m' ->
  ghost_of (m_phi m') = ghost_of (m_phi m).
Proof.
  induction 1; auto.
  rewrite IHfree_list_juicy_mem, <- H1.
  apply free_juicy_mem_ghost.
Qed.

Lemma alloc_juicy_variables_ghost: forall l ge rho jm,
  ghost_of (m_phi (snd (alloc_juicy_variables ge rho jm l))) = ghost_of (m_phi jm).
Proof.
  induction l; auto; simpl; intros.
  destruct a; simpl.
  rewrite IHl; simpl.
  apply ghost_of_make_rmap.
Qed.

Lemma map_snd_typeof_params:
  forall al bl, map snd al = map snd bl -> type_of_params al = type_of_params bl.
Proof.
induction al as [|[? ?]]; destruct bl as [|[? ?]]; intros; inv H; simpl; f_equal; auto.
Qed.

Lemma jsafeN_local_step':
  forall {Espec: OracleKind} ge ora s1 m s2 m2,
  cl_step  ge s1 (m_dry m) s2 (m_dry m2) ->
  resource_decay (nextblock (m_dry m)) (m_phi m) (m_phi m2) ->
  level m = S (level m2) /\
   ghost_of (m_phi m2) =ghost_fmap (approx (level m2)) (approx (level m2)) (ghost_of (m_phi m)) ->
  jsafeN (@OK_spec Espec) ge (level m2) ora s2 m2 ->
  jsafeN (@OK_spec Espec) ge (level m) ora s1 m.
Proof.
intros.
  rename H into Hstep.
  remember (level m) as N.
  destruct N; [constructor|].
  eapply jsafeN_step with
    (m' := m2).
  split3.
  apply Hstep.
  auto.
  rewrite HeqN in H1; auto.
  apply jm_bupd_intro.
  destruct H1. inv H.
  apply H2.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros; simpl; auto.
Qed.

Lemma guard_fallthrough_return:
 forall (Espec : OracleKind) (psi : genv) (f : function)
   (ctl : cont) (ek : exitkind) (vl : option val) 
  (te : temp_env) (ve : env) (rho' : environ)
  (P1 : Prop) (P2 P3 P5 : mpred)
  (P4 : (ffunc (fconst environ) fidentity) mpred)
  (n : nat),
  call_cont ctl = ctl ->
  (!! P1 && (P2 * bind_ret vl (fn_return f) P4 rho' * P5) && P3 >=>
    assert_safe Espec psi f ve te (exit_cont EK_return vl ctl) rho')  n ->
  (!! P1 && (P2 *proj_ret_assert (function_body_ret_assert (fn_return f) P4) ek
      vl rho' * P5) && P3 >=>
   assert_safe Espec psi f ve te (exit_cont ek vl ctl) rho') n.
Proof.
intros.
destruct ek; try solve [intros; simpl proj_ret_assert; normalize];
 unfold function_body_ret_assert, proj_ret_assert,
               RA_normal, RA_return.
destruct (type_eq (fn_return f) Tvoid).
2:{
intros ? ? ? ? [[_ [? [? [? [[? [? [? [_ [? ?]]]]] _]]]]] _].
destruct (fn_return f); contradiction.
}
destruct vl. normalize.
intros ? ? ? ? [[_ [? _]] _]; discriminate.
eapply subp_trans'; [ | eapply subp_trans'; [apply H0 | ]]; clear H0.
rewrite e.
apply derives_subp.
normalize.
apply andp_derives; auto. apply andp_derives; auto.
apply andp_left2; auto.
simpl exit_cont.
apply derives_subp.
apply own.bupd_mono.
intros ?. simpl.
destruct ctl; auto;
elimtype False; clear - H; simpl in H; set (k:=ctl) in *;
unfold k at 1 in H; clearbody k;
induction ctl; try discriminate; eauto.
Qed.

Lemma semax_call_aux2: 
 forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
  (A : TypeTree) 
  (P : forall ts : list Type,
     _functor (dependent_type_functor_rec ts (ArgsTT A)) mpred)
  (Q : forall ts : list Type,
     _functor (dependent_type_functor_rec ts (AssertTT A)) mpred)
  (ts : list Type)
  (x : _functor (dependent_type_functor_rec ts A) mpred) 
  (F : environ -> pred rmap)
  (F0 : assert)
  (ret : option ident)
  (curf : function)
  (fsig : typesig)
  (cc : calling_convention)
  (a : expr) (bl : list expr) (R : ret_assert) 
  (psi : genv) 
  (ora : OK_ty) (jm jmx : juicy_mem)
  (f : function)
  (*(NEP : args_super_non_expansive P)*)
  (NEQ : super_non_expansive Q)
  (Hora : app_pred (juicy_mem_op (ext_compat ora)) jm) 
  (TCret : tc_fn_return Delta ret (snd fsig))
  (TC5 : snd fsig = Tvoid -> ret = None)
  (H : closed_wrt_modvars (Scall ret a bl) F0)
  (HR : app_pred
       (ALL rho' : environ,
        |> ! ((EX old : val,
               substopt ret (`old) F rho' *
               maybe_retval (Q ts x) (snd fsig) ret rho') >=> 
              RA_normal R rho')) (m_phi jm))
  (HGG : cenv_sub cenv_cs (genv_cenv psi))
  (H13 : age1 jm = Some jmx)
  (COMPLETE : Forall
             (fun it : ident * type => complete_type cenv_cs (snd it) = true)
             (fn_vars f))
  (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
  (H17' : list_norepet (map fst (fn_vars f)))
  (H18 : fst fsig = map snd (fst (fn_funsig f)) /\
      snd fsig = snd (fn_funsig f) (*/\ list_norepet (map fst (fst fsig))*)),
forall vx tx k rho
  (H0 : rho = construct_rho (filter_genv psi) vx tx)
  (H1 : app_pred (|> rguard Espec psi Delta curf (frame_ret_assert R F0) k)
       (level (m_phi jm)))
  (TC3 : guard_environ Delta curf rho),
app_pred
  (!! closed_wrt_modvars (fn_body f) (fun _ : environ => F0 rho * F rho) &&
   rguard Espec psi (func_tycontext' f Delta) f
     (frame_ret_assert
        (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x))
           (stackframe_of' cenv_cs f)) (fun _ : environ => F0 rho * F rho))
     (Kcall ret curf vx tx k)) (level jmx).
Proof.
intros.
pose proof I.
assert (LATER : laterR (level (m_phi jm)) (level (m_phi jmx))). {
  apply laterR_level'. apply age_laterR. apply age_jm_phi. auto.
}
rename fsig0 into fsig.
set (ctl := Kcall ret curf vx tx k) in *.
do 2 pose proof I.
 split.
 repeat intro; f_equal.
 intros ek vl te ve.
 rewrite !proj_frame_ret_assert.
 unfold seplog.sepcon, seplog.LiftSepLog .
 remember ((construct_rho (filter_genv psi) ve te)) as rho'.
 simpl seplog.sepcon.
 rewrite <- (sepcon_comm (stackframe_of' cenv_cs f rho')). 
cut ((!! guard_environ (func_tycontext' f Delta) f rho' &&
 (stackframe_of' cenv_cs f rho' *
  bind_ret vl 
(fn_return f) (Q ts x) rho' * 
  (F0 rho * F rho)) && funassert (func_tycontext' f Delta) rho' >=>
 assert_safe Espec psi f ve te (exit_cont EK_return vl ctl) rho')
  (level jmx)). 
apply guard_fallthrough_return; auto.

 rewrite andp_assoc.
 apply prop_andp_subp; intro. simpl in H5.
 repeat rewrite andp_assoc.
 pose proof I.
 pose proof I.
 rewrite <- (sepcon_comm (F0 rho * F rho)).
 change (stackframe_of' cenv_cs f rho') with (stackframe_of f rho').

 intros wx ? w' ? ?.
 assert (level jmx >= level w')%nat.
 apply necR_level in H9.
 apply le_trans with (level wx); auto.
 clear wx H8 H9.
 apply own.bupd_intro; simpl.
 intros ora' jm' Hora' VR ?.
 subst w'.
 intro.
 case_eq (@level rmap ag_rmap (m_phi jm')); [intros; lia | intros n0 H21; clear LW ].
 rewrite <- level_juice_level_phi in H21.
 destruct (levelS_age1 jm' _ H21) as [jm'' H24].
 rewrite -> level_juice_level_phi in H21.
 assert (FL: exists m2, free_list (m_dry jm'')  (Clight.blocks_of_env psi ve) = Some m2). {
    rewrite <- (age_jm_dry H24).
    subst rho'.
    rewrite (sepcon_comm (stackframe_of f _)) in H10.
    repeat rewrite <- sepcon_assoc in H10.
    destruct H10 as [H10 _].
    eapply can_free_list; try eassumption.
    }
 unfold ctl. fold ctl.
 clear Hora ora (*NEP*) P.
 fold ctl.
 destruct FL as [m2 FL2].
 assert (H25: ve_of rho' = make_venv ve) by (subst rho'; reflexivity).
 assert (SFFB := stackframe_of_freeable_blocks Delta _ rho' _ ve HGG COMPLETE H17' H25 H5);
   clear HGG COMPLETE.
 clear H25.
 destruct (free_list_juicy_mem_i _ _ _ (F0 rho * F rho * bind_ret vl (fn_return f) (Q ts x) rho') FL2)
 as [jm2 [FL [H21' FL3]]].
 eapply sepcon_derives. apply SFFB. apply derives_refl.
 forget (F0 rho * F rho) as F0F.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (stackframe_of _ _)). rewrite sepcon_assoc.
 destruct H10 as [H22 _].
 eapply pred_nec_hereditary; try apply H22.
 apply laterR_necR. apply age_laterR. apply age_jm_phi; auto.
 subst m2.
 pose (rval := force_val vl).
 assert (jsafeN OK_spec psi (level jm2) ora'
             (Returnstate rval (call_cont ctl)) jm2). {
   assert (LATER2': (level jmx > level (m_phi jm2))%nat). {
     apply age_level in H24.
     repeat rewrite <- level_juice_level_phi in *. lia.
    } 
   assert (HH1 : forall a' : rmap,
     necR (m_phi jm2) a' ->
     (!! guard_environ Delta curf (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) &&
      seplog.sepcon (fun rho0 : environ => EX old : val, substopt ret (`old) F rho0 * maybe_retval (Q ts x) (snd fsig) ret rho0) F0
        (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) && funassert Delta (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx))) a' ->
     (assert_safe Espec psi curf vx (set_opttemp ret rval tx) (exit_cont EK_normal None k) (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx))) a').
   { intros. hnf in H1.
     assert (Help0: laterM (level (m_phi jm)) (level (m_phi jm2))). { 
       clear - LATER2' LATER.
       eapply necR_laterR. apply laterR_necR; eassumption.
       apply later_nat. rewrite <- !level_juice_level_phi in *. lia. }
     specialize (H1 _ Help0 EK_normal None (set_opttemp ret rval tx) vx); hnf in H1.
     assert (Help1: (level (m_phi jm2) >= level (m_phi jm2))%nat) by lia. 
     apply (H1 _ Help1 _ H8).
     rewrite proj_frame_ret_assert in H1.
     simpl proj_ret_assert in H1.
     rewrite proj_frame_ret_assert.
     simpl proj_ret_assert.
     destruct H9 as [[XX1 XX2] XX3]. split; trivial. split; trivial. clear XX1 XX3.
     destruct XX2 as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 _].
     exists u1, u2; split. trivial. split; [clear U2| trivial].
     assert (JMX: laterM (m_phi jm) (m_phi jmx)). { constructor. apply age_jm_phi. apply H13. }
     assert (JMX_u1: (level (m_phi jmx) >= level u1)%nat).
     { rewrite LevU1; clear -H8 LATER2' H2 H13. apply necR_level in H8. apply age_level in H13.
        rewrite <- !level_juice_level_phi in *. lia. }
     split. reflexivity.
     apply (HR (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) _ JMX _ JMX_u1 _ (necR_refl _) U1). 
   }
   clear H1.
   specialize (HH1 _ (necR_refl _)). simpl in H5.
   spec HH1; [clear HH1 | ].
   - split; [split |].
    + destruct H10 as [H22 _].
        destruct H18 as [H18 H18b].
        simpl. 
        destruct ret; unfold rval; [destruct vl | ].
        *
         assert (tc_val' (fn_return f) v).
           apply tc_val_tc_val'.
           clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
         unfold construct_rho. unfold set_opttemp. rewrite <- map_ptree_rel.
         apply guard_environ_put_te'. subst rho; auto.
         intros.
         cut (t = fn_return f). intros. rewrite H9; auto.
         hnf in TCret; rewrite H8 in TCret. subst; auto.
        *
         assert (f.(fn_return)=Tvoid).
         clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto.
         unfold fn_funsig in H18b. rewrite H1 in H18b. rewrite H18b in TC5. simpl in TC5.
         specialize (TC5 (eq_refl _)); congruence.
        * unfold set_opttemp. rewrite <- H0. auto.
    +
       destruct H10 as [H22a H22b].
       simpl seplog.sepcon.
       rewrite sepcon_comm in H22a|-*.
       rewrite sepcon_assoc in H22a.
       assert (bind_ret vl (fn_return f) (Q ts x) rho' * (F0 rho * F rho)
            |-- (maybe_retval (Q ts x) (snd fsig) ret (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) *
                   (F0 (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx)) *
                    EX old: val, substopt ret (`old) F (construct_rho (filter_genv psi) vx (set_opttemp ret rval tx))))). {
        apply sepcon_derives.
        *
         clear dependent a.
         clear Hora' H6 H7 ora'.
         destruct fsig as [f_params f_ret]. 
         simpl in H18; destruct H18 as [H18 H18b]; subst rho' f_ret.
         clear H22b VR. clear LATER2' jm2 FL FL2 FL3.
         unfold rval; clear rval.
         unfold bind_ret.
         unfold get_result1. simpl.
         unfold bind_ret.
         destruct vl.
         + (*apply derives_extract_prop; intro.*)
           unfold maybe_retval.
           destruct ret.
           - unfold get_result1; simpl.
             apply andp_derives.
             ++ apply prop_derives. intros ? ?. simpl. unfold eval_id; simpl.
                rewrite <- map_ptree_rel, Map.gss. simpl. apply H.
             ++ unfold env_set; simpl.
                unfold eval_id; simpl. rewrite <- map_ptree_rel, Map.gss. simpl; trivial.
           - unfold set_opttemp; simpl. unfold env_set; simpl. clear - TC5 H0.
              destruct (fn_return f); simpl; normalize.
             all: exists v; simpl; split; [ intros ? ; apply H | apply H1].
         +
           unfold fn_funsig in TC5. simpl in TC5.
           destruct (fn_return f) eqn:?; try apply FF_derives.
           specialize (TC5 (eq_refl _)). subst ret.
           unfold maybe_retval. apply derives_refl.
        *
          subst rho.
         destruct ret; apply sepcon_derives; auto.
         +
          clear - H.
          apply derives_refl'.
          apply H. intros. destruct (ident_eq i i0).
          subst; left; hnf; simpl. unfold insert_idset. rewrite PTree.gss; auto.
          right; unfold Map.get; simpl; unfold make_tenv; simpl.
          rewrite PTree.gso; auto.
        +
          simpl in TCret.
          destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
          subst t.
          destruct TC3 as [[TC3 _] _].
          hnf in TC3; simpl in TC3.
          specialize (TC3 _ _ Heqo).
          destruct TC3 as [old [? _]].
          apply exp_right with old. unfold substopt, subst.
          apply derives_refl'. f_equal.
          unfold env_set, construct_rho.
           f_equal. unfold make_tenv. extensionality j.
          simpl. unfold Map.set. if_tac. subst.
          apply H0. rewrite PTree.gso; auto.
        +
          apply exp_right with Vundef; simpl; auto.
       } 
      eapply derives_trans. 3: apply H1. apply derives_refl.
      normalize. intros v. exists v. rewrite <- sepcon_assoc. rewrite sepcon_comm in H8. apply H8.
      eapply free_list_juicy_mem_lem. eauto.
      eapply pred_nec_hereditary.
      apply laterR_necR. apply age_jm_phi in H24. apply age_laterR; eauto.
      eapply sepcon_derives; try apply H22a; auto.
   +
     destruct H10 as [H22a H22b].
     eapply pred_nec_hereditary in H22b.
     2:{  apply laterR_necR. apply age_jm_phi in H24. apply age_laterR; eauto. }
     rewrite VR in H22b; clear - FL H22b. {
      rewrite corable_funassert in H22b.
      rewrite corable_funassert.
      replace (core (m_phi jm2)) with (core (m_phi jm'')).
      apply H22b.
      clear - FL.
      induction FL; auto.
      rewrite <-IHFL.
      rewrite <- H1.
      rewrite free_juicy_mem_core; auto.
     }
  -
    clear - HH1.
    destruct (level jm2) eqn:H26; try solve [constructor];
    destruct (levelS_age _ _ (eq_sym H26)) as [jm2' [H27 ?]].
    subst n;
    apply jsafeN_step with (c' := State curf Sskip k vx (set_opttemp ret rval tx)) (m' := jm2');
    simpl.
    split; [ rewrite <- (age_jm_dry H27); constructor | ].
    split3;
    [ apply age1_resource_decay; auto | auto
    | apply age1_ghost_of; apply age_jm_phi; auto].
    eapply pred_nec_hereditary in HH1;
     [ | apply laterR_necR; apply age_jm_phi in H27; apply age_laterR; eauto];
    apply assert_safe_jsafe'; auto.
 }
   clear H1.
    destruct H18 as [H18 H18b].
    simpl.
    rewrite <- H21; clear n0 H21.
    destruct vl; intros; 
    (eapply jsafeN_local_step' with (m2 := jm2);
     [econstructor; eauto |  .. ]).
    1,5: rewrite (age_jm_dry H24); auto.
    1,4:
    eapply resource_decay_trans;
    [ | | eapply free_list_resource_decay; eauto];
    [ rewrite (age_jm_dry H24); apply Pos.le_refl |
      apply age1_resource_decay ].
    1,2: auto.
    1,3: split; [change (level (m_phi ?a)) with (level a); rewrite <- FL3; apply age_level in H24; lia |].
    1,2:rewrite (free_list_juicy_mem_ghost _ _ _ FL);
      erewrite age1_ghost_of by (eapply age_jm_phi; eauto);
      change (level (m_phi jm'')) with (level jm'');
      rewrite FL3; auto.
      change v with rval; auto.
      change Vundef with rval; auto.
Qed.

Lemma tc_eval_exprlist:
  forall {CS: compspecs} Delta tys bl rho m,
    typecheck_environ Delta rho ->
    (tc_exprlist Delta tys bl rho) m ->
    tc_vals tys (eval_exprlist tys bl rho).
Proof.
induction tys; destruct bl; simpl; intros; auto.
unfold tc_exprlist in H0. simpl in H0.
rewrite !denote_tc_assert_andp in H0.
destruct H0 as [[? ?] ?].
split.
unfold_lift.
eapply tc_val_sem_cast; eauto.
apply IHtys with m; auto.
Qed.

Lemma tc_vals_length: forall tys vs, tc_vals tys vs -> length tys = length vs.
Proof.
induction tys; destruct vs; simpl; intros; auto; try contradiction.
destruct H; auto.
Qed.

Lemma eval_exprlist_relate {CS}:
  forall (Delta : tycontext) (tys: typelist)
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
     (rho : environ) m,
   @denote_tc_assert CS (typecheck_exprlist Delta (typelist2list tys) bl) rho (m_phi m) ->
   typecheck_environ Delta rho ->
   cenv_sub cenv_cs (genv_cenv psi) ->
   rho = construct_rho (filter_genv psi) vx tx ->
   Clight.eval_exprlist psi vx tx (m_dry m) bl
     tys
     (eval_exprlist (typelist2list tys) bl rho).
Proof.
  intros.
  revert bl H; induction tys; destruct bl; simpl; intros; try contradiction H.
  constructor.
 rewrite !denote_tc_assert_andp in H.
 super_unfold_lift.
 destruct H as [[? ?] ?].
 specialize (IHtys bl H4).
 constructor 2 with (eval_expr e (construct_rho (filter_genv psi) vx tx)); auto.
 subst.
 eapply eval_expr_relate; eauto.
 pose proof (cast_exists Delta e t rho (m_phi m) H0 H H3).
 rewrite <- H5; clear H5.
 subst. 
 apply cop2_sem_cast'; try eassumption.
 eapply typecheck_expr_sound; eassumption.
Qed.

Lemma believe_exists_fundef:
  forall {Espec : OracleKind} {CS : compspecs}
    {b : block} {id_fun : ident} {psi : genv} {Delta : tycontext}
    {n: nat} {fspec: funspec}
  (Findb : Genv.find_symbol (genv_genv psi) id_fun = Some b)
  (Believe : app_pred (believe Espec Delta psi Delta) n)
  (H3: (glob_specs Delta) ! id_fun = Some fspec),
 {f : Clight.fundef |
  Genv.find_funct_ptr (genv_genv psi) b = Some f /\
  type_of_fundef f = type_of_funspec fspec }.
Proof.
intros.
destruct fspec as [[params retty] cc A P Q NEP NEQ].
simpl.
specialize (Believe (Vptr b Ptrofs.zero)
                  (params,retty) cc A P Q _ (necR_refl _)).
spec Believe.  { exists id_fun, NEP, NEQ. split; auto. exists b; split; auto. }
simpl (semantics.initial_core _). unfold j_initial_core.
simpl (semantics.initial_core _). unfold cl_initial_core.
destruct (Genv.find_funct_ptr psi b) as [f|] eqn:Eb; swap 1 2.
{ exfalso.
  destruct Believe as [H | (b' & fu & (? & WOB & ASD) & WOBk)].
  + unfold believe_external in *.
    unfold Genv.find_funct in *. rewrite if_true in H by trivial.
    simpl in Eb, H. rewrite Eb in H. auto. 
  + assert (b' = b) by congruence. simpl in WOB, Eb. subst b'. congruence.
}
exists f; split; auto.
destruct Believe as [BE|BI].
 - unfold believe_external in *.
    simpl in BE. if_tac [_|?] in BE. 2:tauto.
    rewrite Eb in BE.
    destruct f as [ | ef sigargs sigret c'']. tauto.
    simpl.
    destruct BE as [((Es & -> & ASD & _) & ?) _].
    inv Es. f_equal. rewrite TTL3; trivial.
 -
    destruct BI as (b' & fu & (? & WOB & ? & ? & ? & ? & wob & ? & ?) & _).
    unfold fn_funsig in *. simpl fst in *; simpl snd in *. 
    assert (b' = b) by congruence. subst b'.
    simpl in Eb, WOB. assert (f = Internal fu) by congruence. subst.
    simpl.
    unfold type_of_function.
    f_equal.
    forget (fn_params fu) as l. clear. rewrite TTL1; trivial.
Qed.

Lemma eval_exprlist_relate' {CS}:
  forall (Delta : tycontext) (tys: typelist)
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env)
     (rho : environ) m tys',
   @denote_tc_assert CS (typecheck_exprlist Delta (typelist2list tys) bl) rho (m_phi m) ->
   typecheck_environ Delta rho ->
   cenv_sub cenv_cs (genv_cenv psi) ->
   rho = construct_rho (filter_genv psi) vx tx ->
   tys' = typelist2list tys ->
   Clight.eval_exprlist psi vx tx (m_dry m) bl
     tys
     (eval_exprlist tys' bl rho). 
Proof. intros. subst tys'. eapply eval_exprlist_relate; eassumption. Qed.

Lemma tc_vals_Vundef {args ids} (TC:tc_vals ids args): Forall (fun v : val => v <> Vundef) args. 
Proof.
generalize dependent ids. induction args; intros. constructor.
destruct ids; simpl in TC. contradiction. destruct TC.
constructor; eauto. intros N; subst. apply (tc_val_Vundef _ H).
Qed.

Lemma semax_call_aux {CS Espec}
  (Delta : tycontext) (psi : genv) (ora : OK_ty) (jm : juicy_mem) (b : block) (id : ident) cc
  A deltaP deltaQ NEP' NEQ' retty clientparams
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
  (F : environ -> pred rmap) 
  (F0 : assert) (ret : option ident) (curf: function) args (a : expr)
  (bl : list expr) (R : ret_assert) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (Hora : juicy_mem_op (ext_compat ora) jm)

  (Bel: believe Espec Delta psi Delta (level (m_phi jm)))
  (Spec: (glob_specs Delta)!id = Some (mk_funspec (clientparams, retty) cc A deltaP deltaQ NEP' NEQ'))
  (FindSymb: Genv.find_symbol psi id = Some b)

  (Classify: Cop.classify_fun (typeof a) = Cop.fun_case_f ((*type_of_params*)typelist_of_type_list clientparams) retty cc)
  (TCRet: tc_fn_return Delta ret retty)
  (TCA: (|>tc_expr Delta a rho) (m_phi jm))
  (TCbl: (|>tc_exprlist Delta clientparams bl rho) (m_phi jm))
  (Argsdef: args = eval_exprlist clientparams bl rho)
  (GuardEnv: guard_environ Delta curf rho)
  (Hretty: retty =Tvoid -> ret=None)
  (CLosed: closed_wrt_modvars (Scall ret a bl) F0)
  nQ
  (*(HR: ( ALL rho' : environ , |>
       !((EX old:val, substopt ret old F rho' * maybe_retval (nQ ts x) retty ret rho') >=> (RA_normal R rho') )) (m_phi jm))*)
 
  (HR: ( ALL rho' : environ , |>
       !((EX old:val, (*!!(tc_val' retty old) &&*)
                     substopt ret (`old) F rho' * maybe_retval (nQ ts x) retty ret rho') >=> (RA_normal R rho') )) (m_phi jm))
  (CSUB: cenv_sub (@cenv_cs CS) (genv_cenv psi))
  (Hrho: rho = construct_rho (filter_genv psi) vx tx)
  (EvalA: eval_expr a rho = Vptr b Ptrofs.zero)
  (Funassert: funassert Delta rho (m_phi jm))
  (RGUARD: (|> rguard Espec psi Delta curf (frame_ret_assert R F0) k) (level (m_phi jm)))
  
  
  (PostAdapt: forall  (vl : fconst environ mpred),
        (! |> (deltaQ ts x vl <=> nQ ts x vl)) (m_phi jm))

  (PRE: (|>(F0 rho * F rho * deltaP ts x (ge_of rho, args))) (m_phi jm)):
   jsafeN (@OK_spec Espec) psi (level (m_phi jm)) ora
     (State curf (Scall ret a bl) k vx tx) jm.
Proof.
destruct (believe_exists_fundef FindSymb Bel Spec)
  as [ff [H16 H16']].
rewrite <- Genv.find_funct_find_funct_ptr in H16.

case_eq (level (m_phi jm)); [solve [simpl; constructor] | intros n H2].
rewrite <- level_juice_level_phi in H2.
destruct (levelS_age1 _ _ H2) as [jmx H13].
rewrite <- H2.
apply jsafeN_local_step
 with (s2 :=  Callstate ff (eval_exprlist clientparams bl rho)
                                     (Kcall ret curf vx tx k)). {
 clear - EvalA TCA H13 GuardEnv Classify H16 CSUB Hrho TCbl H16'.
 (*assert (H88: snd (split clientparams) = typelist2list (type_of_params clientparams))
   by (rewrite <- TTL1, snd_split, TTL1; apply TTL4). *)
 eapply step_call with (vargs:=eval_exprlist clientparams bl rho); try eassumption.
 rewrite <- EvalA.
 erewrite age_jm_dry by eauto.
 eapply eval_expr_relate; try solve[rewrite H0; auto]; auto. destruct GuardEnv; eassumption.
 eapply TCA. apply age_laterR; apply age_jm_phi; auto.
(* rewrite H88.*)
 erewrite age_jm_dry by eauto. 
 eapply eval_exprlist_relate' with Delta.
 + clear - (*H88*) H13 TCbl (*Hparamtypes*). (* rewrite snd_split in H88.
   rewrite H88 in TCbl.*)
   rewrite TTL5. eapply TCbl. apply age_laterR; apply age_jm_phi; auto. 
 + destruct GuardEnv ; auto.
 + assumption.
 + auto.
 + rewrite TTL5; trivial.
}
intros jm2 H22.
assert (jmx = jm2). {clear - H13 H22. red in H22. congruence. }
subst jmx.

specialize (TCA _ (age_laterR (age_jm_phi H13))).
specialize (TCbl _ (age_laterR (age_jm_phi H13))).
specialize (PRE _ (age_laterR (age_jm_phi H13))).
specialize (RGUARD _ (laterR_level' (age_laterR (age_jm_phi H13)))).
apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))) in Funassert.
apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))) in Hora.
assert (LATER: laterR (level (m_phi jm)) n) by (constructor 1; rewrite <- level_juice_level_phi, H2; reflexivity).

assert (TC8 := tc_eval_exprlist _ _ _ _ _ (proj1 GuardEnv) TCbl).
assert (Hargs: Datatypes.length clientparams = 
                 Datatypes.length (eval_exprlist clientparams bl rho)). {
 clear - TCbl.
 revert bl TCbl; induction clientparams; destruct bl; intros; try contradiction.
 reflexivity.
 unfold tc_exprlist in TCbl. simpl in TCbl. rewrite !denote_tc_assert_andp in TCbl.
 destruct TCbl as [[? ?] ?].
 simpl. f_equal; auto.
}
subst args.
set (args := eval_exprlist clientparams bl rho) in *.
clearbody args.
assert (ArgsNotVundef:= tc_vals_Vundef TC8).
assert (H11': forall vl : environ, (! |> (deltaQ ts x vl <=> nQ ts x vl)) (m_phi jm2)). {
  intro vl.
  apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))); auto.
}

clear PostAdapt; rename H11' into H11.

apply (pred_nec_hereditary _ _ _ (laterR_necR (age_laterR (age_jm_phi H13)))) in HR.

apply age_level in H13.
assert (n = level jm2) by congruence.
subst n.

clear TCbl TCA EvalA.
set (ctl := Kcall ret curf vx tx k).
change (level (m_phi jm)) with (level jm) in Bel.
rewrite H2 in Bel.
clear jm LATER H22 H2 H13.
rename jm2 into jm.

(*destruct fsig as [params retty].*)
unfold type_of_funspec, rettype_of_funspec in H16'; simpl in H16'.
simpl fst in *; simpl snd in *.
assert (H2 := I).

(*exploit exactly the nQ=deltaQ equality, to obtain the assertion ocurring in Spec: Delta!id = ...*)
assert (HR':  (ALL rho' : environ,
      |> ! ((EX old : val,
             (*!! tc_val' retty old && *)substopt ret (`old) F rho' *
             maybe_retval (deltaQ ts x) retty ret rho') >=> 
            RA_normal R rho')) (m_phi jm)). {
 clear - HR H11.
 intros rho'; specialize (HR rho').
 intros ? ? ? ? ? ? [old ?].
 apply (HR a' H y H0 a'0 H1); clear HR.
 exists old.
 revert a'0 H1 H2.
 eapply sepcon_subp'; try apply H0.
 apply derives_subp; apply derives_refl.
 intros ? ?.
 unfold maybe_retval; destruct ret.
 intros ? ? [? ?]. split; trivial.
 { eapply H11; [ apply (laterR_level' H) | apply H1 | apply H2 | apply H4]. }
 destruct retty;
 [apply (H11 _ (level a')); auto; apply (laterR_level' H) 
 |  intros ? ?  [v [TCv ?]]; exists v; split; [ trivial | clear TCv; revert a'0 H2 H3;
  apply (H11 _ (level a')); auto; apply (laterR_level' H)] .. ].
}
rewrite closed_wrt_modvars_Scall in CLosed.
clear a bl Classify.

(*reestablish 
clear Q HR H11; rename HR' into HR; rename Q' into Q; assert (H11 := I).*)
rename NEQ' into NEQ.

(*** cut here *****)

assert (Prog_OK' := Bel).
specialize (Prog_OK' (Vptr b Ptrofs.zero)
     (clientparams, retty) cc A deltaP deltaQ _ (necR_refl _)).

spec Prog_OK'.
{ hnf. exists id, NEP', NEQ; split; auto.
  exists b; split; auto.
}
clear Spec FindSymb id.
change (level (m_phi jm)) with (level jm) in Prog_OK'.
(*apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK'.*)
assert (H9: necR (S (level jm)) (level jm)).
 apply laterR_necR; apply age_laterR; reflexivity.
apply (pred_nec_hereditary _ _ _ H9) in Bel. clear H9.

destruct Prog_OK' as [H5|H5].
{ (*external case *)
  eapply semax_call_external; try apply H5 (*.  with (P:=P)(Q:=Q)*); try eassumption. }

(* internal case*)

apply (pred_nec_hereditary _ _ (level jm)) in H5.
2: apply laterR_necR; apply age_laterR; constructor.

red in GuardEnv.
(*(*TEST*)clear HR *)
destruct H5 as [b' [f [[H3a [H3b ?]] H19]]].
injection H3a; intro; subst b'; clear H3a.
change (Genv.find_funct psi (Vptr b Ptrofs.zero) = Some (Internal f)) in H3b.
rewrite H16 in H3b. injection H3b; clear H3b; intros; subst ff.
destruct H as [COMPLETE [H17 [H17' [Hvars [H18 H18']]]]].
simpl fst in *; simpl snd in *.
assert (H3 := True).

specialize (H19 Delta CS _ (necR_refl _)).
spec H19. { intro; apply tycontext_sub_refl. }
specialize (H19 _ (necR_refl _) (cenv_sub_refl) ts x).
red in H19.

change (level (m_phi jm)) with (level jm) in *.
clear H2. destruct (level jm) eqn:H2; [constructor |].
destruct (levelS_age1 _ _ H2) as [jm2 H13]. change (age jm jm2) in H13.
rewrite <- H2 in *. clear H2. pose proof I.
specialize (H19 _ (laterR_level' (age_laterR H13))).
rewrite semax_fold_unfold in H19.
specialize (H19 _ _ _ _ (necR_refl _) 
     (conj (tycontext_sub_refl _) (conj cenv_sub_refl CSUB))  _ (necR_refl _) 
      (pred_nec_hereditary  _ _ _ (necR_level' (laterR_necR (age_laterR H13))) Bel)
                      ctl (fun _: environ => F0 rho * F rho) f _ (necR_refl _)).
clear Bel.
spec H19.
{ eapply semax_call_aux2 with (bl:=nil)(a:=Econst_int Int.zero tint)(R:=R)(jm:=jm)(fsig:=(clientparams, retty)); 
    simpl fst; simpl snd; try assumption.
   - apply Hora.
   - rewrite closed_wrt_modvars_Scall; auto.
   - tauto.  
   - apply now_later; apply RGUARD. }

remember (alloc_juicy_variables psi empty_env jm (fn_vars f)) eqn:AJV.
destruct p as [ve' jm']; symmetry in AJV.
destruct (alloc_juicy_variables_e _ _ _ _ _ _ AJV) as [H15 [H20' CORE]].
assert (MATCH := alloc_juicy_variables_match_venv _ _ _ _ _ AJV).
assert (H20 := alloc_juicy_variables_resource_decay _ _ _ _ _ _ AJV).
destruct (build_call_temp_env f args)
as [te' H21]; auto. 
  { rewrite <- Hargs. subst. rewrite map_length; trivial. }
pose proof (age_twin' _ _ _ H20' H13) as [jm'' [_ H20x]].
rewrite (age_level _ _ H13).
apply jsafeN_step
  with (c' := State f (f.(fn_body)) ctl ve' te')
       (m' := jm''); auto.
split; auto.
apply step_internal_function.
apply list_norepet_append_inv in H17; destruct H17 as [H17 [H22 H23]]; constructor; auto.
rewrite <- (age_jm_dry H20x); auto.
split.
 destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
 apply age1_resource_decay; auto.
 split.
 rewrite H20'; apply age_level; auto.
 erewrite <- (alloc_juicy_variables_ghost _ _ _ jm), AJV; simpl.
 apply age1_ghost_of, age_jm_phi; auto.

assert (H22: (level jm2 >= level jm'')%nat)
  by (apply age_level in H13; apply age_level in H20x; lia).
pose (rho3 := mkEnviron (ge_of rho) (make_venv ve') (make_tenv te')).
assert (H23: app_pred (funassert Delta rho3) (m_phi jm'')). {
  apply (resource_decay_funassert _ _ (nextblock (m_dry jm)) _ (m_phi jm'')) in Funassert.
  2: apply laterR_necR; apply age_laterR; auto.
  unfold rho3; clear rho3.
  apply Funassert.
  rewrite CORE. apply age_core. apply age_jm_phi; auto.
  destruct H20;  apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm'); auto.
   apply age1_resource_decay; auto.
}
specialize (H19 te' ve' _ H22 _ (necR_refl _)).
spec H19; [clear H19|]. {
 split; [split |]; auto.
 3:{ unfold rho3 in H23. unfold construct_rho. rewrite Hrho in H23.
     simpl ge_of in H23. auto.
  }
 split; [ | simpl; split; [ | reflexivity]; apply MATCH ].
 -
  rewrite (age_jm_dry H20x) in H15.
  clear - (*Hparamtypes*) H18 Hrho GuardEnv TC8 H18 H16 H21 H15 H23 H17 H17' H13.
  unfold rho3 in *. simpl in *. destruct H23.
  destruct rho. inv Hrho. simpl in *.
  remember (split (fn_params f)). destruct p.
  simpl in *. if_tac in H16; try congruence.
  destruct GuardEnv as [[_ [_ TC5]] _].
  eapply semax_call_typecheck_environ with (jm := jm2)(jm':=jm'')(args:=args); try eassumption.
  * erewrite <- age_jm_dry by apply H13; auto.
  * rewrite snd_split; apply TC8.
-
 normalize.
 split; auto. unfold rho3 in H23. unfold construct_rho. rewrite Hrho in H23.
 simpl ge_of in H23. auto.
 unfold bind_args.
 unfold tc_formals.
 normalize.
 rewrite <- sepcon_assoc.
 normalize.
 simpl fst in H18; simpl snd in H18.
 split.
 +
 hnf.
 destruct H18' as [H18b H18']. simpl snd in *.
 subst retty.
(* rewrite snd_split in TC8.*)
 subst clientparams. (*replace (map snd clientparams) with (map snd (fn_params f)) in TC8.*)
 * clear - TC8 H21 H17.
   simpl in *.
   match goal with H: tc_vals _ ?A |- tc_vals _ ?B => replace B with A; auto end.
   rewrite list_norepet_app in H17. destruct H17 as [H17 [_ _]].
   clear - H17 H21.
   forget (create_undef_temps (fn_temps f)) as te.
   revert  args te te' H21 H17.
   induction (fn_params f); destruct args; intros; auto; try discriminate.
   destruct a; inv H21.
   destruct a. simpl in H21. inv H17.
   simpl. f_equal. unfold eval_id, construct_rho; simpl.
   inv H21.
   erewrite pass_params_ni; try eassumption.
   rewrite PTree.gss. reflexivity.
   eapply IHl; try eassumption.
 (** rewrite <- H18; trivial.*)
+
 forget (F0 rho * F rho) as Frame.
 destruct H18' as [H18b H18']. simpl snd in *.
 (*rewrite <- snd_split in H18;*) rewrite H18 in *.
 (*rewrite @snd_split in *.*)
 simpl @fst in *.
 apply (alloc_juicy_variables_age H13 H20x) in AJV.
 forget (fn_params f) as fparams.
 clear - H18 H21 PRE AJV H17 H17' Hrho Hvars CSUB COMPLETE H13 ArgsNotVundef.

 assert (app_pred (Frame * close_precondition (map fst fparams)
                              (deltaP ts x)
                              (construct_rho (filter_genv psi) ve' te')) (m_phi jm2)). {
   eapply pred_nec_hereditary.
   - apply laterR_necR. apply age_laterR. eapply age_jm_phi. apply H13.
   - eapply sepcon_derives; try apply PRE; auto.
     subst rho. apply list_norepet_app in H17; destruct H17.
     clear - H21 ArgsNotVundef H.
     eapply make_args_close_precondition; eassumption.
  }
  clear PRE.
  forget (Frame * close_precondition (map fst fparams) ((deltaP ts x))
   (construct_rho (filter_genv psi) ve' te')) as Frame2.
  clear - H17' H21 AJV H Hvars CSUB COMPLETE.
  change (stackframe_of' cenv_cs) with stackframe_of.
  eapply alloc_juicy_variables_lem2; eauto.
  unfold var_sizes_ok in Hvars;
  rewrite Forall_forall in Hvars, COMPLETE |- *.
  intros.
  specialize (COMPLETE x H0).
  specialize (Hvars x H0).
  rewrite (cenv_sub_sizeof CSUB); auto.
}
replace (level jm2) with (level jm'') 
  by (clear - H13 H20x H20'; apply age_level in H13; apply age_level in H20x; lia).
eapply assert_safe_jsafe, own.bupd_mono, H19.
intros ? Hsafe ?? Hora0 ??.
subst; specialize (Hsafe ora0 _ Hora0 eq_refl eq_refl).
clear - Hsafe.
intros.
specialize (Hsafe LW).
simpl in Hsafe.
case_eq (@level rmap ag_rmap (m_phi jm0)); intros; [lia | clear LW ].
rewrite H in Hsafe.
auto.
Qed.

Lemma semax_call_aux' {CS Espec}
  (Delta : tycontext) (psi : genv) (ora : OK_ty) (jm : juicy_mem) (b : block) (id : ident) cc
  A deltaP deltaQ NEP' NEQ' retty clientparams
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
  (F : environ -> pred rmap) 
  (F0 : assert) (ret : option ident) (curf: function) args (a : expr)
  (bl : list expr) (R : ret_assert) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (Hora : juicy_mem_op (ext_compat ora) jm)

  (Bel: believe Espec Delta psi Delta (level (m_phi jm)))
  (Spec: (glob_specs Delta)!id = Some (mk_funspec (clientparams, retty) cc A deltaP deltaQ NEP' NEQ'))
  (FindSymb: Genv.find_symbol psi id = Some b)

  (Classify: Cop.classify_fun (typeof a) = Cop.fun_case_f (*(type_of_params*)(typelist_of_type_list clientparams) retty cc)
  (TCRet: tc_fn_return Delta ret retty)
  (TCA: (|>tc_expr Delta a rho) (m_phi jm))
  (TCbl: (|>tc_exprlist Delta clientparams bl rho) (m_phi jm))
  (Argsdef: args = eval_exprlist clientparams bl rho)
  (GuardEnv: guard_environ Delta curf rho)
  (Hretty: retty =Tvoid -> ret=None)
  (CLosed: closed_wrt_modvars (Scall ret a bl) F0)
  nQ
  (HR: ( ALL rho' : environ ,
       !((EX old:val, (*!!(tc_val' retty old) &&*) substopt ret (`old) F rho' * maybe_retval (nQ ts x) retty ret rho') >=> (RA_normal R rho') )) (m_phi jm))
  (CSUB: cenv_sub (@cenv_cs CS) (genv_cenv psi))
  (Hrho: rho = construct_rho (filter_genv psi) vx tx)
  (EvalA: eval_expr a rho = Vptr b Ptrofs.zero)
  (Funassert: funassert Delta rho (m_phi jm))
  (RGUARD: rguard Espec psi Delta curf (frame_ret_assert R F0) k
        (level (m_phi jm))) (*rguard Espec psi Delta curf (frame_ret_assert R F0) k) (level (m_phi jm)))*)
  
  
  (PostAdapt: forall  (vl : fconst environ mpred),
        (! |> (deltaQ ts x vl <=> nQ ts x vl)) (m_phi jm))

  (PRE: (|>(F0 rho * F rho * deltaP ts x (ge_of rho, args))) (m_phi jm)):
jsafeN (@OK_spec Espec) psi (level (m_phi jm)) ora
     (State curf (Scall ret a bl) k vx tx) jm.
Proof. intros. apply now_later in HR. apply now_later in RGUARD. rewrite box_all in HR.
eapply semax_call_aux; eassumption. 
Qed.
 
Lemma semax_call {CS Espec}:
  forall Delta (A: TypeTree)
  (P : forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: args_super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|>(tc_expr Delta a rho && tc_exprlist Delta argsig bl rho))  &&
           (func_ptr (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret (`old) F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof.
rewrite semax_unfold. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TCF TC5 TC7.
rename argsig into clientparams. rename retsig into retty.
intros.
rename H into Closed; rename H0 into RGUARD.
intros tx vx.
intros ? ? ? NecR_ya' [[TC3 ?] funassertDelta'].

assert (NecR_wa': necR w (level a')).
{ apply nec_nat. apply necR_level in NecR_ya'. apply le_trans with (level y); auto. }
eapply pred_nec_hereditary in RGUARD; [ | apply NecR_wa'].
eapply pred_nec_hereditary in Prog_OK; [ | apply NecR_wa'].
clear w NecR_wa' NecR_ya' y H.
rename a' into w.

assert (TC7': tc_fn_return Delta' ret retty).
{
  clear - TC7 TS.
  hnf in TC7|-*. destruct ret; auto.
  destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
  destruct TS.
  specialize (H i); rewrite Heqo in H. subst t.
  destruct ((temp_types Delta') ! i ).
  destruct H; auto.
  auto.
} clear TC7.
rewrite !later_andp in H0.
apply extend_sepcon_andp in H0; auto.
destruct H0 as [[TC1 TC2] pre].

normalize in pre. (*unfold func_ptr in *. hnf in pre.*)
destruct pre as [preA preB]. destruct preA as [b [EvalA funcatb]].
destruct preB as [z1 [z2 [JZ [HF0 pre]]]].
destruct (level w) eqn: Hl.
{ apply own.bupd_intro; repeat intro.
  rewrite Hl; constructor. }
rewrite <- Hl in *.
destruct (levelS_age w n) as (w' & Hage & Hw'); auto.

hnf in funcatb. 

destruct funcatb as [nspec [GS funcatb]]. simpl in GS.
rename GS into SubClient.

assert (Hpsi: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
unfold filter_genv in Hpsi.
remember (construct_rho (filter_genv psi) vx tx) as rho.

set (args := @eval_exprlist CS clientparams bl rho).
set (args' := @eval_exprlist CS' clientparams bl rho).

assert (MYPROP: exists id fs, 
          Map.get (ge_of rho) id = Some b /\ 
         (glob_specs Delta') ! id = Some fs /\ func_at fs (b, 0) w).
{ clear - funcatb funassertDelta' SubClient JZ.
  assert (XX: exists id:ident, (Map.get (ge_of rho) id = Some b)
                               /\ exists fs, (glob_specs Delta')!id = Some fs).
  
  { destruct funassertDelta' as [_ FD]. 
    apply (FD b (clientparams, retty) cc _ (necR_refl _)); clear FD.
    simpl. destruct nspec. hnf in funcatb. simpl in SubClient.
    destruct SubClient as [[? ?] _]; subst.
    (*specialize (typesigs_match_typesigs_eq H); intros TS. rewrite <- TS.*)
    eexists. apply funcatb. }
  destruct XX as [id [Hb [fs specID]]]; simpl in Hb.

  assert (exists v, Map.get (ge_of rho) id = Some v /\ func_at fs (v, 0) w).
  { destruct funassertDelta' as [funassertDeltaA _].
    destruct (funassertDeltaA id fs _ (necR_refl _) specID) as [v [Hv funcatv]]; simpl in Hv.
    exists v; split; trivial. }
  destruct H as [v [Hv funcatv]].
  assert (VB: b=v); [inversion2 Hb Hv; trivial | subst; clear Hb].
  exists id, fs; auto. }
destruct MYPROP as [id [fs [RhoID [SpecOfID funcatv]]]].
destruct fs as [fsig' cc' A' deltaP deltaQ NEP' NEQ']. 

unfold func_at in funcatv, funcatb. destruct nspec as [nsig ncc nA nP nQ nP_ne nQ_ne].
destruct SubClient as [[NSC Hcc] ClientAdaptation]; subst cc. destruct nsig as [nparams nRetty].

(*specialize (typesigs_match_rettypes NSC); simpl snd; intros; subst nRetty.*) inversion NSC; subst nRetty nparams.
destruct fsig' as [fArgsig fRettp].
hnf in funcatb, funcatv.
 inversion2 funcatb funcatv.
assert (PREPOST: (forall ts (x:dependent_type_functor_rec ts nA mpred) vl, (! |> (deltaP ts x vl <=> nP ts x vl)) w) /\
                 (forall ts (x:dependent_type_functor_rec ts nA mpred) vl, (! |> (deltaQ ts x vl <=> nQ ts x vl)) w)).
{ symmetry in H4. apply inj_pair2 in H4; 
  apply (function_pointer_aux); trivial. f_equal; apply H4. }
clear H4; destruct PREPOST as [Hpre Hpost].
simpl fst in *; simpl snd in *.

(*assert (LenTypes: length (map snd fArgsig) = length (map snd nparams)) by (rewrite H0; trivial).
assert (LenArgs: length fArgsig = length nparams) by (rewrite 2 map_length in LenTypes; trivial).

assert (ParamsEQ: map fst fArgsig = map fst nparams) by (apply check_normalized_unique_idents; trivial).
assert (fArgsig = nparams) by (apply map_fst_snd_eq; trivial).*)

(*subst fArgsig. clear ParamsEQ LenTypes LenArgs H0 fNorm.*) simpl in ClientAdaptation.
(*unfold funspec_normalized in nNorm; simpl in nNorm.*)

fold args in pre. clear Hpsi. 
set (rho := construct_rho (filter_genv psi) vx tx).
(*destruct GS as [? [? GS]]; subst fsig' cc'.*)

  assert (typecheck_environ Delta rho) as TC4.
{ clear - TC3 TS.
  destruct TC3 as [TC3 TC4].
  eapply typecheck_environ_sub in TC3; [| eauto].
  auto.
}

assert (HARGS: args = args').
{ clear - Hage HGG TC4 TC2.
  assert (ARGSEQ: (|> (!! (args = args'))) w). trivial.
  { hnf; intros. specialize (TC2 _ H). subst args args'.
    simpl. destruct HGG as [CSUB HGG].
     apply (typecheck_exprlist_sound_cenv_sub CSUB Delta rho TC4 a'); apply TC2. }
  eapply (ARGSEQ w'). apply age_laterR; trivial. }

eapply later_derives in TC2; [|apply (tc_exprlist_sub _ _ _ TS); auto].
eapply later_derives in TC1; [|apply (tc_expr_sub _ _ _ TS); auto].

assert (LENargs: Datatypes.length clientparams = Datatypes.length args).
{ clear - TC2 Hage. subst args.
  apply age_laterR in Hage. simpl in TC2.
  specialize (TC2 _ Hage). apply tc_exprlist_length in TC2. 
  clear - TC2.
  forget clientparams as m.
  generalize dependent m. clear. induction bl; simpl; intros.
  destruct m; simpl. trivial. inv TC2. destruct m; inv TC2. simpl.
  rewrite (IHbl _ H0); trivial. }

simpl in ClientAdaptation.

assert (HPP: (|> (F0 rho * F rho * (P ts x) (ge_of rho, args)))%pred w).
{ clear - pre JZ HF0 HGG TC1 TC2.
  rewrite sepcon_assoc. rewrite later_sepcon. exists z1, z2; split; trivial.
  split; [ apply now_later |]; trivial. }

simpl in EvalA. clear pre JZ HF0 z1 z2.
rewrite later_sepcon in HPP.
destruct HPP as [w1 [w2 [J [W1 W2]]]]; destruct (join_level _ _ _ J) as [LevW1 LevW2].
destruct (age1_join2 _ J Hage) as [w1' [w2' [J' [Age1 Age2]]]].

assert (TRIV: (forall rho, typecheck_temp_environ rho (PTree.empty type)) /\
              (typecheck_var_environ (Map.empty (block * type)) (PTree.empty type)) /\ 
              (forall rho, typecheck_glob_environ rho (PTree.empty type))).
{ clear. split.
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } split. 
  { intros; hnf; intros. split; intros. rewrite PTree.gempty in H; congruence. 
    destruct H. unfold Map.empty, Map.get in H; congruence. } 
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } }

assert (TCD': tc_environ Delta' rho) by eapply TC3.

assert (LA2: laterM w2 w2'). { constructor; trivial. }
(*assert (TCARGS: tc_environ (funsig_tycontext (clientparams, retty)) 
             (make_args (map fst clientparams) args rho)).
{ assert (LaterW': laterR w w'). constructor; trivial.
  specialize (TC2 _ LaterW'). subst args.
  apply (tc_environ_make_args' clientparams retty bl rho Delta' TCD' _ TC2).  }*)

specialize (ClientAdaptation ts x (ge_of rho, args)). simpl in ClientAdaptation.

destruct (ClientAdaptation w2') as [ts1 [x1 [G [PreAdapt PostAdapt]]]]; clear ClientAdaptation.
{(* clear - LENargs (*TCARGS*) Age2 W2.*)
  simpl; split. 
(*  + red. simpl. apply TRIV.*)
  + clear - TC3 LENargs TC2 W2 Hage. destruct TC3. 
    apply age_laterR in Hage. specialize (TC2 w' Hage).
    specialize (tc_eval_exprlist _ _ _ _ _ H TC2).
    subst args.
    forget (construct_rho (filter_genv psi) vx tx) as lia.
    forget  (@eval_exprlist CS clientparams bl lia) as args.
    clear.
    generalize dependent clientparams.
    clear. induction args; simpl; intros.
    - destruct clientparams; simpl in *. constructor. contradiction.
    - destruct clientparams; simpl in *. contradiction. destruct H.
      apply tc_val_has_type in H. apply IHargs in H0.
      constructor; eauto.
  + apply age_laterR in Age2. apply (W2 _ Age2). }
simpl in PostAdapt.

(*hnf in PreAdapt.*) simpl typesig_of_funspec in *.
clear W2 NEP P.

specialize (Hpre ts1 x1).
assert (ARGS: app_pred (|> (F0 rho *
     (F rho * G) * deltaP ts1 x1 (ge_of rho, args))) w).
{ clear Hpost PostAdapt SpecOfID Prog_OK RhoID TC7' RGUARD funcatb. rewrite HARGS in *.
  assert (XX: (|> (F0 rho * F rho * G * 
                 (deltaP ts1 x1) (ge_of rho, args))) w).
  { rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite <- sepcon_assoc.
    rewrite later_sepcon.
    exists w1, w2; split. trivial. split. trivial. hnf; intros.
    destruct (age_later Age2 H); [ subst a' |].
    - (*w2'=a'*)
      destruct PreAdapt as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 LevU2].
      exists u1, u2; split; trivial. split; trivial. clear TRIV.
      assert (LatWU2: laterM (level w) (level u2)). { rewrite LevU2, <- LevW2 . apply laterR_level'; trivial. }
      eapply (Hpre _ (level u2) LatWU2); [| apply necR_refl | trivial]. lia.
      rewrite HARGS. apply U2.
    - apply now_later in PreAdapt. specialize (PreAdapt _ H0).
      destruct PreAdapt as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 LevU2]. 
      exists u1, u2; split; trivial. split; trivial.
      assert (LatWU2: laterM (level w) (level u2)). { rewrite LevU2, <- LevW2 . apply laterR_level'; trivial. }
      eapply (Hpre _ (level u2) LatWU2); [| apply necR_refl | trivial]. lia.
      rewrite HARGS. apply U2. }
  subst rho. clear - XX HARGS args args'. rewrite 2 sepcon_assoc. rewrite 2 sepcon_assoc in XX.
  intros u U. destruct (XX _ U) as [u1 [u2 [J [U1 U2]]]]; clear XX.
  exists u1, u2; split; trivial. split; trivial. clear - U2 HARGS. subst args' args. rewrite <- HARGS. trivial.
}
clear Hpre.
specialize (Hpost ts1 x1).
apply own.bupd_intro; repeat intro; subst.
assert (CSUBpsi:cenv_sub (@cenv_cs CS) psi).
{ destruct HGG as [CSUB' HGG]. apply (cenv_sub_trans CSUB' HGG). }
destruct HGG as [CSUB HGG].
subst rho.
rewrite (typecheck_expr_sound_cenv_sub CSUB Delta' _ TCD' w' a) in EvalA by (apply (TC1 w' (age_laterR  Hage))).

simpl fst in *. simpl snd in *. 
eapply (@semax_call_aux' CS') with (F := fun rho' => F rho' * G)
       (F0:=F0)(rho:=(construct_rho (filter_genv psi) vx tx))
       (ts:=ts1)(x:=x1)(b:=b)(*(Q:=nQ)*)(Delta:=Delta'); try eassumption.
(*1:{ simpl fst; simpl snd. rewrite TCF; clear - NSC. f_equal.
     specialize (funsigs_match_type_of_params NSC). simpl fst.
     symmetry; trivial. } 
1: simpl snd; assumption.*)
(*1: clear - NSC TCF. (*; apply typesigs_match_typesigs_eq in NSC*) inv NSC; trivial.*)
1: { clear - TC1 CSUB; intros w W. apply (tc_expr_cenv_sub CSUB _ _ _ _ (TC1 _ W)) . }
1: { clear - Espec TC2 CSUB NSC.
     (*apply typesigs_match_typesigs_eq in NSC;*) inv NSC. (*
     rewrite (funsigs_match_argtypes NSC). *)
     intros w W.
     apply (tc_exprlist_cenv_sub CSUB). apply TC2. trivial. }
(*1: { clear - NSC HARGS. apply typesigs_match_typesigs_eq in NSC; inv NSC.
     rewrite HARGS. trivial. }*)
1:{ (*ALL rho-condition*)
  (*apply typesigs_match_typesigs_eq in NSC; inv NSC.*)
  simpl RA_normal; auto. (*clear - TRIV TC7' PostAdapt NSC.*)
  intros rho' u U m NEC [v V]. (*rewrite sepcon_andp_prop1 in V.
  destruct V as [TCv V].  simpl in TCv.*)
  exists v.
  destruct V as [m1 [m2 [JM [M1(*[u1 [u2 [JU [U1 U2]]]]*) M2]]]].
  destruct ret.
  + destruct M1 as [u1 [u2 [JU [U1 U2]]]]. 
    destruct (join_assoc JU JM) as [q1 [Q2 Q1]]; clear JU JM. 
    exists u1, q1; split3; trivial.
    simpl. simpl in M2. destruct M2. split; trivial.
    apply PostAdapt; simpl.
    split.
    - trivial. (*simpl; red. unfold get_result1; simpl; unfold env_set; simpl. constructor; simpl. red; intros. rewrite PTree.gempty in H3; discriminate.
      split; apply TRIV.*)
    - exists u2, m2; split3; trivial.
  + simpl substopt in *. 
    destruct M1 as [u1 [u2 [JU [U1 U2]]]]. 
    destruct (join_assoc JU JM) as [q1 [Q2 Q1]]; clear JU JM. 
    exists u1, q1; split3; trivial. simpl. clear - TRIV TC5 TC7' PostAdapt M2 Q2 U2.
    destruct retty.
    - apply PostAdapt; split; [ | exists u2, m2; split3; trivial]. 
      reflexivity. (* unfold rettype_tycontext.  split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (* split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*)
    - clear - PostAdapt Q2 M2 U2. destruct M2 as [v [TCv M2]].
      exists v; split; trivial.
      apply PostAdapt; split. 2: exists u2, m2; split3; trivial.
      reflexivity. (*split3; simpl; intros ?; intros.
      rewrite PTree.gempty in H; congruence.
      split; intros ?. rewrite PTree.gempty in H; congruence. destruct H. inv H.
      rewrite PTree.gempty in H; congruence.*) }
Qed.

Lemma semax_call_si {CS Espec}:
  forall Delta (A: TypeTree)
  (P : forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: args_super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|>(tc_expr Delta a rho && tc_exprlist Delta argsig bl rho))  &&
           (func_ptr_si (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret (`old) F rho * maybe_retval (Q ts x) retsig ret rho))).
Proof.
rewrite semax_unfold. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TCF TC5 TC7.
rename argsig into clientparams. rename retsig into retty.
intros.
rename H into Closed; rename H0 into RGUARD.
intros tx vx.
intros ? ? ? NecR_ya' [[TC3 ?] funassertDelta'].

assert (NecR_wa': necR w (level a')).
{ apply nec_nat. apply necR_level in NecR_ya'. apply le_trans with (level y); auto. }
eapply pred_nec_hereditary in RGUARD; [ | apply NecR_wa'].
eapply pred_nec_hereditary in Prog_OK; [ | apply NecR_wa'].
clear w NecR_wa' NecR_ya' y H.
rename a' into w.

assert (TC7': tc_fn_return Delta' ret retty).
{
  clear - TC7 TS.
  hnf in TC7|-*. destruct ret; auto.
  destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
  destruct TS.
  specialize (H i); rewrite Heqo in H. subst t.
  destruct ((temp_types Delta') ! i ).
  destruct H; auto.
  auto.
} clear TC7.
rewrite !later_andp in H0.
apply extend_sepcon_andp in H0; auto.
destruct H0 as [[TC1 TC2] pre].

normalize in pre. (*unfold func_ptr_si in *.*)
destruct pre as [preA preB]. destruct preA as [b [EvalA funcatb]].
destruct preB as [z1 [z2 [JZ [HF0 pre]]]].
destruct (level w) eqn: Hl.
{ apply own.bupd_intro; repeat intro.
  rewrite Hl; constructor. }
rewrite <- Hl in *.
destruct (levelS_age w n) as (w' & Hage & Hw'); auto.

hnf in funcatb. 

destruct funcatb as [nspec [GS funcatb]].
simpl in GS; rename GS into SubClient.

assert (Hpsi: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
unfold filter_genv in Hpsi.
remember (construct_rho (filter_genv psi) vx tx) as rho.

set (args := @eval_exprlist CS clientparams bl rho).
set (args' := @eval_exprlist CS' clientparams bl rho).

assert (MYPROP: exists id fs, 
         Map.get (ge_of rho) id = Some b /\
         (glob_specs Delta') ! id = Some fs /\ func_at fs (b, 0) w).
{ clear - funcatb funassertDelta' SubClient JZ.
  assert (XX: exists id:ident, (Map.get (ge_of rho) id = Some b)
                               /\ exists fs, (glob_specs Delta')!id = Some fs).
  
  { destruct funassertDelta' as [_ FD]. 
    apply (FD b (clientparams, retty) cc _ (necR_refl _)); clear FD.
    simpl. destruct nspec. destruct SubClient as [[FSM Hcc] _]. subst t c.
    (*specialize (typesigs_match_typesigs_eq FSM); intros TS; subst.*)
    eexists; trivial. apply funcatb. }
  destruct XX as [id [Hb [fs specID]]]; simpl in Hb.

  assert (exists v, Map.get (ge_of rho) id = Some v /\ func_at fs (v, 0) w).
  { destruct funassertDelta' as [funassertDeltaA _].
    destruct (funassertDeltaA id fs _ (necR_refl _) specID) as [v [ Hv funcatv]]; simpl in Hv.
    exists v; split; trivial. }
  destruct H as [v [Hv funcatv]].
  assert (VB: b=v); [inversion2 Hb Hv; trivial | subst; clear Hb].
  exists id, fs; auto. }
destruct MYPROP as [id [fs [RhoID [SpecOfID funcatv]]]].
destruct fs as [fsig' cc' A' deltaP deltaQ NEP' NEQ'].

unfold func_at in funcatv, funcatb. destruct nspec as [nsig ncc nA nP nQ nP_ne nQ_ne].

destruct SubClient as [[NSC Hcc] ClientAdaptation]; subst cc. destruct nsig as [nparams nRetty].
inversion NSC. subst nparams nRetty.
(*specialize (typesigs_match_rettypes NSC); simpl snd; intros; subst nRetty.*)
destruct fsig' as [fArgsig fRettp].
hnf in funcatb, funcatv.
 inversion2 funcatb funcatv.
assert (PREPOST: (forall ts (x:dependent_type_functor_rec ts nA mpred) vl, (! |> (deltaP ts x vl <=> nP ts x vl)) w) /\
                 (forall ts (x:dependent_type_functor_rec ts nA mpred) vl, (! |> (deltaQ ts x vl <=> nQ ts x vl)) w)).
{ symmetry in H4. apply inj_pair2 in H4; 
  apply (function_pointer_aux); trivial. f_equal; apply H4. }
clear H4; destruct PREPOST as [Hpre Hpost].
simpl fst in *; simpl snd in *.
(*
assert (LenTypes: length (map snd fArgsig) = length (map snd nparams)) by (rewrite H0; trivial).
assert (LenArgs: length fArgsig = length nparams) by (rewrite 2 map_length in LenTypes; trivial).

assert (ParamsEQ: map fst fArgsig = map fst nparams) by (apply check_normalized_unique_idents; trivial).
assert (fArgsig = nparams) by (apply map_fst_snd_eq; trivial).

subst fArgsig. clear ParamsEQ LenTypes LenArgs H0 fNorm. simpl funsig_tycontext in ClientAdaptation.
unfold funspec_normalized in nNorm; simpl in nNorm.
*)
fold args in pre. clear Hpsi.
set (rho:= construct_rho (filter_genv psi) vx tx).

assert (typecheck_environ Delta rho) as TC4.
{ clear - TC3 TS.
  destruct TC3 as [TC3 TC4].
  eapply typecheck_environ_sub in TC3; [| eauto].
  auto.
} 

assert (HARGS: args = args').
{ clear - Hage HGG TC4 TC2.
  assert (ARGSEQ: (|> (!! (args = args'))) w).
  { hnf; intros. specialize (TC2 _ H). subst args args'.
    simpl. destruct HGG as [CSUB HGG].
    apply (typecheck_exprlist_sound_cenv_sub CSUB Delta rho TC4 a'). apply TC2. }
  eapply (ARGSEQ w'). apply age_laterR; trivial. }

eapply later_derives in TC2; [|apply (tc_exprlist_sub _ _ _ TS); auto].
eapply later_derives in TC1; [|apply (tc_expr_sub _ _ _ TS); auto].

assert (LENargs: Datatypes.length clientparams = Datatypes.length args).
{ clear - TC2 Hage. subst args.
  apply age_laterR in Hage. simpl in TC2.
  specialize (TC2 _ Hage). apply tc_exprlist_length in TC2. 
  clear - TC2.
  forget clientparams as m.
  generalize dependent m. clear. induction bl; simpl; intros.
  destruct m; simpl. trivial. inv TC2. destruct m; inv TC2. simpl.
  rewrite (IHbl _ H0); trivial. }

(*simpl in ClientAdaptation.*)

assert (HPP: (|> (F0 rho * F rho * (P ts x) (ge_of rho, args)))%pred w).
{ clear - pre JZ HF0 HGG TC1 TC2.
  rewrite sepcon_assoc. rewrite later_sepcon. exists z1, z2; split; trivial.
  split; [ apply now_later |]; trivial. }

simpl in EvalA. clear pre JZ HF0 z1 z2.
rewrite later_sepcon in HPP.
destruct HPP as [w1 [w2 [J [W1 W2]]]]; destruct (join_level _ _ _ J) as [LevW1 LevW2].
destruct (age1_join2 _ J Hage) as [w1' [w2' [J' [Age1 Age2]]]].

assert (TRIV: (forall rho, typecheck_temp_environ rho (PTree.empty type)) /\
              (typecheck_var_environ (Map.empty (block * type)) (PTree.empty type)) /\ 
              (forall rho, typecheck_glob_environ rho (PTree.empty type))).
{ clear. split.
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } split. 
  { intros; hnf; intros. split; intros. rewrite PTree.gempty in H; congruence. 
    destruct H. unfold Map.empty, Map.get in H; congruence. } 
  { intros; hnf; intros. rewrite PTree.gempty in H; congruence. } }

assert (TCD': tc_environ Delta' rho) by eapply TC3.

assert (LA2: laterM w2 w2'). { constructor; trivial. }
(*assert (TCARGS: tc_environ (funsig_tycontext (clientparams, retty)) (make_args (map fst clientparams) args rho)).
{ assert (LaterW': laterR w w'). constructor; trivial.
  specialize (TC2 _ LaterW'). subst args.
  apply (tc_environ_make_args' clientparams retty bl rho Delta' TCD' _ TC2).  }
*)
specialize (ClientAdaptation _ (age_laterR Hage) ts x (ge_of rho, args)). (*simpl in ClientAdaptation.*)

assert (LW2': (level w' >= level w2')%nat). { apply age_level in Age2. destruct (join_level _ _ _ J); lia. }

destruct (ClientAdaptation w2' LW2' _ (necR_refl _)) as [ts1 [x1 [G [PreAdapt PostAdapt]]]]; clear ClientAdaptation.
{ (*clear - LENargs Age2 W2.*)simpl; split. 
  (*+ red. simpl. apply TRIV.*)
  + clear - TC3 LENargs TC2 W2 Hage. destruct TC3. 
    apply age_laterR in Hage. specialize (TC2 w' Hage).
    specialize (tc_eval_exprlist _ _ _ _ _ H TC2).
    subst args.
    forget (construct_rho (filter_genv psi) vx tx) as lia.
    forget  (@eval_exprlist CS clientparams bl lia) as args.
    clear.
    generalize dependent clientparams.
    clear. induction args; simpl; intros.
    - destruct clientparams; simpl in *. constructor. contradiction.
    - destruct clientparams; simpl in *. contradiction. destruct H.
      apply tc_val_has_type in H. apply IHargs in H0.
      constructor; eauto.
  + apply age_laterR in Age2. apply (W2 _ Age2). }
simpl te_of in PreAdapt; simpl in PostAdapt.

(*hnf in PreAdapt.*) simpl typesig_of_funspec in *.
clear W2 NEP P.

(*destruct PreAdapt as [TCpreadapt PreAdapt].*)

(*clear TCpreadapt.*) (*nrho is welltyped in w2'*)

specialize (Hpre ts1 x1).
assert (ARGS: app_pred (|> (F0 rho *
     (F rho * G) * deltaP ts1 x1 (ge_of rho, args))) w).
{ clear Hpost PostAdapt SpecOfID Prog_OK RhoID TC7' RGUARD funcatb. rewrite HARGS in *.
  assert (XX: (|> (F0 rho * F rho * G * 
                 (deltaP ts1 x1) (ge_of rho, args'))) w).
  { rewrite sepcon_assoc. rewrite sepcon_assoc. rewrite <- sepcon_assoc.
    rewrite later_sepcon.
    exists w1, w2; split. trivial. split. trivial. hnf; intros.
    destruct (age_later Age2 H); [ subst a' |].
    - (*w2'=a'*)
      destruct PreAdapt as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 LevU2].
      exists u1, u2; split; trivial. split; trivial. clear TRIV.
      assert (LatWU2: laterM (level w) (level u2)). { rewrite LevU2, <- LevW2 . apply laterR_level'; trivial. }
      eapply (Hpre _ (level u2) LatWU2); [| apply necR_refl | trivial]. lia.
      (*specialize (funsigs_match_arglengths NSC); simpl fst; intros LEN.
      rewrite make_args_eq; [ simpl; subst rho; simpl in U2 | unfold ident in *; rewrite LEN; trivial].
      apply U2.*)
    - apply now_later in PreAdapt. specialize (PreAdapt _ H0).
      destruct PreAdapt as [u1 [u2 [JU [U1 U2]]]]; destruct (join_level _ _ _ JU) as [LevU1 LevU2]. 
      exists u1, u2; split; trivial. split; trivial.
      assert (LatWU2: laterM (level w) (level u2)). { rewrite LevU2, <- LevW2 . apply laterR_level'; trivial. }
      eapply (Hpre _ (level u2) LatWU2); [| apply necR_refl | trivial]. lia.
      (*clear - U2 NSC LENargs.
      specialize (funsigs_match_arglengths NSC); simpl fst; intros LEN.
      rewrite make_args_eq; trivial. rewrite LEN; apply LENargs.*) }
  subst args' rho. clear - XX. rewrite 2 sepcon_assoc. rewrite 2 sepcon_assoc in XX.
  intros u U. destruct (XX _ U) as [u1 [u2 [J [U1 U2]]]]; clear XX.
  exists u1, u2; split; trivial. split; trivial.
}
clear Hpre.
apply now_later in  RGUARD.

specialize (Hpost ts1 x1).
apply own.bupd_intro; repeat intro; subst.
assert (CSUBpsi:cenv_sub (@cenv_cs CS) psi).
{ destruct HGG as [CSUB' HGG]. apply (cenv_sub_trans CSUB' HGG). }
destruct HGG as [CSUB HGG].
subst rho.
rewrite (typecheck_expr_sound_cenv_sub CSUB Delta' _ TCD' w' a) in EvalA by (apply (TC1 w' (age_laterR  Hage))).

simpl fst in *. simpl snd in *. 
eapply (@semax_call_aux CS') with (F := fun rho' => F rho' * G)
       (F0:=F0)(rho:=(construct_rho (filter_genv psi) vx tx))
       (ts:=ts1)(x:=x1)(b:=b)(*(Q:=nQ)*)(Delta:=Delta'); try eassumption.
1: { clear - TC1 CSUB; intros w W. apply (tc_expr_cenv_sub CSUB _ _ _ _ (TC1 _ W)) . }
1: { clear - Espec TC2 CSUB NSC.
     intros w W.
     apply (tc_exprlist_cenv_sub CSUB). apply TC2. trivial. }
1:{ 
simpl RA_normal; auto.  clear ARGS Hpost RGUARD.
intros rho' l L y Y z YZ [v Z]. exists v.
assert (LEV2': (level w2' >= level w2')%nat) by lia. 
assert (LEVz: (level w2' >= level z)%nat). 
{ destruct (join_level _ _ _ J') as [_ Lw2']; rewrite Lw2'; clear Lw2'.
  apply necR_level in YZ.
  destruct (age_later Hage L).
  + subst l; lia. + apply laterR_level in H1; lia. }

clear - PostAdapt LEVz Z.
  destruct Z as [m1 [m2 [JM [M1 M2]]]].
  destruct ret.
  + destruct M1 as [u1 [u2 [JU [U1 U2]]]]. 
    destruct (join_assoc JU JM) as [q1 [Q2 Q1]]; clear JU JM. 
    exists u1, q1; split3; trivial.
    simpl. simpl in M2. destruct M2. split; trivial.
    destruct (join_level _ _ _ Q1).
    eapply PostAdapt. 2: apply necR_refl. lia. split.
    - reflexivity. 
    - exists u2, m2; split3; trivial.
  + simpl substopt in *. 
    destruct M1 as [u1 [u2 [JU [U1 U2]]]]. 
    destruct (join_assoc JU JM) as [q1 [Q2 Q1]]; clear JU JM. 
    exists u1, q1; split3; trivial.
    destruct (join_level _ _ _ Q1) as [_ LEVq1]. clear - M2 LEVq1 LEVz PostAdapt M2 Q2 U2.
    destruct retty;
     try (clear - PostAdapt Q2 LEVq1 LEVz M2 U2; destruct M2 as [v [TCv M2]];
      exists v; split; trivial;
      eapply (PostAdapt _ q1); [lia | apply necR_refl | split; [| exists u2, m2; split3; trivial]];
      reflexivity).
      apply (PostAdapt _ q1); [lia | apply necR_refl | split; [ | exists u2, m2; split3; trivial]].
      reflexivity. }
Qed.

Lemma semax_call_alt {CS Espec}:
 forall Delta (A: TypeTree)
   (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
   (Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
   (NEP: args_super_non_expansive P) (NEQ: super_non_expansive Q)
     ts x F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => (|> (tc_expr Delta a rho && tc_exprlist Delta argsig bl rho))  &&
           (func_ptr_si (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (ge_of rho, eval_exprlist argsig bl rho)))))
         (Scall ret a bl)
         (normal_ret_assert
          (fun rho => (EX old:val, substopt ret (`old) F rho * maybe_retval (Q ts x) retsig ret rho))).

Proof. exact semax_call_si. Qed.

Lemma semax_call_ext {CS Espec}:
   forall (IF_ONLY: False),
     forall Delta P Q ret a tl bl a' bl',
      typeof a = typeof a' ->
      map typeof bl = map typeof bl' ->
      (forall rho,
          !! (typecheck_environ Delta rho) && P rho |--
            tc_expr Delta a rho && tc_exprlist Delta tl bl rho &&
            tc_expr Delta a' rho && tc_exprlist Delta tl bl' rho &&
            !! (eval_expr a rho = eval_expr a' rho /\
                eval_exprlist tl bl rho = eval_exprlist tl bl' rho)) ->
  semax Espec Delta P (Scall ret a bl) Q ->
  @semax CS Espec Delta P (Scall ret a' bl') Q.
Proof.
intros until 2. intro Hbl. intros.
rewrite semax_unfold in H1|-*.
rename H1 into H2. pose proof I.
intros.
assert (HGpsi: cenv_sub (@cenv_cs CS)  psi).
{ destruct HGG as [CSUB HGG]. apply (cenv_sub_trans CSUB HGG). }
specialize (H2 psi Delta' CS' w TS HGG Prog_OK k F f H3 H4).
intros tx vx; specialize (H2 tx vx).
intros ? ? ? ? ?.
specialize (H2 y H5 a'0 H6 H7).
destruct H7 as[[? ?] _].
hnf in H7.
pose proof I.
intros ? J; destruct (H2 _ J) as (? & J' & m' & Hl & Hr & ? & Hsafe); subst.
eexists; split; eauto; exists m'; repeat split; auto.
hnf in Hsafe|-*; intros ?? Hora ??.
specialize (Hsafe ora jm Hora H10).
intros.
spec Hsafe; auto.
spec Hsafe; auto.
simpl in Hsafe.
eapply convergent_controls_jsafe; try apply Hsafe.
reflexivity.
simpl; intros ? ?. unfold cl_after_external. destruct ret0; auto.
reflexivity.
intros.
destruct H8 as [w1 [w2 [H8' [_ ?]]]]. subst m'.
assert (H8'': extendM w2 a'0) by (eexists; eauto). clear H8'.
remember (construct_rho (filter_genv psi) vx tx) as rho.
assert (H7': typecheck_environ Delta rho).
destruct H7; eapply typecheck_environ_sub; eauto.
destruct H7 as [H7 _].
specialize (H0 rho w2 (conj H7' H8)).
destruct H0 as [[[[TCa TCbl] TCa'] TCbl'] [? ?]].
apply (boxy_e _ _ (extend_tc_expr _ _ _) _ _ H8'') in TCa.
apply (boxy_e _ _ (extend_tc_exprlist _ _ _ _) _ _ H8'') in TCbl.
apply (boxy_e _ _ (extend_tc_expr _ _ _) _ _ H8'') in TCa'.
apply (boxy_e _ _ (extend_tc_exprlist _ _ _ _) _ _ H8'') in TCbl'.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCa; auto.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCa'; auto.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCbl; auto.
eapply denote_tc_resource with (a'1 := m_phi jm) in TCbl'; auto.
assert (forall vf, Clight.eval_expr psi vx tx (m_dry jm) a vf
               -> Clight.eval_expr psi vx tx (m_dry jm) a' vf). {
clear - TCa TCa' H7 H7' H0 Heqrho HGG TS HGpsi.
intros.
eapply tc_expr_sub in TCa; [| eauto | eauto].
pose proof (eval_expr_relate _ _ _ _ _ _ jm HGpsi Heqrho H7 TCa).
pose proof (eval_expr_fun H H1). subst vf.
rewrite H0.
eapply eval_expr_relate; eauto.
}
assert (forall tyargs vargs,
             Clight.eval_exprlist psi vx tx (m_dry jm) bl tyargs vargs ->
             Clight.eval_exprlist psi vx tx (m_dry jm) bl' tyargs vargs). {
clear - IF_ONLY TCbl TCbl' H11 Hbl H7' Heqrho HGpsi.
revert bl bl' H11 Hbl TCbl TCbl'; induction tl; destruct bl, bl'; simpl; intros; auto;
 try (clear IF_ONLY; contradiction).
 unfold tc_exprlist in TCbl,TCbl'. simpl in TCbl, TCbl'.
repeat rewrite denote_tc_assert_andp in TCbl, TCbl'.
destruct TCbl as [[TCe ?] ?].
destruct TCbl' as [[TCe0 ?] ?].
inversion H; clear H. subst bl0 tyargs vargs.
inversion Hbl; clear Hbl. rewrite <- H5 in *.
pose proof (eval_expr_relate _ _ _ _ _ _ _ HGpsi Heqrho H7' TCe).
pose proof (eval_expr_fun H H6).
repeat rewrite <- cop2_sem_cast in *.
unfold force_val in H1.
rewrite H9 in *.
subst.
clear H.
unfold_lift in H11.
inv H11.
specialize (IHtl _ _ H9 H8); clear H9 H8.
assert (exists v1, Clight.eval_expr psi vx tx (m_dry jm) e0 v1 /\
                             Cop.sem_cast v1 (typeof e0) ty (m_dry jm) = Some v2). {
 clear - IF_ONLY H4 H6 H7 TCe H0 TCe0 H2 HGpsi H7'.
   contradiction IF_ONLY.  (* still some work to do here *)
}
destruct H as [v1 [? ?]]; 
econstructor; try eassumption.
eapply IHtl; eauto.
}
destruct H12; split; auto.
inv H12.
eapply step_call; eauto.
rewrite <- H; auto.
destruct H24 as [H24 | H24]; inv H24.
destruct H24 as [H24 | H24]; inv H24.
Qed.

Definition cast_expropt {CS} (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (@eval_expr CS (Ecast e' t))  | None => `None end.

Definition tc_expropt {CS} Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `!!(t=Tvoid)
                     | Some e' => @denote_tc_assert CS (typecheck_expr Delta (Ecast e' t))
   end.

Lemma tc_expropt_char {CS} Delta e t: @tc_expropt CS Delta e t =
                                      match e with None => `!!(t=Tvoid)
                                              | Some e' => @tc_expr CS Delta (Ecast e' t)
                                      end.
Proof. reflexivity. Qed.

Lemma RA_return_castexpropt_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- !!(@cast_expropt CS ret t rho = @cast_expropt CS' ret t rho).
Proof.
  intros w W. simpl. unfold tc_expropt in W. destruct ret. 
  + simpl in W. simpl.
    unfold force_val1, liftx, lift; simpl. rewrite denote_tc_assert_andp in W. destruct W.
    rewrite <- (typecheck_expr_sound_cenv_sub CSUB Delta rho D w); trivial.
  + simpl in W; subst. simpl; trivial.
Qed.

Lemma tc_expropt_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS' Delta ret t rho.
Proof.
  intros w W. simpl. rewrite  tc_expropt_char in W; rewrite tc_expropt_char.
  specialize (tc_expr_cenv_sub CSUB); intros.
  destruct ret; trivial; auto.
Qed.

Lemma tc_expropt_cspecs_sub {CS CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS' Delta ret t rho.
Proof.
  destruct CSUB as [CSUB _].
  apply (@tc_expropt_cenv_sub _ _ CSUB _ _ D).     
Qed.

Lemma tc_expropt_sub {CS} Delta Delta' rho (TS:tycontext_sub Delta Delta') (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS Delta' ret t rho.
Proof.
  intros w W. rewrite  tc_expropt_char in W; rewrite tc_expropt_char.
  specialize (tc_expr_sub _ _ _ TS); intros.
  destruct ret; [ eapply H; assumption | trivial]. 
Qed.

Lemma  semax_return {CS Espec}:
   forall Delta R ret,
      @semax CS Espec Delta
                (fun rho => tc_expropt Delta ret (ret_type Delta) rho &&
                             RA_return R (cast_expropt ret (ret_type Delta) rho) rho)
                (Sreturn ret)
                R.
Proof.
  intros.
  hnf; intros.
  rewrite semax_fold_unfold.
  intros psi Delta' CS'.
  apply prop_imp_i. intros [TS [CSUB HGG]].
  replace (ret_type Delta) with (ret_type Delta')
    by (destruct TS as [_ [_ [? _]]]; auto).
  apply derives_imp.
  clear n.
  intros w ? k F f.
  intros w' ? ?. 
  clear H.
  clear w H0.
  rename w' into w.
  destruct H1.
  do 3 red in H.
  intros te ve.
  intros n ? w' ? ?.
  assert (necR w (level w')).
  {
    apply nec_nat.
    apply necR_level in H2.
    apply le_trans with (level n); auto.
  }
  apply (pred_nec_hereditary _ _ _ H4) in H0.
  clear w n H2 H1 H4.
  destruct H3 as [[H3 ?] ?].
  pose proof I.
  remember ((construct_rho (filter_genv psi) ve te)) as rho.
  assert (H1': ((F rho * proj_ret_assert R EK_return (cast_expropt ret (ret_type Delta') rho) rho))%pred w').
  { 
    eapply sepcon_derives; try apply H1; auto. 
    intros w [W1 W2]. simpl in H3; destruct H3 as [TCD' _].
    assert (TCD: typecheck_environ Delta rho) by (eapply typecheck_environ_sub; eauto). 
    apply (tc_expropt_sub _ _ _ TS) in W1; trivial.
    rewrite <- (RA_return_castexpropt_cenv_sub CSUB Delta' rho TCD' _ _ _ W1); trivial.
  }
  assert (TC: (tc_expropt Delta ret (ret_type Delta') rho) w').
  {
    simpl in H3; destruct H3 as [TCD' _].
    clear - H1 TCD' TS CSUB Espec. 
    assert (TCD: typecheck_environ Delta rho) by (eapply typecheck_environ_sub; eauto); clear TS.
    destruct H1 as [w1 [w2 [? [? [? ?]]]]].
    apply (tc_expropt_cenv_sub CSUB) in H1; trivial.
    rewrite tc_expropt_char; rewrite tc_expropt_char in H1. destruct ret; [ |trivial].
    apply (boxy_e _ _ (extend_tc_expr _ _ _) w2); auto.
    exists w1; auto.
  }
  clear H1; rename H1' into H1.
  specialize (H0 EK_return (cast_expropt ret (ret_type Delta') rho) te ve).
  specialize (H0 _ (le_refl _) _ (necR_refl _)).
  spec H0.
  {
    rewrite <- Heqrho.
    rewrite proj_frame_ret_assert.
    split; auto.
    split; auto.
    rewrite seplog.sepcon_comm; auto.
  }
  unfold tc_expropt in TC; destruct ret; simpl in TC.
  + eapply own.bupd_mono, bupd_denote_tc, H0; eauto.
    clear TC; intros ? [TC Hsafe] ?? Hora ??.
    specialize (Hsafe ora jm Hora (eq_refl _) H6).
    intros. subst a.
    specialize (Hsafe LW e (eval_expr e rho)).
    destruct H3 as [H3a [H3b H3c]].
    rewrite H3c in Hsafe,TC.
    rewrite denote_tc_assert_andp in TC; destruct TC as [?TC ?TC].
    spec Hsafe.
    eapply eval_expr_relate; eauto.
    eapply tc_expr_sub; try eassumption.
    eapply typecheck_environ_sub; try eassumption.
    spec Hsafe. {
    rewrite cop2_sem_cast'; auto.
    2:{ eapply typecheck_expr_sound; eauto.
    eapply tc_expr_sub; try eassumption.
    eapply typecheck_environ_sub; try eassumption.
    }
    eapply cast_exists; eauto.
    eapply tc_expr_sub; try eassumption.
    eapply typecheck_environ_sub; try eassumption.
   }
    clear - Hsafe.
    eapply convergent_controls_jsafe; try apply Hsafe; auto.
    intros ? ? [? ?]; split; auto.
    inv H.
    1,3: destruct H9; discriminate.
    rewrite call_cont_idem.
    econstructor; eauto.
  + eapply own.bupd_mono, H0; eauto.
    intros ? Hsafe ?? Hora ???.
    specialize (Hsafe ora jm Hora (eq_refl _) H6 LW).
     simpl in Hsafe.
    eapply convergent_controls_jsafe; try apply Hsafe; auto.
    intros.
    destruct H7; split; auto.
    inv H7.
    1,3: destruct H17; discriminate.
    rewrite call_cont_idem.
    econstructor; eauto.
Qed.
