Require Import veric.base.
Require Import msl.normalize.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
 
Open Local Scope pred.
Section extensions.
Context (Espec: OracleKind).

(* Scall *)

Lemma opt2list_inj: forall A (a b: option A), opt2list a = opt2list b -> a=b.
Proof.
destruct a; destruct b; intros; inv H; auto.
Qed.

Lemma unlater_writable:
  forall m m', laterR m m' -> 
            forall loc, writable loc m' -> writable loc m.
Proof.
induction 1; intros; auto.
hnf in *.
simpl in H0.
assert (match y @ loc with
     | YES rsh sh k _ => sh = pfullshare /\ isVAL k
     | _ => False
     end) by (destruct (y @ loc); eauto).
clear H0.
revert H1; case_eq (y @ loc); intros; try contradiction.
destruct H1; subst.
destruct (rmap_unage_YES _ _ _ _ _ _ _ H H0).
rewrite H1; simpl; auto.
Qed.

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

Lemma prop_unext: forall P Q: Prop, P=Q -> (P<->Q).
Proof. intros. subst; split; auto. Qed.

Lemma function_pointer_aux:
  forall A P P' Q Q' (w: rmap), 
   SomeP (A::boolT::environ::nil) (approx (level w) oo packPQ P Q) =
   SomeP (A::boolT::environ::nil) (approx (level w) oo packPQ P' Q') ->
   ( (forall x vl, (! |> (P' x vl <=> P x vl)) w) /\
     (forall x vl, (! |> (Q' x vl <=> Q x vl)) w)).
Proof.
intros.
apply someP_inj in H.
unfold packPQ, compose in H.
split; intros.
apply equal_f with (x,(true,(vl,tt))) in H.
simpl in H.
rewrite @later_fash; auto with typeclass_instances.
intros ? ? m' ?.
split; intros m'' ? ?;  apply f_equal with (f:= fun x => app_pred x m'') in H;
apply prop_unext in H; apply approx_p with (level w); apply H;
apply approx_lt; auto; clear - H0 H1 H2; hnf in H1; apply laterR_level in H1;
apply necR_level in H2; simpl in *;
change compcert_rmaps.R.ag_rmap with ag_rmap in *;
change compcert_rmaps.R.rmap with rmap in *;
omega.
apply equal_f with (x,(false,(vl,tt))) in H.
simpl in H.
rewrite @later_fash; auto with typeclass_instances; intros ? ? m' ?;
split; intros m'' ? ?;  apply f_equal with (f:= fun x => app_pred x m'') in H;
apply prop_unext in H; apply approx_p with (level w); apply H;
apply approx_lt; auto; clear - H0 H1 H2; hnf in H1; apply laterR_level in H1;
apply necR_level in H2; simpl in *;
change compcert_rmaps.R.ag_rmap with ag_rmap in *;
change compcert_rmaps.R.rmap with rmap in *; omega.
Qed.


Lemma semax_fun_id:
      forall id fsig (A : Type) (P' Q' : A -> assert)
              Delta P Q c
      (GLBL: (var_types Delta) ! id = None),
    (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A P' Q')) ->
       semax Espec Delta (fun rho => P rho 
                                && fun_assert  fsig A P' Q' (eval_lvalue (Evar id (Tfunction (type_of_params (fst fsig)) (snd fsig))) rho))
                              c Q ->
       semax Espec Delta P c Q.
Proof.
intros.
rewrite semax_unfold in H0|-*.
rename H0 into H1; pose proof I.
intros.
specialize (H1 psi Delta' w TS Prog_OK k F H2 H3).
replace ((var_types Delta) ! id) with ((var_types Delta')!id) in GLBL 
  by (destruct TS as [_ [? _]]; symmetry; auto).
assert (H': (glob_types Delta') ! id = Some (Global_func (mk_funspec fsig A P' Q'))).
clear - H TS.
destruct TS as [_ [_ [_ SUB]]]; specialize (SUB id); hnf in SUB; rewrite H in SUB; auto.
clear H Delta TS. rename H' into H. rename Delta' into Delta.
intros te ve w' ? w'' ? ?.
apply (H1 te ve w' H4 w'' H5); clear H1.
destruct H6; split; auto.
destruct H1 as [H1 ?]; split; auto.
normalize.
split; auto.
assert (app_pred (believe Espec Delta psi Delta) (level w'')).
apply pred_nec_hereditary with (level w'); eauto.
apply nec_nat; apply necR_level; auto.
apply pred_nec_hereditary with w; eauto.
apply nec_nat; auto.
hnf in H1. destruct H1. 
destruct H1 as [_ [_ [H1 SAME]]]. 
rename GLBL into GL1.
specialize (H1 _ _ H).
specialize (SAME _ _ H).
destruct SAME as [SAME | [t SAME]]; [ | congruence].
clear - H6 H8 H SAME H1.
destruct H6 as [H6 H6'].
specialize (H6 _ _  _(necR_refl _) H).
destruct H6 as [v [loc [[? ?] ?]]].
simpl in H0, H1, H2.
specialize (H8 v fsig A P' Q' _ (necR_refl _)).
 
unfold filter_genv in H0. simpl in H0.
invSome.
assert (v = Vptr b Int.zero) by (destruct (type_of_global psi b); inv H6; auto).
subst v.
unfold val2adr in H2.
rewrite Int.signed_zero in H2.
subst loc.
spec H8. exists id. split; auto. exists b; auto.
simpl in SAME.
exists b. exists Int.zero.
split.
unfold eval_lvalue, eval_var.
simpl ve_of. unfold Map.get. rewrite SAME.
simpl. unfold filter_genv. rewrite H0.
destruct (type_of_global psi b); inv H6; auto.
rewrite eqb_type_refl.
replace (eqb_typelist (type_of_params (fst fsig)) (type_of_params (fst fsig))) with true.
simpl; auto.
clear; induction (type_of_params (fst fsig)); simpl; auto.
rewrite <- IHt; simpl; auto.
rewrite eqb_type_refl; auto.
hnf; auto.
intro loc.
hnf.
if_tac; auto.
subst.
hnf. auto.
hnf; auto.
Qed.

Definition func_ptr (f: funspec) : val -> mpred := 
 match f with mk_funspec fsig A P Q => fun_assert fsig A P Q end.

Lemma semax_fun_id_alt:
      forall id f    Delta (P: assert) Q c
      (GLBL: (var_types Delta) ! id = None),
    (glob_types Delta) ! id = Some (Global_func f) ->
       semax Espec Delta (fun rho => P rho && 
                    (func_ptr f (eval_var id (globtype (Global_func f)) rho)))
                  c Q ->
       semax Espec Delta P c Q.
Proof. 
intros id [fsig A P' Q']. apply semax_fun_id.
Qed.

Import JuicyMemOps.

Lemma can_alloc_variables:
  forall jm vl, exists ve', exists jm',
          Clight.alloc_variables empty_env (m_dry jm) vl ve' (m_dry jm')
        /\ level jm = level jm'
        /\ core (m_phi jm) = core (m_phi jm').
Proof.
 intros.
 remember (alloc_juicy_variables empty_env jm vl) as x.
 exists (fst x); exists (snd x).
 destruct x as [rho' jm'].
 symmetry in Heqx.
 apply alloc_juicy_variables_e in Heqx; auto.
Qed.


Lemma can_alloc_variables':
  forall jm vl, 
               (level jm > 0)%nat ->
      exists ve', exists jm',
          Clight.alloc_variables empty_env (m_dry jm) vl ve' (m_dry jm') /\
          (resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\ 
          level jm = S (level jm') /\
          age (core (m_phi jm)) (core (m_phi jm'))).
Proof.
 intros.
 remember (alloc_juicy_variables empty_env jm vl) as x.
 destruct x as [rho' jm'].
 symmetry in Heqx.
 destruct (alloc_juicy_variables_e _ _ _ _ _ Heqx).
 case_eq (age1 jm'); intros; [ | rewrite age1_level0 in H2;  omegaContradiction].
 clear H. rename H2 into H.
 exists rho'; exists j.
 split. apply age_jm_dry in H. rewrite <- H; auto.
 assert (resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
             (nextblock (m_dry jm) <= nextblock (m_dry jm'))%positive /\
             level jm = level jm' /\
            core (m_phi jm) = core (m_phi jm') ).
Focus 2.
  destruct H2 as [? [? [? CORE]]]; split3.
   eapply resource_decay_trans; try eassumption.  
  apply age1_resource_decay. apply H.
  rewrite H4. apply age_level. auto.
  rewrite CORE.
 clear - CORE H.
 apply age_core. apply age_jm_phi; auto.
 clear j H.
 apply -> and_assoc.
 split; auto.
 forget empty_env as rho. clear H0.
 revert rho jm Heqx H1; induction vl; intros.
 inv Heqx. split. apply resource_decay_refl.
   apply juicy_mem_alloc_cohere. apply Ple_refl.
 destruct a as [id ty].
 unfold alloc_juicy_variables in Heqx; fold alloc_juicy_variables in Heqx.
 revert Heqx; case_eq (juicy_mem_alloc jm 0 (sizeof ty)); intros jm1 b1 ? ?.
 pose proof (juicy_mem_alloc_succeeds _ _ _ _ _ H).
  pose proof (juicy_mem_alloc_level _ _ _ _ _ H).
  rewrite (juicy_mem_alloc_core _ _ _ _ _ H) in H1.
  rewrite H2 in H1.
 specialize (IHvl _ _ Heqx H1).
 symmetry in H0; pose proof (nextblock_alloc _ _ _ _ _ H0).
 destruct IHvl.
 split; [ |  rewrite H3 in H5; xomega].
 eapply resource_decay_trans; try eassumption. 
 rewrite H3; xomega.
 clear - H H2 H0.
 change (level (m_phi jm) = level (m_phi jm1)) in H2.
 unfold resource_decay.
 split. rewrite H2; auto.
 intro loc.
 split.
 apply juicy_mem_alloc_cohere.
 rewrite (juicy_mem_alloc_at _ _ _ _ _ H).
 replace (sizeof ty - 0) with (sizeof ty) by omega.
 destruct loc as [b z]. simpl in *.
 if_tac. destruct H1; subst b1.
 right. right. left. split. apply alloc_result in H0; subst b; xomega.
 eauto.
 rewrite <- H2. left. apply resource_at_approx.
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
intros id fs w2 Hw2 H3.
specialize (H0 id fs). cbv beta in H0.
specialize (H0 _ (necR_refl _) H3).
destruct H0 as [v [loc [[? ?] ?]]].
 specialize (H1 loc).
 destruct H1 as [? ?].
exists v; exists loc; split; auto.
split; auto.
destruct fs as [f A a a0].
simpl in H4|-*.
pose proof (necR_resource_at (core w) (core w') loc
         (PURE (FUN f) (SomeP (A :: boolT :: environ :: nil) (packPQ a a0))) CORE).
pose proof (necR_resource_at _ _ loc
         (PURE (FUN f) (SomeP (A :: boolT :: environ :: nil) (packPQ a a0))) Hw2).
apply H7.
clear - H6 H4.
repeat rewrite <- core_resource_at in *.
spec H6. rewrite H4.  rewrite core_PURE.  simpl.  rewrite level_core; reflexivity.
destruct (w' @ loc).
 rewrite core_NO in H6; inv H6.
 rewrite core_YES in H6; inv H6.
 rewrite core_PURE in H6; inv H6. rewrite level_core; reflexivity.

intros loc fs w2 Hw2 H6.
specialize (H2 loc fs _ (necR_refl _)).
spec H2.
clear - Hw2 CORE H6.
destruct fs; simpl in *.
destruct H6 as [pp H6].
 rewrite <- resource_at_approx.
case_eq (w @ loc); intros.
assert (core w @ loc = compcert_rmaps.R.resource_fmap (compcert_rmaps.R.approx (level (core w))) (NO Share.bot)).
 rewrite <- core_resource_at.
simpl; erewrite <- core_NO; f_equal; eassumption.
pose proof (necR_resource_at _ _ _ _ CORE H0).
pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
rewrite <- core_resource_at in H2; rewrite H6 in H2; 
 rewrite core_PURE in H2; inv H2.
assert (core w @ loc = compcert_rmaps.R.resource_fmap (compcert_rmaps.R.approx (level (core w))) (NO Share.bot)).
 rewrite <- core_resource_at.
simpl; erewrite <- core_YES; f_equal; eassumption.
pose proof (necR_resource_at _ _ _ _ CORE H0).
pose proof (necR_resource_at _ _ _ _ (necR_core _ _ Hw2) H1).
rewrite <- core_resource_at in H2; rewrite H6 in H2; 
 rewrite core_PURE in H2; inv H2.
pose proof (resource_at_approx w loc).
pattern (w @ loc) at 1 in H0; rewrite H in H0.
symmetry in H0.
assert (core (w @ loc) = core (compcert_rmaps.R.resource_fmap (compcert_rmaps.R.approx (level w))
       (PURE k p))) by (f_equal; auto).
rewrite core_resource_at in H1.
assert (core w @ loc = 
        compcert_rmaps.R.resource_fmap (compcert_rmaps.R.approx (level (core w))) 
         (PURE k p)). 
 rewrite H1.  simpl. rewrite level_core; rewrite core_PURE; auto.
pose proof (necR_resource_at _ _ _ _ CORE H2).
 assert (w' @ loc = compcert_rmaps.R.resource_fmap
       (compcert_rmaps.R.approx (level w')) (PURE k p)).
 rewrite <- core_resource_at in H3. rewrite level_core in H3.
 destruct (w' @ loc).
  rewrite core_NO in H3; inv H3.
  rewrite core_YES in H3; inv H3.
  rewrite core_PURE in H3; inv H3.
 reflexivity.
 pose proof (necR_resource_at _ _ _ _ Hw2 H4).
 inversion2 H6 H5.
 exists p. reflexivity.
destruct H2 as [id [v [[? ?] ?]]].
exists id, v. split; auto. split; auto.
Qed.

Definition substopt {A} (ret: option ident) (v: val) (P: environ -> A)  : environ -> A :=
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



Lemma exprlist_eval :
  forall (Delta : tycontext) (fsig : funsig) 
     (bl : list expr) (psi : genv) (vx : env) (tx : temp_env) 
     (rho : environ) m,
   denote_tc_assert (typecheck_exprlist Delta (snd (split (fst fsig))) bl) rho ->
   typecheck_environ Delta rho ->
   rho = construct_rho (filter_genv psi) vx tx ->
   forall f : function,
   fsig = fn_funsig f ->
   Clight.eval_exprlist psi vx tx m bl
     (type_of_params (fn_params f))
     (eval_exprlist (snd (split (fst fsig))) bl rho). 
Proof.
 intros until m. intro. assert True; auto. intros.  
destruct fsig. unfold fn_funsig in *. inversion H3; clear H3; subst l t. simpl in *.
 forget (fn_params f) as vl.
 forget (fn_temps f) as tl.
 clear f.
 clear - H1 H2 H.

 rewrite snd_split. rewrite snd_split in H.
 assert (length (map snd vl) = length bl). 
 apply tc_exprlist_length in H; auto. 
 revert vl H H0; induction bl; destruct vl; intros; inv H0; simpl.
 constructor.
 destruct p. simpl in *; subst.
 repeat (rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 destruct H as [[? ?] ?].
 pose proof (typecheck_expr_sound _ _ _ H1 H).
 specialize (IHbl _ H2 H4).
 clear - IHbl H1 H H0 H3.
 constructor 2 with  (eval_expr  a (construct_rho (filter_genv psi) vx tx)); auto.
 apply eval_expr_relate with Delta; auto.
 pose proof  (cast_exists Delta a _ _ H1 H H0).

rewrite cop2_sem_cast.
 apply (cast_exists Delta a _ _ H1 H H0).
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
destruct (peq id i). subst; intuition. auto.
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
destruct (peq i id). subst. intuition. auto.
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
forall id m1 l ve m2 e ,
list_norepet (map fst l) ->
(forall i, In i (map fst l) -> e ! i = None) ->
Clight.alloc_variables (e) m1 l ve m2 ->
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
auto. intros. rewrite PTree.gsspec. if_tac. subst. intuition.
apply H0. auto. 
rewrite PTree.gso; auto. eauto. 
Qed. 

Lemma alloc_vars_lemma : forall id l m1 m2 ve ve'
(SD : forall i, In i (map fst l) -> ve ! i = None),
list_norepet (map fst l) ->

Clight.alloc_variables ve m1 l ve' m2 ->
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
destruct (eq_dec i id). subst. intuition. rewrite PTree.gso; auto. 
rewrite PTree.gss; eauto. 

inv H0. apply IHl in H10; auto. inv H; auto. 
intros. rewrite PTree.gsspec. if_tac. subst. inv H. intuition.
auto. 
Qed. 

Lemma semax_call_typecheck_environ:
  forall (Delta : tycontext) (bl : list expr) (psi : genv) (vx : env) (tx : temp_env) 
           (jm : juicy_mem) (b : block) (f : function) 
     (H17 : list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)))
     (H17' : list_norepet (map fst (fn_vars f)))
     (H16 : Genv.find_funct_ptr psi b = Some (Internal f))
     (ve' : env) (jm' : juicy_mem) (te' : temp_env) 
     (H15 : alloc_variables empty_env (m_dry jm) (fn_vars f) ve' (m_dry jm'))
    (TC3 : typecheck_temp_environ (make_tenv tx) (temp_types Delta))
    (TC4 : typecheck_var_environ (make_venv vx) (var_types Delta))
    (TC5 : typecheck_glob_environ (filter_genv psi) (glob_types Delta))
   (H : forall (b : ident) (b0 : funspec) (a' : rmap),
    necR (m_phi jm') a' ->
    (glob_types Delta) ! b = Some (Global_func b0) ->
    exists b1 : val,
      exists b2 : address,
        (filter_genv psi b = Some (b1, type_of_funspec b0) /\ val2adr b1 b2) /\
        (func_at b0 b2) a')
   (H1 : forall (b : address) (b0 : funspec) (a' : rmap),
     necR (m_phi jm') a' ->
     (func_at' b0 b) a' ->
     exists b1 : ident,
       exists b2 : val,
         (filter_genv psi b1 = Some (b2, type_of_funspec b0) /\ val2adr b2 b) /\
         (exists fs : funspec,
            (glob_types Delta) ! b1 = Some (Global_func fs)))
   (l : list ident) (l0 : list type) 
    (Heqp : (l, l0) = split (fn_params f))
   (TC2 : denote_tc_assert (typecheck_exprlist Delta l0 bl)
        (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
   (H21 : bind_parameter_temps (fn_params f)
        (eval_exprlist l0 bl
           (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
        (create_undef_temps (fn_temps f)) = Some te')
   (TE : typecheck_environ
        Delta (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx))),
   typecheck_environ
     (make_tycontext_t (fn_params f) (fn_temps f), make_tycontext_v (fn_vars f),
     fn_return f, glob_types Delta) (mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
Proof.
 intros.
 pose (rho3 := mkEnviron (filter_genv psi) (make_venv ve') (make_tenv te')).
  
unfold typecheck_environ. repeat rewrite andb_true_iff. 
repeat split. clear H H1 H15.  
unfold typecheck_temp_environ in *. intros. simpl. 
unfold temp_types in *. simpl in *.
apply func_tycontext_t_sound in H; auto.
 clear - H21 H TC2 TC3 Heqp H17 TE. 

destruct H. (*in params*)
destruct H. subst.
forget (create_undef_temps (fn_temps f)) as temps.
generalize dependent temps. 
generalize dependent l. generalize dependent l0.
generalize dependent bl. generalize dependent te'.
{  induction (fn_params f); intros.  
   + inv H.
   + simpl in *. 
     destruct a. simpl in *. remember (split l). destruct p. 
     simpl in *. destruct H. 
      - clear IHl. destruct bl. inv H.  inv Heqp. inv TC2.   
        inv H. inv Heqp. simpl in *. 
        repeat (rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
        destruct TC2 as [[? ?] ?].
        rewrite (pass_params_ni _ _ id _ _ H21) by (inv H17; contradict H4; apply in_app; auto).
        rewrite PTree.gss.
        exists (force_val
          (Cop.sem_cast
             (eval_expr e
                (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx)))
             (typeof e) ty)).
        split. rewrite cop2_sem_cast. auto.
        right. rewrite cop2_sem_cast. eapply typecheck_val_sem_cast; eauto.
      - inv Heqp. destruct bl. inv TC2. inv H17. simpl in TC2.
        repeat (rewrite tc_andp_sound in TC2; simpl in TC2; super_unfold_lift).
        destruct TC2 as [[? ?] ?]. assert (i <> id). intro. subst.
        apply H2. apply in_or_app. left. apply in_map with (f := fst) in H. apply H.
        remember (eval_exprlist (t :: l3) (e :: bl)
            (mkEnviron (filter_genv psi) (make_venv vx) (make_tenv tx))).
        destruct l0; inv H21. simpl in Heql0.
        super_unfold_lift. inv Heql0.  
        eapply IHl; eauto. 
}

(*In temps*)
destruct H. subst.
apply list_norepet_app in H17. destruct H17 as [? [? ?]]. 
generalize dependent (fn_params f). generalize dependent bl.
generalize dependent l0. generalize dependent l. generalize dependent te'.  

induction (fn_temps f); intros.  
inv H. 

simpl in *. destruct H. destruct a. inv H. simpl in *. 
clear IHl. exists Vundef. simpl in *. split; auto. inv H1.  
assert (In id (map fst (l2)) -> False). 
intros. 
unfold list_disjoint in *. eapply H2. eauto. left. auto. auto.
eapply pass_params_ni with (id := id) in H21; auto.  rewrite PTree.gss in *. auto. 


destruct a. 
destruct (eq_dec id i). subst. 
apply pass_params_ni with (id := i) in H21. 
rewrite PTree.gss in *. exists  Vundef. auto.
intros. unfold list_disjoint in *. intuition. 
eapply H2. eauto. left. auto. auto. 

apply smaller_temps_exists with (i := id) in H21.
destruct H21.  destruct H3. 
eapply IHl in H3; auto. 
destruct H3. destruct H3.
exists x0. split. unfold Map.get in *. 
unfold make_tenv in *. rewrite <- H4. auto. auto.
inv H1; auto. unfold list_disjoint in *. intros.
apply H2. auto. right. auto. apply Heqp. auto. 

unfold typecheck_var_environ in *. intros. 



clear TC3 TC5. 
simpl in *. unfold typecheck_var_environ in *.
unfold func_tycontext' in *. unfold var_types in *. 
simpl in *. apply func_tycontext_v_sound in H0; auto.  
generalize dependent (m_dry jm).
assert (forall id, In id (map fst (fn_vars f)) -> empty_env ! id = None). 
intros. rewrite PTree.gempty; auto. 
generalize dependent empty_env. 
induction (fn_vars f); intros. inversion H15. subst.   
inv H0. 

simpl in H0. 
destruct H0. destruct a. inv H0. 
inv H15.  apply alloc_vars_lookup with (id := id) in H10. 
unfold Map.get. unfold make_venv. rewrite H10. 
rewrite PTree.gss. eauto. inv H17'; auto. 
intros. inv H17'. rewrite PTree.gsspec. if_tac.
subst. intuition.  
apply H2. simpl in *. auto. 
rewrite PTree.gss; eauto. 

inv H17'; inv H15. 
apply IHl1 in H12. destruct H12. 
exists x. auto. auto. auto. intros. 
simpl in *. rewrite PTree.gso. apply H2; auto. 
intro. subst. intuition. 

unfold ge_of in *. simpl in *. auto. 

simpl in *. 
unfold typecheck_environ in *.  
destruct TE as [_ [_ [_ TE]]]. 
unfold same_env in *. intros. simpl in *. 
specialize (TE id t H0). 
unfold make_venv.
unfold func_tycontext'. unfold var_types. simpl in *.
assert (empty_env ! id = None). rewrite PTree.gempty. auto. 
generalize dependent empty_env.  generalize dependent (m_dry jm). 
induction (fn_vars f); intros. inversion H15.  subst. left. 
auto.
simpl in *. destruct a. inv H15. 
rewrite PTree.gsspec. if_tac. eauto.

apply IHl1 in H11. destruct H11. auto. right. 
congruence. 
inv H17'. auto. rewrite PTree.gso; auto.
Qed. 

Lemma free_juicy_mem_level:
  forall jm m b lo hi H, level (free_juicy_mem jm m b lo hi H) = level jm.
Proof.
 intros;  simpl;  unfold inflate_free; simpl.
 rewrite level_make_rmap. auto.
Qed.

Lemma free_list_free:
  forall m b lo hi l' m', 
       free_list m ((b,lo,hi)::l') = Some m' ->
         {m2 | free m b lo hi = Some m2 /\ free_list m2 l' = Some m'}.
Proof.
simpl; intros.
 destruct (free m b lo hi). eauto. inv H.
Qed.

Inductive free_list_juicy_mem: 
      forall  (jm: juicy_mem) (bl: list (block * BinInt.Z * BinInt.Z))
                                         (jm': juicy_mem), Prop :=
| FLJM_nil: forall jm, free_list_juicy_mem jm nil jm
| FLJM_cons: forall jm b lo hi bl jm2 jm' 
                          (H: free (m_dry jm) b lo hi = Some (m_dry jm2)), 
                          free_juicy_mem jm (m_dry jm2) b lo hi H = jm2 ->
                          free_list_juicy_mem jm2 bl jm' ->
                          free_list_juicy_mem jm ((b,lo,hi)::bl) jm'.

Lemma free_list_juicy_mem_i:
  forall jm bl m', free_list (m_dry jm) bl = Some m' ->
   exists jm', free_list_juicy_mem jm bl jm'
                  /\ m_dry jm' = m'
                  /\ level jm = level jm'.
Proof.
intros jm bl; revert jm; induction bl; intros.
*
 inv H; exists jm; split3; auto. constructor.
*
 destruct a as [[b lo] hi].
 destruct (free_list_free _ _ _ _ _ _ H) as [m2 [? ?]].
 pose (jm2 := (free_juicy_mem jm m2 b lo hi H0)).
 specialize (IHbl  jm2 m' H1).
 destruct IHbl as [jm' [? [? ?]]].
 exists jm'; split3; auto.
 apply (FLJM_cons jm b lo hi bl jm2 jm' H0 (eq_refl _) H2).
 rewrite <- H4.
 unfold jm2.
 symmetry; apply free_juicy_mem_level.
Qed.

Definition freeable_blocks: list (block * BinInt.Z * BinInt.Z) -> mpred :=
  fold_right (fun (bb: block*BinInt.Z * BinInt.Z) a => 
                        match bb with (b,lo,hi) => 
                                          sepcon (VALspec_range (hi-lo) Share.top Share.top (b,lo)) a
                        end)
                    emp.


Lemma free_juicy_mem_ext:
  forall jm1 jm2 b lo hi m1 m2 H1 H2,
      jm1=jm2 -> m1=m2 -> free_juicy_mem jm1 m1 b lo hi H1 = free_juicy_mem jm2 m2 b lo hi H2.
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
 revert H0; induction H; simpl freeable_blocks; intros.
 rewrite emp_sepcon in H0; auto.
 rewrite sepcon_assoc in H2.
 destruct H2 as [phi1 [phi2 [? [? ?]]]].
 pose proof  (@juicy_free_lemma jm b lo hi _ phi1 H H3).
 spec H5. apply (join_core H2).
 spec H5.
 intros. specialize (H3 l). hnf in H3.  if_tac in H3. destruct H3 as [v ?]. destruct H3. hnf in H3.
 exists Share.top; exists pfullshare; exists NoneP.
 split3; auto. apply top_correct'. apply top_correct'.
 rewrite H3 in H6; inversion H6; clear H6. subst k pp sh rsh.
  clear - H2 H3.  
  apply (resource_at_join _ _ _ l) in H2. rewrite H3 in H2.
  replace (mk_lifted Share.top x) with pfullshare in H2
    by (unfold pfullshare; f_equal; apply proof_irr).
 rewrite preds_fmap_NoneP in H2. inv H2.
 rewrite (join_sub_share_top rsh3) by (econstructor; apply RJ).
  reflexivity.
 pfullshare_join.
 do 3 red in H3. rewrite H6 in H3. apply YES_not_identity in H3; contradiction.
 apply IHfree_list_juicy_mem.
 pose proof (join_canc (join_comm H5) (join_comm H2)).
 rewrite H0 in *. subst phi2; auto.
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

Lemma elements_remove:
  forall {A} (id: positive) (v: A) (rho: PTree.t A),
       PTree.get id rho = Some v ->
       exists l1, exists l2, PTree.elements rho = l1 ++ (id,v) :: l2 /\ 
                             PTree.elements (PTree.remove id rho) = l1++l2.
Proof.
intros.
unfold PTree.elements.
unfold PTree.t in *.
forget (@nil (positive * A)) as rest.
pattern id at 1;
rewrite <- (PTree.append_neutral_l id).
forget 1%positive as k.
revert id H k rest; induction rho; simpl; intros.
rewrite PTree.gleaf in H. inv H.
destruct o, id; simpl in H; try discriminate H.
*
 clear IHrho1.
 replace (PTree.remove id~1 (PTree.Node rho1 (Some a) rho2))
   with (PTree.Node rho1 (Some a) (PTree.remove id rho2))
  by (destruct rho1; auto).
 simpl.
 rewrite (PTree.append_assoc_1 k id).
 destruct (IHrho2 _ H (PTree.append k 3) rest) as [al [bl [? ?]]]; clear IHrho2.
 rewrite H0.
do 2 eexists; split.
rewrite app_comm_cons.
rewrite <- xelements_app. reflexivity.
 change ((k,a)::al) with (((k,a)::nil)++al). 
 rewrite xelements_app.
 rewrite app_ass.
 rewrite <- H1.
 rewrite <- xelements_app. 
 simpl.
 rewrite xelements_app.
 reflexivity.
* 
 clear IHrho2.
 simpl.
 rewrite (PTree.append_assoc_0 k id).
 apply IHrho1; auto.
*
 inv H. clear.
 evar (al: list (positive * A)).
 evar (bl: list (positive * A)).
 exists al,bl.
 rewrite PTree.append_neutral_r.
 change ( ((k, v) :: PTree.xelements rho2 (PTree.append k 3) rest))
   with  ((nil ++ (k, v) :: nil) ++  (PTree.xelements rho2 (PTree.append k 3) rest)).
 repeat rewrite <- xelements_app.
 split.
 rewrite app_ass.
 unfold al, bl; reflexivity.
 unfold al, bl; clear al bl.
 rewrite xelements_app. simpl app.
 destruct rho1.
 destruct rho2; reflexivity.
 destruct o; try reflexivity.
* 
 clear IHrho1.
 rewrite (PTree.append_assoc_1 k id).
 destruct (IHrho2 _ H (PTree.append k 3) rest) as [al [bl [? ?]]]; clear IHrho2.
 rewrite H0.
 evar (al': list (positive * A)).
 evar (bl': list (positive * A)).
 exists al',bl'; split.
 rewrite <- xelements_app.
 unfold al', bl'; reflexivity.
 unfold al', bl'; clear al' bl'.
 change (al) with (nil++al).
 rewrite <- xelements_app.
 rewrite app_ass.
 rewrite <- H1.
 rewrite xelements_app.
 simpl.
 destruct rho1; try reflexivity.
 destruct (PTree.remove id rho2); try reflexivity.
*
 clear IHrho2.
 rewrite (PTree.append_assoc_0 k id).
 destruct (IHrho1 _ H (PTree.append k 2) (PTree.xelements rho2 (PTree.append k 3) rest))
   as [al [bl [? ?]]]; clear IHrho1.
 exists al, bl; split; auto.
 rewrite <- H1.
 clear.
 simpl.
 destruct rho2; try reflexivity.
 destruct (PTree.remove id rho1); try reflexivity.
Qed.

Lemma stackframe_of_freeable_blocks:
  forall Delta f rho ve,
      list_norepet (map fst (fn_vars f)) ->
        ve_of rho = make_venv ve ->
      guard_environ (func_tycontext' f Delta) (Some f) rho ->
       stackframe_of f rho |-- freeable_blocks (blocks_of_env ve).
Proof.
 intros.
 destruct H1. destruct H2 as [H7 _].
 unfold stackframe_of.
 unfold func_tycontext' in H1.
 unfold typecheck_environ in H1.
 destruct H1 as [_ [?  [_ _]]].
 rewrite H0 in H1.
 unfold make_venv in H1.
 unfold var_types in H1.
 simpl in H1. unfold make_tycontext_v in H1.
 unfold blocks_of_env.
 replace (fold_right
  (fun (P Q : environ -> pred rmap) (rho0 : environ) => P rho0 * Q rho0)
  (fun _ : environ => emp)
  (map (fun idt : ident * type => var_block Share.top idt) (fn_vars f)) rho) 
  with (fold_right (@sepcon _ _ _ _ _) emp (map (fun idt => var_block Share.top idt rho) (fn_vars f))).
 2: clear; induction (fn_vars f); simpl; f_equal; auto.
 unfold var_block. unfold lvalue_block; simpl. unfold eval_var.
  rewrite H0. unfold make_venv. forget (ge_of rho) as ZZ. rewrite H0 in H7; clear rho H0.
 revert ve H1 H7; induction (fn_vars f); simpl; intros.
 case_eq (PTree.elements ve); simpl; intros; auto.
 destruct p as [id ?].
 pose proof (PTree.elements_complete ve id p). rewrite H0 in H2. simpl in H2.
 specialize (H7 id). unfold make_venv in H7. rewrite H2 in H7; auto.
 destruct p; inv H7.
 inv H.
 destruct a as [id ty]. simpl in *.
 specialize (IHl H4 (PTree.remove id ve)).
 assert (exists b, ve ! id = Some (b,ty)).
 unfold typecheck_var_environ in *. 
  specialize (H1 id ty).
  rewrite PTree.gss in H1. destruct H1 as [b ?]; auto. exists b; apply H.
 destruct H as [b H].
 destruct (elements_remove id (b,ty) ve H) as [l1 [l2 [? ?]]].
 rewrite H0.
 rewrite map_app. simpl map.
 apply derives_trans with (freeable_blocks ((b,0,sizeof ty) ::  (map block_of_binding (l1 ++ l2)))).
 Focus 2.
 clear. induction l1; simpl; auto.
 destruct a as [id' [hi lo]]. simpl. rewrite <- sepcon_assoc. 
 rewrite (sepcon_comm (VALspec_range (sizeof ty - 0) Share.top Share.top (b, 0))).
 rewrite sepcon_assoc. apply sepcon_derives; auto.
 simpl freeable_blocks. rewrite <- H2.
 apply sepcon_derives.
 unfold Map.get. rewrite H. rewrite eqb_type_refl.
 case_eq (type_is_volatile ty); intros; simpl negb; cbv iota;
 unfold memory_block. normalize. {
 normalize.
 rewrite memory_block'_eq.
 2: rewrite Int.unsigned_zero; omega.
 Focus 2.
 rewrite Int.unsigned_zero. rewrite Zplus_0_r.
 rewrite Int.unsigned_repr.
 rewrite Coqlib.nat_of_Z_eq; auto.
 pose proof (sizeof_pos ty); omega.
 pose proof (sizeof_pos ty); omega.
 rewrite Int.unsigned_zero.
 replace (sizeof ty - 0) with (sizeof ty) by omega.
 rewrite Int.unsigned_repr;  auto.
 unfold memory_block'_alt.
 rewrite Share.contains_Rsh_e by apply top_correct'.
 rewrite Share.contains_Lsh_e by apply top_correct'.
 rewrite Coqlib.nat_of_Z_eq; auto. 
 pose proof (sizeof_pos ty); omega.
 split; auto.  pose proof (sizeof_pos ty); omega.
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
 unfold typecheck_var_environ in *. 
 intros id' ty' ?.
 specialize (H1 id' ty').
 assert (id<>id').
 intro; subst id'.
 clear - H3 H5; induction l; simpl in *. rewrite PTree.gempty in H5; inv H5.
 destruct a; simpl in *.
 rewrite PTree.gso in H5. auto. auto.
 destruct H1 as [v ?].
 rewrite PTree.gso; auto.
 exists v. unfold Map.get. rewrite PTree.gro; auto.
 hnf; intros.
 destruct (make_venv (PTree.remove id ve) id0) eqn:H5; auto.
 destruct p.
 unfold make_venv in H5.
 destruct (eq_dec id id0).
 subst.  rewrite PTree.grs in H5. inv H5. 
 rewrite PTree.gro in H5 by auto.
 specialize (H7 id0). unfold make_venv in H7. rewrite H5 in H7.
 destruct H7; auto. inv H6; congruence.
Qed.

Definition maybe_retval (Q: environ -> mpred) retty ret :=
 match ret with
 | Some id => fun rho => Q (get_result1 id rho)
 | None => 
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.

Lemma VALspec_range_free:
  forall n b phi1 jm,
  app_pred (VALspec_range n Share.top Share.top (b, 0)) phi1 ->
  join_sub phi1 (m_phi jm) ->
  {m' | free (m_dry jm) b 0 n = Some m' }.
Proof.
intros.
apply range_perm_free.
destruct H0 as [phi2 H0].
hnf; intros.
pose proof (juicy_mem_access jm (b,ofs)).
hnf. unfold access_at in H2. simpl in H2. rewrite H2. clear H2.
specialize (H (b,ofs)).
hnf in H.
rewrite if_true in H by (split; auto; omega).
destruct H as [v ?].
apply (resource_at_join _ _ _ (b,ofs)) in  H0.
destruct H.
replace (mk_lifted Share.top x) with pfullshare in H.
hnf in H.
rewrite H in H0.
inv H0; try pfullshare_join.
inv RJ.
rewrite Share.glb_commute, Share.glb_top in H0.
subst rsh2.
rewrite Share.lub_bot.
unfold perm_of_res; simpl.
rewrite perm_of_sh_fullshare. constructor.
symmetry; apply top_pfullshare; reflexivity.
Qed.

Lemma can_free_list:
  forall Delta F f jm psi ve te
  (NOREP: list_norepet (map (@fst _ _) (fn_vars f))),
   guard_environ (func_tycontext' f Delta) (Some f)
        (construct_rho psi ve te) ->
    (F * stackframe_of f (construct_rho psi ve te))%pred (m_phi jm) ->
   exists m2, free_list (m_dry jm) (blocks_of_env ve) = Some m2.
Proof.
intros.
destruct H0 as [? [? [? [_ ?]]]].
unfold stackframe_of in H1.
unfold blocks_of_env in *.
destruct H as [_ [H _]]; clear - NOREP H H0 H1. simpl in H.
pose (F vl := (fold_right
        (fun (P Q : environ -> pred rmap) (rho : environ) => P rho * Q rho)
        (fun _ : environ => emp)
        (map (fun idt : ident * type => var_block Share.top idt) vl))).
change ((F (fn_vars f)  (construct_rho psi ve te)) x0) in H1.
assert (forall id b t, In (id,(b,t)) (PTree.elements ve) -> 
              In (id,t) (fn_vars f)). { 
 intros.
  apply PTree.elements_complete in  H2.
  specialize (H id); unfold make_venv in H; rewrite H2 in H.
   apply H.
}
clear H.
assert (Hve: forall i bt, In (i,bt) (PTree.elements ve) -> ve ! i = Some bt).
apply PTree.elements_complete.
assert (NOREPe: list_norepet (map (@fst _ _) (PTree.elements ve)))
  by apply PTree.elements_keys_norepet.
forget (PTree.elements ve) as el. 
rename x0 into phi.
assert (join_sub phi (m_phi jm)).
econstructor; eauto.
clear H0.
forget (fn_vars f) as vl.
revert vl phi jm H H1 H2 Hve NOREP NOREPe; induction el; intros;
  [ solve [simpl; eauto] | ].
simpl in H2.
destruct a as [id [b t]]. simpl in NOREPe,H2|-*.
assert (H2': In (id,t) vl).
apply H2 with b. auto.
specialize (IHel (filter (fun idt => negb (eqb_ident (fst idt) id)) vl)).
replace (F vl (construct_rho psi ve te))
 with  (var_block Share.top (id,t)  (construct_rho psi ve te) 
               * F (filter (fun idt => negb (eqb_ident (fst idt) id)) vl) (construct_rho psi ve te)) in H1.
Focus 2. {
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
 (var_block Share.top a (construct_rho psi ve te) * 
     F vl (construct_rho psi ve te)); [ | reflexivity].
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
} Unfocus.
pose (H0:=True).
destruct H1 as [phi1 [phi2 [? [? ?]]]].

unfold var_block, lvalue_block in H3.
normalize in H3.
simpl in H3.
assert (0 <= sizeof t) by (pose proof (sizeof_pos t); omega).
simpl in H5.
unfold eval_var, Map.get in H3. simpl in H3.
unfold make_venv in H3.
rewrite (Hve id (b,t)) in H3 by (left; auto).
rewrite eqb_type_refl in H3.
destruct (type_is_volatile t) eqn:?; try (contradiction H3).
simpl in H3.
rewrite Int.unsigned_repr in H3 by omega.
change nat_of_Z with Z.to_nat in H3.
rewrite memory_block'_eq in H3; 
 try rewrite Int.unsigned_zero; try omega.
2: rewrite Z.add_0_r; rewrite Z2Nat.id by omega; auto.
unfold memory_block'_alt in H3.
rewrite Int.unsigned_zero in H3.
rewrite Share.contains_Lsh_e in H3 by apply top_correct'.
rewrite Share.contains_Rsh_e in H3 by apply top_correct'.
rewrite Z2Nat.id in H3 by omega.
assert (join_sub phi1 (m_phi jm))
 by ( apply join_sub_trans with phi; auto; eexists; eauto).
destruct (VALspec_range_free _ _ _ _ H3 H7)
 as [m3 ?H].
pose (jm3 := free_juicy_mem _ _ _ _ _ H8).
destruct H7 as [phi3 H7].
assert (phi3 = m_phi jm3).
apply join_comm in H7.
eapply join_canc. apply H7.
apply join_comm.
apply (@juicy_free_lemma _ _ _ _ _ phi1 H8).
rewrite Z.sub_0_r; auto.
apply join_comm in H7. apply join_core in H7; auto.
intros.
apply (resource_at_join _ _ _ l) in H7.
rewrite H9 in H7.
clear - H7.
inv H7. do 3 eexists; split3; eauto. eexists; eauto. apply join_sub_refl.
do 3 eexists; split3; eauto. eexists; eauto. eexists; eauto.
subst phi3.
assert (join_sub phi2 (m_phi jm3)).
destruct H as [phix H].
destruct (join_assoc (join_comm H1) H) as [phi7 [? ?]].
eapply crosssplit_wkSplit.
apply H7. apply H10.
exists phi; auto.
destruct (IHel phi2 jm3 H9) as [m4 ?]; auto; clear IHel.
intros. 
specialize (H2 id0 b0 t0).
spec H2; [ auto |].
assert (id0 <> id).
clear - NOREPe H10.
inv NOREPe. intro; subst.
apply H1. change id with (fst (id,(b0,t0))); apply in_map; auto.
clear - H2 H11.
induction vl; simpl in *; auto.
destruct H2. subst a. simpl.
replace (eqb_ident id0 id) with false; simpl; auto.
pose proof (eqb_ident_spec id0 id); destruct (eqb_ident id0 id); simpl in *; auto.
contradiction H11; apply H; auto.
pose proof (eqb_ident_spec (fst a) id); destruct (eqb_ident (fst a) id); simpl in *; auto.
intros; eapply Hve; eauto.
right; auto.
clear - NOREP.
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
inv NOREPe; auto.
rewrite H8.
exists m4; auto.
Qed.

Lemma necR_m_dry':
  forall jm jm', m_dry jm = m_dry jm' ->
                (necR (m_phi jm) (m_phi jm')) ->
            necR jm jm'.
Proof.
intros.
remember (m_phi jm) as phi.
remember (m_phi jm') as phi'.
unfold necR in *.
rewrite clos_rt_rt1n_iff in *.
revert jm jm' Heqphi Heqphi' H; induction H0; intros; subst.
replace jm' with jm. constructor 1.
apply juicy_mem_ext; auto.
destruct (can_age_jm jm) as [jm1 ?].
destruct (age1 (m_phi jm)) eqn:?; congruence.
constructor 2 with jm1; auto.
apply age1_juicy_mem_unpack in H2. destruct H2.
apply IHclos_refl_trans_1n.
hnf in H,H2. congruence.
congruence.
congruence.
Qed. (* maybe don't need this? *)

Lemma age_juicy_mem_i:
  forall jm jm', m_dry jm = m_dry jm' ->
        age (m_phi jm) (m_phi jm') ->
       age jm jm'.
Proof.
intros. 
hnf in H0 |-*.
unfold age1; simpl.
apply age1_juicy_mem_unpack'; auto.
Qed. (* maybe don't need this? *)

Lemma rmap_age_i:
 forall w w' : rmap,
    level w = S (level w') ->
   (forall l, resource_fmap (approx (level w')) (w @ l) = w' @ l) -> 
    age w w'.
Proof.
intros.
hnf.
destruct (levelS_age1 _ _ H).
assert (x=w'); [ | subst; auto].
assert (level x = level w')
  by (apply age_level in H1; omega).
apply rmap_ext; auto.
intros.
specialize (H0 l).
rewrite (age1_resource_at w x H1 l (w@l)).
rewrite H2.
apply H0.
symmetry; apply resource_at_approx.
Qed.

Lemma free_juicy_mem_resource_decay:
  forall jm b lo hi m' jm'
     (H : free (m_dry jm) b lo hi = Some m'), 
    free_juicy_mem jm m' b lo hi H = jm' ->
    resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
intros.
 subst jm'. simpl.
 apply (inflate_free_resource_decay _ _ _ _ _ H).
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
 | Some i => match (temp_types Delta) ! i with Some (t',_) => t=t' | _ => False end
 end.

Lemma derives_refl' {A: Type}  `{ageable A}: 
    forall P Q: pred A, P=Q -> P |-- Q.
Proof.  intros; subst; apply derives_refl. Qed.

Lemma semax_call_aux:
 forall (Delta : tycontext) (A : Type)
  (P Q Q' : A -> assert) (x : A) (F : environ -> pred rmap)
  (F0 : assert) (ret : option ident) (fsig : funsig) (a : expr)
  (bl : list expr) (R : ret_assert) (psi : genv) (vx:env) (tx:Clight.temp_env) (k : cont) (rho : environ)
  (ora : OK_ty) (jm : juicy_mem) (b : block) (id : ident),
   Cop.classify_fun (typeof a) =
   Cop.fun_case_f (type_of_params (fst fsig)) (snd fsig) ->
   tc_fn_return Delta ret (snd fsig) ->
   tc_expr Delta a rho (m_phi jm) ->
   tc_exprlist Delta (snd (split (fst fsig))) bl rho (m_phi jm) ->
    (*map typeof bl = map (@snd _ _) (fst fsig) ->*)
    guard_environ Delta (current_function k) rho ->
    (snd fsig=Tvoid -> ret=None) ->
    closed_wrt_modvars (Scall ret a bl) F0 ->
    R EK_normal None = (fun rho0 : environ => EX old:val, substopt ret old F rho0 * maybe_retval (Q x) (snd fsig) ret rho0) ->
    rho = construct_rho (filter_genv psi) vx tx ->
    (*filter_genv psi = ge_of rho ->*)
    eval_expr a rho = Vptr b Int.zero ->
    (funassert Delta rho) (m_phi jm) ->
    (rguard Espec psi (exit_tycon (Scall ret a bl) Delta) (frame_ret_assert R F0) k) (level (m_phi jm)) ->
    (believe Espec Delta psi Delta) (level (m_phi jm)) ->
    (glob_types Delta)!id = Some (Global_func (mk_funspec fsig A P Q')) ->
    Genv.find_symbol psi id = Some b ->
    (forall vl : environ, (!|>(Q' x vl <=> Q x vl)) (m_phi jm)) ->
    (|>(F0 rho * F rho *
           P x (make_args (map (@fst  _ _) (fst fsig)) 
             (eval_exprlist (snd (split (fst fsig))) bl rho) rho)
            )) (m_phi jm) ->
   jsafeN (@OK_spec Espec) psi (level (m_phi jm)) ora
     (State (vx) (tx) (Kseq (Scall ret a bl) :: k)) jm.
Proof.
intros Delta A P Q Q' x F F0 ret fsig a bl R psi vx tx k rho ora jm b id.
intros TC0 TCret TC1 TC2 TC3 TC5 H HR H0 H3 H4 H1 Prog_OK H8 H7 H11 H14.
pose (H6:=True); pose (H9 := True); pose (H16:=True);
pose (H12:=True); pose (H10 := True); pose (H5:=True).
(*************************************************)
assert (Prog_OK' := Prog_OK).
specialize (Prog_OK' (Vptr b Int.zero) fsig A P Q' _ (necR_refl _)).
(*************************************************)
case_eq (level (m_phi jm)); [solve [simpl; auto] | intros n H2].
simpl.
destruct (levelS_age1 _ _ H2) as [phi' H13].
assert (LATER: laterR (level (m_phi jm)) n) by (constructor 1; rewrite H2; reflexivity).
spec Prog_OK'.
hnf. exists id; split; auto.
exists b; split; auto.
clear H16.
clear H10 H6 H5 H8.
specialize (H14 _ (age_laterR H13)).
do 4 (pose proof I).
destruct Prog_OK'.
admit.  (* external case *)
destruct H15 as [b' [f [[? [? [? ?]]] ?]]].
destruct H18 as [H17' H18].
inversion H15; clear H15; subst b'.
specialize (H19 x n LATER).
rewrite semax_fold_unfold in H19.
apply (pred_nec_hereditary _ _ n (laterR_necR LATER)) in Prog_OK.
pose (F0F := fun _: environ => F0 rho * F rho).
specialize (H19 _ _ _ (necR_refl _) (tycontext_sub_refl _)  _ (necR_refl _) (Prog_OK)  
                      (Kseq (Sreturn None) :: Kcall ret f (vx) (tx) :: k)
                       F0F _ (necR_refl _)).
unfold F0F in *; clear F0F.
spec H19 ; [clear H19 |]. {
 split.
 repeat intro; f_equal.
 intros ek vl te ve.  
 unfold frame_ret_assert.
 remember ((construct_rho (filter_genv psi) ve te)) as rho'.
 rewrite <- (sepcon_comm (stackframe_of f rho')).
 unfold function_body_ret_assert.
 destruct ek; try solve [normalize].
 apply prop_andp_subp; intro. simpl in H15.
 repeat rewrite andp_assoc.
 apply subp_trans' with
  (F0 rho * F rho * (stackframe_of f rho' * bind_ret vl (fn_return f) (Q x) rho') && funassert Delta rho').
 apply andp_subp'; auto.
 rewrite (sepcon_comm (F0 rho * F rho)).
 apply sepcon_subp'; auto.
 apply sepcon_subp'; auto.
 unfold bind_ret.
 destruct vl.
 apply andp_subp'; auto.
 apply pred_eq_e1; apply (H11 _ _ LATER).
 destruct (fn_return f); auto.
 apply pred_eq_e1; apply (H11 _ _ LATER).
 clear Q' H11.
 pose proof I.
 pose proof I.
 
 intros wx ? w' ? ?.
 assert (n >= level w')%nat.
 apply necR_level in H21.
 apply le_trans with (level wx); auto.
 clear wx H20 H21.
 intros ora' jm' VR ?.
 subst w'.
 pose (H20:=True).
 assert (FL: exists m2, free_list (m_dry jm')  (Clight.blocks_of_env ve) = Some m2). {
 subst rho'.
 destruct H22 as [H22 _].
 rewrite (sepcon_comm (stackframe_of f _)) in H22.
 repeat rewrite <- sepcon_assoc in H22.
 clear - H17' H22 H15.
 eapply can_free_list; try eassumption.
}
destruct FL as [m2 FL2].
destruct (free_list_juicy_mem_i _ _ _ FL2)
 as [jm2 [FL [? FL3]]]. subst m2.
pose (rval := match vl with Some v => v | None => Vundef end). 
pose (te2 := match ret with
            | None => tx
            | Some rid => PTree.set rid rval tx
            end).
specialize (H1 EK_normal None te2 vx).
unfold frame_ret_assert in H1.  
rewrite HR in H1; clear R HR. simpl exit_cont in H1.
specialize (H1 (m_phi jm2)).
spec H1.
clear - FL3 H2 H23.
repeat rewrite <- level_juice_level_phi in *. omega. 
specialize (H1 _ (necR_refl _)). simpl in H15. 
spec H1; [clear H1 | ].
split.
simpl. unfold te2. destruct ret; unfold rval.
destruct vl.   
assert (typecheck_val v (fn_return f) = true).
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. destruct H. rewrite tc_val_eq in H; apply H. 
unfold construct_rho. rewrite <- map_ptree_rel.
apply guard_environ_put_te'. subst rho; auto.
intros.
 cut (fst t = fn_return f). intros. rewrite H24; auto.
hnf in TCret; rewrite H21 in TCret. destruct t; subst; auto.
assert (f.(fn_return)=Tvoid).  
clear - H22; unfold bind_ret in H22; destruct (f.(fn_return)); normalize in H22; try contradiction; auto. 
unfold fn_funsig in H18. rewrite H1 in H18. rewrite H18 in TC5. simpl in TC5.
specialize (TC5 (eq_refl _)); congruence. 
rewrite <- H0. auto.
 destruct H22 as [H22a H22b].
 split.
 rewrite sepcon_comm.
 rewrite <- exp_sepcon1.
  rewrite <- sepcon_assoc.
 rewrite sepcon_comm in H22a|-*.
  rewrite sepcon_assoc in H22a.
 assert (bind_ret vl (fn_return f) (Q x) rho' * (F0 rho * F rho) 
            |-- (maybe_retval (Q x) (snd fsig) ret (construct_rho (filter_genv psi) vx te2) *
 (F0 (construct_rho (filter_genv psi) vx te2) *
  EX old: val, substopt ret old F (construct_rho (filter_genv psi) vx te2)))). {
apply sepcon_derives.
*
 clear dependent a. clear H11 H19 H20 H10 H9 H12 H5 H6 H8.
 clear Prog_OK ora ora'.  subst rho' fsig.
 clear H22b VR. clear FL jm2 FL2 FL3.
 clear b H16 H7. clear bl TC2 H14. 
 unfold te2; clear te2. unfold rval; clear rval.
 unfold bind_ret.
 unfold get_result1. simpl.
 unfold bind_ret.
 destruct vl.
 +apply derives_extract_prop; intro.
    unfold maybe_retval.
   destruct ret.
   unfold get_result1. simpl.
   apply derives_refl'. f_equal.
   unfold env_set; simpl.
   f_equal. unfold eval_id; simpl.
   f_equal. unfold Map.get. unfold make_tenv. rewrite PTree.gss. reflexivity.
   destruct (fn_return f); try contradiction H; 
   apply exp_right with v;    apply derives_refl.
 +
   unfold fn_funsig in TC5. simpl in TC5.
   destruct (fn_return f) eqn:?; try apply FF_derives.
   specialize (TC5 (eq_refl _)). subst ret.
   unfold maybe_retval. apply derives_refl.
*
  subst rho.
  unfold te2.
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
  destruct p as [t' init]; subst t'.
  destruct TC3 as [[TC3 _] _].
  hnf in TC3; simpl in TC3.
  specialize (TC3 _ _ _ Heqo).
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
 apply H1; clear H1.
 eapply free_list_juicy_mem_lem; eauto.
 eapply sepcon_derives; try apply H22a; auto.
 apply (stackframe_of_freeable_blocks (func_tycontext' f Delta) _ _ _ H17'); auto.
 subst rho'; reflexivity.
 rewrite VR in H22b; clear - H22b.
  admit.  (* looks OK *)
specialize (H1 ora' jm2).
specialize (H1 (eq_refl _) (eq_refl _)).
case_eq (@level rmap ag_rmap (m_phi jm')); intros; [solve [auto] |].
destruct (levelS_age1 jm' _ H21) as [jm'' ?].
destruct (age_twin' jm' jm2 jm'') as [jm2'' [? ?]]; auto.
pose proof (age_safe _ _ _ _ H26 _ _ _ H1).
exists  (State (vx)(te2) k); exists jm2''.
replace n0 with (level jm2'')
 by (rewrite <- H25; 
      apply age_level in H24; 
      rewrite <- level_juice_level_phi in H21;
      clear - H21 H24; omega).
split; auto.
split.
simpl.
rewrite (age_jm_dry H26) in FL2.
destruct vl. 
Focus 2.
unfold fn_funsig in H18.
rewrite H18 in TC5. simpl in TC5.
assert (fn_return f = Tvoid). {
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. repeat rewrite <- sepcon_assoc in H.
 destruct H as [? [? [? [_ ?]]]]. destruct (fn_return f); try contradiction H1. auto.
}
specialize (TC5 H28).
apply step_return with f ret Vundef (tx); simpl; auto.
unfold te2.
rewrite TC5. split; auto.
assert (typecheck_val v (fn_return f) = true).
 clear - H22; unfold bind_ret in H22; normalize in H22; try contradiction; auto.
 destruct H22. destruct H. rewrite tc_val_eq in H; apply H.
simpl.
unfold rval.
destruct ret.
apply step_return with (zap_fn_return f) None Vundef (PTree.set i v tx); simpl; auto.
apply step_return with f None Vundef tx; simpl; auto.
split; [ | rewrite <- H25; apply age_level; auto]. {
 rewrite (age_jm_dry H26) in FL2.
 clear FL3 H1.
 apply resource_decay_trans with (nextblock (m_dry jm')) (m_phi jm2).
 apply Pos.le_refl.
 eapply free_list_resource_decay; eauto.
 replace (nextblock (m_dry jm')) with (nextblock (m_dry jm2)).
 apply age1_resource_decay; auto.
 symmetry.
 rewrite (age_jm_dry H26).
 clear - FL2.
 forget (m_dry jm') as m.
 revert m FL2; induction (blocks_of_env ve); intros.
 simpl in FL2. inv FL2; auto.
 simpl in FL2. destruct a as [[b lo] hi].
 destruct (free m b lo hi) eqn:?; inv FL2.
 rewrite <- (IHl _ H0).
 apply nextblock_free in Heqo; auto.
}
}
(* END OF  "spec H19" *)

destruct (can_alloc_variables' jm (fn_vars f)) as [ve' [jm' [? ?]]].
change (level jm) with (level (m_phi jm)). rewrite H2.
clear; omega.
rewrite <- and_assoc in H20.
destruct H20 as [H20 CORE].
rewrite <- Genv.find_funct_find_funct_ptr in H16.
destruct (build_call_temp_env f (eval_exprlist (snd (split (fst fsig))) bl rho))
as [te' ?]; auto.
(*look here*)
simpl in TC2. 
apply tc_exprlist_length in TC2.  
clear - H18 TC2. 
unfold fn_funsig in *; subst; simpl in *.
revert bl TC2; induction (fn_params f); destruct bl; intros; auto.  
simpl in TC2. destruct a. destruct (split l). inv TC2.
simpl in *.  
destruct a. simpl.
destruct (split l); simpl in *. unfold_lift; simpl. f_equal; auto.  
exists (State ve' te' (Kseq f.(fn_body) :: Kseq (Sreturn None) 
                                     :: Kcall ret f (vx) (tx) :: k)).
exists  jm'.
split.
split; auto.
eapply step_call_internal with (vargs:=eval_exprlist (snd (split (fst fsig))) bl rho); eauto. 
rewrite <- H3.  
eapply eval_expr_relate; try solve[rewrite H0; auto]; auto. destruct TC3; eassumption. auto.
destruct (fsig). unfold fn_funsig in *. inv H18.
eapply exprlist_eval; try eassumption; auto.
 apply TC2. destruct TC3 ; auto.
unfold type_of_function. destruct fsig; inv H18; auto. 

assert (n >= level jm')%nat.
clear - H2 H20. destruct H20 as [_ ?].
change (level (m_phi jm)) with (level jm) in H2.
omega.
pose (rho3 := mkEnviron (ge_of rho) (make_venv ve') (make_tenv te')).
assert (app_pred (funassert Delta rho3) (m_phi jm')).
apply (resource_decay_funassert _ _ (nextblock (m_dry jm)) _ (m_phi jm')) in H4.
2: apply laterR_necR; apply age_laterR; auto.
unfold rho3; clear rho3.
apply H4.
destruct H20; auto.
specialize (H19 te' ve' _ H22 _ (necR_refl _)).
spec H19; [clear H19|].
split; [split|]; auto. Focus 3. 
unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23.
simpl ge_of in H23. auto. 
split.
Focus 2. simpl.
split; [ | reflexivity].
clear - H15.
admit.   (* looks good *)
hnf. unfold func_tycontext'.
unfold construct_rho.  
clear - H0 TC2 TC3 H18 H16 H21 H15 H23 H17 H17'. 
unfold rho3 in *. simpl in *. destruct H23. 
destruct rho. inv H0. simpl in *. 
remember (split (fn_params f)). destruct p.
assert (TE := TC3). 
 destruct TC3 as [TC3 TC3'].
destruct TC3 as [TC3 [TC4 [TC5 TC6]]]. 
simpl in *. if_tac in H16; try congruence. clear H0. 

eapply semax_call_typecheck_environ; try eassumption.
destruct TE; intros; auto.

normalize.
split; auto. unfold rho3 in H23. unfold construct_rho. rewrite H0 in H23. 
simpl ge_of in H23. auto. 
unfold bind_args.
unfold tc_formals.
normalize.
rewrite <- sepcon_assoc.
normalize.
split.
hnf.
clear - TC2 H21 H17.
admit.  (* should be easy *)
admit.  (* plausible?  *)
(* end   "spec H19" *)

specialize (H19 ora jm').
apply age_level in H13.
destruct H20.
change (level jm = S n) in H2. rewrite H2 in H24; inversion H24. subst n.
auto.

Qed.

Lemma func_at_func_at':
 forall fs loc, func_at fs loc |-- func_at' fs loc.
Proof.
unfold func_at, func_at'; destruct fs; intros. hnf; intros.
eexists; eauto.
Qed.

Lemma semax_call: 
    forall Delta A (P Q: A -> assert) x F ret argsig retsig a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig -> 
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax Espec Delta
       (fun rho =>  tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho  && 
           (fun_assert  (argsig,retsig) A P Q (eval_expr a rho) && 
          (F rho * P x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho ))))
         (Scall ret a bl)
         (normal_ret_assert 
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q x) retsig ret rho))).
Proof.
rewrite semax_unfold.  intros ? ? ? ? ? ? ? ? ? ? ? TCF TC5 TC7.
intros.
rename H0 into H1.
intros tx vx.
intros ? ? ? ? [[TC3 ?] ?].
assert (H0': necR w (level a')).
apply nec_nat. apply necR_level in H2. apply le_trans with (level y); auto.
eapply pred_nec_hereditary in H1; [ | apply H0'].
eapply pred_nec_hereditary in Prog_OK; [ | apply H0'].
clear w H0' H0 y H2.
rename a' into w.
intros ora jm _ ?.
subst w.
apply extend_sepcon_andp in H3; auto.
destruct H3 as [H2 H3].
normalize in H3. unfold fun_assert in *. unfold res_predicates.fun_assert in *. 
destruct H3 as [[b [i [H3 H6]]] H5].
specialize (H6 (b, Int.unsigned i)).
rewrite jam_true in H6 by auto.
hnf in H3.
generalize H4; intros [_ H7].
specialize (H7 (b, Int.unsigned i) (mk_funspec (argsig,retsig) A P Q) _ (necR_refl _)).
spec H7.
apply func_at_func_at'; apply H6.
destruct H7 as [id [v [[H7 H8] H9]]].
hnf in H9.
simpl in H8. unfold val2adr in H8. destruct v; try contradiction.
symmetry in H8; inv H8.
rename H11 into H12.
destruct H2 as [TC1 TC2].
generalize H9; intros [fs H8].
generalize H4; intros [H10 _].
specialize (H10 id fs _ (necR_refl _) H8).
destruct H10 as [v' [b' [[H10] H13]]].
assert (H11: filter_genv psi = ge_of (construct_rho (filter_genv psi) vx tx)) by reflexivity.
simpl in H10. simpl in H7. inversion2 H7 H10.
simpl in H0. subst b'.
unfold func_at in H13.
rewrite H12 in H13.
destruct fs as [fsig' A' P' Q'].
assert (fsig' = (argsig,retsig)).
 clear - H6 H13.
 unfold pureat in *. simpl in *. inversion2 H6 H13. auto.
clear H15; subst fsig'.
hnf in H6,H13.
rewrite H6  in H13.
inversion H13; clear H13.
subst A'.
apply inj_pair2 in H10. rename H10 into H15.
clear H6; pose (H6:=True).
clear H9; pose (H9:=True).

unfold filter_genv in H7.
invSome.
assert (b0=b/\ i=i0).
 destruct (type_of_global psi b0); inv H10; split; auto.
 rewrite Int.signed_zero in H12. 
 pose proof (Int.repr_unsigned i). rewrite <- H12 in H0. subst; reflexivity.
destruct H0; subst b0 i.
clear H11. pose (H16:=True).
clear H12; pose (H12:=True).
remember (construct_rho (filter_genv psi) vx tx) as rho.
set (args := eval_exprlist (snd (split argsig)) bl rho).
fold args in H5.
rename H10 into H10'.
destruct (function_pointer_aux A P P' Q Q' (m_phi jm)) as [H10 H11].
f_equal; auto.
clear H15.
specialize (H10 x (make_args (map (@fst  _ _) argsig) (eval_exprlist (snd (split argsig))bl rho) rho)).
specialize (H11 x).
rewrite <- sepcon_assoc in H5.
assert (H14: app_pred (|> (F0 rho * F rho * P' x (make_args (map (@fst  _ _) argsig)
  (eval_exprlist (snd (split argsig)) bl rho) rho))) (m_phi jm)).
do 3 red in H10.
apply eqp_later1 in H10.
rewrite later_sepcon.
apply pred_eq_e2 in H10.
eapply (sepcon_subp' (|>(F0 rho * F rho)) _ (|> P x (make_args (map (@fst  _ _) argsig) (eval_exprlist (snd (split argsig)) bl rho) rho)) _ (level (m_phi jm))); eauto.
rewrite <- later_sepcon. apply now_later; auto.  
apply (tc_exprlist_sub _ _ TS) in TC2.
apply (tc_expr_sub _ _ TS) in TC1.
assert (TC7': tc_fn_return Delta' ret retsig).
clear - TC7 TS.
hnf in TC7|-*. destruct ret; auto.
destruct ((temp_types Delta) ! i) eqn:?; try contradiction.
destruct TS.
specialize (H i); rewrite Heqo in H. destruct p. subst t.
destruct ((temp_types Delta') ! i ). destruct p.
destruct H; auto.
auto.
clear Delta TS TC7. rename Delta' into Delta.
eapply semax_call_aux; try eassumption; 
 try solve [simpl; assumption].
unfold normal_ret_assert.
extensionality rho'.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
auto.
rewrite H3; f_equal.
clear - H10'. destruct (type_of_global psi b); inv H10'; auto.
Qed.

(*
Definition funspec_checkargs (f: funspec) (ty: type) (ret: option ident) :=
 match f, ty, ret with
 | mk_funspec (argsig,retsig) _ _ _, Tpointer (Tfunction args Tvoid) _,  None =>
         (args,Tvoid) = (type_of_params argsig, retsig)
 | mk_funspec (argsig,retsig) _ _ _, Tpointer (Tfunction args res) _, (Some _) =>
        (args,res) = (type_of_params argsig, retsig)
 | mk_funspec (argsig,retsig) _ _ _, Tfunction args Tvoid, None =>
         (args,Tvoid) = (type_of_params argsig, retsig)
 | mk_funspec (argsig,retsig) _ _ _, Tfunction args res, (Some t) =>
        (args,res) = (type_of_params argsig, retsig)
 | _, _, _ => False
 end.

Definition funspec_paramtypes (f: funspec) := 
 match f with mk_funspec (argsig,_) _ _ _ => type_of_params argsig end.
*)

Lemma semax_call_alt: 
    forall Delta A (P Q: A -> assert) x F ret argsig retsig a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig -> 
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax Espec Delta
       (fun rho =>  tc_expr Delta a rho && tc_exprlist Delta (snd (split argsig)) bl rho  && 
           (func_ptr (mk_funspec (argsig,retsig) A P Q) (eval_expr a rho) && 
          (F rho * P x (make_args (map (@fst  _ _) argsig)
                (eval_exprlist (snd (split argsig)) bl rho) rho ))))
         (Scall ret a bl)
         (normal_ret_assert 
          (fun rho => (EX old:val, substopt ret old F rho * maybe_retval (Q x) retsig ret rho))).
Proof. exact semax_call. Qed.

Lemma semax_call_ext:
     forall Delta P Q ret a tl bl a' bl',
      typeof a = typeof a' ->
      (forall rho, 
          !! (typecheck_environ Delta rho) && P rho |-- !! (eval_expr a rho = eval_expr a' rho /\
                                           eval_exprlist tl bl rho = eval_exprlist tl bl'  rho )) ->
  semax Espec Delta P (Scall ret a bl) Q ->
  semax Espec  Delta P (Scall ret a' bl') Q.
Proof.
intros.
rewrite semax_unfold in H1|-*.
rename H1 into H2. pose proof I.
intros.
specialize (H2 psi Delta' w TS Prog_OK k F H3 H4).
intros tx vx; specialize (H2 tx vx).
intros ? ? ? ? ?.
specialize (H2 y H5 a'0 H6 H7).
destruct H7 as [[? ?] _].
hnf in H7.
pose proof I.
hnf in H2|-*; intros.
specialize (H2 ora jm H10).
eapply convergent_controls_safe; try apply H2.
reflexivity.
simpl; intros ? ?. unfold cl_after_external. destruct ret0; auto.
reflexivity.
intros.
destruct H8 as [w1 [w2 [_ [_ ?]]]].
remember (construct_rho (filter_genv psi) vx tx) as rho.
assert (H7': typecheck_environ Delta rho).
destruct H7; eapply typecheck_environ_sub; eauto.
specialize (H0 rho w2 (conj H7' H8)).
destruct H0.
assert (forall vf, Clight.eval_expr psi vx tx (m_dry jm) a vf
               -> Clight.eval_expr psi vx tx (m_dry jm) a' vf).
clear - H H0 H1 H7 H9 .
admit.  (* typechecking proof, without typechecking on a we can't do relate
                               Also need uniqueness proof for eval_expr *) 
assert (forall tyargs vargs, 
             Clight.eval_exprlist psi vx tx (m_dry jm) bl tyargs vargs ->
             Clight.eval_exprlist psi vx tx (m_dry jm) bl' tyargs vargs).
clear - H12 H1 H7.
admit.  (* typechecking proof, same difficulties as above *) 
destruct H12; split; auto.
inv H12; [eapply step_call_internal | eapply step_call_external ]; eauto.
rewrite <- H; auto.
rewrite <- H; auto.
auto.
Qed.

Lemma call_cont_idem: forall k, call_cont (call_cont k) = call_cont k.
Proof.
induction k; intros.
reflexivity.
destruct a; simpl; auto.
Qed.

Definition cast_expropt (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr (Ecast e' t))  | None => `None end.

Lemma call_cont_current_function:
  forall {k i f e t l}, call_cont k = Kcall i f e t :: l -> current_function k = Some f.
Proof. intros. induction k; try destruct a; simpl in *; inv H; auto.
Qed.

Definition tc_expropt Delta (e: option expr) (t: type) : environ -> Prop :=
   match e with None => `(t=Tvoid)
                     | Some e' => denote_tc_assert (typecheck_expr Delta (Ecast e' t))
   end.
 
Lemma  semax_return :
   forall Delta R ret,
      semax Espec Delta 
                (fun rho => !! tc_expropt Delta ret (ret_type Delta) rho && 
                             R EK_return (cast_expropt ret (ret_type Delta) rho) rho)
                (Sreturn ret)
                R.
Proof.
intros.
hnf; intros.
rewrite semax_fold_unfold.
intros psi Delta'.
apply prop_imp_i. intro TS.
replace (ret_type Delta) with (ret_type Delta') 
 by (destruct TS as [_ [_ [? _]]]; auto).
apply derives_imp.
clear n.
intros w ? k F.
intros w' ? ?.
clear H.
clear w H0.
rename w' into w.
destruct H1.
do 3 red in H.
intros te ve.
intros n ? w' ? ?.
assert (necR w (level w')).
apply nec_nat.
apply necR_level in H2.
apply le_trans with (level n); auto.
apply (pred_nec_hereditary _ _ _ H4) in H0.
clear w n H2 H1 H4.
destruct H3 as [[H3 ?] ?].
pose proof I. 
remember ((construct_rho (filter_genv psi) ve te)) as rho.
assert (H1': ((F rho * R EK_return (cast_expropt ret (ret_type Delta') rho) rho))%pred w').
eapply sepcon_derives; try apply H1; auto.
apply andp_left2; auto.
assert (TC: forall w, (!! tc_expropt Delta ret (ret_type Delta') rho) w).
clear - H1. destruct H1 as [w1 [w2 [? [? [? ?]]]]]. intros. 
 destruct ret; apply H1.
clear H1; rename H1' into H1.
specialize (H0 EK_return (cast_expropt ret (ret_type Delta') rho) te ve).
specialize (H0 _ (le_refl _) _ (necR_refl _)).
spec H0.
rewrite <- Heqrho.
unfold frame_ret_assert.
split; auto.
split; auto.
rewrite sepcon_comm; auto.
intros ? ? ? ?.
specialize (H0 ora jm (eq_refl _) H6).
eapply convergent_controls_safe; try apply H0.
simpl; auto.
intros ? ?; simpl.
unfold cl_after_external.
auto.
simpl; auto.
intros.
simpl in H7.
destruct H7; split; auto.
revert H7; simpl.
destruct ret; specialize (TC jm);
   unfold tc_expropt in TC; do 3 red in TC; unfold_lift in TC; red in TC.
simpl.
unfold_lift.
case_eq (call_cont k); intros.
inv H9.
inv H14.
destruct c.
elimtype False; clear - H7.
 revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
elimtype False; clear - H7.
 revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
elimtype False; clear - H7.
 revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
elimtype False; clear - H7.
 revert l H7; induction k; try destruct a; simpl; intros; try discriminate; eauto.
destruct l0.
clear H0 H2 H8.
inv H9. fold denote_tc_assert in TC.
inv H11.
destruct H17.
econstructor; try eassumption; simpl.
2: split; [congruence | eassumption].
exists (eval_expr e (construct_rho (filter_genv psi) ve te)).
assert (TCe: denote_tc_assert (typecheck_expr Delta' e)  (construct_rho (filter_genv psi) ve te)).
eapply tc_expr_sub; try apply TS. instantiate (1:=m_phi jm).
hnf.
simpl in *. 
 repeat (rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
destruct TC; auto.
split.
apply eval_expr_relate with (Delta := Delta'); auto.
destruct H3; auto.
destruct H3.
simpl in H6; rewrite (call_cont_current_function H7) in H6.
destruct H6 as [_ ?].
rewrite H6.
super_unfold_lift.
rewrite cop2_sem_cast.
apply cast_exists with Delta'; auto.

auto.
rewrite <- H6.
simpl in TC. 
 repeat (rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
destruct TC; auto.

fold denote_tc_assert in TC.
inv H9.
symmetry in H14; inv H14.
destruct H20.
subst te''. clear H6.
econstructor; try eassumption.
exists (eval_expr e (construct_rho (filter_genv psi) ve te)).
assert (TCe: denote_tc_assert (typecheck_expr Delta' e)  (construct_rho (filter_genv psi) ve te)).
eapply tc_expr_sub; try apply TS. instantiate (1:=m_phi jm).
hnf.
simpl in *. 
 repeat (rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
destruct TC; auto.
split.
apply eval_expr_relate with (Delta := Delta'); auto.
destruct H3; auto.
rewrite cop2_sem_cast.
apply cast_exists with Delta'; auto.
destruct H3; auto.
destruct H3. simpl in H6.
rewrite (call_cont_current_function H7) in H6.
destruct H6 as [_ H6]; rewrite <- H6.
clear - TC.
simpl in TC.
rewrite denote_tc_assert_andp in TC; destruct TC; auto.
simpl. auto.

intro.
inv H7.
rewrite call_cont_idem in H13; auto.
econstructor; try eassumption.
auto.
Qed.
 
End extensions.
