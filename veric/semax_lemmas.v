Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.own.

Import Ctypes.

Local Open Scope pred.

#[export] Hint Resolve now_later andp_derives sepcon_derives : core.

Lemma no_dups_swap:
  forall F V a b c, @no_dups F V (a++b) c -> @no_dups F V (b++a) c.
Proof.
unfold no_dups; intros.
rewrite map_app in *.
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
rewrite in_app in *.
tauto.
Qed.

Lemma join_sub_share_top: forall sh, join_sub Share.top sh -> sh = Share.top.
Proof.
intros.
generalize (top_correct' sh); intro.
apply join_sub_antisym; auto.
Qed.


Lemma opt2list2opt: forall {A:Type} (l: option A), list2opt (opt2list l) = l.
destruct l; auto.
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

Section SemaxContext.

Lemma universal_imp_unfold {A} {agA: ageable A}:
   forall B (P Q: B -> pred A) w,
     (ALL psi : B, P psi --> Q psi) w = (forall psi : B, (P psi --> Q psi) w).
Proof.
intros.
apply prop_ext; split; intros.
eapply H; eauto.
intro b; apply H.
Qed.

Lemma guard_environ_put_te':
 forall ge te ve Delta id v k,
 guard_environ Delta k (mkEnviron ge ve te)  ->
    (forall t,
        (temp_types Delta) ! id = Some t -> tc_val' t v) ->
 guard_environ Delta k (mkEnviron ge ve (Map.set id v te)).
Proof.
 intros.
 destruct H; split.
 apply typecheck_environ_put_te; auto.
 destruct k; auto.
Qed.

Lemma prop_imp_derives {A}{agA: ageable A}:
  forall (P: Prop) (Q Q': pred A),  (P -> Q |-- Q') -> !!P --> Q |-- !!P --> Q'.
Proof.
 intros.
 repeat intro.
 apply H; auto.
Qed.

Lemma prop_imp {A}{agA: ageable A}:
  forall (P: Prop) (Q Q': pred A),  (P -> Q = Q') -> !!P --> Q = !!P --> Q'.
Proof.
  intros.
  apply pred_ext; apply prop_imp_derives.
  + intros; rewrite H by auto; auto.
  + intros; rewrite H by auto; auto.
Qed.

Lemma age_laterR {A} `{ageable A}: forall {x y}, age x y -> laterR x y.
Proof.
intros. constructor 1; auto.
Qed.
Local Hint Resolve age_laterR : core.

Lemma typecheck_environ_sub:
  forall Delta Delta', tycontext_sub Delta Delta' ->
   forall rho,
   typecheck_environ Delta' rho -> typecheck_environ Delta rho.
Proof.
intros ? ? [? [? [? [? Hs]]]] ?  [? [? ?]].
split; [ | split].
* clear - H H3.
 hnf; intros.
 specialize (H id); rewrite H0 in H.
 destruct ((temp_types Delta') ! id) eqn:?H; try contradiction.
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

Lemma funassert_resource: forall Delta rho a a' (Hl: level a = level a')
  (Hr: resource_at a = resource_at a'),
  funassert Delta rho a -> funassert Delta rho a'.
Proof.
  intros.
  destruct H as [H1 H2]; split; repeat intro. (*rename H into H1; repeat intro.*)
  - destruct (H1 _ _ _ (rt_refl _ _ _) H0) as (b1 & ? & ?).
    exists b1; split; auto.
    destruct b0; simpl in *.
    rewrite Hr in H4.
    pose proof (necR_level _ _ H).
    eapply necR_PURE in H; eauto.
    rewrite H; simpl; f_equal; f_equal.
    extensionality i a0 a1 a2.
    match goal with |-context[compcert_rmaps.R.approx ?a (approx ?b ?c)] =>
      change (compcert_rmaps.R.approx a (approx b c)) with ((approx a oo approx b) c) end.
    rewrite fmap_app, approx_oo_approx', approx'_oo_approx by lia; auto.
  - specialize (H2 b b0 b1). clear H1.
    destruct b0; simpl in *.
    apply (H2 _  (rt_refl _ _ _)).
    rewrite Hr, Hl.
    destruct H0 as [p Hp].
    pose proof (necR_level _ _ H).
    rewrite <- resource_at_approx.
    eapply necR_PURE' in H as [? ->]; simpl; eauto.
Qed.

Lemma cl_corestep_fun: forall ge m q m1 q1 m2 q2,
    cl_step ge q m q1 m1 ->
    cl_step ge q m q2 m2 ->
    (q1,m1)=(q2,m2).
Proof.
intros.
inv H; inv H0; repeat fun_tac; auto;
repeat match goal with H: _ = _ \/ _ = _ |- _ => destruct H; try discriminate end;
try contradiction.
-
inversion2 H1 H16; fun_tac; auto.
-
rewrite andb_true_iff in H15; destruct H15.
pose proof (ef_deterministic_fun _ H0 _ _ _ _ _ _ _ _ _ H3 H17).
inv H4; auto.
-
inv H1. inv H8.
fun_tac.
pose proof (alloc_variables_fun H3 H7). inv H8. auto.
-
rewrite andb_true_iff in H1; destruct H1.
pose proof (ef_deterministic_fun _ H0 _ _ _ _ _ _ _ _ _ H2 H13).
inv H1; auto.
Qed.

Lemma age1_resource_decay:
  forall jm jm', age jm jm' -> resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
 intros. split.
 apply age_level in H.
 change (level (m_phi jm)) with (level jm).
 change (level (m_phi jm')) with (level jm').
 lia.
 intro l. split. apply juicy_mem_alloc_cohere. left.
 symmetry; apply age1_resource_at with (m_phi jm); eauto.
  destruct (age1_juicy_mem_unpack _ _ H); auto.
 symmetry; apply resource_at_approx.
Qed.

Lemma jsafeN_local_step:
  forall {Espec: OracleKind} ge ora s1 m s2,
  cl_step  ge s1 (m_dry m) s2 (m_dry m) ->
  (forall m', age m m' -> 
    jsafeN (@OK_spec Espec) ge (level m') ora s2 m') ->
  jsafeN (@OK_spec Espec) ge (level m) ora s1 m.
Proof.
intros.
  rename H into Hstep.
  remember (level m) as N.
  destruct N; [constructor|].
  case_eq (age1 m); [intros m' H |  intro; apply age1_level0 in H; lia].
  eapply jsafeN_step with
    (m'0 := m').
  split3.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  apply Hstep.
  apply age1_resource_decay; auto. split; [apply age_level; auto|].
  apply age_jm_phi in H.
  erewrite (age1_ghost_of _ _ H) by (symmetry; apply ghost_of_approx).
  unfold level at 1; simpl.
  repeat intro; auto.
  assert (N = level m')%nat.
  apply age_level in H; lia.
  apply jm_bupd_intro.
  subst. apply H0. auto.
Qed.

Lemma derives_skip:
  forall {CS: compspecs} {Espec: OracleKind} p Delta (R: ret_assert),
      (forall rho, p rho |-- proj_ret_assert R EK_normal None rho) ->
        semax Espec Delta p Clight.Sskip R.
Proof.
intros ? ? ? ?; intros.
intros n.
rewrite semax_fold_unfold.
intros psi Delta' CS'.
apply prop_imp_i; intros [? HGG].
clear H0 Delta. rename Delta' into Delta.
intros ?w _ _. clear n.
intros k F f.
intros ?w _ ?.
clear w. rename w0 into n.
intros te ve w ?.
destruct H0 as [H0' H0].
specialize (H0 EK_normal None te ve w H1).
simpl exit_cont in H0.
simpl in H0'. clear n H1. remember ((construct_rho (filter_genv psi) ve te)) as rho.
revert w H0.
apply imp_derives; auto.
apply andp_derives; auto.
apply andp_derives; auto.
repeat intro.
simpl.
split; auto.
specialize (H rho). destruct R; simpl in H. simpl tycontext.RA_normal.
rewrite prop_true_andp in H by auto.
rewrite sepcon_comm.
eapply sepcon_derives; try apply H0; auto.

repeat intro.
destruct (H0 _ H1) as (b & ? & m' & ? & ? & ? & HP); clear H0.
exists b; split; auto; exists m'; repeat split; auto.
simpl.
intros ? ? ? ? ? ?.
specialize (HP ora jm H0 H6 H7 LW).
simpl in HP.
rewrite <- H7 in HP|-*.
change (level (m_phi jm)) with (level jm) in HP|-*.
destruct k as [ | s ctl' | | | |]; try contradiction; auto.
-
inv HP; try contradiction.
change (level jm) with (level (m_phi jm)); rewrite <- H9.
constructor.
change (level jm) with (level (m_phi jm)); rewrite <- H8.
eapply jsafeN_step; eauto.
destruct H9; split; auto.
inv H5.
econstructor; eauto.
simpl. auto.
inv H9.
-
eapply jsafeN_local_step. constructor.
intros.
eapply age_safe in HP; try apply H8.
auto.
-
eapply jsafeN_local_step. constructor.
intros.
eapply age_safe in HP; try apply H8.
auto.
-
inv HP; try contradiction.
change (level jm) with (level (m_phi jm)); rewrite <- H9.
constructor.
change (level jm) with (level (m_phi jm)); rewrite <- H8.
eapply jsafeN_step; eauto.
destruct H9; split; auto.
inv H5.
econstructor; eauto.
simpl. auto.
inv H9.
Qed.

Lemma semax_unfold {CS: compspecs} {Espec: OracleKind}:
  semax Espec = fun Delta P c R =>
    forall (psi: Clight.genv) Delta' CS' (w: nat)
          (TS: tycontext_sub Delta Delta')
          (HGG: cenv_sub (@cenv_cs CS) (@cenv_cs CS') /\ cenv_sub (@cenv_cs CS') (genv_cenv psi))
           (Prog_OK: @believe CS' Espec Delta' psi Delta' w) (k: cont) (F: assert) f,
        closed_wrt_modvars c F ->
       rguard Espec psi Delta' f (frame_ret_assert R F) k w ->
       guard Espec psi Delta' f (fun rho => F rho * P rho) (Kseq c k) w.
Proof.
unfold semax; rewrite semax_fold_unfold.
extensionality Delta P c R.
apply prop_ext; split; intros.
+ eapply (H w); eauto.
  - split; auto. 
  - split; trivial.
+ intros psi Delta' CS'.
  apply prop_imp_i; intros [? HGG].
  intros w' ? ? k F f w'' ? [? ?].
  apply (H psi Delta' CS' w'' H0 HGG); trivial. 
  eapply pred_nec_hereditary; eauto.
Qed.

Fixpoint list_drop (A: Type) (n: nat) (l: list A) {struct n} : list A :=
  match n with O => l | S i => match l with nil => nil | _ :: l' => list_drop A i l' end end.
Arguments list_drop [A] _ _.

Definition straightline (c: Clight.statement) :=
 forall ge f ve te k m f' ve' te' c' k' m',
        cl_step ge (State f c k ve te) m (State f' c' k' ve' te') m' ->  (c'=Sskip /\ k=k').

Lemma straightline_assign: forall e0 e, straightline (Clight.Sassign e0 e).
Proof.
unfold straightline; intros.
inv H; auto.
destruct H13; inv H; auto.
destruct H13; inv H; auto.
Qed.

Lemma extract_exists_pre_later {CS: compspecs} {Espec: OracleKind}:
  forall  (A : Type) (Q: assert) (P : A -> assert) c Delta (R: ret_assert),
  (forall x, semax Espec Delta (fun rho => Q rho && |> P x rho) c R) ->
   semax Espec Delta (fun rho => Q rho && |> exp (fun x => P x rho)) c R.
Proof.
rewrite semax_unfold in *.
intros.
intros.
intros te ve ?w ? ?w ? ?.
destruct H4.
destruct H4.
destruct H6 as [w2 [w3 [? [? [HQ ?]]]]].
destruct (age1 w2) as [w2' | ] eqn:?.
*
destruct (@age1_join _ _ _ _ _ _ _ _ H6 Heqo)
  as [w3' [w1' [? [? ?]]]].
hnf in H8.
specialize (H8 _ (age_laterR H10)).
destruct H8 as [x H8].
specialize (H x psi Delta' CS' w TS HGG Prog_OK k F f H0 H1).
unfold guard, _guard in H.
specialize (H te ve).
cbv beta in H.
specialize (H w0 H2 w1 H3).
apply H.
split; auto. split; auto.
exists w2, w3. split3; auto.
split; auto.
intros w3x ?.
eapply pred_nec_hereditary; [ | apply H8].
clear - H10 H12.
eapply age_later_nec; eauto.
*
assert (level w1 = O). {
  clear - H6 Heqo.
  apply join_level in H6. destruct H6.
  rewrite <- H. apply age1_level0.  auto.
}
hnf.
intros.
eexists; split.
apply H10.
exists w1.
split3; auto. split; auto.
simpl.
hnf; intros.
rewrite H9.
constructor.
Qed.

Lemma extract_exists_pre {CS: compspecs} {Espec: OracleKind}:
  forall  (A : Type) (P : A -> assert) c Delta (R: ret_assert),
  (forall x, semax Espec Delta (P x) c R) ->
   semax Espec Delta (fun rho => exp (fun x => P x rho)) c R.
Proof.
rewrite semax_unfold in *.
intros.
intros.
intros te ve ?w ? ?w ? ?.
rewrite exp_sepcon2 in H4.
destruct H4 as [[TC [x H5]] ?].
specialize (H x).
specialize (H psi Delta' CS' w TS HGG Prog_OK k F f H0).
spec H. {
 clear - H1.
 unfold rguard in *.
 intros ek vl tx vx. specialize (H1 ek vl tx vx).
 red in H1.
 eapply subp_trans'; [| apply H1 ].
 apply derives_subp.
 apply andp_derives; auto.
}
eapply H; eauto.
split; auto.
split; auto.
Qed.

Definition G0: funspecs := nil.

Definition empty_genv prog_pub cenv: Clight.genv :=
   Build_genv (Genv.globalenv (AST.mkprogram (F:=Clight.fundef)(V:=type) nil prog_pub (1%positive))) cenv.

Lemma empty_program_ok {CS: compspecs} {Espec: OracleKind}: forall Delta ge w,
    glob_specs Delta = PTree.empty _ ->
    believe Espec Delta ge Delta w.
Proof.
intros Delta ge w ?.
intro b.
intros fsig cc A P Q.
intros ?n ? ?.
destruct H1 as [id [? [b0 [? ?]]]].
rewrite H in H1. rewrite PTree.gempty in H1.
inv H1.
Qed.

Definition all_assertions_computable  :=
  forall (Espec: OracleKind) psi f tx vx (Q: assert), 
     exists k,  assert_safe Espec psi f tx vx k = Q.
(* This is not generally true, but could be made true by adding an "assert" operator
  to the programming language
*)

Lemma ewand_TT_emp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
    ewand TT emp = emp.
Proof.
intros.
apply pred_ext; intros w ?.
destruct H as [w1 [w3 [? [? ?]]]].
hnf; eapply split_identity.
eapply join_comm; eauto.
auto.
exists w; exists w; split; auto.
change (identity w) in H.
apply identity_unit'; auto.
Qed.

Lemma subp_derives' {A}{agA: ageable A}:
  forall P Q: pred A, (forall n, (P >=> Q) n) -> P |-- Q.
Proof.
intros.
intros n ?. eapply H; eauto.
Qed.

Lemma guard_environ_sub:
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
Qed.

Lemma proj_frame_ret_assert:
 forall (R: ret_assert) (F: assert) ek vl,
  proj_ret_assert (frame_ret_assert R F) ek vl = 
  seplog.sepcon (proj_ret_assert R ek vl) F.
Proof.
intros; extensionality rho; destruct R, ek; simpl;
rewrite ?sepcon_andp_prop1; auto.
Qed.

Lemma semax_extensionality0 {CS: compspecs} {Espec: OracleKind}:
       TT |--
      ALL Delta:tycontext, ALL Delta':tycontext,
      ALL P:assert, ALL P':assert,
      ALL c: statement, ALL R:ret_assert, ALL R':ret_assert,
       ((!! tycontext_sub Delta Delta'
       &&  (ALL ek: exitkind, ALL  vl : option val, ALL rho: environ,  
               (proj_ret_assert R ek vl rho >=> proj_ret_assert R' ek vl rho))
      && (ALL rho:environ, P' rho >=> P rho)  && semax' Espec Delta P c R) >=> semax' Espec Delta' P' c R').
Proof.
apply loeb.
intros w ? Delta Delta' P P' c R R'.
intros w1 ? w2 ? [[[? ?] ?] ?].
do 3 red in H2.
rewrite semax_fold_unfold; rewrite semax_fold_unfold in H5.
intros gx Delta'' CS'.
apply prop_imp_i. intros [TS HGG].
intros w3 ? ?.
specialize (H5 gx Delta'' CS' _ (necR_refl _)
 (conj (tycontext_sub_trans _ _ _ H2 TS) HGG)
                  _ H6 H7).

intros k F f w4 Hw4 [? ?].
specialize (H5 k F f w4 Hw4).
assert ((rguard Espec gx Delta'' f (frame_ret_assert R F) k) w4).
do 9 intro.
apply (H9 b b0 b1 b2 y H10 a' H11).
destruct H12; split; auto; clear H13.
pose proof I.
destruct H12; split; auto.
rewrite proj_frame_ret_assert in H14|-*.
clear H12 H13.
revert a' H11 H14.
apply sepcon_subp' with (level w2).
apply H3.
auto.
apply necR_level in H6.
apply necR_level in Hw4.
eapply le_trans; try eassumption.
eapply le_trans; try eassumption.

specialize (H5 (conj H8 H10)). clear H8 H9 H10.
do 7 intro.
apply (H5 b b0 y H8 _ H9).
destruct H10; split; auto.
destruct H10; split; auto.
clear H10 H11.
revert a' H9 H12.
apply sepcon_subp' with (level w2); auto.
apply necR_level in H6.
apply necR_level in Hw4.
eapply le_trans; try eassumption.
eapply le_trans; try eassumption.
Qed.

Lemma semax_extensionality1 {CS: compspecs} {Espec: OracleKind}:
  forall Delta Delta' (P P': assert) c (R R': ret_assert) ,
       tycontext_sub Delta Delta' ->
       ((ALL ek: exitkind, ALL  vl : option val, ALL rho: environ,  
          (proj_ret_assert R ek vl rho >=> proj_ret_assert R' ek vl rho))
      && (ALL rho:environ, P' rho >=> P rho)  && (semax' Espec Delta P c R) |-- semax' Espec Delta' P' c R').
Proof.
intros.
intros n ?.
apply (semax_extensionality0 n I Delta Delta' P P' c R R' _ (le_refl _) _ (necR_refl _)).
destruct H0;
split; auto.
destruct H0;
split; auto.
split; auto.
Qed.

Lemma semax_frame {CS: compspecs} {Espec: OracleKind}:  forall Delta P s R F,
   closed_wrt_modvars s F ->
  semax Espec Delta P s R ->
    semax Espec Delta (fun rho => P rho * F rho) s (frame_ret_assert R F).
Proof.
intros until F. intros CL H.
rewrite semax_unfold.
rewrite semax_unfold in H.
intros.
pose (F0F := fun rho => F0 rho * F rho).
specialize (H psi Delta' CS' w TS HGG Prog_OK k F0F f).
spec H. {
 unfold F0F.
 clear - H0 CL.
 hnf in *; intros; simpl in *.
 rewrite <- CL. rewrite <- H0. auto.
 tauto. tauto.
}
replace (fun rho : environ => F0 rho * (P rho * F rho))
  with  (fun rho : environ => F0F rho * P rho).
*
apply H.
unfold F0F; clear - H1.
intros ek vl tx vx; specialize (H1 ek vl tx vx).
red in H1.
remember ((construct_rho (filter_genv psi) vx tx)) as rho.
red.
hnf; intros. specialize (H1 _ H).
hnf; intros. apply H1; auto.
destruct H2; split; auto. destruct H2; split; auto.
rewrite proj_frame_ret_assert in H4|-*.
rewrite proj_frame_ret_assert.
rewrite seplog.sepcon_assoc.
eapply sepcon_derives; try apply H4; auto. simpl.
rewrite sepcon_comm; auto.
*
unfold F0F.
extensionality rho.
rewrite sepcon_assoc.
f_equal. apply sepcon_comm.
Qed.

Lemma assert_safe_last:
  forall {Espec: OracleKind} f ge ve te c k rho w,
   (forall w', age w w' -> assert_safe Espec f ge ve te (Cont (Kseq c k)) rho w) ->
    assert_safe Espec f ge ve te (Cont (Kseq c k)) rho w.
Proof.
intros.
case_eq (age1 w). auto.
clear H.
intro; apply bupd_intro; repeat intro.
apply age1_level0 in H. lia. 
Qed.

Lemma pred_sub_later' {A} `{H: ageable A}:
  forall (P Q: pred A),
           (|> P >=> |> Q)  |--  (|> (P >=> Q)).
Proof.
intros.
rewrite later_fash; auto.
rewrite later_imp.
auto.
Qed.

Lemma later_strengthen_safe1:
  forall {Espec: OracleKind} (P: pred rmap) f ge ve te k rho,
              ((|> P) >=> assert_safe Espec f ge ve te k rho) |--   |>  (P >=> assert_safe Espec f ge ve te k rho).
Proof.
intros.
intros w ?.
apply (@pred_sub_later' _ _ P  (assert_safe Espec f ge ve te k rho)); auto.
eapply subp_trans'; try apply H.
apply derives_subp; clear.
apply now_later.
Qed.

End SemaxContext.

#[export] Hint Resolve age_laterR : core.

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

(*
(* BEGIN Lemmas duplicated from Clight_sim. v *)
Lemma dec_skip: forall s, {s=Sskip}+{s<>Sskip}.
Proof.
 destruct s; try (left; congruence); right; congruence.
Qed.

Lemma strip_step:  (* This one uses equality, one in Clight_sim uses <->  *)
  forall ge ve te k m st' m',
     cl_step ge (State ve te (strip_skip k)) m st' m' =
    cl_step ge (State ve te k) m st' m'.
Proof.
intros.
 apply prop_ext.
 induction k; intros; split; simpl; intros; try destruct IHk; auto.
 destruct a; try destruct s; auto.
  constructor; auto.
 destruct a; try destruct s; auto.
 inv H. auto.
Qed.
(* END lemmas duplicated *)

 Lemma strip_skip_app:
  forall k k', strip_skip k = nil -> strip_skip (k++k') = strip_skip k'.
Proof. induction k; intros; auto. destruct a; inv H. destruct s; inv H1; auto.
  simpl. apply IHk. auto.
Qed.

Lemma strip_strip: forall k, strip_skip (strip_skip k) = strip_skip k.
Proof.
induction k; simpl.
auto.
destruct a; simpl; auto.
destruct (dec_skip s).
subst; auto.
destruct s; auto.
Qed.

Lemma strip_skip_app_cons:
 forall {k c l}, strip_skip k = c::l -> forall k', strip_skip  (k++k') = c::l++k'.
Proof. intros. revert k H;  induction k; intros. inv H.
  destruct a; try solve [simpl in *; auto];
  try solve [simpl in *; rewrite cons_app'; rewrite H; auto].
 destruct (dec_skip s). subst. simpl in *; auto.
 destruct s; inv H; simpl; auto.
Qed.

Lemma filter_seq_current_function:
  forall ctl1 ctl2, filter_seq ctl1 = filter_seq ctl2 ->
       current_function ctl1 = current_function ctl2.
Proof.
  intros ? ? H0. revert ctl2 H0; induction ctl1; simpl; intros.
  revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
  destruct a; auto; revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
Qed.
*)

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

Lemma and_FF : forall {A} `{ageable A} (P:pred A),
  P && FF = FF.
Proof.
  intros. rewrite andp_comm. apply FF_and.
Qed.

Lemma sepcon_FF : forall {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A} (P:pred A),
  (P * FF = FF)%pred.
Proof.
  intros. rewrite sepcon_comm. apply FF_sepcon.
Qed.

Section extensions.

Lemma safe_loop_skip:
  forall {Espec: OracleKind}
    ge ora f ve te k m,
    jsafeN (@OK_spec Espec) ge (level m) ora
           (State f (Sloop Clight.Sskip Clight.Sskip) k ve te ) m.
Proof.
  intros.
  pose (M := level m).
  assert (Hge: (M >= level m)%nat) by lia.
  clearbody M.
  revert m Hge; induction M; intros.
  assert (level m = O) by lia. rewrite H.
  constructor.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply jsafeN_local_step. constructor. auto.
  intros.
  eapply jsafeN_local_step. constructor.
  intros.
  apply IHM.
  apply age_level in H. apply age_level in H0. apply age_level in H1. lia.
Qed.  

(*
Lemma safe_seq_skip {Espec: OracleKind} ge n ora ve te k m :
  jsafeN OK_spec ge n ora (State ve te k) m ->
  jsafeN OK_spec ge n ora (State ve te (Kseq Sskip :: k)) m.
Proof.
inversion 1; subst. constructor.
econstructor; eauto. simpl. destruct H0 as (?&?&?). split3; eauto.
eapply step_skip; eauto.
simpl in *; congruence.
contradiction.
Qed.

Lemma safe_seq_skip' {Espec: OracleKind} ge n ora ve te k m :
  jsafeN OK_spec ge n ora (State ve te (Kseq Sskip :: k)) m ->
  jsafeN OK_spec ge n ora (State ve te k) m.
Proof.
inversion 1; subst. constructor.
econstructor; eauto. simpl. destruct H0 as (?&?&?). split3; eauto.
inv H0; auto.
simpl in *; congruence.
contradiction.
Qed.
*)

Local Open Scope nat_scope.

Definition control_as_safex {Espec: OracleKind} ge c1 k1 c2 k2 :=
    forall (ora : OK_ty) f (ve : env) (te : temp_env) (m : juicy_mem),
        jsafeN (@OK_spec Espec) ge (level m) ora (State f c1 k1 ve te) m ->
          jsafeN (@OK_spec Espec) ge (level m) ora (State f c2 k2 ve te) m.

Definition control_as_safe {Espec: OracleKind} ge ctl1 ctl2 :=
 match ctl1, ctl2 with
 | Kseq c1 k1, Kseq c2 k2 =>
                   control_as_safex ge c1 k1 c2 k2
 | Kseq c1 k1, Kloop1 _ _ _ => 
                   control_as_safex ge c1 k1 Sskip ctl2
 | Kseq c1 k1, Kloop2 body incr k2 => 
                   control_as_safex ge c1 k1 (Sloop body incr) k2
 | Kseq c1 k1, Kstop => 
                   control_as_safex ge c1 k1 (Sreturn None) Kstop
 | Kseq c1 k1, Kcall _ _ _ _ _ => 
                   control_as_safex ge c1 k1 (Sreturn None) ctl2
 | Kseq _ _, _ => 
                   False
 | Kloop1 _ _ _, Kseq c2 k2 =>
                   control_as_safex ge Sskip ctl1 c2 k2
 | Kloop1 _ _ _, Kloop1 _ _ _ => 
                   control_as_safex ge Sskip ctl1 Sskip ctl2
 | Kloop1 _ _ _, Kloop2 body incr k2 => 
                   control_as_safex ge Sskip ctl1 (Sloop body incr) k2
 | Kloop1 _ _ _, _ => 
                   False
 | Kloop2 b1 i1 k1, Kseq c2 k2 =>
                   control_as_safex ge (Sloop b1 i1) k1 c2 k2
 | Kloop2 b1 i1 k1, Kloop1 _ _ _ =>
                   control_as_safex ge (Sloop b1 i1) k1 Sskip ctl2
 | Kloop2 b1 i1 k1, Kloop2 b2 i2 k2 =>
                   control_as_safex ge (Sloop b1 i1) k1 (Sloop b2 i2) k2
 | Kloop2 _ _ _, _ =>
                   False
 | Kstop, Kseq c2 k2 => 
                   control_as_safex ge (Sreturn None) Kstop c2 k2 
 | Kcall _ _ _ _ _, Kseq c2 k2=> 
                   control_as_safex ge (Sreturn None) ctl1 c2 k2 

  | _, _ => ctl1 = ctl2
   end.

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

Lemma guard_safe_adj {Espec: OracleKind}:
 forall
   psi Delta f P c1 k1 c2 k2,
  (forall ora m ve te n,
     jsafeN (@OK_spec Espec) psi n ora (State f c1 k1 ve te) m ->
     jsafeN (@OK_spec Espec) psi n ora (State f c2 k2 ve te) m) ->
  guard Espec psi Delta f P (Kseq c1 k1) |-- guard Espec psi Delta f P (Kseq c2 k2).
Proof.
intros.
unfold guard.
apply allp_derives. intros tx.
apply allp_derives. intros vx.
apply subp_derives; auto.
apply bupd_mono.
intros w ? ? ? ? .
simpl in H0.
specialize (H0 ora jm H1).
simpl.
intros.
apply H; auto.
Qed.

Lemma guard_safe_adj' {Espec: OracleKind}:
 forall
   psi Delta f P c1 k1 c2 k2,
  (forall ora m ve te,
     jsafeN (@OK_spec Espec) psi (level m) ora (State f c1 k1 ve te) m ->
     jsafeN (@OK_spec Espec) psi (level m) ora (State f c2 k2 ve te) m) ->
  guard Espec psi Delta f P (Kseq c1 k1) |-- guard Espec psi Delta f P (Kseq c2 k2).
Proof.
intros.
unfold guard.
apply allp_derives. intros tx.
apply allp_derives. intros vx.
apply subp_derives; auto.
apply bupd_mono.
simpl.
intros ? ? ? ? ? ? ? ?.
simpl in H0.
subst.
apply H; auto.
Qed.

Lemma assert_safe_adj:
  forall {Espec: OracleKind} ge f ve te k k' rho,
     control_as_safe ge k k' ->
     assert_safe Espec ge f ve te (Cont k) rho 
    |-- assert_safe Espec ge f ve te (Cont k') rho.
Proof.
 intros. apply bupd_mono.
 simpl in *.
 intros w ?. simpl in H0|-*.
 intros ? ?. specialize (H0 ora jm).
 intros. specialize (H0 H1 H2 H3 LW).
 simpl in H0.
 subst w. change (level (m_phi jm)) with (level jm).
 red in H.
 destruct k as [ | s ctl' | | | |] eqn:Hk; try contradiction;
 destruct k' as [ | s2 ctl2' | | | |] eqn:Hk'; try contradiction;
 try discriminate; auto;
 try solve [apply H; auto].
 inv H; auto.
Qed.

Lemma assert_safe_adj':
  forall {Espec: OracleKind} ge f ve te k k' rho P w,
      (control_as_safe ge k k') ->
     app_pred (P >=> assert_safe Espec ge f ve te (Cont k) rho) w ->
     app_pred (P >=> assert_safe Espec ge f ve te (Cont k') rho) w.
Proof.
 intros.
 eapply subp_trans'; [ | apply derives_subp; eapply assert_safe_adj; try eassumption; eauto].
 auto.
Qed.

Lemma assert_safe_last': forall {Espec: OracleKind} ge f ve te c k rho w,
            (age1 w <> None -> assert_safe Espec ge f ve te (Cont (Kseq c k)) rho w) ->
             assert_safe Espec ge f ve te (Cont (Kseq c k)) rho w.
Proof.
 intros. apply assert_safe_last; intros. apply H. rewrite H0. congruence.
Qed.

Lemma pjoinable_emp_None {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall w: option (psepalg.lifted JA), identity w ->  w=None.
Proof.
intros.
destruct w; auto.
elimtype False.
specialize (H None (Some l)).
spec H.
constructor.
inversion H.
Qed.

Lemma pjoinable_None_emp {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
           identity (None: option (psepalg.lifted JA)).
Proof.
intros; intro; intros.
inv H; auto.
Qed.

Lemma unage_mapsto:
  forall sh t v1 v2 w, age1 w <> None -> (|> mapsto sh t v1 v2) w -> mapsto sh t v1 v2 w.
Proof.
  intros.
  case_eq (age1 w); intros; try contradiction.
  clear H.
  specialize (H0 _ (age_laterR H1)).
  unfold mapsto in *.
  revert H0; case_eq (access_mode t); intros; auto.
  destruct (type_is_volatile t); try contradiction.
  destruct v1; try contradiction.
  rename H into Hmode.
  if_tac; rename H into H_READ.
  + destruct H0 as [H0|H0]; [left | right].
    destruct H0 as [H0' H0]; split; auto.
    destruct H0 as [bl [[] ?]]; exists bl; split; [split|]; auto.
    clear - H0 H1.
     intro loc'; specialize (H0 loc').
     hnf in *.
     if_tac.
     destruct H0 as [p ?]; exists p.
     hnf in *.
     rewrite preds_fmap_NoneP in *.
     apply (age1_YES w r); auto.
     unfold noat in *; simpl in *.
    apply <- (age1_resource_at_identity _ _ loc' H1); auto.
    eapply age1_ghost_of_identity; eauto.
    destruct H0 as [? [v2' [bl [[] ?]]]].
    hnf in H. subst v2. split; hnf; auto. exists v2', bl; split; [split|]; auto.
    clear - H2 H1; rename H2 into H0.
     intro loc'; specialize (H0 loc').
     hnf in *.
     if_tac.
     destruct H0 as [p ?]; exists p.
     hnf in *.
     rewrite preds_fmap_NoneP in *.
     apply (age1_YES w r); auto.
     unfold noat in *; simpl in *.
    apply <- (age1_resource_at_identity _ _ loc' H1); auto.
    eapply age1_ghost_of_identity; eauto.
  + split; [exact (proj1 H0) |].
    destruct H0 as [_ [? Hg]].
    split; [|eapply age1_ghost_of_identity; eauto].
    intro loc'; specialize (H loc').
    hnf in *.
    if_tac.
    - unfold shareat in *; simpl in *.
      pose proof H1.
      apply age1_resource_share with (l := loc') in H1.
      apply age1_nonlock with (l := loc') in H2.
      rewrite H1; tauto.
    - unfold noat in *; simpl in *.
      apply <- (age1_resource_at_identity _ _ loc' H1); auto.
Qed.

Lemma semax_Delta_subsumption {CS: compspecs} {Espec: OracleKind}:
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     semax Espec Delta P c R -> semax Espec Delta' P c R.
Proof.
intros.
unfold semax in *.
intros.
specialize (H0 n).
apply (semax_extensionality1 Delta Delta' P P c R R); auto.
split; auto.
split; auto.
intros ? ? ?; auto.
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
  Variable f3 : forall (o : option ident) (e : external_function) (t : typelist) (l : list expr), P (Sbuiltin o e t l).
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

Require Import VST.msl.eq_dec.

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
  Let eq_dec_option_ident := option_eq (ident_eq).
  Let eq_dec_option_Z : EqDec (option Z). repeat t. Defined.
  Let eq_dec_typelist : EqDec typelist. repeat t. Defined.

  Lemma eq_dec_expr : EqDec expr.
  Proof. repeat t. Defined.

  Let eq_dec_expr := eq_dec_expr.
  Let eq_dec_option_expr : EqDec (option expr). repeat t. Defined.
  Let eq_dec_list_expr : EqDec (list expr). repeat t. Defined.

  Local Ltac eq_dec a a' :=
    let H := fresh in
    assert (H : {a = a'} + {a <> a'}) by (auto; repeat (decide equality ; auto));
    destruct H; [subst; auto | try (right; congruence)].

  Lemma eq_dec_statement : forall s s' : statement, { s = s' } + { s <> s' }.
  Proof.
    apply
      (statement_rect
         (fun s => forall s', { s = s' } + { s <> s' })
         (fun l => forall l', { l = l' } + { l <> l' }));
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

Instance EqDec_statement: EqDec statement := eq_dec_statement.
Instance EqDec_external_function: EqDec external_function := eq_dec_external_function.

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
      destruct H2; [| rewrite <- H0 in *]; tauto.
    - change (mkEnviron (ge_of rho) (ve_of rho) te') with (mkEnviron (ge_of (mkEnviron (ge_of rho) (ve_of rho) te'')) (ve_of (mkEnviron (ge_of rho) (ve_of rho) te'')) te').
      change te'' with (te_of (mkEnviron (ge_of rho) (ve_of rho) te'')) in H3, H4, H2.
      forget (mkEnviron (ge_of rho) (ve_of rho) te'') as rho'.
      apply H0.
      clear H0 H1 H2 H3 H te''.
      intros.
      specialize (H4 i).
      destruct H4; [auto | right; congruence].
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
      destruct H2; [| rewrite <- H0 in *]; tauto.
    - change (mkEnviron (ge_of rho) (ve_of rho) te') with (mkEnviron (ge_of (mkEnviron (ge_of rho) (ve_of rho) te'')) (ve_of (mkEnviron (ge_of rho) (ve_of rho) te'')) te').
      change te'' with (te_of (mkEnviron (ge_of rho) (ve_of rho) te'')) in H3, H4, H2.
      forget (mkEnviron (ge_of rho) (ve_of rho) te'') as rho'.
      apply H0.
      clear H0 H1 H2 H3 H te''.
      intros.
      specialize (H4 i).
      destruct H4; [auto | right; congruence].
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
      destruct H2; [| rewrite <- H0 in *]; tauto.
    - change (mkEnviron (ge_of rho) (ve_of rho) te') with (mkEnviron (ge_of (mkEnviron (ge_of rho) (ve_of rho) te'')) (ve_of (mkEnviron (ge_of rho) (ve_of rho) te'')) te').
      change te'' with (te_of (mkEnviron (ge_of rho) (ve_of rho) te'')) in H3, H4, H2.
      forget (mkEnviron (ge_of rho) (ve_of rho) te'') as rho'.
      apply H0.
      clear H0 H1 H2 H3 H te''.
      intros.
      specialize (H4 i).
      destruct H4; [auto | right; congruence].
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

Lemma semax_eq:
 forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Espec Delta P c R = 
  (TT |-- (ALL psi : genv,
         ALL Delta' : tycontext, ALL CS':compspecs,
         !! (tycontext_sub Delta Delta' /\ cenv_sub (@cenv_cs CS) (@cenv_cs CS') /\
                                          cenv_sub (@cenv_cs CS') (genv_cenv psi)) -->
         @believe CS' Espec Delta' psi Delta' -->
         ALL k : cont ,
         ALL F : assert , ALL f: function,
         !! closed_wrt_modvars c F &&
         rguard Espec psi Delta' f (frame_ret_assert R F) k -->
         guard Espec psi Delta' f (fun rho : environ => F rho * P rho) (Kseq c k))).
Proof.
intros.
extensionality w.
rewrite semax_fold_unfold.
apply prop_ext; intuition.
Qed.

Lemma semax_Slabel {cs:compspecs} {Espec: OracleKind}
       (Gamma:tycontext) (P:environ -> mpred) (c:statement) (Q:ret_assert) l:
@semax cs Espec Gamma P c Q -> @semax cs Espec Gamma P (Slabel l c) Q.
Proof. intros. 
rewrite semax_eq. rewrite semax_eq in H.
eapply derives_trans. eassumption. clear H.
apply allp_derives; intros psi.
apply allp_derives; intros Delta.
apply allp_derives; intros CS'.
apply prop_imp_derives; intros TC.
apply imp_derives; [ apply derives_refl | ].
apply allp_derives; intros k.
apply allp_derives; intros F.
apply allp_derives; intros f.
apply imp_derives; [ apply derives_refl | ].
apply guard_safe_adj'.
intros.
clear - H.
eapply jsafeN_local_step.
constructor.
intros.
eapply age_safe; eauto.
Qed.

Lemma denote_tc_resource: forall {cs: compspecs} rho a a' t, resource_at a = resource_at a' ->
  denote_tc_assert t rho a -> denote_tc_assert t rho a'.
Proof.
  induction t; auto; intros; simpl in *.
  - destruct H0; auto.
  - destruct H0; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho); auto; simpl in *; if_tac; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho); auto; simpl in *; if_tac; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho), (eval_expr e0 rho); auto; simpl in *.
    + simple_if_tac; auto.
      destruct H0; split; auto.
      destruct H1; [left | right]; simpl in *; rewrite <- H; auto.
    + simple_if_tac; auto.
      destruct H0; split; auto.
      destruct H1; [left | right]; simpl in *; rewrite <- H; auto.
    + unfold test_eq_ptrs in *.
      destruct (sameblock _ _), H0; split; simpl in *; rewrite <- H; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho), (eval_expr e0 rho); auto; simpl in *.
    unfold test_order_ptrs in *.
    destruct (sameblock _ _), H0; split; simpl in *; rewrite <- H; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho); auto; simpl in *; if_tac; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho); auto; simpl in *; if_tac; auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho); auto; simpl in *.
    + destruct (Zoffloat f); auto.
    + destruct (Zofsingle f); auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho); auto; simpl in *.
    + destruct (Zoffloat f); auto.
    + destruct (Zofsingle f); auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho), (eval_expr e0 rho); auto.
  - unfold liftx in *; simpl in *.
    unfold lift in *; simpl in *.
    destruct (eval_expr e rho), (eval_expr e0 rho); auto.
Qed.

Lemma bupd_denote_tc: forall {cs: compspecs} P t rho a,
  denote_tc_assert t rho a -> bupd P a -> bupd (denote_tc_assert t rho && P) a.
Proof.
  repeat intro.
  destruct (H0 _ H1) as (b & ? & m & ? & ? & ? & ?); subst.
  eexists; split; eauto; exists m; repeat split; eauto.
  eapply denote_tc_resource; [|eauto]; auto.
Qed.

Lemma assert_safe_jsafe: forall {Espec: OracleKind} ge f ve te c k ora jm,
  assert_safe Espec ge f ve te (Cont (Kseq c k)) (construct_rho (filter_genv ge) ve te) (m_phi jm) ->
  jm_bupd ora (jsafeN OK_spec ge (level jm) ora (State f c k ve te)) jm.
Proof.
  repeat intro.
  destruct (H _ H1) as (? & ? & ? & Hl & Hr & ? & Hsafe); subst.
  do 2 red in Hsafe.
  destruct (juicy_mem_resource _ _ Hr) as (jm' & ? & ?); subst.
  exists jm'; repeat split; auto.
  rewrite level_juice_level_phi, <- Hl.
  destruct (gt_dec (level (m_phi jm')) O).
  specialize (Hsafe ora jm').
  apply Hsafe; auto.
  eapply joins_comm, join_sub_joins_trans, joins_comm, H2.
  destruct H0.
  change (Some (ghost_PCM.ext_ref ora, NoneP) :: nil) with
    (ghost_approx (m_phi jm) (Some (ghost_PCM.ext_ref ora, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
  replace (level (m_phi jm')) with O by lia. constructor.
Qed.

Lemma assert_safe_jsafe': forall {Espec: OracleKind} ge f ve te k ora jm,
  assert_safe Espec ge f ve te (Cont k) (construct_rho (filter_genv ge) ve te) (m_phi jm) ->
  jm_bupd ora (jsafeN OK_spec ge (level jm) ora (State f Sskip k ve te)) jm.
Proof.
  intros.
  repeat intro.
  destruct (H _ H1) as (? & ? & ? & Hl & Hr & ? & Hsafe); subst.
  simpl in Hsafe.
  destruct (juicy_mem_resource _ _ Hr) as (jm' & ? & ?); subst.
  exists jm'; repeat split; auto.
  rewrite level_juice_level_phi, <- Hl.
  specialize (Hsafe ora jm').
  spec Hsafe. {
    eapply joins_comm, join_sub_joins_trans, joins_comm, H2.
    destruct H0.
    change (Some (ghost_PCM.ext_ref ora, NoneP) :: nil) with
      (ghost_approx (m_phi jm) (Some (ghost_PCM.ext_ref ora, NoneP) :: nil)).
    eexists; apply ghost_fmap_join; eauto.
  }
  do 2 (spec Hsafe; [auto|]).
  destruct (gt_dec (level (m_phi jm')) O).
2:   replace (level (m_phi jm')) with O by lia; constructor.
  spec Hsafe; [auto |].
  destruct k; try contradiction; auto.
  destruct (level (m_phi jm')); try lia.
  inv Hsafe; try discriminate; try contradiction.
  eapply jsafeN_step; eauto.
  destruct H5; split; auto. inv H3; econstructor; simpl; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  eapply jsafeN_local_step. constructor.
  intros.
  eapply age_safe; eauto.
  destruct (level (m_phi jm')); try lia.
  inv Hsafe; try discriminate; try contradiction.
  eapply jsafeN_step; eauto.
  destruct H5; split; auto. inv H3; econstructor; simpl; eauto.
Qed.

Lemma jm_bupd_local_step
     : forall {Espec: OracleKind} (ge : genv) (ora : OK_ty) (s1 : CC_core)
         (m : juicy_mem) (s2 : CC_core),
       cl_step ge s1 (m_dry m) s2 (m_dry m) ->
       (forall m' : juicy_mem,
        age m m' -> jm_bupd ora (jsafeN (@OK_spec Espec) ge (level m') ora s2) m') ->
       jm_bupd ora (jsafeN (@OK_spec Espec) ge (level m) ora s1) m.
Proof.
intros.
destruct (age1 m) as [m' | ] eqn:?H.
Abort.  