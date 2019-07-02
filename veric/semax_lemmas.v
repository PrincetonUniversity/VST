Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.own.

Local Open Scope pred.

Hint Resolve @now_later @andp_derives @sepcon_derives.

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
intuition.
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
  omega.
  omega.
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-b)); omega.
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
Hint Resolve @age_laterR.

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
 rewrite H0. clear; intuition.
* clear - H2 H5.
 hnf; intros. eapply H5.
 specialize (H2 id). hnf in H2. rewrite H in H2. eauto.
Qed.
(*
Lemma funassert_orig_resource: forall Delta rho a a' (Hl: level a = level a')
  (Hr: resource_at a = resource_at a'),
  funassert Delta rho a -> funassert Delta rho a'.
Proof.
  intros.
  destruct H as [H1 H2]; split; repeat intro.
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
    rewrite fmap_app, approx_oo_approx', approx'_oo_approx by omega; auto.
  - specialize (H2 b b0).
    destruct b0; simpl in *.
    apply (H2 _ (rt_refl _ _ _)).
    rewrite Hr, Hl.
    destruct H0 as [p Hp].
    pose proof (necR_level _ _ H).
    rewrite <- resource_at_approx.
    eapply necR_PURE' in H as [? ->]; simpl; eauto.
Qed.*)
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
    rewrite fmap_app, approx_oo_approx', approx'_oo_approx by omega; auto.
  - specialize (H2 b b0 b1). clear H1.
    destruct b0; simpl in *.
    apply (H2 _  (rt_refl _ _ _)).
    rewrite Hr, Hl.
    destruct H0 as [p Hp].
    pose proof (necR_level _ _ H).
    rewrite <- resource_at_approx.
    eapply necR_PURE' in H as [? ->]; simpl; eauto.
Qed.

Lemma cl_corestep_fun': forall ge, corestep_fun (cl_core_sem ge).
Proof.  repeat intro. eapply cl_corestep_fun; simpl in *; eauto. Qed.
Hint Resolve cl_corestep_fun'.

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
intros k F.
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
repeat intro. (* simpl exit_tycon. *)
simpl.
specialize (H rho). destruct R; simpl in H. simpl tycontext.RA_normal.
rewrite sepcon_comm.
eapply sepcon_derives; try apply H0; auto.

repeat intro.
destruct (H0 _ H1) as (b & ? & m' & ? & ? & ? & HP).
exists b; split; auto; exists m'; repeat split; auto.
repeat intro.
specialize (HP ora jm H6 H7 H8).
destruct (@level rmap _ m').
constructor.
apply convergent_controls_jsafe with (State ve te k); auto.
simpl.

intros.
destruct H9 as [? [? ?]].
split3; auto.

econstructor; eauto.
Qed.

Lemma jsafe_corestep_forward:
  forall {Espec: OracleKind} ge c m c' m' n z,
    jstep (cl_core_sem ge) c m c' m' -> jsafeN (@OK_spec Espec) ge (S n) z c m ->
    jm_bupd z (jsafeN (@OK_spec Espec) ge n z c') m'.
Proof.
  intros.
  inv H0.
  assert ((c',m') = (c'0,m'0)).
  { eapply juicy_core_sem_preserves_corestep_fun with (csem := cl_core_sem ge); eauto. }
  inv H0; auto.
  setoid_rewrite (semantics.corestep_not_at_external (juicy_core_sem _)) in H2; eauto; congruence.
  contradiction.
Qed.

Lemma semax_unfold {CS: compspecs} {Espec: OracleKind}:
  semax Espec = fun Delta P c R =>
    forall (psi: Clight.genv) Delta' CS' (w: nat)
          (TS: tycontext_sub Delta Delta')
          (HGG: (*genv_cenv psi = cenv_cs*)cenv_sub (@cenv_cs CS) (@cenv_cs CS') /\ cenv_sub (@cenv_cs CS') (genv_cenv psi))
           (Prog_OK: @believe CS' Espec Delta' psi Delta' w) (k: cont) (F: assert),
        closed_wrt_modvars c F ->
       rguard Espec psi Delta' (frame_ret_assert R F) k w ->
       guard Espec psi Delta' (fun rho => F rho * P rho) (Kseq c :: k) w.
Proof.
unfold semax; rewrite semax_fold_unfold.
extensionality Delta P c R.
apply prop_ext; split; intros.
+ eapply (H w); eauto.
  - split; auto. 
  - split; trivial.
+ intros psi Delta' CS'.
  apply prop_imp_i; intros [? HGG].
  intros w' ? ? k F w'' ? [? ?].
  apply (H psi Delta' CS' w'' H0 HGG); trivial. 
  eapply pred_nec_hereditary; eauto.
Qed.

Fixpoint list_drop (A: Type) (n: nat) (l: list A) {struct n} : list A :=
  match n with O => l | S i => match l with nil => nil | _ :: l' => list_drop A i l' end end.
Arguments list_drop [A] _ _.

Definition straightline (c: Clight.statement) :=
 forall ge ve te k m ve' te' k' m',
        cl_step ge (State ve te (Kseq c :: k)) m (State ve' te' k') m' ->  k=k'.

Lemma straightline_assign: forall e0 e, straightline (Clight.Sassign e0 e).
Proof.
unfold straightline; intros.
inv H; auto.
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
specialize (H x psi Delta' CS' w TS HGG Prog_OK k F H0 H1).
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
intros.
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
(*destruct H4 as [[[TC [x H5]] ?] ?].*)
specialize (H x).
specialize (H psi Delta' CS' w TS HGG Prog_OK k F H0).
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
  forall (Espec: OracleKind) psi tx vx (Q: assert), 
     exists k,  assert_safe Espec psi tx vx k = Q.
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
(*not needed
Lemma guard_environ_eqv:
  forall Delta Delta' f rho,
  tycontext_eqv Delta Delta' ->
  guard_environ Delta f rho -> guard_environ Delta' f rho.
Proof.
  intros.
  rewrite tycontext_eqv_spec in H.
  eapply guard_environ_sub; eauto.
  tauto.
Qed.*)

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

intros k F w4 Hw4 [? ?].
specialize (H5 k F w4 Hw4).
assert ((rguard Espec gx Delta'' (frame_ret_assert R F) k) w4).
do 9 intro.
apply (H9 b b0 b1 b2 y H10 a' H11).
destruct H12; split; auto; clear H13.
pose proof I.
destruct H12; split; auto.
(* unfold frame_ret_assert in H14|-*. *)
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
specialize (H psi Delta' CS' w TS HGG Prog_OK k F0F).
spec H. {
 unfold F0F.
 clear - H0 CL.
 hnf in *; intros; simpl in *.
 rewrite <- CL. rewrite <- H0. auto.
 intuition.
 intuition.
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
  forall {Espec: OracleKind} ge ve te st rho w,
   (forall w', age w w' -> assert_safe Espec ge ve te st rho w) ->
    assert_safe Espec ge ve te st rho w.
Proof.
intros.
case_eq (age1 w). auto.
clear H.
intro; apply bupd_intro; repeat intro.
rewrite (af_level1 age_facts) in H.
rewrite H.
constructor.
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
  forall {Espec: OracleKind} (P: pred rmap) ge ve te k rho,
              ((|> P) >=> assert_safe Espec ge ve te k rho) |--   |>  (P >=> assert_safe Espec ge ve te k rho).
Proof.
intros.
intros w ?.
apply (@pred_sub_later' _ _ P  (assert_safe Espec ge ve te k rho)); auto.
eapply subp_trans'; try apply H.
apply derives_subp; clear.
apply now_later.
Qed.

End SemaxContext.

Hint Resolve @age_laterR.


Fixpoint filter_seq (k: cont) : cont :=
 match k with
  | Kseq s :: k1 => filter_seq k1
  | _ => k
  end.

Lemma cons_app: forall A (x: A) (y: list A), x::y = (x::nil)++y.
Proof. auto. Qed.

Lemma cons_app': forall A (x:A) y z,
      x::y++z = (x::y)++z.
Proof. auto. Qed.

Lemma cat_prefix_empty:
   forall {A} prefix (ctl: list A), ctl =  prefix ++ ctl -> prefix = nil.
Proof.
do 3 intro.
destruct prefix; auto; intro; elimtype False.
assert (length ctl = length ((a::prefix) ++ ctl)).
f_equal; auto.
simpl in H0.
rewrite app_length in H0.
omega.
Qed.

Definition true_expr : Clight.expr := Clight.Econst_int Int.one (Tint I32 Signed noattr).


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

Lemma filter_seq_call_cont:
  forall ctl1 ctl2, filter_seq ctl1 = filter_seq ctl2 -> call_cont ctl1 = call_cont ctl2.
Proof.
  intros ? ? H0. revert ctl2 H0; induction ctl1; simpl; intros.
  revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
  destruct a; auto; revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
Qed.

Lemma call_cont_app_nil:
  forall l k, call_cont l = nil -> call_cont (l++k) = call_cont k.
Proof.
 intros l k; revert k; induction l; simpl; intros;
   try destruct a; simpl in *; try congruence; auto.
Qed.
Lemma call_cont_app_cons:
  forall l c l', call_cont l = c::l' -> forall k, call_cont (l++k) = c::l' ++ k.
Proof.
  intros; revert c l' k H; induction l; simpl; intros;
   try destruct a; simpl in *; try congruence; auto.
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

Lemma age1_resource_decay:
  forall jm jm', age jm jm' -> resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
 intros. split.
 apply age_level in H.
 change (level (m_phi jm)) with (level jm).
 change (level (m_phi jm')) with (level jm').
 omega.
 intro l. split. apply juicy_mem_alloc_cohere. left.
 symmetry; apply age1_resource_at with (m_phi jm); eauto.
  destruct (age1_juicy_mem_unpack _ _ H); auto.
 symmetry; apply resource_at_approx.
Qed.

Lemma safe_loop_skip:
  forall {Espec: OracleKind}
    ge ora ve te k m,
    jsafeN (@OK_spec Espec) ge (level m) ora
           (State ve te (Kseq (Sloop Clight.Sskip Clight.Sskip) :: k)) m.
Proof.
  intros.
  remember (level m)%nat as N.
  destruct N; [constructor|].
  case_eq (age1 m); [intros m' ? |  intro; apply age1_level0 in H; omegaContradiction].
  apply jsafeN_step with
    (c' := State ve te (Kseq Sskip :: Kseq Scontinue :: Kloop1 Sskip Sskip :: k))
    (m'0 := m').
  split3.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  repeat econstructor.
  apply age1_resource_decay; auto. split; [apply age_level; auto|].
  apply age_jm_phi in H.
  erewrite (age1_ghost_of _ _ H) by (symmetry; apply ghost_of_approx).
  unfold level at 1; simpl.
  repeat intro; auto.
  assert (N = level m')%nat.
  apply age_level in H; omega.
  clear HeqN m H. rename m' into m.
  intros; eexists; repeat split; eauto.
  clear H H1; revert m H0; induction N; intros; simpl; [constructor|].
  case_eq (age1 m); [intros m' ? |  intro; apply age1_level0 in H; omegaContradiction].
  apply jsafeN_step
    with (c' := State ve te (Kseq Sskip :: Kseq Scontinue :: Kloop1 Sskip Sskip :: k))
         (m'0 := m').
  split3.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  repeat constructor.
 apply age1_resource_decay; auto. split; [apply age_level; auto|].
  apply age_jm_phi in H.
  erewrite (age1_ghost_of _ _ H) by (symmetry; apply ghost_of_approx).
  unfold level at 1; simpl.
  repeat intro; auto.
  intros; eexists; repeat split; eauto.
  eapply IHN; eauto.
  apply age_level in H. omega.
Qed.

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

Lemma safe_step_forward {Espec: OracleKind}:
  forall psi n ora st m,
   cl_at_external st = None ->
   jsafeN (@OK_spec Espec) psi (S n) ora st m ->
 exists st', exists m',
   jstep (cl_core_sem psi) st m st' m' /\ jm_bupd ora (jsafeN (@OK_spec Espec) psi n ora  st') m'.
Proof.
 intros.
 inv H0.
 eexists; eexists; split; eauto.
 simpl in H2; rewrite H2 in H; congruence.
 contradiction.
Qed.

Lemma safeN_strip {Espec: OracleKind}:
  forall ge n ora ve te k m,
     jsafeN (@OK_spec Espec) ge n ora (State ve te (strip_skip k)) m =
     jsafeN (@OK_spec Espec) ge n ora (State ve te k) m.
Proof.
 intros.
 destruct n. apply prop_ext; simpl; intuition.
 constructor. constructor.
 apply prop_ext; split; intros H.
 { induction k. simpl in H. auto. destruct a; auto.
   destruct (dec_skip s); subst.
   simpl in H|-*. apply IHk in H. apply safe_seq_skip; auto.
   destruct s; simpl in *; congruence. }
 { induction k. simpl. auto. destruct a; auto.
   destruct (dec_skip s); subst.
   simpl in *. apply IHk. apply safe_seq_skip'; auto.
   destruct s; simpl in *; congruence. }
Qed.

Local Open Scope nat_scope.

Definition control_as_safe {Espec: OracleKind} ge n ctl1 ctl2 :=
 forall (ora : OK_ty) (ve : env) (te : temp_env) (m : juicy_mem) (n' : nat),
     n' <= n ->
     jsafeN (@OK_spec Espec) ge n' ora (State ve te ctl1) m ->
     jsafeN (@OK_spec Espec) ge n' ora (State ve te ctl2) m.

Fixpoint prebreak_cont (k: cont) : cont :=
  match k with
  | Kloop1 s e3 :: k' => k
  | Kseq s :: k' => prebreak_cont k'
  | Kloop2 s e3 :: k' => k
  | Kswitch :: k' => k
  | _ =>  nil (* stuck *)
  end.

Lemma prebreak_cont_is: forall k,
  match (prebreak_cont k) with
  | Kloop1 _ _ :: _ => True
  | Kloop2 _ _ :: _ => True
  | Kswitch :: _ => True
  | nil => True
  | _ => False
  end.
Proof.
induction k; simpl; auto.
destruct (prebreak_cont k); try contradiction; destruct a; auto.
Qed.

Lemma find_label_prefix:
  forall lbl s ctl k, find_label lbl s ctl = Some k -> exists j, k = j++ctl
with
  find_label_ls_prefix:
  forall lbl s ctl k, find_label_ls lbl s ctl = Some k -> exists j, k = j++ctl.
Proof.
 intros.
  clear find_label_prefix.
  revert ctl k H; induction s; simpl; intros; try congruence.
  revert H; case_eq (find_label lbl s1 (Kseq s2 :: ctl)); intros; [inv H0 | auto ].
  destruct (IHs1 _ _ H) as [j ?]. exists (j++ (Kseq s2::nil)); rewrite app_ass; auto.
  revert H; case_eq (find_label lbl s1 ctl); intros; [inv H0 | auto ]; auto.
  revert H; case_eq (find_label lbl s1 (Kseq Scontinue :: Kloop1 s1 s2 :: ctl)); intros; [inv H0 | auto ].
  destruct (IHs1 _ _ H) as [j ?]. exists (j++ (Kseq Scontinue :: Kloop1 s1 s2::nil)); rewrite app_ass; auto.
  destruct (IHs2 _ _ H0) as [j ?]. exists (j++ (Kloop2 s1 s2::nil)); rewrite app_ass; auto.
  destruct (find_label_ls_prefix _ _ _ _ H) as [j ?]. exists (j++(Kswitch :: nil)); rewrite app_ass; auto.
  if_tac in H. subst l. inv H.
  exists (Kseq s :: nil); auto.
  apply IHs; auto.

 induction s; simpl; intros. inv H.
 revert H; case_eq (find_label lbl s (Kseq (seq_of_labeled_statement s0) :: ctl)); intros.
 inv H0.
 destruct (find_label_prefix _ _ _ _ H) as [j ?]; exists (j++Kseq (seq_of_labeled_statement s0) ::nil); rewrite app_ass; auto.
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

Lemma find_label_prefix2':
 forall lbl s k1 pre, find_label lbl s k1 = Some (pre++k1) ->
               forall k2, find_label lbl s k2 = Some (pre++k2)
with find_label_ls_prefix2':
 forall lbl s k1 pre, find_label_ls lbl s k1 = Some (pre++k1) ->
               forall k2, find_label_ls lbl s k2 = Some (pre++k2) .
Proof.
intros. clear find_label_prefix2'.
revert pre k1 H k2; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 try
 (destruct (find_label_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre;
  erewrite app_ass in H; simpl in H;
  rewrite (IHs1 _ _ H); rewrite app_ass; reflexivity);
 try solve [erewrite (find_label_None); eauto].
 rewrite (IHs1 _ _ H); auto.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k1) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k1)
   in H.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k2) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k2).
destruct (find_label_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre.
  erewrite app_ass in H; simpl in H;
  rewrite (IHs1 _ _ H); rewrite app_ass; reflexivity.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k1) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k1)
   in H.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k2) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k2).
 erewrite (find_label_None); eauto.
 destruct (find_label_prefix _ _ _ _ H0) as [j Hj];
  rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre.
  erewrite app_ass in H0; simpl in H0;
  rewrite (IHs2 _ _ H0); rewrite app_ass; reflexivity.
destruct (find_label_ls_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre.
  erewrite app_ass in H; simpl in H.
  rewrite (find_label_ls_prefix2' _ _ _ _ H); rewrite app_ass; reflexivity.
  if_tac. inv H. rewrite cons_app in H2. apply app_inv_tail in H2; subst. reflexivity.
  eauto.

intros. clear find_label_ls_prefix2'.
revert pre k1 H k2; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 eauto.
 (destruct (find_label_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre;
  erewrite app_ass in H; simpl in H).
  rewrite (find_label_prefix2' _ _ _ _ H); rewrite app_ass; reflexivity;
 try solve [erewrite (find_label_ls_None); eauto].
  erewrite (find_label_None); eauto.
Qed.

Lemma find_label_prefix2:
  forall lbl s pre j ctl1 ctl2,
   find_label lbl s (pre++ctl1) = Some (j++ctl1) ->
   find_label lbl s (pre++ctl2) = Some (j++ctl2).
Proof.
intros.
 destruct (find_label_prefix _ _ _ _ H).
 rewrite <- app_ass in H0.
 apply  app_inv_tail in H0. subst j.
 rewrite app_ass in *.
 forget (pre++ctl1) as k1. forget (pre++ctl2) as k2.
 clear - H. rename x into pre.
 eapply find_label_prefix2'; eauto.
Qed.

Lemma control_as_safe_bupd {Espec: OracleKind}: forall ge n ctl1 ctl2, control_as_safe ge n ctl1 ctl2 ->
 forall (ora : OK_ty) (ve : env) (te : temp_env) (m : juicy_mem) (n' : nat),
     n' <= n ->
     jm_bupd ora (jsafeN (@OK_spec Espec) ge n' ora (State ve te ctl1)) m ->
     jm_bupd ora (jsafeN (@OK_spec Espec) ge n' ora (State ve te ctl2)) m.
Proof.
  repeat intro.
  destruct (H1 _ H2) as (? & ? & ? & ?); eauto.
Qed.

Lemma corestep_preservation_lemma {Espec: OracleKind}:
   forall ge ctl1 ctl2 ora ve te m n c l c' m',
       filter_seq ctl1 = filter_seq ctl2 ->
      (forall k : list cont', control_as_safe ge n (k ++ ctl1) (k ++ ctl2)) ->
      control_as_safe ge (S n) ctl1 ctl2 ->
      jstep (cl_core_sem ge) (State ve te (c :: l ++ ctl1)) m c' m' ->
      jm_bupd ora (jsafeN (@OK_spec Espec) ge n ora c') m' ->
   exists c2 : corestate,
     exists m2 : juicy_mem,
       jstep (cl_core_sem ge) (State ve te (c :: l ++ ctl2)) m c2 m2 /\
       jm_bupd ora (jsafeN (@OK_spec Espec) ge n ora c2) m2.
Proof. intros until m'. intros H0 H4 CS0 H H1.
  remember (State ve te (c :: l ++ ctl1)) as q. rename c' into q'.
  destruct H as [H [Hb [Hc Hg]]].
  remember (m_dry m) as dm; remember (m_dry m') as dm'.
  revert c l m Heqdm m' Heqdm' Hb Hc Hg H1 Heqq; induction H; intros; try inv Heqq.
  (* assign *)
  do 2 eexists; split; [split3; [econstructor; eauto | auto | auto ] | eapply control_as_safe_bupd; auto ].
  (* set *)
  do 2 eexists; split; [split3; [ | eassumption | auto ] | ].
  rewrite <- Heqdm'; econstructor; eauto.
  eapply control_as_safe_bupd; auto.
  (* call_internal *)
  do 2 eexists; split; [split3; [econstructor; eauto | auto | auto ] |  ].
  do 3 rewrite cons_app'. eapply control_as_safe_bupd; auto.
  (* call_external *)
{ do 2 eexists; split; [split3; [ | eassumption | auto ] | ].
  rewrite <- Heqdm';  eapply step_call_external; eauto.
  intros ? HC J; specialize (H5 _ HC J) as (m'' & J' & Hupd & H5).
  exists m''; split; auto; split; auto.
  destruct n; [constructor|].
  inv H5.
  { destruct H7 as (?&?&?). inv H5. }
  { eapply jsafeN_external; eauto.
    intros ret m'0 z'' n'' Hargsty Hretty Hle H10 H11; specialize (H9 ret m'0 z'' n'' Hargsty Hretty Hle H10 H11).
    destruct H9 as [c' [? ?]]. simpl in H5. unfold cl_after_external in *.
    destruct ret as [ret|]. destruct optid.
    exists (State ve (PTree.set i ret te) (l ++ ctl2)); split; auto.
    inv H5. eapply control_as_safe_bupd; auto.
    destruct H10 as (?&?&?). inv H5.
    exists (State ve te (l ++ ctl2)); split; auto. eapply control_as_safe_bupd; auto.
    destruct optid; auto.
    exists (State ve (PTree.set i Vundef te) (l ++ ctl2)); split; auto.  inv H5. eapply control_as_safe_bupd; auto.
    exists (State ve te (l ++ ctl2)); split; auto. eapply control_as_safe_bupd; auto.
    inv H5. auto. }
   contradiction. }
  (* sequence  *)
  { destruct (IHcl_step (Kseq s1) (Kseq s2 :: l)
            _ (eq_refl _) _ (eq_refl _) Hb Hc Hg H1 (eq_refl _))
      as [c2 [m2 [? ?]]]; clear IHcl_step.
    destruct H2 as [H2 [H2b H2c]].
    exists c2, m2; split; auto. split3; auto. constructor. apply H2. }
  (* skip *)
  { destruct l.
    simpl in H.
   assert (jsafeN (@OK_spec Espec) ge (S n) ora (State ve te ctl1) m0).
   { econstructor; eauto; split3; eauto. }
   apply CS0 in H2; auto.
    eapply safe_step_forward in H2; auto.
   destruct H2 as [st2 [m2 [? ?]]]; exists st2; exists m2; split; auto.
   simpl.
     destruct H2 as [H2 [H2b H2c]].
    split3; auto.
    simpl; rewrite <- strip_step. simpl. rewrite strip_step; auto.
    destruct (IHcl_step c l _ (eq_refl _) _ (eq_refl _) Hb Hc Hg H1 (eq_refl _))
      as [c2 [m2 [? ?]]]; clear IHcl_step.
    exists c2; exists m2; split; auto.
    destruct H2 as [H2 [H2b H2c]].
   simpl.
   split3; auto.
   simpl; rewrite <- strip_step.
   change (strip_skip (Kseq Sskip :: c :: l ++ ctl2)) with (strip_skip (c::l++ctl2)).
   rewrite strip_step; auto. }
  (* continue *)
  case_eq (continue_cont l); intros.
  assert (continue_cont (l++ctl1) = continue_cont (l++ctl2)).
  clear - H0 H2.
  induction l; simpl in *.
 revert ctl2 H0; induction ctl1; simpl; intros.
 revert H0; induction ctl2; simpl; intros; auto.
 destruct a; simpl in *; auto. inv H0. inv H0.
 destruct a; auto.
 revert H0; induction ctl2; simpl; intros. inv H0.
 destruct a; try congruence. rewrite <- (IHctl2 H0).
 f_equal.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence.
 auto.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence.
 auto.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence.
 auto.
 destruct a; try congruence. auto. auto.
  rewrite H3 in H.
  exists st', m'0; split; auto.
  split3; auto.
  constructor. auto.
  assert (forall k, continue_cont (l++k) = c::l0++k).
  clear - H2. revert H2; induction l; intros; try destruct a; simpl in *; auto; try discriminate.
  repeat rewrite cons_app'. f_equal; auto.
  rewrite H3 in H, IHcl_step.
  destruct (IHcl_step _ _ _ (eq_refl _) _ (eq_refl _) Hb Hc Hg H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2,m2; split; auto.
   destruct H5 as [H5 [H5b H5c]].
 split3; auto.
 constructor. rewrite H3; auto.
  (* break *)
{
  case_eq (prebreak_cont l); intros.
  {
  assert (break_cont (l++ctl1) = break_cont (l++ctl2)).
  clear - H0 H2.
  revert H2; induction l; simpl; intros; try destruct a; try congruence.
  revert ctl2 H0; induction ctl1; simpl; intros.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence. auto.
 destruct a. auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 destruct s; auto.
  rewrite H3 in H.
  exists st', m'0; split; auto.
  split3; auto.
  constructor. auto.
  }
  {
  assert (PB:= prebreak_cont_is l); rewrite H2 in PB.
  destruct c; try contradiction.
  {
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (semantics.corestep (juicy_core_sem (cl_core_sem ge)) (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (@jsafeN_step genv _ _ genv_symb_injective (cl_core_sem ge) OK_spec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  }
  {
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (semantics.corestep (juicy_core_sem (cl_core_sem ge)) (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (@jsafeN_step genv _ _ genv_symb_injective  (cl_core_sem ge) OK_spec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  }
  {
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (semantics.corestep (juicy_core_sem (cl_core_sem ge)) (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (@jsafeN_step genv _ _ genv_symb_injective  (cl_core_sem ge) OK_spec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  }
  }
}
  (* ifthenelse *)
  exists (State ve te (Kseq (if b then s1 else s2) :: l ++ ctl2)), m'.
  split. split3; auto. rewrite <- Heqdm'. econstructor; eauto.
  rewrite cons_app. rewrite <- app_ass.
  eapply control_as_safe_bupd; auto.
  (* loop *)
  change (Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: l ++ ctl1) with
               ((Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: l) ++ ctl1) in H1.
  eapply control_as_safe_bupd in H1; eauto.
  do 2 eexists; split; eauto.
   split3; eauto. rewrite <- Heqdm'.
  econstructor; eauto.
  (* loop2 *)
  change (Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: l ++ ctl1) with
              ((Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: l) ++ ctl1) in H1.
  eapply control_as_safe_bupd in H1; eauto.
  do 2 eexists; split; eauto.   split3; eauto. rewrite <- Heqdm'.  econstructor; eauto.
 (* return *)
  case_eq (call_cont l); intros.
  rewrite call_cont_app_nil in * by auto.
  exists (State ve' te'' k'), m'0; split; auto.
  split3; auto.
  econstructor; try eassumption. rewrite call_cont_app_nil; auto.
  rewrite <- (filter_seq_call_cont _ _ H0); auto.
  rewrite (call_cont_app_cons _ _ _ H6) in H. inv H.
  do 2 eexists; split.
  split3; eauto.
  econstructor; try eassumption.
 rewrite (call_cont_app_cons _ _ _ H6). reflexivity.
  eapply control_as_safe_bupd; auto.
 (* switch *)
  do 2 eexists; split; [split3; [| eauto | eauto] | ].
  rewrite <- Heqdm'. econstructor; eauto.
  do 2 rewrite cons_app'. eapply control_as_safe_bupd; auto.
 (* label *)
  destruct (IHcl_step _ _  _ (eq_refl _) _ (eq_refl _) Hb Hc Hg H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2, m2; split; auto.
   destruct H2 as [H2 [H2b H2c]].
  split3; auto.
  constructor; auto.
 (* goto *)
  case_eq (call_cont l); intros.
  do 2 eexists; split; [ | apply H1].
  split3; auto.
  rewrite <- Heqdm'; econstructor. 2: rewrite call_cont_app_nil; auto.
  instantiate (1:=f).
  generalize (filter_seq_current_function ctl1 ctl2 H0); intro.
  clear - H3 H2 CUR.
  revert l H3 H2 CUR; induction l; simpl; try destruct a; intros; auto; try congruence.
  rewrite call_cont_app_nil in H by auto.
  rewrite <- (filter_seq_call_cont ctl1 ctl2 H0); eauto.
  rewrite (call_cont_app_cons _ _ _ H2) in H.
  assert (exists j, k' = j ++ ctl1).
  clear - H2 H.
  assert (exists id, exists f, exists ve, exists te, c =  Kcall id f ve te).
  clear - H2; induction l; [inv H2 | ].
  destruct a; simpl in H2; auto. inv H2; do 4 eexists; reflexivity.
  destruct H0 as [id [ff [ve [te ?]]]]. clear H2; subst c.
  change (find_label lbl (fn_body f)
      ((Kseq (Sreturn None) :: Kcall id ff ve te :: l0) ++ ctl1) = Some k') in H.
  forget (Kseq (Sreturn None) :: Kcall id ff ve te :: l0) as pre.
  assert (exists j, k' = j++ (pre++ctl1));
   [ | destruct H0 as [j H0]; exists (j++pre); rewrite app_ass; auto ].
  forget (pre++ctl1) as ctl. forget (fn_body f) as s;  clear - H.
 eapply find_label_prefix; eauto.
  destruct H3 as [j ?].
  subst k'.
  exists (State ve te (j++ctl2)), m'; split; [ | eapply control_as_safe_bupd; eauto].
  split3; auto.
  rewrite <- Heqdm'; econstructor.
  instantiate (1:=f).
  clear - CUR H2.
  revert f c l0 CUR H2; induction l; simpl; intros. inv H2.
  destruct a; simpl in *; eauto.
  rewrite (call_cont_app_cons _ _ _ H2).
  clear - H2 H.
  change (Kseq (Sreturn None) :: c :: l0 ++ ctl1) with ((Kseq (Sreturn None) :: c :: l0) ++ ctl1) in H.
  change (Kseq (Sreturn None) :: c :: l0 ++ ctl2) with ((Kseq (Sreturn None) :: c :: l0) ++ ctl2).
  forget (Kseq (Sreturn None) :: c :: l0)  as pre.
clear - H.
 eapply find_label_prefix2; eauto.
Qed.

Lemma control_as_safe_le {Espec: OracleKind}:
  forall n' n ge ctl1 ctl2, n' <= n -> control_as_safe ge n ctl1 ctl2 -> control_as_safe ge n' ctl1 ctl2.
Proof.
 intros. intro; intros. eapply H0; auto; omega.
Qed.

Lemma control_suffix_safe {Espec: OracleKind}:
    forall
      ge n ctl1 ctl2 k,
      filter_seq ctl1 = filter_seq ctl2 ->
      control_as_safe ge n ctl1 ctl2 ->
      control_as_safe ge n (k ++ ctl1) (k ++ ctl2).
  Proof.
    intro ge. induction n using (well_founded_induction lt_wf).
    intros. hnf; intros.
    destruct n'; [ constructor | ].
    assert (forall k, control_as_safe ge n' (k ++ ctl1) (k ++ ctl2)).
    intro; apply H; auto. apply control_as_safe_le with n; eauto. omega.
   case_eq (strip_skip k); intros.
    rewrite <- safeN_strip in H3|-*.  rewrite strip_skip_app in H3|-* by auto.
   rewrite safeN_strip in H3|-*.
    auto.
   assert (ZZ: forall k, strip_skip (c::l++k) = c::l++k)
    by (clear - H5; intros; rewrite <- (strip_skip_app_cons H5); rewrite strip_strip; auto).
  rewrite <- safeN_strip in H3|-*.
  rewrite (strip_skip_app_cons H5) in H3|-* by auto.
  inv H3.
  apply corestep_preservation_lemma
    with (c0 := c) (l0 := l) (ve0 := ve) (te0 := te) (m0 := m)
         (ctl3:=ctl1) (ctl4:=ctl2) (n0 := n') in H8; auto.
   destruct H8 as [? [? [? ?]]].
   econstructor; eauto.
   eapply control_as_safe_le; eauto.
  simpl in H7. congruence.
  simpl in H6. unfold cl_halted in H6. contradiction.
Qed.

Lemma guard_safe_adj {Espec: OracleKind}:
 forall
   psi Delta P k1 k2,
   current_function k1 = current_function k2 ->
  (forall ora m ve te n,
     jsafeN (@OK_spec Espec) psi n ora (State ve te k1) m ->
     jsafeN (@OK_spec Espec) psi n ora (State ve te k2) m) ->
  guard Espec psi Delta P k1 |-- guard Espec psi Delta P k2.
Proof.
intros.
unfold guard.
apply allp_derives. intros tx.
apply allp_derives. intros vx.
rewrite H; apply subp_derives; auto.
apply bupd_mono.
intros w ? ? ? ? ? ?.
apply H0.
eapply H1; eauto.
Qed.

Lemma assert_safe_adj:
  forall {Espec: OracleKind} ge ve te k k' rho,
      (forall n, control_as_safe ge n k k') ->
     assert_safe Espec ge ve te k rho |-- assert_safe Espec ge ve te k' rho.
Proof.
 intros. apply bupd_mono. intros w ? ? ? ? ? ?. specialize (H0 ora jm H1 H2 H3).
 eapply H; try apply H0. apply le_refl.
Qed.

Lemma assert_safe_adj':
  forall {Espec: OracleKind} ge ve te k k' rho P w,
      (forall n, control_as_safe ge n k k') ->
     app_pred (P >=> assert_safe Espec ge ve te k rho) w ->
     app_pred (P >=> assert_safe Espec ge ve te k' rho) w.
Proof.
 intros.
 eapply subp_trans'; [ | apply derives_subp; eapply assert_safe_adj; try eassumption; eauto].
 auto.
Qed.

Lemma rguard_adj:
  forall {Espec: OracleKind} ge Delta R k k',
      current_function k = current_function k' ->
      (forall ek vl n, control_as_safe ge n (exit_cont ek vl k) (exit_cont ek vl k')) ->
      rguard Espec ge Delta R k |-- rguard Espec ge Delta R k'.
Proof.
 intros.
 intros n H1;  hnf in H1|-*.
 intros ek vl te ve; specialize (H1 ek vl te ve).
 rewrite <- H.
 eapply assert_safe_adj'; eauto.
Qed.

Lemma assert_safe_last': forall {Espec: OracleKind} ge ve te ctl rho w,
            (age1 w <> None -> assert_safe Espec ge ve te ctl rho w) ->
             assert_safe Espec ge ve te ctl rho w.
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
  Let eq_dec_attr : EqDec attr. repeat t. Qed.
  Let eq_dec_signedness : EqDec signedness. t. Qed.
  Let eq_dec_intsize : EqDec intsize. t. Qed.
  Let eq_dec_floatsize : EqDec floatsize. t. Qed.
  Let eq_dec_Z : EqDec Z. repeat t. Qed.
  Let eq_dec_calling_convention : EqDec calling_convention. repeat t. Qed.
  Lemma eq_dec_external_function : EqDec external_function. repeat t. Qed.
  Let eq_dec_option_ident := option_eq (ident_eq).
  Let eq_dec_option_Z : EqDec (option Z). repeat t. Qed.
  Let eq_dec_typelist : EqDec typelist. repeat t. Qed.

  Lemma eq_dec_expr : EqDec expr.
  Proof. repeat t. Qed.

  Let eq_dec_expr := eq_dec_expr.
  Let eq_dec_option_expr : EqDec (option expr). repeat t. Qed.
  Let eq_dec_list_expr : EqDec (list expr). repeat t. Qed.

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
  Qed.

  Lemma eq_dec_labeled_statements : forall l l' : labeled_statements, { l = l' } + { l <> l' }.
  Proof.
    decide equality.
    apply eq_dec_statement.
  Qed.

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
         ALL F : assert ,
         !! closed_wrt_modvars c F &&
         rguard Espec psi Delta' (frame_ret_assert R F) k -->
         guard Espec psi Delta' (fun rho : environ => F rho * P rho) (Kseq c :: k))).
Proof.
intros.
extensionality w.
rewrite semax_fold_unfold.
apply prop_ext; intuition.
Qed.

Lemma safe_kseq_Slabel {Espec: OracleKind} psi n ora ve te l c k m :
  @jsafeN (@OK_ty Espec) (@OK_spec Espec) psi n ora
      (State ve te (@cons cont' (Kseq c) k)) m ->
@jsafeN (@OK_ty Espec) (@OK_spec Espec) psi n ora
  (State ve te (@cons cont' (Kseq (Slabel l c)) k)) m.
Proof.
inversion 1; subst.
+ constructor.
+ econstructor; eauto. simpl. destruct H0 as (?&?&?). split3; eauto. 
  simpl in H0. simpl. eapply step_label; trivial.
+ simpl in *; congruence.
+ simpl in *. unfold cl_halted in H0. contradiction.
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
apply imp_derives; [ apply derives_refl | ].
apply guard_safe_adj; [ trivial | intros].
apply safe_kseq_Slabel; trivial.
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

Lemma assert_safe_jsafe: forall {Espec: OracleKind} ge ve te ctl ora jm,
  assert_safe Espec ge ve te ctl (construct_rho (filter_genv ge) ve te) (m_phi jm) ->
  jm_bupd ora (jsafeN OK_spec ge (level jm) ora (State ve te ctl)) jm.
Proof.
  repeat intro.
  destruct (H _ H1) as (? & ? & ? & Hl & Hr & ? & Hsafe); subst.
  destruct (juicy_mem_resource _ _ Hr) as (jm' & ? & ?); subst.
  exists jm'; repeat split; auto.
  rewrite level_juice_level_phi, <- Hl.
  apply Hsafe; auto.
  simpl.
  eapply joins_comm, join_sub_joins_trans, joins_comm, H2.
  destruct H0.
  change (Some (ghost_PCM.ext_ref ora, NoneP) :: nil) with
    (ghost_approx (m_phi jm) (Some (ghost_PCM.ext_ref ora, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
Qed.
