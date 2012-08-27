Require Import veric.base.
Require Import veric.Address.
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
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.semax.
Require Import veric.Clight_lemmas.

Open Local Scope pred.

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
  (nat_of_Z (z - a) <= nat_of_Z (z - b))%nat.
Proof.
  intros.
  apply inj_le_rev.
  do 2 rewrite nat_of_Z_max.
  rewrite Zmax_spec.
  destruct (zlt 0 (z-a)).
  rewrite Zmax_spec.
  destruct (zlt 0 (z-b)).
  omega.
  omega.
  rewrite Zmax_spec.
  destruct (zlt 0 (z-b)); omega.
Qed.

Section SemaxContext.
Context {Z} (Hspec: juicy_ext_spec Z).

Lemma universal_imp_unfold {A} {agA: ageable A}:
   forall B (P Q: B -> pred A) w,
     (All psi : B, P psi --> Q psi) w = (forall psi : B, (P psi --> Q psi) w).
Proof.
intros.
apply prop_ext; split; intros.
eapply H; eauto.
intro b; apply H. 
Qed.

Lemma semax'_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall ek vl rho, R' ek vl rho |-- R ek vl rho) ->
   semax' Hspec Delta G P c R' |-- semax' Hspec Delta G P c R.
Proof.
intros.
rewrite semax_fold_unfold.
apply allp_derives; intro psi.
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply imp_derives; auto.
unfold rguard, guard.
apply andp_derives; auto.
apply allp_derives; intro ek.
apply allp_derives; intro vl.
apply allp_derives; intro rho.
apply subp_derives; auto.
Qed.

Lemma semax'_pre:
 forall P' Delta G R P c,
  (forall rho, typecheck_environ rho Delta = true ->   P rho |-- P' rho)   
   ->   semax' Hspec Delta G P' c R |-- semax' Hspec Delta G P c R.
Proof.
intros.
repeat rewrite semax_fold_unfold.
apply allp_derives; intro psi.
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply imp_derives; auto.
unfold guard.
apply allp_derives; intro rho.
apply subp_derives; auto.
apply andp_derives; auto.
apply prop_andp_left; intros [? ?].
apply prop_andp_right; auto.
Qed.

Lemma semax'_pre_post:
 forall 
      P' (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall rho, typecheck_environ rho Delta = true ->   P rho |-- P' rho) ->
   (forall ek vl rho, R ek vl rho |-- R' ek vl rho) ->
   semax' Hspec Delta G P' c R |-- semax' Hspec Delta G P c R'.
Proof.
intros.
eapply derives_trans.
apply semax'_pre; eauto.
apply semax'_post; auto.
Qed.


Lemma cl_corestep_fun': corestep_fun cl_core_sem.
Proof.  intro; intros. eapply cl_corestep_fun; eauto. Qed.
Hint Resolve cl_corestep_fun'.

Lemma derives_skip:
  forall p Delta G (R: ret_assert),
      (forall rho, p rho |-- R EK_normal nil rho) -> 
        semax Hspec Delta G p Clight.Sskip R.
Proof.
intros ? ? ? ?; intros.
split. 
apply prove_some_static_thing.
intros n.
rewrite semax_fold_unfold.
intro psi.
intros ?w _ _. clear n.
intros k F.
intros ?w _ ?.
clear w. rename w0 into n.
intros rho w ?.
destruct H0 as [H0' H0].
specialize (H0 EK_normal nil rho w H1).
simpl exit_cont in H0.
simpl in H0'. clear n H1.
revert w H0. 
apply imp_derives; auto.
rewrite andp_assoc.
apply andp_derives; auto.
repeat intro.
simpl in H0.
specialize (H0 ora jm H1).
destruct (@level rmap _ a).
simpl; auto.
apply convergent_controls_safe with (State (ve_of rho) (te_of rho) k); auto.
simpl.

forget (te_of rho) as te. forget (ve_of rho) as ve.

intros.
destruct H2 as [? [? ?]].
split3; auto.
clear - H2.
econstructor; eauto.
Qed.

Lemma safe_strip:
   forall psi n ora ve te k k' m,
        strip_skip k = strip_skip k' ->
         jsafeN Hspec psi n ora (State ve te k) m ->
         jsafeN Hspec psi n ora (State ve te k') m.
Proof.
 intros.
 apply convergent_controls_safe with (State ve te k); simpl in *; auto.
 intros.
 clear - H H1.
 remember (State ve te k) as q.
 revert ve te k Heqq k' H; induction H1; intros; inv Heqq; simpl in *.
Abort.  (* undoubtedly true, tedious to prove, maybe not needed *)

Lemma semax_extract_prop:
  forall Delta G (PP: Prop) P c Q, 
           typecheck_stmt Delta c = true ->
           (PP -> semax Hspec Delta G P c Q) -> 
           semax Hspec Delta G (fun rho => !!PP && P rho) c Q.
Proof.
intros.
split.
apply prove_some_static_thing.
intro w.
rewrite semax_fold_unfold.
intros gx w' ? ? k F w'' ? ?.
intros rho w''' ? w4 ? [[? ?] ?].
rewrite sepcon_andp_prop in H8.
destruct H8.
specialize (H0 H8); clear PP H8.
destruct H0.
rewrite semax_fold_unfold in H8.
eapply H8; try apply H2; try apply H4; try eassumption.
split; auto. split; auto.
Qed.

Lemma semax_ff:
  forall Delta G c R,  
   typecheck_stmt Delta c = true -> 
   semax Hspec Delta G (fun rho => FF) c R.
Proof.
intros.
split.
apply prove_some_static_thing.
intro w.
rewrite semax_fold_unfold.
repeat intro.
destruct H6 as [[_ [? [? [_ [_ ?]]]]] _].
contradiction.
Qed.

Lemma semax_unfold:
  semax Hspec = fun Delta G P c R =>
    some_static_thing Delta c /\ 
    forall (psi: Clight.genv) (w: nat) (Prog_OK: believe Hspec G psi G w) (k: cont) (F: assert),
        closed_wrt_modvars c F ->
       rguard Hspec psi Delta G F R k w ->
       guard Hspec psi Delta G (fun rho => F rho * P rho) (Kseq c :: k) w.
Proof.
unfold semax; rewrite semax_fold_unfold.
extensionality Delta G P; extensionality c R.
f_equal.
apply prop_ext; split; intros.
eapply (H w); eauto.
split; auto.
intros psi w' ? ? k F w'' ? [? ?].
eapply H; eauto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall ek vl rho, R' ek vl rho |-- R ek vl rho) ->
   semax Hspec Delta G P c R' ->  semax Hspec Delta G P c R.
Proof.
unfold semax.
intros.
destruct H0; split; auto; intros.
spec H1 n.
revert n H1.
apply semax'_post.
auto.
Qed.

Lemma semax_pre:
 forall P' Delta G P c R,
   (forall rho, typecheck_environ rho Delta = true ->  P  rho |-- P' rho) ->
     semax Hspec Delta G P' c R  -> semax Hspec Delta G P c R.
Proof.
unfold semax.
intros.
destruct H0 as [TC H0]; split; intros; auto.
spec H0 n.
revert n H0.
apply semax'_pre.
auto.
Qed.

Lemma semax_pre_post:
 forall P' (R': ret_assert) Delta G P c (R: ret_assert) ,
   (forall rho,  typecheck_environ rho Delta = true ->  P rho |-- P' rho ) ->
   (forall ek vl rho , R' ek vl rho |-- R ek vl rho) ->
   semax Hspec Delta G P' c R' ->  semax Hspec Delta G P c R.
Proof.
intros.
eapply semax_pre; eauto.
eapply semax_post; eauto.
Qed.

Lemma semax_Sskip:
   forall Delta G P, semax Hspec Delta G P Sskip (normal_ret_assert P).
Proof.
intros.
apply derives_skip.
intros. 
unfold normal_ret_assert.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
auto.
Qed.

Fixpoint list_drop (A: Type) (n: nat) (l: list A) {struct n} : list A :=
  match n with O => l | S i => match l with nil => nil | _ :: l' => list_drop A i l' end end.
Implicit Arguments list_drop.

Definition straightline (c: Clight.statement) :=
 forall ge ve te k m ve' te' k' m',
        cl_step ge (State ve te (Kseq c :: k)) m (State ve' te' k') m' ->  k=k'.

Lemma straightline_assign: forall e0 e, straightline (Clight.Sassign e0 e).
Proof.
unfold straightline; intros.
inv H; auto.
Qed.


Lemma extract_exists:
  forall  (A : Type) (any: A) (P : A -> assert) c Delta G (R: A -> ret_assert),
  (forall x, semax Hspec Delta G (P x) c (R x)) ->
   semax Hspec Delta G (fun rho => exp (fun x => P x rho)) c (existential_ret_assert R).
Proof.
rewrite semax_unfold in *.
intros.
split.
destruct (H any); auto.
intros.
intros rho ?w ? ?w ? ?.
rewrite exp_sepcon2 in H4.
destruct H4 as [[TC [x H5]] ?].
specialize (H x). destruct H as [TC2 H].
specialize (H psi w Prog_OK k F H0).
spec H.
clear - H1.
unfold rguard in *.
intros ek vl rho; specialize (H1 ek vl rho).
red in H1. 
eapply subp_trans; [| apply H1 ].
apply derives_subp.
apply andp_derives; auto.
apply andp_derives; auto.
(* apply later_derives. *)
apply sepcon_derives; auto.
intros ? ?.
exists x; auto.
eapply H; eauto.
split; auto.
split; auto.
Qed.

Lemma extract_exists_pre:
      forall
        (A : Type) (any: A) (P : A -> assert) (c : Clight.statement)
         Delta (G : funspecs) (R : ret_assert),
       (forall x : A, semax Hspec Delta G (P x) c R) ->
       semax Hspec Delta G (fun rho => exp (fun x => P x rho)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R)).
intros ek vl rho w ?.
simpl in H0. destruct H0; auto.
apply extract_exists; auto.
Qed.

Definition G0: funspecs := nil.

Definition empty_genv : Clight.genv :=
  Genv.globalenv (AST.mkprogram (F:=Clight.fundef)(V:=type) nil ( 1%positive) nil).

Lemma empty_program_ok: forall ge w, believe Hspec G0 ge G0 w.
Proof.
intros ge w.
intro b.
intros fsig A P Q.
intros ?n ? ?.
destruct H0 as [id [? [b0 [? ?]]]].
inv H0.
Qed.

Definition all_assertions_computable  :=
  forall psi (Q: assert), exists k,  assert_safe Hspec psi k = Q.
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
eapply join_com; eauto.
auto.
exists w; exists w; split; auto.
change (identity w) in H.
rewrite identity_unit_equiv in H; auto.
Qed.

Lemma semax_extensionality1:
  forall Delta G (P P': assert) c (R R': ret_assert) ,
       ((All ek: exitkind, All  vl : list val, All rho: environ,  (R ek vl rho >=> R' ek vl rho))
      && (All rho:environ, P' rho >=> P rho)  && (semax' Hspec Delta G P c R) |-- semax' Hspec Delta G P' c R').
Proof.
intros.
intros ? ?.
destruct H as [[H ?] ?].
rewrite semax_fold_unfold; rewrite semax_fold_unfold in H1.
intros gx ?w ?.
specialize (H1 gx _ H2).
apply (pred_nec_hereditary _ _ _ H2) in H.
apply (pred_nec_hereditary _ _ _ H2) in H0.
clear H2 a.
intros.
specialize (H1 H2).
intros st F ? ? ?.
specialize (H1 st F _ H3).
spec H1.
destruct H4; split; auto.
intros ek vl rho. specialize (H5 ek vl rho).
eapply subp_trans; try apply H5.
apply andp_subp; auto.
apply andp_subp; auto.
(* apply subp_later; auto with typeclass_instances. *)
specialize (H ek vl rho).
apply (pred_nec_hereditary _ _ _ H3) in H.
clear - H.
revert a' H.
(* apply box_derives. *)
intros w ?.
apply sepcon_subp;  auto.

apply (pred_nec_hereditary _ _ _ H3) in H0.
clear - H1 H0.
intro rho; specialize (H1 rho); specialize (H0 rho).
eapply subp_trans; try apply H1. clear H1.
apply andp_subp; auto.
apply andp_subp; auto.
apply sepcon_subp; auto.
Qed.

Lemma believe_cons:
  forall gx G P Q st, believe Hspec gx G (P::Q) st -> believe Hspec gx G Q st.
Proof.
unfold believe; intros.
intros id fsig A P0 Q0; spec H id fsig A P0 Q0.
intros ? ? ?. apply (H _ H0).
destruct H1 as [id' [? [b [? ?]]]].
exists id'; split; auto.
right; auto.
exists b; split; auto.
Qed.

Lemma frame_left:  forall Delta G P s R F,
   closed_wrt_modvars s F ->
  semax Hspec Delta G P s R ->
    semax Hspec Delta G (fun rho => P rho * F rho) s (frame_ret_assert R F).
Proof.
intros until F. intros CL H.
rewrite semax_unfold.
rewrite semax_unfold in H.
destruct H as [TC H]; split; auto; intros.
pose (F0F := fun rho => F0 rho * F rho).
specialize (H psi w Prog_OK k F0F).
spec H.
unfold F0F.
clear - H0 CL.
hnf in *; intros; simpl in *.
rewrite <- CL. rewrite <- H0. auto.
intuition.
intuition.
replace (fun rho : environ => F0 rho * (P rho * F rho))
  with  (fun rho : environ => F0F rho * P rho).
apply H.
unfold F0F; clear - H1.
intros ek vl rho; specialize (H1 ek vl rho).
red in H1.
replace (F0 rho * F rho * R ek vl rho) with (F0 rho * (frame_ret_assert R F) ek vl rho); auto.
clear.
unfold frame_ret_assert.
rewrite sepcon_assoc; auto.
f_equal. apply sepcon_comm.
unfold F0F.
extensionality rho.
rewrite sepcon_assoc.
f_equal. apply sepcon_comm.
Qed.

Lemma assert_safe_last:
  forall ge st rho w,
   (forall w', age w w' -> assert_safe Hspec ge st rho w) ->
    assert_safe Hspec ge st rho w.
Proof.
intros.
case_eq (age1 w). auto.
clear H.
repeat intro.
rewrite (af_level1 age_facts) in H.
rewrite H. simpl.
hnf. auto.
Qed.

Lemma age_laterR {A} `{ageable A}: forall {x y}, age x y -> laterR x y.
Proof.
intros. constructor 1; auto.
Qed.
Hint Resolve @age_laterR.

Lemma pred_sub_later' {A} `{H: ageable A} {SS: natty A}:
  forall (P Q: pred A),  
           (|> P >=> |> Q)  |--  (|> (P >=> Q)).
Proof.
intros.
rewrite later_fash; auto.
rewrite later_imp.
auto.
Qed.

Lemma later_strengthen_safe1:  
  forall (P: pred rmap) ge k rho,
              ((|> P) >=> assert_safe Hspec ge k rho) |--   |>  (P >=> assert_safe Hspec ge k rho).
Proof.
intros.
intros w ?.
apply (@pred_sub_later' _ _ natty_rmap P  (assert_safe Hspec ge k rho)); auto.
eapply subp_trans; try apply H.
apply derives_subp; clear.
intros w0 ?.
intros w' ?.
simpl in H0.
revert H; induction H0; intros.
simpl in *; intros.
subst y. change (level (m_phi jm)) with (level jm).
generalize (oracle_unage _ _ H); intros [jm0 [? ?]]. subst x.
eapply age_safe; try eassumption.
specialize (H0 ora jm0 (eq_refl _)).
apply H0.
apply IHclos_trans2.
eapply pred_nec_hereditary; eauto.
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
  intros. rewrite andp_com. apply FF_and.
Qed.

Lemma sepcon_FF : forall {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A} (P:pred A),
  (P * FF = FF)%pred.
Proof.
  intros. rewrite sepcon_comm. apply FF_sepcon.
Qed.

Section extensions.

Context {Z} (Hspec : juicy_ext_spec Z).

Lemma age1_resource_decay:
  forall jm jm', age jm jm' -> resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
 intros. split.
 apply age_level in H.
 change (level (m_phi jm)) with (level jm).
 change (level (m_phi jm')) with (level jm').  
 omega.
 intro l. split. apply juicy_mem_alloc. left.
 symmetry; apply age1_resource_at with (m_phi jm); eauto.
  destruct (age1_juicy_mem_unpack _ _ H); auto.
 apply resource_at_approx.
Qed.

Lemma safe_loop_skip:
  forall 
    ge ora ve te k m,
    jsafeN Hspec ge (level m) ora (State ve te (Kseq (Swhile true_expr Clight.Sskip) :: k)) m.
Proof.
  intros.
  remember (level m)%nat as N.
  destruct N; simpl; auto.
  case_eq (age1 m); [intros m' ? |  intro; apply age1_level0 in H; omegaContradiction].
  exists (State ve te (Kseq Sskip :: Kseq Scontinue :: Kfor2 true_expr Sskip Sskip :: k)), m'.
  split.
  split3.
  repeat constructor.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  change (Kseq Sskip :: Kseq Scontinue :: Kfor2 true_expr Sskip Sskip :: k)
          with (if true then Kseq Sskip :: Kseq Scontinue :: Kfor2 true_expr Sskip Sskip :: k else k).
  repeat econstructor.
 apply age1_resource_decay; auto. apply age_level; auto.
  assert (N = level m')%nat.
  apply age_level in H; omega.
  clear HeqN m H. rename m' into m.
  revert m H0; induction N; intros; simpl; auto.
  case_eq (age1 m); [intros m' ? |  intro; apply age1_level0 in H; omegaContradiction].
  exists (State ve te (Kseq Sskip :: Kseq Scontinue :: Kfor2 true_expr Sskip Sskip :: k)), m'.
  split.
  split3.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  repeat constructor.
  change (Kseq Sskip :: Kseq Scontinue :: Kfor2 true_expr Sskip Sskip :: k)
          with (if true then Kseq Sskip :: Kseq Scontinue :: Kfor2 true_expr Sskip Sskip :: k else k).
  repeat econstructor.
 apply age1_resource_decay; auto. apply age_level; auto.
  eapply IHN; eauto. 
  apply age_level in H. omega.
Qed.

Lemma safe_step_forward:
  forall psi n ora st m,
   cl_at_external st = None ->
   j_safely_halted cl_core_sem psi st m  = None ->
   jsafeN Hspec psi (S n) ora st m ->
 exists st', exists m',
   jstep cl_core_sem psi st m st' m' /\
   jsafeN Hspec psi n ora  st' m'.
Proof.
 intros. simpl in H1. rewrite H in H1.
 destruct H1 as [c' [m' [? ?]]].
 exists c'; exists m'; split; auto.
Qed.

Lemma safeN_strip:
  forall ge n ora ve te k m,
     jsafeN Hspec ge n ora (State ve te (strip_skip k)) m =
     jsafeN Hspec ge n ora (State ve te k) m.
Proof.
 intros.
 destruct n. apply prop_ext; simpl; intuition.
 simpl.
 apply exists_ext; intro c'. 
 apply exists_ext; intro m'.
 f_equal.
 induction k; simpl; auto.
 destruct a; simpl; auto.
 destruct (dec_skip s).
 subst. rewrite IHk.
 clear IHk.
 apply prop_ext; split; intros [? [? ?]]; split3; auto.
 constructor; auto.
  inv H; auto.
 destruct s; simpl; auto.
 congruence.
Qed.

Open Local Scope nat_scope.

Definition control_as_safe ge n ctl1 ctl2 := 
 forall (ora : Z) (ve : env) (te : temp_env) (m : juicy_mem) (n' : nat),
     n' <= n ->
     jsafeN Hspec ge n' ora (State ve te ctl1) m ->
     jsafeN Hspec ge n' ora (State ve te ctl2) m.

Fixpoint prebreak_cont (k: cont) : cont :=
  match k with
  | Kfor2 e2 e3 s :: k' => k
  | Kseq s :: k' => prebreak_cont k'
  | Kfor3 e2 e3 s :: _ => nil  (* stuck *)
  | Kswitch :: k' => k
  | _ =>  nil (* stuck *)
  end.

Lemma prebreak_cont_is: forall k,
  match (prebreak_cont k) with
  | Kfor2 _ _ _ :: _ => True
  | Kswitch :: _ => True
  | nil => True
  | _ => False
  end.
Proof.
induction k; simpl; auto.
destruct (prebreak_cont k); try contradiction; destruct a; auto.
Qed.

Lemma corestep_preservation_lemma:
   forall ge ctl1 ctl2 ora ve te m n c l c' m',
       filter_seq ctl1 = filter_seq ctl2 ->
      (forall k : list cont', control_as_safe ge n (k ++ ctl1) (k ++ ctl2)) ->
      control_as_safe ge (S n) ctl1 ctl2 ->
      jstep cl_core_sem ge (State ve te (c :: l ++ ctl1)) m c' m' ->
      jsafeN Hspec ge n ora c' m' ->
   exists c2 : corestate,
     exists m2 : juicy_mem,
       jstep cl_core_sem ge (State ve te (c :: l ++ ctl2)) m c2 m2 /\
       jsafeN Hspec ge n ora c2 m2.
Proof. intros until m'. intros H0 H4 CS0 H H1.
  remember (State ve te (c :: l ++ ctl1)) as q. rename c' into q'.
  destruct H as [H [Hb Hc]].
  remember (m_dry m) as dm; remember (m_dry m') as dm'.
  revert c l m Heqdm m' Heqdm' Hb Hc H1 Heqq; induction H; intros; try inv Heqq.
  (* assign *)
  do 2 eexists; split; [split3; [econstructor; eauto | auto | auto ] | apply H4; auto ].
  (* set *)
  do 2 eexists; split; [split3; [ | eassumption | auto ] | ].
  rewrite <- Heqdm'; econstructor; eauto.
  apply H4; auto. 
  (* call_internal *)
  do 2 eexists; split; [split3; [econstructor; eauto | auto | auto ] |  ].
  do 3 rewrite cons_app'. apply H4; auto.
  (* call_external *) 
Focus 1.
  do 2 eexists; split; [split3; [ | eassumption | auto ] | ].
  rewrite <- Heqdm';  eapply step_call_external; eauto.
  destruct n; auto.
  simpl in H5|-*.
  destruct H5 as [x ?]; exists x.
  intros z' H7; specialize (H5 z' H7).
  destruct H5; split; auto.
  intros ret m'0 z'' H9; specialize (H6 ret m'0 z'' H9).
  destruct H6 as [c' [? ?]].
  unfold cl_after_external in *.
  destruct ret. inv H6.
  destruct ret. destruct optid.
  exists (State ve (PTree.set i v te) (l ++ ctl2)); split; auto.
  inv H6.
  apply H4; auto.
  exists (State ve te (l ++ ctl2)); split; auto.
  inv H6.
  apply H4; auto.
  inv H6.  
  (* sequence  *)
  destruct (IHcl_step (Kseq s1) (Kseq s2 :: l) _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
   destruct H2 as [H2 [H2b H2c]].
  exists c2, m2; split; auto. split3; auto. constructor. apply H2.
  (* skip *)
  destruct l.
    simpl in H.
 assert (jsafeN Hspec ge (S n) ora (State ve te ctl1) m0).
 eapply safe_corestep_backward; eauto; split3; eauto.
 apply CS0 in H2; auto.
  eapply safe_step_forward in H2; auto.
 destruct H2 as [st2 [m2 [? ?]]]; exists st2; exists m2; split; auto.
 simpl.
   destruct H2 as [H2 [H2b H2c]].
  split3; auto.
  rewrite <- strip_step. simpl. rewrite strip_step; auto.
  destruct (IHcl_step c l _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2; exists m2; split; auto.
   destruct H2 as [H2 [H2b H2c]].
 simpl.
  split3; auto.
  rewrite <- strip_step.
 change (strip_skip (Kseq Sskip :: c :: l ++ ctl2)) with (strip_skip (c::l++ctl2)).
  rewrite strip_step; auto.
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
  destruct (IHcl_step _ _ _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2,m2; split; auto. 
   destruct H5 as [H5 [H5b H5c]].
 split3; auto.
 constructor. rewrite H3; auto.
  (* break *)
Focus 1.  
  case_eq (prebreak_cont l); intros.
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
  assert (PB:= prebreak_cont_is l); rewrite H2 in PB.
  destruct c; try contradiction.
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (forward_simulations.corestep (juicy_core_sem cl_core_sem) ge (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (safe_corestep_backward (juicy_core_sem cl_core_sem) Hspec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (forward_simulations.corestep (juicy_core_sem cl_core_sem) ge (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (safe_corestep_backward (juicy_core_sem cl_core_sem) Hspec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  (* ifthenelse *) 
  exists (State ve te (Kseq (if b then s1 else s2) :: l ++ ctl2)), m'.
  split. split3; auto. rewrite <- Heqdm'. econstructor; eauto.
  rewrite cons_app. rewrite <- app_ass.
  apply H4; auto.
  (* while *)
  inv H.
  exists (State ve te
          (if b
           then Kseq s :: Kseq Scontinue :: Kfor2 a Sskip s :: l ++ ctl2
           else l ++ ctl2)), m'0.
  split.
  split3; auto. constructor. rewrite <- H12; econstructor; eauto.
  destruct b.
 change (Kseq s :: Kseq Scontinue :: Kfor2 a Sskip s :: l ++ ctl2)
    with ((Kseq s :: Kseq Scontinue :: Kfor2 a Sskip s :: l)  ++ ctl2).
 apply H4; auto. apply H4; auto.
 (* dowhile *)
   destruct (IHcl_step (Kseq s) (Kseq Scontinue :: Kfor2 a Sskip s :: l) _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) 
             as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2,m2; split; auto. 
   destruct H2 as [H2 [H2b H2c]].
  split3; auto. constructor. auto.
  (* for *)
  assert (jsafeN Hspec ge n ora
                 (State ve te ((if b then Kseq s :: Kseq Scontinue :: Kfor2 a2 a3 s :: l else l) ++ ctl1)) m').
 destruct b; auto.
 apply H4 in H3; auto.
  do 2 eexists; split; eauto.
  assert (jstep cl_core_sem ge (State ve te (Kseq (Sfor' a2 a3 s) :: l ++ ctl2)) m0
  (State ve te
     (if b then Kseq s :: Kseq Scontinue :: Kfor2 a2 a3 s :: l ++ ctl2 else l ++
      ctl2)) m').
   split3; auto. rewrite <- Heqdm'.
  econstructor; eauto. destruct b; auto.
  (* for3 *)
  assert (jsafeN Hspec ge n ora
       (State ve te
          ((if b
           then Kseq s :: Kseq Scontinue :: Kfor2 a2 a3 s :: l else l) ++ ctl1)) m').
  destruct b; auto.
 apply H4 in H3; auto.
  do 2 eexists; split; eauto.
 assert (jstep cl_core_sem ge (State ve te (Kfor3 a2 a3 s :: l ++ ctl2)) m0
  (State ve te
     (if b then Kseq s :: Kseq Scontinue :: Kfor2 a2 a3 s :: l++ctl2 else l ++ctl2)) m').
  split3; auto. rewrite <- Heqdm'.  econstructor; eauto.
  destruct b; auto.
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
  apply H4; auto.
 (* switch *)
  do 2 eexists; split; [split3; [| eauto | eauto] | ].
  rewrite <- Heqdm'. econstructor; eauto.
  do 2 rewrite cons_app'. apply H4; auto.
 (* label *)
  destruct (IHcl_step _ _  _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
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
  rewrite <- (filter_seq_call_cont ctl1 ctl2 H0); auto.
  rewrite (call_cont_app_cons _ _ _ H2) in H.
  assert (exists j, k' = j ++ ctl1).
  clear - H2 H.
  admit. (* true and provable *)
  destruct H3 as [j ?].
  subst k'.
  exists (State ve te (j++ctl2)), m'; split; [ | apply H4; auto].
  split3; auto.
  rewrite <- Heqdm'; econstructor. 
  instantiate (1:=f).
  admit.  (* easy *)
  rewrite (call_cont_app_cons _ _ _ H2).
  clear - H2 H.
  admit.  (* true and provable *)
Qed.

Lemma control_as_safe_le:
  forall n' n ge ctl1 ctl2, n' <= n -> control_as_safe ge n ctl1 ctl2 -> control_as_safe ge n' ctl1 ctl2.
Proof.
 intros. intro; intros. eapply H0; auto; omega.
Qed.

Lemma control_suffix_safe :
    forall
      ge n ctl1 ctl2 k,
      filter_seq ctl1 = filter_seq ctl2 ->
      control_as_safe ge n ctl1 ctl2 ->
      control_as_safe ge n (k ++ ctl1) (k ++ ctl2).
  Proof.
    intro ge. induction n using (well_founded_induction lt_wf).
    intros. hnf; intros.
    destruct n'; [ simpl; auto | ].
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
   hnf in H3|-*.
   destruct H3 as [c' [m' [? ?]]].
  eapply corestep_preservation_lemma; eauto.
   eapply control_as_safe_le; eauto.
 apply H3.
Qed.


Lemma guard_safe_adj:
 forall 
   psi Delta G P k1 k2,
  (forall ora m ve te n,
     jsafeN Hspec psi n ora (State ve te k1) m -> 
     jsafeN Hspec psi n ora (State ve te k2) m) ->
  guard Hspec psi Delta G P k1 |-- guard Hspec psi Delta G P k2.
Proof.
intros.
unfold guard.
apply allp_derives. intro rho.
apply subp_derives; auto.
intros w ? ? ? ?.
apply H.
eapply H0; eauto.
Qed.

Lemma assert_safe_adj:
  forall ge k k' rho, 
      (forall n, control_as_safe ge n k k') ->
     assert_safe Hspec ge k rho |-- assert_safe Hspec ge k' rho.
Proof.
 intros. intros w ? ? ? ?. specialize (H0 ora jm H1).
 eapply H; try apply H0. apply le_refl.
Qed.

Lemma assert_safe_adj':
  forall ge k k' rho P w, 
      (forall n, control_as_safe ge n k k') ->
     app_pred (P >=> assert_safe Hspec ge k rho) w ->
     app_pred (P >=> assert_safe Hspec ge k' rho) w.
Proof.
 intros.
 eapply subp_trans; [ | apply derives_subp; eapply assert_safe_adj; try eassumption; eauto].
 auto.
Qed.

Lemma rguard_adj:
  forall ge Delta G F R k k',
      (forall ek vl n, control_as_safe ge n (exit_cont ek vl k) (exit_cont ek vl k')) ->
      rguard Hspec ge Delta G F R k |-- rguard Hspec ge Delta G F R k'.
Proof.
 intros.
 intros n H0;  hnf in H0|-*.
 intros ek vl rho; specialize (H0 ek vl rho).
 eapply assert_safe_adj'; eauto.
Qed.


Lemma assert_safe_last': forall {Z} (Hspec: juicy_ext_spec Z) ge ctl rho w,
            (age1 w <> None -> assert_safe Hspec ge ctl rho w) ->
             assert_safe Hspec ge ctl rho w.
Proof.
 intros. apply assert_safe_last; intros. apply H. rewrite H0. congruence.
Qed.

Lemma pjoinable_emp_None {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall w: option (lifted JA), identity w ->  w=None.
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
           identity (None: option (lifted JA)).
Proof.
intros; intro; intros.
inv H; auto.
Qed.

Lemma unage_mapsto':
  forall sh e v rho w, age1 w <> None -> (|> mapsto' sh e v rho) w -> mapsto' sh e v rho w.
Proof.
 intros.
 case_eq (age1 w); intros; try contradiction.
 clear H.
 specialize (H0 _ (age_laterR H1)).
 unfold mapsto' in *.
 revert H0; case_eq (access_mode (typeof e)); intros; auto.
 destruct (eval_lvalue rho e); try contradiction.
 rename H into Hmode.
 destruct H0 as [bl [? ?]]; exists bl; split; auto.
 clear - H0 H1.
  intro loc'; specialize (H0 loc').
  hnf in *.
  if_tac.
  destruct H0 as [p ?]; exists p.
  hnf in *.
  rewrite preds_fmap_NoneP in *.
  apply (age1_YES w r); auto.
  unfold noat in *; simpl in *.
 eapply unage1_resource_at_identity; eauto.
Qed.

End extensions.

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ | Tfloat _ _ => true
  | _ => false
  end.

Definition Cnot (e: Clight.expr) : Clight.expr :=
   Clight.Eunop Onotbool e type_bool.

Lemma bool_val_Cnot:
  forall rho a b, 
    bool_type (typeof a) = true ->
    bool_val (eval_expr rho a) (typeof a) = Some b ->
    bool_val (eval_expr rho (Cnot a)) (typeof (Cnot a)) = Some (negb b).
Proof.
 intros.
 unfold Cnot. simpl.
 destruct (eval_expr rho a);   try solve [inv H0];
 simpl in H0; 
 revert H H0; case_eq (typeof a); intros; inv H1; inv H0;
   try rewrite negb_involutive;
 unfold sem_notbool, classify_bool, Val.of_bool; 
 try (destruct i0; simpl; auto);
 try (destruct s; simpl; auto);
 try (destruct (Int.eq i Int.zero); auto).
 simpl. destruct (Float.cmp Ceq f Float.zero); auto.
Qed.
