Require Import msl.examples.cont.language.
Require Import msl.examples.cont.sep_base.
Require Import msl.msl_standard.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import msl.Coqlib2.

Obligation Tactic := idtac.

Local Open Scope pred.

Hint Extern 3 (list_nodups _ = true) => (compute; reflexivity).
Hint Extern 3 (typecheck _ _ = true) => (compute; reflexivity).
Hint Extern 3 (expcheck _ _ = true) => (compute; reflexivity).
Hint Resolve andb_true_intro.

Module Type SEMAX.

  Parameter semax : varset -> funspecs -> assert -> control -> Prop.
  Parameter semax_func: forall (G: funspecs) (p: program) (G': funspecs), Prop.

Axiom semax_func_nil: forall G, semax_func G nil nil.
Axiom semax_func_cons: 
   forall  fs id f vars P (G G': funspecs),
      inlist id (map (@fst adr (list var * control)) fs) = false ->
      list_nodups vars = true ->
      length vars = length (fst P) ->
      semax vars G (fun s => call P (map s vars)) f ->
      semax_func G fs G' ->
      semax_func G ((id, (vars,f))::fs) ((id, P) :: G').

Definition program_proved (p: program) :=
   exists G, semax_func G p G 
                            /\ table_get G 0 = Some  (0::nil, fun s => allocpool (eval (Var 0) s)).

Axiom semax_sound: 
  forall p, program_proved p -> forall n, run p n <> None.

Axiom semax_go:  forall vars G (P: funspec) x ys,   
    typecheck vars (Go x ys) = true ->
    semax vars G (fun s => cont P (eval x s) && call P (eval_list ys s)) (Go x ys) .

Axiom semax_assign: forall x y c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c -> 
    semax vars G (fun s => |> subst x (eval y s) P s) (Do x := y ; c). 

Axiom semax_if: forall x c1 c2 vars G (P: assert),
    expcheck vars x = true ->
    semax vars G (fun s => !!(eval x s <> 0) && P s) c1 ->
    semax vars G (fun s => !! (eval x s = 0) && P s) c2 ->
    semax vars G (fun s => P s) (If x Then c1 Else c2).

Axiom semax_load:  forall x y z c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c -> 
    semax vars G (fun s => (mapsto (eval y s) z * TT) && |> subst x z P s)
               (Do x := Mem y ; c).

Axiom semax_store: forall x y v c vars G (P: assert),
    expcheck vars x = true ->
    expcheck vars y = true ->
    semax vars G (fun s => mapsto (eval x s) (eval y s) * P s) c ->
    semax vars G (fun s => mapsto (eval x s) v  * P s)  (Do Mem x  := y ; c).

Axiom semax_pre: 
  forall P P' vars G c, (forall s, P s |-- P' s) -> semax vars G P' c -> semax vars G P c.

Axiom semax_exp: forall A vars G (P: A -> assert) c,
    typecheck vars c = true ->
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => Ex v:A, (P v s)) c.

Axiom semax_exp': forall A (any: A) vars G (P: A -> assert) c,
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => Ex v:A, (P v s)) c.

Axiom semax_prop:
  forall (R: Prop) vars G P c,
      typecheck vars c = true ->
      (R -> semax vars G P c) ->
      semax vars G (fun s => !! R && P s) c.

Axiom semax_G:
   forall vars G P c, semax vars G (fun s => P s && funassert G) c -> semax vars G P c.


End SEMAX.

Module Semax : SEMAX.

Local Open Scope pred.

Definition guard (p: program) (G: funspecs) (vars: varset) (P : assert) (k: control) : pred nat :=
     All s:env, P s && funassert G >=> assert_safe p vars k s.

Record semaxArg :Type := SemaxArg {
 sa_vars: varset;
 sa_P: assert;
 sa_c: control
}.

Definition believe (semax: semaxArg -> pred nat) 
      (p: program) (P: funspec) (f: adr) : pred nat :=
      Ex k: list var * control, 
        !!(table_get p f = Some k /\ length (fst k) = length (fst P) /\ list_norepet (fst k)) &&
      |> semax (SemaxArg (fst k) (fun s => call P (map s (fst k))) (snd k)).

Definition believe_all (semax: semaxArg -> pred nat) (G: funspecs) (p: program) (G': funspecs) : pred nat :=
  All v:adr, All args: list var, All P: assert,
     !! (table_get G' v = Some (args,P)) -->
     believe semax p (args, fun s => P s && funassert G) v.

Definition semax_ (semax: semaxArg -> pred nat) (a: semaxArg) : pred nat :=
 match a with SemaxArg vars P c =>
     All p: program, All G: funspecs, believe_all semax G p G --> guard p G vars P c
  end.

Lemma prop_imp {A}{agA: ageable A}: 
  forall (P: Prop) (Q: pred A) w, (P -> app_pred Q w) -> app_pred (!!P --> Q) w.
Proof. repeat intro. specialize (H H1). eapply pred_nec_hereditary; eauto.
Qed.


Lemma HOcontractive_semax_ : HOcontractive semax_.
Proof.
  auto 50 with contractive.
Qed.

Definition semax'  := HORec semax_.

Lemma semax'_unfold: forall vars P c,
     semax' (SemaxArg vars P c) = 
         All p: program, All G:funspecs, believe_all semax' G p G --> guard p G vars P c.
Proof.
  intros. 
  unfold semax' at 1. rewrite HORec_fold_unfold; auto.
  apply HOcontractive_semax_.
Qed.

Definition semax vars (G: funspecs) (P: assert) (k: control) : Prop := 
       typecheck vars k = true /\ forall n,  semax' (SemaxArg vars (fun s => P s && funassert G) k) n.

Definition semax_func (G: funspecs) (p: program) (G': funspecs) :=
    match_specs p G' /\ 
    forall n, believe_all semax' G p G' n.

Lemma semax_func_nil: forall G, semax_func G nil nil.
Proof. split; repeat intro. constructor. inv H0. Qed.

Lemma semax_func_cons: 
   forall  fs id f vars P (G G': funspecs),
      inlist id (map (@fst adr (list var * control)) fs) = false ->
      list_nodups vars = true ->
      length vars = length (fst P) ->
      semax vars G (fun s => call P (map s vars)) f ->
      semax_func G fs G' ->
      semax_func G ((id, (vars,f))::fs) ((id, P) :: G').
Proof.
intros until G'. intros H0 H Hlen ? ?.
apply inlist_notIn in H0.
destruct H2.
split.
constructor; auto.
destruct H1; auto.
intro.
specialize (H3 n).
intros b nargs' Q.
specialize (H3 b nargs' Q).
intros ? ? ?.
destruct (eq_dec id b).
subst.
Focus 2.
specialize (H3 _ H4).
spec H3.
clear - H5 n0.
hnf in H5|-*.
unfold table_get  in H5; fold @table_get in H5.
rewrite if_false in H5; auto.
clear H5.
destruct H3 as [k [? ?]]; exists k; split; auto.
unfold table_get; fold @table_get.
rewrite if_false; auto.
(* End Focus 2 *)
unfold table_get in H5; fold @table_get in H5.
rewrite if_true in H5; auto.
simpl in H5.
inv H5.
exists (vars,f).
split.
simpl.
rewrite if_true; auto. split; auto. split; auto. apply nodups_norepet. auto.
simpl fst; simpl snd.
hnf; intros.
destruct H1 as [_ H1].
specialize (H1 a'0).
replace (fun s : env =>
           call (nargs', fun s0 : env => Q s0 && funassert G) (map s vars))
 with (fun s : env => call (nargs', Q) (map s vars) && funassert G).
apply H1.
extensionality s. forget (map s vars) as vl.
clear.
apply pred_ext; intros ? ?.
destruct H as [[? ?] ?].
split. apply H. simpl snd in *. split; auto.
destruct H. simpl fst in *; simpl snd in *.
destruct H0; split; auto. split; auto.
Qed.

Lemma semax_G:
   forall vars G P c, semax vars G (fun s => P s && funassert G) c -> semax vars G P c.
Proof. 
  intros. destruct H; split; auto.
  intro; specialize (H0 n).
  replace (fun s : env => P s && funassert G) with (fun s : env => P s && funassert G && funassert G);
       auto.
  extensionality s.
  rewrite andp_assoc. f_equal. apply andp_dup.
Qed.

Lemma semax_go:  forall vars G (P: funspec) x ys,   
    typecheck vars (Go x ys) = true ->
    semax vars G (fun s => cont P (eval x s) && call P (eval_list ys s)) (Go x ys) .
Proof.
 intros. rename H into TC.
  split; auto.
   intro n; hnf.
   rewrite semax'_unfold.
  intros p G0.
  hnf. intros n' ? ?.
  clear n H.
  intros s w ? w' ?.
  rewrite andp_assoc.
  intros [[H4 H5] [_ GUARDIAN]].
  pose (H3:=True).
  clear G. rename G0 into G.
  remember (eval x s) as v'.
  destruct (funassert_get G v' P w') as [P' [H2 H2']].
  split; auto.
  generalize (H0 _ _ _ _ (necR_refl _) H2'); intro. clear H2'.
  destruct H6 as [[formals k] [[H6 [H6' H6'']] ?]]. 
  hnf in H6.
 rewrite semax'_unfold in H7.
  apply assert_safe0; intros w'' Hw''.
  assert (LATER: laterR n' (level w'')).
    apply later_nat; apply necR_level in H1; apply age_level in Hw''.
   unfold R.rmap in *; omega. specialize (H2 (eval_list ys s)).
  red in H2. red in H2. red in H2.
  specialize (H2 _ (t_step _ _ _ _ Hw'' )).
  specialize (H7 _ LATER).
  apply (pred_nec_hereditary _ _ _ (laterR_necR LATER)) in H0.
  specialize (H7 p G _ (necR_refl _) H0). clear H0.
  simpl fst in *. simpl snd in *.
  do 3 red in H2.
  apply (pred_hereditary _ _ _ Hw'') in H5.
  specialize (H2 _ (le_refl _)).
  specialize (H7 (locals2env (mk_locals formals (eval_list ys s))) _ (le_refl _) _ (necR_refl _)).
  clear n' H LATER.
  intros ? ? VC L H. rewrite <- L in *. clear L s. rename s' into s.
  assert (step p (s,h, Go x ys) = Some ((mk_locals formals (eval_list ys (locals2env s)), h), k)).
  simpl.
  simpl typecheck in TC.
  rewrite andb_true_iff in TC; destruct TC as [TC1 TC2].
  rewrite (eval_expr_get vars s h x); auto. rewrite <- Heqv'.
  simpl. rewrite H6.  simpl. 
  rewrite (eval_expr_get_list vars s h ys); auto.
  rename Hw'' into H12.
  rewrite (age_level _ _ H12).
  rewrite (safeN_step _ _ _ _ H0).
  clear w H1.
  pose (H11:=True).
  spec H7.
  eapply pred_hereditary in GUARDIAN; eauto.
  split; auto.
  split.
  hnf. rewrite map_length. simpl fst. auto.
  split; auto.
  destruct H2 as [? _]. 
  specialize (H1 _ (necR_refl _) H5).
  simpl.
  unfold call in H1. simpl in H1.
  Transparent arguments.
  unfold arguments in *.
  Opaque arguments.
  replace (map (locals2env (mk_locals formals (eval_list ys (locals2env s)))) formals)
     with (eval_list ys (locals2env s)); [ apply H1 | ].
  destruct H5 as [Hlen H5]. hnf in Hlen.
  assert (length (eval_list ys (locals2env s)) = length formals).
    rewrite H6'. auto.
  forget (eval_list ys (locals2env s)) as vs.
  clear - H2 H6''.
  revert vs H2; induction H6''; intros; destruct vs; inv H2; simpl; auto.
  f_equal. unfold locals2env; simpl. rewrite if_true by auto. auto.
 pattern vs at 1; rewrite (IHH6'' vs) by auto.
 forget (mk_locals tl vs) as y.
 clear - H. induction tl; simpl; auto. f_equal; simpl.
 unfold locals2env; simpl.
 rewrite if_false by (contradict H; simpl in *; intuition). auto.
 apply IHtl. intuition.
  apply H7; auto.
  apply varcompat_mk_locals. unfold eval_list. rewrite map_length. rewrite H6'; auto.
  destruct H5 as [H5 _]; hnf in H5.
  rewrite <- H5.
  clear. induction ys; simpl; omega.
  eapply pred_hereditary; eauto.
Qed.

Lemma semax_assign: forall x y c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c -> 
    semax vars G (fun s => |> subst x (eval y s) P s) (Do x := y ; c).
Proof.
 intros until P; intros TC [TC' ?].
 split.
 simpl in *. destruct y; inv TC; simpl; auto; try rewrite TC'; try rewrite H1; auto.
 intro; intros.
 unfold subst.
 rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [[H6 H6'] H4].
 pose (H5:=True).
 apply assert_safe0; intros w'' ?.
 intros s' h VC L ?. rewrite <- L in *; clear L s; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H9.
 apply (pred_hereditary _ _ _ H7) in H8.
 specialize (H6 _ (t_step _ _ _ _ H7)).
 apply (pred_hereditary _ _ _ H7) in H4.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 apply (pred_nec_hereditary _ _ _ H10) in H1.
 clear n' w H3 H2 H0 H10.
 hnf in H5.
 assert (step p ((s,h), Do (Var x) := y; c) = Some ((table_set x (eval y (locals2env s)) s, h), c)).
 simpl. rewrite (eval_expr_get vars s h y); auto.
 apply (safeN_step _ _ _ _ H0).
  specialize (H (@level _ ag_rmap w')). rewrite semax'_unfold in H.
 specialize (H p G' _ (necR_refl _) H1).
 specialize (H (locals2env (@table_set var _ EqDec_var x (eval y (locals2env s)) s))).
 specialize (H w''). spec H; [rewrite H9; omega | ].
 specialize (H _ (necR_refl _)).
 spec H. split; auto. 
 replace  (locals2env (table_set x (eval y (locals2env s)) s))
   with (env_set (locals2env s) x (eval y (locals2env s))); auto.
  split; [ auto | eapply pred_hereditary; eauto]. 
  clear.
   extensionality i. unfold env_set. unfold locals2env at 3.
   destruct (eq_dec i x). subst. rewrite table_gss; auto. rewrite table_gso; auto.
 apply H; auto.
  clear - VC.
  intros i ?. destruct (eq_dec i x). subst. rewrite table_gss. congruence.
  rewrite table_gso by auto. apply (VC i).
  unfold vs_mem in H. apply ListSet.set_mem_correct1 in H.
  apply ListSet.set_mem_correct2. unfold vs_add in H.
  apply ListSet.set_add_elim2 in H; auto.
Qed.

Lemma semax_if: forall x c1 c2 vars G (P: assert),
    expcheck vars x = true ->
    semax vars G (fun s => !!(eval x s <> 0) && P s) c1 ->
    semax vars G (fun s => !! (eval x s = 0) && P s) c2 ->
    semax vars G (fun s => P s) (If x Then c1 Else c2).
Proof.
 intros. rename H into TC.
 destruct H0 as [TC0 H]; destruct H1 as [TC1 H'].
 split.
 simpl; auto.
 intro.
 rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [H5 H4].
 pose (H6:=True).
 apply assert_safe0; intros w'' ?.
 intros s' h VC L ?. rewrite <- L in *; clear L s; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H9.
 destruct (eq_dec (eval x (locals2env s)) 0).
 (* zero *)
 clear H; rename H' into H.
 subst.
 assert (step p ((s,h), If x Then c1 Else c2) = Some ((s,h), c2)).
 simpl. rewrite (eval_expr_get vars s h x); auto. rewrite e; simpl; auto.
 apply (safeN_step _ _ _ _ H10).
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H11 (pred_nec_hereditary _ _ _ H11 H1)).
 specialize (H (locals2env s) w'').
 spec H. omega.
 specialize (H _ (necR_refl _)).
 spec H.
  rewrite andp_com.
 split. eapply pred_hereditary; eauto.
 apply (pred_hereditary _ _ _ H7) in H5.
 rewrite andp_assoc; split; [ |  apply H5].
 hnf; auto.
 apply H; auto.
 apply (pred_nec_hereditary _ _ _ (rt_step _ _ _ _ H7)); auto. 
 (* nonzero *)
 subst.
 assert (step p ((s,h), If x Then c1 Else c2) = Some ((s,h), c1)).
 simpl. rewrite (eval_expr_get vars s h x); auto. simpl.  rewrite if_false; auto.
 apply (safeN_step _ _ _ _ H10).
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H11 (pred_nec_hereditary _ _ _ H11 H1)).
 specialize (H (locals2env s) w'').
 spec H. omega.
 specialize (H _ (necR_refl _)).
 spec H.
 rewrite andp_com.
 split. eapply pred_hereditary; eauto.
 apply (pred_hereditary _ _ _ H7) in H5.
 rewrite andp_assoc; split; [ |  apply H5].
 hnf; auto.
 apply H; auto.
 apply (pred_nec_hereditary _ _ _ (rt_step _ _ _ _ H7)); auto. 
Qed.

Lemma semax_load: forall x y z c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c -> 
    semax vars G (fun s => ((mapsto (eval y s) z) * TT) && |> subst x z P s)
               (Do x := Mem y ; c).
Proof.
 intros until P. intros TC [TC' ?].
 split.
 simpl; auto.
 intro n.
 rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [H5 H4].
 destruct H5 as [[? HP] HG].
 unfold subst in HP.
 apply assert_safe0; intros w'' H7.
 specialize (HP _ (t_step _ _ _ _ H7)).
 intros s' h VC L ?. rewrite <- L in *; clear s L; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H8.
 assert (step p ((s,h), Do x := Mem y; c) = Some ((table_set x z s, h), c)).
 simpl. rewrite (eval_expr_get vars s h y); auto. simpl.
 replace (heap_get h (eval y (locals2env s))) with (Some z).
 auto.
 symmetry.
 apply H6. apply mapsto_e1; auto.
 apply (safeN_step _ _ _ _ H9). clear H9.
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H9 (pred_nec_hereditary _ _ _ H9 H1)).
 specialize (H (locals2env (@table_set _ _ EqDec_var x z s)) w'').
 spec H.    unfold R.rmap in *; omega. 
 specialize (H _ (necR_refl _)).
 spec H. split; [split|].
  rewrite locals2env_table_set. eauto.
  eapply pred_hereditary; eauto.
  eapply pred_hereditary; eauto.
 apply H; auto.
 apply varcompat_add; auto.
 eapply pred_hereditary; eauto.
Qed.

Lemma semax_store: forall x y v c vars G (P: assert),
    expcheck vars x = true ->
    expcheck vars y = true ->
    semax vars G (fun s => mapsto (eval x s) (eval y s) * P s) c ->
    semax vars G (fun s => mapsto (eval x s) v  * P s)  (Do Mem x  := y ; c).
Proof.
 intros until P; intros TCx TCy [TC ?].
 split.
 simpl; auto.
 intro. rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [[H5 H6] H4].
 apply assert_safe0; intros w'' ?.
 intros s' h VC L ?. rewrite <- L in *; clear L s; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H9.
 assert (step p ((s,h), Do Mem x := y; c) = Some ((s, heap_set (eval x (locals2env s)) (eval y (locals2env s)) h), c)).
 simpl. rewrite (eval_expr_get vars s h y); auto. rewrite (eval_expr_get vars s h x); auto.
 apply (safeN_step _ _ _ _ H10).
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H11 (pred_nec_hereditary _ _ _ H11 H1)).
 apply (pred_hereditary _ (level w') (level w'')) in H;
   [ |  apply age_level in H7; rewrite H7; hnf; simpl; auto].
 apply (pred_hereditary _ _ _ H7) in H5.
 apply (pred_hereditary _ _ _ H7) in H6.
 apply (pred_hereditary _ _ _ H7) in H4.
 apply (pred_hereditary _ _ _ H7) in H8.
 clear H1; pose (H1:=True). clear n H0. pose (H0:=True).
 clear n' H2 H11. pose (H2:=True). pose (H11:=True).
 simpl in H8.
clear w' H7 H9 H3. 
 pose (H7:=True); pose (H9:=True); pose (H3:=True).
 clear H0 H1.
 destruct H5 as [wa [wb [H0 [HP H1]]]].
 pose (m' := singleton_rmap (eval x (locals2env s)) (eval y (locals2env s)) w'').
 assert (joins m' wb).
 apply resource_at_joins2. unfold m'.
 rewrite singleton_rmap_level.
 apply join_level in H0. destruct H0. auto.
 unfold m'. intro i.
 clear - HP H0.
 apply (resource_at_join _ _ _ i) in H0.
 specialize (HP i).
 unfold singleton_rmap. rewrite resource_at_make_rmap.
 destruct (eq_dec i (eval x (locals2env s))). subst; rewrite if_true in HP; auto.
 exists (YES pfullshare (VAL (eval y (locals2env s))) NoneP).
 rewrite HP in *. inv H0; try pfullshare_join. constructor.
 rewrite if_false in HP by auto. 
 exists (wb @ i). 
 apply HP in H0. rewrite H0.
 rewrite <- core_resource_at. apply core_unit.
 destruct H5 as [ww H12].
 replace (level w'') with (level ww) in H.
 Focus 2.
 transitivity (level wb).
 apply join_level in H12. destruct H12 as [H12 H13]. symmetry ; apply H13.
 apply join_level in H0; destruct H0; auto.
 specialize (H (locals2env s) ww).
 spec H. simpl. apply le_refl.
 specialize (H _ (necR_refl _)).
 spec H. rewrite andp_assoc. rewrite andp_com.
 clear - H4 H0 HP H12 H6 H1.
 assert (app_pred ((mapsto (eval x (locals2env s)) v * TT) && (funassert G && funassert G')) w'').
 split; auto. exists wa; exists wb; split3; auto. split; auto.
 destruct H as [? _].
 split.
 apply join_com in H0. apply join_com in H12. apply join_core in H0. apply join_core in H12.
 apply funassert_core in H6. apply funassert_core in H4. rewrite H12 in H0.
 split; apply funassert_core; rewrite H0; auto.
 destruct H as [wa' [wb' [? [? ?]]]].
 assert (wa' = wa). eapply mapsto_uniq; eauto.
 apply join_core in H0; apply join_core in H. rewrite H0; rewrite H. auto. 
 subst wa'. generalize (join_canc (join_com H0) (join_com H)); intro; subst wb'.
  generalize (singleton_rmap_mapsto (eval x (locals2env s)) (eval y (locals2env s)) w''); intro.
 assert (app_pred (mapsto (eval x (locals2env s)) (eval y (locals2env s)) * (TT && (funassert G && funassert G'))) ww).
 exists m'; exists wb; split3; auto.
 split; auto.
 apply join_com in H0. apply join_com in H12. apply join_core in H0. apply join_core in H12.
  apply funassert_core in H6. apply funassert_core in H4.
 split; apply funassert_core; rewrite H0; auto.
 exists m'; exists wb; split3; auto.
 replace (level w'') with (level ww).
 Focus 2. simpl. transitivity (level wb).
 clear - H12; apply join_level in H12; destruct H12; symmetry; apply H0.
 clear - H0; apply join_level in H0; destruct H0; apply H0.
 apply H; auto.
 intros i v0. specialize (HP i).
 simpl.
 apply (resource_at_join _ _ _ i) in H12.
 unfold m' in *; clear m'.
 unfold singleton_rmap in H12.
 rewrite resource_at_make_rmap in H12.
 change AV.address with adr in H12.
  specialize (H8 i v0). simpl in H8. 

  destruct (eq_dec i (eval x (locals2env s))). 
  subst. rewrite heap_gss.
  apply join_unit2_e in H12. rewrite <- H12.
  split; intro Hx; inv Hx; auto.
  apply YES_join_full in H12; auto.
  rewrite H12. apply NO_identity.
  apply join_unit1_e in H12; [ | rewrite <- core_resource_at; apply core_identity].
  rewrite heap_gso; auto. 
 apply (resource_at_join _ _ _ i) in H0.
 rewrite <- H12.
 apply HP in H0. rewrite H0; auto.
Qed.

Lemma semax_pre: 
  forall P P' vars G c, (forall s, P s |-- P' s) -> semax vars G P' c -> semax vars G P c.
Proof.
 intros. destruct H0 as [TC H0]; split; auto.
 intro n; specialize (H0 n).
 rewrite semax'_unfold in *.
 intros p G'. specialize (H0 p G').
 intros n' ? ?. specialize (H0 _ H1 H2).
 intros s w ? ? ? ?. specialize (H0 s _ H3 _ H4).
 apply H0.
 destruct H5; split; auto. destruct H5;  split; auto. apply H; auto.
Qed.


Lemma semax_exp: forall {A} vars G (P: A -> assert) c,
    typecheck vars c = true ->
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => Ex v:A, (P v s)) c.
Proof.
 intros ? ? ? ? ? TC ?.
 split; auto. 
 intro.
 rewrite semax'_unfold.
 intros p G'. intros n' ? ?.
 intros s. intros ? ?. intros ? ?. intros [[[v ?] ?] ?].
 specialize (H v). destruct H as [_ H].
 rewrite semax'_unfold in H. eapply H; eauto. split; auto. split; auto.
Qed.

Lemma semax_exp': forall {A} (any: A) vars G (P: A -> assert) c,
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => Ex v:A, (P v s)) c.
Proof.
 intros ? ? ? ? ? ?.
 split; auto. 
 destruct (H any); auto.
 intro.
 rewrite semax'_unfold.
 intros p G'. intros n' ? ?.
 intros s. intros ? ?. intros ? ?. intros [[[v ?] ?] ?].
 specialize (H v). destruct H as [_ H].
 rewrite semax'_unfold in H. eapply H; eauto. split; auto. split; auto.
Qed.

Lemma semax_prop:
  forall (R: Prop) vars G P c,
      typecheck vars c = true ->
      (R -> semax vars G P c) ->
      semax vars G (fun s => !! R && P s) c.
Proof.
  intros R vars G P c TC ?. split; auto. intro n.  rewrite semax'_unfold. intros p G'.
  intros n' ? ? b w ? w' ? [[[? ?] ?] ?].
  destruct (H H4).
  specialize (H9 n). rewrite semax'_unfold in H9.
  eapply H9; eauto. split; auto. split; auto.
Qed.

Definition program_proved (p: program) :=
   exists G, semax_func G p G  /\ table_get G 0 = Some (0::nil, fun s => allocpool (eval (Var 0) s)).

Lemma semax_sound: 
  forall p, program_proved p -> forall n, run p n <> None.
Proof.
  intros.
  destruct H as [G [[? ?] ?]].
  generalize (funassert_make_world p G n); intro.
  destruct (semax_go nil G  (0::nil, fun s => allocpool (eval (Var 0) s))
                (Const 0) (Const (boundary p) :: nil) (eq_refl _)) as [_ ?].
  specialize (H3 n).
  rewrite semax'_unfold in H3.
  specialize (H3 p G _ (necR_refl _) (H0 _) (locals2env nil) 
                    (make_world G (initial_heap p) n)).
  spec H3. rewrite level_make_world. auto.
  specialize (H3 _ (necR_refl _)).
  spec H3.
  split; auto.
  split; auto.
  split.
  apply (funassert_e _ _ _ H1 _ H2).
  unfold call.
  Transparent arguments. unfold arguments. Opaque arguments.
  simpl snd.
  unfold locals2env, table_get. rewrite if_true; auto.
  split. simpl; auto.
  apply allocpool_make_world; auto.
  hnf in H3.
  specialize (H3 nil (initial_heap p)).
  spec H3. intros i ?. inv H4.
  spec H3. auto.
  spec H3. apply cohere_make_world; auto.
  unfold run; intro.
  destruct H3 as [sk' ?].
  rewrite level_make_world in H3. 
 unfold locals,table, var,adr in H3,H4. rewrite H3 in H4; inv H4.
Qed.

End Semax.

Import Semax.

(* PROOF AUTOMATION FOR SEMAX *)

Hint Extern 3 (inlist _ _ = false) => (compute; reflexivity).

Lemma arguments_gss: forall x xl v vl, arguments (x::xl)(v::vl) x = v.
Proof.
  intros.  
 Transparent arguments. unfold arguments, locals2env,mk_locals;  simpl.
 Opaque arguments.
  rewrite if_true; auto.
Qed.
Lemma arguments_gso: forall x xl v vl x', x<>x' -> arguments (x::xl)(v::vl)x' = arguments xl vl x'.
Proof.
  intros.  
 Transparent arguments. unfold arguments, locals2env,mk_locals;  simpl.
 Opaque arguments.
  rewrite if_false; auto.
Qed.

Ltac compute_neq := solve [let H := fresh in intro H; inversion H].

Hint Rewrite arguments_gss : args.
Hint Rewrite arguments_gso using compute_neq : args.

Ltac call_tac := unfold call; simpl; autorewrite with args; simpl.

Ltac funassert_tac := 
  match goal with 
  | |-   ?A && ?B |-- _ =>
      match A with context [funassert _] => apply andp_left1; funassert_tac  end ||
      match B with context [funassert _] => apply andp_left2; funassert_tac  end
  | |- funassert _ |-- _ => apply funassert_e; simpl; reflexivity
 end.

Ltac func_tac := 
   apply semax_func_cons; 
    [ compute; reflexivity | compute; reflexivity | compute; reflexivity 
    |  (*eapply semax_pre; [intro ; call_tac; apply derives_refl | ] *)
    | ].                     

Ltac rewrite' H := eapply semax_pre; [ intro; rewrite H; apply derives_refl | ].

(* This tactic works but introduces magic wands, which is undesirable *)
Ltac forward_magic := 
  match goal with |- semax _ ?G ?P (Assign (Mem ?e1) ?e2 ?c) =>
      let v := fresh "v" in
        (evar (v:adr);
       apply semax_pre with (P' := fun s => mapsto (eval e1 s) v * (mapsto (eval e1 s) v -* P s));
               [intro | apply semax_store; auto  ] );
       unfold v; clear v
  end.

Ltac forward := 
 match goal with
 | |- semax _ _ _ (language.If _ _ _) =>
          apply semax_if; [ compute; reflexivity | | ]
 | |- semax _ _ _ (Assign (Mem _) _ _) => 
            eapply semax_store; [ compute ; reflexivity | compute; reflexivity | reflexivity | ]
 | |- semax _ _ ?P (Go ?x ?ys) =>
  apply semax_G;
  let p := fresh "P" in 
   evar (p: funspec);
   eapply semax_pre with (fun s => cont p (eval x s) && call p (eval_list ys s));
       [ intro; apply andp_right 
       | apply semax_go; [ compute; reflexivity ] ]; unfold p; clear p;
       [ try funassert_tac | call_tac  ]; simpl
 end.

Hint Resolve now_later sepcon_derives.



Definition semax_body (G: funspecs) (spec: funspec) (f: list var * control) :=
  semax (fst f) G (fun s => call spec (map s (fst f))) (snd f).



   
