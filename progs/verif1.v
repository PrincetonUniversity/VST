Require Import veric.base.
Require Import veric.expr.
Require Import veric.seplog.
(* Require Import veric.SeparationLogic. 
 Declare Module CSL: CLIGHT_SEPARATION_LOGIC. 
  Import CSL. 
*)

Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Require Import veric.SequentialClight.
Require Import msl.msl_standard.
Require Import progs.list.
Require progs.test1.
Module P := progs.test1.

Import SeqC CSL.

Definition sumlist_pre (contents: list int) (args: arguments) : pred rmap :=
  match args with 
  | p::nil => lseg (map (fun i => (Vint i, P.t_int)) contents) p (nullval, snd p)
  | _ => FF 
  end.

Definition sumlist_post (contents: list int) (res: arguments) : pred rmap :=
  match res with 
  | (Vint i, _) ::nil => prop (fold_right Int.add Int.zero contents = i)
  | _ => FF 
  end.

Definition sumlist_fsig : funsig := (Tcons P.t_listptr Tnil, P.t_int).

Definition reverse_pre (contents: list int) (args: arguments) : pred rmap :=
  match args with 
  | p::nil => lseg (map (fun i => (Vint i, P.t_int)) contents) p (nullval, snd p)
  | _ => FF 
  end.

Definition reverse_post (contents: list int) (res: arguments) : pred rmap :=
  match res with 
  | p::nil => lseg (map (fun i => (Vint i, P.t_int)) (rev contents)) p (nullval, snd p)
  | _ => FF 
  end.

Definition reverse_fsig : funsig := (Tcons P.t_listptr Tnil, P.t_listptr).

Definition main_fsig : funsig := (Tnil, P.t_int).

Definition Gprog : funspecs := 
  (P.i_sumlist, mk_funspec sumlist_fsig _ sumlist_pre sumlist_post)::
  (P.i_reverse, mk_funspec reverse_fsig _ reverse_pre reverse_post)::
  (P.i_main, mk_funspec main_fsig _ (main_pre P.prog) (main_post P.prog))::
nil.

Ltac prove_notin := clear; simpl; intuition; match goal with H: _ = _ |- _ => inv H end.
Definition bind_args' (formals: list (ident * type)) (P: arguments -> pred rmap) : assert :=
   fun rho => P (map (fun xt => (eval_expr rho (Etempvar (fst xt) (snd xt)), snd xt)) formals).

Lemma bind_args_eq: bind_args = bind_args'.
Proof.
intros.
extensionality args P rho.
unfold bind_args, bind_args'.
f_equal.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall ek vl rho, R' ek vl rho |-- R ek vl rho) ->
   semax Delta G P c R' ->  semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
Qed.

Lemma semax_pre:
 forall P' Delta G P c R,
   (forall rho, P  rho |-- P' rho) ->   semax Delta G P' c R  -> semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
Qed.

Local Open Scope pred.


Lemma env_gss:
  forall rho id v t, eval_expr (env_set rho id v) (Etempvar id t) = v.
Proof.
intros.  unfold eval_expr, env_set; simpl. rewrite PTree.gss. simpl. auto.
Qed.

Lemma env_gso:
  forall rho id id' v t, id <> id' -> 
      eval_expr (env_set rho id' v) (Etempvar id t) = eval_expr rho (Etempvar id t).
Proof.
intros.  unfold eval_expr, env_set; simpl.
rewrite PTree.gso by auto. auto.
Qed.

Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.

Definition sumlist_Inv (contents: list int) (rho: environ) : pred rmap :=
          (Ex cts: list int, 
           !!(fold_right Int.add Int.zero contents =
             Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
                       (fold_right Int.add Int.zero cts)) &&
           lseg (map (fun i => (Vint i, P.t_int)) cts) 
                 (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_listptr)
                 (nullval, P.t_listptr)).

Require Import veric.normalize.

Lemma lseg_eq:
  forall l v t, 
  match t with Tpointer (Tstruct _ (Fcons _ _ (Fcons _ _ Fnil)) _) _ => True | _ => False end ->
  typecheck_val v t = true ->
    lseg l (v,t) (v,t) = !!(l=nil) && emp.
Proof.
intros.
pose proof (lseg_unfold l (v,t) (v,t) (eq_refl _)).
destruct t; try contradiction.
destruct t; try contradiction.
destruct f; try contradiction.
destruct f; try contradiction.
destruct f; try contradiction.
simpl in *.
destruct l.
rewrite H1.
f_equal.
unfold ptr_eq.
destruct v; simpl in H0; try discriminate.
unfold Int.cmpu.
rewrite Int.eq_true.
normalize.
replace (v0 :: l = nil) with False by (apply prop_ext; intuition; congruence).
apply pred_ext; [ | normalize].
rewrite H1; clear H1.
normalize.
destruct v; normalize.
contradiction H1.
simpl. split; auto. apply Int.eq_true.
Qed.


Lemma prop_right {A}{agA: ageable A}:
  forall (P: pred A)(Q: Prop), Q -> (P |-- !!Q).
Proof.
intros; intros ? ?; auto.
Qed.

Lemma extract_exists_pre:
      forall
        (A : Type) (any: A) (P : A -> assert) (c : Clight.statement)
         Delta (G : funspecs) (R : ret_assert),
       (forall x : A, semax Delta G (P x) c R) ->
       semax Delta G (fun rho => exp (fun x => P x rho)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R)).
intros ek vl rho w ?.
simpl in H0. destruct H0; auto.
apply extract_exists; auto.
Qed.


Lemma body_sumlist:
   semax_body Gprog P.f_sumlist _ sumlist_pre sumlist_post.
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro contents.
simpl.
unfold function_body_entry_assert, sumlist_pre.
simpl fn_params.
rewrite bind_args_eq.
unfold bind_args'.
simpl.
set (contents' :=  map (fun i : int => (Vint i, P.t_int)) contents).
unfold stackframe_of; simpl.
apply semax_Sseq with
  (fun rho => !! (eval_expr rho (Etempvar P.i_s P.t_int) = (Vint (Int.repr 0))) &&
                              lseg contents' (eval_expr rho (Etempvar P.i_p P.t_listptr), P.t_listptr)
                              (nullval, P.t_listptr)).
evar (P1: assert); eapply semax_pre; [ | apply semax_set with (P:=P1)]; unfold P1; clear P1;
   [ | | | reflexivity].
intro. eapply derives_trans; [ |apply now_later].
unfold subst.
unfold overridePost. rewrite if_true by auto.
apply prop_andp_right.
rewrite env_gss. reflexivity.
rewrite sepcon_emp.
rewrite env_gso by (intro Hx; inv Hx); auto.
admit.  (* typechecking proof *)
reflexivity.
apply semax_Sseq with
  (fun rho => !! (eval_expr rho (Etempvar P.i_s P.t_int) = (Vint (Int.repr 0))
                         /\ eval_expr rho (Etempvar P.i_t P.t_listptr) = eval_expr rho (Etempvar P.i_p P.t_listptr)) &&
                              lseg contents' (eval_expr rho (Etempvar P.i_p P.t_listptr), P.t_listptr)
                              (nullval, P.t_listptr)).
evar (P1: assert); eapply semax_pre; [ | apply semax_set with (P:=P1)]; unfold P1; clear P1;
   [ | | | reflexivity].
intro. eapply derives_trans; [ |apply now_later].
apply prop_andp_left; intro.
unfold overridePost. rewrite if_true by auto.
unfold subst.
apply prop_andp_right.
split.
rewrite env_gso by (intro Hx; inv Hx); auto.
rewrite env_gss. rewrite env_gso by (intro Hx; inv Hx); auto.
rewrite env_gso by (intro Hx; inv Hx); auto.
admit.  (* typechecking proof *)
admit.  (* typechecking proof *)
unfold contents'; clear contents'.
 apply semax_pre with (sumlist_Inv contents).
intro.
apply prop_andp_left; intros [? ?].
unfold sumlist_Inv.
apply exp_right with contents.
apply prop_andp_right.
rewrite H. simpl.
rewrite Int.add_zero_l. auto.
rewrite H0. auto.
apply semax_Sseq with
  (fun rho => !!(fold_right Int.add Int.zero contents =
              force_int (eval_expr rho (Etempvar P.i_s P.t_int)))).
apply semax_while.
admit.  (* typechecking proof *)
reflexivity.
intros.
unfold assert_expr.
apply prop_andp_left; intro.
unfold Cnot in H.
simpl in H.
assert (eval_expr rho (Etempvar P.i_t P.t_listptr) = nullval).
admit.
unfold overridePost. rewrite if_true by auto.
unfold sumlist_Inv.
apply exp_left; intro cts.
apply prop_andp_left; intro.
rewrite H0.
rewrite (lseg_eq (map (fun i : int => (Vint i, P.t_int)) cts) nullval P.t_listptr).
2: simpl; auto.
normalize.
apply prop_right.
rewrite H1. destruct cts; inv H2.  simpl fold_right. 
rewrite Int.add_zero.  auto.
admit.  (* typechecking proof *)
unfold sumlist_Inv.
apply semax_pre with 
   (fun rho : environ =>
    (Ex  cts : list int,
   assert_expr (Etempvar P.i_t P.t_listptr) rho &&
    !!(fold_right Int.add Int.zero contents =
       Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
         (fold_right Int.add Int.zero cts)) &&
    lseg (map (fun i : int => (Vint i, P.t_int)) cts)
      (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_listptr)
      (nullval, P.t_listptr))).
intro; normalize; intros.
apply exp_right with x.
repeat rewrite andp_assoc; auto.
apply extract_exists_pre.
apply nil.
intro cts.



Admitted.

Lemma body_reverse:
   semax_body Gprog P.f_reverse _ reverse_pre reverse_post.
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro contents.
simpl.
Admitted.

Lemma body_main:
   semax_body Gprog P.f_main _ (main_pre P.prog) (main_post P.prog).
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro x; destruct x.
simpl.
Admitted.

Lemma all_funcs_correct:
  semax_func Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
apply semax_func_cons; [compute; auto | prove_notin | apply body_sumlist | ].
apply semax_func_cons; [compute; auto | prove_notin | apply body_reverse | ].
apply semax_func_cons; [compute; auto | prove_notin | apply body_main | ].
apply semax_func_nil.
Qed.




