Require Import veric.base.
Require Import veric.expr.
Require Import veric.seplog.
Require Import msl.normalize.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import veric.SequentialClight.
Require Import msl.msl_standard.
Import SeqC CSL.
Require Import progs.client_lemmas.

Require Import progs.list.
Require progs.test1.
Module P := progs.test1.


Instance t_list_spec: listspec P.t_listptr.
Proof.
econstructor.
reflexivity.
intro Hx; inv Hx.
intros.
unfold unroll_composite; simpl.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Local Open Scope pred.

Definition sumlist_pre (contents: list int) (args: arguments) : pred rmap :=
  match args with 
  | p::nil => !!(snd p = P.t_listptr) &&
                   lseg (map (fun i => (Vint i, P.t_int)) contents) (fst p, P.t_listptr) (nullval, P.t_listptr)
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
  | p::nil =>  !!(snd p = P.t_listptr) &&
                     lseg (map (fun i => (Vint i, P.t_int)) contents) (fst p, P.t_listptr) (nullval, P.t_listptr)
  | _ => FF 
  end.

Definition reverse_post (contents: list int) (res: arguments) : pred rmap :=
  match res with 
  | p::nil => !!(snd p = P.t_listptr) &&
                      lseg (map (fun i => (Vint i, P.t_int)) (rev contents)) (fst p, P.t_listptr) (nullval, P.t_listptr)
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


Definition sumlist_Inv (contents: list int) (rho: environ) : pred rmap :=
          (Ex cts: list int, 
           !!(fold_right Int.add Int.zero contents =
             Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
                       (fold_right Int.add Int.zero cts)) &&
           lseg (map (fun i => (Vint i, P.t_int)) cts) 
                 (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_listptr)
                 (nullval, P.t_listptr)).

Lemma prop_right {A}{agA: ageable A}:
  forall (P: pred A)(Q: Prop), Q -> (P |-- !!Q).
Proof.
intros; intros ? ?; auto.
Qed.

Require Import Decidable.
Lemma semax_extract_prop:
  forall Delta G (PP: Prop) P c Q, 
           decidable PP ->
           typecheck_stmt Delta c = true ->
           (PP -> semax Delta G P c Q) -> semax Delta G (fun rho => !!PP && P rho) c Q.
Proof.
intros.
destruct H.
apply semax_pre with P; auto.
intros w [? [? ?]]; auto.
eapply semax_pre with (fun _ => FF); auto.
intros w [? [? ?]]. contradiction.
apply semax_ff; auto.
Qed.

Lemma body_sumlist:
   semax_body Gprog P.f_sumlist _ sumlist_pre sumlist_post.
Proof.
split; [split; simpl; repeat constructor; prove_notin | ].
intro contents.
simpl.
unfold function_body_entry_assert, sumlist_pre.
simpl fn_params.
simpl.
set (contents' :=  map (fun i : int => (Vint i, P.t_int)) contents).
unfold stackframe_of; simpl.
apply semax_Sseq with
  (fun rho => !! (eval_expr rho (Etempvar P.i_s P.t_int) = (Vint (Int.repr 0))) &&
                              lseg contents' (eval_expr rho (Etempvar P.i_p P.t_listptr), P.t_listptr)
                              (nullval, P.t_listptr)).
apply sequential'.
eapply semax_pre; [ | apply semax_set].
intros. eapply derives_trans; [ |apply now_later].
unfold subst.
apply prop_andp_right.
rewrite env_gss. reflexivity.
rewrite sepcon_emp.
rewrite env_gso by (intro Hx; inv Hx); auto.
unfold bind_args. simpl.
normalize.
admit.  (* typechecking proof *)
reflexivity.
apply semax_Sseq with
  (fun rho => !! (eval_expr rho (Etempvar P.i_s P.t_int) = (Vint (Int.repr 0))
                         /\ eval_expr rho (Etempvar P.i_t P.t_listptr) = eval_expr rho (Etempvar P.i_p P.t_listptr)) &&
                              lseg contents' (eval_expr rho (Etempvar P.i_p P.t_listptr), P.t_listptr)
                              (nullval, P.t_listptr)).
apply sequential'.
eapply semax_pre; [ | apply semax_set].
intros. eapply derives_trans; [ |apply now_later].
apply prop_andp_left; intro.
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
intros.
apply prop_andp_left; intros [? ?].
unfold sumlist_Inv.
apply exp_right with contents.
apply prop_andp_right.
rewrite H0. simpl.
rewrite Int.add_zero_l. auto.
rewrite H1. auto.
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
eapply sequential; [intros; simpl; reflexivity | ].
unfold sumlist_Inv at 1.
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

pose (P' rho := 
(Ex  h : val,
 (Ex  r : list valt,
  (Ex  y : val,
  assert_expr (Etempvar P.i_t P.t_listptr) rho &&
!!(fold_right Int.add Int.zero contents =
   Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
     (fold_right Int.add Int.zero cts)) &&
   !!(map (fun i : int => (Vint i, P.t_int)) cts = (h, P.t_int) :: r /\
      typecheck_val h P.t_int = true /\ typecheck_val y P.t_listptr = true) &&
   field_mapsto Share.top
     (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_list) P.i_h
     (h, P.t_int) *
   field_mapsto Share.top
     (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_list) P.i_t
     (y, P.t_listptr) * |>lseg r (y, P.t_listptr) (nullval, P.t_listptr))))).
apply semax_pre with P'; unfold P' in *; clear P'.
intros.
unfold assert_expr.
normalize.
(* BUG: the next line should have been accomplished by normalize *)
rewrite andp_assoc; apply derives_extract_prop; intro.
simpl in H0.
rewrite lseg_neq.
normalize.
intros h r y.
normalize. apply (exp_right h).
normalize. apply (exp_right r).
normalize. apply (exp_right y).
normalize.
admit.  (* typechecking proof *)
admit.  (* typechecking proof *)
intro.
unfold ptr_eq in H1.
destruct (eval_expr rho (Etempvar P.i_t P.t_listptr)); try contradiction.
simpl in H1. 
simpl in H0.
rewrite H1 in H0. inv H0.
apply extract_exists_pre; [apply Vundef |  intro h].
apply extract_exists_pre; [apply nil |  intro r].
apply extract_exists_pre; [apply Vundef |  intro y].
apply semax_pre with
  (fun rho : environ =>
  !!(map (fun i : int => (Vint i, P.t_int)) cts = (h, P.t_int) :: r /\
      typecheck_val h P.t_int = true /\ typecheck_val y P.t_listptr = true) &&
   (assert_expr (Etempvar P.i_t P.t_listptr) rho &&
   !!(fold_right Int.add Int.zero contents =
      Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
        (fold_right Int.add Int.zero cts)) &&
   field_mapsto Share.top
     (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_list) P.i_h
     (h, P.t_int) *
   field_mapsto Share.top
     (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_list) P.i_t
     (y, P.t_listptr) * |>lseg r (y, P.t_listptr) (nullval, P.t_listptr))).
intros.
admit.  (* easy *)
apply semax_extract_prop.
admit.  (* easy *)
admit.  (* typechecking proof *)
intros [? [? ?]].
set (e1:= (Ederef (Etempvar P.i_t P.t_listptr) P.t_list)).
set (P := (fun rho0 : environ =>
         assert_expr (Etempvar P.i_t P.t_listptr) rho0 &&
         !!(fold_right Int.add Int.zero contents =
            Int.add (force_int (eval_expr rho0 (Etempvar P.i_s P.t_int)))
              (fold_right Int.add Int.zero cts)) &&
         !!(map (fun i : int => (Vint i, P.t_int)) cts = (h, P.t_int) :: r /\
            typecheck_val h P.t_int = true /\
            typecheck_val y P.t_listptr = true) &&
         field_mapsto Share.top
           (eval_expr rho0 (Etempvar P.i_t P.t_listptr), P.t_list) P.i_t
           (y, P.t_listptr) *
         |>lseg r (y, P.t_listptr) (nullval, P.t_listptr))).

apply semax_pre with
 (fun rho => |> (field_mapsto Share.top (eval_expr rho e1, P.t_list) P.i_h
     (h, P.t_int) 
   * subst P.i_h h P rho)).
admit.
pose (Q := 
       (fun rho : environ =>
        field_mapsto Share.top (eval_expr rho e1, typeof e1) P.i_h
          (h, P.t_int) * P rho)).
apply semax_Sseq with Q.
apply semax_post with (normal_ret_assert Q).
intros.
normalize.
eapply semax_load_field; eauto.
admit.  (* typechecking proof *)
admit.  (* typechecking proof *)
unfold e1.
admit.  (* typechecking proof *)
unfold e1; simpl. reflexivity.
simpl .
rewrite if_true by auto. reflexivity.

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




