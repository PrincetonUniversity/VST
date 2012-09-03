Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import compcert.Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.list.

Instance Cassert: ClassicalSep assert := _.

Require progs.test1.
Module P := progs.test1.

Local Open Scope logic.

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

Definition int2valt (i: int) := (Vint i, P.t_int).

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH contents 
  PRE [ p : P.t_listptr]  lseg (map (fun i => (Vint i, P.t_int)) contents) (p, P.t_listptr) (nullval, P.t_listptr)
  POST [ i : P.t_int ] prop (i = Vint (fold_right Int.add Int.zero contents)).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH contents : list int
  PRE  [ p : P.t_listptr ] lseg (map int2valt contents) (p, P.t_listptr) (nullval, P.t_listptr)
  POST [p : P.t_listptr ] lseg (map int2valt (rev contents)) (p, P.t_listptr) (nullval, P.t_listptr).

Definition main_spec := (P.i_main, mk_funspec (Tnil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition sumlist_Inv (contents: list int) (rho: environ) : mpred :=
          (EX cts: list int, 
           !!(fold_right Int.add Int.zero contents =
             Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
                       (fold_right Int.add Int.zero cts)) &&
           lseg (map (fun i => (Vint i, P.t_int)) cts) 
                 (eval_expr rho (Etempvar P.i_t P.t_listptr), P.t_listptr)
                 (nullval, P.t_listptr)).

Definition semax_body' (G:  funspecs) (f: function) (spec: ident * funspec) :=
  match spec with (i, mk_funspec _ A pre post) => semax_body G f A pre post end.


Lemma body_sumlist: semax_body' Gprog P.f_sumlist sumlist_spec.
Proof.
intro contents.
simpl fn_params.
normalize.
simpl.
set (contents' :=  map (fun i : int => (Vint i, P.t_int)) contents).
apply semax_Sseq with
  ((fun rho => !! (eval_id rho P.i_s = Vint (Int.repr 0))) &&
   (fun rho => lseg contents' (eval_id rho P.i_p, P.t_listptr) (nullval, P.t_listptr))).
apply sequential'.
eapply semax_pre; [ | apply semax_set].
intros.
normalize.
apply andp_right.
apply prop_right.
compute; auto.
eapply derives_trans; [ |apply now_later].
unfold subst.
normalize.
cbv beta.
normalize.
apply semax_Sseq with
  (fun rho => !! (eval_id rho P.i_s = Vint (Int.repr 0)
                         /\ eval_id rho P.i_t = eval_id rho P.i_p) &&
                              lseg contents' (eval_id rho P.i_p, P.t_listptr)  (nullval, P.t_listptr)).
apply sequential'.
eapply semax_pre; [ | apply semax_set].
intros.
normalize.
unfold tc_expr.
apply andp_right.
apply prop_right.
compute; auto.
eapply derives_trans; [ |apply now_later].
unfold subst.
normalize.
unfold contents'; clear contents'.
apply semax_pre with (sumlist_Inv contents).
intros.
normalize.
destruct H0.
unfold sumlist_Inv.
apply exp_right with contents.
normalize.
rewrite H0. simpl.
rewrite Int.add_zero_l. normalize.
rewrite H1; auto.

apply semax_Sseq with
  (fun rho => !!(fold_right Int.add Int.zero contents = force_int (eval_id rho P.i_s))).
apply semax_while.
intros.
unfold tc_expr; simpl.
unfold denote_tc_initialized.
unfold sumlist_Inv; normalize. intros.
admit.  (* true enough *)
reflexivity.
intro rho.
normalize.
unfold Cnot, expr_true.
normalize.
simpl in H.
assert (eval_id rho P.i_t = nullval).
destruct (eval_id rho P.i_t); simpl in H; try discriminate.
admit.
unfold sumlist_Inv.
apply exp_left; intro cts.
normalize.
rewrite H0.
rewrite (lseg_eq (map (fun i : int => (Vint i, P.t_int)) cts) nullval P.t_listptr).
rewrite H1.
normalize.
destruct cts; inv H2.  simpl fold_right. 
rewrite Int.add_zero.  normalize.
admit.  (* typechecking proof *)
eapply sequential; [intros; simpl; reflexivity | ].
unfold sumlist_Inv at 1.
apply semax_pre with 
   (fun rho : environ =>
    (EX  cts : list int,
    expr_true (Etempvar P.i_t P.t_listptr) rho &&
    !!(fold_right Int.add Int.zero contents =
       Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
         (fold_right Int.add Int.zero cts)) &&
    lseg (map (fun i : int => (Vint i, P.t_int)) cts)
      (eval_id rho P.i_t, P.t_listptr)
      (nullval, P.t_listptr))).
intro; normalize; intros.
apply exp_right with x.
normalize.
apply extract_exists_pre.
apply nil.
intro cts.

pose (P' rho := 
(EX  h : val,
 (EX  r : list valt,
  (EX  y : val,
    expr_true (Etempvar P.i_t P.t_listptr) rho &&
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
unfold expr_true.
normalize.
rewrite lseg_neq.
normalize.
intros h r y.
normalize. apply (exp_right h).
normalize. apply (exp_right r).
normalize. apply (exp_right y).
normalize.
simpl in H0|-*.
destruct (eval_id rho P.i_t); inv H0; auto.
admit.  (* typechecking proof *)
intro.
unfold ptr_eq in H2.
destruct (eval_id rho P.i_t); try contradiction.
simpl in H2.
simpl in H0.
rewrite H2 in H0. inv H0.

apply extract_exists_pre; [apply Vundef |  intro h].
apply extract_exists_pre; [apply nil |  intro r].
apply extract_exists_pre; [apply Vundef |  intro y].
apply semax_pre with
  (fun rho : environ =>
  !!(map (fun i : int => (Vint i, P.t_int)) cts = (h, P.t_int) :: r /\
      typecheck_val h P.t_int = true /\ typecheck_val y P.t_listptr = true) &&
   (expr_true (Etempvar P.i_t P.t_listptr) rho &&
   !!(fold_right Int.add Int.zero contents =
      Int.add (force_int (eval_id rho P.i_s))
        (fold_right Int.add Int.zero cts)) &&
   field_mapsto Share.top
     (eval_id rho P.i_t, P.t_list) P.i_h
     (h, P.t_int) *
   field_mapsto Share.top
     (eval_id rho P.i_t, P.t_list) P.i_t
     (y, P.t_listptr) * |>lseg r (y, P.t_listptr) (nullval, P.t_listptr))).
intros.
unfold expr_true.
normalize.
apply semax_extract_prop.
intros [? [? ?]].
set (e1:= Ederef (Etempvar P.i_t P.t_listptr) P.t_list).
set (P := (fun rho0 : environ =>
         expr_true (Etempvar P.i_t P.t_listptr) rho0 &&
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
 (fun rho => |> (field_mapsto Share.top (eval_lvalue rho e1, P.t_list) P.i_h
     (h, P.t_int) 
   * subst P.i_h h P rho)).
intros.
admit.
pose (Q := 
       ((fun rho => field_mapsto Share.top ((eval_lvalue rho e1), typeof e1) P.i_h (h, P.t_int)) * P)).
apply semax_Sseq with Q.
apply semax_post with (normal_ret_assert Q).
normalize.
evar (Q3: assert).
apply semax_pre with Q3; [ unfold Q3 |  unfold Q3; eapply semax_load_field; eauto].
intros. unfold e1.
simpl.
apply andp_right.
apply prop_right.
simpl. split3; auto. split; auto.
split; auto.
admit.  (* typechecking proof *)
admit.  (* typechecking proof *)
auto.
unfold e1.
admit.  (* easy *) 
simpl. reflexivity.
simpl. reflexivity.
simpl. rewrite if_true by auto. reflexivity.

Admitted.

Lemma body_reverse: semax_body' Gprog P.f_reverse reverse_spec.
Proof.
intro contents.
simpl.
Admitted.

Lemma body_main:
   semax_body Gprog P.f_main _ (main_pre P.prog) (main_post P.prog).
Proof.
intro x; destruct x.
simpl.
Admitted.

Lemma all_funcs_correct:
  semax_func Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.




