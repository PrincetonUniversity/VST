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

Definition ilseg (s: list int) p q := lseg P.t_listptr (map Vint s) p q.

(*
Definition ilseg (s: list int) (p q: expr) : assert
   := fun rho => lseg P.t_listptr (map Vint s) (eval_expr rho p) (eval_expr rho q).
*)

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH contents 
  PRE [ p : P.t_listptr]  ilseg contents p nullval
  POST [ i : P.t_int ] prop (i = Vint (fold_right Int.add Int.zero contents)).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH contents : list int
  PRE  [ p : P.t_listptr ] ilseg contents p nullval
  POST [p : P.t_listptr ] ilseg (rev contents) p nullval.

Definition main_spec := (P.i_main, mk_funspec (Tnil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition sumlist_Inv (contents: list int) : assert :=
          (EX cts: list int, 
           (fun rho => !!(fold_right Int.add Int.zero contents =
             Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
                       (fold_right Int.add Int.zero cts))) &&
           (fun rho => ilseg cts (eval_expr rho (Etempvar P.i_t P.t_listptr)) nullval)).

Definition sumlist_Inv' (contents: list int) (rho: environ) : mpred :=
          (EX cts: list int, 
           !!(fold_right Int.add Int.zero contents =
             Int.add (force_int (eval_expr rho (Etempvar P.i_s P.t_int)))
                       (fold_right Int.add Int.zero cts)) &&
           ilseg cts (eval_expr rho (Etempvar P.i_t P.t_listptr)) nullval).

Definition semax_body' (G:  funspecs) (f: function) (spec: ident * funspec) :=
  match spec with (i, mk_funspec _ A pre post) => semax_body G f A pre post end.

Lemma typecheck_val_ptr_lemma:
  forall rho Delta id t a init,
  typecheck_environ rho Delta = true ->
  (temp_types Delta) ! id =  Some (Tpointer t a, init) ->
  bool_val (eval_id rho id) (Tpointer t a) = Some true ->
  typecheck_val (eval_id rho id) (Tpointer t a) = true.
Proof.
Admitted.

(*
Lemma bool_val_notbool_ptr:
    forall v t a,
   (bool_val (force_val (sem_notbool v (Tpointer t a))) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.
*)

Lemma bool_val_notbool_ptr:
    forall v t,
   match t with Tpointer _ _ => True | _ => False end ->
   (bool_val (force_val (sem_notbool v t)) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.

Hint Rewrite bool_val_notbool_ptr using (solve [simpl; auto]) : normalize.
Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : normalize.

Lemma lseg_unroll': forall T {ls: listspec T} l x z , 
    lseg T l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || 
                          (EX h:val, EX r:list val, EX y:val, 
                          !! (~ptr_eq x z) &&  !!(l=h::r) && 
                       field_mapsto Share.top (x, list_struct) list_data (h, list_dtype) 
                      * field_mapsto Share.top (x, list_struct) list_link (y, T)
                      * |> lseg T r y z).
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
normalize.
apply orp_right1; auto.
apply orp_right2.
apply exp_right with v.
apply exp_right with l.
normalize. intro y.
apply exp_right with y.
normalize.
apply orp_left; auto.
normalize.
normalize.
intros. inv H0.
apply orp_left.
normalize.
inv H0.
normalize.
intros.
inv H0.
apply exp_right with x2.
normalize.
Qed.

Definition ilseg_nil (l: list  int) x z := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons l x z := 
                          (EX h:int, EX r:list int, EX y:val, 
                          !! (~ptr_eq x z) &&  !!(l=h::r) && 
                       field_mapsto Share.top (x, list_struct) list_data (Vint h, P.t_int) 
                      * field_mapsto Share.top (x, list_struct) list_link (y, P.t_listptr)
                      * |> ilseg r y z).

Lemma ilseg_unroll': forall l x z , 
    ilseg l x z = ilseg_nil l x z || ilseg_cons l x z.
Proof.
intros.
unfold ilseg at 1.
rewrite lseg_unroll'.
unfold ilseg_cons, ilseg_nil, ilseg.
f_equal.
f_equal. f_equal.
f_equal.
apply prop_ext; split; intro; destruct l; simpl in *; congruence.
apply pred_ext; normalize.
intros h r ? y. destruct l; inv H0.
apply exp_right with i.
apply exp_right with l.
apply exp_right with y.
normalize.
intros h r y.
apply exp_right with (Vint h).
apply exp_right with (map Vint r).
apply exp_right with y.
simpl.
normalize.
Qed.


Lemma semax_pre':
 forall (P': assert) Delta G (P: assert) c R,
   (fun rho => !! (typecheck_environ rho Delta = true)) && P |-- P' ->   
  semax Delta G P' c R  -> semax Delta G P c R.
Proof. intros; apply semax_pre with P'; auto. 
intros.
eapply derives_trans; [ | apply H].
simpl; apply andp_right; auto.
normalize.
Qed.

Lemma expr_true_Cnot_ptr: 
  forall e, match typeof e with Tpointer _ _ => True | _ => False end ->
     forall rho,  (expr_true (Cnot e) rho) = (eval_expr rho e = nullval).
Proof.
intros.
 unfold expr_true, Cnot.
 apply bool_val_notbool_ptr; auto.
Qed.
Hint Rewrite expr_true_Cnot_ptr using (solve [simpl; auto]) : normalize.

Lemma expr_true_Cnot_ptr': 
  forall e, match typeof e with Tpointer _ _ => True | _ => False end ->
    local (expr_true (Cnot e)) = local (fun rho => eval_expr rho e = nullval).
Proof.
 intros. extensionality rho. unfold local. f_equal. apply expr_true_Cnot_ptr; auto.
Qed.
Hint Rewrite expr_true_Cnot_ptr' using (solve [simpl; auto]) : normalize.

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
Hint Rewrite local_unfold : normalize.

Lemma body_sumlist: semax_body' Gprog P.f_sumlist sumlist_spec.
Proof.
intro contents.
simpl fn_body; simpl fn_params; simpl fn_return.
normalize.
apply forward_set; [compute; auto | compute; auto | auto with closed | compute; auto | ].
apply forward_set; [compute; auto | compute; auto | auto with closed | compute; auto | ].
forward_while (sumlist_Inv contents)
    (fun rho => !!(fold_right Int.add Int.zero contents = force_int (eval_id rho P.i_s))).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv; intros; simpl; normalize.
apply exp_right with contents.
rewrite H0. rewrite H1.  simpl.
rewrite Int.add_zero_l. normalize.
(* Prove that loop invariant implies typechecking condition *)
intros; unfold tc_expr; simpl; normalize.
(* Prove that invariant && not loop-cond implies postcondition *)
intro rho.
normalize.
unfold sumlist_Inv.
simpl.
apply exp_left; intro cts.
normalize.
rewrite H0.
rewrite H.
unfold ilseg; rewrite lseg_eq; auto.
normalize.
destruct cts; inv H1. simpl. normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1. normalize.
apply extract_exists_pre; auto;  intro cts.

apply semax_pre with
(local (expr_true (Etempvar P.i_t P.t_listptr)) &&
 (fun rho => !!(fold_right Int.add Int.zero contents =
       Int.add (force_int (eval_id rho P.i_s))
         (fold_right Int.add Int.zero cts))) &&
 (fun rho => ilseg_cons cts (eval_id rho P.i_t) nullval)).
intro.
simpl.
rewrite ilseg_unroll'. auto.
unfold ilseg_cons, ilseg_nil.
intro.
normalize.
apply orp_left.
normalize.
unfold expr_true, bool_val in H1. simpl in H1.
unfold ptr_eq in H2. destruct (eval_id rho P.i_t); simpl in *; try contradiction.
rewrite H2 in H1; inv H1.
normalize. intros h r ? y.
apply exp_right with h; normalize. apply exp_right with r; normalize.
apply exp_right with y; normalize.
unfold ilseg_cons.
match goal with |- semax _ _ (_ && _ && ?P) _ _ => 
  change P with (EX  h : int, EX  r : list int, EX  y : val,  
      fun rho => !!(~ ptr_eq (eval_id rho P.i_t) nullval) && !!(cts = h :: r) &&
      field_mapsto Share.top (eval_id rho P.i_t, list_struct) list_data
        (Vint h, P.t_int) *
      field_mapsto Share.top (eval_id rho P.i_t, list_struct) list_link
        (y, P.t_listptr) * |>ilseg r y nullval)
 end.
normalize. apply extract_exists_pre; [apply Int.zero | intro h].
normalize. apply extract_exists_pre; [apply nil | intro r].
normalize. apply extract_exists_pre; [apply Vundef | intro y].
simpl.

match goal with |- semax _ _ ?P _ _ => 
  apply semax_pre with (!!(cts = h::r) && P)
end.
intro; normalize.
apply semax_extract_prop.
intro; subst cts.

apply semax_pre with
  (fun rho : environ =>
  !!(map (fun i : int => (Vint i, P.t_int)) cts = (h, P.t_int) :: r /\
      typecheck_val h P.t_int = true /\ typecheck_val y P.t_listptr = true) &&
   (expr_true (Etempvar P.i_t P.t_listptr) rho &&
   !!(fold_right Int.add Int.zero contents =
      Int.add (force_int (eval_id rho P.i_s))
        (fold_right Int.add Int.zero cts)) &&
   field_mapsto Share.top (eval_id rho P.i_t, P.t_list) P.i_h  (h, P.t_int) *
   field_mapsto Share.top (eval_id rho P.i_t, P.t_list) P.i_t  (y, P.t_listptr) *
     |>lseg r (y, P.t_listptr) (nullval, P.t_listptr))).
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
eapply sequential; [intros; simpl; reflexivity | ].
pose (Q := 
       ((fun rho => field_mapsto Share.top ((eval_lvalue rho e1), typeof e1) P.i_h (h, P.t_int)) * P)).
apply semax_seq with Q.
apply semax_post with (normal_ret_assert Q).
normalize.
evar (Q3: assert).
apply semax_pre with Q3; [ unfold Q3 |  unfold Q3; eapply semax_load_field; eauto].
intros. unfold e1.
simpl.
apply andp_right.
apply prop_right.
simpl. split3; auto. split; auto.
clear - H2.
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




