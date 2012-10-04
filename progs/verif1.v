Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import compcert.Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.list.

Local Open Scope logic.

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

Definition semax_body' (G:  funspecs) (f: function) (spec: ident * funspec) :=
  match spec with (i, mk_funspec _ A pre post) => semax_body G f A pre post end.

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
                          !! (ptr_neq x z) &&  !!(l=h::r) && 
                       field_mapsto Share.top list_struct list_data x h 
                      * field_mapsto Share.top list_struct list_link x y
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

Definition ilseg_nil (l: list  int) x z : mpred := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons l x z : mpred := 
                          (EX h:int, EX r:list int, EX y:val, 
                          !! (ptr_neq x z) &&  !!(l=h::r) && 
                       field_mapsto Share.top list_struct list_data x (Vint h) 
                      * field_mapsto Share.top list_struct list_link x y
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

Lemma ilseg_eq: forall s p, 
   typecheck_val p P.t_listptr = true -> 
    (ilseg s p p = !!(s=nil) && emp).
Proof. intros. unfold ilseg. rewrite lseg_eq; auto. f_equal. f_equal.
 apply prop_ext. destruct s; simpl; intuition congruence.
Qed.
Hint Rewrite ilseg_eq : normalize.

Lemma ilseg_nonnull:
  forall s v,
      typed_true P.t_listptr v ->
     ilseg s v nullval = ilseg_cons s v nullval.
Proof.
intros. subst. 
rewrite ilseg_unroll'.
unfold ilseg_cons, ilseg_nil.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
intros.
apply orp_right2. apply exp_right with x; normalize. apply exp_right with x0; normalize.
apply exp_right with x1; normalize.
Qed.

Lemma lift2_ilseg_cons: 
 forall s p q, lift2 (ilseg_cons s)  p q =
    EX h:int, EX r: list int, EX y: val,
      local (lift2 ptr_neq p q) &&
      !! (s = h::r) &&
      lift2 (field_mapsto Share.top list_struct list_data) p (lift0 (Vint h)) *
      lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) *
      |> lift2 (ilseg r) (lift0 y) q.
Proof. reflexivity. Qed.
Hint Rewrite lift2_ilseg_cons : normalize.

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH contents 
  PRE [ P.i_p : P.t_listptr]  lift2 (ilseg contents) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_int ]  local (lift1 (eq (Vint (fold_right Int.add Int.zero contents))) retval).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH contents : list int
  PRE  [ P.i_p : P.t_listptr ] lift2 (ilseg contents) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_listptr ] lift2 (ilseg (rev contents)) retval (lift0 nullval).

Definition main_spec := (P.i_main, mk_funspec (nil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL ((* lift1 (tc_val P.t_int) (eval_id P.i_s); *)
                                     lift1 (partial_sum contents cts) (eval_id P.i_s)) 
            SEP (TT * lift2 (ilseg cts) (eval_id P.i_t) (lift0 nullval))).


Lemma semax_pre:
 forall P' Delta G P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     semax Delta G P' c R  -> 
     semax Delta G (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof.
intros.
eapply semax_pre; try apply H0.
 rewrite insert_local. auto.
Qed.

Ltac forward_while Inv Postcond :=
  apply semax_pre with Inv; 
  [ | apply semax_seq with Postcond;
    [ apply semax_while ; [ | compute; auto | | ] | ]].

Hint Rewrite insert_local:  normalize.

Lemma exp_derives {A}{NA: NatDed A}{B}:
   forall F G: B -> A, (forall x, F x |-- G x) -> exp F |-- exp G.
Proof.
intros.
apply exp_left; intro x. apply exp_right with x; auto.
Qed.

Lemma lift_ilseg_cons_unfold:
   forall s p q, lift2 (ilseg_cons s) p q =
       EX h: int, EX r: list int, EX y: val,
         local (lift2 ptr_neq p q) && !!(s = h :: r) &&
         lift2 (field_mapsto Share.top list_struct list_data) p (lift0 (Vint h)) *
         lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) * |> lift2 (ilseg r) (lift0 y) q.
Proof. intros; extensionality rho; reflexivity.
Qed.
 

Ltac find_in_list A L :=
 match L with 
  | A :: _ => constr:(O)
  | _ :: ?Y => let n := find_in_list A Y in constr:(S n)
  | nil => fail
  end.

Fixpoint delete_nth {A} (n: nat) (xs: list A) {struct n} : list A :=
 match n, xs with
 | O, y::ys => ys
 | S n', y::ys =>y :: delete_nth n' ys
 | _ , _ => nil
 end.


Lemma grab_nth_LOCAL':
   forall n B P Q R,
    do_canon B (PROPx P (LOCALx Q (SEPx R))) = 
    do_canon (local (nth n Q (lift0 True)) && B) (PROPx P (LOCALx (delete_nth n Q) (SEPx R))).
Proof.
intros n B P Q R; revert n Q B.
induction n; intros.
destruct Q; simpl nth. unfold delete_nth.
f_equal.
extensionality rho; unfold local, lift0,lift1. simpl. normalize.
rewrite canon2; auto.
destruct Q; simpl nth; unfold delete_nth; fold @delete_nth.
autorewrite with canon.
f_equal.
extensionality rho; unfold LOCALx; simpl.
unfold local, lift1, lift2.
f_equal.
f_equal.
apply prop_ext; intuition.
extensionality rho; unfold local, lift0,lift1. simpl.
rewrite <- canon2.
rewrite <- canon2.
rewrite IHn.
f_equal.
clear rho.
unfold local, lift0, lift1, lift2; extensionality rho.
simpl.
apply pred_ext; normalize.
Qed.

Lemma grab_nth_LOCAL:
   forall n B P Q R,
    do_canon B (PROPx P (LOCALx Q (SEPx R))) = 
    do_canon (local (nth n Q (lift0 True)) && B) (PROPx P (LOCALx Q (SEPx R))).
Proof.
intros n B P Q R; revert n Q B.
induction n; intros.
destruct Q; simpl nth.
f_equal.
extensionality rho; unfold local, lift0,lift1. simpl. normalize.
rewrite canon2.
f_equal.
f_equal.
extensionality rho; unfold LOCALx; simpl.
f_equal.
unfold local, lift1, lift2.
f_equal.
apply prop_ext; intuition.
destruct Q; simpl nth.
f_equal.
extensionality rho; unfold local, lift0,lift1. simpl. normalize.
rewrite <- canon2.
rewrite <- canon2.
rewrite IHn.
f_equal.
unfold local, lift0, lift1, lift2; extensionality rho.
simpl.
apply pred_ext; normalize.
Qed.

Lemma grab_nth_SEP:
   forall n B P Q R,
    do_canon B (PROPx P (LOCALx Q (SEPx R))) = do_canon (B* nth n R emp) (PROPx P (LOCALx Q (SEPx (delete_nth n R)))).
Proof.
intros n B P Q R; revert n R B.
induction n; intros.
destruct R.
simpl nth.  unfold delete_nth.
f_equal. extensionality rho; simpl; symmetry; apply sepcon_emp.
simpl nth.
unfold delete_nth.
rewrite canon3 by apply I. auto.
destruct R.
simpl nth.  unfold delete_nth.
f_equal. extensionality rho; simpl; symmetry; apply sepcon_emp.
rewrite <- canon3 by apply I.
rewrite (IHn _ (B*a)).
simpl nth.
replace (delete_nth (S n) (a::R)) with (a :: delete_nth n R) by reflexivity.
rewrite <- canon3 by apply I.
f_equal.
repeat rewrite sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

Lemma restart_canon: forall P Q R, (PROPx P (LOCALx Q (SEPx R))) = do_canon emp (PROPx P (LOCALx Q (SEPx R))).
Proof.
intros.
unfold do_canon. rewrite emp_sepcon. auto.
Qed.

Lemma ilseg_nonnullx: 
  forall s p q,
   local (lift1 (typed_true P.t_listptr) p) && lift2 (ilseg s) p q = 
   EX  h : int,
      EX  r : list int,
       EX  y : val,
         local (lift2 ptr_neq p q) && !!(s = h :: r) &&
         lift2 (field_mapsto Share.top list_struct list_data) p
           (lift0 (Vint h)) *
         lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) *
         |>lift2 (ilseg r) (lift0 y) q.
Admitted.

Lemma exp_do_canon:
   forall T (P: T -> assert) (Q: assert), do_canon (exp P) Q = EX x:_, do_canon (P x) Q.
Proof. apply exp_sepcon1. Qed.
Hint Rewrite exp_do_canon: canon.
Hint Rewrite exp_do_canon: normalize.

Ltac go_lower := 
 let rho := fresh "rho" in intro rho; unfold PROPx, LOCALx, SEPx; simpl; normalize.

Ltac replace_in_pre S S' :=
 match goal with |- semax _ _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in apply semax_pre with P'; [go_lower | ]
  end
 end.


Lemma semax_extract_PROP_True:
  forall Delta G (PP: Prop) P QR c Post,
        PP ->
        semax Delta G (PROPx P QR) c Post -> 
       semax Delta G (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply client_lemmas.semax_pre with (PROPx P QR).
unfold PROPx in *; simpl. normalize. auto.
Qed.

Lemma semax_extract_PROP:
  forall Delta G (PP: Prop) P QR c Post,
       (PP -> semax Delta G (PROPx P QR) c Post) -> 
       semax Delta G (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply client_lemmas.semax_pre with (!!PP && PROPx P QR).
unfold PROPx in *; simpl. normalize.
apply semax_extract_prop.
auto.
Qed.

Definition bind1' (i1: ident) (P: assert) (args: list val): mpred :=
   match args with a::nil => ALL rho: environ, !! (eval_id i1 rho = a) --> P rho
  | _ => FF
  end.

Lemma canon9: forall Q1 P Q R,
       local Q1 && (PROPx P (LOCALx Q R)) = 
         PROPx P (LOCALx (Q1::Q) R).
Proof.
intros; unfold PROPx, LOCALx; simpl.
extensionality rho.
normalize.
Admitted.
Hint Rewrite canon9: canon.

Ltac focus_SEP n := 
 rewrite restart_canon; rewrite (grab_nth_SEP n); unfold nth, delete_nth; normalize.


Lemma closed_wrt_subst:
  forall {A} id e (P: environ -> A), closed_wrt_vars (eq id) P -> subst id e P = P.
Proof.
intros.
unfold subst, closed_wrt_vars in *.
extensionality rho.
symmetry.
apply H.
intros.
destruct (eq_dec id i); auto.
right.
rewrite PTree.gso; auto.
Qed.

Lemma denote_tc_isptr1:
  forall Delta rho e,
   typecheck_environ rho Delta = true -> 
   denote_tc_assert (typecheck_expr Delta e) rho ->
   lift1 denote_tc_isptr (eval_expr e) rho.
Admitted.

Lemma subst_andp:
  forall id v P Q, subst id v (P && Q) = subst id v P && subst id v Q.
Admitted.

Lemma PROP_later_derives:
 forall P QR QR', QR |-- |>QR' ->
    PROPx P QR |-- |> PROPx P QR'.
Proof.
intros.
unfold PROPx.
normalize.
Qed.

Lemma LOCAL_later_derives:
 forall Q R R', R |-- |>R' -> LOCALx Q R |-- |> LOCALx Q R'.
Proof.
unfold LOCALx; intros; normalize.
rewrite later_andp.
apply andp_derives; auto.
apply now_later.
Qed.

Lemma SEP_later_derives:
  forall P Q P' Q', 
      P |-- |> P' ->
      SEPx Q |-- |> SEPx Q' ->
      SEPx (P::Q) |-- |> SEPx (P'::Q').
Proof.
intros.
intro rho.
specialize (H0 rho).
unfold SEPx in *; intros; normalize.
simpl.
rewrite later_sepcon.
apply sepcon_derives; auto.
apply H.
Qed.
Hint Resolve PROP_later_derives LOCAL_later_derives SEP_later_derives : derives.

Ltac type_of_field_tac :=
 simpl; 
  repeat first [rewrite if_true by auto 
                    | rewrite if_false by (let H:=fresh in intro H; inversion H)
                    | simpl; reflexivity].

Lemma lvalue_closed_tempvar:
 forall S i t, ~ S i -> lvalue_closed_wrt_vars S (Etempvar i t).
Admitted.
Hint Resolve lvalue_closed_tempvar : closed.


Hint Resolve  eval_expr_Etempvar.

Lemma eval_expr_Etempvar' : forall i t, eval_id i = eval_expr (Etempvar i t).
Proof. intros. symmetry; auto.
Qed.
Hint Resolve  eval_expr_Etempvar'.

Lemma semax_load_field':
forall (Delta: tycontext) (G: funspecs) sh id t1 fld P Q R e1 v2 t2 i2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
        (temp_types Delta) ! id = Some (t2,i2) ->
  forall 
          (TC2: t2 =
           type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld),
    semax Delta G 
       (|> do_canon 
             (local (tc_expr Delta e1) &&
              lift2 (field_mapsto sh t1 fld) (eval_expr e1) (lift0 v2))
            (PROPx P (LOCALx Q (SEPx R))))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (lift1 (eq v2) (eval_id id) :: map (subst id (lift0 old)) Q)
                (SEPx 
                  (map (subst id (lift0 old))
                    (lift2 (field_mapsto sh t1 fld) (eval_expr e1) (lift0 v2) :: R)))))).
Proof.
intros.
unfold do_canon.
eapply semax_pre_post;
  [ | |  apply (semax_load_field Delta G sh id t1 fld (PROPx P (LOCALx Q (SEPx R))) (Ederef e1 t1)
   v2 t2 i2 sid fields)].
match goal with |- ?P |-- _ => 
 let P' := strip1_later P in apply derives_trans with (|>P' ); [auto 50 with derives | ]
end.
apply later_derives.
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
go_lower.
unfold tc_expr, tc_lvalue.
simpl typecheck_lvalue.
simpl denote_tc_assert.
rewrite H0. rewrite H.
simpl.
normalize.
pose proof (denote_tc_isptr1 _ _ e1 H2 H3).
normalize.
hnf in H4.
destruct (eval_expr e1 rho); try contradiction.
auto.

unfold normal_ret_assert.
intros ek vl rho; normalize.
intro old; apply exp_right with old.
simpl.
normalize.
unfold subst.
unfold lift2.
unfold PROPx, LOCALx, SEPx.
simpl.
normalize.
apply andp_right.
apply prop_right.
unfold lift0.
clear - H4.
induction Q; simpl; auto.
destruct H4.
split; auto.
case_eq (eval_expr e1 (env_set rho id old)); intros;
 try solve [rewrite field_mapsto_nonnull; simpl bool_val; normalize; discriminate].
apply sepcon_derives; auto.
unfold lift0.
induction R; simpl; auto.
apply sepcon_derives; auto.
simpl. auto.
auto.
auto.
auto.
Qed.


Ltac simpl_tc_expr :=
    match goal with |- context [tc_expr ?A ?B] =>
        change (tc_expr A B) with (denote_tc_assert (typecheck_expr A B));
        simpl typecheck_expr; simpl denote_tc_assert
    end.


Lemma local_lift0: forall P, local (lift0 P) = prop P.
Proof.
intros. extensionality rho. reflexivity.
Qed.
Hint Resolve local_lift0: normalize.


Ltac extract_prop_in_LOCAL :=
 match goal with |- semax _ _ (PROPx _ (LOCALx ?Q _)) _ _ =>
   match Q with context [ lift0 ?z :: _ ] =>
        let n := find_in_list (lift0 z) Q
         in rewrite restart_canon; rewrite (grab_nth_LOCAL' n); 
              simpl nth; unfold delete_nth;
              rewrite local_lift0; cbv beta; autorewrite with canon
  end
end.

Ltac repeat_extract_exists_pre :=
   first [(apply extract_exists_pre;
             let x := fresh "x" in intro x; normalize;
                repeat_extract_exists_pre;
                revert x)
           | autorewrite with canon
          ].
               
Ltac extract_exists_in_SEP :=
 match goal with |- semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ exp ?z :: _] =>
        let n := find_in_list (exp z) R 
         in focus_SEP n; repeat_extract_exists_pre
  end
end.

Ltac flatten_sepcon_in_SEP :=
 match goal with |- semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ (?x * ?y) :: _] =>
        let n := find_in_list (x * y) R 
         in  rewrite restart_canon; rewrite (grab_nth_SEP n); unfold nth, delete_nth;
             autorewrite with canon
  end
end.

Ltac normalizex :=
  normalize;
  repeat 
  (first [ simpl_tc_expr
         | flatten_sepcon_in_SEP
          | apply semax_extract_PROP_True; [solve [auto] | ]
          | apply semax_extract_PROP; intro
         | extract_prop_in_LOCAL
         | extract_exists_in_SEP
         ]; cbv beta; normalize).

Ltac semax_field_tac1 := 
   eapply semax_load_field'; 
     [ reflexivity 
     | reflexivity 
     | simpl; reflexivity 
     | type_of_field_tac ].

Ltac semax_field_tac :=
match goal with |- semax ?Delta _ (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                  (Ssequence (Sset _ (Efield (Ederef ?e _) ?fld _)) _) _ =>
  apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
   [ go_lower 
   | match R with 
     | context [|> lift2 (field_mapsto ?sh ?struct ?fld') ?e' ?v] =>
          let H := fresh "EE" in assert (H: fld'=fld) by reflexivity;
          let n := find_in_list (|> lift2 (field_mapsto sh struct fld') e' v) R
             in focus_SEP n; rewrite (grab_nth_LOCAL 0); simpl nth;
                replace e' with (eval_expr e) by auto;
                rewrite H; clear H
     | context [ lift2 (field_mapsto ?sh ?struct ?fld') ?e' ?v] =>
          let H := fresh "EE" in assert (H: fld'=fld) by reflexivity;
         let n := find_in_list (lift2 (field_mapsto sh struct fld') e' v) R
             in focus_SEP n; rewrite (grab_nth_LOCAL 0); simpl nth;
                replace e' with (eval_expr e) by auto;
                rewrite H; clear H
     end;
     match goal with |- semax _ _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end;
   first [eapply semax_seq; [ apply sequential'; semax_field_tac1  
                                          | simpl update_tycon; apply extract_exists_pre
                                          ] 
(* should adjust the "semax_post" in the line below...
           | eapply semax_post; [ | apply sequential'; semax_field_tac1 ]
   *)
         ]
   ]
end; normalizex.


Lemma subst_lift2:
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b, 
          subst id v (lift2 f a b) = lift2 f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0: forall {A} id v (f: A),
        subst id v (lift0 f) = lift0 f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1:
  forall {A1 B} id v (f: A1 -> B) a, 
          subst id v (lift1 f a) = lift1 f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @subst_lift0 @subst_lift1 @subst_lift2 : normalize.

Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

Hint Rewrite @map_cons : normalize.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.

Hint Rewrite @map_nil : normalize.

Lemma subst_eval_id_eq:
 forall id v, subst id v (eval_id id) = v.
Proof. unfold subst, eval_id; intros. extensionality rho.
    unfold force_val, env_set; simpl. rewrite PTree.gss; auto.
Qed.

Lemma subst_eval_id_neq:
  forall id v j, id<>j -> subst id v (eval_id j) = eval_id j.
Proof.
    unfold subst, eval_id; intros. extensionality rho.
    unfold force_val, env_set; simpl. rewrite PTree.gso; auto.
Qed.

Hint Rewrite subst_eval_id_eq : normalize.
Hint Rewrite subst_eval_id_neq using (solve [auto with closed]) : normalize.


Lemma typed_false_ptr: 
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct v; try discriminate.
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H.
Qed.






Lemma canon20: forall PQR, do_canon emp PQR = PQR.
Proof.
intros. apply emp_sepcon.
Qed.
Hint Rewrite canon20: canon.


Lemma lift1_lift0:
 forall {A1 B} (f: A1 -> B) (x: A1), lift1 f (lift0 x) = lift0 (f x).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @lift1_lift0 : normalize.


Lemma forward_setx:
  forall Delta G P id e,
  typecheck_temp_id id (typeof e) Delta = true ->
  (forall rho, tc_expr Delta e rho) ->
  semax Delta G
             P
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  local (lift2 eq (eval_id id) (subst id (lift0 old) (eval_expr e))) &&
                            subst id (lift0 old) P)).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_set_forward Delta G P id e)].
eapply derives_trans ; [ | apply now_later].
go_lower.
intros ek vl rho; unfold normal_ret_assert. simpl; normalize.
intros old ?; apply exp_right with old.
normalize.
Qed.


Lemma subst_prop: forall i v P, subst i v (prop P) = prop P.
Proof.
intros; reflexivity.
Qed.
Hint Rewrite @subst_andp subst_prop : normalize.

Lemma fold_right_cons: forall {A B} (f: A -> B -> B) (z: B) x y,
   fold_right f z (x::y) = f x (fold_right f z y).
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_cons : normalize.

Lemma subst_sepcon: forall i v (P Q: assert),
  subst i v (P * Q) = (subst i v P * subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_sepcon : normalize.


Lemma subst_PROP: forall i v P Q R,
     subst i v (PROPx P (LOCALx Q (SEPx R))) =
    PROPx P (LOCALx (map (subst i v) Q) (SEPx (map (subst i v) R))).
Proof.
intros.
unfold PROPx.
normalize.
f_equal.
unfold LOCALx, local.
normalize.
f_equal.
extensionality rho.
unfold lift1.
f_equal.
induction Q; simpl; auto.
normalize.
f_equal; auto.
unfold SEPx.
induction R; auto.
normalize.
f_equal; auto.
Qed.
Hint Rewrite subst_PROP : normalize.

Ltac forward_setx := 
  (eapply semax_seq; [ apply sequential' ;  apply forward_setx; reflexivity 
                               | apply extract_exists_pre; normalize; try (intros _) ] ).


Lemma subst_eval_expr_const:
  forall i v n t, subst i v (eval_expr (Econst_int n t)) = eval_expr (Econst_int n t).
Proof.
intros. reflexivity.
Qed.
Hint Rewrite subst_eval_expr_const : normalize.

Lemma tc_formals_cons:
  forall i t rest, tc_formals ((i,t) :: rest) =
         lift2 and (lift1 (tc_val t) (eval_id i)) (tc_formals rest).
Proof.
intros.
extensionality rho; simpl.
unfold tc_formals; fold tc_formals.
unfold lift2. simpl.
apply prop_ext.
rewrite andb_true_iff.
intuition.
Qed.

Lemma tc_formals_nil : tc_formals nil = lift0 True.
Proof. intros; extensionality rho.  unfold tc_formals.  simpl. 
apply prop_ext; intuition.  hnf; auto. 
Qed.

Hint Rewrite tc_formals_cons tc_formals_nil: normalize.

Lemma local_lift2_and: forall P Q, local (lift2 and P Q) = 
        local P && local Q.
Proof. intros; extensionality rho. unfold local, lift1,lift2.   simpl. normalize. 
Qed.
Hint Rewrite local_lift2_and : normalize.


Lemma canon3b: forall R1 B P Q R,
    nonlocal R1 ->
    do_canon (R1* B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
rewrite (sepcon_comm R1 B).
apply canon3. auto.
Qed.
Hint Rewrite canon3b using check_nonlocal: canon.

Lemma subst_TT: forall i v, subst i v TT = TT.
Admitted.
Lemma subst_FF: forall i v, subst i v FF = FF.
Admitted.
Hint Rewrite subst_TT subst_FF: normalize.


Lemma sequential'':
  forall Delta G P c Q,
        semax Delta G P c (normal_ret_assert (Q EK_normal nil)) ->
          semax Delta G P c Q.
intros. eapply semax_post; eauto.
 intros. go_lower.
 unfold normal_ret_assert; simpl; normalize.
Qed.

Definition eval_binop (op: binary_operation) (t1 t2 : type) (v1 v2: val) :=
       force_val (sem_binary_operation op v1 t1 v2 t2 (fun _ _ => false)).
Lemma subst_eval_expr_binop:
  forall i v op t e1 e2, subst i v  (eval_expr (Ebinop op e1 e2 t)) =
           lift2 (eval_binop op (typeof e1) (typeof e2)) 
                     (subst i v (eval_expr e1)) 
                     (subst i v (eval_expr e2)).
Proof.
 intros. reflexivity.
Qed.
Hint Rewrite subst_eval_expr_binop : normalize.


Lemma tc_eval_id_i:
  forall Delta t i rho, 
               tc_environ Delta rho -> 
              (temp_types Delta)!i = Some (t,true) ->
              tc_val t (eval_id i rho).
Proof.
intros.
unfold tc_environ in H.
apply expr_lemmas.typecheck_environ_sound in H.
destruct H as [? _].
destruct (H i t true H0) as [v [? ?]].
unfold eval_id. rewrite H1. simpl; auto.
Qed.

Lemma local_lift0_True:     local (lift0 True) = TT.
Proof. reflexivity. Qed.
Hint Rewrite local_lift0_True : normalize.

Lemma body_sumlist: semax_body' Gprog P.f_sumlist sumlist_spec.
Proof.
intro contents.
simpl fn_body; simpl fn_params; simpl fn_return.
normalize.
canonicalize_pre.         
forward_setx.
forward_setx.
forward_while (sumlist_Inv contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P.i_s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with contents.
go_lower.
rewrite H0. rewrite H1. simpl. unfold partial_sum.
rewrite Int.add_zero_l. normalize.
rewrite sepcon_comm. apply sepcon_TT.
(* Prove that loop invariant implies typechecking condition *)
normalizex.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv.
go_lower.
intros cts ?.
unfold partial_sum in H0;  rewrite H0.
rewrite (typed_false_ptr H).
normalize.
apply prop_left; intro; subst; normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
normalize.
apply extract_exists_pre; intro cts.
normalize.
replace_in_pre (ilseg cts) (ilseg_cons cts).
   rewrite ilseg_nonnull by auto.
   unfold ilseg_cons.
   normalize. intros h r ? y.
   apply exp_right with h; normalize.
   apply exp_right with r; normalize.
   apply exp_right with y; normalize.
rewrite lift_ilseg_cons_unfold.
normalizex.
intros h r y.
normalizex. subst cts.

semax_field_tac.
semax_field_tac; intro old_t.

apply sequential''; simpl for1_ret_assert.

eapply semax_post;  [ | apply forward_setx; [reflexivity | solve [repeat split; hnf; auto]]];
  cbv beta; normalize.
(* Prove postcondition of loop body implies loop invariant *)
intros ek vl; unfold normal_ret_assert, for1_ret_assert.
normalize.
 intro x; unfold sumlist_Inv.
 apply exp_right with r.
 go_lower. 
 apply andp_right; 
 normalize.
 rewrite H0.
apply prop_right.
unfold partial_sum in *.
simpl in H4.
rewrite H4; clear H4. rewrite <- H1; clear H1.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
assert (exists n, x = Vint n).
clear - H1 H0.
rewrite H0 in H1. clear H0.
destruct x; inv H1. eauto.
destruct H4; subst x.
simpl.
symmetry; apply Int.add_assoc.
rewrite <- (sepcon_comm TT).
repeat rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
normalize.
(* After the loop *)
eapply semax_pre; [ | apply semax_return ].
go_lower.
apply prop_left; intro.
unfold frame_ret_assert.
simpl.
normalize.
apply andp_right; apply prop_right.
eapply tc_eval_id_i; eauto.
unfold retval.
normalize.
rewrite H0.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
clear - H1.
destruct (eval_id P.i_s rho); inv H1; auto.
Qed.


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




