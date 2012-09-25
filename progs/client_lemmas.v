Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Lemma prop_andp_right {A}{NA: NatDed A}: forall (P: Prop) Q R, P -> Q |-- R -> Q |-- !!P && R.
Proof.
 repeat intro.
 apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma prop_andp_left {A}{NA: NatDed A}: forall (P: Prop) Q R, (P -> Q |-- R) -> !!P && Q |-- R.
Proof.
 repeat intro.
 apply imp_andp_adjoint. apply prop_left; intro.
 apply imp_andp_adjoint. rewrite TT_andp. auto.
Qed.


Lemma semax_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (R' |-- R) ->
   semax Delta G P c R' ->  semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

Lemma semax_pre:
 forall P' Delta G P c R,
     (local (tc_environ Delta) && P |-- P') ->
     semax Delta G P' c R  -> semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
Qed.

Lemma env_gss:
  forall rho id v t, eval_expr (Etempvar id t)  (env_set rho id v) = v.
Proof.
intros. simpl. normalize.
Qed.

Hint Rewrite eval_id_other using solve [auto; clear; intro Hx; inversion Hx] : normalize.

Lemma env_gso:
  forall rho id id' v t, id <> id' -> 
      eval_expr (Etempvar id t) (env_set rho id' v) = eval_expr (Etempvar id t) rho.
Proof.
intros. simpl; normalize.
Qed.

Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.

Lemma extract_exists_pre:
      forall
        (A : Type) (P : A -> assert) (c : Clight.statement)
         Delta (G : funspecs) (R : ret_assert),
       (forall x : A, semax Delta G (P x) c R) ->
       semax Delta G (exp (fun x => P x)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R)).
intros ek vl.
unfold existential_ret_assert.
apply exp_left; auto.
apply extract_exists; auto.
Qed.

Lemma sequential: 
    forall Q Delta G P c R,
            (forall vl, R EK_normal vl = Q) ->
               semax Delta G P c (normal_ret_assert Q) -> semax Delta G P c R.
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto.
intros.
unfold normal_ret_assert.
intros ? ?; normalize.  rewrite H; auto.
Qed.

Lemma sequential': 
    forall Q Delta G P c R,
               semax Delta G P c (normal_ret_assert Q) -> 
               semax Delta G P c (overridePost Q R).
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto.
intros.
unfold normal_ret_assert, overridePost.
intros ? ?.
normalize.
rewrite if_true; auto.
Qed.

Lemma field_offset_rec_unroll:
  forall fields0 fld sid fields n,
    field_offset_rec fld (unroll_composite_fields sid (Tstruct sid fields0 noattr) fields) n =
    field_offset_rec fld fields n.
Proof.
intros. revert n; induction fields; intros; auto.
unfold unroll_composite_fields, field_offset.
simpl. if_tac.
f_equal.
f_equal.
change (alignof (unroll_composite  sid (Tstruct sid fields0 noattr) t) = alignof t).
apply alignof_unroll_composite.
change (field_offset_rec fld  (unroll_composite_fields sid (Tstruct sid fields0 noattr) fields)
             (align n (alignof (unroll_composite sid (Tstruct sid fields0 noattr) t)) 
                          + sizeof (unroll_composite sid (Tstruct sid fields0 noattr) t)) = 
    field_offset_rec fld fields (align n (alignof t) + sizeof t)).
rewrite IHfields.
rewrite alignof_unroll_composite.
rewrite sizeof_unroll_composite.
auto.
Qed.

Lemma field_offset_unroll:
  forall fields0 fld sid fields,
    field_offset fld (unroll_composite_fields sid (Tstruct sid fields0 noattr) fields) =
    field_offset fld fields.
Proof.
intros.
apply field_offset_rec_unroll.
Qed.

Lemma with_prop {A} {NA: NatDed A}{SA: SepLog A}:
   forall (Q: A)(P: Prop), 
           (Q |-- !!P) -> Q= !!P && Q.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
apply andp_left2.
auto.
Qed.


Fixpoint type_of_field (f: fieldlist) (fld: ident) : type :=
 match f with
 | Fnil => Tvoid
 | Fcons i t fl => if eq_dec i fld then t else type_of_field fl fld
 end.

Definition field_mapsto (sh: Share.t) (t1: type) (fld: ident) (v1 v2: val) : mpred :=
 match v1, t1 with
  | Vptr l ofs, Tstruct id fList  att =>
    let fList' := unroll_composite_fields id t1 fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList',  access_mode t2 with
     | Errors.OK delta, By_value ch => 
          !! (typecheck_val v2 t2 = true) && 
           address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)  (l, Int.unsigned (Int.add ofs (Int.repr delta)))
     | _, _ => FF
     end
  | _, _  => FF
  end.

Lemma field_mapsto_typecheck_val:
  forall t fld sh x y id fList att, 
     t = Tstruct id fList att ->
     field_mapsto sh t fld x y = 
               !! (typecheck_val y (type_of_field (unroll_composite_fields id t fList) fld) = true) && field_mapsto sh t fld x y.
Proof.
intros. subst.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
destruct x; normalize.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
destruct (access_mode
    (type_of_field (unroll_composite_fields id (Tstruct id fList att) fList) fld)); normalize.
Qed.

Lemma field_mapsto_nonnull:  forall t fld sh x y, 
     field_mapsto sh t fld x y = 
               !! (bool_val x (Tpointer t noattr) = Some true) && field_mapsto sh t fld x y.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
unfold bool_val.
destruct x; normalize.
Qed.

Lemma field_mapsto_access_mode:
  forall sh v t fld v' id fList att,
   t = Tstruct id fList att ->
  field_mapsto sh t fld v v' = 
   !! (exists ch, access_mode (type_of_field (unroll_composite_fields id t fList) fld) = By_value ch) 
           && field_mapsto sh t fld v v'.
Proof.
intros. subst.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
destruct v; normalize.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
case_eq (access_mode
    (type_of_field
       (unroll_composite_fields id (Tstruct id fList att) fList) fld)); intros; normalize.
apply prop_right; eauto.
Qed.

Lemma type_eq_refl:
 forall t, proj_sumbool (type_eq t t) = true.
Proof.
intros.
apply proj_sumbool_is_true.
auto.
Qed.

Lemma semax_load_field:
forall (Delta: tycontext) (G: funspecs) sh id t1 fld P e1 v2 t2 i2 sid fields ,
    lvalue_closed_wrt_vars (eq id) (e1) ->
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
  forall (TC0: t1 = typeof e1) 
          (TC1: typecheck_val v2 t2 = true)
          (TC2: t2 =
           type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld),
    semax Delta G 
       (local (tc_lvalue Delta e1) &&
    |> (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) (lift0 v2) * subst id (lift0 v2) P))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) (lift0 v2) * P)).
Proof with normalize.
pose proof I.
intros.
subst t1.
rename H2 into TE1.
assert (TC5: type_is_volatile t2 = false).
admit.  (* typechecking proof *)
assert (TC3: local (tc_lvalue Delta e1) |-- local (tc_lvalue Delta (Efield e1 fld t2))).
intros.
intro rho.
unfold tc_lvalue.
apply prop_left; intro.
apply prop_right.
hnf in H2|-*.
simpl.
split.  split; auto.
rewrite H1; simpl.
clear - TC2.
admit.  (* easy *)
rewrite TC5.
simpl. auto.
evar (P': assert).
evar (Q': assert).
apply (semax_pre_post
            (local (tc_temp Delta id (typeof (Efield e1 fld t2))) &&
             local (tc_lvalue Delta (Efield e1 fld t2)) &&
              |> (P' * subst id (lift0 v2)  P))
            (normal_ret_assert (Q' * P))).
3: apply semax_load.
intros.
normalize.
apply andp_right.
apply andp_right.
intro rho.
simpl.
unfold tc_temp.
unfold typecheck_temp_id. simpl. rewrite TE1.
unfold local, lift1, lift0.
apply prop_right; apply eqb_type_refl.
apply andp_left2. apply andp_left1; auto.
apply andp_left2. apply andp_left2.
apply later_derives.
apply sepcon_derives; auto.
unfold P'.
unfold mapsto'.
unfold lift2,lift0. intro rho.
erewrite (field_mapsto_access_mode sh (eval_lvalue e1 rho)  (typeof e1) fld v2 sid fields noattr); auto.
normalize.
destruct H2 as [ch H3].
rewrite H1.
rewrite <- H1 in TC2.
rewrite <- TC2 in H3.
simpl typeof. rewrite H3.
instantiate (1:=sh).
unfold field_mapsto.
case_eq (eval_lvalue e1 rho); intros; normalize.
case_eq (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)); intros; normalize.
rewrite <- H1; rewrite <- TC2; rewrite H3.
normalize.
simpl.
rewrite H2.
rewrite H1.
rewrite field_offset_unroll in H4. rewrite H4.
auto.

unfold Q'.
unfold mapsto'.
case_eq (access_mode (typeof (Efield e1 fld t2))); intros; normalize.
intros ? ? ?.
apply normal_ret_assert_derives...
apply sepcon_derives; auto.
simpl in H2.

simpl.
case_eq (eval_lvalue e1 x1); 
     intros; normalize.
rewrite H1.
unfold field_mapsto. unfold lift2. unfold lift0.
rewrite H3.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- TC2.
rewrite H2.
normalize.
intros ? ?; normalize.
intros ? ?; normalize.
intros ? ?; normalize.

intro; intros.
simpl.
rewrite <- H0.
auto.
auto.
Qed.

Global Opaque field_mapsto.

Lemma overridePost_normal:
  forall P R, overridePost P R EK_normal nil = P.
Proof.
 intros. unfold overridePost. rewrite if_true by auto.
 apply prop_true_andp. auto.
Qed.
Hint Rewrite overridePost_normal : normalize.

Lemma eval_expr_Etempvar: 
  forall i t, eval_expr (Etempvar i t) = eval_id i.
Proof. reflexivity.
Qed.
Hint Rewrite eval_expr_Etempvar : normalize.

Definition tc_val (t: type) (v: val) : Prop := typecheck_val v t = true.
Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B) 
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3):  environ -> B := 
     fun rho => P (f1 rho) (f2 rho) (f3 rho).

Definition app1 (f: val -> mpred) (a1: ident*type) : assert := 
   local (lift1 (tc_val (snd a1)) (eval_id (fst a1))) && lift1 f (eval_id (fst a1)).
Definition app2 (f: val -> val -> mpred) (a1 a2: ident*type) : assert := 
  local (lift1 (tc_val (snd a1)) (eval_id (fst a1))) &&
  local (lift1 (tc_val (snd a2)) (eval_id (fst a2))) &&
  lift2 f (eval_id (fst a1)) (eval_id (fst a2)).
Definition app3 (f: val -> val -> val -> mpred) (a1 a2 a3: ident*type) : assert := 
  local (lift1 (tc_val (snd a1)) (eval_id (fst a1))) &&
  local (lift1 (tc_val (snd a2)) (eval_id (fst a2))) &&
  local (lift1 (tc_val (snd a3)) (eval_id (fst a3))) &&
  lift3 f (eval_id (fst a1)) (eval_id (fst a2)) (eval_id (fst a3)).
Definition bind0 (f: mpred) (args: list val) : mpred := 
     match args with nil => f | _ => FF end.

Lemma bind0_e: forall f, bind_args nil (bind0 f) = lift0 f.
Proof. intros. unfold bind_args, bind0. extensionality rho; simpl.
 apply prop_true_andp. auto.
Qed.

Definition bind1 (f: val -> mpred) (args: list val): mpred :=
       match args with a::nil => f a | _ => FF end.

Lemma bind1_e: forall a1 f,
   bind_args (a1::nil) (bind1 f)  = app1 f a1.
Proof. 
 intros; unfold bind_args, bind1, app1;  simpl. 
 extensionality rho.
 f_equal.
 rewrite andb_true_r; auto.
Qed.

Definition bind2 (f: val -> val -> mpred) (args: list val): mpred :=
       match args with a::b::nil => f a b | _ => FF end.

Lemma bind2_e: forall a1 a2 f,
   bind_args (a1::a2::nil) (bind2 f)  = app2 f a1 a2.
Proof. 
 intros; unfold bind_args, bind2, app2;  simpl. 
 extensionality rho.
 f_equal.
 unfold tc_val, local, lift1.
 rewrite andb_true_r; auto.
 destruct (typecheck_val (eval_id (fst a1) rho) (snd a1)); simpl;  normalize.
 destruct (typecheck_val (eval_id (fst a2) rho) (snd a2)); simpl;  normalize.
 rewrite andp_comm. rewrite prop_true_andp; auto.
Qed.

Hint Rewrite bind0_e bind1_e bind2_e: normalize.

Notation "'WITH' x 'PRE' [ ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tnil, tz) _
             (fun x => bind0 P%logic) 
             (fun x => bind1 (fun z => Q%logic)))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100).
Notation "'WITH' x : tx  'PRE' [ ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tnil, tz) _
             (fun (x : tx) => bind0 P%logic)
             (fun (x : tx) => bind1 (fun z => Q%logic)))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100).

Notation "'WITH' x 'PRE' [ a : ta ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta Tnil, tz) _
             (fun x => bind1 (fun a => P%logic))
             (fun x => bind1 (fun z => Q%logic)))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).
Notation "'WITH' x : tx 'PRE' [ a : ta ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta Tnil, tz) _
             (fun (x:tx) => bind1 (fun a => P%logic))
             (fun (x:tx) => bind1 (fun z => Q%logic)))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Notation "'WITH' x 'PRE' [ a : ta , b : tb ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta (Tcons tb Tnil), tz) _
             (fun x => bind2 (fun a b => P%logic)) 
             (fun x => bind1 (fun z => Q%logic)))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).
Notation "'WITH' x : tx 'PRE' [ a : ta , b : tb ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta (Tcons tb Tnil), tz) _
             (fun (x:tx) => bind2 (fun a b => P%logic)) 
             (fun (x:tx) => bind1 (fun z => Q%logic)))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).


Lemma bool_val_int_eq_e: 
  forall i j, bool_val (Val.of_bool (Int.eq i j)) type_bool = Some true -> i=j.
Proof.
 intros.
 apply Clight_lemmas.of_bool_Int_eq_e'.
 forget (Val.of_bool (Int.eq i j)) as v.
 destruct v; simpl in *; try discriminate; auto.
 inv H. intro. subst. rewrite Int.eq_true in H1. inv H1.
Qed.

Fixpoint temp_free_in (id: ident) (e: expr) := 
 match e with
 | Econst_int _ _ => false
 | Econst_float _ _ => false
 | Evar _ _ => false
 | Etempvar i _ => eqb_ident id i
 | Ederef e1 _ => temp_free_in id e1
 | Eaddrof e1 _ => temp_free_in id e1
 | Eunop _ e1 _ => temp_free_in id e1
 | Ebinop _ e1 e2 _ => orb (temp_free_in id e1) (temp_free_in id e2) 
 | Ecast e1 _ => temp_free_in id e1
 | Econdition e0 e1 e2 _ => orb (temp_free_in id e0) (orb (temp_free_in id e1) (temp_free_in id e2)) 
 | Efield e1 _ _ => temp_free_in id e1
end.

Lemma forward_set:
  forall Delta G P id e c Q,
  typecheck_temp_id id (typeof e) Delta = true ->
  temp_free_in id e = false ->
  closed_wrt_vars (modified1 id) P ->
  (forall rho, tc_expr Delta e rho) ->
  semax (initialized id Delta) G
             (local (lift2 eq (eval_id id) (eval_expr e)) && P)
             c Q ->
  semax Delta G P (Ssequence (Sset id e) c) Q.
Proof.
 intros.
 eapply semax_seq; [ | apply H3].
 apply sequential'.
 eapply semax_pre; [ |  apply semax_set].
 clear H3.
 unfold local, lift2, lift1, lift0; intro rho. simpl.
 normalize.
 eapply derives_trans; [ |apply now_later].
 unfold subst.
 normalize. 
 apply andp_right.
 apply prop_right.
 clear - H0.
 admit.  (* straightforward *)
 specialize (H1 rho (PTree.set id (eval_expr e rho) (te_of rho))).
 rewrite H1.
 unfold env_set. auto.
 intros. unfold modified1. destruct (eq_dec i id); auto.
 rewrite PTree.gso; auto.
Qed.


Lemma closed_wrt_andp: forall S P Q,
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P && Q).
Admitted.

Lemma closed_wrt_sepcon: forall S P Q,
  closed_wrt_vars S P -> closed_wrt_vars S Q ->
  closed_wrt_vars S (P * Q).
Admitted.

Lemma closed_wrt_app1: forall a b f,
  a<> fst b -> closed_wrt_vars (modified1 a) (app1 f b).
Proof.
 intros.  intro; intros.
 unfold app1. unfold local, lift0, lift1, tc_val. simpl.
 specialize (H0 (fst b)).
 destruct H0. hnf in H0.  subst; congruence.
 unfold eval_id; simpl. rewrite H0; auto.
Qed.


Lemma closed_wrt_ideq: forall a b e,
  a <> b ->
  temp_free_in a e = false ->
  closed_wrt_vars (modified1 a) (fun rho => !! (eval_id b rho = eval_expr e rho)).
Proof.
Admitted.

Hint Resolve closed_wrt_andp closed_wrt_sepcon : closed.

Hint Extern 2 (closed_wrt_vars (modified1 _) (app1 _ _)) => 
      (apply closed_wrt_app1; solve [let Hx := fresh in (intro Hx; inv Hx)]) : closed.


Hint Extern 2 (closed_wrt_vars (modified1 _) _) => 
      (apply closed_wrt_ideq; [solve [let Hx := fresh in (intro Hx; inv Hx)] | reflexivity]) : closed.



Lemma unfold_lift0: forall {A} (f: A)  rho,  lift0 f rho = f.
Proof. reflexivity. Qed.


Lemma unfold_app1: forall f a1 t1,  app1 f (a1,t1) = 
    local (lift1 (tc_val t1) (eval_id a1)) && lift1 f (eval_id a1).
Proof. intros; extensionality rho; reflexivity. Qed.

Lemma unfold_app2: forall f a1 t1 a2 t2, app2 f (a1,t1) (a2,t2) = 
   local (lift1 (tc_val t1) (eval_id a1)) && 
   local (lift1 (tc_val t2) (eval_id a2)) && 
    lift2 f (eval_id a1) (eval_id a2).
Proof. intros; extensionality rho; reflexivity. Qed.

Lemma unfold_app3: forall f a1 t1 a2 t2 a3 t3, app3 f (a1,t1) (a2,t2) (a3,t3) =
   local (lift1 (tc_val t1) (eval_id a1)) && 
   local (lift1 (tc_val t2) (eval_id a2)) && 
   local (lift1 (tc_val t3) (eval_id a3)) && 
    lift3 f (eval_id a1) (eval_id a2) (eval_id a3).
Proof. intros; extensionality rho; reflexivity. Qed.

Hint Rewrite @unfold_lift0 unfold_app1 unfold_app2 unfold_app3: normalize.

Ltac forward_while Inv Postcond :=
  apply semax_pre with Inv; 
  [ | apply semax_seq with Postcond;
    [ apply semax_while ; [ | compute; auto | | ] | ]].
