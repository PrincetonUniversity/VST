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
intros; eapply semax_pre_post; eauto.
Qed.

Lemma semax_pre:
 forall P' Delta G P c R,
   (forall rho, typecheck_environ rho Delta = true ->  P  rho |-- P' rho) ->   semax Delta G P' c R  -> semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
Qed.

Lemma env_gss:
  forall rho id v t, eval_expr (env_set rho id v) (Etempvar id t) = v.
Proof.
intros. simpl. normalize.
Qed.

Hint Rewrite eval_id_other using solve [auto; clear; intro Hx; inversion Hx] : normalize.

Lemma env_gso:
  forall rho id id' v t, id <> id' -> 
      eval_expr (env_set rho id' v) (Etempvar id t) = eval_expr rho (Etempvar id t).
Proof.
intros. simpl; normalize.
Qed.

Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.

Lemma extract_exists_pre:
      forall
        (A : Type) (any: A) (P : A -> assert) (c : Clight.statement)
         Delta (G : funspecs) (R : ret_assert),
       (forall x : A, semax Delta G (P x) c R) ->
       semax Delta G (fun rho => exp (fun x => P x rho)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R)).
intros ek vl rho.
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
intros ? ? ?; normalize.  rewrite H; auto.
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
intros ? ? ?.
normalize.
rewrite if_true; auto.
normalize.
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

Definition field_mapsto (sh: Share.t) (v1: val*type) (fld: ident) (v2: val*type) : mpred :=
 match v1 with
  | (Vptr l ofs, Tstruct id fList  att) =>
    let fList' := unroll_composite_fields id (snd v1) fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList',  access_mode t2 with
     | Errors.OK delta, By_value ch => 
          !! (snd v2 = t2 /\ typecheck_val (fst v2) t2 = true) && 
           address_mapsto ch (fst v2) (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)  (l, Int.unsigned (Int.add ofs (Int.repr delta)))
     | _, _ => FF
     end
  | _  => FF
  end.

Lemma field_mapsto_type:
  forall fld sh x sid fields a  y, 
     snd x = Tstruct sid fields a ->
     field_mapsto sh x fld y = 
               !! (snd y = type_of_field (unroll_composite_fields sid (Tstruct sid fields a) fields) fld) && field_mapsto sh x fld y.
Proof with normalize.
intros.
apply pred_ext...
apply andp_right; auto.
destruct x as [x t].
simpl in H.
subst t.
unfold field_mapsto.
destruct x...
simpl @snd.
case_eq (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields a) fields)); intros;
  [ | normalize].
case_eq (access_mode
    (type_of_field
       (unroll_composite_fields sid (Tstruct sid fields a) fields) fld)); intros;
  normalize.
destruct H1; normalize.
Qed.

Lemma field_mapsto_typecheck_val:
  forall fld sh x y, 
     field_mapsto sh x fld y = 
               !! (typecheck_val (fst y) (snd y) = true) && field_mapsto sh x fld y.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
destruct x as [x t].
destruct y as [y t'].
unfold field_mapsto.
destruct x; normalize.
destruct t; normalize.
simpl @fst; simpl @snd.
destruct (field_offset fld (unroll_composite_fields i0 (Tstruct i0 f a) f)); normalize.
destruct (access_mode
    (type_of_field (unroll_composite_fields i0 (Tstruct i0 f a) f) fld)); normalize.
destruct H.
rewrite <- H in H0.
normalize.
Qed.

Lemma field_mapsto_nonnull:  forall fld sh x y, 
     field_mapsto sh x fld y = 
               !! (bool_val (fst x) (Tpointer (snd x) noattr) = Some true) && field_mapsto sh x fld y.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
destruct x as [x t].
destruct y as [y t'].
unfold field_mapsto.
unfold bool_val.
destruct x; normalize.
Qed.

Lemma field_mapsto_access_mode:
  forall sh v t fld v' t',
  field_mapsto sh (v,t) fld (v', t') = 
   !! (exists ch, access_mode t' = By_value ch) && field_mapsto sh (v,t) fld (v', t').
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
destruct v; normalize.
destruct t; normalize.
destruct (field_offset fld
    (unroll_composite_fields i0 (snd (Vptr b i, Tstruct i0 f a)) f)); normalize.
case_eq (access_mode
    (type_of_field
       (unroll_composite_fields i0 (snd (Vptr b i, Tstruct i0 f a)) f) fld)); intros; normalize.
simpl @snd in *.
destruct H0.
rewrite <- H0 in H.
apply prop_right; eauto.
Qed.

Lemma semax_load_field:
forall (Delta: tycontext) (G: funspecs) sh id fld P e1 v2 t2 i2 sid fields ,
    expr_closed_wrt_vars (eq id) (e1) ->
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
  forall (TC1: typecheck_val v2 t2 = true)
          (TC2: t2 =
           type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld),
    semax Delta G 
       (tc_expr Delta e1 &&
    |> ((fun rho => field_mapsto sh (eval_expr rho e1, typeof e1) fld (v2,t2)) * subst id v2 P))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert ((fun rho => field_mapsto sh (eval_expr rho e1, typeof e1) fld (v2, t2)) * P)).
Proof with normalize.
pose proof I.
intros.
rename H2 into TE1.
assert (TC3: tc_expr Delta e1 |-- tc_lvalue Delta (Efield e1 fld t2)).
intros.
intro rho.
unfold tc_lvalue. simpl.
(* Admitted: normalize should handle this better *)
unfold tc_expr.
rewrite <- andp_TT at 1.
apply derives_extract_prop.
intro.
apply prop_right. split; auto.
rewrite H1.
admit.  (* provable, but let's wait until the definition of typecheck_lvalue
                        for Efield settles down *)
evar (P': assert).
evar (Q': assert).
apply (semax_pre_post
            (tc_expr Delta (Etempvar id (typeof (Efield e1 fld t2))) &&
             tc_lvalue Delta (Efield e1 fld t2) &&
              |> (P' * subst id v2  P))
            (normal_ret_assert (Q' * P))).
3: apply semax_load.
intros.
normalize.
apply andp_derives.
apply andp_right.
unfold tc_expr. simpl. rewrite TE1. rewrite if_true; auto. simpl.
apply prop_right; auto.
apply TC3.
apply later_derives.
apply sepcon_derives; auto.
unfold P'.
unfold mapsto'.
erewrite field_mapsto_access_mode.
normalize.
destruct H3 as [ch H3].
rewrite H1.
erewrite field_mapsto_type; [ | reflexivity].
simpl @snd.
simpl access_mode.
rewrite H3.
instantiate (1:=sh).
normalize.
unfold field_mapsto.
case_eq (eval_expr rho e1); intros; normalize.
case_eq (field_offset fld
    (unroll_composite_fields sid (snd (Vptr b i, Tstruct sid fields noattr))
       fields)); intros; normalize.
simpl @snd in *.
rewrite <- TC2; rewrite H3.
simpl @fst.
normalize.
simpl.
rewrite H4.
rewrite H1.
rewrite field_offset_unroll in H5. rewrite H5.
auto.
intros.
unfold Q'.
unfold mapsto'.
case_eq (access_mode (typeof (Efield e1 fld t2))); intros; normalize.
intros ? ? ?.
apply normal_ret_assert_derives...
apply sepcon_derives; auto.
simpl in H2.

simpl.
case_eq (eval_expr x1 e1); 
     intros; normalize.
rewrite H1.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- TC2.
rewrite H2.
normalize.
intros ? ? ?; normalize.
intros ? ? ?; normalize.
intros ? ? ?; normalize.
intro; intros.
simpl.
rewrite <- H0.
auto.
auto.
Qed.

Global Opaque field_mapsto.

Definition bind0 (f: mpred) (args: list val) : mpred := 
     match args with nil => f | _ => FF end.

Lemma bind0_e: forall f, bind_args nil (bind0 f) = fun rho => f.
Proof. intros. unfold bind_args, bind0. extensionality rho; simpl.
 apply prop_true_andp. auto.
Qed.

Definition bind1 (f: val -> mpred) (args: list val): mpred :=
       match args with a::nil => f a | _ => FF end.

Lemma bind1_e: forall id t f,
   bind_args ((id,t)::nil) (bind1 f)  =
    (fun rho => !!((typecheck_val (eval_expr rho (Etempvar id t)) t) = true))
          && (fun rho => f (eval_id rho id)).
Proof. 
 intros; unfold bind_args, bind1;  simpl. 
 extensionality rho.
 f_equal.
 rewrite andb_true_r; auto.
Qed.

Definition bind2 (f: val -> val -> mpred) (args: list val): mpred :=
       match args with a::b::nil => f a b | _ => FF end.

Lemma bind2_e: forall id1 t1 id2 t2 f,
   bind_args ((id1,t1)::(id2,t2)::nil) (bind2 f)  =
    (fun rho => !!((typecheck_val (eval_expr rho (Etempvar id1 t1)) t1) = true))
   && (fun rho => !!((typecheck_val (eval_expr rho (Etempvar id2 t2)) t2) = true))
          && (fun rho => f (eval_id rho id1) (eval_id rho id2)).
Proof. 
 intros; unfold bind_args, bind2;  simpl. 
 extensionality rho.
 f_equal.
 rewrite andb_true_r; auto.
 destruct (typecheck_val (eval_id rho id1) t1); simpl;  normalize.
 destruct (typecheck_val (eval_id rho id2) t2); simpl;  normalize.
 rewrite andp_com. rewrite prop_true_andp; auto.
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



