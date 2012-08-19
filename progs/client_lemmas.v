Require Import msl.msl_standard.
Require Import msl.normalize.
Require Import veric.base.
Require Import veric.expr.
Require Import veric.seplog.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope pred.

Lemma semax_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall ek vl rho, R' ek vl rho |-- R ek vl rho) ->
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


Lemma sequential: 
    forall Q Delta G P c R,
            (forall vl, R EK_normal vl = Q) ->
               semax Delta G P c (normal_ret_assert Q) -> semax Delta G P c R.
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto.
intros.
unfold normal_ret_assert.
normalize.
rewrite H; auto.
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

Lemma with_prop {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
   forall (Q: pred A)(P: Prop), 
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

Definition field_mapsto (sh: Share.t) (v1: val*type) (fld: ident) (v2: val*type) : pred rmap :=
 match v1 with
  | (Vptr l ofs, Tstruct id fList  att) =>
    let fList' := unroll_composite_fields id (snd v1) fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList',  access_mode t2 with
     | Errors.OK delta, By_value ch => 
          !! (snd v2 = t2 /\ typecheck_val (fst v2) t2 = true) && 
           address_mapsto ch (fst v2) (unrel Lsh sh) (unrel Rsh sh)  (l, Int.unsigned (Int.add ofs (Int.repr delta)))
     | _, _ => FF
     end
  | _  => FF
  end.

Lemma field_mapsto_type:
  forall fld sh x sid fields a  y, 
     snd x = Tstruct sid fields a ->
     field_mapsto sh x fld y = 
               !! (snd y = type_of_field (unroll_composite_fields sid (Tstruct sid fields a) fields) fld) && field_mapsto sh x fld y.
Proof.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
destruct x as [x t].
simpl in H.
subst t.
unfold field_mapsto.
destruct x; normalize.
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
intros w ?; hnf; eauto.
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
       (fun rho => 
          !!(denote_tc_assert (typecheck_expr Delta e1) rho) &&
    |> (field_mapsto sh (eval_expr rho e1, typeof e1) fld (v2,t2) * subst id v2 P rho))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (fun rho => field_mapsto sh (eval_expr rho e1, typeof e1) fld (v2, t2) * P rho)).
Proof.
pose proof I.
intros.
rename H2 into TE1.
assert (TC3: forall rho, 
  denote_tc_assert (typecheck_expr Delta e1) rho ->
  denote_tc_assert (typecheck_lvalue Delta (Efield e1 fld t2)) rho).
intros.
split; auto.
rewrite H1.
admit.  (* provable, but let's wait until the definition of typecheck_lvalue
                        for Efield settles down *)
evar (P': assert).
evar (Q': assert).
apply (semax_pre_post
            (fun rho =>!!(denote_tc_assert (typecheck_expr Delta 
                    (Etempvar id (typeof (Efield e1 fld t2)))) rho /\
             denote_tc_assert (typecheck_lvalue Delta (Efield e1 fld t2)) rho) &&
              |> (P' rho * subst id v2  P rho))
            (normal_ret_assert (fun rho => Q' rho * P rho))).
3: apply semax_load.
intros.
apply andp_derives.
intros w ?; split. hnf in H3.
simpl typecheck_expr. rewrite TE1. rewrite if_true; auto.
auto.
apply later_derives. apply sepcon_derives; auto.
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
apply normal_ret_assert_derives.
apply sepcon_derives; auto.
simpl in H2.

simpl.
case_eq (eval_expr rho e1); 
     intros; normalize.
rewrite H1.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- TC2.
rewrite H2.
normalize.
intro; intros.
simpl.
rewrite <- H0.
auto.
auto.
Qed.

Opaque field_mapsto.

Notation "'WITH' x 'PRE' [ ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tnil, tz) _
             (fun x (args : list val) => match args with nil => P%pred | _ => FF%pred end) 
             (fun x (args : list val) => match args with z::nil => Q%pred | _ => FF%pred end))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100).
Notation "'WITH' x : tx  'PRE' [ ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tnil, tz) _
             (fun (x : tx) (args : list val) => match args with nil => P%pred | _ => FF%pred end) 
             (fun (x : tx) (args : list val) => match args with z::nil => Q%pred | _ => FF%pred end))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100).

Notation "'WITH' x 'PRE' [ a : ta ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta Tnil, tz) _
             (fun x (args : list val) => match args with a::nil => P%pred | _ => FF%pred end) 
             (fun x (args : list val) => match args with z::nil => Q%pred | _ => FF%pred end))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).
Notation "'WITH' x : tx 'PRE' [ a : ta ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta Tnil, tz) _
             (fun (x:tx) (args : list val) => match args with a::nil => P%pred | _ => FF%pred end) 
             (fun (x:tx) (args : list val) => match args with z::nil => Q%pred | _ => FF%pred end))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Notation "'WITH' x 'PRE' [ a : ta , b : tb ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta (Tcons tb Tnil), tz) _
             (fun x (args : list val) => match args with a::b::nil => P%pred | _ => FF%pred end) 
             (fun x (args : list val) => match args with z::nil => Q%pred | _ => FF%pred end))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).
Notation "'WITH' x : tx 'PRE' [ a : ta , b : tb ] P 'POST' [ z : tz ] Q" := 
     (mk_funspec (Tcons ta (Tcons tb Tnil), tz) _
             (fun (x:tx) (args : list val) => match args with a::b::nil => P%pred | _ => FF%pred end) 
             (fun (x:tx) (args : list val) => match args with z::nil => Q%pred | _ => FF%pred end))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Lemma prop_right {A}{agA: ageable A}:
  forall (P: pred A)(Q: Prop), Q -> (P |-- !!Q).
Proof.
intros; intros ? ?; auto.
Qed.


