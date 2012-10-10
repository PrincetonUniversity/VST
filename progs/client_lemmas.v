Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.


Lemma semax_post:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) &&  R' ek vl |-- R ek vl) ->
   semax Delta G P c R' ->  semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

Lemma semax_post0:
 forall (R': ret_assert) Delta G (R: ret_assert) P c,
   (R' |-- R) ->
   semax Delta G P c R' ->  semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
intros. apply andp_left2; auto.
apply H.
Qed.

Lemma semax_pre:
 forall P' Delta G P c R,
     (local (tc_environ Delta) && P |-- P') ->
     semax Delta G P' c R  -> semax Delta G P c R.
Proof.
intros; eapply semax_pre_post; eauto.
intros; apply andp_left2; auto.
Qed.

Hint Rewrite eval_id_other using solve [auto; clear; intro Hx; inversion Hx] : normalize.

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
apply andp_left2.
apply exp_left; auto.
apply extract_exists; auto.
Qed.


Lemma sequential:
  forall Delta G P c Q,
        semax Delta G P c (normal_ret_assert (Q EK_normal nil)) ->
          semax Delta G P c Q.
intros. eapply semax_post; eauto.
 intros. intro rho. unfold local,lift1; simpl.
 unfold normal_ret_assert; simpl; normalize.
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
apply andp_left2; auto.
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
          !! (typecheck_val v2 t2 = true) && !!(type_is_volatile t2 = false) &&
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

Lemma field_offset_exists1: 
  forall sid t fields fld,
    type_of_field (unroll_composite_fields sid t fields) fld <> Tvoid ->
    exists n, field_offset fld fields = Errors.OK n.
intros.
unfold field_offset.
forget 0 as k. revert k.
induction fields; intro k; simpl in H. congruence.
destruct (eq_dec i fld). subst i.
econstructor; simpl. rewrite if_true by auto.
reflexivity.
simpl. rewrite if_false by auto.
destruct (IHfields H (align k (alignof t0) + sizeof t0)).
eauto.
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

Lemma semax_load_field:
forall (Delta: tycontext) (G: funspecs) sh id t1 fld P e1 v2 t2 i2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    (temp_types Delta) ! id = Some (t2,i2) ->
  forall (TC0: t1 = typeof e1) 
          (TC2: t2 =
           type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld),
    semax Delta G 
       (|> (local (tc_lvalue Delta e1) &&
          (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) (lift0 v2) * P)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, local (lift1 (eq v2) (eval_id id)) &&
                  (subst id (lift0 old) 
                    (lift2 (field_mapsto sh t1 fld) (eval_lvalue e1) (lift0 v2) * P)))).
Proof with normalize.
pose proof I.
pose proof I.
intros.
subst t1.
rename H2 into TE1.
apply (semax_pre_post
            (|> (local (tc_temp Delta id (typeof (Efield e1 fld t2))) &&
             local (tc_lvalue Delta (Efield e1 fld t2)) &&
               (mapsto' sh (Efield e1 fld t2) v2 * 
                  (!! (typecheck_val v2 t2 = true) && !!(type_is_volatile t2 = false) &&  P))))
            (normal_ret_assert 
              (EX old:val, local (lift1 (eq v2) (eval_id id)) &&
              (subst id (lift0 old) (mapsto' sh (Efield e1 fld t2) v2  * 
                (!! (typecheck_val v2 t2 = true) && !!(type_is_volatile t2 = false) && P))))));
  [ | | apply semax_load].

(* PRECONDITION *)
intro rho.
unfold tc_temp, typecheck_temp_id, local, lift1, lift0.
simpl. rewrite TE1.
normalize.
apply later_derives.
normalize.
apply derives_trans with ((!!(eqb_type t2 t2 = true) && !!tc_lvalue Delta (Efield e1 fld t2) rho &&
    (!!(typecheck_val v2 t2 = true) && !!(type_is_volatile t2 = false) && 
     (mapsto' sh (Efield e1 fld t2) v2 rho))) * P rho).
apply sepcon_derives; auto.
unfold lift2.
rewrite eqb_type_refl. normalize.
unfold mapsto'.
unfold tc_lvalue; simpl. unfold lift2.
unfold tc_lvalue in H3. rewrite H1.
unfold field_mapsto.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite <- TC2.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
case_eq (access_mode t2); intros; normalize.
rewrite H8. 
normalize.
normalize.

(* POSTCONDITION *)
intros ek vl rho; unfold normal_ret_assert; simpl.
normalize.
intro old. apply exp_right with old.
normalize.
unfold local,lift0,lift1,lift2; simpl.
normalize.
unfold subst.
normalize.
apply sepcon_derives; auto.
unfold mapsto', field_mapsto.
simpl eval_lvalue. simpl typeof.
case_eq (access_mode t2); intros; normalize.
destruct (eval_lvalue e1 (env_set rho id old)); normalize.
rewrite H1.
rewrite field_offset_unroll.
destruct (field_offset fld fields); normalize.
rewrite <- TC2.
rewrite H4. rewrite H5.
normalize.
Qed.

Lemma splice_top_top: Share.splice Share.top Share.top = Share.top.
Proof.
unfold Share.splice.
unfold Share.Lsh, Share.Rsh.
case_eq (Share.split Share.top); intros L R ?.
simpl.
do 2 rewrite Share.rel_top1.
erewrite Share.split_together; eauto.
Qed.

(* move this elsewhere, and by the way it generalizes the same-named lemma
  in veric/semax_straight.v *)
Lemma cast_exists : forall Delta e2 t rho 
(TC: typecheck_environ rho Delta = true), 
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isCastResultType (typeof e2) t t e2)
  rho ->
sem_cast (eval_expr e2 rho) (typeof e2) t =
Some (force_val (sem_cast (eval_expr e2 rho) (typeof e2) t)).
Proof.
intros. 
assert (exists v, sem_cast (eval_expr e2 rho) (typeof e2) t= Some v).

apply expr_lemmas.typecheck_expr_sound in H.
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent Float.intoffloat.
Transparent Float.intuoffloat.
destruct t; destruct v; destruct t0; simpl in *;
try congruence; try contradiction; eauto;
try solve [
unfold Float.intoffloat, Float.intuoffloat; repeat invSome;
inversion2 H1 H0; hnf in H2,H3; rewrite H3; rewrite Zle_bool_rev; rewrite H2;
simpl; eauto];
try solve [
try destruct i; try destruct s; try destruct i0; try destruct i1; try destruct s0; eauto |

destruct i; destruct s; unfold lift2 in *; try solve[simpl in *; 
  unfold lift2,lift1 in *;  expr_lemmas.unfold_tc_denote; destruct H0; 
try rewrite <- Heqv in *; 
unfold Float.intoffloat; 
destruct (Float.Zoffloat f0); try contradiction;
try rewrite H0; try rewrite H1; simpl; eauto | 
simpl in *;  unfold Float.intuoffloat; destruct H0;
expr_lemmas.unfold_tc_denote; try rewrite <- Heqv in *; destruct (Float.Zoffloat f0);
try rewrite H0; try rewrite H1; simpl; eauto; try contradiction] |

try destruct i0; try destruct i1; destruct s; simpl in *; try contradiction; try rewrite H; eauto ].

destruct i; destruct s; unfold lift2 in *;
simpl in *; unfold lift2,lift1 in *;
unfold Float.intoffloat, Float.intuoffloat;
try (
destruct H0 as [H0 H1]; hnf in H0,H1; rewrite <- Heqv in *;
destruct (Float.Zoffloat f0); try contradiction;
hnf in H0,H1; rewrite H0; rewrite expr_lemmas.Zle_bool_rev; rewrite H1;
simpl; eauto);
simpl; eauto.

auto.
Opaque Float.intoffloat.
Opaque Float.intuoffloat.

destruct H1. rewrite H1. auto.
Qed. 

(* Admitted:  after Joey checks in his revision of environments,
 move this definition (and similar ones in progs/assert_lemmas
  into expr.v, and use it in the definition of eval_expr *)
Definition eval_cast (t t': type) (v: val) : val := force_val (sem_cast v t t').
Definition tc_val (t: type) (v: val) : Prop := typecheck_val v t = true.

Lemma typecheck_val_eval_cast: 
  forall t2 e2 rho Delta,
      tc_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2 t2 e2) rho ->
      typecheck_val (eval_cast (typeof e2) t2 (eval_expr e2 rho)) t2 = true.
Proof. intros ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ H2 H5 H6).
assert (H8 := expr_lemmas.typecheck_expr_sound _ _ _ H2 H5).
clear - H7 H6 H8.
revert H7; case_eq (sem_cast (eval_expr e2 rho) (typeof e2) t2); intros; inv H7.
unfold eval_cast. rewrite H. simpl.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2; inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2); inv H2; inv H1; auto;
try (unfold sem_cast in H0; simpl in H0;
      destruct i0; simpl in*; destruct s; inv H0; simpl; auto).
simpl in *. unfold lift1 in H6. rewrite H99 in *. inv H6. auto.
simpl in *. unfold isCastResultType in H6. simpl in H6.
unfold sem_cast in H0. 
simpl in H0.
destruct i; simpl in*; destruct s; try destruct f; inv H0; simpl; auto;
invSome; simpl; auto.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
Qed.


Lemma semax_store_field: 
forall (Delta: tycontext) (G: funspecs) e1 fld P v0 t2 e2 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield e1 fld t2) ->
   semax Delta G 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) v0 * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) 
                  (lift1 (eval_cast (typeof e2) t2) (eval_expr e2)) * P)).
Proof.
pose proof I.
intros.
rename H0 into TE1.
rename H2 into TCS.
apply semax_pre with 
  (EX v':val, 
    (|>(local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
      (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) (lift0 v') * P)))).
apply andp_left2.
intro rho. simpl. apply exp_right with (v0 rho). auto.
apply extract_exists_pre; intro v'.
clear v0. rename v' into v0.

pose proof (semax_store Delta G (Efield e1 fld t2) e2 v0 Share.top 
               (local (lift1 (tc_val t2) (lift1 (eval_cast (typeof e2) t2) (eval_expr e2))) &&
                 !! (type_is_volatile t2 = false) &&   P)).
simpl typeof in H0. rewrite splice_top_top in H0.
eapply semax_pre_post ; [ | | apply H0; auto].
apply derives_trans with(|> (local (tc_environ Delta) &&
  (local (tc_lvalue Delta e1) &&
   local (tc_expr Delta (Ecast e2 t2)) &&
   (lift2 (field_mapsto Share.top (typeof e1) fld) (eval_lvalue e1) (lift0 v0) * P)))).
rewrite (later_andp (local (tc_environ Delta))). apply andp_derives; auto.
apply now_later.
apply later_derives.
intro rho; unfold local,lift0,lift1,lift2. simpl.
normalize.
unfold field_mapsto, mapsto'.
simpl.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite TE1.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- H1. destruct (access_mode t2); normalize.
apply derives_trans with ((!!tc_lvalue Delta (Efield e1 fld t2) rho &&
    !!tc_expr Delta (Ecast e2 t2) rho &&
     (!!tc_val t2 (eval_cast (typeof e2) t2 (eval_expr e2 rho)) &&
      !!(type_is_volatile t2 = false)) &&
     address_mapsto m v0 (Share.unrel Share.Lsh Share.top)
       (Share.unrel Share.Rsh Share.top)
       (b, Int.unsigned (Int.add i (Int.repr z)))) * P rho).
apply sepcon_derives; auto. 
apply andp_right; normalize.
unfold tc_lvalue; simpl.
unfold lift2. rewrite TE1.
repeat apply andp_right; apply prop_right; auto.
split; auto. split; auto. rewrite H6; auto.
rewrite H8; simpl; auto.
eapply typecheck_val_eval_cast; eauto.
hnf in H4.
destruct H4; auto.
unfold tc_expr in H4.
simpl in H4.
destruct H4; auto.
normalize.

intros ek vl rho; unfold local, lift1, normal_ret_assert, lift2; simpl.
normalize.
apply sepcon_derives; auto.
unfold mapsto', field_mapsto.
simpl.
case_eq (access_mode t2); intros; normalize.
case_eq (eval_lvalue e1 rho); intros; normalize.
rewrite TE1.
rewrite field_offset_unroll.
case_eq (field_offset fld fields); intros; normalize.
rewrite <- H1. rewrite H5.
normalize.
Qed.

Global Opaque field_mapsto.

Definition PROPx (P: list Prop) (Q: assert) := andp (prop (fold_right and True P)) Q.

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z) (at level 10) : logic.
Notation "'PROP' ()   z" :=   (PROPx nil z) (at level 10) : logic.
Notation "'PROP' ( )   z" :=   (PROPx nil z) (at level 10) : logic.

Definition LOCALx (Q: list (environ -> Prop)) (R: assert) := 
                 andp (local (fold_right (lift2 and) (lift0 True) Q)) R.

Notation " 'LOCAL' ( )   z" := (LOCALx nil z)  (at level 9) : logic.
Notation " 'LOCAL' ()   z" := (LOCALx nil z)  (at level 9) : logic.

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z)
         (at level 9) : logic.

Definition SEPx (R: list assert) : assert := fold_right sepcon emp R.

Notation " 'SEP' ( x * .. * y )" := (SEPx (cons x%logic .. (cons y%logic nil) ..))
         (at level 8) : logic.

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8) : logic.
Notation " 'SEP' () " := (SEPx nil) (at level 8) : logic.

Ltac go_lower := 
 let rho := fresh "rho" in intro rho; unfold PROPx, LOCALx, SEPx; simpl; normalize.

Definition do_canon (x y : assert) := (sepcon x y).

Lemma closed_wrt_PROPx:
 forall S P Q, closed_wrt_vars S Q -> closed_wrt_vars S (PROPx P Q).
Proof.
Admitted. 
Hint Resolve closed_wrt_PROPx: closed.

Lemma closed_wrt_LOCALx:
 forall S Q R, Forall (fun q => closed_wrt_vars S (local q)) Q -> 
                    closed_wrt_vars S R -> 
                    closed_wrt_vars S (LOCALx Q R).
Admitted. 
Hint Resolve closed_wrt_LOCALx: closed.

Lemma closed_wrt_SEPx: forall S P, 
     Forall (closed_wrt_vars S) P -> closed_wrt_vars S (SEPx P).
Admitted. 
Hint Resolve closed_wrt_SEPx: closed.

(* Hint Extern 1 (Forall _ (map (@fst ident type) _)) => simpl map. *)

Lemma unfold_lift0: forall {A} (f: A)  rho,  lift0 f rho = f.
Proof. reflexivity. Qed.
Hint Rewrite @unfold_lift0 : normalize.

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
Hint Rewrite local_unfold : normalize.
Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 rho,
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.
Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.
Hint Rewrite @lift2_unfold @lift1_unfold : normalize.

Instance Nassert: NatDed assert := _.
Instance Sassert: SepLog assert := _.
Instance Cassert: ClassicalSep assert := _. 
Instance Iassert: Indir assert := _.
Instance SIassert: SepIndir assert := _.

Lemma lift_prop_unfold: 
   forall P z,  @prop assert Nassert P z = @prop mpred Nveric P.
Proof.  reflexivity. Qed.
Hint Rewrite lift_prop_unfold: normalize.

Lemma andp_unfold: forall P Q rho,
  @andp assert Nassert P Q rho = @andp mpred Nveric (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite andp_unfold: normalize.

Lemma prop_and {A} {NA: NatDed A}: 
    forall P Q: Prop, prop (P /\ Q) = (prop P && prop Q).
Proof. intros. apply pred_ext. apply prop_left. intros [? ?]; normalize.
   normalize.
Qed.
Hint Rewrite @prop_and : normalize.

Lemma exp_unfold : forall A P rho,
 @exp assert Nassert A P rho = @exp mpred Nveric A (fun x => P x rho).
Proof.
intros. reflexivity. 
Qed.
Hint Rewrite exp_unfold: normalize.

Lemma canon1: forall P1 B  P Q R,
   do_canon (prop P1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B  (PROPx (P1::P) (LOCALx Q (SEPx R))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Lemma canon2: forall Q1 B P Q R,
    do_canon (local Q1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx (Q1::Q) (SEPx R))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Definition nonlocal (Q: assert) := True.

Ltac check_nonlocal :=
  match goal with
  |  |- nonlocal (local _) => fail 1 
  |  |- nonlocal (prop _) => fail 1 
  |  |- nonlocal (andp _ _) => fail 1
  |  |- nonlocal (sepcon _ _) => fail 1
  | |- _ => apply I
 end.

Lemma canon3: forall R1 B P Q R,
    nonlocal R1 ->
    do_canon (B * R1) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
clear H.
extensionality rho.
simpl.
rewrite sepcon_assoc.
f_equal.
rewrite sepcon_andp_prop.
f_equal.
normalize.
Qed.

Lemma canon3b: forall R1 B P Q R,
    nonlocal R1 ->
    do_canon (R1* B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
rewrite (sepcon_comm R1 B).
apply canon3. auto.
Qed.

Lemma canon4: forall P, do_canon emp P = P. 
Proof.
apply emp_sepcon.
Qed.

Lemma canon7: forall R1 P Q R, 
   nonlocal R1 -> 
   do_canon R1 (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
Qed.
 
Lemma canon8: forall R1 R2 R3 PQR,
    do_canon ((R1 && R2) && R3) PQR = do_canon (R1 && (R2 && R3)) PQR.
Proof. intros; rewrite andp_assoc; auto. 
Qed.

Lemma start_canon: forall P, P  = do_canon P (PROPx nil (LOCALx nil (SEPx nil ))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho; simpl.
normalize.
Qed.

Hint Rewrite canon1 canon2 canon4 canon8 : canon.
Hint Rewrite canon3 using check_nonlocal : canon.
Hint Rewrite canon3b using check_nonlocal : canon.
Hint Rewrite canon7 using check_nonlocal : canon.
Hint Rewrite <- (@sepcon_assoc assert _) : canon.

Lemma canon5: forall Q R S, 
       nonlocal Q ->
       Q && (local R && S) = local R && (Q && S).
Admitted.


Lemma canon5b: forall Q R S, 
       nonlocal Q ->
       Q && (S && local R) = local R && (Q && S).
Admitted.

Lemma canon5c: forall Q R, 
       nonlocal Q ->
       (Q && local R) = local R && Q.
Admitted.

Lemma canon6: forall Q R S, 
       nonlocal Q ->
       Q && (prop R && S) = prop R && (Q && S).
Admitted.

Lemma canon6b: forall Q R S, 
       nonlocal Q ->
       Q && (S && prop R) = prop R && (Q && S).
Admitted.

Lemma canon6c: forall Q R, 
       nonlocal Q ->
       (Q && prop R) = prop R && Q.
Admitted.

Hint Rewrite canon5 using check_nonlocal : canon.
Hint Rewrite canon5b using check_nonlocal : canon.
Hint Rewrite canon5c using check_nonlocal : canon.
Hint Rewrite canon6 using check_nonlocal : canon.
Hint Rewrite canon6b using check_nonlocal : canon.
Hint Rewrite canon6c using check_nonlocal : canon.

Lemma canon17 : forall (P: Prop) PP QR, prop P && (PROPx PP QR) = PROPx (P::PP) QR.
Proof.
intros. unfold PROPx. simpl. extensionality rho. apply pred_ext; normalize.
Qed.
Hint Rewrite canon17 : canon.


Lemma finish_canon: forall R1 P Q R, 
   do_canon R1 (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
Qed.

Ltac canonicalize_pre :=
  match goal with |- semax _ _ ?P _ _ =>
      rewrite (start_canon P); autorewrite with canon
  end.    

Lemma fst_unfold: forall {A B} (x: A) (y: B), fst (x,y) = x.
Proof. reflexivity. Qed.
Lemma snd_unfold: forall {A B} (x: A) (y: B), snd (x,y) = y.
Proof. reflexivity. Qed.
Hint Rewrite @fst_unfold @snd_unfold : normalize.

Lemma local_andp_prop:  forall P Q, local P && prop Q = prop Q && local P.
Proof. intros. apply andp_comm. Qed.
Lemma local_andp_prop1: forall P Q R, local P && (prop Q && R) = prop Q && (local P && R).
Proof. intros. rewrite andp_comm. rewrite andp_assoc. f_equal. apply andp_comm. Qed.
Hint Rewrite local_andp_prop local_andp_prop1 : normalize.

Lemma local_sepcon_assoc1:
   forall P Q R, (local P && Q) * R = local P && (Q * R).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Lemma local_sepcon_assoc2:
   forall P Q R, R * (local P && Q) = local P && (R * Q).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Hint Rewrite local_sepcon_assoc1 local_sepcon_assoc2 : normalize.

Ltac strip1_later P :=
 match P with 
 | do_canon ?L ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(do_canon L' R')
 | PROPx ?P ?QR => let QR' := strip1_later QR in constr:(PROPx P QR')
 | LOCALx ?Q ?R => let R' := strip1_later R in constr:(LOCALx Q R')
 | SEPx ?R => let R' := strip1_later R in constr:(SEPx R')
 | ?L::?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L'::R')
 | nil => constr:(nil)
 | ?L && ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L' && R')
 | ?L * ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L'*R')
 | |> ?L => constr:(L)
 | ?L => constr:(L)
end.

Lemma andp_later_derives {A} {NA: NatDed A}{IA: Indir A}:
  forall P Q P' Q': A, P |-- |> P' -> Q |-- |> Q' -> P && Q |-- |> (P' && Q').
Proof.
intros. rewrite later_andp. apply andp_derives; auto. Qed.

Lemma sepcon_later_derives {A} {NA: NatDed A}{SL: SepLog A}{IA: Indir A}{SI: SepIndir A}:
  forall P Q P' Q': A, P |-- |> P' -> Q |-- |> Q' -> P * Q |-- |> (P' * Q').
Proof.
intros. rewrite later_sepcon. apply sepcon_derives; auto. Qed.

Hint Resolve andp_later_derives sepcon_later_derives sepcon_derives
              andp_derives imp_derives now_later derives_refl: derives.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Definition retval : environ -> val := eval_id ret_temp.

Notation "'WITH' x 'PRE' [ a : ta ] P 'POST' [ tz ] Q" := 
     (mk_funspec ((a, ta)::nil, tz) _ (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Notation "'WITH' x : tx 'PRE' [ a : ta ] P 'POST' [ tz ] Q" := 
     (mk_funspec ((a, ta)::nil, tz) tx (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).


Lemma exp_derives {A}{NA: NatDed A}{B}:
   forall F G: B -> A, (forall x, F x |-- G x) -> exp F |-- exp G.
Proof.
intros.
apply exp_left; intro x. apply exp_right with x; auto.
Qed.

Lemma insert_local: forall Q1 P Q R,
  local Q1 && (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx (Q1 :: Q) (SEPx R))).
Proof.
intros. extensionality rho.
unfold PROPx, LOCALx, SEPx, lift2.
normalize.
unfold local, lift1. simpl.
f_equal.
apply pred_ext; normalize.
Qed.
Hint Rewrite insert_local:  normalize.


Lemma semax_pre0:
 forall P' Delta G P c R,
     P |-- P' ->
     semax Delta G P' c R  -> 
     semax Delta G P c R.
Proof.
intros.
eapply semax_pre; try apply H0.
 apply andp_left2; auto.
Qed.

Lemma semax_pre_PQR:
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
  apply semax_pre_PQR with Inv; 
  [ | apply semax_seq with Postcond;
    [ apply semax_while ; [ | compute; auto | | ] | ]].

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

Lemma exp_do_canon:
   forall T (P: T -> assert) (Q: assert), do_canon (exp P) Q = EX x:_, do_canon (P x) Q.
Proof. apply exp_sepcon1. Qed.
Hint Rewrite exp_do_canon: canon.
Hint Rewrite exp_do_canon: normalize.

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
apply semax_pre with (PROPx P QR).
unfold PROPx in *; simpl. normalize. auto.
Qed.

Lemma semax_extract_PROP:
  forall Delta G (PP: Prop) P QR c Post,
       (PP -> semax Delta G (PROPx P QR) c Post) -> 
       semax Delta G (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre with (!!PP && PROPx P QR).
unfold PROPx in *; simpl. normalize.
apply semax_extract_prop.
auto.
Qed.

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


Lemma denote_tc_isptr1:
  forall Delta rho e,
   typecheck_environ rho Delta = true -> 
   denote_tc_assert (typecheck_expr Delta e) rho ->
   lift1 denote_tc_isptr (eval_expr e) rho.
Admitted.

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

Lemma semax_store_field':
forall (Delta: tycontext) (G: funspecs) t1 fld P Q R e1 e2 v0 t2 sid fields ,
    t1 = Tstruct sid fields noattr ->
    typeof e1 = Tpointer t1 noattr ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    typecheck_store (Efield (Ederef e1 t1) fld t2) ->
    semax Delta G 
       (|> do_canon 
             (local (tc_expr Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
              lift2 (field_mapsto Share.top t1 fld) (eval_expr e1) v0)
            (PROPx P (LOCALx Q (SEPx R))))
       (Sassign (Efield (Ederef e1 t1) fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx  (lift2 (field_mapsto Share.top t1 fld) (eval_expr e1) 
                  (lift1 (eval_cast (typeof e2) t2) (eval_expr e2)) :: R))))).
Proof.
intros.
eapply semax_pre_post; [ | | eapply (semax_store_field)].
3: subst t1; reflexivity.
3: assumption.
3: assumption.
instantiate (2:=v0).
instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
autorewrite with canon.
go_lower. apply later_derives. normalize.
subst t1.
unfold tc_lvalue.
pose proof (denote_tc_isptr1 _ _ _ H3 H6).
simpl.
unfold lift2. unfold lift1.
normalize. 
repeat apply andp_right; normalize.
rewrite H0; apply prop_right; simpl; hnf; auto.
unfold lift1, denote_tc_isptr in H.
destruct (eval_expr e1 rho); try contradiction; auto.

intros ek vl rho; unfold normal_ret_assert, local, lift1, lift2; simpl.
normalize.
unfold PROPx, LOCALx; simpl.
normalize.
destruct (eval_expr e1 rho); normalize.
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

Lemma canon20: forall PQR, do_canon emp PQR = PQR.
Proof.
intros. apply emp_sepcon.
Qed.
Hint Rewrite canon20: canon.


Lemma subst_andp:
  forall id v P Q, subst id v (P && Q) = subst id v P && subst id v Q.
Admitted.
Lemma subst_prop: forall i v P, subst i v (prop P) = prop P.
Proof.
intros; reflexivity.
Qed.
Hint Rewrite @subst_andp subst_prop : normalize.

Lemma subst_lift1:
  forall {A1 B} id v (f: A1 -> B) a, 
          subst id v (lift1 f a) = lift1 f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

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

Hint Rewrite @subst_lift0 @subst_lift1 @subst_lift2 : normalize.


Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

Hint Rewrite @map_cons : normalize.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.

Hint Rewrite @map_nil : normalize.


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


Lemma forward_setx:
  forall Delta G P id e,
  typecheck_temp_id id (typeof e) Delta = true ->
  (P |-- local (tc_expr Delta e)) ->
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
apply andp_right; auto.
apply H0.
intros ek vl rho; unfold normal_ret_assert. simpl; normalize.
intros old ?; apply exp_right with old.
normalize.
Qed.

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

Ltac forward_setx := 
  first [eapply semax_seq; 
            [ apply sequential' ; apply forward_setx; [reflexivity | normalizex]
              | apply extract_exists_pre; normalize; try (intros _) ]
         | eapply semax_post;  [ | apply forward_setx; [reflexivity | normalizex]];
            cbv beta; normalize
        ].

Ltac semax_field_tac1 := 
   eapply semax_load_field'; 
     [ reflexivity 
     | reflexivity 
     | simpl; reflexivity 
     | type_of_field_tac ].

Ltac isolate_field_tac e fld R := 
  match R with 
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
     end.

Ltac semax_field_tac :=
match goal with
 | |- semax ?Delta _ (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                  (Ssequence (Sset _ (Efield (Ederef ?e _) ?fld _)) _) _ =>
  apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
   [ go_lower 
   | isolate_field_tac e fld R;
     eapply semax_seq; [ apply sequential'; semax_field_tac1  
                                          | simpl update_tycon; apply extract_exists_pre
                                          ]
    ]
 | |- semax ?Delta _ (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                    (Sset _ (Efield (Ederef ?e _) ?fld _)) _ =>
     apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
     [ go_lower 
     | isolate_field_tac e fld R;
       eapply semax_post; [ | semax_field_tac1]
     ]
end; normalizex.

Ltac check_sequential s :=
 match s with
 | Sskip => idtac
 | Sassign _ _ => idtac
 | Sset _ _ => idtac
 | Scall _ _ _ => idtac
 | Ssequence ?s1 ?s2 => check_sequential s1; check_sequential s2
 | _ => fail
 end.

Ltac sequential := 
 match goal with
 |  |- semax _ _ _ _ (normal_ret_assert _) => fail 2
 |  |- semax _ _ _ ?s _ =>  check_sequential s; apply sequential
 end.

Ltac is_canonical P :=
 match P with 
 | PROPx _ (LOCALx _ (SEPx _)) => idtac
 | _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
 end.

Ltac forward := 
  match goal with
  | |- semax _ _ ?P (Ssequence (Sset _ (Efield _ _ _)) _) _ => 
                  is_canonical P; semax_field_tac
  | |- semax _ _ ?P (Sset _ (Efield _ _ _)) _ => 
                  is_canonical P; semax_field_tac
  | |- semax _ _ ?P (Ssequence (Sset _ ?e) _) _ => 
               is_canonical P; match e with (Efield _ _) => fail 2 | _ => forward_setx end
  | |- semax _ _ ?P (Sset _ ?e) _ => 
               is_canonical P; match e with (Efield _ _) => fail 2 | _ => forward_setx end
  | |- semax _ _ _ (Ssequence (Sreturn _) _) _ =>
          apply semax_seq with FF; [eapply semax_pre; [ | apply semax_return ]
                                | apply semax_ff]
  | |- semax _ _ _ (Sreturn _) _ =>
          eapply semax_pre; [ | apply semax_return ]
  end.


