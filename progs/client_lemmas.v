Load loadpath.
Require Import veric.SeparationLogic.
Require Import Coqlib msl.Coqlib2.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import Clightdefs.

Local Open Scope logic.

Lemma semax_ff:
  forall Delta c R,  
   semax Delta FF c R.
Proof.
intros.
apply semax_pre_post with (FF && FF) R.
apply andp_left2. apply andp_right; auto.
intros; apply andp_left2; auto.
apply semax_extract_prop. intros; contradiction.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) &&  R' ek vl |-- R ek vl) ->
   semax Delta P c R' ->  semax Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

Lemma semax_post0:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (R' |-- R) ->
   semax Delta P c R' ->  semax Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
intros. apply andp_left2; auto.
apply H.
Qed.

Lemma semax_post': forall R' Delta R P c,
           R' |-- R ->
      semax Delta P c (normal_ret_assert R') ->
      semax Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto. intros. apply andp_left2.
  intro rho; apply normal_ret_assert_derives; auto.
Qed.

Lemma semax_pre:
 forall P' Delta P c R,
     (local (tc_environ Delta) && P |-- P') ->
     semax Delta P' c R  -> semax Delta P c R.
Proof.
intros; eapply semax_pre_post; eauto.
intros; apply andp_left2; auto.
Qed.

Lemma extract_exists_pre:
      forall
        (A : Type) (P : A -> assert) (c : Clight.statement)
         Delta  (R : ret_assert),
       (forall x : A, semax Delta (P x) c R) ->
       semax Delta (exp (fun x => P x)) c R.
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
  forall Delta P c Q,
        semax Delta P c (normal_ret_assert (Q EK_normal None)) ->
          semax Delta P c Q.
intros. eapply semax_post; eauto.
 intros. intro rho. unfold local,lift1; simpl.
 unfold normal_ret_assert; simpl; normalize.
Qed.

Lemma sequential': 
    forall Q Delta P c R,
               semax Delta P c (normal_ret_assert Q) -> 
               semax Delta P c (overridePost Q R).
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto.
intros.
unfold normal_ret_assert, overridePost.
normalize.
rewrite if_true; auto.
apply andp_left2; auto.
Qed.

Lemma semax_while : 
 forall Delta Q test body R,
     bool_type (typeof test) = true ->
     (local (tc_environ Delta) && Q |-- local (tc_expr Delta test)) ->
     (local (tc_environ Delta) && local (lift1 (typed_false (typeof test)) (eval_expr test)) && Q |-- R EK_normal None) ->
     semax Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)  body (loop1_ret_assert Q R) ->
     semax Delta Q (Swhile test body) R.
Proof.
intros ? ? ? ? ? BT TC Post H.
unfold Swhile.
apply (semax_loop Delta Q Q).
Focus 2.
 clear; eapply semax_post; [ | apply semax_skip];
 destruct ek; unfold normal_ret_assert, loop2_ret_assert; intros; 
    normalize; try solve [inv H]; apply andp_left2; auto.
(* End Focus 2*)
apply semax_seq with 
 (local (`(typed_true (typeof test)) (eval_expr test)) && Q).
apply semax_pre with (local (tc_expr Delta test) && Q).
apply andp_right. apply TC.
apply andp_left2.
intro; auto.
apply semax_ifthenelse; auto.
eapply semax_post; [ | apply semax_skip].
intros.
intro rho; unfold normal_ret_assert, overridePost; simpl.
normalize. rewrite if_true by auto.
apply andp_right. apply TT_right.
apply andp_left2. rewrite andp_comm; auto.
eapply semax_pre; [ | apply semax_break].
unfold overridePost. rewrite if_false by congruence.
unfold loop1_ret_assert.
eapply derives_trans; try apply Post.
rewrite andp_assoc. apply andp_derives; auto.
rewrite andp_comm; auto.
simpl update_tycon.
apply semax_extensionality_Delta with Delta; auto.
apply tycontext_eqv_symm; apply join_tycon_same.
Qed.

Definition PROPx (P: list Prop): forall (Q: assert), assert := 
     andp (prop (fold_right and True P)).

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z) (at level 10) : logic.
Notation "'PROP' ()   z" :=   (PROPx nil z) (at level 10) : logic.
Notation "'PROP' ( )   z" :=   (PROPx nil z) (at level 10) : logic.

Definition LOCALx (Q: list (environ -> Prop)) : forall (R: assert), assert := 
                 andp (local (fold_right (`and) (`True) Q)).

Notation " 'LOCAL' ( )   z" := (LOCALx nil z)  (at level 9) : logic.
Notation " 'LOCAL' ()   z" := (LOCALx nil z)  (at level 9) : logic.

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z)
         (at level 9) : logic.

(* Definition SEPx (R: list assert) : assert := fold_right sepcon emp R. *)

Definition SEPx: forall (R: list assert), assert := fold_right sepcon emp.
Definition SEPx': forall (R: list assert), assert := fold_right sepcon emp.
Global Opaque SEPx.

Notation " 'SEP' ( x ; .. ; y )" := (SEPx (cons x%logic .. (cons y%logic nil) ..))
         (at level 8) : logic.

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8) : logic.
Notation " 'SEP' () " := (SEPx nil) (at level 8) : logic.

Definition nullval : val := Vint Int.zero.

Lemma bool_val_int_eq_e: 
  forall i j, Cop.bool_val (Val.of_bool (Int.eq i j)) type_bool = Some true -> i=j.
Proof.
 intros.
 revert H; case_eq (Val.of_bool (Int.eq i j)); simpl; intros; inv H0.
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. rewrite Int.eq_true in H2. inv H2.
Qed.

Lemma bool_val_notbool_ptr:
    forall v t,
   match t with Tpointer _ _ => True | _ => False end ->
   (Cop.bool_val (force_val (Cop.sem_notbool v t)) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.

Lemma typed_false_ptr: 
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct v; try discriminate.
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H.
Qed.

Definition retval : environ -> val := eval_id ret_temp.

Lemma retval_get_result1: 
   forall i rho, retval (get_result1 i rho) = (eval_id i rho).
Proof. intros. unfold retval, get_result1. simpl. normalize. Qed.
Hint Rewrite retval_get_result1 : normalize.

Lemma retval_lemma1:
  forall rho v,     retval (env_set rho ret_temp v) = v.
Proof.
 intros. unfold retval. unfold eval_id. simpl. auto.
Qed.
Hint Rewrite retval_lemma1 : normalize.

Lemma retval_make_args:
  forall v rho, retval (make_args (ret_temp::nil) (v::nil) rho) = v.
Proof. intros. unfold retval, eval_id; simpl. reflexivity.
Qed.
Hint Rewrite retval_make_args: normalize.

Lemma ret_type_initialized:
  forall i Delta, ret_type (initialized i Delta) = ret_type Delta.
Proof.
intros.
unfold ret_type; simpl.
unfold initialized; simpl.
destruct ((temp_types Delta) ! i); try destruct p; reflexivity.
Qed.
Hint Rewrite ret_type_initialized : normalize.

Hint Rewrite bool_val_notbool_ptr using (solve [simpl; auto]) : normalize.
Instance Nassert: NatDed assert := _.
Instance Sassert: SepLog assert := _.
Instance Cassert: ClassicalSep assert := _. 
Instance Iassert: Indir assert := _.
Instance SIassert: SepIndir assert := _.

Lemma go_lower_lem1:
  forall (P1 P: Prop) (QR PQR: mpred),
      (P1 -> prop P && QR |-- PQR) ->
      (prop (P1 /\ P ) && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
Qed.

Lemma go_lower_lem2:
  forall  (QR PQR: mpred),
      (QR |-- PQR) ->
      (prop True && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intro; auto.
Qed.

Lemma go_lower_lem3:
  forall t a v (P: Prop) (QR PQR: mpred),
      (v=nullval -> prop P && QR |-- PQR) ->
      (prop (typed_false (Tpointer t a) v /\ P ) && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
 eapply typed_false_ptr; eauto.
Qed.

Lemma go_lower_lem6:
  forall {A} P (Q: A -> assert) PQR,
    (forall x, P && Q x |-- PQR) ->
    P && exp Q |-- PQR.
Proof.
 intros. normalize.
Qed.

Lemma go_lower_lem7:
  forall (R1: assert) (Q1: environ -> Prop) P Q R PQR,
      R1 && (PROPx P (LOCALx (Q1::Q) R)) |-- PQR ->
      (R1 && local Q1) && (PROPx P (LOCALx Q R)) |-- PQR.
Admitted.

Lemma go_lower_lem8:
  forall (R1 R2 R3: assert) PQR PQR',
      ((R1 && R2) && R3) && PQR |-- PQR' ->
      (R1 && (R2 && R3)) && PQR |-- PQR'.
Proof.
 intros. rewrite <- andp_assoc; auto.
Qed.

Lemma go_lower_lem9:
  forall (Q1: environ -> Prop) P Q R PQR,
      PROPx P (LOCALx (Q1::Q) R) |-- PQR ->
      local Q1 && (PROPx P (LOCALx Q R)) |-- PQR.
Admitted.

Lemma go_lower_lem10:
  forall (R1 R2 R3: assert) PQR',
      (R1 && R2) && R3 |-- PQR' ->
      (R1 && (R2 && R3)) |-- PQR'.
Proof.
 intros. rewrite <- andp_assoc; auto.
Qed.

Lemma go_lower_lem4:
  forall (P1 P: Prop) (QR PQR: mpred),
      prop P && QR |-- PQR ->
      prop (True /\ P ) && QR |-- PQR.
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
Qed.

Lemma go_lower_lem5:
  forall (P1 P: Prop) (QR PQR: mpred),
      prop P && QR |-- PQR ->
      prop (true=true /\ P ) && QR |-- PQR.
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
Qed.


Lemma go_lower_lem3b:
  forall t a v (QR PQR: mpred),
      (v=nullval -> QR |-- PQR) ->
      (prop (typed_false (Tpointer t a) v) && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intro.
 apply H.
 eapply typed_false_ptr; eauto.
Qed.

Lemma go_lower_lem11:
 forall P R,
   P |-- R ->
   P |-- prop True && R.
Proof.
 intros. normalize.
Qed.

Lemma go_lower_lem20:
  forall QR QR',
    QR |-- QR' ->
    PROPx nil QR |-- QR'.
Proof. unfold PROPx; intros; intro rho; normalize. Qed.

Lemma go_lower_lem21:
  forall QR QR',
    QR |-- QR' ->
    QR |-- PROPx nil QR'.
Proof. unfold PROPx; intros; intro rho; normalize. Qed.

Lemma go_lower_lem22:
  forall (P:Prop)  P' QR PQR',
    (P -> PROPx P' QR |-- PQR') ->
    PROPx (P::P') QR |-- PQR'.
Proof. intros. intro rho. unfold PROPx; simpl.
 normalize.
 destruct H0.
 unfold PROPx in H.
 eapply derives_trans; [ | apply H; auto].
 normalize.
Qed.

Lemma Vint_inj': forall i j,  (Vint i = Vint j) =  (i=j).
Proof. intros; apply prop_ext; split; intro; congruence. Qed.

Lemma TT_andp_right {A}{NA: NatDed A}:
 forall P Q, TT |-- P -> TT |-- Q -> TT |-- P && Q.
Proof.
  intros. apply andp_right; auto.
Qed. 

Lemma TT_prop_right {A}{NA: NatDed A}:
  forall P: Prop , P -> TT |-- prop P.
Proof. intros. apply prop_right. auto.
Qed.


Ltac go_lower1 :=
 repeat match goal with 
   | |- andp _ (exp (fun y => _)) |-- _ => 
          (* Note: matching in this special way uses the user's name 'y'
                 as a hypothesis; thats we use a "match goal" 
                 rather than just trying to apply the various lemmas *)
             apply go_lower_lem6; intro y
   | |- (_ && local _) && (PROPx _ (LOCALx _ _)) |-- _ =>
                     apply go_lower_lem7
   | |- (_ && (_ && _)) && (PROPx _ _) |-- _ =>
               apply go_lower_lem8
   | |- local _ && (PROPx _ (LOCALx _ _)) |-- _ =>
                     apply go_lower_lem9
   | |- _ && (_ && _) |-- _ => 
                    apply go_lower_lem10
   end.

Lemma trivial_typecheck:
  forall P, P |-- local (denote_tc_assert tc_TT).
Proof. intros. intro rho. apply prop_right. apply I. Qed.


Lemma overridePost_normal_right:
  forall P Q R, 
   P |-- Q ->
   P |-- overridePost Q R EK_normal None.
Proof. intros.
  intro rho; unfold overridePost; simpl. rewrite if_true; auto.
  normalize.
Qed.

Lemma go_lower_lem24:
  forall rho (Q1: environ -> Prop)  Q R PQR,
  (Q1 rho -> LOCALx Q R rho |-- PQR) ->
  LOCALx (Q1::Q) R rho |-- PQR.
Proof.
   unfold LOCALx,local; unfold_coerce; simpl; intros.
 normalize. 
 destruct H0.
 eapply derives_trans;  [ | apply (H H0)].
 normalize.
Qed.

Lemma go_lower_lem25:
  forall rho R PQR,
  R rho |-- PQR ->
  LOCALx nil R rho |-- PQR.
Proof. unfold LOCALx; intros; normalize. Qed.


Fixpoint fold_right_sepcon rho (l: list assert) : mpred :=
 match l with 
 | nil => emp
 | b::nil => b rho
 | b::r => b rho * fold_right_sepcon rho r
 end.

Fixpoint fold_right_andp rho (l: list (environ -> Prop)) : Prop :=
 match l with 
 | nil => True
 | b::nil => b rho
 | b::r => b rho /\ fold_right_andp rho r
 end.

Fixpoint fold_right_and P0 (l: list Prop) : Prop :=
 match l with 
 | nil => P0
 | b::r => b  /\ fold_right_and P0 r
 end.

Lemma go_lower_lem26:
 forall R PQR' rho,
  fold_right_sepcon rho R |-- PQR'    ->
  SEPx R rho |-- PQR'.
Proof.
 intros. change SEPx with SEPx'.
 eapply derives_trans with (fold_right_sepcon rho R).
 clear. induction R; simpl; auto.
 destruct R. apply derives_trans with (a rho * emp).
 apply sepcon_derives; auto. rewrite sepcon_emp; auto.
 apply sepcon_derives; auto. auto.
Qed.

Lemma go_lower_lem27a:
 forall P Q' R' rho,
  P |--  andp (prop (fold_right_andp rho Q'))  (fold_right_sepcon rho R') ->
  P |-- LOCALx Q' (SEPx R') rho.
Proof.
 intros. change SEPx with SEPx'.
 eapply derives_trans; [ apply H |].
 clear.
 unfold LOCALx. unfold local. unfold_coerce; simpl.
 apply andp_derives.
 apply prop_left; intro H;  apply prop_right; revert H.
 induction Q'; simpl; auto.
 destruct Q'; simpl in *. auto.
 intros [? ?]; split; auto.
 induction R'; simpl; auto.
 destruct R'. apply derives_trans with (a rho * emp).
 rewrite sepcon_emp; auto.
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
Qed.

Lemma go_lower_lem27c:
 forall P P' Q' R' rho,
  P |--  andp (prop (fold_right_and (fold_right_andp rho Q') P'))  (fold_right_sepcon rho R') ->
  P |-- PROPx P' (LOCALx Q' (SEPx R')) rho.
Proof.
 intros.
 eapply derives_trans; [ apply H |].
 clear.
 unfold PROPx.
 induction P'.
 simpl fold_right_and. normalize. apply go_lower_lem27a.
 apply andp_right; auto. apply prop_right; auto.
 simpl. normalize. destruct H.
 eapply derives_trans.
 2: eapply derives_trans; [ apply IHP' | ].
 apply andp_right; auto. apply prop_right; auto.
 apply andp_right; auto.
 normalize.
 apply andp_left1. 
 apply derives_trans with (!!a && !! (fold_right and True P')).
 apply andp_right. apply prop_right; auto.
 apply derives_refl.
 normalize.
 simpl.
 apply andp_left2; auto.
Qed.

Lemma go_lower_lem24a:
  forall rho t a e  Q R PQR,
  (e rho = nullval -> LOCALx Q R rho |-- PQR) ->
  LOCALx (`(typed_false (Tpointer t a)) e ::Q) R rho |-- PQR.
Proof. unfold LOCALx, local; unfold_coerce; intros.
 simpl. normalize.
 destruct H0.
 apply typed_false_ptr in H0.
  eapply derives_trans; [ | apply (H H0)].
 simpl.
  normalize.
 Qed.


Lemma refold_frame:
 forall rho (F: list assert) A, 
   match F with nil => A | _ :: _ => A * fold_right_sepcon rho F end =
             A * fold_right sepcon emp F rho.
Proof. 
 induction F; simpl; intros; auto.
 rewrite sepcon_emp; auto.
 f_equal; auto.
Qed.

Ltac go_lower2 :=
  match goal with
  | |- derives (PROPx _ (LOCALx _ (SEPx _))) _ =>
             idtac
  | |- _ => fail 1 "go_lower: not in PROP/LOCAL/SEP form"
  end;
 unfold tc_expr, tc_lvalue;
 try apply trivial_typecheck;
 repeat apply overridePost_normal_right;
 repeat (apply go_lower_lem22; intro);
 apply go_lower_lem20;
 try apply go_lower_lem21;
 unfold eval_expr,eval_lvalue;
  let rho := fresh "rho" in intro rho;
 repeat  (first [apply go_lower_lem24a | apply go_lower_lem24];
                 let H := fresh in 
                       (intro H; unfold_coerce));
  apply go_lower_lem25;
 apply go_lower_lem26; 
 try apply go_lower_lem27a;  try apply go_lower_lem27c;
 unfold fold_right_sepcon, fold_right_andp;
 change (TT rho) with (@TT mpred _);
 repeat (unfold ret_type; simpl); 
 unfold local; unfold_coerce;
 repeat rewrite retval_lemma1;
 try rewrite refold_frame.

Lemma tc_eval_id_i:
  forall Delta t i rho, 
               tc_environ Delta rho -> 
              (temp_types Delta)!i = Some (t,true) ->
              tc_val t (eval_id i rho).
Proof.
intros.
unfold tc_environ in H.
destruct rho; apply environ_lemmas.typecheck_environ_sound in H.
destruct H as [? _].
destruct (H i true t H0) as [v [? ?]].
unfold eval_id. simpl. rewrite H1. simpl; auto.
destruct H2. inv H2. auto.
Qed.

Lemma tc_val_extract_int:
 forall v sign ch attr, tc_val (Tint ch sign attr) v -> exists n, v = Vint n.
Proof.
intros. destruct v; inv H; eauto.
Qed.

Definition name (id: ident) := True.

Tactic Notation "name" ident(s) constr(id) := 
    assert (s: name id) by apply I.

Ltac findvars :=
repeat 
match goal with
             | H: tc_environ ?Delta ?RHO, Name: name ?J |- _ =>
                clear Name;
    first [
       let Hty := fresh in 
         assert (Hty: (temp_types Delta) ! J = Some (tint, true)) by (simpl; reflexivity);
       let Htc := fresh in let Htc' := fresh in
       assert (Htc: tc_val tint (eval_id J RHO))
                        by (apply (tc_eval_id_i Delta _ _ _ H Hty));
       destruct (tc_val_extract_int _ _ _ _ Htc) as [Name Htc'];
       rewrite Htc' in *; clear Hty Htc Htc'
    | let t := fresh "t" in let TC := fresh "TC" in
         evar (t: type);
         assert (TC: tc_val t (eval_id J RHO)) 
             by (eapply tc_eval_id_i; try eassumption; unfold t; simpl; reflexivity);
         unfold t in *; clear t;
         forget (eval_id J RHO) as Name
    ]
  end.

Lemma Vint_inj: forall x y, Vint x = Vint y -> x=y.
Proof. congruence. Qed.
Lemma eval_cast_id:
  forall Delta rho,
      tc_environ Delta rho ->
  forall t1 t3 id,
  Cop.classify_cast t1 t3 = Cop.cast_case_neutral ->
  match (temp_types Delta)!id with Some (Tpointer _ _, true) => true | _ => false end = true ->
  eval_cast t1 t3 (eval_id id rho) = eval_id id rho.
Proof.
intros.
 revert H1; case_eq ((temp_types Delta) ! id); intros; try discriminate.
 destruct p as [t2 ?].
 destruct t2; inv H2.
 destruct b; inv H4.
 pose proof (tc_eval_id_i _ _ _ _ H H1).
 hnf in H2.
 unfold typecheck_val in H2.
 destruct (eval_id id  rho); inv H2.
 pose proof (Int.eq_spec i Int.zero). rewrite H4 in H2. subst. clear H4.
 destruct t1; destruct t3; inv H0; 
  try (destruct i; inv H3); try (destruct i0; inv H2); try reflexivity.
 destruct t1; destruct t3; inv H0; 
  try (destruct i0; inv H3); try (destruct i1; inv H2); try reflexivity.
Qed.


Lemma eval_cast_var:
  forall Delta rho,
      tc_environ Delta rho ->
  forall t1 t2 t3 id,
  Cop.classify_cast t1 t3 = Cop.cast_case_neutral ->
  tc_lvalue Delta (Evar id t2) rho ->
  eval_cast t1 t3 (eval_var id t2 rho) = eval_var id t2 rho.
Proof.
intros.
 pose proof (expr_lemmas.typecheck_lvalue_sound _ _ _ H H1 (Tpointer t2 noattr) (eq_refl _)).
 unfold typecheck_val in H2. simpl in H2.
 destruct (eval_var id t2 rho); inv H2.
 pose proof (Int.eq_spec i Int.zero). rewrite H4 in H2. subst. clear H4.
 destruct t1; destruct t3; inv H0; 
  try (destruct i; inv H3); try (destruct i0; inv H2); try reflexivity.
 destruct t1; destruct t3; inv H0; 
  try (destruct i0; inv H3); try (destruct i1; inv H2); try reflexivity.
Qed.

Lemma eval_cast_int:
  forall v sign, 
         tc_val (Tint I32 sign noattr) v ->
         eval_cast (Tint I32 sign noattr) (Tint I32 sign noattr) v = v.
Proof.
 intros.
 unfold tc_val, eval_cast, Cop.sem_cast, force_val; simpl in *; 
 destruct v; simpl; auto; inv H; auto.
Qed.

Lemma eval_cast_pointer2: 
  forall v t1 t2 t3 t1' t2',
   t1' = Tpointer t1 noattr ->
   t2' = Tpointer t2 noattr ->
   tc_val (Tpointer t3 noattr) v ->
   eval_cast t1' t2' v = v.
Proof.
intros.
subst.
hnf in H1. destruct v; inv H1; reflexivity.
Qed.

Ltac eval_cast_simpl :=
     try match goal with H: tc_environ ?Delta ?rho |- _ =>
       repeat first [rewrite (eval_cast_var Delta rho H); [ | reflexivity | hnf; simpl; normalize ]
               | rewrite (eval_cast_id Delta rho H); [ | reflexivity | reflexivity ]
               | rewrite eval_cast_int; [ | assumption]
               | erewrite eval_cast_pointer2; [ | | | eassumption ]; [ | reflexivity | reflexivity ]
               ]
     end.


Ltac go_lower3 :=
                           autorewrite with normalize; 
                           auto with typeclass_instances;
                           findvars; 
                           eval_cast_simpl;
                           try match goal with H: tc_environ _ ?rho |- _ =>
                                   clear H rho
                           end;
                           repeat match goal with H: context [eval_cast ?a ?b ?c] |- _ =>
                                  try change (eval_cast a b c) with c in H
                           end;
                           repeat match goal with |- context [eval_cast ?a ?b ?c] =>
                               try change (eval_cast a b c) with c
                           end;
                           repeat rewrite Vint_inj' in *;
                           autorewrite with normalize;
                           repeat apply TT_andp_right; try apply TT_prop_right; auto.

Ltac go_lower := go_lower2; go_lower3.



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

Lemma unfold_lift0C: forall {A} (f: A) (rho: environ),  `f rho = f.
Proof. reflexivity. Qed.
Hint Rewrite @unfold_lift0C: normalize.

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
Hint Rewrite local_unfold : normalize.

Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfoldC: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        `f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift1_unfoldC: forall {A1 B} (f: A1 -> B) a1 (rho: environ),
        `f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.
Hint Rewrite @lift2_unfold @lift1_unfold : normalize.
Hint Rewrite @lift2_unfoldC @lift1_unfoldC : normalize.

Lemma lower_sepcon:
  forall P Q rho, @sepcon assert Nassert Sassert P Q rho = sepcon (P rho) (Q rho).
Proof. reflexivity. Qed.
Lemma lower_andp:
  forall P Q rho, @andp assert Nassert P Q rho = andp (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite lower_sepcon lower_andp : normalize.

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
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Lemma canon2: forall Q1 B P Q R,
    do_canon (local Q1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx (Q1::Q) (SEPx R))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
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
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
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
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
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
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
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
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
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
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho.
simpl.
normalize.
Qed.

Ltac canonicalize_pre :=
  match goal with |- semax _ ?P _ _ =>
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

Hint Resolve @andp_later_derives @sepcon_later_derives @sepcon_derives
              @andp_derives @imp_derives @now_later @derives_refl: derives.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Notation " a 'OF' ta " := (a%type,ta%type) (at level 100, only parsing): formals.
Delimit Scope formals with formals.

Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) tx (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, P at level 100, Q at level 100).

Notation "'WITH' x : tx 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) tx (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2)
           (fun x => let (x1,x2):=x in P%logic) (fun x => let (x1,x2):=x in Q%logic))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2)
           (fun x => let (x1,x2):=x in P%logic) (fun x => let (x1,x2):=x in Q%logic))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3)
           (fun x => match x with ((x1,x2),x3) => P%logic end)
           (fun x => match x with ((x1,x2),x3) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2*t3)
           (fun x => match x with ((x1,x2),x3) => P%logic end)
           (fun x => match x with ((x1,x2),x3) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100).

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
change SEPx with SEPx'.
unfold PROPx, LOCALx, SEPx', lift2.
normalize.
unfold local, lift1. simpl.
f_equal.
apply pred_ext; normalize.
Qed.
Hint Rewrite insert_local:  normalize.


Lemma semax_pre0:
 forall P' Delta P c R,
     P |-- P' ->
     semax Delta P' c R  -> 
     semax Delta P c R.
Proof.
intros.
eapply semax_pre; try apply H0.
 apply andp_left2; auto.
Qed.

Lemma semax_pre_PQR:
 forall P' Delta P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     semax Delta P' c R  -> 
     semax Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof.
intros.
eapply semax_pre; try apply H0.
 rewrite insert_local. auto.
Qed.

Lemma semax_while' : 
 forall Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta test) ->
     PROPx P (LOCALx (tc_environ Delta :: lift1 (typed_false (typeof test)) (eval_expr test) :: Q) (SEPx R)) |-- Post EK_normal None ->
     semax Delta (PROPx P (LOCALx (lift1 (typed_true (typeof test)) (eval_expr test) :: Q) (SEPx R)))  body (loop1_ret_assert (PROPx P (LOCALx Q (SEPx R))) Post) ->
     semax Delta (PROPx P (LOCALx Q (SEPx R))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
eapply derives_trans; [ | apply H0].
normalize.
eapply derives_trans; [ | apply H1].
intro rho; unfold PROPx,LOCALx,lift1,lift0; simpl; normalize.
eapply semax_pre; [ | apply H2].
intro rho; unfold PROPx,LOCALx,lift1,lift0; simpl; normalize.
Qed.

Lemma semax_whilex : 
 forall Delta A P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall x, PROPx (P x) (LOCALx (tc_environ Delta :: (Q x)) (SEPx (R x))) |-- 
                               local (tc_expr Delta test)) ->
     (forall x, PROPx (P x) (LOCALx (tc_environ Delta :: lift1 (typed_false (typeof test)) (eval_expr test) :: (Q x)) (SEPx (R x))) 
                    |-- Post EK_normal None) ->
     (forall x:A, semax Delta (PROPx (P x) (LOCALx (lift1 (typed_true (typeof test)) (eval_expr test) :: Q x) (SEPx (R x))))  
                           body 
                            (loop1_ret_assert (EX x:A, PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) Post))->
     semax Delta (EX x:A, PROPx (P x) (LOCALx (Q x) (SEPx (R x) ))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
rewrite exp_andp2.
apply exp_left. intro x; eapply derives_trans; [ | apply (H0 x)].
normalize.
rewrite exp_andp2.
apply exp_left. intro x; eapply derives_trans; [ | apply (H1 x)].
intro rho; unfold PROPx,LOCALx,lift1,lift0; simpl; normalize.
normalize.
apply extract_exists_pre; intro x.
eapply semax_pre; [ | apply (H2 x)].
intro rho; unfold PROPx,LOCALx,lift1,lift0; simpl; normalize.
Qed.


Lemma semax_whilex2 : 
 forall Delta A1 A2 P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall x1 x2, PROPx (P x1 x2) (LOCALx (tc_environ Delta :: (Q x1 x2)) (SEPx (R x1 x2))) |-- 
                               local (tc_expr Delta test)) ->
     (forall x1 x2, PROPx (P x1 x2) (LOCALx (tc_environ Delta :: lift1 (typed_false (typeof test)) (eval_expr test) :: (Q x1 x2)) (SEPx (R x1 x2))) 
                    |-- Post EK_normal None) ->
     (forall (x1:A1) (x2: A2), 
               semax Delta (PROPx (P x1 x2) (LOCALx (lift1 (typed_true (typeof test)) (eval_expr test) :: Q x1 x2) (SEPx (R x1 x2))))  
                           body 
                            (loop1_ret_assert (EX x1:A1, EX x2:A2, PROPx (P x1 x2) (LOCALx (Q x1 x2) (SEPx (R x1 x2)))) Post))->
     semax Delta (EX x1:A1, EX x2:A2, PROPx (P x1 x2) (LOCALx (Q x1 x2) (SEPx (R x1 x2) ))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
rewrite exp_andp2. apply exp_left. intro x1.
rewrite exp_andp2. apply exp_left. intro x2.
 eapply derives_trans; [ | apply (H0 x1 x2)].
normalize.
rewrite exp_andp2. apply exp_left. intro x1.
rewrite exp_andp2. apply exp_left. intro x2.
 eapply derives_trans; [ | apply (H1 x1 x2)].
intro rho; unfold PROPx,LOCALx,lift1,lift0; simpl; normalize.
normalize. apply extract_exists_pre; intro x1.
normalize. apply extract_exists_pre; intro x2.
eapply semax_pre; [ | apply (H2 x1 x2)].
intro rho; unfold PROPx,LOCALx,lift1,lift0; simpl; normalize.
Qed.

Ltac forward_while Inv Postcond :=
  apply semax_pre_PQR with Inv;
    [ | (apply semax_seq with Postcond;
            [ apply semax_while' ; [ compute; auto | | | ] 
            | simpl update_tycon ])
        || (repeat match goal with 
         | |- semax _ (?X _ _ _) _ _ => unfold X
         | |- semax _ (?X _ _) _ _ => unfold X
         | |- semax _ (?X _) _ _ => unfold X
         | |- semax _ ?X _ _ => unfold X
        end;
          match goal with
          | |- semax _  (exp (fun y => _)) _ _ =>
             (* Note: matching in this special way uses the user's name 'y'  as a hypothesis *)
              apply semax_seq with Postcond ;
               [apply semax_whilex;
                  [ compute; auto 
                  | intro y | intro y 
                  | intro y ; 
                     match goal with |- semax _ _ _ (loop1_ret_assert ?S _) =>
                             change S with Inv
                     end
                  ]
               | simpl update_tycon ]
          | |- semax _  (exp (fun y1 => (exp (fun y2 => _)))) _ _ =>
             (* Note: matching in this special way uses the user's name 'y'  as a hypothesis *)
              apply semax_seq with Postcond ;
               [apply semax_whilex2; 
                 [ compute; auto
                 | intros y1 y2 
                 | intros y1 y2 
                 | intros y1 y2; 
                     match goal with |- semax _ _ _ (loop1_ret_assert ?S _) =>
                             change S with Inv
                     end
                 ]
               | simpl update_tycon ]
        end)

   ].

Ltac find_in_list A L :=
 match L with 
  | A :: _ => constr:(O)
  | _ :: ?Y => let n := find_in_list A Y in constr:(S n)
  | nil => fail
  end.

Ltac length_of R :=
 match R with
  |  nil => constr:(O)
  |  _:: ?R1 => let n := length_of R1 in constr:(S n)
 end.

Fixpoint delete_nth {A} (n: nat) (xs: list A) {struct n} : list A :=
 match n, xs with
 | O, y::ys => ys
 | S n', y::ys =>y :: delete_nth n' ys
 | _ , _ => nil
 end.

Lemma grab_nth_LOCAL:
   forall n P Q R,
     (PROPx P (LOCALx Q (SEPx R))) = 
     (PROPx P (LOCALx (nth n Q (lift0 True) :: delete_nth n Q) (SEPx R))).
Proof.
intros n P Q R.
f_equal.
unfold LOCALx, local; unfold_coerce.
f_equal.
extensionality rho;  f_equal.
revert Q; induction n; intros.
destruct Q; simpl nth. unfold delete_nth.
apply prop_ext; simpl; intuition.
simpl. auto.
destruct Q; simpl nth; unfold delete_nth; fold @delete_nth.
apply prop_ext; simpl; intuition.
simpl.
apply prop_ext.
rewrite (IHn Q).
simpl.
clear IHn.
intuition.
Qed.

Lemma grab_nth_SEP:
   forall n P Q R,
    PROPx P (LOCALx Q (SEPx R)) = (PROPx P (LOCALx Q (SEPx (nth n R emp :: delete_nth n R)))).
Proof.
intros.
f_equal. f_equal.
change SEPx with SEPx'.
extensionality rho; unfold SEPx'.
revert R; induction n; intros; destruct R.
simpl. rewrite sepcon_emp; auto.
simpl nth.
unfold delete_nth.
auto.
simpl.
rewrite sepcon_emp; auto.
change (fold_right sepcon emp (a :: R) rho)
  with (a rho * fold_right sepcon emp R rho).
rewrite IHn.
simpl.
repeat rewrite <- sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

Ltac focus_SEP n := 
   rewrite (grab_nth_SEP n); unfold nth, delete_nth.

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
 match goal with |- semax _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in 
      apply semax_pre with P'; [ | ]
  end
 end.

Lemma semax_extract_PROP_True:
  forall Delta (PP: Prop) P QR c Post,
        PP ->
        semax Delta (PROPx P QR) c Post -> 
       semax Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre with (PROPx P QR).
unfold PROPx in *; simpl. normalize. auto.
Qed.

Lemma semax_extract_PROP:
  forall Delta (PP: Prop) P QR c Post,
       (PP -> semax Delta (PROPx P QR) c Post) -> 
       semax Delta (PROPx (PP::P) QR) c Post.
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
(*
Ltac focus_SEP n := 
 rewrite restart_canon; rewrite (grab_nth_SEP n); unfold nth, delete_nth; normalize.
*)

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
change SEPx with SEPx'.
intros.
intro rho.
specialize (H0 rho).
unfold SEPx' in *; intros; normalize.
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


Ltac simpl_tc_expr :=
    match goal with |- context [tc_expr ?A ?B] =>
        change (tc_expr A B) with (denote_tc_assert (typecheck_expr A B));
        simpl typecheck_expr; simpl denote_tc_assert
    end.


Lemma local_lift0: forall P, local (lift0 P) = prop P.
Proof.
intros. extensionality rho. reflexivity.
Qed.
Hint Rewrite @local_lift0: normalize.

Lemma move_prop_from_LOCAL:
  forall P1 P Q R, PROPx P (LOCALx (lift0 P1::Q) R) = PROPx (P1::P) (LOCALx Q R).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, local, lift0, lift1.
 simpl.
 normalize.
 apply pred_ext; normalize.
Qed.

Ltac extract_prop_in_LOCAL :=
 match goal with |- semax _ (PROPx _ (LOCALx ?Q _)) _ _ =>
   match Q with context [ lift0 ?z :: _ ] =>
        let n := find_in_list (lift0 z) Q
         in rewrite (grab_nth_LOCAL n); rewrite move_prop_from_LOCAL
  end
end.

Ltac repeat_extract_exists_pre :=
   first [(apply extract_exists_pre;
             let x := fresh "x" in intro x; normalize;
                repeat_extract_exists_pre;
                revert x)
           | autorewrite with canon
          ].
             

Lemma extract_exists_in_SEP:
  forall {A} (R1: A -> assert) P Q R,   
    PROPx P (LOCALx Q (SEPx (exp R1 :: R))) = 
    EX x:A, PROPx P (LOCALx Q (SEPx (R1 x::R))).
Proof.
intros.
extensionality rho.
change SEPx with SEPx'.
unfold PROPx, LOCALx, SEPx'; simpl.
normalize.
Qed.

Ltac extract_exists_in_SEP :=
 match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ exp ?z :: _] =>
        let n := find_in_list (exp z) R 
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  end
end.

Lemma flatten_sepcon_in_SEP:
  forall P Q R1 R2 R, 
           PROPx P (LOCALx Q (SEPx ((R1*R2) :: R))) = 
           PROPx P (LOCALx Q (SEPx (R1 :: R2 :: R))).
Proof.
intros.
f_equal. f_equal. extensionality rho.
change SEPx with SEPx'.
simpl. rewrite sepcon_assoc. auto.
Qed.

Ltac flatten_sepcon_in_SEP :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ (sepcon ?x  ?y) :: ?R'] =>
  let n := length_of R in let n' := length_of R' in 
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth; 
         rewrite flatten_sepcon_in_SEP
end
end.

Lemma move_prop_from_SEP:
  forall P1 R1 P Q R, 
      PROPx P (LOCALx Q (SEPx ((!!P1&&R1) :: R))) = PROPx (P1::P) (LOCALx Q (SEPx (R1::R))).
Proof.
 intros.
 extensionality rho.
change SEPx with SEPx'.
 unfold PROPx, LOCALx, SEPx', local, lift0, lift1.
 simpl.
 apply pred_ext; normalize.
Qed.

Lemma move_local_from_SEP:
  forall P1 R1 P Q R, 
      PROPx P (LOCALx Q (SEPx ((local P1&&R1) :: R))) = PROPx P (LOCALx (P1::Q) (SEPx (R1::R))).
Proof.
 intros.
 extensionality rho.
change SEPx with SEPx'.
 unfold PROPx, LOCALx, SEPx', local, lift0, lift1.
 simpl.
 apply pred_ext; normalize.
Qed.

Hint Rewrite move_prop_from_SEP move_local_from_SEP : normalize.

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
Hint Rewrite @subst_andp subst_prop : subst.

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
Hint Rewrite @subst_lift0 @subst_lift1 @subst_lift2 : subst.

Lemma subst_lift0': forall {A} id v (f: A),
        subst id v (fun _ => f) = (fun _ => f).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1':
  forall {A1 B} id v (f: A1 -> B) a, 
          subst id v (fun rho => f (a rho)) = fun rho => f (subst id v a rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2':
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b, 
          subst id v (fun rho => f (a rho) (b rho)) = fun rho => f (subst id v a rho) (subst id v b rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift0' @subst_lift1' @subst_lift2' : subst.
Hint Rewrite @subst_lift0' @subst_lift1' @subst_lift2' : normalize.

Lemma subst_lift0C:
  forall {B} id (v: environ -> val) (f: B) , 
          subst id v (@coerce B (environ -> B) (lift0_C B) f) = `f.
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @subst_lift0C : normalize.
Hint Rewrite @subst_lift0C : subst.

Lemma subst_lift1C:
  forall {A1 B} id (v: environ -> val) (f: A1 -> B) (a: environ -> A1), 
          subst id v (@coerce (A1 -> B) ((environ -> A1) -> environ -> B) (lift1_C A1 B) f a) 
               = `f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @subst_lift1C : normalize.
Hint Rewrite @subst_lift1C : subst.

Lemma subst_lift2C:
  forall {A1 A2 B} id (v: environ -> val) (f: A1 -> A2 -> B) (a: environ -> A1) (b: environ -> A2), 
          subst id v (@coerce (A1 -> A2 -> B) ((environ -> A1) -> (environ -> A2) -> environ -> B)
                  (lift2_C A1 A2 B) f a b) = `f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.
Hint Rewrite @subst_lift2C : normalize.
Hint Rewrite @subst_lift2C : subst.

Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

Hint Rewrite @map_cons : normalize.
Hint Rewrite @map_cons : subst.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.

Hint Rewrite @map_nil : normalize.
Hint Rewrite @map_nil : subst.

Lemma fold_right_cons: forall {A B} (f: A -> B -> B) (z: B) x y,
   fold_right f z (x::y) = f x (fold_right f z y).
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_cons : normalize.
Hint Rewrite @fold_right_cons : subst.

Lemma subst_sepcon: forall i v (P Q: assert),
  subst i v (P * Q) = (subst i v P * subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_sepcon : normalize.
Hint Rewrite subst_sepcon : subst.

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
change SEPx with SEPx'.
unfold SEPx'.
induction R; auto.
normalize.
f_equal; auto.
Qed.
Hint Rewrite subst_PROP : normalize.
Hint Rewrite subst_PROP : subst.

Lemma subst_stackframe_of:
  forall i v f, subst i v (stackframe_of f) = stackframe_of f.
Proof.
unfold stackframe_of; simpl; intros.
unfold subst.
extensionality rho.
induction (fn_vars f). reflexivity.
simpl map. repeat rewrite fold_right_cons.
f_equal.
apply IHl.
Qed.
Hint Rewrite subst_stackframe_of : normalize.
Hint Rewrite subst_stackframe_of : subst.

Lemma lower_PROP_LOCAL_SEP:
  forall P Q R rho, PROPx P (LOCALx Q (SEPx R)) rho = 
     (!!fold_right and True P && (local (fold_right (`and) (`True) Q) && (fold_right sepcon emp R))) rho.
Proof. reflexivity. Qed.
Hint Rewrite lower_PROP_LOCAL_SEP : normalize.

Lemma lower_TT: forall rho, @TT assert Nassert rho = @TT mpred Nveric.
Proof. reflexivity. Qed.
Hint Rewrite lower_TT : normalize.

Lemma lower_FF: forall rho, @FF assert Nassert rho = @FF mpred Nveric.
Proof. reflexivity. Qed.
Hint Rewrite lower_FF : normalize.

Fixpoint iota_formals (i: ident) (tl: typelist) := 
 match tl with
 | Tcons t tl' => (i,t) :: iota_formals (i+1)%positive tl'
 | Tnil => nil
 end.

Fixpoint do_builtins (defs : list (ident * globdef fundef type)) : funspecs :=
 match defs with
  | (id, Gfun (External (EF_builtin _ sig) argtys resty))::defs' => 
     (id, mk_funspec (iota_formals 1%positive argtys, resty) unit FF FF) 
      :: do_builtins defs'
  | _ => nil
 end.

Lemma semax_seq': 
 forall Delta P c1 P' c2 Q, 
         semax Delta P c1 (normal_ret_assert P') ->
         semax (update_tycon Delta c1) P' c2 Q ->
         semax Delta P (Ssequence c1 c2) Q.
Proof.
 intros. apply semax_seq with P'; auto.
 apply sequential'. auto. 
Qed.

Lemma semax_post_flipped' : 
   forall (R': assert) (Delta: tycontext) (R P: assert) c,
       semax Delta P c (normal_ret_assert R') ->
       R' |-- R ->
       semax Delta P c (normal_ret_assert R).
 Proof. intros; eapply semax_post'; eauto. Qed.

Ltac make_sequential :=
  match goal with
  | |- semax _ _ _ (normal_ret_assert _) => idtac
  | |- _ => apply sequential
  end.

