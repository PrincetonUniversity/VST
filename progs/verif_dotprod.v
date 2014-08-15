Require Import floyd.proofauto.
Require Import progs.dotprod.

Local Open Scope logic.

Definition add_spec :=
 DECLARE _add
  WITH x: val, y : val, z: val, fy : Z -> float, fz: Z -> float
  PRE  [_x OF tptr tdouble, _y OF tptr tdouble, _z OF tptr tdouble] 
      PROP ()
      LOCAL (`(eq x) (eval_id _x);
                  `(eq y) (eval_id _y);
                  `(eq z) (eval_id _z))
      SEP (`(array_at_ tdouble Tsh 0 3 x) ;
             `(array_at tdouble Tsh (Vfloat oo fy) 0 3 y);
             `(array_at tdouble Tsh (Vfloat oo fz) 0 3 z))
  POST [ tvoid ] 
      PROP ()
      LOCAL ()
      SEP (`(array_at tdouble Tsh (Vfloat oo (fun i => Float.add (fy i) (fz i))) 0 3 x);
             `(array_at tdouble Tsh (Vfloat oo fy) 0 3 y);
             `(array_at tdouble Tsh (Vfloat oo fz) 0 3 z) ).

Definition dotprod (n: Z) (fx fy : Z -> float) : float :=
  fold_range (fun i sum => Float.add sum (Float.mul (fx i) (fy i)))
            Float.zero 0 n.

Definition dotprod_spec :=
 DECLARE _dotprod
  WITH n: Z, x: val, y : val, fx : Z -> float, fy: Z -> float, sh: share
  PRE  [_n OF tint, _x OF tptr tdouble, _y OF tptr tdouble] 
      PROP (0 <= n <= Int.max_signed)
      LOCAL (`(eq (Vint (Int.repr n))) (eval_id _n);
                  `(eq x) (eval_id _x);
                  `(eq y) (eval_id _y))
      SEP (`(array_at tdouble sh (Vfloat oo fx) 0 n x);
             `(array_at tdouble sh (Vfloat oo fy) 0 n y))
  POST [ tdouble ] 
      PROP ()
      LOCAL (`(eq (Vfloat (dotprod n fx fy))) retval)
      SEP (`(array_at tdouble sh (Vfloat oo fx) 0 n x);
             `(array_at tdouble sh (Vfloat oo fy) 0 n y) ).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := 
     add_spec::dotprod_spec::nil.

Lemma dotprod_one_more:
  forall i f g, dotprod (i+1) f g = Float.add (dotprod i f g) (Float.mul (f i) (g i)).
Admitted.

Lemma body_dotprod:  semax_body Vprog Gprog f_dotprod dotprod_spec.
Proof.
start_function.
name n_ _n.
name i_ _i.
name x_ _x.
name y_ _y.

forward. (* sum = 0.0; *)
forward_for_simple_bound n
   (EX i:Z,
      PROP ()
      LOCAL (`(eq (Vfloat (dotprod i fx fy))) (eval_id _sum);
                  `(eq x) (eval_id _x);
                  `(eq y) (eval_id _y))
      SEP (`(array_at tdouble sh (Vfloat oo fx) 0 n x);
             `(array_at tdouble sh (Vfloat oo fy) 0 n y))).
* (* initializer *)
entailer!.
* (* body *)
forward_nl;
entailer!.
rewrite <- H1; f_equal.
apply dotprod_one_more.
* (*after the for-loop *)
 forward. (*   return; *)
Qed.

Lemma body_add:  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
name i_ _i.
name x_ _x.
name y_ _y.
name z_ _z.

forward_for_simple_bound 3
   (EX i:Z,
      PROP ()
      LOCAL (`(eq x) (eval_id _x);
                  `(eq y) (eval_id _y);
                  `(eq z) (eval_id _z))
      SEP (`(array_at tdouble Tsh
                   (fun j => if zlt j i then Vfloat (Float.add (fy j) (fz j)) else Vundef)
                  0 3 x) ;
             `(array_at tdouble Tsh (Vfloat oo fy) 0 3 y);
             `(array_at tdouble Tsh (Vfloat oo fz) 0 3 z))).
* (* initializer *)
entailer!.
* (* body *)
forward_nl. (* x[i] = y[i] + z[i]; *)
entailer!.
apply array_at_ext'; intros.
unfold upd. if_tac. subst i0. rewrite if_true by omega. auto.
if_tac. rewrite if_true by omega; auto. rewrite if_false by omega; auto.
* (*after the for-loop *)
 forward. (*   return; *)
Qed.

Definition Svector_add (n: Z) (_i _x _y _z : ident) :=
   Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
     (Sloop
        (Ssequence
           (Sifthenelse
              (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr n) tint) tint)
              Sskip
              Sbreak)
           (Sassign
              (Ederef
                 (Ebinop Oadd (Etempvar _x (tptr tdouble)) (Etempvar _i tint)
                    (tptr tdouble)) tdouble)
              (Ebinop Oadd
                 (Ederef
                    (Ebinop Oadd (Etempvar _y (tptr tdouble))
                       (Etempvar _i tint) (tptr tdouble)) tdouble)
                 (Ederef
                    (Ebinop Oadd (Etempvar _z (tptr tdouble))
                       (Etempvar _i tint) (tptr tdouble)) tdouble) tdouble)))
        (Sset _i
           (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))).

Definition vector_add (fx fy: Z -> float) i := 
    Float.add (fx i) (fy i).

Lemma SEPx_split_rest:
  forall P Q R1 R,
   PROPx P (LOCALx Q (SEPx (R1::R))) =
   PROPx P (LOCALx Q (SEPx (R1::nil))) *PROPx P (LOCALx Q (SEPx R)).
Proof.
Admitted.

Lemma replace_nth_commute:
  forall {A} i j R (a b: A),
   i <> j ->
   replace_nth i (replace_nth j R b) a =
   replace_nth j (replace_nth i R a) b.
Proof.
intros.
rename i into i'. rename j into j'. rename R into R'.
assert (forall i j R (a b: A),
             (i<j)%nat -> 
              replace_nth i (replace_nth j R b) a = replace_nth j (replace_nth i R a) b). {
induction i; destruct j, R; simpl; intros; auto; try omega.
f_equal. apply IHi. omega.
}
assert (i'<j' \/ i'>j')%nat by omega.
clear H.
destruct H1.
apply H0; auto.
symmetry; apply H0; auto.
Qed.

Lemma nth_error_replace_nth':
  forall {A} i j R (a:A),
  (i <> j)%nat -> nth_error (replace_nth i R a) j = nth_error R j.
Proof.
Admitted.
Lemma SEPx_drop_rest:
  forall P Q R1 R,
   PROPx P (LOCALx Q (SEPx (R1::R))) |--
   PROPx P (LOCALx Q (SEPx (R1::nil))) * TT.
Proof.
Admitted.
Ltac instantiate_Vptr :=
  match goal with
  | H:isptr (eval_id ?i ?rho), A:name ?i
    |- _ =>
        let b := fresh "b_" A in
        let z := fresh "z_" A in
        let J := fresh "H_" A in
        destruct (eval_id i rho) as [| | | | b z] eqn:J; try contradiction H;
         clear H; symmetry in J; rename J into H
  | H:isptr (eval_id ?i ?rho)
    |- _ =>
        let b := fresh "b_"  in
        let z := fresh "z_"  in
        let J := fresh "H_"  in
        destruct (eval_id i rho) as [| | | | b z] eqn:J; try contradiction H;
         clear H; symmetry in J; rename J into H
  end.

Lemma semax_vector_add:
    forall (sx sy sz : nat)
              (n: Z) Espec Delta P Q R Rx Ry Rz (_i _x _y _z : ident) (x y z: val) (fy fz : Z -> float),
    typeof_temp Delta _i = Some tint ->
    Forall (closed_wrt_vars (eq _i)) Q ->
    Forall (closed_wrt_vars (eq _i)) R ->
    (0 <= n <= Int.max_signed) ->
    PROPx P (LOCALx Q (SEPx (TT::nil))) |-- 
           local (`(eq x) (eval_id _x)) 
      && local (`(eq y) (eval_id _y)) 
      && local (`(eq z) (eval_id _z))  ->
   PROPx P (LOCALx Q (SEPx (Rx::nil))) |-- `(array_at_ tdouble Tsh 0 n x) ->
   PROPx P (LOCALx Q (SEPx (Ry::nil))) |-- `(array_at tdouble Tsh (Vfloat oo fy) 0 n y) ->
   PROPx P (LOCALx Q (SEPx (Rz::nil))) |-- `(array_at tdouble Tsh (Vfloat oo fz) 0 n z) ->
     nth_error R sx = Some Rx ->
    nth_error R sy = Some Ry ->
    nth_error R sz = Some Rz ->
    sx <> sy ->
    sx <> sz ->  @semax Espec Delta 
        (PROPx P (LOCALx Q (SEPx R)))
        (Svector_add n _i _x _y _z)
        (normal_ret_assert 
         (PROPx P (LOCALx Q
          (SEPx  (replace_nth sx R
             (`(array_at tdouble Tsh (Vfloat oo (vector_add fy fz)) 0 n x))))))).
Proof.
intros until 4. intros H6 H7 H8 H9 ? ? ? Nx Ny.
assert (Ti: (temp_types (initialized _i Delta)) ! _i = Some (tint, true)). {
clear - H. unfold typeof_temp in H.
destruct ((temp_types Delta) ! _i) eqn:?; inv H. destruct p.
inv H1. eapply temp_types_init_same; eauto.
}
apply semax_pre0 with
 (PROPx (isptr x :: isptr y :: isptr z :: P) (LOCALx Q (SEPx R))). {
repeat rewrite <- canonicalize.canon17.
repeat rewrite <- andp_assoc. apply andp_right; auto.
repeat apply andp_right.
rewrite (replace_nth_nth_error _ _ _ H3).
erewrite SEP_replace_nth_isolate by (eapply H3).
apply derives_trans
  with (PROPx P (LOCALx Q (SEP (Rx))) * SEPx (replace_nth sx R emp));
 [go_lower; normalize | ].
eapply derives_trans; 
  [apply sepcon_derives ; [apply H7 | apply TT_right] | ].
 unfold array_at_.
    rewrite array_at_isptr; normalize.
rewrite (replace_nth_nth_error _ _ _ H4).
erewrite SEP_replace_nth_isolate by (eapply H4).
apply derives_trans
  with (PROPx P (LOCALx Q (SEP (Ry))) * SEPx (replace_nth sy R emp));
 [go_lower; normalize | ].
eapply derives_trans; 
  [apply sepcon_derives ; [apply H8 | apply TT_right] | ].
    rewrite array_at_isptr; normalize.
rewrite (replace_nth_nth_error _ _ _ H5).
erewrite SEP_replace_nth_isolate by (eapply H5).
apply derives_trans
  with (PROPx P (LOCALx Q (SEP (Rz))) * SEPx (replace_nth sz R emp));
 [go_lower; normalize | ].
eapply derives_trans; 
  [apply sepcon_derives ; [apply H9 | apply TT_right] | ].
    rewrite array_at_isptr; normalize.
}
repeat rewrite <- canonicalize.canon17.
apply semax_extract_prop; intro Px.
apply semax_extract_prop; intro Py.
apply semax_extract_prop; intro Pz.
apply (semax_for_simple_bound_const_init n
   (EX  i : Z, PROPx ((fun _ => P) i)
                  (LOCALx ((fun _ => Q) i)
                  (SEPx ((fun i => 
                 replace_nth sx R
                   (`(array_at tdouble Tsh (fun j => if zlt j i then Vfloat (Float.add (fy j) (fz j)) else Vundef) 0 n x))
               ) i))))
     Espec Delta _ (fun _ => P) (fun _ => Q) (fun i =>  
                 replace_nth sx R
                   (`(array_at tdouble Tsh (fun j => if zlt j i then Vfloat (Float.add (fy j) (fz j)) else Vundef) 0 n x))
               ));
  try reflexivity; try auto with closed; try repable_signed.
* 
intro.
clear - H1.
revert R H1.
induction sx; destruct R; simpl; intros; auto with closed.
inv H1. auto with closed. inv H1;  constructor; auto with closed.
*
apply andp_left2.
replace (array_at tdouble Tsh
                 (fun j : Z =>
                  if zlt j 0
                  then Vfloat (Float.add (fy j) (fz j))
                  else Vundef) 0 n)
 with (array_at_ tdouble Tsh 0 n).
Focus 2.
unfold array_at_.
simple apply array_at_ext; intros.
rewrite if_false by omega. reflexivity.
apply derives_trans with 
  (PROPx P (LOCALx Q (SEPx (replace_nth sx R Rx)))).
rewrite <- (replace_nth_nth_error _ _ _ H3). auto.
rewrite <- insert_local.
apply andp_right.
go_lowerx; simpl. normalize.
erewrite SEP_replace_nth_isolate by eassumption.
erewrite SEP_replace_nth_isolate by eassumption.
rewrite SEPx_split_rest.
rewrite (SEPx_split_rest _ _ _ (replace_nth _ _ _)).
apply sepcon_derives; auto.
apply andp_right; [apply andp_left1; auto | ].
apply andp_right; [apply andp_left2; apply andp_left1; auto | ].
unfold SEPx at 2. unfold fold_right. rewrite sepcon_emp. auto.
*
intro i.
simpl tc_expr.
go_lowerx; normalize.
apply prop_right.
hnf. simpl. 
rewrite Ti. simpl. apply I.
*
rewrite normal_ret_assert_elim.
simpl update_tycon.
go_lowerx.
normalize.
apply derives_refl'.
f_equal. f_equal. f_equal. apply equal_f.
apply array_at_ext; intros.
rewrite if_true by omega.
reflexivity.
*
intro i.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
   apply semax_pre0 
   with (PROPx P (LOCALx (`(eq x) (eval_id _x) :: `(eq y) (eval_id _y) ::
                           `(eq z) (eval_id _z) :: Q) (SEPx R)))
 end.
rewrite <- (insert_local (`(eq _) (eval_id _x))).
rewrite <- (insert_local (`(eq _) (eval_id _y))).
rewrite <- (insert_local (`(eq _) (eval_id _z))).
repeat rewrite <- andp_assoc. apply andp_right; auto.
rewrite <- insert_local; apply andp_left2.
rewrite <- insert_local; apply andp_left2.
repeat rewrite <- canonicalize.canon17; apply andp_left2.
eapply derives_trans; [ | apply H6].
apply andp_derives; auto.
apply andp_derives; auto.
go_lowerx. rewrite sepcon_emp. apply TT_right.
apply semax_extract_PROP; intro.
eapply semax_pre0; [ apply now_later | ].
eapply semax_post_flipped';
   [simple eapply (semax_loadstore_array sx);
       [ reflexivity | apply I | reflexivity | reflexivity| reflexivity 
       | 
       | erewrite nth_error_replace_nth; eauto
       |  |  |  ]
    |  ].
match goal with |- (PROPx ?P (LOCALx ?Q (SEPx ?R)))  |-- _ =>
   set (R' := R)
end.
apply derives_trans with
(PROPx P
  (LOCALx
     (`(eq x) (eval_id _x)
      :: `(eq y) (eval_id _y)
         :: `(eq z) (eval_id _z)
            :: `(eq (Vint (Int.repr i))) (eval_id _i)
               :: `(eq (Vint (Int.repr n)))
                    (eval_expr (Econst_int (Int.repr n) tint)) :: Q)
     (SEPx R'))
   && ((TT * `(array_at tdouble Tsh (Vfloat oo fy) 0 n y))
     && (TT * `(array_at tdouble Tsh (Vfloat oo fz) 0 n z)))).
apply andp_right; auto.
apply andp_right.

repeat (rewrite <- insert_local;  apply andp_left2).
unfold R'.
rewrite (replace_nth_nth_error _ _ _ H4).
rewrite replace_nth_commute by auto.

erewrite SEP_replace_nth_isolate
 by (rewrite nth_error_replace_nth' by auto; eassumption).

 rewrite sepcon_comm.
 eapply derives_trans; [apply SEPx_drop_rest | ].
 apply sepcon_derives; auto.

repeat (rewrite <- insert_local;  apply andp_left2).
unfold R'.
rewrite (replace_nth_nth_error _ _ _ H5).
rewrite replace_nth_commute by auto.
erewrite SEP_replace_nth_isolate
 by (rewrite nth_error_replace_nth' by auto; eassumption).
 rewrite sepcon_comm.
 eapply derives_trans; [apply SEPx_drop_rest | ].
 apply sepcon_derives; auto.

go_lowerx.
unfold R'; clear R'.
normalize.
apply andp_left2.
 subst. repeat instantiate_Vptr; repeat apply andp_right.
rel_expr.
rel_expr.
simple eapply rel_expr_cast; [ | try (simpl; rewrite_eval_id; reflexivity) ].
simple eapply rel_expr_binop; [ |  | ].
apply andp_left1. rel_expr.
apply andp_left2. rel_expr.
reflexivity.
reflexivity.
auto.
apply I.
auto.

rewrite replace_nth_replace_nth.
go_lowerx; normalize.
apply andp_right.
 apply prop_right; repeat split; auto; omega.
apply derives_refl'.
f_equal. f_equal.
f_equal.
apply equal_f.
apply array_at_ext; intros.
unfold upd.
if_tac. subst. rewrite if_true by omega; try reflexivity.
if_tac.
rewrite if_true by omega; reflexivity.
rewrite if_false by omega; reflexivity.
Qed.

Lemma SEP1_entail:
  forall P Q R, PROPx P (LOCALx Q (SEP (R))) |-- R.
Proof.
intros. apply andp_left2. apply andp_left2.
go_lowerx. rewrite sepcon_emp; auto.
Qed.

Ltac forward_seq := 
  first [eapply semax_seq'; [  | abbreviate_semax ]
         | eapply semax_post_flipped' ].

Ltac forward_vector_add :=
 forward_seq;
 [eapply semax_vector_add;
   [reflexivity | auto 50 with closed | auto 50 with closed
   | repable_signed
   | repeat apply andp_right; go_lowerx; apply prop_right; eauto
   | try simple apply SEP1_entail
   | try simple apply SEP1_entail
   | try simple apply SEP1_entail
   | try solve_nth_error
   | try solve_nth_error
   | try solve_nth_error
   | computable | computable ]
 | unfold replace_nth
 ].

Lemma body_add':  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
name i_ _i.
name x_ _x.
name y_ _y.
name z_ _z.

forward_vector_add.
forward.
Qed.




