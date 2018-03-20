Require Import VST.floyd.proofauto.
Require Import VST.progs.dotprod.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Local Open Scope logic.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.

Definition add_spec :=
 DECLARE _add
  WITH x: val, y : val, z: val, fy : list float, fz: list float
  PRE  [_x OF tptr tdouble, _y OF tptr tdouble, _z OF tptr tdouble]
      PROP ()
      LOCAL (temp _x x; temp _y y; temp _z z)
      SEP (data_at_ Tsh (tarray tdouble 3)  x ;
             data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
             data_at Tsh (tarray tdouble 3) (map Vfloat fz) z)
  POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (data_at Tsh (tarray tdouble 3) (map Vfloat (map2 Float.add fy fz)) x;
             data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
             data_at Tsh (tarray tdouble 3) (map Vfloat fz) z).

Definition dotprod (fx fy : list float) : float :=
  fold_left Float.add (map2 Float.mul fx fy) Float.zero .

Definition dotprod_spec :=
 DECLARE _dotprod
  WITH n: Z, x: val, y : val, fx : list float, fy: list float, sh: share
  PRE  [_n OF tint, _x OF tptr tdouble, _y OF tptr tdouble]
      PROP (0 <= n < Int.max_signed)
      LOCAL (temp _n (Vint (Int.repr n)); temp _x x; temp _y y)
      SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
             data_at Tsh (tarray tdouble n) (map Vfloat fy) y)
  POST [ tdouble ]
      PROP ()
      LOCAL (temp ret_temp (Vfloat (dotprod fx fy)))
      SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
             data_at Tsh (tarray tdouble n) (map Vfloat fy) y).


Definition Gprog : funspecs :=   ltac:(with_library prog [add_spec; dotprod_spec]).

Lemma map2_app:
 forall (A B C: Type) (f: A -> B -> C) al al' bl bl',
  Zlength al = Zlength bl ->
  Zlength al' = Zlength bl' ->
   map2 f (al ++ al') (bl ++ bl') = map2 f al bl ++ map2 f al' bl'.
Proof.
intros.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H. apply Nat2Z.inj in H0.
revert bl H al' bl' H0; induction al; intros.
*
destruct bl; inv H.
simpl. auto.
*
destruct bl.
inv H.
simpl.
f_equal.
auto.
Qed.

Lemma Zlength_map2: forall A B C (f: A -> B -> C) fy fz,
  Zlength fy = Zlength fz -> Zlength (map2 f fy fz) = Zlength fy.
Proof.
intros.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H. f_equal.
revert fz H; induction fy; destruct fz; intros; inv H.
auto.
simpl. f_equal; auto.
Qed.

Lemma Znth_map2:
 forall A B C (a: Inhabitant A) (b: Inhabitant B) (c: Inhabitant C) (f: A -> B -> C) (al: list A) (bl: list B) i,
  Zlength al = Zlength bl ->
  0 <= i < Zlength al ->
  Znth i (map2 f al bl) = f (Znth i al) (Znth i bl).
Proof.
intros.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H. f_equal.
unfold Znth.
if_tac. omega.
assert (Z.to_nat i < length al)%nat.
rewrite <- (Nat2Z.id (length al)).
apply Z2Nat.inj_lt; try omega.
clear H0 H1.
forget (Z.to_nat i) as j. clear i.
revert al bl H H2; induction j; intros.
destruct al; inv H2.
destruct bl; inv H.
simpl. auto.
destruct bl; inv H.
simpl. auto.
destruct al; simpl in H2; try omega.
destruct bl; inv H.
simpl.
apply IHj; auto.
omega.
Qed.

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
      LOCAL (temp _sum (Vfloat (dotprod (sublist 0 i fx) (sublist 0 i fy))); temp _x x; temp _y y; temp _n (Vint (Int.repr n)))
      SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
             data_at Tsh (tarray tdouble n) (map Vfloat fy) y)).
* (* initializer *)
entailer!.
* (* body *)
assert_PROP (Zlength fx = n /\ Zlength fy = n). {
    entailer!. autorewrite with sublist in *; split; auto.
} destruct H1.
forward.
forward. 
rewrite !Znth_map by omega.
forward. 
  entailer!.
  autorewrite with sublist in *.
  f_equal.
  rewrite (sublist_split 0 i _ fx) by omega.
  rewrite (sublist_split 0 i _ fy) by omega.
  unfold dotprod.
 rewrite map2_app by list_solve.
 rewrite fold_left_app.
 rewrite !sublist_len_1 by list_solve.
 simpl. auto.
*
 forward.
 autorewrite with sublist in *.
 autorewrite with sublist.
 entailer!.
Qed.

Lemma body_add:  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
name i_ _i.
name x_ _x.
name y_ _y.
name z_ _z.
pose (fx := map2 Float.add fy fz).
assert_PROP (Zlength fx = 3 /\ Zlength fy = 3 /\ Zlength fz = 3). {
  entailer!.
  autorewrite with sublist in *.
  split3; auto.
  subst fx. clear - H1 H4.
  rewrite Zlength_map2 by omega; auto.
} destruct H as [Hx [Hy Hz]].
forward_for_simple_bound 3
   (EX i:Z,
      PROP ()
      LOCAL (temp _x x; temp _y y; temp _z z)
      SEP (data_at Tsh (tarray tdouble 3) 
          (map Vfloat (sublist 0 i fx) ++ list_repeat (Z.to_nat (3-i)) Vundef) x;
   data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
   data_at Tsh (tarray tdouble 3) (map Vfloat fz) z)).
* (* initializer *)
entailer!.
* (* body *)
forward. (* x[i] = y[i] + z[i]; *)
forward.
forward.
entailer!. {
  autorewrite with sublist in *.
  simpl.
  unfold data_at.
  apply derives_refl'. f_equal.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite map_app.
 rewrite <- app_assoc.
 f_equal.
 replace (Z.to_nat (3-i)) with (Init.Nat.add (Z.to_nat 1) (Z.to_nat (3-(i+1)))).
 rewrite <-list_repeat_app.
 rewrite upd_Znth_app1 by list_solve.
 f_equal.
 autorewrite with sublist.
 simpl list_repeat.
 rewrite upd_Znth0.
 rewrite !sublist_len_1 by list_solve.
 autorewrite with sublist.
 simpl. 
 subst fx.
  f_equal. f_equal.
 rewrite Znth_map2 with (a:=Float.zero) (b:=Float.zero) (c:=Float.zero); try omega.
 auto.
 rewrite <- Z2Nat.inj_add by omega.
 f_equal. omega.
}
*
 forward.
 autorewrite with sublist. subst fx. auto.
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

(*
Lemma semax_vector_add:
    forall (lx ly lz sx sy sz: nat)
              (n: Z) Espec Delta P Q R  (_i _x _y _z : ident) (x y z: val) (fx: Z -> val) (fy fz : Z -> float),
    typeof_temp Delta _i = Some tint ->
    Forall (closed_wrt_vars (eq _i)) Q ->
    Forall (closed_wrt_vars (eq _i)) R ->
    (0 <= n <= Int.max_signed) ->
    nth_error Q lx = Some (`(eq x) (eval_id _x)) ->
    nth_error Q ly = Some (`(eq y) (eval_id _y)) ->
    nth_error Q lz = Some (`(eq z) (eval_id _z)) ->
    nth_error R sx = Some (`(array_at tdouble Tsh fx 0 n x)) ->
    nth_error R sy = Some (`(array_at tdouble Tsh (Vfloat oo fy) 0 n y)) ->
    nth_error R sz = Some (`(array_at tdouble Tsh (Vfloat oo fz) 0 n z)) ->
    sx <> sy ->
    sx <> sz ->
   @semax Espec Delta
        (PROPx P (LOCALx Q (SEPx R)))
        (Svector_add n _i _x _y _z)
        (normal_ret_assert
         (PROPx P (LOCALx Q
          (SEPx  (replace_nth sx R
             (`(array_at tdouble Tsh (Vfloat oo (vector_add fy fz)) 0 n x))))))).
Proof.
intros until 4. intros Jx Jy Jz H3 H4 H5 Ny Nz.
assert (Ti: (temp_types (initialized _i Delta)) ! _i = Some (tint, true)). {
clear - H. unfold typeof_temp in H.
destruct ((temp_types Delta) ! _i) eqn:?; inv H. destruct p.
inv H1. eapply temp_types_init_same; eauto.
}
apply semax_pre0 with
 (PROPx (isptr x :: isptr y :: isptr z :: P) (LOCALx Q (SEPx R))). {
repeat rewrite <- insert_prop.
repeat rewrite <- andp_assoc. apply andp_right; auto.
repeat apply andp_right.
rewrite (replace_nth_nth_error _ _ _ H3).
erewrite SEP_replace_nth_isolate by (eapply H3).
go_lowerx; normalize; rewrite array_at_isptr; normalize.
rewrite (replace_nth_nth_error _ _ _ H4).
erewrite SEP_replace_nth_isolate by (eapply H4).
go_lowerx; normalize; rewrite array_at_isptr; normalize.
rewrite (replace_nth_nth_error _ _ _ H5).
erewrite SEP_replace_nth_isolate by (eapply H5).
go_lowerx; normalize; rewrite array_at_isptr; normalize.
}
repeat rewrite <- insert_prop.
apply semax_extract_prop; intro Px.
apply semax_extract_prop; intro Py.
apply semax_extract_prop; intro Pz.
apply (semax_for_simple_bound_const_init n
   (EX  i : Z, PROPx ((fun _ => P) i)
                  (LOCALx ((fun _ => Q) i)
                  (SEPx ((fun i =>
                 replace_nth sx R
                   (`(array_at tdouble Tsh
                         (fun j => if zlt j i then Vfloat (Float.add (fy j) (fz j)) else fx j) 0 n x))
               ) i))))
     Espec Delta _ (fun _ => P) (fun _ => Q) (fun i =>
                 replace_nth sx R
                   (`(array_at tdouble Tsh (fun j => if zlt j i then Vfloat (Float.add (fy j) (fz j)) else fx j) 0 n x))
               ));
  try reflexivity; try auto with closed; try rep_omega.
*
apply andp_left2.
replace (array_at tdouble Tsh
                 (fun j : Z =>
                  if zlt j 0
                  then Vfloat (Float.add (fy j) (fz j))
                  else fx j) 0 n)
 with (array_at tdouble Tsh fx 0 n).
Focus 2.
simple apply array_at_ext; intros.
rewrite if_false by omega; reflexivity.
rewrite <- (replace_nth_nth_error _ _ _ H3).
rewrite <- insert_local.
apply andp_right; auto. go_lowerx. normalize.
*
intro i.
go_lowerx; normalize. apply prop_right. hnf. simpl.
rewrite Ti. simpl. apply I.
*
rewrite normal_ret_assert_elim.
drop_LOCAL 0%nat.
drop_LOCAL 0%nat.
apply replace_nth_SEP.
go_lowerx. apply array_at_ext'; intros.
rewrite if_true by omega. auto.
*
intro i.
drop_LOCAL 1%nat.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
   apply semax_pre0
   with (PROPx P (LOCALx (`(eq x) (eval_id _x) :: `(eq y) (eval_id _y) ::
                           `(eq z) (eval_id _z) :: Q) (SEPx R)))
 end.
rewrite <- (insert_local (`(eq _) (eval_id _x))).
rewrite <- (insert_local (`(eq _) (eval_id _y))).
rewrite <- (insert_local (`(eq _) (eval_id _z))).
repeat rewrite <- andp_assoc. apply andp_right; auto.
drop_LOCAL 0%nat.
repeat apply andp_right; eapply nth_error_local; eauto.
apply semax_extract_PROP; intro.

eapply semax_pre0; [ apply now_later | ].
eapply semax_post_flipped';
   [simple eapply (semax_loadstore_array sx);
       [ reflexivity | apply I | reflexivity | reflexivity| reflexivity
       |
       | erewrite nth_error_replace_nth; eauto
       | auto |  | eassumption ]
    |  ].
 +
  match goal with |- ?PQR  |-- _ =>
       apply derives_trans with
       (PQR
   && ((TT * `(array_at tdouble Tsh (Vfloat oo fy) 0 n y))
     && (TT * `(array_at tdouble Tsh (Vfloat oo fz) 0 n z))))
  end.
  apply andp_right; auto.
  apply andp_right.

  rewrite (replace_nth_nth_error _ _ _ H4).
  rewrite replace_nth_commute by auto.
  erewrite SEP_replace_nth_isolate
    by (rewrite nth_error_replace_nth' by auto; eassumption).
  rewrite sepcon_comm.
  rewrite <- insert_SEP. apply sepcon_derives; auto.

  rewrite (replace_nth_nth_error _ _ _ H5).
  rewrite replace_nth_commute by auto.
  erewrite SEP_replace_nth_isolate
   by (rewrite nth_error_replace_nth' by auto; eassumption).
   rewrite sepcon_comm.
   rewrite <- insert_SEP. apply sepcon_derives; auto.

  go_lowerx. normalize.
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
 +
   apply I.
 +
  simpl valinject.
  rewrite replace_nth_replace_nth.
  replace (array_at tdouble Tsh
               (upd
                  (fun j : Z =>
                   if zlt j i then Vfloat (Float.add (fy j) (fz j)) else fx j)
                  i (Vfloat (Float.add (fy i) (fz i)))) 0 n)
     with (array_at tdouble Tsh
                   (fun j : Z =>
                    if zlt j (i + 1)
                    then Vfloat (Float.add (fy j) (fz j))
                    else fx j) 0 n).
 entailer.
 apply array_at_ext; intros. symmetry.
 unfold upd.
 if_tac. subst. rewrite if_true by omega; try reflexivity.
 if_tac.
   rewrite if_true by omega; reflexivity.
   rewrite if_false by omega; reflexivity.
Qed.

Ltac forward_vector_add :=
 repeat match goal with |-
      semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 end;
 forward_seq;
 [eapply semax_vector_add;
 [reflexivity | auto 50 with closed | auto 50 with closed
   | rep_omega
   | solve_nth_error | solve_nth_error | solve_nth_error
   | solve_nth_error | solve_nth_error | solve_nth_error
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

*)



