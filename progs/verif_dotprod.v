Require Import floyd.proofauto.
Require Import progs.dotprod.

Local Open Scope logic.

Definition proj_x {A: Type} (p: A*A*A) : A := fst (fst p).
Definition proj_y {A: Type} (p: A*A*A) : A := snd (fst p).
Definition proj_z {A: Type} (p: A*A*A) : A := snd p.

Definition add_spec :=
 DECLARE _add
  WITH n: Z, i: Z, xyz: val*val*val,
            f: (Z -> float) * (Z -> float) * (Z -> float)
  PRE  [_i OF tint, _x OF tptr tdouble, _y OF tptr tdouble, _z OF tptr tdouble] 
      PROP (0 <= i < n; n <= Int.max_signed)
      LOCAL (`(eq (Vint (Int.repr i))) (eval_id _i);
                  `(eq (proj_x xyz)) (eval_id _x);
                  `(eq (proj_y xyz)) (eval_id _y);
                  `(eq (proj_z xyz)) (eval_id _z))
      SEP (`(array_at tdouble Tsh (Vfloat oo (proj_x f)) 0 n (proj_x xyz)) ;
             `(array_at tdouble Tsh (Vfloat oo (proj_y f)) 0 n (proj_y xyz));
             `(array_at tdouble Tsh (Vfloat oo (proj_z f)) 0 n (proj_z xyz)))
  POST [ tvoid ] 
      PROP ()
      LOCAL ()
      SEP (`(array_at tdouble Tsh (Vfloat oo (upd (proj_x f) i (Float.add ((proj_y f) i) ((proj_z f) i)))) 0 n  (proj_x xyz));
             `(array_at tdouble Tsh (Vfloat oo (proj_y f)) 0 n (proj_y xyz));
             `(array_at tdouble Tsh (Vfloat oo (proj_z f)) 0 n (proj_z xyz)) ).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := 
     add_spec::nil.

Lemma isptr_not_Vundef:
  forall v, isptr v -> v <> Vundef.
Proof.
intros. intro; subst; inv H.
Qed.

Lemma eval_id_get:
  forall rho i v, eval_id i rho = v -> v <> Vundef -> Map.get (te_of rho) i = Some v.
Proof.
intros.
unfold eval_id in H.
destruct (Map.get (te_of rho) i).
f_equal; assumption.
subst. contradiction H0; auto.
Qed.

Lemma body_add:  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
name i_ _i.
name x_ _x.
name y_ _y.
name z_ _z.
destruct xyz as [[x y] z].
destruct f as [[fx fy] fz].
unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
clear MORE_COMMANDS POSTCONDITION.
unfold proj_x, proj_y, proj_z; simpl.
eapply semax_seq'.
hoist_later_in_pre.
apply (semax_loadstore
             (Vfloat (fx i))
             (offset_val (Int.repr (i * sizeof tdouble)) x)
             (Vfloat (Float.add (fy i) (fz i)))
             _ _ _ Tsh _
              (PROP  ()
     LOCAL  (`(eq (Vint (Int.repr i))) (eval_id _i);
     `(eq x) (eval_id _x); `(eq y) (eval_id _y); `(eq z) (eval_id _z))
     SEP  (`(array_at tdouble Tsh (Vfloat oo fx) 0 i x);
      `(array_at tdouble Tsh (Vfloat oo fx) (i+1) n x);
     `(array_at tdouble Tsh (Vfloat oo fy) 0 n y);
     `(array_at tdouble Tsh (Vfloat oo fz) 0 n z)))
       writable_share_top).
*
 entailer.
 destruct (eval_id _x rho) eqn:Jx; inv H2. rename b into bx; rename i0 into zx.
 destruct (eval_id _y rho) eqn:Jy; inv H3. rename b into by'; rename i0 into zy.
 destruct (eval_id _z rho) eqn:Jz; inv H4. rename b into bz; rename i0 into zz.
 repeat apply andp_right; simpl.
 eapply rel_lvalue_deref.
 eapply rel_expr_binop.
 apply rel_expr_tempvar; apply eval_id_get; [solve [auto] | congruence ].
 apply rel_expr_tempvar; apply eval_id_get; [solve [auto] | congruence ].
 intro m; simpl. rewrite <- H1; simpl.
 rewrite Jx; unfold Cop.sem_add; simpl. rewrite mul_repr. rewrite Z.mul_comm. auto.
 eapply rel_expr_cast.
 eapply rel_expr_binop.
 eapply rel_expr_lvalue.
 apply rel_lvalue_deref.
 eapply rel_expr_binop.
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 intro m; simpl. rewrite <- H1; simpl.
 rewrite Jy; unfold Cop.sem_add; simpl. rewrite mul_repr. rewrite Z.mul_comm. auto.
 simpl typeof. (instantiate (2:=Tsh)). instantiate (1:= (Vfloat (fy i))).
 rewrite (split3_array_at i tdouble Tsh (Vfloat oo fy) 0 n (Vptr by' zy) H).
 simpl_data_at. normalize.
 unfold add_ptr_int. simpl. rewrite mul_repr. rewrite Z.mul_comm.
 cancel.
 congruence.
 eapply rel_expr_lvalue.
 apply rel_lvalue_deref.
 eapply rel_expr_binop.
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 intro m; simpl. rewrite <- H1; simpl.
 rewrite Jz; unfold Cop.sem_add; simpl. rewrite mul_repr. rewrite Z.mul_comm. auto.
 simpl typeof. (instantiate (2:=Tsh)). instantiate (1:= (Vfloat (fz i))).
 rewrite (split3_array_at i tdouble Tsh (Vfloat oo fz) 0 n (Vptr bz zz) H).
 simpl_data_at. normalize.
 unfold add_ptr_int. simpl. rewrite mul_repr. rewrite Z.mul_comm.
 cancel.
 congruence.
 intro m. simpl. reflexivity.
 simpl. auto.
 rewrite (split3_array_at i tdouble Tsh (Vfloat oo fx) 0 n (Vptr bx zx) H).
 cancel.
 simpl_data_at.
 normalize.
 unfold add_ptr_int. simpl. rewrite mul_repr. rewrite Z.mul_comm.
 cancel.
*
 simpl update_tycon.
 rewrite insert_SEP.
 simpl typeof.
 forward.
 cancel.
 rewrite (split3_array_at i tdouble Tsh (Vfloat oo upd fx i (Float.add (fy i) (fz i))) 0 n x_ H).
 rewrite (array_at_ext tdouble Tsh (Vfloat oo upd fx i (Float.add (fy i) (fz i))) (Vfloat oo fx) 0 i).
 rewrite (array_at_ext tdouble Tsh (Vfloat oo upd fx i (Float.add (fy i) (fz i))) (Vfloat oo fx) _ n).
 cancel.
 simpl_data_at.
 apply andp_right. apply prop_right.
 admit.  (* how to prove this? *)
 destruct x_; try contradiction.
 unfold add_ptr_int. simpl. rewrite mul_repr.
 rewrite Z.mul_comm. rewrite upd_eq. auto.
 intros. unfold Basics.compose.  f_equal. rewrite upd_neq; auto. omega.
 intros. unfold Basics.compose.  f_equal. rewrite upd_neq; auto. omega.
Qed.
