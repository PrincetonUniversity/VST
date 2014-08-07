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
eapply (semax_loadstore_array 0 i 0 n tdouble
               (Vfloat oo fx) x  (Vfloat (Float.add (fy i) (fz i))));
  try apply writable_share_top;
  try apply I; try reflexivity;
  try assumption.
*
 entailer.
 destruct (eval_id _x rho) eqn:Jx; inv H2. rename b into bx; rename i0 into zx.
 destruct (eval_id _y rho) eqn:Jy; inv H3. rename b into by'; rename i0 into zy.
 destruct (eval_id _z rho) eqn:Jz; inv H4. rename b into bz; rename i0 into zz.
 repeat apply andp_right.
 apply rel_expr_tempvar; apply eval_id_get; [solve [auto] | congruence ].
 apply rel_expr_tempvar; apply eval_id_get; [solve [auto] | congruence ].
 eapply rel_expr_cast.
 eapply rel_expr_binop.
 apply (rel_expr_array_load tdouble Tsh (Vfloat oo fy) 0 n (Vptr by' zy) i);
  auto.
 entailer.
 repeat apply andp_right. cancel.
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 apply (rel_expr_array_load tdouble Tsh (Vfloat oo fz) 0 n (Vptr bz zz) i);
  auto.
 repeat apply andp_right. entailer!.
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 eapply rel_expr_tempvar; apply eval_id_get; [auto| congruence].
 reflexivity.
 reflexivity.
*
 simpl update_tycon.
 forward.
 cancel.
 apply derives_refl'.
 apply equal_f.
 apply array_at_ext; intros.
 unfold upd, Basics.compose.  if_tac; auto.
Qed.

