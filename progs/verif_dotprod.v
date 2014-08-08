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

Ltac instantiate_Vptr :=
match goal with H: isptr (eval_id ?i ?rho), A: name ?i |- _ =>
   let b := fresh "b_" A in let z := fresh "z_" A in let J := fresh "H_" A in
   destruct (eval_id i rho) as [ | | | | b z] eqn:J; try contradiction H; clear H;
     rename J into H
end.

Ltac solve_nth_error :=
match goal with |- @nth_error ?T (?A::_) ?n = Some ?B => 
 first [unify n O; unfold nth_error, value; repeat f_equal; reflexivity
        | let b := fresh "n" in evar (b:nat);  unify n (S b); 
          unfold nth_error; fold (@nth_error  T); solve_nth_error
        ]
end.

Lemma upd_compose:
  forall {A}{B}{C} {EA: EqDec A}(f: B ->C) (g: A -> B) (x: A) (y: B) x', 
           upd (Basics.compose f g) x (f y) x' = f (upd g x y x').
Proof.
 intros; unfold upd, Basics.compose.  if_tac; auto.
Qed.
Hint Rewrite @upd_compose : norm.

Lemma array_at_ext':
  forall t sh f g lo hi p,
   (forall i, lo <= i < hi -> f i = g i) ->
   array_at t sh f lo hi p |-- array_at t sh g lo hi p.
Proof.
 intros.
 apply derives_refl';  apply equal_f;  apply array_at_ext; auto.
Qed.

Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at _ _ _ _ _ _) =>
  (apply array_at_ext'; intros; solve [normalize]) : cancel.

Ltac forward_nl :=
 first
 [ simple eapply semax_seq';
   [hoist_later_in_pre;
    simple eapply semax_loadstore_array;
       [ reflexivity | apply I | reflexivity | reflexivity| reflexivity 
       | entailer; repeat instantiate_Vptr; repeat apply andp_right;
               forward_nl
       | try solve_nth_error | auto .. ]
    | unfold replace_nth; simpl valinject; abbreviate_semax ]
 | simple eapply rel_expr_array_load; [reflexivity | reflexivity | apply I 
   | repeat apply andp_right; [forward_nl | forward_nl | cancel | entailer.. ]]
 | simple apply rel_expr_tempvar;  apply eval_id_get; [solve [eauto] | congruence ]
 | simple eapply rel_expr_cast; [forward_nl | try reflexivity ]
 | simple eapply rel_expr_unop; [forward_nl | try reflexivity ]
 | simple eapply rel_expr_binop; [forward_nl | forward_nl | try reflexivity ]
 | simple apply rel_expr_const_int
 | simple apply rel_expr_const_float
 | simple apply rel_expr_const_long
 | simple eapply rel_lvalue_local
 | simple eapply rel_lvalue_global
 | simple eapply rel_lvalue_deref; [forward_nl ]
 | simple eapply rel_lvalue_field_struct; [ reflexivity | reflexivity | forward_nl ]
 | simple eapply rel_expr_lvalue; [ forward_nl | cancel | ]
 | idtac
 ].


Lemma body_add:  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
name i_ _i.
name x_ _x.
name y_ _y.
name z_ _z.
destruct xyz as [[x y] z].
destruct f as [[fx fy] fz].
unfold proj_x, proj_y, proj_z; simpl.
forward_nl. (* x[i] = y[i] + z[i]; *)
 forward. (*   return; *)
 cancel.
Qed.

