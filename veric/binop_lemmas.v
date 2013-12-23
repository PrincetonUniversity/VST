Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Require Import veric.Cop2.
Import Cop.
 
Lemma typecheck_val_void:
  forall v, typecheck_val v Tvoid = true -> False.
Proof.
destruct v; simpl; congruence.
Qed.

Definition denote_tc_assert' (a: tc_assert) (rho: environ) : Prop.
pose (P := denote_tc_assert a rho).
unfold denote_tc_assert in P.
super_unfold_lift.
destruct a; apply P.
Defined.

Lemma denote_tc_assert'_eq:
  denote_tc_assert' = denote_tc_assert.
Proof.
extensionality a rho.
destruct a; reflexivity.
Qed.

Lemma int_eq_true : forall x y,
true = Int.eq x y -> x = y.
Proof.
intros. assert (X := Int.eq_spec x y). if_tac in X; auto. congruence.
Qed.

Definition check_pp_int' e1 e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp'
                         (tc_orp' (tc_iszero' e1) (tc_iszero' e2))
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.

Definition check_pl_long' e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp'
                         (tc_iszero' e2)
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.


Lemma tc_andp_TT2:  forall e, tc_andp e tc_TT = e. 
Proof. intros; unfold tc_andp.  destruct e; reflexivity. Qed.
 
Lemma tc_andp_TT1:  forall e, tc_andp tc_TT e = e. 
Proof. intros; unfold tc_andp; reflexivity. Qed.

Lemma or_False: forall x, (x \/ False) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma or_True: forall x, (x \/ True) = True.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma True_or: forall x, (True \/ x) = True.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma False_or: forall x, (False \/ x) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma denote_tc_assert_orp: forall x y rho, 
  denote_tc_assert (tc_orp x y) rho = (denote_tc_assert x rho \/ denote_tc_assert y rho).
Proof.
 intros.
 unfold tc_orp.
 destruct x; simpl;
  unfold_lift; simpl; try rewrite True_or; try rewrite False_or; try reflexivity;
  destruct y; simpl; unfold_lift; simpl;
       try rewrite True_or; try rewrite False_or; 
       try rewrite or_True; try rewrite or_False; 
  try reflexivity.
Qed. 

Lemma is_true_true: is_true true = True.
Proof. apply prop_ext; intuition. Qed.
Lemma is_true_false: is_true false = False.
Proof. apply prop_ext; intuition. Qed.


Lemma denote_tc_assert_iszero: forall e rho,
  denote_tc_assert (tc_iszero e) rho = 
  match (eval_expr e rho) with 
  | Vint i => is_true (Int.eq i Int.zero) 
  | Vlong i => is_true (Int.eq (Int.repr (Int64.unsigned i)) Int.zero)
   | _ => False end.
Proof.
 unfold tc_iszero.
 destruct e; simpl; intros; auto;
 unfold_lift; simpl; 
  try (destruct (Int.eq i Int.zero); simpl;  symmetry; try apply is_true_true; try apply is_true_false).
 destruct ( Int.eq (Int.repr (Int64.unsigned i)) Int.zero);
symmetry; try apply is_true_true; try apply is_true_false.
Qed.

Lemma denote_tc_assert_iszero': forall e,
  denote_tc_assert (tc_iszero e) = denote_tc_assert (tc_iszero' e).
Proof.
intros.
extensionality rho.
rewrite denote_tc_assert_iszero.
reflexivity.
Qed.


Lemma denote_tc_assert_andp'': 
  forall a b rho, denote_tc_assert (tc_andp' a b) rho =
             (denote_tc_assert a rho /\ denote_tc_assert b rho).
Proof.
 intros. reflexivity. Qed.

Lemma denote_tc_assert_orp'': 
  forall a b rho, denote_tc_assert (tc_orp' a b) rho =
             (denote_tc_assert a rho \/ denote_tc_assert b rho).
Proof.
 intros. reflexivity. Qed.

Lemma denote_tc_assert_andp: 
  forall a b rho, denote_tc_assert (tc_andp a b) rho =
             (denote_tc_assert a rho /\ denote_tc_assert b rho).
Proof.
 intros. apply prop_ext. rewrite tc_andp_sound.
 simpl; apply iff_refl.
Qed.


Lemma denote_tc_assert_andp': 
  forall a b, denote_tc_assert (tc_andp a b) =
                        denote_tc_assert (tc_andp' a b).
Proof. intros. extensionality rho. apply denote_tc_assert_andp. Qed.

Lemma denote_tc_assert_orp': 
  forall a b, denote_tc_assert (tc_orp a b) =
                        denote_tc_assert (tc_orp' a b).
Proof. intros. extensionality rho. apply denote_tc_assert_orp. Qed.

Hint Rewrite denote_tc_assert_andp' denote_tc_assert_andp''
    denote_tc_assert_orp' denote_tc_assert_orp''
    denote_tc_assert_iszero' : dtca.

Ltac dtca := autorewrite with dtca; auto.

Definition stupid_typeconv ty := 
match ty with
| Tarray t _ a => Tpointer t a
| Tfunction _ _ => Tpointer ty noattr
| _ => ty
end.

Definition classify_sub' ty1 ty2 := 
match stupid_typeconv ty1 with
| Tpointer ty a =>
    match stupid_typeconv ty2 with
    | Tint _ _ _ => sub_case_pi ty a
    | Tlong _ _ => sub_case_pl ty a
    | Tpointer _ _ => sub_case_pp ty
    | _ => sub_default
    end
| _ => sub_default
end.

Lemma classify_sub_eq : classify_sub = classify_sub'.
Proof.
unfold classify_sub, classify_sub'; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Definition classify_cmp' ty1 ty2 := 
  match stupid_typeconv ty1, stupid_typeconv ty2 with 
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ _ _ => cmp_case_pp
  | Tint _ _ _, Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tlong _ _ => cmp_case_pl
  | Tlong _ _ , Tpointer _ _ => cmp_case_lp
  | _, _ => cmp_default
  end.

Lemma classify_cmp_eq: classify_cmp = classify_cmp'.
Proof.
unfold classify_cmp, classify_cmp'; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Definition classify_add' ty1 ty2 := 
 match stupid_typeconv ty1 with
 | Tint _ _ _ =>
    match stupid_typeconv ty2 with
    | Tpointer ty a => add_case_ip ty a
    |  _ => add_default
    end
| Tlong _ _ =>
    match stupid_typeconv ty2 with
    | Tpointer ty a => add_case_lp ty a
    | _ => add_default
    end
| Tpointer ty a =>
    match stupid_typeconv ty2 with
    | Tint _ _ _ => add_case_pi ty a
    | Tlong _ _ => add_case_pl ty a
    | _ => add_default
    end
 | _ => add_default
end.

Lemma classify_add_eq:  classify_add = classify_add'.
Proof.
unfold classify_add; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Definition classify_shift' (ty1: type) (ty2: type) :=
  match stupid_typeconv ty1, stupid_typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | Tint I32 Unsigned _, Tlong _ _ => shift_case_il Unsigned
  | Tint _ _ _, Tlong _ _ => shift_case_il Signed
  | Tlong s _, Tint _ _ _ => shift_case_li s
  | Tlong s _, Tlong _ _ => shift_case_ll s
  | _,_  => shift_default
  end.

Lemma classify_shift_eq:  classify_shift = classify_shift'.
Proof.
unfold classify_shift; extensionality t1 t2.
destruct t1,t2; simpl; auto;
try destruct i,s; auto;
try destruct i0,s0; auto.
Qed.

Lemma den_isBinOpR: forall op a1 a2 ty,
  denote_tc_assert (isBinOpResultType op a1 a2 ty) = 
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in 
denote_tc_assert
match op with
  | Cop.Oadd => match classify_add' (typeof a1) (typeof a2) with 
                    | Cop.add_case_pi _ _ => tc_andp' (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr) 
                    | Cop.add_case_ip _ _ => tc_andp' (tc_isptr a2) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_pl _ _ => tc_andp' (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr) 
                    | Cop.add_case_lp _ _ => tc_andp' (tc_isptr a2) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end
  | Cop.Osub => match classify_sub' (typeof a1) (typeof a2) with 
                    | Cop.sub_case_pi _ _ => tc_andp' (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pl _ _ => tc_andp' (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pp ty2 =>  (*tc_isptr may be redundant here*)
                             tc_andp' (tc_andp' (tc_andp' (tc_andp' (tc_samebase a1 a2)
                             (tc_isptr a1)) (tc_isptr a2)) (tc_bool (is_int_type ty) reterr))
			     (tc_bool (negb (Int.eq (Int.repr (sizeof ty2)) Int.zero)) 
                                      (pp_compare_size_0 ty2) )
                    | Cop.sub_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end 
  | Cop.Omul => binarithType (typeof a1) (typeof a2) ty deferr reterr
  | Cop.Omod => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => 
                           tc_andp' (tc_nonzero a2) 
                           (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Unsigned => 
                           tc_andp' (tc_nonzero a2) 
                           (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp' (tc_andp' (tc_nonzero a2) 
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp' (tc_andp' (tc_nonzero a2) 
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_long_type ty) reterr)
                    | _ => tc_FF deferr
            end
  | Cop.Odiv => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => tc_andp' (tc_nonzero a2) (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Unsigned => tc_andp' (tc_nonzero a2) (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp' (tc_andp' (tc_nonzero a2) (tc_nodivover a1 a2)) 
                                                        (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp' (tc_andp' (tc_nonzero a2) (tc_nodivover a1 a2)) 
                                                        (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_f  =>  tc_bool (is_float_type ty) reterr 
                    | Cop.bin_default => tc_FF deferr
            end
  | Cop.Oshl | Cop.Oshr => match classify_shift' (typeof a1) (typeof a2) with
                    | Cop.shift_case_ii _ =>  tc_andp' (tc_ilt a2 Int.iwordsize) (tc_bool (is_int_type ty) 
                                                                                         reterr)
                    | _ => tc_FF deferr
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor => 
                   match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i _ =>tc_bool (is_int_type ty) reterr
                    | _ => tc_FF deferr
                   end   
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => 
                   match classify_cmp' (typeof a1) (typeof a2) with
                    | Cop.cmp_default => 
                           tc_bool (is_numeric_type (typeof a1) 
                                         && is_numeric_type (typeof a2)
                                          && is_int_type ty)
                                             deferr
		    | Cop.cmp_case_pp => check_pp_int' a1 a2 op ty e
                    | Cop.cmp_case_pl => check_pl_long' a2 op ty e
                    | Cop.cmp_case_lp => check_pl_long' a1 op ty e
                   end
  end.
Proof.
 intros.
 rewrite <- classify_add_eq. rewrite <- classify_sub_eq.
 rewrite <- classify_shift_eq. rewrite <- classify_cmp_eq.
 unfold isBinOpResultType, classify_add, classify_sub, classify_binarith, classify_shift, 
  classify_cmp, check_pp_int, check_pp_int', check_pl_long, check_pl_long', typeconv;
  destruct op; dtca;
 extensionality rho;
 destruct (typeof a1), (typeof a2); dtca;
 try (destruct i; dtca); 
 try (destruct s; dtca);
 try (destruct i0; dtca);
 try (destruct s0; dtca).
Qed.

Lemma denote_tc_assert'_andp'_e:
 forall a b rho, denote_tc_assert' (tc_andp' a b) rho ->
    denote_tc_assert' a rho /\ denote_tc_assert' b rho.
Proof. intros.
 rewrite denote_tc_assert'_eq in *. apply H.
Qed.

Lemma cast_int_long_nonzero:
  forall s i, Int.eq i Int.zero = false -> 
             Int64.eq (cast_int_long s i) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
rewrite Int64.eq_false; auto.
unfold cast_int_long.
contradict H0.
unfold Int64.zero in H0.
destruct s.
assert (Int64.signed (Int64.repr (Int.signed i)) = Int64.signed (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.signed_repr in H.
rewrite Int64.signed_repr in H.
rewrite <- (Int.repr_signed i).
rewrite H. reflexivity.
pose proof (Int64.signed_range Int64.zero).
rewrite Int64.signed_zero in H1.
auto.
pose proof (Int.signed_range i).
clear - H1.
destruct H1.
split.
apply Z.le_trans with Int.min_signed; auto.
compute; congruence.
apply Z.le_trans with Int.max_signed; auto.
compute; congruence.

assert (Int64.unsigned (Int64.repr (Int.unsigned i)) = Int64.unsigned (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.unsigned_repr in H.
rewrite Int64.unsigned_repr in H.
rewrite <- (Int.repr_unsigned i).
rewrite H. reflexivity.
split; compute; congruence. 
pose proof (Int.unsigned_range i).
clear - H1.
destruct H1.
split; auto.
unfold Int64.max_unsigned.
apply Z.le_trans with Int.modulus.
omega.
compute; congruence.
Qed.

Definition typecheck_numeric_val (v: val) (t: type) : Prop :=
 match v,t with
 | Vint _, Tint _ _ _ => True
 | Vlong _, Tlong _ _ => True
 | Vfloat _, Tfloat _ _ => True
 | _, _ => False
 end.



Lemma typecheck_val_sem_cmp:
 forall op v1 t1 v2 t2 i3 s3 a3,
 typecheck_numeric_val v1 t1 ->
 typecheck_numeric_val v2 t2 ->
typecheck_val
  (force_val
     (Cop2.sem_cmp op t1 t2 true2 v1 v2))
  (Tint i3 s3 a3) = true.
Proof.
destruct op; intros;
unfold Cop2.sem_cmp, classify_cmp, typeconv,
  Cop2.sem_binarith, Cop2.sem_cast, classify_cast;
destruct v1; 
  destruct t1 as [ | i1 s1 ? | i1 ? | i1 ? | | | | | | ];
 try contradiction H;
destruct v2; 
  destruct t2 as [ | i2 s2 ? | i2 ? | i2 ? | | | | | | ];
 try contradiction H0;
 try destruct i1; try destruct s1; try destruct i2; try destruct s2;
 simpl; 
 try match goal with |- typecheck_val (Val.of_bool ?A) _ = _ =>
  destruct A; reflexivity
 end. 
Qed.

Lemma typecheck_val_cmp_eqne_ip:
 forall op v1 t1 v2 t0 a0 i2 s0 a1,
 match op with Ceq => True | Cne => True | _ => False end ->
 match v1,t1 with
 | Vint i, Tint _ _ _ => Int.eq i Int.zero = true
 | Vlong i, Tlong _ _ => Int.eq (Int.repr (Int64.unsigned i)) Int.zero = true
 | _, _ => False
 end ->
 typecheck_val v2 (Tpointer t0 a0) = true ->
typecheck_val
  (force_val
     (Cop2.sem_cmp op t1 (Tpointer t0 a0) true2 v1 v2))
  (Tint i2 s0 a1) = true.
Proof.
intros until 1; rename H into CMP; intros;
 destruct op; try contradiction CMP; clear CMP;
 destruct v1, t1; try contradiction H;
 destruct v2; inv H0; try rewrite H2;
 try destruct i0; destruct s; 
unfold Cop2.sem_cmp, classify_cmp, typeconv,
  Cop2.sem_binarith, sem_cast, classify_cast, sem_cmp_pp;
 simpl; try rewrite H;
 try reflexivity;
try  match goal with |- typecheck_val (Val.of_bool ?A) _ = _ =>
  destruct A; reflexivity
 end.  
Qed.

Lemma typecheck_val_cmp_eqne_pi:
 forall op v1 t1 v2 t0 a0 i2 s0 a1,
 match op with Ceq => True | Cne => True | _ => False end ->
 match v1,t1 with
 | Vint i, Tint _ _ _ => Int.eq i Int.zero = true
 | Vlong i, Tlong _ _ => Int.eq (Int.repr (Int64.unsigned i)) Int.zero = true
 | _, _ => False
 end ->
 typecheck_val v2 (Tpointer t0 a0) = true ->
typecheck_val
  (force_val
     (Cop2.sem_cmp op (Tpointer t0 a0) t1 true2 v2 v1))
  (Tint i2 s0 a1) = true.
Proof.
intros until 1; rename H into CMP; intros.
 destruct op; try contradiction CMP; clear CMP;
 destruct v1, t1; try contradiction H;
 destruct v2; inv H0; try rewrite H2;
 try destruct i0; destruct s; 
unfold Cop2.sem_cmp, classify_cmp, typeconv,
  sem_binarith, sem_cast, classify_cast, sem_cmp_pp;
 simpl; try rewrite H;
 try reflexivity;
 match goal with |- typecheck_val (Val.of_bool ?A) _ = _ =>
  destruct A; reflexivity
 end.
Qed.

Ltac sem_cmp_solver t1 t2 := 
match t1 with 
  | Tint ?i ?s _ => destruct i,s
  | Tlong ?s _ => destruct s
  | _ => idtac
  end;
  match t2 with 
  | Tint ?i ?s _ => destruct i,s
  | Tlong ?s _ => destruct s
  | _ => idtac
  end;
  unfold Cop2.sem_cmp, sem_cmp_pp, sem_cmp_pl, sem_cmp_lp; simpl;
 repeat match goal with H: _ = true |- _ =>
                try rewrite H; clear H
            end;
  try reflexivity;
  match goal with 
            |- typecheck_val (Val.of_bool ?A) _ = _ =>
                destruct A; reflexivity
            end.

Lemma typecheck_sem_div_sound:
 forall i i1 s1 a1 i0 i2 s2 a2 i3 s3 a3,
 Int.eq i0 Int.zero = false ->
 Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone = false ->
 typecheck_val
  (force_val (Cop2.sem_div (Tint i1 s1 a1) (Tint i2 s2 a2) (Vint i)  (Vint i0))) (Tint i3 s3 a3) = true.
Proof.
 intros.
 unfold Cop2.sem_div, Cop2.sem_binarith, Cop2.sem_cast, force_val,
  both_int, both_long, both_float;
 simpl;
 destruct i1,s1,i2,s2; simpl; try rewrite H; try rewrite H0; try reflexivity.
Qed.

Lemma typecheck_sem_mod_sound:
 forall i i1 s1 a1 i0 i2 s2 a2 i3 s3 a3,
 Int.eq i0 Int.zero = false ->
 Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone = false ->
 typecheck_val
  (force_val (Cop2.sem_mod (Tint i1 s1 a1) (Tint i2 s2 a2) (Vint i) (Vint i0))) (Tint i3 s3 a3) = true.
Proof.
 intros.
 unfold Cop2.sem_mod, Cop2.sem_binarith, Cop2.sem_cast, force_val,
  both_int, both_long, both_float.
 destruct i1,s1,i2,s2; simpl; try rewrite H; try rewrite H0; reflexivity.
Qed.
(*

Ltac crunch := 
repeat (
 unfold is_true in *; simpl;
 match goal with 
  | H: ?f _ = ?f _ |- _ => inv H
  | |- _ => first [contradiction | discriminate | reflexivity
                         | rewrite or_False in * | rewrite False_or in * | rewrite zeq_true ]
  | H: denote_tc_assert' (tc_bool ?A _) _ |- _ => 
     destruct A eqn:?; try contradiction H; clear H
  | H: denote_tc_assert' (tc_andp' _ _) _ |- _ => 
     apply denote_tc_assert'_andp'_e in H; destruct H
  | H: denote_tc_assert' (tc_orp' _ _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_isptr _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_ilt _ _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_iszero' _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_nonzero _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_nodivover _ _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_samebase _ _) _ |- _ => hnf in H
 | H: denote_tc_iszero _ |- _ => hnf in H
  | H: ?A=true |- _ => rewrite H; simpl
  | H: ?A=false |- _ => rewrite H; simpl
  | H: negb ?A = true |- _ => destruct A eqn:?; inv H; simpl; auto
  | H: if negb ?A then True else False |- _ => 
           destruct A eqn:?; try contradiction H; clear H; simpl; auto 
 | H: denote_tc_assert' (match ?A with _ => _ end) _ |- _ => 
          first [is_var A; destruct A 
                 | let J := fresh in destruct A eqn:J; move J before H]
  | H: match ?A with _ => _ end = _ |- _ => 
          first [is_var A; destruct A 
                 | let J := fresh in destruct A eqn:?; move J before H]
  | H: is_int_type ?t = true |- _ => destruct t; inv H 
  | H: is_long_type ?t = true |- _ => destruct t; inv H 
  | H: is_float_type ?t = true |- _ => destruct t; inv H
  | H: is_pointer_type ?t = true |- _ => destruct t; inv H  
  | H: andb _ _ = true |- _ => apply -> andb_true_iff in H; destruct H
  | H: proj_sumbool (zeq ?b ?b') = true |- _ =>  destruct (zeq b b'); inv H
  | |- typecheck_val (Val.of_bool ?A) _ = _ => destruct A
  end).

Lemma typecheck_binop_sound:
forall op (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho)
   (TV2: typecheck_val (eval_expr e2 rho) (typeof e2) = true)
   (TV1: typecheck_val (eval_expr e1 rho) (typeof e1) = true),
   typecheck_val
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof.
intros; destruct op;
abstract (
rewrite den_isBinOpR in IBR; simpl in IBR;
 let E1 := fresh "E1" in let E2 := fresh "E2" in 
 destruct (typeof e1) as [ | i1 s1 ? | s1 ? | i1 ? | | | | | | ];
 destruct (eval_expr e1 rho) eqn:E1; inv TV1;
 destruct (typeof e2) as [ | i2 s2 ? | s2 ? | i2 ? | | | | | | ];
 try solve [inv IBR];
 destruct (eval_expr e2 rho) eqn:E2; inv TV2;
unfold eval_binop, sem_binary_operation;
unfold classify_cmp',classify_add',classify_sub',classify_shift',stupid_typeconv,
  binarithType, classify_binarith in IBR;
 rewrite <- denote_tc_assert'_eq in IBR;
crunch;
try rewrite E1 in *; 
try rewrite E2 in *; 
simpl in *; crunch;
try match goal with
| |- _ => first [simple apply typecheck_val_sem_cmp; apply I
                         |  simple apply typecheck_sem_div_sound; assumption 
                         |  simple apply typecheck_sem_mod_sound; assumption]
| |- context [sem_add] =>
  unfold sem_add; rewrite classify_add_eq; unfold classify_add', stupid_typeconv; 
  reflexivity
 | |- typecheck_val (force_val ((sem_cmp _ _ ?t1 _ ?t2) _)) _ = true =>
        sem_cmp_solver t1 t2
| |- context [sem_sub] =>
     unfold sem_sub; rewrite classify_sub_eq; unfold classify_sub', stupid_typeconv; 
     try rewrite zeq_true;
     try match goal with H: Int.eq _ Int.zero = false |- _ => rewrite H end;
    reflexivity
 | H: Int.eq ?i0 Int.zero = false |- typecheck_val  (force_val  (_ _ _ (Vint ?i0) _)) _ = true =>
       unfold sem_div, sem_mod, sem_binarith, sem_cast;
       simpl; (rewrite H || rewrite cast_int_long_nonzero by assumption); 
       reflexivity
 | H: Int.ltu _ Int.iwordsize = true |- typecheck_val  (force_val  (_ _ _ (Vint ?i0) _)) _ = true =>
       unfold sem_shl, sem_shr, sem_shift;
     rewrite classify_shift_eq; unfold classify_shift', stupid_typeconv;
  simpl; rewrite H; reflexivity
end).
Qed.
*)

Ltac crunchp := 
repeat (
 unfold is_true in *; simpl;
 match goal with 
  | H: ?f _ = ?f _ |- _ => inv H
  | |- _ => first [contradiction | discriminate | reflexivity
                         | rewrite or_False in * | rewrite False_or in * | rewrite peq_true ]
  | H: denote_tc_assert' (tc_bool ?A _) _ |- _ => 
     destruct A eqn:?; try contradiction H; clear H
  | H: denote_tc_assert' (tc_andp' _ _) _ |- _ => 
     apply denote_tc_assert'_andp'_e in H; destruct H
  | H: denote_tc_assert' (tc_orp' _ _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_isptr _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_ilt _ _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_iszero' _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_nonzero _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_nodivover _ _) _ |- _ => hnf in H
 | H: denote_tc_assert' (tc_samebase _ _) _ |- _ => hnf in H
 | H: denote_tc_iszero _ |- _ => hnf in H
  | H: ?A=true |- _ => rewrite H; simpl
  | H: ?A=false |- _ => rewrite H; simpl
  | H: negb ?A = true |- _ => destruct A eqn:?; inv H; simpl; auto
  | H: if negb ?A then True else False |- _ => 
           destruct A eqn:?; try contradiction H; clear H; simpl; auto 
 | H: denote_tc_assert' (match ?A with _ => _ end) _ |- _ => 
          first [is_var A; destruct A 
                 | let J := fresh in destruct A eqn:J; move J before H]
  | H: match ?A with _ => _ end = _ |- _ => 
          first [is_var A; destruct A 
                 | let J := fresh in destruct A eqn:?; move J before H]
  | H: is_int_type ?t = true |- _ => destruct t; inv H 
  | H: is_long_type ?t = true |- _ => destruct t; inv H 
  | H: is_float_type ?t = true |- _ => destruct t; inv H
  | H: is_pointer_type ?t = true |- _ => destruct t; inv H  
  | H: andb _ _ = true |- _ => apply -> andb_true_iff in H; destruct H
  | H: proj_sumbool (peq ?b ?b') = true |- _ =>  destruct (peq b b'); inv H
  | |- typecheck_val (Val.of_bool ?A) _ = _ => destruct A
  end).

Lemma typecheck_val_of_bool:
 forall b i s a, typecheck_val (Val.of_bool b) (Tint i s a) = true.
Proof. destruct b; reflexivity. Qed.

Lemma typecheck_binop_sound:
forall op (Delta : tycontext) (rho : environ) (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho)
   (TV2: typecheck_val (eval_expr e2 rho) (typeof e2) = true)
   (TV1: typecheck_val (eval_expr e1 rho) (typeof e1) = true),
   typecheck_val
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof.
intros; destruct op;
try
abstract(
rewrite den_isBinOpR in IBR; simpl in IBR;
 let E1 := fresh "E1" in let E2 := fresh "E2" in 
 destruct (typeof e1) as [ | i1 s1 ? | s1 ? | i1 ? | | | | | | ];
 destruct (eval_expr e1 rho) eqn:E1; inv TV1;
 destruct (typeof e2) as [ | i2 s2 ? | s2 ? | i2 ? | | | | | | ];
 try solve [inv IBR];
 destruct (eval_expr e2 rho) eqn:E2; inv TV2;
unfold eval_binop, Cop2.sem_binary_operation', force_val2;
unfold classify_cmp',classify_add',classify_sub',classify_shift',stupid_typeconv,
  binarithType, classify_binarith in IBR;
 rewrite <- denote_tc_assert'_eq in IBR;
crunchp;
try rewrite E1 in *; 
try rewrite E2 in *; 
simpl in *; crunchp;
cbv beta;
first [ apply typecheck_val_sem_cmp; apply I
       |  apply typecheck_sem_div_sound; assumption 
       |  apply typecheck_sem_mod_sound; assumption
       | destruct s1; try destruct s2; simpl; apply typecheck_val_of_bool
       | idtac];
try match goal with
| |- context [Cop2.sem_add] =>
  unfold Cop2.sem_add; rewrite classify_add_eq; unfold classify_add', stupid_typeconv; 
  reflexivity
 | |- typecheck_val (force_val ((Cop2.sem_cmp _ ?t1 ?t2 _ _ _ ))) _ = true =>
        sem_cmp_solver t1 t2
| |- typecheck_val (force_val (sem_cmp_default _ ?t1 ?t2 _ _)) _ = true =>
         sem_cmp_solver t1 t2
| |- context [Cop2.sem_sub] =>
     unfold Cop2.sem_sub, sem_sub_pp; rewrite classify_sub_eq; unfold classify_sub', stupid_typeconv; 
     try rewrite peq_true;
     try match goal with H: Int.eq _ Int.zero = false |- _ => rewrite H end;
    reflexivity
 | H: Int.eq ?i0 Int.zero = false |- typecheck_val  (force_val  (_ _ _ _ (Vint ?i0))) _ = true =>
       unfold Cop2.sem_div, Cop2.sem_mod, Cop2.sem_binarith, Cop2.sem_cast;
       simpl;  unfold both_int,both_long; simpl; ((rewrite H; try rewrite Heqb) || rewrite cast_int_long_nonzero by assumption); 
       reflexivity
 | H: Int.ltu _ Int.iwordsize = true |- typecheck_val  (force_val  (_ _ _ _ _ _ (Vint ?i0))) _ = true =>
       unfold Cop2.sem_shl, Cop2.sem_shr, Cop2.sem_shift;
     rewrite classify_shift_eq; unfold classify_shift', stupid_typeconv;
  simpl; rewrite H; reflexivity
 | H: Int.eq ?i0 Int.zero = false |- typecheck_val  (force_val  (_ _ _ _ (Vint ?i0))) _ = true =>
       unfold Cop2.sem_div, Cop2.sem_mod, Cop2.sem_binarith, Cop2.sem_cast;
       simpl; unfold both_int,both_long; simpl; (rewrite H || rewrite cast_int_long_nonzero by assumption); 
       reflexivity
 | H: Int.ltu _ Int.iwordsize = true |- typecheck_val  (force_val  (_ _ _ _ (Vint ?i0))) _ = true =>
       unfold Cop2.sem_shl, Cop2.sem_shr, Cop2.sem_shift;
     rewrite classify_shift_eq; unfold classify_shift', stupid_typeconv;
  simpl; rewrite H; reflexivity
| |- typecheck_val (force_val ( _ ?t1 ?t2 _ _)) _ = true => sem_cmp_solver t1 t2 
end).
Qed.

