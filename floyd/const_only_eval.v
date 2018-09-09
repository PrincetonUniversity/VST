Require Import VST.floyd.base.
Require Import VST.floyd.val_lemmas.
Require Import VST.floyd.typecheck_lemmas.

Definition const_only_isUnOpResultType {CS: compspecs} op typeof_a valueof_a ty : bool :=
match op with
  | Cop.Onotbool => match typeof_a with
                    | Tint _ _ _
                    | Tlong _ _
                    | Tfloat _ _ => is_int_type ty
                    | Tpointer _ _ =>
                        if Archi.ptr64 
                        then match valueof_a with
                             | Vlong v =>
                                andb (negb (eqb_type (typeof_a) int_or_ptr_type))
                                     (andb (is_int_type ty) (Z.eqb 0 (Int64.unsigned v)))
                             | _ => false
                             end
                        else match valueof_a with
                             | Vint v => 
                                andb (negb (eqb_type typeof_a int_or_ptr_type))
                                     (andb (is_int_type ty) (Z.eqb 0 (Int.unsigned v)))
                             | _ => false
                             end
                    | _ => false
                    end
  | Cop.Onotint => match Cop.classify_notint (typeof_a) with
                   | Cop.notint_default => false
                   | Cop.notint_case_i _ => (is_int32_type ty)
                   | Cop.notint_case_l _ => (is_long_type ty)
                   end
  | Cop.Oneg => match Cop.classify_neg (typeof_a) with
                    | Cop.neg_case_i sg => 
                          andb (is_int32_type ty)
                          match (typeof_a) with
                          | Tint _ Signed _ =>
                            match valueof_a with
                            | Vint v => negb (Z.eqb (Int.signed v) Int.min_signed)
                            | _ => false
                            end
                          | Tlong Signed _ =>
                            match valueof_a with
                            | Vlong v => negb (Z.eqb (Int64.signed v) Int64.min_signed)
                            | _ => false
                            end
                          | _ => true
                          end
                    | Cop.neg_case_f => is_float_type ty
                    | Cop.neg_case_s => is_single_type ty
                    | _ => false
                    end
  | Cop.Oabsfloat =>match Cop.classify_neg (typeof_a) with
                    | Cop.neg_case_i sg => is_float_type ty
                    | Cop.neg_case_l _ => is_float_type ty
                    | Cop.neg_case_f => is_float_type ty
                    | Cop.neg_case_s => is_float_type ty
                    | _ => false
                    end
end.

(* TODO: binarithType would better be bool type *)
Definition const_only_isBinOpResultType {CS: compspecs} op typeof_a1 valueof_a1 typeof_a2 valueof_a2 ty : bool :=
  match op with
  | Cop.Oadd =>
      match Cop.classify_add (typeof_a1) (typeof_a2) with
      | Cop.add_case_pi t _ | Cop.add_case_pl t =>
        andb
          (andb
             (andb (match valueof_a1 with Vptr _ _ => true | _ => false end) (complete_type cenv_cs t))
             (negb (eqb_type (typeof_a1) int_or_ptr_type)))
          (is_pointer_type ty)
    | Cop.add_case_ip _ t | Cop.add_case_lp t =>
        andb
          (andb
             (andb (match valueof_a2 with Vptr _ _ => true | _ => false end) (complete_type cenv_cs t))
             (negb (eqb_type (typeof_a2) int_or_ptr_type)))
          (is_pointer_type ty)
    | Cop.add_default => false
                           (*
        andb (binarithType (typeof a1) (typeof a2) ty deferr reterr)
          (tc_nobinover Z.add a1 a2) *)
      end
  | _ => false (* TODO *)
  end.

Definition const_only_isCastResultType {CS: compspecs} (t1 t2: type) (valueof_a: val)  : bool := false. (* TODO *)

Fixpoint const_only_eval_expr {cs: compspecs} (e: Clight.expr): option val :=
  match e with
  | Econst_int i (Tint I32 _ _) => Some (Vint i)
  | Econst_int _ _ => None
  | Econst_long i ty => None (*Some (Vlong i) *)
  | Econst_float f (Tfloat F64 _) => Some (Vfloat f)
  | Econst_float _ _ => None
  | Econst_single f (Tfloat F32 _) => Some (Vsingle f)
  | Econst_single _ _ => None
  | Etempvar id ty => None
  | Evar _ _ => None
  | Eaddrof a ty => None
  | Eunop op a ty =>
      match const_only_eval_expr a with
      | Some v => if const_only_isUnOpResultType op (typeof a) v ty
                  then Some (eval_unop op (typeof a) v)
                  else None
      | None => None
      end
  | Ebinop op a1 a2 ty =>
      match (const_only_eval_expr a1), (const_only_eval_expr a2) with
      | Some v1, Some v2 =>
          if const_only_isBinOpResultType op (typeof a1) v1 (typeof a2) v2 ty
          then Some (eval_binop op (typeof a1) (typeof a2) v1 v2)
          else None
      | _, _ => None
      end
  | Ecast a ty =>
      match const_only_eval_expr a with
      | Some v => if const_only_isCastResultType (typeof a) ty v
                  then Some (eval_cast (typeof a) ty v)
                  else None
      | None => None
      end
  | Ederef a ty => None
  | Efield a i ty => None
  | Esizeof t t0 =>
    if andb (complete_type cenv_cs t) (eqb_type t0 size_t)
    then Some (Vptrofs (Ptrofs.repr (sizeof t)))
    else None
  | Ealignof t t0 =>
    if andb (complete_type cenv_cs t) (eqb_type t0 size_t)
    then Some (Vptrofs (Ptrofs.repr (alignof t)))
    else None
  end.

Lemma const_only_isUnOpResultType_spec: forall {cs: compspecs} rho u e t P,
  const_only_isUnOpResultType u (typeof e) (eval_expr e rho) t = true ->
  P |-- denote_tc_assert (isUnOpResultType u e t) rho.
Proof.
  intros.
  unfold isUnOpResultType.
  unfold const_only_isUnOpResultType in H.
  destruct u.
  + destruct (typeof e);
      try solve [inv H | rewrite H; exact (@prop_right mpred _ True _ I)].
    rewrite !denote_tc_assert_andp.
    match goal with
    | |- context [denote_tc_assert (tc_test_eq ?a ?b)] =>
      change (denote_tc_assert (tc_test_eq a b)) with (expr2.denote_tc_assert (tc_test_eq a b))
    end.
    rewrite binop_lemmas2.denote_tc_assert_test_eq'.
    simpl expr2.denote_tc_assert.
    unfold_lift. simpl.
    unfold tc_int_or_ptr_type.
    destruct Archi.ptr64 eqn:HH.
    - destruct (eval_expr e rho); try solve [inv H].
      rewrite !andb_true_iff in H.
      destruct H as [? [? ?]].
      rewrite H, H0.
      rewrite Z.eqb_eq in H1.
      apply andp_right; [exact (@prop_right mpred _ True _ I) |].
      apply andp_right; [exact (@prop_right mpred _ True _ I) |].
      simpl.
      rewrite HH.
      change (P |-- (!! (i = Int64.zero)) && (!! (Int64.zero = Int64.zero)))%logic.
      apply andp_right; apply prop_right; auto.
      rewrite <- (Int64.repr_unsigned i), <- H1.
      auto.
    - destruct (eval_expr e rho); try solve [inv H].
      rewrite !andb_true_iff in H.
      destruct H as [? [? ?]].
      rewrite H, H0.
      rewrite Z.eqb_eq in H1.
      apply andp_right; [exact (@prop_right mpred _ True _ I) |].
      apply andp_right; [exact (@prop_right mpred _ True _ I) |].
      simpl.
      rewrite HH.
      change (P |-- (!! (i = Int.zero)) && (!! (Int.zero = Int.zero)))%logic.
      apply andp_right; apply prop_right; auto.
      rewrite <- (Int.repr_unsigned i), <- H1.
      auto.
  + destruct (Cop.classify_notint (typeof e));
      try solve [inv H | rewrite H; exact (@prop_right mpred _ True _ I)].
  + destruct (Cop.classify_neg (typeof e));
      try solve [inv H | rewrite H; exact (@prop_right mpred _ True _ I)].
    rewrite !andb_true_iff in H.
    destruct H.
    rewrite H; simpl.
    destruct (typeof e) as [| ? [|] | [|] | | | | | |];
      try solve [exact (@prop_right mpred _ True _ I)].
    - simpl.
      unfold_lift.
      unfold denote_tc_nosignedover.
      destruct (eval_expr e rho); try solve [inv H0].
      rewrite negb_true_iff in H0.
      rewrite Z.eqb_neq in H0.
      apply prop_right.
      change (Int.signed Int.zero) with 0.
      rep_omega.
    - simpl.
      unfold_lift.
      unfold denote_tc_nosignedover.
      destruct (eval_expr e rho); try solve [inv H0].
      rewrite negb_true_iff in H0.
      rewrite Z.eqb_neq in H0.
      apply prop_right.
      change (Int64.signed Int64.zero) with 0.
      rep_omega.
  + destruct (Cop.classify_neg (typeof e)); try solve [inv H | rewrite H; exact (@prop_right mpred _ True _ I)].
Qed.

Lemma const_only_isBinOpResultType_spec: forall {cs: compspecs} rho b e1 e2 t P,
  const_only_isBinOpResultType b (typeof e1) (eval_expr e1 rho) (typeof e2) (eval_expr e2 rho) t = true ->
  P |-- denote_tc_assert (isBinOpResultType b e1 e2 t) rho.
Proof.
  intros.
  unfold isBinOpResultType.
  unfold const_only_isBinOpResultType in H.
  destruct b.
  + destruct (Cop.classify_add (typeof e1) (typeof e2)).
    - rewrite !denote_tc_assert_andp; simpl.
      unfold_lift.
      unfold tc_int_or_ptr_type, denote_tc_isptr.
      destruct (eval_expr e1 rho); inv H.
      rewrite !andb_true_iff in H1.
      destruct H1 as [[? ?] ?].
      rewrite H, H0, H1.
      simpl.
      repeat apply andp_right; apply prop_right; auto.
    - rewrite !denote_tc_assert_andp; simpl.
      unfold_lift.
      unfold tc_int_or_ptr_type, denote_tc_isptr.
      destruct (eval_expr e1 rho); inv H.
      rewrite !andb_true_iff in H1.
      destruct H1 as [[? ?] ?].
      rewrite H, H0, H1.
      simpl.
      repeat apply andp_right; apply prop_right; auto.
    - rewrite !denote_tc_assert_andp; simpl.
      unfold_lift.
      unfold tc_int_or_ptr_type, denote_tc_isptr.
      destruct (eval_expr e2 rho); inv H.
      rewrite !andb_true_iff in H1.
      destruct H1 as [[? ?] ?].
      rewrite H, H0, H1.
      simpl.
      repeat apply andp_right; apply prop_right; auto.
    - rewrite !denote_tc_assert_andp; simpl.
      unfold_lift.
      unfold tc_int_or_ptr_type, denote_tc_isptr.
      destruct (eval_expr e2 rho); inv H.
      rewrite !andb_true_iff in H1.
      destruct H1 as [[? ?] ?].
      rewrite H, H0, H1.
      simpl.
      repeat apply andp_right; apply prop_right; auto.
    - inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
  + inv H.
Qed.

Lemma const_only_isCastResultType_spec: forall {cs: compspecs} rho e t P,
  const_only_isCastResultType (typeof e) t (eval_expr e rho) = true ->
  P |-- denote_tc_assert (isCastResultType (typeof e) t e) rho.
Proof.
  intros.
  inv H.
Qed.

Lemma const_only_eval_expr_eq: forall {cs: compspecs} rho e v,
  const_only_eval_expr e = Some v ->
  eval_expr e rho = v.  
Proof.
  intros.
  revert v H; induction e; try solve [intros; inv H; auto].
  + intros.
    simpl in *.
    destruct t as [| [| | |] | | | | | | |]; inv H.
    auto.
  + intros.
    simpl in *.
    destruct t as [| | | [|] | | | | |]; inv H.
    auto.
  + intros.
    simpl in *.
    destruct t as [| | | [|] | | | | |]; inv H.
    auto.
  + intros.
    simpl in *.
    unfold option_map in H.
    destruct (const_only_eval_expr e); inv H.
    destruct (const_only_isUnOpResultType u (typeof e) v0 t); inv H1.
    specialize (IHe _ eq_refl).
    unfold_lift.
    rewrite IHe; auto.
  + intros.
    simpl in *.
    unfold option_map in H.
    destruct (const_only_eval_expr e1); inv H.
    destruct (const_only_eval_expr e2); inv H1.
    destruct (const_only_isBinOpResultType b (typeof e1) v0 (typeof e2) v1 t); inv H0.
    specialize (IHe1 _ eq_refl).
    specialize (IHe2 _ eq_refl).
    unfold_lift.
    rewrite IHe1, IHe2; auto.
  + intros.
    simpl in *.
    unfold option_map in H.
    destruct (const_only_eval_expr e); inv H. (*
    specialize (IHe _ eq_refl).
    unfold_lift.
    rewrite IHe; auto.*)
  + intros.
    simpl in *.
    destruct (complete_type cenv_cs t && eqb_type t0 size_t); inv H.
    auto.
  + intros.
    simpl in *.
    destruct (complete_type cenv_cs t && eqb_type t0 size_t); inv H.
    auto.
Qed.

Lemma const_only_eval_expr_tc: forall {cs: compspecs} Delta e v P,
  const_only_eval_expr e = Some v ->
  P |-- tc_expr Delta e.
Proof.
  intros.
  intro rho.
  revert v H; induction e; try solve [intros; inv H].
  + intros.
    inv H.
    destruct t as [| [| | |] | | | | | | |]; inv H1.
    exact (@prop_right mpred _ True _ I).
  + intros.
    inv H.
    destruct t as [| | | [|] | | | | |]; inv H1.
    exact (@prop_right mpred _ True _ I).
  + intros.
    inv H.
    destruct t as [| | | [|] | | | | |]; inv H1.
    exact (@prop_right mpred _ True _ I).
  + intros.
    unfold tc_expr in *.
    simpl in *.
    unfold option_map in H.
    destruct (const_only_eval_expr e) eqn:HH; inv H.
    specialize (IHe _ eq_refl).
    unfold_lift.
    rewrite denote_tc_assert_andp; simpl; apply andp_right; auto.
    apply const_only_isUnOpResultType_spec.
    apply (const_only_eval_expr_eq rho) in HH.
    rewrite HH.
    destruct (const_only_isUnOpResultType u (typeof e) v0 t); inv H1; auto.
  + intros.
    unfold tc_expr in *.
    simpl in *.
    unfold option_map in H.
    destruct (const_only_eval_expr e1) eqn:HH1; inv H.
    destruct (const_only_eval_expr e2) eqn:HH2; inv H1.
    specialize (IHe1 _ eq_refl).
    specialize (IHe2 _ eq_refl).
    unfold_lift.
    rewrite !denote_tc_assert_andp; simpl; repeat apply andp_right; auto.
    apply const_only_isBinOpResultType_spec.
    apply (const_only_eval_expr_eq rho) in HH1.
    apply (const_only_eval_expr_eq rho) in HH2.
    rewrite HH1, HH2.
    destruct (const_only_isBinOpResultType b (typeof e1) v0 (typeof e2) v1 t); inv H0; auto.
  + intros.
    unfold tc_expr in *.
    simpl in *.
    unfold option_map in H.
    destruct (const_only_eval_expr e) eqn:HH; inv H. (*
    specialize (IHe _ eq_refl).
    unfold_lift.
    rewrite denote_tc_assert_andp; simpl; apply andp_right; auto.
    apply const_only_isUnOpResultType_spec.
    apply (const_only_eval_expr_eq rho) in HH. *)
  + intros.
    inv H.
    unfold tc_expr.
    simpl typecheck_expr.
    simpl.
    destruct (complete_type cenv_cs t && eqb_type t0 size_t) eqn:HH; inv H1.
    rewrite andb_true_iff in HH.
    unfold tuint in HH; destruct HH.
    rewrite H, H0.
    exact (@prop_right mpred _ True _ I).
  + intros.
    inv H.
    unfold tc_expr.
    simpl typecheck_expr.
    simpl.
    destruct (complete_type cenv_cs t && eqb_type t0 size_t) eqn:HH; inv H1.
    rewrite andb_true_iff in HH.
    unfold tuint in HH; destruct HH.
    rewrite H, H0.
    exact (@prop_right mpred _ True _ I).
Qed.
