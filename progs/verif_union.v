Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import Memdata.

Definition Gprog : funspecs :=
    ltac:(with_library prog (@nil(ident*funspec))).


Definition g_spec :=
 DECLARE _g
 WITH i: Z
 PRE [ size_t]
   PROP() PARAMS(Vptrofs (Ptrofs.repr i)) SEP()
 POST [ size_t ]
   PROP() RETURN (Vptrofs (Ptrofs.repr i)) SEP().

Lemma body_g: semax_body Vprog Gprog f_g g_spec.
Proof.
start_function.
forward.
forward.
forward.
cancel.
Qed.

Lemma decode_float32_int32:
  forall (bl: list memval) (x: float32),
 size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
 decode_val Mfloat32 bl = Vsingle x ->
 decode_val Mint32 bl = Vint (Float32.to_bits x).
Proof.
intros.
unfold decode_val,decode_int,rev_if_be in *.
destruct (proj_bytes bl) eqn:?H.
inv H0.
rewrite Float32.to_of_bits. auto.
inv H0.
Qed.

Lemma NOT_decode_int32_float32:
  Archi.ptr64=false ->
 ~ (forall (bl: list memval) (x: float32),
     size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
     decode_val Mint32 bl = Vint (Float32.to_bits x) ->
     decode_val Mfloat32 bl = Vsingle x).
Proof.
intro Hp.
intro.
set (x := Float32.zero). (* nothing special about zero, any value would do *)
set (i := Float32.to_bits x).
set (bl := [Fragment (Vint i) Q32 3; Fragment (Vint i) Q32 2; Fragment (Vint i) Q32 1; Fragment (Vint i) Q32 0]).
specialize (H bl x).
specialize (H (eq_refl _)).
assert (decode_val Mint32 bl = Vint (Float32.to_bits x)).
unfold decode_val, bl.
rewrite Hp.
simpl.
destruct (Val.eq (Vint i) (Vint i)); [ | congruence].
destruct (quantity_eq Q32 Q32); [ | congruence].
simpl.
reflexivity.
specialize (H H0).
clear - H. subst bl i.
unfold decode_val in H.
simpl in H. inversion H.
Qed.

Lemma decode_float32_iff_int32:
  forall (bl: list Memdata.memval) (x: float32),
 Memdata.size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
 (Memdata.decode_val Mfloat32 bl = Vsingle x <->
   Memdata.decode_val Mint32 bl = Vint (Float32.to_bits x)).
Proof.
Admitted.  (* not provable at present; see https://github.com/AbsInt/CompCert/issues/207
    for a description of how to solve this problem. *)

Definition samerep (ch1 ch2: memory_chunk) (v1 v2: val) :=
  Memdata.size_chunk ch1 = Memdata.size_chunk ch2 /\
  forall bl: list Memdata.memval,
   Memdata.size_chunk ch1 = Z.of_nat (length bl) ->
   (Memdata.decode_val ch1 bl = v1 <-> Memdata.decode_val ch2 bl = v2).

Lemma mapsto_single_int: forall sh v1 v2 p,
  is_single v1 -> is_int I32 Unsigned v2 ->
  samerep Mfloat32 Mint32 v1 v2 ->
  mapsto sh (Tfloat F32 noattr) p v1 = mapsto sh (Tint I32 Unsigned noattr) p v2.
Proof.
  intros.
  subst.
  unfold mapsto.
  simpl. destruct p; auto.
  if_tac.
*
    rewrite (prop_true_andp _ _ H).
    rewrite (prop_true_andp _ _ H0).
    f_equal.
 +
    unfold res_predicates.address_mapsto.
    apply predicates_hered.pred_ext'. extensionality phi.
    simpl. apply exists_ext; intro bl.
    f_equal; f_equal.
    apply and_ext'; auto. intro.
    destruct H1 as [H1' H1].
    specialize (H1 bl).
    f_equal.
    apply prop_ext.
    apply H1. rewrite H3. reflexivity.
 +
    apply pred_ext; Intros; apply exp_left; intro bl; subst; contradiction.
*
    f_equal. f_equal. f_equal.
    unfold tc_val'. apply prop_ext. intuition.
Qed.

Lemma data_at_single_int: forall sh v1 v2 p1 p2,
  is_single v1 -> is_int I32 Unsigned v2 ->
  samerep Mfloat32 Mint32 v1 v2 ->
  readable_share sh ->
  p1 = p2 ->
  data_at sh (Tfloat F32 noattr) v1 p1 = data_at sh (Tint I32 Unsigned noattr) v2 p2.
Proof.
  intros.
  subst.
  apply pred_ext.
  + entailer!.
    erewrite <- mapsto_data_at'; auto.
    erewrite <- mapsto_data_at'; auto.
    - erewrite mapsto_single_int; try apply derives_refl; auto.
    - destruct H3 as [? [? [? [? ?]]]].
      split; [| split; [| split; [| split]]]; auto.
      destruct p2; auto.
      inv H7. econstructor.
      * reflexivity.
      * inv H9.
        exact H10.
  + entailer!.
    erewrite <- mapsto_data_at'; auto.
    erewrite <- mapsto_data_at'; auto.
    - erewrite mapsto_single_int; try apply derives_refl; auto.
    - destruct H3 as [? [? [? [? ?]]]].
      split; [| split; [| split; [| split]]]; auto.
      destruct p2; auto.
      inv H7. econstructor.
      * reflexivity.
      * inv H9.
        exact H10.
Qed.

Lemma float32_to_bits_abs: 
  forall x, Float32.to_bits (Float32.abs x) = Int.and (Float32.to_bits x) (Int.repr (2 ^ 31 - 1)).
Proof.
intros.
Transparent Float32.to_bits.
unfold Float32.to_bits.
Opaque Float32.to_bits.
rewrite and_repr.
f_equal.
Transparent Float32.abs.
unfold Float32.abs.
Opaque Float32.abs.
Admitted.

Lemma fabs_float32_lemma:
  forall x: float32,
  exists y: int,
  samerep Mfloat32 Mint32 (Vsingle x) (Vint y) /\
  samerep Mfloat32 Mint32 (Vsingle (Float32.abs x)) (Vint (Int.and y (Int.repr 2147483647))).
Proof.
intros.
exists (Float32.to_bits x).
split.
*
split; [ reflexivity | ].
intros.
apply decode_float32_iff_int32; auto.
*
split; [ reflexivity | ].
intros.
rewrite <- float32_to_bits_abs.
apply decode_float32_iff_int32; auto.
Qed.

Module Single.

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float32
 PRE [ Tfloat F32 noattr]
   PROP() PARAMS (Vsingle x) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() RETURN (Vsingle (Float32.abs x)) SEP().

Ltac forward_store_union_hack id :=
eapply semax_seq';
[ensure_open_normal_ret_assert;
 hoist_later_in_pre;
 match goal with
  | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e1 ?e2) _ =>
    check_expression_by_value e1;
    let T1 := fresh "T1" in evar (T1: PTree.t val);
    let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
    let G := fresh "GV" in evar (G: option globals);
    let LOCAL2PTREE := fresh "LOCAL2PTREE" in
    assert (local2ptree Q = (T1, T2, nil, G)) as LOCAL2PTREE;
    [subst T1 T2 G; prove_local2ptree |];
 eapply (semax_PTree_field_store_union_hack id);
  [ exact LOCAL2PTREE
  | reflexivity
  | reflexivity
  | reflexivity

  | (solve_msubst_eval_expr                 || fail 1000 "Cannot evaluate right-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)")
  | (solve_msubst_eval_LR                   || fail 1000 "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)")
  | (solve_msubst_efield_denote             || fail 1000 "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)")
  | econstructor
  | solve_field_address_gen
  | reflexivity || fail 1000 "field-path does not end with union field"
  | reflexivity
  | reflexivity || fail 1000 "alternate union field at wrong address"
  | assumption || simpl; match goal with |- ?A => fail 1000 "before this 'forward', assert and prove" A end
  | reflexivity || fail 1000 "alternate field has wrong access mode"
  | reflexivity || fail 1000 "both fields must have numeric type"
  | apply I || match goal with |- ?A => fail 1000 "cannot prove" A end
  | search_field_at_in_SEP (* This line can fail. If it does not, the following should not fail. *)
  | reflexivity
  | (auto                                   || fail 1000 "unexpected failure in store_tac_no_hint.")
  | (reflexivity  || fail 1000 "field_store_union_hack failed in decode_encode_val")
  | convert_stored_value
  | first [apply data_equal_congr; solve_store_rule_evaluation
                                             | fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "unexpected failure in computing stored result"]

  | first [entailer_for_store_tac            | fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "unexpected failure in entailer_for_store_tac"]
  | first [solve_legal_nested_field_in_entailment
                                             | fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "unexpected failure in solve_legal_nested_field_in_entailment"]
  ]
  end
 | unfold replace_nth; abbreviate_semax ].

Lemma union_field_address: forall id,
  tl composites = (Composite id Union ((_f, tfloat) :: (_i, tuint) :: nil) noattr :: nil) ->
 forall p,
  field_address (Tunion id noattr) [UnionField _f] p = field_address (Tunion id noattr) [UnionField _i] p.
Proof.
  intros.
  inversion H.
  assert (field_compatible (Tunion id noattr) [UnionField _f] p 
               <-> field_compatible (Tunion id noattr) [UnionField _i] p).
2: subst id;  unfold field_address; if_tac; if_tac; auto; tauto.
subst id.
  rewrite !field_compatible_cons; simpl.
  unfold in_members; simpl.
  tauto.
Qed.

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
assert_PROP (field_compatible (Tunion __146 noattr) [UnionField _i] v_u) by  entailer!.
forward_store_union_hack _i.
clear H.
forward.
assert_PROP (field_compatible (Tunion __146 noattr) [UnionField _f] v_u) by entailer!.
forward_store_union_hack _f.
forward.
forward.
entailer!.
f_equal.
destruct (fabs_float32_lemma x) as [y [H3 H4]].
unfold_data_at (data_at _ _ _ _).
rewrite field_at_data_at.
erewrite data_at_single_int with (v2:= Vint y);
 [ | apply I | apply I | exact H3 | auto | apply (union_field_address _ (eq_refl _))].
match goal with |- context [Tunion ?structid] =>
 change (Tint I32 Unsigned noattr) with (nested_field_type (Tunion structid noattr) [UnionField _i])
end.
rewrite <- field_at_data_at.
forward.
forward.
rewrite field_at_data_at.
erewrite <- data_at_single_int with (v1:= Vsingle (Float32.abs x));
    [| apply I | apply I | exact H4 | auto | apply (union_field_address _ (eq_refl _))].
match goal with |- context [Tunion ?structid] =>
  change (Tfloat F32 noattr) with (nested_field_type (Tunion structid noattr) [UnionField _f])
end.
rewrite <- field_at_data_at.
forward.
forward.
unfold_data_at (data_at_ _ _ _).
simpl.
entailer!.
Qed.

End Single.

Module Float.

 (* This experiment shows what kind of error message you get
   if you put the wrong LOCAL precondition.
   In fact, Vfloat x is wrong, leading to an unsatisfying precondition,
   it must be Vsingle. *)

Definition fabs_single_spec :=
 DECLARE _fabs_single
 WITH x: float
 PRE [ Tfloat F32 noattr]
   PROP() PARAMS (Vfloat x) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() RETURN (Vfloat (Float.abs x)) SEP().

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
try (start_function; fail 99).
Abort.

End Float.
