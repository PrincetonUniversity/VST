Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import Memdata.

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
 ~ (forall (bl: list memval) (x: float32),
     size_chunk Mfloat32 = Z.of_nat (Datatypes.length bl) ->
     decode_val Mint32 bl = Vint (Float32.to_bits x) ->
     decode_val Mfloat32 bl = Vsingle x).
Proof.
+
intro.
set (x := Float32.zero). (* nothing special about zero, any value would do *)
set (i := Float32.to_bits x).
set (bl := [Fragment (Vint i) Q32 3; Fragment (Vint i) Q32 2; Fragment (Vint i) Q32 1; Fragment (Vint i) Q32 0]).
specialize (H bl x).
specialize (H (eq_refl _)).
assert (decode_val Mint32 bl = Vint (Float32.to_bits x)).
unfold decode_val, bl.
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
    normalize.
    apply pred_ext. normalize. apply exp_left; intro bl. apply exp_right with bl.
    normalize.
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

Lemma float32_to_bits_abs':
 forall x,
  Fappli_IEEE_bits.bits_of_b32 (Fappli_IEEE.Babs 24 128 (fun _ pl => (false,pl)) x) =
   Z.land (Fappli_IEEE_bits.bits_of_b32 x) (2 ^ 31 - 1).
Proof.
intros.
destruct x,b; try reflexivity.
* (* nan sign=true *)
simpl.
destruct n.
unfold Fappli_IEEE_bits.join_bits.
change (0+255) with 255.
admit.
* (* nan sign=false*)
admit.
* (* finite sign=true *)
unfold Fappli_IEEE_bits.bits_of_b32, Fappli_IEEE.Babs, Fappli_IEEE_bits.bits_of_binary_float.
Admitted.

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
unfold Float32.abs_pl.
apply float32_to_bits_abs'.
Qed.

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
 PRE [ _x OF Tfloat F32 noattr]
   PROP() LOCAL(temp _x (Vsingle x)) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() LOCAL (temp ret_temp (Vsingle (Float32.abs x))) SEP().

Definition Gprog : funspecs :=
    ltac:(with_library prog [ fabs_single_spec ]).

Lemma union_field_address: forall id,
  composites = (Composite id Union ((_f, tfloat) :: (_i, tuint) :: nil) noattr :: nil) ->
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
forward.
destruct (fabs_float32_lemma x) as [y [H3 H4]].
unfold_data_at 1%nat.
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
unfold data_at_, field_at_.
unfold_field_at 2%nat.
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
 PRE [ _x OF Tfloat F32 noattr]
   PROP() LOCAL(temp _x (Vfloat x)) SEP()
 POST [ Tfloat F32 noattr ]
   PROP() LOCAL (temp ret_temp (Vfloat (Float.abs x))) SEP().

Definition Gprog : funspecs :=
    ltac:(with_library prog [ fabs_single_spec ]).

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
try (start_function; fail 99).
Abort.

End Float.
