Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition samerep (v1 v2: val) :=
  forall bl: list Memdata.memval,
   Memdata.decode_val Mfloat32 bl = v1 <-> Memdata.decode_val Mint32 bl = v2.

Lemma union_conversion:
forall {CS} (u:ident) sh p (i1 i2: ident) (t1 t2: type),
  match PTree.get u (@cenv_cs CS) with
  | Some {| co_su := Union; 
            co_members := [(i1', t1'); (i2', t2')];
            co_rank := 0;
         |}  => i1'=i1 /\ i2'=i2 /\ t1'=t1 /\ t2'=t2
  | _ => False
  end ->
  i1 <> i2 ->
  forall (x y: val) 
        (v1 v2: reptype (nested_field_type (Tunion u noattr) [])),
  reptype t1 = val ->
  reptype t2 = val ->
  JMeq v1 (@inl val val x) ->
  JMeq v2 (@inr val val y) ->
  samerep x y ->
  @field_at CS sh (Tunion u noattr) [] v1 p =
  @field_at CS sh (Tunion u noattr) [] v2 p.
Proof.
intros.
destruct (cenv_cs ! u) eqn:Heq; try contradiction.
destruct c; try contradiction.
destruct co_su; try contradiction.
destruct co_members as [ | [? ?] ]; try contradiction.
destruct co_members as [ | [? ?] ]; try contradiction.
destruct co_members as [ | [? ?] ]; try contradiction.
destruct co_rank; try contradiction.
destruct H as [? [? [? ?]]]; subst.
match type of Heq with _ = Some ?A => 
  assert (@get_co CS u = A) by (unfold get_co; rewrite Heq; reflexivity)
end.
clear Heq.
unfold field_at. f_equal.
unfold at_offset.
simpl nested_field_offset.
forget (offset_val 0 p) as p'; clear p.
unfold nested_field_type, nested_field_rec.
rewrite !data_at_rec_eq.
rename co_sizeof into sz.
rename co_alignof into aln.
simpl in v1,v2,H3,H4.
assert (H6 := reptype_eq (Tunion u noattr)); simpl in H6.
rewrite H in H6. simpl in H6.
unfold reptype_unionlist in H6.
simpl in H6.
rewrite if_true in H6 by auto.
rewrite if_false in H6 by auto.
rewrite if_true in H6 by auto.
rewrite H1,H2 in H6.
Admitted.

Lemma fabs_float32_lemma:
  forall x: float32,
  exists y: int,
  samerep (Vsingle x) (Vint y) /\
  samerep (Vsingle (Float32.abs x)) (Vint (Int.and y (Int.repr 2147483647))).
Admitted.

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


Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
destruct (fabs_float32_lemma x) as [y [H3 H4]].

pose proof (union_conversion __125 Tsh v_u _f _i tfloat tuint).
simpl in H. spec H; [auto |].
spec H. compute; clear; congruence.

forward.
rewrite (H (Vsingle x) (Vint y) _ _ (eq_refl _) (eq_refl _)
               (JMeq_refl _) (JMeq_refl _) H3).
forward.
forward.
forget (Int.and y (Int.repr 2147483647)) as y'.
forget (Float32.abs x) as x'.

rewrite <- (H (Vsingle x') (Vint y') _ _ (eq_refl _) (eq_refl _)
               (JMeq_refl _) (JMeq_refl _) H4).

forward.
forward.
unfold data_at_.
cancel.
Qed.

End Single.

Module Float.

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
