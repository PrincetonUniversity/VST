Require Import VST.floyd.proofauto.
Require Import VST.progs.union.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition samerep (v1 v2: val) :=
  forall bl: list Memdata.memval,
   Memdata.decode_val Mfloat32 bl = v1 <-> Memdata.decode_val Mint32 bl = v2.

Lemma mapsto_single_int: forall sh v1 v2 p,
  is_single v1 -> is_int I32 Unsigned v2 ->
  samerep v1 v2 ->
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
    f_equal. f_equal. f_equal.
    specialize (H1 bl). apply prop_ext. auto.
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
  samerep v1 v2 ->
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
    erewrite mapsto_single_int; auto.
  + entailer!.
    erewrite <- mapsto_data_at'; auto.
    erewrite <- mapsto_data_at'; auto.
    erewrite mapsto_single_int; auto.
Qed.


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

(* This is not well developped or well tested yet. *)
Ltac unfold_field_at' :=
 match goal with
 | |- context [field_at_mark ?cs ?sh ?t ?gfs ?v ?p] =>
     let F := fresh "F" in
       set (F := field_at_mark cs sh t gfs v p);
       change field_at_mark with @field_at in F;
     let V := fresh "V" in set (V:=v) in F;
     let P := fresh "P" in set (P:=p) in F;
     let T := fresh "T" in set (T:=t) in F;
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type T gfs = Tstruct id noattr)
           by (unfold id,T; reflexivity);
     let H := fresh in
     assert (H:= @field_at_Tstruct cs sh T gfs id noattr
                          V V P  (eq_refl _) (JMeq_refl _));
     unfold id in H; clear Heq id;
     fold F in H; clearbody F;
     simpl co_members in H;
     lazy beta iota zeta delta  [nested_sfieldlist_at ] in H;
     change (@field_at cs sh T) with (@field_at cs sh t) in H;
     hnf in T; subst T;
     change v with (protect _ v) in V;
     simpl in H;
     unfold withspacer in H; simpl in H;
     change (protect _ v) with v in V;
     subst V;
     repeat match type of H with
     | context[fst (?A,?B)] => change (fst (A,B)) with A in H
     | context[snd (?A,?B)] => change (snd (A,B)) with B in H
     end;
     subst P;
     subst F;
     cbv beta;
     repeat flatten_sepcon_in_SEP;
     repeat simplify_project_default_val
 | |- context [field_at_mark ?cs ?sh ?t ?gfs ?v ?p] =>
     let F := fresh "F" in
       set (F := field_at_mark cs sh t gfs v p);
       change field_at_mark with @field_at in F;
     let V := fresh "V" in set (V:=v) in F;
     let P := fresh "P" in set (P:=p) in F;
     let T := fresh "T" in set (T:=t) in F;
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type T gfs = Tunion id noattr)
           by (unfold id,T; reflexivity);
     let H := fresh in
     assert (H:= @field_at_Tunion cs sh T gfs id noattr
                          V V P  (eq_refl _) (JMeq_refl _));
     unfold id in H; clear Heq id;
     fold F in H; clearbody F;
     simpl co_members in H;
     lazy beta iota zeta delta  [nested_ufieldlist_at ] in H;
     change (@field_at cs sh T) with (@field_at cs sh t) in H;
     hnf in T; subst T;
     change v with (protect _ v) in V;
     simpl in H;
     unfold withspacer in H; simpl in H;
     change (protect _ v) with v in V;
     subst V;
     repeat match type of H with
     | context[fst (?A,?B)] => change (fst (A,B)) with A in H
     | context[snd (?A,?B)] => change (snd (A,B)) with B in H
     end;
     subst P;
     subst F;
     cbv beta;
     repeat flatten_sepcon_in_SEP;
     repeat simplify_project_default_val
 end.

Ltac unfold_field_at N  :=
  find_field_at N; unfold_field_at'.

Lemma union_field_address___125: forall p,
  field_address (Tunion __125 noattr) [UnionField _f] p = field_address (Tunion __125 noattr) [UnionField _i] p.
Proof.
  intros.
  assert (field_compatible (Tunion __125 noattr) [UnionField _f] p <-> field_compatible (Tunion __125 noattr) [UnionField _i] p); [|unfold field_address; if_tac; if_tac; auto; tauto].
  rewrite !field_compatible_cons; simpl.
  unfold in_members; simpl.
  tauto.
Qed.

Lemma body_fabs_single: semax_body Vprog Gprog f_fabs_single fabs_single_spec.
Proof.
start_function.
forward.
destruct (fabs_float32_lemma x) as [y [H3 H4]].
unfold_field_at 1%nat.
rewrite field_at_data_at.
erewrite data_at_single_int with (v2:= Vint y);
 [ | apply I | apply I | exact H3 | auto | apply union_field_address___125].
change (Tint I32 Unsigned noattr) with (nested_field_type (Tunion __125 noattr) [UnionField _i]).
rewrite <- field_at_data_at.
forward.
forward.
rewrite field_at_data_at.
erewrite <- data_at_single_int with (v1:= Vsingle (Float32.abs x));
    [| apply I | apply I | exact H4 | auto | apply union_field_address___125].
change (Tfloat F32 noattr) with (nested_field_type (Tunion __125 noattr) [UnionField _f]).
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
