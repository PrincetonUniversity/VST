Require Import VST.veric.SeparationLogic.
Require Export VST.veric.xexpr_rel.

(*

Inductive rel_r_value' {CS: compspecs} (rho: environ) (phi: rmap): r_value -> val -> Prop :=
 | rel_r_value'_const: forall v,
                 rel_r_value' rho phi (R_const v) v
 | rel_r_value'_tempvar: forall id v,
                 Map.get (te_of rho) id = Some v ->
                 rel_r_value' rho phi (R_tempvar id) v
 | rel_r_value'_addrof: forall a v,
                 rel_l_value' rho phi a v ->
                 rel_r_value' rho phi (R_addrof a) v
 | rel_r_value'_unop: forall a ta v1 v op,
                 rel_r_value' rho phi a v1 ->
                 (forall m, Cop.sem_unary_operation op v1 ta m = Some v) ->
                 rel_r_value' rho phi (R_unop op a ta) v
 | rel_r_value'_binop: forall a1 ta1 a2 ta2 v1 v2 v op,
                 rel_r_value' rho phi a1 v1 ->
                 rel_r_value' rho phi a2 v2 ->
                 (forall m, Cop.sem_binary_operation cenv_cs op v1 ta1 v2 ta2 m = Some v) ->
                 rel_r_value' rho phi (R_binop op a1 ta1 a2 ta2) v
 | rel_r_value'_cast: forall a ta v1 v ty,
                 rel_r_value' rho phi a v1 ->
                 Cop.sem_cast v1 ta ty = Some v ->
                 rel_r_value' rho phi (R_cast a ta ty) v
 | rel_r_value'_byref: forall a v1,
                 rel_l_value' rho phi a v1 ->
                 rel_r_value' rho phi (R_byref a) v1
 | rel_r_value'_load: forall a ty sh v1 v2,
                 rel_l_value' rho phi a v1 ->
                 app_pred ((mapsto sh ty v1 v2) * TT) phi ->
                 v2 <> Vundef ->
                 readable_share sh ->
                 rel_r_value' rho phi (R_load a ty) v2
with rel_l_value' {CS: compspecs} (rho: environ) (phi: rmap): l_value -> val -> Prop :=
 | rel_r_value'_local: forall id ty b,
                 Map.get (ve_of rho) id = Some (b,ty) ->
                 rel_l_value' rho phi (L_var id ty) (Vptr  b Int.zero)
 | rel_r_value'_global: forall id ty b,
                 Map.get (ve_of rho) id = None ->
                 Map.get (ge_of rho) id = Some b ->
                 rel_l_value' rho phi (L_var id ty) (Vptr b Int.zero)
 | rel_l_value'_deref: forall a b z,
                 rel_r_value' rho phi a (Vptr b z) ->
                 rel_l_value' rho phi (L_deref a) (Vptr b z)
 | rel_l_value'_field_struct: forall i a ta b z id co att delta,
                 rel_l_value' rho phi a (Vptr b z) ->
                 ta = Tstruct id att ->
                 cenv_cs ! id = Some co ->
                 field_offset cenv_cs i (co_members co) = Errors.OK delta ->
                 rel_l_value' rho phi (L_field a ta i) (Vptr b (Int.add z (Int.repr delta))).
Inductive l_value : Type :=
  | L_var : ident -> type -> l_value
  | L_deref : r_value -> l_value
  | L_field : l_value -> type -> ident -> l_value
  | L_ilegal : expr -> l_value
with r_value : Type :=
  | R_const : val -> r_value
  | R_tempvar : ident -> r_value
  | R_addrof : l_value -> r_value
  | R_unop : Cop.unary_operation -> r_value -> type -> r_value
  | R_binop : Cop.binary_operation -> r_value -> type -> r_value -> type -> r_value
  | R_cast : r_value -> type -> type -> r_value
  | R_byref : l_value -> r_value
  | R_load : l_value -> type -> r_value
  | R_ilegal : expr -> r_value.


*)

Transparent mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.

Lemma rel_r_value_const: forall {CS: compspecs} v P rho,
  P |-- rel_r_value (R_const v) v rho.
Proof. intros. intros ? ?. constructor. Qed.

Lemma rel_r_value_tempvar: forall {CS: compspecs} id v P rho,
  Map.get (te_of rho) id = Some v ->
  P |-- rel_r_value (R_tempvar id) v rho.
Proof. intros. intros ? ?. constructor; auto. Qed.

Lemma rel_r_value_addrof: forall {CS: compspecs} l v P rho,
  P |-- rel_l_value l v rho ->
  P |-- rel_r_value (R_addrof l) v rho.
Proof. intros. intros ? ?. constructor. apply H; auto. Qed.

Lemma rel_r_value_unop: forall {CS: compspecs} op r t v0 P v rho,
  P |-- rel_r_value r v0 rho ->
  sem_unary_operation op t v0 = Some v ->
  P |-- rel_r_value (R_unop op r t) v rho.
Proof.
  intros.
  intros ? ?.
  econstructor; [apply H; auto |].
  intros.
  destruct op; simpl in H0 |- *.
  + clear - H0.
    unfold Cop.sem_notbool; unfold sem_notbool in H0.
    destruct (Cop.classify_bool t), v0; try solve [simpl in H0 |- *; congruence].
    admit.
  + clear - H0.
    unfold Cop.sem_notint; unfold sem_notint in H0.
    destruct (Cop.classify_notint t), v0; try solve [simpl in H0 |- *; congruence].
  + clear - H0.
    unfold Cop.sem_neg; unfold sem_neg in H0.
    destruct (Cop.classify_neg t), v0; try solve [simpl in H0 |- *; congruence].
  + clear - H0.
    unfold Cop.sem_absfloat; unfold sem_absfloat in H0.
    destruct (Cop.classify_neg t), v0; try solve [simpl in H0 |- *; congruence].
Qed.

(*
Check sem_binary_operation'.
Print typecheck_lvalue.
Print isUnOpResultType.
Print tc_comparable.
Print denote_tc_assert.
Lemma rel_r_value_binop: forall {CS: compspecs} op r1 t1 r2 t2 v1 v2 P v rho vp,
  P |-- rel_r_value r1 v1 rho ->
  P |-- rel_r_value r2 v2 rho ->
  sem_binary_operation' op t1 t2 vp v1 v2 = Some v ->
  P |-- rel_r_value (R_binop op r1 t1 r2 t2) v rho.
Proof.
  intros.
  intros ? ?.
SearchAbout sem_binary_operation'.
Print isBinOpResultType.
  econstructor; [apply H; auto | apply H0; auto |].
  intros.
  destruct op; simpl in H1 |- *.
  + clear - H1.
    unfold Cop.sem_add; unfold sem_add in H1.
    destruct (Cop.classify_add t1 t2), v1 , v2; try solve [simpl in H1 |- *; congruence].
unfold sem_add_default in H1; auto.
    admit.
  + clear - H0.
    unfold Cop.sem_notint; unfold sem_notint in H0.
    destruct (Cop.classify_notint t), v0; try solve [simpl in H0 |- *; congruence].
  + clear - H0.
    unfold Cop.sem_neg; unfold sem_neg in H0.
    destruct (Cop.classify_neg t), v0; try solve [simpl in H0 |- *; congruence].
  + clear - H0.
    unfold Cop.sem_absfloat; unfold sem_absfloat in H0.
    destruct (Cop.classify_neg t), v0; try solve [simpl in H0 |- *; congruence].
Qed.

*)

Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric Bveric.
