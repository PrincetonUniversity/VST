Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.fieldlist.
Local Open Scope logic.

Inductive efield : Type :=
  | eArraySubsc: forall i: expr, efield
  | eStructField: forall i: ident, efield
  | eUnionField: forall i: ident, efield.

Section CENV.

Context {cs: compspecs}.

Fixpoint nested_efield (e: expr) (efs: list efield) (tts: list type) : expr :=
  match efs, tts with
  | nil, _ => e
  | _, nil => e
  | cons ef efs', cons t0 tts' =>
    match ef with
    | eArraySubsc ei => Ederef (Ebinop Cop.Oadd (nested_efield e efs' tts') ei (tptr t0)) t0
    | eStructField i => Efield (nested_efield e efs' tts') i t0
    | eUnionField i => Efield (nested_efield e efs' tts') i t0
    end
  end.

Inductive array_subsc_denote {cs: compspecs}: expr -> Z -> environ -> Prop :=
  | array_subsc_denote_intro_int:
      forall e i rho, Vint (Int.repr i) = eval_expr e rho -> array_subsc_denote e i rho
  | array_subsc_denote_intro_long:
      forall e i rho, Vlong (Int64.repr i) = eval_expr e rho -> array_subsc_denote e i rho.

Inductive efield_denote {cs: compspecs}: list efield -> list gfield -> environ -> Prop :=
  | efield_denote_nil: forall rho, efield_denote nil nil rho
  | efield_denote_ArraySubsc_int: forall ei efs i gfs rho,
       match typeconv (typeof ei) with
       | Tint _ Signed _ => Int.min_signed <= i <= Int.max_signed
       | Tint _ Unsigned _ => 0 <= i <= Int.max_unsigned
       | _ => False
       end ->
      array_subsc_denote ei i rho ->
      efield_denote efs gfs rho ->
      efield_denote (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) rho
  | efield_denote_ArraySubsc: forall ei efs i gfs rho,
      is_ptrofs_type (typeof ei) = true ->
      array_subsc_denote ei i rho ->
      efield_denote efs gfs rho ->
      efield_denote (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) rho
  | efield_denote_StructField: forall i efs gfs rho,
      efield_denote efs gfs rho ->
      efield_denote (eStructField i :: efs) (StructField i :: gfs) rho
  | efield_denote_UnionField: forall i efs gfs rho,
      efield_denote efs gfs rho ->
      efield_denote (eUnionField i :: efs) (UnionField i :: gfs) rho.

Fixpoint typecheck_efield {cs: compspecs} (Delta: tycontext) (efs: list efield) : tc_assert :=
  match efs with
  | nil => tc_TT
  | eArraySubsc ei :: efs' =>
    tc_andp (typecheck_expr Delta ei) (typecheck_efield Delta efs')
  | eStructField i :: efs' =>
    typecheck_efield Delta efs'
  | eUnionField i :: efs' =>
    typecheck_efield Delta efs'
  end.

Definition tc_efield {cs: compspecs} (Delta: tycontext) (efs: list efield) : environ -> mpred := denote_tc_assert (typecheck_efield Delta efs).

Definition typeconv' (ty: type): type :=
match ty with
| Tvoid => remove_attributes ty
| Tint I8 _ _ => Tint I32 Signed noattr
| Tint I16 _ _ => Tint I32 Signed noattr
| Tint I32 _ _ => remove_attributes ty
| Tint IBool _ _ => Tint I32 Signed noattr
| Tlong _ _ => remove_attributes ty
| Tfloat _ _ => remove_attributes ty
| Tpointer _ _ => if eqb_type ty int_or_ptr_type then ty else remove_attributes ty
| Tarray t _ _ => Tpointer t noattr
| Tfunction _ _ _ => Tpointer ty noattr
| Tstruct _ _ => remove_attributes ty
| Tunion _ _ => remove_attributes ty
end.

(* Null Empty Path situation *)
Definition type_almost_match e t lr:=
  match typeof e, t, lr with
  | _, Tarray t1 _ a1, RRRR => eqb_type (typeconv' (typeof e)) (Tpointer t1 noattr)
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

(* TODO: remove almost_match' and use "type_is_by_value" in proof for assistent. *)
(* Empty Path situation *)
Definition type_almost_match' e t lr:=
  match typeof e, t, lr with
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

Fixpoint legal_nested_efield_rec t_root (gfs: list gfield) (tts: list type): bool :=
  match gfs, tts with
  | nil, nil => true
  | nil, _ => false
  | _ , nil => false
  | gf :: gfs0, t0 :: tts0 => (legal_nested_efield_rec t_root gfs0 tts0 && eqb_type (nested_field_type t_root gfs) t0)%bool
  end.

Definition legal_nested_efield t_root e gfs tts lr :=
 (match gfs with
  | nil => type_almost_match' e t_root lr
  | _ => type_almost_match e t_root lr
  end &&
  legal_nested_efield_rec t_root gfs tts)%bool.

Lemma legal_nested_efield_rec_cons: forall t_root gf gfs t tts,
  legal_nested_efield_rec t_root (gf :: gfs) (t :: tts) = true ->
  legal_nested_efield_rec t_root gfs tts = true.
Proof.
  intros.
  simpl in H.
  rewrite andb_true_iff in H.
  tauto.
Qed.

Lemma typeconv_typeconv'_eq: forall t1 t2,
  typeconv' t1 = typeconv' t2 ->
  typeconv t1 = typeconv t2.
Proof.
  intros.
  destruct t1 as [| [| | |] | [|] | [|] | | | | |], t2 as [| [| | |] | [|] | [|] | | | | |]; simpl in *; 
  do 2 try match type of H with context [if ?A then _ else _] => destruct A end; congruence.
Qed.

Lemma tc_efield_ind: forall {cs: compspecs} (Delta: tycontext) (efs: list efield),
  tc_efield Delta efs =
  match efs with
  | nil => TT
  | eArraySubsc ei :: efs' =>
    tc_expr Delta ei && tc_efield Delta efs'
  | eStructField i :: efs' =>
    tc_efield Delta efs'
  | eUnionField i :: efs' =>
    tc_efield Delta efs'
  end.
Proof.
  intros.
  destruct efs; auto.
  destruct e; auto.
  unfold tc_efield.
  simpl typecheck_efield.
  extensionality rho.
  rewrite denote_tc_assert_andp.
  auto.
Qed.

Lemma typeof_nested_efield': forall rho t_root e ef efs gf gfs t tts,
  legal_nested_efield_rec t_root (gf :: gfs) (t :: tts) = true ->
  efield_denote (ef :: efs) (gf :: gfs) rho ->
  nested_field_type t_root (gf :: gfs) = typeof (nested_efield e (ef :: efs) (t :: tts)).
Proof.
  intros.
  simpl in H.
  rewrite andb_true_iff in H; destruct H.
  apply eqb_type_true in H1; subst.
  destruct ef; reflexivity.
Qed.

Lemma typeof_nested_efield: forall rho t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  efield_denote efs gfs rho ->
  nested_field_type t_root gfs = typeof (nested_efield e efs tts).
Proof.
  intros.
  unfold legal_nested_efield in H.
  rewrite andb_true_iff in H.
  destruct H.
  inversion H0; subst; destruct tts;
  try solve [inversion H1 | simpl; auto | destruct e0; simpl; auto].
  + destruct lr; try discriminate.
    apply eqb_type_true in H; subst.
    reflexivity.
  + eapply typeof_nested_efield'; eauto.
  + eapply typeof_nested_efield'; eauto.
  + eapply typeof_nested_efield'; eauto.
  + eapply typeof_nested_efield'; eauto.
Qed.

Lemma offset_val_sem_add_pi: forall ofs t0 si e rho i,
  match si with
  | Signed => Int.min_signed <= i <= Int.max_signed
  | Unsigned => 0 <= i <= Int.max_unsigned
  end ->
   offset_val ofs
     (force_val (Cop.sem_add_ptr_int _ t0 si (eval_expr e rho) (Vint (Int.repr i)))) =
   offset_val ofs
     (offset_val (sizeof t0 * i) (eval_expr e rho)).
Proof.
  intros.
  destruct (eval_expr e rho); try reflexivity.
  rewrite sem_add_pi_ptr; auto.
  apply I.
Qed.

Lemma By_reference_eval_expr: forall Delta e rho,
  access_mode (typeof e) = By_reference ->
  tc_environ Delta rho ->
  tc_lvalue Delta e rho |--
  !! (eval_expr e rho = eval_lvalue e rho).
Proof.
  intros.
  eapply derives_trans. apply typecheck_lvalue_sound; auto.
  normalize.
  destruct e; try contradiction; simpl in *;
  reflexivity.
Qed.

Lemma By_reference_tc_expr: forall Delta e rho,
  access_mode (typeof e) = By_reference ->
  tc_environ Delta rho ->
  tc_lvalue Delta e rho |--  tc_expr Delta e rho.
Proof.
  intros.
  unfold tc_lvalue, tc_expr.
  destruct e; simpl in *; try apply @FF_left; rewrite H; auto.
Qed.

Definition LR_of_type (t: type) :=
  match t with
  | Tarray _ _ _ => RRRR
  | _ => LLLL
  end.

Lemma legal_nested_efield_weaken: forall t_root e gfs tts,
  legal_nested_efield t_root e gfs tts (LR_of_type t_root) = true ->
  legal_nested_efield_rec t_root gfs tts = true /\
  type_almost_match e t_root (LR_of_type t_root) = true.
Proof.
  intros.
  unfold legal_nested_efield in H.
  rewrite andb_true_iff in H.
  split; [tauto |].
  destruct gfs; [| tauto].
  destruct H as [? _].
  unfold type_almost_match' in H.
  unfold type_almost_match.
  destruct (LR_of_type t_root), t_root, (typeof e); simpl in H |- *;
  try inv H; auto.
Qed.

Lemma weakened_legal_nested_efield_spec: forall t_root e gfs efs tts rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  efield_denote efs gfs rho ->
  typeconv' (nested_field_type t_root gfs) = typeconv' (typeof (nested_efield e efs tts)).
Proof.
  intros.
  inversion H1; subst; destruct tts; try solve [inv H].
  + rewrite nested_field_type_ind.
    simpl typeof.
    unfold type_almost_match in H0.
    destruct (LR_of_type t_root), t_root, (typeof e); try solve [inv H0]; auto;
    try (apply eqb_type_spec in H0; rewrite H0; auto).
  + f_equal.
    eapply typeof_nested_efield'; eauto.
  + f_equal.
    eapply typeof_nested_efield'; eauto.
  + f_equal.
    eapply typeof_nested_efield'; eauto.
  + f_equal.
    eapply typeof_nested_efield'; eauto.
Qed.


Lemma classify_add_typeconv: forall t n a ty,
  typeconv (Tarray t n a) = typeconv ty ->
  Cop.classify_add ty = Cop.classify_add (Tpointer t a).
Proof.
intros.
simpl in H.
extensionality t2.
destruct ty; inv H.
destruct i; inv H1.
all: simpl; destruct (typeconv t2); auto.
Qed.

(*
Lemma classify_add_add_case_pi: forall ei ty t n a si,
  match typeof ei with Tint _ si' _ => si=si' | _ => False end ->
  typeconv (Tarray t n a) = typeconv ty ->
  Cop.classify_add ty (typeof ei) = Cop.add_case_pi t si.
Proof.
  intros.
  destruct (typeof ei) eqn:?; inv H.
  simpl in *. rewrite <- H0.
  destruct i;auto.
  subst.
  simpl.
  rewrite <- H0; clear H0.
  simpl.
  destruct i; try reflexivity.
Qed.
*)

Lemma isBinOpResultType_add_ptr_ptrofs: forall e t n a t0 ei,
  is_ptrofs_type (typeof ei) = true ->
  typeconv (Tarray t0 n a) = typeconv (typeof e) ->
  complete_legal_cosu_type t0 = true ->
  eqb_type (typeof e) int_or_ptr_type = false ->
  isBinOpResultType Cop.Oadd e ei (tptr t) = tc_isptr e.
Proof.
  intros.
  unfold isBinOpResultType.
  rewrite (classify_add_typeconv _ _ _ _ H0).
  destruct (typeof ei); inv H.
(*  erewrite classify_add_add_case_pi by eauto. *)
  apply complete_legal_cosu_type_complete_type in H1.
  simpl.
  try destruct i; rewrite H1; simpl tc_bool; cbv iota;
  rewrite andb_false_r; simpl; rewrite tc_andp_TT2;
  unfold tc_int_or_ptr_type; rewrite H2; simpl; auto.
Qed.

Lemma isBinOpResultType_add_ptr: forall e t n a t0 ei,
  is_int_type (typeof ei) = true ->
  typeconv (Tarray t0 n a) = typeconv (typeof e) ->
  complete_legal_cosu_type t0 = true ->
  eqb_type (typeof e) int_or_ptr_type = false ->
  isBinOpResultType Cop.Oadd e ei (tptr t) = tc_isptr e.
Proof.
  intros.
  unfold isBinOpResultType.
  rewrite (classify_add_typeconv _ _ _ _ H0).
  destruct (typeof ei); inv H.
(*  erewrite classify_add_add_case_pi by eauto. *)
  apply complete_legal_cosu_type_complete_type in H1.
  simpl.
  destruct i; rewrite H1; simpl tc_bool; cbv iota;
  rewrite andb_false_r; simpl; rewrite tc_andp_TT2;
  unfold tc_int_or_ptr_type; rewrite H2; simpl; auto.
Qed.

Definition add_case_pptrofs t si :=
  if Archi.ptr64 then Cop.add_case_pl t else Cop.add_case_pi t si.

Lemma array_op_facts_ptrofs: forall ei rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  is_ptrofs_type (typeof ei) = true ->
  nested_field_type t_root gfs = Tarray t n a ->
  field_compatible t_root gfs p ->
  efield_denote efs gfs rho ->
  (exists si, Cop.classify_add (typeof (nested_efield e efs tts)) (typeof ei) = add_case_pptrofs t si) /\
  isBinOpResultType Cop.Oadd (nested_efield e efs tts) ei (tptr t0) = tc_isptr (nested_efield e efs tts).
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H4).
  rewrite H2 in H5.
  split.
  +
    erewrite classify_add_typeconv
         by (apply typeconv_typeconv'_eq; eassumption).
   destruct (typeof ei); inv H1.
   try (exists Unsigned; reflexivity);  (* Archi.ptr64 = true *)
   destruct i; simpl; eexists; reflexivity. (* Archi.ptr64 = false *)
  + eapply isBinOpResultType_add_ptr_ptrofs; [auto | apply typeconv_typeconv'_eq; eassumption | |].
    - destruct H3 as [_ [? [_ [_ ?]]]].
      eapply nested_field_type_complete_legal_cosu_type with (gfs0 := gfs) in H3; auto.
      rewrite H2 in H3.
      exact H3.
    - destruct (typeof (nested_efield e efs tts)); try solve [inv H5];
      apply eqb_type_false; try (unfold int_or_ptr_type; congruence).
      Opaque eqb_type. simpl in H5. Transparent eqb_type.
      destruct (eqb_type (Tpointer t1 a0) int_or_ptr_type) eqn:?H.
      * apply eqb_type_true in H6.
        unfold int_or_ptr_type in *; inv H5; inv H6.
      * apply eqb_type_false in H6; auto.
Qed.

Lemma array_op_facts: forall ei rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  is_int_type (typeof ei) = true ->
  nested_field_type t_root gfs = Tarray t n a ->
  field_compatible t_root gfs p ->
  efield_denote efs gfs rho ->
  (exists si, Cop.classify_add (typeof (nested_efield e efs tts)) (typeof ei) = Cop.add_case_pi t si) /\
  isBinOpResultType Cop.Oadd (nested_efield e efs tts) ei (tptr t0) = tc_isptr (nested_efield e efs tts).
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H4).
  rewrite H2 in H5.
  split.
  +
    erewrite classify_add_typeconv
         by (apply typeconv_typeconv'_eq; eassumption).
   destruct (typeof ei); inv H1.
   destruct i; simpl; eexists; reflexivity.
  + eapply isBinOpResultType_add_ptr; [auto | apply typeconv_typeconv'_eq; eassumption | |].
    - destruct H3 as [_ [? [_ [_ ?]]]].
      eapply nested_field_type_complete_legal_cosu_type with (gfs0 := gfs) in H3; auto.
      rewrite H2 in H3.
      exact H3.
    - destruct (typeof (nested_efield e efs tts)); try solve [inv H5];
      apply eqb_type_false; try (unfold int_or_ptr_type; congruence).
      Opaque eqb_type. simpl in H5. Transparent eqb_type.
      destruct (eqb_type (Tpointer t1 a0) int_or_ptr_type) eqn:?H.
      * apply eqb_type_true in H6.
        unfold int_or_ptr_type in *; inv H5; inv H6.
      * apply eqb_type_false in H6; auto.
Qed.


Lemma Ptrofs_repr_Int_signed_special:
  Archi.ptr64=false -> forall i, Ptrofs.repr (Int.signed (Int.repr i)) = Ptrofs.repr i.
Proof.
intros.
apply Ptrofs.eqm_samerepr.
unfold Ptrofs.eqm.
rewrite (Ptrofs.modulus_eq32 H).
change (Int.eqmod Int.modulus (Int.signed (Int.repr i)) i).
rewrite Int.signed_repr_eq.
if_tac.
apply Int.eqmod_sym.
apply Int.eqmod_mod.
computable.
apply Int.eqmod_sym.
eapply Int.eqmod_trans.
apply Int.eqmod_mod.
computable.
rewrite <- (Z.sub_0_r (i mod Int.modulus)) at 1.
apply Int.eqmod_sub.
apply Int.eqmod_refl.
hnf. exists (-1). omega.
Qed. 

Lemma Ptrofs_repr_Int_unsigned_special:
  Archi.ptr64=false -> forall i, Ptrofs.repr (Int.unsigned (Int.repr i)) = Ptrofs.repr i.
Proof.
intros.
pose proof (Ptrofs.agree32_repr H i).
hnf in H0.
rewrite <- H0.
apply Ptrofs.repr_unsigned.
Qed.

Lemma Ptrofs_repr_Int64_unsigned_special:
  Archi.ptr64=true -> forall i, Ptrofs.repr (Int64.unsigned (Int64.repr i)) = Ptrofs.repr i.
Proof.
intros.
pose proof (Ptrofs.agree64_repr H i).
hnf in H0.
rewrite <- H0.
apply Ptrofs.repr_unsigned.
Qed.
(*
Lemma Archi_ptr64_DEPENDENCY: Archi.ptr64=false.
Proof. reflexivity. Qed.
*)

Definition sem_add_ptr_ptrofs t si :=
 if Archi.ptr64 then sem_add_ptr_long t else sem_add_ptr_int t si.

Lemma sem_add_pptrofs_ptr_special:
   forall t si p i,
    isptr p ->
    sem_add_ptr_ptrofs t si p (Vptrofs (Ptrofs.repr i)) = Some (offset_val (sizeof t * i) p).
Proof.
  intros.
  unfold sem_add_ptr_ptrofs, sem_add_ptr_int, sem_add_ptr_long.
  destruct p; try contradiction.
  unfold offset_val, Cop.sem_add_ptr_long, Cop.sem_add_ptr_int.
  unfold Vptrofs, Cop.ptrofs_of_int, Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int.
  destruct Archi.ptr64 eqn:Hp.
  f_equal. f_equal. f_equal. rewrite Ptrofs.of_int64_to_int64 by auto.
  rewrite <- ptrofs_mul_repr;  f_equal.
  f_equal. f_equal. f_equal.
  destruct si.
  rewrite <- ptrofs_mul_repr;  f_equal.
  rewrite ptrofs_to_int_repr.
  rewrite Ptrofs_repr_Int_signed_special by auto. auto.
  rewrite <- ptrofs_mul_repr;  f_equal.
  rewrite ptrofs_to_int_repr.
  rewrite Ptrofs_repr_Int_unsigned_special by auto. auto.
Qed.

Lemma sem_add_pi_ptr_special:
   forall t p i si,
    isptr p ->
   match si with
   | Signed => Int.min_signed <= i <= Int.max_signed
   | Unsigned => 0 <= i <= Int.max_unsigned
   end ->
    sem_add_ptr_int t si p (Vint (Int.repr i)) = Some (offset_val (sizeof t * i) p).
Proof.
  intros.
 unfold sem_add_ptr_int.
  destruct p; try contradiction.
  unfold offset_val, Cop.sem_add_ptr_int.
  unfold Cop.ptrofs_of_int, Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int.
  f_equal. f_equal. f_equal.
  destruct si; rewrite <- ptrofs_mul_repr;  f_equal.
  rewrite Int.signed_repr; auto.
  rewrite Int.unsigned_repr; auto.
Qed.

Lemma sem_add_pi_ptr_special':
   Archi.ptr64 = false ->
   forall t p i si,
    isptr p ->
    sem_add_ptr_int t si p (Vint (Int.repr i)) = Some (offset_val (sizeof t * i) p).
Proof.
  intros Hp.
  intros.
 unfold sem_add_ptr_int.
  destruct p; try contradiction.
  unfold offset_val, Cop.sem_add_ptr_int.
  unfold Cop.ptrofs_of_int, Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int.
  f_equal. f_equal. f_equal.
  destruct si; rewrite <- ptrofs_mul_repr;  f_equal.
  apply (Ptrofs_repr_Int_signed_special Hp).
  apply (Ptrofs_repr_Int_unsigned_special Hp).
Qed.

Lemma sem_add_pl_ptr_special':
   Archi.ptr64 = true ->
   forall t p i,
    isptr p ->
    sem_add_ptr_long t p (Vlong (Int64.repr i)) = Some (offset_val (sizeof t * i) p).
Proof.
  intros Hp.
  intros.
 unfold sem_add_ptr_long.
  destruct p; try contradiction.
  unfold offset_val, Cop.sem_add_ptr_long.
  f_equal. f_equal. f_equal.
  rewrite (Ptrofs.agree64_of_int_eq (Ptrofs.repr i))
    by (apply Ptrofs.agree64_repr; auto).
  rewrite ptrofs_mul_repr. auto.
Qed.

Lemma array_ind_step_ptrofs: forall Delta ei i rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  is_ptrofs_type (typeof ei) = true ->
  array_subsc_denote ei i rho ->
  nested_field_type t_root gfs = Tarray t0 n a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs p = eval_LR (nested_efield e efs tts) (LR_of_type (Tarray t0 n a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tarray t0 n a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eArraySubsc ei :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (ArraySubsc i))
          (field_address t_root gfs p) =
          eval_lvalue (nested_efield e (eArraySubsc ei :: efs) (t :: tts)) rho) &&
          tc_lvalue Delta (nested_efield e (eArraySubsc ei :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH ? ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  destruct (array_op_facts_ptrofs _ _ _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE FIELD_COMPATIBLE EFIELD_DENOTE) as [CLASSIFY_ADD ISBINOP].
  pose proof field_address_isptr _ _ _ FIELD_COMPATIBLE as ISPTR.
  rewrite tc_efield_ind; simpl.
  rewrite andp_comm, andp_assoc.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite andp_comm; exact IH] | ].
  rewrite (add_andp _ _ (typecheck_expr_sound _ _ _ TC_ENVIRON)).
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  +
     assert (H3: Vptrofs (Ptrofs.repr i) = eval_expr ei rho). {
       clear - H1 H0 H.
       unfold is_ptrofs_type, Vptrofs in *.
       destruct Archi.ptr64 eqn:Hp.
       destruct (typeof ei); inv H.
       inv H0. rewrite <- H in H1; inv H1.
       rewrite <- H. f_equal.  apply Ptrofs.agree64_to_int_eq.
       apply Ptrofs.agree64_repr; auto.
       destruct (typeof ei); inv H. destruct i0; inv H3.
       inv H0. 2: rewrite <- H in H1; inv H1.
       rewrite <- H. f_equal. apply ptrofs_to_int_repr.
    }
    rewrite <- H3.
    unfold force_val2, force_val.
    unfold sem_add.
    destruct CLASSIFY_ADD as [si CLASSIFY_ADD].
    rewrite CLASSIFY_ADD.
    match goal with |- _ = match ?A _ _ with Some _ => _ | None => _ end => 
       change A with (sem_add_ptr_ptrofs t0 si)
    end.
    rewrite sem_add_pptrofs_ptr_special.
    2: simpl in H2; rewrite <- H2; auto.
    unfold gfield_offset; rewrite NESTED_FIELD_TYPE, H2.
    reflexivity.
  + unfold tc_lvalue.
    Opaque isBinOpResultType. simpl. Transparent isBinOpResultType.
    rewrite ISBINOP.
    normalize.
    rewrite !denote_tc_assert_andp; simpl.
    repeat apply andp_right.
    - apply prop_right.
      simpl in H2; rewrite <- H2; auto.
    - solve_andp.
    - solve_andp.
    - rewrite andb_false_r. simpl. apply prop_right; auto.
    - apply prop_right.
      simpl; unfold_lift.
      rewrite <- H3.
      normalize.
Qed.

Lemma array_ind_step: forall Delta ei i rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
(*  is_int_type (typeof ei) = true -> *)
   match typeconv (typeof ei) with
   | Tint _ Signed _ => Int.min_signed <= i <= Int.max_signed
   | Tint _ Unsigned _ => 0 <= i <= Int.max_unsigned
   | _ => False
   end ->
  array_subsc_denote ei i rho ->
  nested_field_type t_root gfs = Tarray t0 n a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs p = eval_LR (nested_efield e efs tts) (LR_of_type (Tarray t0 n a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tarray t0 n a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eArraySubsc ei :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (ArraySubsc i))
          (field_address t_root gfs p) =
          eval_lvalue (nested_efield e (eArraySubsc ei :: efs) (t :: tts)) rho) &&
          tc_lvalue Delta (nested_efield e (eArraySubsc ei :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH H ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  rename H into H'.
  assert (H: is_int_type (typeof ei) = true) 
     by (clear - H'; destruct (typeof ei) as [| | | [|] | | | | |]; try contradiction; auto).
  destruct (array_op_facts _ _ _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE FIELD_COMPATIBLE EFIELD_DENOTE) as [CLASSIFY_ADD ISBINOP].
  pose proof field_address_isptr _ _ _ FIELD_COMPATIBLE as ISPTR.
  rewrite tc_efield_ind; simpl.
  rewrite andp_comm, andp_assoc.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | rewrite andp_comm; exact IH] | ].
  rewrite (add_andp _ _ (typecheck_expr_sound _ _ _ TC_ENVIRON)).
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  + 
     assert (H3: Vint (Int.repr i) = eval_expr ei rho). {
       clear - H1 H0 H.
       inv H0; auto.
       destruct (typeof ei); inv H. rewrite <- H2 in H1.
       destruct i0,s; contradiction.
    }
    rewrite <- H3.
    unfold force_val2, force_val.
    unfold sem_add.
    destruct CLASSIFY_ADD as [si CLASSIFY_ADD].
    rewrite CLASSIFY_ADD.
    rewrite sem_add_pi_ptr_special.
    2: simpl in H2; rewrite <- H2; auto.
    unfold gfield_offset; rewrite NESTED_FIELD_TYPE, H2.
    reflexivity.
    clear - H' CLASSIFY_ADD.
    destruct  (typeof (nested_efield e efs tts)) as  [ | [ | | | ] [ | ]| [ | ] | [ | ] | | | | | ], 
                 (typeof ei) as  [ | [ | | | ] [ | ]| [ | ] | [ | ] | | | | | ]; inv CLASSIFY_ADD; try contradiction; auto.
  + unfold tc_lvalue.
    Opaque isBinOpResultType. simpl. Transparent isBinOpResultType.
    rewrite ISBINOP.
    normalize.
    rewrite !denote_tc_assert_andp; simpl.
    repeat apply andp_right.
    - apply prop_right.
      simpl in H2; rewrite <- H2; auto.
    - solve_andp.
    - solve_andp.
    - rewrite andb_false_r. simpl. apply prop_right; auto.
    - apply prop_right.
      simpl; unfold_lift.
      rewrite <- H3.
      normalize.
Qed.

Lemma in_members_Ctypes_offset: forall i m e, in_members i m -> Ctypes.field_offset cenv_cs i m = Errors.Error e -> False.
Proof.
  intros.
  unfold Ctypes.field_offset in H0.
  revert H0; generalize 0; induction m as [| [? ?] ?]; intros.
  + inv H.
  + simpl in H0.
    if_tac in H0; inv H0.
    spec IHm.
    - destruct H; [simpl in H; congruence | auto].
    - apply IHm in H3; auto.
Qed.

Lemma struct_op_facts: forall Delta t_root e gfs efs tts i a i0 t rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i0 (co_members (get_co i)) ->
  nested_field_type t_root gfs = Tstruct i a ->
  efield_denote efs gfs rho ->
  tc_lvalue Delta (nested_efield e efs tts) rho =
  tc_lvalue Delta (nested_efield e (eStructField i0 :: efs) (t :: tts)) rho /\
  eval_field (typeof (nested_efield e efs tts)) i0 =
      offset_val (field_offset cenv_cs i0 (co_members (get_co i))).
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H3).
  rewrite H2 in H4; simpl in H4.
  destruct (typeof (nested_efield e efs tts)) eqn:?H; inv H4.
  1: destruct i1; inv H7.
  1: match type of H7 with context [if ?A then _ else _] => destruct A end; inv H7.
  unfold tc_lvalue, eval_field.
  simpl.
  rewrite H5.
  unfold field_offset, fieldlist.field_offset.
  unfold get_co in *.
  destruct (cenv_cs ! i1); [| inv H1].
  destruct (Ctypes.field_offset cenv_cs i0 (co_members c)) eqn:?H.
  + split; auto.
    rewrite denote_tc_assert_andp; simpl.
    apply add_andp, prop_right; auto.
  + exfalso.
    pose proof in_members_Ctypes_offset i0 (co_members c) e0; auto.
Qed.

Lemma struct_ind_step: forall Delta t_root e gfs efs tts i a i0 t rho p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i (co_members (get_co i0)) ->
  nested_field_type t_root gfs = Tstruct i0 a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho) =
          eval_LR (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eStructField i :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (StructField i))
            (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho)) =
          eval_lvalue (nested_efield e (eStructField i :: efs) (t :: tts)) rho) &&
      tc_lvalue Delta (nested_efield e (eStructField i :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  destruct (struct_op_facts Delta _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE EFIELD_DENOTE) as [TC EVAL].
  rewrite tc_efield_ind; simpl.
  eapply derives_trans; [exact IH | ].
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  + rewrite EVAL, H0, NESTED_FIELD_TYPE.
    reflexivity.
  + simpl in TC; rewrite <- TC.
      apply derives_refl.
Qed.

Lemma union_op_facts: forall Delta t_root e gfs efs tts i a i0 t rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i0 (co_members (get_co i)) ->
  nested_field_type t_root gfs = Tunion i a ->
  efield_denote efs gfs rho ->
  tc_lvalue Delta (nested_efield e efs tts) rho =
  tc_lvalue Delta (nested_efield e (eUnionField i0 :: efs) (t :: tts)) rho /\
  eval_field (typeof (nested_efield e efs tts)) i0 = offset_val 0.
Proof.
  intros.
  pose proof (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0 H3).
  rewrite H2 in H4; simpl in H4.
  destruct (typeof (nested_efield e efs tts)) eqn:?H; inv H4.
  1: destruct i1; inv H7.
  1: match type of H7 with context [if ?A then _ else _] => destruct A end; inv H7.
  unfold tc_lvalue, eval_field.
  simpl.
  rewrite H5.
  unfold get_co in *.
  destruct (cenv_cs ! i1); [| inv H1].
  split; [| normalize; auto].
  rewrite denote_tc_assert_andp; simpl.
  apply add_andp, prop_right; auto.
Qed.

Lemma union_ind_step: forall Delta t_root e gfs efs tts i a i0 t rho p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  in_members i (co_members (get_co i0)) ->
  nested_field_type t_root gfs = Tunion i0 a ->
  tc_environ Delta rho ->
  efield_denote efs gfs rho ->
  field_compatible t_root gfs p ->
  tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho
  |-- !! (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho) =
          eval_LR (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho) &&
          tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (Tstruct i0 a)) rho ->
  tc_LR_strong Delta e (LR_of_type t_root) rho &&
  tc_efield Delta (eUnionField i :: efs) rho
  |-- !! (offset_val (gfield_offset (nested_field_type t_root gfs) (UnionField i))
            (field_address t_root gfs (eval_LR e (LR_of_type t_root) rho)) =
          eval_lvalue (nested_efield e (eUnionField i :: efs) (t :: tts)) rho) &&
      tc_lvalue Delta (nested_efield e (eUnionField i :: efs) (t :: tts)) rho.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?
         LEGAL_NESTED_EFIELD_REC TYPE_MATCH ? NESTED_FIELD_TYPE TC_ENVIRON EFIELD_DENOTE FIELD_COMPATIBLE IH.
  destruct (union_op_facts Delta _ _ _ _ _ _ _ _ t _ LEGAL_NESTED_EFIELD_REC TYPE_MATCH H NESTED_FIELD_TYPE EFIELD_DENOTE) as [TC EVAL].
  rewrite tc_efield_ind; simpl.
  eapply derives_trans; [exact IH | ].
  unfold_lift.
  normalize.
  apply andp_right1; [apply prop_right | normalize].
  + rewrite EVAL, H0, NESTED_FIELD_TYPE.
    reflexivity.
  + simpl in TC; rewrite <- TC.
      apply derives_refl.
Qed.

Definition lvalue_LR_of_type: forall Delta rho P p t e,
  t = typeof e ->
  tc_environ Delta rho ->
  P |-- !! (p = eval_lvalue e rho) && tc_lvalue Delta e rho ->
  P |-- !! (p = eval_LR e (LR_of_type t) rho) && tc_LR_strong Delta e (LR_of_type t) rho.
Proof.
  intros.
  destruct (LR_of_type t) eqn:?H.
  + exact H1.
  + rewrite (add_andp _ _ H1); clear H1.
    simpl; normalize.
    apply andp_left2.
    unfold LR_of_type in H2.
    subst.
    destruct (typeof e) eqn:?H; inv H2.
    apply andp_right.
    - eapply derives_trans; [apply By_reference_eval_expr |]; auto.
      rewrite H; auto. normalize.
    - apply By_reference_tc_expr; auto.
      rewrite H; auto.
Qed.

Lemma eval_lvalue_nested_efield_aux: forall Delta t_root e efs gfs tts p,
  field_compatible t_root gfs p ->
  legal_nested_efield t_root e gfs tts (LR_of_type t_root) = true ->
  local (`(eq p) (eval_LR e (LR_of_type t_root))) &&
  tc_LR Delta e (LR_of_type t_root) &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p))
   (eval_LR (nested_efield e efs tts) (LR_of_type (nested_field_type t_root gfs)))) &&
  tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (nested_field_type t_root gfs)).
Proof.
  (* Prepare *)
  intros Delta t_root e efs gfs tts p FIELD_COMPATIBLE LEGAL_NESTED_EFIELD.
  unfold local, lift1; simpl; intro rho.
  unfold_lift.
  normalize.
  rename H into EFIELD_DENOTE, H0 into TC_ENVIRON.
  apply derives_trans with (tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho).
  {
    repeat (apply andp_derives; auto).
    eapply derives_trans; [| apply tc_LR_tc_LR_strong].
    rewrite andp_comm, prop_true_andp by auto.
    auto.
  }
  pose proof legal_nested_efield_weaken _ _ _ _ LEGAL_NESTED_EFIELD as [LEGAL_NESTED_EFIELD_REC TYPE_ALMOST_MATCH].
  rewrite field_compatible_field_address by auto.
  clear LEGAL_NESTED_EFIELD.

  (* Induction *)
  revert tts LEGAL_NESTED_EFIELD_REC; induction EFIELD_DENOTE; intros;
  destruct tts; try solve [inversion LEGAL_NESTED_EFIELD_REC];
  [normalize; apply derives_refl | ..];
  pose proof FIELD_COMPATIBLE as FIELD_COMPATIBLE_CONS;
  apply field_compatible_cons in FIELD_COMPATIBLE;
  destruct (nested_field_type t_root gfs) eqn:NESTED_FIELD_TYPE; try solve [inv FIELD_COMPATIBLE];
  rename LEGAL_NESTED_EFIELD_REC into LEGAL_NESTED_EFIELD_REC_CONS;
  pose proof (proj1 (proj1 (andb_true_iff _ _) LEGAL_NESTED_EFIELD_REC_CONS) : legal_nested_efield_rec t_root gfs tts = true) as LEGAL_NESTED_EFIELD_REC;
  (spec IHEFIELD_DENOTE; [tauto |]);
  (spec IHEFIELD_DENOTE; [auto |]);
  specialize (IHEFIELD_DENOTE tts LEGAL_NESTED_EFIELD_REC);
  (apply lvalue_LR_of_type; [eapply typeof_nested_efield'; eauto; econstructor; eauto | eassumption |]);
  destruct FIELD_COMPATIBLE as [? FIELD_COMPATIBLE];
  rewrite offset_val_nested_field_offset_ind by auto;
  rewrite <- field_compatible_field_address in IHEFIELD_DENOTE |- * by auto.
  + eapply array_ind_step; eauto.
  + eapply array_ind_step_ptrofs; eauto.
  + eapply struct_ind_step; eauto.
  + eapply union_ind_step; eauto.
Qed.

Lemma nested_efield_facts: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e (LR_of_type t_root))) &&
  tc_LR Delta e (LR_of_type t_root) &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p))
   (eval_lvalue (nested_efield e efs tts))) &&
  tc_lvalue Delta (nested_efield e efs tts).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto; try apply derives_refl.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.
  
Lemma eval_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  local (`(eq (field_address t_root gfs p)) (eval_lvalue (nested_efield e efs tts))).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  apply andp_left1.
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto; try apply derives_refl.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.

Lemma tc_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  local (efield_denote efs gfs) |--
  tc_lvalue Delta (nested_efield e efs tts).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  apply andp_left2.
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto; try apply derives_refl.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.

Fixpoint compute_nested_efield_rec {cs:compspecs} e lr_default :=
  match e with
  | Efield e' id t =>
    match typeof e' with
    | Tstruct id_str _ =>
      if eqb_type (field_type id (co_members (get_co id_str))) t
      then match compute_nested_efield_rec e' LLLL with
           | (e'', efs, lr) => (e'', eStructField id :: efs, lr)
           end
      else (e, nil, lr_default)
    | Tunion id_uni _ =>
      if eqb_type (field_type id (co_members (get_co id_uni))) t
      then match compute_nested_efield_rec e' LLLL with
           | (e'', efs, lr) => (e'', eUnionField id :: efs, lr)
           end
      else (e, nil, lr_default)
    | _ => (e, nil, lr_default)
    end
  | Ederef (Ebinop Cop.Oadd e' ei (Tpointer t a)) t' =>
    match typeof e' with
    | Tarray t'' _ _ =>
      match eqb_type t t'', eqb_type t t', eqb_attr a noattr with
      | true, true, true =>
        match compute_nested_efield_rec e' RRRR with
        | (e'', efs, lr) => (e'', eArraySubsc ei :: efs, lr)
        end
      | _, _, _ => (e, nil, lr_default)
      end
    | Tpointer t'' _ =>
      match eqb_type t t'', eqb_type t t', eqb_attr a noattr, eqb_type (typeof e') int_or_ptr_type with
      | true, true, true, false => (e', eArraySubsc ei :: nil, RRRR)
      | _, _, _, _ => (e, nil, lr_default)
      end
    | _ => (e, nil, lr_default)
    end
  | _ => (e, nil, lr_default)
  end.

Definition compute_nested_efield {cs: compspecs} (e: expr): expr * list efield * LLRR := compute_nested_efield_rec e LLLL.

Inductive compute_root_type: forall (t_from_e: type) (lr: LLRR) (t_root: type), Prop :=
  | compute_root_type_lvalue: forall t, compute_root_type t LLLL t
  | compute_root_type_Tpointer_expr: forall t a1 n a2, compute_root_type (Tpointer t a1) RRRR (Tarray t n a2)
  | compute_root_type_Tarray_expr: forall t n1 a1 n2 a2, compute_root_type (Tarray t n1 a1) RRRR (Tarray t n2 a2).

(* which means (e, lr) is possible to be called by compute_nested_efield_rec *)
Definition LR_possible (e: expr) (lr: LLRR) : bool :=
  match lr with
  | LLLL => match (typeof e) with
                              | Tarray _ _ _ => false
                              | _ => true
            end
  | RRRR => match (typeof e) with
            | Tarray _ _ _ => true
            | _ => false
            end
  end.

Definition array_relexed_type_eq (t1 t2: type): Prop :=
  match t1, t2 with
  | Tarray t1' _ _, Tarray t2' _ _ => t1' = t2'
  | _, _ => t1 = t2
  end.

Lemma compute_nested_efield_trivial: forall e rho lr_default,
  forall e_root efs lr,
  e_root = e -> efs = nil -> lr = lr_default ->
  LR_possible e lr_default = true ->
  forall t_root gfs,
    exists tts,
      compute_root_type (typeof e_root) lr t_root ->
      efield_denote efs gfs rho ->
      nested_efield e_root efs tts = e /\
      LR_of_type t_root = lr /\
      type_almost_match e_root t_root lr = true /\
      legal_nested_efield_rec t_root gfs tts = true /\
      match gfs with
      | nil => array_relexed_type_eq t_root (typeof e)
      | _ => nested_field_type t_root gfs = typeof e
      end.
Proof.
  intros.
  exists nil.
  intros.
  subst.
  unfold LR_possible in H2.
  unfold type_almost_match.
  Opaque eqb_type.
  destruct (typeof e); inv H2; inv H3; inv H4; simpl;
  try rewrite eqb_type_spec; auto.
  + inv H0.
  + inv H0.
Qed.

Lemma compute_nested_efield_aux: forall e rho lr_default,
  (LR_possible e lr_default = true ->
  match compute_nested_efield_rec e lr_default with
  | (e_root, efs, lr) =>
    forall t_root gfs,
      exists tts,
      compute_root_type (typeof e_root) lr t_root ->
      efield_denote efs gfs rho ->
      nested_efield e_root efs tts = e /\
      LR_of_type t_root = lr /\
      type_almost_match e_root t_root lr = true /\
      legal_nested_efield_rec t_root gfs tts = true /\
      match gfs with
      | nil => array_relexed_type_eq t_root (typeof e)
      | _ => nested_field_type t_root gfs = typeof e
      end
  end) /\
  forall t,
  (LR_possible (Ederef e t) lr_default = true ->
  match compute_nested_efield_rec (Ederef e t) lr_default with
  | (e_root, efs, lr) =>
      forall t_root gfs,
      exists tts,
      compute_root_type (typeof e_root) lr t_root ->
      efield_denote efs gfs rho ->
      nested_efield e_root efs tts = Ederef e t /\
      LR_of_type t_root = lr /\
      type_almost_match e_root t_root lr = true /\
      legal_nested_efield_rec t_root gfs tts = true /\
      match gfs with
      | nil => array_relexed_type_eq t_root (typeof (Ederef e t))
      | _ => nested_field_type t_root gfs = typeof (Ederef e t)
      end
  end).
Proof.
  intros ? ?.
  induction e; intros ?; (split; [ | intros ?]);
  try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl).
  + destruct (IHe lr_default). apply (H0 t).
  + destruct b, t; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl).
    simpl.
    destruct (typeof e1) eqn:?H; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl);
    destruct (eqb_type t t1) eqn:?H; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl);
    apply eqb_type_spec in H0;
    destruct (eqb_type t t0) eqn:?H; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl);
    apply eqb_type_spec in H1;
    destruct (eqb_attr a noattr) eqn:?H; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl);
    apply eqb_attr_spec in H2;
    [destruct (eqb_type ((Tpointer t1 a0)) int_or_ptr_type) eqn:HH; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl); apply eqb_type_false in HH |].
    - subst.
      intros.
      exists (t0 :: nil).
      intros.
      inv H1; inv H2.
      * inv H9.
        unfold type_almost_match.
        rewrite H in H4 |- *; inv H4.
        simpl.
        change (nested_field_type (Tarray t0 n a2) (SUB i)) with t0.
        apply eqb_type_false in HH.
        rewrite HH.
        rewrite !eqb_type_spec.
        auto.
      * inv H9.
        unfold type_almost_match.
        rewrite H in H4 |- *; inv H4.
        simpl.
        change (nested_field_type (Tarray t0 n a2) (SUB i)) with t0.
        apply eqb_type_false in HH.
        rewrite HH.
        rewrite !eqb_type_spec.
        auto.
      * inv H9.
        unfold type_almost_match.
        rewrite H in H4 |- *; inv H4.
      * inv H9.
        unfold type_almost_match.
        rewrite H in H4 |- *; inv H4.
    - subst.
      destruct (IHe1 RRRR) as [IH _]; spec IH; [unfold LR_possible; rewrite H; auto |].
      clear IHe1 IHe2.
      destruct (compute_nested_efield_rec e1 RRRR) as ((?, ?), ?).
      intros.
      destruct gfs; [exists nil; intros _ HHH; inv HHH |].
      specialize (IH t_root gfs).
      destruct IH as [tts IH].
      exists (t0 :: tts).
      intros.
      inv H2.
      {
      specialize (IH H1 H10).
      destruct IH as [IH1 [IH2 [IH3 [IH4 IH5]]]].
      simpl.
      rewrite IH1, IH4.
      simpl.
      rewrite eqb_type_spec.
      assert (nested_field_type t_root (gfs SUB i) = t0); auto.
      rewrite nested_field_type_ind; destruct gfs.
      * destruct t_root; inv IH5; auto.
      * rewrite IH5. auto.
      }{
      specialize (IH H1 H10).
      destruct IH as [IH1 [IH2 [IH3 [IH4 IH5]]]].
      simpl.
      rewrite IH1, IH4.
      simpl.
      rewrite eqb_type_spec.
      assert (nested_field_type t_root (gfs SUB i) = t0); auto.
      rewrite nested_field_type_ind; destruct gfs.
      * destruct t_root; inv IH5; auto.
      * rewrite IH5. auto.
      }       
  + Opaque field_type. simpl. Transparent field_type.
    destruct (typeof e) eqn:?H; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl);
    destruct (eqb_type (field_type i (co_members (get_co i0))) t) eqn:?H; try exact (compute_nested_efield_trivial _ _ _ _ _ _ eq_refl eq_refl eq_refl);
    apply eqb_type_spec in H0.
    - intros.
      destruct (IHe LLLL) as [IH _]; clear IHe.
      spec IH; [unfold LR_possible; rewrite H; auto |].
      destruct (compute_nested_efield_rec e LLLL) as ((?, ?), ?).
      intros.
      destruct gfs; [exists nil; intros _ HHH; inv HHH |].
      specialize (IH t_root gfs).
      destruct IH as [tts IH].
      exists (t :: tts); intros.
      revert H0; inv H3; intros.
      specialize (IH H2 H8).
      destruct IH as [IH1 [IH2 [IH3 [IH4 IH5]]]].
      simpl.
      rewrite IH1, IH4.
      simpl.
      rewrite eqb_type_spec.
      assert (nested_field_type t_root (gfs DOT i) = t); auto.
      rewrite nested_field_type_ind; destruct gfs.
      * destruct t_root; inv IH5; auto.
      * rewrite IH5. auto.
    - intros.
      destruct (IHe LLLL) as [IH _]; clear IHe.
      spec IH; [unfold LR_possible; rewrite H; auto |].
      destruct (compute_nested_efield_rec e LLLL) as ((?, ?), ?).
      intros.
      destruct gfs; [exists nil; intros _ HHH; inv HHH |].
      specialize (IH t_root gfs).
      destruct IH as [tts IH].
      exists (t :: tts); intros.
      revert H0; inv H3; intros.
      specialize (IH H2 H8).
      destruct IH as [IH1 [IH2 [IH3 [IH4 IH5]]]].
      simpl.
      rewrite IH1, IH4.
      simpl.
      rewrite eqb_type_spec.
      assert (nested_field_type t_root (gfs UDOT i) = t); auto.
      rewrite nested_field_type_ind; destruct gfs.
      * destruct t_root; inv IH5; auto.
      * rewrite IH5. auto.
Qed.

Lemma compute_nested_efield_lemma: forall e rho,
  type_is_by_value (typeof e) = true ->
  match compute_nested_efield e with
  | (e_root, efs, lr) =>
    forall t_root gfs,
      exists tts,
      compute_root_type (typeof e_root) lr t_root ->
      efield_denote efs gfs rho ->
      nested_efield e_root efs tts = e /\
      LR_of_type t_root = lr /\
      legal_nested_efield t_root e_root gfs tts lr = true /\
      nested_field_type t_root gfs = typeof e
  end.
Proof.
  intros.
  destruct (compute_nested_efield_aux e rho LLLL) as [? _].
  unfold compute_nested_efield.
  destruct (compute_nested_efield_rec e LLLL) as ((?, ?), ?).
  
  intros.
  spec H0; [unfold LR_possible; destruct (typeof e); inv H; auto |].
  specialize (H0 t_root gfs).
  destruct H0 as [tts ?].
  exists tts.
  intros.
  specialize (H0 H1 H2).
  destruct H0 as [? [? [? [? ?]]]].
  assert (nested_field_type t_root gfs = typeof e);
    [| split; [| split; [| split]]; auto].
  + destruct gfs; auto.
    destruct t_root, (typeof e); inv H6; auto; inv H.
  + unfold legal_nested_efield.
    rewrite H5.
    rewrite H4.
    destruct gfs; auto.
    unfold type_almost_match', type_almost_match in *.
    destruct l0, t_root; try rewrite H4; auto.
    destruct tts; [| inv H5].
    inv H2.
    rewrite <- H7 in H.
    inv H.
Qed.

End CENV.
