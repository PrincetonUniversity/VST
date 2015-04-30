Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.compare_lemmas.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.field_at.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Lemma tc_val_Vundef:
  forall t, ~ tc_val t Vundef.
Proof. destruct t as [ | | | [ | ] |  | | | | ]; intro H; inv H.
Qed.

Lemma split3seg_array_at: forall sh t gfs lo ml mr hi ct1 ct2 ct3,
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  Zlength ct1 = ml - lo ->
  Zlength ct2 = mr - ml ->
  array_at sh t gfs lo hi (ct1 ++ ct2 ++ ct3) =
    array_at sh t gfs lo ml ct1 * array_at sh t gfs ml mr ct2 * array_at sh t gfs mr hi ct3.
Proof.
  intros.
  rewrite sepcon_assoc.
  assert (ml <= hi) by omega.
  erewrite <- split2_array_at0 by eauto.
  erewrite <- split2_array_at0 by eauto.
  reflexivity.
Qed.

Lemma extract_prop_from_equal: forall (P: Prop) (Q R: mpred), (P -> Q = R) -> (!! P && Q = !! P && R)%logic.
Proof.
  intros.
  apply pred_ext; normalize;
  rewrite H; auto.
Qed.

Lemma array_seg_reroot_lemma: forall sh t gfs t0 n a lo hi v0 v1 v2 v1' v' p,
  (0 <= lo)%Z ->
  (lo <= hi)%Z ->
  nested_field_type2 t gfs = Tarray t0 n a ->
  (hi <= n)%Z ->
  JMeq v1 v1' ->
  JMeq (v0 ++ v1 ++ v2) v' ->
  Zlength v0 = lo ->
  Zlength v1 = (hi - lo)%Z ->
  field_at sh t gfs v' p =
    array_at sh t gfs 0 lo v0 p *
    data_at sh (Tarray t0 (hi - lo) a) v1'
      (field_address0 t (ArraySubsc lo :: gfs) p) *
    array_at sh t gfs hi n v2 p.
Proof.
  intros.
  erewrite field_at_Tarray by eauto.
  rewrite split3seg_array_at with (ml := lo) (mr := hi) by (try auto; omega).
  normalize.
  erewrite array_at_data_at with (lo := lo) (hi := hi) by eauto.
  pose v0 as v0'.
  assert (JMeq v0 v0') by reflexivity.
  clearbody v0'.
  revert v0' H7.
  pattern (nested_field_type2 t (ArraySubsc 0 :: gfs)) at 1 3.
  rewrite (nested_field_type2_Tarray t0 n a gfs t 0 H1).
  intros.
  reflexivity.
Qed.

Lemma offset_in_range_mid: forall lo hi i t p,
  lo <= i <= hi ->
  offset_in_range (sizeof t * lo) p ->
  offset_in_range (sizeof t * hi) p ->
  offset_in_range (sizeof t * i) p.
Proof.
  intros.
  unfold offset_in_range in *.
  destruct p; auto.
  pose proof sizeof_pos t.
  assert (sizeof t * i <= sizeof t * hi) by (apply Zmult_le_compat_l; omega).
  assert (sizeof t * lo <= sizeof t * i) by (apply Zmult_le_compat_l; omega).
  omega.
Qed.

Ltac solve_andp_left :=
  try apply derives_refl;
  try (apply andp_left1; solve_andp_left);
  apply andp_left2; solve_andp_left.

Lemma extract_prop_from_equal': forall (P: Prop) (Q R: mpred), (P -> Q = R) -> (Q |-- !!P) -> (R |-- !!P) -> Q = R.
Proof.
  intros.
  rewrite (add_andp _ _ H0).
  rewrite (add_andp _ _ H1).
  rewrite !(andp_comm _ (!! P)).
  apply extract_prop_from_equal, H.
Qed.

Lemma prop_andp_ext':
 forall {A} {ND: NatDed A}
    P1 Q1 P2 Q2, 
    (P1 <-> P2) -> (P1 -> (Q1 = Q2)) ->
    (!! P1 && Q1 = !! P2 && Q2).
Proof.
intros.
apply pred_ext; intros; normalize; rewrite H0; auto; intuition;
 apply andp_right; auto; apply prop_right; intuition.
Qed.

Definition in_range (lo hi: Z) (x: Z) := lo <= x < hi.
Arguments in_range lo hi x /.

Lemma Zsucc_sub_self:
 forall x: Z, nat_of_Z (Z.succ x - x) = 1%nat.
Proof.
  intro. replace (Z.succ x - x) with 1 by omega. reflexivity.
Qed.

Definition defined_rep {t} : reptype t -> Prop :=
match t as t0 return (reptype t0 -> Prop) with
| Tvoid => fun _ : reptype Tvoid => False
| Tint i s a =>
    fun v0 : reptype (Tint i s a) => exists v' : int, v0 = Vint v'
| Tlong s a =>
    fun v0 : reptype (Tlong s a) => exists v' : int64, v0 = Vlong v'
| Tfloat f a =>
    fun v0 : reptype (Tfloat f a) => exists v' : float, v0 = Vfloat v'
| Tpointer t0 a => fun v0 : reptype (Tpointer t0 a) => is_pointer_or_null v0
| Tarray t0 z a => fun _ : reptype (Tarray t0 z a) => False
| Tfunction t0 t1 cc => fun _ : reptype (Tfunction t0 t1 cc) => False
| Tstruct i f a => fun _ : reptype (Tstruct i f a) => False
| Tunion i f a => fun _ : reptype (Tunion i f a) => False
| Tcomp_ptr i a => fun _ : reptype (Tcomp_ptr i a) => False
end.

Lemma sem_add_pi_ptr': forall (t : type) sz sg p ofs,
  isptr p ->
  is_int sz sg ofs ->
  isptr (force_val (sem_add_pi t p ofs)).
Proof.
  intros.
  destruct ofs,sg,sz; try inversion H0;
  simpl;
  (rewrite sem_add_pi_ptr; [|exact H];
   destruct p; inversion H; apply I).
Qed.

(*
Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at _ _ _ _ _ _) =>
  (apply array_at_ext'; intros; solve [normalize]) : cancel.

*)
Ltac Z_and_int :=
  repeat
  match goal with
  | |- appcontext [Z.mul _ 0] => rewrite Z.mul_0_r
  | |- appcontext [Z.add _ 0] => rewrite Z.add_0_r
  | |- appcontext [Z.max _ _] => rewrite Z.max_r by omega
  | |- appcontext [Z.max _ _] => rewrite Z.max_l by omega
  | |- appcontext [Int.repr (Int.unsigned _)] => rewrite Int.repr_unsigned
  | |- Int.unsigned ?I <= Int.modulus => pose proof Int.unsigned_range I; omega
  | |- appcontext [Int.add] => unfold Int.add
  | |- appcontext [Int.mul] => unfold Int.mul
  | |- appcontext [Z.of_nat (S _)] => rewrite Nat2Z.inj_succ
  | |- appcontext [Z.succ _] => rewrite <- Z.add_1_r
  | |- appcontext [Int.unsigned (Int.repr _)] => rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega)
  | |- appcontext [Int.Z_mod_modulus ?Z] => change (Int.Z_mod_modulus Z) with (Int.unsigned (Int.repr Z))
  | H: appcontext [Z.of_nat (S _)] |- _ => rewrite Nat2Z.inj_succ in H
  | H: appcontext [Z.succ _] |- _ => rewrite <- Z.add_1_r in H
  | H: appcontext [Int.add] |- _ => unfold Int.add in H
  | H: appcontext [Int.mul] |- _ => unfold Int.mul in H
  | H: appcontext [Int.unsigned (Int.repr _)] |- _ => rewrite Int.unsigned_repr in H by (unfold Int.max_unsigned; omega)
  | H: appcontext [Int.Z_mod_modulus ?Z] |- _ => change (Int.Z_mod_modulus Z) with (Int.unsigned (Int.repr Z)) in H
  end.
(*
Lemma array_at_array_at_: forall t sh contents lo hi p,
  legal_alignas_type t = true ->
  array_at t sh contents lo hi p |-- array_at_ t sh lo hi p.
Proof.
  intros.
  unfold array_at_, array_at, rangespec.
  normalize.
  destruct (zlt hi lo).
  + rewrite nat_of_Z_neg by omega. apply derives_refl.
  + replace hi with (lo + Z.of_nat (nat_of_Z (hi - lo))) in H1 by
      (rewrite nat_of_Z_eq by omega; omega).
    forget (nat_of_Z (hi - lo)) as m. clear hi g.
    revert lo H1 H2; induction m; intros; simpl.
    - apply derives_refl.
    - apply sepcon_derives; [|apply IHm].
      * eapply derives_trans; [apply data_at_data_at_, H|].
        unfold data_at_.
        apply derives_refl.
      * Z_and_int. eapply offset_in_range_mid; [| exact H2 | exact H1].
        omega.
      * Z_and_int. eapply offset_in_range_mid; [| exact H2 | exact H1].
        omega.
Qed.

Hint Resolve array_at_array_at_: cancel.
*)

Lemma add_ptr_int_unfold: forall t1 sz sg v1 v2,
  is_int sz sg v2 ->
  force_val (sem_add_pi t1 v1 v2) = add_ptr_int t1 v1 (force_signed_int v2).
Proof.
  intros.
  destruct v2,sz,sg; try inversion H;
  try (
  unfold add_ptr_int;
  simpl;
  rewrite Int.repr_signed;
  reflexivity).
Qed.

Lemma False_andp:
  forall {A}{NA: NatDed A} (P: A), !! False && P = FF.
Proof. intros. apply pred_ext; normalize. Qed.

Lemma pick_prop_from_eq: forall (P: Prop) (Q R: mpred), (P -> Q = R) -> ((!! P) && Q = (!! P) && R).
Proof.
  intros.
  apply pred_ext; normalize.
  rewrite (H H0); apply derives_refl.
  rewrite (H H0); apply derives_refl.
Qed.

(*
Lemma size_compatible_array_left: forall t n a i b ofs ofs',
  size_compatible (Tarray t n a) (Vptr b ofs) ->
  0 <= i < n ->
  add_ptr_int t (Vptr b ofs) i = (Vptr b ofs') ->
  Int.unsigned ofs' = Int.unsigned ofs + sizeof t * i.
Proof.
  intros.
  unfold add_ptr_int in H1.
  simpl in *.
  inversion H1; clear ofs' H1 H3.
  rewrite Z.max_r in H by omega.
  unfold Int.mul.
  destruct (zeq i 0); [|destruct (zeq (sizeof t) 0)].
  + subst i.
    simpl.
    repeat rewrite <- Zmult_0_r_reverse.
    simpl.
    repeat rewrite <- Zplus_0_r_reverse.
    rewrite Int.Z_mod_modulus_eq.
    rewrite <- Int.unsigned_repr_eq.
    rewrite Int.repr_unsigned.
    reflexivity.
  + rewrite e; clear e.
    simpl.
    repeat rewrite <- Zplus_0_r_reverse.
    rewrite Int.Z_mod_modulus_eq.
    rewrite <- Int.unsigned_repr_eq.
    rewrite Int.repr_unsigned.
    reflexivity.
  + assert (i > 0) by omega.
    assert (n >= 2) by omega.
    pose proof sizeof_pos t.
    pose proof Int.modulus_pos.
    pose proof Int.unsigned_range ofs.
    assert (sizeof t < Int.modulus).
      assert (sizeof t * 2 <= sizeof t * n) by (apply Zmult_le_compat_l; omega).
      rewrite <- Zplus_diag_eq_mult_2 in H6.
      omega.
    assert (n <= Int.modulus).
      assert (n <= sizeof t * n) by (rewrite <- Z.mul_1_l at 1; apply Zmult_le_compat_r; omega).
      omega.
    assert (sizeof t * i < sizeof t * n) by (apply Zmult_lt_compat_l; omega).
    assert (sizeof t * i > 0) by (apply Zmult_gt_0_compat; omega).
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega).
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega).
    simpl.
    repeat (rewrite Int.Z_mod_modulus_eq; rewrite <- Int.unsigned_repr_eq).
    rewrite (Int.unsigned_repr (sizeof t * i)) by (unfold Int.max_unsigned; omega).
    rewrite Int.unsigned_repr; unfold Int.max_unsigned; try omega.
Qed.
(*
Lemma size_compatible_array_right: forall t n a b ofs,
  (forall i ofs', 
  0 <= i < n ->
  add_ptr_int t (Vptr b ofs) i = (Vptr b ofs') ->
  Int.unsigned ofs' + sizeof t <= Int.modulus) ->
  size_compatible (Tarray t n a) (Vptr b ofs).
Proof.
  intros.
  unfold size_compatible; simpl.
  destruct (zlt n 0); Z_and_int.
  assert (Z.of_nat (nat_of_Z n) = n) by (apply nat_of_Z_eq; omega).
  remember (nat_of_Z n) as nn eqn:HH.
  revert n g HH H H0.
  induction nn; intros.
  + simpl in H0; subst. Z_and_int.
  + assert (Int.unsigned ofs + sizeof t * (n - 1) <= Int.modulus).
    - apply (IHnn (n - 1)).
      * Z_and_int.
        pose proof Zle_0_nat nn; omega.
      * subst.
        Z_and_int.
        replace (Z.of_nat nn + 1 - 1) with (Z.of_nat nn) by omega.
        rewrite nat_of_Z_of_nat; reflexivity.
      * intros.
        apply (H i ofs'); [omega | assumption].
      * subst. Z_and_int.
        omega.
    - Z_and_int. assert (0 <= n - 1 < n) by omega.
      pose proof H (n - 1) (Int.repr (Int.unsigned ofs + sizeof t * (n - 1))) H2.
      unfold add_ptr_int in H3; simpl in H3.
      Z_and_int.
      replace (Int.unsigned
               (Int.repr
                  (Int.unsigned (Int.repr (sizeof t)) *
                   Int.unsigned (Int.repr (n - 1))))) with 
              (Int.unsigned
               (Int.repr
                  (sizeof t * (n - 1)))) in H3.
      assert (

SearchAbout Z.of_nat nat_of_Z.
*)

Lemma offset_in_range_size_compatible: forall n t a p,
  offset_in_range (sizeof t * n) p -> size_compatible (Tarray t n a) p.
Proof.
  intros.
  unfold offset_in_range in *.
  unfold size_compatible; simpl sizeof.
  destruct p; auto.
  destruct (zlt n 0); Z_and_int; omega.
Qed.

Lemma semax_loadstore_array:
  forall {Espec: OracleKind},
 forall n vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R, 
  (*H0*) reptype t1 = val -> 
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tptr t1 ->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at t1 sh contents lo hi v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2) 
          (normal_ret_assert 
           (PROPx P (LOCALx Q (SEPx 
            (replace_nth n R `(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1)))))).
Proof.
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl. 
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed. 

Lemma rel_expr_array_load:
  forall ty sh (contents: Z -> reptype ty) lo hi v1 (i: Z) e1 e2 P  rho,
  typeof e1 = tptr ty ->
  typeof e2 = tint ->
  type_is_by_value ty ->
  P |--  rel_expr e1 v1 rho
        && rel_expr e2 (Vint (Int.repr i)) rho
         && (array_at ty sh contents lo hi v1 * TT)
         &&  !! (lo <= i < hi) 
         &&  !! tc_val ty (repinject _ (contents i)) ->
  P |--  rel_expr
      (Ederef
         (Ebinop Oadd e1 e2 (tptr ty)) ty) (repinject _ (contents i)) rho.
Proof.
intros.
eapply derives_trans; [eassumption | clear H2].
 rewrite array_at_isptr. normalize.
 destruct v1; try contradiction. rename i0 into ofs.
 destruct (access_mode_by_value _ H1) as [ch H1'].
 eapply rel_expr_lvalue_By_value with (ch:=ch); auto.
(* destruct ty; inv H1. try contradiction H1. reflexivity. *)
 apply rel_lvalue_deref.
 eapply rel_expr_binop.
 apply andp_left1. apply andp_left1. apply derives_refl.
 apply andp_left1. apply andp_left2. apply derives_refl.
 intro m. rewrite H, H0. simpl. unfold Cop.sem_add; simpl.
  rewrite mul_repr. reflexivity.
 repeat  apply andp_left2.
  rewrite (split3_array_at i ty sh contents lo hi) by omega.
  rewrite (sepcon_comm (array_at ty sh contents lo i (Vptr b ofs))).
  repeat rewrite sepcon_assoc.
  apply sepcon_derives; auto.
  instantiate (1:=sh).
   simpl typeof.
  unfold add_ptr_int. simpl. rewrite mul_repr.
  rewrite  (by_value_data_at sh ty (contents i) (repinject ty (contents i))); auto.
  apply andp_left2. auto.
  clear - H1.
  destruct ty; try contradiction; reflexivity.
  intro Hx; rewrite Hx in H2; clear Hx.
  apply tc_val_Vundef in H2; auto.
Qed.

Lemma offset_val_array_at:
 forall ofs t sh f lo hi v,
  legal_alignas_type t = true ->
  offset_strict_in_range (sizeof t * ofs) v ->
  array_at t sh (fun i => f (i-ofs)%Z)
               (ofs + lo) (ofs + hi) v =
  array_at t sh f lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
  intros.
  unfold array_at, rangespec.
  replace (ofs + hi - (ofs + lo))%Z
    with (hi-lo)%Z by omega.
  forget (nat_of_Z (hi-lo)) as n.
  replace (isptr (offset_val (Int.repr (sizeof t * ofs)) v)) with (isptr v)
    by (apply prop_ext; destruct v; intuition).
  assert (isptr v -> rangespec' (ofs + lo) n
      (fun i : Z => data_at sh t (f (i - ofs)) (add_ptr_int t v i)) =
      rangespec' lo n (fun i : Z =>
      data_at sh t (f i)
        (add_ptr_int t (offset_val (Int.repr (sizeof t * ofs)) v) i))).
  + clear hi.
    revert lo; induction n; simpl; intros; auto.
    replace (ofs+lo-ofs)%Z with lo by omega.
    destruct v; simpl; try tauto.
    f_equal. f_equal.
    unfold add_ptr_int; simpl. unfold sem_add; simpl.
    rewrite Int.add_assoc. f_equal.
    rewrite <- add_repr.
    rewrite <- mul_repr.
    rewrite Int.mul_add_distr_r.
    auto.
    replace (Z.succ (ofs + lo))%Z with (ofs + Z.succ lo)%Z by omega.
    specialize (IHn (Z.succ lo)).
    simpl in IHn. exact (IHn I).
  + unfold offset_in_range, offset_strict_in_range in *.
    destruct v; simpl offset_val in *; auto; apply pred_ext; normalize;
    (rewrite (H1 H5); apply andp_right; [apply prop_right | apply derives_refl]).
    - assert(Int.unsigned (Int.add i (Int.repr (sizeof t * ofs))) = Int.unsigned i + sizeof t * ofs).
      Focus 1. {
        unfold Int.add.
        rewrite !Int.unsigned_repr_eq.
        rewrite Zplus_mod_idemp_r.
        rewrite <- Int.unsigned_repr_eq.
        rewrite Int.unsigned_repr; [reflexivity|].
        unfold Int.max_unsigned.
        omega. } Unfocus.
      unfold align_compatible in *.
      rewrite !H8.
      rewrite <- !Zplus_assoc, <- !Z.mul_add_distr_l.
      repeat split; try omega.
      apply Z.divide_add_r, Z.divide_mul_l; [assumption|].
      apply legal_alignas_sizeof_alignof_compat; assumption.
    - assert(Int.unsigned (Int.add i (Int.repr (sizeof t * ofs))) = Int.unsigned i + sizeof t * ofs).
      Focus 1. {
        unfold Int.add.
        rewrite !Int.unsigned_repr_eq.
        rewrite Zplus_mod_idemp_r.
        rewrite <- Int.unsigned_repr_eq.
        rewrite Int.unsigned_repr; [reflexivity|].
        unfold Int.max_unsigned.
        omega. } Unfocus.
      unfold align_compatible in *.
      rewrite !H8 in *.
      rewrite <- !Zplus_assoc, <- !Z.mul_add_distr_l in *.
      repeat split; try omega.
      rewrite Zplus_comm in H2.
      eapply Z.divide_add_cancel_r; [|exact H2].
      apply Z.divide_mul_l.
      apply legal_alignas_sizeof_alignof_compat; assumption.
Qed.

Lemma split_offset_array_at: forall (ty : type) (sh : Share.t) (contents : Z -> reptype ty)
         (z lo hi : Z) (v : val),
       z <= lo <= hi ->
       sizeof ty > 0 ->
       legal_alignas_type ty = true ->
       array_at ty sh contents z hi v =
       !! offset_in_range (sizeof ty * z) v &&
       !! offset_in_range (sizeof ty * hi) v &&
       array_at ty sh contents z lo v * 
       array_at ty sh (fun i => contents (i + lo)) 0 (hi - lo) 
       (offset_val (Int.repr (sizeof ty * lo)) v).
Proof.
  intros.
  assert (~ offset_strict_in_range (sizeof ty * lo) v \/
          offset_strict_in_range (sizeof ty * lo) v) by
    (unfold offset_strict_in_range; destruct v; auto; omega).
  destruct H2.
  + rewrite (add_andp (array_at ty sh contents z hi v) (!!offset_in_range (sizeof ty * hi) v)) by 
      (unfold array_at; normalize).
    rewrite (add_andp (array_at ty sh contents z hi v) (!!offset_in_range (sizeof ty * z) v)) by 
      (unfold array_at; normalize).
    rewrite andp_assoc.
    rewrite andp_comm.
    normalize.
    apply pick_prop_from_eq; intros.
    assert (lo = hi).
      assert (offset_in_range (sizeof ty * lo) v).
      apply offset_in_range_mid with (lo := z) (hi := hi); [omega | auto |auto].
      tauto.
      tauto.
      assert ((sizeof ty * lo)%Z <= (sizeof ty * hi)%Z) by (apply Z.mul_le_mono_nonneg_l; omega).
      unfold offset_in_range, offset_strict_in_range in *; destruct v; try tauto.
      apply (Z.mul_cancel_l) with (p := sizeof ty); omega.
    subst.
    replace (hi - hi) with 0 by omega.
    rewrite array_at_emp.
    unfold array_at; apply pred_ext; normalize.
    apply andp_right; [apply prop_right | apply derives_refl].
    unfold offset_in_range, offset_strict_in_range in *; destruct v; try tauto.
    unfold offset_val, Int.add, align_compatible.
    pose proof Int.unsigned_range i.
    rewrite !Int.unsigned_repr_eq.
    rewrite Zplus_mod_idemp_r.
    assert ((Int.unsigned i + sizeof ty * hi) = Int.modulus) by omega.
    rewrite H8.
    rewrite Z_mod_same_full.
    repeat split; auto; try omega.
    apply Z.divide_0_r.
  + rewrite split_array_at with (i := lo) (lo := z) (hi := hi) by omega.
    rewrite <- offset_val_array_at with (lo := 0) (hi := hi - lo) (ofs := lo) by assumption.
    rewrite (add_andp (array_at ty sh contents lo hi v) (!!offset_in_range (sizeof ty * hi) v)) by 
      (unfold array_at; normalize).
    rewrite (add_andp (array_at ty sh contents z lo v) (!!offset_in_range (sizeof ty * z) v)) at 1 by 
      (unfold array_at; normalize).
    normalize.
    f_equal.
    f_equal.
    f_equal; [| omega].
    extensionality.
    f_equal.
    omega.
Qed.

(* move this elsewhere *)

Lemma sizeof_tarray_tuchar:
 forall (n:Z), (n>0)%Z -> (sizeof (tarray tuchar n) =  n)%Z.
Proof. intros.
 unfold sizeof,tarray; cbv beta iota.
  rewrite Z.max_r by omega.
  unfold alignof, tuchar; cbv beta iota.
  repeat  rewrite align_1. rewrite Z.mul_1_l. auto.
Qed.

Lemma memory_block_array_tuchar:
  forall sh n, (n>0)%Z -> memory_block sh (Int.repr n) = array_at_ tuchar sh 0 n.
Proof.
  intros.
  replace (Int.repr n) with (Int.repr (sizeof (tarray tuchar n))) by
   (unfold tarray; simpl; rewrite Z.max_r by omega; destruct n; reflexivity).
  assert (legal_alignas_type (Tarray tuchar n noattr) = true).
    unfold tuchar, legal_alignas_type.
    simpl; destruct (n <=? 0); reflexivity.
  assert (nested_non_volatile_type (Tarray tuchar n noattr) = true).
    unfold tuchar, nested_non_volatile_type.
    simpl; destruct (n <=? 0); reflexivity.
  extensionality. erewrite <- data_at__array_at_; [| omega | eassumption].
  rewrite <- memory_block_data_at_ by assumption.
Opaque sizeof.
  simpl. apply pred_ext; normalize.
  apply andp_right; [apply prop_right | apply derives_refl].
  apply align_1_compatible. reflexivity.
Transparent sizeof.
Qed.

Lemma memory_block_array_tuchar':
 forall sh n p, 
   isptr p ->
   (n>=0)%Z -> 
   memory_block sh (Int.repr n) p = array_at_ tuchar sh 0 n p.
Proof.
  intros.
  destruct p; try contradiction. clear H.
  assert (n=0 \/ n>0)%Z by omega.
  destruct H.
  + subst n.
    rewrite memory_block_zero.
    unfold array_at_, array_at. rewrite prop_true_andp by apply I.
    unfold rangespec;  simpl.
    apply pred_ext; normalize.
    apply andp_right; [apply prop_right | apply derives_refl].
    pose proof Int.unsigned_range i; repeat split; try omega.
    apply Z.divide_1_l.
  + apply equal_f; 
    apply memory_block_array_tuchar; auto.
updQed.

Lemma offset_val_array_at_:
 forall ofs t sh lo hi v,
  legal_alignas_type t = true ->
  offset_strict_in_range (sizeof t * ofs) v ->
  array_at_ t sh (ofs + lo) (ofs + hi) v =
  array_at_ t sh lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
intros.
unfold array_at_.
etransitivity; [ | apply offset_val_array_at; try assumption].
f_equal.
Qed.
*)
