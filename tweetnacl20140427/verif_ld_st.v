Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.verif_salsa_base.

Require Import tweetnacl20140427.spec_salsa.
Require Import VST.veric.expr_lemmas3.

Opaque Snuffle20. Opaque Snuffle.Snuffle. Opaque prepare_data.
Opaque fcore_result.

Lemma L32_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_L32 L32_spec.
Proof.
start_function.
Time forward. (*8.8*)   
entailer!. 
- 
 change (Int.unsigned Int.iwordsize) with 32.
 split.
 +
    unfold Int.signed in H;
    destruct (zlt (Int.unsigned c) Int.half_modulus); rep_omega.
 +
    unfold Int.sub.
    change (Int.unsigned (Int.repr 32)) with 32.
    unfold Int.signed in H.
    rewrite Int.unsigned_repr.
    * destruct (zlt (Int.unsigned c) Int.half_modulus); rep_omega.
    * destruct (zlt (Int.unsigned c) Int.half_modulus); rep_omega.
-
  unfold Int.signed in H.
  destruct (zlt (Int.unsigned c) Int.half_modulus); [| rep_omega].
  apply prop_right.
  unfold sem_shift; simpl.
  unfold Int.ltu.
 change (Int.unsigned Int.iwordsize) with 32.
 simpl.
unfold Int.rol, Int.shl, Int.shru. rewrite or_repr.
rewrite Z.mod_small; simpl; try omega.
unfold Int.sub.
rewrite Int.and_mone,Int.unsigned_repr; trivial.
rewrite Int.unsigned_repr; rep_omega.
rep_omega.
Qed.
(*
Lemma L32_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_L32 L32_spec.
Proof.
start_function. forward.
destruct (Int.ltu c Int.iwordsize) eqn:?H.
  2: {
    apply ltu_false_inv in H0.
    change (Int.unsigned Int.iwordsize) with 32 in H0.
    omega.
  } 
  destruct (Int.ltu (Int.sub (Int.repr 32) c) Int.iwordsize) eqn:?H.
  2:{ 
    apply ltu_false_inv in H1.
    unfold Int.sub in H1.
    change (Int.unsigned (Int.repr 32)) with 32 in H1.
    rewrite Int.unsigned_repr in H1 by rep_omega.
    change (Int.unsigned Int.iwordsize) with 32 in H1.
    omega.
  } 
Time forward. (*8.8*)  
{
  entailer!.
<<<<<<< HEAD
  rewrite H0, H1; simpl; auto.
  split3; auto.
  unfold Int.signed.
  if_tac. rep_omega. repable_signed.
=======
  rewrite H0, H1; simpl; auto. intuition. omega.
>>>>>>> master
}
entailer!.
assert (W: Int.zwordsize = 32). reflexivity.
assert (U: Int.unsigned Int.iwordsize=32). reflexivity.
unfold sem_shift; simpl. rewrite H0, H1; simpl.
unfold Int.rol, Int.shl, Int.shru. rewrite or_repr.
rewrite Z.mod_small, W; simpl; try omega.
unfold Int.sub.
rewrite Int.and_mone.
change (Int.unsigned (Int.repr 32)) with 32.
rewrite Int.unsigned_repr by rep_omega.
auto.
Time Qed. (*0.9*)
*)
Lemma ld32_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_ld32 ld32_spec.
Proof.
start_function.
destruct B as (((b0, b1), b2), b3). simpl.
specialize Byte_max_unsigned_Int_max_unsigned; intros BND.
assert (RNG3:= Byte.unsigned_range_2 b3).
assert (RNG2:= Byte.unsigned_range_2 b2).
assert (RNG1:= Byte.unsigned_range_2 b1).
assert (RNG0:= Byte.unsigned_range_2 b0).
Time forward. (*1.8*)
Time entailer!; omega. (*1.1*)
Time forward. (*2*)
Time entailer!; omega. (*1.1*)
Time forward. (*1.1*)
Time forward. (*2.2*)
Time entailer!; omega. (*1.3*)
Time forward. (*1.5*)
drop_LOCAL 1%nat.
Time forward.
Time entailer!; omega. (*1.3*)
Time forward. (*5.2*)
Time entailer!.
  assert (WS: Int.zwordsize = 32). reflexivity.
  assert (TP: two_p 8 = Byte.max_unsigned + 1). reflexivity.
  assert (BMU: Byte.max_unsigned = 255). reflexivity. simpl.
  repeat rewrite Int.shifted_or_is_add; try repeat rewrite Int.unsigned_repr; try omega.
  f_equal. f_equal. simpl.
    rewrite Z.mul_add_distr_r.
    rewrite (Zmult_comm (Z.pow_pos 2 8)).
    rewrite (Zmult_comm (Z.pow_pos 2 16)).
    rewrite (Zmult_comm (Z.pow_pos 2 24)).
    simpl. repeat rewrite <- two_power_pos_correct.
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_add_distr_r.
    repeat rewrite <- Z.mul_assoc.
    rewrite <- Z.add_assoc. rewrite <- Z.add_assoc. rewrite Z.add_comm. f_equal.
    rewrite Z.add_comm. f_equal. rewrite Z.add_comm. f_equal.
  rewrite TP, BMU, Z.mul_add_distr_l. rep_omega.
  rewrite TP, BMU, Z.mul_add_distr_l. rep_omega.
  rewrite TP, BMU, Z.mul_add_distr_l. rep_omega.
Time Qed. (*6.7*)

Fixpoint lendian (l:list byte): Z :=
  match l with
    nil => 0
  | h::t => Byte.unsigned h + 2^8 * lendian t
  end.

Lemma lendian4 b0 b1 b2 b3: littleendian (b0,b1,b2,b3) = Int.repr(lendian [b0;b1;b2;b3]).
Proof. simpl. rewrite Zplus_0_r. 
rewrite ! Z.mul_add_distr_l, ! (Z.mul_assoc _ (2^8)), <- ! Z.add_assoc; reflexivity.
Qed.

Lemma lendian_nil: lendian [] = 0. Proof. reflexivity. Qed.
Lemma lendian_singleton b: lendian [b] = Byte.unsigned b. Proof. simpl; omega. Qed.

Lemma lendian_app: forall l1 l2, lendian (l1++l2) =
   lendian l1 + 2^(8*Zlength l1) * lendian l2.
Proof.
induction l1; intros.
+ rewrite Zlength_nil; simpl; omega.  
+ simpl. rewrite IHl1. rewrite Zlength_cons; clear IHl1.
  rewrite ! Z.mul_add_distr_l, <- ! Z.add_assoc, Z.mul_assoc, Z.pow_pos_fold.
  f_equal. f_equal. 
  rewrite <- Zpower_exp, <- Zmult_succ_r_reverse, Z.add_comm; trivial. omega.
  specialize (Zlength_nonneg l1); omega. 
Qed.

Lemma lendian_range: forall l, 0 <= lendian l < 2^(8*Zlength l).
Proof. induction l; simpl; intros.
+ omega.
+ rewrite Zlength_cons. destruct (Byte.unsigned_range a).
  assert (Z.pow_pos 2 8 = 256) by reflexivity.
  split. rewrite H1. apply Z.add_nonneg_nonneg; trivial; omega.
  rewrite <- Zmult_succ_r_reverse, Z.pow_add_r; [| specialize (Zlength_nonneg l); omega | omega ].
  rewrite Z.mul_comm. change (Z.pow_pos 2 8) with (2^8).
  assert (Byte.unsigned a + lendian l * 2 ^ 8 < Byte.modulus + lendian l * 2 ^ 8). omega.
  eapply Z.lt_le_trans. apply H2. clear H2 H0. change Byte.modulus with 256.
  change (2^8) with 256. specialize (Z.mul_add_distr_r 1 (lendian l) 256). rewrite Z.mul_1_l.
  intros X; rewrite <- X; clear X. apply Zmult_le_compat_r; omega.
Qed.

Definition bendian l: Z := lendian (rev l).
Lemma bendian_nil: bendian [] = 0. Proof. reflexivity. Qed.
Lemma bendian_singleton b: bendian [b] = Byte.unsigned b. Proof. unfold bendian. simpl; omega. Qed.

Lemma bendian_app l1 l2: bendian (l1++l2) = bendian l2 + 2^(8*Zlength l2) * bendian l1.
Proof. unfold bendian. rewrite rev_app_distr, lendian_app, Zlength_rev; trivial. Qed.

Lemma bendian_range l: 0 <= bendian l < 2^(8*Zlength l).
Proof. unfold bendian. specialize (lendian_range (rev l)). rewrite Zlength_rev; trivial. Qed.

Lemma Zlor_2powpos_add a b (n:positive) (B: 0<=b <Z.pow_pos 2 n):
      a * Z.pow_pos 2 n + b = Z.lor (a * Z.pow_pos 2 n) b.
Proof. apply Byte.equal_same_bits; intros.
  rewrite Z.lor_spec. apply Byte.Z_add_is_or; trivial.
  intros. rewrite Z.pow_pos_fold in *.
  destruct (zlt j (Z.pos n)).
  + rewrite Z.mul_pow2_bits_low; simpl; trivial.
  + rewrite <- (positive_nat_Z n) in g, B.
    erewrite (Byte.Ztestbit_above _ b), andb_false_r. trivial. 2: eassumption.
    rewrite two_power_nat_equiv. apply B.
Qed. 

Lemma Byte_unsigned_range_32 b: 0 <= Byte.unsigned b <= Int.max_unsigned.
Proof. destruct (Byte.unsigned_range_2 b). specialize Byte_Int_max_unsigned; omega. Qed.

Lemma Byte_unsigned_range_64 b: 0 <= Byte.unsigned b <= Int64.max_unsigned.
Proof. destruct (Byte.unsigned_range_2 b).
  unfold Int64.max_unsigned; simpl.
  unfold Byte.max_unsigned in H0; simpl in H0; omega.
Qed. 

Lemma dl64_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_dl64 dl64_spec.
Proof.
start_function.
destruct B as (((b0, b1), b2), b3).
destruct C as (((c0, c1), c2), c3).
unfold QuadByte2ValList; simpl. 
forward. simpl. rewrite Int.signed_repr by  rep_omega.

forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL (temp _x x; temp _u (Vlong (Int64.repr (bendian (sublist 0 i [b0;b1;b2;b3;c0;c1;c2;c3])))))
   SEP (data_at Tsh (tarray tuchar 8)
          (map Vint (map Int.repr (map Byte.unsigned 
            [b0;b1;b2;b3;c0;c1;c2;c3]))) x))).
1: solve [ entailer! ]. 
{ rename H into I.
  assert (HH: Znth i
                 [Byte.unsigned b0; Byte.unsigned b1; Byte.unsigned b2; Byte.unsigned b3; 
                 Byte.unsigned c0; Byte.unsigned c1; Byte.unsigned c2; Byte.unsigned c3] 
          = Byte.unsigned (Znth i [b0; b1; b2; b3; c0; c1; c2; c3])).
  solve [erewrite <- (Znth_map _ Byte.unsigned); [ reflexivity | apply I ] ].
  forward. 
  + entailer!. rewrite HH. 
     apply Byte.unsigned_range_2.
  + simpl; rewrite HH. forward.
    entailer!. clear H1 H0 H. f_equal. rewrite <- (sublist_rejoin 0 i (i+1)).
    2: omega. 2: rewrite ! Zlength_cons, Zlength_nil; omega.
    rewrite sublist_len_1.
    2: rewrite ! Zlength_cons, Zlength_nil; omega.
    simpl.
    unfold Int64.or. rewrite Int64.shl_mul_two_p, (Int64.unsigned_repr 8).
    2: unfold Int64.max_unsigned; simpl; omega.
    rewrite Int64.unsigned_repr. 2: apply Byte_unsigned_range_64.
    change (two_p 8) with 256. 
    rewrite bendian_app, bendian_singleton. simpl.
    unfold Int64.mul.
    rewrite (Int64.unsigned_repr 256). 2: unfold Int64.max_unsigned; simpl; omega.
    rewrite Zplus_comm, Zmult_comm, Zlor_2powpos_add. 2: apply Byte.unsigned_range.
    f_equal. f_equal. remember (bendian (sublist 0 i [b0; b1; b2; b3; c0; c1; c2; c3])) as q.
    specialize (Int64.shifted_or_is_add  (Int64.repr q) Int64.zero 8).
    change (two_p 8) with 256. rewrite Int64.unsigned_zero, Z.add_0_r.
    intros X; rewrite <- X, Int64.or_zero; clear X.
     2: replace Int64.zwordsize with 64 by reflexivity; omega. 2: omega.
    rewrite Int64.shl_mul_two_p, (Int64.unsigned_repr 8).
    2: unfold Int64.max_unsigned; simpl; omega.
    unfold Int64.mul.
    assert (Q: 0 <= q < 2^56).
    { specialize (bendian_range (sublist 0 i [b0; b1; b2; b3; c0; c1; c2; c3])).             
      rewrite Zlength_sublist, Zminus_0_r, <- Heqq. intros. 
      assert (2^(8 * i) <= 2^56) by (apply Z.pow_le_mono_r; omega). omega.
      omega. change (Zlength [b0; b1; b2; b3; c0; c1; c2; c3]) with 8; omega. }
    change (2^56) with 72057594037927936 in Q.
    change (two_p 8) with 256. change (Z.pow_pos 2 8) with 256. 
    rewrite (Int64.unsigned_repr 256).
    2: unfold Int64.max_unsigned; simpl; omega.
    rewrite (Int64.unsigned_repr q).
    2: unfold Int64.max_unsigned; simpl; omega.
    rewrite Int64.unsigned_repr; trivial.
    unfold Int64.max_unsigned; simpl; omega. } 
forward. apply prop_right.
clear H H0. 
unfold bendian. simpl. 
rewrite ! Z.mul_add_distr_l, ! (Z.mul_assoc _ (Z.pow_pos 2 8)),
        <- ! Z.add_assoc, ! Z.mul_0_r, Z.add_0_r.
reflexivity.
Qed.

Lemma div_bound u n (N:1<n): 0 <= Int.unsigned u / n <= Int.max_unsigned.
Proof.
destruct (Int.unsigned_range u).
split. apply Z_div_pos; try omega. 
assert (Int.unsigned u / n <Int.modulus).
2: unfold Int.max_unsigned; omega.
apply Z.div_lt_upper_bound; try omega.
specialize (Z.mul_lt_mono_nonneg 1 n (Int.unsigned u) (Int.modulus)).
rewrite Z.mul_1_l. intros Q; apply Q; trivial.
Qed. 

Lemma ST32_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_st32 st32_spec.
Proof. 
start_function. 
remember (littleendian_invert u) as U. destruct U as [[[u0 u1] u2] u3].

Time forward_for_simple_bound 4 (EX i:Z,
  (PROP  ()
   LOCAL (temp _x x; temp _u (Vint (iterShr8 u (Z.to_nat i))))
   SEP (data_at Tsh (tarray tuchar 4) 
              (sublist 0 i (map Vint (map Int.repr (map Byte.unsigned ([u0;u1;u2;u3])))) ++ 
               list_repeat (Z.to_nat(4-i)) Vundef)
                x))).
{ entailer!. }
{ rename H into I.
  Time assert_PROP (field_compatible (Tarray tuchar 4 noattr) [] x /\ isptr x)
       as FC_ptrX by solve [entailer!]. (*2.3*)
  destruct FC_ptrX as [FC ptrX].
  Time forward. (*3.2*)
  Time forward. (*0.8*)
  rewrite Z.add_comm, Z2Nat.inj_add; try omega.
  Time entailer!. (*1.5*)
  unfold upd_Znth.
  autorewrite with sublist.
  simpl.
  apply data_at_ext. rewrite Zplus_comm.
        assert (ZW: Int.zwordsize = 32) by reflexivity.
        assert (EIGHT: Int.unsigned (Int.repr 8) = 8). apply Int.unsigned_repr.
        rep_omega.
        inv HeqU. clear - ZW EIGHT I.
        destruct (zeq i 0); subst; simpl. f_equal. f_equal.
        { rewrite Byte.unsigned_repr.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^8) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^16) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite <- (Int.zero_ext_mod 8).
              rewrite Int.repr_unsigned; trivial.
              rewrite ZW; omega.
          assert (0 <= ((Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16) mod Z.pow_pos 2 8 < Byte.modulus).
            apply Z_mod_lt. cbv; trivial.
            unfold Byte.max_unsigned. omega. }
        destruct (zeq i 1); subst; simpl. f_equal. f_equal. f_equal.
        { rewrite Byte.unsigned_repr.
          2:{ assert (0 <= (Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16 / Z.pow_pos 2 8 < Byte.modulus).
                   2:{ unfold Byte.max_unsigned. omega. }
                   split. apply Z_div_pos. cbv; trivial. apply Z_mod_lt. cbv; trivial.
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Z_mod_lt. cbv; trivial.
          }
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H.
          rewrite (Z.div_pow2_bits _ 8); try omega.
          rewrite (Int.Ztestbit_mod_two_p 16); try omega.
          rewrite (Int.Ztestbit_mod_two_p 24); try omega.
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW. (* Ztest_Inttest.*)
          remember (zlt i 8). 
          destruct s. repeat rewrite zlt_true. trivial. omega. omega. omega.
          rewrite zlt_false. trivial. omega. }
        destruct (zeq i 2); subst; simpl. f_equal. f_equal. f_equal.
          f_equal.
        { rewrite Byte.unsigned_repr.
          2:{ assert (0 <= Int.unsigned u mod Z.pow_pos 2 24 / Z.pow_pos 2 16 < Byte.modulus).
                   2: unfold Byte.max_unsigned; omega.
                   split. apply Z_div_pos. cbv; trivial. apply Z_mod_lt. cbv; trivial.
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Z_mod_lt. cbv; trivial.
          }
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H.
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW.
          rewrite (Z.div_pow2_bits _ 16); try omega.
          rewrite (Int.Ztestbit_mod_two_p 24); try omega.
          (*rewrite Ztest_Inttest.*)
          remember (zlt i 8). 
          destruct s. repeat rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW.
              rewrite zlt_true. rewrite <- Z.add_assoc. reflexivity. omega. omega. omega. omega.
          rewrite zlt_false. trivial. omega. }
        destruct (zeq i 3); subst; simpl.
        + f_equal. f_equal. f_equal. f_equal.
          f_equal.
          rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= Int.unsigned u / Z.pow_pos 2 24 < Byte.modulus).
                   2: unfold Byte.max_unsigned; omega.
                   split. apply Z_div_pos. cbv; trivial. apply Int.unsigned_range. 
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Int.unsigned_range. 
          }
          rewrite ! Int.shru_div_two_p.
          rewrite (Int.unsigned_repr 8); [| cbv; split; congruence ].
          rewrite (Int.unsigned_repr (Int.unsigned u / two_p 8)), Zdiv.Zdiv_Zdiv; [ | cbv; congruence | cbv; congruence | ] .
          2: apply div_bound; cbv; trivial.
          replace (two_p 8 * two_p 8)%Z with (two_p 16) by reflexivity.
          rewrite (Int.unsigned_repr (Int.unsigned u / two_p 16)), Zdiv.Zdiv_Zdiv; [ | cbv; congruence | cbv; congruence | ] .
          2: apply div_bound; cbv; trivial.
          replace (two_p 16 * two_p 8)%Z with (two_p 24) by reflexivity.
          apply zero_ext_inrange.
          rewrite (Int.unsigned_repr (Int.unsigned u / Z.pow_pos 2 24)).
          2: apply div_bound; cbv; trivial. 
          assert (Int.unsigned u / Z.pow_pos 2 24 < two_p 8). 2: omega.
          apply Z.div_lt_upper_bound; trivial. apply Int.unsigned_range.
        + omega. 
 }
 forward. 
Time Qed. (*4.9*) 

Fixpoint iter64Shr8 (u : int64) (n : nat) {struct n} : int64 :=
  match n with
  | 0%nat => u
  | S n' => Int64.shru (iter64Shr8 u n') (Int64.repr 8)
  end.

Definition iter64Shr8' (u : int64) (n : nat): int64 := 
   Int64.shru u (Int64.mul (Int64.repr 8) (Int64.repr (Z.of_nat n))).

Lemma iter64: forall n u (N: Z.of_nat n < 8), 
      iter64Shr8 u n = iter64Shr8' u n.
Proof. unfold iter64Shr8'.
  assert (W: Int64.iwordsize = Int64.repr 64) by reflexivity.
  induction n; simpl; intros.
+ rewrite Int64.mul_zero, Int64.shru_zero; trivial.
+ rewrite Zpos_P_of_succ_nat in *.
  rewrite IHn, Int64.shru_shru, Int64.mul_commut; clear IHn.
  - f_equal.
    specialize (Int64.mul_add_distr_l (Int64.repr (Z.of_nat n)) Int64.one (Int64.repr 8)).
    rewrite (Int64.mul_commut Int64.one), Int64.mul_one.
    intros X; rewrite <- X, Int64.mul_commut, Int64.add_unsigned; clear X.
    f_equal. f_equal. unfold Int64.one.
    rewrite 2 Int64.unsigned_repr; try reflexivity.   
    unfold Int64.max_unsigned; simpl; omega.
    unfold Int64.max_unsigned; simpl; omega.
 - rewrite W, Int64.mul_signed, 2 Int64.signed_repr.
   unfold Int64.ltu. rewrite (Int64.unsigned_repr 64), if_true; trivial.
   rewrite Int64.unsigned_repr. omega.
   unfold Int64.max_unsigned; simpl; omega.
   unfold Int64.max_unsigned; simpl; omega.
   unfold Int64.min_signed, Int64.max_signed; simpl; omega.
   unfold Int64.min_signed, Int64.max_signed; simpl; omega.
 - rewrite W. unfold Int64.ltu. rewrite if_true; trivial.
 - rewrite W. unfold Int64.ltu. rewrite Int64.mul_signed, Int64.add_signed, if_true; trivial.
   rewrite (Int64.signed_repr 8). 
   2: unfold Int64.min_signed, Int64.max_signed; simpl; omega.
   rewrite (Int64.signed_repr (Z.of_nat n)).   
   2: unfold Int64.min_signed, Int64.max_signed; simpl; omega.
   rewrite Int64.signed_repr. 
   2: unfold Int64.min_signed, Int64.max_signed; simpl; omega.
   rewrite 2 Int64.unsigned_repr. omega.
   unfold Int64.max_unsigned; simpl; omega.
   unfold Int64.max_unsigned; simpl; omega.
 - omega.
Qed. 

Lemma unsigned_repr' z (Q: 0 <= z < Byte.modulus): Byte.unsigned (Byte.repr z) = z.
Proof. apply Byte.unsigned_repr. unfold Byte.max_unsigned. omega. Qed.

Lemma shru_shru x n m (NM:Int64.unsigned n + Int64.unsigned m <= Int64.max_unsigned): 
      Int64.shru (Int64.shru x n) m = Int64.shru x (Int64.add n m).
Proof. rewrite 3 Int64.shru_div_two_p. f_equal.
specialize (Int64.unsigned_range n).
specialize (Int64.unsigned_range m).
specialize (Int64.unsigned_range x). intros X M N.
rewrite Int64.unsigned_repr, Zdiv_Zdiv, <- two_p_is_exp, Int64.add_unsigned, 
Int64.unsigned_repr; trivial; try apply two_p_gt_ZERO; try omega.
split. apply Z_div_pos; trivial. apply two_p_gt_ZERO; try omega. omega.
assert (Int64.unsigned x / two_p (Int64.unsigned n) < Int64.max_unsigned +1). 2: omega.
specialize (two_p_gt_ZERO (Int64.unsigned n)); intros A.
apply Z.div_lt_upper_bound. omega. eapply Z.lt_le_trans. apply X.
unfold Int64.max_unsigned. replace (Int64.modulus - 1 + 1) with Int64.modulus by omega.
specialize (Zmult_le_compat_l 1 (two_p (Int64.unsigned n)) Int64.modulus).
rewrite Z.mul_1_r, Z.mul_comm. intros Y; apply Y; omega.
Qed. 
(*
Lemma TS64_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_ts64 ts64_spec.
Proof. 
start_function. 
remember (bigendian64_invert u) as U. 
destruct U as [B C]. destruct B as [[[b3 b2] b1] b0].
destruct C as [[[c3 c2] c1] c0]. (* unfold littleendian64_invert in HeqU. simpl in HeqU.*)
(*unfold Sfor. forward. forward_seq.*)
(*Parameter Data: Z -> list val.*)
(*assert_PROP (isptr x) by entailer!. rename H into isptrX.*)
Time forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL (temp _x x; temp _u (Vlong (iter64Shr8 u (Z.to_nat i))))
   SEP (data_at Tsh (tarray tuchar 8) 
              (list_repeat (Z.to_nat(8-i)) Vundef ++
               sublist (8-i) 8 (map Vint (map Int.repr (map Byte.unsigned ([b3;b2;b1;b0;c3;c2;c1;c0])))))
                x))).
{ entailer!. } 2: solve [forward].
{ rename H into I.
  Time assert_PROP (field_compatible (Tarray tuchar 8 noattr) [] x /\ isptr x) 
       as FC_ptrX by solve [entailer!]. 
  destruct FC_ptrX as [FC ptrX].x
Definition typecheck_expr := 
fix
typecheck_expr (CS : compspecs) (Delta : tycontext) (e : expr) {struct e} :
  tc_assert :=
  let tcr := typecheck_expr CS Delta in
  match e with
  | Econst_int _ Tvoid => tc_FF (invalid_expression e)
  | Econst_int _ (Tint I8 _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tint I16 _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tint I32 _ _) => tc_TT
  | Econst_int _ (Tint IBool _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tlong _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tfloat _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tpointer _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tarray _ _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tfunction _ _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tstruct _ _) => tc_FF (invalid_expression e)
  | Econst_int _ (Tunion _ _) => tc_FF (invalid_expression e)
  | Econst_float _ Tvoid => tc_FF (invalid_expression e)
  | Econst_float _ (Tint _ _ _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tlong _ _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tfloat F32 _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tfloat F64 _) => tc_TT
  | Econst_float _ (Tpointer _ _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tarray _ _ _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tfunction _ _ _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tstruct _ _) => tc_FF (invalid_expression e)
  | Econst_float _ (Tunion _ _) => tc_FF (invalid_expression e)
  | Econst_single _ Tvoid => tc_FF (invalid_expression e)
  | Econst_single _ (Tint _ _ _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tlong _ _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tfloat F32 _) => tc_TT
  | Econst_single _ (Tfloat F64 _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tpointer _ _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tarray _ _ _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tfunction _ _ _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tstruct _ _) => tc_FF (invalid_expression e)
  | Econst_single _ (Tunion _ _) => tc_FF (invalid_expression e)
  | Econst_long _ _ => tc_FF (invalid_expression e)
  | Evar id ty =>
      match access_mode ty with
      | By_value _ => tc_FF (deref_byvalue ty)
      | By_reference =>
          match get_var_type Delta id with
          | Some ty' =>
              tc_bool (eqb_type ty ty') (mismatch_context_type ty ty')
          | None => tc_FF (var_not_in_tycontext Delta id)
          end
      | By_copy => tc_FF (deref_byvalue ty)
      | By_nothing => tc_FF (deref_byvalue ty)
      end
  | Etempvar id ty =>
      match (temp_types Delta) ! id with
      | Some ty' =>
          if
           (is_neutral_cast (fst ty') ty || same_base_type (fst ty') ty)%bool
          then if snd ty' then tc_TT else tc_initialized id ty
          else tc_FF (mismatch_context_type ty (fst ty'))
      | None => tc_FF (var_not_in_tycontext Delta id)
      end
  | Ederef a ty =>
      match access_mode ty with
      | By_value _ => tc_FF (deref_byvalue ty)
      | By_reference =>
          tc_andp
            (tc_andp (typecheck_expr CS Delta a)
               (tc_bool (is_pointer_type (typeof a)) (op_result_type e)))
            (tc_isptr a)
      | By_copy => tc_FF (deref_byvalue ty)
      | By_nothing => tc_FF (deref_byvalue ty)
      end
  | Eaddrof a ty =>
      tc_andp (typecheck_lvalue CS Delta a)
        (tc_bool (is_pointer_type ty) (op_result_type e))
  | Eunop op a ty => tc_andp (isUnOpResultType op a ty) (tcr a)
  | Ebinop op a1 a2 ty =>
      tc_andp (tc_andp (isBinOpResultType op a1 a2 ty) (tcr a1)) (tcr a2)
  | Ecast a ty => tc_andp (tcr a) (isCastResultType (typeof a) ty a)
  | Efield a i ty =>
      match access_mode ty with
      | By_value _ => tc_FF (deref_byvalue ty)
      | By_reference =>
          tc_andp (typecheck_lvalue CS Delta a)
            match typeof a with
            | Tvoid => tc_FF (invalid_field_access e)
            | Tint _ _ _ => tc_FF (invalid_field_access e)
            | Tlong _ _ => tc_FF (invalid_field_access e)
            | Tfloat _ _ => tc_FF (invalid_field_access e)
            | Tpointer _ _ => tc_FF (invalid_field_access e)
            | Tarray _ _ _ => tc_FF (invalid_field_access e)
            | Tfunction _ _ _ => tc_FF (invalid_field_access e)
            | Tstruct id _ =>
                match cenv_cs ! id with
                | Some co =>
                    match Ctypes.field_offset cenv_cs i (co_members co) with
                    | Errors.OK _ => tc_TT
                    | Errors.Error _ => tc_FF (invalid_struct_field i id)
                    end
                | None => tc_FF (invalid_composite_name id)
                end
            | Tunion id _ =>
                match cenv_cs ! id with
                | Some _ => tc_TT
                | None => tc_FF (invalid_composite_name id)
                end
            end
      | By_copy => tc_FF (deref_byvalue ty)
      | By_nothing => tc_FF (deref_byvalue ty)
      end
  | Esizeof ty t =>
      tc_andp (tc_bool (complete_type cenv_cs ty) (invalid_expression e))
        (tc_bool (eqb_type t (Tint I32 Unsigned noattr))
           (invalid_expression e))
  | Ealignof ty t =>
      tc_andp (tc_bool (complete_type cenv_cs ty) (invalid_expression e))
        (tc_bool (eqb_type t (Tint I32 Unsigned noattr))
           (invalid_expression e))
  end
with
typecheck_lvalue (CS : compspecs) (Delta : tycontext) (e : expr) {struct e} :
  tc_assert :=
  match e with
  | Econst_int _ _ => tc_FF (invalid_lvalue e)
  | Econst_float _ _ => tc_FF (invalid_lvalue e)
  | Econst_single _ _ => tc_FF (invalid_lvalue e)
  | Econst_long _ _ => tc_FF (invalid_lvalue e)
  | Evar id ty =>
      match get_var_type Delta id with
      | Some ty' => tc_bool (eqb_type ty ty') (mismatch_context_type ty ty')
      | None => tc_FF (var_not_in_tycontext Delta id)
      end
  | Etempvar _ _ => tc_FF (invalid_lvalue e)
  | Ederef a _ =>
      tc_andp
        (tc_andp (typecheck_expr CS Delta a)
           (tc_bool (is_pointer_type (typeof a)) (op_result_type e)))
        (tc_isptr a)
  | Eaddrof _ _ => tc_FF (invalid_lvalue e)
  | Eunop _ _ _ => tc_FF (invalid_lvalue e)
  | Ebinop _ _ _ _ => tc_FF (invalid_lvalue e)
  | Ecast _ _ => tc_FF (invalid_lvalue e)
  | Efield a i _ =>
      tc_andp (typecheck_lvalue CS Delta a)
        match typeof a with
        | Tvoid => tc_FF (invalid_field_access e)
        | Tint _ _ _ => tc_FF (invalid_field_access e)
        | Tlong _ _ => tc_FF (invalid_field_access e)
        | Tfloat _ _ => tc_FF (invalid_field_access e)
        | Tpointer _ _ => tc_FF (invalid_field_access e)
        | Tarray _ _ _ => tc_FF (invalid_field_access e)
        | Tfunction _ _ _ => tc_FF (invalid_field_access e)
        | Tstruct id _ =>
            match cenv_cs ! id with
            | Some co =>
                match Ctypes.field_offset cenv_cs i (co_members co) with
                | Errors.OK _ => tc_TT
                | Errors.Error _ => tc_FF (invalid_struct_field i id)
                end
            | None => tc_FF (invalid_composite_name id)
            end
        | Tunion id _ =>
            match cenv_cs ! id with
            | Some _ => tc_TT
            | None => tc_FF (invalid_composite_name id)
            end
        end
  | Esizeof _ _ => tc_FF (invalid_lvalue e)
  | Ealignof _ _ => tc_FF (invalid_lvalue e)
  end.

set (e1:=(Ederef
           (Ebinop Oadd (Etempvar _x (tptr tuchar))
              (Ebinop Osub (Econst_int (Int.repr 7) tint) 
                 (Etempvar _i tint) tint) (tptr tuchar)) tuchar)).
set (e2:=(Ecast (Etempvar _u tulong) tuchar)).
assert (XX: typeof e1 = tuchar) by reflexivity.
set (TC:=tc_expr Delta (Ecast e2 tuchar)). cbv in TC. simpl in TC.
Eval compute in (tc_expr Delta (Ecast e2 tuchar)).
  Time forward. apply andp_right. apply andp_right. solve [entailer!]. entailer. 
        myadmit. (*!! typecheck_error (invalid_cast_result tuchar tuchar)*)
        solve [entailer!]. 
  Time forward. entailer. myadmit. (*another tc_error*)  
  rewrite Z.add_comm, Z2Nat.inj_add; try omega.
  Time entailer!. (*1.5*)
  unfold upd_Znth. clear H.
  autorewrite with sublist.
  replace (8 - (1 + i)) with (7-i) by omega. 
  replace (7 - i + 1) with (8-i) by omega.
  replace (i+(8-i)) with 8 by omega.
  rewrite field_at_data_at. simpl. unfold field_address. simpl.
  if_tac. 2: solve [contradiction].
  rewrite isptr_offset_val_zero; [| trivial]. clear H.
  apply data_at_ext. f_equal.
  rewrite <- (sublist_rejoin (7-i) (7-i+1) 8). 2: omega. 2: unfold Zlength; simpl; omega.
  rewrite pure_lemmas.sublist_singleton with (d:=Vundef); simpl.
  2: unfold Zlength; simpl; omega.
  replace (7 - i + 1) with (8-i) by omega. f_equal.
  rewrite iter64; try rewrite Z2Nat.id; try omega. unfold iter64Shr8', Int64.shru. 
  rewrite Int64.mul_signed.
  rewrite 2 Int64.signed_repr; try rewrite Z2Nat.id; try unfold Int64.min_signed, Int64.max_signed; simpl; try omega.
  rewrite (Int64.unsigned_repr (8 * i)).
  2: unfold Int64.max_unsigned; simpl; omega.
  specialize (Int64.unsigned_range u); specialize (Z.pow_pos_nonneg 2 (8*i)); intros NN U.
  rewrite Int64.unsigned_repr.
  2:{ rewrite Z.shiftr_div_pow2 by omega.
           split. apply Z_div_pos; omega. 
           assert (Int64.unsigned u / 2 ^ (8 * i) < Int64.modulus).
           2: solve [unfold Int64.max_unsigned; omega].
           apply Zdiv_lt_upper_bound. omega.
           assert (Int64.modulus <= Int64.modulus * 2 ^ (8 * i)). 2: omega.
           apply Z.le_mul_diag_r; omega.
  }
  assert (ADD16: Int64.add (Int64.repr 8) (Int64.repr 8)
         = Int64.repr 16) by reflexivity.
  assert (ADD24: Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.repr 8))
         = Int64.repr 24) by reflexivity.
  assert (ADD32: Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.repr 8)))
         = Int64.repr 32) by reflexivity.
  assert (ADD40: Int64.add (Int64.repr 8)
                       (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.repr 8))))
         = Int64.repr 40) by reflexivity.
  assert (ADD48: Int64.add (Int64.repr 8)
                 (Int64.add (Int64.repr 8)
                    (Int64.add (Int64.repr 8)
                       (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.repr 8)))))
          = Int64.repr 48) by reflexivity.
  assert (ADD56: Int64.add (Int64.repr 8)
                 (Int64.add (Int64.repr 8)
                    (Int64.add (Int64.repr 8)
                       (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.repr 8))))))
         = Int64.repr 56) by reflexivity.
  assert (UBND: forall n m, Pos.add m n=64%positive -> 0 <= Int64.unsigned u / Z.pow_pos 2 n < Z.pow_pos 2 m).
  { intros. 
    destruct (Int64.unsigned_range u).
    split. apply Z_div_pos; trivial. specialize (Fcore_Zaux.Zpower_pos_gt_0 2 n); omega.
    apply Zdiv_lt_upper_bound; trivial. specialize (Fcore_Zaux.Zpower_pos_gt_0 2 n); omega.
    rewrite <- Zpower_pos_is_exp, H.
    change Int64.modulus with (Z.pow_pos 2 64) in H1; trivial. }(*
  assert (B1: 0 <= Int64.unsigned u / Z.pow_pos 2 56 <= Byte.max_unsigned).
  { destruct (UBND 56 8)%positive. reflexivity.
    replace Byte.max_unsigned with (Z.pow_pos 2 8 -1). omega. reflexivity. }*) 
  assert (UNS_B_I64: Byte.max_unsigned <= Int64.max_unsigned) by (cbv; congruence). 
  assert (UNS_B_I: Byte.max_unsigned <= Int.max_unsigned) by (cbv; congruence).
  destruct (zeq i 0).
  { subst i; simpl in *. unfold Znth; simpl.
    unfold bigendian64_invert in HeqU; inv HeqU.
    rewrite Z.shiftr_0_r. unfold 
  destruct (zeq i 7).
  { subst; simpl in *. unfold Znth; simpl.
    (*specialize (UBND 56 8)%positive. rewrite Z.pow_pos_fold in UBND.*)
    rewrite ! shru_shru, ADD56.
    + rewrite Int64.shru_div_two_p, (Int64.unsigned_repr 56), two_p_correct.
      2: unfold Int64.max_unsigned; simpl; omega.
      rewrite Int64.unsigned_repr.
      * rewrite zero_ext_inrange. f_equal; f_equal.
        - unfold bigendian64_invert in HeqU; inv HeqU.
          rewrite Byte.unsigned_repr. reflexivity. change Byte.max_unsigned with (Z.pow_pos 2 8 -1).
          specialize (UBND 56 8 (eq_refl _))%positive; omega.
        - rewrite Int.unsigned_repr, two_p_equiv. specialize (UBND 56 8 (eq_refl _))%positive.
          rewrite ! Z.pow_pos_fold in UBND. omega.
          specialize (UBND 56 8 (eq_refl _))%positive.
          rewrite ! Z.pow_pos_fold in UBND.
          assert (2^8 < Int.max_unsigned) by (cbv; trivial). omega.
       * specialize (UBND 56 8 (eq_refl _))%positive.
         rewrite ! Z.pow_pos_fold in UBND.
         assert (2^8 < Int64.max_unsigned) by (cbv; trivial). omega.
    + rewrite ADD48. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD40. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD32. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD24. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD16. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ! Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega. }
  destruct (zeq i 0).
  { subst; simpl in *. unfold Znth; simpl. f_equal.
    unfold bigendian64_invert in HeqU; inv HeqU. simpl.
        rewrite Byte.unsigned_repr.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^8) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^16) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^24) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^32) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^40) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^48) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
           unfold Int.zero_ext. apply Int.eqm_samerepr. apply Int.eqm_same_bits. change Int.zwordsize with 32; intros.
           rewrite Int.Zzero_ext_spec. destruct (zlt i 8); subst; simpl. 
           + destruct (zeq i 0); subst; simpl. remember u as uu. destruct uu; simpl.
             rewrite Int.unsigned_repr. unfold Z.odd. unfold Int64.unsigned, Int64.intval. simpl. 
              remember (Int.unsigned (Int.repr (Int64.unsigned u))). destruct z.
               Int.eqm. apply Int.testbit 
specialize (Int.zero_ext_mod 8).
            Check Int64.zero_ext_mod. Require Import compcert.lib.Integers.
  intros. specialize (Int.equal_same_bits (Int.unsigned (Int.zero_ext 8 (Int.repr (Int64.unsigned u)))) (Int.unsigned (Int.repr (Int64.unsigned u mod 2 ^ 8)))). intros.
  unfold Int.zero_ext in *.
  
  rewrite Ztestbit_mod_two_p; auto.
  fold (testbit (zero_ext n x) i).
  destruct (zlt i zwordsize).
  rewrite bits_zero_ext; auto.
  rewrite bits_above. rewrite zlt_false; auto. omega. omega.
  omega.
Qed.


              rewrite Int.repr_unsigned; trivial.
              rewrite ZW; omega.
          assert (0 <= ((Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16) mod Z.pow_pos 2 8 < Byte.modulus).
            apply Z_mod_lt. cbv; trivial. 
            unfold Byte.max_unsigned. omega. }
  destruct (zeq i 6).
  { subst; simpl in *. unfold Znth; simpl.
    (*assert ((56 <= 56)%positive) by apply Pos.le_refl.
    specialize (B1 _ H); clear H. rewrite Z.pow_pos_fold in B1.*)
    rewrite ! shru_shru, ADD48.
    + rewrite Int64.shru_div_two_p, (Int64.unsigned_repr 48), two_p_correct.
      2: unfold Int64.max_unsigned; simpl; omega.
      assert (QQ:= (UBND 48 16 (eq_refl _))%positive).
      rewrite ! Z.pow_pos_fold in QQ.
      rewrite Int64.unsigned_repr.
      2:{ assert (2 ^ 16 < Int64.max_unsigned) by (cbv; trivial). omega. f_equal; f_equal. }
      unfold bigendian64_invert in HeqU; inv HeqU. simpl.
      destruct (Int64.unsigned_range u).
      destruct (zlt (Int64.unsigned u) (Z.pow_pos 2 56)).
      - rewrite Zmod_small by omega. rewrite ! Z.pow_pos_fold.
        assert (0<= Int64.unsigned u / 2 ^ 48 < 2^8).
        { split; try omega. apply Zdiv_lt_upper_bound; trivial. }
        (*rewrite Int.unsigned_repr. 2: change Byte.max_unsigned with (2^8-1) in UNS_B_I; omega.*)
        rewrite Byte.unsigned_repr. 2: change Byte.max_unsigned with (2^8-1); omega.
        rewrite zero_ext_inrange; trivial.
        rewrite Int.unsigned_repr. 2: change Byte.max_unsigned with (2^8-1) in UNS_B_I; omega.
        change (two_p 8) with (2^8); omega.
      - specialize (Fcore_Zaux.Zdiv_mod_mult (Int64.unsigned u) (Z.pow_pos 2 48) (Z.pow_pos 2 8)); intros.
        change ((Z.pow_pos 2 48 * Z.pow_pos 2 8)%Z) with (Z.pow_pos 2 56) in H1.
        rewrite H1. rewrite Byte.unsigned_repr. 2:{ destruct (Z_mod_lt (Int64.unsigned u / Z.pow_pos 2 48) (Z.pow_pos 2 8)). cbv; trivial. }
              change Byte.max_unsigned with (Z.pow_pos 2 8 -1). omega.
        unfold Int.zero_ext.
 clear - H1; rewrite int_max_unsigned_eq; split; try omega. specialize (Fcore_Zaux.Zpower_pos_gt_0 2 n); omega.
    rewrite <- Zpower_pos_is_exp, H.
    change Int64.modulus with (Z.pow_pos 2 64) in H1; trivial.
        
      rewrite (Zdiv_small (Int64.unsigned u mod Z.pow_pos 2 56)).
      2:{ specialize (Zmod_unique (Int64.unsigned u) (Z.pow_pos 2 56)); intros.
      rewrite Int.unsigned_repr.
      2:{ assert (2 ^ 16 < Int64.max_unsigned) by (cbv; trivial). omega. }
      unfold Int.zero_ext. f_equal. f_equal. }
      apply Byte.equal_same_bits; intros. rewrite Int.Zzero_ext_spec by omega.
      unfold bigendian64_invert in HeqU; inv HeqU. simpl.
specialize (Zmod_recombine (Int64.unsigned u) (Z.pow_pos 2 8) (Z.pow_pos 2 48)). intros.
replace (Z.pow_pos 2 8 * Z.pow_pos 2 48)%Z with (Z.pow_pos 2 56) in H0.
      rewrite H0.
      destruct (zlt i 8).
      rewrite <- (Byte.testbit_repr (Byte.unsigned b2)), Byte.repr_unsigned. unfold Byte.testbit.
      rewrite if_true. by omega.
      rewrite Int64.unsigned_repr.
      unfold Int.zero_ext. rewrite Int.unsigned_repr.
 
 unfold Int.zero_ext. f_equal. f_equal.
      rewrite Int64.unsigned_repr by omega.
      rewrite zero_ext_inrange. f_equal; f_equal.
      - unfold bigendian64_invert in HeqU; inv HeqU.
        rewrite Byte.unsigned_repr. reflexivity. rewrite Z.pow_pos_fold. omega.
      - rewrite Int.unsigned_repr. apply B1. omega.
    + rewrite ADD48. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD40. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD32. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD24. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ADD16. rewrite 2 Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega.
    + rewrite ! Int64.unsigned_repr; unfold Int64.max_unsigned; simpl; omega. }

    + rewrite ! Int64.add_unsigned. rewrite ! Int64.unsigned_repr; simpl; unfold Int64.max_unsigned; simpl; try omega.
    + } 
    rewrite two_p_correct. rewrite Z.pow_pos_fold in B1. omega.
    unfold Int64.max_unsigned; simpl; omega.
    rewrite Int64.shru_div_two_p.  UNSB_I64.  <- two_power_nat_two_p. omega. apply B1; apply  Pos.le_refl. cbv. omega. myadmit.  myadmit.  myadmit.  myadmit.  myadmit.
    myadmit.  myadmit.  myadmit.  myadmit.  myadmit. }
  destruct (zeq i 6).
  { subst; simpl in *. unfold Znth; simpl.
    rewrite ! shru_shru. 
    replace (Int64.add (Int64.repr 8)
                 (Int64.add (Int64.repr 8)
                    (Int64.add (Int64.repr 8)
                       (Int64.add (Int64.repr 8) (Int64.add (Int64.repr 8) (Int64.repr 8))))))
    with (Int64.repr 48) by reflexivity.
    rewrite zero_ext_inrange. f_equal; f_equal.
    unfold bigendian64_invert in HeqU; inv HeqU.
    rewrite Int64.shru_div_two_p.
    rewrite (Int64.unsigned_repr 48).
    rewrite Int64.unsigned_repr.
    rewrite Byte.unsigned_repr.x
    specialize (Fcore_Zaux.Zdiv_mod_mult (Int64.unsigned u) (Z.pow_pos 2 8) (Z.pow_pos 2 48) ). intros.
    replace (Z.pow_pos 2 8 * Z.pow_pos 2 48)%Z with (Z.pow_pos 2 56) in H by reflexivity.
    rewrite H.
    specialize (Fcore_Zaux.Zdiv_mod_mult). (Int64.unsigned u) (Z.pow_pos 2 40) (Z.pow_pos 2 8)). intros.
    replace (Z.pow_pos 2 40 * Z.pow_pos 2 8)%Z with (Z.pow_pos 2 48) in H0 by reflexivity.

 intros.
    replace (Z.pow_pos 2 48 * Z.pow_pos 2 8)%Z with (Z.pow_pos 2 56) in H by reflexivity.
    rewrite H.  reflexivity. myadmit.  myadmit.  myadmit.  myadmit.  myadmit.
    myadmit.  myadmit.  myadmit.  myadmit.  myadmit. }
      
    unfold Int64.shru.  simpl. ! Int64.add_unsigned. (Int64.unsigned_repr 8).
    

 rewrite if_false by omega.

  unfold Znth; simpl. 
  rewrite if_false by omega. destruct (Int64.unsigned_range_2 u).
  unfold bigendian64_invert in HeqU. inv HeqU. 
  assert (BMU: Byte.max_unsigned = 255) by reflexivity.
  assert (I64MU: Int64.max_unsigned = Z.pow 2 64 -1) by reflexivity.
  rewrite iter64. 2: rewrite Z2Nat.id; omega. 
  unfold iter64Shr8'. rewrite Z2Nat.id; try omega. 
  rewrite Int64.mul_signed.
  rewrite 2 Int64.signed_repr; try (unfold Int64.min_signed, Int64.max_signed; simpl; omega).
  rewrite Int64.shru_div_two_p, (Int64.unsigned_repr (8 * i)). 2: unfold Int64.max_unsigned; simpl; omega.
  assert (GT:= two_p_gt_ZERO (8*i)).
  assert (BND1: 0 <= Int64.unsigned u / Z.pow_pos 2 56 < Byte.modulus).
  { split. apply Z_div_pos; trivial. cbv; trivial.
           apply Z.div_lt_upper_bound. cbv; trivial. simpl in *. omega. } 
(*  assert (BND1: 0 <= Int64.unsigned u / Z.pow_pos 2 56 < Byte.max_unsigned).
  { split. apply Z_div_pos; trivial. cbv; trivial.
           assert (Int64.unsigned u / Z.pow_pos 2 56 < Byte.modulus). 2: unfold Byte.max_unsigned; omega.
           apply Z.div_lt_upper_bound. cbv; trivial. simpl in *. omega. }*)
  (*assert (BND1: 0 <= Int64.unsigned u / Z.pow_pos 2 56 < Byte.modulus).
  { split. apply Z_div_pos; trivial. cbv; trivial.
           apply Z.div_lt_upper_bound. cbv; trivial. simpl in *. omega. }*)
  rewrite unsigned_repr'; trivial.
(*  rewrite Int64.unsigned_repr.
  2:{ split. apply Z_div_pos; trivial. omega. 
           apply Z.div_le_upper_bound. omega. 
           eapply Z.le_trans; eauto. 
           specialize (Zmult_le_compat_r 1 (two_p (8 * i)) Int64.max_unsigned). simpl.
           intros Q; apply Q; omega.*)
  rewrite unsigned_repr'.
  2:{ split.  apply Z_div_pos; trivial. cbv; trivial. apply Z_mod_lt. cbv; trivial. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  rewrite unsigned_repr'.
  2:{ split.  apply Z_div_pos; trivial. cbv; trivial. apply Z_mod_lt. cbv; trivial. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  rewrite unsigned_repr'.
  2:{ split.  apply Z_div_pos; trivial. cbv; trivial. apply Z_mod_lt. cbv; trivial. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  rewrite unsigned_repr'.
  2:{ split.  apply Z_div_pos; trivial. cbv; trivial. apply Z_mod_lt. cbv; trivial. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  rewrite unsigned_repr'.
  2:{ split.  apply Z_div_pos; trivial. cbv; trivial. apply Z_mod_lt. cbv; trivial. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  rewrite unsigned_repr'.
  2:{ split.  apply Z_div_pos; trivial. cbv; trivial. apply Z_mod_lt. cbv; trivial. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  rewrite unsigned_repr'.
  2:{ split.  apply Z_mod_lt. cbv; trivial. apply Z_mod_lt. cbv; trivial.
  assert (BND: 0 <= Int64.unsigned u / Z.pow_pos 2 56 <= Byte.max_unsigned).
  { unfold Byte.max_unsigned; omega. }
  assert (IMU: Int.max_unsigned = 4294967295) by reflexivity.
  destruct (zeq i 7).
  { subst; simpl in *. rewrite two_power_pos_correct, zero_ext_inrange.
    + rewrite Int64.unsigned_repr; trivial.
      split. apply Z_div_pos; trivial. cbv; trivial. 
           apply Z.div_le_upper_bound. cbv; trivial. 
           eapply Z.le_trans; eauto.
    + rewrite Int.unsigned_repr, Int64.unsigned_repr. apply BND. omega. 
      rewrite Int64.unsigned_repr. omega. omega. } 
  destruct (zeq i 6).
  { subst; simpl in *. rewrite two_power_pos_correct, zero_ext_inrange.
       specialize (Fcore_Zaux.Zdiv_mod_mult (Int64.unsigned u) (Z.pow_pos 2 48) (Z.pow_pos 2 8)).
       rewrite <- Zpower_pos_is_exp. intros Q.
       replace (Z.pow_pos 2 (48 + 8)) with (Z.pow_pos 2 56) in Q by reflexivity.
       rewrite Q. rewrite Zmod_small; trivial. f_equal. f_equal.  simpl. reflexivity.
    rewrite Int.unsigned_repr; simpl in *; omega. }

 omega.
    replace Byte.modulus with (two_p 8) in BND1 unfold Byte.modulus in BND1. simpl in *. cbv. unfold Int.zero_ext. rewrite Int.unsigned_repr. 
           apply Z.div_lt_upper_bound. cbv; trivial.
           eapply Z.lt_le_trans. apply Z_mod_lt. cbv; trivial. cbv; congruence.
  . omega. cbv. 
           specialize (Zmult_le_compat_r 1 (two_p (8 * i)) Int64.max_unsigned). simpl.
           intros Q; apply Q; omega.
  rewrite zero_ext_inrange. 
  2:{ rewrite Int.unsigned_repr.
           assert (Int64.unsigned u / two_p (8 * i) < two_p 8). 2: omega.
           apply Z.div_lt_upper_bound. omega.
           assert (Int64.max_unsigned < two_p (8 * i) * two_p 8). 2: omega.
           rewrite 2 two_p_equiv, Z.pow_mul_r, I64MU; try omega.
           specialize (Zpower_exp (2^8) i 1); rewrite Z.pow_1_r.
           intros Q; rewrite <- Q. simpl. omega. simpl.
              simpl in *. omega. split. apply Z_div_pos; trivial. cbv; trivial.
           assert (Int64.unsigned u / Z.pow_pos 2 56 < Byte.modulus). 2: unfold Byte.max_unsigned; omega.
           apply Z.div_lt_upper_bound. cbv; trivial. simpl in *. omega.
 
  destruct (zeq i 7). { subst. simpl in *. rewrite zero_ext_inrange. rewrite Byte.unsigned_repr. reflexivity.
  { split. apply Z_div_pos; trivial. cbv; trivial.
           assert (Int64.unsigned u / Z.pow_pos 2 56 < Byte.modulus). 2: unfold Byte.max_unsigned; omega.
           apply Z.div_lt_upper_bound. cbv; trivial. simpl. omega. } 
           eapply Z.le_trans; eauto. rewrite I64MU. simpl. clear. cbv. omega. 
           unfold omega.  simpl. omega.  Zdiv_interval_2.
  destruct (zeq i 0); subst; simpl. rewrite Byte.unsigned_repr. myadmit.
  + f_equal. rewrite iter64. 2: rewrite Z2Nat.id; omega.
    unfold iter64Shr8'. rewrite Z2Nat.id; try omega.  
    unfold Int64.mul. rewrite 2 Int64.unsigned_repr.
    2: unfold Int64.max_unsigned; simpl; omega.
    2: unfold Int64.max_unsigned; simpl; omega.
    rewrite Int64.shru_div_two_p.
    rewrite (Int64.unsigned_repr (8 * i)), two_p_equiv.
    2: unfold Int64.max_unsigned; simpl; omega. 
    assert (X: 0 < 2 ^ (8 * i)) by (apply Z.pow_pos_nonneg; omega).
    destruct (Int64.unsigned_range_2 u).
    assert (T: 0 <= Int64.unsigned u / 2 ^ (8 * i) <= 255).
    { split. apply Z_div_pos. omega. omega. 
       apply Zdiv_le_upper_bound; trivial. eapply Z.le_trans. apply H0.       
       unfold Int64.max_unsigned. rewrite Int64.modulus_power. 
       replace (two_p Int64.zwordsize) with (2^64) by reflexivity.
       assert (2 ^ 64 < 255 * 2 ^ (8 * i)). 2: omega.
       specialize (Zmult_le_compat_l 1 (2 ^ (8 * i)) Int64.max_unsigned).
       rewrite Z.mul_1_r. intros Y; apply Y. omega. unfold Int64.max_unsigned; simpl; omega. }   
    
    assert (Q: 0 <= Int64.unsigned u / 2 ^ (8 * i) <= Int64.max_unsigned).
    { split. apply Z_div_pos. omega. omega. 
       apply Zdiv_le_upper_bound; trivial. eapply Z.le_trans. apply H0.
       specialize (Zmult_le_compat_l 1 (2 ^ (8 * i)) Int64.max_unsigned).
       rewrite Z.mul_1_r. intros Y; apply Y. omega. unfold Int64.max_unsigned; simpl; omega. }   
    rewrite Int64.unsigned_repr; trivial.  
    rewrite zero_ext_inrange. f_equal. myadmit.
    rewrite Int.unsigned_repr. replace (two_p 8 - 1) with 255 by reflexivity.
  replace (1 + (7 - i)) with (8-i) by omega. replace (i + (8 - i)) with 8 by omega.
  destruct (zeq i 0).
  { subst; unfold sublist;  simpl. unfold littleendian64_invert in HeqU.
    inv HeqU. 
  rewrite <- app_comm_cons. (sublist_app1 _ 0 i). 2: omega. 2: rewrite Zlength_sublist. omega.
  rewrite <- app_assoc.
        assert (ZW: Int.zwordsize = 32) by reflexivity.
        assert (EIGHT: Int.unsigned (Int.repr 8) = 8). apply Int.unsigned_repr. rewrite int_max_unsigned_eq; omega.
        inv HeqU. clear - ZW EIGHT I. simpl.
        destruct (zeq i 0); subst; simpl. f_equal. f_equal.
        { rewrite Byte.unsigned_repr.              
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^8) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^16) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite <- (Int.zero_ext_mod 8).
              rewrite Int.repr_unsigned; trivial.
              rewrite ZW; omega.
          assert (0 <= ((Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16) mod Z.pow_pos 2 8 < Byte.modulus).
            apply Z_mod_lt. cbv; trivial. 
            unfold Byte.max_unsigned. omega. }
        destruct (zeq i 1); subst; simpl. f_equal. f_equal. f_equal.
        { rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= (Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16 / Z.pow_pos 2 8 < Byte.modulus).
                   2:{ unfold Byte.max_unsigned. omega.
                   split. apply Z_div_pos. cbv; trivial. apply Z_mod_lt. cbv; trivial.
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Z_mod_lt. cbv; trivial.
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H. 
          rewrite (Z.div_pow2_bits _ 8); try omega.
          rewrite (Int.Ztestbit_mod_two_p 16); try omega.
          rewrite (Int.Ztestbit_mod_two_p 24); try omega.
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW, Ztest_Inttest.
          remember (zlt i 8). 
          destruct s. repeat rewrite zlt_true. trivial. omega. omega. omega.
          rewrite zlt_false. trivial. omega. }
        destruct (zeq i 2); subst; simpl. f_equal. f_equal. f_equal.
          f_equal.
        { rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= Int.unsigned u mod Z.pow_pos 2 24 / Z.pow_pos 2 16 < Byte.modulus).
                   2: unfold Byte.max_unsigned; omega.
                   split. apply Z_div_pos. cbv; trivial. apply Z_mod_lt. cbv; trivial.
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Z_mod_lt. cbv; trivial.
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H. 
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW.
          rewrite (Z.div_pow2_bits _ 16); try omega.
          rewrite (Int.Ztestbit_mod_two_p 24); try omega.
          rewrite Ztest_Inttest.
          remember (zlt i 8). 
          destruct s. repeat rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW.
              rewrite zlt_true. rewrite <- Z.add_assoc. reflexivity. omega. omega. omega. omega.
          rewrite zlt_false. trivial. omega. }
        destruct (zeq i 3); subst; simpl. f_equal. f_equal. f_equal. f_equal.
          f_equal.
        { rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= Int.unsigned u / Z.pow_pos 2 24 < Byte.modulus).
                   2: unfold Byte.max_unsigned; omega.
                   split. apply Z_div_pos. cbv; trivial. apply Int.unsigned_range. 
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Int.unsigned_range. 
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H. 
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW.
          rewrite (Z.div_pow2_bits _ 24); try omega.
          rewrite Ztest_Inttest.
          remember (zlt i 8). 
          destruct s. rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW.
              rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW. 
              rewrite zlt_true. repeat rewrite <- Z.add_assoc. reflexivity. omega. omega. omega. omega. omega.
          rewrite Int.bits_above. trivial. omega. }
        omega. }
  Time forward. (*1.6*)
Time Qed. (*4.9*) 

 unfold data_at_, field_at_.
  rewrite field_at_data_at. 
  rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero. apply data_at_ext. unfold default_val. simpl. unfold tarray. simpl.   destruct tv. reflexivity. cancel. rewrite unfold field_address; simpl. normalize. cancel. }

forward_for (EX z:_, 
  (PROP (0<= z <= 7 )
   LOCAL (temp _i (Vint (Int.repr z)); temp _x x; 
          temp _u (Vlong u))
   SEP (data_at Tsh (tarray tuchar 8) (Data z) x))). 
{ Exists 7. entailer!. myadmit. (*Data 7 = list_repeat 8 Vundef*) }

eapply semax_for with (A:=Z)(v:= fun a => Val.of_bool (negb (Int.lt (Int.repr a) (Int.repr 0)))).
 solve [ reflexivity].
 intros. solve [entailer!].
 intros. entailer!. 
{ intros i. simpl. normalize. rename H into I0. rename H0 into I7.
  apply negb_true_iff in I0. (* apply lt_repr_false in I0. 
   2: red; unfold Int.min_signed, Int.max_signed; simpl. 2: split; try omega. 2:{
   2: red; unfold Int.min_signed, Int.max_signed; simpl; omega.*)

 forward.
  { apply andp_right. 2: solve [entailer].
    apply andp_right. solve [entailer!].
    entailer. myadmit. (*typecheck_error (invalid_cast_result tuchar tuchar)*) }

  forward. entailer. simpl. myadmit. (*typecheck_error
         (arg_type
            (Ebinop Oshr (Etempvar _u tulong) (Econst_int (Int.repr 8) tint)
               tulong))*)

  
  unfold arg_type.
 go_lower. entailer!. Search invalid_cast_result. unfold invalid_cast_result. typecheck_error. simpl.  simpl. destruct (zlt   
{ apply extract_exists_pre. intros i. Intros. rename H into I.
  
 cancel. 2:{ eapply semax_for with (A:=Z).
  reflexivity.
Ltac forward_for_simple_bound n Pre ::=
  check_Delta;
 repeat match goal with |-
      semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 end. (*
 first [ 
    match type of n with
      ?t => first [ unify t Z | elimtype (Type_of_bound_in_forward_for_should_be_Z_but_is t)]
    end;
    match type of Pre with
      ?t => first [unify t (environ -> mpred); fail 1 | elimtype (Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is t)]
    end
  | simple eapply semax_seq'; 
    [forward_for_simple_bound' n Pre 
    | cbv beta; simpl update_tycon; abbreviate_semax  ]
  | eapply semax_post_flipped'; 
     [forward_for_simple_bound' n Pre 
     | ]
  ].*)

Time forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL (temp _x x; temp _u (Vlong (iter64Shr8 u (Z.to_nat i))))
   SEP (data_at Tsh (tarray tuchar 8) 
              (sublist 0 i (map Vint (map Int.repr (map Byte.unsigned ([w0;w1;w2;w3;u0;u1;u2;u3])))) ++ 
               list_repeat (Z.to_nat(8-i)) Vundef)
                x))).
{ entailer!. }
{ rename H into I.
  Time assert_PROP (field_compatible (Tarray tuchar 4 noattr) [] x /\ isptr x) 
       as FC_ptrX by solve [entailer!]. (*2.3*)
  destruct FC_ptrX as [FC ptrX].
  Time forward. (*3.2*)
  Time forward. (*0.8*)  
  rewrite Z.add_comm, Z2Nat.inj_add; try omega.
  Time entailer!. (*1.5*)
  unfold upd_Znth.
  autorewrite with sublist. 
  rewrite field_at_data_at. simpl. unfold field_address. simpl.
  if_tac. 2: solve [contradiction].
  replace (4 - (1 + i)) with (4-i-1) by omega.
  rewrite isptr_offset_val_zero; trivial. clear H.
  apply data_at_ext. rewrite Zplus_comm.
        assert (ZW: Int.zwordsize = 32) by reflexivity.
        assert (EIGHT: Int.unsigned (Int.repr 8) = 8). apply Int.unsigned_repr. rewrite int_max_unsigned_eq; omega.
        inv HeqU. clear - ZW EIGHT I.
        destruct (zeq i 0); subst; simpl. f_equal. f_equal.
        { rewrite Byte.unsigned_repr.              
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^8) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite (Fcore_Zaux.Zmod_mod_mult _ (2^16) (2^8)). 2: cbv; trivial. 2: cbv; intros; discriminate.
            rewrite <- (Int.zero_ext_mod 8).
              rewrite Int.repr_unsigned; trivial.
              rewrite ZW; omega.
          assert (0 <= ((Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16) mod Z.pow_pos 2 8 < Byte.modulus).
            apply Z_mod_lt. cbv; trivial. 
            unfold Byte.max_unsigned. omega. }
        destruct (zeq i 1); subst; simpl. f_equal. f_equal. f_equal.
        { rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= (Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16 / Z.pow_pos 2 8 < Byte.modulus).
                   2:{ unfold Byte.max_unsigned. omega.
                   split. apply Z_div_pos. cbv; trivial. apply Z_mod_lt. cbv; trivial.
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Z_mod_lt. cbv; trivial.
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H. 
          rewrite (Z.div_pow2_bits _ 8); try omega.
          rewrite (Int.Ztestbit_mod_two_p 16); try omega.
          rewrite (Int.Ztestbit_mod_two_p 24); try omega.
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW, Ztest_Inttest.
          remember (zlt i 8). 
          destruct s. repeat rewrite zlt_true. trivial. omega. omega. omega.
          rewrite zlt_false. trivial. omega. }
        destruct (zeq i 2); subst; simpl. f_equal. f_equal. f_equal.
          f_equal.
        { rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= Int.unsigned u mod Z.pow_pos 2 24 / Z.pow_pos 2 16 < Byte.modulus).
                   2: unfold Byte.max_unsigned; omega.
                   split. apply Z_div_pos. cbv; trivial. apply Z_mod_lt. cbv; trivial.
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Z_mod_lt. cbv; trivial.
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H. 
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW.
          rewrite (Z.div_pow2_bits _ 16); try omega.
          rewrite (Int.Ztestbit_mod_two_p 24); try omega.
          rewrite Ztest_Inttest.
          remember (zlt i 8). 
          destruct s. repeat rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW.
              rewrite zlt_true. rewrite <- Z.add_assoc. reflexivity. omega. omega. omega. omega.
          rewrite zlt_false. trivial. omega. }
        destruct (zeq i 3); subst; simpl. f_equal. f_equal. f_equal. f_equal.
          f_equal.
        { rewrite Byte.unsigned_repr.  
          2:{ assert (0 <= Int.unsigned u / Z.pow_pos 2 24 < Byte.modulus).
                   2: unfold Byte.max_unsigned; omega.
                   split. apply Z_div_pos. cbv; trivial. apply Int.unsigned_range. 
                   apply Zdiv_lt_upper_bound. cbv; trivial. apply Int.unsigned_range. 
          apply Int.same_bits_eq. rewrite ZW; intros.
          rewrite Int.bits_zero_ext, Int.testbit_repr; try apply H. 
          rewrite Int.bits_shru; try omega. rewrite EIGHT, ZW.
          rewrite (Z.div_pow2_bits _ 24); try omega.
          rewrite Ztest_Inttest.
          remember (zlt i 8). 
          destruct s. rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW.
              rewrite zlt_true. rewrite Int.bits_shru, EIGHT, ZW. 
              rewrite zlt_true. repeat rewrite <- Z.add_assoc. reflexivity. omega. omega. omega. omega. omega.
          rewrite Int.bits_above. trivial. omega. }
        omega. }
  Time forward. (*1.6*)
Time Qed. (*4.9*) 
*)

(*
Definition L32_specZ :=
  DECLARE _L32
   WITH x : int, c: int
   PRE [ _x OF tuint, _c OF tint ]
      PROP () (*c=Int.zero doesn't seem to satisfy spec???*)
      LOCAL (temp _x (Vint x); temp _c (Vint Int.zero))
      SEP ()
  POST [ tuint ]
     PROP (True)
     LOCAL ()
     SEP ().

Definition LDZFunSpecs : funspecs :=
  L32_specZ::nil.

Lemma L32_specZ_ok: semax_body SalsaVarSpecs LDZFunSpecs
       f_L32 L32_specZ.
Proof.
start_function.
name x' _x.
name c' _c.
forward. entailer. apply prop_right.
assert (W: Int.zwordsize = 32). reflexivity.
assert (U: Int.unsigned Int.iwordsize=32). reflexivity.
(*remember (Int.eq c' Int.zero) as z.
  destruct z. apply binop_lemmas.int_eq_true in Heqz. subst. simpl. *)
remember (Int.ltu (Int.repr 32) Int.iwordsize) as d. symmetry in Heqd.
destruct d; simpl.
2:{ apply ltu_false_inv in Heqd. rewrite U in *. rewrite Int.unsigned_repr in Heqd. 2: rewrite int_max_unsigned_eq; omega.
clear Heqd. split; trivial.
remember (Int.ltu (Int.sub (Int.repr 32) c') Int.iwordsize) as z. symmetry in Heqz.
destruct z.
2:{ apply ltu_false_inv in Heqz. rewrite U in *.
         unfold Int.sub in Heqz.
         rewrite (Int.unsigned_repr 32) in Heqz.
           rewrite Int.unsigned_repr in Heqz. omega. rewrite int_max_unsigned_eq; omega.
           rewrite int_max_unsigned_eq; omega.
simpl; split; trivial. split; trivial.
apply ltu_inv in Heqz. unfold Int.sub in *.
  rewrite (Int.unsigned_repr 32) in *; try (rewrite int_max_unsigned_eq; omega).
  rewrite Int.unsigned_repr in Heqz. 2: rewrite int_max_unsigned_eq; omega.
  unfold Int.rol, Int.shl, Int.shru. rewrite or_repr.
  assert (Int.unsigned c' mod Int.zwordsize = Int.unsigned c').
    apply Zmod_small. rewrite W; omega.
  rewrite H0, W. f_equal. f_equal. f_equal.
  rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
  rewrite Int.and_mone. trivial.
Qed.
*)
