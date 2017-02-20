Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.

Require Import tweetnacl20140427.split_array_lemmas.
Require Import ZArith. 
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.verif_salsa_base.

Require Import tweetnacl20140427.spec_salsa.
Require Import veric.expr_lemmas3.

Opaque Snuffle20. Opaque Snuffle.Snuffle. Opaque prepare_data. 
Opaque fcore_result.

Lemma L32_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_L32 L32_spec.
Proof.
start_function.
Time forward. (*8.8*)
Time entailer!. (*0.8*)
assert (W: Int.zwordsize = 32). reflexivity.
assert (U: Int.unsigned Int.iwordsize=32). reflexivity. simpl.
remember (Int.ltu c Int.iwordsize) as d. symmetry in Heqd.
destruct d; simpl. 
{ clear Heqd.
  remember (Int.ltu (Int.sub (Int.repr 32) c) Int.iwordsize) as z. symmetry in Heqz.
  destruct z.
  - simpl; split; trivial. split. 2: split; trivial.
    apply ltu_inv in Heqz. unfold Int.sub in *.
    rewrite (Int.unsigned_repr 32) in *; try (rewrite int_max_unsigned_eq; omega).
    rewrite Int.unsigned_repr in Heqz. 2: rewrite int_max_unsigned_eq; omega.
    unfold Int.rol, Int.shl, Int.shru. rewrite or_repr. 
    rewrite Z.mod_small, W; simpl; try omega.
    rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
    rewrite Int.and_mone. trivial.
  - apply ltu_false_inv in Heqz. rewrite U in *. 
    unfold Int.sub in Heqz. 
    rewrite (Int.unsigned_repr 32), Int.unsigned_repr in Heqz. omega.
    rewrite int_max_unsigned_eq; omega.
    rewrite int_max_unsigned_eq; omega. }
{ apply ltu_false_inv in Heqd. rewrite U in *. omega. }
Time Qed. (*0.9*)

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
  rewrite TP, BMU, Z.mul_add_distr_l, int_max_unsigned_eq. omega. 
  rewrite TP, BMU, Z.mul_add_distr_l, int_max_unsigned_eq. omega.
  rewrite TP, BMU, Z.mul_add_distr_l, int_max_unsigned_eq. omega.
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

Axiom myadmit: False.

Lemma dl64_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_dl64 dl64_spec.
Proof.
start_function.
destruct B as (((b0, b1), b2), b3).
destruct C as (((c0, c1), c2), c3).
unfold QuadByte2ValList; simpl. 
forward. simpl. rewrite Int.signed_repr.
2: rewrite int_min_signed_eq, int_max_signed_eq; omega.

forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL (temp _x x; temp _u (Vlong (Int64.repr (bendian (sublist 0 i [b0;b1;b2;b3;c0;c1;c2;c3])))))
   SEP (data_at Tsh (tarray tuchar 8)
          (map Vint (map Int.repr (map Byte.unsigned 
            [b0;b1;b2;b3;c0;c1;c2;c3]))) x))).
1: solve [ entailer! ]. 
{ rename H into I.
  forward. 
  + entailer!.
    apply zero_ext_range'. change Int.zwordsize with 32; omega.
  + forward. entailer!. exfalso. (*tc_error tulong int*) apply myadmit.
    entailer!. clear H1 H0 H. f_equal. rewrite <- (sublist_rejoin 0 i (i+1)).
    2: omega. 2: rewrite ! Zlength_cons, Zlength_nil; omega.
    rewrite pure_lemmas.sublist_singleton with (d:=Byte.zero).
    2: rewrite ! Zlength_cons, Zlength_nil; omega.
    simpl.
    unfold Int64.or. rewrite Int64.shl_mul_two_p, (Int64.unsigned_repr 8).
    2: unfold Int64.max_unsigned; simpl; omega.
    replace (Znth i
                 [Byte.unsigned b0; Byte.unsigned b1; Byte.unsigned b2; Byte.unsigned b3; 
                 Byte.unsigned c0; Byte.unsigned c1; Byte.unsigned c2; Byte.unsigned c3] 0) 
       with (Byte.unsigned (Znth i [b0; b1; b2; b3; c0; c1; c2; c3] Byte.zero)).
    2: erewrite <- (Znth_map' Byte.unsigned) with (d:= Z.zero); [ reflexivity | apply I ].
    rewrite zero_ext_inrange.
    2: rewrite Int.unsigned_repr; [ apply Byte.unsigned_range_2 | apply Byte_unsigned_range_32 ].
    rewrite Int.unsigned_repr. 2: apply Byte_unsigned_range_32.
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
          Focus 2. assert (0 <= (Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16 / Z.pow_pos 2 8 < Byte.modulus).
                   Focus 2. unfold Byte.max_unsigned. omega.
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
          Focus 2. assert (0 <= Int.unsigned u mod Z.pow_pos 2 24 / Z.pow_pos 2 16 < Byte.modulus).
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
          Focus 2. assert (0 <= Int.unsigned u / Z.pow_pos 2 24 < Byte.modulus).
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

Fixpoint iter64Shr8 (u : int64) (n : nat) {struct n} : int64 :=
  match n with
  | 0%nat => u
  | S n' => Int64.shru (iter64Shr8 u n') (Int64.repr 8)
  end.
(*
Lemma TS64_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_ts64 ts64_spec.
Proof. 
start_function. 
remember (littleendian64_invert u) as U. 
destruct U as [W U]. destruct U as [[[u3 u2] u1] u0].
destruct W as [[[w3 w2] w1] w0].
(*unfold Sfor. forward. forward_seq.*)
(*Parameter Data: Z -> list val.*)
(*assert_PROP (isptr x) by entailer!. rename H into isptrX.*)
Time forward_for_simple_bound 8 (EX i:Z, 
  (PROP  ()
   LOCAL (temp _x x; temp _u (Vlong (iter64Shr8 u (Z.to_nat i))))
   SEP (data_at Tsh (tarray tuchar 8) 
              (sublist 0 i (map Vint (map Int.repr (map Byte.unsigned ([u0;u1;u2;u3;w0;w1;w2;w3])))) ++ 
               list_repeat (Z.to_nat(8-i)) Vundef)
                x))).
{ entailer!. }
{ rename H into I.
  Time assert_PROP (field_compatible (Tarray tuchar 8 noattr) [] x /\ isptr x) 
       as FC_ptrX by solve [entailer!]. (*2.3*)
  destruct FC_ptrX as [FC ptrX].
  Time forward. apply andp_right. apply andp_right. solve [entailer!]. entailer. 
        admit. (*!! typecheck_error (invalid_cast_result tuchar tuchar)*)
        solve [entailer!]. 
  Time forward. entailer. admit. (*another tc_error*)  
  rewrite Z.add_comm, Z2Nat.inj_add; try omega.
  Time entailer!. (*1.5*)
  unfold upd_Znth.
  autorewrite with sublist. 
  rewrite field_at_data_at. simpl. unfold field_address. simpl.
  if_tac. 2: solve [contradiction].
  replace (8 - (1 + i)) with (8-i-1) by omega.
  rewrite isptr_offset_val_zero; trivial. clear H.
  apply data_at_ext. rewrite Zplus_comm.
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
          Focus 2. assert (0 <= (Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16 / Z.pow_pos 2 8 < Byte.modulus).
                   Focus 2. unfold Byte.max_unsigned. omega.
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
          Focus 2. assert (0 <= Int.unsigned u mod Z.pow_pos 2 24 / Z.pow_pos 2 16 < Byte.modulus).
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
          Focus 2. assert (0 <= Int.unsigned u / Z.pow_pos 2 24 < Byte.modulus).
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
{ Exists 7. entailer!. admit. (*Data 7 = list_repeat 8 Vundef*) }

eapply semax_for with (A:=Z)(v:= fun a => Val.of_bool (negb (Int.lt (Int.repr a) (Int.repr 0)))).
 solve [ reflexivity].
 intros. solve [entailer!].
 intros. entailer!. 
{ intros i. simpl. normalize. rename H into I0. rename H0 into I7.
  apply negb_true_iff in I0. (* apply lt_repr_false in I0. 
   2: red; unfold Int.min_signed, Int.max_signed; simpl. 2: split; try omega. Focus 2.
   2: red; unfold Int.min_signed, Int.max_signed; simpl; omega.*)

 forward.
  { apply andp_right. 2: solve [entailer].
    apply andp_right. solve [entailer!].
    entailer. admit. (*typecheck_error (invalid_cast_result tuchar tuchar)*) }

  forward. entailer. simpl. admit. (*typecheck_error
         (arg_type
            (Ebinop Oshr (Etempvar _u tulong) (Econst_int (Int.repr 8) tint)
               tulong))*)

  
  unfold arg_type.
 go_lower. entailer!. Search invalid_cast_result. unfold invalid_cast_result. typecheck_error. simpl.  simpl. destruct (zlt   
{ apply extract_exists_pre. intros i. Intros. rename H into I.
  
 cancel. Focus 2. eapply semax_for with (A:=Z).
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
          Focus 2. assert (0 <= (Int.unsigned u mod Z.pow_pos 2 24) mod Z.pow_pos 2 16 / Z.pow_pos 2 8 < Byte.modulus).
                   Focus 2. unfold Byte.max_unsigned. omega.
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
          Focus 2. assert (0 <= Int.unsigned u mod Z.pow_pos 2 24 / Z.pow_pos 2 16 < Byte.modulus).
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
          Focus 2. assert (0 <= Int.unsigned u / Z.pow_pos 2 24 < Byte.modulus).
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
Focus 2. apply ltu_false_inv in Heqd. rewrite U in *. rewrite Int.unsigned_repr in Heqd. 2: rewrite int_max_unsigned_eq; omega.
clear Heqd. split; trivial.
remember (Int.ltu (Int.sub (Int.repr 32) c') Int.iwordsize) as z. symmetry in Heqz.
destruct z.
Focus 2. apply ltu_false_inv in Heqz. rewrite U in *. 
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
