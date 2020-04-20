Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.spec_salsa.
Require Import sha.general_lemmas.
Require Import tweetnacl20140427.tweetNaclBase.

(*from verif_ld_st*)
Lemma Byte_unsigned_range_32 b: 0 <= Byte.unsigned b <= Int.max_unsigned.
Proof. rep_omega. Qed.

Lemma vn_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_vn vn_spec.
Proof.
start_function.
forward.
assert_PROP (n = Zlength (map Vint (map Int.repr (map Byte.unsigned xcont))) /\ 
             n = Zlength (map Vint (map Int.repr (map Byte.unsigned ycont)))) as LEN by entailer!.
destruct LEN as [LenX LenY].
assert (ZWS: Int.zwordsize = 32) by reflexivity. 
assert (BWS: Byte.zwordsize = 8) by reflexivity.
forward_for_simple_bound n
(EX i:Z, EX d:_,
  (PROP  (Byte.eq d Byte.zero = if list_eq_dec Byte.eq_dec (sublist 0 i xcont) (sublist 0 i ycont) then true else false)
   LOCAL (temp _d (Vint (Int.repr (Byte.unsigned d)));
          temp _x x; temp _y y; temp _n (Vint (Int.repr n)))
   SEP (data_at xsh (Tarray tuchar n noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
   data_at ysh (Tarray tuchar n noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y))).
{ Exists Byte.zero. entailer!.  }
{ Intros. rename H0 into I. rename H1 into B. rename d into b.
  rewrite 3 Zlength_map in LenX, LenY. 
  forward.
  { entailer!. rep_omega. }
  forward.
  { entailer!. rep_omega. }
  forward. entailer!. clear H3 H6 H4 H7.
  rewrite <- (sublist_rejoin 0 i (i+1) xcont), sublist_len_1; try omega.
  rewrite <- (sublist_rejoin 0 i (i+1) ycont), sublist_len_1; try omega.
  rewrite list_eq_dec_app. 2: rewrite 2 Zlength_sublist; trivial; omega. 2: rewrite 2 Zlength_cons, Zlength_nil; trivial.
  rewrite <- B. unfold Int.xor. 
  remember (list_eq_dec Byte.eq_dec [Znth i xcont] [Znth i ycont]).  simpl.
  rewrite or_repr. clear H0 H1 H2 (*H4*) H5 (*H7*) SH SH0 PNx PNy Heqs.
(*  rewrite 2 zero_ext_inrange by 
      (rewrite Int.unsigned_repr; [ apply Byte.unsigned_range_2 | apply byte_unsigned_range_int_unsigned_max]).*)
  rewrite 2 Int.unsigned_repr by apply byte_unsigned_range_int_unsigned_max. 
  destruct (list_eq_dec Byte.eq_dec (sublist 0 i xcont) (sublist 0 i ycont)).
  + specialize (Byte.eq_spec b Byte.zero); rewrite B; intros; subst b; clear B.
    simpl. destruct s.
    - inv e0. rewrite H1, Z.lxor_nilpotent, Z.lor_0_r.
      Exists Byte.zero. entailer.
    - destruct (Z_lxor_byte_neq (Znth i xcont) (Znth i ycont)) as [bb [BB HBB]].
      * intros N. apply n; rewrite N; trivial.
      * Exists bb; entailer!. split. apply Byte.eq_false; trivial. 
        rewrite BB, Zlor_Byteor, Byte.or_zero_l; trivial.
  + destruct s.
    - inv e. rewrite H1, Z.lxor_nilpotent, Z.lor_0_r, andb_true_r.
      Exists b. entailer!.
    - destruct (Z_lxor_byte_neq (Znth i xcont) (Znth i ycont)) as [bb [BB HBB]].
      * intros N. apply n0; rewrite N; trivial.
      * rewrite BB, Zlor_Byteor, andb_false_r. 
        Exists (Byte.or b bb). entailer!. apply Byte.eq_false. intros N.
        destruct (ByteOr_zero _ _ N). contradiction. }
apply extract_exists_pre; intros b.
forward. apply prop_right.
  rewrite ! Zlength_map in *. rewrite 2 sublist_same in H0; trivial. 
  clear H1 H4 H6 H3 H2 H5 SH SH0 PNx PNy.
  destruct (list_eq_dec Byte.eq_dec xcont ycont).
  + specialize (Byte.eq_spec b Byte.zero). rewrite H0; intros; subst. reflexivity.
  + specialize (Byte.eq_spec b Byte.zero). rewrite H0; intros. clear - ZWS BWS H1.
    f_equal. unfold Int.sub. 
    assert (Int.shru (Int.repr (Byte.unsigned b - 1)) (Int.repr 8) = Int.zero).
    - apply Int.same_bits_eq. rewrite ZWS; intros. rewrite Int.bits_zero, Int.bits_shru; try omega.
      rewrite (Int.unsigned_repr 8) by rep_omega; rewrite ZWS.
      if_tac; trivial. rewrite Int.testbit_repr by omega.
      replace (Byte.unsigned b - 1) with (Byte.unsigned (Byte.sub b Byte.one)).
      apply byte_testbit. omega. unfold Byte.sub.
      rewrite Byte.unsigned_repr; try rep_omega. reflexivity.
      split; [ | rep_omega]. change (Byte.unsigned Byte.one) with 1.
      destruct (Byte.unsigned_range b). replace Byte.modulus with 256 in H3 by reflexivity.
      destruct (zle 0 (Byte.unsigned b - 1)); trivial. elim H1; clear H1.
      assert (ZZ: Byte.unsigned b =0) by omega.
      apply initialize.zero_ext_inj. rewrite ZZ; reflexivity.
    - rewrite H, Int.and_zero; reflexivity.
Qed.

Lemma verify16_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_crypto_verify_16_tweet verify16_spec.
Proof.
start_function.
forward_call (x,y,16,xsh,ysh,xcont,ycont).
forward.
Qed.

Lemma verify32_spec_ok: semax_body SalsaVarSpecs SalsaFunSpecs
       f_crypto_verify_32_tweet verify32_spec.
Proof.
start_function.
forward_call (x,y,32,xsh,ysh,xcont,ycont).
forward.
Qed.