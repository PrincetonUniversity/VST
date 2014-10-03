Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.

Local Open Scope logic.

Lemma int_unsigned_mod:
 forall i, Int.unsigned i mod Int.modulus = Int.unsigned i.
Proof.
intros. rewrite <- (Int.repr_unsigned i).
rewrite <- Int.unsigned_repr_eq.
rewrite Int.repr_unsigned.
auto.
Qed.

Lemma Z_div_mul: forall a b, b <> 0 ->
      (a/b*b = a - a mod b)%Z.
Proof.
intros.
pose proof (Z_div_mod_eq_full a b H).
rewrite H0 at 2.
rewrite Z.mul_comm; omega.
Qed.

Lemma body_SHA256_addlength: semax_body Vprog Gtot f_SHA256_addlength SHA256_addlength_spec.
Proof.
start_function.
name c_ _c.
name len_ _len.
name l_ _l.
name Nl _cNl.
name Nh _cNh.
unfold sha256_length.
normalize.
rename H into BOUND.
intro lo.
normalize.
intro hi.
normalize.
revert POSTCONDITION; subst n; intro.
assert (MN: Int.modulus <> 0) by (intro Hx; inv Hx).
forward.
forward.
forward. (* l=(cNl+(((SHA_LONG)len)<<3))&0xffffffffUL; *)
apply semax_pre with 
  (PROP  (0 <= len < Int.modulus)
   LOCAL 
   (`(eq (Vint (Int.repr (Int.unsigned lo+len*8)))) (eval_id _l);
   `(eq (Vint hi)) (eval_id _cNh);
   `(eq (Vint lo)) (eval_id _cNl);
   `(eq (Vint (Int.repr len))) (eval_id _len);
   `(eq c) (eval_id _c))
   SEP  (`(field_at Tsh t_struct_SHA256state_st [_Nl] (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st [_Nh] (Vint hi) c))).
entailer!.
change Int.modulus with (Int.max_unsigned + 1); omega.
rewrite Int.shl_mul_two_p.
change (two_p (Int.unsigned (Int.repr 3))) with 8.
rewrite Int.and_mone.
rewrite mul_repr.
rewrite <- add_repr.
rewrite Int.repr_unsigned. auto.
apply semax_extract_PROP; intro.
pose (carry := ((Int.unsigned lo + (len * 8) mod Int.modulus)
                        -  (Int.unsigned lo + len * 8) mod Int.modulus)/Int.modulus).
forward_if (
   PROP  ()
   LOCAL  (`(eq (Vint (Int.repr (Int.unsigned lo + len * 8)))) (eval_id _l);
   `(eq (Vint (Int.repr (Int.unsigned hi + carry)))) (eval_id _cNh);
   `(eq (Vint lo)) (eval_id _cNl);
   `(eq (Vint (Int.repr len))) (eval_id _len); `(eq c) (eval_id _c))
   SEP  (`(field_at Tsh t_struct_SHA256state_st [_Nl] (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st [_Nh] (Vint hi) c))).
* (* then-clause *)
 forward.
 entailer!.
 rewrite <- (Int.repr_unsigned hi) at 2.
 rewrite add_repr.
 f_equal.
 f_equal.
 unfold carry.
 unfold Int.ltu in H1.
 rewrite <- add_repr in H1.
 rewrite Int.repr_unsigned in H1.
 if_tac in H1; [clear H1 | discriminate].
  
 clear - MN H2 H. rename H2 into H0.
 destruct (Int.unsigned_add_either lo (Int.repr (len*8))) as [H9|H9].
 elimtype False; rewrite H9 in H0; clear H9.
 destruct (Int.unsigned_range (Int.repr (len*8))) as [? _]; omega.
 clear H0.
 unfold Int.add in H9.
 rewrite (Int.unsigned_repr_eq (len*8)) in H9.
 replace (Int.unsigned lo + (len * 8) mod Int.modulus)
  with (Int.unsigned (Int.repr (Int.unsigned lo + (len * 8) mod Int.modulus)) +
           Int.modulus) by omega.
 clear - MN.
 rewrite Int.unsigned_repr_eq.
 rewrite (Z.add_mod (Int.unsigned lo) (len*8)) by assumption.
 rewrite int_unsigned_mod.
 replace ((Int.unsigned lo + (len * 8) mod Int.modulus) mod Int.modulus + Int.modulus -
 (Int.unsigned lo + (len * 8) mod Int.modulus) mod Int.modulus)
   with Int.modulus by omega.
 apply Z.div_same; assumption.
* (* else clause *)
 forward.  (* skip; *)
 entailer!.
 unfold carry; clear carry.
 clear H0; rename H1 into H0.
 unfold Int.ltu in H0.
 rewrite <- add_repr in H0.
 rewrite Int.repr_unsigned in H0.
 if_tac in H0; [ discriminate |].
 clear - MN H1 H.
 destruct (Int.unsigned_add_either lo (Int.repr (len*8))) as [H9|H9];
  [ | destruct (Int.unsigned_range (Int.repr (len*8))); omega].
 clear H1.
 rewrite <- (Int.repr_unsigned lo) in H9 at 1.
 rewrite add_repr in H9.
 rewrite Int.unsigned_repr_eq in H9 .
  rewrite Int.unsigned_repr_eq in H9 .
 rewrite <- H9; clear H9.
 rewrite Z.sub_diag.
 rewrite Z.div_0_l by auto.
 rewrite Z.add_0_r.
 apply Int.repr_unsigned.
* (* after the if *)
 forward. (* cNh += (len>>29); *)
 forward. (* c->Nl=l; *)
 forward. (* c->Nh=cNh; *)
 forward. (* return; *)
 unfold sha256_length.
 apply exp_right with (Int.repr (Int.unsigned lo + len * 8)).
 apply exp_right with (Int.add (Int.repr (Int.unsigned hi + carry))
        (Int.shru (Int.repr len) (Int.repr 29))).
 rewrite prop_true_andp; auto.
 unfold carry; clear - MN H BOUND.
 unfold hilo in *.
 rewrite Int.shru_div_two_p.
 change (Int.unsigned (Int.repr 29)) with 29.
 assert (Int.max_unsigned + 1 = Int.modulus) by reflexivity.
 rewrite (Int.unsigned_repr len) by omega.
 unfold Int.add.
 repeat rewrite Int.unsigned_repr_eq.
 rewrite (Z.add_mod _ (len*8)) by auto; 
 repeat rewrite int_unsigned_mod in *.
 rewrite <- (Int.repr_unsigned hi).
 rewrite <- (Int.repr_unsigned lo).
 pose proof (Int.unsigned_repr_eq (Int.unsigned hi)).
 pose proof (Int.unsigned_repr_eq (Int.unsigned lo)).
 repeat rewrite Int.repr_unsigned in *.
 forget (Int.unsigned hi) as hi'; forget (Int.unsigned lo) as lo'; clear hi lo.
 rewrite H1, H2 in *.
 symmetry in H1,H2.
 rewrite H1 in *. rewrite H2 in *.
 rename hi' into hi; rename lo' into lo.
Local Open Scope Z.
 repeat rewrite <- Z.add_mod by auto.
 change 8 with (two_p 3) in *.
 change Int.modulus with (two_p 32) in *.
 replace (len/two_p 29) with (len * two_p 3 / two_p 32)
 by (change (two_p 32) with (two_p 29 * two_p 3);
       apply Z.div_mul_cancel_r;  (intro Hx; inv Hx)).
 assert (0 <= len * two_p 3 < two_p 35).
 split.
 apply Z.mul_nonneg_nonneg; [omega  | ]. compute; congruence.
 change (two_p 35) with (two_p 32 * two_p 3).
 apply Zmult_lt_compat_r; [compute; congruence | omega].
 clear H.
 forget (len * two_p 3) as N.
 clear len.
 remember (two_p 32) as M.
 assert (HM': 0 < M) by (subst M; compute; congruence).
 rewrite <- (Z.add_assoc (hi*M) lo N).
 rewrite (Z.div_mod (lo+N)) with M by auto.
 rewrite (Z.mul_comm M).
 rewrite Z.add_assoc.
 rewrite <- Z.mul_add_distr_r.
 f_equal.
2: symmetry; rewrite Z.add_mod by auto; rewrite H2; auto.
 f_equal.
 rewrite <- Z.add_assoc.
assert (forall a, (a - a mod M)/M = a/M). {
 intro.
 pose proof (Z.div_mod a M MN).
 replace (a - a mod M) with (M * (a/M)) by omega.
 rewrite Z.mul_comm.
 apply Z.div_mul; auto.
}
rewrite H.
assert (0 <= lo + N mod M).
rewrite <- H2.
pose proof (Z.mod_pos_bound lo M HM').
pose proof (Z.mod_pos_bound N M HM').
omega.
change 64 with (32+32) in BOUND.
rewrite two_p_is_exp in BOUND by omega.
rewrite <-  HeqM in BOUND.
assert (Blo:=Z.mod_pos_bound lo M HM'); rewrite H2 in Blo.
assert (Bhi:=Z.mod_pos_bound hi M HM'); rewrite H1 in Bhi.
assert (BN: 0 <= N/M) by (apply Z.div_pos; omega).
assert (Bx: 0 <= (lo + N mod M)/M) by (apply Z.div_pos; omega).
rewrite Z.mod_small.
Focus 2. {
split. omega.
apply Zmult_lt_reg_r with M; auto.
rewrite Z.mul_add_distr_r.
assert (((lo + N mod M) / M + N / M) * M <= lo+N); [ | omega].
rewrite Z.mul_add_distr_r.
rewrite (Z_div_mul N) by auto.
assert ((lo + N mod M) / M * M <= lo + N mod M); [  | omega].
rewrite (Z_div_mul (lo + N mod M)) by auto.
assert (0 <= (lo + N mod M) mod M)
 by (apply Z.mod_pos_bound; auto).
omega.
} Unfocus.
f_equal.
assert (((lo + N mod M) / M + N / M)*M = (lo + N) / M *M);
  [ | apply Z.mul_reg_r with M; auto].
rewrite Z.mul_add_distr_r.
repeat rewrite Z_div_mul by auto.
rewrite <- H2 at 2.
rewrite <- Z.add_mod by auto.
omega.
Qed.


