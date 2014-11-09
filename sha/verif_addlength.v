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
rename H into BOUND.
assert (Hn: 0 <= n) by admit.  (* add this to spec *)
(*revert POSTCONDITION; subst n; intro.*)
assert (MN: Int.modulus <> 0) by (intro Hx; inv Hx).
forward.
forward.
forward. (* l=(cNl+(((SHA_LONG)len)<<3))&0xffffffffUL; *)
assert (0 <= len < Int.modulus) 
 by (change Int.modulus with (Int.max_unsigned + 1); omega).
replace (Int.and
              (Int.add (lo_part n) (Int.shl (Int.repr len) (Int.repr 3)))
              (Int.repr (-1)))
 with (Int.repr (Int.unsigned (lo_part n)+len*8))
 by (unfold lo_part;
    rewrite Int.and_mone, Int.shl_mul_two_p, mul_repr, <- add_repr,
    Int.repr_unsigned; reflexivity).
fold (temp _l (Vint (Int.repr (Int.unsigned (lo_part n) + len * 8)))).
fold (temp _cNh (Vint (hi_part n))).
fold (temp _cNl (Vint (lo_part n))).
pose (carry := ((Int.unsigned (lo_part n) + (len * 8) mod Int.modulus)
                        -  (Int.unsigned (lo_part n) + len * 8) mod Int.modulus)/Int.modulus).
forward_if (
   PROP  ()
   LOCAL  (temp _l (Vint (Int.repr (Int.unsigned (lo_part n) + len * 8)));
     temp _cNh (Vint (Int.repr (Int.unsigned (hi_part n) + carry)));
     temp _cNl (Vint (lo_part n)); temp _len (Vint (Int.repr len));
     temp _c c)
   SEP  (`(field_at Tsh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part n)) c);
   `(field_at Tsh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part n)) c))).
* (* then-clause *)
 forward.
 entailer!.
 rewrite <- (Int.repr_unsigned (hi_part n)) at 2.
 rewrite add_repr.
 f_equal.
 f_equal.
 unfold carry.
 unfold Int.ltu in H1.
 rewrite <- add_repr in H1.
 rewrite Int.repr_unsigned in H1.
 if_tac in H1; [clear H1 | discriminate].
  
 clear - MN H2 H. rename H2 into H0.
 destruct (Int.unsigned_add_either (lo_part n) (Int.repr (len*8))) as [H9|H9].
 elimtype False; rewrite H9 in H0; clear H9.
 destruct (Int.unsigned_range (Int.repr (len*8))) as [? _]; omega.
 clear H0.
 unfold Int.add in H9.
 rewrite (Int.unsigned_repr_eq (len*8)) in H9.
 replace (Int.unsigned (lo_part n) + (len * 8) mod Int.modulus)
  with (Int.unsigned (Int.repr (Int.unsigned (lo_part n) + (len * 8) mod Int.modulus)) +
           Int.modulus) by omega.
 clear - MN.
 rewrite Int.unsigned_repr_eq.
 rewrite (Z.add_mod (Int.unsigned (lo_part n)) (len*8)) by assumption.
 rewrite int_unsigned_mod.
 replace ((Int.unsigned (lo_part n) + (len * 8) mod Int.modulus) mod Int.modulus + Int.modulus -
 (Int.unsigned (lo_part n) + (len * 8) mod Int.modulus) mod Int.modulus)
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
 destruct (Int.unsigned_add_either (lo_part n) (Int.repr (len*8))) as [H9|H9];
  [ | destruct (Int.unsigned_range (Int.repr (len*8))); omega].
 clear H1.
 rewrite <- (Int.repr_unsigned (lo_part n)) in H9 at 1.
 rewrite add_repr in H9.
 rewrite Int.unsigned_repr_eq in H9 .
 rewrite (Int.unsigned_repr_eq (_ * _)) in H9.
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
 unfold carry; clear carry.
 clear - MN BOUND H Hn.
 apply derives_refl'; f_equal.
 + f_equal. f_equal.
    unfold lo_part.
    apply Int.eqm_samerepr.
    apply Int.eqm_add.
    apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
    apply Int.eqm_refl.
 + f_equal. f_equal.
     unfold hi_part.
  rename Hn into Hn'; 
    assert (Hn: 0 <= n < two_p 64) by omega;
   clear Hn'.
 rewrite Int.shru_div_two_p.
 change (Int.unsigned (Int.repr 29)) with 29.
 assert (Int.max_unsigned + 1 = Int.modulus) by reflexivity.
 rewrite (Int.unsigned_repr len) by omega.
 unfold Int.add.
 repeat rewrite Int.unsigned_repr_eq.
 rewrite (Z.add_mod _ (len*8)) by auto; 
 repeat rewrite int_unsigned_mod in *.
(* rewrite <- (Int.repr_unsigned hi).
 rewrite <- (Int.repr_unsigned lo).
 pose proof (Int.unsigned_repr_eq (Int.unsigned hi)).
 pose proof (Int.unsigned_repr_eq (Int.unsigned lo)).
*)
 repeat rewrite <- Z.add_mod by auto.
 change 8 with (two_p 3) in *.
 change Int.modulus with (two_p 32) in *.
Local Open Scope Z.
replace (len/two_p 29) with (len * two_p 3 / two_p 32)
 by (change (two_p 32) with (two_p 29 * two_p 3);
       apply Z.div_mul_cancel_r;  (intro Hx; inv Hx)).
 assert (0 <= len * two_p 3 < two_p 35).
 split.
 apply Z.mul_nonneg_nonneg; [omega  | ]. compute; congruence.
 change (two_p 35) with (two_p 32 * two_p 3).
 apply Zmult_lt_compat_r; [compute; congruence | omega].
 f_equal.
 clear H.
 forget (len * two_p 3) as N.
 change (two_p 64) with (two_p 32 * two_p 32) in BOUND, Hn.
 change (two_p 35) with (two_p 32 * two_p 3) in H1.
 assert (Hzz: 0 <= N < two_p 32 * two_p 32). {
   destruct H1; split; auto.
   eapply Z.lt_trans; try apply H1.
   compute; auto.
 }   
 remember (two_p 32) as M.
 assert (HM': 0 < M) by (subst M; compute; congruence). 
(*
 assert (0 <= n/M < M)
 by (split; [apply Z.div_pos; omega 
         | apply Zmult_gt_0_lt_reg_r with M; try omega;
           rewrite Z_div_mul by auto;
           pose proof (Z.mod_pos_bound n M HM'); omega]).
 rewrite (Z.mod_small (n/M)) by omega.
 set (hi := n/M).
 set (lo := n mod M).
 

(hi + (lo + N mod M - (lo + N mod M) mod M) / M + N / M) mod M * M +
(lo + N mod M) mod M = hi * M + lo + N
*)


 rename n into a. rename N into b.
 clear len.
 clear - MN HM' Hn BOUND Hzz Hn.
 rewrite (Z.add_mod (a mod M) b) by auto.
 repeat rewrite Z.mod_mod by auto.
 rewrite <- Z.add_mod by auto.
 assert (0 <= a/M < M)
 by (split; [apply Z.div_pos; omega 
         | apply Zmult_gt_0_lt_reg_r with M; try omega;
           rewrite Z_div_mul by auto;
           pose proof (Z.mod_pos_bound a M HM'); omega]).
 assert (0 <= b/M < M)
 by (split; [apply Z.div_pos; omega 
         | apply Zmult_gt_0_lt_reg_r with M; try omega;
           rewrite Z_div_mul by auto;
           pose proof (Z.mod_pos_bound b M HM'); omega]).
 assert (0 <= (a+b)/M < M)
 by (split; [apply Z.div_pos; omega 
         | apply Zmult_gt_0_lt_reg_r with M; try omega;
           rewrite Z_div_mul by auto;
           pose proof (Z.mod_pos_bound (a+b) M HM'); omega]).
 rewrite (Z.mod_small (a/M)) by omega.
 rewrite (Z.mod_small (b/M)) by omega.
 symmetry.
 pattern a at 1; rewrite (Z.div_mod a M MN).
 pattern b at 1; rewrite (Z.div_mod b M MN).
 transitivity ((M * (a/M) + M * (b/M) + (a mod M + b mod M)) / M);
    [ f_equal; omega | ].
 rewrite <- Z.mul_add_distr_l.
 rewrite (Z.div_mod (a mod M + b mod M) M MN).
 rewrite Z.add_assoc.
 rewrite <- Z.mul_add_distr_l.
 rewrite (Z.mul_comm M).
rewrite Z.div_add_l by omega.
 rewrite <- Z.add_mod by auto.
rewrite Z.add_simpl_r.
 rewrite (Z.mul_comm M).
 rewrite Z_div_mult_full by auto.
 rewrite (Z.mod_small (_ + _/M)).
 rewrite (Z.div_small (_ mod M) M)
  by (apply Z.mod_pos_bound; auto).
 omega.
 split.
 apply Z.add_nonneg_nonneg; apply Z.div_pos; auto; try omega.
 apply Z.add_nonneg_nonneg; apply Z.mod_pos_bound; auto.
(*
assert (a mod M + b mod M = (a+b) mod M + (a mod M + b mod M)/M*M).
 rewrite (Z.add_mod); auto.
 pattern (a mod M + b mod M) at 1;
 rewrite (Z.div_mod _ M) by auto.
 rewrite Z.mul_comm. omega.
 rewrite H2. clear H2.
 *)
 admit.
Qed.


