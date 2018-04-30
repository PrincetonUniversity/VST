Require Import VST.floyd.proofauto.
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

Lemma eqm_mod1:
  forall a b, Int.eqm a b <-> Int.eqm (a mod Int.modulus) b.
Proof.
intros.
split; intros [x ?]; hnf.
rewrite H; clear H.
rewrite Z.add_mod by (compute; congruence).
rewrite Z.mod_mul by  (compute; congruence).
rewrite Z.add_0_l.
rewrite Z.mod_mod by (compute; congruence).
rewrite Zmod_eq by (compute; congruence).
exists (- (b / Int.modulus)).
rewrite Z.mul_opp_l. omega.
rewrite (Zmod_eq a) in H by (compute; congruence).
replace a with (a / Int.modulus * Int.modulus + x * Int.modulus + b) by omega.
rewrite <- Z.mul_add_distr_r.
econstructor; reflexivity.
Qed.

Lemma eqm_mod2:
  forall a b, Int.eqm a b <-> Int.eqm a (b mod Int.modulus).
Proof.
intros.
split; intro; apply Int.eqm_sym.
apply -> eqm_mod1. apply Int.eqm_sym; auto.
apply <- eqm_mod1. apply Int.eqm_sym; auto.
Qed.

Lemma addlength_assist:
 forall (a b : Z),
Int.eqm
  (((a / Int.modulus) mod Int.modulus +
    (a mod Int.modulus + b mod Int.modulus -
     (a mod Int.modulus + b) mod Int.modulus) / Int.modulus) mod Int.modulus +
   (b / Int.modulus) mod Int.modulus) ((a + b) / Int.modulus).
Proof.
intros.
assert (HM' : 0 < Int.modulus) by (compute; congruence).
assert  (MN : Int.modulus <> 0) by omega.
Local Notation "'N'" := Int.modulus (at level 0).
apply <- eqm_mod1.
rewrite <- Z.add_mod by auto.
eapply Int.eqm_trans.
rewrite <- eqm_mod1.
eapply Int.eqm_add; [ | apply Int.eqm_refl].
eapply Int.eqm_add; [ | apply Int.eqm_refl].
rewrite <- eqm_mod1.
apply Int.eqm_refl.
rewrite <- (Z.add_comm (b/_)).
rewrite Z.add_assoc.
rewrite (Z.add_comm (b/_)).
rewrite (Z.add_mod (a mod N)) by auto.
rewrite Z.mod_mod by auto.
rewrite <- Z.add_mod by auto.
apply Int.eqm_trans with ((a/N*N + a mod N + b/N*N + b mod N)/N);
 [ |
   repeat rewrite <- (Z.mul_comm N);
   rewrite <- (Z.div_mod a N) by auto;
   rewrite <- Z.add_assoc;
   rewrite <- (Z.div_mod b N) by auto;
   apply Int.eqm_refl].
apply Int.eqm_trans with
   ((a/N*N + (b/N*N + (a mod N + b mod N))) / N);
  [ | apply Int.eqm_refl2; f_equal; clear; omega].
 rewrite Z.div_add_l by auto.
 rewrite Z.div_add_l by auto.
 rewrite Z.add_assoc.
 apply Int.eqm_add. apply Int.eqm_refl.
 apply Int.eqm_refl2.
assert (N | a mod N + b mod N - (a + b) mod N). {
 assert (Int.eqm (a mod N + b mod N) ((a+b) mod N)).
 apply -> eqm_mod2.
 apply Int.eqm_add. apply -> eqm_mod1; apply Int.eqm_refl.
 apply -> eqm_mod1; apply Int.eqm_refl.
 destruct H.
 rewrite H. exists x; omega.
}
destruct H as [x ?].
 rewrite H.
 rewrite Z.div_mul by auto.
 assert (a mod N + b mod N = x * N + (a+b) mod N) by omega.
 rewrite H0.
 rewrite Z.div_add_l by auto.
 rewrite Z.div_small.
 omega.
 apply Z.mod_pos_bound; auto.
Qed.

 Lemma addlength_aux2:
     forall len n,
          0 <= len < Int.modulus ->
          Int.unsigned (Int.repr (n + len * 8)) < Int.unsigned (lo_part n) ->
Int.unsigned (hi_part n) +
  (Int.unsigned (lo_part n) + (len * 8) mod Int.modulus -
   (Int.unsigned (lo_part n) + len * 8) mod Int.modulus) / Int.modulus
   = Int.unsigned (hi_part n) + 1.
Proof.
intros.
assert (MN: Int.modulus <> 0) by (intro Hx; inv Hx).
rename H0 into H1.

 assert (Int.unsigned (Int.add (lo_part n) (Int.repr (len * 8))) <
     Int.unsigned (lo_part n)) by normalize.
 clear H1.
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
 reflexivity.
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
rename H1 into Hn.
assert (MN: Int.modulus <> 0) by (intro Hx; inv Hx).
forward. (* cNl=c->Nl; *)
forward. (* cNh=c->Nh; *)
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
pose (carry := ((Int.unsigned (lo_part n) + (len * 8) mod Int.modulus)
                        -  (Int.unsigned (lo_part n) + len * 8) mod Int.modulus)/Int.modulus).
forward_if (temp _cNh (Vint (Int.repr (Int.unsigned (hi_part n) + carry)))).
* (* then-clause *)
 rewrite <- add_repr in H1.
 rewrite Int.repr_unsigned in H1.
 forward. (* cNh ++; *)
 entailer!.
 rewrite <- (Int.repr_unsigned (hi_part n)) at 2.
 rewrite add_repr.
 f_equal.
 f_equal.
 apply addlength_aux2; auto.
* (* else clause *)
 rewrite <- add_repr in H1.
 rewrite Int.repr_unsigned in H1.
 forward.  (* skip; *)
 entailer!.
 subst carry.
 f_equal.
 clear - MN H1 H.
 assert (H0: Int.unsigned (Int.add (lo_part n) (Int.repr (len * 8))) >=
     Int.unsigned (lo_part n)) by normalize.
 clear H1.
 destruct (Int.unsigned_add_either (lo_part n) (Int.repr (len*8))) as [H9|H9];
  [ | destruct (Int.unsigned_range (Int.repr (len*8))); omega].
 clear H0.
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
 subst carry.
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
 clear H.
 apply Int.eqm_samerepr.
apply addlength_assist; auto.
Qed.
