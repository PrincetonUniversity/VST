(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

(*Add LoadPath "../FCF".*)

Require Import fcf.FCF.
Require Import fcf.PRF.
Require Import hmacfcf.splitVector.

Require Import hmacfcf.HMAC_spec.

Section RelatedKeyAttack.

  Variable K D R Phi_s : Set.
  Variable K_EqDec : EqDec K.
  Variable D_EqDec : EqDec D.
  Variable R_EqDec : EqDec R.
  Variable RndK : Comp K.
  Variable RndR : Comp R.
  Variable f : K -> D -> R.
  Variable Phi : Phi_s -> K -> K.

  Variable A : OracleComp (Phi_s * D) R bool.

  Definition RKA_F k (s : unit) p :=
    [phi_s, x] <-2 p; ret (f (Phi phi_s k) x, tt).

  Definition RKA_randomFunc := @randomFunc (K * D) R RndR _.

  Definition RKA_R k s p :=
    [phi_s, x] <-2 p; (RKA_randomFunc s (Phi phi_s k, x)).

  Definition RKA_G0 :=
    k <-$ RndK;
    [b, _] <-$2 A _ _ (RKA_F k) tt;
    ret b.


  Definition RKA_G1 :=
    k <-$ RndK;
    [b, _] <-$2 A _ _ (RKA_R k) nil;
    ret b.

  Definition RKA_Advantage :=
    | Pr[RKA_G0] - Pr[RKA_G1] |.

End RelatedKeyAttack.

Definition dual_f (A B C : Set)(f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Section NMAC_to_HMAC.

  Variable c p : nat.
  Definition b := @b c p.

  Variable h : Bvector c -> Bvector b -> Bvector c.
  Variable iv : Bvector c.
  Variable fpad : Bvector c -> Bvector p.

  Definition GHMAC_2K := GHMAC_2K h iv fpad.
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC := GHMAC h iv fpad opad ipad.

  Variable A : OracleComp (list (Bvector b)) (Bvector c) bool.

  Definition app_fpad := @app_fpad c p fpad.
  Definition h_star := h_star p h.

  Definition GNMAC := GNMAC h fpad.

  Definition A_NMAC :=
    x <-$ {0, 1}^(c + c);
    [b, _] <-$2 A _ _ (f_oracle GNMAC _ x) tt;
    ret b.

  Definition A_HMAC :=
    x <-$ {0, 1}^b;
    [b, _] <-$2 A _ _ (f_oracle GHMAC _ x) tt;
    ret b.

  Theorem GHMAC_2K_GNMAC_equiv :
    forall k ls,
      let (k_Out, k_In) := splitVector b b k in
        let k' := Vector.append (h iv k_Out) (h iv k_In) in
      GHMAC_2K k ls = GNMAC k' ls.

    intuition.
    unfold GHMAC_2K, HMAC_spec.GHMAC_2K, GNMAC, HMAC_spec.GNMAC, b, HMAC_spec.b.
    remember (splitVector (c + p) (c + p) k) as z.
    destruct z.
    rewrite splitVector_append.
    unfold app_fpad, hash_words.
    simpl.
    trivial.

  Qed.

  Definition HMAC_RKA_A : OracleComp (Bvector b * Bvector c) (Bvector c) bool :=
    k_Out <--$ OC_Query _ (opad, iv);
    k_In <--$ OC_Query _ (ipad, iv);
    [b, _] <--$2 $ A _ _ (f_oracle GNMAC _ (Vector.append k_Out k_In)) tt;
    $ ret b.

  Local Opaque evalDist.

  Theorem A_HMAC_RKA_equiv :
    Pr[A_HMAC] == Pr[RKA_G0 _ (Rnd b) (dual_f h) (BVxor b) HMAC_RKA_A].

    unfold A_HMAC, RKA_G0, GHMAC,  HMAC_RKA_A, GNMAC, HMAC_spec.GHMAC.
    comp_skip.

    simpl.
    repeat ( inline_first; comp_simp).
    comp_skip.
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_consequence.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => a = b)).
    trivial.
    intuition.
    unfold f_oracle.
    eapply comp_spec_ret; intuition.
    simpl.
    specialize (GHMAC_2K_GNMAC_equiv (Vector.append (x xor opad) (x xor ipad)) a0); intuition.
    rewrite splitVector_append in H1.
    unfold dual_f.
    eapply eq_trans.
    eapply H1.
    unfold GNMAC.
    f_equal.
    f_equal.
    f_equal.
    eapply BVxor_comm.
    f_equal.
    eapply BVxor_comm.

    intuition.
    destruct b2; simpl in *; subst; intuition.

    comp_simp.
    simpl.
    inline_first.
    comp_simp.
    intuition.
  Qed.

  Definition A_NMAC_G1 :=
    x1 <-$ {0, 1}^c;
    x2 <-$ {0, 1}^c;
    [b, _] <-$2 A _ _ (f_oracle GNMAC _ (Vector.append x1 x2)) tt;
    ret b.

  Definition A_NMAC_G1_0 :=
    [x1, x2] <-$2 (
    x <-$ {0, 1}^(c + c);
    ret (splitVector c c x));
    [b, _] <-$2 A _ _ (f_oracle GNMAC _ (Vector.append x1 x2)) tt;
    ret b.

  Definition A_NMAC_G1_1 :=
    [x1, x2] <-$2 (
    x1 <-$ {0, 1}^c;
    x2 <-$ {0, 1}^c;
    ret (x1, x2));
    [b, _] <-$2 A _ _ (f_oracle GNMAC _ (Vector.append x1 x2)) tt;
    ret b.

  Theorem A_NMAC_G1_0_equiv :
    Pr[A_NMAC] == Pr[A_NMAC_G1_0].

    unfold A_NMAC, A_NMAC_G1_0.
    inline_first.
    comp_skip.
    remember (splitVector c c x) as z.
    comp_simp.
    erewrite append_splitVector.
    reflexivity.
    trivial.
  Qed.

  Theorem A_NMAC_G1_0_1_equiv :
    Pr[A_NMAC_G1_0] == Pr[A_NMAC_G1_1].

    unfold A_NMAC_G1_0, A_NMAC_G1_1.
    comp_skip.
    eapply Rnd_split_equiv.
    reflexivity.

  Qed.

  Theorem  A_NMAC_G1_1_equiv :
    Pr[A_NMAC_G1_1] == Pr[A_NMAC_G1].

    unfold A_NMAC_G1_1, A_NMAC_G1.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.

  Qed.

  Theorem A_NMAC_G1_equiv :
    Pr[A_NMAC] == Pr[A_NMAC_G1].

    rewrite A_NMAC_G1_0_equiv.
    rewrite A_NMAC_G1_0_1_equiv.
    apply A_NMAC_G1_1_equiv.

  Qed.

    Theorem xor_1_1 :
      forall (n : nat)(x y z : Bvector n),
        BVxor _ y x = BVxor _ z x ->
        y = z.

      intuition.
      rewrite <- BVxor_id_r at 1.
      rewrite <- (BVxor_same_id x).
      rewrite <- BVxor_assoc.
      rewrite H.
      rewrite  BVxor_assoc.
      rewrite (BVxor_same_id x).
      rewrite BVxor_id_r.
      trivial.

    Qed.

  Theorem A_NMAC_RKA_equiv :
    Pr[A_NMAC] == Pr[RKA_G1 _ _ _ (Rnd b) (Rnd c) (BVxor b) HMAC_RKA_A].

    rewrite A_NMAC_G1_equiv .

    unfold A_NMAC_G1, RKA_G1, HMAC_RKA_A.
    comp_irr_r.
    wftac.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    unfold RKA_randomFunc, randomFunc.
    simpl.

    case_eq (
      @eqbPair (Bvector b) (Bvector c) (Bvector_EqDec b)
                 (Bvector_EqDec c)
                 (@pair (Bvector b) (Bvector c) (BVxor b ipad x) iv)
                 (@pair (Bvector b) (Bvector c) (BVxor b opad x) iv)
                 ); intuition.

    unfold eqbPair in *.
    simpl in *.
    apply andb_true_iff in H1.
    intuition.

    apply eqbBvector_sound in H2.

    exfalso.
    eapply opad_ne_ipad.
    eapply xor_1_1.
    eauto.

    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    inline_first.
    comp_simp.
    intuition.
  Qed.

  Theorem A_HMAC_NMAC_close :
    | Pr[A_HMAC] - Pr[A_NMAC] | <=
      RKA_Advantage _ _ _ (Rnd b) (Rnd c) (dual_f h) (BVxor b) HMAC_RKA_A.

    rewrite A_HMAC_RKA_equiv.
    rewrite A_NMAC_RKA_equiv.
    reflexivity.

  Qed.

End NMAC_to_HMAC.