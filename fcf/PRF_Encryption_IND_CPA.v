

(* A simple symmetric encryption scheme based on a pseudorandom function, and a proof that the scheme is secure according to IND-CPA. *)

Set Implicit Arguments.

Require Import FCF.
Require Import PRF.
Require Import Encryption.

Opaque evalDist.
Opaque getSupport.

Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

Section PRF_Encryption_concrete.
  
  Variable eta : nat.
  
  Definition Key := Bvector eta.
  Definition Plaintext := Bvector eta.
  Definition Ciphertext := Bvector eta * Bvector eta.

  Variable f : Bvector eta -> Bvector eta -> Bvector eta.

  Definition PRFE_KeyGen := 
    {0, 1} ^ eta.
  
  Definition PRFE_Encrypt (k : Key )(p : Plaintext) :=
    r <-$ {0, 1} ^ eta;
    pad <- f k r;
    ret (r, p xor pad).
  
  Definition PRFE_Decrypt (k : Key)(c : Ciphertext) :=
    r <- fst c;
    pad <- f k r;
    (snd c) xor pad.
    
  Theorem PRF_Encrypt_correct : 
    forall k p c,
      In c (getSupport (PRFE_Encrypt k p)) ->
      PRFE_Decrypt k c = p.
    
    intuition.
    unfold PRFE_Encrypt, PRFE_Decrypt in *.
    repeat simp_in_support.

    simpl.
    rewrite BVxor_assoc.
    rewrite BVxor_same_id.
    rewrite BVxor_id_r.
    intuition.
  Qed.
  
  Section PRF_Encryption_IND_CPA_concrete.
  
    Variable State : Set.
    Hypothesis State_EqDec : EqDec State.
    Variable A1 : OracleComp Plaintext Ciphertext (Plaintext * Plaintext * State).
    Variable A2 : State -> Ciphertext -> OracleComp Plaintext Ciphertext bool.

    Hypothesis A1_wf : well_formed_oc A1.
    Hypothesis A2_wf : forall x y, well_formed_oc (A2 x y).

    Variable q1 q2 : nat.
    Hypothesis A1_qam : queries_at_most A1 q1.
    Hypothesis A2_qam : forall s c, queries_at_most (A2 s c) q2.
    
    Definition PRFE_EncryptOracle := EncryptOracle PRFE_Encrypt _.
    
    Local Open Scope nat_scope.

    (* Step 1: Inline some definitions and simplify. *)
    Definition G1 :=
      key <-$ PRFE_KeyGen;
      [b, _] <-$2
      (
        [p0, p1, s_A] <--$3 A1;
        b <--$$ {0, 1};
        pb <- if b then p1 else p0;
        c <--$$ PRFE_Encrypt key pb;
        b' <--$ (A2 s_A c);
        $ ret (eqb b b')
      )
      _ _
      (PRFE_EncryptOracle key) tt;
      ret b.

    Theorem G1_equiv : 
      Pr[IND_CPA_SecretKey_G PRFE_KeyGen PRFE_Encrypt A1 A2 _] == Pr[G1].
      reflexivity.
    
    Qed.

    (* Step 2 : Replace the PRF with a random function. *)

    Definition PRFE_RandomFunc := @randomFunc (Bvector eta) (Bvector eta) ({0,1}^eta) _.

    Definition RF_Encrypt s p :=
      r <-$ {0, 1} ^ eta;
      [pad, s] <-$2 PRFE_RandomFunc s r;
      ret (r, p xor pad, s).
    
    Definition G2 :=
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      [p0, p1, s_A] <-3 a;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        [c, o] <-$2 RF_Encrypt o pb;
        [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
        ret (eqb b b').


    (* To prove this step, we put the game in the form of a computation that access the PRF as an oracle.  This allows us to apply the PRF definition. *)

    Definition PRFE_Encrypt_OC (x : unit)(p : Plaintext) : OracleComp (Bvector eta) (Bvector eta) (Ciphertext * unit) :=
        r <--$$ {0, 1} ^ eta;
        pad <--$ OC_Query _ r;
        $ (ret (r, p xor pad, tt)).

    Definition PRF_A : OracleComp (Bvector eta) (Bvector eta) bool :=
      [a, n] <--$2 OC_Run _ _ _ A1 PRFE_Encrypt_OC tt;
      [p0, p1, s_A] <-3 a;
      b <--$$ {0, 1};
      pb <- if b then p1 else p0;
      r <--$$ {0, 1} ^ eta;
      pad <--$ OC_Query _ r;
      c <- (r, pb xor pad);
      z <--$ OC_Run  _ _ _ (A2 s_A c) PRFE_Encrypt_OC n;
      [b', _] <-2 z;
      $ ret (eqb b b').

    (* Later we will need to reason about the cost of PRF_A, so we make an equivalent procedure without some of the complications. *)
    Definition PRF_A' :=
      z <--$
      OC_Run _ _ _ A1 PRFE_Encrypt_OC tt;
      b <--$$
      (m <-$ { 0 , 1 }^1; ret Vector.hd m);
      r <--$$ { 0 , 1 }^eta;
      pad <--$ OC_Query (Vector.t bool eta) r;
      z0 <--$
      OC_Run _ _ _ (A2 (snd (fst z)) (r, 
        (if b then  (snd (fst (fst z)))  else (fst (fst (fst z))))
        xor pad)) PRFE_Encrypt_OC (snd z);
       $ ret eqb b (fst z0).

    Theorem PRF_A'_equiv :
      forall (S : Set)(eqds : EqDec S)(o : S -> (Bvector eta) -> Comp ((Bvector eta) * S)) s x, 
      evalDist (PRF_A _ _ o s) x == evalDist (PRF_A' _ _ o s) x.

      intuition.
      unfold PRF_A, PRF_A'.

      do 5 (comp_simp; simpl;
      comp_skip; try eapply eqRat_refl).
      comp_simp; simpl.
      comp_simp.
      intuition.

    Qed.

    Definition f_oracle(k : Bvector eta)(x : unit)(v : Bvector eta) :=
      ret (f k v, tt).
   
    Theorem Ciphertext_inh : 
      Ciphertext.

      apply (oneVector eta, oneVector eta).

    Qed.
    Hint Resolve Ciphertext_inh : inhabited.

    Theorem PRFE_EncryptOracle_spec : forall a x2 x,
       comp_spec
     (fun (y1 : Ciphertext * unit) (y2 : Ciphertext * (unit * unit)) =>
      fst y1 = fst y2 /\ snd y1 = fst (snd y2))
     (PRFE_EncryptOracle x (fst x2) a)
     (p <-$
      (PRFE_Encrypt_OC (fst x2) a) unit unit_EqDec (f_oracle x) (snd x2);
      ret (fst (fst p), (snd (fst p), snd p))).

      intuition.
      unfold PRFE_EncryptOracle, EncryptOracle, PRFE_Encrypt.
      simpl.

      prog_inline_l.
      do 2 prog_inline_r.
      comp_skip.
      prog_simp.
      unfold f_oracle.
      do 2 (prog_inline_r;
      prog_simp).
      eapply comp_spec_ret.
      simpl.
      intuition.
      
    Qed.

    Theorem RF_EncryptOracle_spec : forall a x2,
      comp_spec
      (fun (y1 : Ciphertext * list (Bvector eta * Bvector eta))
        (y2 : Ciphertext * (unit * list (Bvector eta * Bvector eta))) =>
        fst y1 = fst y2 /\ snd y1 = snd (snd y2)) (RF_Encrypt (snd x2) a)
      (p <-$
        (PRFE_Encrypt_OC (fst x2) a) (list (Bvector eta * Bvector eta))
        (list_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta)))
        PRFE_RandomFunc (snd x2); ret (fst (fst p), (snd (fst p), snd p))).
      
      intuition.
      unfold RF_Encrypt, PRFE_RandomFunc, randomFunc.
      simpl.
      do 2 prog_inline_r.
      comp_skip.
      prog_simp.
      prog_inline_r.
      comp_skip.
      prog_inline_r.
      prog_simp.
      eapply comp_spec_ret.
      simpl.
      intuition.
      
    Qed.
      
    Theorem G1_PRF_A_equiv : 
      Pr[G1] == Pr[k <-$ {0, 1}^ eta; [b, _] <-$2 PRF_A _ _ (f_oracle k) tt; ret b].

      Opaque PRFE_Encrypt_OC.

      unfold G1, PRF_A, PRFE_KeyGen.
      comp_skip.

      simpl.
      inline_first.
          
      eapply comp_spec_impl_eq.
      eapply (@comp_spec_seq _ _ 
        (fun a1 a2 => fst a1 = fst a2 /\ snd a1 = fst (snd a2))); eauto with inhabited.
      
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => a = fst b)).
      trivial.
      intuition.
      subst.

      eapply PRFE_EncryptOracle_spec.
      intuition.
      destruct b2.
      simpl in *.
      subst.
      
      prog_simp.
      simpl.
     
      do 2 prog_inline_l.
      do 2 prog_inline_r.
      comp_skip.
      prog_simp.

      unfold PRFE_Encrypt.
      do 3 prog_inline_l.
      do 2 (prog_inline_r; prog_simp).
      comp_skip.
      prog_simp.
    
      unfold f_oracle.
      prog_inline_l.
      do 3 (prog_inline_r; prog_simp).
      
      eapply comp_spec_seq; eauto with inhabited.
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        (fun a b => a = fst b)).
      trivial.
      intuition.
      subst.
      
      eapply PRFE_EncryptOracle_spec.
      intuition.
      destruct b4; simpl in *; subst.
      
      prog_simp.
      simpl.
      prog_inline_l; prog_simp.
      prog_inline_r; prog_simp.
      eapply comp_spec_ret.
      intuition.
      
    Qed.

    Theorem G1_PRF_A'_equiv : 
      Pr[k <-$ {0, 1}^ eta; [b, _] <-$2 PRF_A _ _ (f_oracle k) tt; ret b] ==
      Pr[k <-$ {0, 1}^ eta; [b, _] <-$2 PRF_A' _ _ (f_oracle k) tt; ret b].

      intuition.
      comp_skip.
      comp_skip.
      eapply PRF_A'_equiv.

    Qed.

    Theorem G2_PRF_A_equiv : 
      Pr[G2] == Pr[[b, _] <-$2 PRF_A _ _ PRFE_RandomFunc nil; ret b].
      
      unfold G2, PRF_A.
      simpl.
      inline_first.
      
      eapply comp_spec_impl_eq.
      eapply (@comp_spec_seq _ _ 
        (fun a1 a2 => fst a1 = fst a2 /\ snd a1 = snd (snd a2))); eauto with inhabited.
      
      eapply comp_spec_consequence.
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => a = snd b)).
      trivial.
      intuition.
      subst.
      
      eapply RF_EncryptOracle_spec.
      intuition.
      intuition.
      prog_simp.
      simpl.
      
      do 2 prog_inline_r.
      comp_skip.
      unfold RF_Encrypt at 1.
      prog_simp.
      prog_inline_l.
      do 2 prog_inline_r.
      comp_skip.
      prog_simp.
      simpl in *.
      subst.
      
      prog_inline_l.
      prog_inline_r.
      comp_skip.
      inversion H3; clear H3; subst.
      do 2 prog_inline_r.
      eapply comp_spec_seq; eauto with inhabited.
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x y => x = snd y)).
      trivial.
      intuition.
      subst.
      
      eapply RF_EncryptOracle_spec.
      intuition.
      prog_simp.
      simpl.
      prog_inline_r.
      simpl.
      prog_simp.
      eapply comp_spec_ret.
      simpl in *.
      intuition.
      subst.
      intuition.
      subst; intuition.

    Qed.

    Theorem G2_PRF_A'_equiv : 
      Pr[[b, _] <-$2 PRF_A _ _ PRFE_RandomFunc nil; ret b] ==
      Pr[[b, _] <-$2 PRF_A' _ _ PRFE_RandomFunc nil; ret b].

      intuition.
      comp_skip.
      eapply PRF_A'_equiv.

    Qed.
      
    Theorem G1_G2_close : |Pr[G1] - Pr[G2]| == PRF_Advantage ({0, 1}^eta) ({0, 1}^eta) f _ _ PRF_A'.
      rewrite G1_PRF_A_equiv.
      rewrite G1_PRF_A'_equiv.
      rewrite G2_PRF_A_equiv.
      rewrite G2_PRF_A'_equiv.
      reflexivity.
    Qed.


    (* Step 3 : replace the PRF output with random value *)
    (* This is identical to G2 as long as the adversary does not encounter the encryption nonce during a query. *)

    Definition G3 :=
    [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
    [p0, p1, s_A] <-3 a;
    b <-$ {0, 1};
    pb <- if b then p1 else p0;
      r <-$ {0, 1}^eta;
      pad <-$ {0, 1}^eta;
      c <- (r, pb xor pad);
      [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
      ret (eqb b b').

    (* start with G2 and move the challenge encryption sampling to the front. *)
    Definition G2_1 :=
      r <-$ {0, 1}^eta;
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      [p0, p1, s_A] <-3 a;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        [pad, o] <-$2 PRFE_RandomFunc o r;
        c <- (r, pb xor pad);
        [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
        ret (eqb b b').

    Theorem G2_1_equiv : 
      Pr[G2] == Pr[G2_1].

      unfold G2, G2_1.

      do 2 (comp_swap_r; comp_skip; comp_simp).
      unfold RF_Encrypt.
      do 2(inline_first; comp_skip; comp_simp).
      intuition.
    Qed.

    (* We will modify the procedure one adversary call at a time.  Start with the first one. *)
    (* make the bad event visible. *)
    Definition G2_2 :=
      r <-$ {0, 1}^eta;
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      bad <- if (arrayLookup _ o r) then true else false;
      [p0, p1, s_A] <-3 a;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        [pad, o] <-$2 PRFE_RandomFunc o r;
        c <- (r, pb xor pad);
        [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
        ret (eqb b b', bad).

    Theorem G2_1_2_equiv : 
      Pr[G2_1] == Pr[x <-$ G2_2; ret fst x].

      unfold G2_1, G2_2.

      do 5 (inline_first; comp_skip; comp_simp).
      simpl; intuition.
    Qed.

    (* When r is not in the domain of the random function, we can sample the pad randomly, then add it to the function. *)
    
    Definition G2_3 :=
      r <-$ {0, 1}^eta;
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      bad <- if (arrayLookup _ o r) then true else false;
      [p0, p1, s_A] <-3 a;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        pad <-$ {0, 1}^ eta;
        c <- (r, pb xor pad);
        [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt ((r, pad) :: o);
        ret (eqb b b', bad).

    Local Open Scope rat_scope.

    Theorem RF_Encrypt_wf : 
      forall s a,
        well_formed_comp (RF_Encrypt s a).
      
      intuition.
      unfold RF_Encrypt.
      wftac.
      eapply randomFunc_wf.
      wftac.
    Qed.

    Hint Resolve RF_Encrypt_wf : wftac.

      
    Theorem G2_2_3_eq_until_bad : 
      forall z,
        evalDist G2_2 (z, false) == evalDist G2_3 (z, false).

      intuition.
      unfold G2_2, G2_3.

      do 3 (comp_skip; comp_simp).
      unfold PRFE_RandomFunc, randomFunc.
      case_eq (arrayLookup (Bvector_EqDec eta) l x ); intuition.
      comp_simp.

      comp_irr_r; wftac.

      comp_irr_l; wftac. 
      eapply oc_comp_wf; intuition.

      comp_irr_r; wftac.
      eapply oc_comp_wf; intuition.

      comp_simp.

      Transparent evalDist.
      Transparent getSupport.
      dist_compute.

      inline_first.
      comp_skip.

    Qed.

    Theorem G2_2_3_badness_same : 
      Pr[x <-$ G2_2; ret (snd x)] == Pr[x <-$ G2_3; ret (snd x)].

      unfold G2_2, G2_3.
      
      do 3 (inline_first; comp_skip; comp_simp).
    
      comp_inline_l.
      comp_irr_l; wftac.
      eapply randomFunc_wf; wftac.

      comp_inline_r.
      comp_irr_r; wftac.
      
      comp_simp.
      comp_inline_l.
      comp_irr_l; wftac.
      eapply oc_comp_wf; intuition.

      comp_inline_r.
      comp_irr_r; wftac.
      eapply oc_comp_wf; intuition.

      comp_simp.
      simpl.
      intuition.

    Qed.

    (* provide a simplified form of the same with the same probability of badness. *)
    Definition G2_2_bad :=
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      ls <- fst (split o);
      r <-$ {0, 1}^eta;
      ret if (in_dec (EqDec_dec _) r ls) then true else false.

    Theorem arrayLookup_In_split : 
      forall (A B : Set)(eqda : EqDec A)(ls : list (A * B))(a : A)(b : B),
        arrayLookup _ ls a = Some b ->
        In a (fst (split ls)).
      
      induction ls; intuition; simpl in *.
      discriminate.
      case_eq (eqb a a0); intuition.
      rewrite H0 in H.
      inversion H; clear H; subst.
      
      rewrite eqb_leibniz in H0.
      subst.
      remember (split ls) as x.
      destruct x.
      simpl.
      intuition.
      
      rewrite H0 in H.
      remember (split ls) as x.
      destruct x.
      simpl.
      right.
      eapply IHls.
      eauto.
      
    Qed.

    Theorem arrayLookup_not_In_split : 
      forall (A B : Set)(eqda : EqDec A)(ls : list (A * B))(a : A),
        arrayLookup _ ls a = None ->
        ~In a (fst (split ls)).
      
      induction ls; intuition; simpl in *.
      case_eq (eqb a a0); intuition;
      rewrite H1 in H.
      discriminate.

      remember (split ls) as x.
      destruct x.
      simpl in *.
      intuition; subst.
      rewrite eqb_refl in H1.
      discriminate.
      eauto.
    Qed.
    
    Theorem G2_2_bad_equiv : 
      Pr[x <-$ G2_2; ret snd x] == Pr[G2_2_bad].

      rewrite G2_2_3_badness_same.

      unfold G2_3, G2_2_bad.
      inline_first.
      comp_at comp_inline leftc 1%nat.
      comp_swap_l.
      comp_skip.
      comp_simp.
      comp_skip.
      do 3 (comp_inline_l;
      comp_irr_l; wftac).
      eapply oc_comp_wf; intuition.

      comp_simp.
      eapply evalDist_ret_eq; simpl.
      case_eq (arrayLookup (Bvector_EqDec eta) l x); intuition;
      destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x (fst (split l))); intuition.
      exfalso.
      eauto using arrayLookup_In_split.

      exfalso.
      eapply (@arrayLookup_not_In_split _ _ (Bvector_EqDec eta)).
      eauto.
      trivial.
      
    Qed.

    Require Import RndInList.

    Theorem G2_2_bad_small : Pr[x <-$ G2_2; ret snd x] <= q1 / (2 ^ eta).

      rewrite G2_2_bad_equiv.
      unfold G2_2_bad.
      comp_irr_l.
      eapply oc_comp_wf; intuition.
      comp_simp.
     
      Theorem RF_Encrypt_length_incr : 
        forall a b c d,
          In (a, b) (getSupport (RF_Encrypt c d)) ->
          (length b <= 1 + length c)%nat.

        intuition.
        unfold RF_Encrypt in *.
        repeat simp_in_support.
        destruct x0.
        repeat simp_in_support.
        unfold PRFE_RandomFunc, randomFunc in *.
        destruct (arrayLookup (Bvector_EqDec eta) c x); repeat simp_in_support;
        simpl in *; omega.

      Qed.

      
      assert (length l <= q1)%nat.
      eapply qam_count;
      eauto.
      eapply RF_Encrypt_length_incr.
      simpl; intuition.

      eapply RndInList_prob.
      rewrite split_length_l.
      trivial.
    Qed.

    Theorem G2_2_3_close : 
      forall z, 
      | evalDist (x <-$ G2_2; ret fst x) z - evalDist (x <-$ G2_3; ret fst x) z | <=
         q1 / (2 ^ eta).

      intuition.
      eapply leRat_trans.
      eapply fundamental_lemma_h.
      eapply G2_2_3_badness_same.
      eapply G2_2_3_eq_until_bad.
      eapply G2_2_bad_small.
    Qed.    

    (* Now switch the the second adversary call *)
    
    (* for this part we need an oracle that makes the bad event visible *)
    Definition RF_Encrypt_bad (x : Bvector eta)(z : list (Bvector eta * Bvector eta) * bool) (p : Bvector eta):=
      [s, bad] <-2 z;
      r <-$ { 0 , 1 }^eta;
      z <-$ PRFE_RandomFunc s r; 
      [pad, s0]<-2 z; 
      ret (r, p xor pad, (s0, bad || eqb x r)).

    Definition G2_4 :=
      r <-$ {0, 1}^eta;
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      [p0, p1, s_A] <-3 a;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        pad <-$ {0, 1}^ eta;
        c <- (r, pb xor pad);
        [b', o] <-$2 (A2 s_A c) _ _ (RF_Encrypt_bad r) ((r, pad) :: o, false);
        ret (eqb b b', (snd o)).

    Theorem G2_3_4_equiv : 
      Pr[x <-$ G2_3; ret fst x] == Pr[x <-$ G2_4; ret fst x].

      unfold G2_3, G2_4.
      
       do 4 (inline_first; comp_skip; comp_simp).

      inline_first.
      eapply comp_spec_impl_eq.
      eapply comp_spec_seq; eauto with inhabited.
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => a = fst b)); intuition.
      destruct x3; simpl in *; subst.
      unfold RF_Encrypt.
      clear H2.
      comp_skip.
      comp_skip.
      eapply comp_spec_ret; simpl in *; intuition.

      intuition.
      simpl in *; subst.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
    Qed.

     (* When this procedure doesn't go bad, we can remove the challenge pad from the function. *)
    Definition G2_5 :=
      r <-$ {0, 1}^eta;
      [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
      [p0, p1, s_A] <-3 a;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        pad <-$ {0, 1}^ eta;
        c <- (r, pb xor pad);
        [b', o] <-$2 (A2 s_A c) _ _ (RF_Encrypt_bad r) (o, false);
        ret (eqb b b', snd o).

    Theorem RF_Encrypt_bad_preserved : 
      forall a c d e f g h,
        In (a, (c, d)) (getSupport (RF_Encrypt_bad e (f, g) h)) ->
        g = true ->
        d = true.
      
      intuition.
      unfold RF_Encrypt_bad in *.
      repeat simp_in_support.
      destruct x0.
      repeat simp_in_support.
      eapply orb_true_l.
      
    Qed.

    Theorem G2_4_5_eq_until_bad : 
      forall z,
        evalDist G2_4 (z, false) == evalDist G2_5 (z, false).

      intuition.
      unfold G2_4, G2_5.
      do 4 (comp_skip; comp_simp).

      eapply comp_spec_impl_eq.
      eapply comp_spec_seq; eauto with inhabited.
      eapply (@oc_comp_spec_eq_until_bad _ _ _ _ _ _ _ _ _ _ _ _ _ 
        (fun a => snd a) (fun a => snd a)
        (fun a b => forall z,  z <> x -> arrayLookup _ (fst a) z = arrayLookup _ (fst b) z)).

      Theorem RF_Encrypt_bad_wf : 
        forall x a b, 
          well_formed_comp (RF_Encrypt_bad x a b).

        intuition.
        unfold RF_Encrypt_bad; wftac.
        eapply randomFunc_wf; wftac.
     
      Qed.

      intuition.
      apply RF_Encrypt_bad_wf.
      intuition.
      apply RF_Encrypt_bad_wf.
    
      (* Prove that as long as the procedures don't go bad, the invariant holds *)
      intuition.
      simpl in H5; subst.
      
      (* TODO: mako this a theorem *)
      unfold RF_Encrypt_bad, PRFE_RandomFunc, randomFunc.
      comp_skip.
      case_eq (eqb x b); intuition.
   
      prog_irr_l.
      destruct (arrayLookup (Bvector_EqDec eta) a b); wftac.
      prog_irr_r.
      destruct (arrayLookup (Bvector_EqDec eta) a0 b); wftac.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
      rewrite orb_true_r in H10.
      discriminate.
      rewrite orb_true_r in H10.
      discriminate.

      case_eq (arrayLookup (Bvector_EqDec eta) a b); intuition.
      rewrite <- H4.
      simpl.
      rewrite H8.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
      intuition; subst.
      rewrite eqb_refl in H7.
      discriminate.

      rewrite <- H4.
      simpl.
      rewrite H8.
      prog_inline_l.
      prog_inline_r.
      comp_skip.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
      case_eq (eqbBvector z0 b); intuition.
      intuition. subst.
      rewrite eqb_refl in H7.
      discriminate.
      intuition.

      (* Prove that once the oracle goes bad, it stays bad. *)
      eapply RF_Encrypt_bad_preserved.
      eapply H5.
      trivial.

      intuition.
      eapply RF_Encrypt_bad_preserved.
      eapply H5.
      trivial.

      (* prove that the invariant holds on the initial state *)
      intuition.
      simpl.
      case_eq (eqbBvector z0 x); intuition.
      apply eqbBvector_sound in H5; intuition.

      (* prove that the bad events are the same *)
      trivial.
      
      intuition.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intros.
      destruct p1; simpl in *; subst.
      intuition.
      inversion H6; clear H6; subst.
      intuition.
      subst.
      trivial.
      inversion H6; clear H6; subst.
      intuition.
      subst.
      trivial.

      Grab Existential Variables.
      eauto.
    Qed.
    
    Theorem G2_4_5_badness_same : 
      Pr[x <-$ G2_4; ret (snd x)] == Pr[x <-$ G2_5; ret (snd x)].

      unfold G2_4, G2_5.
      do 4 (inline_first; comp_skip; comp_simp).
      inline_first.

      inline_first.

      eapply comp_spec_impl_eq.
      eapply comp_spec_seq; eauto with inhabited.
      
      eapply (@oc_comp_spec_eq_until_bad _ _ _ _ _ _ _ _ _ _ _ _ _ 
        (fun a => snd a) (fun a => snd a)
        (fun a b => forall z,  z <> x -> arrayLookup _ (fst a) z = arrayLookup _ (fst b) z)).
      intuition.
      eapply RF_Encrypt_bad_wf.
      intuition.
      eapply RF_Encrypt_bad_wf.

      intuition.
      simpl in *; subst.
      clear H2.
      comp_skip.
      (* The theorem from before would be helpful here *)
      unfold PRFE_RandomFunc, randomFunc.
      case_eq (eqbBvector x b); intuition.

      prog_irr_l.
      destruct (arrayLookup (Bvector_EqDec eta) a b); wftac.
      prog_irr_r.
      destruct ( arrayLookup (Bvector_EqDec eta) a0 b); wftac.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
      rewrite orb_true_r in H9.
      discriminate.
      rewrite orb_true_r in H9.
      discriminate.
      
      case_eq (arrayLookup (Bvector_EqDec eta) a b); intuition.
      rewrite <- H4.
      rewrite H7.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
      intuition; subst.
      rewrite eqbBvector_complete in H6.
      discriminate.
      rewrite <- H4.
      rewrite H7.
      prog_inline_l.
      prog_inline_r.
      comp_skip.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
      case_eq (eqbBvector z b); intuition.
      intuition; subst.
      rewrite eqbBvector_complete in H6.
      discriminate.

      intros.
      destruct c.
      destruct b.
      eapply RF_Encrypt_bad_preserved .
      eauto.
      trivial.

      intros.
      destruct c.
      destruct b.
      eapply RF_Encrypt_bad_preserved .
      eauto.
      trivial.

      intuition.
      simpl.
      case_eq ( eqbBvector z x); intuition.
      apply eqbBvector_sound in H5; intuition.
      
      trivial.

      intuition.
      prog_simp.
      clear H2.
      eapply comp_spec_ret; simpl in *; intuition.
      subst.
      trivial.
      destruct p1; simpl in *.
      subst; intuition.

      Grab Existential Variables.
      eauto.
    Qed.
    
    Theorem G2_4_bad_small : Pr[x <-$ G2_4; ret snd x] <= q2 / (2 ^ eta).
      
      unfold G2_4.
      inline_first;
      comp_irr_l; wftac.
      inline_first;
      comp_irr_l; wftac.
      eapply oc_comp_wf; intuition.
      comp_simp.
      dist_inline_l.
      comp_irr_l; wftac.
      comp_inline_l; comp_irr_l; wftac.
      comp_inline_l.
      
      assert ( Pr 
   [a <-$
    (A2 s (x, (if x0 then p0 else p) xor x1))
      (list (Bvector eta * Bvector eta) * bool)%type
      (pair_EqDec
         (list_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta)))
         bool_EqDec) (RF_Encrypt_bad x) ((x, x1) :: l, false);
    x2 <-$ ([b', o]<-2 a; ret (eqb x0 b', snd o)); ret snd x2 ]  ==
    Pr 
   [a <-$
    (A2 s (x, (if x0 then p0 else p) xor x1))
      (list (Bvector eta * Bvector eta) * bool)%type
      (pair_EqDec
         (list_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta)))
         bool_EqDec) (RF_Encrypt_bad x) ((x, x1) :: l, false);
   ret (snd (snd a))] ).

      comp_skip.
      comp_simp.
      simpl.
      intuition.
      rewrite H4.
      clear H4.
      
      eapply leRat_trans.

      eapply RndInAdaptive_prob; eauto.

      Theorem RF_Encrypt_bad_prob : 
        forall x (a : list (Bvector eta * Bvector eta)) (b : Plaintext),
          (Pr  [d <-$ RF_Encrypt_bad x (a, false) b; ret snd (snd d) ] <= 1 / (2 ^ eta))%rat.

        intuition.
        unfold RF_Encrypt_bad.
        
        assert ( Pr 
   [d <-$
    (r <-$ { 0 , 1 }^eta;
     z <-$ PRFE_RandomFunc a r;
     [pad, s0]<-2 z; ret (r, b xor pad, (s0, false || eqb x r)));
    ret snd (snd d) ] ==
    Pr 
   [r <-$ { 0 , 1 }^eta;
     ret eqb x r] ).

        inline_first.
        comp_skip.
        inline_first.
        comp_irr_l.
        eapply randomFunc_wf; wftac.
        comp_simp.
        simpl; intuition.

        rewrite H. clear H.
        (* dist_compute isn't working for some reason *)
        simpl.
        rewrite (@sumList_exactly_one _ x).
        rewrite eqbBvector_complete.
        destruct (EqDec_dec bool_EqDec true true ); intuition.
        rewrite ratMult_1_r.
        eapply leRat_refl.
        eapply getAllBvectors_NoDup.
        eapply in_getAllBvectors.
        intuition.
        destruct ( EqDec_dec bool_EqDec (eqbBvector x b0) true); intuition.
        apply eqbBvector_sound in e; subst; intuition.
        eapply ratMult_0_r.
      Qed.
      
      intros.
      destruct a.
      simpl in H4; subst.
      eapply RF_Encrypt_bad_prob.

      intuition.
      eapply RF_Encrypt_bad_preserved.
      eauto.
      trivial.

      eapply eqRat_impl_leRat.
      rewrite <- ratMult_num_den.
      eapply eqRat_terms.
      omega.
      unfold posnatMult, natToPosnat, posnatToNat.
      omega.
    Qed.

    Theorem G2_4_5_close : 
      forall z, 
      | evalDist (x <-$ G2_4; ret fst x) z - evalDist (x <-$ G2_5; ret fst x) z | <=
        q2 / (2 ^ eta).

      intuition.
      eapply leRat_trans.
      eapply fundamental_lemma_h.
      eapply G2_4_5_badness_same.
      eapply G2_4_5_eq_until_bad.
      eapply G2_4_bad_small.
    Qed.

    Theorem G2_5_G3_equiv :
      Pr[x <-$ G2_5; ret fst x] == Pr[G3].

      unfold G2_5, G3.
      intuition.
      inline_first.
      comp_at comp_inline leftc 1%nat.
      comp_swap_l.
      comp_skip.
      comp_simp.
      comp_swap_r.
      comp_skip.
      comp_inline_l.
      comp_skip.
      inline_first; comp_skip.
      inline_first.
      eapply comp_spec_impl_eq.
      eapply comp_spec_seq; eauto with inhabited.
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => fst a = b)); intuition.
      simpl in *; subst.
      unfold RF_Encrypt.
      comp_skip.
      comp_skip.
      eapply comp_spec_ret; simpl in *; intuition.
      
      intuition.
      simpl in *; subst.
      prog_simp.
      eapply comp_spec_ret; simpl in *; intuition.
  
    Qed.    
  
   Theorem G2_G3_close : 
    | Pr[G2] - Pr[G3] | <= q1 / (2 ^ eta) + q2 / (2 ^ eta).

     rewrite G2_1_equiv.
     rewrite G2_1_2_equiv.
     eapply ratDistance_le_trans.
     eapply G2_2_3_close.
     rewrite G2_3_4_equiv.
     rewrite <- G2_5_G3_equiv.
     eapply G2_4_5_close.
   Qed.

   (* Step 4 : apply one-time pad argument to replace ciphertext with random values *)
   Require Import OTP.

   Definition G4 :=
    [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
    [p0, p1, s_A] <-3 a;
    b <-$ {0, 1};
    pb <- if b then p1 else p0;
      r <-$ {0, 1}^eta;
      pad <-$ {0, 1}^eta;
      c <- (r, pad);
      [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
      ret (eqb b b').

    (* Put the game into the form expected by the argument. *)
    Definition G3_1 :=
    [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
    [p0, p1, s_A] <-3 a;
    b <-$ {0, 1};
    pb <- if b then p1 else p0;
      r <-$ {0, 1}^eta;
      pad <-$ (x <-$ {0, 1}^eta; ret (pb xor x));
      c <- (r, pad);
      [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
      ret (eqb b b').

    Theorem G3_G3_1_equiv:
      Pr[G3] == Pr[G3_1].

      unfold G3, G3_1. 

      repeat (comp_simp;
        inline_first;
        comp_skip).
    Qed.

    Theorem G3_1_G4_equiv:
      Pr[G3_1] == Pr[G4].

      unfold G3_1, G4.
      do 4 (comp_skip;
      comp_simp).
      apply xor_OTP_eq.
      reflexivity.
    Qed.

    Theorem G3_G4_equiv : 
      Pr[G3] == Pr[G4].

      rewrite G3_G3_1_equiv.
      eapply G3_1_G4_equiv.

    Qed.

    (* Step 5: Move the coin toss to the end to produce a game that that the adversary obviously wins with probability 1/2. *)
    Definition G5 :=
    [a, o] <-$2 A1 _ _ (RF_Encrypt) nil;
    [p0, p1, s_A] <-3 a;
    r <-$ {0, 1}^eta;
    pad <-$ {0, 1}^eta;
    c <- (r, pad);
    [b', o] <-$2 (A2 s_A c) _ _ RF_Encrypt o;
    b <-$ {0, 1};
    ret (eqb b b').

    Theorem G4_G5_equiv : 
      Pr[G4] == Pr[G5].

      unfold G4, G5.
      do 3 (comp_skip; comp_simp; comp_swap_l).
      comp_skip; comp_simp.
      reflexivity.
    Qed.

    (* Show that the probability of the adversary winning G5 is 1/2 *)
    Theorem G5_one_half : 
      Pr[G5] == 1/2.

      unfold G5.
      
      comp_irr_l.
      eapply oc_comp_wf; intuition.
 
      comp_simp.
      
      do 3 (comp_irr_l; wftac).
      eapply oc_comp_wf; intuition.

      comp_simp.
      
      Transparent evalDist.
      Transparent getSupport.

      dist_compute.

      Opaque evalDist.
      Opaque getSupport.
      
    Qed.

    Theorem PRFE_IND_CPA_concrete : 
      IND_CPA_SecretKey_Advantage PRFE_KeyGen PRFE_Encrypt A1 A2 _ <=
      PRF_Advantage ({0, 1}^eta) ({0, 1}^eta) f _ _ PRF_A' +
      (q1 / 2^eta + q2 / 2^eta).

      unfold IND_CPA_SecretKey_Advantage.
      rewrite G1_equiv.      
      eapply ratDistance_le_trans.
      eapply eqRat_impl_leRat.
      eapply G1_G2_close.

      eapply leRat_trans.
      eapply ratDistance_le_trans.
      eapply G2_G3_close.
      eapply eqRat_impl_leRat.
      rewrite <- ratIdentityIndiscernables.
      rewrite G3_G4_equiv.
      rewrite G4_G5_equiv.
      eapply G5_one_half.
      eapply eqRat_impl_leRat.
      symmetry.
      eapply ratAdd_0_r.
    Qed.
    
    (* Concrete cost of executing the constructed adversary *)
    Require Import WC_PolyTime.
    Context `{function_cost_model}.
    Local Open Scope nat_scope.

    Variable A1_cost : nat -> nat.
    Hypothesis A1_cost_correct : oc_cost cost (comp_cost cost) A1 A1_cost.
    Variable A2_cost_1 : nat.
    Hypothesis A2_cost_1_correct : cost (fun p => A2 (fst p) (snd p)) A2_cost_1.
    Variable A2_cost_2 : nat -> nat.
    Hypothesis A2_cost_correct : forall x y, oc_cost cost (comp_cost cost) (A2 x y) A2_cost_2.
  
    Theorem PRF_A'_cost : 
      oc_cost cost (comp_cost cost) PRF_A' 
       (fun x => (A1_cost (x + (5 * eta))) + (A2_cost_2 (x + (5 * eta))) + 
        x + 5 * A2_cost_1 + 6 + 7 * eta).

      unfold PRF_A'.

      eapply oc_cost_le.

      costtac.
      eauto.

      Theorem PRFE_Encrypt_OC_cost_1 : 
        cost PRFE_Encrypt_OC 0.

        Transparent PRFE_Encrypt_OC.
        unfold PRFE_Encrypt_OC.
        eapply cost_const.     
      Qed.

      Theorem PRFE_Encrypt_OC_cost_2 : 
        forall x, cost (PRFE_Encrypt_OC x) (2 * eta).

        intuition.
        Transparent PRFE_Encrypt_OC.
        unfold PRFE_Encrypt_OC.
        eapply cost_le.
        eapply cost_compose_binary; costtac.
        eapply cost_uncurry_1.
        eapply cost_compose_binary; costtac.
        eapply cost_uncurry_1.
        eapply cost_compose_unary; costtac.
        eapply cost_compose_unary; costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_uncurry_1.
        eapply cost_BVxor.
        intuition.
        eapply cost_uncurry_2.
        eapply cost_BVxor.

        omega.
       
      Qed.

      Theorem PRFE_Encrypt_OC_oc_cost : 
         forall (x : unit) (y : Bvector eta),
           oc_cost cost (comp_cost cost) (PRFE_Encrypt_OC x y) (fun x => x + 3*eta).

        intuition.
        eapply oc_cost_le.
        unfold PRFE_Encrypt_OC.
        costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_uncurry_1.
        eapply cost_compose_unary; costtac.
        eapply cost_compose_unary; costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_uncurry_2.
        eapply cost_BVxor.
        intuition.
        costtac.

        eapply cost_compose_unary; costtac.
        eapply cost_compose_unary; costtac.
        eapply cost_compose_binary; costtac.
        eapply cost_uncurry_2.
        eapply cost_BVxor.
        eapply cost_pair_2.
        intuition.
        costtac.

        intuition.
      Qed.
      
      eapply PRFE_Encrypt_OC_cost_1.
      eapply PRFE_Encrypt_OC_cost_2.
      eapply PRFE_Encrypt_OC_oc_cost.
      
      costtac.
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_compose_binary; costtac.

      eapply (@cost_compose _ _ _ _ _ 
        (fun a => (snd (fst (fst (fst a)))))
        (fun (a : Plaintext * Plaintext * State * unit * bool * Bvector eta *
            Vector.t bool eta) => (OC_Run
        unit_EqDec
        (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta)
        (A2 (snd (fst (fst (fst (fst a)))))
           (snd (fst a),
           (if snd (fst (fst a))
            then snd (fst (fst (fst (fst (fst a)))))
            else fst (fst (fst (fst (fst (fst a)))))) xor 
           snd a)) 
        PRFE_Encrypt_OC ))
        ); costtac.
      

      eapply (@cost_compose_unary _ _ _ _ _ 
        (fun a : (Plaintext * Plaintext * State * unit * bool * Bvector eta *
            Vector.t bool eta) => (A2 (snd (fst (fst (fst (fst a)))))
           (snd (fst a),
           (if snd (fst (fst a))
            then snd (fst (fst (fst (fst (fst a)))))
            else fst (fst (fst (fst (fst (fst a)))))) xor 
           snd a)))

        (fun x => 
           OC_Run unit_EqDec
        (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta) x PRFE_Encrypt_OC)
        ).
      
      eapply cost_compose_binary; costtac.
      eapply cost_compose_binary; costtac.
      eapply cost_compose_binary; costtac.
      eapply cost_if_bool; costtac.
      eapply cost_uncurry_1.
      eapply cost_BVxor.
      eapply cost_uncurry_2.
      eapply cost_BVxor.

      eapply cost_uncurry_1.
      eauto.
      eapply cost_uncurry_2.
      eauto.

      eapply (@cost_compose _ _ _ _ _ 
        (fun x => _)
        ( OC_Run unit_EqDec
        (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta))
        ); costtac.

      eapply cost_OC_Run_1.
      intuition.
      eapply cost_OC_Run_2.
      intuition.
      eapply cost_OC_Run_3.

      eapply cost_uncurry_1.
      eapply cost_compose_unary; costtac.
      eapply cost_compose_binary; costtac.

      eapply cost_uncurry_1.
      eapply cost_eqb_bool.
      eapply cost_uncurry_2.
      eapply cost_eqb_bool.

      intuition.
      costtac.
      eapply cost_vec_head.
      intuition.
      costtac.
      
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_compose_binary; costtac.
      simpl.
      

      eapply (@cost_compose _ _ _ _ _ 
        (fun a => _)
        (fun a0 : bool * Bvector eta * Vector.t bool eta =>
      OC_Run unit_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta)
        (A2 b0 (snd (fst a0), (if fst (fst a0) then b1 else a) xor snd a0))
        PRFE_Encrypt_OC)

        ); costtac.
      
      eapply (@cost_compose _ _ _ _ _ 
        (fun a => _)
        (fun a0 : bool * Bvector eta * Vector.t bool eta =>
      OC_Run unit_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta)
        (A2 b0 (snd (fst a0), (if fst (fst a0) then b1 else a) xor snd a0)))

        ); costtac.
      
      eapply cost_compose_binary; costtac.
      eapply cost_compose_binary; costtac.
      eapply cost_if_bool; costtac.
      eapply cost_uncurry_1.
      eapply cost_BVxor.
      intuition.
      eapply cost_uncurry_2.
      eapply cost_BVxor.
      eapply cost_uncurry_2.
      eauto.
      eapply cost_OC_Run_1.
      intuition.
      eapply cost_OC_Run_2.
      intuition.
      eapply cost_OC_Run_3.
      eapply cost_uncurry_1.
      eapply cost_compose_unary; costtac.
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_eqb_bool.
      intuition.
      eapply cost_uncurry_2.
      eapply cost_eqb_bool.

      intuition.
      costtac.
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_1.
      eapply cost_compose_binary; costtac.
      simpl.
      
      eapply (@cost_compose _ _ _ _ _ 
        (fun a => _)
        (fun a0 : Bvector eta * Vector.t bool eta =>
      OC_Run unit_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta)
        (A2 b0 (fst a0, (if y then b1 else a) xor snd a0)) PRFE_Encrypt_OC)
        ); costtac.
      
      eapply (@cost_compose _ _ _ _ _ 
        (fun a => _)
        (fun a0 : Bvector eta * Vector.t bool eta =>
      OC_Run unit_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta)
        (A2 b0 (fst a0, (if y then b1 else a) xor snd a0)))
        ); costtac.
      
      eapply cost_compose_binary; costtac.
      eapply cost_uncurry_2.
      eapply cost_BVxor.
      eapply cost_uncurry_2.
      eauto.
      eapply cost_OC_Run_1.
      intuition.
      eapply cost_OC_Run_2.
      intuition.
      eapply cost_OC_Run_3.

      intuition.
      costtac.
      eapply cost_compose_binary; costtac.
      simpl.
      eapply (@cost_compose _ _ _  _ _ 
        (fun a => _)
         (fun a0 : Vector.t bool eta =>
      OC_Run unit_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta) (A2 b0 (y0, (if y then b1 else a) xor a0))
        PRFE_Encrypt_OC)
        ); costtac.
      
      eapply (@cost_compose _ _ _  _ _ 
        (fun a => _)
         (fun a0 : Vector.t bool eta =>
      OC_Run unit_EqDec (pair_EqDec (Bvector_EqDec eta) (Bvector_EqDec eta))
        (Bvector_EqDec eta) (A2 b0 (y0, (if y then b1 else a) xor a0))
        )
        ); costtac.

      eapply cost_uncurry_2.
      eapply cost_BVxor.
      eapply cost_pair_2.
      eapply cost_uncurry_2.
      eauto.
      eapply cost_OC_Run_1.
      intuition.
      eapply cost_OC_Run_2.
      intuition.
      eapply cost_OC_Run_3.
      intuition.
      costtac.
      simpl.
      eauto.
      
      eapply PRFE_Encrypt_OC_cost_1.
      eapply PRFE_Encrypt_OC_cost_2.
      eapply PRFE_Encrypt_OC_oc_cost.

      eapply cost_uncurry_2.
      eapply cost_eqb_bool.
      
      intuition.
      costtac.

      intuition.

      simpl.
      repeat rewrite plus_0_r.

      (* omega can't handle the functions -- remove them *)
      assert (A1_cost (eta + eta + (x + (eta + (eta + eta)))) =
        A1_cost (x + (eta + (eta + (eta + (eta + eta)))))).
      f_equal; omega.
      rewrite H0.
      clear H0.
      remember ( A1_cost (x + (eta + (eta + (eta + (eta + eta)))))) as t1.
      assert (A2_cost_2 (eta + eta + (x + (eta + (eta + eta)))) = 
        A2_cost_2 (x + (eta + (eta + (eta + (eta + eta)))))).
      f_equal; omega.
      rewrite H0.
      clear H0.
      remember (A2_cost_2 (x + (eta + (eta + (eta + (eta + eta)))))) as t2.
      omega.
    Qed.
      
  End PRF_Encryption_IND_CPA_concrete.

End PRF_Encryption_concrete.

Require Import Asymptotic.

Section PRF_Encryption.

  Context `{function_cost_model}.

  Local Open Scope nat_scope.
  
  Variable f : forall n, Bvector n -> Bvector n -> Bvector n.

  Section PRF_Encryption_IND_CPA.

    Variable State : nat -> Set.
    Variable A1 : forall n, OracleComp (Plaintext n) (Ciphertext n) (Plaintext n * Plaintext n * State n).
    Variable A2 : forall n, State n -> Ciphertext n -> OracleComp (Plaintext n) (Ciphertext n) bool.

    Hypothesis A1_admissible : 
      admissible_oc cost _ _ _ A1.

    Hypothesis A2_admissible : 
      admissible_oc_func_2 cost _ _ _ _ _ A2.

    Theorem PRFE_Encrypt_OC_poly_time : 
      poly_time_nonuniform_oc_func_2 cost _ _ _ _ _ PRFE_Encrypt_OC.

      unfold poly_time_nonuniform_oc_func_2.
      exists (fun x o => o + 3*x).
      exists (fun x => 2 * x).
      intuition.

      eapply polynomial_plus; intuition.
      eapply polynomial_mult.
      eapply polynomial_const.
      eapply polynomial_ident.

      eapply polynomial_mult.
      eapply polynomial_const.
      eapply polynomial_ident.

      eapply cost_le.
      eapply cost_curry.
      eapply (PRFE_Encrypt_OC_cost_1 n).
      eapply (@PRFE_Encrypt_OC_cost_2 n); eauto.
      omega.

      eapply PRFE_Encrypt_OC_oc_cost; intuition.

    Qed.

    Theorem PRFE_Encrypt_wf : 
       forall n x (y : Bvector n), well_formed_oc (PRFE_Encrypt_OC x y).

      intuition.
      econstructor.
      econstructor.
      wftac.
      intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      wftac.

    Qed.

    Theorem PRF_A'_wf : 
      forall n, well_formed_oc (PRF_A' (A1 n) (@A2 n)).

      intuition.
      econstructor.
      econstructor.
      eapply A1_admissible.
      eapply PRFE_Encrypt_wf.
      intuition.
      econstructor.
      econstructor.
      wftac.
      intuition.
      econstructor.
      econstructor.
      wftac.
      intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      econstructor.
      simpl.
      eapply A2_admissible.
      intuition.
      eapply PRFE_Encrypt_wf.
      intuition.
      econstructor.
      wftac.

    Qed.
  
    Theorem PRF_A'_poly_time : 
      poly_time_nonuniform_oc cost _ _ _ (fun n => PRF_A' (A1 n) (@A2 n)).

      intuition.
      unfold PRF_A'.
      unfold poly_time_nonuniform_oc.

      destruct (PRFE_Encrypt_OC_poly_time).
      destruct H0.
      unfold admissible_oc in *.
      unfold admissible_oc_func_2 in *.
      intuition.
      destruct H0.
      destruct H2.
      destruct H2.
      intuition.

      exists (fun x o : nat =>
     x1 x (o + 5 * x) + x2 x (o + 5 * x) + o + 5 * (x3 x) + 6 +
     7 * x).

      intuition.
      eapply polynomial_plus.
      eapply polynomial_plus.
      eapply polynomial_plus.
      eapply polynomial_plus.
      eapply polynomial_plus.
      eapply H6.
      eapply polynomial_plus; intuition.
      eapply polynomial_mult.
      eapply polynomial_const.
      eapply polynomial_ident.
      eapply H0.
      eapply polynomial_plus; intuition.
      eapply polynomial_mult.
      eapply polynomial_const.
      eapply polynomial_ident.
      intuition.
      eapply polynomial_mult.
      eapply polynomial_const.
      intuition.
      eapply polynomial_const.
      eapply polynomial_mult.
      eapply polynomial_const.
      eapply polynomial_ident.

      eapply oc_cost_le.
      eapply PRF_A'_cost;
      eauto.
      eapply H12.
      intuition.
      eapply H12.
      intuition.
     
    Qed.

    Theorem PRF_A'_poly_queries : 
      polynomial_queries_oc _ _ _ 
      (fun n  => PRF_A' (A1 n) (@A2 n)).

      unfold admissible_oc, admissible_oc_func_2 in *.
      intuition.
      destruct H5.
      destruct H6.
      intuition.
      exists (fun n => x n + (1 + x0 n)).
      intuition.
      eapply polynomial_plus; intuition.
      eapply polynomial_plus; intuition.
      eapply polynomial_const.

      eapply qam_le.
      econstructor.
      econstructor.
      eauto.
      intuition.

      Theorem PRFE_Encrypt_OC_qam : 
        forall n x (y : Bvector n), queries_at_most (PRFE_Encrypt_OC x y) 1.

        intuition.
        unfold PRFE_Encrypt_OC.
        econstructor.
        econstructor.
        econstructor.
        intuition.
        econstructor.
        econstructor.
        intuition.
        econstructor.

        omega.

      Qed.

      eapply PRFE_Encrypt_OC_qam.
      
      intuition.
      econstructor.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      econstructor.
      econstructor.
      eapply H8.
      eapply le_refl.
      eapply le_refl.
      intuition.
      eapply PRFE_Encrypt_OC_qam.
      intuition.
      econstructor.

      omega.

    Qed.
    
    Theorem PRF_A'_admissible : 
      admissible_oc cost _ _ _ (fun n => PRF_A' (A1 n) (@A2 n)).

      unfold admissible_oc.
      intuition.
      eapply PRF_A'_wf.
      eapply PRF_A'_poly_time.
      eapply PRF_A'_poly_queries.
      
    Qed.

  End PRF_Encryption_IND_CPA. 

      
  Theorem PRFE_IND_CPA : 
    PRF _ _ _ Rnd Rnd f _ _ (admissible_oc cost) -> 
    IND_CPA_SecretKey (fun n => pair_EqDec (Bvector_EqDec n) (Bvector_EqDec n))
    PRFE_KeyGen (fun n => PRFE_Encrypt (@f n))
    (admissible_oc cost)
    (admissible_oc_func_2 cost).

    unfold IND_CPA_SecretKey.
    intuition.

    destruct H1.
    destruct H2.
    intuition.
    unfold polynomial_queries_oc, polynomial_queries_oc_func_2 in *.
    destruct H7.
    destruct H8.
    intuition.

    eapply negligible_le.
    intuition.
    eapply PRFE_IND_CPA_concrete.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    eapply negligible_plus.
    eapply H0.
    apply PRF_A'_admissible; eauto.

    unfold admissible_oc; intuition.
    econstructor; eauto.
    unfold admissible_oc_func_2; intuition.
    econstructor; eauto.

    eapply negligible_plus.
    eapply negligible_poly_num; intuition.
    eapply negligible_poly_num; intuition.
  Qed.

  Print Assumptions PRFE_IND_CPA.

End PRF_Encryption.



