Require Import VST.floyd.proofauto.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import sha.HMAC256_functional_prog.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import compcert.lib.Integers.
Require Import sha.general_lemmas. 
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.spec_hmac_drbg.

Lemma HMAC256_DRBG_reseed_algorithmWFaux d l y A B zz 
      (H: (A, B, zz) = HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_algorithm d l y):
      0 <= zz < Int.max_signed /\ Zlength A = 32.
Proof.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_algorithm, HMAC_DRBG_algorithms.HMAC_DRBG_reseed_algorithm in H.
  destruct d as [[? ?] ?]. 
  remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         (l ++ y) l1 l0) as q; destruct q. inv H. split. rep_omega.
  eapply spec_hmac_drbg_pure_lemmas.HMAC_DRBG_update_value; eassumption.
Qed.

Lemma HMAC256_DRBG_reseed_functionWFaux a b c s t x y A B zz C D ss 
      (H: ENTROPY.success (A, B, zz, C, D) ss =
        HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_function a b c s t x y):
      0 <= zz < Int.max_signed /\ Zlength A = 32.
Proof. unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_function, DRBG_functions.DRBG_reseed_function in H.
  destruct t. destruct p.
  remember ((x && negb b0)%bool) as bb; destruct bb; try discriminate.
  remember (Zlength y >? c) as cc; destruct cc; try discriminate.
  remember (get_entropy z a b x s) as dd. destruct dd; try discriminate. inv H.
  eapply HMAC256_DRBG_reseed_algorithmWFaux; eassumption.
Qed.

Lemma mbedtls_HMAC256_DRBG_reseed_functionWFaux a s data ss A B zz C D
      (H: mbedtls_HMAC256_DRBG_reseed_function s a data =
          ENTROPY.success (A, B, zz, C, D)  ss):
      0 <= zz < Int.max_signed /\ Zlength A = 32.
Proof. unfold mbedtls_HMAC256_DRBG_reseed_function in H.
  destruct a; symmetry in H. eapply HMAC256_DRBG_reseed_functionWFaux; eauto. Qed.


Lemma HMAC_DRBG_updateWF a b c d e:
      (d,e) = HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256 a b c ->
       Zlength e = 32.
Proof. unfold HMAC_DRBG_algorithms.HMAC_DRBG_update.
  destruct a; intros.
  + inv H. apply hmac_common_lemmas.HMAC_Zlength.
  + inversion H; clear H. rewrite hmac_common_lemmas.HMAC_Zlength; auto.
Qed.

Lemma false_zgt z a: false = (z >? a) -> z<=a. 
Proof. unfold Z.gtb.
  remember (z ?= a). destruct c. symmetry in Heqc; apply Z.compare_eq in Heqc. subst; intros. omega.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H in Heqc. omega.
  discriminate.
Qed. 

Lemma HMAC256_DRBG_generate_algorithmWF a v k rc n l bytes V K RC (N:n >=0)
      (A: 0<= a +1< Int.max_signed) (Rc: 0<=rc) 
      (H: DRBG_functions.generate_algorithm_success bytes (V, K, RC) =
          HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a (v,k,rc) n l):
      Zlength V = 32 /\ 0 <= RC < Int.max_signed.
Proof.
  unfold  HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm in H.
  unfold HMAC_DRBG_algorithms.HMAC_DRBG_generate_algorithm in H.
  remember (rc >? a) as q; destruct q; try discriminate.
  apply false_zgt in Heqq.
  destruct l.
  + rewrite HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z_equation in H.
    remember (0 >=? n). destruct b.
    - symmetry in Heqb; apply Z.geb_le in Heqb.
      assert (NN: n=0) by omega. subst n; clear N Heqb. simpl in H.
      inversion H; clear H. subst.
      split. apply hmac_common_lemmas.HMAC_Zlength. omega.
    - remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z
           HMAC256_functional_prog.HMAC256 k v (n - Z.of_nat 32)). 
      destruct p. 
      remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         [] k (HMAC256_functional_prog.HMAC256 l k)). 
      destruct p. inv H. 
      apply HMAC_DRBG_updateWF in Heqp0. destruct Heqp0.
      split; trivial. omega.
  + remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256 (i :: l) k v). 
    destruct p.
    rewrite HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z_equation in H.
    remember (0 >=? n) as b; destruct b.
    - symmetry in Heqb. apply Z.geb_le in Heqb.
      assert (NN: n=0) by omega. subst n; clear N Heqb.
      remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         (i :: l) l0 l1). 
      destruct p. inv H. apply HMAC_DRBG_updateWF in Heqp0. destruct Heqp0.
      split; trivial. omega.
    - remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z
           HMAC256_functional_prog.HMAC256 l0 l1 (n - Z.of_nat 32)).
      destruct p.
      remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         (i :: l) l0 (HMAC256_functional_prog.HMAC256 l2 l0)). 
      destruct p. inv H. apply HMAC_DRBG_updateWF in Heqp1. destruct Heqp1.
      split; trivial. omega.
Qed.

Lemma HMAC256_DRBG_generate_functionWF f a b c s v k rc d pr n e l V K RC z PR ss bytes
      (A: 0<= a+1 < Int.max_signed) (N: n>=0) (Rc: 0<=rc)
      (F: forall s d z b x y zz A B C D ss, ENTROPY.success (A, B, zz, C, D) ss = f s (d, z, b) x y -> 0<=zz)
      (H : ENTROPY.success (bytes, (V, K, RC, z, PR)) ss =
          HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_function f a b c s (v, k, rc, d, pr) n e pr l):
Zlength V = 32 /\ 0 <= RC < Int.max_signed.
Proof.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_function in H.
  unfold DRBG_functions.DRBG_generate_function in H.
  remember (n >? b) as q1; destruct q1; try discriminate.
  remember (e >? d) as q2; destruct q2; try discriminate.
  remember (Zlength l >? c) as q3; destruct q3; try discriminate.
  assert (P: (pr && negb pr)%bool = false). { destruct pr; trivial. }
  rewrite P in H; clear P.
  remember (DRBG_functions.DRBG_generate_function_helper
        (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a) f s
        (v, k, rc, d, pr) n pr l pr 1). 
  destruct r; try discriminate.
  destruct p. symmetry in H; inv H.
  unfold DRBG_functions.DRBG_generate_function_helper in Heqr.
  destruct PR.
  + remember (f s (v, k, rc, z, true) true l). 
    destruct r; try discriminate.
    destruct p. destruct p. apply false_zgt in Heqq1. apply false_zgt in Heqq2. apply false_zgt in Heqq3.
    remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a p n []).
    destruct d.
    * remember (f s0 (p, z0, b0) true [] ). 
      destruct r; try discriminate.
      destruct p0. destruct p0.
         remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a p0 n []).
         destruct d; try discriminate.
         symmetry in Heqr; inv Heqr. destruct p0 as [[XX yy] zz].
         apply HMAC256_DRBG_generate_algorithmWF in Heqd0; trivial.
         apply F in Heqr1; trivial.
    * symmetry in Heqr; inv Heqr.
      destruct p as [[? ?] ?]. apply HMAC256_DRBG_generate_algorithmWF in Heqd; trivial.
      apply F in Heqr0; trivial.
  + remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a
           (v, k, rc) n l).
    destruct d.
    - remember (f s (v, k, rc, z, false) false l). destruct r; try discriminate.
      destruct p. destruct p.
      remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a p n
           []).
      destruct d; try discriminate. symmetry in Heqr; inv Heqr.
      destruct p as [[? ?] ?]. apply HMAC256_DRBG_generate_algorithmWF in Heqd0; trivial.
      apply F in Heqr0; trivial.
    - symmetry in Heqr; inv Heqr. apply HMAC256_DRBG_generate_algorithmWF in Heqd; trivial.
Qed.


Lemma mbedtls_HMAC256_DRBG_generate_functionWF_success s k v rc el pr rsi n l bytes V K RC z PR ss
      (N: n>=0) (Rc: 0<=rc) (HRSI: 0 <= rsi+1 < Int.max_signed)
      (H: ENTROPY.success (bytes, (V, K, RC, z, PR)) ss =
        mbedtls_HMAC256_DRBG_generate_function s (HMAC256DRBGabs k v rc el pr rsi) n l):
Zlength V = 32 /\ 0 <= RC < Int.max_signed.
Proof. unfold  mbedtls_HMAC256_DRBG_generate_function, hmac256drbgabs_generate in H.
  apply HMAC256_DRBG_generate_functionWF in H; trivial.
  intros. eapply HMAC256_DRBG_reseed_functionWFaux; eassumption.
Qed.

Lemma hmac256drbgabs_generateWF I s n l K V RC el PR rsi (N:n>=0)
      (HI: Zlength (hmac256drbgabs_value I) = 32 /\ 
           0 <= hmac256drbgabs_reseed_counter I < Int.max_signed)
      (HRSI: 0 <= rsi +1< Int.max_signed)
      (G: hmac256drbgabs_generate I s n l = HMAC256DRBGabs K V RC el PR rsi):
      Zlength V = 32 /\ 0 <= RC < Int.max_signed.
Proof. unfold hmac256drbgabs_generate in G. destruct I; simpl in HI.
  remember ( mbedtls_HMAC256_DRBG_generate_function s
        (HMAC256DRBGabs key V0 reseed_counter entropy_len
           prediction_resistance reseed_interval) n l). 
  destruct r.
  + destruct p. destruct d. destruct p. destruct d. destruct p.
    inv G. apply mbedtls_HMAC256_DRBG_generate_functionWF_success in Heqr; trivial. omega.
  + inv G. trivial.
Qed. 
