Require Import aes.api_specs.
Require Import aes.bitfiddling.
Open Scope Z.

Axiom EverythingIsTrue: forall (P: Prop), P.

Goal forall
Espec: OracleKind,
semax
  (initialized_list
     [_i]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP () LOCAL () SEP ())
  Sskip
  (normal_ret_assert (PROP () LOCAL () SEP())).
Proof.
  intros.
Time simplify_Delta.
  apply EverythingIsTrue.
Time Qed. (* 0.147 secs *)

Goal forall
Espec: OracleKind,
semax
  (initialized_list
     [_i; _RK]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP () LOCAL () SEP ())
  Sskip
  (normal_ret_assert (PROP () LOCAL () SEP())).
Proof.
  intros.
Time simplify_Delta.
  apply EverythingIsTrue.
Time Qed. (* 0.201 secs *)

Goal forall
Espec: OracleKind,
semax
  (initialized_list
     [_i; _RK; _X0]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP () LOCAL () SEP ())
  Sskip
  (normal_ret_assert (PROP () LOCAL () SEP())).
Proof.
  intros.
Time simplify_Delta.
  apply EverythingIsTrue.
Time Qed. (* 0.577 secs *)


Goal forall
Espec: OracleKind,
semax
  (initialized_list
     [_i; _RK; _X0; _X1]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP () LOCAL () SEP ())
  Sskip
  (normal_ret_assert (PROP () LOCAL () SEP())).
Proof.
  intros.
Time  simplify_Delta.
  apply EverythingIsTrue.
Time Qed. (* 1.823 secs *)

Goal forall
Espec: OracleKind,
semax
  (initialized_list
     [_i; _RK; _X0; _X1; _X2]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP () LOCAL () SEP ())
  Sskip
  (normal_ret_assert (PROP () LOCAL () SEP())).
Proof.
  intros.
Time  simplify_Delta.
  apply EverythingIsTrue.
Time Qed. (* 6.952 secs *)

Goal forall
Espec: OracleKind,
semax
  (initialized_list
     [_i; _RK; _X0; _X1; _X2; _X3]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP () LOCAL () SEP ())
  Sskip
  (normal_ret_assert (PROP () LOCAL () SEP())).
Proof.
  intros.
Time  simplify_Delta.
  apply EverythingIsTrue.
Time Qed. (* 28.175 secs *)
