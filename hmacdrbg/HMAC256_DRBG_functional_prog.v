Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import sha.HMAC256_functional_prog.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.

Definition HMAC256_DRBG_update := HMAC_DRBG_update HMAC256.

Definition HMAC256_DRBG_instantiate_algorithm := HMAC_DRBG_instantiate_algorithm HMAC256.

Definition HMAC256_DRBG_instantiate_function := DRBG_instantiate_function HMAC256_DRBG_instantiate_algorithm.

Definition HMAC256_DRBG_generate_algorithm := HMAC_DRBG_generate_algorithm HMAC256.

Definition HMAC256_DRBG_generate_function := DRBG_generate_function HMAC256_DRBG_generate_algorithm.

Definition HMAC256_DRBG_reseed_algorithm := HMAC_DRBG_reseed_algorithm HMAC256.

Definition HMAC256_DRBG_reseed_function := DRBG_reseed_function HMAC256_DRBG_reseed_algorithm.