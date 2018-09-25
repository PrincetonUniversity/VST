Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import VST.floyd.functional_base.

Require Import hmacdrbg.DRBG_functions.

Definition HMAC_DRBG_update (HMAC: list byte -> list byte -> list byte) (provided_data K V: list byte): (list byte * list byte) :=
  let K := HMAC (V ++ [Byte.zero] ++ provided_data) K in
  let V := HMAC V K in
  match provided_data with
    | [] => (K, V)
    | _::_ =>
      let K := HMAC (V ++ [Byte.one] ++ provided_data) K in
      let V := HMAC V K in
      (K, V)
  end.

Definition initial_key: list byte := list_repeat 32 Byte.zero.

Definition initial_value: list byte := list_repeat 32 Byte.one.

Definition HMAC_DRBG_instantiate_algorithm (HMAC: list byte -> list byte -> list byte)
           (entropy_input nonce personalization_string: list byte) (security_strength: Z): DRBG_working_state :=
  let seed_material := entropy_input ++ nonce ++ personalization_string in
  let key := initial_key in
  let value := initial_value in
  let (key, value) := HMAC_DRBG_update HMAC seed_material key value in
  let reseed_counter := 1 in
  (value, key, reseed_counter).

Definition HMAC_DRBG_reseed_algorithm (HMAC: list byte -> list byte -> list byte)
           (working_state: DRBG_working_state) (entropy_input additional_input: list byte): DRBG_working_state :=
  match working_state with (v, key, _) =>
                           let seed_material := entropy_input ++ additional_input in
                           let (key, v) := HMAC_DRBG_update HMAC seed_material key v in
                           let reseed_counter := 1 in
                           (v, key, reseed_counter)
  end.

Function HMAC_DRBG_generate_helper_Z (HMAC: list byte -> list byte -> list byte) (key v: list byte)
          (requested_number_of_bytes: Z) {measure Z.to_nat requested_number_of_bytes}: (list byte * list byte) :=
  if 0 >=? requested_number_of_bytes then (v, [])
  else
    let len := 32%nat in
    let (v, rest) := HMAC_DRBG_generate_helper_Z HMAC key v (requested_number_of_bytes - (Z.of_nat len)) in
    let v := HMAC v key in
    let temp := v in
    (v, rest ++ temp).
Proof.
  intros. rewrite Z2Nat.inj_sub by omega.
  rewrite Nat2Z.id.
  assert ((0 <? requested_number_of_bytes) = true).
  *
    rewrite Z.ltb_antisym.
    rewrite <- Z.geb_leb.
    rewrite teq.
    auto.
  *
  apply Zlt_is_lt_bool in H.
  apply Z2Nat.inj_lt in H; omega.
Defined.

Definition HMAC_DRBG_generate_algorithm (HMAC: list byte -> list byte -> list byte) (reseed_interval: Z)
           (working_state: DRBG_working_state) (requested_number_of_bytes: Z)
           (additional_input: list byte): DRBG_generate_algorithm_result :=
  match working_state with (v, key, reseed_counter) =>
    if reseed_counter >? reseed_interval then generate_algorithm_reseed_required
    else
      let (key, v) := match additional_input with
                        | [] => (key, v)
                        | _::_ => HMAC_DRBG_update HMAC additional_input key v
                      end in
      let (v, temp) := HMAC_DRBG_generate_helper_Z HMAC key v requested_number_of_bytes in
      let returned_bits := firstn (Z.to_nat requested_number_of_bytes) temp in
      let (key, v) := HMAC_DRBG_update HMAC additional_input key v in
      let reseed_counter := reseed_counter + 1 in
      generate_algorithm_success returned_bits (v, key, reseed_counter)
  end.
