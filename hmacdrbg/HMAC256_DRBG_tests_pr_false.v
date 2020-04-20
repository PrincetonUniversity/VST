Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import sha.functional_prog.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.DRBG_functions.
(*Require Import DRBG_state_handle.
Require Import DRBG_generate_function.
Require Import DRBG_instantiate_function.
Require Import DRBG_reseed_function.
*)
Require Import sha.ByteBitRelations.

Definition stream_dummy (result: string) (n: nat) : option bool :=
  let hex := bytesToBits (hexstring_to_Zlist result) in
  if nth_ok n hex false then Some (nth n hex false)
  else None.

Definition get_nonce_dummy (result: string) (_: unit) := hexstring_to_Zlist result.

Definition noop_reseed_function (s: ENTROPY.stream) (x: DRBG_state_handle) (_: bool) (_: list Z) := ENTROPY.success x s.

Fixpoint DRBG_generate_check (state_handle: DRBG_state_handle) (internal_states: list (string * string * string)) (returned_bits: string) :=
  let test_HMAC256_DRBG_generate_function := HMAC256_DRBG_generate_function noop_reseed_function 1024 128 128 in
  match internal_states with
    | [] => True
    | (key, v, additional_input)::[] =>
      let key := hexstring_to_Zlist key in
      let value := hexstring_to_Zlist v in
      let additional_input := hexstring_to_Zlist additional_input in
      let returned_bits := hexstring_to_Zlist returned_bits in
      match test_HMAC256_DRBG_generate_function (stream_dummy "") state_handle 128 256 false additional_input with
        | ENTROPY.success (returned_bits', ((value', key', _), _, _)) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ listZ_eq returned_bits returned_bits' = true
        | ENTROPY.error _ _ => False
      end
    | (key, v, additional_input)::tl =>
      let key := hexstring_to_Zlist key in
      let value := hexstring_to_Zlist v in
      let additional_input := hexstring_to_Zlist additional_input in
      match test_HMAC256_DRBG_generate_function (stream_dummy "") state_handle 128 256 false additional_input with
        | ENTROPY.success (_, ((value', key', x), y, z)) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_generate_check ((value', key', x), y, z) tl returned_bits
        | ENTROPY.error _ _ => False
      end
  end.

Definition DRBG_reseed_check (state_handle: DRBG_state_handle) (entropy_input_reseed additional_input_reseed key_reseed value_reseed: string) (internal_states: list (string * string * string)) (returned_bits: string) :=
  let key := hexstring_to_Zlist key_reseed in
  let value := hexstring_to_Zlist value_reseed in
  match HMAC256_DRBG_reseed_function 32 32 256 (stream_dummy entropy_input_reseed) state_handle false (hexstring_to_Zlist additional_input_reseed) with
    | ENTROPY.success ((value', key', x), y, z) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_generate_check ((value', key', x), y, z) internal_states returned_bits
    | _ => False
  end.

Definition DRBG_check (entropy_input nonce key value personalization_string: string) (entropy_input_reseed additional_input_reseed key_reseed value_reseed: string) (internal_states: list (string * string * string)) (returned_bits: string) :=
  let key := hexstring_to_Zlist key in
  let value := hexstring_to_Zlist value in
  let personalization_string := hexstring_to_Zlist personalization_string in
  match HMAC256_DRBG_instantiate_function 32 32 (get_nonce_dummy nonce) 256 256 false (stream_dummy entropy_input) 256 false personalization_string with
    | ENTROPY.success ((value', key', x), y, z) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_reseed_check ((value', key', x), y, z) entropy_input_reseed additional_input_reseed key_reseed value_reseed internal_states returned_bits
    | _ => False
  end.

Lemma test0: DRBG_check
               "06032cd5eed33f39265f49ecb142c511da9aff2af71203bffaf34a9ca5bd9c0d"
               "0e66f71edc43e42a45ad3c6fc6cdc4df"
               "17dc11c2389f5eeb9d0f6a5148a1ea83ee8a828f4f140ac78272a0da435fa121"
               "81e0d8830ed2d16f9b288a1cb289c5fab3f3c5c28131be7cafedcc7734604d34"
               ""
               "01920a4e669ed3a85ae8a33b35a74ad7fb2a6bb4cf395ce00334a9c9a5a5d552"
               ""
               "ca43e73325de43c41d7e0a7a3163fb04061b09fcee4c7b8884e969e3bdfdff9a"
               "c246fa97570ba2b9d9e5b453fe4632366f146fbd8491146563eb463c9eafe50c"
               [
                 ("8be4c7f9f249d5af2c6345a8f07af14be1d7adc2b9892286ffe37760d8aa5a1b"%string, "df67d0816d6a8f3b73ba7638ea113bef0e33a1da451272ef1472211fb31c1cd6"%string, ""%string);
                 ("5ed31bc06cc4f3a97f7f34929b0558b0c34de1f4bd1cef456a8364140e2d9f41"%string, "80524881711e89a61e6fe7169581e50fb9ad642f3dff48fba5773352fa04cec3"%string, ""%string)
               ]
               "76fc79fe9b50beccc991a11b5635783a83536add03c157fb30645e611c2898bb2b1bc215000209208cd506cb28da2a51bdb03826aaf2bd2335d576d519160842e7158ad0949d1a9ec3e66ea1b1a064b005de914eac2e9d4f2d72a8616a80225422918250ff66a41bd2f864a6a38cc5b6499dc43f7f2bd09e1e0f8f5885935124".
  vm_compute. repeat (split;auto). Qed.

Lemma test_with_additional_input0: DRBG_check
               "05ac9fc4c62a02e3f90840da5616218c6de5743d66b8e0fbf833759c5928b53d"
               "2b89a17904922ed8f017a63044848545"
               "8d3006bd33b7d8b935a8484b786850f107b731a7efc51521848b875c2214d154"
               "eaa29892ee1e46198ea68c07588ac12641fc901e484eda321c2f26a9ff328e3d"
               ""
               "2791126b8b52ee1fd9392a0a13e0083bed4186dc649b739607ac70ec8dcecf9b"
               "43bac13bae715092cf7eb280a2e10a962faf7233c41412f69bc74a35a584e54c"
               "3138df070c49f48b080004df669f386676b4cb92b40de4d021b2a9e4451e5013"
               "25d3b766cd9f8ad5c45efd7fa01cc08dbce8d0d3792ec2b59bfead7bce39ed01"
               [
                 ("cac850b111de755bb8a5ed1ebc052ed53ab1ff1b9d0fab2946a3728c7e9f43e4"%string, "06624fa590e1d63397b13a0e69081274434f793fdfc1e6298a7373834024da46"%string, "3f2fed4b68d506ecefa21f3f5bb907beb0f17dbc30f6ffbba5e5861408c53a1e"%string);
                 ("b15ae269570790a8c6a81c5be7aef33f645abb161d218761ff8739cb7997eed8"%string, "92971e96fc46608d4343821491990915cdb957ae983ab6cdab84fd094bce1380"%string, "529030df50f410985fde068df82b935ec23d839cb4b269414c0ede6cffea5b68"%string)
               ]
               "02ddff5173da2fcffa10215b030d660d61179e61ecc22609b1151a75f1cbcbb4363c3a89299b4b63aca5e581e73c860491010aa35de3337cc6c09ebec8c91a6287586f3a74d9694b462d2720ea2e11bbd02af33adefb4a16e6b370fa0effd57d607547bdcfbb7831f54de7073ad2a7da987a0016a82fa958779a168674b56524".
  vm_compute. repeat (split;auto). Qed.

Lemma test_with_additional_input_and_personalization0: DRBG_check
               "cdb0d9117cc6dbc9ef9dcb06a97579841d72dc18b2d46a1cb61e314012bdf416"
               "d0c0d01d156016d0eb6b7e9c7c3c8da8"
               "108a7674f3348216c91f5745dd87a919f552fc44373b84ad4b3b843a26b574cb"
               "6c02577c505aed360be7b1cecb61068d8765be1391bacb10f4180d91bd3915db"
               "6f0fb9eab3f9ea7ab0a719bfa879bf0aaed683307fda0c6d73ce018b6e34faaa"
               "8ec6f7d5a8e2e88f43986f70b86e050d07c84b931bcf18e601c5a3eee3064c82"
               "1ab4ca9014fa98a55938316de8ba5a68c629b0741bdd058c4d70c91cda5099b3"
               "e57f901d4bff2909f09467003096edfdb46c89af6bd82e904d11b6753d645c90"
               "21a645aeca821899e7e733a10f64565deee5ced3cd5c0356b66c76dc8a906e69"
               [
                 ("648f92d385c3fbf61526deef48ca5ca4dfe4646d82fe8e73bc1705824e181dc9"%string, "490c0b7786c80f16ad5ee1cc0efd29618968dce14cccebecec8964ea8a41b439"%string, "16e2d0721b58d839a122852abd3bf2c942a31c84d82fca74211871880d7162ff"%string);
                 ("db4853ca51700d43c5b6d63eb6cd20ea2dbe3dff512f2dc9531b5b3d9120121c"%string, "47390036d5cb308cf9592fdfe95bf19b8ed1a3db88ed8c3b2b2d77540dfb5470"%string, "53686f042a7b087d5d2eca0d2a96de131f275ed7151189f7ca52deaa78b79fb2"%string)
               ]
               "dda04a2ca7b8147af1548f5d086591ca4fd951a345ce52b3cd49d47e84aa31a183e31fbc42a1ff1d95afec7143c8008c97bc2a9c091df0a763848391f68cb4a366ad89857ac725a53b303ddea767be8dc5f605b1b95f6d24c9f06be65a973a089320b3cc42569dcfd4b92b62a993785b0301b3fc452445656fce22664827b88f".
  vm_compute. repeat (split;auto). Qed.