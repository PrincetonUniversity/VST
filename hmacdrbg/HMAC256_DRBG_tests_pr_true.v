Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import sha.functional_prog.
Require Import HMAC256_DRBG_functional_prog.
Require Import entropy.
Require Import DRBG_state_handle.
Require Import DRBG_generate_function.
Require Import DRBG_instantiate_function.
Require Import DRBG_reseed_function.

Require Import sha.ByteBitRelations.

Definition stream_dummy (result: string) (n: nat) : option bool :=
  let hex := bytesToBits (hexstring_to_Zlist result) in
  if nth_ok n hex false then Some (nth n hex false)
  else None.

Definition get_nonce_dummy (result: string) (_: unit) := hexstring_to_Zlist result.

Fixpoint DRBG_generate_check (state_handle: DRBG_state_handle) (internal_states: list (string * string * string * string)) (returned_bits: string) :=
  match internal_states with
    | [] => True
    | (key, v, additional_input, entropy_input_reseed)::[] =>
      let test_HMAC256_DRBG_reseed_function := HMAC256_DRBG_reseed_function 32 32 256 in
      let test_HMAC256_DRBG_generate_function := HMAC256_DRBG_generate_function test_HMAC256_DRBG_reseed_function 1024 128 128 in
      let key := hexstring_to_Zlist key in
      let value := hexstring_to_Zlist v in
      let additional_input := hexstring_to_Zlist additional_input in
      let returned_bits := hexstring_to_Zlist returned_bits in
      match test_HMAC256_DRBG_generate_function (stream_dummy entropy_input_reseed) state_handle 128 256 true additional_input with
        | ENTROPY.success (returned_bits', ((value', key', _), _, _)) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ listZ_eq returned_bits returned_bits' = true
        | ENTROPY.error _ _ => False
      end
    | (key, v, additional_input, entropy_input_reseed)::tl =>
      let test_HMAC256_DRBG_reseed_function := HMAC256_DRBG_reseed_function 32 32 256 in
      let test_HMAC256_DRBG_generate_function := HMAC256_DRBG_generate_function test_HMAC256_DRBG_reseed_function 1024 128 128 in
      let key := hexstring_to_Zlist key in
      let value := hexstring_to_Zlist v in
      let additional_input := hexstring_to_Zlist additional_input in
      match test_HMAC256_DRBG_generate_function (stream_dummy entropy_input_reseed) state_handle 128 256 true additional_input with
        | ENTROPY.success (_, ((value', key', x), y, z)) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_generate_check ((value', key', x), y, z) tl returned_bits
        | ENTROPY.error _ _ => False
      end
  end.

Definition DRBG_check (entropy_input nonce key value personalization_string: string) (internal_states: list (string * string * string * string)) (returned_bits: string) :=
  let key := hexstring_to_Zlist key in
  let value := hexstring_to_Zlist value in
  let personalization_string := hexstring_to_Zlist personalization_string in
  match HMAC256_DRBG_instantiate_function 32 32 (get_nonce_dummy nonce) 256 256 true (stream_dummy entropy_input) 256 true personalization_string with
    | ENTROPY.success ((value', key', x), y, z) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_generate_check ((value', key', x), y, z) internal_states returned_bits
    | _ => False
  end.

Lemma test0:
  DRBG_check
    "9969e54b4703ff31785b879a7e5c0eae0d3e309559e9fe96b0676d49d591ea4d"
    "07d20d46d064757d3023cac2376127ab"
    "c2d1fd328b9789a72097325a5623f1b23eed73ed2fdcb477e9a2dd10a96f9d27"
    "cba657aa552473950ef85a02f228224514c648f01cdb2cd04aa773c25ca836f2"
    ""
    [
      ("d89d68107440e91a57a841b688ad0fd1fbeb440d26b199bad639280ba809da2e"%string, "df85d42ae075f3560d00a653ecf4dba120a90dc4510245aaf77c799f488df76e"%string, ""%string, "c60f2999100f738c10f74792676a3fc4a262d13721798046e29a295181569f54"%string);
      ("ee60a512e1383ffef37971a07a9754ceeb5b3d0aa640514e13e2a7359ec7157e"%string, "a964fd634f8f05a22719d37453ede555d6dd8fdf7beccf757e69c6fa782c5f16"%string, ""%string, "c11d4524c9071bd3096015fcf7bc24a607f22fa065c937658a2a77a8699089f4"%string)
    ]
    "abc015856094803a938dffd20da94843870ef935b82cfec17706b8f551b8385044235dd44b599f94b39be78dd476e0cf11309c995a7334e0a78b37bc9586235086fa3b637ba91cf8fb65efa22a589c137531aa7b2d4e2607aac27292b01c698e6e01ae679eb87c01a89c7422d4372d6d754ababb4bf896fcb1cd09d692d0283f"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test_with_personalization0:
  DRBG_check
    "f7b90c797a4a376cdd9f5c435f5985e77f36ec1df1145a12072cbb2a0da378fc"
    "d95202986d45896e9f4a65f2f353fa35"
    "628f0d947dca7e4171940799bfbc9b61c0ec7c2555a606c75940c37c9432bad0"
    "2fbafb7afd31927f8f5ee0c4fcdb27c15db4c5dda3d40bc091bfdb782561df85"
    "61535c5c045e784267fd0d85f2861778fa53c8e8586af67cf5c9f21a28ebb656"
    [
      ("b31f8c3d56139a901abc4dd953c43a3fc65cfcb7647061e4d9e2a7e31206a5f3"%string, "1ef1e9d5d8901b71c4f9cca6c68f320d5493f2fef1c71f5e58c5c83e144822f2"%string, ""%string, "130ab64f41a5d49d6a241e0260b4bb8a46a16c6ac9e234c84b5b26cdb518d459"%string);
      ("da8e4563d0180619c92b29c3b8dd8f3508df3e8fa844bf331cfb0b1f4205df75"%string, "4fe4168ff2aa97bdc0235b4df3eed8bd377aa3805ff6cd9445efb6e287a71e80"%string, ""%string, "f7670e817ac061ac60439be60982492000dc5da8bc6636bdac8b1cab03198dfd"%string)
    ]
    "8df4e349f9ea43cc509ecb2b1124358cda2de1f5cc9315edca63610a413478d68b8bb49c2814c82ce571f6e0a6780fa21c4b570610ee0c04d3edb92124f580f962d741330200c19885ca716502223247b728d66fbbeb7c6cc25cfe9866b1450b346227c7663074c8b15d189f1c6edba172a53c733d67c1c69bd7aca7e62013cd"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test_with_additional_input0:
  DRBG_check
    "2cad88b2b6a06e703de46185ccb2ddcf5e0ee030995ebdf95cc4fbc38441f17f"
    "32310770e04172c0cf91f6590cce44a4"
    "bef6a1ebb29164bc4d7ae6ca2d5a02d619b91dd0d88147e7e87454898ce99338"
    "6f78b5982fef43f09bd7096ecc3aa02a5c3a4dbf71e17341ff3814bbc5dcddd2"
    ""
    [
      ("bc4186dc24c4b64d8c094c79c7605ae9a3ce6a9e6cdb071a766897c8df302e4c"%string, "5f1aa99b991e37d7ffa7e6779d36b8295976a26ff13efaf72fe90f30a2d16aff"%string, "ef6da5e6530e0d621749ab192e06327e995c3ac0c3963ab8c8cd2df2839ab5df"%string, "448bfbc5ce9e3b9da3e9642daecd994dfe373e75253e8eb585141224eca7ad7b"%string);
      ("2afc9c4d27f850d0f982499199af67d0c20d324ebf9260fb021d377861ef257e"%string, "c5beeb04e4bfae254053c26d1ef0ff637da4873e7488fc08ab5660142a6311ae"%string, "44278b31ed853f0a510bd14650ac4b4971d8b426799a43511d016be68dedbb8d"%string, "afb57f69799c0b892b3015990e133698d543aa87829ace868e4a5e9525d62357"%string)
    ]
    "4c7dfbe509dc5a3ac26998723c6a44cad20b197fc86117c778d1568ab828923862885e97198f77a1cb45113f5d78726a0f120aec94afc45f57c8dcc1cb092b343480012858ef5bc559f57023442209326ec4a54d91ca3a77dfdf9e75f117cef50e6fd2dc9af6ddce8e6515b4a97357a97b6cd274f68a042fa41bbd7b7261b034"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test_with_additional_input_and_personalization0:
  DRBG_check
    "4294671d493dc085b5184607d7de2ff2b6aceb734a1b026f6cfee7c5a90f03da"
    "d071544e599235d5eb38b64b551d2a6e"
    "3ab4e27f331bf194cec5762baf84b7fb16e7cf81d69635c48b96febdfb809c18"
    "7a232bc40bdd9c92ddaffbe76aa322ba1a47234d227060d8ac187e680780c02a"
    "63bc769ae1d95a98bde870e4db7776297041d37c8a5c688d4e024b78d83f4d78"
    [
      ("6acd0c98e1f7340bd7ab4a594960b63357bd19b99471cc8ea34817af77259880"%string, "db7c92e4c55c43b370b81a6024f0e14675a86c9667412b10ce5d1ea76259c1e4"%string, "28848becd3f47696f124f4b14853a456156f69be583a7d4682cff8d44b39e1d3"%string, "db9b4790b62336fbb9a684b82947065393eeef8f57bd2477141ad17e776dac34"%string);
      ("2bcafedb81361b2cf44555d3739fdff9dcd6315dd861bb640e812ddcb26045a5"%string, "48e842ba5cb7784211bdc0c19eedec0e23cdfa6c81ad56a7e993eee15a604e2e"%string, "8bfce0b7132661c3cd78175d83926f643e36f7608eec2c5dac3ddcbacc8c2182"%string, "4a9abe80f6f522f29878bedf8245b27940a76471006fb4a4110beb4decb6c341"%string)
    ]
    "e580dc969194b2b18a97478aef9d1a72390aff14562747bf080d741527a6655ce7fc135325b457483a9f9c70f91165a811cf4524b50d51199a0df3bd60d12abac27d0bf6618e6b114e05420352e23f3603dfe8a225dc19b3d1fff1dc245dc6b1df24c741744bec3f9437dbbf222df84881a457a589e7815ef132f686b760f012"%string.
  vm_compute. repeat (split;auto). Qed.

