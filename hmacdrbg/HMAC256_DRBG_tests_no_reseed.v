Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import sha.functional_prog.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.DRBG_functions.
(*
Require Import DRBG_state_handle.
Require Import DRBG_generate_function.
Require Import DRBG_instantiate_function.
Require Import DRBG_reseed_function.*)

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

Definition DRBG_check (entropy_input nonce key value personalization_string: string) (internal_states: list (string * string * string)) (returned_bits: string) :=
  let key := hexstring_to_Zlist key in
  let value := hexstring_to_Zlist value in
  let personalization_string := hexstring_to_Zlist personalization_string in
  match HMAC256_DRBG_instantiate_function 32 32 (get_nonce_dummy nonce) 256 256 false (stream_dummy entropy_input) 256 false personalization_string with
    | ENTROPY.success ((value', key', x), y, z) _ => listZ_eq value value' = true /\ listZ_eq key key' = true /\ DRBG_generate_check ((value', key', x), y, z) internal_states returned_bits
    | _ => False
  end.

Lemma test0: DRBG_check
               "ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488"%string
               "659ba96c601dc69fc902940805ec0ca8"
               "302a4aba78412ab36940f4be7b940a0c728542b8b81d95b801a57b3797f9dd6e"%string
               "e75855f93b971ac468d200992e211960202d53cf08852ef86772d6490bfb53f9"%string
               ""
               [
                 ("911bf7cbda4387a172a1a3daf6c9fa8e17c4bfef69cc7eff1341e7eef88d2811"%string, "bfbdcf455d5c82acafc59f339ce57126ff70b67aef910fa25db7617818faeafe"%string, ""%string);
                 ("6dd2cd5b1edba4b620d195ce26ad6845b063211d11e591432de37a3ad793f66c"%string, "6b94e773e3469353a1ca8face76b238c5919d62a150a7dfc589ffa11c30b5b94"%string, ""%string)
               ]
               "e528e9abf2dece54d47c7e75e5fe302149f817ea9fb4bee6f4199697d04d5b89d54fbb978a15b5c443c9ec21036d2460b6f73ebad0dc2aba6e624abf07745bc107694bb7547bb0995f70de25d6b29e2d3011bb19d27676c07162c8b5ccde0668961df86803482cb37ed6d5c0bb8d50cf1f50d476aa0458bdaba806f48be9dcb8"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test1: DRBG_check
               "79737479ba4e7642a221fcfd1b820b134e9e3540a35bb48ffae29c20f5418ea3"%string
               "3593259c092bef4129bc2c6c9e19f343"
               "587959c1169cc9a308506ea52c2648cebf4498a35d71f6329e457ecc3204ca50"%string
               "b57cb403b6cd62860139c3484c9a5998fd0d82670846a765a87c9ead65f663c5"%string
               ""
               [
                 ("48f38d0c6a344959cc94502b7b5e8dffb6a5f41795d9066fc9a649557167ee2f"%string, "1d495eef7761b65dccd0a983d2d7204fea28b5c81f1758046e062eb043755ea1"%string, ""%string);
                 ("9356bdc03c35b21e600892ed64f8efc8edcaf19258fa987b56b8eb0e13a07ff1"%string, "3d52cfa76ba57ef836fc507390fac83fbebd81799604f0a9beaf60874dabc5e9"%string, ""%string)
               ]
               "cf5ad5984f9e43917aa9087380dac46e410ddc8a7731859c84e9d0f31bd43655b924159413e2293b17610f211e09f770f172b8fb693a35b85d3b9e5e63b1dc252ac0e115002e9bedfb4b5b6fd43f33b8e0eafb2d072e1a6fee1f159df9b51e6c8da737e60d5032dd30544ec51558c6f080bdbdab1de8a939e961e06b5f1aca37"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test2: DRBG_check
               "b340907445b97a8b589264de4a17c0bea11bb53ad72f9f33297f05d2879d898d"%string
               "65cb27735d83c0708f72684ea58f7ee5"
               "f35c29e8db08c1b947ad0263cf3dbe735d74abb99c021728c3c9235a7cdb0bbf"%string
               "0b8e71f560cbe2b358684fc682ba7837480017785266d698a49c0bdf02a65eda"%string
               ""
               [
                 ("f943ed975c2013dbc9dc1025d7c3ebaa463bc1e4368df1c04348677e5148c9b7"%string, "6a66c83034d1f48cfc9fa7708c643792e790e9a25ed0e2f479f481d833343366"%string, ""%string);
                 ("6b1e253f4cfd379ce55e9659dc97fe7c24f07ee54648807a2f72c5faf2dd1d35"%string, "d508c96ba979c61a2034d1f6335fe7e967da7fec6752d0cb09de2530eca537d3"%string, ""%string)
               ]
               "75183aaaf3574bc68003352ad655d0e9ce9dd17552723b47fab0e84ef903694a32987eeddbdc48efd24195dbdac8a46ba2d972f5808f23a869e71343140361f58b243e62722088fe10a98e43372d252b144e00c89c215a76a121734bdc485486f65c0b16b8963524a3a70e6f38f169c12f6cbdd169dd48fe4421a235847a23ff"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test3: DRBG_check
               "8e159f60060a7d6a7e6fe7c9f769c30b98acb1240b25e7ee33f1da834c0858e7"%string
               "c39d35052201bdcce4e127a04f04d644"
               "491e895a4bc06253db3c0410616a9a4935d02713e37aa25ab65849d0128ba270"%string
               "ec970281607ce9a5e6fec81f018351173f7ea2accaa00d2e229c91f86c255eea"%string
               ""
               [
                 ("411a2ab43a06f1811c223503c9791df80e6a1d2d52aa955500b65b90adf3ea72"%string, "ef605c0169af189955b413449028ff4279401c66dd1c050c26ff506d736e31fc"%string, ""%string);
                 ("1866622117806c6cbaa148fc8edf5181e9a85d2013c54f3d24b7f2c15bf4a6d8"%string, "e173654682d55066b870e1c82acca0026581919fca0ed03f5a410f310464968e"%string, ""%string)
               ]
               "62910a77213967ea93d6457e255af51fc79d49629af2fccd81840cdfbb4910991f50a477cbd29edd8a47c4fec9d141f50dfde7c4d8fcab473eff3cc2ee9e7cc90871f180777a97841597b0dd7e779eff9784b9cc33689fd7d48c0dcd341515ac8fecf5c55a6327aea8d58f97220b7462373e84e3b7417a57e80ce946d6120db5"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test4: DRBG_check
               "74755f196305f7fb6689b2fe6835dc1d81484fc481a6b8087f649a1952f4df6a"%string
               "c36387a544a5f2b78007651a7b74b749"
               "9adfb5d44f961fc5e8dd8392a2faed6b7ea120be0390aed78aec9a0f0ad96ba4"%string
               "b80f5b61e4095fc3191d9abd3f64ae42eaf59062f6f1c9d0302f3192addd9d0f"%string
               ""
               [
                 ("3529765f9d1b3a4e4d2aa1f76b79078c13e491dd084c91c9c60a1ca71d136cb5"%string, "2459df9b9298b87758fee7eb96fcef9417d7bcedfaedf051179b5308f6affbda"%string, ""%string);
                 ("b13c4e2404d451638990a1c93cf61ec24ee9786170c03381d555caf34462d9e5"%string, "77b52d69a686cd0ec28905a8cdb3579f2e429a5a8a4403842d81faf3c72f768a"%string, ""%string)
               ]
               "b2896f3af4375dab67e8062d82c1a005ef4ed119d13a9f18371b1b873774418684805fd659bfd69964f83a5cfe08667ddad672cafd16befffa9faed49865214f703951b443e6dca22edb636f3308380144b9333de4bcb0735710e4d9266786342fc53babe7bdbe3c01a3addb7f23c63ce2834729fabbd419b47beceb4a460236"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test5: DRBG_check
               "4b222718f56a3260b3c2625a4cf80950b7d6c1250f170bd5c28b118abdf23b2f"%string
               "7aed52d0016fcaef0b6492bc40bbe0e9"
               "f4157eb3844c88ea985e1236683431b882b70b63db891750ab3f41b4e02819f6"%string
               "b52d87fcf3249f61e9c73af4c3e0c949579aa580dd7271399b22490671a49792"%string
               ""
               [
                 ("f247aad1bbc398152cd0d6c9f84c0e7c8b98289ced8768bf0708efc0a90ab10f"%string, "f55a1cb5c058c5c6650e05018a7d9ea5e5cc427d1af9ca89ccf5ef59852ece80"%string, ""%string);
                 ("4bf638e7f1e0c50014336ea17dc5f7b83ced0b780fba1c88abb5025a8bec6f28"%string, "dec827fc18d3c9691663d4bb6dd4a5202b6432549976e374ab33f4d8d9321e04"%string, ""%string)
               ]
               "a6da029b3665cd39fd50a54c553f99fed3626f4902ffe322dc51f0670dfe8742ed48415cf04bbad5ed3b23b18b7892d170a7dcf3ef8052d5717cb0c1a8b3010d9a9ea5de70ae5356249c0e098946030c46d9d3d209864539444374d8fbcae068e1d6548fa59e6562e6b2d1acbda8da0318c23752ebc9be0c1c1c5b3cf66dd967"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test6: DRBG_check
               "b512633f27fb182a076917e39888ba3ff35d23c3742eb8f3c635a044163768e0"%string
               "e2c39b84629a3de5c301db5643af1c21"
               "4038798b0b8bfc7be148adbdeacaf082155c46bbc86538d574aaeb0f187c52fc"%string
               "e46a05a9268ecc00ecc3310947baa11d1ccd42cedd0ed80d78b6fb43bfd1b903"%string
               ""
               [
                 ("5464d1f719fff5cda06a0ee358b18b8a9d8dfa3525d461f343f1a3be5138fa9a"%string, "759926760ecbb5c000992227f1065c18cbff9a5aaec38911d6e7a399bab4783b"%string, ""%string);
                 ("df2103bf3d5dd0d60870042d702478272caef5198ff71441a772d705f28ee760"%string, "cad9c856f921f6a248e0db4b3356e06e205fd9a15980030e1d32a303f4278329"%string, ""%string)
               ]
               "fb931d0d0194a97b48d5d4c231fdad5c61aedf1c3a55ac24983ecbf38487b1c93396c6b86ff3920cfa8c77e0146de835ea5809676e702dee6a78100da9aa43d8ec0bf5720befa71f82193205ac2ea403e8d7e0e6270b366dc4200be26afd9f63b7e79286a35c688c57cbff55ac747d4c28bb80a2b2097b3b62ea439950d75dff"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test7: DRBG_check
               "aae3ffc8605a975befefcea0a7a286642bc3b95fb37bd0eb0585a4cabf8b3d1e"%string
               "9504c3c0c4310c1c0746a036c91d9034"
               "57dcea5091d3f590da9046aa835e2af193d323e4dea4cd68dc8d655838b64205"%string
               "4e24e7f387135fdc233ad60089c247c568573a97aac6420ddc581b76e7a3d663"%string
               ""
               [
                 ("724d8b8a6d067981150eb9eb32056fed40b5f7b9bc50090160832d413d97e833"%string, "2071b79328ba1641521fc7f266b07d03ef2a11b80f4d05a483bcb2590b18bdc2"%string, ""%string);
                 ("ded598669683bf021fa00809a363e41526267e1e7155a70fe82f0a1562a7e4d6"%string, "68ab4d6d3b44ec6dc2ef35724a3208a985e1e100f74497519a2044f77e02e354"%string, ""%string)
               ]
               "2819bd3b0d216dad59ddd6c354c4518153a2b04374b07c49e64a8e4d055575dfbc9a8fcde68bd257ff1ba5c6000564b46d6dd7ecd9c5d684fd757df62d85211575d3562d7814008ab5c8bc00e7b5a649eae2318665b55d762de36eba00c2906c0e0ec8706edb493e51ca5eb4b9f015dc932f262f52a86b11c41e9a6d5b3bd431"%string.
  vm_compute. repeat (split;auto). Qed.

Lemma test_with_personalization_and_additional0: DRBG_check
               "5d3286bc53a258a53ba781e2c4dcd79a790e43bbe0e89fb3eed39086be34174b"%string
               "c5422294b7318952ace7055ab7570abf"
               "87ce5b45d0964e20e5e56418ae1de8b6b5fa6cdf4ff0efe5ab4444bce5658b99"%string
               "2ccbf4b25c4b263d59b14080c83492b05769b583adf37c57b7eb59ab07bb4d40"%string
               "2dba094d008e150d51c4135bb2f03dcde9cbf3468a12908a1b025c120c985b9d"
               [
                 ("c60114af6165b77a36dbab54b96c21bae4a3aa329782f4b850f423eb3b760483"%string, "09a7df20d9f87656efa075fae3f8db432904bbd3165b125b1a688a8b5c4de88f"%string, "793a7ef8f6f0482beac542bb785c10f8b7b406a4de92667ab168ecc2cf7573c6"%string);
                 ("ef3855c4da0eb30c90a935c98006bac71059d1a4884bc7e63f28fe56df4e92a6"%string, "7925c738fb6e7f7c7e147cb3b8b306b485a545ae63dc878cc49dd93e86dbed9b"%string, "2238cdb4e23d629fe0c2a83dd8d5144ce1a6229ef41dabe2a99ff722e510b530"%string)
               ]
               "d04678198ae7e1aeb435b45291458ffde0891560748b43330eaf866b5a6385e74c6fa5a5a44bdb284d436e98d244018d6acedcdfa2e9f499d8089e4db86ae89a6ab2d19cb705e2f048f97fb597f04106a1fa6a1416ad3d859118e079a0c319eb95686f4cbcce3b5101c7a0b010ef029c4ef6d06cdfac97efb9773891688c37cf"%string.
  vm_compute. repeat (split;auto). Qed.

