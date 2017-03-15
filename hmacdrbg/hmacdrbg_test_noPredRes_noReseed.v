Require Import compcert.lib.Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import sha.functional_prog.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.

Module TestSection8424_8625.
(*Relevant Section of HMAC_DRBG.txt: lines 8424 -- 8625
[SHA-256]
[PredictionResistance = False]
[EntropyInputLen = 256]
[NonceLen = 128]
[PersonalizationStringLen = 0]
[AdditionalInputLen = 0]
[ReturnedBitsLen = 1024]*)

Definition Instantiate (entropy nonce: string) : DRBG_functions.DRBG_working_state :=
HMAC256_DRBG_instantiate_algorithm (hexstring_to_Zlist entropy) 
                                   (hexstring_to_Zlist nonce) 
                                   nil (*pers_string -- nil in these test cases*)
                                   0 (*sec_strength -- ignored by HMAC256_DRBG_instantiate_algorithm*).

Definition reseedInterval:Z := 100000.
Definition addInput:list Z := nil.
Definition Generate (WS: DRBG_functions.DRBG_working_state): DRBG_functions.DRBG_generate_algorithm_result :=
           HMAC256_DRBG_generate_algorithm reseedInterval
                                           WS
                                           128 (*number of bytes: 1024bits*)
                                           addInput.

Definition CheckWS (WS:DRBG_functions.DRBG_working_state) 
  (V K: string) (rc:Z):=
  match WS with (value, key, reseedcounter) =>
   listZ_eq (hexstring_to_Zlist V) value &&
   listZ_eq (hexstring_to_Zlist K) key && 
   zeq reseedcounter rc = true
  end.

Definition Inst0: DRBG_functions.DRBG_working_state :=
  Instantiate "ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488" 
              "659ba96c601dc69fc902940805ec0ca8".

Definition Gen0_1: DRBG_functions.DRBG_generate_algorithm_result := Generate Inst0. 

Lemma Intantiate0: 
  CheckWS Inst0
          "e75855f93b971ac468d200992e211960202d53cf08852ef86772d6490bfb53f9"
        	"302a4aba78412ab36940f4be7b940a0c728542b8b81d95b801a57b3797f9dd6e" 1.
Proof. vm_compute; trivial. Qed.

Definition Value0_1:string := "bfbdcf455d5c82acafc59f339ce57126ff70b67aef910fa25db7617818faeafe".
Definition Key0_1:string:= "911bf7cbda4387a172a1a3daf6c9fa8e17c4bfef69cc7eff1341e7eef88d2811".
(*
Eval vm_compute in (hexstring_to_Zlist Value0_1). (*191...254*)
Eval vm_compute in (hexstring_to_Zlist Key0_1). (*145...17*)
*)
Lemma Generate0_1: exists x y, Gen0_1 = DRBG_functions.generate_algorithm_success x y /\ CheckWS y Value0_1 Key0_1 2.
Proof. vm_compute. eexists; eexists; split; reflexivity. Qed. 

Definition Gen0_2: DRBG_functions.DRBG_generate_algorithm_result :=
  match Gen0_1 with 
    DRBG_functions.generate_algorithm_success x y => Generate y
  | z => z (*DRBG_functions.generate_algorithm_reseed_required*)
  end.

Definition Value0_2:string := "6b94e773e3469353a1ca8face76b238c5919d62a150a7dfc589ffa11c30b5b94".
Definition Key0_2:string:= "6dd2cd5b1edba4b620d195ce26ad6845b063211d11e591432de37a3ad793f66c".
Definition Bits0_2:list Z := hexstring_to_Zlist "e528e9abf2dece54d47c7e75e5fe302149f817ea9fb4bee6f4199697d04d5b89d54fbb978a15b5c443c9ec21036d2460b6f73ebad0dc2aba6e624abf07745bc107694bb7547bb0995f70de25d6b29e2d3011bb19d27676c07162c8b5ccde0668961df86803482cb37ed6d5c0bb8d50cf1f50d476aa0458bdaba806f48be9dcb8".
(*
Eval vm_compute in Bits0_2. (*229..184*)
Eval vm_compute in (hexstring_to_Zlist Value0_2). (*107...148*)
Eval vm_compute in (hexstring_to_Zlist Key0_2). (*109...108*)
*)
Lemma Generate0_2: exists ws, Gen0_2 = DRBG_functions.generate_algorithm_success Bits0_2 ws /\ 
                                       CheckWS ws Value0_2 Key0_2 3.
Proof. vm_compute. eexists. split; reflexivity. Qed.

Definition Check_8424_8625 (entropy nonce Value0 Key0 Value1 Key1 Bits Value2 Key2: string) :=
  let ws0 := Instantiate entropy nonce 
  in match Generate ws0 with 
       DRBG_functions.generate_algorithm_success Bits1 ws1 =>
         match Generate ws1 with
             DRBG_functions.generate_algorithm_success Bits2 ws2 =>
             CheckWS ws0 Value0 Key0 1 /\ CheckWS ws1 Value1 Key1 2 /\  
             CheckWS ws2 Value2 Key2 3 /\ Bits2 = hexstring_to_Zlist Bits
         | err => False
         end
    | err => False
    end.

Lemma Check_8424_8625_COUNT0: 
      Check_8424_8625
  (*entropy*) "ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488" 
  (*nonce*)   "659ba96c601dc69fc902940805ec0ca8"
  (*Value0*)  "e75855f93b971ac468d200992e211960202d53cf08852ef86772d6490bfb53f9"
  (*Key1*)    "302a4aba78412ab36940f4be7b940a0c728542b8b81d95b801a57b3797f9dd6e"
  Value0_1 Key0_1 
  (*ReturnedBits*) "e528e9abf2dece54d47c7e75e5fe302149f817ea9fb4bee6f4199697d04d5b89d54fbb978a15b5c443c9ec21036d2460b6f73ebad0dc2aba6e624abf07745bc107694bb7547bb0995f70de25d6b29e2d3011bb19d27676c07162c8b5ccde0668961df86803482cb37ed6d5c0bb8d50cf1f50d476aa0458bdaba806f48be9dcb8"
  Value0_2 Key0_2.
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT1: 
      Check_8424_8625
      "79737479ba4e7642a221fcfd1b820b134e9e3540a35bb48ffae29c20f5418ea3"
      "3593259c092bef4129bc2c6c9e19f343"
      "b57cb403b6cd62860139c3484c9a5998fd0d82670846a765a87c9ead65f663c5"
	    "587959c1169cc9a308506ea52c2648cebf4498a35d71f6329e457ecc3204ca50"
      "1d495eef7761b65dccd0a983d2d7204fea28b5c81f1758046e062eb043755ea1"
	    "48f38d0c6a344959cc94502b7b5e8dffb6a5f41795d9066fc9a649557167ee2f"
      "cf5ad5984f9e43917aa9087380dac46e410ddc8a7731859c84e9d0f31bd43655b924159413e2293b17610f211e09f770f172b8fb693a35b85d3b9e5e63b1dc252ac0e115002e9bedfb4b5b6fd43f33b8e0eafb2d072e1a6fee1f159df9b51e6c8da737e60d5032dd30544ec51558c6f080bdbdab1de8a939e961e06b5f1aca37"
      "3d52cfa76ba57ef836fc507390fac83fbebd81799604f0a9beaf60874dabc5e9"
	    "9356bdc03c35b21e600892ed64f8efc8edcaf19258fa987b56b8eb0e13a07ff1".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT2:
      Check_8424_8625
           "b340907445b97a8b589264de4a17c0bea11bb53ad72f9f33297f05d2879d898d"
           "65cb27735d83c0708f72684ea58f7ee5"
	           "0b8e71f560cbe2b358684fc682ba7837480017785266d698a49c0bdf02a65eda"
	           "f35c29e8db08c1b947ad0263cf3dbe735d74abb99c021728c3c9235a7cdb0bbf"
	           "6a66c83034d1f48cfc9fa7708c643792e790e9a25ed0e2f479f481d833343366"
	           "f943ed975c2013dbc9dc1025d7c3ebaa463bc1e4368df1c04348677e5148c9b7"
             "75183aaaf3574bc68003352ad655d0e9ce9dd17552723b47fab0e84ef903694a32987eeddbdc48efd24195dbdac8a46ba2d972f5808f23a869e71343140361f58b243e62722088fe10a98e43372d252b144e00c89c215a76a121734bdc485486f65c0b16b8963524a3a70e6f38f169c12f6cbdd169dd48fe4421a235847a23ff"
	           "d508c96ba979c61a2034d1f6335fe7e967da7fec6752d0cb09de2530eca537d3"
	           "6b1e253f4cfd379ce55e9659dc97fe7c24f07ee54648807a2f72c5faf2dd1d35".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT3: 
      Check_8424_8625
           "8e159f60060a7d6a7e6fe7c9f769c30b98acb1240b25e7ee33f1da834c0858e7"
           "c39d35052201bdcce4e127a04f04d644"
	           "ec970281607ce9a5e6fec81f018351173f7ea2accaa00d2e229c91f86c255eea"
	           "491e895a4bc06253db3c0410616a9a4935d02713e37aa25ab65849d0128ba270"
	           "ef605c0169af189955b413449028ff4279401c66dd1c050c26ff506d736e31fc"
	           "411a2ab43a06f1811c223503c9791df80e6a1d2d52aa955500b65b90adf3ea72"
           "62910a77213967ea93d6457e255af51fc79d49629af2fccd81840cdfbb4910991f50a477cbd29edd8a47c4fec9d141f50dfde7c4d8fcab473eff3cc2ee9e7cc90871f180777a97841597b0dd7e779eff9784b9cc33689fd7d48c0dcd341515ac8fecf5c55a6327aea8d58f97220b7462373e84e3b7417a57e80ce946d6120db5"
	           "e173654682d55066b870e1c82acca0026581919fca0ed03f5a410f310464968e"
	           "1866622117806c6cbaa148fc8edf5181e9a85d2013c54f3d24b7f2c15bf4a6d8".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT4: 
      Check_8424_8625
           "74755f196305f7fb6689b2fe6835dc1d81484fc481a6b8087f649a1952f4df6a"
           "c36387a544a5f2b78007651a7b74b749"
	           "b80f5b61e4095fc3191d9abd3f64ae42eaf59062f6f1c9d0302f3192addd9d0f"
	           "9adfb5d44f961fc5e8dd8392a2faed6b7ea120be0390aed78aec9a0f0ad96ba4"
	           "2459df9b9298b87758fee7eb96fcef9417d7bcedfaedf051179b5308f6affbda"
	           "3529765f9d1b3a4e4d2aa1f76b79078c13e491dd084c91c9c60a1ca71d136cb5"
           "b2896f3af4375dab67e8062d82c1a005ef4ed119d13a9f18371b1b873774418684805fd659bfd69964f83a5cfe08667ddad672cafd16befffa9faed49865214f703951b443e6dca22edb636f3308380144b9333de4bcb0735710e4d9266786342fc53babe7bdbe3c01a3addb7f23c63ce2834729fabbd419b47beceb4a460236"
	           "77b52d69a686cd0ec28905a8cdb3579f2e429a5a8a4403842d81faf3c72f768a"
	           "b13c4e2404d451638990a1c93cf61ec24ee9786170c03381d555caf34462d9e5".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT5: 
      Check_8424_8625
           "4b222718f56a3260b3c2625a4cf80950b7d6c1250f170bd5c28b118abdf23b2f"
           "7aed52d0016fcaef0b6492bc40bbe0e9"
	           "b52d87fcf3249f61e9c73af4c3e0c949579aa580dd7271399b22490671a49792"
	           "f4157eb3844c88ea985e1236683431b882b70b63db891750ab3f41b4e02819f6"
	           "f55a1cb5c058c5c6650e05018a7d9ea5e5cc427d1af9ca89ccf5ef59852ece80"
	           "f247aad1bbc398152cd0d6c9f84c0e7c8b98289ced8768bf0708efc0a90ab10f"
           "a6da029b3665cd39fd50a54c553f99fed3626f4902ffe322dc51f0670dfe8742ed48415cf04bbad5ed3b23b18b7892d170a7dcf3ef8052d5717cb0c1a8b3010d9a9ea5de70ae5356249c0e098946030c46d9d3d209864539444374d8fbcae068e1d6548fa59e6562e6b2d1acbda8da0318c23752ebc9be0c1c1c5b3cf66dd967"
	           "dec827fc18d3c9691663d4bb6dd4a5202b6432549976e374ab33f4d8d9321e04"
	           "4bf638e7f1e0c50014336ea17dc5f7b83ced0b780fba1c88abb5025a8bec6f28".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT6: 
      Check_8424_8625
           "b512633f27fb182a076917e39888ba3ff35d23c3742eb8f3c635a044163768e0"
           "e2c39b84629a3de5c301db5643af1c21"
	           "e46a05a9268ecc00ecc3310947baa11d1ccd42cedd0ed80d78b6fb43bfd1b903"
	           "4038798b0b8bfc7be148adbdeacaf082155c46bbc86538d574aaeb0f187c52fc"
	           "759926760ecbb5c000992227f1065c18cbff9a5aaec38911d6e7a399bab4783b"
	           "5464d1f719fff5cda06a0ee358b18b8a9d8dfa3525d461f343f1a3be5138fa9a"
           "fb931d0d0194a97b48d5d4c231fdad5c61aedf1c3a55ac24983ecbf38487b1c93396c6b86ff3920cfa8c77e0146de835ea5809676e702dee6a78100da9aa43d8ec0bf5720befa71f82193205ac2ea403e8d7e0e6270b366dc4200be26afd9f63b7e79286a35c688c57cbff55ac747d4c28bb80a2b2097b3b62ea439950d75dff"
	           "cad9c856f921f6a248e0db4b3356e06e205fd9a15980030e1d32a303f4278329"
	           "df2103bf3d5dd0d60870042d702478272caef5198ff71441a772d705f28ee760".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT7: 
      Check_8424_8625
           "aae3ffc8605a975befefcea0a7a286642bc3b95fb37bd0eb0585a4cabf8b3d1e"
           "9504c3c0c4310c1c0746a036c91d9034"
	           "4e24e7f387135fdc233ad60089c247c568573a97aac6420ddc581b76e7a3d663"
	           "57dcea5091d3f590da9046aa835e2af193d323e4dea4cd68dc8d655838b64205"
	           "2071b79328ba1641521fc7f266b07d03ef2a11b80f4d05a483bcb2590b18bdc2"
	           "724d8b8a6d067981150eb9eb32056fed40b5f7b9bc50090160832d413d97e833"
           "2819bd3b0d216dad59ddd6c354c4518153a2b04374b07c49e64a8e4d055575dfbc9a8fcde68bd257ff1ba5c6000564b46d6dd7ecd9c5d684fd757df62d85211575d3562d7814008ab5c8bc00e7b5a649eae2318665b55d762de36eba00c2906c0e0ec8706edb493e51ca5eb4b9f015dc932f262f52a86b11c41e9a6d5b3bd431"
	           "68ab4d6d3b44ec6dc2ef35724a3208a985e1e100f74497519a2044f77e02e354"
	           "ded598669683bf021fa00809a363e41526267e1e7155a70fe82f0a1562a7e4d6".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT8: 
      Check_8424_8625
           "b9475210b79b87180e746df704b3cbc7bf8424750e416a7fbb5ce3ef25a82cc6"
           "24baf03599c10df6ef44065d715a93f7"
	           "0a56aaa8f57f86d4a9a9c7e521eb4dba4f1d2e8c6299d4b0119743301a773b4b"
	           "ef6511082b20d91b4000d64c0e9e65948b61a17192c06ec3cad37d7d5c6da8be"
	           "379cfe13adaf62721639ca8ea5c5765f84fdb62e13cc0fc9588dd76d55d998db"
	           "490bdfd0c62f8170bdb3dab563422c44532c7b681b6df981d7f370f95d16dd93"
           "ae12d784f796183c50db5a1a283aa35ed9a2b685dacea97c596ff8c294906d1b1305ba1f80254eb062b874a8dfffa3378c809ab2869aa51a4e6a489692284a25038908a347342175c38401193b8afc498077e10522bec5c70882b7f760ea5946870bd9fc72961eedbe8bff4fd58c7cc1589bb4f369ed0d3bf26c5bbc62e0b2b2"
	           "0305ffc83c199fdd6a769297ac73515a48cc86875371bdae35f42d0cb017e405"
	           "a77464143df2ad8a6c1020c329bb3e3400c27510825d09e3295441a6afcb32d5".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT9: 
      Check_8424_8625
           "27838eb44ceccb4e36210703ebf38f659bc39dd3277cd76b7a9bcd6bc964b628"
           "39cfe0210db2e7b0eb52a387476e7ea1"
	           "0fd98ec7cbed31cdea2ae2277da8576ceec36ced6dbb0311b8a6630a5b35435a"
	           "62681fcae70946fff0f5b0bd93f301b3e36d5c2fad16de861b633428b499faf4"
	           "229b1234314bf8fb5d7731255269039326b9648547814c0db17f892fafdb5409"
	           "e7152de68da8ead95e2febdb07e5f3051528150b06f4bc0636b3590ecc5280ec"
           "e5e72a53605d2aaa67832f97536445ab774dd9bff7f13a0d11fd27bf6593bfb52309f2d4f09d147192199ea584503181de87002f4ee085c7dc18bf32ce5315647a3708e6f404d6588c92b2dda599c131aa350d18c747b33dc8eda15cf40e95263d1231e1b4b68f8d829f86054d49cfdb1b8d96ab0465110569c8583a424a099a"
	           "5a7f36b8c43240f70dfe0190c316fefcf1de99a4bf59e5f026de39744e583fc6"
	           "d1c0b5a886b12810870649c63a072cfd00398e39c4ac4febc441613b58eabfda".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT10: 
      Check_8424_8625
           "d7129e4f47008ad60c9b5d081ff4ca8eb821a6e4deb91608bf4e2647835373a5"
           "a72882773f78c2fc4878295840a53012"
	           "e831c88f8d20edd22c2ec13b094a9140e1bddb1e19c5041dd5079b37971d9ab2"
	           "7576fc90ab884d2cb9c7d094e15815364f61914521e884677c6796848c28f35c"
	           "2754f712659eed4901cc412f024961bf6d9431ebcd335cbe0ac801f465dc5b74"
	           "7d34b1e97e698c50b093fbaaa0c784e433217cf8aa09dcc6e79fae5db2ca61e6"
           "0cbf48585c5de9183b7ff76557f8fc9ebcfdfde07e588a8641156f61b7952725bbee954f87e9b937513b16bba0f2e523d095114658e00f0f3772175acfcb3240a01de631c19c5a834c94cc58d04a6837f0d2782fa53d2f9f65178ee9c837222494c799e64c60406069bd319549b889fa00a0032dd7ba5b1cc9edbf58de82bfcd"
	           "c08544bcbf95f2b33ecb23c5a6ca6b6d92bffab469b455219a5539279bc49180"
	           "ad9747ac2827e73be2d4ff3ad6d8839133011b41e08d8192ba73c4f6bf674121".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT11: 
      Check_8424_8625
           "67fe5e300c513371976c80de4b20d4473889c9f1214bce718bc32d1da3ab7532"
           "e256d88497738a33923aa003a8d7845c"
	           "4cff638a9926fd3d53055516bd146ed44998b09cff0e8fb8fb10f78609e83068"
	           "7a405e4a25411acb4844ba4de5868d18e58ecd3d5c0bba99e2a951324f2bca2c"
	           "95c739f113888a5501e52d9fdb3d05e501cc540736427d69d45eaacf66c482dc"
	           "1862b846d878a8c47436ec1d6127d86cfc0db6fe56b616d3abaae6785d1702a0"
           "b44660d64ef7bcebc7a1ab71f8407a02285c7592d755ae6766059e894f694373ed9c776c0cfc8594413eefb400ed427e158d687e28da3ecc205e0f7370fb089676bbb0fa591ec8d916c3d5f18a3eb4a417120705f3e2198154cd60648dbfcfc901242e15711cacd501b2c2826abe870ba32da785ed6f1fdc68f203d1ab43a64f"
	           "5548a575ed45f11bdc19fea5e36dc9576acb52b8749cc4c4eb9cdd654d0480f2"
	           "e2c7d0c90a3f2e5c700f3baf6da6034bc2853bb67f780dc2ba8dd91acdd97cc4".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT12: 
      Check_8424_8625
           "de8142541255c46d66efc6173b0fe3ffaf5936c897a3ce2e9d5835616aafa2cb"
           "d01f9002c407127bc3297a561d89b81d"
	           "162b13fdafaecf6c2d8dbfc2e40a84ce707691f741030a0d34c28d36af4362f2"
	           "3dc0ae423330c460c1826ab18a6d36a01b403df4de6f30ed5639675665f05404"
	           "24a754abec7a6ec4b07d8b48279decee1811c358161db99d6ff0a1714c7e72e8"
	           "c61d8bac12a52c7860d82c609a3510bdf08d09248b69642da940f31c93f7ce94"
           "64d1020929d74716446d8a4e17205d0756b5264867811aa24d0d0da8644db25d5cde474143c57d12482f6bf0f31d10af9d1da4eb6d701bdd605a8db74fb4e77f79aaa9e450afda50b18d19fae68f03db1d7b5f1738d2fdce9ad3ee9461b58ee242daf7a1d72c45c9213eca34e14810a9fca5208d5c56d8066bab1586f1513de7"
	           "a987482b7b585e85a5068836b4019409bd5f0b731d88065d19b0c661f76bc3ce"
	           "e2a4ca79624ba4de60ba270f2ee630421d2ecd25c3e07970a44e888791e97398".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT13: 
      Check_8424_8625
           "4a8e0bd90bdb12f7748ad5f147b115d7385bb1b06aee7d8b76136a25d779bcb7"
           "7f3cce4af8c8ce3c45bdf23c6b181a00"
	           "f85a9ec074983762f1d47fc6bf4d348a4faa10b44bf1405e4e5840ed0c8a6697"
	           "9ad22f80df3e06707cc379025be8cbb5c4a3276a0d270048935e503b568d7e07"
	           "660f90cd93a771ef5cf53f564a90cb0470811763ec7c8aad508534b183f5f20f"
	           "6b976808298e4533d6e512e8ec7266437a3f07c7892cc61f92c3728c013d7db3"
           "320c7ca4bbeb7af977bc054f604b5086a3f237aa5501658112f3e7a33d2231f5536d2c85c1dad9d9b0bf7f619c81be4854661626839c8c10ae7fdc0c0b571be34b58d66da553676167b00e7d8e49f416aacb2926c6eb2c66ec98bffae20864cf92496db15e3b09e530b7b9648be8d3916b3c20a3a779bec7d66da63396849aaf"
	           "3ee6e05109b0bbafab95d7e655d2f5a5b1e130cab921dd74210397e1eccaaf5c"
	           "76f620017cb5600c32283f2d065e0d905c9b6b385e1097365cea54c7dc8df765".
Proof. vm_compute; auto. Qed.

Lemma Check_8424_8625_COUNT14: 
      Check_8424_8625
           "451ed024bc4b95f1025b14ec3616f5e42e80824541dc795a2f07500f92adc665"
           "2f28e6ee8de5879db1eccd58c994e5f0"
	           "fcc4d72fbbaab8ab9b461fb37f122fa43ed9250c492d0c7d6530f40afc181593"
	           "08ad47bfefbad762076bcdcf219df03a7114c4f3e152e72b47cdf054eb4b5dc1"
	           "27c2edd9fe08e69f2a7729fa9c1bd5216647bea05b962fa92a21f44a33f94989"
	           "b3add48b1df4d7c996bb2364ab9a84efb9ea9e60ef2c92136303a21898220adb"
           "3fb637085ab75f4e95655faae95885166a5fbb423bb03dbf0543be063bcd48799c4f05d4e522634d9275fe02e1edd920e26d9accd43709cb0d8f6e50aa54a5f3bdd618be23cf73ef736ed0ef7524b0d14d5bef8c8aec1cf1ed3e1c38a808b35e61a44078127c7cb3a8fd7addfa50fcf3ff3bc6d6bc355d5436fe9b71eb44f7fd"
	           "89c4b1031e90c49a10d0ed44a734f652b95a701b89871d08d1d6dbae3a27b6da"
	           "84ada90f5a8530922ae907c1eac4a5513a80fd7299062dcb0dc75b3e17e7b589".
Proof. vm_compute; auto. Qed.

End TestSection8424_8625.