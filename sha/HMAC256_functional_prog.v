Require Import Integers.
Require Import Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. Import ListNotations.
Require Import general_lemmas.
Require Import SHA256.
Require Import functional_prog.
Require Import HMAC_functional_prog.

Module SHA256 <: HP.HASH_FUNCTION.
  Definition BlockSize:= 64%nat.
  Definition DigestLength:= 32%nat.
  Definition Hash : list Z -> list Z := SHA_256'.
  Lemma Hash_isbyteZ m: Forall isbyteZ (SHA_256' m).
    apply isbyte_intlist_to_Zlist. Qed.
End SHA256.

Module HMAC_SHA256 := HP.HMAC_FUN SHA256.

Definition Ipad := Byte.repr 54. (*0x36*) 
Definition Opad := Byte.repr 92. (*0x5c*)

Definition HMAC256 := HMAC_SHA256.HMAC Ipad Opad.

Definition HMACString (txt passwd:string): list Z :=
  HMAC256 (str_to_Z txt) (str_to_Z passwd).

Definition HMACHex (text password:string): list Z := 
  HMAC256 (hexstring_to_Zlist text) (hexstring_to_Zlist password).

Definition check password text digest := 
  listZ_eq (HMACString text password) (hexstring_to_Zlist digest) = true.

(*a random example, solution obtained via 
  http://www.freeformatter.com/hmac-generator.html#ad-output*)
Goal check "bb" "aa"
      "c1201d3dccfb84c069771d07b3eda4dc26e5b34a4d8634b2bba84fb54d11e265". 
vm_compute. reflexivity. Qed.

Lemma RFC4231_exaple4_2: 
  check "Jefe" "what do ya want for nothing?" 
      "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843".
vm_compute. reflexivity. Qed.

Definition checkHex password text digest := 
  listZ_eq (HMACHex text password) (hexstring_to_Zlist digest) = true.

Lemma RFC6868_example4_2hex: 
  checkHex "4a656665" 
           "7768617420646f2079612077616e7420666f72206e6f7468696e673f"
           "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843".
vm_compute. reflexivity. Qed.

Lemma RFC6868_example4_5hex: 
  checkHex 
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 
    "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374"
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54".
vm_compute. reflexivity. Qed.

Lemma RFC6868_exampleAUTH256_2: 
  checkHex 
  "4a6566654a6566654a6566654a6566654a6566654a6566654a6566654a656665"
  "7768617420646f2079612077616e7420666f72206e6f7468696e673f"
  "167f928588c5cc2eef8e3093caa0e87c9ff566a14794aa61648d81621a2a40c6".
vm_compute. reflexivity. Qed.
