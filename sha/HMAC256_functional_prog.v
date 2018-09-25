Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.SHA256.
Require Import sha.functional_prog.
Require Import sha.HMAC_functional_prog.

Module SHA256 <: HP.HASH_FUNCTION.
  Definition BlockSize:= 64%nat.
  Definition DigestLength:= 32%nat.
  Definition Hash : list byte -> list byte := SHA_256'.
End SHA256.

Module HMAC_SHA256 := HP.HMAC_FUN SHA256.

Definition Ipad := Byte.repr 54. (*0x36*)
Definition Opad := Byte.repr 92. (*0x5c*)

Definition HMAC256 := HMAC_SHA256.HMAC Ipad Opad.

Definition HMACString (txt passwd:string): list byte :=
  HMAC256 (str_to_bytes txt) (str_to_bytes passwd).

Definition HMACHex (text password:string): list byte :=
  HMAC256 (hexstring_to_bytelist text) (hexstring_to_bytelist password).

Definition check password text digest :=
  bytelist_eq (HMACString text password) (hexstring_to_bytelist digest) = true.

(*a random example, solution obtained via
  http://www.freeformatter.com/hmac-generator.html#ad-output*)
Goal check "bb" "aa"
      "c1201d3dccfb84c069771d07b3eda4dc26e5b34a4d8634b2bba84fb54d11e265".
vm_compute. reflexivity. Qed.

Lemma RFC4231_Section4_3: 
  check "Jefe" "what do ya want for nothing?" 
      "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843".
vm_compute. reflexivity. Qed.

Definition checkHex password text digest :=
  bytelist_eq (HMACHex text password) (hexstring_to_bytelist digest) = true.


Lemma RFC4231_Section4_2_hex: (*called PRF-1 in RFC4868*)
  checkHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
        "4869205468657265"
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7".
vm_compute. reflexivity. Qed.

Lemma RFC4231_Section4_3_hex: (*called PRF-2 in RFC4868*)
  checkHex "4a656665"
        "7768617420646f2079612077616e7420666f72206e6f7468696e673f"
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843".
vm_compute. reflexivity. Qed.

Lemma RFC4231_Section4_4_hex: (*called PRF-3 in RFC4868*)
  checkHex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
        "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe".
vm_compute. reflexivity. Qed.

Lemma RFC4231_Section4_5_hex: (*called PRF-4 in RFC4868*)
  checkHex "0102030405060708090a0b0c0d0e0f10111213141516171819"
        "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"
        "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b".
vm_compute. reflexivity. Qed.

(*Test with a truncation of output to 128 bits, ie the first 16 bytes*)
Definition checkHexTrunc password text digest := 
  bytelist_eq (firstn 16 (HMACHex text password)) (hexstring_to_bytelist digest) = true.

Lemma RFC4231_Section4_6_hex:
  checkHexTrunc "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c"
        "546573742057697468205472756e636174696f6e"
        "a3b6167473100ee06e0c796c2955552b".
vm_compute. reflexivity. Qed.


Lemma RFC4231_Section4_7_hex: (*called PRF-5 in RFC4868*)
  checkHex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374"
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54".
vm_compute. reflexivity. Qed.

Lemma RFC4231_Section4_8_hex: (*called PRF-6 in RFC4868*)
  checkHex "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e"
        "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2".
vm_compute. reflexivity. Qed.

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
