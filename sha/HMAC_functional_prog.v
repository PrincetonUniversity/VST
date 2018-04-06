Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.

Module HP.

(*SHA256: blocksize = 64bytes
    corresponds to
    #define SHA_LBLOCK	16
    #define SHA256_CBLOCK	(SHA_LBLOCK*4) *)

Module Type HASH_FUNCTION.
  Parameter BlockSize:nat. (*measured in bytes; 64 in SHA256*)
  Parameter DigestLength: nat. (*measured in bytes; 32 in SHA256*)
  Parameter Hash : list Z -> list Z.
  Parameter Hash_isbyteZ: forall m, Forall isbyteZ (Hash m).
End HASH_FUNCTION.


Module Type HMAC_Module.
  Parameter HMAC: byte -> byte -> list Z -> list Z -> list Z.
End HMAC_Module.

Module HMAC_FUN (HF:HASH_FUNCTION)  <: HMAC_Module.

Definition sixtyfour {A} (i:A): list A:= list_repeat HF.BlockSize i.

(*Reading rfc4231 reveals that padding happens on the right*)
Definition zeroPad (k: list Z) : list Z :=
  k ++ list_repeat (HF.BlockSize-length k) Z0.

Definition mkKey (l:list Z) : list Z :=
  if Z.gtb (Zlength l) (Z.of_nat HF.BlockSize)
  then (zeroPad (HF.Hash l))
  else zeroPad l.

Definition KeyPreparation (l:list Z) : list byte := map Byte.repr (mkKey l).

Definition mkArg (key:list byte) (pad:byte): list byte :=
       (map (fun p => Byte.xor (fst p) (snd p))
          (combine key (sixtyfour pad))).
Definition mkArgZ key (pad:byte): list Z :=
     map Byte.unsigned (mkArg key pad).
(*
Definition Ipad := P.Ipad.
Definition Opad := P.Opad.
*)
(*innerArg to be applied to message, (map Byte.repr (mkKey password)))*)

Definition innerArg IP (text: list Z) key : list Z :=
  (mkArgZ key IP) ++ text.

Definition INNER IP k text := HF.Hash (innerArg IP text k).

Definition outerArg OP (innerRes: list Z) key: list Z :=
  (mkArgZ key OP) ++ innerRes.

Definition OUTER OP k innerRes := HF.Hash (outerArg OP innerRes k).

Definition HmacCore IP OP txt (key: list byte): list Z := OUTER OP key (INNER IP key txt).

Definition HASH a txt :=  HF.Hash (a ++ txt).

Definition HmacCore' IP OP txt (key: list byte): list Z :=
  HASH (mkArgZ key OP) (HASH (mkArgZ key IP) txt).

Goal forall IP OP txt key, HmacCore IP OP txt key = HmacCore' IP OP txt key.
Proof. intros. reflexivity. Qed.

Definition HMAC IP OP txt password: list Z :=
  let key := KeyPreparation password in
  HmacCore IP OP txt key.

Lemma SF_ByteRepr x: isbyteZ x ->
                     sixtyfour x =
                     map Byte.unsigned (sixtyfour (Byte.repr x)).
Proof. intros. unfold sixtyfour.
 rewrite map_list_repeat.
 rewrite Byte.unsigned_repr; trivial. destruct H.
 assert (BMU: Byte.max_unsigned = 255). reflexivity. omega.
Qed.

Lemma length_SF {A} (a:A) :length (sixtyfour a) = HF.BlockSize.
Proof. apply length_list_repeat. Qed.

Lemma isbyte_hmaccore ipad opad m k:
   Forall isbyteZ (HmacCore (Byte.repr ipad) (Byte.repr opad) m k).
Proof. apply HF.Hash_isbyteZ. Qed.

End HMAC_FUN.

End HP.
