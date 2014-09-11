Require Import Integers.
Require Import Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. 

Require Import sha.SHA256.
Require Import sha.functional_prog.
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

(*SHA256: blocksize = 64bytes=512bits; 
    corresponds to 
    #define SHA_LBLOCK	16
    #define SHA256_CBLOCK	(SHA_LBLOCK*4) *)

Lemma firstn_app1: forall {A} n (p l: list A),
  (n <= Datatypes.length p)%nat ->
   firstn n (p ++ l) = firstn n p.
Proof. intros A n.
induction n; simpl; intros. trivial.
  destruct p; simpl in H. omega.
  apply le_S_n in H. simpl. f_equal. auto. 
Qed.  

Lemma firstn_app2: forall {A} n (p l: list A),
  (n > Datatypes.length p)%nat ->
   firstn n (p ++ l) = p ++ (firstn (n-Datatypes.length p) l).
Proof. intros A n.
induction n; simpl; intros. 
  destruct p; simpl in *. trivial. omega.
  destruct p; simpl in *. trivial.
  rewrite IHn. trivial. omega. 
Qed.  

Lemma firstn_map {A B} (f:A -> B): forall n l, 
      firstn n (map f l) = map f (firstn n l).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma firstn_combine {A}: forall n (l k: list A), 
      firstn n (combine l k) = combine (firstn n l) (firstn n k).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  destruct k; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma firstn_precise {A}: forall n (l:list A), length l = n -> 
      firstn n l = l.
Proof. intros n. 
  induction n; intros; destruct l; simpl in *; trivial.
    inversion H.
    rewrite IHn; trivial. inversion H; trivial.
Qed. 

Fixpoint Nlist {A} (i:A) n: list A:=
  match n with O => nil
  | S m => i :: Nlist i m
  end.

Definition sixtyfour {A} (i:A): list A:= Nlist i 64%nat.


Lemma first64_sixtyfour {A} (a:A): 
      firstn 64 (sixtyfour a) = sixtyfour a.
Proof. apply firstn_precise. simpl. reflexivity. Qed. 

Lemma length_Nlist {A} (i:A): forall n, length (Nlist i n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma str_to_Z_length: forall k, 
      String.length k = length (str_to_Z k).
Proof. intros. induction k; simpl; auto. Qed.
  

Definition SHA256_DIGEST_LENGTH := 32.
Definition SHA256_BlockSize := 64%nat.

Axiom length_SHA256': forall l, 
  length (SHA_256' l) = Z.to_nat SHA256_DIGEST_LENGTH.

Definition Ipad := Byte.repr 54. (*0x36*)
Definition Opad := Byte.repr 92. (*0x5c*)

Module HMAC_FUN.

(*Reading rfc4231 reveals that padding happens on the right*)
Definition zeroPad (k: list Z) : list Z :=
  k ++ Nlist Z0 (SHA256_BlockSize-length k).

Definition mkKey (l:list Z) : list Z :=
  if Z.gtb (Zlength l) (Z.of_nat SHA256_BlockSize)
  then (zeroPad (SHA_256' l)) 
  else zeroPad l.

Definition mkArg (key:list byte) (pad:byte): list byte := 
       (map (fun p => Byte.xor (fst p) (snd p))
          (combine key (sixtyfour pad))).
Definition mkArgZ key (pad:byte): list Z := 
     map Byte.unsigned (mkArg key pad).

(*innerArg to be applied to message, (map Byte.repr (mkKey password)))*)
Definition innerArg (text: list Z) key : list Z :=
  (mkArgZ key Ipad) ++ text.

Definition INNER k text := SHA_256' (innerArg text k).

Definition outerArg (innerRes: list Z) key: list Z :=
  (mkArgZ key Opad) ++ innerRes.

Definition OUTER k innerRes := SHA_256' (outerArg innerRes k).

Definition HMAC txt password: list Z := 
  let key := map Byte.repr (mkKey password) in
  OUTER key (INNER key txt).

(*Definition mkKey (s:string) : list Z := mkKeyZ (str_to_Z s).*)

Definition HMACString (txt passwd:string): list Z :=
  HMAC (str_to_Z txt) (str_to_Z passwd).

Definition HMACHex (text password:string): list Z := 
  HMAC (hexstring_to_Zlist text) (hexstring_to_Zlist password).

Lemma zeroPad_BlockSize: forall k, (length k <= SHA256_BlockSize)%nat ->
  length (zeroPad k) = SHA256_BlockSize%nat.
Proof. unfold zeroPad. intros. rewrite app_length, length_Nlist. omega. 
Qed. 

Lemma mkKey_length l: length (mkKey l) = SHA256_BlockSize.
Proof. intros. unfold mkKey.
  remember (Zlength l >? Z.of_nat SHA256_BlockSize) as z. 
  destruct z. apply zeroPad_BlockSize.
    rewrite length_SHA256'.  
    apply Nat2Z.inj_le. simpl. omega. 
  apply zeroPad_BlockSize.
    rewrite Zlength_correct in Heqz. 
    apply Nat2Z.inj_le. 
    specialize (Zgt_cases (Z.of_nat (Datatypes.length l)) (Z.of_nat SHA256_BlockSize)). rewrite <- Heqz. trivial.
Qed.

Lemma mkKey_atBlockSize s: length s = SHA256_BlockSize%nat ->
      mkKey s = s.
Proof. unfold mkKey. rewrite Zlength_correct.
  intros. rewrite H.
  simpl. unfold zeroPad. rewrite H. simpl.
  apply app_nil_r.  
Qed.

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

End HMAC_FUN.
