(*A version of the functional program for hmac-sha256, 
refined to partially capture the structure of our C program*)

Require Import Integers.
Require Import Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. 

Require Import sha.SHA256.
Require Import sha.functional_prog.
Require Import sha.HMAC_functional_prog.
Module HMAC_Refined.
Definition Digest:=list Z.

Record Args := 
  { text : list Z; (*let's do the conversion from
                       string to list Z outside*)
    text_len : Z; (*alternative: int*)
    key : list Z; (*let's do the conversion from
                       string to list Z outside*)
    key_len : Z; (*alternative: int*)
    digest : Digest}.

(*All local data that's held in memory - we parametrize by type A
so that we can use the same data structure to associate shares and val's
to the individual components in the proof in HMAC_concrete.*)
Record localRecord {A:Type} :=
  { k_ipad : A;
    k_opad : A;
    tk     : A;
    tk2    : A;
    bufferIn: A;
    bufferOut: A}.

Definition Locals := @localRecord (list Z).

Record hmacState :=
  { args   : Args;
    locals : Locals
(*    k_ipad : list Z;
    k_opad : list Z;
    tk     : list Z;
    tk2    : list Z;
    bufferIn: list Z;
    bufferOut: list Z;*)
(*for the current partitioning into snippets there's
  no need to represent i
    i: int*) }. 

(*update functions for all state components that 
  are not declared const (and non-arrays)*)

Definition upd_text (s:hmacState) x : hmacState :=
 let a := args s in
 {| args := {| text := x; text_len := text_len a;
               key := key a; key_len:= key_len a;
               digest := digest a |};
    locals := locals s|}.

Definition upd_text_len (s:hmacState) x : hmacState :=
 let a := args s in
 {| args := {| text := text a; text_len := x;
               key := key a; key_len:= key_len a;
               digest := digest a |};
    locals := locals s|}.

Definition upd_key (s:hmacState) x : hmacState :=
 let a := args s in
 {| args := {| text := text a; text_len := text_len a;
               key := x; key_len:= key_len a;
               digest := digest a |};
    locals := locals s|}.

Definition upd_key_len (s:hmacState) x : hmacState :=
 let a := args s in
 {| args := {| text := text a; text_len := text_len a;
               key := key a; key_len:= x;
               digest := digest a |};
    locals := locals s|}.

Definition upd_digest (s:hmacState) x : hmacState :=
 let a := args s in
 {| args := {| text := text a; text_len := text_len a;
               key := key a; key_len:= key_len a;
               digest := x |};
    locals := locals s|}.

Definition upd_k_ipad (s:hmacState) x : hmacState :=
 {| args := args s;
    locals := {| k_ipad := x;
                   k_opad := k_opad (locals s);
                   tk:= tk (locals s);
                   tk2:= tk2 (locals s);
                   bufferIn:= bufferIn (locals s);
                   bufferOut:= bufferOut (locals s) |} |}.

Definition upd_k_opad (s:hmacState) x : hmacState :=
 {| args := args s;
    locals := {| k_ipad := k_ipad (locals s);
                   k_opad := x;
                   tk:= tk (locals s);
                   tk2:= tk2 (locals s);
                   bufferIn:= bufferIn (locals s);
                   bufferOut:= bufferOut (locals s) |} |}.

Definition upd_tk (s:hmacState) x : hmacState :=
 {| args := args s;
    locals := {| k_ipad := k_ipad (locals s);
                   k_opad := k_opad (locals s);
                   tk:= x;
                   tk2:= tk2 (locals s);
                   bufferIn:= bufferIn (locals s);
                   bufferOut:= bufferOut (locals s) |} |}.

Definition upd_tk2 (s:hmacState) x : hmacState :=
 {| args := args s;
    locals := {| k_ipad := k_ipad (locals s);
                   k_opad := k_opad (locals s);
                   tk:= tk (locals s);
                   tk2:= x;
                   bufferIn:= bufferIn (locals s);
                   bufferOut:= bufferOut (locals s) |} |}.

Definition upd_bufferIn (s:hmacState) x : hmacState :=
 {| args := args s;
    locals := {| k_ipad := k_ipad (locals s);
                   k_opad := k_opad (locals s);
                   tk:= tk (locals s);
                   tk2:= tk2 (locals s);
                   bufferIn:= x;
                   bufferOut:= bufferOut (locals s) |} |}.

Definition upd_bufferOut (s:hmacState) x : hmacState :=
 {| args := args s;
    locals := {| k_ipad := k_ipad (locals s);
                   k_opad := k_opad (locals s);
                   tk:= tk (locals s);
                   tk2:= tk2 (locals s);
                   bufferIn:= bufferIn (locals s);
                   bufferOut:= x|} |}.

Definition SNIPPET:Type := hmacState -> hmacState.

(*First code snippet: key fiddling*)
Definition snippet1:SNIPPET := fun s =>
  if Z.gtb (key_len (args s)) (Z.of_nat SHA256_BlockSize)
  then let kk := SHA_256' (key (args s))
       in upd_key_len (upd_key (upd_tk s kk) kk) SHA256_DIGEST_LENGTH
  else s.

Definition Memcpy (old newfrag : list Z) n:list Z:=
   newfrag ++ (skipn n old).

Lemma length_Memcpy old newfrag: 
  (length old >= length newfrag)%nat ->
   length (Memcpy old newfrag (length newfrag)) = length old.
Proof. intros.
  unfold Memcpy. rewrite app_length, skipn_length; trivial.
    omega. 
Qed. 

(*Second snippet: initializing ipad, opad, *)
Definition snippet2:SNIPPET := fun s =>
  let s1 := upd_k_ipad s (Nlist Z0 (length (k_ipad (locals s)))) in
  let s2 := upd_k_opad s1 (Nlist Z0 (length (k_opad (locals s1)))) in
  let s3 := upd_k_ipad s2 
             (Memcpy (k_ipad (locals s2)) (key (args s2)) 
               (Z.to_nat (key_len (args s2)))) in
  upd_k_opad s3
             (Memcpy (k_opad (locals s3)) (key (args s3)) 
               (Z.to_nat (key_len (args s3)))).

(***** SNIPPET 3: xoring key onto ipad and opad. ******)
Definition mkArg (key:list byte) (pad:byte): list byte := 
       (map (fun p => Byte.xor (fst p) (snd p))
          (combine key (sixtyfour pad))).
Definition mkArgZ key (pad:byte): list Z := 
     map Byte.unsigned (mkArg key pad).

Definition snippet3: SNIPPET:= fun s =>
  let s1:= upd_k_ipad s 
         (mkArgZ (map Byte.repr (k_ipad (locals s))) Ipad) in
  upd_k_opad s1 
         (mkArgZ (map Byte.repr (k_opad (locals s1))) Opad).

(*We're not capturing the fact that i=64 at loop exit, and
  could indeed omit i from the record*) 


(***** SNIPPET 4: prepare for inner application of SHA **************)

Definition snippet4:SNIPPET := fun s =>
  let s1 := upd_bufferIn s (Nlist Z0 1024) in 
  let s2 := upd_bufferIn s1
            (Memcpy (bufferIn (locals s1)) 
                    (k_ipad (locals s1)) SHA256_BlockSize) in 
  upd_bufferIn s2
            ((firstn SHA256_BlockSize (bufferIn (locals s2))) 
             ++ (text (args s2)))
           (*maybe we should again add the trailing 
              zeros here? No, since the ensuing call to sha
             passes only the nonzero prefix*).

(******* SNIPPET 5: inner application of SHA **********************)
Definition snippet5 s := upd_tk2 s (SHA_256' (bufferIn (locals s))).

(****** SNIPPET 6: prepare for outer application of SHA ************)

Definition snippet6:SNIPPET := fun s =>
  let s1 := upd_bufferOut s (Nlist Z0 1024) in 
  let s2 := upd_bufferOut s1
            (Memcpy (bufferOut (locals s1)) (k_opad (locals s1)) SHA256_BlockSize) in 
  upd_bufferOut s2
            ((firstn SHA256_BlockSize (bufferOut (locals s2))) ++ (tk2 (locals s2)))
           (*maybe we should again add the trailing 
              zeros here? No, since the ensuing call to sha
             passes only the nonzero prefix*).

(******* SNIPPET 7: inner application of SHA **********************)
Definition snippet7 s := upd_digest s (SHA_256' (bufferOut (locals s))).

(***** Put together the code ****)

Definition RES:Type := unit. (*ie void*)
Definition CODE:Type := Args -> Args * RES. 
(*The rest of hmacState is allocated locally, and deallocated 
  upon function return*)

Definition initLocalVals: Locals :=
{| k_ipad := Nlist Z0 64;
                   k_opad := Nlist Z0 64;
             (*    k_ipad := Nlist Z0 65;
                   k_opad := Nlist Z0 65; *)
                   tk:= Nlist Z0 32;
                   tk2:= Nlist Z0 32;
                   bufferIn:= Nlist Z0 1024;
                   bufferOut:= Nlist Z0 1024 |}.

Definition initialHmacState (a: Args): hmacState :=
 {| args := a;
    locals := initLocalVals
    (*i:= Int.zero*) |}.

Definition RefinedHMAC: CODE := fun a =>
  let s0 := initialHmacState a in
  let s := snippet7 (snippet6 (snippet5 (snippet4 
             (snippet3 (snippet2 (snippet1 s0))))))
  in (args s,tt).

Definition mkArgs (txt password:list Z):Args :=
  {| text := txt;
     text_len := Zlength txt;
     key := password;
     key_len := Zlength password;
     digest := nil |}.

Definition HMAC_A txt pwd := 
  let a := mkArgs txt pwd in fst (RefinedHMAC a).

Definition HMAC txt pwd := digest (HMAC_A txt pwd).

Definition HMACString (txt password:string): list Z := 
  HMAC (str_to_Z txt) (str_to_Z password).

Definition HMACHex (txt password:string): list Z :=
  HMAC (hexstring_to_Zlist txt) 
       (hexstring_to_Zlist password).

Definition check password text digest := 
  listZ_eq (HMACString text password) (hexstring_to_Zlist digest) = true.

Definition checkHex password text digest := 
  listZ_eq (HMACHex text password) (hexstring_to_Zlist digest) = true.

(*a random example, solution obtained via 
  http://www.freeformatter.com/hmac-generator.html#ad-output*)
Goal check "bb" "aa"
      "c1201d3dccfb84c069771d07b3eda4dc26e5b34a4d8634b2bba84fb54d11e265". 
vm_compute. reflexivity. Qed.

Lemma RFC4231_example4_2: 
  check "Jefe" "what do ya want for nothing?" 
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

Lemma firstN_Memcpy: forall p L N,
  firstn N (Memcpy L p N) = firstn N (p ++ skipn N L).
Proof. intros. reflexivity. Qed. 

Lemma firstN_Memcpy' p L N N': (N' <= Datatypes.length p)%nat ->
  firstn N' (Memcpy L p N) = firstn N' p. 
Proof. intros. unfold Memcpy. 
 apply firstn_app1. trivial.
Qed.

Lemma firstn_mkArgsZ key pad:
  (Datatypes.length key >= 64)%nat ->
  firstn SHA256_BlockSize (mkArgZ key pad) = (mkArgZ key pad).
Proof. intros. apply firstn_precise. 
unfold mkArgZ, mkArg.
rewrite map_length.  
rewrite map_length.  
rewrite combine_length.
unfold SHA256_BlockSize. simpl.
apply Min.min_r.
apply H.
Qed. 

Lemma BufferInSN4 s:
  bufferIn (locals (snippet4 s)) = 
      (firstn SHA256_BlockSize 
              (Memcpy (Nlist Z0 1024) (k_ipad (locals s)) SHA256_BlockSize)) 
      ++ (text (args s)).
Proof. reflexivity. Qed. 

Lemma k_ipad_SN3: forall s,
  k_ipad (locals (snippet3 s)) = 
  mkArgZ (map Byte.repr (k_ipad (locals s))) Ipad.
Proof. intros. reflexivity. Qed.

Lemma k_ipad_SN2: forall s,
  k_ipad (locals (snippet2 s)) = 
    Memcpy (Nlist 0 (Datatypes.length (k_ipad (locals s)))) (key (args s))
      (Z.to_nat (key_len (args s))).
Proof. intros. simpl. reflexivity. Qed.

Lemma k_ipad_SN1 s:
  k_ipad (locals (snippet1 s)) = k_ipad (locals s).
Proof. intros. unfold snippet1. simpl.
  remember (key_len (args s) >? 64) as d. 
  destruct d; simpl; trivial.
Qed.

Lemma key_SN1 s:
  key (args (snippet1 s)) = 
  if key_len (args s) >? 64 
  then SHA_256' (key (args s))
  else key (args s).
Proof. intros. unfold snippet1. simpl.
  remember (key_len (args s) >? 64) as d. 
  destruct d; simpl; trivial.
Qed.

Lemma keylen_SN1 s:
  key_len (args (snippet1 s)) = 
  if key_len (args s) >? 64 
  then SHA256_DIGEST_LENGTH
  else key_len (args s).
Proof. intros. unfold snippet1. simpl.
  remember (key_len (args s) >? 64) as d. 
  destruct d; simpl; trivial. 
Qed.

Definition Post1 (txt password:list Z): hmacState := 
  let a := mkArgs txt password in
  let kk := SHA_256' (key a) in
  {| args :=  {| text := text a; 
                 text_len := text_len a;
                 key := if Z.gtb (key_len a)
                          (Z.of_nat SHA256_BlockSize)
                        then kk else key a; 
                 key_len:= if Z.gtb (key_len a)
                              (Z.of_nat SHA256_BlockSize)
                           then SHA256_DIGEST_LENGTH else key_len a;
                 digest := digest a |};
    locals := {| k_ipad := Nlist Z0 64;
                   k_opad := Nlist Z0 64;
             (*    k_ipad := Nlist Z0 65;
                   k_opad := Nlist Z0 65;*)
                   tk:= if Z.gtb (key_len a) (Z.of_nat SHA256_BlockSize)
                        then kk 
                        else Nlist Z0 (Z.to_nat SHA256_DIGEST_LENGTH);
                   tk2:= Nlist Z0 32;
                   bufferIn:= Nlist Z0 1024;
                   bufferOut:= Nlist Z0 1024 |}
(*    i:= Int.zero*) |}.
(*
Lemma length_ipad_Post1 txt passwd:
 length (k_ipad (Post1 txt passwd)) = 65%nat.
Proof. simpl. reflexivity. Qed.*)
Lemma length_ipad_Post1 txt passwd:
 length (k_ipad (locals (Post1 txt passwd))) = 64%nat.
Proof. simpl. reflexivity. Qed.

Lemma key_Post1_A txt passwd:
  Zlength passwd > 64 ->
  key (args (Post1 txt passwd)) = SHA_256' passwd.
Proof. intros. simpl.
  remember (Zlength passwd >? 64) as d. 
  destruct d; trivial. 
    specialize (Zgt_cases (Zlength passwd) 64). 
    rewrite <- Heqd. intros. exfalso. omega. 
Qed.

Lemma length_key_Post1_A txt passwd:
  Zlength passwd > 64 ->
  length (key (args (Post1 txt passwd))) = 32%nat.
Proof. intros. rewrite (key_Post1_A _ _ H), length_SHA256'. trivial. 
Qed. 

Lemma keylen_Post1_A txt passwd:
  Zlength passwd > 64 ->
  key_len (args (Post1 txt passwd)) = 32.
Proof. intros. simpl.
  remember (Zlength passwd >? 64) as d. 
  destruct d; trivial. 
    specialize (Zgt_cases (Zlength passwd) 64). 
    rewrite <- Heqd. intros. exfalso. omega. 
Qed.

Lemma key_Post1_B txt passwd:
  Zlength passwd <= 64 ->
  key (args (Post1 txt passwd)) = passwd.
Proof. intros. simpl.
  remember (Zlength passwd >? 64) as d. 
  destruct d; trivial. 
    specialize (Zgt_cases (Zlength passwd) 64). 
    rewrite <- Heqd. intros. exfalso. omega. 
Qed.

Lemma length_key_Post1_B txt passwd:
  Zlength passwd <= 64 ->
  length (key (args (Post1 txt passwd))) = length passwd. 
Proof. intros. rewrite (key_Post1_B _ _ H). trivial. Qed.

Lemma keylen_Post1_B txt passwd:
  Zlength passwd <= 64 ->
  key_len (args (Post1 txt passwd)) = Zlength passwd.
Proof. intros. simpl.
  remember (Zlength passwd >? 64) as d. 
  destruct d; trivial. 
    specialize (Zgt_cases (Zlength passwd) 64). 
    rewrite <- Heqd. intros. exfalso. omega. 
Qed.

Lemma SN1 txt passwd: 
  let a := mkArgs txt passwd in
  let s := initialHmacState a in
  snippet1 s = Post1 txt passwd.
Proof.
  unfold snippet1, Post1.
  remember (mkArgs txt passwd) as a. clear Heqa.
  remember (Z.of_nat SHA256_BlockSize) as b; clear Heqb.
  remember (key_len (args (initialHmacState a)) >? b) as d.
  destruct d; simpl in Heqd; rewrite <- Heqd.
    reflexivity.
  unfold initialHmacState. 
    destruct a. reflexivity.
Qed.

Lemma lengthMemcpy1 l k n: (length (Memcpy l k n) 
  = Datatypes.length k + Datatypes.length (skipn n l))%nat.
Proof. intros.
  unfold Memcpy. rewrite app_length.  reflexivity. 
Qed.

Lemma skipn_Nlist {A} (a:A): forall n k, (n <= k)%nat ->
   skipn n (Nlist a k) = Nlist a (k - n).
Proof. induction n; simpl; intros.
  rewrite <- minus_n_O. trivial.
destruct k; simpl. omega.
  rewrite IHn. trivial. omega. 
Qed. 

Lemma ZeroPadOK l: 
      (Datatypes.length l <= 64)%nat ->
       Memcpy (Nlist 0 64) l (Z.to_nat (Zlength l)) = HMAC_FUN.zeroPad l.
Proof. intros. 
  unfold Memcpy, HMAC_FUN.zeroPad.
  unfold SHA256_BlockSize. rewrite Zlength_correct, Nat2Z.id. 
  rewrite skipn_Nlist; trivial.
Qed.   

Lemma ZeroPad_SHA_OK pwdZ: 
  Memcpy (Nlist 0 64) (SHA_256' pwdZ) (Z.to_nat 32) =
  HMAC_FUN.zeroPad (SHA_256' pwdZ).
Proof. intros. rewrite <- ZeroPadOK.
  rewrite Zlength_correct, Nat2Z.id, length_SHA256'. trivial.
  apply Nat2Z.inj_le. rewrite length_SHA256'; simpl. omega. 
Qed.

Lemma Zlength_nonneg: forall {A} (l:list A), 0 <= Zlength l.
Proof. intros.
  induction l. rewrite Zlength_nil. omega.
  rewrite Zlength_cons. omega.
Qed. 

Lemma InnerArgsOK_A (txt passwd:list Z) s
  (HP: Zlength passwd > 64):
  snippet4 (snippet3 (snippet2 (Post1 txt passwd))) = s ->
  bufferIn (locals s) = HMAC_FUN.innerArg txt
                        (map Byte.repr (HMAC_FUN.mkKey passwd)).
Proof. intros.
subst s. 
rewrite BufferInSN4.
unfold HMAC_FUN.innerArg.
f_equal.
remember (Nlist 0 1024) as NL.
rewrite k_ipad_SN3.
rewrite k_ipad_SN2, length_ipad_Post1.
rewrite firstN_Memcpy. 
rewrite (keylen_Post1_A txt _ HP).
rewrite (key_Post1_A txt _ HP).
rewrite firstn_app1.
Focus 2. unfold mkArgZ, mkArg. rewrite map_length.
  rewrite map_length. rewrite combine_length. 
  rewrite map_length, lengthMemcpy1, length_SHA256'. 
  simpl. unfold SHA256_BlockSize. omega. 
rewrite firstn_mkArgsZ.
Focus 2. rewrite map_length, lengthMemcpy1, length_SHA256'. 
         simpl. omega.
unfold mkArgZ, HMAC_FUN.mkArgZ.
unfold mkArg, HMAC_FUN.mkArg.
unfold HMAC_FUN.mkKey.
remember (Zlength passwd >? Z.of_nat SHA256_BlockSize) as d.  
destruct d. 
Focus 2. exfalso. 
  specialize (Zgt_cases (Zlength passwd)
             (Z.of_nat SHA256_BlockSize)). 
  rewrite <- Heqd. simpl. intros. omega. 
rewrite ZeroPad_SHA_OK. trivial. 
Qed.

Lemma InnerArgsOK_B (txt passwd:list Z) s
  (HP: Zlength passwd <= 64):
  snippet4 (snippet3 (snippet2 (Post1 txt passwd))) = s ->
  bufferIn (locals s) = HMAC_FUN.innerArg txt
                        (map Byte.repr (HMAC_FUN.mkKey passwd)).
Proof. intros.
subst s. 
rewrite BufferInSN4.
unfold HMAC_FUN.innerArg.
f_equal.
remember (Nlist 0 1024) as NL.
rewrite k_ipad_SN3.
rewrite k_ipad_SN2, length_ipad_Post1.
rewrite firstN_Memcpy. 
rewrite (keylen_Post1_B txt _ HP).
rewrite (key_Post1_B txt _ HP).
rewrite firstn_app1.
Focus 2. unfold mkArgZ, mkArg. rewrite map_length.
  rewrite map_length. rewrite combine_length. 
  rewrite map_length, lengthMemcpy1.
  rewrite Zlength_correct. rewrite Nat2Z.id. rewrite skipn_length.
  rewrite le_plus_minus_r. simpl. unfold SHA256_BlockSize. omega. 
  simpl. rewrite Zlength_correct in HP. 
        apply Nat2Z.inj_le. rewrite HP. simpl. omega. 
  simpl. rewrite Zlength_correct in HP. 
         apply Nat2Z.inj_le. rewrite HP. simpl. omega. 
rewrite firstn_mkArgsZ.
Focus 2. rewrite map_length, lengthMemcpy1, skipn_length, length_Nlist.
         rewrite Zlength_correct. rewrite Nat2Z.id. 
         rewrite le_plus_minus_r. omega. 
    rewrite Zlength_correct in HP. 
         apply Nat2Z.inj_le. rewrite HP. simpl. omega.
    simpl.  
         apply Nat2Z.inj_le. simpl. rewrite Z2Nat.id. omega.
         apply Zlength_nonneg. 
unfold mkArgZ, HMAC_FUN.mkArgZ.
unfold mkArg, HMAC_FUN.mkArg.
unfold HMAC_FUN.mkKey.
remember (Zlength passwd >? Z.of_nat SHA256_BlockSize) as d.  
destruct d. exfalso. 
  specialize (Zgt_cases (Zlength passwd)
             (Z.of_nat SHA256_BlockSize)). 
  rewrite <- Heqd. simpl. intros. omega. 
rewrite ZeroPadOK. trivial. 
  apply Nat2Z.inj_le. rewrite Zlength_correct in HP. trivial. 
Qed.

Lemma InnerArgs (txt passwd:list Z) s:
  snippet4 (snippet3 (snippet2 (Post1 txt passwd))) = s ->
  bufferIn (locals s) = HMAC_FUN.innerArg txt
                        (map Byte.repr (HMAC_FUN.mkKey passwd)).
Proof. intros.
  specialize (Zgt_cases (Zlength passwd) 64).
  destruct (Zlength passwd >? 64); intros. 
  eapply InnerArgsOK_A; eassumption.
  eapply InnerArgsOK_B; eassumption.
Qed.

Lemma tk2_SN5 s:
  tk2 (locals (snippet5 s)) = SHA_256' (bufferIn (locals s)).
Proof. reflexivity. Qed. 

Lemma InnerOK txt passwd s:
  snippet5 (snippet4 (snippet3 (snippet2 (Post1 txt passwd)))) = s ->
  tk2 (locals s) = SHA_256' (HMAC_FUN.innerArg txt
                        (map Byte.repr (HMAC_FUN.mkKey passwd))).
Proof. intros.
  subst s. rewrite tk2_SN5. rewrite (InnerArgs txt passwd); trivial.
Qed.

Lemma bufferOut_SN6 s: 
  bufferOut (locals (snippet6 s)) = 
  (firstn SHA256_BlockSize 
          (Memcpy (Nlist Z0 1024) (k_opad (locals s)) SHA256_BlockSize))
   ++ (tk2 (locals s)).
Proof. reflexivity. Qed. 

Lemma digest_SN7 s: 
digest (args (snippet7 s)) = SHA_256' (bufferOut (locals s)).
Proof. reflexivity. Qed.

Lemma digest_SN7' s s':
 bufferOut (locals s) = bufferOut (locals s') ->
digest (args (HMAC_Refined.snippet7 s)) = SHA_256' (bufferOut (locals s')).
Proof. intros. rewrite <- H. reflexivity. Qed.

Lemma k_opadSN_3to5 s: 
  k_opad (locals (snippet5 (snippet4 (snippet3 s)))) = 
  mkArgZ (map Byte.repr (k_opad (locals s))) Opad. 
Proof. reflexivity. Qed. 

Lemma OuterArgs (txt passwd:list Z) s:
  snippet6 (snippet5 (snippet4 (snippet3 
           (snippet2 (Post1 txt passwd))))) = s ->
   bufferOut (locals s) =
   HMAC_FUN.outerArg
     (HMAC_FUN.INNER (map Byte.repr (HMAC_FUN.mkKey passwd)) txt)
     (map Byte.repr (HMAC_FUN.mkKey passwd)). 
Proof. intros. subst s. rewrite bufferOut_SN6, tk2_SN5.
  unfold HMAC_FUN.outerArg, HMAC_FUN.INNER.
  f_equal. 
  2: rewrite (InnerArgs txt passwd); trivial.
  rewrite firstN_Memcpy'.
  Focus 2. simpl.
unfold mkArgZ, mkArg. rewrite map_length. rewrite map_length.
rewrite combine_length. rewrite map_length, lengthMemcpy1.
unfold SHA256_BlockSize. 
remember (Zlength passwd >? 64) as d. 
destruct d. rewrite length_SHA256'. simpl. omega.
simpl. rewrite skipn_length.
  rewrite Zlength_correct. rewrite Nat2Z.id. 
         rewrite le_plus_minus_r. simpl. omega. 
  simpl. specialize (Zgt_cases (Zlength passwd) 64).
      rewrite <- Heqd. 
      rewrite Zlength_correct. intros. apply Nat2Z.inj_le. simpl. trivial. 
  simpl. apply Nat2Z.inj_le. 
      specialize (Zgt_cases (Zlength passwd) 64).
      rewrite <- Heqd. 
      rewrite Z2Nat.id. simpl. trivial. 
   apply Zlength_nonneg.

rewrite k_opadSN_3to5.
rewrite firstn_mkArgsZ.
Focus 2. rewrite map_length; simpl.
         rewrite lengthMemcpy1, skipn_length.
         remember (Zlength passwd >? 64) as d. 
         destruct d. simpl. rewrite length_SHA256'. simpl. omega.
         rewrite Zlength_correct, Nat2Z.id.
         rewrite le_plus_minus_r. simpl. omega.  
          simpl. specialize (Zgt_cases (Zlength passwd) 64).
            rewrite <- Heqd. 
            rewrite Zlength_correct. intros. apply Nat2Z.inj_le. 
            simpl. trivial.
       simpl. remember (Zlength passwd >? 64) as d. 
         destruct d. simpl. apply Nat2Z.inj_le. simpl. omega. 
          specialize (Zgt_cases (Zlength passwd) 64).
            rewrite <- Heqd. 
            rewrite Zlength_correct, Nat2Z.id.
            intros. apply Nat2Z.inj_le. 
            simpl. trivial.
unfold mkArgZ, HMAC_FUN.mkArgZ.
unfold mkArg, HMAC_FUN.mkArg.
unfold HMAC_FUN.mkKey.
unfold SHA256_BlockSize. simpl.
rewrite <- ZeroPad_SHA_OK. 
remember (Zlength passwd >? 64) as d.  
destruct d; trivial.
rewrite <- ZeroPadOK. trivial.
          specialize (Zgt_cases (Zlength passwd) 64).
            rewrite <- Heqd. 
            rewrite Zlength_correct.
            intros. apply Nat2Z.inj_le. 
            simpl. trivial.
Qed.

Lemma fst_D {A B :Type} (a:A) (b:B): fst(a,b) = a.
Proof. reflexivity. Qed.

Lemma Equiv txt passwd: HMAC txt passwd = HMAC_FUN.HMAC txt passwd.
Proof.
 unfold HMAC, HMAC_A, RefinedHMAC. rewrite fst_D, digest_SN7.
  unfold HMAC_FUN.HMAC.  
  unfold HMAC_FUN.OUTER.
  rewrite (OuterArgs txt passwd). trivial. rewrite SN1; trivial. 
Qed. 
 
Lemma EquivString txt passwd: HMACString txt passwd = HMAC_FUN.HMACString txt passwd.
Proof.
 unfold HMACString, HMAC_FUN.HMACString. apply Equiv.
Qed.

Lemma EquivHex txt passwd: HMACHex txt passwd = HMAC_FUN.HMACHex txt passwd.
Proof.
 unfold HMACHex, HMAC_FUN.HMACHex. apply Equiv.
Qed.

End HMAC_Refined.

Notation text := HMAC_Refined.text.
Notation text_len := HMAC_Refined.text_len. 
Notation key := HMAC_Refined.key. 
Notation key_len := HMAC_Refined.key_len. 
Notation digest := HMAC_Refined.digest. 
Notation k_ipad := HMAC_Refined.k_ipad. 
Notation k_opad := HMAC_Refined.k_opad. 
Notation tk := HMAC_Refined.tk. 
Notation tk2 := HMAC_Refined.tk2.
Notation bufferIn := HMAC_Refined.bufferIn. 
Notation bufferOut := HMAC_Refined.bufferOut.  
Notation args := HMAC_Refined.args. 
Notation locals := HMAC_Refined.locals.  
Notation RefinedHMAC := HMAC_Refined.RefinedHMAC. 