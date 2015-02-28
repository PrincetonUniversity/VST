(* Lemmas used by the hmac proofs that are independent of C/CompCert/VST*)

Require Import Integers.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import SHA256.
Require Import sha.spec_sha.
Require Import pure_lemmas.     (* sha *)
Require Import hmac_pure_lemmas.

Require Import HMAC_functional_prog.

Lemma app_inv_length1 {A}: forall (l1 m1 l2 m2:list A),
  l1++l2 = m1++m2 -> length l1 = length m1 -> l1=m1 /\ l2=m2.
Proof.
induction l1; simpl; intros.
{ destruct m1; simpl in *. split; trivial. omega. }
{ destruct m1; simpl in *. discriminate.
  inversion H; clear H; subst a0.
  destruct (IHl1 _ _ _ H3). omega.
  subst. split; trivial. }
Qed.

Lemma app_inv_length2 {A}: forall (l1 m1 l2 m2:list A),
  l1++l2 = m1++m2 -> length l2 = length m2 -> l1=m1 /\ l2=m2.
Proof.
induction l1; simpl; intros.
{ destruct m1; simpl in *. split; trivial.
  assert (length l2 = length (a :: m1 ++ m2)). rewrite <- H; trivial.
  rewrite H1 in H0; clear H H1. simpl in H0. rewrite app_length in H0. omega. }
{ assert (length (a :: l1 ++ l2) = length (m1 ++ m2)). rewrite <- H; trivial.
  simpl in H1. do 2 rewrite app_length in H1. rewrite H0 in H1.
  destruct m1; simpl in *. omega.
  inversion H; clear H. subst a0.
  destruct (IHl1 _ _ _ H4 H0). subst. split; trivial. }
Qed.

Lemma cons_inv {A}: forall (a1 a2:A) t1 t2, a1::t1 = a2::t2 -> a1=a2 /\ t1=t2.
  intros. inversion H; split; trivial. Qed.

Lemma mod_exists a b c: a mod b = c -> b<> 0 -> exists k, k*b+c=a.
Proof. intros. specialize (Zmod_eq_full a b H0). intros.
  exists (a/b). rewrite H in H1; clear H H0. subst c. omega. Qed.

Lemma Forall2_map {A B} (f:A -> B): forall l m, 
      Forall2 (fun x y => y = f x) l m -> map f l = m.
Proof. intros.
  induction H; simpl. reflexivity.
  subst y. f_equal. trivial.
Qed.

Lemma app_inj1 {A} l2 m2: forall (l1 m1:list A) (H:l1++l2=m1++m2),
      length l1=length m1 -> l1=m1 /\ l2=m2.
Proof. induction l1.
  destruct m1; simpl; intros. split; trivial. discriminate.
  destruct m1; simpl; intros. discriminate.
  inversion H; subst. 
  destruct (IHl1 _ H3). omega.
  subst. split; trivial.
Qed.

Lemma str_to_Z_length: forall k, 
      String.length k = length (str_to_Z k).
Proof. intros. induction k; simpl; auto. Qed.

Lemma first64_sixtyfour {A} (a:A): 
      firstn 64 (HP.HMAC_SHA256.sixtyfour a) = HP.HMAC_SHA256.sixtyfour a.
Proof. apply firstn_precise. simpl. reflexivity. Qed. 

Lemma length_SF {A} (x:A): length (HP.HMAC_SHA256.sixtyfour x) = 64%nat.
Proof.
  unfold HP.HMAC_SHA256.sixtyfour.
  rewrite length_list_repeat; trivial.
Qed.

Lemma Zlength_mkArgZ k pad: Zlength (HP.HMAC_SHA256.mkArgZ k pad) = Z.of_nat (min (length k) 64).
Proof. intros. repeat rewrite Zlength_correct.
   unfold HP.HMAC_SHA256.mkArgZ, HP.HMAC_SHA256.mkArg, HP.HMAC_SHA256.sixtyfour.
   repeat rewrite map_length. 
   rewrite combine_length, length_list_repeat . trivial.
Qed.

Lemma zeropad_isbyteZ: forall l, Forall isbyteZ l -> Forall isbyteZ (HP.HMAC_SHA256.zeroPad l).
Proof. unfold isbyteZ, HP.HMAC_SHA256.zeroPad; intros.
  rewrite Forall_forall in *. intros.
  apply in_app_or in H0.
  destruct H0. apply (H _ H0).
  apply in_list_repeat in H0. (*apply In_Nlist in H0.*) subst; omega.
Qed.

Lemma unsigned_Brepr_isbyte z: isbyteZ z -> Byte.unsigned (Byte.repr z) = z.
Proof. intros. 
      unfold isbyteZ in H. apply Byte.unsigned_repr.
      unfold Byte.max_unsigned, Byte.modulus. simpl. omega.
Qed.  

Lemma map_unsigned_Brepr_isbyte: forall l, Forall isbyteZ l ->
      map Byte.unsigned (map Byte.repr l) = l.
Proof. intros. induction l; simpl in *. trivial.
   rewrite IHl. rewrite Forall_forall in H. 
   assert (In a (a::l)). left. trivial. 
   specialize (H _ H0); clear H0.
   rewrite unsigned_Brepr_isbyte; trivial.
   rewrite Forall_forall in *. intros. apply H. right; trivial.
Qed.

Lemma isByte_ByteUnsigned b: isbyteZ (Byte.unsigned b).
Proof.
  unfold Byte.unsigned, Byte.intval. destruct b.
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize in intrange.
  rewrite two_power_nat_correct in intrange.
  unfold Zpower_nat in intrange. simpl in intrange. unfold isbyteZ. omega.
Qed.

Lemma nth_zeropad_left {d d'}: forall l i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HP.HMAC_SHA256.zeroPad l) d = nth (Z.to_nat i) l d'.
Proof. unfold HP.HMAC_SHA256.zeroPad. intros.
  destruct I.
  apply Z2Nat.inj_lt in H0; try omega.
  rewrite Zlength_correct, Nat2Z.id in H0.
  rewrite app_nth1; trivial.
  apply nth_indep; trivial. 
Qed.

Lemma mkKey_left {d d'}: forall l (L: false = (Zlength l >? 64)) 
        i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HP.HMAC_SHA256.mkKey l) d = nth (Z.to_nat i) l d'.
Proof.
  unfold HP.HMAC_SHA256.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_left; trivial.
Qed.

Lemma nth_zeropad_right {d} l i (I: Zlength l <= i < 64):
      nth (Z.to_nat i) (HP.HMAC_SHA256.zeroPad l) d = Z0.
Proof. unfold HP.HMAC_SHA256.zeroPad. 
  specialize (Zlength_nonneg l). intros.
  rewrite app_nth2. rewrite nth_list_repeat'. trivial.
  apply minus_lt_compat_r. destruct I. apply Z2Nat.inj_lt in H1. apply H1.
  omega.
  omega.
  destruct I. apply Z2Nat.inj_le in H0; trivial.
    rewrite Zlength_correct, Nat2Z.id in H0. apply H0.
    omega.
  destruct I. apply Z2Nat.inj_le in H0; trivial.
    rewrite Zlength_correct, Nat2Z.id in H0. apply H0.
    omega.
Qed.


Lemma mkKey_right {d}: forall l (L: false = (Zlength l >? 64)) 
        i (I: Zlength l <= i < 64),
      nth (Z.to_nat i) (HP.HMAC_SHA256.mkKey l) d = Z0.
Proof.
  unfold HP.HMAC_SHA256.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_right; trivial.
Qed.

Lemma isbyte_map_ByteUnsigned l: Forall isbyteZ (map Byte.unsigned l).
Proof. 
  rewrite Forall_forall. intros. 
  apply list_in_map_inv in H. destruct H as [b [B1 _]]. subst x.
  apply isByte_ByteUnsigned.
Qed.

(* HP.SHA256_ changed *)

Lemma zeroPad_BlockSize: forall k, (length k <= HP.SHA256.BlockSize)%nat ->
  length (HP.HMAC_SHA256.zeroPad k) = HP.SHA256.BlockSize%nat.
Proof. unfold HP.HMAC_SHA256.zeroPad. intros. rewrite app_length, (*length_Nlist*) length_list_repeat. omega. 
Qed. 

Lemma length_SHA256': forall l, 
  length (functional_prog.SHA_256' l) = HP.SHA256.DigestLength.
Proof. intros. unfold functional_prog.SHA_256'. simpl.
  rewrite length_intlist_to_Zlist, functional_prog.length_process_msg. reflexivity.
Qed.
 

Lemma mkKey_length l: length (HP.HMAC_SHA256.mkKey l) = HP.SHA256.BlockSize.
Proof. intros. unfold HP.HMAC_SHA256.mkKey.
  remember (Zlength l >? Z.of_nat HP.SHA256.BlockSize) as z. 
  destruct z. apply zeroPad_BlockSize.
    rewrite length_SHA256'.  
    apply Nat2Z.inj_le. simpl. omega. 
  apply zeroPad_BlockSize.
    rewrite Zlength_correct in Heqz. 
    apply Nat2Z.inj_le. 
    specialize (Zgt_cases (Z.of_nat (Datatypes.length l)) (Z.of_nat HP.SHA256.BlockSize)). rewrite <- Heqz. trivial.
Qed.

Lemma mkKey_atBlockSize s: length s = HP.SHA256.BlockSize%nat ->
      HP.HMAC_SHA256.mkKey s = s.
Proof. unfold HP.HMAC_SHA256.mkKey. rewrite Zlength_correct.
  intros. rewrite H.
  simpl. unfold HP.HMAC_SHA256.zeroPad. rewrite H. simpl.
  apply app_nil_r.  
Qed.

Lemma isbyteZ_xor a b: isbyteZ a -> isbyteZ b -> isbyteZ (Z.lxor a b).
Proof. intros. rewrite xor_inrange.
        apply Z_mod_lt. omega.
        symmetry; apply Zmod_small. apply H.
        symmetry; apply Zmod_small. apply H0.
Qed.

Lemma unsigned_repr_isbyte x:
  isbyteZ x -> Int.unsigned (Int.repr x) = x.
Proof. intros; apply Int.unsigned_repr. 
  rewrite int_max_unsigned_eq. destruct H; omega. 
Qed.

Lemma isbyteZ_range q: isbyteZ q -> 0 <= q <= Byte.max_unsigned. 
Proof. intros B; destruct B. unfold Byte.max_unsigned, Byte.modulus; simpl. omega. Qed.

Lemma isbyte_sha x: Forall isbyteZ (functional_prog.SHA_256' x).
Proof. apply isbyte_intlist_to_Zlist. Qed.

Lemma isbyteZ_mkKey: forall l, Forall isbyteZ l -> Forall isbyteZ (HP.HMAC_SHA256.mkKey l).
Proof. intros.
  unfold HP.HMAC_SHA256.mkKey.
  remember (Zlength l >? Z.of_nat HP.SHA256.BlockSize).
  destruct b.
    apply zeropad_isbyteZ. unfold HP.SHA256.Hash. apply isbyte_sha.
    apply zeropad_isbyteZ; trivial.
Qed.

Lemma isbyte_hmac ipad opad m k: 
   Forall isbyteZ (HMAC_functional_prog.HP.HMAC_SHA256.HMAC ipad opad m k).
Proof. apply isbyte_sha. Qed.

Lemma updAbs_len: forall L s t, update_abs L s t -> s256a_len t = s256a_len s + Zlength L * 8.
Proof. intros. inversion H; clear H.
  unfold s256a_len, bitlength. simpl.
  rewrite Zlength_app. subst. 
  repeat rewrite Z.mul_add_distr_r.
  repeat rewrite <- Z.add_assoc.
  assert (Zlength blocks * WORD * 8 + Zlength newfrag * 8 =
          Zlength oldfrag * 8 + Zlength L * 8).
    assert (Zlength (oldfrag ++ L) = Zlength (SHA256.intlist_to_Zlist blocks ++ newfrag)).
      rewrite H4; trivial.
    clear H4. rewrite Zlength_app in H.
              rewrite <- (Z.mul_add_distr_r (Zlength oldfrag)), H. clear H.
              rewrite Zlength_app, Zlength_intlist_to_Zlist.
              rewrite (Z.mul_comm WORD). rewrite Z.mul_add_distr_r. trivial. 
  rewrite H; trivial.
Qed.

Lemma HMAC_length d k: length (HP.HMAC256 d k) = 32%nat.
Proof.
  unfold HP.HMAC_SHA256.HMAC, HP.HMAC_SHA256.OUTER.
  apply length_SHA256'.
Qed.
Lemma HMAC_Zlength d k: Zlength (HP.HMAC256 d k) = 32.
Proof.
  rewrite Zlength_correct, HMAC_length. reflexivity.
Qed.