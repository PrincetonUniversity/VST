Require Recdef.
Require Import compcert.lib.Integers.
Require Coq.Strings.String.
Require Coq.Strings.Ascii.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.sublist.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.SHA256.

(* LINEAR-TIME FUNCTIONAL VERSION OF SHA256 *)
Function zeros (n : Z) {measure Z.to_nat n} : list Int.int :=
 if Z.gtb n 0 then Int.zero :: zeros (n-1) else nil.
Proof.
   intros. rewrite Z2Nat.inj_sub by omega.
   apply Zgt_is_gt_bool in teq.
   assert (0 < n) by omega. apply Z2Nat.inj_lt in H; try omega.
   simpl in H. change (Z.to_nat 1) with 1%nat. omega.
Defined.

Definition padlen (n: Z) : list Int.int :=
    let p := n/4+3 (* number of words with trailing 128-byte,
                                                      up to 3 zero bytes, and 2 length words *)
    in let q := (p+15)/16*16 - p   (* number of zero-pad words *)
      in zeros q ++ [Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)].

Fixpoint generate_and_pad' (n: list byte) len : list Int.int :=
  match n with
  | nil => bytes_to_Int (Byte.repr 128) Byte.zero Byte.zero Byte.zero :: padlen len
  | [h1]=> bytes_to_Int h1 (Byte.repr 128) Byte.zero Byte.zero :: padlen (len+1)
  | [h1; h2] => bytes_to_Int h1 h2 (Byte.repr 128) Byte.zero :: padlen (len+2)
  | [h1; h2; h3] => bytes_to_Int h1 h2 h3 (Byte.repr 128) :: padlen (len+3)
  | h1::h2::h3::h4::t => bytes_to_Int h1 h2 h3 h4 :: generate_and_pad' t (len+4)
  end.

Definition generate_and_pad_alt (n: list byte) : list Int.int :=
   generate_and_pad' n 0.

Definition Wnext (msg : list int) : int :=
 match msg with
 | x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::_ =>
   (Int.add (Int.add (sigma_1 x2) x7) (Int.add (sigma_0 x15) x16))
 | _ => Int.zero  (* impossible *)
 end.

(*generating 64 words for the given message block imput*)
Fixpoint generate_word (msg : list int) (n : nat) {struct n}: list int :=
  match n with
  |O   => msg
  |S n' => generate_word (Wnext msg :: msg) n'
  end.
Arguments generate_word msg n : simpl never.
Global Opaque generate_word. (* for some reason the Arguments...simpl-never
   command does not do the job *)

(*execute round function for 64 rounds*)
Fixpoint rnd_64 (x: registers) (k w : list int) : registers :=
  match k, w with
  | k1::k', w1::w' => rnd_64 (rnd_function x k1 w1) k' w'
  | _ , _ => x
  end.
Arguments rnd_64  x k w : simpl never.  (* blows up otherwise *)

Definition process_block (r: registers) (block: list int) : registers :=
       (map2 Int.add r (rnd_64 r K256 (rev(generate_word block 48)))).

Fixpoint grab_and_process_block (n: nat) (r: registers) (firstrev msg: list int) : registers * list int :=
 match n, msg with
  | O, _ => (process_block r firstrev, msg)
  | S n', m1::msg' => grab_and_process_block n' r (m1::firstrev) msg'
  | _, nil => (r,nil) (* impossible *)
 end.

(*iterate through all the message blocks; this could have been done with just a Fixpoint
  if we incorporated grab_and_process_block into process_msg, but I wanted to
  modularize a bit more. *)
Function process_msg  (r: registers) (msg : list int) {measure length msg}  : registers :=
 match msg with
 | nil => r
 | _ => let (r', msg') := grab_and_process_block 16 r nil msg
             in process_msg r' msg'
 end.
Proof.
  intros; subst.
  simpl.
  assert (Datatypes.length msg' <= Datatypes.length l)%nat; [ | omega].
  simpl in teq0.
  do 16 (destruct l; [inv teq0; solve [simpl; auto 50] | ]).
  unfold process_block in teq0.
  assert (i15::l = msg') by congruence.
  subst msg'.
  simpl.
  omega.
Defined.

Definition SHA_256' (str : list byte) : list byte :=
    intlist_to_bytelist (process_msg init_registers (generate_and_pad_alt str)).

(*EXAMPLES*)

Fixpoint bytelist_eq (al bl: list byte) : bool :=
 match al, bl with
 | nil, nil => true
 | a::al', b::bl' => Byte.eq a b && bytelist_eq al' bl'
 | _, _ => false
  end.

Definition hexdigit(a: Z) : Z :=
 if Z.leb 48 a && Z.ltb a 58 then Z.sub a 48
 else if Z.leb 65 a && Z.ltb a 71 then Z.sub a 55
 else if Z.leb 97 a && Z.ltb a 103 then Z.sub a 87
 else 0%Z.

Fixpoint hexstring_to_bytelist (s: String.string): list byte  :=
 match s with
 | String.String a (String.String b r) => Byte.repr ((hexdigit (Z.of_N (Ascii.N_of_ascii a)) * 16
                                         + hexdigit (Z.of_N (Ascii.N_of_ascii b))))
                                          :: hexstring_to_bytelist r
 | _ => nil
 end.

Section CHECKS.
Import String.
Definition check m h :=
  bytelist_eq (SHA_256' (str_to_bytes m)) (hexstring_to_bytelist h) = true.

(*This input message is 344 bits long, which would have one message block after padding*)
Goal  check   "The quick brown fox jumps over the lazy dog"
  "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592".
Proof. vm_compute; auto. Qed.

(*This input message would have four message blocks after padding*)
Goal check "The Secure Hash Algorithm is a family of cryptographic hash functions published by the National Institute of Standards and Technology (NIST) as a U.S. Federal Information Processing Standard (FIPS)"
 "27c3971526f07a22decc4dc01340c6c4b972ba6d31b74fb1fbb2edf2bce5fea6".
Proof. vm_compute; auto. Qed.
End CHECKS.

(* PROOF OF EQUIVALENCE OF FAST FUNCTIONAL PROGRAM WITH
    FUNCTIONAL SPECIFICATION *)

Require Import sha.common_lemmas.
Require Import VST.msl.Coqlib2.

Local Open Scope nat.

Lemma length_rnd_64:
  forall r k w, length r = 8 -> length (rnd_64 r k w) = 8.
Proof.
intros.
revert r H w; induction k; simpl; intros; auto.
unfold rnd_64; fold rnd_64.
destruct w; auto.
rename H into H0.
repeat  (destruct r as [ | ? r]; rename H0 into H2; inv H2).
apply IHk.
reflexivity.
Qed.

Lemma length_rnd_64_inv:
  forall r k w, length (rnd_64 r k w) = 8 -> length r = 8.
Proof.
intros.
revert w r H; induction k; simpl; intros.
unfold rnd_64 in H; auto.
unfold rnd_64 in H; fold rnd_64 in H.
destruct w; inv H; auto.
rewrite H1.
apply IHk in H1.
clear - H1.
unfold rnd_function in H1.
rename H1 into H0.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0. destruct r; inv H1.
destruct r; inv H0.
simpl.
auto.
Qed.

Lemma length_process_block:
  forall r b, length r = 8 -> length (process_block r b) = 8.
Proof.
 intros. unfold process_block.
 apply length_map2; auto.
 apply length_rnd_64; auto.
Qed.


Lemma length_map2_add_rnd_64:
 forall regs w,
  length regs = 8 ->
  length (map2 Int.add regs (rnd_64 regs K256 w)) = 8.
Proof.
 intros.
 apply length_map2; auto.
 apply length_rnd_64; auto.
Qed.

Lemma grab_and_process_block_length:
 forall n r firstr msg r' m',
    length r = 8 ->
    length msg >= n ->
    grab_and_process_block n r firstr msg  = (r',m') ->
    length r' = 8.
Proof.
 induction n; intros.
 inv H1.
 apply length_process_block; auto.
 destruct msg.
 inv H0.
 simpl in H0.
 apply IHn in H1; auto.
 omega.
Qed.

Lemma length_process_msg:
  forall b, length (process_msg init_registers b) = 8.
Proof.
 intros.
 assert (length init_registers = 8%nat) by reflexivity.
 forget init_registers as regs.
 assert (exists n, n >= length b)%nat by eauto.
 destruct H0 as [n H0].
 revert regs b H H0; induction n; intros; rewrite process_msg_equation.
 destruct b; auto.
 inv H0.
 unfold grab_and_process_block.
 repeat (destruct b; [apply H | ]).
 apply IHn.
 apply length_process_block; auto.
 simpl in H0.
 omega.
Qed.

Lemma process_msg_eq2:
 forall regs hashed b,
  length b = 16 ->
 process_msg regs (b++hashed) =
  process_msg (process_block regs (rev b)) hashed.
Proof.
intros.
rewrite process_msg_equation.
destruct (b++hashed) eqn:?.
destruct b; inv H. inv Heql.
rewrite <- Heql; clear i l Heql.
unfold grab_and_process_block.
rename H into H0.
repeat (destruct b as [ | ?x b]; inv H0; rename H1 into H0).
destruct b; inv H0.
simpl. auto.
Qed.

Lemma rnd_64_S:
  forall regs i b k w,
    nth_error K256 i = Some k ->
    nth_error b i = Some w ->
    rnd_64 regs K256 (firstn (S i) b) =
    rnd_function (rnd_64 regs K256 (firstn i b)) k w.
Proof.
intros.
forget K256 as K'.
assert (firstn (S i) b = firstn i b++[w]).
clear - H0.
revert b w H0; induction i; destruct b; simpl; intros; inv H0; auto.
rewrite <- (IHi _ _ H1).
reflexivity.
rewrite H1.
clear H1.
pose proof (firstn_length i b).
rewrite min_l in H1.
2:{
clear - H0; revert b H0; induction i; destruct b; simpl; intros; inv H0; try omega.
specialize (IHi _ H1). omega.
}
rewrite <- H1 in H.
clear H0 H1.
revert K' k H regs; induction (firstn i b); destruct K'; simpl; intros; inv H.
unfold rnd_64; simpl; fold rnd_64.
destruct K'; reflexivity.
specialize (IHl _ _ H1).
unfold rnd_64; simpl; fold rnd_64.
apply IHl.
Qed.

Lemma Zlength_zeros:
    forall n, (n>=0)%Z -> Zlength (zeros n) = n.
Proof.
intros.
rewrite <- (Z2Nat.id n) in * by omega.
clear H.
induction (Z.to_nat n).
reflexivity.
rewrite inj_S.
rewrite zeros_equation.
pose proof (Zgt_cases (Z.succ (Z.of_nat n0)) 0).
destruct (Z.succ (Z.of_nat n0) >? 0); try omega.
rewrite Zlength_cons.
f_equal.  rewrite <- IHn0.
f_equal. f_equal. omega.
Qed.

Lemma length_zeros: forall n:Z, length (zeros n) = Z.to_nat n.
Proof.
intros. destruct (zlt n 0).
rewrite zeros_equation.
pose proof (Zgt_cases n 0).
destruct (n>?0). omega.
destruct n. inv l. inv l. simpl. reflexivity.
rename g into H.
pose proof (Zlength_zeros n H).
rewrite Zlength_correct in H0.
rewrite <- H0 at 2.
rewrite Nat2Z.id. auto.
Qed.

Hint Rewrite length_zeros : norm.

Local Open Scope Z.

Lemma Zlength_padlen:
 forall n,
  n>=0 ->
  Zlength (padlen n) = roundup (n/4+3) 16 - n/4 - 1.
Proof.
intros.
unfold padlen.
rewrite Zlength_app.
rewrite Zlength_zeros.
repeat rewrite Zlength_cons; rewrite Zlength_nil.
change (Z.succ (Z.succ 0)) with 2.
unfold roundup.
change (16-1) with 15; omega.
assert (n/4 >= 0).
apply Z_div_ge0; omega.
assert (n/4+3>0) by omega.
forget (n/4+3) as d.
clear - H1.
replace (d+15) with ((1*16)+ (d-1)) by (simpl Z.mul; omega).
rewrite Z_div_plus_full_l by omega.
rewrite Z.mul_add_distr_r.
change (1*16) with 16.
assert ((d-1)/16*16 + 15 >= d-1); [ | omega].
assert (d-1>=0) by omega.
forget (d-1) as e.
clear - H.
pattern e at 2; rewrite (Z_div_mod_eq e 16) by omega.
rewrite Z.mul_comm.
 assert (15 >= e mod 16); [| omega].
destruct (Z.mod_pos_bound e 16); omega.
Qed.

Lemma zeros_app:
  forall n m, (n >= 0 -> m >=0 -> zeros n ++ zeros m = zeros (n+m))%Z.
Proof.
intro.
intros ? ?.
rewrite <- (Z2Nat.id n).
induction (Z.to_nat n); intros; try reflexivity.
rewrite inj_S. unfold Z.succ.
rewrite zeros_equation; symmetry; rewrite zeros_equation; symmetry.
replace ( Z.of_nat n0 + 1 + m >? 0) with true.
replace (Z.of_nat n0 + 1 >? 0) with true.
simpl.
f_equal.
rewrite Z.add_simpl_r.
rewrite IHn0; auto.
f_equal; omega.
symmetry; apply Z.gtb_lt; auto; omega.
symmetry; apply Z.gtb_lt; auto; omega.
omega.
Qed.

Lemma zeros_Zsucc:
 forall n, n >= 0 -> zeros (Z.succ n) = Int.repr 0 :: zeros n.
Proof.
intros.
rewrite zeros_equation.
replace (Z.succ n >? 0) with true.
f_equal. f_equal. omega.
symmetry.
apply Z.gtb_lt; omega.
Qed.

Lemma intlist_to_bytelist_zeros:
  forall n:Z, intlist_to_bytelist (zeros n) = map Byte.repr (map Int.unsigned (zeros (4*n)%Z)).
Proof.
intro.
destruct (zlt n 0).
destruct n; try omega. inv l. reflexivity.
rewrite <- (Z2Nat.id n) by omega.
induction (Z.to_nat n).
simpl; auto.
rewrite inj_S.
rewrite zeros_Zsucc by omega.
unfold intlist_to_bytelist; fold intlist_to_bytelist.
unfold Z.succ.
rewrite Z.add_comm.
rewrite Z.mul_add_distr_l.
replace (4 * 1 + 4 * Z.of_nat n0) with (Z.succ (Z.succ (Z.succ (Z.succ (4 * Z.of_nat n0))))) by omega.
repeat rewrite zeros_Zsucc by omega.
rewrite IHn0.
reflexivity.
Qed.

Definition padlen' (n: Z) : list Int.int :=
     let q := (n+8)/64*16 + 15 - (n+8)/4   (* number of zero-pad words *)
      in zeros q ++ [Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)].

Lemma padlen_eq: padlen=padlen'.
Proof.
extensionality n.
unfold padlen,padlen'; simpl.
f_equal. f_equal.
assert ((n+12)/4 = n/4+3).
intros.
replace (n+12) with (3*4+n) by omega.
 rewrite Z_div_plus_full_l by omega. omega.
rewrite <- H.
replace ((n+12)/4) with ((n+8)/4+1).
rewrite <- Z.add_assoc.
change (1+15) with (1*16).
rewrite <- (Z.add_comm (1*16)).
 rewrite Z_div_plus_full_l by omega.
rewrite Z.mul_add_distr_r.
rewrite Z.div_div by omega.
change (4*16) with 64.
omega.
replace (n+12) with (1*4+(n+8)) by omega.
 rewrite Z_div_plus_full_l by omega.
omega.
Qed.

Lemma length_generate_and_pad'':
  forall (l: list byte) (k: Z),
     k >= 0 ->
     k + Zlength (generate_and_pad' l (k*4)) = roundup (((k*4+Zlength l)+12)/4) 16.
Proof.
intro l.
remember (S (length l)) as L.
assert (length l < L)%nat by omega.
clear HeqL; revert l H; clear; induction L; intros.
inversion H.
destruct l.
simpl; repeat rewrite Zlength_cons; repeat rewrite Zlength_nil.
rewrite Zlength_padlen
  by (apply Z.le_ge; apply Z.mul_nonneg_nonneg; omega).
unfold Z.succ.
replace (k*4+0+12) with (k*4+4+8) by omega.
change 8 with (2*4).
rewrite Z_div_plus_full by omega.
replace ((k*4+4)/4)%Z with (k+1)%Z
 by (replace ((k*4+4)/4)%Z with (k*4/4 + 1)%Z
         by (symmetry; apply (Z_div_plus (k*4) 1 4); omega);
      rewrite Z_div_mult by omega; auto).
rewrite Z.sub_add.
rewrite Z.div_mul by congruence.
replace (k+1+2) with (k+3) by omega.
omega.
assert (k*4 >= 0).
apply Z.le_ge; apply Z.mul_nonneg_nonneg; omega.
destruct l.
simpl; repeat rewrite Zlength_cons; repeat rewrite Zlength_nil.
rewrite Zlength_padlen by omega.
unfold Z.succ. rewrite Z.sub_add.
replace (k*4+(0+1)+12) with (k*4+1+4+8) by omega.
change 8 with (2*4).
rewrite Z_div_plus_full by omega.
change (k * 4 + 1 + 4) with (k * 4 + 1 + 1*4).
rewrite (Z_div_plus (k*4+1) 1 4) by omega.
rewrite (Z.add_comm (k*4)).
rewrite Z_div_plus by omega.
change (1/4) with 0.
rewrite Z.add_0_l.
replace (k+1+2) with (k+3) by omega.
omega.
destruct l.
simpl; repeat rewrite Zlength_cons; repeat rewrite Zlength_nil.
rewrite Zlength_padlen by omega.
unfold Z.succ. rewrite Z.sub_add.
replace (k*4+(0+1+1)+12) with (k*4+2+4+8) by omega.
change 8 with (2*4).
rewrite Z_div_plus_full by omega.
change (k * 4 + 2 + 4) with (k * 4 + 2 + 1*4).
rewrite (Z_div_plus (k*4+2) 1 4) by omega.
rewrite (Z.add_comm (k*4)).
rewrite Z_div_plus by omega.
change (2/4) with 0.
rewrite Z.add_0_l.
replace (k+1+2) with (k+3) by omega.
omega.
destruct l.
simpl; repeat rewrite Zlength_cons; repeat rewrite Zlength_nil.
rewrite Zlength_padlen by omega.
unfold Z.succ. rewrite Z.sub_add.
replace (k*4+(0+1+1+1)+12) with (k*4+3+4+8) by omega.
change 8 with (2*4).
rewrite Z_div_plus_full by omega.
change (k * 4 + 3 + 4) with (k * 4 + 3 + 1*4).
rewrite (Z_div_plus (k*4+3) 1 4) by omega.
rewrite (Z.add_comm (k*4)).
rewrite Z_div_plus by omega.
change (3/4) with 0.
rewrite Z.add_0_l.
replace (k+1+2) with (k+3) by omega.
omega.
simpl; repeat rewrite Zlength_cons; repeat rewrite Zlength_nil.
unfold Z.succ.
transitivity (k+1 + (Zlength (generate_and_pad' l ((k+1) * 4)))).
rewrite Z.mul_add_distr_r.
change (1*4) with 4.
omega.
simpl in H.
rewrite IHL; try omega.
f_equal.
f_equal.
omega.
Qed.

Lemma length_generate_and_pad':
  forall (l: list byte),
     Zlength (generate_and_pad' l 0) = roundup ((Zlength l +12)/4) 16.
Proof.
intros.
transitivity (0 + Zlength (generate_and_pad' l (0*4))).
rewrite Z.add_0_l.
reflexivity.
apply length_generate_and_pad''.
omega.
Qed.

Lemma roundup_ge:
 forall a b,  b > 0 -> roundup a b >= a.
Proof.
intros.
assert (roundup a b - a >= 0); [ | omega].
rewrite roundup_minus by auto.
pose proof (Z.mod_pos_bound (-a) b); omega.
Qed.


Lemma generate_and_pad'_eq:
 generate_and_pad = generate_and_pad_alt.
Proof.
extensionality msg.
unfold generate_and_pad,  generate_and_pad_alt.
match goal with |- context [bytelist_to_intlist ?A] =>
  remember A as PADDED eqn:HP
end.
assert (Nat.divide 4 (length PADDED)). {
subst PADDED.
pose proof (roundup_ge (Zlength msg + 9) 64).
 spec H; [ omega | ].
assert (Zlength msg >= 0) by (rewrite Zlength_correct; omega).
exists (Z.to_nat (roundup (Zlength msg+9) 64 / 4 - 2)).
repeat rewrite app_length.
rewrite length_list_repeat.
simpl length.
symmetry.
transitivity (Z.to_nat (roundup (Zlength msg + 9) 64 / 4 - 2) * Z.to_nat 4)%nat; [reflexivity |].
rewrite <- Z2Nat.inj_mul; try omega.
2:{
assert (roundup (Zlength msg + 9) 64 / 4 >= (Zlength msg + 9) / 4)
 by (apply Z_div_ge; omega).
assert ((Zlength msg + 9) / 4 = (Zlength msg + 1)/4 + 2).
replace (Zlength msg + 9) with (Zlength msg + 1 + 2*4) by omega.
rewrite Z_div_plus_full by omega.
auto.
assert (0 <= (Zlength msg + 1)/4).
apply Z.div_pos;  omega.
omega. } 
rewrite Z.mul_sub_distr_r.
replace (roundup (Zlength msg + 9) 64 / 4 * 4) with
  (roundup (Zlength msg + 9) 64).
2:{
unfold roundup.
forget ((Zlength msg + 9 + (64 - 1)) / 64 ) as N.
change 64 with (16 * 4).
rewrite Z.mul_assoc.
rewrite Z_div_mult_full by omega.
auto.
}
rewrite <- roundup_minus by omega.
change 64 with 64.
forget (roundup (Zlength msg + 9) 64) as N.
clear H0.
rewrite Zlength_correct in *.
forget (length msg) as L.
transitivity (Z.to_nat (Z.of_nat L + (1 + (N - (Z.of_nat L + 9))))).
f_equal. omega.
rewrite Z2Nat.inj_add  by omega.
rewrite Nat2Z.id.
f_equal.
rewrite Z2Nat.inj_add by omega.
f_equal.
}
remember (Z.to_nat (Zlength msg / 4)) as n.
change PADDED with (skipn 0 PADDED).
change msg with (skipn 0 msg) at 3.
change 0 with (Z.of_nat 0).
replace 0%nat with ((Z.to_nat (Zlength msg / 4) - n)*4)%nat
 by (rewrite Heqn, minus_diag; reflexivity).
assert (H88: (n * 4 <= length msg)%nat). {
 subst n.
 apply Nat2Z.inj_le.
 rewrite <- Zlength_correct. rewrite Nat2Z.inj_mul.
 rewrite Z2Nat.id.
 rewrite (Z_div_mod_eq (Zlength msg) 4) at 2 by omega.
 change (Z.of_nat 4) with 4. rewrite <- Z.mul_comm.
 pose proof (Z.mod_pos_bound (Zlength msg) 4); omega.
 apply Z.div_pos; try rewrite Zlength_correct; omega.
}
clear Heqn.
revert H88; induction n; intros.
* (* base case for n *)
clear H88.
rewrite Nat.sub_0_r.
rewrite Nat2Z.inj_mul.
assert (0 <= Zlength msg) by (rewrite Zlength_correct; omega).
assert (0 <= Zlength msg / 4) by (apply Z.div_pos; omega).
pose proof (Z_div_mod_eq (Zlength msg) 4). spec H2; [omega|].
assert (H99: (Z.to_nat (Zlength msg / 4) * 4 <= length msg)%nat).
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Nat2Z.inj_mul.
rewrite Z2Nat.id by auto.
change (Z.of_nat 4) with 4.
destruct (Z.mod_pos_bound (Zlength msg) 4); omega.
rewrite Z2Nat.id by omega.
change (Z.of_nat 4) with 4.
rewrite Z.mul_comm in H2.
assert (length (skipn (Z.to_nat (Zlength msg / 4) * 4) msg) < 4)%nat.
rewrite skipn_length.
apply Nat2Z.inj_lt.
rewrite Nat2Z.inj_sub. rewrite <- Zlength_correct.
rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with 4.
rewrite Z2Nat.id by auto.
destruct (Z.mod_pos_bound (Zlength msg) 4); omega.
omega.
rewrite HP.
rewrite skipn_app1 by omega.
remember (skipn (Z.to_nat (Zlength msg / 4) * 4) msg) as ccc.
assert (HQ: (Zlength msg + 8) / 64 * 16 + 15 - (Zlength msg + 8) / 4 >= 0). {
clear - H0.
assert (0 <= Zlength msg + 8) by omega.
clear H0. forget (Zlength msg + 8) as a.
pose proof (Z_div_mod_eq a 64); spec H0; [omega|].
rewrite H0 at 2.
rewrite (Z.mul_comm 64).
change 64 with (16*4) at 3.
rewrite Z.mul_assoc.
rewrite Z_div_plus_full_l by omega.
assert (a mod 64 / 4 < 16).
apply Z.div_lt_upper_bound. omega. apply Z.mod_pos_bound; omega.
omega.
}
assert (- (Zlength msg + 9) mod 64 =
           (3 - Zlength ccc) + 4* ((Zlength msg+8)/64 * 16 + 15 - (Zlength msg + 8) / 4)). {
assert (LL: length ccc = length (skipn (Z.to_nat (Zlength msg / 4) * 4) msg))
 by congruence.
rewrite skipn_length in LL.
assert (LL': Zlength msg = Zlength ccc + (Zlength msg/4)*4).
rewrite Zlength_correct at 1.
rewrite Zlength_correct at 1.
 rewrite LL.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_mul.
rewrite Z2Nat.id by auto.
change (Z.of_nat 4) with 4; omega.
rewrite Nat2Z.inj_le.
rewrite Nat2Z.inj_mul.
rewrite Z2Nat.id by auto.
rewrite <- Zlength_correct.
change (Z.of_nat 4) with 4.
assert (0 <= Zlength msg mod 4)
 by (apply Z.mod_pos_bound; omega).
omega.
replace (Zlength ccc) with (Zlength msg - Zlength msg / 4 * 4) by omega.
clear LL LL'.
clear - H0 HQ. forget (Zlength msg) as a.
 rewrite <- roundup_minus by omega; unfold roundup.
replace (a  + 9 + (64-1)) with (a + 8 + 1*64) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.mul_add_distr_r.
rewrite (Z.mul_comm 4).
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_add_distr_r.
change (15*4) with (64-4).
rewrite <- Z.mul_assoc.
change (16*4) with 64.
assert (0 =8+ a / 4 * 4 - (a + 8) / 4 * 4);  [ | omega].
change 8 with (2*4) at 2.
rewrite Z_div_plus_full by omega.
rewrite Z.mul_add_distr_r.
omega.
}
rewrite H4.
assert (0 <= Zlength ccc < 4)
 by (clear - H3; rewrite Zlength_correct; omega).
rewrite Z2Nat.inj_add by omega.
rewrite <- list_repeat_app.
replace (Zlength msg / 4 * 4) with (Zlength msg - Zlength ccc).
2:{
rewrite Heqccc.
rewrite (Zlength_correct (skipn _ _)).
rewrite skipn_length by omega.
rewrite Nat2Z.inj_sub by omega.
rewrite <- Zlength_correct.
rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with 4.
rewrite Z2Nat.id  by omega.
 omega.
} 
match goal with |- context [_ ++ list_repeat (Z.to_nat (4 * ?qq)) Byte.zero] =>
 assert (bytelist_to_intlist (list_repeat (Z.to_nat (4 * qq)) Byte.zero) =
  zeros ((Zlength msg + 8) / 64 * 16 + 15 - (Zlength msg + 8) / 4));
  set (Q := qq) in *
end. {
 rewrite Z2Nat.inj_mul by omega. change (Z.to_nat 4) with 4%nat.
 rewrite <- Z2Nat.id at 2 by omega.
 induction (Z.to_nat Q). reflexivity.
 rewrite inj_S. rewrite zeros_equation.
 assert (0 < Z.succ (Z.of_nat n)) by omega.
 apply Z.gtb_lt in H6; rewrite H6.
 replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by omega.
 rewrite <- IHn.
 replace (4 * S n)%nat with (S (S (S (S (4*n)))))%nat.
 reflexivity. omega.
}
set (Q4 := Z.to_nat (4 * Q)) in *.
destruct ccc as [|a [|b [|c [|]]]]; simpl in H3; try omega; clear H3;
 unfold generate_and_pad'; rewrite padlen_eq; unfold padlen';
 simpl;
repeat rewrite Zlength_cons; rewrite Zlength_nil.
+ (* ccc = [] *)
  rewrite Z.sub_0_r. rewrite H6. reflexivity.
+ (* ccc = [a] *)
   change (Z.succ 0) with 1; rewrite Z.sub_add. rewrite H6. reflexivity.
+ (* ccc = [a,b] *)
   change (Z.succ (Z.succ 0)) with 2; rewrite Z.sub_add.
   rewrite H6. reflexivity.
+ (* ccc = [a,b,c] *)
   change (Z.succ (Z.succ (Z.succ 0))) with 3; rewrite Z.sub_add.
   rewrite H6. reflexivity.
* (* inductive case for n *)
replace (S n * 4)%nat with (4 + n*4)%nat in H88 by omega.
assert ((Z.to_nat (Zlength msg / 4) - S n) * 4 = ((Z.to_nat (Zlength msg / 4) - n) * 4) - 4)%nat
  by omega.
rewrite H0. clear H0.
spec IHn; [omega |].
set (Q := ((Z.to_nat (Zlength msg / 4) - n) * 4)%nat) in *.
assert (Hyy : 0 <= Zlength msg) by (rewrite Zlength_correct; omega).
assert (Hzz:=Zmod_eq (Zlength msg) 4); spec Hzz; [omega|].
destruct (Z.mod_pos_bound (Zlength msg) 4); try  omega.
apply Nat2Z.inj_le in H88.
rewrite Nat2Z.inj_add, Nat2Z.inj_mul in H88.
rewrite <- Zlength_correct in H88.
change (Z.of_nat 4) with 4 in *.
assert (Huu:= Z.div_pos (Zlength msg) 4 Hyy); spec Huu; [omega|].
assert (Q >= 4)%nat. {
 clear - H88 Hyy Hzz H0 H1 Huu; unfold Q; clear Q.
apply Nat2Z.inj_ge. rewrite Nat2Z.inj_mul.
change (Z.of_nat 4) with 4 in *.
rewrite Nat2Z.inj_sub
 by (apply Nat2Z.inj_le; rewrite Z2Nat.id by auto;
       apply Zmult_le_reg_r with 4; omega).
 rewrite Z2Nat.id by auto.
change 4 with (1*4) at 3.
apply Zmult_ge_reg_r with 4; omega.
}
rewrite <- (firstn_skipn 4 (skipn (Q-4) PADDED)), skipn_drop.
rewrite <- (firstn_skipn 4 (skipn (Q-4) msg)), skipn_drop.
replace (4 + (Q-4))%nat with Q by omega.
rewrite HP at 1.
assert (QL: (Q <= length msg)%nat). {
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
unfold Q.
rewrite Nat2Z.inj_mul.
rewrite Nat2Z.inj_sub.
 rewrite Z2Nat.id by auto.
change (Z.of_nat 4) with 4 in *.
 rewrite Z.mul_sub_distr_r.
omega.
apply Nat2Z.inj_le.
 rewrite Z2Nat.id by auto.
omega.
}
rewrite skipn_app1 by omega.
rewrite firstn_app1
 by (rewrite skipn_length by omega; omega).
assert (length (firstn 4 (skipn (Q - 4) msg)) = 4)%nat.
rewrite firstn_length. rewrite skipn_length by omega.
apply min_l. omega.
destruct (firstn 4 (skipn (Q - 4) msg))
 as [ | z0 [| z1 [| z2 [|z3 [|]]]]];inv H3.
unfold app at 2. unfold app at 4.
unfold generate_and_pad'; fold generate_and_pad'.
unfold bytelist_to_intlist; fold bytelist_to_intlist.
replace (Z.of_nat (Q-4) + 4) with (Z.of_nat Q)
 by (rewrite Nat2Z.inj_sub by omega;
       change (Z.of_nat 4) with 4; omega).
rewrite <- IHn.
reflexivity.
Qed.

Lemma roundup_divide:
 forall a b, b > 0 ->  (b | roundup a b).
Proof.
intros.
unfold roundup.
apply Z.divide_factor_r.
Qed.

Lemma length_generate_and_pad:
  forall (l: list byte),
     Zlength (generate_and_pad l) = roundup ((Zlength l +12)/4) 16.
Proof.
intros.
rewrite generate_and_pad'_eq.
unfold generate_and_pad_alt.
apply length_generate_and_pad'.
Qed.

Transparent generate_word.

Lemma generate_word_lemma1:
  forall b n, length b = 16%nat ->
   firstn 16 (rev (generate_word (rev b) n)) = b.
Proof.
intros.
change (rev b) with (nil ++ rev b).
forget (@nil int) as a.
revert a; induction n; intro.
unfold generate_word.
rewrite rev_app_distr.
rewrite rev_involutive.
rewrite firstn_app1 by omega.
rewrite firstn_same; auto; omega.
unfold generate_word; fold generate_word.
change (Wnext (a ++ rev b) :: a ++ rev b) with
      ((Wnext (a ++ rev b) ::a) ++ rev b).
apply IHn.
Qed.

Lemma length_generate_word: forall b n,
  length (generate_word b n) = (length b + n)%nat.
Proof.
intros.
revert b; induction n; intros; simpl.
unfold generate_word; fold generate_word.
omega.
unfold generate_word; fold generate_word.
rewrite IHn.
simpl. omega.
Qed.

Lemma nth_generate_word_S:
  forall k i n b',
   nth (i+k) (generate_word b' (n+k)) = nth i (generate_word b' n).
Proof.
induction k; intros.
repeat rewrite plus_0_r. auto.
replace (n + S k)%nat with (S (n + k))%nat by omega.
unfold generate_word; fold generate_word.
replace (i + S k)%nat with (S i + k)%nat by omega.
rewrite IHk by (simpl; omega).
clear IHk.
revert i b' ; induction n; intros.
unfold generate_word; fold generate_word.
extensionality d; reflexivity.
unfold generate_word; fold generate_word.
apply IHn.
Qed.

Lemma generate_word_small:
  forall i b n,
           length b = 16%nat ->
           (i < length b)%nat ->
           nth i (rev (generate_word (rev b) n)) = nth i b.
Proof.
intros.
extensionality d.
rewrite <- (nth_firstn_low _ _ 16).
rewrite (generate_word_lemma1 b n H).
auto.
rewrite rev_length, length_generate_word, rev_length, H.
omega.
Qed.

Lemma generate_word_plus:
  forall msg a b, (16 <= length msg)%nat ->
         generate_word msg (a+b) = generate_word (generate_word msg a) b.
Proof.
intros msg a b.
revert msg b; induction a; simpl; intros.
unfold generate_word; fold generate_word.
auto.
unfold generate_word; fold generate_word.
rewrite IHa by (simpl; omega).
auto.
Qed.

Definition nthB (b: list int) (i: nat) (n: Z) :=
  nth (Z.to_nat (Z.of_nat i - 16 + n)) (rev (generate_word (rev b) 48)) Int.zero.

Lemma nth_rev_generate_word:
 forall i b,
   length b = 16%nat ->
   (16 <= i < 64)%nat ->
    nth i (rev (generate_word (rev b) 48)) Int.zero =
  Int.add (nthB b i 0)
    (Int.add (Int.add (sigma_0 (nthB b i 1)) (sigma_1 (nthB b i 14)))
       (nthB b i 9)).
Proof.
intros.
unfold nthB.
rewrite <- rev_length in H.
forget (rev b) as b'.
clear b.
assert (length (generate_word b' 48) = 64)%nat
 by (rewrite length_generate_word, H; reflexivity).
rewrite rev_nth by omega.
repeat rewrite rev_nth
 by (rewrite H1; change 64%nat with (Z.to_nat 64); apply Z2Nat.inj_lt; omega).
rewrite H1.
rewrite <- (plus_0_l (64 - S i)).
assert (48 = (i - 16) + 1 + (64 - S i))%nat by (clear - H0; omega).
rewrite H2 at 2.
rewrite nth_generate_word_S.
rewrite generate_word_plus by omega.
unfold generate_word at 1.
unfold nth at 1.
assert (forall n:nat, (n < 16) ->
    ((64 - S (Z.to_nat (Z.of_nat i - 16 + Z.of_nat n))) =
      (16-n) + (48 - S (Z.to_nat (Z.of_nat i - 16)))))%nat.
clear - H0.
intros.
rewrite Z2Nat.inj_add by omega.
rewrite Nat2Z.id.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
change (Z.to_nat 16) with 16%nat.
omega.
change 0%Z with (Z.of_nat 0); rewrite H3 by (clear; omega).
change 1%Z with (Z.of_nat 1); rewrite H3 by (clear; omega).
change 14%Z with (Z.of_nat 14); rewrite H3 by (clear; omega).
change 9%Z with (Z.of_nat 9); rewrite H3 by (clear; omega).
clear H3.
assert (48 = S (Z.to_nat (Z.of_nat i - 16)) + (48 - S (Z.to_nat (Z.of_nat i - 16))))%nat.
clear - H0.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
change (Z.to_nat 16) with 16%nat.
omega.
pattern (generate_word b' 48).
rewrite H3 at 1.
repeat rewrite nth_generate_word_S.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
change (Z.to_nat 16) with 16%nat.
simpl.
change (nth 16) with (@nth int (15+1)).
change (nth 15) with (@nth int (14+1)).
change (nth 2) with (@nth int (1+1)).
change (nth 7) with (@nth int (6+1)).
replace (S (i-16)) with ((i-16)+1)%nat by omega.
repeat rewrite nth_generate_word_S.
assert (length (generate_word b' (i-16)) >= 16)%nat.
rewrite length_generate_word, H; omega.
clear - H4.
forget (generate_word b' (i-16)) as s.
rename H4 into H.
do 16 (destruct s; [simpl in H; omega | ]).
simpl.
rewrite <- Int.add_assoc.
rewrite Int.add_commut.
f_equal.
rewrite Int.add_commut.
rewrite <- Int.add_assoc.
auto.
Qed.

Opaque generate_word.

Definition c48 := 48%nat. Opaque c48.

Lemma generate_word_W:
 forall block n
 (LB: length block = 16%nat),
  0 <= n < 64 ->
  nthi (rev (generate_word (rev block) 48)) n =
  W (nthi block) n.
Proof.
intros.
assert (forall i, (i <= Z.to_nat 64)%nat ->
              forall n, 0 <= n < Z.of_nat i ->
 nthi (rev (generate_word (rev block) 48)) n = W (nthi block) n).
2:{
apply (H0 (S (Z.to_nat n))).
apply Nat2Z.inj_le. rewrite inj_S.
repeat rewrite Z2Nat.id by omega. omega.
rewrite inj_S.
rewrite Z2Nat.id by omega. omega.
} 
clear H n. induction i; intros.
change (Z.of_nat 0) with 0 in H0; omega.
spec IHi; [ omega | ].
unfold nthi at 1.
destruct (zlt n 16).
rewrite generate_word_small; auto.
2:{
rewrite LB.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega. apply l.
}
rewrite W_equation.
rewrite if_true by auto.
reflexivity.
rewrite nth_rev_generate_word; auto.
2: {
split.
apply Nat2Z.inj_le. change (Z.of_nat 16) with 16.
rewrite Z2Nat.id by omega. omega.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega.
change (Z.of_nat 64) with 64.
apply Nat2Z.inj_le in H.
rewrite Z2Nat.id in H by omega.
omega.
} 
rewrite W_equation.
rewrite if_false by omega.
rewrite inj_S in H0.
rewrite <- IHi by omega.
rewrite <- IHi by omega.
rewrite <- IHi by omega.
rewrite <- IHi by omega.
unfold nthB.
rewrite Z2Nat.id by omega.
replace (n - 16 + 14) with (n-2) by omega.
replace (n - 16 + 9) with (n - 7) by omega.
replace (n - 16 + 0) with (n-16) by omega.
replace (n - 16 + 1) with (n - 15) by omega.
unfold nthi.
forget (nth (Z.to_nat (n - 16)) (rev (generate_word (rev block) 48)) Int.zero)
  as A.
forget (sigma_1
        (nth (Z.to_nat (n - 2)) (rev (generate_word (rev block) 48)) Int.zero))
  as B.
forget  (sigma_0
           (nth (Z.to_nat (n - 15)) (rev (generate_word (rev block) 48))
              Int.zero))
  as C.
forget (nth (Z.to_nat (n - 7)) (rev (generate_word (rev block) 48)) Int.zero)
  as D.
rewrite Int.add_commut.
repeat rewrite <- Int.add_assoc.
f_equal.
rewrite <- (Int.add_commut D).
rewrite <- (Int.add_commut D).
rewrite Int.add_assoc.
f_equal.
apply Int.add_commut.
Qed.

Lemma process_block_hash_block:
 forall regs block,
   length regs = 8%nat ->
   length block = 16%nat ->
   process_block regs (rev block) = hash_block regs block.
Proof.
intros.
unfold process_block.
unfold hash_block.
f_equal.
rewrite <- (firstn_same _ 64 (rev (generate_word _ _)))
 by (rewrite rev_length, length_generate_word, rev_length; omega).
change 64%nat with (48+16)%nat.
change 63%Z with (Z.of_nat (48+16)-1).
assert (48 <= 48)%nat by omega.
remember 48%nat as n.
rewrite Heqn at 2.
rewrite Heqn in H1 at 2.
clear Heqn. rename H1 into H7.
revert regs H H7; induction n; intros.
simpl plus.
change 48%nat with c48 in H7 |- *.
remember 16%nat as n.
rewrite Heqn in H0.
assert (n <= 16)%nat by omega.
clear Heqn H7.
revert H1; induction n; intros.
* (* n=0 *)
simpl.
rewrite Round_equation.
rewrite if_true by omega.
reflexivity.
* (*0 < n <= 16 *)
rewrite Round_equation.
rewrite inj_S.
rewrite if_false by omega.
replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by omega.
rewrite <- IHn by omega. clear IHn.
rewrite (rnd_64_S _ _ _
    (nthi K256 (Z.of_nat n))
    (nthi block (Z.of_nat n))).
2: (unfold nthi; rewrite Nat2Z.id; apply nth_error_nth; simpl; omega).
2:{
unfold nthi; rewrite Nat2Z.id.
rewrite (nth_error_nth _ Int.zero n).
2: rewrite rev_length, length_generate_word, rev_length, H0;
  change c48 with 48%nat; omega.
f_equal.
rewrite generate_word_small by omega.
auto.
}
unfold rnd_function.
destruct (rnd_64 regs K256 (firstn n (rev (generate_word (rev block) c48))))
  as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; auto.
rewrite W_equation.
rewrite if_true; auto.
omega.
* (* 16 <= n < 64 *)
change (S n + 16)%nat with (S (n + 16)).
rewrite inj_S.
unfold Z.succ.
rewrite Z.add_simpl_r.
rewrite (rnd_64_S _ _ _
    (nthi K256 (Z.of_nat (n+16)))
    (nthi (rev (generate_word (rev block) c48)) (Z.of_nat (n+16)))).
2: (unfold nthi; rewrite Nat2Z.id; apply nth_error_nth; simpl; omega).
2:{
unfold nthi; rewrite Nat2Z.id.
apply (nth_error_nth _ Int.zero (n+16)).
rewrite rev_length, length_generate_word, rev_length, H0;
  change c48 with 48%nat; omega.
}
rewrite Round_equation.
rewrite <- IHn by omega.
rewrite if_false by omega.
forget (rnd_64 regs K256 (firstn (n + 16) (rev (generate_word (rev block) 48))))
   as regs'.
unfold rnd_function.
destruct regs'
  as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; auto.
replace (W (nthi block) (Z.of_nat (n + 16)))
  with  (nthi (rev (generate_word (rev block) c48)) (Z.of_nat (n + 16)));
auto.
change c48 with 48%nat.
apply generate_word_W; auto.
rewrite Nat2Z.inj_add. change (Z.of_nat 16) with 16.
omega.
Qed.

Lemma process_msg_hash_blocks:
  forall regs blocks,
    (16 | Zlength blocks) ->
    length regs = 8%nat ->
    process_msg regs blocks = hash_blocks regs blocks.
Proof.
intros.
destruct H as [n ?].
rewrite Zlength_correct in H.
assert (0 <= n).
 apply Zmult_le_0_reg_r with 16; auto. omega.
 omega.
rewrite <- (Z2Nat.id n) in H by omega.
change 16 with (Z.of_nat 16) in H.
rewrite <- Nat2Z.inj_mul in H.
apply Nat2Z.inj in H.
clear H1.
revert blocks H regs H0; induction (Z.to_nat n); intros.
destruct blocks; inv H.
rewrite process_msg_equation, hash_blocks_equation.
reflexivity.
assert (length (firstn 16 blocks) = 16)%nat
 by (rewrite firstn_length, H; simpl; omega).
rewrite hash_blocks_equation.
destruct blocks; [ inv H | ].
forget (i::blocks) as bb.
clear n i blocks; rename bb into blocks.
rewrite <- (firstn_skipn 16 blocks) at 1.
rewrite process_msg_eq2 by auto.
rewrite process_block_hash_block; auto.
apply IHn0.
rewrite skipn_length; omega.
apply length_hash_block; auto.
Qed.

Lemma SHA_256'_eq:  SHA_256' = SHA_256.
Proof.
extensionality msg.
unfold SHA_256', SHA_256.
f_equal.
rewrite <- generate_and_pad'_eq.
assert (16 | Zlength (generate_and_pad msg)).
rewrite (length_generate_and_pad msg).
apply roundup_divide; omega.
assert (length init_registers = 8%nat) by reflexivity.
forget init_registers as regs.
forget (generate_and_pad msg) as blocks.
apply process_msg_hash_blocks; auto.
Qed.