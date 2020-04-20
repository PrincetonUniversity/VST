(* Definition of Salsa according to Bernstein's paper
"The Salsa20 family of stream ciphers", http://cr.yp.to/snuffle/salsafamily-20071225.pdf*)

Require Import compcert.lib.Coqlib.
Require Import Coq.Strings.String.
Require Import VST.msl.Extensionality.
Require Import List. Import ListNotations.

Require Import compcert.lib.Integers.
Require Import sha.functional_prog.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.tweetNaclBase. (*for bind, combinelist*)

Definition Step1 (x:list int): option (list int):=
match x with [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]
=>
 let y3 := Int.xor x3 (Int.rol (Int.add x15 x11) (Int.repr 7)) in
 let y4 := Int.xor x4 (Int.rol (Int.add x0 x12) (Int.repr 7)) in
 let y9 := Int.xor x9 (Int.rol (Int.add x5 x1) (Int.repr 7)) in
 let y14 := Int.xor x14 (Int.rol (Int.add x10 x6) (Int.repr 7)) in
 Some [x0; x1; x2; y3;
       y4; x5; x6; x7;
       x8; y9; x10; x11;
       x12; x13; y14; x15]
| _ => None
 end.
Definition test1_in := map x2i
  ([ "61707865"; "04030201"; "08070605"; "0c0b0a09";
     "100f0e0d"; "3320646e"; "01040103"; "06020905";
     "00000007"; "00000000"; "79622d32"; "14131211";
     "18171615"; "1c1b1a19"; "201f1e1d"; "6b206574"])%string.
Definition test1_out1 := map x2i ([
"61707865"; "04030201"; "08070605"; "95b0c8b6";
"d3c83331"; "3320646e"; "01040103"; "06020905";
"00000007"; "91b3379b"; "79622d32"; "14131211";
"18171615"; "1c1b1a19"; "130804a0"; "6b206574"])%string.

Goal Step1 test1_in = Some(test1_out1). reflexivity. Qed.

Definition Step2 (x:list int): option (list int):=
match x with [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]
=>
 let y2 := Int.xor x2 (Int.rol (Int.add x10 x14) (Int.repr 9)) in
 let y7 := Int.xor x7 (Int.rol (Int.add x15 x3) (Int.repr 9)) in
 let y8 := Int.xor x8 (Int.rol (Int.add x0 x4) (Int.repr 9)) in
 let y13 := Int.xor x13 (Int.rol (Int.add x5 x9) (Int.repr 9)) in
 Some [x0; x1; y2; x3;
       x4; x5; x6; y7;
       y8; x9; x10; x11;
       x12; y13; x14; x15]
| _ => None
 end.

Definition test1_out2 := map x2i ([
"61707865"; "04030201"; "dc64a31d"; "95b0c8b6";
"d3c83331"; "3320646e"; "01040103"; "a45e5d04";
"71572c6d"; "91b3379b"; "79622d32"; "14131211";
"18171615"; "bb230990"; "130804a0"; "6b206574"])%string.
Goal Step2 test1_out1 = Some(test1_out2). reflexivity. Qed.

Definition Step3 (x:list int): option (list int):=
match x with [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]
=>
 let y1 := Int.xor x1 (Int.rol (Int.add x9 x13) (Int.repr 13)) in
 let y6 := Int.xor x6 (Int.rol (Int.add x14 x2) (Int.repr 13)) in
 let y11 := Int.xor x11 (Int.rol (Int.add x3 x7) (Int.repr 13)) in
 let y12 := Int.xor x12 (Int.rol (Int.add x4 x8) (Int.repr 13)) in
 Some [x0; y1; x2; x3;
       x4; x5; y6; x7;
       x8; x9; x10; y11;
       y12; x13; x14; x15]
| _ => None
 end.

Definition test1_out3 := map x2i ([
"61707865"; "cc266b9b"; "dc64a31d"; "95b0c8b6";
"d3c83331"; "3320646e"; "95f3bcee"; "a45e5d04";
"71572c6d"; "91b3379b"; "79622d32"; "f0a45550";
"f3e4deb6"; "bb230990"; "130804a0"; "6b206574"])%string.
Goal Step3 test1_out2 = Some(test1_out3). reflexivity. Qed.

Definition Step4 (x:list int): option (list int):=
match x with [x0; x1; x2; x3;  x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]
=>
 let y0 := Int.xor x0 (Int.rol (Int.add x8 x12) (Int.repr 18)) in
 let y5 := Int.xor x5 (Int.rol (Int.add x13 x1) (Int.repr 18)) in
 let y10 := Int.xor x10 (Int.rol (Int.add x2 x6) (Int.repr 18)) in
 let y15 := Int.xor x15 (Int.rol (Int.add x7 x11) (Int.repr 18)) in
 Some [y0; x1; x2; x3;
       x4; y5; x6; x7;
       x8; x9; y10; x11;
       x12; x13; x14; y15]
| _ => None
 end.

Definition test1_out4 := map x2i ([
"4dfdec95"; "cc266b9b"; "dc64a31d"; "95b0c8b6";
"d3c83331"; "e78e794b"; "95f3bcee"; "a45e5d04";
"71572c6d"; "91b3379b"; "f94fe453"; "f0a45550";
"f3e4deb6"; "bb230990"; "130804a0"; "a272317e"])%string.
Goal Step4 test1_out3 = Some(test1_out4). reflexivity. Qed.

Definition transp (x:list int): option (list int):=
match x with [x0; x1; x2; x3;  x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]
=> Some [x0; x4; x8; x12;
         x1; x5; x9; x13;
         x2; x6; x10; x14;
         x3; x7; x11; x15]
| _ => None
 end.
Definition test1_out := map x2i ([
"4dfdec95"; "d3c83331"; "71572c6d"; "f3e4deb6";
"cc266b9b"; "e78e794b"; "91b3379b"; "bb230990";
"dc64a31d"; "95f3bcee"; "f94fe453"; "130804a0";
"95b0c8b6"; "a45e5d04"; "f0a45550"; "a272317e"])%string.
Goal transp test1_out4 = Some(test1_out). reflexivity. Qed.

Definition snuffleStep x :=
  bind (Step1 x) (fun y => bind (Step2 y) (fun z => bind (Step3 z) Step4)).

Definition snuffleRound x := bind (snuffleStep x) transp.

Goal snuffleRound test1_in = Some test1_out. reflexivity. Qed.

Definition test1_round2 := map x2i ([
"ba2409b1"; "1b7cce6a"; "29115dcf"; "5037e027";
"37b75378"; "348d94c8"; "3ea582b3"; "c3a9a148";
"825bfcb9"; "226ae9eb"; "63dd7748"; "7129a215";
"4effd1ec"; "5f25dc72"; "a6c3d164"; "152a26d8"])%string.
Goal snuffleRound test1_out = Some(test1_round2). reflexivity. Qed.

Fixpoint Snuffle n x :=
  match n with O => Some x | S m => bind (Snuffle m x) snuffleRound end.

Goal Snuffle 1 = snuffleRound. extensionality. reflexivity. Qed.
Goal Snuffle 2 test1_in = Some(test1_round2). reflexivity. Qed.

Definition test1_round20 := map x2i ([
"58318d3e"; "0292df4f"; "a28d8215"; "a1aca723";
"697a34c7"; "f2f00ba8"; "63e9b0a1"; "27250e3a";
"b1c7f1f3"; "62066edc"; "66d3ccf1"; "b0365cf3";
"091ad09e"; "64f0c40f"; "d60d95ea"; "00be78c9"])%string.
Goal Snuffle 20 test1_in = Some(test1_round20). reflexivity. Qed.

Lemma snuffleRound_length r l:
  snuffleRound r = Some l -> length l = 16%nat /\ length r = 16%nat.
Proof. intros.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H. inv H.
destruct r; simpl in H; inv H.
split; trivial.
Qed.

Lemma snuffleRound_Zlength r l (R: snuffleRound r = Some l):
      Zlength l = 16 /\ Zlength r = 16.
Proof.
  do 2 rewrite Zlength_correct.
  destruct (snuffleRound_length _ _ R) as [A B].
  rewrite A, B; split; reflexivity.
Qed.

Lemma Snuffle_length r: forall i l, Snuffle i r = Some l -> length r = 16%nat -> length l = 16%nat.
Proof. induction i; simpl; intros. inv H; trivial.
remember (Snuffle i r) as s. symmetry in Heqs; destruct s; inv H.
apply snuffleRound_length in H2. apply H2.
Qed.

Lemma Snuffle_Zlength r i l (SN:Snuffle i r = Some l)
      (R:Zlength r = 16): Zlength l= 16.
Proof.
  rewrite Zlength_correct.
  rewrite (Snuffle_length _ _ _ SN); trivial.
  apply sublist.Zlength_length in R; trivial.
Qed.
Opaque Snuffle.