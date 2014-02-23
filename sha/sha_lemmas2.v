Require Import proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.sha.

Local Open Scope Z.

Definition padlen' (n: Z) : list Int.int :=
     let q := (n+8)/64*16 + 15 - (n+8)/4   (* number of zero-pad words *)
      in zeros q ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)].

Lemma padlen_eq: padlen=padlen'.
Proof.
extensionality n.
unfold padlen,padlen'; simpl.
f_equal. f_equal.
assert ((n+12)/4 = n/4+3).
intros.
replace (n+12) with (3*4+n) by omega.
 rewrite Z_div_plus_full_l by computable. omega.
rewrite <- H.
replace ((n+12)/4) with ((n+8)/4+1).
rewrite <- Z.add_assoc.
change (1+15) with (1*16).
rewrite <- (Z.add_comm (1*16)).
 rewrite Z_div_plus_full_l by computable.
rewrite Z.mul_add_distr_r.
rewrite Z.div_div by computable.
change (4*16) with 64.
omega.
replace (n+12) with (1*4+(n+8)) by omega.
 rewrite Z_div_plus_full_l by computable.
omega.
Qed.

Lemma length_generate_and_pad'':
  forall (l: list Z) (k: Z),
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
  forall (l: list Z),
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
match goal with |- context [Zlist_to_intlist ?A] =>
  remember A as PADDED eqn:HP
end.
assert (NPeano.divide 4 (length PADDED)). {
subst PADDED.
assert (CBLOCKz > 0) by (change CBLOCKz with 64; computable).
pose proof (roundup_ge (Zlength msg + 9) CBLOCKz H).
assert (Zlength msg >= 0) by (rewrite Zlength_correct; omega).
exists (Z.to_nat (roundup (Zlength msg+9) CBLOCKz / 4 - 2)).
repeat rewrite app_length.
rewrite length_list_repeat.
simpl length.
symmetry.
transitivity (Z.to_nat (roundup (Zlength msg + 9) CBLOCKz / 4 - 2) * Z.to_nat 4)%nat; [reflexivity |].
rewrite <- Z2Nat.inj_mul; try omega.
Focus 2. {
assert (roundup (Zlength msg + 9) CBLOCKz / 4 >= (Zlength msg + 9) / 4)
 by (apply Z_div_ge; omega).
assert ((Zlength msg + 9) / 4 = (Zlength msg + 1)/4 + 2).
replace (Zlength msg + 9) with (Zlength msg + 1 + 2*4) by omega.
rewrite Z_div_plus_full by omega.
auto.
assert (0 <= (Zlength msg + 1)/4).
apply Z.div_pos;  omega.
omega. } Unfocus.
rewrite Z.mul_sub_distr_r.
replace (roundup (Zlength msg + 9) CBLOCKz / 4 * 4) with
  (roundup (Zlength msg + 9) CBLOCKz).
Focus 2.
unfold roundup.
forget ((Zlength msg + 9 + (CBLOCKz - 1)) / CBLOCKz ) as N.
change CBLOCKz with (LBLOCKz * 4).
rewrite Z.mul_assoc.
rewrite Z_div_mult_full by computable.
auto.
rewrite <- roundup_minus by (change CBLOCKz with 64; computable).
change 64 with CBLOCKz.
forget (roundup (Zlength msg + 9) CBLOCKz) as N.
rewrite Zlength_correct in H0|-*.
forget (length msg) as L.
transitivity (Z.to_nat (Z.of_nat L + (1 + (N - (Z.of_nat L + 9))))).
f_equal.
omega.
rewrite Z2Nat.inj_add by omega.
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
rewrite NPeano.Nat.sub_0_r.
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
rewrite Z_div_plus_full_l by computable.
assert (a mod 64 / 4 < 16).
apply Z.div_lt_upper_bound. computable. apply Z.mod_pos_bound; computable.
omega.
}
assert (- (Zlength msg + 9) mod CBLOCKz = 
           (3 - Zlength ccc) + 4* ((Zlength msg+8)/64 * 16 + 15 - (Zlength msg + 8) / 4)). {
assert (LL: length ccc = length (skipn (Z.to_nat (Zlength msg / 4) * 4) msg))
 by congruence.
rewrite skipn_length in LL.
Focus 2.
apply Nat2Z.inj_ge; rewrite <- Zlength_correct. 
 rewrite Nat2Z.inj_mul. rewrite Z2Nat.id by auto. change (Z.of_nat 4) with 4.
assert (0 <= Zlength msg mod 4) 
 by (apply Z.mod_pos_bound; computable).
omega.
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
 by (apply Z.mod_pos_bound; computable).
omega.
replace (Zlength ccc) with (Zlength msg - Zlength msg / 4 * 4) by omega.
clear LL LL'.
change CBLOCKz with 64.
clear - H0 HQ. forget (Zlength msg) as a.
 rewrite <- roundup_minus by omega; unfold roundup.
replace (a  + 9 + (64-1)) with (a + 8 + 1*64) by omega.
rewrite Z_div_plus_full by computable.
rewrite Z.mul_add_distr_r.
rewrite (Z.mul_comm 4).
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_add_distr_r.
change (15*4) with (64-4).
rewrite <- Z.mul_assoc.
change (16*4) with 64.
assert (0 =8+ a / 4 * 4 - (a + 8) / 4 * 4);  [ | omega].
change 8 with (2*4) at 2.
rewrite Z_div_plus_full by computable.
rewrite Z.mul_add_distr_r.
omega.
}
change 64 with CBLOCKz.
rewrite H4.
assert (0 <= Zlength ccc < 4)
 by (clear - H3; rewrite Zlength_correct; omega).
rewrite Z2Nat.inj_add by omega.
rewrite <- list_repeat_app.
replace (Zlength msg / 4 * 4) with (Zlength msg - Zlength ccc).
Focus 2. {
rewrite Heqccc.
rewrite (Zlength_correct (skipn _ _)).
rewrite skipn_length by omega.
rewrite Nat2Z.inj_sub by omega.
rewrite <- Zlength_correct.
rewrite Nat2Z.inj_mul. change (Z.of_nat 4) with 4.
rewrite Z2Nat.id  by omega.
 omega.
} Unfocus.
match goal with |- context [_ ++ list_repeat (Z.to_nat (4 * ?qq)) 0] => 
 assert (Zlist_to_intlist (list_repeat (Z.to_nat (4 * qq)) 0) =
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
unfold Zlist_to_intlist; fold Zlist_to_intlist.
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


Lemma lastblock_lemma:
  forall msg hashed d pad hi lo
  (PAD: pad=0 \/ d=nil),
  (length d + 8 <= CBLOCK)%nat ->
  (0 <= pad < 8)%Z ->
  NPeano.divide LBLOCK (length hashed) ->
  intlist_to_Zlist hashed ++ d =
     msg ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
  (Zlength msg * 8)%Z = hilo hi lo ->
  Forall isbyteZ msg ->
  intlist_to_Zlist (generate_and_pad msg) =
     (msg ++ [128%Z] ++ map Int.unsigned (zeros pad)) ++
  map Int.unsigned (zeros ( -(Zlength msg + 9) mod CBLOCKz - pad) ++
     map Int.repr (intlist_to_Zlist [hi, lo])).
Proof.
intros.
assert (LM: 0 <= Zlength msg) by (rewrite Zlength_correct; omega).
(*rewrite <- generate_and_pad'_eq. *)
unfold generate_and_pad.
rewrite intlist_to_Zlist_app.
rewrite Zlist_to_intlist_to_Zlist.
Focus 2. {
repeat rewrite app_length.
repeat rewrite length_list_repeat.
change CBLOCKz with 64.
rewrite <- roundup_minus by computable.
rewrite Z2Nat.inj_sub by omega.
rewrite Zlength_correct at 2.
rewrite Z2Nat.inj_add by (try rewrite Zlength_correct; omega).
rewrite Nat2Z.id. 
match goal with |- NPeano.divide _ ?A =>
replace A with (Z.to_nat (roundup (Zlength msg + 9) 64 - 8))
end.
unfold roundup.
change 64 with (16*4) at 3.
rewrite Z.mul_assoc.
change 8 with (2*4).
rewrite <- Z.mul_sub_distr_r.
rewrite Z2Nat.inj_mul; try computable.
eexists; reflexivity.
replace (Zlength msg + 9 + (64 - 1)) with (Zlength msg + 8 + 1*64) by omega.
 rewrite Z_div_plus_full by omega.
rewrite Z.mul_add_distr_r.
assert (0 <= (Zlength msg + 8)/64 * 16).
apply Zmult_gt_0_le_0_compat; try omega.
apply Z.div_pos; try omega.
omega.
assert (roundup (Zlength msg + 9) 64 >= Zlength msg + 9)
   by (apply roundup_ge; computable).
simpl length.
apply Nat2Z.inj.
rewrite Z2Nat.id.
repeat rewrite Nat2Z.inj_add.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_add.
repeat rewrite Z2Nat.id by omega.
repeat rewrite <- Zlength_correct.
change (Z.of_nat 1) with 1; omega.
apply Nat2Z.inj_le.
rewrite Nat2Z.inj_add. rewrite Zlength_correct.
repeat rewrite Z2Nat.id by omega.
rewrite <- Zlength_correct.
rewrite Z2Nat.id; omega.
omega.
} Unfocus.
assert (0 <= - (Zlength msg + 9) mod CBLOCKz - pad). {
destruct (zeq pad 0).
clear PAD; subst.
rewrite Z.sub_0_r.
apply Z.mod_pos_bound.
change CBLOCKz with 64; computable.
destruct PAD; [contradiction | subst d].
rename H0 into H0'; assert (H0: 0 < pad < 8) by omega; clear H0' n.
rewrite <- app_nil_end in H2.
clear H.
assert (Z.of_nat (length (intlist_to_Zlist hashed)) =
     Z.of_nat (length (msg ++ [128] ++ map Int.unsigned (zeros pad))))
 by congruence.
rewrite length_intlist_to_Zlist in H.
repeat rewrite app_length in H.
repeat rewrite map_length in H.
rewrite length_zeros in H.
destruct H1 as [n H1].
rewrite H1 in H.
destruct n.
destruct hashed; inv H1.
destruct msg; inv H2.
replace (S n) with (1+n)%nat in H by omega.
rewrite mult_plus_distr_r in H.
rewrite mult_plus_distr_l in H.
repeat rewrite Nat2Z.inj_add in H.
repeat rewrite <- Zlength_correct in H.
change (Zlength [128]) with 1 in H.
rewrite Z2Nat.id in H by omega.
change (Z.of_nat (4*(1*LBLOCK))) with 64 in H.
rewrite mult_assoc in H. rewrite (mult_comm 4) in H.
rewrite <- mult_assoc in H.
rewrite Nat2Z.inj_mul in H. 
change (Z.of_nat (4*LBLOCK)) with CBLOCKz in H.
assert (Zlength msg + 9 = 64 + Z.of_nat n * CBLOCKz + (8-pad)) by omega.
rewrite H5.
change CBLOCKz with 64.
replace (64 + Z.of_nat n * 64) with ((1 + Z.of_nat n) * 64)
 by (rewrite Z.mul_add_distr_r; reflexivity).
rewrite Z.mod_opp_l_nz; try computable.
rewrite Z.add_mod by computable.
rewrite Z_mod_mult.
rewrite Z.add_0_l.
rewrite Z.mod_mod by computable.
rewrite Z.mod_small by omega.
omega.
rewrite Z.add_mod by computable.
rewrite Z_mod_mult.
rewrite Z.add_0_l.
rewrite Z.mod_mod by computable.
rewrite Z.mod_small by omega.
omega.
}
repeat rewrite app_ass.
f_equal. f_equal.
rewrite map_app.
rewrite <- app_ass.
f_equal.
rewrite <- map_app.
rewrite zeros_app by omega.
change 64 with CBLOCKz.
forget (- (Zlength msg + 9) mod CBLOCKz) as B.
replace (pad + (B - pad)) with B by omega.
clear - H5 H0.
rewrite <- (Z2Nat.id B) at 2 by omega.
clear.
induction (Z.to_nat B).
reflexivity.
rewrite inj_S.
rewrite zeros_Zsucc by omega.
simpl.
f_equal; auto.
rewrite H3.
rewrite hilo_lemma.
pose proof (isbyte_intlist_to_Zlist [hi,lo]).
clear - H6.
induction (intlist_to_Zlist [hi,lo]).
reflexivity.
inv H6.
simpl; f_equal; auto.
rewrite Int.unsigned_repr; auto.
unfold isbyteZ in H1; repable_signed. 
clear - H4.
apply Forall_app; split; auto.
apply Forall_app; split; auto.
repeat constructor. omega.
clear.
induction  (Z.to_nat (- (Zlength msg + 9) mod 64)).
constructor.
simpl. constructor; auto. split; repable_signed.
Qed.
