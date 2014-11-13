Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.
Local Open Scope nat.

Definition rearrange_regs2c := 
     Ssequence (Sset _h (Etempvar _g tuint))
        (Ssequence (Sset _g (Etempvar _f tuint))
           (Ssequence (Sset _f (Etempvar _e tuint))
              (Ssequence
                 (Sset _e
                    (Ebinop Oadd (Etempvar _d tuint) (Etempvar _T1 tuint)
                       tuint))
                 (Ssequence (Sset _d (Etempvar _c tuint))
                    (Ssequence (Sset _c (Etempvar _b tuint))
                       (Ssequence (Sset _b (Etempvar _a tuint))
                          (Sset _a
                             (Ebinop Oadd (Etempvar _T1 tuint)
                                (Etempvar _T2 tuint) tuint)))))))).

Definition rearrange_regs2b :=
Ssequence
  (Sset _T1
     (Ebinop Oadd (Etempvar _T1 tuint)
        (Ebinop Oadd
           (Ebinop Oadd
              (Ebinop Oadd (Etempvar _h tuint)
                 (Ebinop Oxor
                    (Ebinop Oxor
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _e tuint)
                             (Econst_int (Int.repr 26) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _e tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 26) tint) tint) tuint)
                          tuint)
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _e tuint)
                             (Econst_int (Int.repr 21) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _e tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 21) tint) tint) tuint)
                          tuint) tuint)
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _e tuint)
                          (Econst_int (Int.repr 7) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _e tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 7) tint) tint) tuint)
                       tuint) tuint) tuint)
              (Ebinop Oxor
                 (Ebinop Oand (Etempvar _e tuint) (Etempvar _f tuint) tuint)
                 (Ebinop Oand (Eunop Onotint (Etempvar _e tuint) tuint)
                    (Etempvar _g tuint) tuint) tuint) tuint)
           (Etempvar _Ki tuint) tuint) tuint))
  (Ssequence
     (Sset _T2
        (Ebinop Oadd
           (Ebinop Oxor
              (Ebinop Oxor
                 (Ebinop Oor
                    (Ebinop Oshl (Etempvar _a tuint)
                       (Econst_int (Int.repr 30) tint) tuint)
                    (Ebinop Oshr
                       (Ebinop Oand (Etempvar _a tuint)
                          (Econst_int (Int.repr (-1)) tuint) tuint)
                       (Ebinop Osub (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 30) tint) tint) tuint) tuint)
                 (Ebinop Oor
                    (Ebinop Oshl (Etempvar _a tuint)
                       (Econst_int (Int.repr 19) tint) tuint)
                    (Ebinop Oshr
                       (Ebinop Oand (Etempvar _a tuint)
                          (Econst_int (Int.repr (-1)) tuint) tuint)
                       (Ebinop Osub (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 19) tint) tint) tuint) tuint)
                 tuint)
              (Ebinop Oor
                 (Ebinop Oshl (Etempvar _a tuint)
                    (Econst_int (Int.repr 10) tint) tuint)
                 (Ebinop Oshr
                    (Ebinop Oand (Etempvar _a tuint)
                       (Econst_int (Int.repr (-1)) tuint) tuint)
                    (Ebinop Osub (Econst_int (Int.repr 32) tint)
                       (Econst_int (Int.repr 10) tint) tint) tuint) tuint)
              tuint)
           (Ebinop Oxor
              (Ebinop Oxor
                 (Ebinop Oand (Etempvar _a tuint) (Etempvar _b tuint) tuint)
                 (Ebinop Oand (Etempvar _a tuint) (Etempvar _c tuint) tuint)
                 tuint)
              (Ebinop Oand (Etempvar _b tuint) (Etempvar _c tuint) tuint)
              tuint) tuint))
       rearrange_regs2c).

Definition bdo_loop2_body :=
  (Ssequence
     (Sset _s0
        (Ederef
           (Ebinop Oadd (Evar _X (tarray tuint 16))
              (Ebinop Oand
                 (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint)
                 (Econst_int (Int.repr 15) tint) tint) (tptr tuint)) tuint))
     (Ssequence
        (Sset _s0
           (Ebinop Oxor
              (Ebinop Oxor
                 (Ebinop Oor
                    (Ebinop Oshl (Etempvar _s0 tuint)
                       (Econst_int (Int.repr 25) tint) tuint)
                    (Ebinop Oshr
                       (Ebinop Oand (Etempvar _s0 tuint)
                          (Econst_int (Int.repr (-1)) tuint) tuint)
                       (Ebinop Osub (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 25) tint) tint) tuint) tuint)
                 (Ebinop Oor
                    (Ebinop Oshl (Etempvar _s0 tuint)
                       (Econst_int (Int.repr 14) tint) tuint)
                    (Ebinop Oshr
                       (Ebinop Oand (Etempvar _s0 tuint)
                          (Econst_int (Int.repr (-1)) tuint) tuint)
                       (Ebinop Osub (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 14) tint) tint) tuint) tuint)
                 tuint)
              (Ebinop Oshr (Etempvar _s0 tuint)
                 (Econst_int (Int.repr 3) tint) tuint) tuint))
        (Ssequence
           (Sset _s1
              (Ederef
                 (Ebinop Oadd (Evar _X (tarray tuint 16))
                    (Ebinop Oand
                       (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 14) tint) tint)
                       (Econst_int (Int.repr 15) tint) tint) (tptr tuint))
                 tuint))
           (Ssequence
              (Sset _s1
                 (Ebinop Oxor
                    (Ebinop Oxor
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _s1 tuint)
                             (Econst_int (Int.repr 15) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _s1 tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 15) tint) tint) tuint)
                          tuint)
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _s1 tuint)
                             (Econst_int (Int.repr 13) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _s1 tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 13) tint) tint) tuint)
                          tuint) tuint)
                    (Ebinop Oshr (Etempvar _s1 tuint)
                       (Econst_int (Int.repr 10) tint) tuint) tuint))
              (Ssequence
                 (Sset _T1
                    (Ederef
                       (Ebinop Oadd (Evar _X (tarray tuint 16))
                          (Ebinop Oand (Etempvar _i tint)
                             (Econst_int (Int.repr 15) tint) tint)
                          (tptr tuint)) tuint))
                 (Ssequence
                    (Sset _t
                       (Ederef
                          (Ebinop Oadd (Evar _X (tarray tuint 16))
                             (Ebinop Oand
                                (Ebinop Oadd (Etempvar _i tint)
                                   (Econst_int (Int.repr 9) tint) tint)
                                (Econst_int (Int.repr 15) tint) tint)
                             (tptr tuint)) tuint))
                    (Ssequence
                       (Sset _T1
                          (Ebinop Oadd (Etempvar _T1 tuint)
                             (Ebinop Oadd
                                (Ebinop Oadd (Etempvar _s0 tuint)
                                   (Etempvar _s1 tuint) tuint)
                                (Etempvar _t tuint) tuint) tuint))
                       (Ssequence
                          (Sassign
                             (Ederef
                                (Ebinop Oadd (Evar _X (tarray tuint 16))
                                   (Ebinop Oand (Etempvar _i tint)
                                      (Econst_int (Int.repr 15) tint) tint)
                                   (tptr tuint)) tuint) (Etempvar _T1 tuint))
                          (Ssequence
                             (Sset _Ki
                                (Ederef
                                   (Ebinop Oadd
                                      (Evar _K256 (tarray tuint 64))
                                      (Etempvar _i tint) (tptr tuint)) tuint))
                             rearrange_regs2b))))))))).

Definition block_data_order_loop2 := 
   nth 1 (loops (fn_body f_sha256_block_data_order)) Sskip.

Lemma bdo_loop2_body_part2:
forall (Espec : OracleKind)
  (b : list int) (ctx : val) (regs : list int) 
  (i : nat) (kv Xv : val) 
  (Hregs : length regs = 8)
  (H : Zlength b = 16%Z)
  (H0 : LBLOCK <= i < c64)
  (H1 : (16 <= Z.of_nat i < 64)%Z),
semax
  (initialized _t
     (initialized _T1 (initialized _s1 (initialized _s0 Delta_loop1))))
  (PROP  ()
   LOCAL 
   (`(eq
        (Vint
           (Int.add (W (nthi b) (Z.of_nat i - 16))
              (Int.add
                 (Int.add (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1)))
                    (sigma_1 (W (nthi b) (Z.of_nat i - 16 + 14))))
                 (W (nthi b) (Z.of_nat i - 16 + 9)))))) (eval_id _T1);
   temp _s0 (Vint (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1))));
   temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i)));
   temp _a (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0));
   temp _b (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1));
   temp _c (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2));
   temp _d (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3));
   temp _e (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4));
   temp _f (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5));
   temp _g (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6));
   temp _h (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7));
   var _X (tarray tuint 16) Xv; var _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(K_vector kv);
   `(data_at Tsh (tarray tuint 16) (map Vint (Xarray b (Z.of_nat i) 0)) Xv)))
  (Ssequence
     (Sassign
        (Ederef
           (Ebinop Oadd (Evar _X (tarray tuint 16))
              (Ebinop Oand (Etempvar _i tint) (Econst_int (Int.repr 15) tint)
                 tint) (tptr tuint)) tuint) (Etempvar _T1 tuint))
     (Ssequence
        (Sset _Ki
           (Ederef
              (Ebinop Oadd (Evar _K256 (tarray tuint 64)) (Etempvar _i tint)
                 (tptr tuint)) tuint)) rearrange_regs2b))
  (normal_ret_assert
     (EX  i0 : nat,
      PROP  (LBLOCK <= i0 <= c64)
      LOCAL  (temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i0 - 1)));
      temp _a (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 0));
      temp _b (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 1));
      temp _c (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 2));
      temp _d (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 3));
      temp _e (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 4));
      temp _f (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 5));
      temp _g (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 6));
      temp _h (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 7));
      var _X (tarray tuint LBLOCKz) Xv; var _K256 (tarray tuint CBLOCKz) kv)
      SEP  (`(K_vector kv);
      `(data_at Tsh (tarray tuint LBLOCKz)
          (map Vint (Xarray b (Z.of_nat i0) 0)) Xv)))).
Proof.
intros.
abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name t_ _t.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
assert (H': length b = 16). {
  rewrite Zlength_correct in H.
  change 16%Z with (Z.of_nat 16) in H.
  apply Nat2Z.inj; auto.
}
assert (LBE := LBLOCK_zeq).

forward. (* X[i&0xf] = T1; *)
normalize.
replace (W (nthi b) (Z.of_nat i - 16))%Z
 with (W (nthi b) (Z.of_nat i - 16 + 0))%Z
  by (rewrite Z.add_0_r; auto).
replace (Int.add (W (nthi b) (Z.of_nat i - 16 + 0))
             (Int.add
                (Int.add (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1)))
                   (sigma_1 (W (nthi b) (Z.of_nat i - 16 + 14))))
                (W (nthi b) (Z.of_nat i - 16 + 9))))
    with (W (nthi b) (Z.of_nat i))
 by (rewrite W_equation; rewrite if_false by omega;
      rewrite Z.add_0_r;
      rewrite (Int.add_commut (W (nthi b) (Z.of_nat i - 16)));
      repeat rewrite <- Int.add_assoc; f_equal;
      rewrite Int.add_commut; repeat rewrite Int.add_assoc; f_equal;
        [do 2 f_equal; omega | ];
      f_equal; [do 2 f_equal; omega | f_equal; omega]).
rewrite Zland_15.
rewrite Xarray_update by assumption.

unfold K_vector.
change CBLOCKz with 64%Z.
change (Zlength K256) with 64%Z.
forward.  (* Ki=K256[i]; *)
 entailer!.
clear - H1.
unfold Znth. rewrite if_false by omega.
rewrite (@nth_map' int val _ _ Int.zero); [apply I | ].
change (length K256) with (Z.to_nat 64).
apply Z2Nat.inj_lt; omega.
replace (`(eq (Znth (Z.of_nat i) (map Vint K256) Vundef)) (eval_id _Ki))
  with (temp _Ki (Vint (nth i K256 Int.zero)))
 by (unfold temp; f_equal; f_equal;
      unfold Znth; rewrite if_false by omega;
      rewrite (@nth_map' int val _ _ Int.zero);
      f_equal; rewrite Nat2Z.id; auto;
      apply H0).

rename b into bb.
remember (Round regs (nthi bb) (Z.of_nat i - 1)) as regs' eqn:?.
assert (exists a b c d e f g h, regs' = [a;b;c;d;e;f;g;h]).
assert (length regs' = 8%nat) by (subst; apply length_Round; auto).
do 8 (destruct regs' as [ | ? regs']; [inv H2 | ]).
destruct regs'; [ | inv H2].
do 8 eexists; reflexivity.
destruct H2 as [a [b [c [d [e [f [g [h H2]]]]]]]].
rewrite Heqregs' in *. clear Heqregs'.
rewrite H2.
unfold nthi at 2 3 4 5 6 7 8 9. simpl.
unfold rearrange_regs2b.
forward. (* T1 += h + Sigma1(e) + Ch(e,f,g) + Ki; *)
assert_PROP (x=Vint (W (nthi bb) (Z.of_nat i))); [entailer! | ].
drop_LOCAL 2.
subst x.
normalize.
simpl.
rewrite <- Sigma_1_eq, <- Ch_eq.
forward. 	(* T2 = Sigma0(a) + Maj(a,b,c); *)
rewrite <- Sigma_0_eq, <- Maj_eq.
unfold rearrange_regs2c.
repeat forward.
apply exp_right with (i+1)%nat.
entailer.
change (nthi [b_; c_; d_; d; f_; g_; h_; h] 7) with h.
clear Delta H3.
replace (Z.of_nat (i + 1) - 1)%Z with (Z.of_nat i)
 by (clear; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1%Z; omega).
apply prop_right.
clear - H H0 H1 H2.
rewrite Round_equation.
rewrite if_false by omega.
rewrite H2.
unfold rnd_function.
repeat split; try reflexivity.
unfold nthi at 1; simpl.
f_equal. rewrite Int.add_commut.
f_equal. f_equal. unfold nthi. rewrite Nat2Z.id; auto.
unfold nthi at 1; simpl.
f_equal. rewrite Int.add_commut. f_equal.
f_equal. unfold nthi. rewrite Nat2Z.id; auto.
Qed.


Lemma bdo_loop2_body_proof:
 forall (Espec : OracleKind)
   (b : list int) (ctx : val) ( regs : list int) (i : nat) kv Xv
   (Hregs: length regs = 8%nat)
   (H : Zlength b = LBLOCKz)
   (H0 : (LBLOCK <= i < c64)%nat),
semax Delta_loop1
  (PROP  ()
   LOCAL  (temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i)));
                 temp _a  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0));
                 temp _b  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1));
                 temp _c  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2));
                 temp _d  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3));
                 temp _e  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4));
                 temp _f  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5));
                 temp _g  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6));
                 temp _h  (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                 var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(K_vector kv);
   `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (Xarray b (Z.of_nat i) 0)) Xv)))
  bdo_loop2_body
  (normal_ret_assert
     (EX  i0 : nat,
      PROP  (LBLOCK <= i0 <= c64)
      LOCAL  (temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i0 - 1)));
                 temp _a  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 0));
                 temp _b  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 1));
                 temp _c  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 2));
                 temp _d  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 3));
                 temp _e  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 4));
                 temp _f  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 5));
                 temp _g  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 6));
                 temp _h  (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                 var  _K256 (tarray tuint CBLOCKz) kv)
      SEP  (`(K_vector kv);
      `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (Xarray b (Z.of_nat i0) 0)) Xv)))).
Proof.
intros.
unfold bdo_loop2_body; abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name t_ _t.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
assert (H': length b = 16). {
  rewrite Zlength_correct in H.
  change 16%Z with (Z.of_nat 16) in H.
  apply Nat2Z.inj; auto.
}
assert (LBE := LBLOCK_zeq).
assert (16 <= Z.of_nat i < 64)%Z. {
 destruct H0.
 apply Nat2Z.inj_le in H0.
 apply Nat2Z.inj_lt in H1.
 change (Z.of_nat c64) with 64%Z in H1.
 omega.
}
change (tarray tuint LBLOCKz) with (tarray tuint 16).
change LBLOCKz with 16%Z in H.
forward.	(*s0 = X[(i+1)&0x0f]; *)
entailer!.
normalize.
rewrite Znth_nthi' by reflexivity.

forward. (* s0 = sigma0(s0); *)
rename x into s0'.

apply (assert_LOCAL (temp _s0 (Vint (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1))
   )))). {
clear POSTCONDITION MORE_COMMANDS.
drop_LOCAL 5.
abstract ( entailer!; rewrite extract_from_b by auto; rewrite Int.and_mone; apply sigma_0_eq).
}
drop_LOCAL 1.
drop_LOCAL 1.
clear s0'.

forward. (* s1 = X[(i+14)&0x0f]; *)
abstract entailer!.
normalize.
rewrite Znth_nthi' by reflexivity.

forward. (* s1 = sigma1(s1); *)
rename x into s1'.

apply (assert_LOCAL (temp _s1 (Vint (sigma_1 (W (nthi b) (Z.of_nat i - 16 + 14)))))).
clear POSTCONDITION MORE_COMMANDS.
drop_LOCAL 6.
abstract (entailer!; rewrite extract_from_b by auto; rewrite Int.and_mone; apply sigma_1_eq).
drop_LOCAL 1.
drop_LOCAL 1.
clear s1'.

forward. (* T1 = X[i&0xf]; *)
entailer!.
normalize.
rewrite Znth_nthi' by reflexivity.

apply (assert_LOCAL (temp _T1 (Vint (W (nthi b) (Z.of_nat i - 16 + 0))))).
drop_LOCAL 6%nat.
clear - H' H0 H1 LBE.
abstract (
 entailer!;
  replace (Z.of_nat i mod 16) with ((Z.of_nat i + 0) mod 16) 
    by (rewrite Z.add_0_r; auto);
 rewrite extract_from_b; try omega; auto;
 rewrite Z.add_0_r; auto).
drop_LOCAL 1%nat.
forward. (* t = X[(i+9)&0xf]; *)
entailer!.
normalize.
rewrite Znth_nthi' by reflexivity.

apply (assert_LOCAL (temp _t (Vint (W (nthi b) (Z.of_nat i - 16 + 9))))).
clear - H' H0 H1 LBE.
abstract (entailer!; rewrite extract_from_b by (try assumption; try omega); auto).
drop_LOCAL 1%nat.
forward.  (* T1 += s0 + s1 + t; *)
replace (Int.add (W (nthi b) (Z.of_nat i - 16 + 0))
             (Int.add
                (Int.add (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1)))
                   (sigma_1 (W (nthi b) (Z.of_nat i - 16 + 14))))
                (W (nthi b) (Z.of_nat i - 16 + 9))))
    with (W (nthi b) (Z.of_nat i))
 by (rewrite W_equation; rewrite if_false by omega;
      rewrite Z.add_0_r;
      rewrite (Int.add_commut (W (nthi b) (Z.of_nat i - 16)));
      repeat rewrite <- Int.add_assoc; f_equal;
      rewrite Int.add_commut; repeat rewrite Int.add_assoc; f_equal;
        [do 2 f_equal; omega | ];
      f_equal; [do 2 f_equal; omega | f_equal; omega]).

do 3 drop_LOCAL 1%nat.

replace Delta with
 (initialized _t (initialized _T1 (initialized _s1 (initialized _s0 Delta_loop1))))
  by (simplify_Delta; reflexivity).
unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
apply  bdo_loop2_body_part2; try assumption.
Qed.

Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) ctx (regs: list int) kv Xv
     (Hregs: length regs = 8%nat),
     Zlength b = LBLOCKz ->
     semax  Delta_loop1
 (PROP ()
   LOCAL (temp _ctx ctx; temp _i (Vint (Int.repr 16));
               temp _a (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 0));
               temp _b (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 1));
               temp _c (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 2));
               temp _d (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 3));
               temp _e (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 4));
               temp _f (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 5));
               temp _g (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 6));
               temp _h (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP ( `(K_vector kv);
           `(data_at Tsh (tarray tuint LBLOCKz) (map Vint b) Xv)))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(temp _ctx ctx; 
                temp _a (Vint (nthi (Round regs (nthi b) 63) 0));
                temp _b (Vint (nthi (Round regs (nthi b) 63) 1));
                temp _c (Vint (nthi (Round regs (nthi b) 63) 2));
                temp _d (Vint (nthi (Round regs (nthi b) 63) 3));
                temp _e (Vint (nthi (Round regs (nthi b) 63) 4));
                temp _f (Vint (nthi (Round regs (nthi b) 63) 5));
                temp _g (Vint (nthi (Round regs (nthi b) 63) 6));
                temp _h (Vint (nthi (Round regs (nthi b) 63) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                var  _K256 (tarray tuint CBLOCKz) kv)
     SEP (`(K_vector kv);
           `(data_at_ Tsh (tarray tuint LBLOCKz) Xv)))).
Proof.
intros.
unfold block_data_order_loop2; simpl nth.
fold rearrange_regs2c.
fold rearrange_regs2b.
fold bdo_loop2_body.
abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name t_ _t.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
change 16%nat with LBLOCK.

Definition loop2_inv (rg0: list int) (b: list int) ctx kv Xv (delta: Z) (i: nat) :=
    PROP ( (LBLOCK <= i <= c64)%nat )
    LOCAL  (temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i - delta)));
                  temp _a (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 0));
                  temp _b (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 1));
                  temp _c (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 2));
                  temp _d (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 3));
                  temp _e (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 4));
                  temp _f (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 5));
                  temp _g (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 6));
                  temp _h (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                var  _K256 (tarray tuint CBLOCKz) kv)
     SEP (`(K_vector kv);
   `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (Xarray b (Z.of_nat i) 0)) Xv)).

apply semax_pre with (EX i:nat, loop2_inv regs b ctx kv Xv 0 i).
clear -H.
abstract (
 unfold loop2_inv;  apply exp_right with LBLOCK;
 change LBLOCKz with 16%Z;
  change (Z.of_nat LBLOCK) with LBLOCKz;
 rewrite Xarray_0
 by (apply Zlength_length in H; auto);
  entailer!;
  change LBLOCK with 16%nat; change c64 with 64%nat; clear; omega
).

apply semax_post' with (loop2_inv regs b ctx kv Xv 0 c64). 
clear POSTCONDITION;
abstract (unfold loop2_inv;  entailer!).

apply (semax_loop _ _ (EX i:nat, loop2_inv regs b ctx kv Xv 1 i)).
2: abstract (
apply extract_exists_pre; intro i;
forward;  (*  i += 1; *)
apply exp_right with i;
 unfold loop2_inv;  entailer! ; f_equal; omega).

apply extract_exists_pre; intro i.
unfold loop2_inv.
repeat rewrite Z.sub_0_r.

forward_if (
   PROP  ((LBLOCK <= i < c64)%nat)
   LOCAL  (temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i)));
               temp _a (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0));
               temp _b (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1));
               temp _c (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2));
               temp _d (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3));
               temp _e (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4));
               temp _f (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5));
               temp _g (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6));
               temp _h (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(K_vector kv);
   `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (Xarray b (Z.of_nat i) 0)) Xv))).
 forward; (* skip *)
   assert (LBE : LBLOCKz=16%Z) by reflexivity; change c64 with 64%nat in *; entailer. 
   apply semax_extract_PROP; intro;
   assert (LBE : LBLOCKz=16%Z) by reflexivity; change c64 with 64%nat in *;
   forward; (* break; *)
   cbv beta.
  change 64%nat with c64.
  entailer.
   assert (i=64)%nat by omega; subst i;
   apply andp_right; [ apply prop_right | cancel].
 split; auto. change (16<=64)%nat; clear; omega.
 repeat split; reflexivity.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
make_sequential. rewrite loop1_ret_assert_normal.
normalize.
replace Delta with Delta_loop1 by (simplify_Delta; reflexivity).
simple apply bdo_loop2_body_proof; auto.
Qed.

