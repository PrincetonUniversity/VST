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

Lemma Zland_15:
 forall i, Z.land i 15 = i mod 16.
Proof.
intros.
change 15%Z with (Z.ones 4).
rewrite Z.land_ones by (compute; congruence).
reflexivity.
Qed.

Lemma length_Xarray:
  forall b i, length (Xarray b i 0) = 16.
Proof.
intros. rewrite Xarray_eq by computable. reflexivity.
Qed.

Lemma Znth_nthi:
  forall i b,
  (0 <= i < Zlength b)%Z -> Znth i (map Vint b) Vundef = Vint (nthi b i).
Proof.
intros; unfold Znth.
rewrite if_false by omega.
rewrite (@nth_map' int val _ _ Int.zero).
reflexivity.
rewrite Zlength_correct in H.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega. omega.
Qed.

Lemma Znth_nthi':
 forall i b,
  Zlength b = 16%Z ->
  Znth (Z.land i 15) (map Vint b) Vundef = Vint (nthi b (i mod 16)).
Proof.
 intros.
 rewrite Zland_15.
 apply Znth_nthi.
 rewrite H.
 apply Z.mod_pos_bound.
 computable.
Qed.

Lemma Znth_land_is_int:
  forall i b j, 
  is_int I32 Unsigned (Znth (Z.land i 15) (map Vint (Xarray b j 0)) Vundef).
Proof.
intros.
rewrite Zland_15.
rewrite Znth_nthi.
apply I.
apply Z.mod_pos_bound.
change (Zlength (Xarray b j 0)) with (16%Z).
compute; auto.
Qed.

Lemma Zland_in_range:
  forall i, (0 <= Z.land i 15 < 16)%Z.
Proof.
intros.
rewrite Zland_15. apply Z_mod_lt. compute; congruence.
Qed.

Hint Resolve Znth_land_is_int Zland_in_range.

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

STOP.  (* Qinxiang:  the next "forward" crashes Coq! *)

forward. (* X[i&0xf] = T1; *)
{
  instantiate (2:= (Z.of_nat i  mod 16)).
  instantiate (1:=  (Vint  (W (nthi b) (Z.of_nat i)))).
   
  apply prop_right; split.
   
  change (tarray tuint 16) with (tarray tuint LBLOCKz).
  replace (force_val (sem_and tint tint (eval_id _i rho) (Vint (Int.repr 15))))
    with (Vint (Int.repr (Z.of_nat i mod 16))).
  rewrite sem_add_pi_ptr by assumption.
  simpl force_val.
  unfold Int.mul.
  rewrite Int.unsigned_repr by repable_signed. 
  rewrite Int.unsigned_repr.
  simpl sizeof.
  reflexivity.
   
  assert (0 <= Z.of_nat i mod 16 < 16)%Z by (apply Z_mod_lt; omega).
  repable_signed.
   
    change (Int.repr 15) with (Int.repr (Z.ones 4)).
    change (16)%Z with (2 ^ 4)%Z.
    rewrite <- Z.land_ones by (clear; omega).
    rewrite <- H4.
    unfold sem_and.
    simpl.
    unfold Int.and.
    rewrite Int.unsigned_repr by repable_signed; auto.
   
  rewrite <- and_assoc. split.
   
  change LBLOCKz with 16%Z; apply Z.mod_bound_pos; omega.
   
  rewrite <- H2.
  reflexivity.
}
rewrite Xarray_update by (apply Zlength_length in H; auto).

unfold K_vector.
forward.  (* Ki=K256[i]; *)
 entailer!.
 change (Zlength K256) with 64%Z; clear - H1; omega.
unfold tuints, ZnthV; rewrite if_false by (clear; omega);
 rewrite (@nth_map' int val _ _ Int.zero); [apply I | ];
 change (length K256) with 64%nat; rewrite Nat2Z.id; destruct H0 as [_ H0]; apply H0.

(* I am wondering whether this is because I changed the order or assumptions *)

apply (assert_LOCAL (temp _Ki (Vint (nth i K256 Int.zero)))).
drop_LOCAL 4%nat. drop_LOCAL 3%nat. drop_LOCAL 2%nat.
abstract (
   entailer; apply prop_right;
   try rewrite Int.signed_repr in H3 by repable_signed;
   unfold tuints, ZnthV in H3; 
   rewrite if_false in H3 by omega; 
   rewrite Nat2Z.id in H3; 
   rewrite (@nth_map' int val _ _ Int.zero) in H3 by apply H0; 
   injection H3; clear; auto;
   clear - H0; apply H0).
drop_LOCAL 1%nat.

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
rewrite <- Sigma_1_eq, <- Ch_eq.
forward. 	(* T2 = Sigma0(a) + Maj(a,b,c); *)
rewrite <- Sigma_0_eq, <- Maj_eq.
unfold rearrange_regs2c.
repeat forward.
apply exp_right with (i+1)%nat.
entailer.
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
clear - Hregs H H0 Struct_env LBE H1.

Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) ctx (regs: list int) kv
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
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP ( `(K_vector kv);
           `(array_at tuint Tsh (tuints b) 0 16) (eval_var _X (tarray tuint 16))))
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
                var  _K256 (tarray tuint CBLOCKz) kv)
     SEP (`(K_vector kv);
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16))))).
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

Definition loop2_inv (rg0: list int) (b: list int) ctx kv (delta: Z) (i: nat) :=
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
                var  _K256 (tarray tuint CBLOCKz) kv)
     SEP (`(K_vector kv);
    `(array_at tuint Tsh (Xarray b (Z.of_nat i)) 0 LBLOCKz)
           (eval_var _X (tarray tuint LBLOCKz))).

apply semax_pre with (EX i:nat, loop2_inv regs b ctx kv 0 i).
clear -H.
abstract (
 unfold loop2_inv;  apply exp_right with LBLOCK;
 change LBLOCKz with 16%Z;
  change (Z.of_nat LBLOCK) with LBLOCKz;
 rewrite array_at_Xarray
 by (apply Zlength_length in H; auto);
  entailer!;
  change LBLOCK with 16%nat; change c64 with 64%nat; clear; omega
).

apply semax_post' with (loop2_inv regs b ctx kv 0 c64). 
clear POSTCONDITION;
abstract (unfold loop2_inv;  entailer!).

apply (semax_loop _ _ (EX i:nat, loop2_inv regs b ctx kv 1 i)).
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
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(K_vector kv);
   `(array_at tuint Tsh (Xarray b (Z.of_nat i)) 0 LBLOCKz)
     (eval_var _X (tarray tuint LBLOCKz)))).
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

