Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.sha_lemmas2.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo5.
Local Open Scope logic.

Lemma rearrange_regs2_proof:
 forall (Espec : OracleKind)
   (b : list int) (ctx : val) ( regs : list int) (i : nat),
   (length b = LBLOCK)%nat ->
   (LBLOCK <= i < c64)%nat ->
   (16 <= Z.of_nat i < 64) ->
semax
  (initialized _Ki
     (initialized _T1
        (initialized _t (initialized _s1 (initialized _s0 Delta_loop1)))))
  (PROP  ()
   LOCAL  (`(eq (Vint (nth i K Int.zero))) (eval_id _Ki);
   `(eq
       (Vint
          (Int.add (nthB b i 0)
             (Int.add
                (Int.add (sigma_0 (nthB b i 1)) (sigma_1 (nthB b i 14)))
                (nthB b i 9))))) (eval_id _T1); `(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq
       (map Vint (rnd_64 regs K (firstn i (rev (generate_word (rev b) c48))))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP 
   (`(array_at tuint Tsh (tuints K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
   `(array_at tuint Tsh (Xarray b (Z.of_nat (i + 1))) 0 LBLOCKz)
     (eval_var _X (tarray tuint LBLOCKz)))) rearrange_regs2b
  (normal_ret_assert
     (EX  i0 : nat,
      PROP  ((LBLOCK <= i0 <= c64)%nat)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.of_nat i0 - 1)))) (eval_id _i);
      `(eq
          (map Vint
             (rnd_64 regs K (firstn i0 (rev (generate_word (rev b) c48))))))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
      
      SEP  (K_vector;
      `(array_at tuint Tsh (Xarray b (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
Proof.
intros.
simplify_Delta; abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name T1_ _T1.
name T2_ _T2.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
assert (LBE := LBLOCK_zeq).
rename b into bb.
remember (rnd_64 regs K (firstn i (rev (generate_word (rev bb) c48)))) as regs' eqn:?.
apply (assert_LOCAL (`(exists a b c d e f g h, regs' = [a,b,c,d,e,f,g,h]))).
clear Heqregs'.
entailer.
clear - H3. rename H3 into H0.
exists a_,b_,c_,d_,e_,f_,g_,h_.
do 8 (destruct regs' as [ | ? regs']; [inv H0 | ]).
destruct regs'; inv H0. reflexivity.
normalize.
destruct H2 as [a [b [c [d [e [f [g [h H2]]]]]]]].
rewrite Heqregs' in *. clear Heqregs'.
rewrite H2.
fold (@nth int).
unfold rearrange_regs2b.
forward. (* T1 += h + Sigma1(e) + Ch(e,f,g) + Ki; *)
apply (assert_LOCAL (`(eq (Vint
       (Int.add
          (Int.add (nthB bb i 0) 
             (Int.add (Int.add (sigma_0 (nthB bb i 1)) (sigma_1 (nthB bb i 14))) (nthB bb i 9)))
        (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) (nth i K Int.zero)))))
          (eval_id _T1))).
entailer.
symmetry in H5; inv H5.
f_equal. f_equal. f_equal. f_equal.
apply Sigma_1_eq.
apply (drop_LOCAL 1%nat); unfold delete_nth.
apply (drop_LOCAL 2%nat); unfold delete_nth.
clear T1_0.
forward. 	(* T2 = Sigma0(a) + Maj(a,b,c); *)
apply (assert_LOCAL (`(eq (Vint (Int.add (Sigma_0 a) (Maj a b c))))
          (eval_id _T2))).
entailer.
symmetry in H4; inv H4.
f_equal.
apply Sigma_0_eq.
apply Maj_eq.
apply (drop_LOCAL 1%nat); unfold delete_nth.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with (initialized _T2 (initialized _Ki (initialized _T1 (initialized _t
                                (initialized _s1 (initialized _s0 Delta_loop1))))))
  by (simplify_Delta; reflexivity).
clear Delta.
simple apply rearrange_regs2c_proof; assumption.
Qed.

Local Open Scope Z.

Lemma sha_bdo_loop2b:
 forall (Espec : OracleKind) (b : list int)
    (ctx : val) (regs : list int) (i : nat) (s0 s1 : val), 
length b = LBLOCK ->
(LBLOCK <= i < c64)%nat ->
16 <= Z.of_nat i < 64 ->
semax (initialized _s1 (initialized _s0 Delta_loop1))
  (PROP  ()
   LOCAL  (`(eq (Vint (sigma_1 (nthB b i 14)))) (eval_id _s1);
   `(eq (Vint (sigma_0 (nthB b i 1)))) (eval_id _s0);
   `(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq
       (map Vint (rnd_64 regs K (firstn i (rev (generate_word (rev b) c48))))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP  (K_vector;
   `(array_at tuint Tsh (Xarray b (Z.of_nat i)) 0 LBLOCKz)
     (eval_var _X (tarray tuint LBLOCKz))))
  (Ssequence
     (Sset _T1
        (Ederef
           (Ebinop Oadd (Evar _X (tarray tuint 16))
              (Ebinop Oand (Etempvar _i tint) (Econst_int (Int.repr 15) tint)
                 tint) (tptr tuint)) tuint))
     (Ssequence
        (Sset _t
           (Ederef
              (Ebinop Oadd (Evar _X (tarray tuint 16))
                 (Ebinop Oand
                    (Ebinop Oadd (Etempvar _i tint)
                       (Econst_int (Int.repr 9) tint) tint)
                    (Econst_int (Int.repr 15) tint) tint) (tptr tuint)) tuint))
        (Ssequence
           (Sset _T1
              (Ebinop Oadd (Etempvar _T1 tuint)
                 (Ebinop Oadd
                    (Ebinop Oadd (Etempvar _s0 tuint) (Etempvar _s1 tuint)
                       tuint) (Etempvar _t tuint) tuint) tuint))
           (Ssequence
              (Sassign
                 (Ederef
                    (Ebinop Oadd (Evar _X (tarray tuint 16))
                       (Ebinop Oand (Etempvar _i tint)
                          (Econst_int (Int.repr 15) tint) tint) (tptr tuint))
                    tuint) (Etempvar _T1 tuint))
              (Ssequence
                 (Sset _Ki
                    (Ederef
                       (Ebinop Oadd (Evar _K256 (tarray tuint 64))
                          (Etempvar _i tint) (tptr tuint)) tuint))
                 rearrange_regs2b)))))
  (normal_ret_assert
     (EX  i0 : nat,
      PROP  ((LBLOCK <= i0 <= c64)%nat)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.of_nat i0 - 1)))) (eval_id _i);
      `(eq
          (map Vint
             (rnd_64 regs K (firstn i0 (rev (generate_word (rev b) c48))))))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
      
      SEP  (K_vector;
      `(array_at tuint Tsh (Xarray b (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
Proof.
intros.
simplify_Delta; abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name T1_ _T1.
name T2_ _T2.
name t_ _t.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
assert (LBE := LBLOCK_zeq).

forward. (* T1 = X[i&0xf]; *) 
clear - H H1 LBE;
abstract (
  entailer; 
  replace (Int.repr (Z.of_nat i)) with (Int.repr (Z.of_nat i + 0)) by (rewrite Z.add_0_r; auto);
  apply prop_right; split;
   [apply X_subscript_aux; assumption | apply and_mod_15_lem]
).

apply (assert_LOCAL (`(eq (Vint (nthB b i 0))) (eval_id _T1))).
abstract (
 entailer; apply prop_right;
 replace (Int.repr (Z.of_nat i)) with (Int.repr (Z.of_nat i + 0)) in H4  by (rewrite Z.add_0_r; auto);
 rewrite X_subscript_aux2 in H3 by repable_signed;
 replace (Z.of_nat i mod 16) with ((Z.of_nat i + 0) mod 16) in H3
    by (rewrite Z.add_0_r; auto);
 rewrite extract_from_b in H3 by omega;
  clear - H3; congruence
).
apply (drop_LOCAL 1%nat); unfold delete_nth.

forward. (* t = X[(i+9)&0xf]; *)
clear - H H1 LBE;
abstract (
  entailer; apply prop_right; split;
 [apply X_subscript_aux; assumption | apply and_mod_15_lem]).

apply (assert_LOCAL (`(eq (Vint (nthB b i 9))) (eval_id _t))).
abstract (
 entailer; apply prop_right;
 rewrite add_repr in H3;
 rewrite X_subscript_aux2 in H3 by repable_signed;
 rewrite extract_from_b in H3 by omega;
 clear - H3; congruence).
apply (drop_LOCAL 1%nat); unfold delete_nth.
forward.  (* T1 += s0 + s1 + t; *)
apply (assert_LOCAL (`(eq (Vint (Int.add (nthB b i 0)
                         (Int.add (Int.add (sigma_0 (nthB b i 1))
                                                   (sigma_1 (nthB b i 14)))
                                      (nthB b i 9))))) (eval_id _T1))).
 abstract entailer.
apply (drop_LOCAL 1%nat); unfold delete_nth.
apply (drop_LOCAL 1%nat); unfold delete_nth.
apply (drop_LOCAL 1%nat); unfold delete_nth.
apply (drop_LOCAL 1%nat); unfold delete_nth.
apply (drop_LOCAL 1%nat); unfold delete_nth.
 clear s0 s1 T1_0.

forward. (* X[i&0xf] = T1; *)
instantiate (2:= (Z.of_nat i  mod 16)).
instantiate (1:=  (Vint (Int.add (nthB b i 0)
                         (Int.add (Int.add (sigma_0 (nthB b i 1))
                                                   (sigma_1 (nthB b i 14)))
                                      (nthB b i 9))))).
abstract (
 entailer;
 apply prop_right; split;
 [ unfold Int.and; rewrite mul_repr;
  f_equal; f_equal; f_equal; 
  change (Int.unsigned (Int.repr 15)) with (Z.ones 4);
  rewrite Z.land_ones by (clear; omega);
  f_equal; rewrite Int.unsigned_repr by repable_signed; auto
 | change LBLOCKz with 16; apply Z.mod_bound_pos; omega
 ]).
rewrite Xarray_update by auto.

unfold K_vector.
forward.  (* Ki=K256[i]; *)
abstract (
 entailer; split;
 [unfold tuints, ZnthV; rewrite if_false by (clear; omega);
 rewrite (@nth_map' int val _ _ Int.zero); [apply I | ];
 change (length K) with 64%nat; rewrite Nat2Z.id; destruct H0 as [_ H0]; apply H0
 | change (Zlength K) with 64; destruct H1; assumption]).

apply (assert_LOCAL (`(eq (Vint (nth i K Int.zero))) (eval_id _Ki))).
entailer.
rewrite Int.signed_repr in H3 by repable_signed.
unfold tuints, ZnthV in H3.
rewrite if_false in H3 by omega.
rewrite Nat2Z.id in H3.
rewrite (@nth_map' int val _ _ Int.zero) in H3.
injection H3; clear; auto.
clear - H0. apply H0.
apply (drop_LOCAL 1%nat); unfold delete_nth.

unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with (initialized _Ki (initialized _T1 (initialized _t
                                (initialized _s1 (initialized _s0 Delta_loop1)))))
  by (simplify_Delta; reflexivity).
clear Delta.
apply rearrange_regs2_proof; assumption.
Admitted. (* Proof is done here, Qed takes more than 2 gigs *)
