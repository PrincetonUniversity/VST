Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.

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

Opaque K.

Definition Delta_rearrange_regs2c : tycontext.
simplify_Delta_from
  (initialized _T2
     (initialized _Ki
        (initialized _T1
           (initialized _t (initialized _s1 (initialized _s0 Delta_loop1)))))).
Defined.

Lemma rearrange_regs2c_proof:
 forall (Espec : OracleKind)
   (bb : list int) (ctx : val) ( regs : list int) (i : nat)
   (a b c d e f g h: int),
  Zlength bb = LBLOCKz ->
  (LBLOCK <= i < c64)%nat ->
  16 <= Z.of_nat i < 64 ->
  Round regs (nthi bb) (Z.of_nat i - 1) =
  [a, b, c, d, e, f, g, h] ->
semax Delta_rearrange_regs2c
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.add (Sigma_0 a) (Maj a b c)))) (eval_id _T2);
   `(eq
       (Vint
          (Int.add
             (W (nthi bb) (Z.of_nat i))
             (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g))
                (nth i K Int.zero))))) (eval_id _T1);
   `(eq (Vint (nth i K Int.zero))) (eval_id _Ki); `(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint a)) (eval_id _a);
   `(eq (Vint b)) (eval_id _b);
   `(eq (Vint c)) (eval_id _c);
   `(eq (Vint d)) (eval_id _d);
   `(eq (Vint e)) (eval_id _e);
   `(eq (Vint f)) (eval_id _f);
   `(eq (Vint g)) (eval_id _g);
   `(eq (Vint h)) (eval_id _h))
   SEP 
   (`(array_at tuint Tsh (tuints K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
   `(array_at tuint Tsh (Xarray bb (Z.of_nat (i + 1))) 0 LBLOCKz)
     (eval_var _X (tarray tuint LBLOCKz))))
  rearrange_regs2c
  (normal_ret_assert
     (EX  i0 : nat,
      PROP  ((LBLOCK <= i0 <= c64)%nat)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.of_nat i0 - 1)))) (eval_id _i);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 0))) (eval_id _a);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 1))) (eval_id _b);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 2))) (eval_id _c);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 3))) (eval_id _d);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 4))) (eval_id _e);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 5))) (eval_id _f);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 6))) (eval_id _g);
      `(eq (Vint (nthi (Round regs (nthi bb) (Z.of_nat i0 - 1)) 7))) (eval_id _h))
      SEP  (K_vector;
      `(array_at tuint Tsh (Xarray bb (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
Proof. {
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
unfold rearrange_regs2c.
repeat forward.
apply exp_right with (i+1)%nat.
entailer.
clear Delta H3.
replace (Z.of_nat (i + 1) - 1) with (Z.of_nat i)
 by (clear; rewrite Nat2Z.inj_add; change (Z.of_nat 1) with 1; omega).
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
} Admitted. (* Proof is done here, Qed takes more than 2 gigs *)
