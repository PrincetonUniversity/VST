Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo5.
Local Open Scope logic.

Definition Delta_rearrange_regs2 : tycontext.
simplify_Delta_from 
  (initialized _Ki
     (initialized _T1
        (initialized _t (initialized _s1 (initialized _s0 Delta_loop1))))).
Defined.

Lemma rearrange_regs2_proof:
 forall (Espec : OracleKind)
   (b : list int) (ctx : val) ( regs : list int) (i : nat)
   (Hregs: length regs = 8%nat),
   (Zlength b = LBLOCKz) ->
   (LBLOCK <= i < c64)%nat ->
   (16 <= Z.of_nat i < 64) ->
semax Delta_rearrange_regs2
  (PROP  ()
   LOCAL  (`(eq (Vint (nth i K Int.zero))) (eval_id _Ki);
   `(eq (Vint (W (nthi b) (Z.of_nat i)))) (eval_id _T1);
    `(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0))) (eval_id _a);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1))) (eval_id _b);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2))) (eval_id _c);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3))) (eval_id _d);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4))) (eval_id _e);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5))) (eval_id _f);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6))) (eval_id _g);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h))
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
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 0))) (eval_id _a);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 1))) (eval_id _b);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 2))) (eval_id _c);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 3))) (eval_id _d);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 4))) (eval_id _e);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 5))) (eval_id _f);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 6))) (eval_id _g);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 7))) (eval_id _h))
      
      SEP  (K_vector;
      `(array_at tuint Tsh (Xarray b (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
Proof. {
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
name T1_ _T1.
name T2_ _T2.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
assert (LBE := LBLOCK_zeq).
rename b into bb.
remember (Round regs (nthi bb) (Z.of_nat i - 1)) as regs' eqn:?.
assert (exists a b c d e f g h, regs' = [a,b,c,d,e,f,g,h]).
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
(*apply (drop_LOCAL 1%nat); unfold delete_nth. *)
forward. 	(* T2 = Sigma0(a) + Maj(a,b,c); *)
rewrite <- Sigma_0_eq, <- Maj_eq.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with Delta_rearrange_regs2c
  by (simplify_Delta; reflexivity).
clear Delta.
simple apply (rearrange_regs2c_proof); assumption.
} Qed.

Local Open Scope Z.

Lemma sha_bdo_loop2b:
 forall (Espec : OracleKind) (b : list int)
    (ctx : val) (regs : list int) (i : nat) (s0 s1 : val)
 (Hregs: length regs = 8%nat),
 Zlength b = LBLOCKz ->
(LBLOCK <= i < c64)%nat ->
16 <= Z.of_nat i < 64 ->
semax (initialized _s1 (initialized _s0 Delta_loop1))
  (PROP  ()
   LOCAL  (`(eq (Vint (sigma_1 (W (nthi b) (Z.of_nat i - 16 + 14))))) (eval_id _s1);
   `(eq (Vint (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1))))) (eval_id _s0);
   `(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0))) (eval_id _a);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1))) (eval_id _b);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2))) (eval_id _c);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3))) (eval_id _d);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4))) (eval_id _e);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5))) (eval_id _f);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6))) (eval_id _g);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h))
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
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 0))) (eval_id _a);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 1))) (eval_id _b);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 2))) (eval_id _c);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 3))) (eval_id _d);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 4))) (eval_id _e);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 5))) (eval_id _f);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 6))) (eval_id _g);
      `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 7))) (eval_id _h))
      SEP  (K_vector;
      `(array_at tuint Tsh (Xarray b (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
Proof. {
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
name T1_ _T1.
name T2_ _T2.
name t_ _t.
name Ki _Ki.
name ctx_ _ctx.
name i_ _i.
assert (LBE := LBLOCK_zeq).

forward. (* T1 = X[i&0xf]; *) 
clear - H H1 LBE.
drop_LOCAL 5%nat.
abstract (entailer; apply prop_right; apply and_mod_15_lem).

apply (assert_LOCAL (`(eq (Vint (W (nthi b) (Z.of_nat i - 16 + 0)))) (eval_id _T1))). 
drop_LOCAL 6%nat.
clear - H H0 H1 LBE.
abstract (
 entailer; apply prop_right;
 replace (Int.repr (Z.of_nat i)) with (Int.repr (Z.of_nat i + 0)) in H3  by (rewrite Z.add_0_r; auto);
 rewrite X_subscript_aux2 in H3 by repable_signed;
 replace (Z.of_nat i mod 16) with ((Z.of_nat i + 0) mod 16) in H3
    by (rewrite Z.add_0_r; auto);
 apply Zlength_length in H; auto;
 rewrite extract_from_b in H3 by (try assumption; omega);
 rewrite Z.add_0_r in H3; 
  clear - H3; congruence
).
drop_LOCAL 1%nat.
forward. (* t = X[(i+9)&0xf]; *)
clear - H H1 LBE.
abstract (entailer; apply prop_right; apply and_mod_15_lem).

apply (assert_LOCAL (`(eq (Vint (W (nthi b) (Z.of_nat i - 16 + 9)))) (eval_id _t))).
clear - H H0 H1 LBE.
abstract (
 entailer; apply prop_right;
 rewrite add_repr in H3;
 rewrite X_subscript_aux2 in H3 by repable_signed;
 apply Zlength_length in H; auto;
 rewrite extract_from_b in H3 by (try assumption; omega);
 clear - H3; congruence
).
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
clear s0 s1.

forward. (* X[i&0xf] = T1; *)
instantiate (2:= (Z.of_nat i  mod 16)).
instantiate (1:=  (Vint  (W (nthi b) (Z.of_nat i)))).
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
rewrite Xarray_update by (apply Zlength_length in H; auto).

unfold K_vector.
forward.  (* Ki=K256[i]; *)
abstract (
 entailer!;
 [unfold tuints, ZnthV; rewrite if_false by (clear; omega);
 rewrite (@nth_map' int val _ _ Int.zero); [apply I | ];
 change (length K) with 64%nat; rewrite Nat2Z.id; destruct H0 as [_ H0]; apply H0
 | change (Zlength K) with 64; clear - H1; omega]).

apply (assert_LOCAL (`(eq (Vint (nth i K Int.zero))) (eval_id _Ki))).
drop_LOCAL 5%nat. drop_LOCAL 3%nat. drop_LOCAL 2%nat.
abstract (
   entailer; apply prop_right;
   rewrite Int.signed_repr in H3 by repable_signed;
   unfold tuints, ZnthV in H3; 
   rewrite if_false in H3 by omega; 
   rewrite Nat2Z.id in H3; 
   rewrite (@nth_map' int val _ _ Int.zero) in H3 by apply H0; 
   injection H3; clear; auto;
   clear - H0; apply H0).
drop_LOCAL 1%nat.

unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with Delta_rearrange_regs2
  by (simplify_Delta; reflexivity).
clear Delta.
simple apply (rearrange_regs2_proof _ b ctx regs i); assumption.
} Qed.
