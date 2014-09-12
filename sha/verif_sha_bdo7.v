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

Lemma bdo_loop2_body_proof:
 forall (Espec : OracleKind)
   (b : list int) (ctx : val) ( regs : list int) (i : nat) kv
   (Hregs: length regs = 8%nat)
   (H : Zlength b = LBLOCKz)
   (H0 : (LBLOCK <= i < c64)%nat),
semax Delta_loop1
  (PROP  ()
   LOCAL  (`(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0))) (eval_id _a);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1))) (eval_id _b);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2))) (eval_id _c);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3))) (eval_id _d);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4))) (eval_id _e);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5))) (eval_id _f);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6))) (eval_id _g);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h);
   `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
   SEP  (`(K_vector kv);
   `(array_at tuint Tsh (Xarray b (Z.of_nat i)) 0 LBLOCKz)
     (eval_var _X (tarray tuint LBLOCKz))))
  bdo_loop2_body
  (normal_ret_assert
     (EX  i0 : nat,
      PROP  (LBLOCK <= i0 <= c64)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.of_nat i0 - 1)))) (eval_id _i);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 0))) (eval_id _a);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 1))) (eval_id _b);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 2))) (eval_id _c);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 3))) (eval_id _d);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 4))) (eval_id _e);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 5))) (eval_id _f);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 6))) (eval_id _g);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 7))) (eval_id _h);
   `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
      SEP  (`(K_vector kv);
      `(array_at tuint Tsh (Xarray b (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
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
assert (LBE := LBLOCK_zeq).
assert (16 <= Z.of_nat i < 64)%Z. {
 destruct H0.
 apply Nat2Z.inj_le in H0.
 apply Nat2Z.inj_lt in H1.
 change (Z.of_nat c64) with 64%Z in H1.
 omega.
}

forward.	(*s0 = X[(i+1)&0x0f]; *)
clear; entailer; apply andp_right; [| cancel].
apply prop_right; repeat split; try apply and_mod_15_lem.

forward. (* s0 = sigma0(s0); *)
rename x into s0'.

apply (assert_LOCAL (`(eq (Vint (sigma_0 (W (nthi b) (Z.of_nat i - 16 + 1))
   ))) (eval_id _s0))). {
clear POSTCONDITION MORE_COMMANDS.
drop_LOCAL 5.
abstract (
 entailer; apply prop_right;
 repeat rewrite add_repr in H3;
 repeat rewrite X_subscript_aux2 in H3 by repable_signed;
 rewrite extract_from_b in H3;
 try apply Zlength_length in H; auto; try omega;
 simpl in H3;
 rewrite Int.and_mone in H3;
 inv H3;
 apply sigma_0_eq).
}
drop_LOCAL 1.
drop_LOCAL 1.
clear s0'.

forward. (* s1 = X[(i+14)&0x0f]; *)
clear;  (entailer; apply andp_right; [| cancel]; apply prop_right; repeat split; apply and_mod_15_lem).
forward. (* s1 = sigma1(s1); *)
rename x into s1'.

apply (assert_LOCAL (`(eq (Vint (sigma_1 (W (nthi b) (Z.of_nat i - 16 + 14))))) (eval_id _s1))).
clear POSTCONDITION MORE_COMMANDS.
drop_LOCAL 6.
abstract (
 entailer; apply prop_right;
 rewrite add_repr in H3;
 rewrite X_subscript_aux2 in H3 by repable_signed;
 rewrite extract_from_b in H3;
 try apply Zlength_length in H; auto; try omega;
 simpl in H3; rewrite Int.and_mone in H3;
 inv H3; 
 apply sigma_1_eq).
drop_LOCAL 1.
drop_LOCAL 1.
clear s1'.

forward. (* T1 = X[i&0xf]; *) 
clear - H H1 LBE.
clear; (entailer; apply andp_right; [| cancel]; apply prop_right; repeat split; apply and_mod_15_lem).

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
clear;  (entailer; apply andp_right; [| cancel]; apply prop_right; repeat split; apply and_mod_15_lem).

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
(* clear s0 s1. *)

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
    rewrite <- H3.
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

apply (assert_LOCAL (`(eq (Vint (nth i K256 Int.zero))) (eval_id _Ki))).
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

Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) ctx (regs: list int) kv
     (Hregs: length regs = 8%nat),
     Zlength b = LBLOCKz ->
     semax  Delta_loop1
 (PROP ()
   LOCAL (`(eq ctx) (eval_id _ctx);
               `(eq (Vint (Int.repr 16))) (eval_id _i);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 0))) (eval_id _a);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 1))) (eval_id _b);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 2))) (eval_id _c);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 3))) (eval_id _d);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 4))) (eval_id _e);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 5))) (eval_id _f);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 6))) (eval_id _g);
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 7))) (eval_id _h);
        `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
   SEP ( `(K_vector kv);
           `(array_at tuint Tsh (tuints b) 0 16) (eval_var _X (tarray tuint 16))))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq ctx) (eval_id _ctx);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 0))) (eval_id _a);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 1))) (eval_id _b);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 2))) (eval_id _c);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 3))) (eval_id _d);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 4))) (eval_id _e);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 5))) (eval_id _f);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 6))) (eval_id _g);
                `(eq (Vint (nthi (Round regs (nthi b) 63) 7))) (eval_id _h);
                `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
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
    LOCAL  (`(eq ctx) (eval_id _ctx); 
                 `(eq (Vint (Int.repr (Z.of_nat i - delta)))) (eval_id _i);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 0))) (eval_id _a);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 1))) (eval_id _b);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 2))) (eval_id _c);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 3))) (eval_id _d);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 4))) (eval_id _e);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 5))) (eval_id _f);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 6))) (eval_id _g);
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h);
     `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
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
   LOCAL  (`(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0))) (eval_id _a);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1))) (eval_id _b);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2))) (eval_id _c);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3))) (eval_id _d);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4))) (eval_id _e);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5))) (eval_id _f);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6))) (eval_id _g);
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h);
   `(eq kv) (eval_var _K256 (tarray tuint CBLOCKz)))
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

