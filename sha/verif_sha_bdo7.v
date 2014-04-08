Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo5.
Require Import sha.verif_sha_bdo6.
Local Open Scope logic.
Local Open Scope nat.

Lemma bdo_loop2_body_proof:
 forall (Espec : OracleKind)
   (b : list int) (ctx : val) ( regs : list int) (i : nat)
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
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h))
   SEP  (K_vector;
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
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i0 - 1)) 7))) (eval_id _h))
      SEP  (K_vector;
      `(array_at tuint Tsh (Xarray b (Z.of_nat i0)) 0 LBLOCKz)
        (eval_var _X (tarray tuint LBLOCKz))))).
Proof.
intros.
simplify_Delta; unfold bdo_loop2_body; abbreviate_semax.
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
drop_LOCAL 3. drop_LOCAL 2.
clear; abstract (entailer; apply prop_right; apply and_mod_15_lem).

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
clear; abstract (entailer; apply prop_right; apply and_mod_15_lem).
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

unfold MORE_COMMANDS, POSTCONDITION, abbreviate; clear MORE_COMMANDS POSTCONDITION.
replace Delta with (initialized _s1 (initialized _s0 Delta_loop1))
  by (simplify_Delta; reflexivity).
clear Delta.
simple apply sha_bdo_loop2b; assumption.
Qed.


Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) ctx (regs: list int)
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
        `(eq (Vint (nthi (Round regs (nthi b) (LBLOCKz-1)) 7))) (eval_id _h))
   SEP ( K_vector;
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
                `(eq (Vint (nthi (Round regs (nthi b) 63) 7))) (eval_id _h))
     SEP (K_vector;
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

Definition loop2_inv (rg0: list int) (b: list int) ctx  (delta: Z) (i: nat) :=
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
     `(eq (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h))
     SEP (K_vector;
    `(array_at tuint Tsh (Xarray b (Z.of_nat i)) 0 LBLOCKz)
           (eval_var _X (tarray tuint LBLOCKz))).

apply semax_pre with (EX i:nat, loop2_inv regs b ctx 0 i).
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

apply semax_post' with (loop2_inv regs b ctx 0 c64). 
clear POSTCONDITION;
abstract (unfold loop2_inv;  entailer!).

apply (semax_loop _ _ (EX i:nat, loop2_inv regs b ctx 1 i)).
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
   `(eq (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7))) (eval_id _h))
   SEP  (K_vector;
   `(array_at tuint Tsh (Xarray b (Z.of_nat i)) 0 LBLOCKz)
     (eval_var _X (tarray tuint LBLOCKz)))).
 abstract entailer.
 forward; (* skip *)
   assert (LBE : LBLOCKz=16%Z) by reflexivity; change c64 with 64%nat in *; entailer. 
 (* change (Z.of_nat c64) with 64. *)
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
replace Delta with
  (Delta_loop1) by (simplify_Delta; reflexivity).
simple apply bdo_loop2_body_proof; auto.
Qed.

