Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.

Definition block_data_order_loop2 :=
   nth 1 (loops (fn_body f_sha256_block_data_order)) Sskip.

Fixpoint Xarray' (b: list int) (i k: nat) : list int :=
 match k with
 | O => nil
 | S k' => W (nthi b) (Z.of_nat i - 16 + (16-(Z.of_nat k)- Z.of_nat i) mod 16) ::
                 Xarray' b i k'
 end.

Definition Xarray (b: list int) (i: nat) := Xarray' b i 16.


Lemma Xarray_simpl:
   forall b, Zlength b = 16 -> Xarray b 16 = b.
Proof.
intros.
apply Zlength_length in H; [ simpl in H | computable].
assert (forall n, (n<=16)%nat -> Xarray' b 16 n = skipn (16-n) b);
 [ | apply H0; auto ].
induction n; intros.
clear H0. rewrite skipn_short by omega. reflexivity.

unfold Xarray'; fold Xarray'.
rewrite IHn by omega. clear IHn.
change (Z.of_nat 16) with 16%Z.

assert (H1: firstn 1 (skipn (16 - S n) b) =
            W (nthi b) (16 - 16 + (Z.of_nat (16 - S n) - 16) mod 16) :: nil). {
 unfold firstn.
 destruct (skipn (16 - S n) b) eqn:?.
 pose proof (skipn_length b (16 - S n)).
 rewrite Heql in H1.
 simpl length in H1.
 omega.
 f_equal.
 pose proof (nth_skipn 0 (16 - S n)%nat b Int.zero).
 rewrite Heql in H1.
 unfold nth at 1 in H1.
 subst.
 rewrite Z.sub_diag. rewrite Z.add_0_l.
 rewrite plus_0_l.
 rewrite Zminus_mod.
 rewrite Z.mod_same by omega. rewrite Z.sub_0_r.
 rewrite Z.mod_mod by omega.
 assert (0 <= (Z.of_nat (16 - S n))mod 16 < 16)%Z by (apply Z.mod_pos_bound; omega).
 rewrite W_equation.
 rewrite if_true by  omega.
 rewrite Z.mod_small.
 unfold nthi.
 rewrite Nat2Z.id.
 reflexivity.
 split; try omega.
 change (Z.of_nat (16 - S n) < Z.of_nat 16)%Z.
 apply Nat2Z.inj_lt.
 omega.
}
assert (H2 := skipn_skipn 1 (16 - S n) b).
replace (16 - S n + 1)%nat with (16 - n)%nat in H2 by omega.
rewrite <- H2.
rewrite <- (firstn_skipn 1 (skipn (16 - S n) b)) at 2.
rewrite H1.
unfold app.
rewrite Nat2Z.inj_sub by omega.
reflexivity.
Qed.

Lemma length_Xarray:
  forall b i, Zlength (Xarray b i) = 16.
Proof.
intros. reflexivity.
Qed.

Lemma nth_Xarray:
  forall b i k,
     (0 <= k < 16)%Z ->
  nthi (Xarray b i) k = W (nthi b) (Z.of_nat i - 16 + (k- Z.of_nat i) mod 16)%Z .
Proof.
intros.
unfold nthi at 1.
remember (Z.to_nat k) as k'.
rewrite <- (Nat2Z.id k') in Heqk'.
apply Z2Nat.inj in Heqk'; try omega.
subst k.
assert (k'<16)%nat by omega.
clear H.
do 16 (destruct k'; try reflexivity).
elimtype False; omega.
Qed.

Lemma extract_from_b:
  forall b i n,
    Zlength b = 16 ->
    (16 <= i < 64) ->
    (0 <= n < 16) ->
    nthi (Xarray b (Z.to_nat i)) ((i + n) mod 16) = W (nthi b) (i - 16 + n).
Proof.
intros.
rewrite nth_Xarray by (apply Z.mod_pos_bound; omega).
f_equal.
f_equal.
rewrite Z2Nat.id by omega. auto.
rewrite Z2Nat.id by omega.
rewrite Zminus_mod.
rewrite Zmod_mod.
rewrite Zplus_mod.
rewrite <- Zminus_mod.
rewrite (Zmod_small n) by omega.
replace (i mod 16 + n - i) with (i mod 16 - i + n) by omega.
rewrite Zplus_mod.
rewrite Zminus_mod.
rewrite Zmod_mod.
rewrite Z.sub_diag.
rewrite (Zmod_small 0) by omega.
rewrite Z.add_0_l.
repeat rewrite Zmod_mod.
apply Zmod_small; omega.
Qed.

Global Opaque Xarray.

Lemma Xarray_update:
 forall i b,
  Zlength b = LBLOCKz ->
  16 <= i < 64 ->
   upd_Znth (i mod 16) (map Vint (Xarray b (Z.to_nat i)))
          (Vint (W (nthi b) i))
  = map Vint (Xarray b (Z.to_nat i+1)).
Proof.
intros.
unfold upd_Znth.
rewrite !sublist_map.
rewrite <- !map_cons, <- !map_app.
f_equal.
repeat match type of H0 with
| (64 <= _ < _)%Z => elimtype False; omega
| (?A <= _ < _)%Z =>
 assert (H9: i=A \/ (A+1 <= i < 64)%Z) by omega;
 clear H0; destruct H9 as [H0|H0];
 [subst i; reflexivity
 | simpl in H0 ]
end.
Qed.

Lemma W_unfold:
  forall i b,
  16 <= i < 64 ->
   W (nthi b) (i) =
    Int.add (W (nthi b) (i - 16 + 0))
             (Int.add
                (Int.add (sigma_0 (W (nthi b) (i - 16 + 1)))
                   (sigma_1 (W (nthi b) (i - 16 + 14))))
                (W (nthi b) (i - 16 + 9))).
Proof.
 intros.
 rewrite W_equation.
 rewrite if_false by omega.
  rewrite Z.add_0_r;
      rewrite (Int.add_commut (W (nthi b) (i - 16)));
      repeat rewrite <- Int.add_assoc; f_equal;
      rewrite Int.add_commut; repeat rewrite Int.add_assoc; f_equal;
        [do 2 f_equal; omega | ];
      f_equal; [do 2 f_equal; omega | f_equal; omega].
Qed.


Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) ctx (regs: list int) gv Xv
     (Hregs: length regs = 8%nat),
     Zlength b = LBLOCKz ->
     semax (func_tycontext f_sha256_block_data_order Vprog Gtot nil)
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
               gvars gv; lvar _X (tarray tuint LBLOCKz) Xv)
   SEP ( K_vector gv;
           data_at Tsh (tarray tuint LBLOCKz) (map Vint b) Xv))
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
                gvars gv; lvar _X (tarray tuint LBLOCKz) Xv)
     SEP (K_vector gv;
            data_at_ Tsh (tarray tuint LBLOCKz) Xv))).
Proof.
intros.
unfold block_data_order_loop2; simpl nth.
rewrite semax_skip_seq.
match goal with
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3)] =>
      fold (Sfor s1 e s2 s3)
 end.
abbreviate_semax.
change 16%nat with LBLOCK.

forward_for_simple_bound 64%Z
   (EX i:Z,
    PROP ((16 <= i)%Z )
    LOCAL  (temp _ctx ctx;
                  temp _a (Vint (nthi (Round regs (nthi b) (i - 1)) 0));
                  temp _b (Vint (nthi (Round regs (nthi b) (i - 1)) 1));
                  temp _c (Vint (nthi (Round regs (nthi b) (i - 1)) 2));
                  temp _d (Vint (nthi (Round regs (nthi b) (i - 1)) 3));
                  temp _e (Vint (nthi (Round regs (nthi b) (i - 1)) 4));
                  temp _f (Vint (nthi (Round regs (nthi b) (i - 1)) 5));
                  temp _g (Vint (nthi (Round regs (nthi b) (i - 1)) 6));
                  temp _h (Vint (nthi (Round regs (nthi b) (i - 1)) 7));
                  lvar _X (tarray tuint LBLOCKz) Xv;
                  gvars gv)
     SEP (K_vector gv;
       data_at Tsh (tarray tuint LBLOCKz) (map Vint (Xarray b (Z.to_nat i))) Xv)).
*
forward. (* skip; *)
Exists 16.
entailer!.
rewrite Xarray_simpl; auto.
*
Intros.
destruct H0 as [_ H2].
assert (H0: LBLOCKz <= i < 64) by (change LBLOCKz with 16%Z; omega).
clear H2 H1.
(*assert (H': length b = 16%nat) by (apply Zlength_length in H; auto). *)
assert (LBE := LBLOCK_zeq).
change LBLOCKz with 16%Z in H0.
change (tarray tuint LBLOCKz) with (tarray tuint 16).
change LBLOCKz with 16%Z in H.
forward.	(*s0 = X[(i+1)&0x0f]; *)
autorewrite with sublist. rewrite Zland_15.
forward. (* s0 = sigma0(s0); *)
rewrite extract_from_b by auto; rewrite Int.and_mone; rewrite <- sigma_0_eq.

forward. (* s1 = X[(i+14)&0x0f]; *)
autorewrite with sublist. rewrite Zland_15.

forward. (* s1 = sigma1(s1); *)
rewrite extract_from_b by auto; rewrite Int.and_mone; rewrite <- sigma_1_eq.

forward. (* T1 = X[i&0xf]; *)
autorewrite with sublist. rewrite Zland_15.
replace (nthi (Xarray b (Z.to_nat i)) (i mod 16))
  with (W (nthi b) (i - 16 + 0))
 by (replace (i mod 16) with ((i + 0) mod 16)
        by (rewrite Z.add_0_r; auto);
      rewrite extract_from_b; try omega; auto).

forward. (* t = X[(i+9)&0xf]; *)
autorewrite with sublist. rewrite Zland_15.
rewrite extract_from_b by (try assumption; try omega).

forward.  (* T1 += s0 + s1 + t; *)
pattern (i-16) at 1; rewrite <- (Z.add_0_r (i - 16)).
rewrite <- (W_unfold i b) by auto.

forward. (* X[i&0xf] = T1; *)
rewrite Zland_15.
rewrite Xarray_update by assumption.
unfold K_vector.
change CBLOCKz with 64%Z.
assert (LEN: Zlength K256 = 64%Z) by reflexivity.
forward.  (* Ki=K256[i]; *)
autorewrite with sublist.
rename b into bb.
assert (Hregs' := length_Round _ (nthi bb) (i-1) Hregs).
remember (Round regs (nthi bb) (i - 1)) as regs' eqn:H1.
(destruct regs' as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]];
  try now inversion Hregs'); [ clear Hregs' ].
change (nthi [a;b;c;d;e;f;g;h]) with (fun t => nth (Z.to_nat t) [a;b;c;d;e;f;g;h] Int.zero);
  cbv beta; simpl nth.
forward. (* T1 += h + Sigma1(e) + Ch(e,f,g) + Ki; *)
rewrite <- Sigma_1_eq, <- Ch_eq.
forward. 	(* T2 = Sigma0(a) + Maj(a,b,c); *)
rewrite <- Sigma_0_eq, <- Maj_eq.
repeat forward.
rewrite Z.add_simpl_r.
rewrite Z2Nat.inj_add by omega.
entailer!. 2: apply derives_refl.
clear - H H0 H1.
rewrite Round_equation.
forget (W (nthi bb) i) as Wbbi.
rewrite if_false by omega.
rewrite <- H1; clear H1.
unfold rnd_function, nthi; simpl.
repeat split; try reflexivity.
 +
  f_equal.
  rewrite <- Int.add_assoc; symmetry; rewrite <- Int.add_assoc.
  f_equal. f_equal.
  rewrite Int.add_commut. rewrite !Int.add_assoc. reflexivity.
 +
  f_equal. f_equal. rewrite Int.add_commut. f_equal.
*
 entailer!.
Qed.
