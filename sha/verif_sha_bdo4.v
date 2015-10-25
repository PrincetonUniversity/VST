Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.

Lemma rearrange_aux:
 forall h f c k l,
 Int.add (Int.add (Int.add (Int.add h f) c) k) l =
Int.add (Int.add (Int.add (Int.add l h) f) c) k.
Proof.
intros.
rewrite <- (Int.add_commut l).
repeat rewrite (Int.add_assoc h).
rewrite <- (Int.add_assoc l).
repeat rewrite (Int.add_assoc (Int.add l h)).
reflexivity.
Qed.

Lemma loop1_aux_lemma1:
  forall i b,
  (0 <= i < Zlength b) ->
  Zlength b <= 16 ->
  upd_Znth_in_list i
          (map Vint (sublist 0 i b) ++ list_repeat (Z.to_nat (16 - i)) Vundef)
          (Vint (Znth i b Int.zero))
  =  map Vint (sublist 0 (i+1) b) ++ list_repeat (Z.to_nat (16 - (i+1))) Vundef.
Proof.
intros.
unfold upd_Znth_in_list.
autorewrite with sublist.
rewrite (sublist_split 0 i (i+1)) by omega.
rewrite map_app.
rewrite app_ass.
f_equal.
rewrite (sublist_singleton i _ Int.zero) by omega.
simpl. f_equal. f_equal. f_equal. omega.
Qed.

Definition block_data_order_loop1 := 
 Ssequence
 (Sset _i (Econst_int (Int.repr 0) tint))
   (nth 0 (loops (fn_body f_sha256_block_data_order)) Sskip).

Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind) (sh: share)
     (b: list int) ctx (data: val) (regs: list int) kv Xv
     (Hregs: length regs = 8%nat)
     (Hsh: readable_share sh),
     Zlength b = LBLOCKz ->
     semax Delta_loop1
  (PROP  ()
   LOCAL  (temp _a (Vint (nthi regs 0)); temp _b (Vint (nthi regs 1));
                temp _c (Vint (nthi regs 2)); temp _d (Vint (nthi regs 3));
                temp _e (Vint (nthi regs 4)); temp _f (Vint (nthi regs 5));
                temp _g (Vint (nthi regs 6)); temp _h (Vint (nthi regs 7));
                temp _data data; temp _ctx ctx; temp _in data; 
                gvar _K256 kv; lvar _X (tarray tuint LBLOCKz) Xv)
   SEP  (`(data_at_ Tsh (tarray tuint 16) Xv);
           `(data_block sh (intlist_to_Zlist b) data); `(K_vector kv)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(temp _ctx ctx; temp _i (Vint (Int.repr LBLOCKz));
                temp _a (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 0));
                temp _b (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 1));
                temp _c (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 2));
                temp _d (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 3));
                temp _e (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 4));
                temp _f (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 5));
                temp _g (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 6));
                temp _h (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 7));
                gvar _K256 kv; lvar _X (tarray tuint LBLOCKz) Xv)
     SEP (`(K_vector kv);
           `(data_at Tsh (tarray tuint LBLOCKz) (map Vint b) Xv);
           `(data_block sh (intlist_to_Zlist b) data))) ).
Proof.
unfold block_data_order_loop1.
intros.
simpl nth; fold rearrange_regs.
abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
assert (LBE := LBLOCKz_eq).
unfold MORE_COMMANDS, abbreviate.

forward_for_simple_bound 16
   (EX i:Z,
    PROP ()
    LOCAL  (temp _ctx ctx;
                 temp _data  (offset_val (Int.repr (i*4)) data);
                 temp _a (Vint (nthi (Round regs (nthi b) (i - 1)) 0));
                 temp _b (Vint (nthi (Round regs (nthi b) (i - 1)) 1));
                 temp _c (Vint (nthi (Round regs (nthi b) (i - 1)) 2));
                 temp _d (Vint (nthi (Round regs (nthi b) (i - 1)) 3));
                 temp _e (Vint (nthi (Round regs (nthi b) (i - 1)) 4));
                 temp _f (Vint (nthi (Round regs (nthi b) (i - 1)) 5));
                 temp _g (Vint (nthi (Round regs (nthi b) (i - 1)) 6));
                 temp _h (Vint (nthi (Round regs (nthi b) (i - 1)) 7));
                 lvar _X (tarray tuint LBLOCKz) Xv;
                 gvar _K256 kv)
     SEP (`(K_vector kv);
       `(data_at Tsh (tarray tuint LBLOCKz) 
           (map Vint (sublist 0 i b) ++ list_repeat (Z.to_nat (16-i)) Vundef)
            Xv);
   `(data_block sh (intlist_to_Zlist b) data))).
* (* precondition of loop entails the loop invariant *)
 rewrite Round_equation. rewrite if_true by (compute; auto).
 entailer!.
* (* loop body & loop condition preserves loop invariant *)

assert_PROP (data_block sh (intlist_to_Zlist b) data =
   array_at sh (tarray tuchar (Zlength b * 4)) [] 0 (i * 4)
       (sublist 0 (i * 4) (map Vint (map Int.repr (intlist_to_Zlist b))))
       data *
   data_at sh (tarray tuchar 4)
        (map Vint (sublist (i * 4) ((i + 1) * 4) (map Int.repr (intlist_to_Zlist b))))
        (offset_val (Int.repr (i * 4)) data) *
   array_at sh (tarray tuchar (Zlength b * 4)) [] (i * 4 + 4)
       (Zlength b * 4)
       (sublist (4 + i * 4) (Zlength b * 4)
          (map Vint (map Int.repr (intlist_to_Zlist b)))) data). {
 entailer!.
 unfold data_block. rewrite prop_true_andp by auto.
 clear H5 H6.
 unfold data_at at 1. 
   erewrite field_at_Tarray; try reflexivity; auto; try omega.
  2: autorewrite with sublist; Omega1.
   rewrite (split2_array_at _ _ _ 0 (i*4)) by (autorewrite with sublist; omega).
   rewrite (split2_array_at _ _ _ (i*4) (i*4+4)) by (autorewrite with sublist; omega).
   autorewrite with sublist.
  rewrite <- !sepcon_assoc.
  f_equal. f_equal.
  rewrite Zlength_intlist_to_Zlist in H7.
  rewrite array_at_data_at'.
  unfold nested_field_array_type; simpl.
  autorewrite with sublist.
  fold (tarray tuchar 4). f_equal.
   rewrite <- sublist_map.
  rewrite Z.add_comm, Z.mul_add_distr_r.
  reflexivity.
  unfold field_address0; rewrite if_true.
  f_equal. f_equal. simpl. omega.
  eapply field_compatible0_cons_Tarray; try reflexivity; auto; omega.
  eapply field_compatible0_cons_Tarray; try reflexivity; auto; omega.
  eapply field_compatible0_cons_Tarray; try reflexivity; auto; omega.
 }

forward_call (* l = __builtin_read32_reversed(_data) *)
      (offset_val (Int.repr (i*4)) data, sh, 
         sublist (i*4) ((i+1)*4) (map Int.repr (intlist_to_Zlist b)))
      l.
 entailer!; make_Vptr data; reflexivity.
 rewrite H1; cancel.
 autorewrite with sublist; omega.
 simpl map.
 gather_SEP 3 0 4.
 match goal with |- context [SEPx (?A::_)] => 
  replace A with (`(data_block sh (intlist_to_Zlist b) data))
    by (rewrite H1; extensionality rho; unfold_lift; simpl;
         rewrite <- !sepcon_assoc; auto)
 end.
 clear H1. subst l.
rewrite <- Znth_big_endian_integer by omega.
forward. (* data := data + 4; *)
(* 1,194,800 849,172 *)
(* 1,291,784 894,136 *)
forward. (* X[i]=l; *)
simpl.
rewrite loop1_aux_lemma1 by Omega1.
(* 1,506,948 1,110,852 *)
(* 1,506,948 1,134,576 *)
unfold K_vector.
assert (i < Zlength K256)
  by (change (Zlength K256) with (LBLOCKz + 48); 
       pose proof LBLOCKz_eq; omega).
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)
entailer!.
rewrite Znth_nthi by omega. apply I.
(* 1,811,028 1,406,332 *)
subst POSTCONDITION; unfold abbreviate.
replace (i + 1 - 1)%Z with i by omega.
rewrite (Round_equation _ _ i).
unfold Znth at 2. rewrite if_false by omega.
fold (nthi b i).
forget (nthi b) as M.
replace (M i) with (W M i)
  by (rewrite W_equation; rewrite if_true by omega; auto).
assert_PROP (isptr data) as H3 by entailer!.
change (data_at Tsh (tarray tuint  (Zlength K256)) (map Vint K256)) with K_vector.
change (tarray tuint LBLOCKz) with (tarray tuint 16).
match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
  semax_frame [  ] R
end.
clear b H1 H.
replace (Znth i (map Vint K256) Vundef) with (Vint (nthi K256 i))
  by (unfold Znth, nthi; rewrite if_false by omega;
        rewrite nth_map' with (d':=Int.zero); auto;
        apply Nat2Z.inj_lt; rewrite Z2Nat.id by omega;
        change (Z.of_nat (length K256)) with 64; omega).
forget (nthi K256 i) as k.
forget (W M i) as w.
assert (length (Round regs M (i - 1)) = 8)%nat
  by (apply length_Round; auto).
forget (Round regs M (i - 1)) as regs'.
change 16%nat with LBLOCK.
destruct regs' as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; inv H.
unfold rearrange_regs.
abbreviate_semax.
forward. (* T1 = l + h + Sigma1(e) + Ch(e,f,g) + Ki; *)
rewrite <- Sigma_1_eq, <- Ch_eq, rearrange_aux.
forward. (* T2 = Sigma0(a) + Maj(a,b,c); *)
 rewrite <- Sigma_0_eq, <- Maj_eq.
do 8 forward.
rewrite if_false by omega.
unfold nthi; simpl nth.
entailer!.
split3.
+ rewrite Z.mul_add_distr_r; reflexivity.
+ f_equal.  f_equal.
  rewrite rearrange_aux. rewrite rearrange_aux. auto.
+ f_equal. f_equal.
   rewrite (Int.add_commut (Int.add Ki _)).
   do 5 rewrite Int.add_assoc.
   f_equal. rewrite (Int.add_commut (Int.add Ki _)).
   rewrite <- Int.add_assoc. auto.
* (* loop invariant & not test implies postcondition *)
cbv beta.
autorewrite with sublist.
entailer!.
Qed.
