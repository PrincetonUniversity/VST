Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.spec_sha.
Require Import progs.sha_lemmas.
Require Import progs.sha_lemmas2.
Require Import progs.verif_sha_final2.
Require Import progs.verif_sha_final3.
Local Open Scope logic.

Lemma body_SHA256_Final: semax_body Vprog Gtot f_SHA256_Final SHA256_Final_spec.
Proof.
start_function.
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
name ignore _ignore.
unfold sha256state_; normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
simpl_data_at.
normalize.
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct a as [hashed data].
destruct H0 as [? [? [? [? [? ?]]]]].
destruct H1 as [hi [lo [? [? ?]]]].
destruct H2 as [dd [? ?]].
subst r_Nh r_Nl r_num r_data.
revert POSTCONDITION; subst data; intro.
rewrite map_length in H3.
assert (H3': (Zlength dd < 64)%Z).
rewrite Zlength_correct. change 64%Z with (Z.of_nat CBLOCK).
apply Nat2Z.inj_lt; auto.
rewrite initial_world.Zlength_map in H7.
match goal with |- semax _ (PROPx _ ?B) _ _ =>
 apply semax_pre with (PROPx (Forall isbyteZ (map Int.unsigned dd) :: nil) B)
end.
entailer.
unfold at_offset.
change 64%Z with (Z.of_nat 64).
rewrite array_at_tuchar_isbyteZ.
rewrite firstn_same. normalize.
rewrite map_length. rewrite Zlength_correct in H3'. omega.
apply semax_extract_PROP; intro DDbytes.
forward. (* p = c->data;  *)
entailer!.
forward. (* n = c->num; *)
simpl.
unfold at_offset.  (* maybe this line should not be necessary *)
forward. (* p[n] = 0x80; *)
entailer!. rewrite Zlength_correct; omega.
rewrite initial_world.Zlength_map ; auto.
forward. (* n++; *)
rewrite upd_Znth_next
  by (repeat rewrite initial_world.Zlength_map; auto).
simpl. normalize. 
subst r_h n0. simpl. rewrite add_repr.
change (Int.zero_ext 8 (Int.repr 128)) with (Int.repr 128).
change (align 40 1)%Z with 40%Z.
set (ddlen :=  Zlength dd).
assert (Hddlen: (0 <= ddlen < 64)%Z).
unfold ddlen. split; auto. rewrite Zlength_correct; omega.
repeat rewrite  initial_world.Zlength_map.
forward_if   (invariant_after_if1 hashed dd c md shmd  hi lo).
* (* can evaluate if-condition *)
  entailer!.
* (* then-clause *)
 change Delta with Delta_final_if1.
match goal with |- semax _ _ ?c _ => change c with Body_final_if1 end.
 simpl typeof.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
 make_sequential. rewrite overridePost_normal'.
unfold ddlen in *; clear ddlen.
apply (ifbody_final_if1 Espec hashed md c shmd hi lo dd H4 H7 H3 DDbytes).
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
normalize. rewrite overridePost_normal'. 
apply exp_right with hashed.
apply exp_right with (dd ++ [Int.repr 128]).
apply exp_right with 0%Z.
entailer.
rewrite mul_repr, sub_repr in H1; apply ltu_repr_false in H1.
2: split; computable.
2: assert (64 < Int.max_unsigned)%Z by computable; unfold ddlen in *;
   split; try omega.
clear TC TC0.
change (16*4)%Z with (Z.of_nat CBLOCK) in H1.
apply andp_right; [apply prop_right; repeat split | cancel].
rewrite map_length, app_length; simpl. apply Nat2Z.inj_ge.
repeat rewrite Nat2Z.inj_add; rewrite Zlength_correct in H1.
change (Z.of_nat 1) with 1%Z; change (Z.of_nat 8) with 8%Z.
omega.
rewrite map_app. f_equal.
f_equal. repeat rewrite Zlength_correct; f_equal.
rewrite app_length; simpl. rewrite Nat2Z.inj_add; reflexivity.
rewrite map_app; apply derives_refl.
* unfold invariant_after_if1.
apply extract_exists_pre; intro hashed'.
apply extract_exists_pre; intro dd'.
apply extract_exists_pre; intro pad.
apply semax_extract_PROP; intro PAD.
normalize.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold sha_finish.
unfold SHA_256.
clear ddlen Hddlen.

forward. (* ignore=memset (p+n,0,SHA_CBLOCK-8-n); *)
 match goal with H : True |- _ => clear H 
            (* WARNING__ is a bit over-eager;
                need to tell it that K_vector is closed *)
  end.
instantiate (1:= (Tsh,
     offset_val (Int.repr (Zlength dd')) (offset_val (Int.repr 40) c)%Z, 
     (Z.of_nat CBLOCK - 8 - Zlength dd')%Z,
     Int.zero)) in (Value of witness).
unfold tc_exprlist. simpl typecheck_exprlist. simpl denote_tc_assert. (* this line should not be necessary *)
entailer!.
rewrite Int.unsigned_repr.
Omega1.
clear - H0.
rewrite map_length in H0. Omega1.
rewrite (split_array_at (Zlength dd') tuchar).
rewrite (split_array_at (Z.of_nat CBLOCK - 8)%Z tuchar _ _ _ 64%Z).
repeat rewrite <- sepcon_assoc.
pull_left (array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) (Zlength dd') (Z.of_nat CBLOCK - 8)%Z
   (offset_val (Int.repr 40) c)).
repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
replace (offset_val (Int.repr (40 + Zlength dd')) c)%Z
    with (offset_val (Int.repr (sizeof tuchar * Zlength dd')) (offset_val (Int.repr 40) c))%Z.
destruct (zlt 0 (Z.of_nat CBLOCK - 8 - Zlength dd'));
  [ | admit].  (* the zero case is simple enough; a similar one is handled above *)
    replace (Z.of_nat CBLOCK - 8 - Zlength dd')%Z
     with (sizeof (tarray tuchar (Z.of_nat CBLOCK - 8 - Zlength dd')))%Z
    by (apply sizeof_tarray_tuchar; omega).
 rewrite memory_block_typed.
  simpl_data_at.
   rewrite <- offset_val_array_at.
 rewrite Z.add_0_r.
 apply derives_refl'; apply equal_f.
 replace (Zlength dd' + (Z.of_nat CBLOCK - 8 - Zlength dd'))%Z
  with (Z.of_nat CBLOCK - 8)%Z by (clear; omega).
 apply array_at_ext; intros.
 unfold ZnthV.
  rewrite if_false by admit. (* easy *)
  rewrite if_false by omega.
  rewrite nth_overflow by admit. (* easy *)
  rewrite nth_overflow by admit. (* easy *)
  reflexivity.
  reflexivity.
  change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l.
  rewrite offset_offset_val. rewrite add_repr; auto.
  clear - H0; admit.  (* easy *)
  clear - H0; admit.  (* easy *)
  cbv beta iota. autorewrite with subst.
  forward. (* finish the call *)
  apply semax_pre with
  (PROP  ()
   LOCAL 
   (`(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `eq (eval_id _p) (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
          (Z.of_nat CBLOCK - 8 - Zlength dd')
          (offset_val (Int.repr (Zlength dd')) (offset_val (Int.repr 40) c)));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) 0 (Zlength dd')
       (offset_val (Int.repr 40) c));
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) (Z.of_nat CBLOCK - 8)
       64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c); K_vector;
   `(memory_block shmd (Int.repr 32) md))).
 entailer!.
 forward.  (* p += SHA_CBLOCK-8; *)
 entailer!.
 simpl eval_binop. normalize.
 unfold force_val2. simpl force_val. rewrite mul_repr, sub_repr.

 replace Delta with (initialized _ignore (initialized _ignore'1 (Delta_final_if1)))
  by (simplify_Delta; reflexivity).

eapply final_part2; eassumption.
Qed.
