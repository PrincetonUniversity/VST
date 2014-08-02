Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_final2.
Require Import sha.verif_sha_final3.
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
unfold sha256state_; normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
unfold_data_at 1%nat.
unfold_field_at 1%nat.
unfold_field_at 3%nat.
normalize.
rename H1 into H99.
rename H2 into H98.
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct a as [hashed data].
destruct H0 as [H0 [H1 [H2 [[H3 DDbytes] [H4 H5]]]]].
destruct H1 as [hi [lo [? [? ?]]]].
subst r_Nh r_Nl r_num r_data. rename data into dd.
assert (H3': (Zlength dd < 64)%Z) by assumption.
unfold at_offset.
forward. (* p = c->data;  *)
entailer!.
forward. (* n = c->num; *)
simpl.
unfold at_offset.  (* maybe this line should not be necessary *)
forward. (* p[n] = 0x80; *)
  instantiate (2:= Zlength dd).
  entailer!; [| rewrite Zlength_correct in H3'|-*; omega].
  rewrite <- H2, <- H1.
  rewrite <- offset_val_force_ptr by omega.
  destruct (eval_id _c rho); inversion H5.
  rewrite sem_add_pi_ptr by auto.
  simpl force_val. unfold offset_val.
  unfold Int.mul; change (Int.unsigned (Int.repr 1)) with 1.
  rewrite Z.mul_1_l.
  unfold Int.add at 3 4.
  change (Int.unsigned Int.zero) with 0.
  rewrite Z.add_0_r.
  rewrite !Int.repr_unsigned.
  rewrite <- int_add_assoc1.
  reflexivity.
forward. (* n++; *)
rewrite upd_Znth_next
  by (repeat rewrite initial_world.Zlength_map; auto).
simpl. normalize. 
subst r_h. simpl.
change (Int.zero_ext 8 (Int.repr 128)) with (Int.repr 128).
change (align 40 1)%Z with 40%Z.
set (ddlen :=  Zlength dd).
assert (Hddlen: (0 <= ddlen < 64)%Z).
unfold ddlen. split; auto. rewrite Zlength_correct; omega.
repeat rewrite  initial_world.Zlength_map.
forward_if   (invariant_after_if1 hashed dd c md shmd  hi lo).
* (* then-clause *)
 change Delta with Delta_final_if1.
match goal with |- semax _ _ ?c _ => change c with Body_final_if1 end.
 simpl typeof.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
 make_sequential. rewrite overridePost_normal'.
unfold ddlen in *; clear ddlen.
eapply semax_pre0; [|apply (ifbody_final_if1 Espec hashed md c shmd hi lo dd H4 H7 H3 DDbytes)].
entailer!.
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
normalize. rewrite overridePost_normal'. 
apply exp_right with hashed.
apply exp_right with (dd ++ [128]).
apply exp_right with 0%Z.
entailer.
rewrite mul_repr, sub_repr in H1; apply ltu_repr_false in H1.
2: split; computable.
2: assert (64 < Int.max_unsigned)%Z by computable; unfold ddlen in *;
   split; try omega.
clear TC0.
change (16*4)%Z with (Z.of_nat CBLOCK) in H1.
apply andp_right; [apply prop_right; repeat split | cancel].
rewrite Forall_app; split; auto.
repeat constructor; omega.
rewrite app_length; simpl. apply Nat2Z.inj_ge.
repeat rewrite Nat2Z.inj_add; unfold ddlen in H1; rewrite Zlength_correct in H1.
change (Z.of_nat 1) with 1%Z; change (Z.of_nat 8) with 8%Z.
omega.
f_equal. unfold ddlen; repeat rewrite Zlength_correct; f_equal.
rewrite app_length; simpl. rewrite Nat2Z.inj_add; reflexivity.
repeat rewrite map_app; apply derives_refl.
* unfold invariant_after_if1.
apply extract_exists_pre; intro hashed'.
apply extract_exists_pre; intro dd'.
apply extract_exists_pre; intro pad.
apply semax_extract_PROP; intro DDbytes'.
apply semax_extract_PROP; intro PAD.
normalize.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
unfold sha_finish.
unfold SHA_256.
clear ddlen Hddlen.

forward_call (* memset (p+n,0,SHA_CBLOCK-8-n); *)
  (Tsh,
     offset_val (Int.repr (Zlength dd')) (offset_val (Int.repr 40) c)%Z, 
     (Z.of_nat CBLOCK - 8 - Zlength dd')%Z,
     Int.zero).
change 40%Z with data_offset.
entailer!.
rewrite Int.unsigned_repr. Omega1. Omega1. 
rewrite (split_array_at (Z.of_nat CBLOCK - 8)%Z tuchar _ _ _ 64%Z) by
 (change CBLOCK with (64%nat); simpl; omega).
rewrite split_offset_array_at with (z := 0) (lo := Zlength dd') (hi := Z.of_nat CBLOCK - 8); [| | simpl; omega | reflexivity].
Focus 2.
  { 
    change CBLOCK with (64%nat) in *.
    rewrite Zlength_correct.
    simpl.
    omega.
  } Unfocus.
repeat rewrite <- sepcon_assoc.
normalize.
pull_left (array_at tuchar Tsh
     (fun i : Z =>
      ZnthV tuchar (map Vint (map Int.repr dd')) (i + Zlength dd')) 0
     (Z.of_nat CBLOCK - 8 - Zlength dd')
     (offset_val (Int.repr (data_offset + Zlength dd')) c)).
repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
replace (offset_val (Int.repr (data_offset + Zlength dd')) c)%Z
    with (offset_val (Int.repr (sizeof tuchar * Zlength dd')) (offset_val (Int.repr 40) c))%Z.
eapply derives_trans; [apply array_at_array_at_; reflexivity |].
erewrite <- data_at__array_at_ with (a:= noattr); [|rewrite Zlength_correct; omega| unfold legal_alignas_type; simpl; rewrite orb_true_iff; auto].
rewrite <- memory_block_data_at_; [| unfold legal_alignas_type; simpl; rewrite orb_true_iff; auto | unfold nested_non_volatile_type; simpl; rewrite orb_true_iff; auto].
replace (sizeof (Tarray tuchar (Z.of_nat CBLOCK - 8 - Zlength dd') noattr)) with
  (Z.of_nat CBLOCK - 8 - Zlength dd') by
  (simpl sizeof;
   rewrite Z.max_r by (rewrite Zlength_correct; omega);
   destruct (Z.of_nat CBLOCK - 8 - Zlength dd'); reflexivity).
entailer!.


  change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l.
  rewrite offset_offset_val. rewrite add_repr; auto.
  clear - H0. apply Nat2Z.inj_le in H0. rewrite Nat2Z.inj_add in H0.

  (* after_call matually *)
  cbv beta iota. autorewrite with subst.
replace_SEP 0%Z (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
          (Z.of_nat CBLOCK - 8 - Zlength dd')
          (offset_val (Int.repr (Zlength dd')) (offset_val (Int.repr 40) c)))).
entailer!.
 forward.  (* p += SHA_CBLOCK-8; *)
 entailer!.
 simpl eval_binop. normalize.
 unfold force_val2. simpl force_val. rewrite mul_repr, sub_repr.

 replace Delta with Delta_final_if1
  by (simplify_Delta; reflexivity).
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.

(*
1 focused subgoals (unfocused: 0)
, subgoal 1 (ID 18263)
  
  Espec : OracleKind
  hashed : list int
  dd : list Z
  md : val
  c : val
  shmd : share
  hi : int
  lo : int
  hashed' : list int
  dd' : list Z
  H0 : Z.of_nat (length dd') + Z.of_nat 8 <= Z.of_nat CBLOCK
  x : val
  Delta := abbreviate : tycontext
  MORE_COMMANDS := abbreviate : statement
  ============================
   semax Delta_final_if1
     (PROP  ()
      LOCAL 
      (`(eq (force_val (sem_add_pi tuchar x (Vint (Int.repr (16 * 4 - 8))))))
         (eval_id _p); `(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
      `(eq x oo offset_val (Int.repr 40) oo offset_val Int.zero) (eval_id _c);
      `(eq md) (eval_id _md); `(eq c) (eval_id _c))
      SEP 
      (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
           (Z.of_nat CBLOCK - 8 - Zlength dd')
           (offset_val (Int.repr (40 + Zlength dd')) c));
      `(array_at tuint Tsh
          (ZnthV tuint (map Vint (hash_blocks init_registers hashed'))) 0 8 c);
      `(field_at Tsh t_struct_SHA256state_st [_Nl] (Vint lo) c);
      `(field_at Tsh t_struct_SHA256state_st [_Nh] (Vint hi) c);
      `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0
          (Zlength dd') (offset_val (Int.repr data_offset) c));
      `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd')))
          (Z.of_nat CBLOCK - 8) 64 (offset_val (Int.repr data_offset) c));
      `(field_at_ Tsh t_struct_SHA256state_st [_num] c);
      `K_vector (eval_var _K256 (tarray tuint 64));
      `(memory_block shmd (Int.repr 32) md)))
     (Ssequence
        (Sset _cNh
           (Efield
              (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                 t_struct_SHA256state_st) _Nh tuint)) MORE_COMMANDS)
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP  (`K_vector (eval_var _K256 (tarray tuint 64));
         `(data_at_ Tsh t_struct_SHA256state_st c);
         `(data_block shmd
             (intlist_to_Zlist
                (hash_blocks init_registers
                   (generate_and_pad (intlist_to_Zlist hashed ++ dd)))) md))))
*)
simple apply final_part2 with pad; assumption.
Qed.
