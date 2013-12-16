Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma const_liftx0:
  forall B (P: B), (fun _ : environ => P) = `P.
Proof. reflexivity. Qed.
Hint Rewrite const_liftx0 : norm.

Lemma sizeof_tarray_tuchar:
 forall (n:Z), (n>0)%Z -> (sizeof (tarray tuchar n) =  n)%Z.
Proof. intros.
 unfold sizeof,tarray; cbv beta iota.
  rewrite Z.max_r by omega.
  unfold alignof, tuchar; cbv beta iota.
  repeat  rewrite align_1. rewrite Z.mul_1_l. auto.
Qed.

Lemma Zlength_zeros: forall n, Zlength (zeros n) = n.
Admitted.

Lemma nth_map_zeros:
 forall i j v, (Z.of_nat i < j)%Z -> nth i (map Vint (zeros j)) v = Vint Int.zero.
Admitted.

Hint Rewrite eval_var_env_set : norm. (* needed? *)

Arguments sem_cmp_default c t1 t2 v1 v2 / .

Lemma closed_env_set:
 forall {B} i v (P: environ -> B) rho, 
     closed_wrt_vars (eq i) P -> 
     P (env_set rho i v) = P rho.
Proof.
 intros. hnf in H.
 symmetry; destruct rho; apply H.
 intros; simpl; destruct (ident_eq i i0). left; auto.
 right; rewrite Map.gso; auto.
Qed.
Hint Rewrite @closed_env_set using (solve[auto 50 with closed]) : norm.

Lemma ltu_repr: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma length_zeros: forall n, length (zeros n) = Z.to_nat n.
Proof.
intros. pose proof (Zlength_zeros n).
rewrite Zlength_correct in H.
rewrite <- H at 2.
rewrite Nat2Z.id. auto.
Qed.

Definition Delta_final_if1 : tycontext :=
 initialized _n
          (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot)).

Definition Body_final_if1 := 
  (Ssequence
              (Ssequence
                (Scall (Some _ignore')
                  (Evar _memset (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons tint (Tcons tuint Tnil)))
                                  (tptr tvoid)))
                  ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                     (Etempvar _n tuint) (tptr tuchar)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Ebinop Osub
                     (Ebinop Omul (Econst_int (Int.repr 16) tint)
                       (Econst_int (Int.repr 4) tint) tint)
                     (Etempvar _n tuint) tuint) :: nil))
                (Sset _ignore (Etempvar _ignore' (tptr tvoid))))
              (Ssequence
                (Sset _n (Econst_int (Int.repr 0) tint))
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   (Tcons
                                                     (tptr t_struct_SHA256state_st)
                                                     (Tcons (tptr tvoid)
                                                       Tnil)) tvoid))
                  ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _p (tptr tuchar)) :: nil)))).

Definition invariant_after_if1 hashed dd c md shmd  hi lo:= 
   (EX hashed':list int, EX dd': list int, EX pad:Z,
   PROP  (length (map Int.unsigned dd') + 8 <= CBLOCK;
              (0 <= pad < 8)%Z;
              NPeano.divide LBLOCK (length hashed');
              intlist_to_Zlist (map swap hashed') ++ map Int.unsigned dd' =
              intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd 
                  ++ [128%Z] ++ map Int.unsigned (zeros pad)   )          
   LOCAL 
   (`(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `eq (eval_id _p)
     (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP  (`(array_at tuint Tsh (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) 0 64 
                          (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c);
     K_vector;
   `(memory_block shmd (Int.repr 32) md))).

Lemma map_swap_involutive:
 forall l, map swap (map swap l)  = l.
Proof. intros.
 rewrite map_map. 
 replace (fun x => swap (swap x)) with (@Datatypes.id int).
 apply map_id. extensionality x. symmetry; apply swap_swap.
Qed.

Lemma ifbody_final_if1:
  forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share)
  (hi lo : int) (dd : list int)
 (H4: NPeano.divide LBLOCK (length hashed))
 (H7: (Zlength hashed * 4 + Zlength dd = hilo hi lo)%Z)
 (H3: length dd < CBLOCK),
  semax Delta_final_if1
  (PROP  ()
   LOCAL 
   (`(typed_true tint)
      (eval_expr
         (Ebinop Ogt (Etempvar _n tuint)
            (Ebinop Osub
               (Ebinop Omul (Econst_int (Int.repr 16) tint)
                  (Econst_int (Int.repr 4) tint) tint)
               (Econst_int (Int.repr 8) tint) tint) tint));
   `(eq (Vint (Int.repr (Zlength dd + 1)))) (eval_id _n);
   `eq (eval_id _p) (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuint Tsh
        (ZnthV tuint (map Vint (process_msg init_registers hashed))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh
       (ZnthV tuchar (map Vint dd ++ [Vint (Int.repr 128)])) 0 64
       (offset_val (Int.repr 40) c));
   `(field_at Tsh t_struct_SHA256state_st _num (Vint (Int.repr (Zlength dd))) c);
   K_vector; `(memory_block shmd (Int.repr 32) md))) Body_final_if1
  (normal_ret_assert (invariant_after_if1 hashed dd c md shmd hi lo)).
Proof.
assert (H:=True).
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
name ignore _ignore.
intros.
assert (Hddlen: (0 <= Zlength dd < 64)%Z).
  split; auto; rewrite Zlength_correct; try omega.
 apply Z2Nat.inj_lt; try omega. rewrite Nat2Z.id. apply H3.
set (ddlen := Zlength dd) in *.
intros.
assert (H3': (ddlen < 64)%Z)
 by (unfold ddlen; rewrite Zlength_correct; change 64%Z with (Z.of_nat CBLOCK);
  apply Nat2Z.inj_lt; auto).
 unfold Delta_final_if1; simplify_Delta; unfold Body_final_if1; abbreviate_semax.
 forward.
  {instantiate (1:= (Tsh,
     offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)%Z, 
     (Z.of_nat CBLOCK - (ddlen + 1))%Z,
     Int.zero)) in (Value of witness).
  unfold tc_exprlist. simpl denote_tc_assert.  (* this line should not be necessary *)
  entailer!.
  + hnf. rewrite mul_repr, sub_repr in H1. rewrite H1. reflexivity.
  + simpl. destruct c; try (contradiction Pc); simpl.
       f_equal; rewrite mul_repr. rewrite Int.add_assoc; f_equal.
       rewrite add_repr; change (align 1 1)%Z with 1%Z.
       rewrite Z.mul_1_l. f_equal; apply Z.add_comm.
  + rewrite (split_array_at (ddlen+1) tuchar) by omega.
   repeat rewrite <- sepcon_assoc;
    pull_left (array_at tuchar Tsh (ZnthV tuchar (map Vint dd ++ [Vint (Int.repr 128)]))
   (ddlen + 1) 64 (offset_val (Int.repr 40) c)).
   repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  change (Z.of_nat CBLOCK) with 64%Z.
  destruct (zlt (ddlen+1) 64).
Focus 2. {
 replace (ddlen+1)%Z with 64%Z by omega. rewrite array_at_emp.
 rewrite Z.sub_diag.
 destruct c; try (contradiction Pc). simpl. 
 rewrite memory_block_zero. normalize.
 } Unfocus.
    replace (64 - (ddlen + 1))%Z
     with (sizeof (tarray tuchar (64 - (ddlen + 1))))%Z
    by (apply sizeof_tarray_tuchar; omega).
   rewrite memory_block_typed.
    replace (offset_val (Int.repr (40 + (ddlen+1))) c)%Z
    with (offset_val (Int.repr (sizeof tuchar * (ddlen+1))) (offset_val (Int.repr 40) c))%Z.
  set (jj:= (64-(ddlen+1))%Z).
  simpl_data_at.
   rewrite <- offset_val_array_at.
  rewrite Z.add_0_r.
 replace (ddlen + 1 + jj)%Z with 64%Z by (unfold jj; omega). clear jj.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 unfold ZnthV.
 rewrite if_false by omega.
 rewrite if_false by omega.
 repeat rewrite nth_overflow; auto.
 simpl; omega.
 rewrite app_length; rewrite map_length; simpl.
apply Nat2Z.inj_le. rewrite Z2Nat.id by omega.
 rewrite Nat2Z.inj_add. replace (Z.of_nat (length dd)) with ddlen.
 change (Z.of_nat 1) with 1%Z; omega.
 unfold ddlen. rewrite Zlength_correct; auto.
 rewrite offset_offset_val; f_equal.
 rewrite add_repr; simpl sizeof. change (align 1 1) with 1%Z.
 rewrite Z.mul_1_l. auto.
   reflexivity.
 }
  forward. (* finish the call *)
  forward.  (* n=0; *)
replace_SEP 0%Z (
      `(array_at tuchar Tsh (fun _ => Vint Int.zero) 0
          (Z.of_nat CBLOCK - (ddlen + 1))
          (offset_val (Int.repr (ddlen + 1)) (offset_val (Int.repr 40) c)))).
entailer!.
gather_SEP 4%Z 0%Z.
pose (ddz := ((dd ++ [Int.repr 128]) ++ zeros (Z.of_nat CBLOCK-(ddlen+1)))%Z).
replace_SEP 0%Z (  `(array_at tuchar Tsh
        (ZnthV tuchar (map Vint ddz)) 0 64
        (offset_val (Int.repr 40) c))).
{entailer!.
 rewrite mul_repr, sub_repr in H0.
 apply ltu_repr in H0.
 2: split; computable.
 2: assert (64 < Int.max_unsigned)%Z by computable; omega.
 change (16*4)%Z with (Z.of_nat CBLOCK) in H0.
 rewrite (split_array_at (ddlen+1) tuchar _ _ 0 64).
 apply sepcon_derives.
 + apply derives_refl'; apply equal_f; apply array_at_ext; intros.
    unfold ZnthV. if_tac; try omega.
    unfold ddz.
    repeat rewrite map_app. simpl map.
   set (dd1 :=  map Vint dd ++ [Vint (Int.repr 128)%Z]).
   rewrite app_nth1. auto. 
   unfold dd1; rewrite app_length. 
   clear - H1; unfold ddlen in *; rewrite Zlength_correct in *;
   rewrite map_length in *. simpl. 
   apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
   rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1%Z. omega.
 +  clear - Pc_ Hddlen.
 assert (ddlen = Zlength dd) by reflexivity.
  replace (Int.repr (40+(ddlen+1))%Z)
   with (Int.add  (Int.repr 40) (Int.repr (sizeof tuchar * (ddlen+1))))%Z
  by (rewrite add_repr;  change (sizeof tuchar) with 1%Z;
  rewrite Z.mul_1_l; auto).
 rewrite <- offset_offset_val.
 rewrite <- offset_val_array_at.
 rewrite Z.add_0_r.
 change (Z.of_nat CBLOCK) with 64%Z.
 replace (ddlen + 1 + (64 - (ddlen + 1)))%Z with 64%Z by omega.
 apply derives_refl'; apply equal_f; apply array_at_ext; intros.
 symmetry.
 unfold ZnthV. rewrite if_false by omega.
 unfold ddz. clear ddz. rewrite map_app.
 rewrite app_nth2.
 rewrite nth_map_zeros; [reflexivity |].
 change (Z.of_nat CBLOCK) with 64%Z.
 rewrite map_length; rewrite app_length.
 apply Z2Nat.inj_lt; try omega.
 rewrite Nat2Z.id.
 replace (length dd + length [Int.repr 128]) with (Z.to_nat (ddlen + 1)).
 rewrite <- Z2Nat.inj_sub.
 apply Z2Nat.inj_lt; try omega. omega.
 rewrite H; simpl. rewrite Zlength_correct.
 rewrite Z2Nat.inj_add by omega. rewrite Nat2Z.id. f_equal.
 rewrite map_length, app_length.
  replace (length dd + length [Int.repr 128]) with (Z.to_nat (ddlen + 1)).
 apply Nat2Z.inj_ge; try omega.
 rewrite Z2Nat.id by omega.
 rewrite Z2Nat.id by omega.
 omega.
 rewrite H; simpl. rewrite Zlength_correct.
 rewrite Z2Nat.inj_add by omega. rewrite Nat2Z.id. f_equal.
 + omega.
 }

destruct (exists_intlist_to_Zlist' LBLOCK (map Int.unsigned ddz))
  as [ddzw [? ?]].
apply Nat2Z.inj. rewrite map_length.
unfold ddz; repeat rewrite app_length.
repeat rewrite Nat2Z.inj_add.
repeat rewrite <- Zlength_correct.
rewrite Zlength_zeros.
rewrite Zlength_cons; rewrite Zlength_nil.
unfold ddlen.
change (LBLOCK*4)%nat with CBLOCK.
clear; omega.
 forward. (* sha256_block_data_order (c,p); *)
 match goal with H : True |- _ => clear H 
            (* WARNING__ is a bit over-eager;
                need to tell it that K_vector is closed *)
  end.

simpl typeof.
instantiate (1:=(hashed, 
                           ddzw,
                           c, 
                           offset_val (Int.repr 40) c,
                           Tsh)) in (Value of witness).
{entailer!.
* subst;  simpl in *.
 rewrite mul_repr, sub_repr in H5. apply H5.
* unfold K_vector. normalize.
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
 cancel.
 repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
 unfold data_block.
 apply derives_refl'; f_equal. 
 unfold tuchars. f_equal. f_equal.
 rewrite <- H0.
 rewrite map_map.
 replace (fun x => Int.repr (Int.unsigned x)) with (@id int) by 
  (extensionality xx; rewrite Int.repr_unsigned; auto).
 symmetry; apply map_id.
 rewrite Zlength_correct;rewrite length_intlist_to_Zlist; rewrite map_length;
  rewrite H1; reflexivity.
}
unfold invariant_after_if1.
 apply exp_right with (hashed ++ (* map swap *) ddzw).
set (pad := (Z.of_nat CBLOCK - (ddlen+1))%Z) in *.
 apply exp_right with (@nil int).
 apply exp_right with pad.
entailer.
rewrite mul_repr, sub_repr in H5.
apply ltu_repr in H5.
2: split; computable.
2: assert (64 < Int.max_unsigned)%Z by computable; omega.
simpl in H2.
assert (0 <= pad < 8)%Z.
unfold pad.
change (16*4)%Z with (Z.of_nat CBLOCK) in H5. 
change (64)%Z with (Z.of_nat CBLOCK) in Hddlen; omega.
assert (length (zeros pad) < 8). 
rewrite length_zeros.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega. 
change (Z.of_nat 8) with 8%Z. omega.
entailer!.
* change CBLOCK with 64; clear; omega.
* apply divide_length_app.
  auto. exists 1; rewrite H1; reflexivity.
* rewrite <- app_nil_end.
  rewrite map_app. 
  rewrite intlist_to_Zlist_app.
  repeat rewrite app_ass.
  f_equal.
  rewrite <- H0.
  unfold ddz.
  repeat rewrite map_app.
  repeat rewrite app_ass.
  simpl.
  rewrite Int.unsigned_repr; auto.
  repable_signed.
* unfold K_vector. normalize.
 erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
  cancel.
  unfold data_block.
  replace (Zlength (intlist_to_Zlist (map swap ddzw))) with 64%Z.
 apply array_at__array_at.
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
 rewrite map_length; rewrite H1.
 reflexivity.
Qed.

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
apply (ifbody_final_if1 Espec hashed md c shmd hi lo dd H4 H7 H3).
* (* else-clause *)
forward. (* skip; *)
unfold invariant_after_if1.
normalize. rewrite overridePost_normal'. 
apply exp_right with hashed.
apply exp_right with (dd ++ [Int.repr 128]).
apply exp_right with 0%Z.
entailer.

Lemma ltu_repr_false: forall i j, 
 (0 <= i <= Int.max_unsigned -> 
  0 <= j <= Int.max_unsigned -> 
  Int.ltu (Int.repr i) (Int.repr j) = false -> i>=j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.
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
destruct c; try contradiction.
unfold offset_val, sem_add_pi.
f_equal. rewrite Int.add_assoc; f_equal.
rewrite mul_repr, add_repr.
change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l.
reflexivity.
rewrite Int.unsigned_repr.
f_equal.
clear - H0.
admit.  (* easy enough *)
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
Admitted.