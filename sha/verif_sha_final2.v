Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope Z.
Local Open Scope logic.

Definition Delta_final_if1 : tycontext.
simplify_Delta_from
 (initialized _n  (initialized _p
     (func_tycontext f_SHA256_Final Vprog Gtot))).
Defined.

Definition Body_final_if1 := 
  (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub
                   (Ebinop Omul (Econst_int (Int.repr 16) tint)
                     (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                   tuint) :: nil))
              (Ssequence
                (Sset _n (Econst_int (Int.repr 0) tint))
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   (Tcons
                                                     (tptr t_struct_SHA256state_st)
                                                     (Tcons (tptr tvoid)
                                                       Tnil)) tvoid cc_default))
                  ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _p (tptr tuchar)) :: nil)))).

Definition invariant_after_if1 hashed (dd: list Z) c md shmd kv:= 
   @exp (environ -> mpred) _ _ (fun hashed': list int =>
   @exp (environ -> mpred) _ _ (fun dd': list Z =>
   @exp (environ -> mpred) _ _ (fun pad: Z =>
   PROP  (Forall isbyteZ dd';
              pad=0%Z \/ dd'=nil;
              (length dd' + 8 <= CBLOCK)%nat;
              (0 <= pad < 8)%Z;
              (LBLOCKz | Zlength hashed')%Z;
              intlist_to_Zlist hashed' ++ dd' =
              intlist_to_Zlist hashed ++  dd 
                  ++ [128%Z] ++ list_repeat (Z.to_nat pad) 0)
   LOCAL 
   (temp _n (Vint (Int.repr (Zlength dd')));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _md md; temp _c c;
    gvar _K256 kv)
   SEP  (`(data_at Tsh t_struct_SHA256state_st 
           (map Vint (hash_blocks init_registers hashed'),
            (Vint (lo_part (bitlength hashed dd)),
             (Vint (hi_part (bitlength hashed dd)),
              (map Vint (map Int.repr dd') 
                 ++ list_repeat (Z.to_nat (CBLOCKz - Zlength dd')) Vundef,
               Vundef))))
           c);
         `(K_vector kv);
         `(memory_block shmd 32 md))))).

Lemma ifbody_final_if1:
  forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share)
  (dd : list Z) (kv: val)
 (H4: (LBLOCKz  | Zlength hashed))
 (H3: Zlength dd < CBLOCKz)
 (H0 : Zlength dd + 1 > 16 * 4 - 8)
 (DDbytes: Forall isbyteZ dd),
  semax Delta_final_if1
  (PROP  ()
   LOCAL 
   (temp _n (Vint (Int.repr (Zlength dd + 1)));
    temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _md md; temp _c c;
    gvar _K256 kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers hashed),
        (Vint (lo_part (bitlength hashed dd)), 
         (Vint (hi_part (bitlength hashed dd)),
          (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)] ++
            list_repeat (Z.to_nat (64 - (Zlength dd + 1))) Vundef,
           Vint (Int.repr (Zlength dd))))))
      c);
    `(K_vector kv);
    `(memory_block shmd 32 md)))
  Body_final_if1
  (normal_ret_assert (invariant_after_if1 hashed dd c md shmd kv)).
Proof.
assert (H:=True).
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
intros.
assert (Hddlen: (0 <= Zlength dd < CBLOCKz)%Z) by Omega1.
set (ddlen := Zlength dd) in *.
set (fill_len := (64 - (ddlen + 1))).
 unfold Delta_final_if1; simplify_Delta; unfold Body_final_if1; abbreviate_semax.
change CBLOCKz with 64 in Hddlen.
unfold data_at. unfold_field_at 1%nat.
normalize.

eapply semax_seq'.
evar (Frame: list (LiftEnviron mpred)).
evar (V: list val).
Require Import sha.call_memcpy.
  eapply (call_memset_tuchar Tsh
   (*dst*) t_struct_SHA256state_st [StructField _data] (ddlen+1)
                V c
   (*src*) Int.zero
   (*len*) (CBLOCKz - (ddlen+1))
        Frame); try reflexivity; try omega; auto.
 split; try omega. change CBLOCKz with 64; repable_signed.
 change CBLOCKz with 64; omega.
 entailer!.
 unfold field_address, field_address0. 
 rewrite ?if_true; auto.
 normalize. f_equal. f_equal.
 rewrite nested_field_offset2_ind. 
 f_equal.
 rewrite !nested_field_type2_ind.
 simpl. destruct (ddlen+1); reflexivity.
 apply compute_legal_nested_field0_spec'.
 repeat constructor; simpl; omega.
 eapply field_compatible0_cons_Tarray; try reflexivity; try omega; auto.
 subst V; cancel.
 abbreviate_semax.
replace (ddlen + 1 + (CBLOCKz - (ddlen + 1))) with CBLOCKz by (clear; omega).
change 64 with CBLOCKz.
pose (ddz := ((map Int.repr dd ++ [Int.repr 128]) ++ list_repeat (Z.to_nat (CBLOCKz-(ddlen+1))) Int.zero)).

replace (splice_into_list (ddlen + 1) CBLOCKz CBLOCKz
           (list_repeat (Z.to_nat (CBLOCKz - (ddlen + 1))) (Vint Int.zero))
           (map Vint (map Int.repr dd) ++
            Vint (Int.repr 128) :: list_repeat (Z.to_nat fill_len) Vundef))
  with  (map Vint ddz).
Focus 2. {
 unfold ddz. rewrite !map_app.
 change (cons (Vint (Int.repr 128))) with (app [Vint (Int.repr 128)]).
 rewrite map_list_repeat.
 rewrite <- ?app_ass.
 assert (Zlength (map Vint (map Int.repr dd) ++ [Vint (Int.repr 128)])
             = ddlen + 1)
  by (rewrite ?Zlength_app, ?Zlength_map, ?Zlength_cons, ?Zlength_nil; reflexivity).
 unfold splice_into_list.
 rewrite sublist_app1
  by (try omega;
       subst fill_len; rewrite Zlength_app, H2,
         Zlength_list_repeat, Z.max_r; omega).
 rewrite sublist_app1
  by (try omega;
       subst fill_len; rewrite Zlength_app, H2,
         Zlength_list_repeat, Z.max_r; omega).
 rewrite (sublist_app1 _ 0 (CBLOCKz - (ddlen+1)))
  by (try omega; rewrite Zlength_list_repeat, Z.max_r; omega).
 rewrite !sublist_same by omega.
 rewrite sublist_same
  by (try omega;
       subst fill_len; rewrite
         Zlength_list_repeat, Z.max_r; omega).
 rewrite sublist_nil. rewrite <- app_nil_end.
 subst fill_len. reflexivity.
} Unfocus.
pose (ddzw := Zlist_to_intlist (map Int.unsigned ddz)).
assert (H0': length ddz = CBLOCK). {
  subst ddz ddlen. clear - Hddlen H3.
  repeat rewrite app_length. simpl.
   apply Nat2Z.inj.   (* Maybe build this into Omega or MyOmega? *)
   MyOmega.
}
assert (H1': length ddzw = LBLOCK). {
  unfold ddzw.
  apply length_Zlist_to_intlist. rewrite map_length. apply H0'.
}
assert (HU: map Int.unsigned ddz = intlist_to_Zlist ddzw). {
  unfold ddzw; rewrite Zlist_to_intlist_to_Zlist; auto.
  rewrite map_length, H0'; exists LBLOCK; reflexivity.
  unfold ddz; repeat rewrite map_app; repeat rewrite Forall_app; repeat split; auto.
  apply Forall_isbyteZ_unsigned_repr; auto.
  constructor. compute. clear; split; congruence.
  constructor.
  rewrite map_list_repeat.
  apply Forall_list_repeat.
  rewrite Int.unsigned_zero. split; clear; omega.
}
clear H0'.
clearbody ddzw.
forward.  (* n=0; *)
erewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
rewrite semax_seq_skip.
forward_call (* sha256_block_data_order (c,p); *)
  (hashed, ddzw, c,
    field_address t_struct_SHA256state_st [StructField _data] c,
    Tsh, kv).
{
  repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
  unfold data_block.
  simpl. apply andp_right.
  apply prop_right.
  apply isbyte_intlist_to_Zlist.
  normalize.
  apply derives_refl'.
  rewrite Zlength_correct.
  rewrite length_intlist_to_Zlist.
  rewrite H1'.
  rewrite <- HU.
  unfold tarray.
  rewrite map_map with (g := Int.repr).
  replace (fun x => Int.repr (Int.unsigned x)) with (@id int) by 
    (extensionality xx; rewrite Int.repr_unsigned; auto).
  rewrite map_id.
  reflexivity.
}
 split; auto.
 rewrite Zlength_length. assumption. change LBLOCKz with 16%Z; computable.
 simpl map.
 unfold invariant_after_if1.
 apply exp_right with (hashed ++ ddzw).
 set (pad := (CBLOCKz - (ddlen+1))%Z) in *.
 apply exp_right with (@nil Z).
 apply exp_right with pad.
 entailer!.
*
split; [ Omega1 |].
split; [ Omega1 |].
split. 
 + rewrite initial_world.Zlength_app.
   apply Zlength_length in H1'; [ | auto]. rewrite H1'.
 clear - H4; destruct H4 as [n ?]; exists (n+1). 
  rewrite Z.mul_add_distr_r; omega.
 +  rewrite <- app_nil_end.
  rewrite intlist_to_Zlist_app.
  f_equal.
  rewrite <- HU.
  unfold ddz.
  repeat rewrite map_app.
  repeat rewrite app_ass.
 f_equal.
 clear - DDbytes; induction dd; simpl.
  auto.
 inv DDbytes; f_equal; auto.
 apply Int.unsigned_repr; unfold isbyteZ in H1; repable_signed.
 rewrite map_list_repeat.
 simpl.  f_equal.
*
 unfold data_at. unfold_field_at 5%nat.
 unfold data_block.
 normalize.
 rewrite prop_true_andp.
 cancel.
 rewrite field_at_data_at by reflexivity.
 normalize.
 rewrite Zlength_intlist_to_Zlist.
 replace (WORD * Zlength ddzw)%Z with 64%Z
  by (rewrite Zlength_correct, H1'; reflexivity).
 rewrite Zlength_nil, Z.sub_0_r.
 eapply derives_trans; [apply data_at_data_at_ | ].
 change (nested_field_type2 t_struct_SHA256state_st [StructField _data])
    with (tarray tuchar 64).
 rewrite Zlength_correct, H1'.
 change (Z.of_nat LBLOCK * 4) with 64.
 apply derives_refl.
 repeat simplify_value_fits.
 repeat split; auto.
 rewrite ?Zlength_map.
 rewrite Zlength_correct, length_hash_blocks; auto.
 rewrite Zlength_app.
 apply Z.divide_add_r; auto.
 rewrite Zlength_correct, H1'.
 apply Z.divide_refl.
 apply Forall_map.
 apply Forall_forall; intros; hnf; simpl; auto.
 apply Forall_list_repeat. intro Hx; contradiction Hx; auto.
Qed.

Definition final_loop :=
 Sfor (Sset _xn (Econst_int (Int.repr 0) tint))
        (Ebinop Olt (Etempvar _xn tuint)
          (Ebinop Odiv (Econst_int (Int.repr 32) tint)
            (Econst_int (Int.repr 4) tint) tint) tint)
        (Ssequence
          (Sset _ll
                             (Ederef
                                (Ebinop Oadd
                                   (Efield
                                      (Ederef
                                         (Etempvar _c
                                            (tptr t_struct_SHA256state_st))
                                         t_struct_SHA256state_st) _h
                                      (tarray tuint 8)) (Etempvar _xn tuint)
                                   (tptr tuint)) tuint))
                          (Ssequence
                             (Scall None
                                (Evar ___builtin_write32_reversed
                                   (Tfunction
                                      (Tcons (tptr tuint) (Tcons tuint Tnil))
                                      tvoid cc_default))
                                [Ecast (Etempvar _md (tptr tuchar))
                                   (tptr tuint); Etempvar _ll tuint])
                             (Sset _md
                                (Ebinop Oadd (Etempvar _md (tptr tuchar))
                                   (Econst_int (Int.repr 4) tint)
                                   (tptr tuchar)))))
      (Sset _xn
         (Ebinop Oadd (Etempvar _xn tuint)
          (Econst_int (Int.repr 1) tint) tuint)).

Lemma align_compatible_tarray_tuchar:
  forall n v, align_compatible (tarray tuchar n) v.
Proof.
intros.
destruct v; simpl; auto.
exists (Int.unsigned i).
symmetry. apply Z.mul_1_r.
Qed.

Lemma final_part4:
 forall (Espec: OracleKind) md c shmd hashedmsg kv,
 length hashedmsg = 8%nat ->
 writable_share shmd ->
semax
  (initialized _cNl (initialized _cNh Delta_final_if1))
  (PROP  ()
   LOCAL  (temp _md md; temp _c c)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint hashedmsg,  (Vundef, (Vundef, (list_repeat (Z.to_nat CBLOCKz) (Vint Int.zero), Vint Int.zero))))
      c);
    `(K_vector kv);
    `(memory_block shmd 32 md)))
  (Ssequence final_loop (Sreturn None))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (`(K_vector kv);
      `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd (intlist_to_Zlist hashedmsg) md)))).
Proof.
intros.
unfold final_loop.
abbreviate_semax.
rewrite memory_block_isptr. normalize. (* not clear we need this *)
assert (H': Zlength hashedmsg = 8) by (rewrite Zlength_correct, H; reflexivity).
forward_for_simple_bound 8 
   (@exp (environ -> mpred) _ _ (fun i: Z =>
   PROP  ()
   LOCAL  (temp _md (offset_val (Int.repr (i * 4)) md);
                temp _c c)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint hashedmsg, (Vundef, (Vundef, (list_repeat (Z.to_nat 64) (Vint Int.zero), Vint Int.zero))))
      c);
    `(K_vector kv);
    `(data_at shmd (tarray tuchar 32) 
         (map Vint (map Int.repr (intlist_to_Zlist (sublist 0 i hashedmsg)))
           ++ list_repeat (Z.to_nat (32 - WORD*i)) Vundef) md)
     ))).
*
 entailer!.
  change 32%Z with (sizeof cenv_cs (tarray tuchar 32)) at 1.
rewrite memory_block_size_compatible
  by (compute; auto).
normalize.
rewrite memory_block_data_at_; [ cancel | ].
repeat split; auto; try reflexivity.
apply align_compatible_tarray_tuchar.
*
  drop_LOCAL 1%nat. (* shouldn't need this *)
  assert (H1': (Z.to_nat i < 8)%nat) by Omega1.
  forward. (* ll=(c)->h[xn]; *)
  {
    entailer!.
    unfold Znth. rewrite if_false by omega.
    rewrite (nth_map' Vint _ Int.zero).
    apply I. omega.
  }
  pose (w := nth (Z.to_nat i) hashedmsg Int.zero).
  pose (bytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [w])))).
  assert (BYTES: bytes = 
     sublist (i * 4) (i * 4 + 4)
         (map Int.repr (intlist_to_Zlist hashedmsg))). {
  subst bytes.
  rewrite sublist_map.
  replace (i*4+4) with ((i+1)*WORD)%Z.
  change 4 with WORD.
  rewrite sublist_intlist_to_Zlist.
  rewrite !map_map.
  replace (fun x : Z => force_int (Vint (Int.repr x))) with Int.repr
   by (extensionality zz; reflexivity).
  f_equal.
  rewrite sublist_singleton with (d:=Int.zero) by omega.
  subst w.
  unfold Znth. rewrite if_false by omega. auto.
  change WORD with 4.
  rewrite Z.mul_add_distr_r. omega.
 } 
 unfold data_at.
 assert_PROP (field_compatible (tarray tuchar 32) [] md).
   entailer!. rename H2 into FCmd.
 erewrite (field_at_Tarray _ (tarray tuchar 32)) by (try reflexivity; computable).
     rewrite (split2_array_at _ _ _ 0 (i*4)) by omega.
     rewrite (split2_array_at _ _ _ (i*4) (i*4+4)) by omega.
change WORD with 4.
autorewrite with sublist.
replace (i * 4 + (32 - 4 * i) - i * 4 - (i * 4 + 4 - i * 4))
   with (32 - (i*4+4)) by (clear; omega).
replace (i * 4 + 4 - i * 4)
   with 4 by (clear; omega).
   normalize.
  change 64 with CBLOCKz. set (N32 := 32).
  set (N32W := N32 - i*4).
  change (Z.to_nat 4) with (Z.to_nat WORD).
 assert (COMPAT: field_compatible0 (tarray tuchar 32) [ArraySubsc (i * 4)] md).
     repeat split; auto; try omega.
     hnf in FCmd; intuition. apply align_compatible_tarray_tuchar.
  replace (N32-(i*4+4)) with (N32W - WORD)
   by (change WORD with 4; subst N32W; omega).
  forward_call (* builtin_write32_reversed *)
     (field_address0 (tarray tuchar 32) [ArraySubsc (i*4)] md, shmd, bytes).
 +
  apply prop_right.
  split.
  rewrite Znth_map with (d':=Int.zero) by omega.
  rewrite Znth_big_endian_integer by omega.
  f_equal. simpl force_val. f_equal. f_equal.
  rewrite BYTES. f_equal. change WORD with 4; omega.

  f_equal.
  destruct md; try contradiction; simpl.
  unfold field_address0. rewrite if_true by auto.
  unfold offset_val. f_equal. f_equal. f_equal.
  rewrite !nested_field_offset2_ind.
  rewrite nested_field_type2_ind.
  unfold gfield_offset, tarray.
  simpl sizeof; omega.
  apply I. split; auto. simpl. omega.
 +
assert (forall m,
  array_at shmd (tarray tuchar N32) [] (i * 4) (i * 4 + 4) m md
   |-- memory_block shmd 4
      (field_address0 (tarray tuchar 32) [ArraySubsc (i * 4)] md));
 [ | cancel].
intro.
clear Frame.
rewrite array_at_data_at.
normalize.
unfold at_offset.
set (z := nested_field_array_type (tarray tuchar N32) [] (i * 4) (i * 4 + 4)).
unfold nested_field_array_type in z; simpl in z.
subst z.
replace (i*4+4-i*4)%Z with 4%Z by (clear; omega).
eapply derives_trans; [apply data_at_data_at_ | ].
rewrite <- memory_block_data_at_.
apply derives_refl'. f_equal.
unfold field_address0.
rewrite if_true by auto. reflexivity.
clear - COMPAT FCmd H1.
hnf in COMPAT |- *.
intuition.
hnf in H6|-*. unfold offset_val. destruct md; auto.
rewrite <- (Int.repr_unsigned i0).
rewrite add_repr. rewrite Int.unsigned_repr.
subst N32. rewrite !nested_field_offset2_ind.
unfold gfield_offset, tarray.
rewrite nested_field_type2_ind. 
simpl sizeof in H6|-*.
omega.
destruct H9; auto.
auto.
rewrite !nested_field_offset2_ind.
rewrite nested_field_type2_ind. 
unfold gfield_offset, tarray.
simpl sizeof in H6|-*.
change (Int.max_unsigned) with (Int.modulus-1). 
rewrite Z.mul_1_l, Z.add_0_l.
pose proof (Int.unsigned_range i0); omega.
destruct H9; auto.
auto.
apply align_compatible_tarray_tuchar.
destruct H9; auto.
+
     split; auto.
      rewrite Zlength_correct; subst bytes.
      simpl.
      clear; omega.
 +
  unfold map at 3. (* should not be necessary *)
  forward. (* md += 4; *)
  replace (32 - WORD * (i+1)) with (N32W-WORD)
    by  (subst N32W N32; change WORD with 4; omega).
  change 64 with CBLOCKz.
  set (vbytes := map Vint bytes).
  entailer!.
    f_equal. f_equal. omega.
   unfold data_at.
   erewrite field_at_Tarray; try reflexivity; try omega.
   erewrite field_at_Tarray; try reflexivity; try omega.
     rewrite (split2_array_at _ _ _ 0 (i*4) 32) by omega.
     rewrite (split2_array_at _ _ _ (i*4) (i*4+4) 32) by omega.
  unfold N32W, N32; change WORD with 4.
  autorewrite with sublist.
   replace ((i + 1) * 4 + (32 - i * 4 - 4) - (i + 1) * 4 -
              (i * 4 + 4 - (i + 1) * 4))
        with (32-i*4-4)
  by (clear; rewrite Z.mul_add_distr_r; omega).
  rewrite !sublist_map.
  rewrite <- (sublist_intlist_to_Zlist 0 (i+1)). change WORD with 4.
  autorewrite with sublist.
  change (@sublist Z 0 (i*4)) with (@sublist Z (0*WORD) (i*WORD)).
  rewrite sublist_intlist_to_Zlist.
  rewrite <- !(sublist_map Int.repr). rewrite <- BYTES.
  fold vbytes.
  change (32 - i*4 - 4) with (N32W - WORD).
  cancel.
rewrite !array_at_data_at.
normalize.
rewrite prop_true_andp.
unfold at_offset.
unfold nested_field_array_type.
replace (i*4+4-i*4)%Z with 4%Z by (clear; omega).
simpl attr_of_type.
rewrite Z.sub_0_r.
apply derives_refl'.
f_equal.
unfold field_address0. rewrite if_true by auto.
normalize.
clear - FCmd H1.
hnf in FCmd|-*; intuition.
split; auto.
hnf. omega.
*
  change 64%Z with CBLOCKz.
  set (32 - WORD * 8) as N24.
Time  forward. (* return; *)  (* 60 seconds!!!! *)
  rewrite <- app_nil_end.
  rewrite sublist_same by omega.
  unfold data_block.
  rewrite prop_true_andp with (P:= Forall isbyteZ (intlist_to_Zlist hashedmsg))
    by apply isbyte_intlist_to_Zlist.
  autorewrite with sublist. rewrite H'.
  entailer!.
Time Qed. (* 45 sec *)


