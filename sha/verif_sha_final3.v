Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope logic.

Definition final_loop :=
 Sfor (Sset _xn (Econst_int (Int.repr 0) tint))
        (Ebinop Olt (Etempvar _xn tuint)
          (Ebinop Odiv (Econst_int (Int.repr 32) tint)
            (Econst_int (Int.repr 4) tint) tint) tint)
        (Ssequence
          (Sset _ll (Ederef
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

Definition sha_final_epilog :=
              (Ssequence
                          (Scall None
                            (Evar _sha256_block_data_order (Tfunction
                                 (Tcons(tptr t_struct_SHA256state_st)
                                   (Tcons (tptr tvoid) Tnil))
                                 tvoid cc_default))
                            ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                             (Etempvar _p (tptr tuchar)) :: nil))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr t_struct_SHA256state_st))
                                  t_struct_SHA256state_st) _num tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Scall None
                                (Evar _memset (Tfunction
                                                (Tcons (tptr tvoid)
                                                  (Tcons tint
                                                    (Tcons tuint Tnil)))
                                                (tptr tvoid) cc_default))
                                ((Etempvar _p (tptr tuchar)) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Ebinop Omul (Econst_int (Int.repr 16) tint)
                                   (Econst_int (Int.repr 4) tint) tint) ::
                                 nil))
           (Ssequence final_loop (Sreturn None))))).

Definition sha_final_part2 :=
  (Ssequence
     (Sset _cNh
        (Efield
           (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _Nh tuint))
     (Ssequence
        (Ssequence
           (Scall None
              (Evar ___builtin_write32_reversed
                 (Tfunction (Tcons (tptr tuint) (Tcons tuint Tnil)) tvoid cc_default))
              [Ecast (Etempvar _p (tptr tuchar)) (tptr tuint);
              Etempvar _cNh tuint])
           (Sset _p
              (Ebinop Oadd (Etempvar _p (tptr tuchar))
                 (Econst_int (Int.repr 4) tint) (tptr tuchar))))
        (Ssequence
           (Sset _cNl
              (Efield
                 (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _Nl tuint))
           (Ssequence
              (Ssequence
                 (Scall None
                    (Evar ___builtin_write32_reversed
                       (Tfunction (Tcons (tptr tuint) (Tcons tuint Tnil))
                          tvoid cc_default))
                    [Ecast (Etempvar _p (tptr tuchar)) (tptr tuint);
                    Etempvar _cNl tuint])
                 (Sset _p
                    (Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Econst_int (Int.repr 4) tint) (tptr tuchar))))
              (Ssequence
                 (Sset _p
                    (Ebinop Osub (Etempvar _p (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 16) tint)
                          (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
                 sha_final_epilog))))).

Lemma align_compatible_tarray_tuchar:
  forall n v, align_compatible (tarray tuchar n) v.
Proof.
intros.
destruct v; simpl; auto.
constructor; intros.
eapply align_compatible_rec_by_value; [reflexivity |].
apply Z.divide_1_l.
Qed.

Lemma sha_final_part3:
forall (Espec : OracleKind) (md c : val) (wsh shmd : share)
  (hashed lastblock: list int) msg gv
 (Hwsh: writable_share wsh)
 (Hshmd: writable_share shmd),
 (LBLOCKz | Zlength hashed) ->
 Zlength lastblock = LBLOCKz ->
 generate_and_pad msg = hashed++lastblock ->
semax
     (func_tycontext f_SHA256_Final Vprog Gtot nil)
  (PROP  ()
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
           temp _md md; temp _c c;
           gvars gv)
   SEP
   (data_at wsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers hashed),
        (Vundef, (Vundef, (map Vubyte (intlist_to_bytelist lastblock), Vundef)))) c;
    K_vector gv;
    memory_block shmd 32 md))
  sha_final_epilog
  (frame_ret_assert
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector gv;
        data_at_ wsh t_struct_SHA256state_st c;
        data_block shmd (SHA_256 msg) md))) emp).
Proof.
  intros. Intros.
  unfold sha_final_epilog.
  abbreviate_semax.
  Time unfold_data_at 1%nat.
  assert (Zlength (hash_blocks init_registers hashed) = 8)
   by (rewrite Zlength_length;[apply length_hash_blocks|]; auto).
  Time forward_call (* sha256_block_data_order (c,p); *)
    (hash_blocks init_registers hashed, lastblock, c, wsh,
      field_address t_struct_SHA256state_st [StructField _data] c,
       wsh, gv).
  {
    unfold data_block. simpl.
    Time entailer!. autorewrite with sublist.
    rewrite H0.
    rewrite field_at_data_at with (gfs := [StructField _data]).
    Time cancel.
  }
  rewrite hash_blocks_last by auto.
  unfold data_block.
  simpl.
  rewrite <- H1.
  Time forward. (* c->num=0; *)
  Time forward_call (* memset (p,0,SHA_CBLOCK); *)
    (wsh, (field_address t_struct_SHA256state_st [StructField _data] c), 64%Z, Int.zero).
  {
    replace (Zlength (intlist_to_bytelist lastblock)) with 64
        by (rewrite Zlength_intlist_to_bytelist, H0; reflexivity).
    change (memory_block wsh 64) with (memory_block wsh (sizeof (tarray tuchar 64))).
    entailer!.
    rewrite memory_block_data_at_ by auto.
    cancel.
  }
 gather_SEP 0 1 3 4 5.
 replace_SEP 0 (data_at wsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers (generate_and_pad msg)),
        (Vundef,
         (Vundef,
          (list_repeat (Z.to_nat CBLOCKz) (Vint Int.zero), Vint Int.zero)))) c).
 unfold_data_at 2%nat.
 change (Z.to_nat 64) with (Z.to_nat CBLOCKz).
 rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
 entailer!.
 drop_LOCAL 0%nat. drop_LOCAL 2%nat.
 assert (H': Zlength (hash_blocks init_registers (generate_and_pad msg)) = 8). {
   rewrite Zlength_correct, length_hash_blocks; auto.
    rewrite H1.
    apply divide_length_app; auto.
    rewrite H0. apply Z.divide_refl.
  }
 subst POSTCONDITION; unfold abbreviate.
 unfold SHA_256.
 forget (hash_blocks init_registers (generate_and_pad msg)) as hashedmsg.
 clear - Hwsh Hshmd H'; rename H' into H. rename Hshmd into H0.
 unfold final_loop.

 forward_for_simple_bound 8
   (@exp (environ -> mpred) _ _ (fun i: Z =>
   PROP  ()
   LOCAL  (temp _md (offset_val (i * 4) md);
                temp _c c)
   SEP
   (data_at wsh t_struct_SHA256state_st
       (map Vint hashedmsg, (Vundef, (Vundef, (list_repeat (Z.to_nat 64) (Vint Int.zero), Vint Int.zero))))
      c;
    K_vector gv;
    data_at shmd (tarray tuchar 32)
         (map Vubyte (intlist_to_bytelist (sublist 0 i hashedmsg))
           ++ list_repeat (Z.to_nat (32 - WORD*i)) Vundef) md)
     )).
*
 entailer!.
 change 32%Z with (sizeof (tarray tuchar 32)) at 1.
 rewrite memory_block_size_compatible by (compute; auto).
 (* memory_block_size_compatible should perhaps(?) be
     woven into memory_block_local_facts *)
 Intros.
 rewrite memory_block_data_at_.
 apply derives_refl.
 repeat split; auto; try reflexivity.
 apply align_compatible_tarray_tuchar.
*
  forward. (* ll=(c)->h[xn]; *)
  pose (w := Znth i hashedmsg).
  pose (bytes := intlist_to_bytelist [w]).
  assert (BYTES: bytes =
     sublist (i * 4) (i * 4 + 4)
         (intlist_to_bytelist hashedmsg)). {
  subst bytes.
  replace (i*4+4) with ((i+1)*WORD)%Z
    by (change WORD with 4; rewrite Z.mul_add_distr_r; clear; omega).
  change 4 with WORD.
  rewrite sublist_intlist_to_bytelist.
  f_equal.
  rewrite sublist_len_1 by omega.
  reflexivity.
 }
 unfold data_at.
 assert_PROP (field_compatible (tarray tuchar 32) [] md)
     as FCmd by entailer!.
 change WORD with 4.
 erewrite (field_at_Tarray _ (tarray tuchar 32)) by (try (apply JMeq_refl; reflexivity); try reflexivity; computable).
     rewrite (split2_array_at _ _ _ 0 (i*4)) by (autorewrite with sublist; omega).
     rewrite (split2_array_at _ _ _ (i*4) (i*4+4)) by (autorewrite with sublist; omega).
 autorewrite with sublist.
 replace (32 - 4 * i - 4)  with (32 - (i*4+4)) by (clear; omega).
 Intros.
  change 64 with CBLOCKz. set (N32 := 32).
  change (Z.to_nat 4) with (Z.to_nat WORD).
 assert (COMPAT: field_compatible0 (tarray tuchar 32) [ArraySubsc (i * 4)] md).
     repeat split; auto; try omega.
     hnf in FCmd; intuition. apply align_compatible_tarray_tuchar.
  replace (N32-(i*4+4)) with (N32 - i*4 - WORD)
   by (change WORD with 4; omega).
  forward_call (* builtin_write32_reversed *)
     (field_address0 (tarray tuchar 32) [ArraySubsc (i*4)] md, shmd, bytes).
 +
  apply prop_right.
  split.
  rewrite Znth_big_endian_integer by omega.
  f_equal. simpl. f_equal. f_equal.
  rewrite BYTES. f_equal.
  change WORD with 4; clear; omega.
  simpl; f_equal.
  destruct md; try contradiction; simpl.
  rewrite field_address0_offset by auto with field_compatible.
  simpl. normalize.
 +
assert (forall m,
  array_at shmd (tarray tuchar N32) [] (i * 4) (i * 4 + 4) m md
   |-- memory_block shmd 4
      (field_address0 (tarray tuchar 32) [ArraySubsc (i * 4)] md));
 [ | cancel].
intro.
clear Frame.
rewrite array_at_data_at by omega.
simpl.
Intros.
unfold at_offset.
autorewrite with sublist.
eapply derives_trans; [apply data_at_data_at_ | ].
rewrite <- memory_block_data_at_.
1:{
  rewrite field_address0_offset by auto with field_compatible.
  apply derives_refl.
} 
clear - COMPAT FCmd H1.
hnf in COMPAT |- *.
(* TODO: simplify this proof. *)
intuition.
- hnf in H6|-*. unfold offset_val. destruct md; auto.
  rewrite <- (Ptrofs.repr_unsigned i0).
  rewrite ptrofs_add_repr.
  simpl in H6|-*.
  simpl in H2; inv_int i0.
  rewrite Ptrofs.unsigned_repr; try omega.
  rewrite Z.mul_1_l.
  change (Ptrofs.max_unsigned) with (Ptrofs.modulus-1).
  omega.
- apply align_compatible_tarray_tuchar.
- destruct H6; auto.
+
     split; auto.
      rewrite Zlength_correct; subst bytes.
      simpl.
      clear; omega.
 +
  forward. (* md += 4; *)
  replace (32 - WORD * (i+1)) with (N32 - i*4-WORD)
    by  (subst N32; change WORD with 4; omega).
  change 64 with CBLOCKz.
  set (vbytes := map Vubyte bytes).
  simpl (temp _md _).
  entailer!.
  f_equal. omega.
   unfold data_at.
   erewrite field_at_Tarray; try (apply JMeq_refl); try reflexivity; try omega.
   erewrite field_at_Tarray; try (apply JMeq_refl); try reflexivity; try omega.
  unfold N32; change WORD with 4.
     rewrite (split2_array_at _ _ _ 0 (i*4) 32) by (autorewrite with sublist; omega).
     rewrite (split2_array_at _ _ _ (i*4) (i*4+4) 32) by (autorewrite with sublist; omega).
  autorewrite with sublist.
   replace (32 - i * 4 - 4 - (4 + i * 4 - (i + 1) * 4))
        with (32-i*4-4)
  by (clear; rewrite Z.mul_add_distr_r; omega).
  rewrite !sublist_map.
  rewrite <- (sublist_intlist_to_bytelist 0 (i+1)). change WORD with 4.
  autorewrite with sublist.
  change (@sublist byte 0 (i*4)) with (@sublist byte (0*WORD) (i*WORD)).
  rewrite sublist_intlist_to_bytelist.
  rewrite (Z.add_comm 4 (i*4)).
  rewrite <- BYTES.
  fold vbytes.
  change (32 - i*4 - 4) with (N32 - i*4 - WORD).
  cancel.
rewrite !array_at_data_at' by (auto with field_compatible; omega).
simpl.
autorewrite with sublist.
apply derives_refl'.
f_equal.
rewrite field_address0_offset by auto with field_compatible.
normalize.
*
  change 64%Z with CBLOCKz.
  autorewrite with sublist.
Time  forward. (* return; *)  (* 60 seconds -> 4.7 seconds*)
  unfold data_block.
   rewrite Zlength_intlist_to_bytelist. rewrite H.
  cancel.
Time Qed. (* 64 sec *)

Lemma final_part2:
forall (Espec : OracleKind) (hashed : list int) (md c : val) (wsh shmd : share) gv
(Hwsh: writable_share wsh),
writable_share shmd ->
forall bitlen (dd : list byte),
(LBLOCKz | Zlength hashed) ->
((Zlength hashed * 4 + Zlength dd)*8)%Z = bitlen ->
(Zlength dd < CBLOCKz) ->
forall (hashed': list int) (dd' : list byte) (pad : Z),
 (pad=0%Z \/ dd'=nil) ->
(Zlength dd' + 8 <= CBLOCKz)%Z ->
(0 <= pad < 8)%Z ->
(LBLOCKz | Zlength hashed') ->
intlist_to_bytelist hashed' ++ dd' =
intlist_to_bytelist hashed ++ dd ++ [Byte.repr 128%Z] ++ list_repeat (Z.to_nat pad) Byte.zero ->
semax
     (func_tycontext f_SHA256_Final Vprog Gtot nil)
  (PROP  ()
      LOCAL
      (temp _p
         (field_address t_struct_SHA256state_st [ArraySubsc (CBLOCKz - 8); StructField _data] c);
      temp _n (Vint (Int.repr (Zlength dd')));
      temp _md md; temp _c c; gvars gv)
      SEP
      (field_at wsh t_struct_SHA256state_st [StructField _data]
           (map Vubyte dd' ++
            list_repeat (Z.to_nat (CBLOCKz - 8 - Zlength dd')) (Vubyte Byte.zero)
              ++ list_repeat (Z.to_nat 8) Vundef) c;
      field_at wsh t_struct_SHA256state_st [StructField _num] Vundef c;
      field_at wsh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part bitlen)) c;
      field_at wsh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part bitlen)) c;
      field_at wsh t_struct_SHA256state_st [StructField _h]
          (map Vint (hash_blocks init_registers hashed')) c;
      K_vector gv;
      memory_block shmd 32 md))
  sha_final_part2
  (frame_ret_assert
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector gv;
        data_at_ wsh t_struct_SHA256state_st c;
        data_block shmd
          (intlist_to_bytelist
             (hash_blocks init_registers
                (generate_and_pad
                   (intlist_to_bytelist hashed ++ dd))))
          md))) emp).
Proof.
  intros Espec hashed md c wsh shmd kv Hwsh H
  bitlen dd H4 H7 H3 hashed' dd' pad
  PAD H0 H1 H2 H5(* Pofs*).
  unfold sha_final_part2, sha_final_epilog; abbreviate_semax.
  pose (hibytes := intlist_to_bytelist [hi_part bitlen]).
  pose (lobytes := intlist_to_bytelist [lo_part bitlen]).
  assert_PROP (field_compatible t_struct_SHA256state_st [StructField _data] c).
    Time entailer!. (*2.3*) rename H6 into FC.

  Time forward. (* cNh=c->Nh; *) (*3.5*)

  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?A :: _)))) _ _ =>
    pattern A;
    match goal with |- ?F A => set (GOAL := F) end
  end.
  erewrite field_at_Tarray; try apply JMeq_refl; try reflexivity;
   [ | apply compute_legal_nested_field_spec'; repeat constructor; auto; omega
   | omega].
  rewrite <- app_ass.
   change (Z.to_nat 8) with (Z.to_nat 4 + Z.to_nat 4)%nat.
   rewrite <- list_repeat_app.
   rewrite (split3seg_array_at _ _ _ 0 56 60) by (autorewrite with sublist; rep_omega).
   assert (CBZ := CBLOCKz_eq).
   Time autorewrite with sublist. (*11.5*)
   clear CBZ; subst GOAL. cbv beta.
   Intros.  (* to flatten the SEP *)
  Time forward_call (* (void)HOST_l2c(cNh,p); *)
     (field_address0 t_struct_SHA256state_st
                    [ArraySubsc 56; StructField _data] c,
      wsh, hibytes). (*9*)
  apply prop_right; repeat constructor; hnf; simpl.
  rewrite (nth_big_endian_integer 0 [hi_part bitlen]) at 1; reflexivity.

  rewrite field_address_offset by auto.
  rewrite field_address0_offset by auto with field_compatible.
  destruct c; try contradiction; simpl; auto.
  split; auto.
  clear; compute; congruence.
  Time forward. (* p += 4; *) (*11 secs*)
  simpl (temp _p _).
  Time forward. (* cNl=c->Nl; *) (*12*)
  Time forward_call (* (void)HOST_l2c(cNl,p); *)
    (field_address0 t_struct_SHA256state_st
                    [ArraySubsc 60; StructField _data] c,
     wsh, lobytes). (*8.8*)
  apply prop_right; repeat constructor; hnf; simpl.
  rewrite (nth_big_endian_integer 0 [lo_part bitlen]) at 1; reflexivity.

  rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address_offset by (pose proof CBLOCKz_eq; auto with field_compatible).
  make_Vptr c. simpl. unfold Ptrofs.of_ints. normalize.
  split; auto.  clear; compute; congruence.

  match goal with |- context [SEPx (?A :: _)] =>
   replace A with (array_at wsh t_struct_SHA256state_st [StructField _data] 60 64
                           (map Vubyte lobytes) c)
  by (clear - FC;
        rewrite array_at_data_at' by auto with field_compatible;
        reflexivity)
 end.
  gather_SEP 0 1 2.
  replace_SEP 0
    (field_at wsh t_struct_SHA256state_st [StructField _data]
         (map Vubyte dd' ++
             list_repeat (Z.to_nat (CBLOCKz - 8 - Zlength dd'))
               (Vubyte Byte.zero) ++ ((map Vubyte hibytes) ++ (map Vubyte lobytes))) c).
  {
    assert (LENhi: Zlength hibytes = 4) by reflexivity.
    clearbody hibytes. clearbody lobytes.
    Time entailer!. (*8.7*)
  erewrite field_at_Tarray; try apply JMeq_refl; try reflexivity;
   [ | apply compute_legal_nested_field_spec'; repeat constructor; auto; omega
   | omega].
   rewrite <- app_ass.
   Time autorewrite with sublist in *|-.
   rewrite (split3seg_array_at _ _ _ 0 56 60 64)
     by (autorewrite with sublist; Omega1).
   rewrite CBLOCKz_eq in *.
   pose proof (Zlength_nonneg dd').
   Time autorewrite with sublist. (*7*)
   cancel.
   rewrite array_at_data_at'; auto.  apply derives_refl.
 }
  Time forward. (* p += 4; *) (*5.1*) {
   go_lower. apply prop_right.
    pose proof CBLOCKz_eq.
    rewrite field_address_offset by auto with field_compatible.
    normalize.
  }
  Time forward. (* p -= SHA_CBLOCK; *) (*5.9*)
  {
   go_lower. apply prop_right.
    pose proof CBLOCKz_eq.
    rewrite field_address_offset by auto with field_compatible.
    make_Vptr c; simpl in *; auto.
  }
  drop_LOCAL 1%nat. (* drop cNl *)
  drop_LOCAL 1%nat. (* drop cNh *)
  match goal with
  | |- context [temp _p ?X] =>
     replace X with  (field_address t_struct_SHA256state_st [StructField _data] c)
      by (pose proof CBLOCKz_eq;
            rewrite !field_address_offset by auto with field_compatible;
           make_Vptr c;  simpl;  rewrite Ptrofs.sub_add_opp;
           rewrite !Ptrofs.add_assoc; normalize)
   end.
  subst hibytes; subst lobytes.
(*  change (Vint Int.zero) with (Vint (Int.repr 0)). *)
  rewrite <- !map_list_repeat.
  rewrite <- !map_app.
  rewrite <- intlist_to_bytelist_app.
  simpl ([hi_part bitlen] ++ [lo_part bitlen]).
  set (lastblock :=
          dd' ++ list_repeat (Z.to_nat (CBLOCKz - 8 - Zlength dd')) Byte.zero
              ++ intlist_to_bytelist [hi_part bitlen; lo_part bitlen]).
  assert (H99: Zlength lastblock = CBLOCKz)
    by (unfold lastblock; autorewrite with sublist; omega).
  unfold POSTCONDITION, abbreviate.
  fold (SHA_256 (intlist_to_bytelist hashed ++ dd)).
  pose (lastblock' := bytelist_to_intlist lastblock).
  eapply semax_pre; [ | simple apply (sha_final_part3 Espec md c wsh shmd hashed' lastblock'); auto].
  * Time entailer!.
     Time unfold_data_at 1%nat. (*0.62*)
      unfold lastblock'.
      rewrite bytelist_to_intlist_to_bytelist; auto.
      2:    rewrite H99; exists LBLOCKz; reflexivity.
      cancel.
  * apply Zlength_bytelist_to_intlist.
     assumption.
  * eapply generate_and_pad_lemma1; eassumption.
Time Qed. (*VST2.0: 3.1s *)

