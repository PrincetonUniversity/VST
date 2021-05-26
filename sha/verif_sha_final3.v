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
  intros.
  unfold sha_final_epilog.
  abbreviate_semax.
  Time unfold_data_at (data_at _ _ _ _).
  assert (Zlength (hash_blocks init_registers hashed) = 8)
   by (rewrite Zlength_length;[apply length_hash_blocks|]; auto).
  Time forward_call (* sha256_block_data_order (c,p); *)
    (hash_blocks init_registers hashed, lastblock, c, wsh,
      field_address t_struct_SHA256state_st [StructField _data] c,
       wsh, gv).
  {
    unfold data_block.
    autorewrite with sublist.
    rewrite H0.
    rewrite field_at_data_at with (gfs := [StructField _data]).
    Time cancel.
  }
  rewrite hash_blocks_last by auto.
  unfold data_block.
  rewrite <- H1.
  Time forward. (* c->num=0; *)
  Time forward_call (* memset (p,0,SHA_CBLOCK); *)
    (wsh, (field_address t_struct_SHA256state_st [StructField _data] c), 64, Int.zero).
  {
    rewrite Zlength_intlist_to_bytelist, H0.
    change (memory_block wsh 64) 
      with (memory_block wsh (sizeof (tarray tuchar 64))).
    entailer!.
    rewrite memory_block_data_at_ by auto.
    change (LBLOCKz*4)%Z with 64.
    cancel.
  }
 gather_SEP 
   (data_at _ _ _ _)
   (field_at _ _ [StructField _h] _ _)
   (field_at _ _ [StructField _Nl] _ _)
   (field_at _ _ [StructField _Nh] _ _)
   (field_at _ _ [StructField _num] _ _).
 replace_SEP 0 (data_at wsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers (generate_and_pad msg)),
        (Vundef,
         (Vundef,
          (repeat (Vint Int.zero) (Z.to_nat CBLOCKz), Vint Int.zero)))) c). {
   unfold_data_at (data_at _ _ _ c).
   change (Z.to_nat 64) with (Z.to_nat CBLOCKz).
   rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
   entailer!.
 }
 deadvars!.
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
       (map Vint hashedmsg, (Vundef, (Vundef, (repeat (Vint Int.zero) (Z.to_nat 64), Vint Int.zero))))
      c;
    K_vector gv;
    data_at shmd (tarray tuchar 32)
         (map Vubyte (intlist_to_bytelist (sublist 0 i hashedmsg))
           ++ repeat Vundef (Z.to_nat (32 - WORD*i))) md)
     )).
*
 entailer!.
 change 32%Z with (sizeof (tarray tuchar 32)) at 1.
 saturate_local.
 rewrite memory_block_data_at_.
 apply derives_refl.
 repeat split; auto; try reflexivity.
 apply align_compatible_tarray_tuchar.
* forward. (* ll=(c)->h[xn]; *)
  pose (w := Znth i hashedmsg).
  pose (bytes := intlist_to_bytelist [w]).
  assert (BYTES: bytes =
     sublist (i * 4) (i * 4 + 4)
         (intlist_to_bytelist hashedmsg)). {
  subst bytes.
  replace (i*4+4) with ((i+1)*WORD)%Z
    by (change WORD with 4; rewrite Z.mul_add_distr_r; clear; lia).
  change 4 with WORD.
  rewrite sublist_intlist_to_bytelist.
  f_equal.
  rewrite sublist_len_1 by lia.
  reflexivity.
  }
  unfold data_at.
  assert_PROP (field_compatible (tarray tuchar 32) [] md)
      as FCmd by entailer!.
  change WORD with 4.
  erewrite (field_at_Tarray _ (tarray tuchar 32)) by (try (apply JMeq_refl; reflexivity); try reflexivity; computable).
      rewrite (split2_array_at _ _ _ 0 (i*4)) by (autorewrite with sublist; lia).
      rewrite (split2_array_at _ _ _ (i*4) (i*4+4)) by (autorewrite with sublist; lia).
  autorewrite with sublist.
  replace (32 - 4 * i - 4)  with (32 - (i*4+4)) by (clear; lia).
  Intros.
  change 64 with CBLOCKz. set (N32 := 32).
  change (Z.to_nat 4) with (Z.to_nat WORD).
  assert (COMPAT: field_compatible0 (tarray tuchar 32) [ArraySubsc (i * 4)] md).
     repeat split; auto; try lia.
     hnf in FCmd; intuition. apply align_compatible_tarray_tuchar.
  replace (N32-(i*4+4)) with (N32 - i*4 - WORD)
   by (change WORD with 4; lia).
  forward_call (* builtin_write32_reversed *)
     (field_address0 (tarray tuchar 32) [ArraySubsc (i*4)] md, shmd, bytes).
  + apply prop_right. simpl.
    rewrite Znth_big_endian_integer by lia.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite BYTES.
    change WORD with 4. simpl.
    f_equal; f_equal; [ | do 3 f_equal]; lia.
  + sep_apply (array_at_memory_block shmd (tarray tuchar N32) nil (i*4)).
    lia. simpl. normalize. replace  (i * 4 + 4 - i * 4) with 4 by lia.
    cancel.
  + subst bytes. autorewrite with sublist. clear; lia.
  + forward. (* md += 4; *)
    replace (32 - WORD * (i+1)) with (N32 - i*4-WORD)
      by  (subst N32; change WORD with 4; lia).
    change 64 with CBLOCKz.
    set (vbytes := map Vubyte bytes).
    entailer!.
    f_equal. lia.
    unfold data_at.
    erewrite field_at_Tarray; try (apply JMeq_refl); try reflexivity; try lia.
    erewrite field_at_Tarray; try (apply JMeq_refl); try reflexivity; try lia.
    unfold N32; change WORD with 4.
    rewrite (split2_array_at _ _ _ 0 (i*4) 32) by (autorewrite with sublist; lia).
    rewrite (split2_array_at _ _ _ (i*4) (i*4+4) 32) by (autorewrite with sublist; lia).
    autorewrite with sublist.
    replace (32 - i * 4 - 4 - (4 + i * 4 - (i + 1) * 4))
          with (32-i*4-4)
     by (clear; rewrite Z.mul_add_distr_r; lia).
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
    rewrite !array_at_data_at' by (auto with field_compatible; lia).
    simpl.
    autorewrite with sublist.
    apply derives_refl'.
    f_equal.
    rewrite field_address0_offset by auto with field_compatible.
    normalize.
* change 64%Z with CBLOCKz.
  autorewrite with sublist.
  Time forward. (* return; *)  (* 60 seconds -> 4.7 seconds*)
  unfold data_block.
  rewrite Zlength_intlist_to_bytelist. rewrite H.
  cancel.
Time Qed. (*02/21/20: 1.9s (WAS: 64 sec) *)

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
intlist_to_bytelist hashed ++ dd ++ [Byte.repr 128%Z] ++ repeat Byte.zero (Z.to_nat pad) ->
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
            repeat (Vubyte Byte.zero) (Z.to_nat (CBLOCKz - 8 - Zlength dd'))
              ++ repeat Vundef (Z.to_nat 8)) c;
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
        data_block shmd (SHA_256 (intlist_to_bytelist hashed ++ dd)) md))) emp).
Proof.
  intros Espec hashed md c wsh shmd kv Hwsh H
  bitlen dd H4 H7 H3 hashed' dd' pad
  PAD H0 H1 H2 H5(* Pofs*).
  unfold sha_final_part2, sha_final_epilog; abbreviate_semax.
  pose (hibytes := intlist_to_bytelist [hi_part bitlen]).
  pose (lobytes := intlist_to_bytelist [lo_part bitlen]).
  assert_PROP (field_compatible t_struct_SHA256state_st [StructField _data] c) as FC
     by entailer!.

  Time forward. (* cNh=c->Nh; *) (*3.5*)

  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?A :: _)))) _ _ =>
    pattern A;
    match goal with |- ?F A => set (GOAL := F) end
  end.
  erewrite field_at_Tarray;
   [ | apply compute_legal_nested_field_spec'; repeat constructor; auto; lia
   | reflexivity | lia | apply JMeq_refl].
  rewrite <- app_ass.
   change (Z.to_nat 8) with (Z.to_nat 4 + Z.to_nat 4)%nat.
   rewrite repeat_app.
   rewrite (split3seg_array_at _ _ _ 0 56 60) by (autorewrite with sublist; rep_lia).
   rewrite <- !app_ass.
   assert (CBZ := CBLOCKz_eq).
   Time autorewrite with sublist. (*7*)
    clear CBZ.
  subst GOAL. cbv beta. Intros.
  Time forward_call (* (void)HOST_l2c(cNh,p); *)
     (field_address0 t_struct_SHA256state_st
                    [ArraySubsc 56; StructField _data] c,
      wsh, hibytes). (*9*)
  { apply prop_right; repeat constructor; hnf; simpl.
    rewrite (nth_big_endian_integer 0 [hi_part bitlen]) at 1 by reflexivity.
    rewrite field_address_offset.
    rewrite field_address0_offset by auto with field_compatible; reflexivity.
    red in FC; red. simpl in FC; simpl. intuition. }
  { clear; compute; congruence. }
  Time forward. (* p += 4; *) (*11 secs*)
  replace (force_val _) 
   with  (field_address t_struct_SHA256state_st [ArraySubsc 60; StructField _data] c)
    by (rewrite CBLOCKz_eq; 
         rewrite !field_address_offset by auto with field_compatible;
         make_Vptr c;  simpl; normalize).
  Time forward. (* cNl=c->Nl; *) (*12*)
  Time forward_call (* (void)HOST_l2c(cNl,p); *)
    (field_address0 t_struct_SHA256state_st
                    [ArraySubsc 60; StructField _data] c,
     wsh, lobytes). (*8.8*)
  { apply prop_right; repeat constructor; hnf; simpl.
    rewrite (nth_big_endian_integer 0 [lo_part bitlen]) at 1 by reflexivity.
    rewrite field_address0_offset by auto with field_compatible.
    rewrite field_address_offset by (pose proof CBLOCKz_eq; auto with field_compatible).
    reflexivity. }
  { clear; compute; congruence. }

  match goal with |- context [SEPx (?A :: _)] =>
   replace A with (array_at wsh t_struct_SHA256state_st [StructField _data] 60 64
                           (map Vubyte lobytes) c)
  by (clear - FC;
        rewrite array_at_data_at' by auto with field_compatible;
        reflexivity)
 end.
  gather_SEP (array_at _ _ _ 60 64 _ _) (data_at _ _ _ _) (array_at _ _ _ 0 56 _ _).
  replace_SEP 0
    (field_at wsh t_struct_SHA256state_st [StructField _data]
         (map Vubyte dd' ++
             repeat (Vubyte Byte.zero) (Z.to_nat (CBLOCKz - 8 - Zlength dd'))
                ++ ((map Vubyte hibytes) ++ (map Vubyte lobytes))) c).
  {
    assert (LENhi: Zlength hibytes = 4) by reflexivity.
    clearbody hibytes. clearbody lobytes.
    Time entailer!. (*8.7*)
  erewrite field_at_Tarray; try apply JMeq_refl; try reflexivity;
   [ | apply compute_legal_nested_field_spec'; repeat constructor; auto; lia
   | lia].
   Time autorewrite with sublist in *|-.
   rewrite (split3seg_array_at _ _ _ 0 56 60 64)
     by (autorewrite with sublist; lia).
   rewrite CBLOCKz_eq in *.
   rewrite <- !app_ass.
   Time autorewrite with sublist. (*7*)
   change (64-8) with 56.
   rewrite (array_at_data_at' _ _ _ 56 60) by auto.
   simpl. cancel.
 }
  Time forward. (* p += 4; *) (*5.1*)
  Time forward. (* p -= SHA_CBLOCK; *) (*5.9*)
  {
    go_lower; apply prop_right.
    rewrite field_address_offset by auto with field_compatible.
    make_Vptr c. auto.
  }
  deadvars!.
  replace (force_val _) with  (field_address t_struct_SHA256state_st [StructField _data] c)
    by ( rewrite !field_address_offset by auto with field_compatible;
           make_Vptr c;  simpl;  rewrite Ptrofs.sub_add_opp;
           rewrite !Ptrofs.add_assoc; normalize).
  subst hibytes; subst lobytes.
  rewrite <- !map_repeat.
  rewrite <- !map_app.
  rewrite <- intlist_to_bytelist_app.
  simpl ([_] ++ [_]).
  set (lastblock := dd' ++ _ ++ _).
  assert (H99: Zlength lastblock = CBLOCKz)
    by (unfold lastblock; autorewrite with sublist; lia).
  unfold POSTCONDITION, abbreviate.
  fold (SHA_256 (intlist_to_bytelist hashed ++ dd)).
  pose (lastblock' := bytelist_to_intlist lastblock).
  eapply semax_pre; [ | simple apply (sha_final_part3 Espec md c wsh shmd hashed' lastblock'); auto].
  * Time entailer!.
     Time unfold_data_at (data_at _ _ _ _). (*0.62*)
      unfold lastblock'.
      rewrite bytelist_to_intlist_to_bytelist
        by (rewrite H99; exists LBLOCKz; reflexivity).
      cancel.
  * apply Zlength_bytelist_to_intlist.
     assumption.
  * eapply generate_and_pad_lemma1; eassumption.
Time Qed. (*VST2.0: 3.1s *)

