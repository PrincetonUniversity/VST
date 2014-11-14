Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_final2.
Local Open Scope logic.

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

(*
Lemma sha_final_part3:
forall (Espec : OracleKind) (md c : val) (shmd : share)
  (hashed lastblock: list int) msg kv
 (Hshmd: writable_share shmd),
 (LBLOCKz | Zlength hashed) ->
 Zlength lastblock = LBLOCKz ->
 generate_and_pad msg = hashed++lastblock ->
semax
  (initialized _cNl (initialized _cNh Delta_final_if1))
  (PROP  (Forall isbyteZ (intlist_to_Zlist lastblock))
   LOCAL  (temp _p (offset_val (Int.repr 40) c);
           temp _md md; temp _c c;
           var _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(data_at Tsh t_struct_SHA256state_st
       (map Vint (hash_blocks init_registers hashed),
        (Vundef, (Vundef, (map Vint (map Int.repr (intlist_to_Zlist lastblock)), Vundef)))) c);
    `(K_vector kv);
    `(memory_block shmd (Int.repr 32) md)))
  sha_final_epilog
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (`(K_vector kv);
      `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd (SHA_256 msg) md)))).
Proof.
intros.
unfold sha_final_epilog.
abbreviate_semax.

  unfold data_block.
  unfold_data_at 1%nat.
  rewrite field_at_data_at.
  rewrite at_offset

forward_call (* sha256_block_data_order (c,p); *)
  (hashed, lastblock, c,
    offset_val (Int.repr (nested_field_offset2 t_struct_SHA256state_st [StructField _data])) c,
      Tsh, kv).
{
  entailer!.
}
 after_call.
unfold data_block.
simpl. rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
rewrite <- H1.
forward. (* c->num=0; *)
forward_call (* memset (p,0,SHA_CBLOCK); *) 
  (Tsh, (offset_val (Int.repr 40) c), 64%Z, Int.zero).
entailer!. 
 rewrite (memory_block_array_tuchar _ 64%Z) by Omega1.
 rewrite Zlength_intlist_to_Zlist, H0. change (4*LBLOCKz) with 64.
 cancel.
after_call.
replace Delta with
   (initialized _cNl (initialized _cNh Delta_final_if1))
 by (simplify_Delta; reflexivity).
eapply semax_pre; [ | apply final_part4; auto].
entailer!.
apply length_hash_blocks; auto.
rewrite H1.
apply divide_length_app; auto.
exists 1; apply H0.
Qed.
*)

Lemma nth_list_repeat':
  forall A i n (a d: A),
   (i < n)%nat -> nth i (list_repeat n a) d = a.
Proof.
 induction i; destruct n; simpl; intros; auto; try omega.
 apply IHi; omega.
Qed.

(*
Lemma final_part5:
forall (hashed: list int) (dd:list Z) (hashed': list int) (dd' : list Z) (pad : Z) (hi' lo' : list Z)
  (hi lo : int) c_,
 (LBLOCKz | Zlength hashed) ->
(Zlength dd < CBLOCKz) ->
(length dd' + 8 <= CBLOCK)%nat ->
(0 <= pad < 8)%Z ->
(LBLOCKz | Zlength hashed') ->
intlist_to_Zlist hashed' ++ dd' =
intlist_to_Zlist hashed ++ dd ++ [128%Z] ++ list_repeat (Z.to_nat pad) 0 ->
length hi' = 4%nat ->
length lo' = 4%nat ->
isptr c_ ->
hi' = intlist_to_Zlist [hi] /\ lo' = intlist_to_Zlist [lo] ->
offset_in_range 64 (offset_val (Int.repr 40) c_) ->
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr lo'))) 0 4
  (offset_val (Int.repr 100) c_) *
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr hi'))) 0 4
  (offset_val (Int.repr 96) c_) *
array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
  (Z.of_nat CBLOCK - 8 - Zlength dd')
  (offset_val (Int.repr (Zlength dd' + 40)) c_) *
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd')
  (offset_val (Int.repr 40) c_)
|-- array_at tuchar Tsh
      (ZnthV tuchar
         (map Vint
            (map Int.repr dd' ++
             list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd')) Int.zero ++
             map Int.repr (hi' ++ lo')))) 0 64 (offset_val (Int.repr 40) c_).
Proof.
intros until c_.
intros H4 H3 H0 H1 H2 H5 Lhi Llo Pc_ Hhilo Hofs.
 rewrite split_offset_array_at with (lo := 60) (hi := 64); [| omega | simpl; omega | reflexivity].
 rewrite split_offset_array_at with (lo := 56) (hi := 60); [| omega | simpl; omega | reflexivity].
 rewrite split_offset_array_at with (lo := Zlength dd') (hi := 56);
  [| change CBLOCK with 64%nat in H0; rewrite Zlength_correct in *; omega | simpl; omega | reflexivity].

 replace (offset_val (Int.repr 100) c_) with
            (offset_val (Int.repr (sizeof tuchar * 60)) (offset_val (Int.repr 40) c_))
  by (rewrite offset_offset_val; destruct c_; reflexivity).
 replace (offset_val (Int.repr 96) c_) with
            (offset_val (Int.repr (sizeof tuchar * 56)) (offset_val (Int.repr 40) c_))
  by (rewrite offset_offset_val; destruct c_; reflexivity).
 replace (offset_val (Int.repr (Zlength dd' + 40)) c_) with
            (offset_val (Int.repr (sizeof tuchar * Zlength dd')) (offset_val (Int.repr 40) c_))
  by (change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l; rewrite offset_offset_val; rewrite Int.add_commut, add_repr; reflexivity).
 forget (offset_val (Int.repr 40) c_) as cc.
 apply derives_trans with
  (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd') cc *
   array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
     (Z.of_nat CBLOCK - 8 - Zlength dd')
     (offset_val (Int.repr (sizeof tuchar * Zlength dd')) cc) *
   array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr hi'))) 0 4
     (offset_val (Int.repr (sizeof tuchar * 56)) cc) *
  array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr lo'))) 0 4
     (offset_val (Int.repr (sizeof tuchar * 60)) cc));
  [solve [cancel] | ].
  change (64 - 60) with 4.
  change (60 - 56) with 4.
 assert (Zlength dd' >= 0)%Z by (rewrite Zlength_correct; omega).
 assert (Zlength dd' = Z.of_nat (length (map Vint (map Int.repr dd')))).
 rewrite Zlength_correct; repeat rewrite map_length; reflexivity.
 assert (Z.of_nat CBLOCK - 8 - Z.of_nat (length dd') >= 0)%Z.
 clear - H0. apply Nat2Z.inj_le in H0. rewrite Nat2Z.inj_add in H0.
  change (Z.of_nat 8) with 8 in H0. omega.
 assert (Hofs0: offset_in_range (sizeof tuchar * 0) cc).
   unfold offset_in_range; destruct cc; auto.
   pose proof Int.unsigned_range i.
   omega.
 assert (Hofs1: offset_in_range (sizeof tuchar * 56) cc) by
   (apply offset_in_range_mid with (lo := 0) (hi := 64); auto; omega).
 assert (Hofs2: offset_in_range (sizeof tuchar * 60) cc) by
   (apply offset_in_range_mid with (lo := 0) (hi := 64); auto; omega).
 normalize.
 repeat rewrite sepcon_assoc;
 repeat apply sepcon_derives; apply derives_refl';
 apply equal_f; try apply array_at_ext; intros;
 unfold ZnthV; repeat rewrite if_false by omega.
+ repeat rewrite map_app.
   rewrite app_nth1; [reflexivity | ].
 apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega; omega.
+ repeat rewrite map_app.
   rewrite map_list_repeat.
 change (Z.of_nat CBLOCK - 8) with 56.
   rewrite app_nth2. rewrite app_nth1.
 rewrite nth_list_repeat'; auto.
 repeat rewrite map_length.
 rewrite <- (Nat2Z.id (length dd')).
 rewrite <- Zlength_correct.
 rewrite <- Z2Nat.inj_sub by omega.
 apply Z2Nat.inj_lt; omega.
 repeat rewrite map_length.
 rewrite <- (Nat2Z.id (length dd')).
 rewrite <- Zlength_correct.
 rewrite <- Z2Nat.inj_sub by omega.
  rewrite length_list_repeat.
 apply Z2Nat.inj_lt; omega.
  repeat rewrite map_length.
 rewrite <- (Nat2Z.id (length dd')).
 rewrite <- Zlength_correct.
 apply Z2Nat.inj_le; omega.
+ repeat rewrite map_app.
   rewrite <- app_ass.
   rewrite app_nth2. rewrite app_nth1.
   f_equal.    rewrite app_length.  
   repeat rewrite map_length; rewrite map_length in H6.
   rewrite length_list_repeat.
   rewrite H6. Omega1.
  rewrite app_length; rewrite (map_list_repeat); rewrite length_list_repeat.
  rewrite H6. repeat rewrite map_length.
  rewrite Lhi.
    change (Z.of_nat CBLOCK - 8)%Z with 56%Z. 
  apply Nat2Z.inj_lt; try omega.
  rewrite Nat2Z.inj_sub; try Omega1.
  rewrite H6; repeat rewrite app_length; repeat rewrite map_length;
   rewrite length_list_repeat.
  Omega1.
+
assert (length
  (map Vint
     ((map Int.repr dd' ++ list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd')) Int.zero) ++
      map Int.repr hi')) = 60%nat).
  rewrite map_length.
 repeat rewrite app_length.
 repeat rewrite map_length.
 rewrite length_list_repeat.
 change (Z.of_nat CBLOCK - 8) with 56.
 rewrite Lhi, Zlength_correct.
 rewrite Z2Nat.inj_sub by omega.
 rewrite Nat2Z.id.
 change (Z.to_nat 56) with 56%nat.
 clear- H0; change CBLOCK with 64%nat in H0; omega.
  rewrite (map_app Int.repr).
  repeat rewrite <- app_ass.
  rewrite map_app.
  rewrite app_nth2.
 rewrite H9.
  
  rewrite Z2Nat.inj_add by omega; auto.
  replace (Z.to_nat i + Z.to_nat 60 - 60)%nat with (Z.to_nat i) by (simpl; omega).
 reflexivity.
 rewrite H9.
 clear - H8. change 60%nat with (Z.to_nat 60).
 apply Z2Nat.inj_le; omega.
Qed.
*)

Lemma NPeano_divide_add:
  forall a b c, NPeano.divide a b -> NPeano.divide a c -> NPeano.divide a (b+c).
Proof. intros.
 destruct H,H0. exists (x+x0)%nat. rewrite mult_plus_distr_r. subst; auto.
Qed.

Lemma final_part2:
forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share) kv,
writable_share shmd ->
name _md ->
name _c ->
name _p ->
name _n ->
name _cNl ->
name _cNh ->
forall (hi lo : int) (dd : list Z),
(LBLOCKz | Zlength hashed) ->
((Zlength hashed * 4 + Zlength dd)*8)%Z = hilo hi lo ->
(Zlength dd < CBLOCKz) ->
 (Forall isbyteZ dd) ->
forall (hashed': list int) (dd' : list Z) (pad : Z),
 (Forall isbyteZ dd') ->
 (pad=0%Z \/ dd'=nil) ->
(length dd' + 8 <= CBLOCK)%nat ->
(0 <= pad < 8)%Z ->
(LBLOCKz | Zlength hashed') ->
intlist_to_Zlist hashed' ++ dd' =
intlist_to_Zlist hashed ++ dd ++ [128%Z] ++ list_repeat (Z.to_nat pad) 0 ->
offset_in_range 64 (offset_val (Int.repr 40) c) ->
semax Delta_final_if1
  (PROP  ()
      LOCAL 
      (`(eq
           (offset_val
              (Int.repr
                 (nested_field_offset2 t_struct_SHA256state_st
                    [ArraySubsc (Z.of_nat CBLOCK - 8); StructField _data])) c))
         (eval_id _p); temp _n (Vint (Int.repr (Zlength dd'))); 
      temp _md md; temp _c c; var _K256 (tarray tuint CBLOCKz) kv)
      SEP 
      (`(field_at Tsh t_struct_SHA256state_st [StructField _data]
           (map Vint (map Int.repr dd') ++
            list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
              (Vint Int.zero) ++ []) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _num] Vundef c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _Nh] (Vint hi) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _Nl] (Vint lo) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _h]
          (map Vint (hash_blocks init_registers hashed')) c);
      `K_vector (eval_var _K256 (tarray tuint CBLOCKz));
      `(memory_block shmd (Int.repr 32) md)))
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
                 (Ssequence
                    (Scall None
                       (Evar _sha256_block_data_order
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st)
                                (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
                       [Etempvar _c (tptr t_struct_SHA256state_st);
                       Etempvar _p (tptr tuchar)])
                    (Ssequence
                       (Sassign
                          (Efield
                             (Ederef
                                (Etempvar _c (tptr t_struct_SHA256state_st))
                                t_struct_SHA256state_st) _num tuint)
                          (Econst_int (Int.repr 0) tint))
                       (Ssequence
                             (Scall None
                                (Evar _memset
                                   (Tfunction
                                      (Tcons (tptr tvoid)
                                         (Tcons tint (Tcons tuint Tnil)))
                                      (tptr tvoid) cc_default))
                                [Etempvar _p (tptr tuchar);
                                Econst_int (Int.repr 0) tint;
                                Ebinop Omul (Econst_int (Int.repr 16) tint)
                                  (Econst_int (Int.repr 4) tint) tint])
                          (Ssequence
                             final_loop
                             (Sreturn None))))))))))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (`(K_vector kv);
      `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd
          (intlist_to_Zlist
             (hash_blocks init_registers
                (generate_and_pad
                   (intlist_to_Zlist hashed ++ dd))))
          md)))).
Proof.
  intros Espec hashed md c shmd kv H md_ c_ p n cNl cNh
  hi lo dd H4 H7 H3 DDbytes hashed' dd' pad
  DDbytes' PAD H0 H1 H2 H5 Pofs.
  abbreviate_semax.
  pose (hibytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [hi])))).
  pose (lobytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [lo])))).
  forward. (* cNh=c->Nh; *)
  
  replace (field_at Tsh t_struct_SHA256state_st [StructField _data]
            (map Vint (map Int.repr dd') ++
             list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
               (Vint Int.zero) ++ []) c) with
    (field_at Tsh t_struct_SHA256state_st [StructField _data]
            ((map Vint (map Int.repr dd') ++
             list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
               (Vint Int.zero)) ++ (list_repeat 4%nat Vundef) ++ (list_repeat 4%nat Vundef)) c).
  Focus 2. {
    erewrite field_at_data_equal; [reflexivity | reflexivity |].
    rewrite !app_nil_r.
    apply data_equal_sym.
    rewrite app_assoc.
    eapply data_equal_trans;
    apply data_equal_list_repeat_default;
    reflexivity.
  } Unfocus.
  erewrite array_seg_reroot_lemma with (lo := 56) (hi := 60%Z);
    [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | | reflexivity].
  Focus 2. {
    rewrite Zlength_app, !Zlength_map.
    rewrite !Zlength_correct.
    rewrite length_list_repeat.
    rewrite Z2Nat.id by omega.
    change (Z.of_nat CBLOCK) with 64.
    omega.
  } Unfocus.
  Focus 2. {
    rewrite Zlength_correct, length_list_repeat.
    reflexivity.
  } Unfocus.
  normalize.

  forward_call (* (void)HOST_l2c(cNh,p); *)
     (offset_val
              (Int.repr
                 (nested_field_offset2 t_struct_SHA256state_st
                    [ArraySubsc 56; StructField _data])) c,
                          Tsh, hibytes).
  {
    entailer!.
    + unfold hibytes.
      rewrite !Zlength_map.
      rewrite Zlength_intlist_to_Zlist.
      change (WORD * Zlength [hi])%Z with 4.
      omega.
    + destruct c; try solve [inversion Pc].
      simpl. f_equal; rewrite Int.add_assoc; rewrite mul_repr; rewrite add_repr; reflexivity.
    + unfold hibytes.
      symmetry; rewrite (nth_big_endian_integer 0 [hi] hi) at 1 by reflexivity.
      f_equal.
    + pull_left
       (data_at Tsh (Tarray tuchar 4 noattr) [Vundef; Vundef; Vundef; Vundef]
         (offset_val
            (Int.repr
               (nested_field_offset2 t_struct_SHA256state_st
                  [ArraySubsc 56; StructField _data])) c)) .
      repeat rewrite sepcon_assoc.
      apply sepcon_derives; [ | cancel_frame].
      change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))).
      eapply derives_trans; [apply data_at_data_at_; reflexivity |].
      erewrite data_at__memory_block;
        [| reflexivity | reflexivity | change Int.modulus with  4294967296; simpl; omega].
      entailer.
  }
  after_call.
  forward. (* p += 4; *)
  forward. (* cNl=c->Nl; *)
  gather_SEP 0 1 2.
  replace_SEP 0 (`(field_at Tsh t_struct_SHA256state_st [StructField _data]
    ((map Vint (map Int.repr dd') ++
     list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd')) (Vint Int.zero) ++
     map Vint hibytes) ++ [Vundef; Vundef; Vundef; Vundef] ++ []) c)).
  Focus 1. {
    rewrite app_nil_r.
    rewrite app_assoc with (n := map Vint hibytes).
    rewrite <- app_assoc with (m := map Vint hibytes).
    erewrite array_seg_reroot_lemma with (lo := 56) (hi := 60%Z);
      [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | | reflexivity].
    Focus 2. {
      rewrite Zlength_app, !Zlength_map.
      rewrite !Zlength_correct.
      rewrite length_list_repeat.
      rewrite Z2Nat.id by omega.
      change (Z.of_nat CBLOCK) with 64.
      omega.
    } Unfocus.
    Focus 2. {
      unfold hibytes.
      rewrite !Zlength_map, Zlength_intlist_to_Zlist.
      reflexivity.
    } Unfocus.
    entailer!.
  } Unfocus.
  erewrite array_seg_reroot_lemma with (lo := 60) (hi := 64);
    [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | reflexivity | reflexivity].
  Focus 2. {
    rewrite Zlength_app, !Zlength_map.
    rewrite !Zlength_correct.
    rewrite app_length.
    rewrite map_length.
    rewrite length_list_repeat.
    change (length hibytes) with 4%nat.
    rewrite Nat2Z.inj_add by omega.
    rewrite Z2Nat.id by omega.
    change (Z.of_nat CBLOCK) with 64.
    change (Z.of_nat 4) with 4.
    omega.
  } Unfocus.
  normalize.
  forward_call (* (void)HOST_l2c(cNl,p); *)
    (offset_val (Int.repr
      (nested_field_offset2 t_struct_SHA256state_st
         [ArraySubsc 60; StructField _data])) c, Tsh, lobytes).
  {
    entailer!.
    + change (Zlength lobytes) with 4. omega.
    + destruct c; try (contradiction Pc); simpl.
      f_equal; repeat rewrite Int.add_assoc; reflexivity.
    + unfold lobytes.
      symmetry; rewrite (nth_big_endian_integer 0 [lo] lo) at 1 by reflexivity.
      f_equal.
    + pull_left
        (data_at Tsh (Tarray tuchar 4 noattr) [Vundef; Vundef; Vundef; Vundef]
          (offset_val
             (Int.repr
                (nested_field_offset2 t_struct_SHA256state_st
                   [ArraySubsc 60; StructField _data])) c)).
      repeat rewrite sepcon_assoc.
      apply sepcon_derives; [ | cancel_frame].
      change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))).
      eapply derives_trans; [apply data_at_data_at_; reflexivity |].
      erewrite data_at__memory_block;
        [| reflexivity | reflexivity | change Int.modulus with  4294967296; simpl; omega].
      entailer.
  }
  after_call.
  forward. (* p += 4; *)
  forward. (* p -= SHA_CBLOCK; *)
  {
    entailer!.
    destruct c_; try (contradiction Pc_); apply I.
  }
STOP.

 simpl. normalize.
 simpl force_val2. normalize.
 replace (array_at tuchar Tsh (cVint lobytes) 0 4) with 
     (array_at tuchar Tsh  (ZnthV tuchar
                (map Vint (map Int.repr (intlist_to_Zlist [lo])))) 0 4).
Focus 2. apply array_at_ext; intros; unfold cVint, lobytes, ZnthV, Basics.compose; if_tac; try reflexivity.
omega.
rewrite (nth_map' Vint Vundef Int.zero)
 by (simpl length; apply Nat2Z.inj_lt;
       rewrite Z2Nat.id; change (Z.of_nat 4) with 4%Z; omega).
 reflexivity.
 replace (array_at tuchar Tsh (cVint hibytes) 0 4) with 
     (array_at tuchar Tsh  (ZnthV tuchar
                (map Vint (map Int.repr (intlist_to_Zlist [hi])))) 0 4).
Focus 2. apply array_at_ext; intros; unfold cVint, hibytes, ZnthV, Basics.compose; if_tac; try reflexivity.
omega.
rewrite (nth_map' Vint Vundef Int.zero)
 by (simpl length; apply Nat2Z.inj_lt;
       rewrite Z2Nat.id; change (Z.of_nat 4) with 4%Z; omega).
 reflexivity.
clear lobytes hibytes.
normalize.
pose (lastblock := (
         (map Int.repr dd' ++ list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd')) Int.zero
          ++  map Int.repr (intlist_to_Zlist [hi;lo])))).
assert (H99: length lastblock = CBLOCK).
unfold lastblock; repeat rewrite app_length.
rewrite length_list_repeat; simpl.
clear - H0.
rewrite Zlength_correct. repeat rewrite Z2Nat.inj_sub by omega.
repeat rewrite Nat2Z.id. simpl Z.to_nat. rewrite map_length; omega.
assert (BYTESlastblock: Forall isbyteZ (map Int.unsigned lastblock)). {
 unfold lastblock.
 repeat rewrite map_app.
 repeat rewrite Forall_app.
 repeat split; auto.
 apply Forall_isbyteZ_unsigned_repr; auto.
 rewrite map_list_repeat.
 apply Forall_list_repeat. rewrite Int.unsigned_zero; clear; split; omega.
 apply isbyte_intlist_to_Zlist'.
}
unfold POSTCONDITION, abbreviate.
fold (SHA_256 (intlist_to_Zlist hashed ++ dd)).
pose (lastblock' := Zlist_to_intlist (map Int.unsigned lastblock)).
eapply semax_pre; [ | simple apply (sha_final_part3 Espec md c shmd hashed' lastblock'); auto].
* entailer!.
 + destruct c_; try (contradiction Pc_); simpl;
     f_equal; rewrite Int.sub_add_opp;
     repeat rewrite Int.add_assoc; f_equal; reflexivity.
 + 
unfold lastblock', data_block.
simpl.
rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
rewrite Zlist_to_intlist_to_Zlist; [ |rewrite map_length; rewrite H99; exists LBLOCK; reflexivity | assumption].
rewrite Forall_isbyte_repr_unsigned.
rewrite (Zlength_correct (map _ lastblock)).
rewrite map_length; rewrite H99.
change (Z.of_nat CBLOCK) with 64%Z at 2.
change (intlist_to_Zlist [hi; lo])
  with (intlist_to_Zlist [hi] ++intlist_to_Zlist [lo]).
apply (final_part5 hashed dd hashed' dd' pad (intlist_to_Zlist [hi]) (intlist_to_Zlist [lo]) hi lo);
  auto.
* unfold lastblock'.
apply Zlength_length; auto; apply length_Zlist_to_intlist.
rewrite map_length; assumption.
*
apply intlist_to_Zlist_inj.
rewrite intlist_to_Zlist_app.
unfold lastblock'.
rewrite Zlist_to_intlist_to_Zlist; auto.
2: rewrite map_length,H99; exists LBLOCK; reflexivity.
unfold lastblock.
rewrite map_app.
rewrite map_unsigned_repr_isbyte by auto.
rewrite <- app_ass. rewrite H5.
rewrite map_app.
rewrite map_list_repeat.
rewrite Int.unsigned_zero.
rewrite map_unsigned_repr_isbyte by apply isbyte_intlist_to_Zlist.
unfold generate_and_pad.
rewrite intlist_to_Zlist_app.
rewrite Zlist_to_intlist_to_Zlist; auto.
repeat rewrite app_ass.
f_equal. f_equal. f_equal.
rewrite <- app_ass.
f_equal.
rewrite list_repeat_app.
f_equal.
clear - H5 H2 H1 H0 PAD.
assert (Zlength dd' <= 56). rewrite Zlength_correct; change 56 with (Z.of_nat (CBLOCK-8)); apply Nat2Z.inj_le; omega.
clear H0.
replace (Zlength (intlist_to_Zlist hashed ++ dd))
  with (4*Zlength hashed' + Zlength dd' - (1+pad)).
Focus 2. {
rewrite <-  Zlength_intlist_to_Zlist.
rewrite <- initial_world.Zlength_app.
rewrite H5.
rewrite <- app_ass.
rewrite initial_world.Zlength_app.
forget (Zlength (intlist_to_Zlist hashed ++ dd)) as B.
rewrite initial_world.Zlength_app.
rewrite Zlength_cons, Zlength_nil, Zlength_correct.
rewrite length_list_repeat. rewrite Z2Nat.id by omega. omega.
} Unfocus.
change (Z.of_nat CBLOCK - 8) with 56.
clear H5.
rewrite <- Z2Nat.inj_add by omega.
f_equal. {
 transitivity (- (4 * Zlength hashed' + (Zlength dd' - (1 + pad) + 9)) mod 64).
 f_equal. f_equal. omega.
 rewrite <- Z.sub_0_l.
 rewrite Zminus_mod.
 rewrite Zplus_mod.
 rewrite Z.mul_comm.
 destruct H2 as [a H2]; rewrite H2.
 rewrite <- Z.mul_assoc.
 change (LBLOCKz * 4)%Z with 64%Z.
 rewrite Zmult_mod.
 assert (64<>0) by (clear; omega).
 rewrite Z.mod_same by auto. rewrite Z.mul_0_r.
 rewrite Z.mod_0_l at 2 by auto.
 rewrite Z.add_0_l. rewrite Z.mod_mod by auto.
 replace (0 mod 64) with (64 mod 64) by reflexivity.
 destruct PAD; subst.
 rewrite <- Zminus_mod.
 rewrite Z.mod_small; try omega.
 rewrite Zlength_correct in H|-*; omega.
 rewrite Zlength_nil in *.
 rewrite <- Zminus_mod.
 rewrite Z.mod_small; try omega.
}
 rewrite initial_world.Zlength_app, Zlength_intlist_to_Zlist.
 rewrite <- (Z.mul_comm 4) in H7; change 4 with WORD in H7; rewrite H7.
 f_equal; apply hilo_lemma.

 repeat rewrite app_length. rewrite length_list_repeat.
 rewrite length_intlist_to_Zlist.
 repeat rewrite <- plus_assoc.
 rewrite initial_world.Zlength_app, Zlength_intlist_to_Zlist.
 clear.
 apply NPeano_divide_add.
 exists (length hashed). apply mult_comm.
 assert (4 | (Zlength dd + (1 + (- (4 * Zlength hashed + Zlength dd + 9) mod 64)))).
 forget (Zlength dd) as d. forget (Zlength hashed) as h.
 apply Zmod_divide; try omega.
 rewrite <- Z.add_assoc. 
 rewrite Z.add_assoc.
 replace (d + 9) with (d + 1 + 8) by omega.
 forget (d+1) as e.
 rewrite Zplus_mod.
 change 64 with (16*4)%Z.
 rewrite Fcore_Zaux.Zmod_mod_mult by omega.
 rewrite <- Z.sub_0_l.
 rewrite Zminus_mod.
 rewrite (Zplus_mod (4*h)%Z).
 rewrite Zmult_mod.
 rewrite Z.mod_same by omega.
 rewrite Z.mul_0_l.
 rewrite (Zplus_mod e).
 change (8 mod 4) with 0.
 rewrite Z.add_0_r.
 rewrite Z.mod_mod by omega.
 change (0 mod 4) with (4 mod 4) at 1.
 change (0  mod 4) with 0.
  rewrite Z.add_0_l.
 rewrite <- Zminus_mod.
 destruct (zeq (e mod 4) 0). rewrite e0; reflexivity.
 rewrite (Z.mod_small (4 - e mod 4)).
 transitivity (4 mod 4). f_equal; omega.
 reflexivity.
 pose proof (Z.mod_pos_bound e 4). spec H; [omega |].
 omega.
 change WORD with 4. 
 forget (- (4 * Zlength hashed + Zlength dd + 9)) as n.
 assert (0 <= n mod 64) by (apply Z.mod_pos_bound; omega).
 destruct H. exists (Z.to_nat x).
 assert (0 <= x).
 apply Zmult_le_0_reg_r with 4; try omega.
 rewrite <- H.
 clear H. 
 rewrite Zlength_correct at 1. omega.
  rewrite <- Z2Nat.inj_mul by omega.
 rewrite <- H. clear H.
 rewrite Zlength_correct. 
 rewrite Z2Nat.inj_add; try  omega.
 rewrite Nat2Z.id. f_equal.
 simpl length.
 rewrite Z2Nat.inj_add; try  omega.
 reflexivity.

 repeat (apply Forall_app; split; auto).
 apply isbyte_intlist_to_Zlist.
 constructor; auto. split; clear; omega.
 apply Forall_list_repeat. split; clear; omega. 
Qed.

