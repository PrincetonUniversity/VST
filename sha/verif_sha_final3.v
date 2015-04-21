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
   LOCAL  (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
           temp _md md; temp _c c;
           gvar _K256 kv)
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
  rewrite field_at_data_at by reflexivity.
  normalize.
  set (X := map Vint (map Int.repr (intlist_to_Zlist lastblock))).
  assert (JMeq.JMeq X (map Vint (map Int.repr (intlist_to_Zlist lastblock)))) by reflexivity.
  clearbody X.
  revert X H3.

  change (list val) with (reptype (nested_field_type2 t_struct_SHA256state_st [StructField _data])).
  pattern (nested_field_type2 t_struct_SHA256state_st [StructField _data]) at 1 2 4.
  replace (nested_field_type2 t_struct_SHA256state_st [StructField _data])
    with (tarray tuchar (Zlength (intlist_to_Zlist lastblock))).
  Focus 2. {
    rewrite Zlength_correct, length_intlist_to_Zlist.
    apply Zlength_length in H0; [| rewrite Zlength_correct in H0; omega].
    rewrite H0.
    reflexivity.
  } Unfocus.
  intros; subst X.

  forward_call' (* sha256_block_data_order (c,p); *)
    (hashed, lastblock, c,
      field_address t_struct_SHA256state_st [StructField _data] c,
       Tsh, kv).
  {
    unfold data_block.
    unfold Frame.
    instantiate (1:= [field_at Tsh t_struct_SHA256state_st [StructField _num] Vundef c ;
       field_at Tsh t_struct_SHA256state_st [StructField _Nh] Vundef c ;
       field_at Tsh t_struct_SHA256state_st [StructField _Nl] Vundef c ;
       memory_block shmd (Int.repr 32) md]).
   entailer.
  }
  simpl map.
  unfold data_block.
  simpl. rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
  rewrite <- H1.
  forward. (* c->num=0; *)
  forward_call' (* memset (p,0,SHA_CBLOCK); *) 
    (Tsh, (field_address t_struct_SHA256state_st [StructField _data] c), 64%Z, Int.zero)
    vret.
  {
    entailer!.
    replace (Zlength (intlist_to_Zlist lastblock)) with 64
        by (rewrite Zlength_intlist_to_Zlist, H0; reflexivity).
    cancel.
  }
  simpl map.
  replace Delta with
    (initialized _cNl (initialized _cNh Delta_final_if1))
    by (simplify_Delta; reflexivity).
  eapply semax_pre; [ | apply final_part4; auto].
  + unfold_data_at 2%nat.
    rewrite field_at_data_at with (gfs := [StructField _data]) by reflexivity.
    entailer!.
  + apply length_hash_blocks; auto.
    rewrite H1.
    apply divide_length_app; auto.
    exists 1; apply H0.
Qed.

Lemma nth_list_repeat':
  forall A i n (a d: A),
   (i < n)%nat -> nth i (list_repeat n a) d = a.
Proof.
 induction i; destruct n; simpl; intros; auto; try omega.
 apply IHi; omega.
Qed.


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
forall bitlen (dd : list Z),
(LBLOCKz | Zlength hashed) ->
((Zlength hashed * 4 + Zlength dd)*8)%Z = bitlen ->
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
(*offset_in_range 64 (offset_val (Int.repr 40) c) ->*)
semax Delta_final_if1
  (PROP  ()
      LOCAL 
      (temp _p 
         (field_address t_struct_SHA256state_st [ArraySubsc (Z.of_nat CBLOCK - 8); StructField _data] c);
      temp _n (Vint (Int.repr (Zlength dd'))); 
      temp _md md; temp _c c; gvar _K256 kv)
      SEP 
      (`(field_at Tsh t_struct_SHA256state_st [StructField _data]
           (map Vint (map Int.repr dd') ++
            list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
              (Vint Int.zero) ++ []) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _num] Vundef c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part bitlen)) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part bitlen)) c);
      `(field_at Tsh t_struct_SHA256state_st [StructField _h]
          (map Vint (hash_blocks init_registers hashed')) c);
      `(K_vector kv);
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
  bitlen dd H4 H7 H3 DDbytes hashed' dd' pad
  DDbytes' PAD H0 H1 H2 H5(* Pofs*).
  abbreviate_semax.
  pose (hibytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [hi_part bitlen])))).
  pose (lobytes := map force_int (map Vint (map Int.repr (intlist_to_Zlist [lo_part bitlen])))).
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
    erewrite field_at_data_equal; [ reflexivity |].
    rewrite !app_nil_r.
    apply data_equal_sym.
    rewrite app_assoc.
    eapply data_equal_trans;
    apply data_equal_list_repeat_default;
    reflexivity.
  } Unfocus.
  erewrite array_seg_reroot_lemma with (lo := 56) (hi := 60%Z);
    [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | ].
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
(*  rewrite <- seq_assoc.  shouldn't be necessary *)
  forward_call' (* (void)HOST_l2c(cNh,p); *)
     (field_address0 t_struct_SHA256state_st
                    [ArraySubsc 56; StructField _data] c,
      Tsh, hibytes).
     apply prop_right; repeat constructor; hnf; simpl.
  unfold hibytes.
  rewrite (nth_big_endian_integer 0 [hi_part bitlen] (hi_part bitlen)) at 1 by reflexivity.
  reflexivity.
  
  rewrite field_address_clarify by auto.
  rewrite field_address0_clarify by auto.
  destruct c_; try contradiction; normalize.
  split; auto. change (Zlength hibytes) with 4. clear; omega.
  unfold map at 2.
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
      [| omega | omega | reflexivity | omega | reflexivity | reflexivity |  | reflexivity].
    Focus 2. {
      rewrite Zlength_app, !Zlength_map.
      rewrite !Zlength_correct.
      rewrite length_list_repeat.
      rewrite Z2Nat.id by omega.
      change (Z.of_nat CBLOCK) with 64.
      omega.
    } Unfocus.
    entailer!.
  } Unfocus.
  forward p_old. (* p += 4; *)
  forward. (* cNl=c->Nl; *)
  erewrite array_seg_reroot_lemma with (lo := 60) (hi := 64);
    [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | reflexivity].
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
  forward_call' (* (void)HOST_l2c(cNl,p); *)
    (field_address0 t_struct_SHA256state_st
                    [ArraySubsc 60; StructField _data] c,
     Tsh, lobytes).
  {
  apply prop_right; repeat constructor; hnf; simpl; auto.
  rewrite (nth_big_endian_integer 0 [lo_part bitlen] (lo_part bitlen)) at 1 by reflexivity;
  reflexivity.
  make_Vptr c_; simpl.
  symmetry.
  rewrite field_address0_clarify by auto.
  rewrite field_address_clarify. simpl.
  normalize.
  clear - TC0.
  unfold field_address in *; simpl in *.
  if_tac; try contradiction. apply I.
 }
  split; auto.
  compute; congruence.
  simpl map.
  gather_SEP 0 1 2.
  replace_SEP 0
    (`(field_at Tsh t_struct_SHA256state_st [StructField _data]
         ((map Vint (map Int.repr dd') ++
             list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd'))
               (Vint Int.zero) ++ (map Vint hibytes)) ++ (map Vint lobytes) ++ []) c)).
  {
    erewrite array_seg_reroot_lemma with (lo := 60) (hi := 64);
      [| omega | omega | reflexivity | omega | reflexivity | reflexivity | | reflexivity ].
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
    entailer!.
  }
  rewrite app_nil_r.
  forward p1. (* p += 4; *)
    entailer!. rewrite field_address_clarify. normalize.
    clear - TC0.
     unfold field_address in *. if_tac; try contradiction.
      destruct c_; simpl in *; try contradiction. auto.
  forward p2. (* p -= SHA_CBLOCK; *)
  {
    entailer!. rewrite field_address_clarify.
          make_Vptr c_; simpl in *; auto.
    clear - TC0.
     unfold field_address in *. if_tac; try contradiction.
      destruct c_; simpl in *; try contradiction. auto.
  }
 clear p2 H9. clear p1 H8.
  drop_LOCAL 1%nat. (* drop cNl *)
  drop_LOCAL 1%nat. (* drop cNh *)
  match goal with
  | |- semax _ (PROPx nil (LOCALx (_ :: ?L) (SEPx ?S))) _ _ =>
         apply semax_pre0 with (PROPx nil (LOCALx (
           temp _p (field_address t_struct_SHA256state_st [StructField _data] c)
           :: L) (SEPx S)))
  end.
  Focus 1. {
    entailer!.
    rewrite <- H8.
    unfold field_address.
    make_Vptr (eval_id _c rho).
    simpl.
    if_tac; [rewrite if_true | rewrite if_false]; auto.
    unfold offset_val, force_val; simpl.
    f_equal.     rewrite Int.sub_add_opp.
    rewrite !Int.add_assoc.
    f_equal. normalize.
    rewrite Int.neg_repr. normalize.
    hnf in H6|-*; decompose [and] H6; repeat split; auto.
  } Unfocus.
  change (map Vint hibytes) with (map Vint (map Int.repr (intlist_to_Zlist [hi_part bitlen]))).
  change (map Vint lobytes) with (map Vint (map Int.repr (intlist_to_Zlist [lo_part bitlen]))).
  clear lobytes hibytes.
  change (Vint Int.zero) with (Vint (Int.repr 0)).
  rewrite <- !map_list_repeat.
  rewrite <- !map_app.
  rewrite <- !app_assoc.
  rewrite <- intlist_to_Zlist_app.
  simpl ([hi_part bitlen] ++ [lo_part bitlen]).
  set (lastblock := map Int.repr
          (dd' ++ list_repeat (Z.to_nat (Z.of_nat CBLOCK - 8 - Zlength dd')) 0
              ++ intlist_to_Zlist [hi_part bitlen; lo_part bitlen])).
  assert (H99: length lastblock = CBLOCK).
  Focus 1. {
    unfold lastblock.
    rewrite map_length, !app_length.
    rewrite length_list_repeat; simpl.
    clear - H0.
    rewrite Zlength_correct. repeat rewrite Z2Nat.inj_sub by omega.
    repeat rewrite Nat2Z.id. simpl Z.to_nat.
    omega.
  } Unfocus.
  assert (BYTESlastblock: Forall isbyteZ (map Int.unsigned lastblock)). {
    unfold lastblock.
    repeat rewrite map_app.
    repeat rewrite Forall_app.
    repeat split; auto.
    apply Forall_isbyteZ_unsigned_repr; auto.
    rewrite !map_list_repeat.
    apply Forall_list_repeat.
    change (Int.unsigned (Int.repr 0)) with 0; split; omega.
    apply isbyte_intlist_to_Zlist'.
  }
  unfold POSTCONDITION, abbreviate.
  fold (SHA_256 (intlist_to_Zlist hashed ++ dd)).
  pose (lastblock' := Zlist_to_intlist (map Int.unsigned lastblock)).
  eapply semax_pre; [ | simple apply (sha_final_part3 Espec md c shmd hashed' lastblock'); auto].
  * entailer!.
    + apply isbyte_intlist_to_Zlist.
    + unfold_data_at 1%nat.
      unfold lastblock'.
      rewrite Zlist_to_intlist_to_Zlist; auto.
      Focus 2. {
        rewrite map_length,H99.
        exists LBLOCK; reflexivity.
      } Unfocus.
      rewrite map_map with (g := Int.repr).
      replace ((fun x : int => Int.repr (Int.unsigned x))) with (@id int).
      Focus 2.
      {
        extensionality i.
        rewrite Int.repr_unsigned.
        reflexivity.
      } Unfocus.
      rewrite map_id.
      cancel.
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
rewrite !map_app.
rewrite map_unsigned_repr_isbyte by auto.
rewrite <- app_ass. rewrite H5.
rewrite !map_list_repeat.
change (Int.unsigned (Int.repr 0)) with 0.
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
 reflexivity.

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

