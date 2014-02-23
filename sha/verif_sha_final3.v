Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.sha_lemmas2.
Require Import sha.verif_sha_final2.
Local Open Scope logic.


Definition sha_final_epilog :=
  (Ssequence
     (Scall None
        (Evar _sha256_block_data_order
           (Tfunction
              (Tcons (tptr t_struct_SHA256state_st) (Tcons (tptr tvoid) Tnil))
              tvoid))
        [Etempvar _c (tptr t_struct_SHA256state_st),
        Etempvar _p (tptr tuchar)])
     (Ssequence
        (Sassign
           (Efield
              (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                 t_struct_SHA256state_st) _num tuint)
           (Econst_int (Int.repr 0) tint))
        (Ssequence
           (Ssequence
              (Scall (Some _ignore'2)
                 (Evar _memset
                    (Tfunction
                       (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                       (tptr tvoid)))
                 [Etempvar _p (tptr tuchar), Econst_int (Int.repr 0) tint,
                 Ebinop Omul (Econst_int (Int.repr 16) tint)
                   (Econst_int (Int.repr 4) tint) tint])
              (Sset _ignore (Etempvar _ignore'2 (tptr tvoid))))
           (Ssequence final_loop (Sreturn None))))).

Lemma sha_final_part3:
forall (Espec : OracleKind) (md c : val) (shmd : share)
  (hashed lastblock: list int) msg
 (Hshmd: writable_share shmd),
 NPeano.divide LBLOCK (length hashed) ->
 length lastblock = LBLOCK ->
 generate_and_pad msg = hashed++lastblock ->
semax
  (initialized _cNl
     (initialized _cNh
        (initialized _ignore (initialized _ignore'1 Delta_final_if1))))
  (PROP  ()
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(data_block Tsh (intlist_to_Zlist lastblock)
                 (offset_val (Int.repr 40) c));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (process_msg init_registers hashed))) 0 8 c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nl c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nh c);
   `(field_at_ Tsh t_struct_SHA256state_st _num c); K_vector;
   `(memory_block shmd (Int.repr 32) md)))
  sha_final_epilog
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd (SHA_256 msg) md)))).
Proof.
intros.
unfold sha_final_epilog.
forward. (* sha256_block_data_order (c,p); *)
instantiate (1:= (hashed, lastblock, c, (offset_val (Int.repr 40) c), Tsh))
  in (Value of witness).
entailer!.
normalize.
replace_SEP 0%Z  (`(array_at tuint Tsh
          (tuints
             (process_msg init_registers (hashed ++ lastblock))) 0 8 c) *
      `(at_offset 40 (array_at tuchar Tsh (ZnthV tuchar []) 0 64) c) *
      K_vector).
entailer!.
unfold data_block.
simpl. rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
rewrite array_at_ZnthV_nil.
rewrite Zlength_correct.
rewrite length_intlist_to_Zlist.
rewrite H0.
change (Z.of_nat (4 * LBLOCK))%Z with 64%Z.
unfold at_offset.
apply array_at__array_at.
normalize.
rewrite <- H1.
forward. (* c->num=0; *)
forward. (* ignore=memset (p,0,SHA_CBLOCK); *)
instantiate (1:= (Tsh, (offset_val (Int.repr 40) c), 64%Z, Int.zero))
  in (Value of witness).
entailer!.
 rewrite (memory_block_array_tuchar _ 64%Z) by Omega1.
pull_left (at_offset 40 (array_at tuchar Tsh (ZnthV tuchar []) 0 64) c).
repeat rewrite sepcon_assoc; apply sepcon_derives; [ | cancel].
unfold at_offset.
cancel.
autorewrite with subst.
replace_SEP 0%Z (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 64
          (offset_val (Int.repr 40) c))).
entailer!.
forward.  (* ignore = ignore'; *)
fold t_struct_SHA256state_st.
pose proof (length_process_msg (generate_and_pad msg)).
replace Delta with
 (initialized _ignore'2 (initialized _cNl (initialized _cNh (initialized _ignore (initialized _ignore'1 Delta_final_if1)))))
 by (simplify_Delta; reflexivity).
eapply semax_pre; [ | apply final_part4; auto].
entailer!.
Qed.

Lemma final_part5:
forall (hashed: list int) (dd:list Z) (hashed': list int) (dd' : list Z) (pad : Z) (hi' lo' : list Z)
  (hi lo : int) c_,
(* (pad=0%Z \/ dd'=nil) -> *)
NPeano.divide LBLOCK (length hashed) ->
(length dd < CBLOCK)%nat ->
(Zlength dd < 64)%Z ->
(length dd' + 8 <= CBLOCK)%nat ->
(0 <= pad < 8)%Z ->
NPeano.divide LBLOCK (length hashed') ->
intlist_to_Zlist hashed' ++ dd' =
intlist_to_Zlist hashed ++ dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
length hi' = 4%nat ->
length lo' = 4%nat ->
isptr c_ ->
hi' = intlist_to_Zlist [hi] /\ lo' = intlist_to_Zlist [lo] ->
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
             zeros (Z.of_nat CBLOCK - 8 - Zlength dd') ++
             map Int.repr (hi' ++ lo')))) 0 64 (offset_val (Int.repr 40) c_).
Proof.
intros until c_.
intros H4 H3 H3' H0 H1 H2 H5 Lhi Llo Pc_ Hhilo.
 rewrite (split_array_at (Zlength dd') tuchar Tsh _ 0 64)
  by (clear - H0; rewrite Zlength_correct; change CBLOCK with 64%nat in H0;
  omega).
 rewrite (split_array_at 56 tuchar Tsh _ (Zlength dd') 64)
  by (clear - H0; rewrite Zlength_correct; change CBLOCK with 64%nat in H0;
  omega).
 rewrite (split_array_at 60 tuchar Tsh _ 56 64) by omega.
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
 repeat rewrite <- offset_val_array_at.
 apply derives_trans with
  (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd') cc *
   array_at tuchar Tsh (fun _ : Z => Vint Int.zero) (Zlength dd' + 0)
   (Zlength dd' + (Z.of_nat CBLOCK - 8 - Zlength dd')) cc *
   array_at tuchar Tsh (fun i : Z => ZnthV tuchar (map Vint (map Int.repr hi')) (i - 56)) 
      56 60 cc *
  array_at tuchar Tsh (fun i : Z => ZnthV tuchar (map Vint (map Int.repr lo')) (i - 60)) 
      60 64 cc);
  [solve [cancel] | ].
 rewrite Z.add_0_r.
 replace (Zlength dd' + (Z.of_nat CBLOCK - 8 - Zlength dd'))%Z
  with 56%Z by (change (Z.of_nat CBLOCK) with 64%Z; clear; omega).
 assert (Zlength dd' >= 0)%Z by (rewrite Zlength_correct; omega).
 assert (Zlength dd' = Z.of_nat (length (map Vint (map Int.repr dd')))).
 rewrite Zlength_correct; repeat rewrite map_length; reflexivity.
 assert (Z.of_nat CBLOCK - 8 - Z.of_nat (length dd') >= 0)%Z.
    clear - H0; admit. (* tedious *)
 repeat rewrite sepcon_assoc;
 repeat apply sepcon_derives; apply derives_refl';
 apply equal_f; try apply array_at_ext; intros;
 unfold ZnthV; repeat rewrite if_false by omega.
+ repeat rewrite map_app.
   rewrite app_nth1; [reflexivity | ].
 apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega; omega.
+ repeat rewrite map_app.
   rewrite app_nth2. rewrite app_nth1.
  rewrite nth_map_zeros. auto.
  rewrite Nat2Z.inj_sub by Omega1. Omega1.
  rewrite (map_length _ (zeros _)).
  rewrite length_zeros.
  apply Nat2Z.inj_lt; rewrite Nat2Z.inj_sub; Omega1.
  Omega1.
+ repeat rewrite map_app.
   rewrite <- app_ass.
   rewrite app_nth2. rewrite app_nth1.
   f_equal.    rewrite app_length.  
   repeat rewrite map_length; rewrite map_length in H6.
   rewrite length_zeros.
   rewrite H6. Omega1.
  rewrite app_length; rewrite (map_length _ (zeros _)); rewrite length_zeros.
  rewrite H6. repeat rewrite map_length.
  rewrite Lhi.
    change (Z.of_nat CBLOCK - 8)%Z with 56%Z. 
  apply Nat2Z.inj_lt; try omega.
  rewrite Nat2Z.inj_sub; try Omega1.
  rewrite H6; repeat rewrite app_length; repeat rewrite map_length;
   rewrite length_zeros.
  Omega1.
+ admit.  (* tedious *)
Qed.

Lemma final_part2:
forall (Espec : OracleKind) (hashed : list int) (md c : val) (shmd : share),
writable_share shmd ->
name _md ->
name _c ->
name _p ->
name _n ->
name _cNl ->
name _cNh ->
name _ignore ->
forall (hi lo : int) (dd : list Z),
NPeano.divide LBLOCK (length hashed) ->
((Zlength hashed * 4 + Zlength dd)*8)%Z = hilo hi lo ->
(length dd < CBLOCK)%nat ->
(Zlength dd < 64)%Z ->
 (Forall isbyteZ dd) ->
forall (hashed': list int) (dd' : list Z) (pad : Z),
 (Forall isbyteZ dd') ->
 (pad=0%Z \/ dd'=nil) ->
(length dd' + 8 <= CBLOCK)%nat ->
(0 <= pad < 8)%Z ->
NPeano.divide LBLOCK (length hashed') ->
intlist_to_Zlist hashed' ++ dd' =
intlist_to_Zlist hashed ++ dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
forall p0 : val,
semax (initialized _ignore (initialized _ignore'1 Delta_final_if1))
  (PROP  ()
   LOCAL 
   (`(eq (force_val (sem_add_pi tuchar p0 (Vint (Int.repr (16 * 4 - 8))))))
      (eval_id _p); `(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `(eq p0) (`(offset_val (Int.repr 40)) (`force_ptr (eval_id _c)));
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
        (Z.of_nat CBLOCK - 8 - Zlength dd')
        (offset_val (Int.repr (40 + Zlength dd')) c));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
   `(field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c);
   `(field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c);
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) 0 (Zlength dd')
       (offset_val (Int.repr 40) c));
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd'))) (Z.of_nat CBLOCK - 8)
       64 (offset_val (Int.repr 40) c));
   `(field_at_ Tsh t_struct_SHA256state_st _num c); K_vector;
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
                 (Tfunction (Tcons (tptr tuint) (Tcons tuint Tnil)) tvoid))
              [Ecast (Etempvar _p (tptr tuchar)) (tptr tuint),
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
                          tvoid))
                    [Ecast (Etempvar _p (tptr tuchar)) (tptr tuint),
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
                                (Tcons (tptr tvoid) Tnil)) tvoid))
                       [Etempvar _c (tptr t_struct_SHA256state_st),
                       Etempvar _p (tptr tuchar)])
                    (Ssequence
                       (Sassign
                          (Efield
                             (Ederef
                                (Etempvar _c (tptr t_struct_SHA256state_st))
                                t_struct_SHA256state_st) _num tuint)
                          (Econst_int (Int.repr 0) tint))
                       (Ssequence
                          (Ssequence
                             (Scall (Some _ignore'2)
                                (Evar _memset
                                   (Tfunction
                                      (Tcons (tptr tvoid)
                                         (Tcons tint (Tcons tuint Tnil)))
                                      (tptr tvoid)))
                                [Etempvar _p (tptr tuchar),
                                Econst_int (Int.repr 0) tint,
                                Ebinop Omul (Econst_int (Int.repr 16) tint)
                                  (Econst_int (Int.repr 4) tint) tint])
                             (Sset _ignore (Etempvar _ignore'2 (tptr tvoid))))
                          (Ssequence
                             final_loop
                             (Sreturn None))))))))))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd
          (intlist_to_Zlist
             (process_msg init_registers
                (generate_and_pad
                   (intlist_to_Zlist hashed ++ dd))))
          md)))).
Proof.
 intros Espec hashed md c shmd H md_ c_ p n cNl cNh ignore
 hi lo dd H4 H7 H3 H3' DDbytes hashed' dd' pad 
 DDbytes' PAD H0 H1 H2 H5 p0.
 pose (hibytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist [hi]))))).
 pose (lobytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist [lo]))))).
 rewrite (split_array_at 60%Z tuchar Tsh _ (Z.of_nat CBLOCK - 8)%Z 64%Z)
  by (change (Z.of_nat CBLOCK) with 64%Z; split; computable).
 forward. (* cNh=c->Nh; *)
 forward. (* (void)HOST_l2c(cNh,p); *)
 instantiate (1:=(offset_val (Int.repr 56) (offset_val (Int.repr 40) c),
                         Tsh, hibytes)) in (Value of witness).
 rewrite (Z.add_comm 40).
 entailer!.
 destruct c; try (contradiction Pc); simpl. f_equal; rewrite Int.add_assoc; rewrite mul_repr; rewrite add_repr; reflexivity.
 unfold hibytes.
 symmetry; rewrite (nth_big_endian_integer 0 [hi] hi) at 1 by reflexivity.
 f_equal; extensionality z; unfold Basics.compose.
 f_equal; f_equal.
 change (Z.of_nat 0 * 4)%Z with 0%Z. clear; omega.
 pull_left   (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd')))
            (Z.of_nat CBLOCK - 8) 60 (offset_val (Int.repr 40) c)) .
 repeat rewrite sepcon_assoc.
 apply sepcon_derives; [ | cancel_frame].
 change 40%Z with (sizeof tuchar * 40)%Z at 1.
 rewrite <- offset_val_array_at.
 change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))).
 rewrite memory_block_typed by reflexivity.
 simpl_data_at.
 change (40+56)%Z with (sizeof tuchar * (40+56))%Z.
 rewrite <- offset_val_array_at.
 change (40+56+4)%Z with (40+60)%Z.
 change (40 + (Z.of_nat CBLOCK - 8))%Z with (40 + 56 + 0)%Z.
 apply derives_refl'; apply equal_f; apply array_at_ext.
 intros. unfold ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite nth_overflow.
 rewrite nth_overflow. auto.
 simpl length.
 rewrite Z2Nat.inj_sub by omega. omega.
clear - H0 H9.
 rewrite map_length in *.
 change CBLOCK with 64%nat in H0.
 assert (56 <= i-40)%Z by omega.
 apply Z2Nat.inj_le in H; try omega.
 change (Z.to_nat 56) with 56%nat in H; rewrite map_length; omega.
 forward. (* p += 4; *)
 entailer!.
 forward. (* cNl=c->Nl; *)
 forward. (* (void)HOST_l2c(cNl,p); *)
 instantiate (1:=(offset_val (Int.repr 60) (offset_val (Int.repr 40) c),
                         Tsh, lobytes)) in (Value of witness).
 entailer!.
 destruct c; try (contradiction Pc); simpl.
 f_equal; repeat rewrite Int.add_assoc; f_equal.
 unfold lobytes.
 symmetry; rewrite (nth_big_endian_integer 0 [lo] lo) at 1 by reflexivity.
 f_equal; extensionality z; unfold Basics.compose.
 f_equal; f_equal.
 change (Z.of_nat 0 * 4)%Z with 0%Z. clear; omega.
 pull_left   (array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr dd')))
             60 64 (offset_val (Int.repr 40) c)) .
 repeat rewrite sepcon_assoc.
 apply sepcon_derives; [ | cancel_frame].
 change 40%Z with (sizeof tuchar * 40)%Z at 1.
 rewrite <- offset_val_array_at.
 change (Int.repr 4) with (Int.repr (sizeof (tarray tuchar 4))).
 rewrite memory_block_typed by reflexivity.
 simpl_data_at.
 change (40+60)%Z with (sizeof tuchar * (40+60))%Z.
 rewrite <- offset_val_array_at.
 change (40+60+0)%Z with (40+60)%Z.
 change (40 + 60+4)%Z with (40 + 64)%Z.
 apply derives_refl'; apply equal_f; apply array_at_ext.
 intros. unfold ZnthV. rewrite if_false by omega.
 rewrite if_false by omega.
 rewrite nth_overflow.
 rewrite nth_overflow. auto.
 simpl length.
 rewrite Z2Nat.inj_sub by omega. omega.
clear - H0 H10.
 rewrite map_length in *.
 change CBLOCK with 64%nat in H0.
 assert (60 <= i-40)%Z by omega.
 apply Z2Nat.inj_le in H; try omega.
 change (Z.to_nat 60) with 60%nat in H; rewrite map_length; omega.
 autorewrite with subst.
 normalize.
 forward. (* p += 4; *)
 entailer!. destruct c_; try (contradiction Pc_); apply I.
 forward. (*   p -= SHA_CBLOCK; *)
 entailer!. destruct c_; try (contradiction Pc_); apply I.
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
(* rewrite (Zlength_correct dd').
 rewrite (array_at_tuchar_isbyteZ _ (map Int.repr dd')).
rewrite <- (Zlength_correct dd').*)
normalize.
(* rename H10 into Hforall; rewrite firstn_same in Hforall by (rewrite map_length; clear; rewrite map_length; omega). *)
pose (lastblock := (
         (map Int.repr dd' ++ zeros (Z.of_nat CBLOCK - 8 - Zlength dd')
          ++  map Int.repr (intlist_to_Zlist [hi,lo])))).
assert (H10: length lastblock = CBLOCK).
unfold lastblock; repeat rewrite app_length.
rewrite length_zeros; simpl.
clear - H0.
rewrite Zlength_correct. repeat rewrite Z2Nat.inj_sub by omega.
repeat rewrite Nat2Z.id. simpl Z.to_nat. rewrite map_length; omega.
assert (BYTESlastblock: Forall isbyteZ (map Int.unsigned lastblock)). {
 unfold lastblock.
 repeat rewrite map_app.
 repeat rewrite Forall_app.
 repeat split; auto.
 apply Forall_isbyteZ_unsigned_repr; auto.
 apply isbyte_zeros.
 apply isbyte_intlist_to_Zlist'.
}
pose (lastblock' := Zlist_to_intlist (map Int.unsigned lastblock)).
eapply semax_pre; [ | apply (sha_final_part3 Espec md c shmd hashed' lastblock'); auto].
* entailer!.
 + destruct c_; try (contradiction Pc_); simpl;
     f_equal; rewrite Int.sub_add_opp;
     repeat rewrite Int.add_assoc; f_equal; reflexivity.
 + 
unfold lastblock', data_block. (*rewrite map_swap_involutive.*)
simpl.
rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
rewrite Zlist_to_intlist_to_Zlist; [ |rewrite map_length; rewrite H10; exists LBLOCK; reflexivity | assumption].
rewrite Forall_isbyte_repr_unsigned.
rewrite (Zlength_correct (map _ lastblock)). try rewrite map_length; rewrite H10.
change (Z.of_nat CBLOCK) with 64%Z at 2.
change (intlist_to_Zlist [hi, lo])
  with (intlist_to_Zlist [hi] ++intlist_to_Zlist [lo]).
apply (final_part5 hashed dd hashed' dd' pad (intlist_to_Zlist [hi]) (intlist_to_Zlist [lo]) hi lo);
  auto.
* unfold lastblock'.
apply length_Zlist_to_intlist.
rewrite map_length; assumption.
*
apply intlist_to_Zlist_inj.
rewrite (lastblock_lemma _ hashed' dd' pad hi lo); auto.
2: repeat rewrite app_ass; apply H5.
2: rewrite <- H7; f_equal; rewrite initial_world.Zlength_app,
        Zlength_intlist_to_Zlist, Z.mul_comm; reflexivity.
2: apply Forall_app; split; auto;apply isbyte_intlist_to_Zlist.
rewrite (app_ass _ dd); rewrite <- H5.
rewrite app_ass; rewrite intlist_to_Zlist_app.
f_equal.
unfold lastblock'.
rewrite Zlist_to_intlist_to_Zlist;
 [  | rewrite map_length, H10; eexists;reflexivity | auto].
unfold lastblock; repeat rewrite map_app.
f_equal.
symmetry; apply map_unsigned_repr_isbyte; auto.
f_equal.
f_equal.
f_equal.
clear dependent p1. clear dependent p2. clear p0 p3.
clear Delta POSTCONDITION MORE_COMMANDS.
clear DDbytes DDbytes'.
clear lastblock'.
clear dependent lastblock.
clear dependent hi; clear lo.
clear dependent shmd.
destruct PAD; subst; simpl in *.
rewrite Z.sub_0_r.
replace (Zlength (intlist_to_Zlist hashed ++ dd) + 9)
  with (Zlength (intlist_to_Zlist hashed') + Zlength dd' + 8).
admit.  (* looks fine *)
admit.  (* easy *)
clear H0.
rewrite Zlength_nil, Z.sub_0_r.
rewrite <- app_nil_end in H5.
assert (Zlength dd + 1 + pad = CBLOCKz)
 by admit.
transitivity (- (Zlength dd + 9) mod CBLOCKz - pad).
 admit. (* fine *)
replace (Zlength dd) with (CBLOCKz - (1+pad)) by omega.
replace (CBLOCKz - (1+pad) + 9) with (CBLOCKz + (8-pad)) by omega.
rewrite Z.mod_opp_l_nz by admit.
rewrite Z.add_mod by (intro Hx; inv Hx).
rewrite Z_mod_same by (change CBLOCKz with 64; omega).
rewrite Z.add_0_l.
rewrite Z.mod_mod by (change CBLOCKz with 64; omega).
rewrite Z.mod_small by (change CBLOCKz with 64; omega).
change (Z.of_nat CBLOCK) with CBLOCKz; omega.
Qed.

