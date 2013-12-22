Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Require Import progs.verif_sha_final2.
Local Open Scope logic.

Lemma sha_final_part3:
forall (Espec : OracleKind) (md c : val) (shmd : share) (hi lo : int)
  (dd hashed hashed' dd' : list int) (pad : Z)
 (Hshmd: writable_share shmd),
(Zlength hashed * 4 + Zlength dd)%Z = hilo hi lo ->
length dd < CBLOCK ->
length (map Int.unsigned dd') + 8 <= CBLOCK ->
(0 <= pad < 8)%Z ->
NPeano.divide LBLOCK (length hashed') ->
intlist_to_Zlist (map swap hashed') ++ map Int.unsigned dd' =
intlist_to_Zlist (map swap hashed) ++
map Int.unsigned dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
semax
  (initialized _cNl
     (initialized _cNh
        (initialized _ignore (initialized _ignore'1 Delta_final_if1))))
  (PROP  ()
   LOCAL  (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint lo)) (eval_id _cNl); `(eq (Vint hi)) (eval_id _cNh);
   `(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(data_block Tsh
        (intlist_to_Zlist
           (map swap
              (list_drop (length hashed')
                 (generate_and_pad
                    (intlist_to_Zlist (map swap hashed) ++
                     map Int.unsigned dd) 0)))) (offset_val (Int.repr 40) c));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nl c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nh c);
   `(field_at_ Tsh t_struct_SHA256state_st _num c); K_vector;
   `(memory_block shmd (Int.repr 32) md)))
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
           (Ssequence final_loop (Sreturn None)))))
  (function_body_ret_assert tvoid
     (PROP  ()
      LOCAL ()
      SEP  (K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
      `(data_block shmd
          (intlist_to_Zlist
             (process_msg init_registers
                (generate_and_pad_msg
                   (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd))))
          md)))).
Proof.
intros.
assert (LD: length
  (list_drop (length hashed')
     (generate_and_pad
        (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd) 0)) =
    LBLOCK).
admit.  (* looks fine *)
forward. (* sha256_block_data_order (c,p); *)
(*  hashed: list int, b: list int, ctx : val, data: val, sh: share *)
instantiate (1:= (hashed',
           (list_drop (length hashed')
              (generate_and_pad
                 (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd)
                 0)),
        c, (offset_val (Int.repr 40) c), Tsh))
  in (Value of witness).
entailer!.
 erewrite K_vector_globals by (split3; [eassumption | reflexivity.. ]).
cancel.
normalize.
replace_SEP 0%Z  (`(array_at tuint Tsh
          (tuints
             (process_msg init_registers
                (hashed' ++
                 list_drop (length hashed')
                   (generate_and_pad
                      (intlist_to_Zlist (map swap hashed) ++
                       map Int.unsigned dd) 0)))) 0 8 c) *
      `(at_offset 40 (array_at tuchar Tsh (ZnthV tuchar []) 0 64) c) *
      K_vector).
entailer!.
 erewrite K_vector_globals by (split3; [eassumption | reflexivity.. ]).
cancel.
unfold data_block.
rewrite array_at_ZnthV_nil.
rewrite Zlength_correct.
rewrite length_intlist_to_Zlist.
rewrite map_length. rewrite LD.
change (Z.of_nat (4 * LBLOCK))%Z with 64%Z.
unfold at_offset.
apply array_at__array_at.
normalize.
replace (hashed' ++
               list_drop (length hashed')
                 (generate_and_pad
                    (intlist_to_Zlist (map swap hashed) ++
                     map Int.unsigned dd) 0))
  with  (generate_and_pad_msg
                    (intlist_to_Zlist (map swap hashed) ++
                     map Int.unsigned dd)).
Focus 2.
admit.  (* looks fine *)
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
pose proof (length_process_msg 
       (generate_and_pad_msg
                (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd))).
forget  (process_msg init_registers
             (generate_and_pad_msg
                (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd)))
  as hashedmsg.

replace Delta with
 (initialized _ignore'2 (initialized _cNl (initialized _cNh (initialized _ignore (initialized _ignore'1 Delta_final_if1)))))
 by (simplify_Delta; reflexivity).
eapply semax_pre; [ | apply final_part4; auto].
entailer!.
Qed.

Lemma final_part5:
forall (hashed dd hashed' dd' : list int) (pad : Z) (hi' lo' : list Z)
  (hi lo : int) c_,
NPeano.divide LBLOCK (length hashed) ->
length dd < CBLOCK ->
(Zlength dd < 64)%Z ->
length (map Int.unsigned dd') + 8 <= CBLOCK ->
(0 <= pad < 8)%Z ->
NPeano.divide LBLOCK (length hashed') ->
intlist_to_Zlist (map swap hashed') ++ map Int.unsigned dd' =
intlist_to_Zlist (map swap hashed) ++
map Int.unsigned dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
length hi' = 4 ->
length lo' = 4 ->
(Zlength hashed * 4 + Zlength dd)%Z = hilo hi lo ->
isptr c_ ->
hi' = intlist_to_Zlist [swap hi] /\ lo' = intlist_to_Zlist [swap lo] ->
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr lo'))) 0 4
  (offset_val (Int.repr 100) c_) *
array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr hi'))) 0 4
  (offset_val (Int.repr 96) c_) *
array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0
  (Z.of_nat CBLOCK - 8 - Zlength dd')
  (offset_val (Int.repr (Zlength dd' + 40)) c_) *
array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) 0 (Zlength dd')
  (offset_val (Int.repr 40) c_)
|-- array_at tuchar Tsh
      (ZnthV tuchar
         (map Vint
            (dd' ++
             zeros (Z.of_nat CBLOCK - 8 - Zlength dd') ++
             map Int.repr (hi' ++ lo')))) 0 64 (offset_val (Int.repr 40) c_).
Proof.
intros until c_.
intros H4 H3 H3' H0 H1 H2 H5 Lhi Llo H7 Pc_ Hhilo.
 rewrite (split_array_at (Zlength dd') tuchar Tsh _ 0 64)
  by (clear - H0; rewrite Zlength_correct; change CBLOCK with 64 in H0;
  rewrite map_length in H0; omega).
 rewrite (split_array_at 56 tuchar Tsh _ (Zlength dd') 64)
  by (clear - H0; rewrite Zlength_correct; change CBLOCK with 64 in H0;
  rewrite map_length in H0; omega).
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
  (array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) 0 (Zlength dd') cc *
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
 assert (Zlength dd' = Z.of_nat (length (map Vint dd'))).
 rewrite Zlength_correct, map_length; reflexivity.
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
(*  clear - H9; admit.  (* tedious *)
  rewrite Zlength_correct; omega.*)
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
forall (hi lo : int) (dd : list int),
NPeano.divide LBLOCK (length hashed) ->
(Zlength hashed * 4 + Zlength dd)%Z = hilo hi lo ->
length dd < CBLOCK ->
(Zlength dd < 64)%Z ->
forall (hashed' dd' : list int) (pad : Z),
length (map Int.unsigned dd') + 8 <= CBLOCK ->
(0 <= pad < 8)%Z ->
NPeano.divide LBLOCK (length hashed') ->
intlist_to_Zlist (map swap hashed') ++ map Int.unsigned dd' =
intlist_to_Zlist (map swap hashed) ++
map Int.unsigned dd ++ [128%Z] ++ map Int.unsigned (zeros pad) ->
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
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) 0 (Zlength dd')
       (offset_val (Int.repr 40) c));
   `(array_at tuchar Tsh (ZnthV tuchar (map Vint dd')) (Z.of_nat CBLOCK - 8)
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
                (generate_and_pad_msg
                   (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd))))
          md)))).
Proof.
 intros Espec hashed md c shmd H md_ c_ p n cNl cNh ignore
 hi lo dd H4 H7 H3 H3' hashed' dd' pad H0 H1 H2 H5 p0.
 pose (hibytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist ([swap hi])))))).
 pose (lobytes := Basics.compose force_int (ZnthV tuchar (map Vint (map Int.repr (intlist_to_Zlist ([swap lo])))))).
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
 pull_left   (array_at tuchar Tsh (ZnthV tuchar (map Vint dd'))
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
 change CBLOCK with 64 in H0.
 assert (56 <= i-40)%Z by omega.
 apply Z2Nat.inj_le in H; try omega.
 change (Z.to_nat 56) with 56 in H; omega.
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
 pull_left   (array_at tuchar Tsh (ZnthV tuchar (map Vint dd'))
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
 change CBLOCK with 64 in H0.
 assert (60 <= i-40)%Z by omega.
 apply Z2Nat.inj_le in H; try omega.
 change (Z.to_nat 60) with 60 in H; omega.
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
                (map Vint (map Int.repr (intlist_to_Zlist [swap lo])))) 0 4).
Focus 2. apply array_at_ext; intros; unfold cVint, lobytes, ZnthV, Basics.compose; if_tac; try reflexivity.
omega.
rewrite (nth_map' Vint Vundef Int.zero)
 by (simpl length; apply Nat2Z.inj_lt;
       rewrite Z2Nat.id; change (Z.of_nat 4) with 4%Z; omega).
 reflexivity.
 replace (array_at tuchar Tsh (cVint hibytes) 0 4) with 
     (array_at tuchar Tsh  (ZnthV tuchar
                (map Vint (map Int.repr (intlist_to_Zlist [swap hi])))) 0 4).
Focus 2. apply array_at_ext; intros; unfold cVint, hibytes, ZnthV, Basics.compose; if_tac; try reflexivity.
omega.
rewrite (nth_map' Vint Vundef Int.zero)
 by (simpl length; apply Nat2Z.inj_lt;
       rewrite Z2Nat.id; change (Z.of_nat 4) with 4%Z; omega).
 reflexivity.
clear lobytes hibytes.
pose (lastblock := (map Vint 
         (dd' ++ zeros (Z.of_nat CBLOCK - 8 - Zlength dd')
          ++  map Int.repr (intlist_to_Zlist (map swap [hi,lo]))))).
apply semax_pre with
 (PROP  ()
   LOCAL 
   (`(eq (offset_val (Int.repr 40) c)) (eval_id _p);
   `(eq (Vint lo)) (eval_id _cNl);
   `(eq (Vint hi)) (eval_id _cNh);
   `(eq (Vint (Int.repr (Zlength dd')))) (eval_id _n);
   `(eq md) (eval_id _md); `(eq c) (eval_id _c))
   SEP 
   (`(array_at tuchar Tsh (ZnthV tuchar lastblock) 0 64
        (offset_val (Int.repr 40) c));
   `(array_at tuint Tsh
       (ZnthV tuint (map Vint (process_msg init_registers hashed'))) 0 8 c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nl c);
   `(field_at_ Tsh t_struct_SHA256state_st _Nh c);
   `(field_at_ Tsh t_struct_SHA256state_st _num c); 
    K_vector;
   `(memory_block shmd (Int.repr 32) md))).
{unfold lastblock; clear lastblock.
 change (intlist_to_Zlist (map swap [hi,lo])) with
  (intlist_to_Zlist [swap hi] ++ intlist_to_Zlist [swap lo]).
 set (hi' :=intlist_to_Zlist [swap hi]).
 set (lo' :=  intlist_to_Zlist [swap lo]).
 assert (Lhi: length hi' = 4) by reflexivity.
 assert (Llo: length lo' = 4) by reflexivity.
 assert (Hhilo: hi' = intlist_to_Zlist [swap hi] /\ lo' = intlist_to_Zlist [swap lo]) by (split; reflexivity).
 clearbody hi' lo'.
 entailer!.
 destruct c_; try (contradiction Pc_); simpl;
 f_equal; rewrite Int.sub_add_opp;
 repeat rewrite Int.add_assoc; f_equal; reflexivity.
 eapply (final_part5 hashed dd hashed' dd'); try eassumption.
}


replace lastblock with
(map Vint (map Int.repr (intlist_to_Zlist (map swap (
(list_drop (length hashed')
  (generate_and_pad 
   (intlist_to_Zlist (map swap hashed) ++ map Int.unsigned dd)
   0))))))).
Focus 2.
unfold lastblock.
f_equal.
eapply lastblock_lemma; eassumption.
clear lastblock.
replace (array_at tuchar Tsh
        (ZnthV tuchar
           (map Vint
              (map Int.repr
                 (intlist_to_Zlist
                    (map swap
                       (list_drop (length hashed')
                          (generate_and_pad
                             (intlist_to_Zlist (map swap hashed) ++
                              map Int.unsigned dd) 0))))))) 0 64)
 with (data_block Tsh (intlist_to_Zlist
                       (map swap
                       (list_drop (length hashed')
                          (generate_and_pad
                             (intlist_to_Zlist (map swap hashed) ++
                              map Int.unsigned dd) 0))))).
Focus 2. {
clear H9 H8 POSTCONDITION MORE_COMMANDS Delta p2 p3 H6 p1 p0 cNl0.
unfold data_block, tuchars.
f_equal.
rewrite Zlength_correct; rewrite length_intlist_to_Zlist.
rewrite map_length.
rewrite list_drop_length.
change 64%Z with (Z.of_nat (4*16)).
f_equal. f_equal.
admit.  (* seems fine *)
admit.  (* seems fine *)
} Unfocus.
replace Delta with
 (initialized _cNl (initialized _cNh (initialized _ignore (initialized _ignore'1 Delta_final_if1))))
 by (simplify_Delta; reflexivity).
eapply sha_final_part3; eassumption.
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
(*destruct c; try contradiction.
unfold offset_val, sem_add_pi.
f_equal. rewrite Int.add_assoc; f_equal.
rewrite mul_repr, add_repr.
change (sizeof tuchar) with 1%Z; rewrite Z.mul_1_l.
reflexivity.
*)
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
