Require Import aes.api_specs.
Require Import aes.partially_filled.
Require Import aes.bitfiddling.
Open Scope Z.
Local Open Scope logic.

(* Calls forward_if with the current precondition to which the provided conditions are added *)
(* QQQ TODO does this already exist? Add to library? *)
Ltac forward_if_diff add := match add with
| (PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2))) => match goal with
  | |- semax ?Delta (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ _ =>
    let P3 := fresh "P3" in let Q3 := fresh "Q3" in let R3 := fresh "R3" in
    pose (P3 := P1 ++ P2); pose (Q3 := Q1 ++ Q2); pose (R3 := R1 ++ R2);
    simpl in P3, Q3, R3;
    forward_if (PROPx P3 (LOCALx Q3 (SEPx R3)));
    subst P3 Q3 R3
  end
end.

(* TODO floyd put this in library *)
Ltac replace_temp name new_value := match goal with
| |- context [ (temp name ?old_value) ] =>
     let E := fresh "E" in assert_PROP (old_value = new_value) as E;
     [ | replace (temp name old_value) with (temp name new_value) by congruence; clear E ]
end.
Tactic Notation "replace_temp" constr(name) constr(new_value) :=
  replace_temp name new_value.
Tactic Notation "replace_temp" constr(name) constr(new_value) "by" tactic(t) :=
  replace_temp name new_value; [ t | ].

Definition first_loop_inv00 ctx key init_done key_chars ctx_sh key_sh ish i gv :=
    PROP ( )
    LOCAL (
      temp _RK  (field_address t_struct_aesctx [StructField _buf] ctx);
      temp _key key; temp _keybits (Vint (Int.repr 256));
      gvars gv)
    SEP (
      field_at ctx_sh t_struct_aesctx [StructField _nr] (Vint (Int.repr 14)) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _rk] 
        (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _buf]
        (partially_filled i 68 (fun i => get_uint32_le key_chars (i*4))) ctx;
      data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars)) key;
      data_at ish tint (Vint (Int.repr init_done)) (gv _aes_init_done);
      tables_initialized (gv _tables)).

Definition first_loop_inv0 ctx key init_done key_chars ctx_sh key_sh ish gv :=
  EX i: Z, first_loop_inv00 ctx key init_done key_chars ctx_sh key_sh ish i gv.

Definition main_loop_invariant0 ctx key ctx_sh key_sh ish key_chars init_done i gv :=
  PROP ( )
  LOCAL (
    temp _RK (offset_val (i*32) (field_address t_struct_aesctx [StructField _buf] ctx));
    gvars gv
  ) SEP (
    field_at ctx_sh t_struct_aesctx [StructField _nr] (Vint (Int.repr 14)) ctx;
    field_at ctx_sh t_struct_aesctx [StructField _rk]
      (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
    field_at ctx_sh t_struct_aesctx [StructField _buf]
      (map Vint (pow_fun GrowKeyByOne (Z.to_nat (i*8)) (key_bytes_to_key_words key_chars))
      ++ repeat_op_table (60-i*8) Vundef id) ctx;
    data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars)) key;
    data_at ish tint (Vint (Int.repr init_done)) (gv _aes_init_done);
    tables_initialized (gv _tables)
  ).

Definition main_loop_invariant ctx key ctx_sh key_sh ish key_chars init_done gv :=
  EX i: Z, main_loop_invariant0 ctx key ctx_sh key_sh ish key_chars init_done i gv.


Lemma Znth_partially_expanded_key: forall key i,
  0 <= i < 7 ->
  forall j,
  0 <= j < 8 + i*8 ->
  (Znth j (map Vint (pow_fun GrowKeyByOne (Z.to_nat (i * 8)) key)
           ++ repeat_op_table (60 - i * 8) Vundef id))
  = Vint (Znth j (KeyExpansion2 key)).
Admitted.

Lemma Zlength_partially_expanded_key: forall i key_chars,
  0 <= i < 7 ->
  Zlength key_chars = 32 ->
  Zlength (map Vint (pow_fun GrowKeyByOne (Z.to_nat (i * 8)) (key_bytes_to_key_words key_chars)) ++
          repeat_op_table (60 - i * 8) Vundef id) = 68.
Admitted.

Lemma update_partially_expanded_key: forall k j j' v key_chars,
(* TODO what's the value of v? *)
  j = j'+k-8 ->
  upd_Znth (j' + k) (map Vint (pow_fun GrowKeyByOne (Z.to_nat j) (key_bytes_to_key_words key_chars))
                   ++ repeat_op_table (60 - j) Vundef id) v
  = (map Vint (pow_fun GrowKeyByOne (Z.to_nat (j + 1)) (key_bytes_to_key_words key_chars))
                   ++ repeat_op_table (60 - (j + 1)) Vundef id).
Proof.
intros.
replace (j' + k) with (j + 8) by omega. clear j' H.
Admitted.

(* TODO this does not hold, we have to replace Vundef by (Vint Int.zero) in the whole proof *)
Lemma Vundef_is_Vint:
  repeat_op_table 4 Vundef id = repeat_op_table 4 (Vint Int.zero) id.
Admitted.

Definition setkey_enc_loop_body := 
(Ssequence
                    (Sset _rk0
                      (Ederef
                        (Ebinop Oadd (Etempvar _RK (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _rk7
                        (Ederef
                          (Ebinop Oadd (Etempvar _RK (tptr tuint))
                            (Econst_int (Int.repr 7) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _rcon
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                _RCON (tarray tuint 10)) (Etempvar _i tuint)
                              (tptr tuint)) tuint))
                        (Ssequence
                          (Sset _b0__1
                            (Ecast
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                    _FSb (tarray tuchar 256))
                                  (Ebinop Oand
                                    (Ebinop Oshr (Etempvar _rk7 tuint)
                                      (Econst_int (Int.repr 8) tint) tuint)
                                    (Econst_int (Int.repr 255) tint) tuint)
                                  (tptr tuchar)) tuchar) tuint))
                          (Ssequence
                            (Sset _b1__1
                              (Ecast
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                      _FSb (tarray tuchar 256))
                                    (Ebinop Oand
                                      (Ebinop Oshr (Etempvar _rk7 tuint)
                                        (Econst_int (Int.repr 16) tint)
                                        tuint)
                                      (Econst_int (Int.repr 255) tint) tuint)
                                    (tptr tuchar)) tuchar) tuint))
                            (Ssequence
                              (Sset _b2__1
                                (Ecast
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                        _FSb (tarray tuchar 256))
                                      (Ebinop Oand
                                        (Ebinop Oshr (Etempvar _rk7 tuint)
                                          (Econst_int (Int.repr 24) tint)
                                          tuint)
                                        (Econst_int (Int.repr 255) tint)
                                        tuint) (tptr tuchar)) tuchar) tuint))
                              (Ssequence
                                (Sset _b3__1
                                  (Ecast
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                          _FSb (tarray tuchar 256))
                                        (Ebinop Oand (Etempvar _rk7 tuint)
                                          (Econst_int (Int.repr 255) tint)
                                          tuint) (tptr tuchar)) tuchar)
                                    tuint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _RK (tptr tuint))
                                        (Econst_int (Int.repr 8) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oxor
                                      (Ebinop Oxor
                                        (Ebinop Oxor
                                          (Ebinop Oxor
                                            (Ebinop Oxor
                                              (Etempvar _rk0 tuint)
                                              (Etempvar _rcon tuint) tuint)
                                            (Etempvar _b0__1 tuint) tuint)
                                          (Ebinop Oshl
                                            (Etempvar _b1__1 tuint)
                                            (Econst_int (Int.repr 8) tint)
                                            tuint) tuint)
                                        (Ebinop Oshl (Etempvar _b2__1 tuint)
                                          (Econst_int (Int.repr 16) tint)
                                          tuint) tuint)
                                      (Ebinop Oshl (Etempvar _b3__1 tuint)
                                        (Econst_int (Int.repr 24) tint)
                                        tuint) tuint))
                                  (Ssequence
                                    (Sset _rk0
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _RK (tptr tuint))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _rk7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _RK (tptr tuint))
                                            (Econst_int (Int.repr 8) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _RK (tptr tuint))
                                              (Econst_int (Int.repr 9) tint)
                                              (tptr tuint)) tuint)
                                          (Ebinop Oxor (Etempvar _rk0 tuint)
                                            (Etempvar _rk7 tuint) tuint))
                                        (Ssequence
                                          (Sset _rk0
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _RK (tptr tuint))
                                                (Econst_int (Int.repr 2) tint)
                                                (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _rk7
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _RK (tptr tuint))
                                                  (Econst_int (Int.repr 9) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _RK (tptr tuint))
                                                    (Econst_int (Int.repr 10) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Oxor
                                                  (Etempvar _rk0 tuint)
                                                  (Etempvar _rk7 tuint)
                                                  tuint))
                                              (Ssequence
                                                (Sset _rk0
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _RK (tptr tuint))
                                                      (Econst_int (Int.repr 3) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _rk7
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _RK (tptr tuint))
                                                        (Econst_int (Int.repr 10) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _RK (tptr tuint))
                                                          (Econst_int (Int.repr 11) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oxor
                                                        (Etempvar _rk0 tuint)
                                                        (Etempvar _rk7 tuint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _rk0
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _RK (tptr tuint))
                                                            (Econst_int (Int.repr 4) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _rk7
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _RK (tptr tuint))
                                                              (Econst_int (Int.repr 11) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b0__1
                                                            (Ecast
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                  (Ebinop Oand
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuchar))
                                                                tuchar)
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _b1__1
                                                              (Ecast
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                  tuchar)
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _b2__1
                                                                (Ecast
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _b3__1
                                                                  (Ecast
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _b0__1 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b1__1 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b2__1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b3__1 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _rk0
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _rk7 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk0
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _rk7 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk0
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _rk7 tuint)
                                                                    tuint))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint)))))))))))))))))))))))))))))))))))).

Lemma setkey_enc_loop_body_lemma:
forall 
 (Espec : OracleKind) (ctx key : val) (ctx_sh key_sh : share) 
 (key_chars : list Z) (init_done : Z) (ish : share) (gv: globals)
 (SH : writable_share ctx_sh) (SH0 : readable_share key_sh) (SH1 : readable_share ish)
 (H : Zlength key_chars = 32) (H0 : init_done = 1) (i : Z)
 (H1 : 0 <= i < 7),
semax (func_tycontext f_mbedtls_aes_setkey_enc Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _RK
     (offset_val (i * 32) (field_address t_struct_aesctx [StructField _buf] ctx));
   gvars gv)
   SEP (field_at ctx_sh t_struct_aesctx [StructField _nr] (Vint (Int.repr 14)) ctx;
   field_at ctx_sh t_struct_aesctx [StructField _rk]
     (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
   field_at ctx_sh t_struct_aesctx [StructField _buf]
     (map Vint
        (pow_fun GrowKeyByOne (Z.to_nat (i * 8)) (key_bytes_to_key_words key_chars)) ++
      repeat_op_table (60 - i * 8) Vundef id) ctx;
   data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars)) key;
   data_at ish tint (Vint (Int.repr init_done)) (gv _aes_init_done);
   tables_initialized (gv _tables)))
  setkey_enc_loop_body
  (normal_ret_assert
     (PROP ()
      LOCAL (temp _i (Vint (Int.repr i));
      temp _RK
        (offset_val ((i + 1) * 32)
           (field_address t_struct_aesctx [StructField _buf] ctx));
      gvars gv)
      SEP (field_at ctx_sh t_struct_aesctx [StructField _nr] 
             (Vint (Int.repr 14)) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _rk]
        (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _buf]
        (map Vint
           (pow_fun GrowKeyByOne (Z.to_nat ((i + 1) * 8))
              (key_bytes_to_key_words key_chars)) ++
         repeat_op_table (60 - (i + 1) * 8) Vundef id) ctx;
      data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars))
        key; data_at ish tint (Vint (Int.repr init_done)) (gv _aes_init_done);
      tables_initialized (gv _tables)))).
Proof.
intros.
unfold setkey_enc_loop_body.
abbreviate_semax.
clearbody Delta_specs.
    assert_PROP (isptr (field_address t_struct_aesctx [StructField _buf] ctx)) as J by entailer!.
    assert (P: isptr ctx) by (apply isptr_field_address_lemma in J; destruct J as [? _]; auto).
    assert_PROP (forall j, 0 <= j < 16 -> force_val
      (sem_add_ptr_int tuint Signed (offset_val (i * 32) (field_address t_struct_aesctx [StructField _buf] ctx))
      (Vint (Int.repr j)))
      = field_address t_struct_aesctx [ArraySubsc (i*8+j); StructField _buf] ctx) as E. {
      destruct ctx; inv P.
      entailer!.
      intros j B.
      rewrite field_compatible_field_address by assumption.
      rewrite field_compatible_field_address by auto with field_compatible.
      simpl. rewrite Ptrofs.add_assoc. rewrite ptrofs_add_repr. do 4 f_equal. omega.
    }

    pose proof (Zlength_partially_expanded_key i key_chars H1 H) as L.
    pose proof (Znth_partially_expanded_key (key_bytes_to_key_words key_chars) i H1) as L'.
    set (PFUN :=pow_fun GrowKeyByOne (Z.to_nat (i * 8))
            (key_bytes_to_key_words key_chars)) in *.
    set (KE2 := KeyExpansion2 (key_bytes_to_key_words key_chars)) in *.
    freeze [0; 3; 4] FR1.
    Ltac RK_load :=
      let A := fresh "A" in let E2 := fresh "E" in
      match goal with 
        E: forall j, 0 <= j < 16 -> force_val _ = _ |- 
        semax _ _ (Ssequence (Sset _ (Ederef (Ebinop _ _ (Econst_int (Int.repr ?j) _) _) _)) _) _
       =>
        assert (0 <= j < 16) as A by computable;
        pose proof (E _ A) as E2; clear A
      end;
      forward;
      rewrite ?upd_Znth_diff by (repeat rewrite upd_Znth_Zlength; omega);
      rewrite ?upd_Znth_same by (repeat rewrite upd_Znth_Zlength; omega);
      match goal with L': forall j : Z,  0 <= j < 8 + _ * 8 -> _ |- _ => 
            rewrite ?L' by omega
      end;
    [
     go_lowerx;
     apply TT_right (*
     apply andp_right;
     [unfold tc_lvalue; simpl denote_tc_assert; unfold_lift;
      match goal with H: context [eval_id _RK] |- _ => unfold_lift in H; hnf in H; rewrite <- H end;
      apply andp_right; unfold denote_tc_isptr; apply prop_right;
      [apply isptr_offset_val'; assumption
     | unfold force_val2; rewrite E2; apply field_address_isptr; auto with field_compatible
      ]
    | apply prop_right; auto ] *)
    | ] ;
   clear E2.

(*
    Ltac RK_load E :=
      let A := fresh "A" in let E2 := fresh "E" in
      match goal with 
      |- semax _ _ (Ssequence (Sset _ (Ederef (Ebinop _ _ (Econst_int (Int.repr ?j) _) _) _)) _) _ =>
        assert (0 <= j < 16) as A by computable
      end;
      pose proof (E _ A) as E2; clear A;
      forward;
      repeat rewrite upd_Znth_diff by (repeat rewrite upd_Znth_Zlength; omega);
      repeat rewrite upd_Znth_same by (repeat rewrite upd_Znth_Zlength; omega);
      rewrite ?Znth_partially_expanded_key by omega; [ entailer! | ];
      clear E2.
*)

    Ltac RK_store :=
      let A := fresh "A" in let E2 := fresh "E" in
      match goal with
         E: forall j, 0 <= j < 16 -> force_val _ = _
        |- semax _ _ (Ssequence (Sassign (Ederef (Ebinop _ _ (Econst_int (Int.repr ?j) _) _) _) _) _) _ 
        =>
          assert (0 <= j < 16) as A by computable;
         pose proof (E _ A) as E2; clear A
      end;
      forward;
      clear E2;
      deadvars!;
      match goal with |- context [upd_Znth _ _ (Vint ?a)]  =>
          let A := fresh "A" in set (A:= Vint a) in *
      end.

    assert (Zlength RCON = 10) by reflexivity.
    pose proof masked_byte_range.

  assert (H2': forall i, 0 <= Int.unsigned (Int.and i (Int.repr 255)) < 256). {
    clear.  intros. rewrite Int.and_commut.
    pose proof (Int.and_le (Int.repr 255) i).
    rewrite Int.unsigned_repr in H by computable. 
    pose proof (Int.unsigned_range (Int.and (Int.repr 255) i)). omega.
  }

    Arguments Z.land _ _ : simpl never.
    set (ROT := repeat_op_table (60 - i * 8) Vundef id) in *.
    RK_load.
    RK_load.
    unfold tables_initialized.
    forward.
    forward. forward.
    forward. forward.
    fold (tables_initialized (gv _tables)).
    simpl.
    RK_store.
    RK_load.
    RK_load.
    RK_store.
    RK_load.
    RK_load.
    RK_store.
    RK_load.
    RK_load.
    RK_store.

    RK_load.
    RK_load.
    unfold tables_initialized.
    forward. forward.
    forward. forward.
    fold (tables_initialized (gv _tables)).
    simpl.
    RK_store.
    RK_load.
    RK_load.
    RK_store.
    RK_load.
    RK_load.
    RK_store.
    RK_load.
    RK_load.
    RK_store.

    forward. 
    destruct ctx; inv P.
    thaw FR1. 
    entailer!.
    - clear. f_equal. simpl. omega. 
    - clear.
      subst PFUN ROT KE2.
      repeat match goal with A := _ |- _ => fold A end.
      apply derives_refl'.
      f_equal.
      match goal with |- _ = ?b => set (B:=b) end.
      rewrite ?update_partially_expanded_key by omega.
      subst B. clear. 
      f_equal. f_equal. f_equal. f_equal. omega. f_equal. omega.
Time Qed.
