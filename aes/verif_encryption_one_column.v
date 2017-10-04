Require Import aes.api_specs.
Require Import aes.bitfiddling.
Open Scope Z.

Definition round_column_ast rk b0 b1 b2 b3 t Y X0 X1 X2 X3 := 
(Ssequence (Sset t (Etempvar _RK (tptr tuint)))
   (Ssequence
      (Sset _RK
         (Ebinop Oadd (Etempvar t (tptr tuint))
            (Econst_int (Int.repr 1) tint) (tptr tuint)))
      (Ssequence (Sset rk (Ederef (Etempvar t (tptr tuint)) tuint))
         (Ssequence
            (Sset b0
               (Ederef
                  (Ebinop Oadd
                     (Efield
                        (Evar _tables t_struct_tables)
                        _FT0 (tarray tuint 256))
                     (Ebinop Oand (Etempvar X0 tuint)
                        (Econst_int (Int.repr 255) tint) tuint) (tptr tuint))
                  tuint))
            (Ssequence
               (Sset b1
                  (Ederef
                     (Ebinop Oadd
                        (Efield
                           (Evar _tables t_struct_tables)
                           _FT1 (tarray tuint 256))
                        (Ebinop Oand
                           (Ebinop Oshr (Etempvar X1 tuint)
                              (Econst_int (Int.repr 8) tint) tuint)
                           (Econst_int (Int.repr 255) tint) tuint)
                        (tptr tuint)) tuint))
               (Ssequence
                  (Sset b2
                     (Ederef
                        (Ebinop Oadd
                           (Efield
                              (Evar _tables
                                 t_struct_tables) _FT2
                              (tarray tuint 256))
                           (Ebinop Oand
                              (Ebinop Oshr (Etempvar X2 tuint)
                                 (Econst_int (Int.repr 16) tint) tuint)
                              (Econst_int (Int.repr 255) tint) tuint)
                           (tptr tuint)) tuint))
                  (Ssequence
                     (Sset b3
                        (Ederef
                           (Ebinop Oadd
                              (Efield
                                 (Evar _tables
                                    t_struct_tables) _FT3
                                 (tarray tuint 256))
                              (Ebinop Oand
                                 (Ebinop Oshr (Etempvar X3 tuint)
                                    (Econst_int (Int.repr 24) tint) tuint)
                                 (Econst_int (Int.repr 255) tint) tuint)
                              (tptr tuint)) tuint))
                     (Sset Y
                        (Ebinop Oxor
                           (Ebinop Oxor
                              (Ebinop Oxor
                                 (Ebinop Oxor (Etempvar rk tuint)
                                    (Etempvar b0 tuint) tuint)
                                 (Etempvar b1 tuint) tuint)
                              (Etempvar b2 tuint) tuint)
                           (Etempvar b3 tuint) tuint))))))))).

Axiom Test: forall (P: Prop), P.

Lemma encryption_loop_body_proof: forall
  (Espec : OracleKind)
  (ctx input output : val)
  (ctx_sh in_sh out_sh : share)
  (plaintext exp_key : list Z)
  (tables : val)
  (H : Zlength plaintext = 16)
  (H0 : Zlength exp_key = 60)
  (SH : readable_share ctx_sh)
  (SH0 : readable_share in_sh)
  (SH1 : writable_share out_sh)
  (buf : list Z)
  (Heqbuf : buf = exp_key ++ list_repeat 8 0)
  (Fctx : field_compatible t_struct_aesctx [StructField _buf] ctx)
  (LenBuf : Zlength buf = 68)
  (Eq : forall i : Z,
     0 <= i < 60 ->
     force_val
       (sem_add_pi tuint
          (field_address t_struct_aesctx [ArraySubsc i; StructField _buf] ctx)
          (Vint (Int.repr 1))) =
     field_address t_struct_aesctx [ArraySubsc (i + 1); StructField _buf] ctx)
  (S0 S' : four_ints)
  (i : Z)
  (H1 : 0 < i <= 6)
  (HeqS0 : S0 = mbed_tls_initial_add_round_key plaintext buf)
  (HeqS' : S' = mbed_tls_fround (mbed_tls_enc_rounds (12-2*Z.to_nat i) S0 buf 4) buf (52-i*8)),
semax
  (initialized_list
     [_i; _RK; _X0; _X1; _X2; _X3; _tmp; _b0; _b1; _b2; _b3; _b0__1; _b1__1;
     _b2__1; _b3__1; _b0__2; _b1__2; _b2__2; _b3__2; _b0__3; _b1__3; _b2__3;
     _b3__3; _t'4; _t'3; _t'2; _t'1]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))
  (PROP ( )
   LOCAL (temp _RK
            (field_address t_struct_aesctx
               [ArraySubsc (52 - i * 8); StructField _buf] ctx);
   temp _X3
     (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
   temp _X2
     (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
   temp _X1
     (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
   temp _X0
     (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
   gvar _tables tables)
   SEP (data_at_ out_sh (tarray tuchar 16) output;
   data_at Ews t_struct_tables
     (map Vint FSb,
     (map Vint FT0,
     (map Vint FT1,
     (map Vint FT2,
     (map Vint FT3,
     (map Vint RSb,
     (map Vint RT0,
     (map Vint RT1, (map Vint RT2, (map Vint RT3, map Vint RCON))))))))))
     tables;
   data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
   data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
     map Vint (map Int.repr buf))) ctx))
  (round_column_ast _rk _b0__4 _b1__4 _b2__4 _b3__4 _t'5 _Y0 _X0 _X1 _X2 _X3)
  (normal_ret_assert (PROP ( )
  LOCAL (
    temp _Y0 (Vint (col 0 S'));
    temp _RK (field_address t_struct_aesctx [ArraySubsc (52 - i * 8 + 1); StructField _buf] ctx);
    temp _X3 (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
    temp _X2 (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
    temp _X1 (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
    temp _X0 (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)));
    gvar _tables tables
  ) SEP (
    data_at_ out_sh (tarray tuchar 16) output;
    data_at Ews t_struct_tables
      (map Vint FSb,
      (map Vint FT0,
      (map Vint FT1,
      (map Vint FT2,
      (map Vint FT3,
      (map Vint RSb,
      (map Vint RT0,
      (map Vint RT1, (map Vint RT2, (map Vint RT3, map Vint RCON)))))))))) tables;
    data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
    data_at ctx_sh t_struct_aesctx
      (Vint (Int.repr Nr),
      (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
      map Vint (map Int.repr buf))) ctx
   ))).
Proof.
  intros. unfold round_column_ast.
  forward.
  apply Test.
Time Qed. (* This takes >10min! (I've never seen it finish) *)

(* rest of the proof:
  pose proof masked_byte_range.
  forward. simpl (temp _RK _). rewrite Eq by omega. forward. do 4 forward. forward.

  match goal with |- context [temp _Y0 (Vint ?E0)] =>
    assert (col 0 S' = E0) as Eq2
  end.
  {
    subst S'.
    rewrite (split_four_ints (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)).
    reflexivity.
  }
  rewrite <- Eq2.
  entailer!.
Time Qed.
*)
