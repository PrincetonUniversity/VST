Require Import aes.api_specs.
Require Import aes.spec_encryption_LL.
Require Import aes.bitfiddling.
Local Open Scope Z.

Definition encryption_loop_body : statement :=
   ltac:(find_statement_in_body
       f_mbedtls_aes_encrypt
       reassociate_stmt
       ltac:(fun body => match body with
              context [  Sloop
                       (Ssequence
                         (Sifthenelse (Ebinop Ogt (Etempvar _i _) (Econst_int (Int.repr 0) _)  _)
                             Sskip  Sbreak)
                       ?S) _ ] => S
      end)).

Definition encryption_loop_body_proof_statement :=
 forall
  (Espec : OracleKind)
  (ctx input output : val)
  (ctx_sh in_sh out_sh : share)
  (plaintext exp_key : list Z)
  (gv : globals)
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
       (sem_add_ptr_int tuint Signed
          (field_address t_struct_aesctx [ArraySubsc i; StructField _buf] ctx)
          (Vint (Int.repr 1))) =
     field_address t_struct_aesctx [ArraySubsc (i + 1); StructField _buf] ctx)
  (S12 S0 : four_ints)
  (HeqS0 : S0 = mbed_tls_initial_add_round_key plaintext buf)
  (HeqS12 : S12 = mbed_tls_enc_rounds 12 S0 buf 4)
  (i : Z)
  (H1 : 0 < i <= 6),
semax (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _RK
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
   temp _output output;
   gvars gv)
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
     (gv _tables);
   data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
   data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
     map Vint (map Int.repr buf))) ctx))
  encryption_loop_body
  (normal_ret_assert
     (EX a : Z,
      PROP (0 < a <= 6)
      LOCAL (temp _i (Vint (Int.repr a));
      temp _RK
        (field_address t_struct_aesctx
           [ArraySubsc (52 - (a - 1) * 8); StructField _buf] ctx);
      temp _X3
        (Vint
           (col 3 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (a - 1)) S0 buf 4)));
      temp _X2
        (Vint
           (col 2 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (a - 1)) S0 buf 4)));
      temp _X1
        (Vint
           (col 1 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (a - 1)) S0 buf 4)));
      temp _X0
        (Vint
           (col 0 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (a - 1)) S0 buf 4)));
      temp _output output; gvars gv)
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
        (gv _tables);
      data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext))
        input;
      data_at ctx_sh t_struct_aesctx
        (Vint (Int.repr Nr),
        (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
        map Vint (map Int.repr buf))) ctx))%assert).

(* previous version used loop1_ret_assert, for the same proof
Definition encryption_loop_body_proof_statement :=
 forall
  (Espec : OracleKind)
  (DS: PTree.t funspec)
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
  (S12 S0 : four_ints)
  (HeqS0 : S0 = mbed_tls_initial_add_round_key plaintext buf)
  (HeqS12 : S12 = mbed_tls_enc_rounds 12 S0 buf 4)
  (i : Z)
  (H1 : 0 < i <= 6),
semax (encryption_loop_body_Delta DS)
  (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i));
   temp _RK
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
   temp _output output;
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
  encryption_loop_body
  (loop1_ret_assert
     (EX i0 : Z,
      PROP (0 < i0 <= 6)
      LOCAL (temp _i (Vint (Int.repr i0));
      temp _RK
        (field_address t_struct_aesctx
           [ArraySubsc (52 - (i0 - 1) * 8); StructField _buf] ctx);
      temp _X3
        (Vint
           (col 3 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (i0 - 1)) S0 buf 4)));
      temp _X2
        (Vint
           (col 2 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (i0 - 1)) S0 buf 4)));
      temp _X1
        (Vint
           (col 1 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (i0 - 1)) S0 buf 4)));
      temp _X0
        (Vint
           (col 0 (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (i0 - 1)) S0 buf 4)));
      temp _output output;
      gvar _tables tables)
      SEP (data_at_ out_sh (tarray tuchar 16) output;
      tables_initialized tables;
      data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext))
        input;
      data_at ctx_sh t_struct_aesctx
        (Vint (Int.repr Nr),
        (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
        map Vint (map Int.repr buf))) ctx))%assert
     (normal_ret_assert
        (PROP ( )
         LOCAL (temp _RK
                  (field_address t_struct_aesctx
                     [ArraySubsc 52; StructField _buf] ctx);
         temp _X3 (Vint (col 3 S12)); temp _X2 (Vint (col 2 S12));
         temp _X1 (Vint (col 1 S12)); temp _X0 (Vint (col 0 S12));
         temp _output output;
         gvar _tables tables)
         SEP (data_at_ out_sh (tarray tuchar 16) output;
         tables_initialized tables;
         data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext))
           input;
         data_at ctx_sh t_struct_aesctx
           (Vint (Int.repr Nr),
           (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf]
              ctx, map Vint (map Int.repr buf))) ctx)))).*)
Hint Resolve 0%Z : inhabited.

Lemma encryption_loop_body_proof: encryption_loop_body_proof_statement.
Proof.
  unfold encryption_loop_body_proof_statement. intros.
  unfold encryption_loop_body.
  abbreviate_semax.
  pose proof masked_byte_range.
  assert (H2': forall i, 0 <= Int.unsigned (Int.and i (Int.repr 255)) < 256). {
    clear.  intros. rewrite Int.and_commut.
    pose proof (Int.and_le (Int.repr 255) i).
    rewrite Int.unsigned_repr in H by computable. 
    pose proof (Int.unsigned_range (Int.and (Int.repr 255) i)). omega.
  }

  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.
  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.
  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.
  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.

  replace (52 - i * 8 + 1 + 1 + 1 + 1) with (52 - i * 8 + 4) by omega.
  replace (52 - i * 8 + 1 + 1 + 1)     with (52 - i * 8 + 3) by omega.
  replace (52 - i * 8 + 1 + 1)         with (52 - i * 8 + 2) by omega.

  pose (S' := mbed_tls_fround (mbed_tls_enc_rounds (12-2*Z.to_nat i) S0 buf 4) buf (52-i*8)).

  match goal with |- context [temp _Y0 (Vint ?E0)] =>
    match goal with |- context [temp _Y1 (Vint ?E1)] =>
      match goal with |- context [temp _Y2 (Vint ?E2)] =>
        match goal with |- context [temp _Y3 (Vint ?E3)] =>
          assert (S' = (E0, (E1, (E2, E3)))) as Eq2
        end
      end
    end
  end.
  {
    subst S'.
    rewrite (split_four_ints (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)).
    simpl. unfold mbed_tls_fround_col, byte0, byte1, byte2, byte3, Int.and. simpl.
    rewrite !Int.unsigned_repr by computable.
    rewrite !Int.unsigned_repr by
     match goal with |- context [Z.land ?A] => clear - H2; specialize (H2 A); rep_omega end.
    reflexivity.
  }
  apply split_four_ints_eq in Eq2. destruct Eq2 as [EqY0 [EqY1 [EqY2 EqY3]]].
  rewrite EqY0. rewrite EqY1. rewrite EqY2. rewrite EqY3.
  clear EqY0 EqY1 EqY2 EqY3.

  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.
  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.
  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward. deadvars!.
  do 2 forward. simpl (temp _RK _). rewrite Eq by omega. do 6 forward.

  pose (S'' := mbed_tls_fround S' buf (52-i*8+4)).

  replace (52 - i * 8 + 4 + 1 + 1 + 1 + 1) with (52 - i * 8 + 4 + 4) by omega.
  replace (52 - i * 8 + 4 + 1 + 1 + 1)     with (52 - i * 8 + 4 + 3) by omega.
  replace (52 - i * 8 + 4 + 1 + 1)         with (52 - i * 8 + 4 + 2) by omega.

  match goal with |- context [temp _X0 (Vint ?E0)] =>
    match goal with |- context [temp _X1 (Vint ?E1)] =>
      match goal with |- context [temp _X2 (Vint ?E2)] =>
        match goal with |- context [temp _X3 (Vint ?E3)] =>
          assert (S'' = (E0, (E1, (E2, E3)))) as Eq2
        end
      end
    end
  end.
  {
    subst S''.
    rewrite (split_four_ints S').
    simpl. unfold mbed_tls_fround_col, byte0, byte1, byte2, byte3, Int.and. simpl.
    rewrite !Int.unsigned_repr by computable.
    rewrite !Int.unsigned_repr by
     match goal with |- context [Z.land ?A] => clear - H2; specialize (H2 A); rep_omega end.
    reflexivity.
  }
  apply split_four_ints_eq in Eq2. destruct Eq2 as [EqX0 [EqX1 [EqX2 EqX3]]].
  rewrite EqX0. rewrite EqX1. rewrite EqX2. rewrite EqX3.
  clear EqX0 EqX1 EqX2 EqX3.

  Exists i.
  replace (52 - i * 8 + 4 + 4) with (52 - (i - 1) * 8) by omega.
  subst S' S''.
  assert (
    (mbed_tls_fround
      (mbed_tls_fround
         (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4)
         buf
         (52 - i * 8))
      buf
      (52 - i * 8 + 4))
  = (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (i - 1)) S0 buf 4)) as Eq2. {
    replace (12 - 2 * Z.to_nat (i - 1))%nat with (S (S (12 - 2 * Z.to_nat i))).
    - unfold mbed_tls_enc_rounds (*at 2*). fold mbed_tls_enc_rounds.
      f_equal.
      * f_equal.
        rewrite Nat2Z.inj_sub. {
          change (Z.of_nat 12) with 12.
          rewrite Nat2Z.inj_mul.
          change (Z.of_nat 2) with 2.
          rewrite Z2Nat.id; omega.
        }
        assert (Z.to_nat i <= 6)%nat. {
          change 6%nat with (Z.to_nat 6).
          apply Z2Nat.inj_le; omega.
        }
        omega.
      * rewrite Nat2Z.inj_succ.
        change 2%nat with (Z.to_nat 2) at 2.
        rewrite <- Z2Nat.inj_mul; [ | omega | omega ].
        change 12%nat with (Z.to_nat 12).
        rewrite <- Z2Nat.inj_sub; [ | omega ].
        rewrite Z2Nat.id; omega.
    - rewrite Z2Nat.inj_sub; [ | omega ].
      change (Z.to_nat 1) with 1%nat.
      assert (Z.to_nat i <= 6)%nat. {
        change 6%nat with (Z.to_nat 6).
        apply Z2Nat.inj_le; omega.
      }
      assert (0 < Z.to_nat i)%nat. {
        change 0%nat with (Z.to_nat 0).
        apply Z2Nat.inj_lt; omega.
      }
      omega.
  }
  rewrite Eq2. clear Eq2.
  remember (mbed_tls_enc_rounds (12 - 2 * Z.to_nat (i - 1)) S0 buf 4) as S''.
  remember (mbed_tls_fround (mbed_tls_enc_rounds (12 - 2 * Z.to_nat i) S0 buf 4) buf (52 - i * 8)) as S'.
  replace (52 - i * 8 + 4 + 4) with (52 - (i - 1) * 8) by omega.
  entailer!.
Time Qed. 
(* On Andrew's ThinkPad T440p, April 13, 2017, to do Qed:
  With deadvar-elim:  37.6 seconds, 0.934GB
  Without deadvar-elim: 47.8 seconds, 1.073 GB
  (This computer seems to be same speed as Sam's Ubuntu laptop *)
