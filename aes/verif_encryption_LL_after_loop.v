Require Import aes.api_specs.
Require Import aes.bitfiddling.
Require Import aes.encryption_LL_round_step_eqs.
Open Scope Z.

(* duplicated from verif_encryption_LL_loop_body to allow make -j *)
Definition encryption_loop_body_Delta' DS :=
 (with_Delta_specs DS
   (initialized_list
     [_i; _RK; _X0; _X1; _X2; _X3; _tmp; _b0; _b1; _b2; _b3; _b0__1; _b1__1;
     _b2__1; _b3__1; _b0__2; _b1__2; _b2__2; _b3__2; _b0__3; _b1__3; _b2__3;
     _b3__3; _t'4; _t'3; _t'2; _t'1]
     (func_tycontext f_mbedtls_aes_encrypt Vprog Gprog))).

Definition encryption_after_loop : statement :=
   ltac:(find_statement_in_body
       f_mbedtls_aes_encrypt
       reassociate_stmt
       ltac:(fun body => match body with
              context [Ssequence
                     (Sloop
                       (Ssequence
                         (Sifthenelse (Ebinop Ogt (Etempvar _i _) (Econst_int (Int.repr 0) _)  _)
                             Sskip  Sbreak)
                         _) _) ?S ] => S
       end)).

Ltac simpl_upd_Znth := match goal with
| |- context [ (upd_Znth ?i ?l (Vint ?v)) ] =>
  let vv := fresh "vv" in remember v as vv;
  let a := eval cbv in (upd_Znth i l (Vint vv)) in change (upd_Znth i l (Vint vv)) with a
end.

Ltac remember_temp_Vints done :=
lazymatch goal with
| |- context [ ?T :: done ] => match T with
  | temp ?Id (Vint ?V) =>
    let V0 := fresh "V" in remember V as V0;
    remember_temp_Vints ((temp Id (Vint V0)) :: done)
  | _ => remember_temp_Vints (T :: done)
  end
| |- semax _ (PROPx _ (LOCALx done (SEPx _))) _ _ => idtac
| _ => fail 100 "assertion failure: did not find" done
end.

Lemma encryption_after_loop_proof:
forall (Espec : OracleKind) (ctx input output : val)
  (ctx_sh in_sh out_sh : share) (plaintext (*exp_key*) : list Z) (tables : val)
  (Delta_specs : PTree.t funspec)
 (H: Zlength plaintext = 16)
 (SH: readable_share ctx_sh)
 (SH0: readable_share in_sh)
 (SH1: writable_share out_sh)
 (buf : list Z)
 (Fctx: field_compatible t_struct_aesctx [StructField _buf] ctx)
 (LenBuf: Zlength buf = 68)
 (Eq: forall i : Z,
  0 <= i < 60 ->
  force_val
    (sem_add_pi tuint
       (field_address t_struct_aesctx [ArraySubsc i; StructField _buf] ctx)
       (Vint (Int.repr 1))) =
  field_address t_struct_aesctx [ArraySubsc (i + 1); StructField _buf] ctx),
  let S0 := mbed_tls_initial_add_round_key plaintext buf in
   forall (S12 : four_ints)
   (HeqS12: S12 = mbed_tls_enc_rounds 12 S0 buf 4),
semax (encryption_loop_body_Delta' Delta_specs)
  (PROP ( )
   LOCAL (temp _RK
            (field_address t_struct_aesctx [ArraySubsc 52; StructField _buf]
               ctx); temp _X3 (Vint (col 3 S12));
   temp _X2 (Vint (col 2 S12)); temp _X1 (Vint (col 1 S12));
   temp _X0 (Vint (col 0 S12)); temp _ctx ctx; temp _input input;
   temp _output output; gvar _tables tables)
   SEP (data_at_ out_sh (tarray tuchar 16) output; tables_initialized tables;
   data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
   data_at ctx_sh t_struct_aesctx 
        (Vint (Int.repr Nr),
         (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
         map Vint (map Int.repr buf)))
           ctx))
  encryption_after_loop
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP ( )
         LOCAL ()
         SEP (data_at ctx_sh t_struct_aesctx
                (Vint (Int.repr spec_utils_LL.Nr),
                (field_address t_struct_aesctx [StructField _buf] ctx,
                map Vint (map Int.repr buf))) ctx;
         data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext))
           input;
         data_at out_sh (tarray tuchar 16)
           (map Vint (mbed_tls_aes_enc plaintext buf)) output;
         tables_initialized tables))) emp).
Proof.
intros.
  unfold encryption_after_loop, encryption_loop_body_Delta'.
  abbreviate_semax.
  unfold tables_initialized.
  pose proof masked_byte_range.

  (* 2nd-to-last AES round: just a normal AES round, but not inside the loop *)
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.

  remember (mbed_tls_fround S12 buf 52) as S13.

  destruct (round13eq _ _ _ HeqS13) as [EqY0 [EqY1 [EqY2 EqY3]]].
  rewrite EqY0. rewrite EqY1. rewrite EqY2. rewrite EqY3.
  clear EqY0 EqY1 EqY2 EqY3.

  (* last AES round: special (uses S-box instead of forwarding tables) *)
  assert (forall i, Int.unsigned (Znth i FSb Int.zero) <= Byte.max_unsigned). {
    intros. pose proof (FSb_range i) as P. change 256 with (Byte.max_unsigned + 1) in P. omega.
  }

  (* We have to hide the definition of S12 and S13 for subst, because otherwise the entailer
     will substitute them and then call my_auto, which calls now, which calls easy, which calls
     inversion on a hypothesis containing the substituted S12, which takes forever, because it
     tries to simplify S12.
     TODO floyd or documentation: What should users do if "forward" takes forever? *)
  pose proof (HeqS12, HeqS13) as hidden. clear HeqS12 HeqS13.

  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.
  forward. forward. simpl (temp _RK _). rewrite Eq by computable. forward. do 4 forward. forward.

  remember (mbed_tls_final_fround S13 buf 56) as S14.

  destruct (round14eq _ _ _ HeqS14) as [EqX0 [EqX1 [EqX2 EqX3]]].
  rewrite EqX0. rewrite EqX1. rewrite EqX2. rewrite EqX3.
  clear EqX0 EqX1 EqX2 EqX3.


  remember_temp_Vints (@nil localdef).
  do 4 (forward; simpl_upd_Znth).
  do 4 (forward; simpl_upd_Znth).
  do 4 (forward; simpl_upd_Znth).
  do 4 (forward; simpl_upd_Znth).

  cbv [cast_int_int] in *.
  rewrite zero_ext_mask in *.
  rewrite zero_ext_mask in *.
  rewrite Int.and_assoc in *.
  rewrite Int.and_assoc in *.
  rewrite Int.and_idem in *.
  rewrite Int.and_idem in *.
  repeat subst.

  rewrite (final_aes_eq buf plaintext S0 S12 S13) by (destruct hidden as [? ?]; auto).

  (* TODO reuse from above *)
  assert ((field_address t_struct_aesctx [StructField _buf] ctx)
        = (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx)) as EqBuf. {
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    reflexivity.
  }
  rewrite <- EqBuf in *.
  subst POSTCONDITION; unfold abbreviate.
  forget (mbed_tls_aes_enc plaintext buf) as Res.
  unfold tables_initialized.
  (* return None *)
  forward.
  cancel.
Admitted.
(* Qed uses more than 1.2 gigs of memory, blows up on Windows *)
(* Time Qed.
   Finished transaction in 69.962 secs (57.209u,0.259s) (successful)
   In 32-bit CoqIde on Sam's Fedora Laptop, 1.2 GB of memory, Apr 12, 2017 *)
