Require Import aes.api_specs.
Require Import aes.bitfiddling.
Require Import aes.verif_encryption_LL_loop_body.
Require Import aes.encryption_LL_round_step_eqs.
Open Scope Z.

Ltac simpl_Int := repeat match goal with
| |- context [ (Int.mul (Int.repr ?A) (Int.repr ?B)) ] =>
    let x := fresh "x" in (pose (x := (A * B)%Z)); simpl in x;
    replace (Int.mul (Int.repr A) (Int.repr B)) with (Int.repr x); subst x; [|reflexivity]
| |- context [ (Int.add (Int.repr ?A) (Int.repr ?B)) ] =>
    let x := fresh "x" in (pose (x := (A + B)%Z)); simpl in x;
    replace (Int.add (Int.repr A) (Int.repr B)) with (Int.repr x); subst x; [|reflexivity]
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

Ltac simpl_upd_Znth := match goal with
| |- context [ (upd_Znth ?i ?l (Vint ?v)) ] =>
  let vv := fresh "vv" in remember v as vv;
  let a := eval cbv in (upd_Znth i l (Vint vv)) in change (upd_Znth i l (Vint vv)) with a
end.

Lemma body_aes_encrypt: semax_body Vprog Gprog f_mbedtls_aes_encrypt encryption_spec_ll.
Proof.
  idtac "Starting body_aes_encrypt".
  start_function.
  reassoc_seq.

  (* RK = ctx->rk; *)
  forward.
  { entailer!. auto with field_compatible. (* TODO floyd: why is this not done automatically? *) }

  assert_PROP (field_compatible t_struct_aesctx [StructField _buf] ctx) as Fctx. entailer!.
  assert ((field_address t_struct_aesctx [StructField _buf] ctx)
        = (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx)) as Eq. {
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    reflexivity.
  }
  rewrite Eq in *. clear Eq.
  remember (exp_key ++ list_repeat 8 0) as buf.
  (* TODO floyd: This is important for automatic rewriting of (Znth (map Vint ...)), and if
     it's not done, the tactics might become very slow, especially if they try to simplify complex
     terms that they would never attempt to simplify if the rewriting had succeeded.
     How should the user be told to put prove such assertions before continuing? *)
  assert (Zlength buf = 68) as LenBuf. {
    subst. rewrite Zlength_app. rewrite H0. reflexivity.
  }

  assert_PROP (forall i, 0 <= i < 60 -> force_val (sem_add_pi tuint
       (field_address t_struct_aesctx [ArraySubsc  i   ; StructField _buf] ctx) (Vint (Int.repr 1)))
     = (field_address t_struct_aesctx [ArraySubsc (i+1); StructField _buf] ctx)) as Eq. {
    entailer!. intros.
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    simpl. destruct ctx; inversion PNctx; try reflexivity.
    simpl. f_equal. rewrite Int.add_assoc.
    change (Int.mul (Int.repr 4) (Int.repr 1)) with (Int.repr 4).
    rewrite add_repr. f_equal. f_equal.  clear; omega.
  }

  (* GET_UINT32_LE( X0, input,  0 ); X0 ^= *RK++;
     GET_UINT32_LE( X1, input,  4 ); X1 ^= *RK++;
     GET_UINT32_LE( X2, input,  8 ); X2 ^= *RK++;
     GET_UINT32_LE( X3, input, 12 ); X3 ^= *RK++; *)
  do 9 (forward; simpl); rewrite Eq by computable; simpl.
  do 9 (forward; simpl); rewrite Eq by computable; simpl.
  do 9 (forward; simpl); rewrite Eq by computable; simpl.
  do 9 (forward; simpl); rewrite Eq by computable; simpl.

  pose (S0 := mbed_tls_initial_add_round_key plaintext buf).
  match goal with |- context [temp _X0 (Vint ?E)] => change E with (col 0 S0) end.
  match goal with |- context [temp _X1 (Vint ?E)] => change E with (col 1 S0) end.
  match goal with |- context [temp _X2 (Vint ?E)] => change E with (col 2 S0) end.
  match goal with |- context [temp _X3 (Vint ?E)] => change E with (col 3 S0) end.

  forward. unfold Sfor. forward.

  (* ugly hack to avoid type mismatch between
   "(val * (val * list val))%type" and "reptype t_struct_aesctx" *)
  assert (exists (v: reptype t_struct_aesctx), v =
       (Vint (Int.repr Nr),
          (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
          map Vint (map Int.repr buf))))
  as EE by (eexists; reflexivity).

  destruct EE as [vv EE].

  remember (mbed_tls_enc_rounds 12 S0 buf 4) as S12.

  apply semax_pre with (P' := 
  (EX i: Z, PROP ( 
     0 <= i <= 6
  ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc (52 - i*8); StructField _buf] ctx);
     temp _X3 (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X2 (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X1 (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X0 (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx
  ))).
  { subst vv. Exists 6. entailer!. }

  eapply semax_seq' with (P' :=
  PROP ( )
  LOCAL (
     temp _RK (field_address t_struct_aesctx [ArraySubsc 52; StructField _buf] ctx);
     temp _X3 (Vint (col 3 S12));
     temp _X2 (Vint (col 2 S12));
     temp _X1 (Vint (col 1 S12));
     temp _X0 (Vint (col 0 S12));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx 
  )).
  { apply semax_loop with (
  (EX i: Z, PROP ( 
     0 < i <= 6
  ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc (52 - (i-1)*8); StructField _buf] ctx);
     temp _X3 (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _X2 (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _X1 (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _X0 (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx
  ))).
  { (* loop body *) 
  Intro i.
  reassoc_seq.

  forward_if
  (EX i: Z, PROP ( 
     0 < i <= 6
  ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc (52 - i*8); StructField _buf] ctx);
     temp _X3 (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X2 (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X1 (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X0 (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx
  )).
  { (* then-branch: Sskip to body *)
  Intros. forward. Exists i.
  rewrite Int.signed_repr in *; [ | repable_signed ]. (* TODO floyd why is this not automatic? *)
  entailer!.
  }
  { (* else-branch: exit loop *)
  Intros.
  rewrite Int.signed_repr in *; [ | repable_signed ]. (* TODO floyd why is this not automatic? *)
  forward. assert (i = 0) by omega. subst i.
  change (52 - 0 * 8) with 52.
  change (12 - 2 * Z.to_nat 0)%nat with 12%nat.
  replace (mbed_tls_enc_rounds 12 S0 buf 4) with S12 by reflexivity. (* interestingly, if we use
     "change" instead of "replace", it takes much longer *)
  entailer!.
  }
  { (* rest: loop body *)
  clear i. Intro i. Intros. 
  unfold tables_initialized. subst vv.
  subst MORE_COMMANDS POSTCONDITION. unfold abbreviate.
  change Delta with (encryption_loop_body_Delta Delta_specs).
  simple eapply encryption_loop_body_proof; eauto.
  }} { (* loop decr *)
  Intro i. forward. unfold loop2_ret_assert. Exists (i-1). entailer!.
  }} {
  abbreviate_semax. subst vv. unfold tables_initialized.
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

  Ltac entailer_for_load_tac ::= idtac.

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
  repeat subst. remember (exp_key ++ list_repeat 8 0) as buf.

  rewrite (final_aes_eq buf plaintext S0 S12 S13) by (destruct hidden as [? ?]; auto).

  Ltac entailer_for_return ::= idtac.

  (* TODO reuse from above *)
  assert ((field_address t_struct_aesctx [StructField _buf] ctx)
        = (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx)) as EqBuf. {
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    reflexivity.
  }
  rewrite <- EqBuf in *.

  (* return None *)
  forward.
  remember (mbed_tls_aes_enc plaintext buf) as Res.
  unfold tables_initialized.
  entailer!.
  }
(* Time Qed.
   In 32-bit CoqIde on Andrew's Windows laptop:  runs out of memory 
   In 32-bit CoqIde on Sam's laptop:
      Finished transaction in 97.856 secs (81.632u,0.332s) (successful) *)
Admitted.

(* TODO floyd: sc_new_instantiate: distinguish between errors caused because the tactic is trying th
   wrong thing and errors because of user type errors such as "tuint does not equal t_struct_aesctx" *)

(* TODO floyd: compute_nested_efield should not fail silently *)

(* TODO floyd: if field_address is given a gfs which doesn't match t, it should not fail silently,
   or at least, the tactics should warn.
   And same for nested_field_offset. *)

(* TODO floyd: I want "omega" for int instead of Z
   maybe "autorewrite with entailer_rewrite in *"
*)

(* TODO floyd: when load_tac should tell that it cannot handle memory access in subexpressions *)

(* TODO floyd: for each tactic, test how it fails when variables are missing in Pre *)

(*
Note:
field_compatible/0 -> legal_nested_field/0 -> legal_field/0:
  legal_field0 allows an array index to point 1 past the last array cell, legal_field disallows this
*)
