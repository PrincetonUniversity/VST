Require Import aes.api_specs.
Require Import aes.bitfiddling.
Require Import aes.encryption_LL_round_step_eqs.
Require Import aes.verif_encryption_LL_loop_body.
Require Import aes.verif_encryption_LL_after_loop.
Open Scope Z.

Lemma body_aes_encrypt: semax_body Vprog Gprog f_mbedtls_aes_encrypt encryption_spec_ll.
Proof.
  idtac "Starting body_aes_encrypt".
  function_pointers.  (* This is a temporary expedient.  It signals to start_function
                                  NOT to clearbody Delta_specs, so that the 
                                  [eapply encryption_loop_body_proof] works. *)
  start_function.
  Opaque list_repeat.
  simpl.
  Transparent list_repeat.
  reassoc_seq.

  (* RK = ctx->rk; *)
  forward.
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

  assert_PROP (forall i, 0 <= i < 60 -> force_val (sem_add_ptr_int tuint Signed
       (field_address t_struct_aesctx [ArraySubsc  i   ; StructField _buf] ctx) (Vint (Int.repr 1)))
     = (field_address t_struct_aesctx [ArraySubsc (i+1); StructField _buf] ctx)) as Eq. {
    entailer!. intros.
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    simpl. destruct ctx; inversion PNctx; try reflexivity.
    simpl. f_equal. rewrite Ptrofs.add_assoc.
    change (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr 1))) with (Ptrofs.repr 4).
    rewrite ptrofs_add_repr. f_equal. f_equal.  clear; omega.
  }

  (* GET_UINT32_LE( X0, input,  0 ); X0 ^= *RK++;
     GET_UINT32_LE( X1, input,  4 ); X1 ^= *RK++;
     GET_UINT32_LE( X2, input,  8 ); X2 ^= *RK++;
     GET_UINT32_LE( X3, input, 12 ); X3 ^= *RK++; *)
  do 9 (forward; simpl); rewrite Eq by computable; simpl. deadvars!.
  do 9 (forward; simpl); rewrite Eq by computable; simpl. deadvars!.
  do 9 (forward; simpl); rewrite Eq by computable; simpl. deadvars!.
  do 9 (forward; simpl); rewrite Eq by computable; simpl. deadvars!.

  pose (S0 := mbed_tls_initial_add_round_key plaintext buf).
  match goal with |- context [temp _X0 (Vint ?E)] => change E with (col 0 S0) end.
  match goal with |- context [temp _X1 (Vint ?E)] => change E with (col 1 S0) end.
  match goal with |- context [temp _X2 (Vint ?E)] => change E with (col 2 S0) end.
  match goal with |- context [temp _X3 (Vint ?E)] => change E with (col 3 S0) end.

  forward. 
  (* ugly hack to avoid type mismatch between
   "(val * (val * list val))%type" and "reptype t_struct_aesctx" *)
  assert (exists (v: reptype t_struct_aesctx), v =
       (Vint (Int.repr Nr),
          (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
          map Vint (map Int.repr buf))))
  as EE by (eexists; reflexivity).

  destruct EE as [vv EE].
  remember (mbed_tls_enc_rounds 12 S0 buf 4) as S12.

  forward_for 
  (* Loop Invariant *)  
  (fun i:Z => PROP ( 
     0 <= i <= 6
   ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc (52 - i*8); StructField _buf] ctx);
     temp _X3 (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X2 (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X1 (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _X0 (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat i)) S0 buf 4)));
     temp _output output;
     gvars gv
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized (gv _tables);
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx
  ))
  continue: (* PreInc invariant *)
   (fun i: Z => PROP ( 
     0 < i <= 6
  ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc (52 - (i-1)*8); StructField _buf] ctx);
     temp _X3 (Vint (col 3 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _X2 (Vint (col 2 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _X1 (Vint (col 1 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _X0 (Vint (col 0 (mbed_tls_enc_rounds (12 - 2 * (Z.to_nat (i-1))) S0 buf 4)));
     temp _output output;
     gvars gv
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized (gv _tables);
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx
  ))
  break: (* Loop postcondition *)
   (PROP() LOCAL (
     temp _RK (field_address t_struct_aesctx [ArraySubsc 52; StructField _buf] ctx);
     temp _X3 (Vint (col 3 S12));
     temp _X2 (Vint (col 2 S12));
     temp _X1 (Vint (col 1 S12));
     temp _X0 (Vint (col 0 S12));
     temp _output output;
     gvars gv
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized (gv _tables);
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx 
  )).
* (* initializer establishes loop invariant *)
 forward. Exists 6. entailer!.
* (* loop-test typechecks *)
 entailer!.
* (*  loop body *)
  rename a into i.
  assert (0 < i <= 6) by (clear - H1 H2; omega).
  unfold tables_initialized. subst vv.
  reassoc_seq.
  eapply encryption_loop_body_proof; eauto.
  (* the next few lines should not be necessary if the statement
    of encryption_loop_body_proof is adjusted. 
  clear. 
  intros. match goal with |- 
     context [loop1_ret_assert ?PP (normal_ret_assert ?QQ)] =>
     set (P:=PP); set (Q := QQ)
   end.
  apply andp_left2.
  unfold loop1_ret_assert, normal_ret_assert, overridePost; destruct ek; auto.
  rewrite if_true by auto. rewrite !prop_true_andp by auto.
  subst Q. solve [auto].
  apply derives_extract_prop; intro Hx; inv Hx.*)
* (* loop decr *)
  rename a into i. forward. Exists (i-1). entailer!.
* (* after the loop, entailment *)
 assert (a=0) by omega. clear H1 H2; subst a.
 change (12 - 2 * Z.to_nat 0)%nat with 12%nat. 
 rewrite <- HeqS12.
 change (52 - 0 * 8) with 52. 
 clear. entailer!.
* (** AFTER THE LOOP **)
subst vv.
eapply encryption_after_loop_proof; eassumption.
Time Qed. (* 9.2 secs on Andrew's machine *)

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
