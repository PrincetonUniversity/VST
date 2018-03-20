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

Definition first_loop_inv00 ctx key tables aes_init_done init_done key_chars ctx_sh key_sh ish i :=
    PROP ( )
    LOCAL (
      temp _RK  (field_address t_struct_aesctx [StructField _buf] ctx);
      temp _key key; temp _keybits (Vint (Int.repr 256));
      gvar _aes_init_done aes_init_done; gvar _tables tables)
    SEP (
      field_at ctx_sh t_struct_aesctx [StructField _nr] (Vint (Int.repr 14)) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _rk] 
        (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _buf]
        (partially_filled i 68 (fun i => get_uint32_le key_chars (i*4))) ctx;
      data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars)) key;
      data_at ish tint (Vint (Int.repr init_done)) aes_init_done;
      tables_initialized tables).

Definition first_loop_inv0 ctx key tables aes_init_done init_done key_chars ctx_sh key_sh ish :=
  EX i: Z, first_loop_inv00 ctx key tables aes_init_done init_done key_chars ctx_sh key_sh ish i.

Definition main_loop_invariant0 ctx key tables ctx_sh key_sh ish key_chars aes_init_done init_done i :=
  PROP ( )
  LOCAL (
    temp _RK (offset_val (i*32) (field_address t_struct_aesctx [StructField _buf] ctx));
    gvar _tables tables
  ) SEP (
    field_at ctx_sh t_struct_aesctx [StructField _nr] (Vint (Int.repr 14)) ctx;
    field_at ctx_sh t_struct_aesctx [StructField _rk]
      (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
    field_at ctx_sh t_struct_aesctx [StructField _buf]
      (map Vint (pow_fun GrowKeyByOne (Z.to_nat (i*8)) (key_bytes_to_key_words key_chars))
      ++ repeat_op_table (60-i*8) Vundef id) ctx;
    data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars)) key;
    data_at ish tint (Vint (Int.repr init_done)) aes_init_done;
    tables_initialized tables
  ).

Definition main_loop_invariant ctx key tables ctx_sh key_sh ish key_chars aes_init_done init_done :=
  EX i: Z, main_loop_invariant0 ctx key tables ctx_sh key_sh ish key_chars aes_init_done init_done i.

Lemma Znth_partially_expanded_key: forall i j key,
  0 <= i < 7 ->
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

Lemma update_partially_expanded_key: forall j v key_chars,
(* TODO what's the value of v? *)
  upd_Znth (j + 8) (map Vint (pow_fun GrowKeyByOne (Z.to_nat j) (key_bytes_to_key_words key_chars))
                   ++ repeat_op_table (60 - j) Vundef id) v
  = (map Vint (pow_fun GrowKeyByOne (Z.to_nat (j + 1)) (key_bytes_to_key_words key_chars))
                   ++ repeat_op_table (60 - (j + 1)) Vundef id).
Admitted.

(* TODO this does not hold, we have to replace Vundef by (Vint Int.zero) in the whole proof *)
Lemma Vundef_is_Vint:
  repeat_op_table 4 Vundef id = repeat_op_table 4 (Vint Int.zero) id.
Admitted.

Lemma key_expansion_final_eq: forall key_chars,
  pow_fun GrowKeyByOne (Z.to_nat (Nb * (Nr + 2) - Nk)) (key_bytes_to_key_words key_chars)
  = KeyExpansion2 (key_bytes_to_key_words key_chars).
Proof.
  intros. unfold KeyExpansion2. reflexivity.
Qed.

Lemma body_key_expansion: semax_body Vprog Gprog f_mbedtls_aes_setkey_enc key_expansion_spec.
Proof.
  start_function.
  forward.
  match goal with
  | |- semax ?Delta (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ _ =>
    forward_if (PROPx P1 (LOCALx Q1 (SEPx R1)))
  end.
  congruence. (* then-branch: contradiction *)
  forward. entailer!. (* else-branch: Sskip *) (* TODO floyd why do I have to call entailer? *)
  (* rest: *)
  (* ctx->nr = 14; *)
  forward.  deadvars!.
  (* ctx->rk = RK = ctx->buf; *)
  forward. replace_temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx). {
    entailer!. rewrite field_compatible_field_address by auto with field_compatible. reflexivity.
  }
  forward. replace_temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx) by entailer!.
  forward.  deadvars!.
  (* first loop: *)
  forward_for_simple_bound 8 
    (first_loop_inv0 ctx key tables aes_init_done init_done key_chars ctx_sh key_sh ish).
  { (* precondition implies loop invariant: *)
    entailer!.
    unfold_data_at 1%nat. cancel. }
  { (* loop body preserves invariant: *)
    reassoc_seq.
    assert (Int.unsigned (Int.shl (Int.repr i) (Int.repr 2)) = (4 * i)%Z) as E1. {
      rewrite <- Int.mul_pow2 with (n := (Int.repr 4)) by reflexivity.
      rewrite mul_repr. rewrite Z.mul_comm. apply Int.unsigned_repr. rep_omega.
    }
    forward. 
    assert (Int.unsigned (Int.repr 1) = 1) by reflexivity.
    forward.
    assert (Int.unsigned (Int.repr 2) = 2) by reflexivity.
    forward.
    assert (Int.unsigned (Int.repr 3) = 3) by reflexivity.
    forward.

    rewrite E1, H2, H3, H4. clear H2 H3 H4.
    simpl.
    forward.
    (* assert_PROP what forward asks us to prove: *)
    assert_PROP ((if field_compatible_dec t_struct_aesctx [StructField _buf] ctx then offset_val 8 ctx
      else Vundef) = field_address t_struct_aesctx [StructField _buf] ctx) by entailer!.
    forward.
    entailer!.
    replace (4 * i)%Z with (i * 4)%Z by omega.
    assert (forall sh t gfs v1 v2 p, v1 = v2 -> field_at sh t gfs v1 p |-- field_at sh t gfs v2 p)
    as field_at_change_value. (* TODO floyd: this might be useful elsewhere *)
    { intros. replace v1 with v2 by assumption. apply derives_refl. }
    apply field_at_change_value.
    fold ((fun i0 => get_uint32_le key_chars (i0 * 4)) i).
    apply update_partially_filled. omega.
  }
  reassoc_seq.
  deadvars!.
  (* main loop: *)

  (* TODO floyd: we can only use forward_for_simple_bound because we moved the "RK += 8" from the 
     increment to the end of the loop body *)
  forward_for_simple_bound 7
    (main_loop_invariant ctx key tables ctx_sh key_sh ish key_chars aes_init_done init_done).
  { (* precondition implies loop invariant: *)
    (* TODO floyd: this should be automatic, and entailer should not clear the P I'm asserting here *)
    assert_PROP (isptr (field_address t_struct_aesctx [StructField _buf] ctx)) as P by entailer!.
    change (0 * 32)%Z with 0.
    rewrite isptr_offset_val_zero by assumption.
    entailer!. }
  { (* loop body preserves invariant: *)
    assert_PROP (forall j, 0 <= j < 16 -> force_val
      (sem_add_ptr_int tuint Signed (offset_val (i * 32) (field_address t_struct_aesctx [StructField _buf] ctx))
      (Vint (Int.repr j)))
      = field_address t_struct_aesctx [ArraySubsc (i*8+j); StructField _buf] ctx) as E. {
      assert_PROP (isptr ctx) as P by entailer!. destruct ctx; inv P.
      entailer!.
      intros j B.
      rewrite field_compatible_field_address by assumption.
      rewrite field_compatible_field_address by auto with field_compatible.
      simpl. rewrite Ptrofs.add_assoc. rewrite ptrofs_add_repr. do 4 f_equal. omega.
    }

    (* TODO floyd: In these two tactics, entailer! does not solve everything, but entailer works *)

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

    Ltac RK_store E :=
      let A := fresh "A" in let E2 := fresh "E" in
      match goal with
      |- semax _ _ (Ssequence (Sassign (Ederef (Ebinop _ _ (Econst_int (Int.repr ?j) _) _) _) _) _) _ =>
          assert (0 <= j < 16) as A by computable
      end;
      pose proof (E _ A) as E2; clear A;
      forward;
      clear E2.

    Arguments Z.land _ _ : simpl never.

    pose proof (Zlength_partially_expanded_key i key_chars H1 H) as L.

    RK_load E.
    RK_load E.
    unfold tables_initialized.
    Transparent RCON.
    assert (Zlength RCON = 10) by reflexivity.
    forward.
    pose proof masked_byte_range.
    forward. forward.
    forward. forward.
    fold (tables_initialized tables).
    simpl.
    RK_store E.  deadvars!.
    RK_load E.
    RK_load E.
    RK_store E.  deadvars!.
    RK_load E.
    RK_load E.
    RK_store E.  deadvars!.
    RK_load E.
    RK_load E.
    RK_store E.  deadvars!.

    RK_load E.
    RK_load E.
    unfold tables_initialized.
    pose proof masked_byte_range.
    forward. forward.
    forward. forward.
    fold (tables_initialized tables).
    simpl.
    RK_store E.  deadvars!.
    RK_load E.
    RK_load E.
    RK_store E.  deadvars!.
    RK_load E.
    RK_load E.
    RK_store E.  deadvars!.
    RK_load E.
    RK_load E.
    RK_store E.  deadvars!.

    forward. 
    assert_PROP (isptr ctx) as P by entailer!. destruct ctx; inv P.
    entailer!.
    - clear. f_equal. simpl. omega. 
    - clear.
      apply derives_refl'. f_equal.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 9) with (i * 8 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 10) with (i * 8 + 1 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 11) with (i * 8 + 1 + 1 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 12) with (i * 8 + 1 + 1 + 1 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 13) with (i * 8 + 1 + 1 + 1 + 1 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 14) with (i * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 15) with (i * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 8) by (clear; omega).
      rewrite update_partially_expanded_key.
      replace (i * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) with ((i + 1) * 8)%Z by (clear; omega).
      reflexivity.
  }
  (* return 0 *)
  assert ((Nb * (Nr + 2) - Nk) = 7 * 8)%Z as E by reflexivity.
  rewrite <- E.
  rewrite key_expansion_final_eq. rewrite E.
  change (60 - 7 * 8) with 4.
  forget (KeyExpansion2 (key_bytes_to_key_words key_chars)) as R.
  forward.
  rewrite Vundef_is_Vint.
  unfold_data_at 4%nat. cancel.
  Fail idtac.  (* make sure there are no subgoals *)
(* Time Qed. takes forever *)
Admitted.
