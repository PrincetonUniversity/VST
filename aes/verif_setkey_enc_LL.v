Require Import aes.api_specs.
Require Import aes.partially_filled.
Require Import aes.bitfiddling.
Require Import aes.verif_setkey_enc_LL_loop_body.
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
    (first_loop_inv0 ctx key init_done key_chars ctx_sh key_sh ish gv).
  { (* precondition implies loop invariant: *)
    unfold first_loop_inv00.
    entailer!.
    unfold_data_at 1%nat. cancel. }
  { (* loop body preserves invariant: *)
    reassoc_seq.
    assert (Int.unsigned (Int.shl (Int.repr i) (Int.repr 2)) = (4 * i)%Z) as E1. {
      rewrite <- Int.mul_pow2 with (n := (Int.repr 4)) by reflexivity.
      rewrite mul_repr. rewrite Z.mul_comm. apply Int.unsigned_repr. rep_omega.
    }
    forward. 
    assert (Hz: 0 <= Int.unsigned (Int.add (Int.shl (Int.repr i) (Int.repr 2)) (Int.repr 1)) < Zlength key_chars). {
        rewrite H. unfold Int.add. rewrite E1.
        rewrite (Int.unsigned_repr (Z.pos _)) by computable.
        rewrite Int.unsigned_repr; [ omega | ]. rep_omega.
     }
    forward. clear Hz.
    assert (Hz: 0 <= Int.unsigned (Int.add (Int.shl (Int.repr i) (Int.repr 2)) (Int.repr 2)) < Zlength key_chars). {
        rewrite H. unfold Int.add. rewrite E1.
        rewrite (Int.unsigned_repr (Z.pos _)) by computable.
        rewrite Int.unsigned_repr; [ omega | ]. rep_omega.
     }
    forward. clear Hz.
    assert (Hz: 0 <= Int.unsigned (Int.add (Int.shl (Int.repr i) (Int.repr 2)) (Int.repr 3)) < Zlength key_chars). {
        rewrite H. unfold Int.add. rewrite E1.
        rewrite (Int.unsigned_repr (Z.pos _)) by computable.
        rewrite Int.unsigned_repr; [ omega | ]. rep_omega.
     }
    forward. clear Hz.

    rewrite E1. (*  H2, H3, H4. clear H2 H3 H4. *)
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
   rewrite <- update_partially_filled by omega. f_equal. f_equal. 
   unfold get_uint32_le. unfold Int.add. rewrite E1. 
   rewrite !(Int.unsigned_repr (Z.pos _)) by computable.
   rewrite !Int.unsigned_repr by rep_omega.
   rewrite !(Z.mul_comm 4). reflexivity.
  }
  reassoc_seq.
  deadvars!.
  (* main loop: *)

  (* TODO floyd: we can only use forward_for_simple_bound because we moved the "RK += 8" from the 
     increment to the end of the loop body *)
  forward_for_simple_bound 7
    (main_loop_invariant ctx key ctx_sh key_sh ish key_chars init_done gv).
  { (* precondition implies loop invariant: *)
    (* TODO floyd: this should be automatic, and entailer should not clear the P I'm asserting here *)
    unfold main_loop_invariant0.
    assert_PROP (isptr (field_address t_struct_aesctx [StructField _buf] ctx)) as P by entailer!.
    change (0 * 32)%Z with 0.
    rewrite isptr_offset_val_zero by assumption.
    entailer!. }
  { (* loop body preserves invariant: *)
    simple apply setkey_enc_loop_body_lemma; assumption.
  }
  clearbody Delta_specs.
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
(* Time Qed. takes forever, many minutes on a fast machine, then I gave up.  Appel, March 2018, Coq 8.7.2 *)
Admitted.
