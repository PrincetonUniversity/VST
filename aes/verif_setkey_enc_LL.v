Require Import aes.verif_utils.
Require Import aes.spec_utils_LL. (* TODO write & import LL spec of key expansion *)

Local Open Scope logic.

Definition word_to_int (w : (int * int * int * int)) : int :=
  match w with (b0, b1, b2, b3) =>
    (Int.or (Int.or (Int.or
             b0
    (Int.shl b1 (Int.repr  8)))
    (Int.shl b2 (Int.repr 16)))
    (Int.shl b3 (Int.repr 24)))
  end.

(* SubWord function from section 5.2: apply S-box to each byte in a word *)
Definition SubWord (w: int) : int := word_to_int (
  (Znth (byte0 w) FSb Int.zero),
  (Znth (byte1 w) FSb Int.zero),
  (Znth (byte2 w) FSb Int.zero),
  (Znth (byte3 w) FSb Int.zero)
).

Definition RotWord(i: int): int := 
  Int.or (Int.and (Int.shl i (Int.repr 8)) (Int.repr (-1))) (Int.shru i (Int.repr 24)).

(* round constant (RCon) array, described in section 5.2 and explicitly written
 * out in appendix A.3 (256-bit key expansion example) *)
Definition RCon : list int := map (fun i => Int.shl i (Int.repr 24)) [
  (* 0x01000000 *) (Int.repr 1);
  (* 0x02000000 *) (Int.repr 2);
  (* 0x04000000 *) (Int.repr 4);
  (* 0x08000000 *) (Int.repr 8);
  (* 0x10000000 *) (Int.repr 16);
  (* 0x20000000 *) (Int.repr 32);
  (* 0x40000000 *) (Int.repr 64)
].

Definition GrowKeyByOne(w: list int): list int :=
  let i := Zlength w in
  let temp := (Znth (i-1) w Int.zero) in
  let temp' := if (i mod Nk =? 0) then
    Int.xor (SubWord (RotWord temp)) (Znth (i/Nk) RCon Int.zero)
  else if (i mod Nk =? 4) then
    SubWord temp
  else
    temp
  in
    w ++ [Int.xor (Znth (i-8) w Int.zero) temp'].

Fixpoint pow_fun{T: Type}(f: T -> T)(n: nat)(a: T): T := match n with
| O => a
| S m => f (pow_fun f m a)
end.

(* +2 because 1 is for the initial round which is not counted, and 1 superfluous round key is
   created in the last loop iteration, because each iteration creates 2 round keys.
   -Nk because the first two round keys are just the unexpanded key.
  Note that (Nb*(Nr+2)-Nk) = 56. *)
Definition KeyExpansion: list int -> list int := pow_fun GrowKeyByOne (Z.to_nat (Nb*(Nr+2)-Nk)).

(* arr: list of bytes *)
Definition get_uint32_le (arr: list Z) (i: Z) : int :=
 (Int.or (Int.or (Int.or
            (Int.repr (Znth  i    arr 0))
   (Int.shl (Int.repr (Znth (i+1) arr 0)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth (i+2) arr 0)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth (i+3) arr 0)) (Int.repr 24))).

Definition partially_filled(i n: Z)(f: Z -> int): list val := 
  (map Vint (fill_list i f)) ++ (repeat_op_table (n-i) Vundef id).

Lemma update_partially_filled: forall (i: Z) (n: Z) (f: Z -> int),
  0 <= i < n ->
  upd_Znth i (partially_filled i n f) (Vint (f i))
  = partially_filled (i+1) n f.
Admitted.

Lemma Znth_partially_filled: forall (i j n: Z) (f: Z -> int),
  0 <= i -> i < j -> j <= n ->
  Znth i (partially_filled j n f) Vundef = Vint (f i).
Admitted.

Definition key_bytes_to_key_words(key_bytes: list Z): list int := 
  fill_list 8 (fun i => get_uint32_le key_bytes (i*4)).

(*
Definition append_4_bytes_as_word(bytes: list Z)(words: list int): list int :=
  let i := Zlength words in
  words ++ [get_uint32_le bytes (i*4)].

Definition key_bytes_to_key_words(key_bytes: list Z): list int := 
  pow_fun (append_4_bytes_as_word key_bytes) 8%nat [].
*)

(* Note: clightgen turns global variables of type int to pointers to int, to make them addressable,
   so aes_init_done is a pointer to int, not an int! *)
Definition key_expansion_spec :=
  DECLARE _mbedtls_aes_setkey_enc
    WITH ctx : val, key : val, ctx_sh : share, key_sh : share, key_chars : list Z,
         tables : val, aes_init_done: val, init_done : Z, ish: share
    PRE [ _ctx OF (tptr t_struct_aesctx), _key OF (tptr tuchar), _keybits OF tuint  ]
      PROP (writable_share ctx_sh; readable_share key_sh; readable_share ish;
            Zlength key_chars = 32;
            init_done = 1 (*TODO also prove case where init_done=0*))
      LOCAL (temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256)); 
             gvar _aes_init_done aes_init_done;
             gvar _tables tables)
      SEP (data_at ctx_sh t_struct_aesctx 
                   (Vint Int.zero,
                   (nullval, 
                   (map Vint (repeat_op_table 68 Int.zero id)))) ctx;
           data_at key_sh (tarray tuchar (4*8)) (map Vint (map Int.repr key_chars)) key;
           (*if init_done ?= 1 then tables_initialized tables else tables_uninitialized tables*)
           data_at ish tint (Vint (Int.repr init_done)) aes_init_done;
           tables_initialized tables)
    POST [  tint ]
      PROP () 
      LOCAL (temp ret_temp (Vint Int.zero))
      SEP (data_at key_sh (tarray tuchar (4*8)) (map Vint (map Int.repr key_chars)) key;
           data_at ctx_sh t_struct_aesctx 
                   (Vint (Int.repr 14),
                   ((field_address t_struct_aesctx [StructField _buf] ctx), 
                   (map Vint (KeyExpansion (key_bytes_to_key_words key_chars))
                    ++ (repeat_op_table 4 (Vint Int.zero) id)))) ctx;
           data_at ish tint (Vint (Int.repr init_done)) aes_init_done;
           tables_initialized tables).

Definition Gprog : funspecs := ltac:(with_library prog [ key_expansion_spec ]).

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
      temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx);
      temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256));
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
    temp _ctx ctx;
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
           ++ repeat_op_table (60 - i * 8) Vundef id) Vundef)
  = Vint (Znth j (KeyExpansion key) Int.zero).
Admitted.

Lemma Zlength_partially_expanded_key: forall i key_chars,
  0 <= i < 7 ->
  Zlength key_chars = 32 ->
  Zlength (map Vint (pow_fun GrowKeyByOne (Z.to_nat (i * 8)) (key_bytes_to_key_words key_chars)) ++
          repeat_op_table (60 - i * 8) Vundef id) = 68.
Admitted.

Lemma masked_byte_range: forall i,
  0 <= Z.land i 255 < 256.
Admitted.

Lemma body_key_expansion: semax_body Vprog Gprog f_mbedtls_aes_setkey_enc key_expansion_spec.
Proof.
  start_function.
  forward.
  match goal with
  | |- semax ?Delta (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ _ =>
    forward_if (PROPx P1 (LOCALx Q1 (SEPx R1)))
  end.
  omega. (* then-branch: contradiction *)
  forward. entailer!. (* else-branch: Sskip *) (* TODO floyd why do I have to call entailer? *)
  (* rest: *)
  (* ctx->nr = 14; *)
  forward.
  (* ctx->rk = RK = ctx->buf; *)
  forward. replace_temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx). {
    entailer!. rewrite field_compatible_field_address by auto with field_compatible. reflexivity.
  }
  forward. replace_temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx) by entailer!.
  forward.
  (* first loop: *)
  forward_for_simple_bound 8 
    (first_loop_inv0 ctx key tables aes_init_done init_done key_chars ctx_sh key_sh ish).
  { (* precondition implies loop invariant: *)
    entailer!.
    unfold_field_at 1%nat. entailer!. }
  { (* loop body preserves invariant: *)
    reassoc_seq.
    assert (Int.unsigned (Int.shl (Int.repr i) (Int.repr 2)) = (4 * i)%Z) as E1. {
      rewrite <- Int.mul_pow2 with (n := (Int.repr 4)) by reflexivity.
      rewrite mul_repr. rewrite Z.mul_comm. apply Int.unsigned_repr. repable_signed.
    }
    forward.
    assert (Int.unsigned (Int.repr 1) = 1) by (apply Int.unsigned_repr; repable_signed).
    forward.
    assert (Int.unsigned (Int.repr 2) = 2) by (apply Int.unsigned_repr; repable_signed).
    forward.
    assert (Int.unsigned (Int.repr 3) = 3) by (apply Int.unsigned_repr; repable_signed).
    forward.
    rewrite E1. rewrite H2, H3, H4. clear H2 H3 H4.
    simpl.
    forward.
    (* assert_PROP what forward asks us to prove: *)
    assert_PROP ((if field_compatible_dec t_struct_aesctx [StructField _buf] ctx then offset_val 8 ctx
      else Vundef) = field_address t_struct_aesctx [StructField _buf] ctx) by entailer!.
    forward.
    entailer!.
    replace (4 * i)%Z with (i * 4)%Z by omega.
    fold ((fun i0 => get_uint32_le key_chars (i0 * 4)) i).
    rewrite update_partially_filled by omega.
    apply derives_refl.
  }
  reassoc_seq.
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
      (sem_add_pi tuint (offset_val (i * 32) (field_address t_struct_aesctx [StructField _buf] ctx))
      (Vint (Int.repr j)))
      = field_address t_struct_aesctx [ArraySubsc (i*8+j); StructField _buf] ctx) as E. {
      assert_PROP (isptr ctx) as P by entailer!. destruct ctx; inv P.
      entailer!.
      intros j B.
      rewrite field_compatible_field_address by assumption.
      rewrite field_compatible_field_address by auto with field_compatible.
      simpl. rewrite Int.add_assoc. rewrite add_repr. do 4 f_equal. omega.
    }

    (* TODO floyd: In these two tactics, entailer! does not solve everything, but entailer works *)

    Ltac RK_load E j :=
      let A := fresh "A" in let E2 := fresh "E" in
      assert (0 <= j < 16) as A by omega;
      pose proof (E _ A) as E2; clear A;
      forward;
      repeat rewrite upd_Znth_diff by (repeat rewrite upd_Znth_Zlength; omega);
      repeat rewrite upd_Znth_same by (repeat rewrite upd_Znth_Zlength; omega);
      rewrite ?Znth_partially_expanded_key by omega; [ entailer | ];
      clear E2.

    Ltac RK_store E j :=
      let A := fresh "A" in let E2 := fresh "E" in
      assert (0 <= j < 16) as A by omega;
      pose proof (E _ A) as E2; clear A;
      forward; [ entailer | ];
      clear E2.

    Arguments Z.land _ _ : simpl never.

    pose proof (Zlength_partially_expanded_key i key_chars) as L.
    spec L; [ omega | ]. spec L; [ assumption | ].

    RK_load E 0.
    RK_load E 7.
    unfold tables_initialized.
    Transparent RCON.
    assert (Zlength RCON = 10) by reflexivity.
    forward.
    pose proof masked_byte_range.
    forward. forward.
    forward. forward.
    fold (tables_initialized tables).
    simpl.
    RK_store E 8.
    RK_load E 1.
    RK_load E 8.
    RK_store E 9.
    RK_load E 2.
    RK_load E 9.
    RK_store E 10.
    RK_load E 3.
    RK_load E 10.
    RK_store E 11.

    RK_load E 4.
    RK_load E 11.
    unfold tables_initialized.
    pose proof masked_byte_range.
    forward. forward.
    forward. forward.
    fold (tables_initialized tables).
    simpl.
    RK_store E 12.
    RK_load E 5.
    RK_load E 12.
    RK_store E 13.
    RK_load E 6.
    RK_load E 13.
    RK_store E 14.
    RK_load E 7.
    RK_load E 14.
    RK_store E 15.

    forward. {
      entailer.
    }
    assert_PROP (isptr ctx) as P by entailer!. destruct ctx; inv P.
    entailer!.
    - simpl. rewrite E by omega.
      rewrite field_compatible_field_address by assumption.
      rewrite field_compatible_field_address by auto with field_compatible.
      simpl. rewrite Int.add_assoc. do 2 f_equal. rewrite add_repr. f_equal. omega.
    - clear H10.

Lemma update_partially_expanded_key: forall j v key_chars,
(* TODO what's the value of v? *)
  upd_Znth (j + 8) (map Vint (pow_fun GrowKeyByOne (Z.to_nat j) (key_bytes_to_key_words key_chars))
                   ++ repeat_op_table (60 - j) Vundef id) v
  = (map Vint (pow_fun GrowKeyByOne (Z.to_nat (j + 1)) (key_bytes_to_key_words key_chars))
                   ++ repeat_op_table (60 - (j + 1)) Vundef id).
Admitted.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 9) with (i * 8 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 10) with (i * 8 + 1 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 11) with (i * 8 + 1 + 1 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 12) with (i * 8 + 1 + 1 + 1 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 13) with (i * 8 + 1 + 1 + 1 + 1 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 14) with (i * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 15) with (i * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 8) by omega.
      rewrite update_partially_expanded_key.
      replace (i * 8 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) with ((i + 1) * 8)%Z by omega.
      apply derives_refl.
  }
  (* return 0 *)
  assert ((Nb * (Nr + 2) - Nk) = 7 * 8)%Z as E by reflexivity.
  rewrite <- E.
  progress fold (KeyExpansion (key_bytes_to_key_words key_chars)).
  rewrite E. clear E. change (60 - 7 * 8) with 4.
  forget (KeyExpansion (key_bytes_to_key_words key_chars)) as R.
  forward.
(* TODO this does not hold, we have to replace Vundef by (Vint Int.zero) in the whole proof *)
Lemma Vundef_is_Vint:
  repeat_op_table 4 Vundef id = repeat_op_table 4 (Vint Int.zero) id.
Admitted.
  rewrite Vundef_is_Vint.
  unfold_data_at 4%nat. entailer!.
Time Qed. (* takes too long, using 25% CPU only *)
