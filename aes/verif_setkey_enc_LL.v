Require Import floyd.proofauto.
Require Import floyd.reassoc_seq.
Require Import aes.GF_ops_LL.
Require Import aes.tablesLL.
Require Import aes.aes.

Local Open Scope logic.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_struct_aesctx := Tstruct _mbedtls_aes_context_struct noattr.
Definition t_struct_tables := Tstruct _aes_tables_struct noattr.

Definition tables_initialized (tables : val) := data_at Ews t_struct_tables (map Vint FSb, 
  (map Vint FT0, (map Vint FT1, (map Vint FT2, (map Vint FT3, (map Vint RSb,
  (map Vint RT0, (map Vint RT1, (map Vint RT2, (map Vint RT3, 
  (map Vint RCON))))))))))) tables.

Definition Vundef256 : list val := repeat Vundef 256%nat.

Definition tables_uninitialized tables := data_at Ews t_struct_tables (Vundef256, 
  (Vundef256, (Vundef256, (Vundef256, (Vundef256, (Vundef256,
  (Vundef256, (Vundef256, (Vundef256, (Vundef256, 
  (repeat Vundef 10))))))))))) tables.

Definition key_expansion_spec :=
  DECLARE _mbedtls_aes_setkey_enc
    WITH ctx : val, key : val, ctx_sh : share, key_sh : share, key_chars : list Z,
         tables : val, init_done : Z
    PRE [ _ctx OF (tptr t_struct_aesctx), _key OF (tptr tuchar), _keybits OF tuint  ]
      PROP (writable_share ctx_sh; readable_share key_sh;
            Zlength key_chars = 32;
            init_done = 1 (*TODO also prove case where init_done=0*))
      LOCAL (temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256)); 
             gvar _aes_init_done (Vint (Int.repr init_done));
             gvar _tables tables)
      SEP (data_at_ ctx_sh t_struct_aesctx ctx;
           data_at key_sh (tarray tuchar (4*8)) (map Vint (map Int.repr key_chars)) key;
           (*if init_done ?= 1 then tables_initialized tables else tables_uninitialized tables*)
           tables_initialized tables)
    POST [  tint ]
      PROP () 
      LOCAL (temp ret_temp (Vint Int.zero); gvar _aes_init_done (Vint Int.one))
      SEP (data_at key_sh (tarray tuchar (4*8)) (map Vint [] (*TODO*)) key;
           data_at ctx_sh t_struct_aesctx 
                   (Vint (Int.repr 8),
                   (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])), 
                   (map Vint [] (*TODO*)))) ctx;
          tables_initialized tables)
.

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
Tactic Notation "replace_temp" constr(name) constr(new_value) "by" tactic(t) :=
  replace_temp name new_value; [ t | ].

Definition first_loop_inv00 ctx key tables init_done key_chars ctx_sh key_sh i :=
    PROP ( )
    LOCAL (
      temp _RK  (field_address t_struct_aesctx [StructField _buf] ctx);
      temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx);
      temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256));
      gvar _aes_init_done (Vint (Int.repr init_done)); gvar _tables tables)
    SEP (
      field_at ctx_sh t_struct_aesctx [StructField _nr] (Vint (Int.repr 14)) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _rk] 
        (field_address t_struct_aesctx [StructField _buf] ctx) ctx;
      field_at ctx_sh t_struct_aesctx [StructField _buf]
        (map Vint (map Int.repr (sublist 0 i key_chars)) ++ (repeat Vundef (Z.to_nat (68-i)))) ctx;
      data_at key_sh (tarray tuchar (4 * 8)) (map Vint (map Int.repr key_chars)) key;
      tables_initialized tables).

Definition first_loop_inv0 ctx key tables init_done key_chars ctx_sh key_sh :=
  EX i: Z, first_loop_inv00 ctx key tables init_done key_chars ctx_sh key_sh i.

Lemma body_key_expansion: semax_body Vprog Gprog f_mbedtls_aes_setkey_enc key_expansion_spec.
Proof.
  start_function.
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
  forward. replace_temp _t'1 (field_address t_struct_aesctx [StructField _buf] ctx) by entailer!.
  forward. replace_temp _RK (field_address t_struct_aesctx [StructField _buf] ctx) by entailer!.
  forward.
  (* first loop: *)
  forward_for_simple_bound 8 (first_loop_inv0 ctx key tables init_done key_chars ctx_sh key_sh).
  { (* precondition implies loop invariant: *)
    entailer!. }
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
    (* here, we'd need the same improvements as those to load_tac, or... *)
    replace_SEP 2 (data_at ctx_sh (tarray tuchar 68)
        (map Vint (map Int.repr (sublist 0 i key_chars)) ++ repeat Vundef (Z.to_nat (68 - i)))
        (field_address t_struct_aesctx [StructField _buf] ctx))
    by entailer!.
    forward. (* TODO store_tac still fails *)



Qed.
