Require Import floyd.proofauto.
Require Import aes.
Require Import tablesLL.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* definitions copied from other files, just to see what we need: *)
Definition t_struct_aesctx := Tstruct _mbedtls_aes_context_struct noattr.
Definition t_struct_tables := Tstruct _aes_tables_struct noattr.
Definition Nr := 14. (* number of cipher rounds *)

Definition tables_initialized (tables : val) := data_at Ews t_struct_tables 
  (map Vint FSb, (map Vint FT0, (map Vint FT1, (map Vint FT2, (map Vint FT3,
  (map Vint RSb, (map Vint RT0, (map Vint RT1, (map Vint RT2, (map Vint RT3, 
  (map Vint RCON))))))))))) tables.

(* arr: list of 4 bytes *)
Definition get_uint32_le (arr: list int) (i: Z) : int :=
 (Int.or (Int.or (Int.or
            (Znth  i    arr Int.zero)
   (Int.shl (Znth (i+1) arr Int.zero) (Int.repr  8)))
   (Int.shl (Znth (i+2) arr Int.zero) (Int.repr 16)))
   (Int.shl (Znth (i+3) arr Int.zero) (Int.repr 24))).

(* outputs a list of 4 bytes *)
Definition put_uint32_le (x : int) : list int :=
  [ (Int.and           x                (Int.repr 255));
    (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255)) ].

Definition byte0 (x : int) : Z :=
  (Z.land (Int.unsigned x) (Int.unsigned (Int.repr 255))).
Definition byte1 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).
Definition byte2 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 16))) (Int.unsigned (Int.repr 255))).
Definition byte3 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).

Definition mbed_tls_fround_col (col0 col1 col2 col3 : int) (rk : int) : int :=
  (Int.xor (Int.xor (Int.xor (Int.xor rk 
    (force_int (Znth (byte0 col0) (map Vint FT0) Vundef)))
    (force_int (Znth (byte1 col1) (map Vint FT1) Vundef)))
    (force_int (Znth (byte2 col2) (map Vint FT2) Vundef)))
    (force_int (Znth (byte3 col3) (map Vint FT3) Vundef))).

Definition four_ints := (int * (int * (int * int)))%type.

Definition mbed_tls_fround (cols : four_ints) (rks : list int) (i : Z) : four_ints :=
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_fround_col col0 col1 col2 col3 (Znth  i    rks Int.zero)),
  ((mbed_tls_fround_col col1 col2 col3 col0 (Znth (i+1) rks Int.zero)),
  ((mbed_tls_fround_col col2 col3 col0 col1 (Znth (i+2) rks Int.zero)),
   (mbed_tls_fround_col col3 col0 col1 col2 (Znth (i+3) rks Int.zero)))))
end.

Fixpoint mbed_tls_enc_rounds (n : nat) (state : four_ints) (rks : list int) (i : Z) : four_ints :=
match n with
| O => state
| S m => mbed_tls_enc_rounds m (mbed_tls_fround state rks i) rks (i+4)
end.

Definition mbed_tls_final_enc_round (state : four_ints) (rks : list int) : four_ints := state. (* TODO *)

(* plaintext: array of bytes
   rks: expanded round keys, array of Int32 *)
Definition mbed_tls_initial_add_round_key (plaintext : list int) (rks : list int) : four_ints :=
((Int.xor (get_uint32_le plaintext  0) (Znth 0 rks Int.zero)),
((Int.xor (get_uint32_le plaintext  4) (Znth 1 rks Int.zero)),
((Int.xor (get_uint32_le plaintext  8) (Znth 2 rks Int.zero)),
 (Int.xor (get_uint32_le plaintext 12) (Znth 3 rks Int.zero))))).

Definition mbed_tls_aes_enc (plaintext : list int) (rks : list int) : list int :=
  let state0 := mbed_tls_initial_add_round_key plaintext rks in
  match (mbed_tls_final_enc_round (mbed_tls_enc_rounds 13 state0 rks 0) rks) with
  | (col0, (col1, (col2, col3))) => 
       (put_uint32_le col0) ++ (put_uint32_le col1) ++ (put_uint32_le col2) ++ (put_uint32_le col3)
  end.

Definition encryption_spec_ll :=
  DECLARE _mbedtls_aes_encrypt
  WITH ctx : val, input : val, output : val, (* arguments *)
       ctx_sh : share, in_sh : share, out_sh : share, (* shares *)
       plaintext : list Z, (* 16 chars *)
       exp_key : list Z, (* expanded key, 4*(Nr+1)=60 32-bit integers *)
       tables : val (* global var *)
  PRE [ _ctx OF (tptr t_struct_aesctx), _input OF (tptr tuchar), _output OF (tptr tuchar) ]
    PROP (Zlength plaintext = 16; Zlength exp_key = 60;
          readable_share ctx_sh; readable_share in_sh; writable_share out_sh)
    LOCAL (temp _ctx ctx; temp _input input; temp _output output; gvar _tables tables)
    SEP (data_at ctx_sh (t_struct_aesctx) (
          (Vint (Int.repr Nr)), 
          ((field_address t_struct_aesctx [StructField _buf] ctx),
          ((map Vint (map Int.repr exp_key)) ++ (list_repeat (8%nat) Vundef)))
         ) ctx;
         data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
         data_at_ out_sh (tarray tuchar 16) output;
         tables_initialized tables)
  POST [ tvoid ]
    PROP() LOCAL()
    SEP (data_at out_sh (tarray tuchar 16) 
                        (map Vint (mbed_tls_aes_enc (map Int.repr plaintext) (map Int.repr exp_key)))
                         output).

(* QQQ: How to know that if x is stored in a var of type tuchar, 0 <= x < 256 ? *)
(* QQQ: Declare vars of type Z or of type int in API spec ? *)

Definition Gprog : funspecs := ltac:(with_library prog [ encryption_spec_ll ]).

Ltac simpl_Int := repeat match goal with
| |- context [ (Int.mul (Int.repr ?A) (Int.repr ?B)) ] =>
    let x := fresh "x" in (pose (x := (A * B)%Z)); simpl in x;
    replace (Int.mul (Int.repr A) (Int.repr B)) with (Int.repr x); subst x; [|reflexivity]
| |- context [ (Int.add (Int.repr ?A) (Int.repr ?B)) ] =>
    let x := fresh "x" in (pose (x := (A + B)%Z)); simpl in x;
    replace (Int.add (Int.repr A) (Int.repr B)) with (Int.repr x); subst x; [|reflexivity]
end.

Lemma body_aes_encrypt: semax_body Vprog Gprog f_mbedtls_aes_encrypt encryption_spec_ll.
Proof.
  start_function.
  (* TODO floyd: put (Sreturn None) in such a way that the code can be folded into MORE_COMMANDS *)

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

  (* Bring the SEP clause about ctx into a suitable form: *)
  remember (list_repeat 8 Vundef) as Vundefs.
  assert (exists k1 k2 k3 k4 exp_key_tail, exp_key = k1 :: k2 :: k3 :: k4 :: exp_key_tail) as Eq. {
    destruct exp_key as [|k1 [| k2 [| k3 [| k4 exp_key_tail]]]];
      try solve [compute in H0; omega]. repeat eexists.
  }
  destruct Eq as [k1 [k2 [k3 [k4 [exp_tail Eq]]]]]. subst exp_key. 
  repeat rewrite map_cons.

  (* GET_UINT32_LE( X0, input,  0 ); X0 ^= *RK++;
     GET_UINT32_LE( X1, input,  4 ); X1 ^= *RK++;
     GET_UINT32_LE( X2, input,  8 ); X2 ^= *RK++;
     GET_UINT32_LE( X3, input, 12 ); X3 ^= *RK++; *)
  Ltac GET_UINT32_LE_tac := do 4 (
    (forward; repeat rewrite zlist_hint_db.Znth_map_Vint by (rewrite Zlength_map; omega));
    [ solve [ entailer! ] | idtac ]
  ).

  assert_PROP (forall i, 0 <= i < 60 -> force_val (sem_add_pi tuint
       (field_address t_struct_aesctx [ArraySubsc  i   ; StructField _buf] ctx) (Vint (Int.repr 1)))
     = (field_address t_struct_aesctx [ArraySubsc (i+1); StructField _buf] ctx)) as Eq. {
    entailer!. intros.
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    simpl. destruct ctx; inversion PNctx; try reflexivity.
    simpl. rewrite Int.add_assoc.
    replace (Int.mul (Int.repr 4) (Int.repr 1)) with (Int.repr 4) by reflexivity.
    rewrite add_repr.
    replace (8 + 4 * (i + 1)) with (8 + 4 * i + 4) by omega.
    reflexivity.
  }

  Time do 4 (
    GET_UINT32_LE_tac; simpl; forward; forward; forward;
    rewrite Eq by omega; simpl;
    forward; forward
  ). (* 1308s *)

  match goal with
  | |- context [temp _X0 (Vint (Int.xor ?E (Int.repr k1)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 0) by reflexivity
  end.
  match goal with
  | |- context [temp _X1 (Vint (Int.xor ?E (Int.repr k2)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 4) by reflexivity
  end.
  match goal with
  | |- context [temp _X2 (Vint (Int.xor ?E (Int.repr k3)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 8) by reflexivity
  end.
  match goal with
  | |- context [temp _X3 (Vint (Int.xor ?E (Int.repr k4)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 12) by reflexivity
  end.

unfold Sfor.

(* beginning of for loop *)

forward. forward.

(* ugly hack to avoid type mismatch between
   "(val * (val * list val))%type" and "reptype t_struct_aesctx" *)
assert (exists (v: reptype t_struct_aesctx), v =
       (Vint (Int.repr Nr),
          (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
          Vint (Int.repr k1)
          :: Vint (Int.repr k2)
             :: Vint (Int.repr k3)
                :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs)))
as EE by (eexists; reflexivity).

destruct EE as [vv EE].

eapply semax_seq' with (P' :=
  PROP ( )
  LOCAL (
     temp _RK (field_address t_struct_aesctx [ArraySubsc 4; StructField _buf] ctx);
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx 
  )
).
{
apply semax_pre with (P' := 
  (EX i: Z,   PROP ( ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc 4; StructField _buf] ctx);
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
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
{ apply semax_loop with (
  (EX i: Z,   PROP ( ) LOCAL ( 
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc 4; StructField _buf] ctx);
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
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

forward_if (PROP ( ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (field_address t_struct_aesctx [ArraySubsc 4; StructField _buf] ctx);
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
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
  forward. entailer!.
 }
{
 (* else-branch: exit loop *)
  forward. entailer!.
 }
{ (* rest: loop body *)
  forward. forward.
  (* now we need the SEP clause about ctx: *) subst vv.
  forward.

{
entailer!.
(* TODO simplify this earlier! *)
admit. (* TODO is_int *)
}

(* next command in loop body: *)
(*     uint32_t b0 = tables.FT0[ ( Y0       ) & 0xFF ];    *)
unfold tables_initialized.

Definition lo_byte (i : Z) : Z := (Z.land i (Int.unsigned (Int.repr 255))).
Arguments lo_byte i : simpl never.

Ltac entailer_for_load_tac ::= idtac.
(* without override: forward takes >5 min, with override: 40s *)
Time forward.

match goal with
| |- context [ (Z.land ?i (Int.unsigned (Int.repr 255))) ] =>
        change (Z.land  i (Int.unsigned (Int.repr 255))) with (lo_byte i)
end.

{ (* entailer!. takes forever, even with lo_byte and "simpl never" *)
  rewrite zlist_hint_db.Znth_map_Vint. {

repeat apply andp_right.
{ (* TODO floyd entailer! takes forever, but the goal is so simple: *)
  apply prop_right. apply I. }
{ unfold tc_val. apply local_True_right. }
{ match goal with
| |- _ |-- ?E1 => let E2 := eval cbv in E1 in replace E1 with E2 by reflexivity
end.
apply local_True_right.
}
{ apply prop_right. apply I. }
}
{ 

Lemma masked_byte_range: forall i,
  0 <= Z.land i 255 < 256. Admitted.

apply masked_byte_range.
}
}
{ apply prop_right. apply masked_byte_range. }

forward. admit. admit.

Arguments Z.land _ _ : simpl never.

let x := eval simpl in (Z.land
                 (Int.unsigned
                    (Int.shru (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3))
                       (Int.repr 16))) (Int.unsigned (Int.repr 255)))
in idtac x. (* now fast *)

eapply semax_seq'. {
eapply semax_seq'. {
Require Import floyd.simpl_reptype.
Time ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with   
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
 (* Super canonical load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "HLE" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H_Denote" in
    let gfsB := fresh "gfsB" in
      solve_efield_denote Delta P Q R efs gfsB H_Denote (* 11s until here *);

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs0" in evar (gfs0: list gfield);
    let gfsA := fresh "gfsA" in evar (gfsA: list gfield);
    let a := fresh "a" in evar (a: val);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let Hf := fresh "Hf" in
    let eqL := constr:(p = field_address t_root gfsA a) in
    let eqR := constr:(p = a /\ gfsA = nil) in
    let g := constr:((ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! eqL) \/ eqR) in
    let HNice := fresh "HNice" in

    tryif (
      tryif (
        assert g as HNice by (
          subst p gfsA gfsB a t_root;
          left;
          (eassumption || (apply prop_right; (eassumption || reflexivity)))
        )
      ) then (
        (sc_new_instantiate P Q R R Delta e1 gfsA gfsB tts lr a sh t_root gfs0 v n (0%nat) Hf
         || fail 15 "sc_new_instantiate should really not have failed" )
      ) else (
        instantiate (gfsA := nil); instantiate (a := p);
        (* will fail if these instantiations were a bad idea: *)
        sc_new_instantiate P Q R R Delta e1 gfsA gfsB tts lr a sh t_root gfs0 v n (0%nat) Hf;
        (assert g as HNice by (
          subst p gfsA gfsB a t_root;
          right;
          split; reflexivity
        ) || fail 15 "assert should really not have failed" )
      )
    ) then (
      (* 12s until here *)
      let len := fresh "len" in
      pose ((length (gfsB ++ gfsA) - length gfs0)%nat) as len;
      simpl in len;
      let gfs1 := fresh "gfs1" in
      match goal with
      | len := ?len' |- _ => pose (gfs1 := (firstn len' (gfsB ++ gfsA)));
                             cbv [app gfsB gfsA firstn] in gfs1
      end;

      let gfsEq := fresh "gfsEq" in
      assert (gfsB ++ gfsA = gfs1 ++ gfs0) as gfsEq by reflexivity;

      let Heq := fresh "Heq" in
      match type of Hf with
      | (?R0 = _) => assert (nth_error R n = Some R0) as Heq by reflexivity
      end;

      refine (semax_SC_field_load_general' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _  _ _ lr _ _ _ HLE H_Denote HNice Heq _ gfsEq _ _ _ _ _) (*12.7s until here; try reflexivity;
      [ auto (* readable_share *)
      | solve_load_rule_evaluation
      | clear HLE H_Denote;
        subst lr e1 gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        repeat match goal with H := _ |- _ => clear H end;
        try quick_typecheck3; 
        unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
        entailer_for_load_tac
      | subst lr e1 gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        solve_legal_nested_field_in_entailment; try clear HLE H_Denote ] *)
    ) else (
      assert (undo_and_first__assert_PROP eqL); subst t_root gfsA gfsB a p
    )

end.

reflexivity.
reflexivity.
reflexivity.
auto.
Time solve_load_rule_evaluation.
(* culprit #1 for slowness: 
clear HLE H_Denote;
        subst lr e gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        repeat match goal with H := _ |- _ => clear H end;
        try quick_typecheck3; 
        unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
        entailer_for_load_tac.
*)
rewrite ?Znth_map with (d' := Int.zero) by apply masked_byte_range.
clear HLE H_Denote;
        subst lr e gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        repeat match goal with H := _ |- _ => clear H end;
        try quick_typecheck3.
(* now quick_typecheck3 is quick again! *)

(* culprit #2:
subst lr e gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        solve_legal_nested_field_in_entailment; try clear HLE H_Denote.
*)
subst lr e gfs0 gfs1 gfsA gfsB efs tts t_root a v n.

Time solve_legal_nested_field_in_entailment.
 (* now "only" takes 7.9s, because array indices are not simplified *)

apply prop_right. apply masked_byte_range.

reflexivity.
reflexivity.

}

fwd_result.

(* b3 = ... and whole rest of 1st macro invocation *)
admit.

}

(* 2nd macro invocation *)
unfold MORE_COMMANDS, abbreviate.

admit.

} }

{ (* loop incr *)
admit.
}
}
}
{
admit.
}

Qed.

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
