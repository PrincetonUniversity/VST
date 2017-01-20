Require Import floyd.proofauto.
Require Import floyd.reassoc_seq.
Require Import aes.aes.
Require Import aes.tablesLL.

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

Definition tables_uninitialized tables := data_at_ Ews t_struct_tables tables.

Definition gen_tables_spec :=
  DECLARE _aes_gen_tables
    WITH tables : val
    PRE [  ]
      PROP ()
      LOCAL (gvar _tables tables)
      SEP (tables_uninitialized tables)
    POST [ tvoid ]
      PROP ()
      LOCAL (gvar _tables tables)
      SEP (tables_initialized tables)
.

Definition Gprog : funspecs := ltac:(with_library prog [ gen_tables_spec ]).

Lemma ff_exp_range: forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Int.unsigned (ff_exp (Int.repr a) (Int.repr b)) < 256.
Proof.
Admitted.

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

Lemma body_gen_tables: semax_body Vprog Gprog f_aes_gen_tables gen_tables_spec.
Proof.
  start_function.
  reassoc_seq.
  (* DONE floyd: Thanks to reassoc_seq, we don't need the two preparation steps any more *)
  forward_for_simple_bound 256 (EX i: Z,
    PROP ( 0 <= i ) (* TODO floyd: why do we only get "Int.min_signed <= i < 256", instead of lo=0 ?
                       Probably because there are 2 initialisations in the for-loop... *)
    LOCAL (temp _x (Vint (ff_exp (Int.repr 3) (Int.repr i))); 
        (* TODO documentation should say that I don't need to do this *)
        (* TODO floyd: tactic should tell me so *)
        (* temp _i (Vint (Int.repr i)); *)
           lvar _log (tarray tint 256) lvar1;
           lvar _pow (tarray tint 256) lvar0;
           gvar _tables tables)
    SEP (EX log : list val,
           !!(Zlength log = 256) &&
           (* Note: log[1] is set to 0 in the first iteration, and overwritten with 255 in the last 
              iteration, so we needn't assert anything about j=0, but we do about j=255.
              And btw, log[0] remains Vundef.
              Think "each j has to be stored in the right cell of the log array". *)
           !!(forall j, 1 <= j < i -> Vint (Int.repr j)
                = Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr j))) log Vundef)
           && data_at Tsh (tarray tint 256) log lvar1;
         EX pow : list val,
           !!(Zlength pow = 256) &&
           !!(forall j, 0 <= j < i -> Znth j pow Vundef = Vint (ff_exp (Int.repr 3) (Int.repr j)))
           && data_at Tsh (tarray tint 256) pow lvar0;
         tables_uninitialized tables)).
  { (* init *)
    forward. forward. Exists 0. entailer!. do 2 Exists (repeat Vundef 256).
    entailer!.
    split; intros; omega. (* TODO floyd why doesn't entailer! do this itself? *)
  }
  { (* body *)
    (* forward. TODO floyd: "forward" should tell me to use Intros instead of just failing *)
    Intros log pow.
    freeze [0; 2] Fr.
    forward.
    (* forward. "Error: No applicable tactic." 
       TODO floyd: error message should say that I have to thaw *)
    thaw Fr.
    forward.
    + entailer!. apply ff_exp_range; omega.
    + (* t'1 = ( x & 0x80 ) ? 0x1B : 0x00 ) *)
      forward_if_diff (PROP () LOCAL (temp _t'1 (Vint (
        if Int.eq (Int.and (ff_exp (Int.repr 3) (Int.repr i)) (Int.repr 128)) Int.zero
        then Int.zero
        else (Int.repr 27)
      ))) SEP ()).
      * (* then-branch of "_ ? _ : _" *)
        forward. rewrite Int.eq_false by assumption. entailer!.
      * (* else-branch of "_ ? _ : _" *)
        forward.
        match goal with
        | H: @eq int _ _ |- _ => rewrite H
        end.
        rewrite Int.eq_true.
        entailer!.
      * (* after  "_ ? _ : _" *)
        (* x = (x ^ ((x << 1) ^ t'1)) & 0xFF *)
        forward.
        entailer!.
        { f_equal. admit. }
        { Exists (upd_Znth i pow (Vint (ff_exp (Int.repr 3) (Int.repr i)))).
          Exists (upd_Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr i))) log (Vint (Int.repr i))).
          entailer!. assert (0 <= i < 256) by omega. repeat split.
          - replace 256 with (Zlength log) by assumption.
            apply upd_Znth_Zlength.
            replace (Zlength log) with 256 by assumption.
            apply ff_exp_range; omega.
          - (*  apply log_table_invariant; assumption. *) admit.
          - replace 256 with (Zlength pow) by assumption.
            apply upd_Znth_Zlength. omega.
          - (* apply pow_table_invariant; assumption. *) admit.
        }
  } {
  Intros log pow.

  (* next part: round constants *)
  forward_for_simple_bound 10 (EX i: Z,
    (PROP ( 0 <= i ) (* note: the upper bound is added by the tactic, but the lower isn't! *)
     LOCAL (temp _x (Vint (ff_exp (Int.repr 2) (Int.repr i)));
            lvar _log (tarray tint 256) lvar1;
            lvar _pow (tarray tint 256) lvar0;
            gvar _tables tables)
     SEP (data_at Tsh (tarray tint 256) log lvar1;
          data_at Tsh (tarray tint 256) pow lvar0;
          tables_uninitialized tables))).
  { (* init *)
    forward. forward. Exists 0. entailer!. }
  { (* body *)
    unfold tables_uninitialized.
    (* TODO floyd: if I don't unfold, "forward" fails with the default error message *)
    forward. entailer!.
    simpl (field_at _ _ _ _ tables).
    freeze [0; 1; 2] Fr.
    (* t'2 = ( x & 0x80 ) ? 0x1B : 0x00 ) *)
    forward_if_diff (PROP () LOCAL (temp _t'2 (Vint (
      if Int.eq (Int.and (ff_exp (Int.repr 2) (Int.repr i)) (Int.repr 128)) Int.zero
      then Int.zero
      else (Int.repr 27)
    ))) SEP ()).
    * (* then-branch of "_ ? _ : _" *)
      forward. rewrite Int.eq_false by assumption. entailer!.
    * (* else-branch of "_ ? _ : _" *)
      forward.
      match goal with
      | H: @eq int _ _ |- _ => rewrite H
      end.
      rewrite Int.eq_true.
      entailer!.
    * (* after  "_ ? _ : _" *)
      (* x = ((x << 1) ^ t'2)) & 0xFF *)
      forward.
      entailer!.
      { (*
Vint (ff_exp (Int.repr 2) (Int.repr (i + 1))) =
Vint
  (Int.and
     (Int.xor (Int.shl (ff_exp (Int.repr 2) (Int.repr i)) (Int.repr 1))
        (if Int.eq (Int.and (ff_exp (Int.repr 2) (Int.repr i)) (Int.repr 128)) Int.zero
         then Int.zero
         else Int.repr 27)) (Int.repr 255))
*)
        (* apply exp2_step. *) admit. }
      { thaw Fr. unfold tables_uninitialized. simpl. (* TODO first make loop invariant for RCON *)

    admit. }
  }
  { (* rest *)
    admit. }
}
Qed.

