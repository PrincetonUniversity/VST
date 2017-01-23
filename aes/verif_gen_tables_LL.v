Require Import floyd.proofauto.
Require Import floyd.reassoc_seq.
Require Import aes.sbox.
Require Import aes.aes.

Fixpoint repeat_op_nat{T: Type}(n: nat)(start: T)(op: T -> T): T := match n with
| O => start
| S m => op (repeat_op_nat m start op)
end.

Definition repeat_op{T: Type}(n: Z)(start: T)(op: T -> T): T := repeat_op_nat (Z.to_nat n) start op.

Lemma repeat_op_step: forall {T: Type} (i: Z) (start: T) (op: T -> T),
  0 <= i ->
  repeat_op (i + 1) start op = op (repeat_op i start op).
Proof.
  intros. unfold repeat_op. rewrite Z2Nat.inj_add by omega.
  rewrite Nat.add_1_r. simpl. reflexivity.
Qed.

Fixpoint repeat_op_table_nat{T: Type}(n: nat)(start: T)(op: T -> T): list T := match n with
| O => []
| S m => (repeat_op_table_nat m start op) ++ [repeat_op_nat m start op]
end.

Definition repeat_op_table{T: Type}(n: Z)(start: T)(op: T -> T): list T :=
  repeat_op_table_nat (Z.to_nat n) start op.

Lemma repeat_op_table_step: forall {T: Type} (i: Z) (start: T) (op: T -> T),
  0 <= i ->
  repeat_op_table (i + 1) start op = (repeat_op_table i start op) ++ [repeat_op i start op].
Proof.
  intros. unfold repeat_op_table. rewrite Z2Nat.inj_add by omega.
  rewrite Nat.add_1_r. simpl. reflexivity.
Qed.

Definition times3(x: int): int := 
  Int.and
    (Int.xor x (Int.xor (Int.shl x (Int.repr 1))
                        (if Int.eq (Int.and x (Int.repr 128)) Int.zero then Int.zero else Int.repr 27)))
    (Int.repr 255).

Definition pow3(e: Z): int := repeat_op e (Int.repr 1) times3.

Definition times2(x: int): int := 
  Int.and
    (Int.xor (Int.shl x (Int.repr 1))
             (if Int.eq (Int.and x (Int.repr 128)) Int.zero then Int.zero else Int.repr 27))
    (Int.repr 255).

Definition pow2(e: Z): int := repeat_op e (Int.repr 1) times2.

(* instead of
     Require Import aes.tablesLL.
   we do, for the moment:
*)
Definition FSb := map Int.repr sbox.
Definition FT0 := (@nil int).
Definition FT1 := (@nil int).
Definition FT2 := (@nil int).
Definition FT3 := (@nil int).
Definition RSb := map Int.repr inv_sbox.
Definition RT0 := (@nil int).
Definition RT1 := (@nil int).
Definition RT2 := (@nil int).
Definition RT3 := (@nil int).
Definition RCON := repeat_op_table 10 Int.one times2.

Global Opaque FSb FT0 FT1 FT2 FT3 RSb RT0 RT1 RT2 RT3 RCON.

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

Lemma pow2_range: forall e,
  0 <= e ->
  0 <= Int.unsigned (pow2 e) < 256.
Admitted.

Lemma pow3_range: forall e,
  0 <= e ->
  0 <= Int.unsigned (pow3 e) < 256.
Admitted.

Lemma pow3_inj: forall (i j : Z),
  pow3 i = pow3 j -> Int.eqmod 255 i j.
Admitted.

(* TODO floyd this lemma should be invoked by entailer!
   Note: in summaray, this already works for data_at, but why doesn't it work for field_at?
   QQQ: And why/how does it work for data_at? *)
Lemma field_at_update_val: forall sh t gfs v v' p,
  v = v' -> field_at sh t gfs v p |-- field_at sh t gfs v' p.
Proof.
  intros. rewrite H. apply derives_refl.
Qed.

Lemma repeat_op_table_nat_length: forall {T: Type} (i: nat) (x: T) (f: T -> T),
  length (repeat_op_table_nat i x f) = i.
Proof.
  intros. induction i. reflexivity. simpl. rewrite app_length. simpl.
  rewrite IHi. omega.
Qed.

Lemma repeat_op_table_length: forall {T: Type} (i: Z) (x: T) (f: T -> T),
  0 <= i ->
  Zlength (repeat_op_table i x f) = i.
Proof.
  intros. unfold repeat_op_table.
  rewrite Zlength_correct. rewrite repeat_op_table_nat_length.
  apply Z2Nat.id. assumption.
Qed.

Lemma repeat_op_nat_id: forall {T: Type} (n: nat) (v: T),
  repeat_op_nat n v id = v.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Lemma repeat_op_table_nat_id_app: forall {T: Type} (len1 len2: nat) (v: T),
  repeat_op_table_nat (len1 + len2) v id 
  = repeat_op_table_nat len1 v id ++ repeat_op_table_nat len2 v id.
Proof.
  intros. induction len2.
  - simpl. replace (len1 + 0)%nat with len1 by omega. rewrite app_nil_r. reflexivity.
  - replace (len1 + S len2)%nat with (S (len1 + len2)) by omega. simpl.
    rewrite IHlen2. rewrite <- app_assoc. f_equal. f_equal. do 2 rewrite repeat_op_nat_id.
    reflexivity.
Qed.

Lemma sublist_repeat_op_table_id: forall {T: Type} (lo n: Z) (v: T),
  0 <= lo ->
  0 <= n ->
  sublist lo (lo + n) (repeat_op_table (lo + n) v id) = repeat_op_table n v id.
Proof.
  intros.
  replace (lo + n) with (Zlength (repeat_op_table (lo + n) v id)) at 1
    by (apply repeat_op_table_length; omega).
  rewrite sublist_skip by omega.
  unfold repeat_op_table at 1. rewrite Z2Nat.inj_add by omega.
  rewrite repeat_op_table_nat_id_app.
  rewrite Zskipn_app1 by (
    rewrite Zlength_correct;
    rewrite repeat_op_table_nat_length;
    rewrite Z2Nat.id; omega
  ).
  rewrite skipn_short; [ reflexivity | ].
  rewrite repeat_op_table_nat_length. omega.
Qed.

Lemma invert_pow3: forall i,
  1 <= i < 256 ->
  exists j, 1 <= j < 256 /\ i = (Int.unsigned (pow3 j)).
Admitted.

Lemma FSb_def: forall b1,
     0 <= b1 < 256 ->
     Znth (Int.unsigned (pow3 (255 - b1))) FSb Int.zero
     = Int.xor
         (Int.xor
            (Int.xor
               (Int.xor (pow3 b1)
                  (Int.and (Int.or (Int.shl (pow3 b1) (Int.repr 1)) (Int.shr (pow3 b1) (Int.repr 7)))
                     (Int.repr 255)))
               (Int.and
                  (Int.or
                     (Int.shl
                        (Int.and
                           (Int.or (Int.shl (pow3 b1) (Int.repr 1)) (Int.shr (pow3 b1) (Int.repr 7)))
                           (Int.repr 255)) (Int.repr 1))
                     (Int.shr
                        (Int.and
                           (Int.or (Int.shl (pow3 b1) (Int.repr 1)) (Int.shr (pow3 b1) (Int.repr 7)))
                           (Int.repr 255)) (Int.repr 7))) (Int.repr 255)))
            (Int.and
               (Int.or
                  (Int.shl
                     (Int.and
                        (Int.or
                           (Int.shl
                              (Int.and
                                 (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                    (Int.shr (pow3 b1) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 1))
                           (Int.shr
                              (Int.and
                                 (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                    (Int.shr (pow3 b1) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 7))) (Int.repr 255)) (Int.repr 1))
                  (Int.shr
                     (Int.and
                        (Int.or
                           (Int.shl
                              (Int.and
                                 (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                    (Int.shr (pow3 b1) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 1))
                           (Int.shr
                              (Int.and
                                 (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                    (Int.shr (pow3 b1) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 7))) (Int.repr 255)) (Int.repr 7))) 
               (Int.repr 255)))
         (Int.xor
            (Int.and
               (Int.or
                  (Int.shl
                     (Int.and
                        (Int.or
                           (Int.shl
                              (Int.and
                                 (Int.or
                                    (Int.shl
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 1))
                                    (Int.shr
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 1))
                           (Int.shr
                              (Int.and
                                 (Int.or
                                    (Int.shl
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 1))
                                    (Int.shr
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 7))) (Int.repr 255)) (Int.repr 1))
                  (Int.shr
                     (Int.and
                        (Int.or
                           (Int.shl
                              (Int.and
                                 (Int.or
                                    (Int.shl
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 1))
                                    (Int.shr
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 1))
                           (Int.shr
                              (Int.and
                                 (Int.or
                                    (Int.shl
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 1))
                                    (Int.shr
                                       (Int.and
                                          (Int.or (Int.shl (pow3 b1) (Int.repr 1))
                                             (Int.shr (pow3 b1) (Int.repr 7))) 
                                          (Int.repr 255)) (Int.repr 7))) (Int.repr 255)) 
                              (Int.repr 7))) (Int.repr 255)) (Int.repr 7))) 
               (Int.repr 255)) (Int.repr 99)).
Admitted.

Lemma FSb_range: forall i,
  0 <= Int.unsigned (Znth i FSb Int.zero) < 256.
Admitted.

Lemma zero_ext_nop: forall i,
  0 <= (Int.unsigned i) < 256 ->
  Int.zero_ext 8 i = i.
Admitted.

Lemma FSb_inj: forall i j,
  0 <= i < 256 ->
  0 <= j < 256 ->
  Znth i FSb Int.zero = Znth j FSb Int.zero ->
  i = j.
Admitted.

Definition rcon_loop_inv00(i: Z)(lvar0 lvar1 tables: val)(frozen: list mpred) : environ -> mpred :=
     PROP ( 0 <= i) (* note: the upper bound is added by the tactic, but the lower isn't! *)
     LOCAL (temp _x (Vint (pow2 i));
            lvar _log (tarray tint 256) lvar1;
            lvar _pow (tarray tint 256) lvar0;
            gvar _tables tables)
     SEP (FRZL frozen;
          field_at Ews t_struct_tables [StructField _RCON]
                   ((map Vint (repeat_op_table i Int.one times2)) ++ (repeat_op_table (10-i) Vundef id))
                   tables).

Definition rcon_loop_inv0(lvar0 lvar1 tables: val)(frozen: list mpred) :=  EX i: Z,
  rcon_loop_inv00 i lvar0 lvar1 tables frozen.

(* TODO floyd if I inline inv00 into inv0, why doesn't this typecheck?
Definition rcon_loop_inv(lvar0 lvar1 tables: val) :=
  EX i: Z,
     PROP ( 0 <= i) (* note: the upper bound is added by the tactic, but the lower isn't! *)
     LOCAL (temp _x (Vint (pow2 i));
            lvar _log (tarray tint 256) lvar1;
            lvar _pow (tarray tint 256) lvar0;
            gvar _tables tables)
     SEP (field_at Ews t_struct_tables [StructField _RCON]
                   ((map Vint (repeat_op_table i Int.one times2)) ++ (repeat_op_table (10-i) Vundef id))
                   tables).
*)

Definition gen_sbox_inv00 i lvar0 lvar1 tables log pow frozen :=
    PROP ( )
    LOCAL (lvar _log (tarray tint 256) lvar1;
           lvar _pow (tarray tint 256) lvar0;
           gvar _tables tables)
    SEP (FRZL frozen; data_at Tsh (tarray tint 256) log lvar1; data_at Tsh (tarray tint 256) pow lvar0;
         EX fsb : list val,
           !!(Zlength fsb = 256) &&
           !!(forall j, 0 <= j < i -> Znth j fsb Vundef = Vint (Znth j FSb Int.zero)) &&
           !!(Znth 0 fsb Vundef = Vint (Int.repr 99))
           && field_at Ews t_struct_tables [StructField _FSb] fsb tables;
         EX rsb : list val,
           !!(Zlength rsb = 256) &&
           !!(forall j, 1 <= j < i ->
                (Znth (Int.unsigned (Znth j FSb Int.zero)) rsb Vundef) = Vint (Int.repr j)) &&
           !!(Znth 99 rsb Vundef = Vint Int.zero)
           && field_at Ews t_struct_tables [StructField _RSb] rsb tables).

Definition gen_sbox_inv0 lvar0 lvar1 tables log pow frozen :=
  EX i: Z, gen_sbox_inv00 i lvar0 lvar1 tables log pow frozen.

Lemma body_gen_tables: semax_body Vprog Gprog f_aes_gen_tables gen_tables_spec.
Proof.
  start_function.
  reassoc_seq.
  (* DONE floyd: Thanks to reassoc_seq, we don't need the two preparation steps any more *)
  forward_for_simple_bound 256 (EX i: Z,
    PROP ( 0 <= i ) (* TODO floyd: why do we only get "Int.min_signed <= i < 256", instead of lo=0 ?
                       Probably because there are 2 initialisations in the for-loop... *)
    LOCAL (temp _x (Vint (pow3 i)); 
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
                = Znth (Int.unsigned (pow3 j)) log Vundef)
           && data_at Tsh (tarray tint 256) log lvar1;
         EX pow : list val,
           !!(Zlength pow = 256) &&
           !!(forall j, 0 <= j < i -> Znth j pow Vundef = Vint (pow3 j))
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
    + entailer!. apply pow3_range; omega.
    + (* t'1 = ( x & 0x80 ) ? 0x1B : 0x00 ) *)
      forward_if_diff (PROP () LOCAL (temp _t'1 (Vint (
        if Int.eq (Int.and (pow3 i) (Int.repr 128)) Int.zero
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
        { f_equal. unfold pow3. rewrite repeat_op_step by omega. reflexivity. }
        { Exists (upd_Znth i pow (Vint (pow3 i))).
          Exists (upd_Znth (Int.unsigned (pow3 i)) log (Vint (Int.repr i))).
          entailer!. assert (0 <= i < 256) by omega. repeat split.
          - replace 256 with (Zlength log) by assumption.
            apply upd_Znth_Zlength.
            replace (Zlength log) with 256 by assumption.
            apply pow3_range; omega.
          - intros. assert (1 <= j < i \/ j = i) as C by omega. destruct C as [C | C].
            * rewrite upd_Znth_diff.
              + auto.
              + replace (Zlength log) with 256 by assumption. apply pow3_range; omega.
              + replace (Zlength log) with 256 by assumption. apply pow3_range; omega.
              + intro E. apply unsigned_eq_eq in E.
                apply pow3_inj in E. unfold Int.eqmod in E. destruct E as [k E]. omega.
            * subst. rewrite upd_Znth_same.
              + reflexivity.
              + replace (Zlength log) with 256 by assumption. apply pow3_range; omega.
          - replace 256 with (Zlength pow) by assumption.
            apply upd_Znth_Zlength. omega.
          - intros. assert (0 <= j < i \/ j = i) as C by omega. destruct C as [C | C].
            * rewrite upd_Znth_diff by omega. auto.
            * subst. rewrite upd_Znth_same by omega. reflexivity.
        }
  } {
  Intros log pow.

  unfold tables_uninitialized.
  unfold_data_at 3%nat.
  freeze [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] Fr.

  forward_for_simple_bound 10 (rcon_loop_inv0 lvar0 lvar1 tables Fr).
  { (* init *)
    forward. forward. Exists 0. entailer!.
  }
  { (* body *)
    forward. entailer!.
    (* t'2 = ( x & 0x80 ) ? 0x1B : 0x00 ) *)
    forward_if_diff (PROP () LOCAL (temp _t'2 (Vint (
      if Int.eq (Int.and (pow2 i) (Int.repr 128)) Int.zero
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
      - f_equal. unfold pow2 at 1. rewrite repeat_op_step by omega. reflexivity.
      - apply field_at_update_val.
        rewrite upd_Znth_app2.
        + rewrite Zlength_map. rewrite repeat_op_table_length by assumption.
          replace (i - i) with 0 by omega. rewrite upd_Znth0.
          rewrite repeat_op_table_length by omega.
          rewrite repeat_op_table_step by omega.
          rewrite map_app. rewrite <- app_assoc. f_equal. simpl. f_equal.
          replace (10 - i) with (1 + (10 - (i + 1))) by omega.
          apply sublist_repeat_op_table_id; omega.
        + pose proof (Zlength_nonneg ((repeat_op_table (10 - i) Vundef id))).
          rewrite Zlength_map. rewrite repeat_op_table_length by omega. omega.
  } {
  rewrite app_nil_r.

Transparent FSb RSb.

  (* generate the forward and reverse S-boxes *)
  thaw Fr.
  freeze [3; 4; 5; 6; 8; 9; 10; 11; 12] Fr.
  forward.
  forward.
  forward_for_simple_bound 256 (gen_sbox_inv0 lvar0 lvar1 tables log pow Fr).
  { (* loop invariant holds initially: *)
    entailer!.
    Exists (upd_Znth 99 Vundef256 (Vint (Int.repr 0))).
    Exists (upd_Znth 0 Vundef256 (Vint (Int.repr 99))).
    entailer!. split.
    - intros. assert (j = 0) by omega. subst j. rewrite upd_Znth_same.
      * reflexivity.
      * change (Zlength Vundef256) with 256. omega.
    - intros. omega.
  }
  { (* loop body preserves invariant: *)
    Ltac expose_pow_Vint pow Hpow :=
      match goal with
      | |- context [ Znth ?i pow Vundef ] => rewrite (Hpow i) by omega
      end.
    Ltac expose_log_Vint log Hlog :=
      match goal with
      | |- context [ Znth ?i log Vundef ] =>
        let b := fresh "b0" in let B := fresh "B0" in let E := fresh "E0" in
        destruct (invert_pow3 i) as [b [B E]]; [ omega |
          rewrite E; rewrite <- (Hlog b B); rewrite ?Int.repr_unsigned ]
      end.
    forward. { entailer!. expose_log_Vint log H1. auto. }
    expose_log_Vint log H1.
    (* TODO floyd: If I don't do the above to make sure that "temp _logi" is a Vint,
       "forward" fails, with the default error, because it cannot calculate the array index. *)
    forward. { entailer!. expose_pow_Vint pow H3. auto. }
    expose_pow_Vint pow H3.
    forward. forward. forward. forward. forward. forward. forward. forward. forward.

    match goal with
    | |- context [ temp _x (Vint ?v) ] => remember v as x
    end.
    remember (255 - b0) as b1. assert (b0 = 255 - b1) by omega. subst b0. clear Heqb1.
    assert (0 <= b1 < 256) as B1 by omega. clear B0.
    rewrite <- FSb_def in Heqx by omega. subst x.
    match goal with
    | |- context [ temp _y (Vint ?v) ] => forget v as y
    end.

    Intro fsb. Intro rsb. normalize.
    (* TODO floyd if I don't do the above, "forward" fails with the default error message, because
       in store_tac, sc_new_instantiate cannot find the right SEP clause. *)
    forward. forward.
    - (* entailment of "forward" *)
      entailer!.
      apply FSb_range.
    - (* postcondition implies loop invariant *)
      entailer!.
      * rewrite Int.repr_unsigned. reflexivity.
      * match goal with
        | |- field_at _ _ _ ?fsb' _ * field_at _ _ _ ?rsb' _ |-- _ => Exists rsb'; Exists fsb'
        end.
        entailer!. repeat split.
        + rewrite upd_Znth_diff; (omega || auto).
        + rewrite upd_Znth_Zlength; omega.
        + intros.
          assert (0 <= j < Int.unsigned (pow3 (255 - b1)) \/ j = Int.unsigned (pow3 (255 - b1))) as C
          by omega. destruct C as [C | C].
          { rewrite upd_Znth_diff; (omega || auto). }
          { subst j. rewrite upd_Znth_same.
            - repeat rewrite zero_ext_nop; try reflexivity; apply FSb_range.
            - omega.
          }
        + intros.
          assert (0 <= j < Int.unsigned (pow3 (255 - b1)) \/ j = Int.unsigned (pow3 (255 - b1))) as C
          by omega. destruct C as [C | C].
          { rewrite upd_Znth_diff.
            - apply H10. omega.
            - replace (Zlength rsb) with 256 by assumption. apply FSb_range.
            - replace (Zlength rsb) with 256 by assumption. apply FSb_range.
            - intro HH. apply unsigned_eq_eq in HH.
              apply FSb_inj in HH; omega.
          }
          { subst j. rewrite Int.repr_unsigned. rewrite upd_Znth_same.
            - repeat rewrite zero_ext_nop; try reflexivity; omega.
            - replace (Zlength rsb) with 256 by assumption. apply FSb_range.
          }
        + rewrite upd_Znth_diff.
          { auto. }
          { omega. }
          { replace (Zlength rsb) with 256 by assumption. apply FSb_range. }
          { replace 99 with (Int.unsigned (Znth 0 FSb Int.zero)) by reflexivity.
            intro HH. apply unsigned_eq_eq in HH. apply FSb_inj in HH; omega. }
        + rewrite upd_Znth_Zlength; [ omega | ].
          replace (Zlength rsb) with 256 by reflexivity. apply FSb_range.
  }

  (* generate the forward and reverse tables *)
  admit.
} }
Qed.
