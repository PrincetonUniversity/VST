Require Import aes.api_specs.
Require Import aes.partially_filled.
Require Import aes.bitfiddling.
Open Scope Z.

(* Note: x must be non-zero, y is allowed to be zero (because x is a constant in all usages, its
   non-zero-check seems to be removed by the parser). *)
Definition mul_with_table(x y: Z)(pow: list int)(log: list Z): int :=
  if Int.eq (if Int.eq (Int.repr y) Int.zero then Int.zero else Int.one) Int.zero
  then Int.zero
  else Znth (Int.unsigned
               (Int.mods (Int.repr (Znth x log + Znth y log))
                  (Int.repr 255))) pow.

Lemma mul_equiv: forall (x y: Z) (pow : list int) (log : list Z),
  (forall j : Z, 0 <= j < 256 -> Znth j pow = pow3 j) ->
  Zlength pow = 256 ->
  (forall j : Z, 1 <= j < 256 -> Znth j log = log3 (Int.repr j)) ->
  Zlength log = 256 ->
  1 <= x < 256 ->
  0 <= y < 256 ->
  mul_with_table x y pow log = mul (Int.repr x) (Int.repr y).
Proof.
  intros x y pow log Hpow Lpow Hlog Llop Bx By.
  unfold mul_with_table, mul.
  assert (y = 0 \/ 1 <= y < 256) as Cy by omega; destruct Cy as [Cy | Cy];
  subst; simpl.
  - destruct (Int.eq (Int.repr x)); reflexivity.
  - rewrite (Hlog _ Bx). rewrite (Hlog _ Cy).
    destruct (Int.eq (Int.repr x)) eqn: D.
    + apply int_eq_e in D. change Int.zero with (Int.repr 0) in D.
      apply repr_inj_unsigned in D; rep_omega.
    + destruct (Int.eq (Int.repr y) Int.zero).
      * reflexivity.
      * simpl.
        assert (forall j : Z, 0 <= j < 255 -> Znth j pow = pow3 j) as Hpow'. {
          intros. apply Hpow. omega.
        }
        rewrite Hpow'; [ reflexivity | apply mod_range ]; try omega.
        pose proof (log3range x). pose proof (log3range y). omega.
Qed.

Definition Z_to_val(x: Z): val := if zeq x (-1) then Vundef else Vint (Int.repr x).

Lemma Z_to_val_to_Vint: forall j,
  j <> -1 ->
  Z_to_val j = Vint (Int.repr j).
Proof.
  intros. unfold Z_to_val. destruct (zeq j (-1)) as [E | E]. omega. reflexivity.
Qed.

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

(* TODO floyd this lemma should be invoked by entailer!
   Note: in summaray, this already works for data_at, but why doesn't it work for field_at?
   QQQ: And why/how does it work for data_at? *)
Lemma field_at_update_val: forall sh t gfs v v' p,
  v = v' -> field_at sh t gfs v p |-- field_at sh t gfs v' p.
Proof.
  intros. rewrite H. apply derives_refl.
Qed.

Definition rcon_loop_inv00(i: Z)(v_pow v_log: val)(gv: globals)(frozen: list mpred) : environ -> mpred :=
     PROP ( 0 <= i) (* note: the upper bound is added by the tactic, but the lower isn't! *)
     LOCAL (temp _x (Vint (pow2 i));
            lvar _log (tarray tint 256) v_log;
            lvar _pow (tarray tint 256) v_pow;
            gvars gv)
     SEP (FRZL frozen;
          field_at Ews t_struct_tables [StructField _RCON]
                   ((map Vint (repeat_op_table i Int.one times2)) ++ (repeat_op_table (10-i) Vundef id))
                   (gv _tables)).

Definition rcon_loop_inv0(v_pow v_log: val)(gv: globals)(frozen: list mpred) :=  EX i: Z,
  rcon_loop_inv00 i v_pow v_log gv frozen.

(* TODO floyd if I inline inv00 into inv0, why doesn't this typecheck?
Definition rcon_loop_inv(v_pow v_log tables: val) :=
  EX i: Z,
     PROP ( 0 <= i) (* note: the upper bound is added by the tactic, but the lower isn't! *)
     LOCAL (temp _x (Vint (pow2 i));
            lvar _log (tarray tint 256) v_log;
            lvar _pow (tarray tint 256) v_pow;
            gvar _tables tables)
     SEP (field_at Ews t_struct_tables [StructField _RCON]
                   ((map Vint (repeat_op_table i Int.one times2)) ++ (repeat_op_table (10-i) Vundef id))
                   tables).
*)

Definition gen_sbox_inv00 i v_pow v_log log pow gv frozen :=
    PROP ( )
    LOCAL (lvar _log (tarray tint 256) v_log;
           lvar _pow (tarray tint 256) v_pow;
           gvars gv)
    SEP (FRZL frozen; data_at Tsh (tarray tint 256) log v_log; data_at Tsh (tarray tint 256) pow v_pow;
         EX fsb : list val,
           !!(Zlength fsb = 256) &&
           !!(forall j, 0 <= j < i -> Znth j fsb = Vint (Znth j FSb)) &&
           !!(Znth 0 fsb = Vint (Int.repr 99))
           && field_at Ews t_struct_tables [StructField _FSb] fsb (gv _tables);
         EX rsb : list val,
           !!(Zlength rsb = 256) &&
           !!(forall j, 1 <= j < i ->
                (Znth (Int.unsigned (Znth j FSb)) rsb) = Vint (Int.repr j)) &&
           !!(Znth 99 rsb = Vint Int.zero)
           && field_at Ews t_struct_tables [StructField _RSb] rsb (gv _tables)).

Definition gen_sbox_inv0 v_pow v_log log pow gv frozen :=
  EX i: Z, gen_sbox_inv00 i v_pow v_log log pow gv frozen.

(* TODO floyd put in sublist? *)
Lemma list_equiv: forall {T: Type}{d: Inhabitant T} (l1 l2: list T) (n: Z),
  Zlength l1 = n ->
  Zlength l2 = n ->
  (forall j, 0 <= j < n -> Znth j l1 = Znth j l2) ->
  l1 = l2.
Proof.
  intros T d l1. induction l1; intros.
  - cbv in H. subst n. apply Zlength_nil_inv in H0. subst l2. reflexivity.
  - rewrite Zlength_cons in H.
    pose proof (Zlength_nonneg l1).
    rename a into a1. destruct l2 as [ | a2 l2 ].
    * cbv in H0. subst n. omega.
    * f_equal.
      + assert (0 <= 0 < n) as B by omega. specialize (H1 0 B). cbv in H1. assumption.
      + rewrite Zlength_cons in H0. apply (IHl1 l2 (n-1)); try omega.
        intros. assert (0 <= (j+1) < n) as B by omega. specialize (H1 (j+1) B).
        do 2 rewrite Znth_pos_cons in H1 by omega.
        replace (j + 1 - 1) with j in H1 by omega.
        assumption.
Qed.

Definition gen_ftrt_inv00 i v_pow v_log log pow gv :=
    PROP ( )
    LOCAL (lvar _log (tarray tint 256) v_log;
           lvar _pow (tarray tint 256) v_pow;
           gvars gv)
    SEP (data_at Tsh (tarray tint 256) pow v_pow;
         data_at Tsh (tarray tint 256) log v_log;
         field_at Ews t_struct_tables [StructField _FSb] (map Vint FSb) (gv _tables);
         field_at Ews t_struct_tables [StructField _FT0] (partially_filled i 256 calc_FT0) (gv _tables);
         field_at Ews t_struct_tables [StructField _FT1] (partially_filled i 256 calc_FT1) (gv _tables);
         field_at Ews t_struct_tables [StructField _FT2] (partially_filled i 256 calc_FT2) (gv _tables);
         field_at Ews t_struct_tables [StructField _FT3] (partially_filled i 256 calc_FT3) (gv _tables);
         field_at Ews t_struct_tables [StructField _RSb] (map Vint RSb) (gv _tables);
         field_at Ews t_struct_tables [StructField _RT0] (partially_filled i 256 calc_RT0) (gv _tables);
         field_at Ews t_struct_tables [StructField _RT1] (partially_filled i 256 calc_RT1) (gv _tables);
         field_at Ews t_struct_tables [StructField _RT2] (partially_filled i 256 calc_RT2) (gv _tables);
         field_at Ews t_struct_tables [StructField _RT3] (partially_filled i 256 calc_RT3) (gv _tables);
         field_at Ews t_struct_tables [StructField _RCON] (map Vint RCON) (gv _tables)).

Definition gen_ftrt_inv0 v_pow v_log log pow gv :=
  EX i: Z, gen_ftrt_inv00 i v_pow v_log log pow gv.

Lemma add_no_overflow: forall n i log
  (Hn: 1 <= n < 256)
  (Hlog : forall j : Z, 1 <= j < 256 -> Znth j log = log3 (Int.repr j))
  (H1: forall i : Z, Int.unsigned (Znth i RSb) <= Byte.max_unsigned)
  (H3 : (if Int.eq (Znth i RSb) Int.zero
             then Int.zero else Int.one) <> Int.zero),
 Int.min_signed <=
   Int.signed (Int.repr (Znth n log)) +
   Int.signed (Int.repr (Znth (Int.unsigned (Znth i RSb)) log))
   <= Int.max_signed.
Proof. intros.
        destruct (Int.eq (Znth i RSb)) eqn:?; try congruence.
        apply int_eq_false_e in Heqb.
        change Byte.max_unsigned with 255 in H1. clear H3.
        assert (Int.unsigned (Znth i RSb) <> 0).
           contradict Heqb. rewrite <- (Int.repr_unsigned (Znth _ _)).
           rewrite Heqb. reflexivity.
        rewrite Hlog by auto.
        assert (H2 := log3range n). spec H2; auto.
        specialize (H1 i).
        pose proof (Int.unsigned_range (Znth i RSb)).
        assert (H4 := log3range (Int.unsigned (Znth i RSb))).
        spec H4; [omega|].
        rewrite Hlog.
        rewrite Int.signed_repr by rep_omega.
        rewrite Int.signed_repr.
        rep_omega.
        rep_omega.
        omega.
Qed.

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
           lvar _log (tarray tint 256) v_log;
           lvar _pow (tarray tint 256) v_pow;
           gvars gv)
    SEP (EX log : list val,
           !!(Zlength log = 256) &&
           (* Note: log[1] is set to 0 in the first iteration, and overwritten with 255 in the last 
              iteration, so we needn't assert anything about j=0, but we do about j=255.
              And btw, log[0] remains Vundef.
              Think "each j has to be stored in the right cell of the log array". *)
           !!(forall j, 1 <= j < i -> Vint (Int.repr j)
                = Znth (Int.unsigned (pow3 j)) log) &&
           !!(Znth 0 log = Vundef)
           && data_at Tsh (tarray tint 256) log v_log;
         EX pow : list val,
           !!(Zlength pow = 256) &&
           !!(forall j, 0 <= j < i -> Znth j pow = Vint (pow3 j))
           && data_at Tsh (tarray tint 256) pow v_pow;
         tables_uninitialized (gv _tables))).
  { (* init *)
    forward. forward. Exists 0. entailer!. do 2 Exists (repeat Vundef 256).
    entailer!; try apply derives_refl.
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
          - rewrite upd_Znth_diff.
              + assumption.
              + omega.
              + replace (Zlength log) with 256 by assumption. apply pow3_range; omega.
              + intro E. change 0 with (Int.unsigned Int.zero) in E. apply unsigned_eq_eq in E.
                symmetry in E. apply (pow3_not0 i E).
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
          - intros. assert (0 <= j < i \/ j = i) as C by omega. destruct C as [C | C].
            * rewrite upd_Znth_diff by omega. auto.
            * subst. rewrite upd_Znth_same by omega. reflexivity.
        }
  } {
  Intros log pow.

  unfold tables_uninitialized.
  unfold_data_at 3%nat.
  freeze [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] Fr.

  forward_for_simple_bound 10 (rcon_loop_inv0 v_pow v_log gv Fr).
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

  (* Before using log and pow, let's turn these "list val" into "list int" or "list Z", respectively. *)
  rename log into log0, pow into pow0.
  assert (exists pow, pow0 = map Vint pow /\ forall j, 0 <= j < 256 -> Znth j pow = pow3 j)
  as E. {
    exists (map force_int pow0). split.
    - apply list_equiv with (n := 256); rewrite ?Zlength_map; try assumption.
      intros. autorewrite with sublist. rewrite H4 by omega. reflexivity.
    - intros. autorewrite with sublist. rewrite H4 by omega. reflexivity.
  }
  destruct E as [pow [E Hpow]]. subst pow0. clear H4. rewrite Zlength_map in H3. rename H3 into Lpow.
  assert (exists log, log0 = map Z_to_val log /\
                      forall j, 1 <= j < 256 -> Znth j log = log3 (Int.repr j))
  as E. {
    exists (map (fun x => match x with
                          | Vint i => Int.unsigned i
                          | _ => -1
                          end)
                 log0). split.
    - apply list_equiv with (n := 256); rewrite ?Zlength_map; try assumption.
      intros. autorewrite with sublist.
      assert (j = 0 \/ j <> 0) as C by omega. destruct C as [C | C].
      + subst j. rewrite H0. reflexivity.
      + assert (1 <= j < 256) as A by omega.
        specialize (H2 (log3 (Int.repr j))).
        pose proof (log3range j A).
        rewrite pow3log3 in H2 by assumption.
        rewrite <- H2 by assumption.
        rewrite Int.unsigned_repr by rep_omega. unfold Z_to_val.
        destruct (zeq (log3 (Int.repr j)) (-1)) as [E | E]; [ | reflexivity ].
        rewrite E in H4. omega.
    - intros. autorewrite with sublist.
      specialize (H2 (log3 (Int.repr j))).
      pose proof (log3range j H3).
      rewrite pow3log3 in H2 by assumption.
      rewrite <- H2 by assumption.
      rewrite Int.unsigned_repr by rep_omega.
      reflexivity.
  }
  destruct E as [log [E Hlog]]. subst log0. clear H2. rewrite Zlength_map in H1. rename H1 into Llog.
  clear H H0.
  assert (forall j, 1 <= j < 256 ->
    Z_to_val (Znth j log) = Vint (Int.repr (log3 (Int.repr j)))
  ) as Hlog'. {
    intros. rewrite Hlog by assumption. unfold Z_to_val.
    destruct (zeq (log3 (Int.repr j)) (-1)) as [Eq | Ne].
    - pose proof (log3range j). omega.
    - reflexivity.
  }

  Transparent FSb RSb.

  (* generate the forward and reverse S-boxes *)
  thaw Fr.
  freeze [3; 4; 5; 6; 8; 9; 10; 11; 12] Fr.
  forward.
  forward.
  forward_for_simple_bound 256 (gen_sbox_inv0 v_pow v_log (map Z_to_val log) (map Vint pow) gv Fr).
  { (* loop invariant holds initially: *)
    unfold gen_sbox_inv00.
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
    forward. { entailer!. rewrite Hlog' by omega. auto. }
    pose proof (log3range i).
    rewrite Hlog' by omega.
    (* TODO floyd: If I don't do the above to make sure that "temp _logi" is a Vint,
       "forward" fails, with the default error, because it cannot calculate the array index. *)
    forward.

    Ltac fold_rotl1 :=
    repeat match goal with
    | |- context[Int.and (Int.or (Int.shl ?b (Int.repr 1)) (Int.shr ?b (Int.repr 7))) (Int.repr 255)]
      => change (Int.and (Int.or (Int.shl  b (Int.repr 1)) (Int.shr  b (Int.repr 7))) (Int.repr 255))
         with (rotl1 b)
    end.

    forward. forward. fold_rotl1.
    forward. forward. fold_rotl1.
    forward. forward. fold_rotl1.
    forward. forward. fold_rotl1.
    forward.
    rewrite Hpow by omega.
    match goal with
    | |- context [ temp _x (Vint ?v) ] => change v with (calc_FSb_nonzero i)
    end.
    rewrite FSb_equiv by omega.

    Intro fsb. Intro rsb.
    forward. forward.
    - (* entailment of "forward" *)
      entailer!.
      apply FSb_range.
    - (* postcondition implies loop invariant *)
      entailer!.
        match goal with
        | |- (field_at _ _ _ ?fsb' _ * field_at _ _ _ ?rsb' _)%logic |-- _ => Exists rsb'; Exists fsb'
        end.
        entailer!. repeat split.
        + rewrite upd_Znth_diff; (omega || auto).
        + rewrite upd_Znth_Zlength; omega.
        + intros.
          assert (0 <= j < i \/ j = i) as C
          by omega. destruct C as [C | C].
          { rewrite upd_Znth_diff; (omega || auto). }
          { subst j. rewrite upd_Znth_same.
            - repeat rewrite zero_ext_nop; try reflexivity; apply FSb_range.
            - omega.
          }
        + intros.
          assert (1 <= j < i \/ j = i) as C
          by omega. destruct C as [C | C].
          { rewrite upd_Znth_diff.
            - auto.
            - replace (Zlength rsb) with 256 by assumption. apply FSb_range.
            - replace (Zlength rsb) with 256 by assumption. apply FSb_range.
            - intro HH. apply unsigned_eq_eq in HH.
              apply FSb_inj in HH; omega.
          }
          { subst j. rewrite upd_Znth_same.
            - repeat rewrite zero_ext_nop; try reflexivity; rewrite Int.unsigned_repr; rep_omega.
            - replace (Zlength rsb) with 256 by assumption. apply FSb_range.
          }
        + rewrite upd_Znth_diff.
          { auto. }
          { omega. }
          { replace (Zlength rsb) with 256 by assumption. apply FSb_range. }
          { replace 99 with (Int.unsigned (Znth 0 FSb)) by reflexivity.
            intro HH. apply unsigned_eq_eq in HH. apply FSb_inj in HH; omega. }
        + rewrite upd_Znth_Zlength; [ omega | ].
          replace (Zlength rsb) with 256 by reflexivity. apply FSb_range.
  }

  thaw Fr.
  Intro fsb. Intro rsb.

  (* TODO floyd: the following should be done by normalize *)
  assert_PROP (
    (Zlength rsb = 256) /\
    (forall j : Z, 1 <= j < 256 ->
       Znth (Int.unsigned (Znth j FSb)) rsb = Vint (Int.repr j)) /\
    (Znth 99 rsb = Vint Int.zero)
  ) as P. { entailer!. }
  destruct P as [?H [?H ?H]].
  match goal with
  | |- semax ?D (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?e ?Post => match R with
    | [?s0; ?s1; ?s2; ?s3; ?s4; ?s5; ?s6; ?s7; ?s8; ?s9; ?s10; ?s11; ?s12] => match s12 with
      | _ && _ && _ && ?f => apply semax_pre with (P' :=
         (PROPx P (LOCALx Q (SEPx [s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; f]))))
      end
    end
  end. { entailer!. }

  assert (fsb = (map Vint FSb)) as E. {
    apply list_equiv with (n := 256).
    - assumption.
    - rewrite Zlength_map. reflexivity.
    - intros. rewrite Znth_map; auto.
  }
  subst fsb.
  assert (rsb = (map Vint RSb)) as E. {
    apply list_equiv with (n := 256).
    - assumption.
    - rewrite Zlength_map. reflexivity.
    - intros. assert (j = 99 \/ j <> 99) as C by omega. destruct C as [C | C].
      + subst j. auto.
      + rewrite (FSb_RSb_id j) at 1 by assumption. rewrite H4.
        * rewrite Int.repr_unsigned. symmetry. apply Znth_map.
          replace (Zlength RSb) with 256 by reflexivity. omega.
        * assert (Int.unsigned (Znth j RSb) = 0 \/ Int.unsigned (Znth j RSb) <> 0)
          as D by omega. destruct D as [D | D].
          { change 0 with (Int.unsigned Int.zero) in D. apply unsigned_eq_eq in D.
            change Int.zero with (Znth 99 RSb) in D at 1.
            apply RSb_inj in D; omega. }
          { pose proof (RSb_range j). omega. }
  }
  subst rsb.
  clear H H0 H1 H2 H3 H4 H5.

  (* generate the forward and reverse tables *)
  forward_for_simple_bound 256 (gen_ftrt_inv0 v_pow v_log (map Z_to_val log) (map Vint pow) gv).
  { (* loop invariant holds initially: *)
    unfold gen_ftrt_inv00.
    entailer!.
  }
  { (* loop body preserves invariant: *)

    (* forward tables: *)
    assert (forall i, Int.unsigned (Znth i FSb) <= Byte.max_unsigned). {
      pose proof FSb_range as F. intro. change Byte.max_unsigned with 255. specialize (F i0). omega.
    }
    forward.
    Opaque FSb RSb.
    (* t'3 = ( x & 0x80 ) ? 0x1B : 0x00 ) *)
    forward_if_diff (PROP () LOCAL (temp _t'3 (Vint (
      if Int.eq (Int.and (Znth i FSb) (Int.repr 128)) Int.zero
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
      forward.
      match goal with
      | |- context [ temp _y (Vint ?v) ] => change v with (times2 (Znth i FSb))
      end.
      forward.
      forward.
      match goal with
      | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_FT0) (Vint ?v)) _ ] =>
        change v with (calc_FT0 i)
      end.
      rewrite (update_partially_filled i calc_FT0) by assumption.

      Ltac canon_load_result ::= rewrite Znth_partially_filled by omega.
      forward. forward.
      match goal with
      | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_FT1) (Vint ?v)) _ ] =>
        change v with (calc_FT1 i)
      end.
      rewrite (update_partially_filled i calc_FT1) by assumption.

      forward. forward.
      match goal with
      | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_FT2) (Vint ?v)) _ ] =>
        change v with (calc_FT2 i)
      end.
      rewrite (update_partially_filled i calc_FT2) by assumption.

      forward. forward.
      match goal with
      | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_FT3) (Vint ?v)) _ ] =>
        change v with (calc_FT3 i)
      end.
      rewrite (update_partially_filled i calc_FT3) by assumption.

      (* reset back to normal: *)
      Ltac canon_load_result ::= default_canon_load_result.

    (* reverse tables: *)
    assert (forall i, Int.unsigned (Znth i RSb) <= Byte.max_unsigned). {
      pose proof RSb_range as F. intro. change Byte.max_unsigned with 255. specialize (F i0). omega.
    }
    forward.
    (* MUL(0x0E, x, prod1); *)
    assert (forall j, 1 <= j < 256 -> Znth j log <> -1). {
      intros j B. specialize (Hlog j B). pose proof (log3range j B). omega.
    }
    Ltac canon_load_result ::= 
      (* default: *)
      default_canon_load_result;
      (* additional: *)
      try rewrite Z_to_val_to_Vint by
      match goal with
      | H : forall j : Z, 1 <= j < 256 -> Znth j _ <> -1 |- _ => apply H; omega
      end.

    pose proof RSb_range as F. replace 256 with (Zlength log) in F by assumption.
    (* Note: Looking at the expression
       (Sset _t'4 (Ecast (Etempvar _x tint) tbool))
       which should be the parse result of "0x0E && x", it seems that the parser optimized away
       the constant "0x0E"... *)
    forward.
    forward_if_diff (PROP () LOCAL (temp _prod1 (Vint (
      if Int.eq (cast_int_int IBool Unsigned (Znth i RSb)) Int.zero
      then Int.zero
      else (Znth (Int.unsigned
              (Int.mods (Int.repr (Znth 14 log + Znth (Int.unsigned (Znth i RSb)) log))
                        (Int.repr 255))) pow)
    ))) SEP ()).
    { (* TODO floyd: this should be derived automatically from H3 *)
      assert (Int.unsigned (Znth i RSb) <> 0) as Ne. {
        intro E. apply H3. change 0 with (Int.unsigned Int.zero) in E.
        apply unsigned_eq_eq in E. rewrite E. rewrite Int.eq_true. reflexivity.
      }
      pose proof (RSb_range i).
      forward. forward. forward. {
        entailer!.
       (* We have to show that we're not in the case "INT_MIN % -1", because that's undefined behavior.
          TODO floyd: Make sure floyd can solve this automatically, also in solve_efield_denote, so
          that we don't have to factor out the modulo, but can use it directly as the array index. *)
        split.
         intros [? H99]; inv H99.
        clear - Hlog H1 H3.
      apply add_no_overflow; auto; computable.
      }
      assert (0 <= Znth 14 log + Znth (Int.unsigned (Znth i RSb)) log) as A. {
        do 2 rewrite Hlog by omega.
        pose proof (log3range 14).
        pose proof (log3range (Int.unsigned (Znth i RSb))). omega.
      }
      pose proof (mod_range _ 255 A).
      forward.
      entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - exfalso. apply H3. reflexivity.
      - simpl. reflexivity.
    }
    { (* else-branch *)
      forward. entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - simpl. reflexivity.
      - discriminate.
    }

    (* MUL(0x09, x, prod2); *)
    forward.
    forward_if_diff (PROP () LOCAL (temp _prod2 (Vint (
      if Int.eq (cast_int_int IBool Unsigned (Znth i RSb)) Int.zero
      then Int.zero
      else (Znth (Int.unsigned
              (Int.mods (Int.repr (Znth 9 log + Znth (Int.unsigned (Znth i RSb)) log))
                        (Int.repr 255))) pow)
    ))) SEP ()). {
      assert (Int.unsigned (Znth i RSb) <> 0) as Ne. {
        intro E. apply H3. change 0 with (Int.unsigned Int.zero) in E.
        apply unsigned_eq_eq in E. rewrite E. rewrite Int.eq_true. reflexivity.
      }
      pose proof (RSb_range i).
      forward. forward. 
      forward. { 
         entailer!.
         split.
         intros [? H99]; inv H99.
         apply add_no_overflow; auto; computable.
      }
      assert (0 <= Znth 9 log + Znth (Int.unsigned (Znth i RSb)) log) as A. {
        do 2 rewrite Hlog by omega.
        pose proof (log3range 9).
        pose proof (log3range (Int.unsigned (Znth i RSb))). omega.
      }
      pose proof (mod_range _ 255 A).
      forward.
      entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - exfalso. apply H3. reflexivity.
      - simpl. reflexivity.
    }
    { (* else-branch *)
      forward. entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - simpl. reflexivity.
      - discriminate.
    }

    (* MUL(0x0D, x, prod3); *)
    forward.
    forward_if_diff (PROP () LOCAL (temp _prod3 (Vint (
      if Int.eq (cast_int_int IBool Unsigned (Znth i RSb)) Int.zero
      then Int.zero
      else (Znth (Int.unsigned
              (Int.mods (Int.repr (Znth 13 log + Znth (Int.unsigned (Znth i RSb)) log))
                        (Int.repr 255))) pow)
    ))) SEP ()). {
      assert (Int.unsigned (Znth i RSb) <> 0) as Ne. {
        intro E. apply H3. change 0 with (Int.unsigned Int.zero) in E.
        apply unsigned_eq_eq in E. rewrite E. rewrite Int.eq_true. reflexivity.
      }
      pose proof (RSb_range i).
      forward. forward. 
      forward. { 
         entailer!. 
         split. 
         intros [? H99]; inv H99.
         apply add_no_overflow; auto; computable.
      }
      assert (0 <= Znth 13 log + Znth (Int.unsigned (Znth i RSb)) log) as A. {
        do 2 rewrite Hlog by omega.
        pose proof (log3range 13).
        pose proof (log3range (Int.unsigned (Znth i RSb))). omega.
      }
      pose proof (mod_range _ 255 A).
      forward.
      entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - exfalso. apply H3. reflexivity.
      - simpl. reflexivity.
    }
    { (* else-branch *)
      forward. entailer!.
      destruct (Int.eq (Znth i RSb)) eqn: E.
      - simpl. reflexivity.
      - discriminate.
    }

    (* MUL(0x0B, x, prod4); *)
    forward.
    forward_if_diff (PROP () LOCAL (temp _prod4 (Vint (
      if Int.eq (cast_int_int IBool Unsigned (Znth i RSb)) Int.zero
      then Int.zero
      else (Znth (Int.unsigned
              (Int.mods (Int.repr (Znth 11 log + Znth (Int.unsigned (Znth i RSb)) log))
                        (Int.repr 255))) pow)
    ))) SEP ()). {
      assert (Int.unsigned (Znth i RSb) <> 0) as Ne. {
        intro E. apply H3. change 0 with (Int.unsigned Int.zero) in E.
        apply unsigned_eq_eq in E. rewrite E. rewrite Int.eq_true. reflexivity.
      }
      pose proof (RSb_range i).
      forward. forward.
      forward. { 
         entailer!.
         split.
         intros [? H99]; inv H99.
         apply add_no_overflow; auto; computable.
      }
      assert (0 <= Znth 11 log + Znth (Int.unsigned (Znth i RSb)) log) as A. {
        do 2 rewrite Hlog by omega.
        pose proof (log3range 11).
        pose proof (log3range (Int.unsigned (Znth i RSb))). omega.
      }
      pose proof (mod_range _ 255 A).
      forward.
      entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - exfalso. apply H3. reflexivity.
      - simpl. reflexivity.
    }
    { (* else-branch *)
      forward. entailer!.
      destruct (Int.eq (Znth i RSb) Int.zero) eqn: E.
      - simpl. reflexivity.
      - discriminate.
    }
    replace (if Int.eq                      (Znth i RSb)   Int.zero then Int.zero else Int.one)
    with (if Int.eq (Int.repr (Int.unsigned (Znth i RSb))) Int.zero then Int.zero else Int.one)
    by (rewrite Int.repr_unsigned; reflexivity).

    let t := constr:(mul_with_table 14 (Int.unsigned (Znth i RSb)) pow log) in
      let u := eval unfold mul_with_table in t in change u with t.
    let t := constr:(mul_with_table 9 (Int.unsigned (Znth i RSb)) pow log) in
      let u := eval unfold mul_with_table in t in change u with t.
    let t := constr:(mul_with_table 13 (Int.unsigned (Znth i RSb)) pow log) in
      let u := eval unfold mul_with_table in t in change u with t.
    let t := constr:(mul_with_table 11 (Int.unsigned (Znth i RSb)) pow log) in
      let u := eval unfold mul_with_table in t in change u with t.

    pose proof RSb_range.
    do 4 rewrite mul_equiv by (auto || omega).

    forward.
    match goal with
    | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_RT0) (Vint ?v)) _ ] =>
      change v with (calc_RT0 i)
    end.
    rewrite (update_partially_filled i calc_RT0) by assumption.

    Ltac canon_load_result ::= rewrite Znth_partially_filled by omega.
    forward. forward.
    match goal with
    | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_RT1) (Vint ?v)) _ ] =>
      change v with (calc_RT1 i)
    end.
    rewrite (update_partially_filled i calc_RT1) by assumption.

    forward. forward.
    match goal with
    | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_RT2) (Vint ?v)) _ ] =>
      change v with (calc_RT2 i)
    end.
    rewrite (update_partially_filled i calc_RT2) by assumption.

    forward. forward.
    match goal with
    | |- context [ field_at _ _ _ (upd_Znth i (partially_filled i 256 calc_RT3) (Vint ?v)) _ ] =>
      change v with (calc_RT3 i)
    end.
    rewrite (update_partially_filled i calc_RT3) by assumption.

    Ltac canon_load_result ::= default_canon_load_result.

    (* postcondition implies loop invariant: *)
    entailer!.
  }
  unfold partially_filled. change (repeat_op_table (256 - 256) Vundef id) with (@nil val).
  do 8 rewrite app_nil_r.

  (* loop invariant at 256 implies postcondition of gen_tables: *)
  (* TODO floyd "forward" takes forever here, because RT0 is so complex (even thoug it's opaque for
     reduction) *)
  unfold POSTCONDITION, abbreviate.
  unfold tables_initialized.
  unfold_data_at 3%nat.
  change (fill_list 256 calc_FT0) with FT0.
  change (fill_list 256 calc_FT1) with FT1.
  change (fill_list 256 calc_FT2) with FT2.
  change (fill_list 256 calc_FT3) with FT3.
  change (fill_list 256 calc_RT0) with RT0.
  change (fill_list 256 calc_RT1) with RT1.
  change (fill_list 256 calc_RT2) with RT2.
  change (fill_list 256 calc_RT3) with RT3.

  forget RT0 as RT0'.
  forget RT1 as RT1'.
  forget RT2 as RT2'.
  forget RT3 as RT3'.

  forward.
  entailer!.
} }
(*  Show.*)
Time Qed.
(* Coq 8.5.2: 177s
   Coq 8.6  :  75s
*)
