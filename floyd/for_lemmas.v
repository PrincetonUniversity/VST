Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.forward_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.local2ptree_typecheck.
Import Cop.
Import LiftNotation.
Local Open Scope logic.

Definition int_type_min_max (type_i type_hi: type): option (Z * Z) :=
  match type_i, type_hi with
  | Tint I32 Signed _, Tint I32 Unsigned _ => Some (0, Int.max_signed)
  | Tint I32 Signed _, Tint _ _ _ => Some (Int.min_signed, Int.max_signed)
  | Tint I32 Unsigned _, Tint _ _ _ => Some (0, Int.max_unsigned)
  | Tint I32 Signed _, Tlong Unsigned _ => Some (0, Int.max_signed)
  | Tint I32 Signed _, Tlong Signed _ => Some (Int.min_signed, Int.max_signed)
  | Tint I32 Unsigned _, Tlong _ _ => Some (0, Int.max_unsigned)
  | Tlong Signed _, Tint I32 Unsigned _ =>  Some (0, Int.max_unsigned)
  | Tlong Signed _, Tint _ _ _ => Some (0 (*Int.min_signed*), Int.max_signed)
  | Tlong Unsigned _, Tint _ Unsigned _ => Some (0, Int.max_unsigned)
  | Tlong Unsigned _, Tint _ Signed _ =>  Some (0, Int.max_signed)
  | Tlong Signed _, Tlong Unsigned _ => Some (0, Int64.max_signed)
  | Tlong Signed _, Tlong Signed _ => Some (Int64.min_signed, Int64.max_signed)
  | Tlong Unsigned _, Tlong Unsigned _ => Some (0, Int64.max_unsigned)
  | _, _ => None
  end.

Inductive range_init_hl (type_lo type_i type_hi: type): (Z -> Z -> Prop) -> Prop :=
| construct_range_init_hl:
  forall int_min int_max,
    (if is_long_type type_i then is_long_type else is_int_type) type_lo = true ->
    int_type_min_max type_i type_hi = Some (int_min, int_max) ->
    range_init_hl type_lo type_i type_hi (fun m n => int_min <= m <= n /\ n <= int_max).

Inductive range_init_h (type_i type_hi: type): Z -> (Z -> Prop) -> Prop :=
| construct_range_init_h:
  forall int_min int_max,
    int_type_min_max type_i type_hi = Some (int_min, int_max) ->
    range_init_h type_i type_hi int_min (fun n =>
      int_min <= n <= int_max).

Inductive Int_eqm_unsigned: int -> Z -> Prop :=
| Int_eqm_unsigned_repr: forall z, Int_eqm_unsigned (Int.repr z) z.

Inductive Int64_eqm_unsigned: int64 -> Z -> Prop :=
| Int64_eqm_unsigned_repr: forall z, Int64_eqm_unsigned (Int64.repr z) z.

Inductive Int6432_val: type -> val -> Z -> Prop :=
| Int_64_eqm_unsigned_repr: forall s i64 z,
    Int64_eqm_unsigned i64 z ->
    Int6432_val (Tlong s noattr) (Vlong i64) z
| Int_32_eqm_unsigned_repr: forall s i i32 z,
    Int_eqm_unsigned i32 z ->
    Int6432_val (Tint s i noattr) (Vint i32) z.

Lemma Int_eqm_unsigned_repr': forall i z,
  i = Int.repr z ->
  Int_eqm_unsigned i z.
Proof.
  intros.
  subst; constructor.
Qed.

Lemma Int64_eqm_unsigned_repr': forall i z,
  i = Int64.repr z ->
  Int64_eqm_unsigned i z.
Proof.
  intros.
  subst; constructor.
Qed.

Lemma Int_eqm_unsigned_spec: forall i z,
  Int_eqm_unsigned i z -> Int.eqm (Int.unsigned i) z.
Proof.
  intros.
  inv H.
  apply Int.eqm_sym, Int.eqm_unsigned_repr.
Qed.

Lemma Int64_eqm_unsigned_spec: forall i z,
  Int64_eqm_unsigned i z -> Int64.eqm (Int64.unsigned i) z.
Proof.
  intros.
  inv H.
  apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Inductive Sfor_inv_rec (LONG: bool) {cs: compspecs} (Delta: tycontext): ident -> Z -> Z -> expr -> Z -> (environ -> mpred) -> (environ -> mpred) -> (environ -> mpred) -> Prop :=
| Sfor_inv_rec_step': forall A _i i m hi n assert_callee inv0 inv1,
    (forall x: A,
       Sfor_inv_rec LONG Delta _i i m hi n (assert_callee x) (inv0 x) (inv1 x)) ->
    Sfor_inv_rec LONG Delta _i i m hi n (exp assert_callee) (exp inv0) (exp inv1)
| Sfor_inv_rec_end: forall _i i m hi n' n P Q R T1 T2 GV (*tactic callee*),
    local2ptree Q = (T1, T2, nil, GV) ->
    T1 ! _i = None ->
    msubst_eval_expr Delta T1 T2 GV hi = Some n' ->
    Int6432_val (typeof hi) n' n ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta hi ->
    Sfor_inv_rec LONG Delta _i i m hi n
      (PROPx P (LOCALx Q (SEPx R)))
      (PROPx ((m <= i <= n) :: P) (LOCALx (temp _i (if LONG then Vlong (Int64.repr i) else Vint (Int.repr i)) :: Q) (SEPx R)))
      (PROPx P (LOCALx (temp _i (if LONG then Vlong (Int64.repr i) else Vint (Int.repr i)) :: Q) (SEPx R))).

Lemma Sfor_inv_rec_step (LONG: bool) {cs: compspecs} (Delta: tycontext): forall A _i i m hi n assert_callee inv0 inv1,
    (forall x: A, exists inv0' inv1',
       Sfor_inv_rec LONG Delta _i i m hi n (assert_callee x) inv0' inv1' /\
       inv0 x = inv0' /\ inv1 x = inv1') ->
    Sfor_inv_rec LONG Delta _i i m hi n (exp assert_callee) (exp inv0) (exp inv1).
Proof.
  intros.
  apply Sfor_inv_rec_step'.
  intros.
  specialize (H x).
  destruct H as [? [? [? [? ?]]]].
  subst; auto.
Qed.

Inductive Sfor_inv (LONG: bool) {cs: compspecs} (Delta: tycontext):
  forall (_i: ident) (m: Z) (hi: expr) (n: Z)
         (assert_callee: Z -> environ -> mpred)
         (inv0: environ -> mpred)
         (inv1 inv2: Z -> environ -> mpred), Prop :=
| construct_Sfor_inv: forall _i m hi n assert_callee inv0 inv1,
    (forall i i', exists inv0' inv0'' inv1' inv1'', Sfor_inv_rec LONG Delta _i i' m hi n (assert_callee i) inv0'' inv1'' /\ inv0' i' = inv0'' /\ inv0 i = inv0' /\ inv1' i' = inv1'' /\ inv1 i = inv1') ->
    Sfor_inv LONG Delta _i m hi n assert_callee (EX i: Z, inv0 i i) (fun i => inv1 i i) (fun i => inv1 (i+1) i).

Inductive Sfor_setup {cs: compspecs} {Espec: OracleKind} (Delta: tycontext):
  forall (_i: ident) (Pre: environ -> mpred) (init: statement) (hi: expr) (type_i: type)
         (m n: Z) (assert_callee: Z -> environ -> mpred)
         (inv0: environ -> mpred), Prop :=
| Sfor_setup_const_init: forall (m' m: Z) lo _i type_i hi n Pre assert_callee inv0 range,
    range_init_hl (typeof lo) type_i (typeof hi) range ->
    const_only_eval_expr lo = Some (if is_long_type type_i then Vlong (Int64.repr m') else Vint (Int.repr m')) ->
    (if is_long_type type_i then Int64_eqm_unsigned (Int64.repr m') m else Int_eqm_unsigned (Int.repr m') m) ->
    range m n ->
    ENTAIL Delta, Pre |-- assert_callee m ->
    Sfor_setup Delta _i Pre (Sset _i lo) hi type_i m n assert_callee inv0
| Sfor_setup_other: forall _i Pre init hi type_i m n assert_callee inv0 range,
    range_init_h type_i (typeof hi) m range ->
    range n ->
    @semax cs Espec Delta Pre init (normal_ret_assert inv0) ->
    Sfor_setup Delta _i Pre init hi type_i m n assert_callee inv0.

Lemma Sfor_inv_rec_spec (LONG: bool) : forall {cs: compspecs} (Delta: tycontext),
  forall _i i m hi n assert_callee inv0 inv1,
    Sfor_inv_rec LONG Delta _i i m hi n assert_callee inv0 inv1 ->
    ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)) /\
    ENTAIL Delta, inv0 |-- tc_expr Delta hi /\
    (closed_wrt_vars (eq _i) assert_callee) /\
    local (locald_denote (temp _i (if LONG then Vlong (Int64.repr i) else Vint (Int.repr i)))) && assert_callee = inv1 /\
    !! (m <= i <= n) && inv1 = inv0.
Proof.
  intros.
  induction H.
  + split; [| split; [| split; [| split]]].
    - specialize (fun x => proj1 (H0 x)); clear H H0; intros.
      rewrite exp_andp2.
      apply exp_left; auto.
    - specialize (fun x => proj1 (proj2 (H0 x))); clear H H0; intros.
      rewrite exp_andp2.
      apply exp_left; auto.
    - specialize (fun x => proj1 (proj2 (proj2 (H0 x)))); clear H H0; intros.
      apply closed_wrt_exp; auto.
    - specialize (fun x => proj1 (proj2 (proj2 (proj2 (H0 x))))); clear H H0; intros.
      rewrite exp_andp2.
      apply exp_congr; auto.
    - specialize (fun x => proj2 (proj2 (proj2 (proj2 (H0 x))))); clear H H0; intros.
      rewrite exp_andp2.
      apply exp_congr; auto.
  + split; [| split; [| split; [| split]]].
    - eapply (msubst_eval_expr_eq _ P _ _ _ R) in H1.
      erewrite <- (app_nil_l P), <- local2ptree_soundness in H1 by eauto.
      rewrite <- insert_local, <- insert_prop.
      Exists n'.
      normalize.
      eapply derives_trans; [| exact H1].
      solve_andp.
    - rewrite <- insert_local, <- insert_prop.
      eapply derives_trans; [| exact H3].
      solve_andp.
    - erewrite local2ptree_soundness, app_nil_l by eauto.
      apply closed_wrt_PROPx.
      apply closed_wrt_LOCALx; [| apply closed_wrt_SEPx].
      rewrite Forall_forall.
      intros.
      rewrite in_map_iff in H4.
      destruct H4 as [? [? ?]]; subst.
      apply LocalD_complete in H5.
      destruct H5 as [[? [? [? ?]]] | [[? [? [? [? ?]]]] | [? [? ?]]]]; subst.
      * apply closed_wrt_temp.
        intros; subst; congruence.
      * apply closed_wrt_lvar.
      * apply closed_wrt_gvars.
    - rewrite <- insert_local.
      reflexivity.
    - rewrite <- insert_prop.
      reflexivity.
Qed.

Lemma Sfor_inv_spec (LONG: bool): forall {cs: compspecs} (Delta: tycontext),
  forall _i m hi n assert_callee inv0 inv1 inv2,
    Sfor_inv LONG Delta _i m hi n assert_callee inv0 inv1 inv2 ->
    ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)) /\
    ENTAIL Delta, inv0 |-- tc_expr Delta hi /\
    (forall v i, subst _i (`v) (assert_callee i) = assert_callee i) /\
    (forall i, local (locald_denote (temp _i (if LONG then Vlong (Int64.repr i) else Vint (Int.repr i)))) && assert_callee i = inv1 i) /\
    (forall i, local (locald_denote (temp _i (if LONG then Vlong (Int64.repr i) else Vint (Int.repr i)))) && assert_callee (i+1) = inv2 i) /\
    (EX i: Z, !! (m <= i <= n) && inv1 i = inv0).
Proof.
  intros.
  inv H.
  rename inv3 into inv0, inv4 into inv1.
  assert (forall i i' : Z,
             Sfor_inv_rec LONG Delta _i i' m hi n (assert_callee i) (inv0 i i') (inv1 i i')); [| clear H0].
  {
    intros i i'; specialize (H0 i i').
    destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
    subst; auto.
  }
  specialize (fun i i' => Sfor_inv_rec_spec LONG _ _ _ _ _ _ _ _ _ (H i i')).
  clear H; intros.
  split; [| split; [| split; [| split; [| split]]]].
  + Intros i.
    specialize (H i i).
    destruct H as [? _].
    auto.
  + Intros i.
    specialize (H i i).
    destruct H as [_ [? _]].
    auto.
  + intros.
    apply closed_wrt_subst.
    specialize (H i i).
    destruct H as [_ [_ [? _]]].
    auto.
  + intros.
    specialize (H i i).
    destruct H as [_ [_ [_ [? _]]]].
    auto.
  + intros.
    specialize (H (i + 1) i).
    destruct H as [_ [_ [_ [? _]]]].
    auto.
  + apply exp_congr; intros i.
    specialize (H i i).
    destruct H as [_ [_ [_ [_ ?]]]].
    auto.
Qed.

Lemma Sfor_setup_spec: forall {cs: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall _i Pre init type_i hi m n assert_callee inv0 inv1,
    Sfor_setup Delta _i Pre init hi type_i m n assert_callee inv0 ->
    forall
      (TI: (temp_types Delta) ! _i = Some type_i),
    (forall i, local (locald_denote (temp _i (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)))) && assert_callee i = inv1 i) ->
    (EX i: Z, !! (m <= i <= n) && inv1 i = inv0) ->
    (forall v i, subst _i (`v) (assert_callee i) = assert_callee i) ->
    @semax cs Espec Delta Pre init (normal_ret_assert inv0) /\
    exists int_min int_max,
    int_type_min_max type_i (typeof hi) = Some (int_min, int_max) /\
    int_min <= m <= int_max /\
    int_min <= n <= int_max.
Proof.
  intros.
  inv H.
  + remember (typeof hi) as type_hi eqn:?H.
    inv H3.
    split.
    - eapply semax_pre; [apply H7 | clear H7].
      eapply semax_post'; [| clear H0].
      {
        apply andp_left2, (exp_right m).
        apply andp_right; [apply prop_right; lia |].
        apply derives_refl', H0.
      }
      eapply semax_pre_post'; [| | apply semax_set_forward].
      * eapply derives_trans; [| apply now_later].
        apply andp_right; [| apply andp_left2, derives_refl].
        unfold tc_expr, tc_temp_id.
        apply andp_right; [eapply const_only_eval_expr_tc; eauto |].
        unfold typecheck_temp_id.
        rewrite TI.
        simpl typeof.
        replace (is_neutral_cast (implicit_deref (typeof lo)) type_i) with true
        by (destruct type_i as [| [| | |] | [|] | | | | | | ]; inv H8; 
               destruct (typeof lo) as [| [| | |] [|] | [|] | | | | | | ]; inv H1; simpl; auto).
        simpl tc_bool.
        rewrite tc_andp_TT1.
        unfold isCastResultType.
        destruct Archi.ptr64 eqn:Hp;
         destruct type_i as [| [| | |] | [|] | | | | | | ]; inv H8; auto;
         destruct (typeof lo) as [| [| | |] | | | | | | | ]; inv H1; auto;
        simpl denote_tc_assert; rewrite Hp; try apply TT_right;
        simple_if_tac; apply TT_right.
      * apply andp_left2.
        Intros old.
        apply andp_derives; [| rewrite H2; auto].
        simpl; intro rho.
        eapply (const_only_eval_expr_eq (env_set rho _i old)) in H4.
        unfold subst, local, lift1; unfold_lift; simpl.
        rewrite H4.
        set (m'1 := Int64.repr m') in *.
        set (m'2 := Int.repr m') in *. clearbody m'1. clearbody m'2. clear m'.
        destruct (is_long_type type_i); inv H5; normalize.
        split; [auto | congruence].
        split; [auto | congruence].
    - exists int_min, int_max.
      split; auto. lia.
  + inv H3.
    split.
    - auto.
    - exists m, int_max.
      split; auto. lia.
Qed.

Lemma typed_false_tint_e:
  forall v, typed_false tint v -> v = Vint Int.zero.
Proof.
clear; intros.
destruct v; inv H.
pose proof (Int.eq_spec i Int.zero).
destruct (Int.eq i Int.zero); inv H1; auto.
Qed.

Section Sfor.

Context
        {cs : compspecs}
        (Delta: tycontext)
        (_i: ident)
        (m n: Z)
        (init: statement)
        (hi: expr)
        (inv0: environ -> mpred)
        (assert_callee inv1 inv2: Z -> environ -> mpred)
        (type_i: type)
        (int_min int_max: Z).

Hypothesis EVAL_hi: ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)).
Hypothesis TC_hi: ENTAIL Delta, inv0 |-- tc_expr Delta hi.
(*Hypothesis I32_i: (if LONG then is_long_type else is_int32_type) type_i = true. *)
Hypothesis IMM: int_type_min_max type_i (typeof hi) = Some (int_min, int_max).
Hypothesis Range_m: int_min <= m <= int_max.
Hypothesis Range_n: int_min <= n <= int_max.
Hypothesis TI: (temp_types Delta) ! _i = Some type_i.
Hypothesis EQ_inv1: forall i : Z, local (locald_denote (temp _i (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)))) && assert_callee i = inv1 i.
Hypothesis EQ_inv0: (EX i : Z, !! (m <= i <= n) && inv1 i)%assert = inv0.
Hypothesis EQ_inv2: forall i, local (locald_denote (temp _i (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)))) && assert_callee (i+1) = inv2 i.
Hypothesis SUBST_callee: forall v i, subst _i (`v) (assert_callee i) = assert_callee i.

Lemma CLASSIFY_CMP: classify_cmp type_i (typeof hi) = cmp_default.
Proof.
  destruct type_i as [| [| | |] [|] | [|] | | | | | | ];
  destruct (typeof hi) as [| [| | |] [|] | | | | | | | ]; inv IMM; auto.
Qed.

Lemma Sfor_loop_cond_tc:
  ENTAIL Delta, inv0 |-- tc_expr Delta (Eunop Onotbool (Ebinop Olt (Etempvar _i type_i) hi tint) tint).
Proof.
  intros.
  remember (Ebinop Olt (Etempvar _i type_i) hi tint).
  unfold tc_expr at 1; simpl typecheck_expr.
  replace (typeof e) with tint by (rewrite Heqe; auto).
  rewrite tc_andp_TT1.
  subst e.

  Opaque isBinOpResultType.
  simpl typecheck_expr.
  Transparent isBinOpResultType.
  rewrite TI.

  simpl orb.
  simpl snd.
  replace (is_neutral_cast type_i type_i || same_base_type type_i type_i)%bool with true
    by (destruct type_i as [| [| | |] [|] | | | | | | | ]; inv IMM; auto).
  
  rewrite denote_tc_assert_andp; apply andp_right; auto.
  rewrite (add_andp _ _ EVAL_hi).
  Intros n'.
  apply andp_left1.
  rewrite <- EQ_inv0.
  Intros i.
  rewrite <- EQ_inv1.
  rewrite denote_tc_assert_andp; apply andp_right.
 2:{ eapply derives_trans; [ | apply temp_tc_initialized].
    apply andp_derives. apply derives_refl. apply andp_left2.
    apply andp_left1.   apply derives_refl. auto. }
  
  unfold isBinOpResultType; simpl typeof.
  rewrite CLASSIFY_CMP.
  replace (is_numeric_type type_i) with true
    by (destruct type_i as [| [| | |] [|] | | | | | | | ]; inv IMM; auto).
  replace (is_numeric_type (typeof hi)) with true
    by (destruct type_i as [| [| | |] [|] | [|] | | | | | | ]; destruct (typeof hi) as [| [| | |] [|] | [|] | | | | | | ]; inv IMM; auto).
  simpl tc_bool.
  apply TT_right.
Qed.

Lemma Sfor_comparison_Signed_I32: forall i n',
  Int6432_val (typeof hi) n' n ->
  classify_binarith type_i (typeof hi) = bin_case_i Signed ->
  m <= i <= n ->
  force_val (sem_cmp_default Clt type_i (typeof hi) (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') = Vint Int.zero <->
  i >= n.
Proof.
  intros.
  unfold sem_cmp_default, Clight_Cop2.sem_binarith, binarith_type.
  rewrite H0.
  destruct type_i as [| [| | |] [|] a_i | [|] | | | | | |];
    try solve [destruct (typeof hi) as [| [ | | | ] [|] | [|] | [|] | | | | |]; inv H0; inv IMM].
 destruct (typeof hi) as [| [ | | | ] [|] | [|] | [|] | | | | |]; inv H0; inv IMM; inv H; inv H6;
  simpl;
  unfold Int.lt;
  unfold both_int; simpl; unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast;
  destruct Archi.ptr64 eqn:Hp; simpl;  rewrite !Int.signed_repr by rep_lia;
  try solve [if_tac; [split; [intro HH; inv HH | intros; lia] |  split; auto]].
Qed.

Lemma Sfor_comparison_Unsigned_I32: forall i n',
  Int6432_val (typeof hi) n' n ->
  classify_binarith type_i (typeof hi) = bin_case_i Unsigned ->
  m <= i <= n ->
  force_val (sem_cmp_default Clt type_i (typeof hi) (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') = Vint Int.zero <->
  i >= n.
Proof.
  intros.
  unfold sem_cmp_default, Clight_Cop2.sem_binarith, binarith_type.
  rewrite H0.
  destruct type_i as [| [| | |] [|] a_i | [|] | | | | | |];
  destruct (typeof hi) as [| [| | |] [|] | [|] | [|] | | | | |]; inv IMM; inv H0; inv H; inv H6;
  simpl;
  unfold both_int; simpl; unfold Clight_Cop2.sem_cast, Clight_Cop2.classify_cast;
  destruct Archi.ptr64 eqn:Hp; simpl; unfold Int.ltu;
  rewrite ?Int.signed_repr by rep_lia;
  rewrite ?Int.unsigned_repr by rep_lia;
  try solve [if_tac; [split; [intro HH; inv HH | intros; lia] |  split; auto]].
Qed.

Lemma Sfor_comparison_Signed_I64: forall i n',
  Int6432_val (typeof hi) n' n ->
  classify_binarith type_i (typeof hi) = bin_case_l Signed ->
  m <= i <= n ->
  force_val (sem_cmp_default Clt type_i (typeof hi) (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') = Vint Int.zero <->
  i >= n.
Proof.
  intros.
  unfold sem_cmp_default, Clight_Cop2.sem_binarith, binarith_type.
  rewrite H0.
  destruct type_i as [| [| | |] [|] | [|] | | | | | |]; 
  destruct (typeof hi) as [| [| | |] [|] | [|] | [|] | | | | |]; inv IMM; inv H0; inv H; try inv H6; try inv H5;
  unfold both_long, Clight_Cop2.sem_cast; simpl;
  destruct Archi.ptr64 eqn:Hp; simpl;
  unfold Int64.lt;
  rewrite ?Int64.signed_repr by rep_lia;
  rewrite ?Int.signed_repr by rep_lia;
  rewrite ?Int.unsigned_repr by rep_lia;
  if_tac; split; intro Hx; try solve [inv Hx]; try lia; reflexivity.
Qed.

Lemma Sfor_comparison_Unsigned_I64: forall i n',
  Int6432_val (typeof hi) n' n ->
  classify_binarith type_i (typeof hi) = bin_case_l Unsigned ->
  m <= i <= n ->
  force_val (sem_cmp_default Clt type_i (typeof hi) (if is_long_type type_i  then Vlong (Int64.repr i) else Vint (Int.repr i)) n') = Vint Int.zero <->
  i >= n.
Proof.
  intros.
  unfold sem_cmp_default, Clight_Cop2.sem_binarith, binarith_type.
  rewrite H0.
  destruct type_i as [| [| | |] [|] | [|] | | | | | |]; 
  destruct (typeof hi) as [| [| | |] [|] | [|] | [|] | | | | |]; inv H0;
  unfold both_long, Clight_Cop2.sem_cast; simpl;
  destruct Archi.ptr64 eqn:Hp; simpl;
   inv H; try inv H5; try inv H6; simpl;
   inv IMM;
  unfold Int64.ltu;
  rewrite ?Int.signed_repr by rep_lia;
  rewrite ?Int.unsigned_repr by rep_lia;
  rewrite ?Int64.unsigned_repr by rep_lia;
  rewrite ?Int64.signed_repr by rep_lia;
  try ( if_tac; split; intro Hx; try solve [inv Hx]; try lia; reflexivity).
Qed.

Lemma Sfor_loop_cond_true:
  ENTAIL Delta, inv0 && local
    ((` (typed_true (typeof (Ebinop Olt (Etempvar _i type_i) hi tint))))
       (eval_expr (Ebinop Olt (Etempvar _i type_i) hi tint))) |--
  EX i: Z, !! (m <= i < n) && inv1 i.
Proof.
  intros.
  rewrite <- andp_assoc, (add_andp _ _ EVAL_hi), <- EQ_inv0.
  Intros n' i; Exists i.
  rewrite <- EQ_inv1.
  apply andp_right; [| solve_andp].
  simpl eval_expr.
  unfold local, lift1; intro rho; simpl; unfold_lift.
  normalize.
  apply prop_right; auto.
  rewrite <- H4 in H.
  forget (eval_expr hi rho) as n'.
  clear H4.
  rename H5 into H4. rename H into H'. rename H1 into H.
  rename H2 into H2'.
  rename H0 into H2.
  assert (H0 := conj H2' H3). clear H2' H3. rename H' into H1.
  unfold force_val2, Clight_Cop2.sem_cmp in H1.
  rewrite CLASSIFY_CMP in H1.
  destruct (classify_binarith type_i (typeof hi)) as [ [|] | [|] | | |] eqn:H3;
    [| | | | 
      destruct type_i as [| [| | |] [|] | [|] | | | | | |]; try solve [inv IMM];
     destruct (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM; inv H3 ..].
  + assert (H6: force_val (sem_cmp_default Clt type_i (typeof hi)
                           (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') <> Vint Int.zero) 
        by (intro Hx; rewrite Hx in H1; inv H1).
      rewrite Sfor_comparison_Signed_I32 in H6 by auto.
      lia.
  + assert (H6: force_val (sem_cmp_default Clt type_i (typeof hi)
                           (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') <> Vint Int.zero) 
        by (intro Hx; rewrite Hx in H1; inv H1).
      rewrite Sfor_comparison_Unsigned_I32 in H6 by auto.
      lia.
  + assert (H6: force_val (sem_cmp_default Clt type_i (typeof hi)
                           (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') <> Vint Int.zero) 
        by (intro Hx; rewrite Hx in H1; inv H1).
      rewrite Sfor_comparison_Signed_I64 in H6 by auto.
      lia.
  + assert (H6: force_val (sem_cmp_default Clt type_i (typeof hi)
                           (if is_long_type type_i then Vlong (Int64.repr i) else Vint (Int.repr i)) n') <> Vint Int.zero) 
        by (intro Hx; rewrite Hx in H1; inv H1).
      rewrite Sfor_comparison_Unsigned_I64 in H6 by auto.
    lia.
Qed.

Lemma Sfor_loop_cond_false:
  ENTAIL Delta, inv0 && local
    ((` (typed_false (typeof (Ebinop Olt (Etempvar _i type_i) hi tint))))
       (eval_expr (Ebinop Olt (Etempvar _i type_i) hi tint))) |--
  inv1 n.
Proof.
  intros.
  rewrite <- andp_assoc, (add_andp _ _ EVAL_hi), <- EQ_inv0.
  Intros n' i. assert_PROP (i = n); [| subst; solve_andp].
  rewrite <- EQ_inv1.
  simpl eval_expr.
  unfold local, lift1; intro rho; simpl; unfold_lift.
  normalize.
  apply prop_right; auto.
  rename H into H'. rename H1 into H. rename H' into H1.
  rename H0 into H0'. assert (H0 := conj H2 H3). clear H2 H3.
  rename H0' into H2. rename H4 into H3. rename H5 into H4.
  rewrite <- H3 in H1.
  forget (eval_expr hi rho) as n'.
  clear H3.
  unfold force_val2, Clight_Cop2.sem_cmp in H1.
  rewrite CLASSIFY_CMP in H1.
  destruct (classify_binarith type_i (typeof hi)) as [ [|] | [|] | | |] eqn:H3;
    [| | | | 
     destruct type_i as [| [| | |] [|] | [|] | | | | | |]; try solve [inv IMM];
     destruct (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM; inv H3 ..];
    try apply typed_false_tint_e in H1.
  + rewrite Sfor_comparison_Signed_I32 in H1 by auto.
    lia.
  + rewrite Sfor_comparison_Unsigned_I32 in H1 by auto.
    lia.
  + rewrite Sfor_comparison_Signed_I64 in H1 by auto.
    lia.
  + rewrite Sfor_comparison_Unsigned_I64 in H1 by auto.
    lia.
Qed.

Lemma Sfor_inc_tc: forall i s,
  m <= i < n ->
  ENTAIL Delta, inv2 i
  |-- tc_expr Delta (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i) &&
      tc_temp_id _i (typeof (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i))
        Delta (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i).
Proof.
(*  intros until s; intro H'; *) intros.
  unfold tc_expr, tc_temp_id.
  destruct type_i as [| [| | |] [|] | | | | | | |]; 
  simpl typecheck_expr; unfold typecheck_temp_id;
  try solve [destruct (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM].
  + 
    rewrite TI. simpl tc_andp.
    match goal with
    | |- context [ binarithType ?A ?B ?C ?D ?E ] =>
           replace (binarithType A B C D E) with tc_TT by (destruct s; auto)
    end;
     destruct s, (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM;
    rewrite <- EQ_inv2, <- denote_tc_assert_andp, tc_andp_TT1, !tc_andp_TT2;
    rewrite ?denote_tc_assert_andp;
    unfold isCastResultType;
    simpl denote_tc_assert; unfold locald_denote; unfold local, lift1; unfold_lift;
    intro rho; repeat change (andp ?A ?B rho) with (andp (A rho) (B rho)); cbv beta;
    destruct Archi.ptr64 eqn:Hp;
    simpl; Intros; rewrite <- ?H1;
    repeat (simple_if_tac; simpl);
    repeat apply andp_right; try apply prop_right; auto;
    try (unfold eval_id in H1;
          destruct (Map.get (te_of rho) _i); simpl in H1; try discriminate H1; subst v;
          eexists; split; [reflexivity | apply I]);
     rewrite ?Int64.signed_repr by rep_lia;
     rewrite ?Int.signed_repr by rep_lia;
     rep_lia.
  + rewrite TI. simpl tc_andp.
    intro rho.
    simpl.
    rewrite <- EQ_inv2.
    unfold isCastResultType;
    simpl; unfold_lift; unfold local, lift1.
    destruct Archi.ptr64 eqn:Hp;
    normalize.
    apply prop_right.
    exists (Vint (Int.repr i)); split; auto.
    unfold eval_id in H1.
    destruct (Map.get (te_of rho) _i); simpl in H1; inv H1; auto.
    apply andp_right.
    apply prop_right.
       exists (Vint (Int.repr i)); split; auto;
      unfold eval_id in H1;
      destruct (Map.get (te_of rho) _i); simpl in H1; inv H1; auto.
    simple_if_tac; simpl; apply TT_right.
  + 
    rewrite TI. simpl tc_andp.
    match goal with
    | |- context [ binarithType ?A ?B ?C ?D ?E ] =>
           replace (binarithType A B C D E) with tc_TT by (destruct s0; auto)
    end.
     destruct s0, (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM;
    rewrite <- EQ_inv2, <- denote_tc_assert_andp, tc_andp_TT1, !tc_andp_TT2;
    rewrite ?denote_tc_assert_andp;
    unfold isCastResultType;
    simpl denote_tc_assert; unfold locald_denote; unfold local, lift1; unfold_lift;
    intro rho; repeat change (andp ?A ?B rho) with (andp (A rho) (B rho)); cbv beta;
    destruct Archi.ptr64 eqn:Hp;
    simpl; Intros; rewrite <- ?H1;
    repeat (simple_if_tac; simpl);
    repeat apply andp_right; try apply prop_right; auto;
    try (unfold eval_id in H1;
          destruct (Map.get (te_of rho) _i); simpl in H1; try discriminate H1; subst v;
          eexists; split; [reflexivity | apply I]);
     rewrite ?Int64.signed_repr by rep_lia;
     rewrite ?Int.signed_repr by rep_lia;
     rep_lia.
Qed.

Lemma Sfor_inc_entail: forall i s,
  m <= i < n ->
  EX old : val,
  local
    ((` eq) (eval_id _i)
       (subst _i (` old)
          (eval_expr (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i)))) &&
    subst _i (` old) (inv2 i) |--
  inv0.
Proof.
  intros.
  Intros old.
  rewrite <- EQ_inv0.
  Exists (i + 1).
  rewrite <- EQ_inv1, <- EQ_inv2.
  rewrite subst_andp, SUBST_callee.
  simpl.
  intro rho; unfold local, lift1, subst; unfold_lift.
  normalize.
  rewrite eval_id_same in *.
  subst old.
  normalize.
  apply andp_right; auto.
  apply prop_right.
  split; [lia |].
  rewrite H0; clear H0.
  clear H2.
  destruct type_i as [| [| | |] [|] | | | | | | |];
  try solve [destruct (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM];
  simpl;
  destruct s; try destruct s0; unfold Clight_Cop2.sem_binarith; simpl;
  unfold both_int; simpl; unfold Clight_Cop2.sem_cast; simpl;
  destruct Archi.ptr64 eqn:Hp; simpl;
  (split; [ | congruence]);
   rewrite ?add_repr, ?add64_repr;
   reflexivity.
Qed.

End Sfor.

Lemma semax_for:
 forall (Inv: environ->mpred) (n: Z) Espec {cs: compspecs} Delta
           (Pre: environ->mpred)
           (_i: ident) (init: statement) (m: Z) (hi: expr) (body MORE_COMMAND: statement) (Post: ret_assert)
           (type_i: type)
           (assert_callee: Z -> environ -> mpred)
           (inv0: environ -> mpred)
           (inv1 inv2: Z -> environ -> mpred) s
     (TI: (temp_types Delta) ! _i = Some type_i),
    forall
     (CALLEE: Inv = exp assert_callee)
     (INV: Sfor_inv (is_long_type type_i) Delta _i m hi n assert_callee inv0 inv1 inv2)
     (SETUP: Sfor_setup Delta _i Pre init hi type_i m n assert_callee inv0),
     (forall i, m <= i < n ->
     @semax cs Espec Delta (inv1 i)
        body
        (for_ret_assert (inv2 i) Post)) ->
     @semax cs Espec Delta
        (inv1 n) MORE_COMMAND Post ->
     @semax cs Espec Delta Pre
       (Ssequence
         (Sfor init
                (Ebinop Olt (Etempvar _i type_i) hi (Tint I32 Signed noattr))
                body
                (Sset _i (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i)))
         MORE_COMMAND) Post.
Proof.
  intros.
  destruct Post as [nPost bPost cPost rPost].
  apply semax_seq with (inv1 n); [clear H0 | exact H0].
  apply semax_post with {| RA_normal := inv1 n; RA_break := FF; RA_continue := FF; RA_return := rPost |};
    [apply andp_left2, derives_refl | apply andp_left2, FF_left | apply andp_left2, FF_left | intros; simpl RA_return; solve_andp |].
  simpl for_ret_assert in H.
  clear bPost cPost.
  unfold Sfor.

  apply Sfor_inv_spec in INV.
  destruct INV as [? [? [? [? [? ?]]]]].
  eapply Sfor_setup_spec in SETUP; [| eauto ..].
  destruct SETUP as [INIT [init_min_i [init_max_i [init_min_hi [init_max_hi [? ?]]]]]].

  apply semax_seq' with inv0; [exact INIT | clear INIT].
  apply (semax_loop _ inv0 (EX i: Z, !! (m <= i < n) && inv2 i));
    [apply semax_seq with (EX i : Z, !! (m <= i < n) && inv1 i) |].
  + apply semax_pre with (tc_expr Delta (Eunop Onotbool (Ebinop Olt (Etempvar _i type_i) hi tint) (Tint I32 Signed noattr)) && inv0).
    {
      apply andp_right; [| solve_andp].
      eapply Sfor_loop_cond_tc; eauto.
    }
    apply semax_ifthenelse; auto.
    - eapply semax_post; [.. | apply semax_skip].
      * unfold RA_normal, normal_ret_assert, overridePost, loop1_ret_assert.
        eapply Sfor_loop_cond_true; eauto.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros; apply andp_left2, FF_left.
    - eapply semax_pre; [| apply semax_break].
      unfold RA_break, overridePost, loop1_ret_assert.
      eapply Sfor_loop_cond_false; eauto.
  + Intros i.
    apply semax_extract_prop; intros.
    unfold loop1_ret_assert.
    eapply semax_post; [.. | apply H; auto].
    - unfold RA_normal.
      apply (exp_right i).
      apply andp_right; [apply prop_right | apply andp_left2]; auto.
    - unfold RA_break.
      intro; simpl;
      apply andp_left2, FF_left.
    - unfold RA_continue.
      apply (exp_right i).
      apply andp_right; [apply prop_right | apply andp_left2]; auto.
    - intros.
      apply andp_left2, derives_refl.
  + Intros i.
    apply semax_extract_prop; intros.
    eapply semax_pre_post; [.. | apply semax_set_forward].
    - eapply derives_trans; [| apply now_later].
      apply andp_right; [| apply andp_left2, derives_refl].
      eapply (Sfor_inc_tc _ _ m n); eauto.
    - unfold RA_normal, loop2_ret_assert, normal_ret_assert.
      eapply andp_left2, (Sfor_inc_entail _ _ m n); eauto.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intros; apply andp_left2, FF_left.
Qed.

Lemma semax_for_x :
 forall (Inv: environ->mpred) (n: Z) Espec {cs: compspecs} Delta
           (Pre: environ->mpred)
           (_i: ident) (init: statement) (m: Z) (hi: expr) (body MORE_COMMAND: statement) (Post: ret_assert)
           (type_i: type)
           (assert_callee: Z -> environ -> mpred)
           (inv0: environ -> mpred)
           (inv1 inv2: Z -> environ -> mpred) s
           test incr,
     test = Ebinop Olt (Etempvar _i type_i) hi (Tint I32 Signed noattr) ->
     incr = Sset _i (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i) ->
     forall
     (TI: (temp_types Delta) ! _i = Some type_i)
     (CALLEE: Inv = exp assert_callee)
     (INV: Sfor_inv (is_long_type type_i) Delta _i m hi n assert_callee inv0 inv1 inv2)
     (SETUP: Sfor_setup Delta _i Pre init hi type_i m n assert_callee inv0),
     (forall i, m <= i < n ->
     @semax cs Espec Delta (inv1 i)
        body
        (for_ret_assert (inv2 i) Post)) ->
     @semax cs Espec Delta
        (inv1 n) MORE_COMMAND Post ->
     @semax cs Espec Delta Pre
       (Ssequence (Sfor init test body incr)
         MORE_COMMAND) Post.
Proof.
intros.
subst test incr.
eapply semax_for; eauto.
Qed.

Lemma quick_derives_right:
  forall P Q : environ -> mpred,
   TT |-- Q -> P |-- Q.
Proof.
intros. eapply derives_trans; try eassumption; auto.
Qed.

Ltac quick_typecheck3 :=
 clear;
 repeat match goal with
 | H := _ |- _ => clear H
 | H : _ |- _ => clear H
 end;
 apply quick_derives_right; clear; go_lowerx; intros;
 clear; repeat apply andp_right; auto; fail.

Ltac default_entailer_for_load_store :=
  repeat match goal with H := _ |- _ => clear H end;
  try quick_typecheck3;
  unfold tc_expr; simpl typeof;
  try solve [entailer!].

Ltac solve_Int_eqm_unsigned :=
    autorewrite with norm;
    match goal with
    | |- Int_eqm_unsigned ?V _ =>
      match V with
      | Int.repr _ => idtac
      | Int.sub _ _ => unfold Int.sub at 1
      | Int.add _ _ => unfold Int.add at 1
      | Int.mul _ _ => unfold Int.mul at 1
      | Int.and _ _ => unfold Int.and at 1
      | Int.or _ _ => unfold Int.or at 1
(*      | Int.shl _ _ => unfold Int.shl at 1
      | Int.shr _ _ => unfold Int.shr at 1*)
      | _ => rewrite <- (Int.repr_unsigned V) at 1
      end
    end;
    first [apply Int_eqm_unsigned_repr | apply Int_eqm_unsigned_repr'].

Ltac solve_Int64_eqm_unsigned :=
    autorewrite with norm;
    match goal with
    | |- Int64_eqm_unsigned ?V _ =>
      match V with
      | Int64.repr _ => idtac
      | Int64.sub _ _ => unfold Int64.sub at 1
      | Int64.add _ _ => unfold Int64.add at 1
      | Int64.mul _ _ => unfold Int64.mul at 1
      | Int64.and _ _ => unfold Int64.and at 1
      | Int64.or _ _ => unfold Int64.or at 1
      | _ => rewrite <- (Int64.repr_unsigned V) at 1
      end
    end;
    first [apply Int64_eqm_unsigned_repr | apply Int64_eqm_unsigned_repr'].

Ltac prove_Int6432_val :=
  first [ apply Int_64_eqm_unsigned_repr; solve_Int64_eqm_unsigned
        | apply Int_32_eqm_unsigned_repr; solve_Int_eqm_unsigned].

Ltac prove_Sfor_inv_rec :=
  match goal with
  | |- Sfor_inv_rec _ _ _ _ _ _ _ ?assert_callee _ _ =>
    lazymatch assert_callee with
    | exp (fun x => _) =>
        let x' := fresh x in
        eapply Sfor_inv_rec_step;
        intros x';
        do 2 eexists;
        split; [prove_Sfor_inv_rec | split; build_func_abs_right]
    | _ =>
        eapply Sfor_inv_rec_end;
        [ prove_local2ptree
        | reflexivity
        | solve_msubst_eval_expr
        | prove_Int6432_val
        | default_entailer_for_load_store]
    end
  end.

Ltac prove_Sfor_inv :=
  apply construct_Sfor_inv;
  intros ? ?;
  do 4 eexists;
  split; [prove_Sfor_inv_rec | split; [| split; [| split]]; build_func_abs_right].

Ltac simplify_Zmax a b :=
  let c := eval hnf in (Z.compare a b) in
  change (Z.max a b) with (match c with | Lt => b | _ => a end); cbv beta iota.

Ltac simplify_Zmin a b :=
  let c := eval hnf in (Z.compare a b) in
  change (Z.min a b) with (match c with | Gt => b | _ => a end); cbv beta iota.

Ltac prove_range_init_hl :=
  eapply construct_range_init_hl; reflexivity.

Ltac prove_range_init_h :=
  eapply construct_range_init_h; reflexivity.

Ltac simplify_Sfor_setup :=
  first
  [ simple eapply Sfor_setup_const_init;
    [ prove_range_init_hl
    | reflexivity
    | try change (if is_long_type _ then ?A else ?B) with A;
      try change (if is_long_type _ then ?A else ?B) with B;
      first [solve_Int_eqm_unsigned | solve_Int64_eqm_unsigned]
    | cbv beta;
      repeat match goal with
             | |- _ <= _ <= _ => fail
             | |- _ /\ _ => split
             end;
      try rep_lia
    | ]
  | simple eapply Sfor_setup_other;
    [ prove_range_init_h
    | cbv beta; try rep_lia
    | ]
].

Ltac check_forloop_test :=
 reflexivity ||
 match goal with |- ?test = ?desired =>
  fail "To use forward_for_simple_bound, your loop test must have the form i<n, where i is the loop iteration variable and n is the bound expression.
 You have:" test "
Required:" desired
  end.

Ltac check_forloop_incr :=
 reflexivity ||
 match goal with |- ?incr = ?desired =>
  fail "To use forward_for_simple_bound, your loop increment must be i=i+1, where i is the loop iteration variable.
 You have:" incr "
Required:" desired
  end.

Ltac forward_for_simple_bound'' n Inv :=
  eapply (semax_for_x Inv n);
  [ check_forloop_test
  | check_forloop_incr
  | reflexivity
  | (reflexivity || fail 1000 "The loop invariant for forward_for_simple_bound should have form (EX i: Z, _).")
  | prove_Sfor_inv
  | try change (if is_long_type _ then ?A else ?B) with A;
    try change (if is_long_type _ then ?A else ?B) with B;
    simplify_Sfor_setup
  | intros;
    try change (if is_long_type _ then ?A else ?B) with A;
    try change (if is_long_type _ then ?A else ?B) with B;
    abbreviate_semax;
    repeat
      match goal with
      | |- semax _ (exp (fun x => _)) _ _ =>
          let x' := fresh x in
          apply extract_exists_pre; intro x'; cbv beta
      end
  | try change (if is_long_type _ then ?A else ?B) with A;
    try change (if is_long_type _ then ?A else ?B) with B;
    idtac ].

