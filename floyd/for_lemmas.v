Require Import VST.floyd.base2.
Require Import VST.floyd.expr_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.forward_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Import Cop.
Local Open Scope logic.

Definition int_type_min_max (t: type): option (Z * Z) :=
match t with
| Tint i s _ =>
    Some
    match s with
    | Unsigned => (0, match i with
                      | IBool => 1
                      | I8 => Byte.max_unsigned
                      | I16 => two_p 16 -1
                      | I32 => Int.max_unsigned
                      end)
    | Signed =>
      match i with
      | IBool => (0, 1)
      | I8 => (Byte.min_signed, Byte.max_signed)
      | I16 => (- two_p (16-1), two_p (16-1) -1)
      | I32 => (Int.min_signed, Int.max_signed)
      end
    end
| Tlong s _ =>
    Some
      match s with
      | Unsigned => (0, Int64.max_unsigned)
      | Signed => (Int64.min_signed, Int64.max_signed)
      end
| _ => None
end.

Inductive range_init_hl (type_lo type_i type_hi: type): (Z -> Z -> Prop) -> Prop :=
| construct_range_init_hl:
  forall int_min_lo int_max_lo int_min_i int_max_i int_min_hi int_max_hi
    int_min int_max,
    is_int32_type type_lo = true ->
    is_int32_type type_i = true ->
    int_type_min_max type_lo = Some (int_min_lo, int_max_lo) ->
    int_type_min_max type_i = Some (int_min_i, int_max_i) ->
    int_type_min_max type_hi = Some (int_min_hi, int_max_hi) ->
    int_min = Z.max int_min_lo int_min_i ->
    int_max = Z.min int_max_i int_max_hi ->
    range_init_hl type_lo type_i type_hi (fun m n =>
      (if Z.ltb int_max_lo int_max
       then m <= int_max_lo /\ int_min <= m <= n
       else int_min <= m <= n) /\
      (if Z.gtb int_min_hi int_min
       then int_min_hi <= n <= int_max
       else n <= int_max)).

Lemma range_init_hl_spec: forall (type_lo type_i type_hi: type) range,
  range_init_hl type_lo type_i type_hi range ->
  exists int_min_lo int_max_lo int_min_i int_max_i int_min_hi int_max_hi
    int_min int_max,
    is_int32_type type_lo = true /\
    is_int32_type type_i = true /\
    int_type_min_max type_lo = Some (int_min_lo, int_max_lo) /\
    int_type_min_max type_i = Some (int_min_i, int_max_i) /\
    int_type_min_max type_hi = Some (int_min_hi, int_max_hi) /\
    int_min = Z.max int_min_lo int_min_i /\
    int_max = Z.min int_max_i int_max_hi /\
    forall m n,
      range m n ->
      m <= int_max_lo /\ int_min <= m <= n /\
      int_min_hi <= n <= int_max.
Proof.
  intros.
  inv H.
  exists int_min_lo, int_max_lo, int_min_i, int_max_i, int_min_hi, int_max_hi, (Z.max int_min_lo int_min_i), (Z.min int_max_i int_max_hi).
  do 7 (split; auto).
  intros.
  destruct (int_max_lo <? Z.min int_max_i int_max_hi) eqn:?H, (int_min_hi >? Z.max int_min_lo int_min_i) eqn:?H.
  + rewrite Z.ltb_lt in H5.
    rewrite Z.gtb_lt in H6.
    omega.
  + rewrite Z.ltb_lt in H5.
    rewrite <- not_true_iff_false, Z.gtb_lt in H6.
    omega.
  + rewrite <- not_true_iff_false, Z.ltb_lt in H5.
    rewrite Z.gtb_lt in H6.
    omega.
  + rewrite <- not_true_iff_false, Z.ltb_lt in H5.
    rewrite <- not_true_iff_false, Z.gtb_lt in H6.
    omega.
Qed.

Inductive range_init_h (type_i type_hi: type): Z -> (Z -> Prop) -> Prop :=
| construct_range_init_h:
  forall int_min_i int_max_i int_min_hi int_max_hi
    int_min int_max,
    is_int32_type type_i = true ->
    int_type_min_max type_i = Some (int_min_i, int_max_i) ->
    int_type_min_max type_hi = Some (int_min_hi, int_max_hi) ->
    int_min = Z.max int_min_i int_min_hi ->
    int_max = Z.min int_max_i int_max_hi ->
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

(*

type_hi
type_i
type_lo (probably equal to type_i)
int_min
int_max
range_prop lo (by type_lo, int_min, int_max)
range_prop hi

who generate type_lo? Do it together by init-setup: type_lo, 

int_min <= lo <= n
maybe lo <= int_max_lo

n <= int_max
maybe int_min_hi <= n <= int_max

*)

Inductive Sfor_inv_rec {cs: compspecs} (Delta: tycontext): ident -> Z -> Z -> expr -> Z -> (environ -> mpred) -> (environ -> mpred) -> (environ -> mpred) -> Prop :=
| Sfor_inv_rec_step': forall A _i i m hi n assert_callee inv0 inv1,
    (forall x: A,
       Sfor_inv_rec Delta _i i m hi n (assert_callee x) (inv0 x) (inv1 x)) ->
    Sfor_inv_rec Delta _i i m hi n (exp assert_callee) (exp inv0) (exp inv1)
| Sfor_inv_rec_end: forall _i i m hi n' n P Q R T1 T2 GV (*tactic callee*),
    local2ptree Q = (T1, T2, nil, GV) ->
    T1 ! _i = None ->
    msubst_eval_expr Delta T1 T2 GV hi = Some n' ->
    Int6432_val (typeof hi) n' n ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta hi ->
    Sfor_inv_rec Delta _i i m hi n
      (PROPx P (LOCALx Q (SEPx R)))
      (PROPx ((m <= i <= n) :: P) (LOCALx (temp _i (Vint (Int.repr i)) :: Q) (SEPx R)))
      (PROPx P (LOCALx (temp _i (Vint (Int.repr i)) :: Q) (SEPx R))).

Lemma Sfor_inv_rec_step {cs: compspecs} (Delta: tycontext): forall A _i i m hi n assert_callee inv0 inv1,
    (forall x: A, exists inv0' inv1',
       Sfor_inv_rec Delta _i i m hi n (assert_callee x) inv0' inv1' /\
       inv0 x = inv0' /\ inv1 x = inv1') ->
    Sfor_inv_rec Delta _i i m hi n (exp assert_callee) (exp inv0) (exp inv1).
Proof.
  intros.
  apply Sfor_inv_rec_step'.
  intros.
  specialize (H x).
  destruct H as [? [? [? [? ?]]]].
  subst; auto.
Qed.

Inductive Sfor_inv {cs: compspecs} (Delta: tycontext):
  forall (_i: ident) (m: Z) (hi: expr) (n: Z)
         (assert_callee: Z -> environ -> mpred)
         (inv0: environ -> mpred)
         (inv1 inv2: Z -> environ -> mpred), Prop :=
| construct_Sfor_inv: forall _i m hi n assert_callee inv0 inv1,
    (forall i i', exists inv0' inv0'' inv1' inv1'', Sfor_inv_rec Delta _i i' m hi n (assert_callee i) inv0'' inv1'' /\ inv0' i' = inv0'' /\ inv0 i = inv0' /\ inv1' i' = inv1'' /\ inv1 i = inv1') ->
    Sfor_inv Delta _i m hi n assert_callee (EX i: Z, inv0 i i) (fun i => inv1 i i) (fun i => inv1 (i+1) i).

(* need to export range_hi? no *)

Inductive Sfor_setup {cs: compspecs} {Espec: OracleKind} (Delta: tycontext):
  forall (_i: ident) (Pre: environ -> mpred) (init: statement) (hi: expr) (type_i: type)
         (m n: Z) (assert_callee: Z -> environ -> mpred)
         (inv0: environ -> mpred), Prop :=
| Sfor_setup_const_init: forall m type_lo _i type_i hi n Pre assert_callee inv0 range,
    range_init_hl type_lo type_i (typeof hi) range ->
    range m n ->
    ENTAIL Delta, Pre |-- assert_callee m ->
    Sfor_setup Delta _i Pre (Sset _i (Econst_int (Int.repr m) type_lo)) hi type_i m n assert_callee inv0
| Sfor_setup_other: forall _i Pre init hi type_i m n assert_callee inv0 range,
    range_init_h type_i (typeof hi) m range ->
    range n ->
    @semax cs Espec Delta Pre init (normal_ret_assert inv0) ->
    Sfor_setup Delta _i Pre init hi type_i m n assert_callee inv0.

Lemma Sfor_inv_rec_spec: forall {cs: compspecs} (Delta: tycontext),
  forall _i i m hi n assert_callee inv0 inv1,
    Sfor_inv_rec Delta _i i m hi n assert_callee inv0 inv1 ->
    ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)) /\
    ENTAIL Delta, inv0 |-- tc_expr Delta hi /\
    (closed_wrt_vars (eq _i) assert_callee) /\
    local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee = inv1 /\
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

Lemma Sfor_inv_spec: forall {cs: compspecs} (Delta: tycontext),
  forall _i m hi n assert_callee inv0 inv1 inv2,
    Sfor_inv Delta _i m hi n assert_callee inv0 inv1 inv2 ->
    ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)) /\
    ENTAIL Delta, inv0 |-- tc_expr Delta hi /\
    (forall v i, subst _i (`v) (assert_callee i) = assert_callee i) /\
    (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee i = inv1 i) /\
    (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee (i+1) = inv2 i) /\
    (EX i: Z, !! (m <= i <= n) && inv1 i = inv0).
Proof.
  intros.
  inv H.
  rename inv3 into inv0, inv4 into inv1.
  assert (forall i i' : Z,
             Sfor_inv_rec Delta _i i' m hi n (assert_callee i) (inv0 i i') (inv1 i i')); [| clear H0].
  {
    intros i i'; specialize (H0 i i').
    destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
    subst; auto.
  }
  specialize (fun i i' => Sfor_inv_rec_spec _ _ _ _ _ _ _ _ _ (H i i')).
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
      (TI: (temp_types (update_tycon Delta init)) ! _i = Some (type_i, true)),
    (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee i = inv1 i) ->
    (EX i: Z, !! (m <= i <= n) && inv1 i = inv0) ->
    (forall v i, subst _i (`v) (assert_callee i) = assert_callee i) ->
    @semax cs Espec Delta Pre init (normal_ret_assert inv0) /\
    exists int_min_i int_max_i int_min_hi int_max_hi,
    is_int32_type type_i = true /\
    int_type_min_max type_i = Some (int_min_i, int_max_i) /\
    int_type_min_max (typeof hi) = Some (int_min_hi, int_max_hi) /\
    int_min_i <= m <= int_max_i /\
    int_min_i <= n <= int_max_i /\
    int_min_hi <= n <= int_max_hi.
Proof.
  intros.
  inv H.
  + remember (typeof hi) as type_hi eqn:?H.
    apply range_init_hl_spec in H3.
    destruct H3 as [int_min_lo [int_max_lo
                   [int_min_i  [int_max_i
                   [int_min_hi [int_max_hi
                   [int_min    [int_max
                                  [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]].
    apply H11 in H4; clear H11.
    destruct H4 as [? [? ?]].
    split.
    - eapply semax_pre; [apply H5 | clear H5].
      eapply semax_post'; [| clear H0].
      {
        apply andp_left2, (exp_right m).
        apply andp_right; [apply prop_right; omega |].
        apply derives_refl', H0.
      }
      assert (exists b, (temp_types Delta) ! _i = Some (type_i, b)) as [? TI'].
      {
        simpl in TI.
        rewrite temp_types_same_type' in TI.
        destruct ((temp_types Delta) ! _i) as [[? ?] |].
        + inv TI.
          eauto.
        + inv TI.
      }
      eapply semax_pre_post'; [| | apply semax_set_forward].
      * eapply derives_trans; [| apply now_later].
        apply andp_right; [| apply andp_left2, derives_refl].
        unfold tc_expr, tc_temp_id.
        replace (typecheck_expr Delta (Econst_int (Int.repr m) type_lo)) with tc_TT
          by (destruct type_lo as [| [| | |] | | | | | | | ]; inv H1; auto).
        unfold typecheck_temp_id.
        rewrite TI'.
        simpl typeof.
        replace (is_neutral_cast (implicit_deref type_lo) type_i) with true
          by (destruct type_lo as [| [| | |] | | | | | | | ]; inv H1; auto).
        simpl tc_bool.
        rewrite <- denote_tc_assert_andp, !tc_andp_TT1.
        unfold isCastResultType.
        replace (Cop2.classify_cast (implicit_deref type_lo) type_i) with cast_case_pointer
          by (destruct type_lo as [| [| | |] | | | | | | | ]; inv H1; auto;
              destruct type_i as [| [| | |] | | | | | | | ]; inv H3; auto).
        change Archi.ptr64 with false; cbv beta iota; simpl orb.
        replace (is_pointer_type type_i && is_pointer_type (implicit_deref type_lo)
            || is_int_type type_i && is_int_type (implicit_deref type_lo))%bool with true
          by (destruct type_lo as [| [| | |] | | | | | | | ]; inv H1; auto;
              destruct type_i as [| [| | |] | | | | | | | ]; inv H3; auto).
        simple_if_tac; intro; simpl; apply TT_right.
      * apply andp_left2.
        Intros old.
        apply andp_derives; [| rewrite H2; auto].
        simpl; intro rho.
        unfold subst, local, lift1; unfold_lift; simpl.
        normalize.
    - exists int_min_i, int_max_i, int_min_hi, int_max_hi.
      do 3 (split; auto).
      pose proof Z.le_min_l int_max_i int_max_hi.
      pose proof Z.le_min_r int_max_i int_max_hi.
      pose proof Z.le_max_l int_min_lo int_min_i.
      pose proof Z.le_max_r int_min_lo int_min_i.
      omega.
  + inv H3.
    split.
    - auto.
    - exists int_min_i, int_max_i, int_min_hi, int_max_hi.
      do 3 (split; auto).
      pose proof Z.le_min_l int_max_i int_max_hi.
      pose proof Z.le_min_r int_max_i int_max_hi.
      pose proof Z.le_max_l int_min_i int_min_hi.
      pose proof Z.le_max_r int_min_i int_min_hi.
      omega.
Qed.

Section Sfor.

Context {cs : compspecs}
        (Delta: tycontext)
        (_i: ident)
        (m n: Z)
        (init: statement)
        (hi: expr)
        (inv0: environ -> mpred)
        (assert_callee inv1: Z -> environ -> mpred)
        (type_i: type)
        (int_min_i int_max_i int_min_hi int_max_hi: Z).

Hypothesis EVAL_hi: ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)).
Hypothesis TC_hi: ENTAIL Delta, inv0 |-- tc_expr Delta hi.
Hypothesis I32_i: is_int32_type type_i = true.
Hypothesis IMM_i: int_type_min_max type_i = Some (int_min_i, int_max_i).
Hypothesis IMM_hi: int_type_min_max (typeof hi) = Some (int_min_hi, int_max_hi).
Hypothesis Range_n: int_min_i <= m <= int_max_i.
Hypothesis Range1_n: int_min_i <= n <= int_max_i.
Hypothesis Range2_n: int_min_hi <= n <= int_max_hi.
Hypothesis TI: (temp_types Delta) ! _i = Some (type_i, true).
Hypothesis EQ_inv1: (forall i : Z, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee i = inv1 i).
Hypothesis EQ_inv0: (EX i : Z, !! (m <= i <= n) && inv1 i)%assert = inv0.

Lemma CLASSIFY_CMP: classify_cmp type_i (typeof hi) = cmp_default.
Proof.
  destruct type_i as [| [| | |] [|] | | | | | | | ]; inv IMM_i; auto;
  destruct (typeof hi) as [| [| | |] [|] | | | | | | | ]; inv IMM_hi; auto.
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
    by (destruct type_i as [| [| | |] [|] | | | | | | | ]; inv IMM_i; auto).
  rewrite tc_andp_TT2.
  
  rewrite denote_tc_assert_andp; apply andp_right; auto.
  rewrite (add_andp _ _ EVAL_hi).
  Intros n'.
  apply andp_left1.

  unfold isBinOpResultType; simpl typeof.
  rewrite CLASSIFY_CMP.
  replace (is_numeric_type type_i) with true
    by (destruct type_i as [| [| | |] [|] | | | | | | | ]; inv IMM_i; auto).
  replace (is_numeric_type (typeof hi)) with true
    by (destruct (typeof hi) as [| [| | |] [|] | | | | | | | ]; inv IMM_hi; auto).
  simpl tc_bool.
  apply TT_right.
Qed.

Lemma Sfor_loop_cond_true: (*s
     (TI: (temp_types Delta) ! _i = Some (type_i, true))
     (IMM: int_type_min_max type_i int_min int_max)
     (N_MAX: n <= int_max),
  ENTAIL Delta, inv0 |-- EX n': val, !! (Int6432_val (typeof hi) n' n) && local (` (eq n') (eval_expr hi)) ->
  (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee i = inv1 i) ->
  (EX i: Z, !! (m <= i <= n) && inv1 i = inv0) ->
  int_min <= m -> *)
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
  rewrite <- H3 in H1.
  forget (eval_expr hi rho) as n'.
  clear H3.
  unfold force_val2, Cop2.sem_cmp in H1.
  rewrite CLASSIFY_CMP in H1.
  destruct (classify_binarith type_i (typeof hi)) as [ [|] | [|] | | |] eqn:H3;
    [| | | | 
     destruct type_i as [| [| | |] [|] | [|] | | | | | |]; inv IMM_i;
     destruct (typeof hi) as [| [| | |] [|] | [|] | | | | | |]; inv IMM_hi; inv H3 ..].
  + unfold sem_cmp_default, Cop2.sem_binarith, binarith_type in H1.
    rewrite H3 in H1.
    destruct type_i as [| [| | |] [|] a_i | [|] | | | | | |]; inv I32_i;
      try solve [destruct (typeof hi) as [| | | [|] | | | | |]; inv H3].
    inv IMM_i.
    destruct (typeof hi) as [| i_hi s_hi a_hi | | [|] | | | | |]; try solve [inv H3].
    change (Cop2.sem_cast (Tint I32 Signed a_i) (Tint I32 Signed noattr))
      with sem_cast_pointer in H1.
    change (Cop2.sem_cast (Tint i_hi s_hi a_hi) (Tint I32 Signed noattr))
      with sem_cast_pointer in H1.
    inv H.
    inv H9.
    simpl in H1.
    unfold Int.lt in H1.
    rewrite !Int.signed_repr in H1 by omega.
    if_tac in H1.
    - omega.
    - exfalso; apply H1; auto.
  + unfold sem_cmp_default, Cop2.sem_binarith, binarith_type in H1.
    rewrite H3 in H1.
    destruct type_i as [| [| | |] s_i a_i | [|] | | | | | |]; inv I32_i;
      try solve [destruct (typeof hi) as [| | | [|] | | | | |]; inv H3].
    destruct (typeof hi) as [| i_hi s_hi a_hi | | [|] | | | | |]; try solve [destruct s_i; inv H3].
    change (Cop2.sem_cast (Tint I32 s_i a_i) (Tint I32 Unsigned noattr))
      with sem_cast_pointer in H1.
    change (Cop2.sem_cast (Tint i_hi s_hi a_hi) (Tint I32 Unsigned noattr))
      with sem_cast_pointer in H1.
    inv H.
    inv H9.
    simpl in H1.
    unfold Int.ltu in H1.
    assert (s_i = Unsigned \/ s_i = Signed /\ s_hi = Unsigned /\ i_hi = I32)
      by (destruct s_i, s_hi, i_hi; auto; inv H3).
    destruct (zle 0 i) as [?H | ?H];
      [| destruct H as [? | [? [? ?]]]; subst; inv IMM_i; [| inv IMM_hi]; omega].
    rewrite !Int.unsigned_repr in H1
      by (destruct H as [? | [? [? ?]]]; subst; inv IMM_i; [| inv IMM_hi]; omega).
    if_tac in H1.
    - omega.
    - exfalso; apply H1; auto.
  + unfold sem_cmp_default, Cop2.sem_binarith, binarith_type in H1.
    rewrite H3 in H1.
    destruct type_i as [| [| | |] s_i a_i | [|] | | | | | |]; inv I32_i.
    destruct (typeof hi) as [| [| | |] [|] | [|] | [|] | | | | |];
      try solve [destruct s_i; inv H3].
    change (Cop2.sem_cast (Tint I32 s_i a_i) (Tlong Signed noattr))
      with (sem_cast_i2l s_i) in H1.
    change (Cop2.sem_cast (Tlong Signed a) (Tlong Signed noattr))
      with (sem_cast_l2l) in H1.
    inv H.
    inv H8.
    simpl in H1.
    unfold Int64.lt in H1.
    replace (cast_int_long s_i (Int.repr i)) with (Int64.repr i) in H1.
    2: {
      unfold cast_int_long.
      destruct s_i; inv IMM_i.
      + rewrite Int.signed_repr by omega; auto.
      + rewrite Int.unsigned_repr by omega; auto.
    }
    inv IMM_hi.
    rewrite !Int64.signed_repr in H1 by (destruct s_i; inv IMM_i; rep_omega).
    if_tac in H1.
    - omega.
    - exfalso; apply H1; auto.
  + unfold sem_cmp_default, Cop2.sem_binarith, binarith_type in H1.
    rewrite H3 in H1.
    destruct type_i as [| [| | |] s_i a_i | [|] | | | | | |]; inv I32_i.
    destruct (typeof hi) as [| [| | |] [|] | [|] | [|] | | | | |];
      try solve [destruct s_i; inv H3].
    change (Cop2.sem_cast (Tint I32 s_i a_i) (Tlong Unsigned noattr))
      with (sem_cast_i2l s_i) in H1.
    change (Cop2.sem_cast (Tlong Unsigned a) (Tlong Unsigned noattr))
      with (sem_cast_l2l) in H1.
    inv H.
    inv H8.
    simpl in H1.
    unfold Int64.ltu in H1.
    replace (cast_int_long s_i (Int.repr i)) with (Int64.repr i) in H1.
    2: {
      unfold cast_int_long.
      destruct s_i; inv IMM_i.
      + rewrite Int.signed_repr by omega; auto.
      + rewrite Int.unsigned_repr by omega; auto.
    }
    inv IMM_hi.
    destruct (zle 0 i) as [?H | ?H]; [| omega].
    rewrite !Int64.unsigned_repr in H1 by (destruct s_i; inv IMM_i; rep_omega).
    if_tac in H1.
    - omega.
    - exfalso; apply H1; auto.
Qed.

Lemma Sfor_loop_cond_false: forall {cs : compspecs} Delta assert_callee inv0 inv1 _i type_i m hi n int_min int_max s
     (TI: (temp_types Delta) ! _i = Some (type_i, true))
     (IMM: int_type_min_max type_i int_min int_max)
     (Thi: int_type_compat type_i (typeof hi) = true)
     (N_MAX: n <= int_max),
  ENTAIL Delta, inv0 |-- local ((` (eq (Vint (Int.repr n)))) (eval_expr hi)) ->
  (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee i = inv1 i) ->
  (EX i: Z, !! (m <= i <= n) && inv1 i = inv0) ->
  int_min <= m ->
  ENTAIL Delta, inv0 && local
    ((` (typed_false (typeof (Ebinop Olt (Etempvar _i type_i) hi (Tint I32 s noattr)))))
       (eval_expr (Ebinop Olt (Etempvar _i type_i) hi (Tint I32 s noattr)))) |--
  inv1 n.
Proof.
  intros.
  rewrite <- andp_assoc, (add_andp _ _ H), <- H1.
  Intros i. assert_PROP (i = n); [| subst; solve_andp].
  rewrite <- H0.
  clear inv0 inv1 H H0 H1.
  simpl eval_expr.
  unfold local, lift1; intro rho; simpl; unfold_lift.
  normalize.
  apply prop_right; auto.
  rewrite <- H0, <- H4 in H; clear H0 H4.
  inv IMM; destruct (typeof hi) as [| [| | |] [|] | | | | | | | ]; inv Thi; auto.
  + change (Val.of_bool (Int.lt (Int.repr i) (Int.repr n)) = nullval) in H.
    unfold Int.lt in H.
    rewrite !Int.signed_repr in H by omega.
    if_tac in H.
    - cbv in H.
      destruct Archi.ptr64; congruence.
    - omega.
  + change (Val.of_bool (Int.ltu (Int.repr i) (Int.repr n)) = nullval) in H.
    unfold Int.ltu in H.
    rewrite !Int.unsigned_repr in H by omega.
    if_tac in H.
    - cbv in H.
      destruct Archi.ptr64; congruence.
    - omega.
  + change (Val.of_bool (Int.ltu (Int.repr i) (Int.repr n)) = nullval) in H.
    unfold Int.ltu in H.
    rewrite !Int.unsigned_repr in H by omega.
    if_tac in H.
    - cbv in H.
      destruct Archi.ptr64; congruence.
    - omega.
Qed.

Lemma Sfor_inc_tc: forall {cs: compspecs} Delta assert_callee inv2 i _i type_i int_min int_max m n s,
  int_type_min_max type_i int_min int_max ->
  (temp_types Delta) ! _i = Some (type_i, true) ->
  m <= i < n ->
  n <= int_max ->
  int_min <= m ->
  (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee (i+1) = inv2 i) ->
  ENTAIL Delta, inv2 i
  |-- tc_expr Delta (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1%Z) (Tint I32 s noattr)) type_i) &&
      tc_temp_id _i (typeof (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i))
        Delta (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i).
Proof.
  intros.
  unfold tc_expr, tc_temp_id.
  inv H; simpl typecheck_expr; unfold typecheck_temp_id.
  + rewrite H0. simpl tc_andp.
    simpl isCastResultType.
    change ((isCastResultType tint tint (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) (Tint I32 s noattr)) tint))) with tc_TT.
    match goal with
    | |- context [ binarithType ?A ?B ?C ?D ?E ] =>
           replace (binarithType A B C D E) with tc_TT by (destruct s; auto)
    end.
    rewrite <- H4, <- denote_tc_assert_andp, tc_andp_TT1, !tc_andp_TT2.
    simpl; intro rho.
    unfold_lift; unfold local, lift1.
    normalize.
    rewrite <- H5.
    simpl.
    apply prop_right.
    rewrite !Int.signed_repr by rep_omega.
    omega.
  + rewrite H0. simpl tc_andp.
    simpl isCastResultType.
    intro rho.
    simpl.
    unfold_lift; unfold local, lift1.
    normalize.
Qed.

Lemma Sfor_inc_entail: forall {cs: compspecs} _i (i: Z) m n type_i int_min int_max assert_callee inv0 inv1 inv2 s,
  int_type_min_max type_i int_min int_max ->
  (forall v i, subst _i (`v) (assert_callee i) = assert_callee i) ->
  (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee i = inv1 i) ->
  (forall i, local (locald_denote (temp _i (Vint (Int.repr i)))) && assert_callee (i+1) = inv2 i) ->
  (EX i: Z, !! (m <= i <= n) && inv1 i = inv0) ->
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
  rewrite <- H3.
  Exists (i + 1).
  rewrite <- H1, <- H2.
  rewrite subst_andp, H0.
  simpl.
  intro rho; unfold local, lift1, subst; unfold_lift.
  normalize.
  rewrite eval_id_same in *.
  subst old.
  normalize.
  apply andp_right; auto.
  apply prop_right.
  split; [omega |].
  rewrite H5; clear H5.
  inv H.
  + destruct s.
    - change (force_val2 (Cop2.sem_add tint (Tint I32 Signed noattr)) (Vint (Int.repr i)) (Vint (Int.repr 1))) with (Vint (Int.add (Int.repr i) (Int.repr 1))).
      rewrite add_repr.
      auto.
    - change (force_val2 (Cop2.sem_add tint (Tint I32 Unsigned noattr)) (Vint (Int.repr i)) (Vint (Int.repr 1))) with (Vint (Int.add (Int.repr i) (Int.repr 1))).
      rewrite add_repr.
      auto.
  + destruct s.
    - change (force_val2 (Cop2.sem_add tuint (Tint I32 Signed noattr)) (Vint (Int.repr i)) (Vint (Int.repr 1))) with (Vint (Int.add (Int.repr i) (Int.repr 1))).
      rewrite add_repr.
      auto.
    - change (force_val2 (Cop2.sem_add tuint (Tint I32 Unsigned noattr)) (Vint (Int.repr i)) (Vint (Int.repr 1))) with (Vint (Int.add (Int.repr i) (Int.repr 1))).
      rewrite add_repr.
      auto.
Qed.
*)
Lemma semax_for :
 forall (Inv: environ->mpred) (n: Z) Espec {cs: compspecs} Delta
           (Pre: environ->mpred)
           (_i: ident) (init: statement) (m: Z) (hi: expr) (body MORE_COMMAND: statement) (Post: ret_assert)
           (type_i type_lo type_hi: type)
           (int_min_i int_max_i: Z)
           (assert_callee: Z -> environ -> mpred)
           (inv0: environ -> mpred)
           (inv1 inv2: Z -> environ -> mpred) s
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (type_i, true))
     (IMM: int_type_min_max type_i = Some (int_min_i, int_max_i))
     (CALLEE: Inv = exp assert_callee)
     (INV: Sfor_inv (update_tycon Delta init) _i m hi n assert_callee inv0 inv1 inv2)
     (INIT: Sfor_init_triple Delta _i Pre init type_i int_min m n assert_callee inv0),
     (forall i, m <= i < n ->
     @semax cs Espec (update_tycon Delta init) (inv1 i)
        body
        (for_ret_assert (inv2 i) Post)) ->
     @semax cs Espec (update_tycon Delta (Sfor init
                (Ebinop Olt (Etempvar _i type_i) hi (Tint I32 Signed noattr))
                body
                (Sset _i (Ebinop Oadd (Etempvar _i type_i) (Econst_int (Int.repr 1) (Tint I32 s noattr)) type_i))))
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
  eapply Sfor_init_triple_spec in INIT; [| eauto ..].
  destruct INIT as [INIT M].

  apply semax_seq' with inv0; [exact INIT | clear INIT].
  forget (update_tycon Delta init) as Delta'; clear Delta.
  apply (semax_loop _ inv0 (EX i: Z, !! (m <= i < n) && inv2 i));
    [apply semax_seq with (EX i : Z, !! (m <= i < n) && inv1 i) |].
  + apply semax_pre with (tc_expr Delta' (Eunop Onotbool (Ebinop Olt (Etempvar _i type_i) hi tint) (Tint I32 Signed noattr)) && inv0).
    {
      apply andp_right; [| solve_andp].
      eapply Sfor_loop_cond_tc; eauto.
    }
    apply semax_ifthenelse; auto.
    - eapply semax_post; [.. | apply semax_skip].
      * unfold RA_normal, normal_ret_assert, overridePost, loop1_ret_assert.
        simpl update_tycon.
        eapply Sfor_loop_cond_true; eauto.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros; apply andp_left2, FF_left.
    - eapply semax_pre; [| apply semax_break].
      unfold RA_break, overridePost, loop1_ret_assert.
      eapply Sfor_loop_cond_false; eauto.
  + simpl update_tycon.
    eapply semax_extensionality_Delta with Delta';
      [apply tycontext_eqv_sub, tycontext_eqv_symm, join_tycon_same |].
    Intros i.
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
      eapply Sfor_inc_tc; eauto.
    - unfold RA_normal, loop2_ret_assert, normal_ret_assert.
      eapply andp_left2, Sfor_inc_entail; eauto.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intros; apply andp_left2, FF_left.
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

Ltac prove_Sfor_inv_rec :=
  match goal with
  | |- Sfor_inv_rec _ _ _ _ _ _ ?assert_callee _ _ =>
    match assert_callee with
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
        | solve_Int_eqm_unsigned
        | default_entailer_for_load_store]
    end
  end.

Ltac prove_Sfor_inv :=
  apply construct_Sfor_inv;
  intros ? ?;
  do 4 eexists;
  split; [prove_Sfor_inv_rec | split; [| split; [| split]]; build_func_abs_right].

Ltac simplify_Sfor_init_triple :=
first
[ simple eapply Sfor_init_triple_const_init; [try rep_omega | reflexivity |]
| simple eapply Sfor_init_triple_other
].

Ltac forward_for_simple_bound'' n Inv :=
  eapply (semax_for Inv n);
  [ reflexivity
  | solve [apply tint_min_max | apply tuint_min_max]
  | reflexivity
  | try rep_omega
  | (reflexivity || fail 1000 "The loop invariant for forward_for_simple_bound should have form (EX i: Z, _).")
  | prove_Sfor_inv
  | simplify_Sfor_init_triple
  | intros; abbreviate_semax;
    repeat
      match goal with
      | |- semax _ (exp (fun x => _)) _ _ =>
          let x' := fresh x in
          apply extract_exists_pre; intro x'; cbv beta
      end
  | ..].

