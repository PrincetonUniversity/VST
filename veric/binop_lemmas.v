Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.Cop2.
Require Import veric.binop_lemmas2.
Import Cop.

Lemma denote_tc_nonzero_e:
 forall i m, app_pred (denote_tc_nonzero (Vint i)) m -> Int.eq i Int.zero = false.
Proof.
simpl; intros . destruct (Int.eq i Int.zero); auto; contradiction.
Qed.

Lemma denote_tc_nodivover_e:
 forall i j m, app_pred (denote_tc_nodivover (Vint i) (Vint j)) m ->
   Int.eq i (Int.repr Int.min_signed) && Int.eq j Int.mone = false.
Proof.
simpl; intros.
destruct (Int.eq i (Int.repr Int.min_signed) && Int.eq j Int.mone); try reflexivity; contradiction.
Qed.

Lemma Int64_eq_repr_signed32_nonzero:
  forall i, Int.eq i Int.zero = false ->
             Int64.eq (Int64.repr (Int.signed i)) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
rewrite Int64.eq_false; auto.
contradict H0.
unfold Int64.zero in H0.
assert (Int64.signed (Int64.repr (Int.signed i)) = Int64.signed (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.signed_repr in H.
rewrite Int64.signed_repr in H.
rewrite <- (Int.repr_signed i).
rewrite H. reflexivity.
pose proof (Int64.signed_range Int64.zero).
rewrite Int64.signed_zero in H1.
auto.
pose proof (Int.signed_range i).
clear - H1.
destruct H1.
split.
apply Z.le_trans with Int.min_signed; auto.
compute; congruence.
apply Z.le_trans with Int.max_signed; auto.
compute; congruence.
Qed.


Lemma Int64_eq_repr_unsigned32_nonzero:
  forall i, Int.eq i Int.zero = false ->
             Int64.eq (Int64.repr (Int.unsigned i)) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
rewrite Int64.eq_false; auto.
contradict H0.
unfold Int64.zero in H0.
assert (Int64.unsigned (Int64.repr (Int.unsigned i)) = Int64.unsigned (Int64.repr 0)) by (f_equal; auto).
rewrite Int64.unsigned_repr in H.
rewrite Int64.unsigned_repr in H.
rewrite <- (Int.repr_unsigned i).
rewrite H. reflexivity.
split; compute; congruence.
pose proof (Int.unsigned_range i).
clear - H1.
destruct H1.
split; auto.
unfold Int64.max_unsigned.
apply Z.le_trans with Int.modulus.
omega.
compute; congruence.
Qed.

Lemma denote_tc_igt_e:
  forall m i j, app_pred (denote_tc_igt j (Vint i)) m ->
        Int.ltu i j = true.
Proof.
intros.
hnf in H. destruct (Int.ltu i j); auto; contradiction.
Qed.

Lemma denote_tc_iszero_long_e:
 forall m i,
  app_pred (denote_tc_iszero (Vlong i)) m ->
  Int.eq (Int.repr (Int64.unsigned i)) Int.zero = true.
Proof.
intros.
hnf in H.
destruct (Int.eq (Int.repr (Int64.unsigned i)) Int.zero);
  auto; contradiction.
Qed.

Lemma sem_cmp_pp_pp:
  forall c b i b0 i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
 typecheck_val
  match sem_cmp_pp c (Vptr b i) (Vptr b0 i0) with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros; destruct OP; subst; unfold sem_cmp_pp; simpl.
  + destruct (eq_block b b0); [ destruct (Int.eq i i0) |];
    destruct ii,ss; simpl; try reflexivity.
  + destruct (eq_block b b0); [ destruct (Int.eq i i0) |];
    destruct ii,ss; simpl; try reflexivity.
Qed.

Lemma sem_cmp_pp_pp':
  forall c b i b0 i0 ii ss aa m
    (OP: c = Cle \/ c = Clt \/ c = Cge \/ c = Cgt),
    is_true (sameblock (Vptr b i) (Vptr b0 i0)) \/
        (denote_tc_iszero (Vptr b i)) m /\ (denote_tc_iszero (Vptr b0 i0)) m ->
 typecheck_val
  match sem_cmp_pp c (Vptr b i) (Vptr b0 i0) with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros; destruct OP as [| [| [|]]]; subst; unfold sem_cmp_pp; simpl;
  (destruct H as [| [? ?]]; [| inv H]).
  + unfold sameblock in H; unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i0 i);
    destruct ii,ss; simpl; try reflexivity.
  + unfold sameblock in H; unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i i0);
    destruct ii,ss; simpl; try reflexivity.
  + unfold sameblock in H; unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i i0);
    destruct ii,ss; simpl; try reflexivity.
  + unfold sameblock in H; unfold eq_block.
    destruct (peq b b0); [subst | inv H].
    simpl.
    destruct (Int.ltu i0 i);
    destruct ii,ss; simpl; try reflexivity.
Qed.

Lemma sem_cmp_pp_ip:
  forall c b i i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
  i = Int.zero ->
 typecheck_val
  match sem_cmp_pp c (Vint i)  (Vptr b i0)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros; destruct OP; subst; unfold sem_cmp_pp; simpl.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; reflexivity.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; reflexivity.
Qed.
(*
Lemma sem_cmp_lp_lp:
  forall c b i i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
  i = Int64.zero ->
 typecheck_val
  match sem_cmp_lp c (Vlong i)  (Vptr b i0)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros; destruct OP; subst; unfold sem_cmp_lp; simpl.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; reflexivity.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; reflexivity.
Qed.
*)
Lemma sem_cmp_pp_ip':
  forall c b i i0 ii ss aa m
  (OP: c = Cle \/ c = Clt \/ c = Cge \/ c = Cgt),
    False \/ False /\ (denote_tc_iszero (Vint i)) m ->
 typecheck_val
  match sem_cmp_pp c (Vint i) (Vptr b i0)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros.
  exfalso.
  tauto.
Qed.
(*
Lemma sem_cmp_lp_lp':
  forall c b i i' i0 ii ss aa m
  (OP: c = Cle \/ c = Clt \/ c = Cge \/ c = Cgt),
    False \/ False /\ (denote_tc_iszero (Vint i')) m  ->
 typecheck_val
  match sem_cmp_lp c (Vlong i) (Vptr b i0)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros.
  exfalso.
  tauto.
Qed.
*)
Lemma sem_cmp_pp_pi:
  forall c b i i0 ii ss aa
    (OP: c = Ceq \/ c = Cne),
  i = Int.zero ->
 typecheck_val
  match sem_cmp_pp c (Vptr b i0)  (Vint i)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros; destruct OP; subst; unfold sem_cmp_pp; simpl.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; reflexivity.
  + rewrite Int.eq_true.
    destruct ii,ss; simpl; reflexivity.
Qed.

Lemma sem_cmp_pp_pi':
  forall c b i i0 ii ss aa m
  (OP: c = Cle \/ c = Clt \/ c = Cge \/ c = Cgt),
    False \/ False /\ (denote_tc_iszero (Vint i)) m ->
 typecheck_val
  match sem_cmp_pp c (Vptr b i0) (Vint i)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros.
  exfalso.
  tauto.
Qed.
(*
Lemma sem_cmp_pl_pl':
  forall c b i i' i0 ii ss aa m
  (OP: c = Cle \/ c = Clt \/ c = Cge \/ c = Cgt),
    False \/ False /\ (denote_tc_iszero (Vint i')) m ->
 typecheck_val
  match sem_cmp_pl c (Vptr b i0) (Vlong i)  with
  | Some v' => v'
  | None => Vundef
  end (Tint ii ss aa) = true.
Proof.
  intros.
  exfalso.
  tauto.
Qed.
*)
Lemma typecheck_binop_sound:
forall {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType Ole e1 e2 t) rho m)
   (TV2: typecheck_val (eval_expr e2 rho) (typeof e2) = true)
   (TV1: typecheck_val (eval_expr e1 rho) (typeof e1) = true),
   typecheck_val
     (eval_binop Ole (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof.
  intros;
  rewrite den_isBinOpR in IBR; simpl in IBR;
 unfold binarithType in IBR;
 destruct (typeof e1) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ] eqn:TE1;
 try contradiction IBR;
 destruct (typeof e2) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ] eqn:TE2;
 simpl in IBR;
 rewrite ?TE1, ?TE2 in IBR; simpl in IBR; clear TE1 TE2;
 match type of IBR with context [@liftx] => unfold_lift in IBR | _ => idtac end;
 try contradiction IBR;
 try simple apply tc_bool_e in IBR;  try discriminate IBR;
 destruct (eval_expr e1 rho); try discriminate TV1; clear TV1;
 destruct (eval_expr e2 rho); try discriminate TV2; clear TV2;
 clear - IBR;
 destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction IBR; try discriminate IBR;
 simpl; unfold Cop2.sem_div, Cop2.sem_mod,
 Cop2.sem_binarith, Cop2.sem_cast, Cop2.sem_shift,
 force_val, sem_shift_ii, both_int, both_long, both_float,
 sem_cmp_lp, sem_cmp_pl, cast_out_long; simpl;
 repeat (let H := fresh in revert IBR; intros [IBR H];
                try contradiction IBR;
                try contradiction H;
                try (simple apply tc_bool_e in IBR; try discriminate IBR);
                try (simple apply denote_tc_nonzero_e in IBR; try rewrite IBR);
                try (simple apply denote_tc_nodivover_e in H; try rewrite H);
                try (simple apply tc_bool_e in H; try discriminate H));
    try simple apply eq_refl;
    try simple apply typecheck_val_of_bool;
    try (simple apply sem_cmp_pp_pp; solve [auto]);
    try (simple eapply sem_cmp_pp_pp'; solve [eauto]);
    try (simple apply sem_cmp_pp_ip; solve [eauto]);
    try (simple eapply sem_cmp_pp_ip'; [solve [auto] | exact IBR]);
    try (simple apply sem_cmp_pp_pi; solve [auto]);
    try (simple eapply sem_cmp_pp_pi'; [solve [auto] | exact IBR]);
    try (rewrite Int64_eq_repr_signed32_nonzero by assumption; reflexivity);
    try (rewrite Int64_eq_repr_unsigned32_nonzero by assumption; reflexivity);
    try (rewrite (denote_tc_igt_e m) by assumption; reflexivity);
    try (rewrite (denote_tc_iszero_long_e m) by assumption; reflexivity).
    Focus 1.
    simple eapply sem_cmp_pp_ip'; [solve [auto] |].

simpl in IBR.
    exact IBR]);
unfold .    
  (simple eapply sem_cmp_pp_ip; solve [eauto]).
  destruct IBR.
  inv H0.
  inv H0.


  (*
Definition sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_pp =>
      option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
  | cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2) in
          option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n2))
      | _ => None
      end
  | cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
          let n1 := Int.repr (Int64.unsigned n1) in
          option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c (Vint n1) v2)
      | _ => None
      end
  | cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float32.cmp c n1 n2)))
        v1 t1 v2 t2 m
  end.

*)

  
Lemma typecheck_binop_sound:
forall op {CS: compspecs} (rho : environ) m (e1 e2 : expr) (t : type)
   (IBR: denote_tc_assert (isBinOpResultType op e1 e2 t) rho m)
   (TV2: typecheck_val (eval_expr e2 rho) (typeof e2) = true)
   (TV1: typecheck_val (eval_expr e1 rho) (typeof e1) = true),
   typecheck_val
     (eval_binop op (typeof e1) (typeof e2) (eval_expr e1 rho)
        (eval_expr e2 rho)) t = true.
Proof.
Time (* reduced from 548.6 sec to 192 sec *)
destruct op;
try abstract (
  intros;
  rewrite den_isBinOpR in IBR; simpl in IBR;
 unfold binarithType in IBR;
 destruct (typeof e1) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ] eqn:TE1;
 try contradiction IBR;
 destruct (typeof e2) as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ] eqn:TE2;
 simpl in IBR;
 rewrite ?TE1, ?TE2 in IBR; simpl in IBR; clear TE1 TE2;
 match type of IBR with context [@liftx] => unfold_lift in IBR | _ => idtac end;
 try contradiction IBR;
 try simple apply tc_bool_e in IBR;  try discriminate IBR;
 destruct (eval_expr e1 rho); try discriminate TV1; clear TV1;
 destruct (eval_expr e2 rho); try discriminate TV2; clear TV2;
 clear - IBR;
 destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 try contradiction IBR; try discriminate IBR;
 simpl; unfold Cop2.sem_div, Cop2.sem_mod,
 Cop2.sem_binarith, Cop2.sem_cast, Cop2.sem_shift,
 force_val, sem_shift_ii, both_int, both_long, both_float; simpl;
 repeat (let H := fresh in revert IBR; intros [IBR H];
                try contradiction IBR;
                try contradiction H;
                try (simple apply tc_bool_e in IBR; try discriminate IBR);
                try (simple apply denote_tc_nonzero_e in IBR; try rewrite IBR);
                try (simple apply denote_tc_nodivover_e in H; try rewrite H);
                try (simple apply tc_bool_e in H; try discriminate H));
    try simple apply eq_refl;
    try simple apply typecheck_val_of_bool;
    try simple apply sem_cmp_pp_pp;
    try simple apply sem_cmp_pp_pp';
    try (simple apply sem_cmp_pp_ppx; assumption);
    try (simple apply sem_cmp_pp_ppx'; assumption);
    try (simple apply sem_cmp_pp_ppy; assumption);
    try (simple apply sem_cmp_pp_ppy'; assumption);
    try (rewrite Int64_eq_repr_signed32_nonzero by assumption; reflexivity);
    try (rewrite Int64_eq_repr_unsigned32_nonzero by assumption; reflexivity);
    try (rewrite (denote_tc_igt_e m) by assumption; reflexivity);
    try (rewrite (denote_tc_iszero_long_e m) by assumption; reflexivity)
).
Time Qed. (* 24.5 sec *)





