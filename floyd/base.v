From compcert Require Export Clightdefs.
Require Export VST.veric.base.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.veric.juicy_extspec.
Require Import VST.veric.NullExtension.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.floyd.val_lemmas.
Require Export VST.floyd.assert_lemmas.
Require VST.floyd.SeparationLogicAsLogicSoundness.
Export SeparationLogicAsLogicSoundness.MainTheorem.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Def.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Defs.

Local Open Scope logic.

Definition extract_exists_pre:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type) (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R
  := @semax_extract_exists.

Arguments alignof_two_p {env} t.

Lemma co_alignof_pos: forall co, (co_alignof co > 0)%Z.
Proof.
  intros.
  destruct (co_alignof_two_p co).
  pose proof two_power_nat_pos x.
  omega.
Qed.

Section GET_CO.

Context {cs: compspecs}.

Open Scope Z.

Definition co_default (s: struct_or_union): composite.
  apply (Build_composite s nil noattr 0 1 0).
  + intro. inv H.
  + exists 0%nat; auto.
  + exists 0; auto.
Defined.

Definition get_co id :=
  match cenv_cs ! id with
  | Some co => co
  | _ => co_default Struct
  end.

Lemma co_default_consistent: forall su, composite_consistent cenv_cs (co_default su).
Proof.
  intros.
  split.
  + reflexivity.
  + reflexivity.
  + destruct su; reflexivity.
  + reflexivity.
Defined.

Lemma get_co_consistent: forall id, composite_consistent cenv_cs (get_co id).
Proof.
  intros.
  unfold get_co.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + exact (cenv_consistent id co CO).
  + apply co_default_consistent.
Defined.

Lemma get_co_members_nil_sizeof_0: forall id,
  co_members (get_co id) = nil -> co_sizeof (get_co id) = 0%Z.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:?H; [destruct (co_su co) eqn:?H |].
  + pose proof co_consistent_sizeof cenv_cs co (cenv_consistent id co H0).
    unfold sizeof_composite in H2.
    rewrite H1 in H2; clear H1.
    rewrite H in H2; clear H.
    simpl in H2.
    rewrite align_0 in H2 by apply co_alignof_pos.
    auto.
  + pose proof co_consistent_sizeof cenv_cs co (cenv_consistent id co H0).
    unfold sizeof_composite in H2.
    rewrite H1 in H2; clear H1.
    rewrite H in H2; clear H.
    simpl in H2.
    rewrite align_0 in H2 by apply co_alignof_pos.
    auto.
  + reflexivity.
Defined.

Lemma get_co_members_no_replicate: forall id,
  members_no_replicate (co_members (get_co id)) = true.
Proof.
  intros.
  unfold get_co.
  destruct (cenv_cs ! id) as [co |] eqn:?H.
  + exact (cenv_legal_fieldlist id co H).
  + reflexivity.
Defined.

Lemma sizeof_Tstruct: forall id a,
  sizeof (Tstruct id a) = co_sizeof (get_co id).
Proof.
  intros.
  simpl. unfold get_co.
  destruct (cenv_cs ! id); auto.
Qed.

Lemma sizeof_Tunion: forall id a,
  sizeof (Tunion id a) = co_sizeof (get_co id).
Proof.
  intros.
  simpl. unfold get_co.
  destruct (cenv_cs ! id); auto.
Qed.

End GET_CO.

Lemma co_members_get_co_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  co_members (@get_co cs_from id) = co_members (@get_co cs_to id).
Proof.
  intros.
  destruct ((@cenv_cs cs_to) ! id) eqn:?H.
  + pose proof proj1 (coeq_complete _ _ id) (ex_intro _ c H0) as [b ?].
    rewrite H1 in H.
    apply (coeq_consistent _ _ id _ _ H0) in H1.
    unfold test_aux in H.
    destruct b; [| inv H].
    rewrite !H0 in H.
    destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
    simpl in H.
    rewrite !andb_true_iff in H.
    destruct H as [[? _] _].
    apply eqb_list_spec in H; [| apply eqb_member_spec].
    unfold get_co; rewrite H0, H2.
    auto.
  + destruct ((coeq cs_from cs_to) ! id) eqn:?H.
    - pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
      congruence.
    - inv H.
Qed.

Lemma co_sizeof_get_co_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  co_sizeof (@get_co cs_from id) = co_sizeof (@get_co cs_to id).
Proof.
  intros.
  rewrite <- !sizeof_Tstruct with (a := noattr).
  apply sizeof_change_composite.
  auto.
Qed.

Definition member_dec: forall (it0 it1: ident * type), {it0 = it1} + {it0 <> it1}.
  intros.
  destruct it0, it1.
  destruct (ident_eq i i0), (type_eq t t0); [left | right | right | right]; congruence.
Defined.

Fixpoint fold_right_sepcon (l: list mpred) : mpred :=
 match l with
 | nil => emp
 | b::r => b * fold_right_sepcon r
 end.

Inductive LLRR : Type :=
  | LLLL : LLRR
  | RRRR : LLRR.

