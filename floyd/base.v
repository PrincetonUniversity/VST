From compcert Require Export Clightdefs.
Require Export VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.veric.juicy_extspec.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.floyd.val_lemmas.
Require Export VST.floyd.assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Export compcert.cfrontend.Ctypes.
Require Export VST.veric.expr.
Require VST.floyd.SeparationLogicAsLogicSoundness.
Export SeparationLogicAsLogicSoundness.MainTheorem.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Def.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_PracticalLogic.CSHL_MinimumLogic.CSHL_Defs.

Global Instance: Params (@semax) 7 := {}.

Create HintDb gather_prop discriminated.
Create HintDb gather_prop_core discriminated.

Ltac gather_prop :=
 autorewrite with gather_prop_core;  (* faster to do this first *)
 autorewrite with gather_prop.

Arguments sizeof {cs} !t / .
Arguments alignof {cs} !t / .

Lemma sizeof_pos: forall {cs: compspecs} (t: type), sizeof t >= 0.
Proof. intros. apply Ctypes.sizeof_pos. Qed.
Lemma alignof_pos: forall {cs: compspecs} (t: type), alignof t > 0.
Proof. intros. apply Ctypes.alignof_pos. Qed.

Definition extract_exists_pre:
  forall `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs},
  forall (A : Type) (P : A -> assert) c E (Delta: tycontext) (R: ret_assert),
  (forall x, semax E Delta (P x) c R) ->
   semax E Delta (∃ x:A, P x) c R
  := @semax_extract_exists.

Arguments alignof_two_p {env} t.

Lemma co_alignof_pos: forall co, (co_alignof co > 0)%Z.
Proof.
  intros.
  destruct (co_alignof_two_p co).
  pose proof two_power_nat_pos x.
  lia.
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
  match cenv_cs !! id with
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
  destruct (cenv_cs !! id) as [co |] eqn:CO.
  + exact (cenv_consistent id co CO).
  + apply co_default_consistent.
Defined.

Lemma get_co_members_nil_sizeof_0: forall id,
  co_members (get_co id) = nil -> co_sizeof (get_co id) = 0%Z.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs !! id) as [co |] eqn:?H; [destruct (co_su co) eqn:?H |].
  + pose proof co_consistent_sizeof cenv_cs co (cenv_consistent id co H0).
    unfold sizeof_composite in H2.
    rewrite H1 in H2; clear H1.
    rewrite H in H2; clear H.
    simpl in H2.
    rewrite -> align_0 in H2 by apply co_alignof_pos.
    auto.
  + pose proof co_consistent_sizeof cenv_cs co (cenv_consistent id co H0).
    unfold sizeof_composite in H2.
    rewrite H1 in H2; clear H1.
    rewrite H in H2; clear H.
    simpl in H2.
    rewrite -> align_0 in H2 by apply co_alignof_pos.
    auto.
  + reflexivity.
Defined.

Lemma get_co_members_no_replicate: forall id,
  members_no_replicate (co_members (get_co id)) = true.
Proof.
  intros.
  unfold get_co.
  destruct (cenv_cs !! id) as [co |] eqn:?H.
  + exact (cenv_legal_fieldlist id co H).
  + reflexivity.
Defined.

Lemma sizeof_Tstruct: forall id a,
  sizeof (Tstruct id a) = co_sizeof (get_co id).
Proof.
  intros. unfold sizeof.
  simpl. unfold get_co.
  destruct (Maps.PTree.get id cenv_cs); auto.
Qed.

Lemma sizeof_Tunion: forall id a,
  sizeof (Tunion id a) = co_sizeof (get_co id).
Proof.
  intros. unfold sizeof.
  simpl. unfold get_co.
  destruct (Maps.PTree.get id cenv_cs); auto.
Qed.

End GET_CO.

Lemma co_members_get_co_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) !! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  co_members (@get_co cs_from id) = co_members (@get_co cs_to id).
Proof.
  intros.
  destruct (Maps.PTree.get id (@cenv_cs cs_to)) eqn: H0.
  + pose proof proj1 (coeq_complete _ _ id) (ex_intro _ c H0) as [b ?].
    setoid_rewrite H1 in H.
    apply (coeq_consistent _ _ id _ _ H0) in H1.
    unfold test_aux in H.
    destruct b; [| inv H].
    rewrite !H0 in H.
    destruct (Maps.PTree.get id (@cenv_cs cs_from)) eqn:?H2; [| inv H].
    simpl in H.
    rewrite !andb_true_iff in H.
    destruct H as [[? _] _].
    apply eqb_list_spec in H; [| apply eqb_member_spec].
    unfold get_co; setoid_rewrite H0; setoid_rewrite H2.
    auto.
  + destruct ((coeq cs_from cs_to) !! id) eqn:?H.
    - pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
      congruence.
    - inv H.
Qed.

Lemma co_sizeof_get_co_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) !! id with
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

Definition member_dec: forall (it0 it1: member), {it0 = it1} + {it0 <> it1}.
  intros.
  destruct it0, it1.
  - destruct (ident_eq id id0); [ | right; congruence].
    destruct (type_eq t t0); [ | right; congruence].
    left; congruence.
  - right; congruence.
  - right; congruence.
  - destruct (ident_eq id id0); [subst | right; congruence].
    destruct (intsize_eq sz sz0);  [subst | right; congruence].
    destruct (signedness_eq sg sg0);  [subst | right; congruence].
    destruct (attr_eq a a0);  [subst | right; congruence].
    destruct (Z.eq_dec width width0);  [subst | right; congruence].
    destruct (bool_dec padding padding0);  [subst | right; congruence].
    left; reflexivity.
Defined.

Fixpoint fold_right_sepcon {PROP : bi} (l: list PROP) : PROP :=
 match l with
 | nil => emp
 | b::r => b ∗ fold_right_sepcon r
 end.

Inductive LLRR : Type :=
  | LLLL : LLRR
  | RRRR : LLRR.

(* Define these so that Floyd tactics can operate on skipn/firstn
   without damage to the user's uses of List.firstn, List.skipn *)
Definition Floyd_skipn [A: Type] :=
  fix skipn (n : nat) (l : list A) {struct n} : list A :=
  match n with
  | 0%nat => l
  | S n0 =>
      match l with
      | nil => nil
      | _ :: l0 => skipn n0 l0
      end
  end.

Definition Floyd_firstn [A: Type] :=
fix firstn (n : nat) (l : list A) {struct n} : list A :=
  match n with
  | 0%nat => nil
  | S n0 =>
      match l with
      | nil => nil
      | a :: l0 => a :: firstn n0 l0
      end
  end.

Lemma Floyd_firstn_eq: @Floyd_firstn = @firstn.
Proof. reflexivity. Qed.

Lemma Floyd_skipn_eq: @Floyd_skipn = @skipn.
Proof. reflexivity. Qed.

Lemma Floyd_firstn_skipn: forall [A : Type] (n : nat) (l : list A),
       Floyd_firstn n l ++ Floyd_skipn n l = l.
Proof. rewrite Floyd_firstn_eq Floyd_skipn_eq; exact @firstn_skipn.
Qed.

Definition Floyd_app [A: Type] :=
fix app (l m : list A) {struct l} : list A :=
  match l with
  | nil => m
  | a :: l1 => a :: app l1 m
  end.

Lemma Floyd_app_eq: @Floyd_app = @app.
Proof. reflexivity. Qed.

#[export] Hint Resolve Share.nontrivial : core.
