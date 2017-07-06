From compcert Require Export Clightdefs.
Require Export veric.SeparationLogic.
Require Export msl.Extensionality.
Require Export compcert.lib.Coqlib msl.Coqlib2 veric.coqlib4 floyd.coqlib3.
Require Export floyd.jmeq_lemmas.
Require Export veric.juicy_extspec.
Require veric.SeparationLogicSoundness.
Export SeparationLogicSoundness.SoundSeparationLogic.CSL.
Require Import veric.NullExtension.

Local Open Scope logic.

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

