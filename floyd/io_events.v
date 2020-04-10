Require Import VST.floyd.proofauto.
Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Eq.SimUpToTaus.
Require Import ITree.Interp.Traces.
(*Import ITreeNotations.*)
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Require Import Morphisms.

Section IO_events.

Context {file_id : Type}.

Inductive IO_event : Type -> Type :=
| ERead (f : file_id) : IO_event byte
| EWrite (f : file_id) (c : byte) : IO_event unit.

Context {E : Type -> Type} `{IO_event -< E}.

Definition read f : itree E byte := embed (ERead f).

Definition write f (c : byte) : itree E unit := embed (EWrite f c).

Definition IO_itree := itree E unit.

(* We need a layer of inclusion to allow us to use the monad laws. *)
Definition ITREE (tr : IO_itree) := EX tr' : _, !!(sutt eq tr tr') &&
  has_ext tr'.

(* this should be in ITrees *)
Global Instance Reflexive_sutt {R} : RelationClasses.Reflexive (@sutt E R R eq).
Proof. intro; apply eutt_sutt; reflexivity. Qed.

(* not in ITree currently because it's specific to unit *)
Lemma bind_ret' : forall E (s : itree E unit), eutt eq (s;; Ret tt) s.
Proof.
  intros.
  etransitivity; [|apply eq_sub_eutt, bind_ret_r].
  apply eqit_bind; [intros []|]; reflexivity.
Qed.

Lemma has_ext_ITREE : forall tr, has_ext tr |-- ITREE tr.
Proof.
  intro; unfold ITREE.
  Exists tr; entailer!.
Qed.

Lemma ITREE_impl' : forall tr tr', sutt eq tr' tr ->
  ITREE tr |-- ITREE tr'.
Proof.
  intros.
  unfold ITREE.
  Intros tr1; Exists tr1; entailer!.
  rewrite trace_incl_iff_sutt in *; unfold trace_incl in *; auto.
Qed.

Lemma ITREE_impl : forall tr tr', eutt eq tr tr' ->
  ITREE tr |-- ITREE tr'.
Proof.
  intros; apply ITREE_impl'.
  apply eutt_sutt; symmetry; auto.
Qed.

Lemma ITREE_ext : forall tr tr', eutt eq tr tr' ->
  ITREE tr = ITREE tr'.
Proof.
  intros; apply pred_ext; apply ITREE_impl; auto.
  symmetry; auto.
Qed.

Global Instance eutt_ITREE :
  Proper (eutt eq ==> eq) ITREE.
Proof. repeat intro. apply ITREE_ext; auto. Qed.

Fixpoint write_list f l : IO_itree :=
  match l with
  | nil => Ret tt
  | c :: rest => write f c ;; write_list f rest
  end.

Lemma write_list_app : forall f l1 l2,
  eutt eq (write_list f (l1 ++ l2)) (write_list f l1;; write_list f l2).
Proof.
  induction l1; simpl in *; intros.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_bind.
    setoid_rewrite IHl1; reflexivity.
Qed.

Definition char0 : Z := 48.
Definition newline := 10.

End IO_events.
