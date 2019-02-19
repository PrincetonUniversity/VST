Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_extspec.
Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
Require Import DeepWeb.Free.Monad.Eq.Utt.
Import String.
Require Import VST.progs.io_mem. (* for CompSpecs -- do we need this? *)

Inductive IO_event : Type -> Type :=
| ERead : IO_event int
| EWrite (c : int) : IO_event unit.

Definition read : itree IO_event int := embed ERead.

Definition write (c : int) : itree IO_event unit := embed (EWrite c).

Definition IO_itree := itree IO_event unit.

Fixpoint write_list l : IO_itree :=
  match l with
  | nil => Ret tt
  | c :: rest => write c ;; write_list rest
  end.

Fixpoint read_list_aux n d : itree IO_event (list int) :=
  match n with
  | O => Ret d
  | S n' => x <- read ;; read_list_aux n' (x :: d)
  end.

Definition read_list n : itree IO_event (list int) := read_list_aux n [].

(* We need a layer of equivalence to allow us to use the monad laws. *)
Definition ITREE (tr : IO_itree) := EX tr' : _, !!(eq_utt tr tr') &&
  has_ext tr'.

Lemma has_ext_ITREE : forall tr, has_ext tr |-- ITREE tr.
Proof.
  intro; unfold ITREE.
  Exists tr; entailer!.
Qed.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition putchars_spec := DECLARE _putchars
  WITH sh : share, buf : val, msg : list int, k : IO_itree
  PRE [ 1%positive OF tint ]
    PROP (readable_share sh)
    LOCAL (temp 1%positive buf)
    SEP (ITREE (write_list msg ;; k); data_at sh (tarray tuchar (Zlength msg)) (map Vint msg) buf)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength msg))))
    SEP (ITREE k; data_at sh (tarray tuchar (Zlength msg)) (map Vint msg) buf).

Definition getchars_spec := DECLARE _getchars
  WITH sh : share, buf : val, len : Z, k : list int -> IO_itree
  PRE [ ]
    PROP (writable_share sh)
    LOCAL ()
    SEP (ITREE (r <- read_list (Z.to_nat len) ;; k r); data_at_ sh (tarray tuchar len) buf)
  POST [ tint ]
   EX msg : list int, (* for a first pass, assume it always fills the buffer *)
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr len)))
    SEP (ITREE (k msg); data_at sh (tarray tuchar len) (map Vint msg) buf).

Lemma ITREE_impl : forall tr tr', eq_utt tr tr' ->
  ITREE tr |-- ITREE tr'.
Proof.
  intros.
  unfold ITREE.
  Intros tr1; Exists tr1; entailer!.
  etransitivity; eauto.
  symmetry; auto.
Qed.

Lemma ITREE_ext : forall tr tr', eq_utt tr tr' ->
  ITREE tr = ITREE tr'.
Proof.
  intros; apply pred_ext; apply ITREE_impl; auto.
  symmetry; auto.
Qed.

Lemma write_list_app : forall l1 l2,
  eq_utt (write_list (l1 ++ l2)) (write_list l1;; write_list l2).
Proof.
  induction l1; simpl in *; intros.
  - rewrite ret_bind.
    apply push_tau; reflexivity.
  - rewrite bind_bind.
    apply bind_mor; [reflexivity|].
    intro; auto.
Qed.

Definition char0 : Z := 48.
Definition newline := 10.

(* Build the external specification. *)
Definition ext_link := ext_link_prog prog.

Definition IO_ext_spec :=
  semax_ext.add_funspecs_rec
    ext_link
    (ok_void_spec IO_itree).(@OK_ty)
    (ok_void_spec IO_itree).(@OK_spec)
    [getchars_spec; putchars_spec].
