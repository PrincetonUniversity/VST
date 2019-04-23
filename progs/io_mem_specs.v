Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_extspec.
Require Import ITree.ITree.
Require Export ITree.Eq.UpToTausEquivalence.
(* Import ITreeNotations. *) (* one piece conflicts with subp notation *)
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.

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
Definition ITREE (tr : IO_itree) := EX tr' : _, !!(eutt eq tr tr') &&
  has_ext tr'.

Lemma has_ext_ITREE : forall tr, has_ext tr |-- ITREE tr.
Proof.
  intro; unfold ITREE.
  Exists tr; entailer!.
Qed.

Definition putchars_spec {CS : compspecs} :=
  WITH sh : share, buf : val, msg : list int, len : Z, rest : list val, k : IO_itree
  PRE [ 1%positive OF tptr tuchar, 2%positive OF tint ]
    PROP (readable_share sh)
    LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr (Zlength msg))))
    SEP (ITREE (write_list msg ;; k);
           data_at sh (tarray tuchar len) (map Vint msg ++ rest) buf)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength msg))))
    SEP (ITREE k;
           data_at sh (tarray tuchar len) (map Vint msg ++ rest) buf).

Definition getchars_spec {CS : compspecs} :=
  WITH sh : share, buf : val, len : Z, k : list int -> IO_itree
  PRE [ 1%positive OF tptr tuchar, 2%positive OF tint ]
    PROP (writable_share sh)
    LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr len)))
    SEP (ITREE (r <- read_list (Z.to_nat len) ;; k r); data_at_ sh (tarray tuchar len) buf)
                                                                  (* buf |-> _ *)
  POST [ tint ]
   EX msg : list int,
    PROP (Forall (fun i => Int.unsigned i <= Byte.max_unsigned) msg)
    LOCAL (temp ret_temp (Vint (Int.repr len)))
    SEP (ITREE (k msg); data_at sh (tarray tuchar len) (map Vint msg) buf).
                                                                  (* buf |-> msg *)

Lemma ITREE_impl : forall tr tr', eutt eq tr tr' ->
  ITREE tr |-- ITREE tr'.
Proof.
  intros.
  unfold ITREE.
  Intros tr1; Exists tr1; entailer!.
  etransitivity; eauto.
  symmetry; auto.
Qed.

Lemma ITREE_ext : forall tr tr', eutt eq tr tr' ->
  ITREE tr = ITREE tr'.
Proof.
  intros; apply pred_ext; apply ITREE_impl; auto.
  symmetry; auto.
Qed.

Lemma write_list_app : forall l1 l2,
  eutt eq (write_list (l1 ++ l2)) (write_list l1;; write_list l2).
Proof.
  induction l1; simpl in *; intros.
  - rewrite bind_ret; reflexivity.
  - rewrite bind_bind.
    setoid_rewrite IHl1; reflexivity.
Qed.

Definition char0 : Z := 48.
Definition newline := 10.

(* Build the external specification. *)
Definition IO_void_Espec : OracleKind := ok_void_spec IO_itree.

Definition IO_specs {CS : compspecs} (ext_link : string -> ident) :=
  [(ext_link "putchars"%string, putchars_spec); (ext_link "getchars"%string, getchars_spec)].

Definition IO_Espec {CS : compspecs} (ext_link : string -> ident) : OracleKind :=
  add_funspecs IO_void_Espec ext_link (IO_specs ext_link).
