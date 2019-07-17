Require Import VST.floyd.proofauto.
Require Import VST.veric.juicy_extspec.
Require Export VST.floyd.io_events.
Require Import ITree.ITree.
Require Export ITree.Eq.Eq.
Require Export ITree.Eq.SimUpToTaus.
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

Fixpoint read_list_aux {file_id : Type} f n d : itree (@IO_event file_id) (list byte) :=
  match n with
  | O => Ret d
  | S n' => x <- read f ;; read_list_aux f n' (x :: d)
  end.

Definition read_list {file_id : Type} f n : itree (@IO_event file_id) (list byte) := read_list_aux f n [].

Definition stdin := 0%nat.
Definition stdout := 1%nat.

Definition putchars_spec {CS : compspecs} :=
  WITH sh : share, buf : val, msg : list byte, len : Z, rest : list val, k : IO_itree
  PRE [ 1%positive OF tptr tuchar, 2%positive OF tint ]
    PROP (readable_share sh)
    LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr (Zlength msg))))
    SEP (ITREE (write_list stdout msg ;; k);
           data_at sh (tarray tuchar len) (map Vubyte msg ++ rest) buf)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength msg))))
    SEP (ITREE k;
           data_at sh (tarray tuchar len) (map Vubyte msg ++ rest) buf).

Definition getchars_spec {CS : compspecs} :=
  WITH sh : share, buf : val, len : Z, k : list byte -> IO_itree
  PRE [ 1%positive OF tptr tuchar, 2%positive OF tint ]
    PROP (writable_share sh)
    LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr len)))
    SEP (ITREE (r <- read_list stdin (Z.to_nat len) ;; k r); data_at_ sh (tarray tuchar len) buf)
  POST [ tint ]
   EX msg : list byte,
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr len)))
    SEP (ITREE (k msg); data_at sh (tarray tuchar len) (map Vubyte msg) buf).

(* Build the external specification. *)
Definition IO_void_Espec : OracleKind := ok_void_spec (@IO_itree nat).

Definition IO_specs {CS : compspecs} (ext_link : string -> ident) :=
  [(ext_link "putchars"%string, putchars_spec); (ext_link "getchars"%string, getchars_spec)].

Definition IO_Espec {CS : compspecs} (ext_link : string -> ident) : OracleKind :=
  add_funspecs IO_void_Espec ext_link (IO_specs ext_link).
