Require Import VST.veric.juicy_extspec. (* We should probably move has_ext into Separation Logic.v *)
Require Import VST.progs.ghosts.
Require Import VST.progs.io.
Require Import VST.floyd.proofauto.
Require Import DeepWeb.Free.Monad.Free.
Import MonadNotations.
Require Import DeepWeb.Free.Monad.Common.
(*Require Import DeepWeb.Free.Monad.Verif.*)

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Inductive IO_event : Type -> Type :=
| ERead : IO_event int
| EWrite (c : int) : IO_event unit.

Definition IO_itree := M IO_event unit.

Definition read : IO_itree := embed ERead.

Definition write (c : int) : IO_itree := embed (EWrite c).

Definition putchar_spec :=
 DECLARE _putchar
  WITH c : int, k : unit -> IO_itree
  PRE [ _c OF tint ]
    PROP ()
    LOCAL (temp _c (Vint c))
    SEP (has_ext (write c ;; k))
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint Int.zero))
    SEP (has_ext k).

Definition getchar_spec :=
 DECLARE _getchar
  WITH k : int -> IO_itree
  PRE [ ]
    PROP ()
    LOCAL ()
    SEP (has_ext (r <- read ;; k r))
  POST [ tint ]
   EX i : int,
    PROP ()
    LOCAL (temp ret_temp (Vint i))
    SEP (has_ext (k i)).

Parameter chars_of_Z : Z -> list int.

Fixpoint write_list l : IO_itree :=
  match l with
  | nil => Ret tt
  | c :: rest => write c ;; write_list rest
  end.

Definition print_intr_spec :=
 DECLARE _print_intr
  WITH i : Z, tr : IO_itree
  PRE [ _i OF tuint ]
    PROP ()
    LOCAL (temp _i (Vint (Int.repr i)))
    SEP (has_ext (write_list (chars_of_Z i) ;; tr)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (has_ext tr).

Definition Gprog : funspecs := ltac:(with_library prog [putchar_spec; getchar_spec;
  print_intr_spec]).
