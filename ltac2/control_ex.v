Require Import Ltac2.Ltac2.

(* Throw invalid argument function which takes a printf style format *)

Ltac2 throw_invalid_argument fmt :=
  Message.Format.kfprintf (fun x => Control.throw (Invalid_argument (Some x))) fmt.

Ltac2 Notation "throw_invalid_argument" fmt(format) := throw_invalid_argument fmt.
