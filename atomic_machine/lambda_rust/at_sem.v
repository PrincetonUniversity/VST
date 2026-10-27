(** A demo that the lambda-rust aotmic step can be obtained by plugging
    the lambda-rust language instance into the generic at_step definition.
    This file should usually not be imported, since it suffices to import the
    [lr_language] instance from [sq_sem.v]. *)

Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.


Definition lr_at_step :=
  at_step (L := lr_language).
