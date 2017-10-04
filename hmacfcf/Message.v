(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import Bvector.
Require Import EqDec.

Local Open Scope type_scope.

Section HMAC_Message.

  Variable word_size max_size : nat.

  Definition Message := nat * Vector.t (Bvector word_size) max_size.

  Instance Message_EqDec : EqDec Message.

  eapply pair_EqDec;  eauto with typeclass_instances.
  eapply Vector_EqDec.
  eapply Vector_EqDec.
  eauto with typeclass_instances.

  Qed.

End HMAC_Message.