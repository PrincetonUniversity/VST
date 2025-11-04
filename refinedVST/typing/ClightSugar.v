Require Import compcert.cfrontend.Clight.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.typing.type.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Section type.
  Context `{!typeG OK_ty Σ}.

  Definition Sannot (a : assert) := Sskip.
  Definition Sloop (a : assert) s1 s2 := Sloop s1 s2.
End type.
