Require Import compcert.cfrontend.Clight.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.typing.type.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Section type.
  Context `{!typeG OK_ty Σ}.

  Definition Sannot (a : assert) := Sskip.
  #[global] Arguments Sannot : simpl never.
  Global Typeclasses Opaque Sannot.

  Definition Sloop (a : assert) s1 s2 := Sloop s1 s2.
  #[global] Arguments Sloop : simpl never.
  Global Typeclasses Opaque Sloop.

End type.
