Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export int programs type boolean  (*intptr*) function bytes own struct optional singleton fixpoint automation (*padded*) exist (*immovable*) constrained union array (*wand*) globals (*tyfold*) (*atomic_bool*) (*locked*) (*tagged_ptr*) (*bitfield*).
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Close Scope bi_scope.

#[global] Notation int := VST.typing.int.int.
