Unset Universe Polymorphism.
Require Import VST.floyd.jmeq_lemmas.

Definition caller_default (A: Type) := A.
Fail Check caller_default@{Set}.
