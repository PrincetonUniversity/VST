Require Import VST.floyd.proofauto.
Require Import hmacdrbg.mocked_md.

Global Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
