Require Import VST.floyd.proofauto.

Section ReptypeFunspec.
Context {CompSpecs : compspecs}.

Check VST.veric.SeparationLogic.NDmk_funspec
  (nil, tvoid) cc_default (reptype tint).
Check VST.veric.seplog.NDmk_funspec
  (nil, tvoid) cc_default (reptype tint).

End ReptypeFunspec.
