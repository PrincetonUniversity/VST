Require msl.tree_shares.

Extraction Language Ocaml.

Set Extraction AutoInline.

Extraction Inline proj1_sig sigT_of_sig projT1.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
EXtract Inductive sigT => "(*)"  [ "(,)" ].

EXtraction "tree_shares.ml" tree_shares.Share.
