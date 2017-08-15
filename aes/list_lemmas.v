Require Export aes.list_utils.
Require Export ZArith.
Local Open Scope Z_scope.
Require Export VST.floyd.sublist.

Lemma Znth_fill_list: forall {T: Type} (i n: Z) (f: Z -> T) (d: T),
  0 <= i < n ->
  Znth i (fill_list n f) d = f i.
Admitted.
