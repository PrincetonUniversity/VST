Require Export aes.list_utils.
Require Export ZArith.
Local Open Scope Z_scope.
Require Export VST.floyd.sublist.

Lemma Znth_fill_list: forall {T: Type}{d: Inhabitant T} (i n: Z) (f: Z -> T) ,
  0 <= i < n ->
  Znth i (fill_list n f) = f i.
Admitted.
