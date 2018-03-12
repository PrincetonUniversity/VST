Require Import ZArith.
Local Open Scope Z_scope.
Require Import Integers.
Require Import VST.floyd.proofauto.
Require Import compcert.common.Values.
Require Export List. Export ListNotations.
Require Export aes.list_utils.

Definition partially_filled(i n: Z)(f: Z -> int): list val := 
  (map Vint (fill_list i f)) ++ (repeat_op_table (n-i) Vundef id).

Lemma update_partially_filled: forall (i: Z) (f: Z -> int) (l: Z),
  0 <= i < l ->
  upd_Znth i (partially_filled i l f) (Vint (f i))
  = partially_filled (i+1) l f.
Admitted.

Lemma Znth_partially_filled: forall (i j n: Z) (f: Z -> int),
  0 <= i -> i < j -> j <= n ->
  Znth i (partially_filled j n f) = Vint (f i).
Admitted.
