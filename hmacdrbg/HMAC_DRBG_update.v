Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.

Definition HMAC_DRBG_update (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let K := HMAC (V ++ [0] ++ provided_data) K in
  let V := HMAC V K in
  match provided_data with
    | [] => (K, V)
    | _::_ =>
      let K := HMAC (V ++ [1] ++ provided_data) K in
      let V := HMAC V K in
      (K, V)
  end.