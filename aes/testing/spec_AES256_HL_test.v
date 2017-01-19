Require Import aes.spec_AES256_HL.

Tactic Notation "calc" constr(x) := let r := eval cbv in x in exact r.

Definition word0 : word := (Int.zero, Int.zero, Int.zero, Int.zero).
Definition state0 : state := (word0, word0, word0, word0).
Definition key0 : list word := ltac:(calc (repeat word0 8)).
(*Definition exp_key0 : list block := ltac:(calc (repeat state0 15)).*)
Definition exp_key0 : list block := KeyExpansion key0.

Definition ciphertext1 := (Cipher exp_key0 state0).

Extraction "aes/extracted/ciphertext1.ml" ciphertext1.

Require Import aes.aes.

Definition aes_test_ecb_enc : list int := ltac:(
  let r := eval cbv in (let (_, v, _, _) := v_aes_test_ecb_enc in (map (fun data => match data with
  | AST.Init_int8 i => i
  | _ => Int.repr Int.max_signed
  end) v))
  in exact r).

Definition test1 := ltac:(
  let r := eval cbv in (sublist 0 16 aes_test_ecb_enc)
  in exact r).

Definition test2 := ltac:(
  let r := eval cbv in (sublist 16 24 aes_test_ecb_enc)
  in exact r).

Definition test3 := ltac:(
  let r := eval cbv in (sublist 24 48 aes_test_ecb_enc)
  in exact r).
