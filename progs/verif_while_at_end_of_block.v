Require Import floyd.proofauto.
Require Import progs.while_at_end_of_block.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition identity_spec :=
 DECLARE _identity
  WITH v: Z, by_counting: Z
  PRE  [_v OF tuint, _by_counting OF tbool] 
        PROP (0 <= v <= Int.max_unsigned)
        LOCAL(temp _v (Vint (Int.repr v)); temp _by_counting (Vint (Int.repr by_counting)))
        SEP()
  POST [ tuint ]
         PROP() 
         LOCAL (temp ret_temp (Vint (Int.repr v)))
         SEP ().

Definition Gprog : funspecs := nil.

Lemma body_identity: semax_body Vprog Gprog f_identity identity_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP() LOCAL (temp _v (Vint (Int.repr v)); temp _result (Vint (Int.repr v))) SEP ()).
  * forward_while (EX r: Z, (PROP(0 <= r <= v)
                             LOCAL (temp _v (Vint (Int.repr v));
                                    temp _result (Vint (Int.repr r))) SEP ())).
    - Exists 0. entailer!.
    - entailer!.
    - forward. Exists (r + 1). entailer!.
    - entailer!. f_equal. f_equal. omega.
  * forward. entailer!.
  * forward.
Qed.

