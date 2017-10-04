Require Import floyd.proofauto.
Require Import Coqlib.
Require Import Recdef.
Require Import progs.fact.

Function FAC (i : Z) {measure Z.to_nat i} : Z :=
if zle i 1 then 1 else FAC (i - 1) * i.
Proof. intros. apply Z2Nat.inj_lt; omega. Defined.

Lemma FAC_step (i : Z) :
i > 0 -> FAC (i + 1) = FAC i * (i + 1).
Proof.
intros. rewrite FAC_equation. destruct (zle (i + 1) 1). omega.
assert (i + 1 - 1 = i). omega.
rewrite H0. auto.
Qed.

Definition fac_spec :=
DECLARE _fac
  WITH n : Z
    PRE [ _n OF tint ]
    PROP (0 <= n <= Int.max_signed)
    LOCAL (temp _n (Vint (Int.repr n)))
    SEP ()
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (FAC n))))
    SEP().

Definition fac_inv (n : Z) : environ -> mpred :=
EX i : Z,
  PROP (1 <= i <= n \/ (n = 0 /\ i = 1))
  LOCAL (temp _n (Vint (Int.repr n));
          temp _i (Vint (Int.repr i));
          temp _f (Vint (Int.repr (FAC i))))
  SEP().

(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=  ltac:(with_library prog [fac_spec]).

Lemma body_fac: semax_body Vprog Gprog f_fac fac_spec.
Proof.
start_function. forward. forward. forward.
forward_while (fac_inv n).
- Exists 1. entailer!. omega.
- entailer!.
- forward. forward. forward. Exists (i + 1). entailer!.
split. omega. rewrite FAC_step. auto. omega.
- forward.
destruct H0. assert (i = n) by omega. subst. entailer!.
destruct H0. subst. entailer!.
Qed.