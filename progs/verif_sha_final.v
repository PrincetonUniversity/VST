Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma body_SHA256_Final: semax_body Vprog Gtot f_SHA256_Final SHA256_Final_spec.
Proof.
start_function.
name md_ _md.
name c_ _c.
name p _p.
name n _n.
name cNl _cNl.
name cNh _cNh.
unfold sha256state_; normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
simpl_data_at.
normalize.
unfold s256_relate in H0.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd in H0|-*.
destruct a as [hashed data].
destruct H0 as [? [? [? [? [? ?]]]]].
destruct H1 as [hi [lo [? [? ?]]]].
destruct H2 as [dd [? ?]].
subst r_Nh r_Nl r_num r_data.
revert POSTCONDITION; subst data; intro.
assert (H3': (Zlength (map Int.unsigned dd) < 64)%Z).
rewrite Zlength_correct. change 64%Z with (Z.of_nat CBLOCK).
apply Nat2Z.inj_lt; auto.
forward. (* p = c->data;  *)
entailer!.
forward. (* n = c->num; *)
simpl.
unfold at_offset.  (* maybe this line should not be necessary *)
forward. (* p[n] = 0x80; *)
entailer!. rewrite Zlength_correct; omega.
forward. (* n++; *)
rewrite upd_Znth_next.
simpl.
Admitted.
