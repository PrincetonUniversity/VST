Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Local Open Scope logic.

Lemma body_SHA256: semax_body Vprog Gtot f_SHA256 SHA256_spec.
Proof.
start_function.

abbreviate_semax.
name d_ _d.
name n_ _n.
name md_ _md.
name c_ _c.
normalize.
fixup_local_var; intro c.

forward_call' (* SHA256_Init(&c); *)
   (c).

forward_call' (* SHA256_Update(&c,d,n); *)
  (init_s256abs,data,c,d,dsh, Zlength data, kv) a.
 repeat split; try omega.
 pose proof (Zlength_nonneg data); omega.
 simpl. apply H0.

forward_call' (* SHA256_Final(md,&c); *)
    (a,md,c,msh,kv).

forward. (* return; *)
rewrite (lvar_eval_lvar _ _ _ _ H4).
replace (SHA_256 data) with (sha_finish a); [cancel |].
clear - H2.
inv H2.
simpl in *.
rewrite <- H8.
rewrite firstn_same; auto.
rewrite Zlength_correct. rewrite Nat2Z.id. omega.
Qed.
