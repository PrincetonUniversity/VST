Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Local Open Scope logic.

(* BEGIN move these to floyd *)

(* END move these to floyd *)

Lemma body_SHA256: semax_body Vprog Gtot f_SHA256 SHA256_spec.
Proof.
start_function.
unfold POSTCONDITION, abbreviate; simpl_stackframe_of;
abbreviate_semax.
name d_ _d.
name n_ _n.
name md_ _md.
name c_ _c.
normalize.
apply (remember_value (eval_lvar _c t_struct_SHA256state_st)); intro c.

replace_SEP 0 (`(data_at_ Tsh t_struct_SHA256state_st c)).
entailer!.
assert_LOCAL (lvar _c t_struct_SHA256state_st c).
 entailer!. apply normalize_lvar; auto.
drop_LOCAL 1%nat.

forward_call' (* SHA256_Init(&c); *)
   (c).
 repeat split; try repable_signed.

forward_call' (* SHA256_Update(&c,d,n); *)
  (init_s256abs,data,c,d,dsh, Zlength data, kv).
 repeat split; try repable_signed.
 pose proof (Zlength_nonneg data); omega.
 simpl. apply H0.
 apply extract_exists_pre; intro a.
 normalize.

forward_call' (* SHA256_Final(md,&c); *)
    (a,md,c,msh,kv).

forward. (* return; *)
rewrite (lvar_eval_lvar _ _ _ _ H4).
replace (SHA_256 data) with (sha_finish a); [cancel |].
clear - H2.
inv H2.
simpl in *.
rewrite <- H8.
rewrite firstn_same by (clear; omega).
auto.
Qed.
