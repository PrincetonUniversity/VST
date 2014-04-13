Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Local Open Scope logic.

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
apply (remember_value (eval_var _c t_struct_SHA256state_st)); intro c.
forward_call (* SHA256_Init(&c); *)
   (c).
entailer!.
normalize.
after_call.
forward_call (* SHA256_Update(&c,d,n); *)
  (init_s256abs,data,c,d,dsh, length data).
entailer!.
after_call.
replace_SEP 0 (
 EX  x : s256abs,
      (PROP  (update_abs (firstn (length data) data) init_s256abs x)
       LOCAL ()
       SEP  (`K_vector (eval_var _K256 (tarray tuint 64));
               `(sha256state_ x c); `(data_block dsh data d)))).
entailer.
apply exp_right with x.
entailer.
normalize. intro a.
simpl.

forward_call (* SHA256_Final(md,&c); *)
    (a,md,c,msh,dsh).
entailer!.
after_call.
simpl.
replace_SEP 0 (`K_vector (eval_var _K256 (tarray tuint 64))).
entailer.

forward. (* return; *)
unfold frame_ret_assert; simpl.
entailer!.
replace (SHA_256 data) with (sha_finish a); auto.
clear - H1.
inv H1.
simpl in *.
rewrite <- H8.
rewrite firstn_same by (clear; omega).
auto.
Qed.
