Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.sha_lemmas2.

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
forward.
instantiate (1:=c) in (Value of witness).
unfold witness.
entailer!.
normalize.
forward. (* SHA256_Update(&c,d,n); *)
instantiate (1:=(init_s256abs,data,c,d,dsh, length data)) in (Value of witness).
entailer!.
cbv beta iota.
change (make_args [] []) with globals_only.
change (fun a : environ =>
      EX  x : s256abs,
      (PROP  (update_abs (firstn (length data) data) init_s256abs x)
       LOCAL ()
       SEP  (K_vector; `(sha256state_ x c); `(data_block dsh data d))) a)
 with (EX  x : s256abs,
      (PROP  (update_abs (firstn (length data) data) init_s256abs x)
       LOCAL ()
       SEP  (K_vector; `(sha256state_ x c); `(data_block dsh data d)))).
replace_SEP 0 (
 EX  x : s256abs,
      (PROP  (update_abs (firstn (length data) data) init_s256abs x)
       LOCAL ()
       SEP  (K_vector; `(sha256state_ x c); `(data_block dsh data d)))).
entailer.
apply exp_right with x.
entailer.
normalize. intro a.
simpl.

forward. (* SHA256_Final(md,&c); *)
instantiate (1:=(a,md,c,msh,dsh)) in (Value of witness).
entailer!.
normalize.
simpl.
normalize.
replace_SEP 0 (K_vector).
entailer.

forward. (* return; *)
unfold frame_ret_assert; simpl.
entailer!.
replace (SHA_256 data) with (sha_finish a); auto.
clear - H1.
inv H1.
simpl in *.
rewrite <- H8.
rewrite firstn_same.
auto.
clear; omega.
Qed.
