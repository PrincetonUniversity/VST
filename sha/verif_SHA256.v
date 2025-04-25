Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Lemma body_SHA256: semax_body Vprog Gtot f_SHA256 SHA256_spec.
Proof.
start_function.
rewrite data_at__isptr; Intros.
forward_call (* SHA256_Init(&c); *)
   (v_c, Tsh).
forward_call (* SHA256_Update(&c,d,n); *)
  (@nil byte, data,v_c,Tsh, d,dsh, Zlength data, gv).
 simpl app.

forward_call (* SHA256_Final(md,&c); *)
    (sublist 0 (Zlength data) data, md, v_c, Tsh, msh, gv).

forward. (* return; *)
change (Tstruct _SHA256state_st noattr) with t_struct_SHA256state_st.
autorewrite with sublist.
entailer!.
Qed.
