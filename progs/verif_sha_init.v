Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma ZnthV_nil_None:
  forall t, ZnthV t nil = fun _ => default_val t.
Proof.
unfold ZnthV; intros.
extensionality i; if_tac; auto.
rewrite nth_overflow; auto.
simpl; omega.
Qed.

Lemma body_SHA256_Init: semax_body Vprog Gtot f_SHA256_Init SHA256_Init_spec.
Proof.
start_function.
name c_ _c.
simpl_typed_mapsto.
normalize.

replace (array_at_ tuint Tsh) with (array_at tuint Tsh (ZnthV tuint nil))
 by (rewrite ZnthV_nil_None; reflexivity).

do 8 (forward; [entailer!; [reflexivity | omega..]
              | rewrite upd_Znth_next by (compute; reflexivity); simpl app]).
change (fun _ => c) with (`c). normalize.
forward. (* c->Nl=0; *)
forward. (* c->Nh=0; *)
forward. (* c->num=0; *)
forward. (* return; *)
unfold sha256state_.
apply exp_right with (map Some init_registers, 
      (Some Int.zero, (Some Int.zero, (nil, Some Int.zero)))).
simpl_typed_mapsto.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
entailer!.
exists Int.zero, Int.zero; repeat split; reflexivity.
exists nil; split; reflexivity.
simpl; change CBLOCK with 64; omega.
exists 0; simpl; reflexivity.
apply derives_refl'; f_equal.
f_equal.
repeat (apply f_equal2; [f_equal; apply int_eq_e; compute; reflexivity | ]); auto.
Qed.
