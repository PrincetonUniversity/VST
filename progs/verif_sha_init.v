Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma array_at_emp:
 forall t sh f (lo hi: Z) c, (lo >= hi)%Z -> array_at t sh f lo hi c = emp.
Proof.
intros.
unfold array_at, rangespec.
rewrite nat_of_Z_neg by omega.
simpl. reflexivity.
Qed.

Lemma array_at_offset_zero:
  forall t sh f lo hi c,
   array_at t sh f lo hi c |-- array_at t sh f lo hi (offset_val (Int.repr 0) (force_ptr c)).
Proof.
intros.
destruct (zlt lo hi).
saturate_local.
normalize.
do 2 rewrite array_at_emp by auto.
auto.
Qed.

Hint Resolve array_at_offset_zero : cancel.

Lemma body_SHA256_Init: semax_body Vprog Gtot f_SHA256_Init SHA256_Init_spec.
Proof.
start_function.
name c_ _c.
revert Delta POSTCONDITION; simpl_typed_mapsto; intros.
normalize.

replace_SEP 0%Z (`(array_at tuint Tsh (ZnthV tuint nil) 0 8 c)).
entailer.

Ltac one_store :=
match goal with |- semax _ _ (Ssequence 
                              (Sassign (Ederef (Ebinop Oadd _ (Econst_int (Int.repr ?i) _) _) _)  _) _) _ =>
 forward; [ instantiate (1:=force_option Int.zero (ZnthV tuint init_registers i));
                 instantiate (1:= i);
                 entailer!; 
                 try (apply int_eq_e; compute; reflexivity)
               | rewrite upd_Znth_next by (compute; reflexivity); simpl app
               ]
end.
one_store.
one_store.
one_store.
one_store.
one_store.
one_store.
one_store.
one_store.
forward. (* c->Nl=0; *)
forward. (* c->Nh=0; *)
forward. (* c->num=0; *)
forward. (* return; *)
unfold sha256state_.
apply exp_right with (init_registers, (Int.zero, (Int.zero, (nil, Int.zero)))).
simpl_typed_mapsto.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
entailer!.
repeat split.
simpl; change CBLOCK with 64; omega.
exists 0; simpl; reflexivity.
Qed.
