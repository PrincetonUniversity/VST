Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Local Open Scope logic.

(* BEGIN move these to floyd *)
Lemma normalize_lvar:
  forall v i t rho,  isptr (eval_lvar i t rho) ->
        v  = (eval_lvar i t rho) -> lvar i t v rho.
Proof.
unfold_lift.
unfold lvar, eval_lvar.
intros.
destruct (Map.get (ve_of rho) i) as [[? ?] | ].
destruct (eqb_type t t0); inv H; auto.
inv H.
Qed.

Lemma lvar_isptr:
  forall i t v rho, lvar i t v rho -> isptr v.
Proof.
unfold lvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (eqb_type t t0); try contradiction; subst; apply I.
Qed.

Lemma lvar_eval_lvar:
  forall i t v rho, lvar i t v rho -> eval_lvar i t rho = v.
Proof.
unfold lvar, eval_lvar; intros.
destruct (Map.get (ve_of rho) i) as [[? ?]|]; try contradiction.
destruct (eqb_type t t0); try contradiction; subst; auto.
Qed.

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

apply seq_assoc. (* shouldn't need this *)

forward_call' (* SHA256_Init(&c); *)
   (c).

apply seq_assoc. (* shouldn't need this *)
(* TODO:  this next one cannot use forward_call'
   because the postcondition has an existential 
*)
forward_call (* SHA256_Update(&c,d,n); *)
  (init_s256abs,data,c,d,dsh, Zlength data, kv).
entailer!.
pose proof (Zlength_nonneg data); omega.
hnf in H3.
unfold eval_var.
destruct (Map.get (ve_of rho) _c) as [[? ?]|]; try contradiction.
destruct (eqb_type t_struct_SHA256state_st t); try contradiction.
auto.
after_call.
replace_SEP 0 (
 EX  x : s256abs,
      (PROP  (update_abs (firstn (length data) data) init_s256abs x)
       LOCAL ()
       SEP  (`(K_vector kv);
               `(sha256state_ x c); `(data_block dsh data d)))).
entailer.
apply exp_right with x.
entailer.
normalize. intro a.
simpl.

forward_call' (* SHA256_Final(md,&c); *)
    (a,md,c,msh,kv).
apply prop_right; repeat constructor; hnf; simpl; auto.
pose proof (lvar_isptr _ _ _ _ H4); destruct c; try contradiction; reflexivity.
destruct md_; try contradiction; reflexivity.
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
