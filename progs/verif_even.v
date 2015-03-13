Require Import floyd.proofauto.

Require Import progs.even.
Local Open Scope logic.

Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, 0 <= z <= Int.max_signed -> repr z (Vint (Int.repr z)).

Lemma repr0_not_odd z n :
  repr z (Vint n) -> Int.eq n (Int.repr 0) = true -> Z.odd z = false.
Proof.
inversion 1; subst; intros A.
symmetry in A; apply binop_lemmas.int_eq_true in A.
rewrite A in H; inv H.
rewrite Int.Z_mod_modulus_eq, Zmod_divides in H0.
destruct H0 as [c H0]; rewrite H0, Z.odd_mul; auto.
unfold Int.modulus; simpl; intro Contra; inv Contra.
Qed.

Lemma repr0_even z n :
  repr z (Vint n) -> Int.eq n (Int.repr 0) = true -> Z.even z = true.
Proof.
inversion 1; subst; intros A.
symmetry in A; apply binop_lemmas.int_eq_true in A.
rewrite A in H; inv H.
rewrite Int.Z_mod_modulus_eq, Zmod_divides in H0.
destruct H0 as [c H0]; rewrite H0, Z.even_mul; auto.
unfold Int.modulus; simpl; intro Contra; inv Contra.
Qed.

Lemma repr_eq0_not0 z :
  Int.eq (Int.repr z) (Int.repr 0) = false -> z <> 0.
Proof.
intros H; generalize (Int.eq_spec (Int.repr z) (Int.repr 0)); rewrite H.
intros H2 H3; rewrite H3 in H2; apply H2; auto.
Qed.

Definition odd_spec :=
 DECLARE _odd
  WITH z : Z, v : val, b: unit
  PRE [ _n OF tuint]
    PROP(repr z v) LOCAL(temp _n v) SEP()
  POST [ tint ] 
    PROP() LOCAL(temp ret_temp (Vint (if Z.odd z then Int.one else Int.zero))) SEP().

Definition even_spec :=
 DECLARE _even
  WITH z : Z, v : val
  PRE [ _n OF tuint]
    PROP(repr z v) LOCAL(temp _n v) SEP()
  POST [ tint ] 
    PROP() LOCAL(temp ret_temp (Vint (if Z.even z then Int.one else Int.zero))) SEP().

Definition main_spec :=
 DECLARE _main
  WITH z : Z, v : val
  PRE [ ] PROP(repr 42 v) LOCAL() SEP ()
  POST [ tint ] 
    PROP() LOCAL(temp ret_temp (Vint (if Z.even 42 then Int.one else Int.zero))) SEP().

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := odd_spec :: even_spec :: main_spec :: nil.

Lemma int_eq_false_e:
  forall i j, Int.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int.eq_true in H; inv H.
Qed.

Lemma body_even : semax_body Vprog Gprog f_even even_spec.
Proof.
start_function.
name n _n.
forward_if (PROP (z > 0) LOCAL (temp _n v) SEP ()).
*
 simpl typeof.
 assert_PROP (v= Vint (Int.repr 0)).
 entailer!. apply int_eq_e in H0; f_equal; auto.
 drop_LOCAL 0%nat.
 forward.
 eapply repr0_even in H; eauto. rewrite H. entailer!.
*
 assert_PROP (v <> Vint (Int.repr 0)).
 entailer!.
 apply int_eq_false_e in H0. congruence.
 drop_LOCAL 0%nat.
 forward. entailer!.
  inv H. 
  assert (z <> 0); [contradict H0; subst; auto | omega].
* normalize.
  forward_call' (z-1,Vint (Int.sub (Int.repr z) (Int.repr 1)), tt).
  (* Prove that parameters are OK *)
  entailer!. inv H. normalize.
  (* Prove that PROP precondition is OK *)
  inv H; normalize; constructor. omega.
  (* After the call *)
  forward.
  entailer!.
  rewrite Z.odd_sub; simpl. 
  case_eq (Z.odd z); rewrite Zodd_even_bool; destruct (Z.even z); simpl; try congruence.
Qed.

Ltac repr_tac := 
  constructor; split; [omega | 
  unfold Int.max_signed, Int.half_modulus, Int.modulus; simpl; omega].

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
start_function. 
forward_call' (42,Vint (Int.repr 42)).
repr_tac.
forward.
Qed.

Definition Espec := add_funspecs NullExtension.Espec Gprog.
Existing Instance Espec.

Lemma temp_make_ext_rval_e:
  forall gx v v', 
   temp ret_temp v (make_ext_rval gx v') ->
   v <> Vundef ->
   v' = Some v.
Proof.
intros.
hnf in H. subst.
unfold make_ext_rval, eval_id in *.
destruct v'; simpl in *; auto.
contradiction H0; auto.
Qed.

Lemma all_funcs_correct: semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct.
semax_func_skipn.
semax_func_cons_ext.
  apply temp_make_ext_rval_e in H; try congruence.
  subst; simpl; entailer.
semax_func_cons body_even.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

