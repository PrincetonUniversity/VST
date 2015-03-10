Require Import floyd.proofauto.
Require Import progs.float.

Local Open Scope logic.

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.


Definition Vprog : varspecs := (_s, t_struct_foo)::nil.

Definition Gprog : funspecs := 
     main_spec::nil.

Lemma gvar_size_compatible:
  forall i s rho t, 
    gvar i s rho -> 
    sizeof t <= Int.modulus ->
    size_compatible t s.
Proof.
intros.
hnf in H. destruct (Map.get (ve_of rho) i) as [[? ? ] | ]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst s.
simpl; auto.
Qed.


Lemma gvar_align_compatible:
  forall i s rho t, 
    gvar i s rho -> 
    align_compatible t s.
Proof.
intros.
hnf in H. destruct (Map.get (ve_of rho) i) as [[? ? ] | ]; try contradiction.
destruct (ge_of rho i); try contradiction.
subst s.
simpl; auto.
exists 0. reflexivity.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name x1 _x1.
name y1 _y1.
name y2 _y2.
name s _s.
start_function.
apply semax_pre with
 (PROP  ()
   LOCAL  (gvar _s s)
   SEP 
   (`(data_at Ews t_struct_foo (Vint (Int.repr 5), 
          (Vsingle (Float32.of_bits (Int.repr 14302577)),
           Vfloat (Float.of_bits (Int64.repr 0)))) s))). {
simpl_data_at.
entailer.
rewrite prop_true_andp.
fold tfloat. fold tint. fold tdouble.
cancel.
split.
  eapply gvar_size_compatible; eauto; simpl; computable.
  eapply gvar_align_compatible; eauto.
}
forward.
forward.
forward.
forward.
forward.
unfold main_post.
entailer!.
Qed.
