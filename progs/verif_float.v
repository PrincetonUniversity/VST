Require Import floyd.proofauto.
Require Import progs.float.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Local Open Scope logic.

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition t_struct_foo := Tstruct _foo noattr.

Definition Vprog : varspecs := (_s, t_struct_foo)::nil.

Definition Gprog : funspecs := 
     main_spec::nil.

Lemma gvar_size_compatible:
  forall i s rho t, 
    gvar i s rho -> 
    sizeof cenv_cs t <= Int.modulus ->
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
pose (f :=  PROP () LOCAL (gvar _s s) 
  SEP (`(data_at Ews t_struct_foo (Vint (Int.repr 5), 
          (Vsingle (Float32.of_bits (Int.repr 1079655793)),
           Vfloat (Float.of_bits (Int64.repr 0)))) s))).
apply semax_pre with f; subst f. (* factored out "f" to work around a bug
   in Coq 8.4pl6 (and earlier versions back at least to 8.4pl3). 
  To exhibit the bug, put the r.h.s. of the "pose" as in place of f
  in the "apply...with".  *)
 {
unfold data_at.
 unfold_field_at 1%nat.
entailer!.
simpl.
unfold field_at, data_at', at_offset. simpl.
rewrite proj_sumbool_is_true by auto.
repeat rewrite prop_true_andp by
 (split; [(split3; [ | | split3; [ | | split3; [ | | split]]]; auto; try reflexivity; try apply I;
   try (eapply gvar_size_compatible; eauto; simpl; computable);
   try (eapply gvar_align_compatible; eauto);
   solve [compute; auto])
  | intro; apply I
  ]).
fold noattr; fold tint; fold tfloat; fold tdouble.
repeat match goal with |- context [field_offset ?A ?B ?C] =>
  set (aa :=field_offset A B C); compute in aa; subst aa
end.
normalize. cancel.
}
forward.
forward.
forward.
forward y1_old.
forward.
Qed.
