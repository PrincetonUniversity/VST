Require Import VST.floyd.proofauto.
Require Import linking.
Require Import main.
Require Import spec_stdlib.
Require Import spec_fastonepile.
Require Import spec_fastapile.
Require Import spec_fasttriang.
Require Import spec_fastmain.
Require verif_fasttriang.

Definition Gprog : funspecs :=   
   spec_fastapile.specs ++ spec_fastonepile.specs ++ spec_fasttriang.specs ++ spec_fastmain.specs.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (make_mem_mgr gv).
sep_apply (make_apile gv).
generalize (make_onepile gv).
assert (change_composite_env spec_fastonepile.CompSpecs CompSpecs).
make_cs_preserve spec_fastonepile.CompSpecs CompSpecs.
change_compspecs CompSpecs.
intro Hx; sep_apply Hx; clear Hx.
forward_call gv.
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (onepile gv (Some (verif_fasttriang.decreasing (Z.to_nat i)));
          apile gv (verif_fasttriang.decreasing (Z.to_nat i));
          mem_mgr gv)).
-
 entailer!.
-
forward_call (i+1, verif_fasttriang.decreasing(Z.to_nat i), gv).
rep_omega.
forward_call (i+1, verif_fasttriang.decreasing(Z.to_nat i), gv).
rep_omega.
entailer!.
replace (verif_fasttriang.decreasing (Z.to_nat (i + 1)))
  with (i + 1 :: verif_fasttriang.decreasing (Z.to_nat i)).
cancel.
replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
unfold verif_fasttriang.decreasing; fold verif_fasttriang.decreasing.
f_equal. rewrite inj_S. rewrite Z2Nat.id by omega. omega.
rewrite <- Z2Nat.inj_succ by omega. f_equal; omega.
-
forward_call (verif_fasttriang.decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (verif_fasttriang.decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
omega.
forward.
Qed.

Definition module := 
  [mk_body body_main ].
