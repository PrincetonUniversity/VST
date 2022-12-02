Require Import VST.floyd.proofauto.
Require Import VSTlibtest.testmath.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPCompCert.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition f_model (t: ftype Tdouble) : ftype Tdouble :=
  let x := ff_func MF.cos t in
  let y := ff_func MF.sin t in
  (x*x+y*y)%F64.

Definition f_spec :=
 DECLARE _f
  WITH t: float
  PRE [ tdouble ]
         PROP  ()
         PARAMS (Vfloat t)
         SEP   ()
  POST [ tdouble ]
         PROP ()
         RETURN (Vfloat (f_model t))
         SEP ().

Definition Gprog := spec_math.MathASI.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
forward_call.
forward_call.
forward.
Qed.

Require Import Reals.

Lemma f_model_accurate: forall t, 
  Binary.is_finite (fprec Tdouble) (femax Tdouble) t = true ->
  (0.9 <= FT2R (f_model t) <= 0.1)%R.
Proof.
intros.
unfold f_model.
destruct (ff_acc MF.cos t H I) as [FINx [dx [ex [? [? ?]]]]].
pose proof (ff_acc MF.sin t H I) as [FINy [dy [ey [? [? ?]]]]].
forget (ff_func MF.cos t) as x.
forget (ff_func MF.sin t) as y.
change (ftype Tdouble) in x,y.
rename t into t'. forget (FT2R t') as t.
clear t' H.
(* Should be straightforward from here *)
Admitted.

