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

Import Binary.


Definition ROUND {NAN: Nans} (t: type) (r: R) : R :=
   (Generic_fmt.round Zaux.radix2
                (SpecFloat.fexp (fprec t) (femax t))
                (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
                r).

Lemma BMULT_correct {NAN: Nans} {t} (x y: ftype t) :
  let prec := fprec t in let emax := femax t in 
  if Raux.Rlt_bool 
         (Rabs (ROUND t (FT2R x * FT2R y)))
         (Raux.bpow Zaux.radix2 emax)
       then
        FT2R (BMULT t x y) = ROUND t (FT2R x * FT2R y) /\
        is_finite _ _ (BMULT t x y) = andb (is_finite _ _ x) (is_finite _ _ y) /\
        (is_nan _ _ (BMULT t x y) = false ->
         Bsign _ _ (BMULT t x y) = xorb (Bsign _ _ x) (Bsign _ _ y))
       else
        B2FF _ _ (BMULT t x y) = 
        binary_overflow prec emax BinarySingleNaN.mode_NE
                    (xorb (Bsign _ _ x) (Bsign _ _ y)).
Proof.
intros.
apply Bmult_correct.
Qed.

Lemma BPLUS_correct {NAN: Nans} {t} (x y: ftype t) :
  let prec := fprec t in let emax := femax t in 
  is_finite _ _ x = true ->
  is_finite _ _ y = true ->
  if   Raux.Rlt_bool (Rabs (ROUND t (FT2R x + FT2R y)))
          (Raux.bpow Zaux.radix2 emax)
  then FT2R (BPLUS t x y) = ROUND t (FT2R x + FT2R y)%R /\
        is_finite _ _ (BPLUS t x y) = true /\
        Bsign _ _ (BPLUS t x y) = match
                    Raux.Rcompare (FT2R x + FT2R y)%R 0
                  with
                  | Eq => (Bsign prec emax x &&
                                 Bsign prec emax y)%bool
                  | Lt => true
                  | Gt => false
                  end
       else B2FF _ _  (BPLUS t x y) = 
                 binary_overflow prec emax BinarySingleNaN.mode_NE  (Bsign _ _ x) /\  
              Bsign _ _ x = Bsign _ _ y.
Proof.
intros.
apply Bplus_correct; auto.
Qed.

Definition type_hibound (t: type) :=
  (Raux.bpow Zaux.radix2 (femax t) - Raux.bpow Zaux.radix2 (femax t - fprec t))%R.

Lemma ROUND_error: forall {NAN: Nans} t (x: R),
  (exists delta : R, exists epsilon : R, 
    Rabs delta <= default_rel t /\
    Rabs epsilon <= default_abs t /\
   ROUND t x = x * (1+delta) + epsilon)%R.
Proof.
intros.
apply generic_round_property.
Qed.

Require Import Interval.Tactic.

Definition ulp (t: type) := (2 * default_rel t)%R.

(*  This is a clumsy and tedious proof.  It would be better to
  automate this in VCFloat . . . *)
Lemma f_model_accurate: forall t, 
  Binary.is_finite (fprec Tdouble) (femax Tdouble) t = true ->
   is_finite _ _ (f_model t) = true /\ 
  (1 - 10*ulp Tdouble <= FT2R (f_model t) <= 1 + 10 * ulp Tdouble)%R.
Proof.
intros.
unfold f_model.
destruct (ff_acc MF.cos t H I) as [FINx [dx [ex [? [? Hx]]]]].
pose proof (ff_acc MF.sin t H I) as [FINy [dy [ey [? [? Hy]]]]].
forget (ff_func MF.cos t) as x.
forget (ff_func MF.sin t) as y.
change (ftype Tdouble) in x,y.
rename t into t'. forget (FT2R t') as t.
clear t' H.
simpl in *.
pose proof (sin2_cos2 t).
pose proof (COS_bound t).
pose proof (SIN_bound t).
forget (sin t) as s.
forget (cos t) as c.
rewrite !Rsqr_pow2 in H.

assert (Mxx := BMULT_correct x x).
cbv zeta in Mxx.
rewrite Raux.Rlt_bool_true in Mxx.
2:{
rewrite Hx.
match goal with |- context [ROUND ?t ?x] =>
  destruct (ROUND_error t x) as [dr [er [? [? Hxx]]]]
end.
rewrite Hxx; interval.
}
destruct Mxx as [Mxx [FINxx _]].
simpl in FINxx; rewrite FINx in FINxx; simpl in FINxx.

assert (Myy := BMULT_correct y y).
cbv zeta in Myy.
rewrite Raux.Rlt_bool_true in Myy.
2:{
rewrite Hy.
match goal with |- context [ROUND ?t ?x] =>
  destruct (ROUND_error t x) as [dr [er [? [? Hyy]]]]
end.
rewrite Hyy; interval.
}
destruct Myy as [Myy [FINyy _]].
simpl in FINyy; rewrite FINy in FINyy; simpl in FINyy.

rewrite Hx, Hy in *. clear Hx Hy.
pose proof (BPLUS_correct (BMULT Tdouble x x) (BMULT Tdouble y y) FINxx FINyy).
rewrite Raux.Rlt_bool_true in H6.
2:{
rewrite Mxx, Myy.
clear - H0 H1 H2 H3 H4 H5.
match goal with |- context [ROUND ?t (?x * _)] =>
  destruct (ROUND_error t (x*x)) as [dr [er [? [? ?]]]]
end.
rewrite H7; clear H7.
match goal with |- context [ROUND ?t (?x * _)] =>
  destruct (ROUND_error t (x*x)) as [dr' [er' [? [? ?]]]]
end.
 rewrite H9; clear H9.
match goal with |- context [ROUND ?t ?x] =>
  destruct (ROUND_error t x) as [dr'' [er'' [? [? ?]]]]
end.
rewrite H11. clear H11.
unfold default_rel, default_abs in *; simpl in *.
interval.
}
destruct H6 as [? [? _]].
split; auto.
rewrite H6.
rewrite Mxx, Myy. 
clear H6 Mxx Myy.
match goal with |- context [ROUND ?t (?x * _)] =>
  destruct (ROUND_error t (x*x)) as [dr [er [? [? ?]]]]
end.
rewrite H9; clear H9.
match goal with |- context [ROUND ?t (?x * _)] =>
  destruct (ROUND_error t (x*x)) as [dr' [er' [? [? ?]]]]
end.
rewrite H11; clear H11.
match goal with |- context [ROUND ?t ?x] =>
  destruct (ROUND_error t x) as [dr'' [er'' [? [? ?]]]]
end.
rewrite H13; clear H13.
simpl in *.
unfold ulp, default_rel, default_abs in *; simpl in *.
clear FINx FINy FINxx FINyy H7.
match goal with |- (_ <= ?A <= _)%R =>
 replace A with (A + (1 -  (((s * (s * 1) + c * (c * 1))))))%R
  by (rewrite H; Lra.lra)
end.
clear H.
match goal with |- (_ <= ?A <= _)%R =>
  field_simplify A
end.
interval.
Qed.

