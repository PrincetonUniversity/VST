Require Import VST.floyd.proofauto.
Require Import VSTlibtest.testmath.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPCompCert.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import vcfloat.VCFloat.

Definition cos := ltac:(apply_func (Build_floatfunc_package _ _ _ _ MF.cos)).
Definition sin := ltac:(apply_func (Build_floatfunc_package _ _ _ _ MF.sin)).

Definition f_model (t: ftype Tdouble) : ftype Tdouble :=
  let x := cos t in
  let y := sin t in
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

From Stdlib Require Import Reals.

Import Binary.


Definition ROUND {NAN: Nans} (t: type) (r: R) : R :=
   (Generic_fmt.round Zaux.radix2
                (SpecFloat.fexp (fprec t) (femax t))
                (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
                r).

Lemma BMULT_correct {NAN: Nans} {t} `{STD: is_standard t} (x y: ftype t) :
  let prec := fprec t in let emax := femax t in 
  if Raux.Rlt_bool 
         (Rabs (ROUND t (FT2R x * FT2R y)))
         (Raux.bpow Zaux.radix2 emax)
       then
        FT2R (BMULT x y) = ROUND t (FT2R x * FT2R y) /\
        FPCore.is_finite (BMULT x y) = andb (FPCore.is_finite x) (FPCore.is_finite y) /\
        (is_nan _ _ (float_of_ftype (BMULT x y)) = false ->
         Bsign _ _ (float_of_ftype (BMULT x y)) = xorb (Bsign _ _ (float_of_ftype x)) (Bsign _ _ (float_of_ftype y)))
       else
        B2FF _ _ (float_of_ftype (BMULT x y)) = 
        binary_overflow prec emax BinarySingleNaN.mode_NE
                    (xorb (Bsign _ _ (float_of_ftype x)) (Bsign _ _ (float_of_ftype y))).
Proof.
intros.
unfold BMULT, BINOP, ROUND.
rewrite !FT2R_ftype_of_float.
rewrite <- !B2R_float_of_ftype.
rewrite !is_finite_Binary, !float_of_ftype_of_float.
apply Bmult_correct.
Qed.

Lemma BPLUS_correct {NAN: Nans} {t} `{STD: is_standard t}  (x y: ftype t) :
  let prec := fprec t in let emax := femax t in 
  FPCore.is_finite x = true ->
  FPCore.is_finite y = true ->
  if   Raux.Rlt_bool (Rabs (ROUND t (FT2R x + FT2R y)))
          (Raux.bpow Zaux.radix2 emax)
  then FT2R (BPLUS x y) = ROUND t (FT2R x + FT2R y)%R /\
        FPCore.is_finite (BPLUS x y) = true /\
        Bsign _ _ (float_of_ftype (BPLUS x y)) = match
                    Raux.Rcompare (FT2R x + FT2R y)%R 0
                  with
                  | Eq => (Bsign prec emax (float_of_ftype x) &&
                                 Bsign prec emax (float_of_ftype y))%bool
                  | Lt => true
                  | Gt => false
                  end
       else B2FF _ _  (float_of_ftype (BPLUS x y)) = 
                 binary_overflow prec emax BinarySingleNaN.mode_NE  
                    (Bsign _ _ (float_of_ftype x)) /\  
              Bsign _ _ (float_of_ftype x) = Bsign _ _ (float_of_ftype y).
Proof.
intros.
unfold BPLUS, BINOP, ROUND.
rewrite !FT2R_ftype_of_float.
rewrite <- !B2R_float_of_ftype.
rewrite !is_finite_Binary, !float_of_ftype_of_float in *.
apply Bplus_correct; auto.
Qed.

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

Definition F' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x]) f_model in exact e').

Definition bmap_list : list varinfo := 
  [trivbound_varinfo Tdouble _x].

(** Then we calculate an efficient lookup table, the "boundsmap". *)
Definition bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list bmap_list) in exact z).
Set Bullet Behavior "Strict Subproofs".

Definition ulp (t: type) := (2 * default_rel t)%R.
(** Now we prove that the leapfrogx expression (deep-embedded as  x' )
   has a roundoff error less than 1.0e-5 *)
Lemma prove_roundoff_bound_x:
  forall vmap,
  prove_roundoff_bound bmap vmap F'  (10*ulp Tdouble).
Proof.
intros.
unfold ulp, default_rel. simpl bpow.
prove_roundoff_bound.
-
prove_rndval.
all: interval.
- 
prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end. (* improves the bound *)
 interval.
Qed.

Definition some_valmap [v: Maps.PTree.t {x: type & ftype x}] (H: valmap_valid v) :=
  exist (@valmap_valid empty_collection) _ H.

Ltac pose_valmap_of_list name vml :=
    let z := compute_PTree (valmap_of_list' vml) in
    let z := constr:(@abbreviate _ z) in
    let H := fresh "VV" in
    assert (H: valmap_valid z);
      [apply (@compute_valmap_valid _); repeat apply conj; try apply I;
         cbv[test_ptree test_ptree']; prove_incollection
      | pose (name := some_valmap H : valmap)].



Lemma f_model_accurate': forall t, 
  Binary.is_finite (fprec Tdouble) (femax Tdouble) t = true ->
   is_finite _ _ (f_model t) = true /\ 
  (1 - 10*ulp Tdouble <= FT2R (f_model t) <= 1 + 10 * ulp Tdouble)%R.
Proof.
intros.
rename t into x.
pose_valmap_of_list vmap [(_x, existT ftype Tdouble (ftype_of_float x))].
pose proof prove_roundoff_bound_x vmap.
red in H0.
spec H0. {
  apply boundsmap_denote_i; simpl; auto.
  eexists; split3; try reflexivity. split; auto. 
  apply trivbound_correct.
}
red in H0.
destruct H0.
split; auto.
unfold f_model.
change (FT2R _) with (FT2R (fval (env_ vmap) F')).
forget (FT2R (fval (env_ vmap) F')) as g.
simpl in H1.
change (env_ vmap Tdouble _ _x) with x in H1.
clear - H1.
rewrite  Rplus_comm in H1.
change (sin ?t * sin ?t + cos ?t * cos ?t) with ((sin t)² + (cos t)²) in H1.
rewrite sin2_cos2 in H1.
apply Rabs_le_inv in H1.
lra.
Qed.

