Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat.
Require Import VSTlib.math_extern.
Require Import vcfloat.FPCompCert vcfloat.klist vcfloat.FPCore.
Require Import Reals.
Import ListNotations.

Local Open Scope assert.

Module GNU_Errors.
Definition Generic : nat := 0.
Definition AArch64 : nat := 1.
Definition ARM : nat := 2.
Definition PowerPC : nat := 3.
Definition RISCV32 : nat := 4.
Definition RISCV64 : nat := 5.
Definition i686 : nat := 6.
Definition x86_64 : nat := 7.
Open Scope string.
Definition arch': nat :=
 match Info.arch, Info.bitsize with
 | "arm", 32 => ARM
 | "powerpc", 32 => PowerPC
 | "x86", 32 => i686
 | "x86", 64 => x86_64
 | "riscV", 64 => RISCV64
 | "riscV", 32 => RISCV32
 | "aarch64", 64 => AArch64
 | _, _ => Generic
 end.

Definition arch : nat := ltac:(let x := constr:(arch') in let x := eval compute in x in exact x).

Lemma architecture_is_known: arch <> Generic.
Proof. compute. lia. Abort.

Definition process_GNU_errors (al: list (ident * list N)) :=
 List.fold_left (fun m il => Maps.PTree.set (fst il) (nth arch (snd il) 0%N) m)
  al (Maps.PTree.empty N).

Definition GNU_errors : Maps.PTree.t N.
pose (j := process_GNU_errors
  (* This information is taken from 
      https://www.gnu.org/software/libc/manual/html_node/Errors-in-Math-Functions.html 
Function; Generic; AArch64; ARM; PowerPC; RISCV32; RISCV64; i686; x86_64 *)
[
(_acosf, [0; 1; 1; 1; 1; 1; 0; 1]);
(_acos, [0; 1; 1; 1; 0; 1; 1; 1]);
(_acoshf, [0; 2; 2; 2; 2; 2; 0; 2]);
(_acosh, [0; 2; 2; 2; 2; 2; 1; 2]);
(_asinf, [0; 1; 1; 1; 1; 1; 0; 1]);
(_asin, [0; 1; 1; 1; 0; 1; 1; 1]);
(_asinhf, [0; 2; 2; 2; 2; 2; 0; 2]);
(_asinh, [0; 2; 2; 2; 1; 2; 1; 2]);
(_atanf, [0; 1; 1; 1; 1; 1; 0; 1]);
(_atan, [0; 1; 1; 1; 0; 1; 1; 1]);
(_atan2f, [0; 1; 2; 1; 1; 1; 0; 2]);
(_atan2, [0; 0; 0; 0; 0; 0; 1; 0]);
(_atanhf, [0; 2; 2; 2; 2; 2; 0; 2]);
(_atanh, [0; 2; 2; 2; 2; 2; 1; 2]);
(_cbrtf, [0; 1; 1; 1; 1; 1; 1; 1]);
(_cbrt, [0; 4; 4; 4; 3; 4; 1; 4]);
(_cosf, [0; 1; 1; 3; 1; 1; 1; 1]);
(_cos, [0; 1; 1; 1; 1; 1; 1; 1]);
(_coshf, [0; 2; 2; 2; 2; 2; 2; 2]);
(_cosh, [0; 2; 2; 2; 1; 2; 1; 2]);
(_erff, [0; 1; 1; 1; 1; 1; 1; 1]);
(_erf, [0; 1; 1; 1; 1; 1; 1; 1]);
(_erfcf, [0; 2; 3; 2; 2; 2; 3; 3]);
(_erfc, [0; 2; 5; 2; 2; 2; 5; 5]);
(_expf, [0; 1; 1; 1; 1; 1; 1; 1]);
(_exp, [0; 1; 1; 1; 0; 1; 1; 1]);
(_exp2f, [0; 1; 1; 0; 0; 0; 0; 1]);
(_exp2, [0; 1; 1; 1; 1; 1; 1; 1]);
(_expm1f, [0; 1; 1; 1; 1; 1; 0; 1]);
(_expm1, [0; 1; 1; 1; 1; 1; 1; 1]);
(_fmodf, [0; 0; 0; 0; 0; 0; 0; 0]);
(_fmod, [0; 0; 0; 0; 0; 0; 0; 0]);
(_hypotf, [0; 0; 0; 0; 0; 0; 0; 0]);
(_hypot, [0; 1; 1; 1; 1; 1; 1; 1]);
(_lgammaf, [0; 4; 7; 4; 3; 3; 5; 7]);
(_lgamma, [0; 3; 4; 3; 3; 3; 4; 4]);
(_logf, [0; 1; 1; 1; 0; 0; 0; 1]);
(_log, [0; 1; 0; 1; 0; 1; 1; 1]);
(_log10f, [0; 2; 2; 2; 2; 2; 0; 2]);
(_log10, [0; 2; 2; 2; 2; 2; 1; 2]);
(_log1pf, [0; 1; 1; 1; 1; 1; 0; 1]);
(_log1p, [0; 1; 1; 1; 1; 1; 1; 1]);
(_log2f, [0; 1; 1; 1; 1; 1; 1; 1]);
(_log2, [0; 1; 2; 1; 1; 1; 1; 2]);
(_powf, [0; 1; 1; 1; 0; 0; 0; 1]);
(_pow, [0; 1; 1; 1; 1; 1; 1; 1]);
(_sinf, [0; 1; 1; 1; 1; 1; 1; 1]);
(_sin, [0; 1; 1; 1; 1; 1; 1; 1]);
(_sinhf, [0; 2; 2; 2; 2; 2; 2; 2]);
(_sinh, [0; 2; 2; 2; 2; 2; 2; 2]);
(_sqrtf, [0; 0; 0; 0; 0; 0; 0; 0]);
(_sqrt, [0; 0; 0; 0; 0; 0; 0; 0]);
(_tanf, [0; 1; 1; 3; 1; 1; 1; 1]);
(_tan, [0; 0; 0; 0; 0; 0; 0; 0]);
(_tanhf, [0; 2; 2; 2; 2; 2; 2; 2]);
(_tanh, [0; 2; 2; 2; 2; 2; 2; 2]);
(_tgammaf, [0; 8; 8; 8; 8; 8; 8; 8]);
(_tgamma, [0; 9; 9; 9; 5; 9; 9; 9])]%N).
compute in j.
exact j.
Defined.
End GNU_Errors.

Definition GNU_error (i: ident) : N := 
 match Maps.PTree.get i GNU_Errors.GNU_errors with Some z => z | None => 0%N end.

Definition reflect_to_ctype (t: FPCore.type) := 
match fprec t, femax t with
 | 53, 1024 => tdouble
 | 24, 128 => tfloat
 | _, _  => tvoid
 end.

Definition reflect_to_val_constructor (t: FPCore.type) :  ftype t -> val.
unfold ftype, fprec.
destruct (nonstd t).
exact (fun _ => Vundef).
exact    match (fprecp t), (femax t) with
   | 53%positive, 1024 => Vfloat
   | 24%positive, 128 => Vsingle
   | _, _  => fun _ => Vundef
   end.
Defined.

Definition reflect_to_val (t: FPCore.type) (x: ftype t) : val :=
  reflect_to_val_constructor t x.


Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.

Definition vacuous_funspec' args result : funspec := 
  mk_funspec (map reflect_to_ctype args, reflect_to_ctype result)
     cc_default
     (ConstType Impossible)
  (λne a, ⊤)
 (λne a : leibnizO Impossible , (fun _ => FF): _ -d> iProp Σ)
 (λne a : leibnizO Impossible , (fun _ => FF): _ -d> iProp Σ).

Definition floatspec {args result} :
  forall {precond rfunc} 
       (ff: floatfunc args result precond rfunc), @funspec Σ.
refine (match args with [a1] => _ | [a1;a2] => _ | [a1;a2;a3] => _ | _ => _ end); 
  intros.
exact (vacuous_funspec' args result).
refine (
   WITH x : ftype a1
   PRE [ reflect_to_ctype a1 ]
       PROP ()
       PARAMS (reflect_to_val a1 x)
       SEP ()
    POST [ reflect_to_ctype result ]
       PROP ()
       RETURN (reflect_to_val result  (ff_func ff x))
       SEP ()).
refine (
   WITH x1 : ftype a1, x2: ftype a2
   PRE [ reflect_to_ctype a1, reflect_to_ctype a2 ]
       PROP ()
       PARAMS (reflect_to_val a1 x1; reflect_to_val a2 x2)
       SEP ()
    POST [ reflect_to_ctype result ]
       PROP ()
       RETURN (reflect_to_val result (ff_func ff x1 x2))
       SEP ()).
refine (
   WITH x1 : ftype a1, x2: ftype a2, x3: ftype a3
   PRE [ reflect_to_ctype a1, reflect_to_ctype a2, reflect_to_ctype a3 ]
       PROP ()
       PARAMS (reflect_to_val a1 x1; reflect_to_val a2 x2; reflect_to_val a3 x3)
       SEP ()
    POST [ reflect_to_ctype result ]
       PROP ()
       RETURN (reflect_to_val result (ff_func ff x1 x2 x3))
       SEP ()).
exact (vacuous_funspec' args result).
Defined.

Lemma generic_round_property:
  forall (t: type) (x: R),
exists delta epsilon : R,
  (Rabs delta <= default_rel t)%R /\
  (Rabs epsilon <= default_abs t)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               x = (x * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
split3; auto.
Qed.

Require Import vcfloat.FPLang.
Set Bullet Behavior "Strict Subproofs".

Definition sqrt_bounds (ty: type) `{STD: is_standard ty} : klist bounds [ty] :=
  Kcons ((Zconst ty 0,false), (ftype_of_float (Binary.B754_infinity (fprec ty) (femax ty) false), true)) Knil.

Definition sqrt_ff (t: type)`{STD: is_standard t} : floatfunc  [ t ] t (sqrt_bounds t) R_sqrt.sqrt.
apply (Build_floatfunc  [ t ] t _ _ (BSQRT t _)  1%N 1%N).
intros x ?.
simpl in H.
rewrite andb_true_iff in H.
destruct H as [H H'].
unfold BSQRT, UNOP .
destruct (Binary.Bsqrt_correct (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) 
           (sqrt_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE (float_of_ftype x)) as [? [??]].

(*rewrite <- FT2R_ftype_of_float in H0.*)
rewrite <- (ftype_of_float_of_ftype STD STD x) in H,H'|-*.
rewrite !FT2R_ftype_of_float in *.
set (y := float_of_ftype x) in *.
clearbody y. clear x. rename y into x.
(*change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.*)
split3; [ tauto | intro Hx; inv Hx |  ].
rewrite !FT2R_ftype_of_float in *.
rewrite is_finite_Binary, !float_of_ftype_of_float.
intro.
-
rewrite H0; clear H0.
rewrite !Rmult_1_l.
split.
+
destruct t; simpl in *.
destruct nonstd; try contradiction.
destruct x; try destruct s; simpl in *; auto.
+
apply generic_round_property.
-
hnf; intros.
inv H. apply inj_pair2 in H2,H3.  subst. 
inv H5. apply inj_pair2 in H,H0.  subst.
rewrite (@float_equiv_binary_float_equiv _ STD) in *.
unfold applyk, applyk_aux, eq_rect_r, eq_rect, eq_sym; simpl.
unfold BSQRT, UNOP.
rewrite !float_of_ftype_of_float.
set (x := @float_of_ftype _ STD ah) in *. set (y := @float_of_ftype _ STD bh) in *.
clearbody x. clearbody y. clear ah bh.
destruct x; try destruct s; destruct y; try destruct s; simpl; try contradiction; auto;
destruct H4 as [? [? ?]]; subst; try discriminate.
proof_irr.
apply binary_float_equiv_refl.
Defined.

Definition finite_bnds ty {STD: is_standard ty} : bounds ty := 
    ((ftype_of_float (Binary.B754_infinity (fprec ty) (femax ty) true), true), 
     (ftype_of_float (Binary.B754_infinity (fprec ty) (femax ty) false), true)).

Lemma finite_bnds_e: forall t {STD: is_standard t} (x: ftype t),
  interp_bounds (finite_bnds t) x = true -> is_finite x = true.
Proof.
intros.
simpl in H. rewrite andb_true_iff in H; destruct H.
rewrite is_finite_Binary.
unfold compare, compare' in *.
destruct t; simpl in *.
destruct nonstd; try contradiction; clear STD.
unfold extend_comp in *; simpl in *.
destruct x; try destruct s; auto; discriminate.
Qed.

Definition vacuous_bnds ty {STD: is_standard ty} : bounds ty := 
    ((ftype_of_float (Binary.B754_infinity (fprec ty) (femax ty) true), false), 
     (ftype_of_float (Binary.B754_infinity (fprec ty) (femax ty) false), false)).

Lemma vacuous_bnds_i: forall {ty} {STD: is_standard ty}  {x: ftype ty},
  is_finite x = true -> 
   interp_bounds (vacuous_bnds ty) x = true.
Proof.
intros.
rewrite is_finite_Binary in H.
unfold interp_bounds, vacuous_bnds.
destruct ty. destruct nonstd; try contradiction; simpl in *.
destruct x; try destruct s; try discriminate; simpl; try reflexivity.
Qed.

Lemma exact_round_abs: forall t (x: ftype t), exact_round t (Rabs (FT2R x)).
Admitted.

Definition abs_ff (t: type) `{STD: is_standard t} : floatfunc  [ t ] t (Kcons (finite_bnds t) Knil) Rabs.
apply (Build_floatfunc  [ t ] t _ _ BABS  0%N 0%N).
intros x ?.
simpl in H.
rewrite andb_true_iff in H.
destruct H as [H H0].
unfold BABS, UNOP .
split3; [ tauto | intro Hx; inv Hx |  ].
-
 apply exact_round_abs.
-
 intro FIN.
 split.
 + rewrite is_finite_Binary, float_of_ftype_of_float.
   rewrite <- (ftype_of_float_of_ftype _ STD x) in H,H0,FIN.
   rewrite FT2R_ftype_of_float in FIN.
   set (y := float_of_ftype x) in *. clearbody y. clear x.
   destruct t, nonstd; try contradiction.
   simpl in *.
  destruct y; try destruct s; auto; try discriminate.
 +
   rewrite <- (ftype_of_float_of_ftype _ STD x) in *|-*.
   rewrite ?FT2R_ftype_of_float in *.
   rewrite ?float_of_ftype_of_float in *.  
   set (y := float_of_ftype x) in *. clearbody y. clear x.
   pose proof (Binary.B2R_Babs (fprec t) (femax t) 
                (FPCore.abs_nan (fprec t) (femax t) (fprec_gt_one t))
                       y).
   rewrite H1; clear H1.
   exists 0%R, 0%R.
   split; simpl;
rewrite Rabs_R0;
try match goal with |- context [Raux.bpow ?a ?b] =>
  pose proof (Raux.bpow_gt_0 a b)
end;
Lra.nra.
-
 red.
 intros.
 inv H. apply inj_pair2 in H2,H3. subst.
 inv H5.  apply inj_pair2 in H,H0. subst.
  simpl. unfold eq_rect_r, eq_rect, eq_sym; simpl.
  unfold BABS, UNOP.
  destruct t; destruct nonstd; try contradiction; simpl.
  destruct ah; try destruct s; destruct bh; try destruct s;
  try contradiction; try discriminate; try reflexivity;
  simpl in H4;
  destruct H4 as [? [? ?]]; subst; repeat proof_irr; simpl; auto.  
Defined.

Lemma trunc_ff_aux: forall t `{STD: is_standard t} (x: ftype t),
  is_finite x = true ->
  (Rabs (FT2R x) < Raux.bpow Zaux.radix2 (femax t - 1))%R ->
  (Rabs  (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (IZR (Binary.Btrunc (fprec t) (femax t) (float_of_ftype x))))
           <  Raux.bpow Zaux.radix2 (femax t) )%R.
Admitted. (* might be true *)

Definition trunc_max (ty: type) : ftype ty.
 (* Raux.bpow Zaux.radix2 (femax ty - 1)))  *)
Admitted.

Definition trunc_bounds (ty: type) `{STD: is_standard ty} : bounds ty :=
    ((BOPP (trunc_max ty), true),   (trunc_max ty, true)).

Lemma trunc_bounds_e (ty: type) `{STD: is_standard ty}:
  forall x: ftype ty, 
  interp_bounds (trunc_bounds ty) x = true ->
  is_finite x  = true /\
 Rlt (Rabs (FT2R x)) (Raux.bpow Zaux.radix2 (femax ty - 1)).
Admitted.


Definition trunc_ff (t: type) `{STD: is_standard t} : floatfunc  [ t ] t  (Kcons (trunc_bounds t) Knil)
           (Generic_fmt.round Zaux.radix2 (FIX.FIX_exp 0) Raux.Ztrunc).
apply (Build_floatfunc  [ t ] t _ _ 
              (fun x => ftype_of_float (IEEE754_extra.BofZ (fprec t) (femax t)  
                           (fprec_gt_0 t) (fprec_lt_femax t)
                      (Binary.Btrunc (fprec t) (femax t) (float_of_ftype x))))
                      1%N 1%N).
-
intros x H.
split3; [ tauto | intro Hx; inv Hx | ].
intros H0.
apply trunc_bounds_e in H.
destruct H as [FIN  H].
pose proof (Binary.Btrunc_correct (fprec t) (femax t) (fprec_lt_femax t) (float_of_ftype x)).
replace (FT2R x) with (Binary.B2R (fprec t) (femax t) (float_of_ftype x))
 by (rewrite <- ftype_of_float_of_ftype at 2; rewrite FT2R_ftype_of_float; auto).
rewrite FT2R_ftype_of_float.
rewrite <- H1; clear H1.
pose proof IEEE754_extra.BofZ_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
            (Binary.Btrunc (fprec t) (femax t) (float_of_ftype x)).
match type of H1 with if Raux.Rlt_bool ?a ?b then _ else _ => 
  destruct (Raux.Rlt_bool_spec a b)
end.
+
destruct H1 as [? [? ?]].
rewrite H1.
split.
rewrite is_finite_Binary, float_of_ftype_of_float.
destruct (float_of_ftype x); try destruct s; try discriminate; auto.
simpl.
rewrite !Rmult_1_l.
apply generic_round_property.
+
exfalso; clear - VSTGS_OK H H0 H2 FIN.
pose proof trunc_ff_aux t x FIN.
Lra.lra.
-
hnf; intros.
inv H. apply inj_pair2 in H2,H3.  subst. 
inv H5. apply inj_pair2 in H,H0.  subst.
destruct t; destruct nonstd; try contradiction; simpl in *.
unfold eq_rect_r, eq_rect, eq_sym; simpl.
destruct ah; try destruct s; destruct bh; try destruct s; simpl in *; auto; try contradiction;
 destruct H4 as [? [? ?]]; try discriminate; subst; repeat proof_irr;
apply binary_float_equiv_refl.
Defined.

(*
Definition fma_no_overflow (t: type) (x y z: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.
*)

Definition rounded_finite (t: type) (x: R) : Prop :=
  (Rabs (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
                         (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) x) 
    < Raux.bpow Zaux.radix2 (femax t))%R.


Definition fma_bnds (t: type) `{STD: is_standard t} := 
   Kcons (finite_bnds t) (Kcons (finite_bnds t) (Kcons (finite_bnds t) Knil)).

Lemma B2R_float_of_ftype: forall {ty} {STD: is_standard ty} (x: ftype ty),
    Binary.B2R _ _ (float_of_ftype x) = FT2R x.
Proof.
intros.
rewrite <- (ftype_of_float_of_ftype _ _ x).
rewrite FT2R_ftype_of_float.
rewrite ftype_of_float_of_ftype; auto.
Qed.

Require Import vcfloat.FPLib.

Lemma feq_float_equiv: 
  forall t `{STD: is_standard t} (x y: ftype t), 
   is_finite x = true -> is_finite y = true -> 
   (float_equiv x y -> feq x y).
Proof.
intros.
rewrite <- feq'_iff.
rewrite (@float_equiv_binary_float_equiv _ STD) in *.
rewrite is_finite_Binary in *.
unfold feq', binary_float_equiv in *.
destruct (float_of_ftype x), (float_of_ftype y); auto; try tauto;
try discriminate.
Qed.

Ltac binary_float_equiv_cases H := 
 match type of H with binary_float_equiv ?ah ?bh =>
   destruct ah as [ [|] | [|] | | [|] ? ?] ; 
   destruct bh as [ [|] | [|] | | [|] ? ?] ; 
   simpl in H;
   try match type of H with _ /\ _ /\ _ => destruct H as [? [? ?]]; subst end;
   simpl in *; auto; try contradiction; try discriminate
 end.

Lemma fma_ff_aux1:
 forall (t : type) (STD : is_standard t),
 acc_prop [t; t; t] t 1 1 (fma_bnds t) (fun x y z : RR t => (x * y + z)%R)
   (fun x y z : ftype' t =>
    ftype_of_float
     (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
        (fma_nan (fprec t) (femax t) (fprec_gt_one t)) 
        BinarySingleNaN.mode_NE (float_of_ftype x) 
        (float_of_ftype y) (float_of_ftype z))).
Proof.
intros.
intros x ? y ? z ?.
rewrite <- !B2R_float_of_ftype.
split3; [ tauto | intro Hx; inv Hx | ].
rewrite FT2R_ftype_of_float.
rewrite is_finite_Binary, float_of_ftype_of_float.
intros FIN.
simpl.
apply finite_bnds_e in H,H0,H1.
rewrite is_finite_Binary in *.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) 
                (fma_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE (float_of_ftype x) (float_of_ftype y) (float_of_ftype z) H H0 H1).
cbv zeta in H2.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (Binary.B2R (fprec t) (femax t) (float_of_ftype x) *
           Binary.B2R (fprec t) (femax t) (float_of_ftype y) +
           Binary.B2R (fprec t) (femax t) (float_of_ftype z)) ))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H3.
+
destruct H2 as [? [? ?]].
change (FMA_NAN.fma_nan_pl (fprec t) (femax t) (fprec_gt_one t)) with
   (fma_nan (fprec t) (femax t) (fprec_gt_one t)).
rewrite H2.
rewrite !Rmult_1_l.
split; auto.
apply generic_round_property.
+
exfalso.
red in FIN.
set (u := Rabs _) in *.
set (v := Raux.bpow _ _) in *.
clear - FIN H3.
Lra.lra.
Qed.


Lemma fma_ff_aux2:
 forall (t : type) `(STD : is_standard t),
 @floatfunc_congr [t; t; t] t
  (fun x y z : ftype' t =>
    ftype_of_float
     (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
        (@fma_nan _ (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE (@float_of_ftype t STD x)
        (@float_of_ftype t STD y) (@float_of_ftype t STD z))).
Proof.
intros; hnf; intros.
inv H. apply inj_pair2 in H2,H3.  subst. 
inv H5. apply inj_pair2 in H1,H2.  subst.
inv H6. apply inj_pair2 in H1,H2.  subst.
inv H7. apply inj_pair2 in H,H0.  subst.

rewrite (float_equiv_binary_float_equiv _ STD) in H4, H3, H5.
destruct t; destruct nonstd; try contradiction; simpl in *.
unfold eq_rect_r, eq_rect, eq_sym; simpl.
unfold eq_rect_r, eq_rect, eq_sym; simpl.
unfold eq_rect_r, eq_rect, eq_sym; simpl.
simpl in *.
unfold ftype in *. simpl in *.
set (J0 := fprec_gt_0 _)  in *.
set (J1 := fprec_lt_femax _) in *.
set (prec := FPCore.fprec _) in *.
unfold FPCore.femax in *.
clearbody J0. clearbody J1.
binary_float_equiv_cases H4;
binary_float_equiv_cases H3;
binary_float_equiv_cases H5;
apply binary_float_equiv_refl.
Qed.

Definition fma_ff (t: type) `{STD: is_standard t}  : floatfunc  [ t;t;t ] t (fma_bnds t) (fun x y z => x*y+z)%R.
apply (Build_floatfunc [t;t;t] t _ _ 
         (fun x y z => ftype_of_float (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
               (fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
              (float_of_ftype x) (float_of_ftype y) (float_of_ftype z)))
           1%N 1%N).
apply fma_ff_aux1.
apply fma_ff_aux2.
Defined.

Definition ldexp_spec' (t: type) `{STD: is_standard t} : @funspec Σ :=
   WITH x : ftype t, i: Z
   PRE [ reflect_to_ctype t , tint ]
       PROP (Int.min_signed <= i <= Int.max_signed)
       PARAMS (reflect_to_val t x; Vint (Int.repr i))
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t 
                (ftype_of_float (Binary.Bldexp (fprec t) (femax t) 
                  (fprec_gt_0 t) (fprec_lt_femax t) BinarySingleNaN.mode_NE
                   (float_of_ftype x) i)))
       SEP ().

Definition frexp_spec' (t: type) `{STD: is_standard t} :=
   WITH x : ftype t, p: val, sh: share
   PRE [ reflect_to_ctype t , tptr tint ]
       PROP (writable_share sh)
       PARAMS (reflect_to_val t x; p)
       SEP (data_at_ (cs:=emptyCS) sh tint p)
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t 
                     (ftype_of_float (fst (Binary.Bfrexp (fprec t) (femax t)  (fprec_gt_0 t) 
                              (float_of_ftype x)))))
       SEP (data_at (cs:=emptyCS) sh tint (Vint (Int.repr 
                         (snd (Binary.Bfrexp (fprec t) (femax t)  (fprec_gt_0 t) 
                              (float_of_ftype x)))))
                         p).

Definition bogus_nan t `(STD: is_standard t) := 
   (* This is probably not the right NaN to use, wherever you see it used *)
   FMA_NAN.quiet_nan  (fprec t) (femax t) (fprec_gt_one t) 
   (FMA_NAN.default_nan  (fprec t)). 

Definition nextafter (t: type) `{STD: is_standard t} (x y: ftype t) : ftype t := 
 match Binary.Bcompare (fprec t) (femax t) (float_of_ftype x) (float_of_ftype y) with
  | Some Lt => ftype_of_float (Binary.Bsucc (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t)
                     (float_of_ftype x))
  | Some Eq => y
  | Some Gt => ftype_of_float (Binary.Bpred (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) 
                     (float_of_ftype x))
  | None => ftype_of_float (proj1_sig (bogus_nan t _))
  end.

Definition nextafter_spec' (t: type) `{STD: is_standard t} : @funspec Σ  :=
   WITH x : ftype t, y: ftype t
   PRE [ reflect_to_ctype t , reflect_to_ctype t ]
       PROP ()
       PARAMS (reflect_to_val t x; reflect_to_val t y)
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t (nextafter t x y))
       SEP ().

Definition copysign (t: type) `{STD: is_standard t} (x y: ftype t) : ftype t :=
 ftype_of_float
 match float_of_ftype x with
 | Binary.B754_zero _ _ _ => Binary.B754_zero _ _ (Binary.Bsign _ _ (float_of_ftype y))
 | Binary.B754_infinity _ _ _ => Binary.B754_infinity _ _ (Binary.Bsign _ _ (float_of_ftype y))
 | Binary.B754_finite _ _ _ m e H => Binary.B754_finite _ _ (Binary.Bsign _ _ (float_of_ftype y)) m e H
 | Binary.B754_nan _ _ _ pl H => Binary.B754_nan _ _ (Binary.Bsign _ _ (float_of_ftype y)) pl H
end.

Definition copysign_spec' (t: type) `{STD: is_standard t} : @funspec Σ  :=
   WITH x : ftype t, y : ftype t
   PRE [ reflect_to_ctype t , reflect_to_ctype t ]
       PROP ()
       PARAMS (reflect_to_val t x; reflect_to_val t y) 
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t (copysign t x y))
       SEP ().

Definition nan_spec' (t: type) `{STD: is_standard t}: @funspec Σ  :=
   WITH p: val
   PRE [ tptr tschar ]
       PROP ()
       PARAMS (p) 
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
        (* here it _is_ actually permissible to use bogus_nan *)
       RETURN (reflect_to_val t (ftype_of_float (proj1_sig (bogus_nan t _))))
       SEP ().

Definition arccosh (x: R) := Rabs (Rpower.arcsinh (sqrt (Rsqr x - 1)))%R.
Definition arctanh (x: R) := (/2 * ln ((1+x)/(1-x)) )%R.

Fixpoint always_true (args: list type) : function_type (map RR args) Prop :=
 match args with
 | nil => True
 | _ :: args' => fun _ => always_true args'
 end.

End GFUNCTORS.

Ltac floatspec Σ f :=
   let a := constr:(floatspec (Σ:=Σ) f) in
   let a := eval cbv [floatspec reflect_to_ctype reflect_to_val reflect_to_val_constructor] in a in 
   let a := eval simpl in a in
   exact a.

Ltac vacuous_bnds_list tys :=
 match tys with
 | nil => constr:(@Knil _ bounds )
 | ?t :: ?ts =>
   let b := constr:(vacuous_bnds t) in
   let bs := vacuous_bnds_list ts in
   constr:(Kcons b bs)
 end.

(*
Fixpoint vacuous_bnds_klist (tys: list type) : klist bounds tys :=
 match tys as l return (klist bounds l) with
  | [] => Knil
  | a :: l =>
      (fun (t : type) (tys0 : list type) =>
       Kcons (vacuous_bnds t) (vacuous_bnds_klist tys0)) a l
  end.
*)

Parameter c_function: forall (i: ident) (args: list type) (res: type)
      bnds
     (f: function_type (map RR args) R),
   {ff: function_type (map ftype' args) (ftype res) 
   | acc_prop args res (1 + (2 * GNU_error i))%N 1%N bnds f ff}.

Parameter axiom_floatfunc_congr: forall args result ff_func, 
   @floatfunc_congr args result ff_func.

Ltac floatfunc' i args res f :=
 let rel := constr:((1 + 2 * GNU_error i)%N) in
 let rel := eval compute in rel in 
 let abs := constr:(1%N) in
 let bnds := vacuous_bnds_list args in
 let cf := constr:(c_function i args res bnds f) in
 exact (Build_floatfunc args res bnds f (proj1_sig cf) rel abs (proj2_sig cf)
        (axiom_floatfunc_congr _ _ _)).


Module Type MathFunctions.
Definition acos := ltac:(floatfunc' _acos [Tdouble] Tdouble Ratan.acos).
Definition acosf := ltac:(floatfunc' _acos [Tsingle] Tsingle Ratan.acos).
Definition acosh := ltac:(floatfunc' _acosh [Tdouble] Tdouble arccosh).
Definition acoshf := ltac:(floatfunc' _acoshf [Tsingle] Tsingle arccosh).
Definition asin := ltac:(floatfunc' _asin [Tdouble] Tdouble Ratan.asin).
Definition asinf := ltac:(floatfunc' _asinf [Tsingle] Tsingle Ratan.asin).
Definition asinh := ltac:(floatfunc' _asinh [Tdouble] Tdouble Rpower.arcsinh).
Definition asinhf := ltac:(floatfunc' _asinhf [Tsingle] Tsingle Rpower.arcsinh).
Definition atan := ltac:(floatfunc' _atan [Tdouble] Tdouble Ratan.atan). 
Definition atanf := ltac:(floatfunc' _atanf [Tsingle] Tsingle Ratan.atan).
Definition atan2 := ltac:(floatfunc' _atan2 [Tdouble;Tdouble] Tdouble (fun y x => Ratan.atan(y/x))%R). 
Definition atan2f := ltac:(floatfunc' _atan2f [Tsingle;Tsingle] Tsingle (fun y x => Ratan.atan(y/x))%R). 
Definition atanh := ltac:(floatfunc' _atanh [Tdouble] Tdouble arctanh).
Definition atanhf := ltac:(floatfunc' _atanhf [Tsingle] Tsingle arctanh).
Definition cbrt := ltac:(floatfunc' _cbrt [Tdouble] Tdouble (fun x => Rpower x (/3))%R).
Definition cbrtf := ltac:(floatfunc' _cbrtf [Tsingle] Tsingle (fun x => Rpower x (/3))%R).
Definition cos := ltac:(floatfunc' _cos [Tdouble] Tdouble Rtrigo_def.cos). 
Axiom FINcos: forall t, Binary.is_finite _ _ (ff_func cos t) = true.
Definition cosf := ltac:(floatfunc' _cosf [Tsingle] Tsingle Rtrigo_def.cos).
Definition cosh := ltac:(floatfunc' _cosh [Tdouble] Tdouble Rtrigo_def.cosh).
Definition coshf := ltac:(floatfunc' _coshf [Tsingle] Tsingle Rtrigo_def.cosh).
Definition exp := ltac:( floatfunc' _exp [Tdouble] Tdouble Rtrigo_def.exp).
Definition expf := ltac:( floatfunc' _expf [Tsingle] Tsingle Rtrigo_def.exp).
Definition exp2 := ltac:( floatfunc' _exp2 [Tdouble] Tdouble (Rpower 2%R)).
Definition exp2f := ltac:( floatfunc' _exp2f [Tsingle] Tsingle  (Rpower 2%R)).
Definition expm1 := ltac:( floatfunc' _expm1 [Tdouble] Tdouble (fun x => Rtrigo_def.exp x - 1)%R).
Definition expm1f := ltac:( floatfunc' _expm1f [Tsingle] Tsingle (fun x => Rtrigo_def.exp x - 1)%R).
Definition pow := ltac:(floatfunc' _pow [Tdouble;Tdouble] Tdouble Rpower). 
Definition powf := ltac:(floatfunc' _powf [Tsingle;Tsingle] Tsingle Rpower). 
Definition sin := ltac:(floatfunc' _sin [Tdouble] Tdouble Rtrigo_def.sin).
Axiom FINsin: forall t, Binary.is_finite _ _ (ff_func sin t) = true.
Definition sinf := ltac:(floatfunc' _sinf [Tsingle] Tsingle Rtrigo_def.sin).
Definition sinh := ltac:(floatfunc' _sinh [Tdouble] Tdouble Rtrigo_def.sinh).
Definition sinhf := ltac:(floatfunc' _sinhf [Tsingle] Tsingle Rtrigo_def.sinh).
Definition tan := ltac:(floatfunc' _tan [Tdouble] Tdouble Rtrigo1.tan).
Definition tanf := ltac:(floatfunc' _tanf [Tsingle] Tsingle Rtrigo1.tan).
Definition tanh := ltac:(floatfunc' _tanh [Tdouble] Tdouble Rtrigo_def.tanh).
Definition tanhf := ltac:(floatfunc' _tanhf [Tsingle] Tsingle Rtrigo_def.tanh).

End MathFunctions.

Declare Module MF: MathFunctions.

Ltac reduce1 t := 
    let p := eval red in t in 
   let a := eval cbv [reflect_to_ctype reflect_to_val reflect_to_val_constructor] in p in 
   let a := eval simpl in a in
   exact a.

Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.

Definition acos_spec := DECLARE _acos ltac:(floatspec Σ MF.acos). 
Definition acosf_spec := DECLARE _acosf ltac:(floatspec Σ MF.acosf).
Definition acosh_spec := DECLARE _acosh ltac:(floatspec Σ MF.acosh).
Definition acoshf_spec := DECLARE _acoshf ltac:(floatspec Σ MF.acoshf).
Definition asin_spec := DECLARE _asin ltac:(floatspec Σ MF.asin).
Definition asinf_spec := DECLARE _asinf ltac:(floatspec Σ MF.asinf).
Definition asinh_spec := DECLARE _asinh ltac:(floatspec Σ MF.asinh).
Definition asinhf_spec := DECLARE _asinhf ltac:(floatspec Σ MF.asinhf).
Definition atan_spec := DECLARE _atan ltac:(floatspec Σ MF.atan).
Definition atanf_spec := DECLARE _atanf ltac:(floatspec Σ MF.atanf).
Definition atan2_spec := DECLARE _atan2 ltac:(floatspec Σ MF.atan2).
Definition atan2f_spec := DECLARE _atan2f ltac:(floatspec Σ MF.atan2f).
Definition atanh_spec := DECLARE _atanh ltac:(floatspec Σ MF.atanh).
Definition atanhf_spec := DECLARE _atanhf ltac:(floatspec Σ MF.atanhf).
Definition cbrt_spec := DECLARE _cbrt ltac:(floatspec Σ MF.cbrt).
Definition cbrtf_spec := DECLARE _cbrtf ltac:(floatspec Σ MF.cbrtf).
Definition copysign_spec := DECLARE _copysign ltac:(reduce1 (copysign_spec' (Σ:=Σ) Tdouble)).
Definition copysignf_spec := DECLARE _copysignf ltac:(reduce1 (copysign_spec' (Σ:=Σ)  Tsingle)).
Definition cos_spec := DECLARE _cos ltac:(floatspec Σ MF.cos).
Definition cosf_spec := DECLARE _cosf ltac:(floatspec Σ MF.cosf).
Definition cosh_spec := DECLARE _cosh ltac:(floatspec Σ MF.cosh).
Definition coshf_spec := DECLARE _coshf ltac:(floatspec Σ MF.coshf).
Definition exp_spec := DECLARE _exp ltac:(floatspec Σ MF.exp).
Definition expf_spec := DECLARE _expf ltac:(floatspec Σ MF.expf).
Definition exp2_spec := DECLARE _exp2 ltac:(floatspec Σ MF.exp2).
Definition exp2f_spec := DECLARE _exp2f ltac:(floatspec Σ MF.exp2f).
Definition expm1_spec := DECLARE _expm1 ltac:(floatspec Σ MF.expm1).
Definition expm1f_spec := DECLARE _expm1f ltac:(floatspec Σ MF.expm1f).
Definition fabs_spec := DECLARE _fabs ltac:(floatspec Σ (abs_ff Tdouble)).
Definition fabsf_spec := DECLARE _fabsf ltac:(floatspec Σ (abs_ff Tsingle)).
Definition pow_spec := DECLARE _pow ltac:(floatspec Σ MF.pow).
Definition powf_spec := DECLARE _powf ltac:(floatspec Σ MF.powf).
Definition sqrt_spec := DECLARE _sqrt ltac:(floatspec Σ (sqrt_ff Tdouble)).
Definition sqrtf_spec := DECLARE _sqrtf ltac:(floatspec Σ (sqrt_ff Tsingle)).
Definition sin_spec := DECLARE _sin ltac:(floatspec Σ MF.sin).
Definition sinf_spec := DECLARE _sinf ltac:(floatspec Σ MF.sinf).
Definition sinh_spec := DECLARE _sinh ltac:(floatspec Σ MF.sinh).
Definition sinhf_spec := DECLARE _sinhf ltac:(floatspec Σ MF.sinhf).
Definition tan_spec := DECLARE _tan ltac:(floatspec Σ MF.tan).
Definition tanf_spec := DECLARE _tanf ltac:(floatspec Σ MF.tanf).
Definition tanh_spec := DECLARE _tanh ltac:(floatspec Σ MF.tanh).
Definition tanhf_spec := DECLARE _tanhf ltac:(floatspec Σ MF.tanhf).

Definition fma_spec := DECLARE _fma ltac:(floatspec Σ (fma_ff Tdouble)).
Definition fmaf_spec := DECLARE _fmaf ltac:(floatspec Σ (fma_ff Tsingle)).
Definition frexp_spec := DECLARE _frexp ltac:(reduce1 (frexp_spec' Tdouble)).
Definition frexpf_spec := DECLARE _frexpf ltac:(reduce1 (frexp_spec' Tsingle)).
Definition ldexp_spec := DECLARE _ldexp ltac:(reduce1 (ldexp_spec' (Σ:=Σ) Tdouble)).
Definition ldexpf_spec := DECLARE _ldexpf ltac:(reduce1 (ldexp_spec' (Σ:=Σ) Tsingle)).
Definition nan_spec := DECLARE _nan ltac:(reduce1 (nan_spec' (Σ:=Σ) Tdouble)).
Definition nanf_spec := DECLARE _nanf ltac:(reduce1 (nan_spec' (Σ:=Σ) Tsingle)).
Definition nextafter_spec := DECLARE _nextafter ltac:(reduce1 (nextafter_spec' (Σ:=Σ) Tdouble)).
Definition nextafterf_spec := DECLARE _nextafterf ltac:(reduce1 (nextafter_spec' (Σ:=Σ) Tsingle)).
Definition trunc_spec := DECLARE _trunc ltac:(floatspec Σ (trunc_ff Tdouble)).
Definition truncf_spec := DECLARE _truncf ltac:(floatspec Σ (trunc_ff Tsingle)).

Definition MathASI:funspecs := [ 
  acos_spec; acosf_spec; acosh_spec; acoshf_spec; asin_spec; asinf_spec; asinh_spec; asinhf_spec;
  atan_spec; atanf_spec; atan2_spec; atan2f_spec; atanh_spec; atanhf_spec;
  cbrt_spec; cbrtf_spec; copysign_spec; copysignf_spec;
  cos_spec; cosf_spec; cosh_spec; coshf_spec; 
  exp_spec; expf_spec; exp2_spec; exp2f_spec; expm1_spec; expm1f_spec;
  fabs_spec; fabsf_spec; pow_spec; powf_spec; sqrt_spec; sqrtf_spec; 
  sin_spec; sinf_spec; sinh_spec; sinhf_spec;
  tan_spec; tanf_spec; tanh_spec; tanhf_spec; 
  fma_spec; fmaf_spec; frexp_spec; frexpf_spec; ldexp_spec; ldexpf_spec; 
  nan_spec; nanf_spec; nextafter_spec; nextafterf_spec; trunc_spec; truncf_spec
].

Goal map string_of_ident (duplicate_ids (map fst MathASI)) = nil.
compute.
reflexivity. (* If this line fails, then it lists the duplicate names in your DECLARE statements above *)
Abort.

Local Remark sqrt_accurate: forall x: ftype Tdouble, 
  (0 <= FT2R x ->
   Binary.is_finite (fprec Tdouble) (femax Tdouble) x = true ->
   exists delta, exists epsilon,
   Rabs delta <= default_rel Tdouble /\
   Rabs epsilon <= default_abs Tdouble /\ 
   exists x', nonneg x' = FT2R x /\
   FT2R (ff_func (sqrt_ff Tdouble) x) = sqrt x' * (1+delta) + epsilon)%R.
Proof.
intros.
rename H0 into H8.
assert (H0: Binary.is_finite _ _ (ff_func (sqrt_ff Tdouble) x) = true). {
  destruct x; try destruct s; try discriminate; simpl; auto.
 -
  simpl in H. unfold FT2R in H.  simpl in H. unfold Defs.F2R in H. simpl in H.
  pose proof Raux.bpow_gt_0 Zaux.radix2 e.
  rewrite IZR_NEG in H. unfold IZR in H.
  set (j :=  Raux.bpow Zaux.radix2 e) in *. clearbody j.
 rewrite Ropp_mult_distr_l_reverse in H.
 clear - H H0.
 pose proof (IZR_lt 0 (Z.pos m) ltac:(lia)). unfold IZR in H1.
 unfold IZR in H0.
 Lra.nra.
 - unfold BSQRT, UNOP; simpl.
  destruct (Binary.Bsqrt_correct (fprec Tdouble) 1024 (fprec_gt_0 Tdouble)
     (fprec_lt_femax Tdouble)  (fun _ : Binary.binary_float (fprec Tdouble) 1024 =>
      any_nan (fprec Tdouble) (femax Tdouble) (fprec_gt_one Tdouble)) BinarySingleNaN.mode_NE
  (Binary.B754_finite (fprec Tdouble) 1024 false m e e0)).
 apply H1.
}  
assert (interp_bounds
   (Zconst Tdouble 0, false,  (Binary.B754_infinity (fprec Tdouble) (femax Tdouble) false, true))
   x = true). {
 destruct x eqn:?H; try destruct s; try discriminate; simpl; auto.
}
destruct (ff_acc (sqrt_ff Tdouble) x H1) as [_ [_ ?]].
destruct H2 as [FIN [delta [epsilon [? [? ?]]]]].
admit.  (* should be provable *)
exists delta, epsilon.
simpl in H2,H3.
rewrite Rmult_1_l in *.
split3; auto.
destruct (Rcase_abs (FT2R x)). Lra.lra.
exists {| nonneg:= FT2R x; cond_nonneg := H |}.
split; auto.
Admitted.

End GFUNCTORS.

