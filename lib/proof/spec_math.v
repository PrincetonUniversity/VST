Require Import VST.floyd.proofauto.
Require Import VSTlib.math_extern.
Require Import vcfloat.FPCompCert.
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

Definition process_GNU_errors (al: list (ident * list Z)) :=
 List.fold_left (fun m il => Maps.PTree.set (fst il) (nth arch (snd il) 0) m)
  al (Maps.PTree.empty Z).

Definition GNU_errors : Maps.PTree.t Z.
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
(_tgamma, [0; 9; 9; 9; 5; 9; 9; 9])]).
compute in j.
exact j.
Defined.
End GNU_Errors.

Definition GNU_error (i: ident) : Z := 
 match Maps.PTree.get i GNU_Errors.GNU_errors with Some z => z | None => 0 end.

Fixpoint function_type (args: list Type) (rhs: Type) : Type :=
  match args with
  | nil => rhs
  | a::r =>  a -> function_type r rhs
 end.

Definition RR (_: FPCore.type) : Type := R.
Definition ftype'  (t: FPCore.type) : Type := ftype t.

Fixpoint acc_prop  (args: list FPCore.type) (result: FPCore.type)
             (rel abs : R)
             (precond: function_type (map RR args) Prop)
             (rf: function_type (map RR args) R)
             (f: function_type (map ftype' args) (ftype' result)) {struct args} : Prop.
destruct args as [ | a r].
exact (precond ->
                   Binary.is_finite _ _ f = true /\ 
                   exists delta epsilon,
                  (Rabs delta <= rel /\ Rabs epsilon <= abs /\
                   FT2R f = rf * (1+delta) + epsilon)%R).
exact (forall z: ftype a, Binary.is_finite (fprec a) (femax a) z = true ->
            acc_prop r result rel abs (precond (FT2R z)) (rf (FT2R z)) (f z)).
Defined.

Record floatfunc (args: list FPCore.type) (result: FPCore.type) 
     (precond: function_type (map RR args) Prop)
     (realfunc: function_type (map RR args) R) := 
 {ff_func: function_type (map ftype' args) (ftype' result);
  ff_rel: R;
  ff_abs: R;
  ff_acc: acc_prop args result ff_rel ff_abs precond realfunc ff_func
 }.

(*
Record floatfunc (args: list FPCore.type) (result: FPCore.type) 
     (precond: function_type (map RR args) Prop)
     (realfunc: function_type (map RR args) R)
     (rel abs: R) :=
 {ff_func: function_type (map ftype' args) (ftype' result);
  ff_acc: acc_prop args result rel abs precond realfunc ff_func
 }.
*)

Arguments ff_func [args result precond realfunc].
Arguments ff_acc [args result precond realfunc].
Arguments ff_rel [args result precond realfunc].
Arguments ff_abs [args result precond realfunc].

Definition default_rel (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Definition reflect_to_ctype (t: FPCore.type) := 
match fprec t, femax t with
 | 53, 1024 => tdouble
 | 24, 128 => tfloat
 | _, _  => tvoid
 end.

Definition reflect_to_val_constructor (t: FPCore.type) :  ftype t -> val.
unfold ftype, fprec.
exact    match (fprecp t), (femax t) with
   | 53%positive, 1024 => Vfloat
   | 24%positive, 128 => Vsingle
   | _, _  => fun _ => Vundef
   end.
Defined.

Definition reflect_to_val (t: FPCore.type) (x: ftype t) : val :=
  reflect_to_val_constructor t x.

Definition vacuous_funspec' args result : funspec := 
  mk_funspec (map reflect_to_ctype args, reflect_to_ctype result) cc_default
     (rmaps.ConstType Impossible)
     (fun _ _ => FF) (fun _ _ => FF) 
     (args_const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition floatspec {args result} :
  forall {precond rfunc} 
       (ff: floatfunc args result precond rfunc), funspec.
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

Ltac floatspec f :=
   let a := constr:(floatspec f) in
   let a := eval cbv [floatspec reflect_to_ctype reflect_to_val reflect_to_val_constructor] in a in 
   let a := eval simpl in a in
   exact a.

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

Definition sqrt_ff (t: type) : floatfunc  [ t ] t (Rle 0) R_sqrt.sqrt.
apply (Build_floatfunc  [ t ] t _ _ (BSQRT t)  (default_rel t) (default_abs t)).
intros x ? ?.
unfold BSQRT, UNOP .
destruct (Binary.Bsqrt_correct (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (sqrt_nan t)
                      BinarySingleNaN.mode_NE x) as [? [??]].
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
rewrite H1; clear H1.
split.
-
destruct x; try destruct s; simpl in H; try discriminate; auto.
exfalso. clear - H0.
simpl in H0.
unfold Defs.F2R in H0.
simpl in H0.
unfold IZR in H0. rewrite Raux.bpow_powerRZ in H0.
simpl in H0.
Search powerRZ.
pose proof (powerRZ_lt 2 e ltac:(Lra.lra)).
pose proof (Pos2Nat.is_pos m).
rewrite <- INR_IPR in H0.
assert (0 < INR (Pos.to_nat m) * powerRZ 2 e)%R.
apply Rmult_lt_0_compat; auto.
change 0%R with (INR 0).
apply lt_INR. auto.
Lra.lra.
-
apply generic_round_property.
Defined.

Definition abs_ff (t: type) : floatfunc  [ t ] t (fun _ => True) Rabs.
apply (Build_floatfunc  [ t ] t _ _ (BABS t)  0%R 0%R).
intros x ? ?.
unfold BABS, UNOP .
pose proof (Binary.B2R_Babs (fprec t) (femax t)  (FPCore.abs_nan t)
                       x).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
rewrite H1; clear H1.
split.
rewrite Binary.is_finite_Babs; auto.
exists 0%R, 0%R. 
split; simpl;
rewrite Rabs_R0;
try match goal with |- context [Raux.bpow ?a ?b] =>
  pose proof (Raux.bpow_gt_0 a b)
end;
Lra.nra.
Defined.

Lemma trunc_ff_aux: forall t (x: ftype t),
  Binary.is_finite (fprec t) (femax t) x = true ->
  (Rabs (FT2R x) < Raux.bpow Zaux.radix2 (femax t - 1))%R ->
  (Rabs  (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (IZR (Binary.Btrunc (fprec t) (femax t) x)))
           <  Raux.bpow Zaux.radix2 (femax t) )%R.
Admitted. (* might be true *)


Definition trunc_ff (t: type) : floatfunc  [ t ] t 
      (fun x => Rlt (Rabs x) (Raux.bpow Zaux.radix2 (femax t - 1))) 
           (Generic_fmt.round Zaux.radix2 (FIX.FIX_exp 0) Raux.Ztrunc).
apply (Build_floatfunc  [ t ] t _ _ 
              (fun x => IEEE754_extra.BofZ (fprec t) (femax t)  
                           (fprec_gt_0 t) (fprec_lt_femax t)
                      (Binary.Btrunc (fprec t) (femax t) x))
                      (default_rel t) (default_abs t)).
intros x ? ?.
pose proof (Binary.Btrunc_correct (fprec t) (femax t) (fprec_lt_femax t) x).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
rewrite <- H1; clear H1.
pose proof IEEE754_extra.BofZ_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
            (Binary.Btrunc (fprec t) (femax t) x).
match type of H1 with if Raux.Rlt_bool ?a ?b then _ else _ => 
  destruct (Raux.Rlt_bool_spec a b)
end.
-
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
destruct H1 as [? [? ?]].
rewrite H1.
split; [ auto | ].
apply generic_round_property.
-
exfalso; clear - H H0 H2.
pose proof trunc_ff_aux t x H.
Lra.lra.
Defined.

Definition fma_no_overflow (t: type) (x y z: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.

Definition fma_ff (t: type) : floatfunc  [ t;t;t ] t (fma_no_overflow t) (fun x y z => x*y+z)%R.
apply (Build_floatfunc [t;t;t] t _ _ 
          (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
               (fma_nan t) BinarySingleNaN.mode_NE)
           (default_rel t) (default_abs t)).
intros x ? y ? z ? ?.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z H H0 H1).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H3.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y + FT2R z)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H4.
-
destruct H3 as [? [? ?]].
rewrite H3.
split; auto.
apply generic_round_property.
-
red in H2.
Lra.lra.
Defined.

Definition ldexp_spec' (t: type) :=
   WITH x : ftype t, i: Z
   PRE [ reflect_to_ctype t , tint ]
       PROP (Int.min_signed <= i <= Int.max_signed)
       PARAMS (reflect_to_val t x; Vint (Int.repr i))
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t 
                       ((Binary.Bldexp (fprec t) (femax t) 
                           (fprec_gt_0 t) (fprec_lt_femax t) BinarySingleNaN.mode_NE x i)))
       SEP ().

Definition frexp_spec' (t: type) :=
   WITH x : ftype t, p: val, sh: share
   PRE [ reflect_to_ctype t , tptr tint ]
       PROP (writable_share sh)
       PARAMS (reflect_to_val t x; p)
       SEP (@data_at_ emptyCS sh tint p)
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t 
                        (fst (Binary.Bfrexp (fprec t) (femax t)  (fprec_gt_0 t) x)))
       SEP (@data_at emptyCS sh tint (Vint (Int.repr 
                         (snd (Binary.Bfrexp (fprec t) (femax t)  (fprec_gt_0 t) x))))
                         p).

Definition bogus_nan t := 
   (* This is probably not the right NaN to use, wherever you see it used *)
   FMA_NAN.quiet_nan t (FMA_NAN.default_nan t). 

Definition nextafter (t: type) (x y: ftype t) : ftype t := 
 match Binary.Bcompare (fprec t) (femax t) x y with
  | Some Lt => Binary.Bsucc (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) x
  | Some Eq => y
  | Some Gt => Binary.Bpred (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) x
  | None => proj1_sig (bogus_nan t)
  end.

Definition nextafter_spec' (t: type) :=
   WITH x : ftype t, y: ftype t
   PRE [ reflect_to_ctype t , reflect_to_ctype t ]
       PROP ()
       PARAMS (reflect_to_val t x; reflect_to_val t y)
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t (nextafter t x y))
       SEP ().

Definition copysign (t: type) (x y: ftype t) :=
 match x with
 | Binary.B754_zero _ _ _ => Binary.B754_zero _ _ (Binary.Bsign _ _ y)
 | Binary.B754_infinity _ _ _ => Binary.B754_infinity _ _ (Binary.Bsign _ _ y)
 | Binary.B754_finite _ _ _ m e H => Binary.B754_finite _ _ (Binary.Bsign _ _ y) m e H
 | Binary.B754_nan _ _ _ pl H => Binary.B754_nan _ _ (Binary.Bsign _ _ y) pl H
end.

Definition copysign_spec' (t: type) :=
   WITH x : ftype t, y : ftype t
   PRE [ reflect_to_ctype t , reflect_to_ctype t ]
       PROP ()
       PARAMS (reflect_to_val t x; reflect_to_val t y) 
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
       RETURN (reflect_to_val t (copysign t x y))
       SEP ().

Definition nan_spec' (t: type) :=
   WITH p: val
   PRE [ tptr tschar ]
       PROP ()
       PARAMS (p) 
       SEP ()
    POST [ reflect_to_ctype t ]
       PROP ()
        (* here it _is_ actually permissible to use bogus_nan *)
       RETURN (reflect_to_val t (proj1_sig (bogus_nan t)))
       SEP ().

Definition arccosh (x: R) := Rabs (Rpower.arcsinh (sqrt (Rsqr x - 1)))%R.
Definition arctanh (x: R) := (/2 * ln ((1+x)/(1-x)) )%R.

Fixpoint always_true (args: list type) : function_type (map RR args) Prop :=
 match args with
 | nil => True
 | _ :: args' => fun _ => always_true args'
 end.

Parameter c_function: forall (i: ident) (args: list type) (res: type) (f: function_type (map RR args) R),
   {ff: function_type (map ftype' args) (ftype res) 
   | acc_prop args res (IZR (1 + 2 * GNU_error i) * default_rel res)%R (default_abs res)
                   (always_true args) f ff}.

Ltac floatfunc' i args res f :=
 let r := constr:(1 + 2 * GNU_error i) in
 let r := eval compute in r in 
 let rel := constr:((IZR r * default_rel res)%R) in
 let abs := constr:(default_abs res) in
 let cf := constr:(c_function i args res f) in 
 exact (Build_floatfunc args res (always_true args) f (proj1_sig cf) rel abs (proj2_sig cf)).



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

Definition acos_spec := DECLARE _acos ltac:(floatspec MF.acos).
Definition acosf_spec := DECLARE _acosf ltac:(floatspec MF.acosf).
Definition acosh_spec := DECLARE _acosh ltac:(floatspec MF.acosh).
Definition acoshf_spec := DECLARE _acoshf ltac:(floatspec MF.acoshf).
Definition asin_spec := DECLARE _asin ltac:(floatspec MF.asin).
Definition asinf_spec := DECLARE _asinf ltac:(floatspec MF.asinf).
Definition asinh_spec := DECLARE _asinh ltac:(floatspec MF.asinh).
Definition asinhf_spec := DECLARE _asinhf ltac:(floatspec MF.asinhf).
Definition atan_spec := DECLARE _atan ltac:(floatspec MF.atan).
Definition atanf_spec := DECLARE _atanf ltac:(floatspec MF.atanf).
Definition atan2_spec := DECLARE _atan2 ltac:(floatspec MF.atan2).
Definition atan2f_spec := DECLARE _atan2f ltac:(floatspec MF.atan2f).
Definition atanh_spec := DECLARE _atanh ltac:(floatspec MF.atanh).
Definition atanhf_spec := DECLARE _atanhf ltac:(floatspec MF.atanhf).
Definition cbrt_spec := DECLARE _cbrt ltac:(floatspec MF.cbrt).
Definition cbrtf_spec := DECLARE _cbrtf ltac:(floatspec MF.cbrtf).
Definition copysign_spec := DECLARE _copysign ltac:(reduce1 (copysign_spec' Tdouble)).
Definition copysignf_spec := DECLARE _copysignf ltac:(reduce1 (copysign_spec' Tsingle)).
Definition cos_spec := DECLARE _cos ltac:(floatspec MF.cos).
Definition cosf_spec := DECLARE _cosf ltac:(floatspec MF.cosf).
Definition cosh_spec := DECLARE _cosh ltac:(floatspec MF.cosh).
Definition coshf_spec := DECLARE _coshf ltac:(floatspec MF.coshf).
Definition exp_spec := DECLARE _exp ltac:(floatspec MF.exp).
Definition expf_spec := DECLARE _expf ltac:(floatspec MF.expf).
Definition exp2_spec := DECLARE _exp2 ltac:(floatspec MF.exp2).
Definition exp2f_spec := DECLARE _exp2f ltac:(floatspec MF.exp2f).
Definition expm1_spec := DECLARE _expm1 ltac:(floatspec MF.expm1).
Definition expm1f_spec := DECLARE _expm1f ltac:(floatspec MF.expm1f).
Definition fabs_spec := DECLARE _fabs ltac:(floatspec (abs_ff Tdouble)).
Definition fabsf_spec := DECLARE _fabsf ltac:(floatspec (abs_ff Tsingle)).
Definition pow_spec := DECLARE _pow ltac:(floatspec MF.pow).
Definition powf_spec := DECLARE _powf ltac:(floatspec MF.powf).
Definition sqrt_spec := DECLARE _sqrt ltac:(floatspec (sqrt_ff Tdouble)).
Definition sqrtf_spec := DECLARE _sqrtf ltac:(floatspec (sqrt_ff Tsingle)).
Definition sin_spec := DECLARE _sin ltac:(floatspec MF.sin).
Definition sinf_spec := DECLARE _sinf ltac:(floatspec MF.sinf).
Definition sinh_spec := DECLARE _sinh ltac:(floatspec MF.sinh).
Definition sinhf_spec := DECLARE _sinhf ltac:(floatspec MF.sinhf).
Definition tan_spec := DECLARE _tan ltac:(floatspec MF.tan).
Definition tanf_spec := DECLARE _tanf ltac:(floatspec MF.tanf).
Definition tanh_spec := DECLARE _tanh ltac:(floatspec MF.tanh).
Definition tanhf_spec := DECLARE _tanhf ltac:(floatspec MF.tanhf).

Definition fma_spec := DECLARE _fma ltac:(floatspec (fma_ff Tdouble)).
Definition fmaf_spec := DECLARE _fmaf ltac:(floatspec (fma_ff Tsingle)).
Definition frexp_spec := DECLARE _frexp ltac:(reduce1 (frexp_spec' Tdouble)).
Definition frexpf_spec := DECLARE _frexpf ltac:(reduce1 (frexp_spec' Tsingle)).
Definition ldexp_spec := DECLARE _ldexp ltac:(reduce1 (ldexp_spec' Tdouble)).
Definition ldexpf_spec := DECLARE _ldexpf ltac:(reduce1 (ldexp_spec' Tsingle)).
Definition nan_spec := DECLARE _nan ltac:(reduce1 (nan_spec' Tdouble)).
Definition nanf_spec := DECLARE _nanf ltac:(reduce1 (nan_spec' Tsingle)).
Definition nextafter_spec := DECLARE _nextafter ltac:(reduce1 (nextafter_spec' Tdouble)).
Definition nextafterf_spec := DECLARE _nextafterf ltac:(reduce1 (nextafter_spec' Tsingle)).
Definition trunc_spec := DECLARE _trunc ltac:(floatspec (trunc_ff Tdouble)).
Definition truncf_spec := DECLARE _truncf ltac:(floatspec (trunc_ff Tsingle)).

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

Local Remark sqrt_accurate: forall x, 
  (0 <= FT2R x ->
   Binary.is_finite (fprec Tdouble) (femax Tdouble) x = true ->
   Binary.is_finite _ _ (ff_func (sqrt_ff Tdouble) x) = true /\
   exists delta, exists epsilon,
   Rabs delta <= default_rel Tdouble /\
   Rabs epsilon <= default_abs Tdouble /\ 
   exists x', nonneg x' = FT2R x /\
   FT2R (ff_func (sqrt_ff Tdouble) x) = sqrt x' * (1+delta) + epsilon)%R.
Proof.
intros.
destruct (ff_acc (sqrt_ff Tdouble) x H0 H) as [FIN [delta [epsilon [? [? ?]]]]].
split; auto.
exists delta, epsilon.
split3; auto.
destruct (Rcase_abs (FT2R x)). Lra.lra.
exists {| nonneg:= FT2R x; cond_nonneg := H |}.
split; auto.
Qed.



