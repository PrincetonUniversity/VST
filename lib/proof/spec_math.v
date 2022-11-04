Require Import VST.floyd.proofauto.
Require Import math_extern.
Require Import vcfloat.FPCompCert.
Require Import Reals.
Import ListNotations.

Local Open Scope assert.

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
exact (precond -> exists delta epsilon,
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

Definition sqrt_ff (t: type) : floatfunc  [ t ] t (fun _ => True) R_sqrt.sqrt.
apply (Build_floatfunc  [ t ] t _ _ (BSQRT t)  (default_rel t) (default_abs t)).
intros x ? ?.
unfold BSQRT, UNOP .
destruct (Binary.Bsqrt_correct (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (sqrt_nan t)
                      BinarySingleNaN.mode_NE x) as [? _].
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
rewrite H1; clear H1.
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
apply generic_round_property.
-
elimtype False; clear - H H0 H2.
pose proof trunc_ff_aux t x H.
Lra.lra.
Defined.

(* BEGIN definitions adapted from [the open-source part of] CompCert  *)

(** Transform a Nan payload to a quiet Nan payload. *)

Definition quiet_nan_payload (t: type) (p: positive) :=
  Z.to_pos (Zbits.P_mod_two_p (Pos.lor p ((Zaux.iter_nat xO (Z.to_nat (fprec t - 2)) 1%positive))) (Z.to_nat (fprec t - 1))).

Lemma quiet_nan_proof (t: type): forall p, Binary.nan_pl (fprec t) (quiet_nan_payload t p) = true.
Proof. 
intros.
pose proof (fprec_gt_one t).
 apply normalized_nan; auto; lia.
Qed.

Definition quiet_nan (t: type) (sp: bool * positive) : {x : ftype t | Binary.is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (Binary.B754_nan (fprec t) (femax t) s (quiet_nan_payload t p) (quiet_nan_proof t p)) (eq_refl true).

Definition default_nan (t: type) := (fst Archi.default_nan_64, iter_nat (Z.to_nat (fprec t - 2)) _ xO xH).

Inductive NAN_SCHEME := NAN_SCHEME_ARM | NAN_SCHEME_X86 | NAN_SCHEME_RISCV.

Definition the_nan_scheme : NAN_SCHEME.
try (unify Archi.choose_nan_64 Archi.default_nan_64; exact NAN_SCHEME_RISCV);
try (unify Archi.choose_nan_64 (fun l => match l with nil => Archi.default_nan_64 | n::_ => n end);
      exact NAN_SCHEME_X86);
try (let p := constr:(Archi.choose_nan_64) in
      let p := eval red in p in
      match p with _ (fun p => negb (Pos.testbit p 51)) _ => idtac end;
      exact NAN_SCHEME_ARM).
Defined.

Definition ARMchoose_nan (is_signaling: positive -> bool) 
                      (default: bool * positive)
                      (l0: list (bool * positive)) : bool * positive :=
  let fix choose_snan (l1: list (bool * positive)) :=
    match l1 with
    | nil =>
        match l0 with nil => default | n :: _ => n end
    | ((s, p) as n) :: l1 =>
        if is_signaling p then n else choose_snan l1
    end
  in choose_snan l0.

Definition choose_nan (t: type) : list (bool * positive) -> bool * positive :=
 match the_nan_scheme with
 | NAN_SCHEME_RISCV => fun _ => default_nan t
 | NAN_SCHEME_X86 => fun l => match l with nil => default_nan t | n :: _ => n end
 | NAN_SCHEME_ARM => ARMchoose_nan (fun p => negb (Pos.testbit p (Z.to_N (fprec t - 2))))
                                          (default_nan t)
 end.

Definition cons_pl {t: type} (x : ftype t) (l : list (bool * positive)) :=
match x with
| Binary.B754_nan _ _ s p _ => (s, p) :: l
| _ => l
end.

Definition fma_nan_1 (t: type) (x y z: ftype t) : {x : ftype t | @Binary.is_nan (fprec t) (femax t) x = true} :=
  let '(a, b, c) := Archi.fma_order x y z in
  quiet_nan t (choose_nan t (cons_pl a (cons_pl b (cons_pl c [])))).

Definition fma_nan (t: type) (x y z: ftype t) : {x : ftype t | Binary.is_nan _ _ x = true} :=
  match x, y with
  | Binary.B754_infinity _ _ _, Binary.B754_zero _ _ _ | Binary.B754_zero _ _ _, Binary.B754_infinity _ _ _ =>
      if Archi.fma_invalid_mul_is_nan
      then quiet_nan t (choose_nan t (default_nan t :: cons_pl z []))
      else fma_nan_1 t x y z
  | _, _ =>
      fma_nan_1 t x y z
  end.
(* END definitions adapted from [the open-source part of] CompCert  *)

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
destruct H3 as [? _].
rewrite H3.
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

Definition nextafter (t: type) (x y: ftype t) : ftype t := 
 match Binary.Bcompare (fprec t) (femax t) x y with
  | Some Lt => Binary.Bsucc (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) x
  | Some Eq => y
  | Some Gt => Binary.Bpred (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) x
  | None => proj1_sig (quiet_nan t (default_nan t))  (* this is probably the wrong NaN *)
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
       RETURN (reflect_to_val t (proj1_sig (quiet_nan t (default_nan t))))
       SEP ().

Definition arccosh (x: R) := Rabs (Rpower.arcsinh (sqrt (Rsqr x - 1)))%R.
Definition arctanh (x: R) := (/2 * ln ((1+x)/(1-x)) )%R.

Module Type MathFunctions.
Parameter acos: floatfunc [Tdouble] Tdouble (fun _ => True) Ratan.acos. 
Parameter acosf: floatfunc [Tsingle] Tsingle (fun _ => True) Ratan.acos.
Parameter acosh: floatfunc [Tdouble] Tdouble (fun _ => True) arccosh.
Parameter acoshf: floatfunc [Tsingle] Tsingle (fun _ => True) arccosh.
Parameter asin: floatfunc [Tdouble] Tdouble (fun _ => True) Ratan.asin.
Parameter asinf: floatfunc [Tsingle] Tsingle (fun _ => True) Ratan.asin.
Parameter asinh: floatfunc [Tdouble] Tdouble (fun _ => True) Rpower.arcsinh.
Parameter asinhf: floatfunc [Tsingle] Tsingle (fun _ => True) Rpower.arcsinh.
Parameter atan: floatfunc [Tdouble] Tdouble (fun _ => True) Ratan.atan. 
Parameter atanf: floatfunc [Tsingle] Tsingle (fun _ => True) Ratan.atan.
Parameter atan2: floatfunc [Tdouble;Tdouble] Tdouble (fun _ _ => True) (fun y x => Ratan.atan(y/x))%R. 
Parameter atan2f: floatfunc [Tsingle;Tsingle] Tsingle (fun _ _ => True) (fun y x => Ratan.atan(y/x))%R. 
Parameter atanh: floatfunc [Tdouble] Tdouble (fun _ => True) arctanh.
Parameter atanhf: floatfunc [Tsingle] Tsingle (fun _ => True) arctanh.
Parameter cbrt: floatfunc [Tdouble] Tdouble (fun _ => True) (fun x => Rpower x (/3))%R.
Parameter cbrtf: floatfunc [Tsingle] Tsingle (fun _ => True) (fun x => Rpower x (/3))%R.
Parameter cos: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.cos. 
Parameter cosf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.cos.
Parameter cosh: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.cosh.
Parameter coshf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.cosh.
Parameter exp:  floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.exp.
Parameter expf:  floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.exp.
Parameter exp2:  floatfunc [Tdouble] Tdouble (fun _ => True) (Rpower 2%R).
Parameter exp2f:  floatfunc [Tsingle] Tsingle (fun _ => True)  (Rpower 2%R).
Parameter expm1:  floatfunc [Tdouble] Tdouble (fun _ => True) (fun x => Rtrigo_def.exp x - 1)%R.
Parameter expm1f:  floatfunc [Tsingle] Tsingle (fun _ => True) (fun x => Rtrigo_def.exp x - 1)%R.
Parameter pow: floatfunc [Tdouble;Tdouble] Tdouble (fun _ _ => True) Rpower. 
Parameter powf: floatfunc [Tsingle;Tsingle] Tsingle (fun _ _ => True) Rpower. 

Parameter sin: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.sin.
Parameter sinf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.sin.
Parameter sinh: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.sinh.
Parameter sinhf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.sinh.
Parameter tan: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo1.tan.
Parameter tanf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo1.tan.
Parameter tanh: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.tanh.
Parameter tanhf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.tanh.

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
   exists delta, exists epsilon,
   Rabs delta <= default_rel Tdouble /\
   Rabs epsilon <= default_abs Tdouble /\ 
   exists x', nonneg x' = FT2R x /\
   FT2R (ff_func (sqrt_ff Tdouble) x) = sqrt x' * (1+delta) + epsilon)%R.
Proof.
intros.
destruct (ff_acc (sqrt_ff Tdouble) x H0 I) as [delta [epsilon [? [? ?]]]].
exists delta, epsilon.
split3; auto.
destruct (Rcase_abs (FT2R x)). Lra.lra.
exists {| nonneg:= FT2R x; cond_nonneg := H |}.
split; auto.
Qed.


