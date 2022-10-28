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
exact (forall z: ftype a, 
            acc_prop r result rel abs (precond (FT2R z)) (rf (FT2R z)) (f z)).
Defined.

Record floatfunc (args: list FPCore.type) (result: FPCore.type) 
     (precond: function_type (map RR args) Prop)
     (realfunc: function_type (map RR args) R)
     (rel abs: R) :=
 {ff_func: function_type (map ftype' args) (ftype' result);
  ff_acc: acc_prop args result rel abs precond realfunc ff_func
 }.

Arguments ff_func [args result precond realfunc rel abs].
Arguments ff_acc [args result precond realfunc rel abs].

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
  forall {precond rfunc rel abs} 
       (ff: floatfunc args result precond rfunc rel abs), funspec.
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

Locate sin.

Module Type MathFunctions.

Definition Rsqrt' (x: R) : R :=
match Rle_dec 0 x with
| left a => Rsqrt {| nonneg := x; cond_nonneg := a |}
| right b => 0%R
end.

Parameter sqrt : floatfunc [ Tdouble ] Tdouble (Rle 0) Rsqrt' (default_rel Tdouble) (default_abs Tdouble).
Parameter sqrtf : floatfunc [ Tsingle ] Tsingle  (Rle 0)  Rsqrt' (default_rel Tsingle) (default_abs Tsingle).

Parameter sin: floatfunc [Tdouble] Tdouble (fun _ => True) Rtrigo_def.sin (2*default_rel Tdouble) (3*default_abs Tdouble).
Parameter sinf: floatfunc [Tsingle] Tsingle (fun _ => True) Rtrigo_def.sin (default_rel Tsingle) (default_abs Tsingle).

Parameter fma: floatfunc [Tdouble;Tdouble;Tdouble] Tdouble (fun _ _ _ =>True) 
           (fun x y z => x*y+z)%R (default_rel Tdouble) (default_abs Tdouble).
Parameter fmaf: floatfunc [Tsingle;Tsingle;Tsingle] Tsingle (fun _ _ _ =>True) 
           (fun x y z => x*y+z)%R (default_rel Tsingle) (default_abs Tsingle).

End MathFunctions.

Declare Module MF: MathFunctions.

Definition sqrt_spec := DECLARE _sqrt ltac:(floatspec MF.sqrt).
Definition sqrtf_spec := DECLARE _sqrtf ltac:(floatspec MF.sqrtf).
Definition sin_spec := DECLARE _sin ltac:(floatspec MF.sin).
Definition sinf_spec := DECLARE _sinf ltac:(floatspec MF.sinf).
Definition fma_spec := DECLARE _fma ltac:(floatspec MF.fma).
Definition fmaf_spec := DECLARE _fmaf ltac:(floatspec MF.fmaf).

Definition MathASI:funspecs := [ 
  sqrt_spec; sqrtf_spec; sin_spec; sinf_spec;
  fma_spec; fmaf_spec 
].

Remark sqrt_accurate: forall x, 
  (0 <= FT2R x  ->
  exists delta, exists epsilon,
   Rabs delta <= default_rel Tdouble /\
   Rabs epsilon <= default_abs Tdouble /\ 
   exists x', nonneg x' = FT2R x /\
   FT2R (ff_func MF.sqrt x) = Rsqrt x' * (1+delta) + epsilon)%R.
Proof.
intros.
destruct (ff_acc MF.sqrt _ H) as [delta [epsilon ?]].
exists delta, epsilon.
destruct H0 as [? [? ?]].
split3; auto.
exists {| nonneg:= FT2R x; cond_nonneg := H |}.
split; auto.
rewrite H2.
unfold MF.Rsqrt'.
destruct (Rle_dec _ _); try contradiction.
repeat f_equal.
apply proof_irr.
Qed.

