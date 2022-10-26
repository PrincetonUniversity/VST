Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import math.
Require Import spec_math.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Parameter body_sqrt:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "sqrt" (mksignature [AST.Tfloat] AST.Tfloat cc_default))
    (snd (sqrt_spec)).

Parameter body_sqrtf:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "sqrtf" (mksignature [AST.Tsingle] AST.Tsingle cc_default))
    (snd (sqrtf_spec)).

Parameter body_sin:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "sin" (mksignature [AST.Tfloat] AST.Tfloat cc_default))
    (snd (sin_spec)).

Parameter body_sinf:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "sinf" (mksignature [AST.Tsingle] AST.Tsingle cc_default))
    (snd (sinf_spec)).

Parameter body_fma:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "fma" (mksignature [AST.Tfloat;AST.Tfloat;AST.Tfloat] AST.Tfloat cc_default))
    (snd (fma_spec)).

Parameter body_fmaf:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "fmaf" (mksignature [AST.Tsingle;AST.Tsingle;AST.Tsingle] AST.Tsingle cc_default))
    (snd (fmaf_spec)).

Definition math_placeholder_spec :=
 DECLARE _math_placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition Math_imported_specs:funspecs :=  nil.

Definition Math_internal_specs: funspecs := math_placeholder_spec::MathASI.

Definition MathVprog : varspecs. mk_varspecs prog. Defined.
Definition MathGprog: funspecs := Math_imported_specs ++ Math_internal_specs.

Lemma Math_Init: VSU_initializer prog emp.
Proof. InitGPred_tac. apply derives_refl. Qed.

Lemma body_placeholder: semax_body MathVprog MathGprog f_math_placeholder math_placeholder_spec.
Proof.
start_function.
contradiction.
Qed.

Definition Math_E : funspecs := MathASI.

Definition is_float_val v :=
 match v with Vfloat _ => true | Vsingle _ => true | _ => false end.

Lemma RETURN_tc_option_val_float:
 forall P v R t ret gx,
  is_float_val v = true ->
  (PROPx P (LOCALx (temp ret_temp v :: nil) (SEPx R)))
         (make_ext_rval gx (rettype_of_type t) ret)
  && !! Builtins0.val_opt_has_rettype ret (rettype_of_type t)
  |-- prop (tc_option_val t ret).
Proof.
intros.
Intros.
cbv [PROPx LOCALx SEPx local liftx lift lift1 lift_curry lift_uncurry_open fold_right].
simpl. 
apply andp_left2.
apply andp_left1.
apply prop_derives.
intros [[? _] _].
hnf in H0,H1.
subst v.
(*hnf in H2.*)
unfold eval_id, make_ext_rval in *.
unfold tc_option_val.
destruct (type_eq t Tvoid).
subst; auto.
assert (match ret with
       | Some v => tc_val t v
       | None => False
       end); [ | destruct t; try contradiction; auto].
assert (match rettype_of_type t with
               | AST.Tvoid =>
                   mkEnviron gx (Map.empty (block * type))
                     (Map.empty val)
               | _ =>
                   match ret with
                   | Some v' =>
                       mkEnviron gx (Map.empty (block * type))
                         (Map.set 1 v' (Map.empty val))
                   | None =>
                       mkEnviron gx (Map.empty (block * type))
                         (Map.empty val)
                   end
               end = match ret with
                   | Some v' =>
                       mkEnviron gx (Map.empty (block * type))
                         (Map.set 1 v' (Map.empty val))
                   | None =>
                       mkEnviron gx (Map.empty (block * type))
                         (Map.empty val)
                   end)
  by (destruct (rettype_of_type t); auto; discriminate H).
rewrite H1 in *; clear H1.
destruct ret; [ | discriminate H].
simpl in H.
hnf in H0.
destruct t; try destruct i; try destruct s; try destruct f; simpl in H0; try contradiction;
destruct v; try contradiction; try discriminate H; hnf in H; auto.
Qed.


Definition MathVSU: @VSU NullExtension.Espec
        Math_E Math_imported_specs ltac:(QPprog prog) MathASI emp.
  Proof. 
    mkVSU prog Math_internal_specs. 
    - solve_SF_internal body_placeholder.
    - solve_SF_external (@body_sqrt NullExtension.Espec).
           apply RETURN_tc_option_val_float; reflexivity.
    - solve_SF_external (@body_sqrtf NullExtension.Espec).
           apply RETURN_tc_option_val_float; reflexivity.
    - solve_SF_external (@body_sin NullExtension.Espec).
           apply RETURN_tc_option_val_float; reflexivity.
    - solve_SF_external (@body_sinf NullExtension.Espec).
           apply RETURN_tc_option_val_float; reflexivity.
    - solve_SF_external (@body_fma NullExtension.Espec).
           apply RETURN_tc_option_val_float; reflexivity.
    - solve_SF_external (@body_fmaf NullExtension.Espec).
           apply RETURN_tc_option_val_float; reflexivity.
Qed.

