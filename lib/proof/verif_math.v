Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.math_extern.
Require Import VSTlib.spec_math.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.

Definition math_placeholder_spec : ident * @funspec Σ :=
 DECLARE _math_placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition Math_imported_specs: @funspecs Σ :=  nil.

Definition Math_internal_specs: funspecs := math_placeholder_spec::MathASI.

Definition MathVprog : varspecs. mk_varspecs prog. Defined.
Definition MathGprog: funspecs := Math_imported_specs ++ Math_internal_specs.


Lemma Math_Init: VSU_initializer prog (id (fun gv => emp)).
Proof.
intros ? ?.
eapply InitGPred_process_globvars; auto.
Qed.

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
  (PROPx (Σ:=Σ) P (LOCALx (temp ret_temp v :: nil) (SEPx R)))
         (make_ext_rval gx (rettype_of_type t) ret)
  && !! Builtins0.val_opt_has_rettype ret (rettype_of_type t)
  |-- !! (tc_option_val t ret).
Proof.
intros.
Intros.
cbv [PROPx LOCALx SEPx local liftx lift lift1 lift_curry lift_uncurry_open fold_right].
rewrite !monPred_at_and.
apply andp_left2.
apply andp_left1.
simpl.
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
               | Xvoid =>
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

 Ltac admit_external := 
 split3;
     [ reflexivity
     | reflexivity
     | split3;
        [ reflexivity
        | reflexivity
        | split3;
           [ left; trivial
           | clear; intros ? ? ?; cbv [ofe_mor_car]; 
             try (solve [ entailer ! ]);
              repeat
               match goal with
               | |- monPred_at (let (y, z) := ?x in _) _ && _ |-- _ =>
                     destruct x as [y z]
               end;
               apply RETURN_tc_option_val_float; reflexivity
           | split; [  | eexists; split; compute; reflexivity ] ] ] ];
     [ admit ].


Definition MathVSU `{Espec: ext_spec OK_ty}:
    VSU Math_E Math_imported_specs ltac:(QPprog prog) MathASI (fun _ => emp).
  Proof.
    mkVSU prog Math_internal_specs;
    [solve_SF_internal body_placeholder | try admit_external .. ].
all: fail.
Admitted.

End GFUNCTORS.
