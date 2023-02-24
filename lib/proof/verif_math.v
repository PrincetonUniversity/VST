Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.math_extern.
Require Import VSTlib.spec_math.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

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

Ltac carefully_unroll_Forall := 
match goal with |- Forall _ (_ _ ?L) => 
     let z := constr:(L) in let z := eval hnf in z 
     in lazymatch z with 
         | (_ , _)::_ => change L with z
         | ?u :: ?r => let u' := eval hnf in u in change L with (u'::r)
         | _ => apply Forall_nil
          end
end;
(cbv beta delta [filter_options] fix;
 cbv match;
 match goal with |- context [Maps.PTree.get ?i ?m] =>
    let u := fresh "u" in set (u := Maps.PTree.get i m); hnf in u; subst u; 
    cbv beta zeta match  delta [snd]
 end;
 match goal with |- Forall _ (?hx :: ?tx) => 
    let h := fresh "h" in let t := fresh "t" in 
     set (h := hx); set (t := tx); simple apply Forall_cons; subst h t
 end; 
  [ |  carefully_unroll_Forall]).

Ltac VSU.mkComponent prog ::=
 hnf;
 match goal with |- Component _ _ ?IMPORTS _ _ _ _ =>
     let i := compute_list' IMPORTS in change_no_check IMPORTS with i 
 end;
 test_Component_prog_computed;
 let p := fresh "p" in
 match goal with |- @Component _ _ _ _ ?pp _ _ _ => set (p:=pp) end;
 let HA := fresh "HA" in 
   assert (HA: PTree_samedom cenv_cs ha_env_cs) by repeat constructor;
 let LA := fresh "LA" in 
   assert (LA: PTree_samedom cenv_cs la_env_cs) by repeat constructor;
 let OK := fresh "OK" in
  assert (OK: QPprogram_OK p)
   by (split; [apply compute_list_norepet_e; reflexivity 
           |  apply (QPcompspecs_OK_i HA LA) ]);
 (* Doing the  set(myenv...), instead of before proving the CSeq assertion,
     prevents nontermination in some cases  *)
 pose (myenv:= (QP.prog_comp_env (QPprogram_of_program prog ha_env_cs la_env_cs)));
 assert (CSeq: _ = compspecs_of_QPcomposite_env myenv 
                     (proj2 OK))
   by (apply compspecs_eq_of_QPcomposite_env; reflexivity);
 subst myenv;
 change (QPprogram_of_program prog ha_env_cs la_env_cs) with p in CSeq;
 clear HA LA;
 exists OK;
  [ check_Comp_Imports_Exports
  | apply compute_list_norepet_e; reflexivity || fail "Duplicate funspec among the Externs++Imports"
  | apply compute_list_norepet_e; reflexivity || fail "Duplicate funspec among the Exports"
  | apply compute_list_norepet_e; reflexivity
  | apply forallb_isSomeGfunExternal_e; reflexivity
  | intros; simpl; split; trivial; try solve [lookup_tac]
  | let i := fresh in let H := fresh in 
    intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; reflexivity |]); try contradiction
  | apply prove_G_justified; carefully_unroll_Forall;  try SF_vacuous
  | finishComponent
  | first [ solve [intros; apply derives_refl] | solve [intros; reflexivity] | solve [intros; simpl; cancel] | idtac]
  ].


 Ltac admit_external := 
 split3;
     [ reflexivity
     | reflexivity
     | split3;
        [ reflexivity
        | reflexivity
        | split3;
           [ left; trivial
           | clear; intros ? ? ? ?; try (solve [ entailer ! ]);
              repeat
               match goal with
               | |- (let (y, z) := ?x in _) _ && _ |-- _ =>
                     destruct x as [y z]
               end;
               apply RETURN_tc_option_val_float; reflexivity
           | split; [  | eexists; split; compute; reflexivity ] ] ] ];
     [ admit ].

Definition MathVSU: @VSU NullExtension.Espec
        Math_E Math_imported_specs ltac:(QPprog prog) MathASI emp.
  Proof. 
    mkVSU prog Math_internal_specs; 
    [solve_SF_internal body_placeholder | try admit_external .. ].
all: fail.
Admitted.

