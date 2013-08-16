Require Import floyd.proofauto.
Require Import progs.sumarray.

Local Open Scope logic.

Definition add_elem (f: Z -> int) (i: Z) := Int.add (f i).

Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a0: val, sh : share, contents : Z -> int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed)
          LOCAL (`(eq a0) (eval_id _a);
                      `(eq (Vint (Int.repr size))) (eval_id _n);
                      `isptr (eval_id _a))
          SEP (`(array_at tint sh contents 0 size) (eval_id _a))
  POST [ tint ]  
        local (`(eq (Vint (fold_range (add_elem contents) Int.zero 0 size))) retval)
                 && `(array_at tint sh contents 0 size a0).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    sumarray_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Definition sumarray_Inv a0 sh contents size := 
 EX i: Z,
  (PROP  (0 <= i <= size)
   LOCAL  (`(eq a0) (eval_id _a);   `(eq (Vint (Int.repr i))) (eval_id _i);
                `(eq (Vint (Int.repr size))) (eval_id _n);
           `isptr (eval_id _a); 
    `(eq (Vint (fold_range (add_elem contents) Int.zero 0 i))) (eval_id _s))
   SEP (`(array_at tint sh contents 0 size) (eval_id _a))).

Lemma split3_array_at:
  forall i ty sh contents lo hi v,
       lo <= i < hi ->
     array_at ty sh contents lo hi v =
     array_at ty sh contents lo i v *
     typed_mapsto sh ty (add_ptr_int ty v i) (contents i) *
     array_at ty sh contents (Zsucc i) hi v.
Proof.
 intros.
Admitted.

Lemma lift_split3_array_at:
  forall i ty sh contents lo hi,
       lo <= i < hi ->
     array_at ty sh contents lo hi =
     array_at ty sh contents lo i *
     (fun v => typed_mapsto sh ty (add_ptr_int ty v i) (contents i)) *
     array_at ty sh contents (Zsucc i) hi.
Proof.
 intros. extensionality v. simpl. apply split3_array_at. auto.
Qed.

Lemma body_sumarray: semax_body Vprog Gtot f_sumarray sumarray_spec.
Proof.
start_function.
name a _a.
name n _n.
name i _i.
name s _s.
name x _x.
forward.  (* i = 0; *) 
forward.  (* s = 0; *)
forward_while (sumarray_Inv a0 sh contents size)
    (PROP() LOCAL (`(eq a0) (eval_id _a);   
     `(eq (Vint (fold_range (add_elem contents) Int.zero 0 size))) (eval_id _s))
     SEP (`(array_at tint sh contents 0 size) (eval_id _a))).
(* Prove that current precondition implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with 0.
entailer.
  apply andp_right.
  apply prop_right; repeat split; auto; omega.
  cancel.
(* Prove that loop invariant implies typechecking condition *)
entailer.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer.
 apply andp_right.
   apply prop_right. f_equal. omega.
   cancel.
(* Prove that loop body preserves invariant *)
simpl.
forward_with new_load_tac.  (* x = a[i]; *)
entailer.
repeat split; auto; rewrite Int.signed_repr by repable_signed; omega.
forward. (* s += x; *)
forward. (* i++; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with (Zsucc i0).
entailer.
 apply andp_right; [apply prop_right | cancel].
 inv H2. simpl in H3. inv H3.
 rewrite Int.add_signed.
repeat rewrite Int.signed_repr by repable_signed.
 repeat split; auto; try omega.
 admit.  (* need simple lemma fold_range_split *)
(* After the loop *)
forward.  (* return s; *)
entailer.
Qed.

Definition four_contents (z: Z) : int := Int.repr (Zsucc z).

Lemma  setup_globals:
  forall u rho,  tc_environ (func_tycontext f_main Vprog Gtot) rho ->
     main_pre prog u rho
      |-- array_at tint Ews four_contents 0 4
                (eval_var _four (tarray tint 4) rho).
Proof.
 unfold main_pre.
 intros _ rho; normalize.
 simpl.
 destruct (globvar_eval_var _ _ _four _ H (eq_refl _) (eq_refl _))
  as [b [z [H97 H99]]]. simpl in *.
 unfold tarray.
 rewrite H97.
 unfold globvar2pred. simpl. rewrite H99. simpl.
 unfold array_at, rangespec; simpl.
 unfold array_at.
 repeat  simpl_typed_mapsto.
 rewrite sepcon_emp.
 unfold four_contents. simpl.
 change (umapsto  (Share.splice extern_retainer Tsh) (Tint I32 Unsigned noattr))
       with (umapsto Ews tint).
 replace (Vptr b z) with (Vptr b (Int.add z (Int.repr 0)))
    by (rewrite Int.add_zero; auto).
repeat (apply sepcon_derives;
 [unfold mapsto; apply andp_right; [apply prop_right; reflexivity | ];
 unfold add_ptr_int, eval_binop; simpl;
 repeat rewrite Int.add_assoc;
 apply derives_refl
 | ]).
auto.
Qed.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name s _s.
apply (remember_value (eval_var _four (tarray tint 4))); intro a0.
forward.  (*  r = sumarray(four,4); *)
instantiate (1:= (a0,Ews,four_contents,4)) in (Value of witness).
instantiate (1:=nil) in (Value of Frame).
unfold Frame.
 entailer. apply andp_right.
 apply prop_right; repeat split; auto; try solve [ compute; congruence].
 eapply eval_var_isptr; eauto.
 apply setup_globals; auto.
 try (auto with typeclass_instances). (* remove this line when it's no longer needed! *)
 auto with closed.
 forward. (* return s; *)
 entailer.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons; [ reflexivity | apply body_sumarray | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

