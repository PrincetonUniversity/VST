Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.malloc_lemmas.
Require Import progs.sumarray.

Local Open Scope logic.

Definition add_elem (f: Z -> int) (i: Z) := Int.add (f i).

Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a0: val, sh : share, contents : Z -> int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ] 
          !! (0 <= size <= Int.max_signed) &&
          local (`(eq a0) (eval_id _a)) &&
          local (`(eq (Vint (Int.repr size))) (eval_id _n))   &&
          local (`denote_tc_isptr (eval_id _a)) &&
          `(array_at_range tint sh contents 0 size) (eval_id _a)
  POST [ tint ]  
    local (`(eq (Vint (fold_range (add_elem contents) Int.zero 0 size))) retval) &&
            `(array_at_range tint sh contents 0 size a0).

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
           `denote_tc_isptr (eval_id _a); 
    `(eq (Vint (fold_range (add_elem contents) Int.zero 0 i))) (eval_id _s))
   SEP (`(array_at_range tint sh contents 0 size) (eval_id _a))).

Lemma split3_array_at_range:
  forall i ty sh contents lo hi v,
       lo <= i < hi ->
     array_at_range ty sh contents lo hi v =
     array_at_range ty sh contents lo i v *
     typed_mapsto ty sh 0 (add_ptr_int ty v i) (contents i) *
     array_at_range ty sh contents (Zsucc i) hi v.
Proof.
 intros.
Admitted.

Lemma lift_split3_array_at_range:
  forall i ty sh contents lo hi,
       lo <= i < hi ->
     array_at_range ty sh contents lo hi =
     array_at_range ty sh contents lo i *
     (fun v => typed_mapsto ty sh 0 (add_ptr_int ty v i) (contents i)) *
     array_at_range ty sh contents (Zsucc i) hi.
Proof.
 intros. extensionality v. simpl. apply split3_array_at_range. auto.
Qed.

Lemma body_sumarray: semax_body Vprog Gtot f_sumarray sumarray_spec.
Proof.
start_function. destruct p as [[a0 sh] contents].
name a _a.
name n _n.
name i _i.
name s _s.
name x _x.
repeat rewrite andp_assoc.
normalizex.
forward.  (* i = 0; *) 
forward.  (* s = 0; *)
forward_while (sumarray_Inv a0 sh contents size)
    (PROP() LOCAL (`(eq a0) (eval_id _a);   
     `(eq (Vint (fold_range (add_elem contents) Int.zero 0 size))) (eval_id _s))
     SEP (`(array_at_range tint sh contents 0 size) (eval_id _a))).
(* Prove that current precondition implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with 0.
go_lower. subst. normalize.
 repeat apply andp_right; auto; apply prop_right; auto; omega.
(* Prove that loop invariant implies typechecking condition *)
go_lower.
(* Prove that invariant && not loop-cond implies postcondition *)
go_lower.  subst.
 repeat apply andp_right; try apply prop_right; repeat split; auto.
 f_equal. simpl in H2.
 intcompare H2.
 omega.
(* Prove that loop body preserves invariant *)
apply semax_pre_PQR with
 (PROP (0 <= i0 < size) 
  LOCAL (`(eq a0) (eval_id _a); `(eq (Vint (Int.repr i0))) (eval_id _i);
   `(eq (Vint (Int.repr size))) (eval_id _n); `denote_tc_isptr (eval_id _a);
   `(eq (Vint (fold_range (add_elem contents) Int.zero 0 i0))) (eval_id _s))
   SEP  (`(array_at_range tint sh contents 0 size) (eval_id _a))).
go_lower. subst. simpl in H2. apply andp_right; auto.
apply prop_right; repeat split; auto; try omega.
 intcompare H2. auto.
apply semax_extract_PROP; intro.
apply semax_pre_PQR with
(PROP  ()
   LOCAL  (`(eq a0) (eval_id _a); `(eq (Vint (Int.repr i0))) (eval_id _i);
   `(eq (Vint (Int.repr size))) (eval_id _n); `denote_tc_isptr (eval_id _a);
   `(eq (Vint (fold_range (add_elem contents) Int.zero 0 i0))) (eval_id _s))
   SEP 
   (`(array_at_range tint sh contents 0 i0) (eval_id _a);
    `(typed_mapsto tint sh 0) (`(eval_binop Oadd (tptr tint) tint)  (eval_id _a) (eval_id _i)) `(contents i0);
    `(array_at_range tint sh contents (Zsucc i0) size) (eval_id _a))).
rewrite typed_mapsto_tint.
go_lower. subst.
apply andp_right. apply prop_right; repeat split; auto.
rewrite (split3_array_at_range i0) by omega.
cancel.
simpl_typed_mapsto.
rewrite mapsto_offset_zero.
auto.
rewrite typed_mapsto_tint.
forward. (* x = a[i]; *)
forward. (* s += x; *)
forward. (* i++; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with (Zsucc i0).
go_lower. subst. simpl in H3.
 unfold eval_binop in H3; simpl in H3. inv H3.
 unfold eval_binop in H2; simpl in H2.  inv H2.
 apply andp_right. apply prop_right; repeat split; auto; try omega.
unfold Zsucc. rewrite Int.add_signed.
repeat (rewrite Int.signed_repr 
      by (unfold Int.min_signed, Int.max_signed in *; omega)).
auto.
 admit.  (* need simple lemma fold_range_split *)
 rewrite split3_array_at_range with (i:=i0) (lo:=0)(hi:=size); auto.
 simpl_typed_mapsto.
 rewrite mapsto_offset_zero.
 cancel.
(* After the loop *)
forward.  (* return s; *)
go_lower.  subst; normalize.
Qed.

Definition four_contents (z: Z) : int := Int.repr (Zsucc z).

Lemma  setup_globals:
  forall u rho,  tc_environ (func_tycontext f_main Vprog Gtot) rho ->
     main_pre prog u rho
      |-- array_at_range tint Ews four_contents 0 4
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
 unfold array_at_range, rangespec; simpl.
 unfold array_at.
 repeat  simpl_typed_mapsto.
 rewrite sepcon_emp.
 unfold four_contents. simpl.
 change (umapsto  (Share.splice extern_retainer Share.top) (Tint I32 Unsigned noattr))
       with (umapsto Ews tint).
 replace (Vptr b z) with (Vptr b (Int.add z (Int.repr 0)))
    by (rewrite Int.add_zero; auto).
 repeat apply sepcon_derives; auto;
 (repeat  rewrite Int.add_assoc; unfold mapsto;
 apply andp_right; [apply prop_right; reflexivity | ];
 match goal with
  |- (umapsto _ _ (Vptr _ (Int.add z ?a)) _) |-- 
      (umapsto _ _ (Vptr _ (Int.add z ?b)) _) =>
     replace b with a; [auto | ]
 end; compute; auto).
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
 go_lower. normalize. eval_cast_simpl.
 repeat apply andp_right; try apply prop_right; simpl; auto. 
 compute; congruence.
 simpl.
 apply eval_var_isptr with Delta; simpl; auto.
 apply setup_globals; auto.
 forward.
 forward. (* return s; *)
 go_lower. subst. normalize.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons; [ reflexivity | apply body_sumarray | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

