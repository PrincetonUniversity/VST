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
          SEP (`(array_at tint sh (cSome contents) 0 size) (eval_id _a))
  POST [ tint ]  
        local (`(eq (Vint (fold_range (add_elem contents) Int.zero 0 size))) retval)
                 && `(array_at tint sh (cSome contents) 0 size a0).

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
   SEP (`(array_at tint sh (cSome contents) 0 size) (eval_id _a))).

Lemma fold_range_split:
  forall A f (z: A) lo hi delta,
   lo <= hi -> delta >= 0 ->
   fold_range f z lo (hi+delta) =
   fold_range f (fold_range f z hi (hi+delta)) lo hi.
Proof.
unfold fold_range; intros.
replace (hi+delta-hi) with delta by omega.
replace (hi+delta-lo) with ((hi-lo)+ delta) by omega.
rewrite nat_of_Z_plus by omega.
forget (nat_of_Z delta) as d.
clear delta H0.
pattern hi at 2.
replace hi with (hi-lo+lo) by omega.
remember (hi-lo) as r. 
replace r with (Z.of_nat (Z.to_nat r))
 by (rewrite Z2Nat.id; omega).
forget (Z.to_nat r) as n; clear r hi H Heqr.
rewrite nat_of_Z_of_nat.
revert z lo d; induction n; intros.
reflexivity.
change (S n + d)%nat with (S (n + d)).
unfold fold_range' at 1 2; fold @fold_range'.
f_equal.
rewrite IHn; clear IHn.
f_equal. f_equal.
rewrite Nat2Z.inj_succ.
omega.
Qed.

Lemma fold_range_fact1:
 forall lo hi contents,
  lo <= hi ->
  fold_range (add_elem contents) Int.zero lo (Z.succ hi) =
  Int.add (fold_range (add_elem contents) Int.zero lo hi) (contents hi).
Proof.
intros.
unfold Z.succ.
rewrite fold_range_split by omega.
unfold fold_range at 2.
replace (hi+1-hi) with 1 by omega.
change (nat_of_Z 1) with 1%nat.
unfold fold_range'.
*
unfold fold_range.
forget (nat_of_Z (hi-lo)) as n.
unfold add_elem at 2.
forget (contents hi) as a.
rewrite Int.add_zero.
clear.
revert lo; induction n; intros.
simpl. rewrite Int.add_zero_l. auto.
simpl.
rewrite (IHn (Z.succ lo)).
clear IHn.
forget (fold_range' (add_elem contents) Int.zero (Z.succ lo) n) as B.
unfold add_elem.
rewrite Int.add_assoc.
auto.
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
     SEP (`(array_at tint sh (cSome contents) 0 size) (eval_id _a))).
(* Prove that current precondition implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with 0.
entailer!. omega.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer!. f_equal. omega.
(* Prove that loop body preserves invariant *)
forward.  (* x = a[i]; *)
entailer!.
forward. (* s += x; *)
forward. (* i++; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with (Zsucc i0).
entailer.
 omega.
 omega.
 apply fold_range_fact1; omega.
(* After the loop *)
forward.  (* return s; *)
Qed.

Definition four_contents (z: Z) : int := Int.repr (Zsucc z).

Lemma  setup_globals:
  forall u rho,  tc_environ (func_tycontext f_main Vprog Gtot) rho ->
     main_pre prog u rho
      |-- array_at tint Ews (cSome four_contents) 0 4
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
 entailer.
 assert (isptr (eval_var _four (tarray tint 4) rho)) 
  by (eapply eval_var_isptr; eauto).
 normalize.
 apply andp_right.
 apply prop_right; repeat split; auto; try solve [ compute; congruence].
 apply setup_globals; auto.
 auto with closed.
 forward. (* return s; *)
 entailer!.
 unfold main_post. entailer.
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

