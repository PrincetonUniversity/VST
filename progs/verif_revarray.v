Require Import floyd.proofauto.
Require Import progs.revarray.

Local Open Scope logic.

Definition flip (n: Z) (f: Z -> int) (i: Z) := f (n-1-i).

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : Z -> int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed; writable_share sh)
          LOCAL (`(eq a0) (eval_id _a);
                      `(eq (Vint (Int.repr size))) (eval_id _n);
                      `isptr (eval_id _a))
          SEP (`(array_at tint sh (cSome contents) 0 size) (eval_id _a))
  POST [ tvoid ]  `(array_at tint sh (cSome (flip size contents)) 0 size a0).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    reverse_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.
 
Definition flip_between (n: Z)(lo hi: Z) (f: Z -> int) (i: Z) := 
   f (if zlt i lo then n-1-i
      else if zlt i hi then i
             else n-1-i).

Definition reverse_Inv a0 sh contents size := 
 EX j:Z,
  (PROP  (0 <= j; j <= size-j; isptr a0)
   LOCAL  (`(eq a0) (eval_id _a);
                `(eq (Vint (Int.repr j))) (eval_id _lo);
                `(eq (Vint (Int.repr (size-j)))) (eval_id _hi))
   SEP (`(array_at tint sh (cSome (flip_between size j (size-j) contents)) 0 size a0))).


Lemma body_reverse: semax_body Vprog Gtot f_reverse reverse_spec.
Proof.
start_function.
name a _a.
name n _n.
name lo' _lo.
name hi' _hi.
name s _s.
name t _t.
forward.  (* lo = 0; *) 
forward.  (* hi = n; *)
forward_while (reverse_Inv a0 sh contents size)
    (PROP  (isptr a0)
   LOCAL  (`(eq a0) (eval_id _a))
   SEP (`(array_at tint sh (cSome (flip size contents)) 0 size a0))).
(* Prove that current precondition implies loop invariant *)
unfold reverse_Inv.
apply exp_right with 0.
entailer!; try omega.
f_equal; omega.
apply derives_refl'.
apply equal_f.
apply array_at_ext.
intros.
unfold flip_between.
unfold cSome. f_equal.
rewrite if_false by omega.
rewrite if_true by omega.
auto.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer!.
rename H3 into H5.
rewrite Int.sub_signed in H5.
normalize in H5.
simpl_compare.
apply derives_refl'.
apply equal_f.
apply array_at_ext.
intros. unfold flip_between, flip.
unfold cSome; f_equal.
if_tac; auto.
if_tac; auto.
f_equal.
assert (j+j >= size-1) by omega; clear H3.
assert (j+j <= size) by omega; clear H1.
assert (j+j=size \/ j+j=size-1) by omega.
destruct H1; try omega.
(* Prove that loop body preserves invariant *)
forward.  (* t = a[lo]; *)
entailer!.
rewrite Int.sub_signed in H3.
normalize in H3.
simpl_compare.
omega.
forward.  (* s = a[hi]; *)
entailer.
rename H3 into H6.
rewrite Int.sub_signed in H6.
normalize in H6.
simpl_compare.
apply prop_right; omega.

normalize. simpl typeof.
forward. (*  a[hi-1] = t ; *)
entailer.
rewrite Int.sub_signed in H4.
normalize in H4.
simpl_compare.
apply prop_right; omega.

normalize.
forward. (*  a[lo] = s; *) 
entailer.
rewrite Int.sub_signed in H4.
normalize in H4.
simpl_compare.
apply prop_right; omega.

normalize.
forward. (* lo++; *)
forward. (* hi--; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold reverse_Inv.
apply exp_right with (Zsucc j).
entailer.
 simpl in H7. rewrite Int.sub_signed in H7. normalize in H7.
 simpl_compare.
 apply andp_right.
 apply prop_right.
 normalize. repeat split; try omega.
 f_equal; omega.
 apply derives_refl'.
 apply equal_f.
 apply array_at_ext; intros.
 unfold upd, cSome. if_tac. subst.
 normalize.
 unfold flip_between.
 rewrite if_false by omega.
 rewrite if_true by omega.
 rewrite if_true by omega.
 f_equal; f_equal; omega.
 if_tac.
 unfold flip_between. rewrite if_false by omega.
 if_tac; try omega. if_tac; try omega. if_tac; try omega.
 f_equal; f_equal; omega.
 unfold flip_between.
 if_tac; try omega. if_tac; try omega. auto.
 if_tac; try omega. if_tac; try omega.  if_tac; try omega. auto.
 if_tac; try omega.  if_tac; try omega.  auto.
(* After the loop *)
forward. (* return; *)
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
apply (remember_value (eval_var _four (tarray tint 4))); intro a0.
(*
 THIS forward FAILS, because we don't yet support void functions 
forward.  (*  revarray(four,4); *)
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
 entailer!.
 unfold main_post. entailer.
Qed.
*)
Admitted.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

