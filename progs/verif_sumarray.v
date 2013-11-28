Require Import floyd.proofauto.
Require Import progs.sumarray.

Local Open Scope logic.

Definition force_option {A} (x:A) (i: option A) := 
  match i with Some y => y | None => x end.

Definition add_elem (f: Z -> val) (i: Z) := Int.add (force_int (f i)).

Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a0: val, sh : share, contents : Z -> val, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed;
                    forall i, 0 <= i < size -> is_int (contents i))
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
  Int.add (fold_range (add_elem contents) Int.zero lo hi) 
                 (force_int (contents hi)).
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
     SEP (`(array_at tint sh contents 0 size) (eval_id _a))).
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
specialize (H0 _ (conj H1 H3)).
destruct (contents i0); try contradiction.
eauto.
forward. (* s += x; *)
forward. (* i++; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumarray_Inv.
apply exp_right with (Zsucc i0).
entailer.
 omega.
 omega.
 simpl in H5. rewrite Int.signed_repr in H5 by repable_signed.
 rewrite fold_range_fact1 by omega.
 destruct (contents i0); inv H5. simpl. auto.
(* After the loop *)
forward.  (* return s; *)
Qed.

Definition four_contents := (ZnthV tint
           (map Vint (map Int.repr (1::2::3::4:: nil)))).

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name s _s.
apply (remember_value (eval_var _four (tarray tint 4))); intro a0.
forward.  (*  r = sumarray(four,4); *)
instantiate (1:= (a0,Ews,four_contents,4)) in (Value of witness).
 entailer!. 
   intros. unfold four_contents. apply ZnthV_map_Vint_is_int. apply H2.
 auto with closed.
 forward. (* return s; *)
 unfold main_post. entailer!.
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

