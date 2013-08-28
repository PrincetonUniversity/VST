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
          SEP (`(array_at tint sh contents 0 size) (eval_id _a))
  POST [ tint ]  `(array_at tint sh (flip size contents) 0 size a0).

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
   SEP (`(array_at tint sh (flip_between size j (size-j) contents) 0 size a0))).

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

Lemma array_at_ext:
  forall t sh f  f' lo hi,
   (forall i, lo <= i < hi -> f i = f' i) ->
   array_at t sh f lo hi = array_at t sh f' lo hi.
Proof.
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


Definition typecheck_store' t := 
(is_int_type t = true -> t = Tint I32 Signed noattr) /\
(is_float_type t = true -> t = Tfloat F64 noattr).

Lemma semax_store_array:
forall Espec (Delta: tycontext) n sh t1 (contents: Z -> reptype t1)
              lo hi   
              (v1: environ-> val) inject P Q R            
             e1  e2 (v2: Z) (v: reptype t1),
    writable_share sh ->
    typeof e1 =  tptr t1 ->
    type_is_volatile t1 = false ->
    typecheck_store' t1 ->
    repinject t1 = Some inject ->
    nth_error R n = Some (`(array_at t1 sh contents lo hi) v1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1))
          && !! (in_range lo hi v2)
          && local (tc_expr Delta e1) && local (tc_expr Delta (Ecast e2 t1))
          && local (`(eq (inject v)) (eval_expr (Ecast e2 t1))) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(array_at t1 sh (upd contents v2 v) lo hi) v1)))))).
Proof.
intros.
rewrite (SEP_nth_isolate _ _ _ H4) in H5|-*.
rewrite (SEP_replace_nth_isolate _ _ _ (`(array_at t1 sh (upd contents v2 v) lo hi) v1) H4).
forget (@replace_nth (environ -> mpred) n R (@emp _ _ _)) as R'.
clear n H4 R. rename R' into R.
eapply semax_pre_post;
 [ | | apply (semax_store Delta _ _ sh 
          (PROPx P (LOCALx
              (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1) ::
              tc_expr Delta e1 :: tc_expr Delta (Ecast e2 t1) :: `(in_range lo hi v2) ::
              `(eq (inject v)) (eval_expr (Ecast e2 t1)) :: 
             Q)
            (SEPx 
             (`(array_at t1 sh contents lo v2) v1 ::
             `(array_at t1 sh contents (Zsucc v2) hi) v1 :: R))))); auto].
* apply later_left2.
  rewrite insert_local.
  rewrite <- (andp_dup (PROPx _ _)).
  eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H5] |  clear H5].
  go_lowerx.
  entailer.
  apply andp_right.
  apply prop_right.
  hnf. simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
  rewrite H0; reflexivity. simpl. unfold_lift. rewrite <- H7; simpl. destruct (v1 rho); inv H13; apply I.
  rewrite H1; reflexivity.
  apply sepcon_derives; auto.
  rewrite  (split3_array_at v2).
  cancel.
  rewrite <- H7; simpl.
  destruct (v1 rho); inv H13. simpl.
  unfold add_ptr_int; simpl.
  rewrite (repinject_typed_mapsto _ _ _ _ _ H3).
  apply mapsto_mapsto_.
  omega.
* intros.
  clear H5.
  go_lowerx. apply normal_ret_assert_derives. entailer.
  rewrite  (split3_array_at v2 _ _ _ lo hi).
  cancel.
  rewrite (sepcon_comm (mapsto _ _ _ _)).
  apply sepcon_derives; [apply sepcon_derives | ].
  apply derives_refl'; apply equal_f; apply array_at_ext; intros.
  rewrite upd_neq; auto. omega.
  rewrite (repinject_typed_mapsto _ _ _ _ _ H3).
  destruct (eval_expr e1 rho); inv H13.
  destruct (v1 rho); inv H6.
  unfold add_ptr_int. simpl.
  rewrite upd_eq. rewrite H11. unfold_lift; simpl.
  apply derives_refl.
  apply derives_refl'; apply equal_f; apply array_at_ext; intros.
  rewrite upd_neq by omega. auto. omega.
Qed.

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
   SEP (`(array_at tint sh (flip size contents) 0 size a0))).
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
rewrite if_false by omega.
rewrite if_true by omega.
auto.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer!.
rename H4 into H5.
simpl in H5.
rewrite Int.sub_signed in H5.
normalize in H5.
unfold Int.lt in H5.
if_tac in H5; inv H5.
normalize in H4.
apply derives_refl'.
apply equal_f.
apply array_at_ext.
intros. unfold flip_between, flip.
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
simpl in H4. rewrite Int.sub_signed in H4.
normalize in H4.
simpl_compare.
omega.
forward.  (* s = a[hi]; *)
entailer.
rename H4 into H6.
simpl in H6. rewrite Int.sub_signed in H6|-*.
normalize in H6.
simpl_compare.
rewrite (Int.signed_repr (size-j)) by repable_signed.
rewrite (Int.signed_repr 1) by repable_signed.
normalize.
apply prop_right; omega.

normalize. simpl typeof.

Ltac new_array_store_tac :=
 ensure_normal_ret_assert;
  hoist_later_in_pre;
match goal with |- @semax ?Esp ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) 
     (Sassign (Ederef (Ebinop Oadd ?e1 ?ei _) ?t) ?e2) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let contents := fresh "contents" in evar (contents: Z -> reptype t);
  let lo := fresh "lo" in evar (lo: Z);
  let hi := fresh "hi" in evar (hi: Z);
  let a := fresh "a" in evar (a: val);
  let H := fresh in 
  assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (array_at t sh contents lo hi a))) * TT);
  [unfold number_list, n, sh, contents, lo, hi, a; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   solve [entailer; cancel]
 | clear H ];
 eapply(@semax_store_array Esp Delta n sh t contents lo hi (`a));
  unfold number_list, n, sh, contents, lo, hi, a;
  [solve [auto] | reflexivity | reflexivity | hnf; intuition | reflexivity 
  | autorewrite with norm; reflexivity
  | ]
end.

forward_with new_array_store_tac.
entailer.
apply (int_cmp_repr Clt) in H5; [ | repable_signed| normalize; repable_signed ].
unfold Zcmp in H5.
normalize in H5.
apply prop_right; split; [reflexivity |].
normalize.
omega.

(* forward_with new_array_store_tac. *)
admit.
(*
forward. (*  a[hi-1] = t ; *)
forward. (*  a[lo] = s; *)
forward. (* lo++; *)
forward. (* hi--; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold reverse_Inv.
apply exp_right with (Zsucc i0).
entailer.
 apply andp_right; auto.
 apply prop_right. inv H3; inv H2.
 rewrite Int.add_signed;
  repeat rewrite Int.signed_repr by repable_signed.
 repeat split;  try omega.
 apply fold_range_fact1; omega.
*)
(* After the loop *)
forward. (* return; *)
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
apply (remember_value (eval_var _four (tarray tint 4))); intro a0.
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

