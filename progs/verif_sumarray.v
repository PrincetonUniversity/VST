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


Fixpoint rangespec' (lo: Z) (n: nat) (P: Z -> mpred): mpred :=
  match n with
  | O => emp
  | S n' => P lo * rangespec' (Zsucc lo) n' P
 end.

Definition rangespec (lo hi: Z) (P: Z -> mpred) : mpred :=
  rangespec' lo (nat_of_Z (hi-lo)) P.

Definition repable (z: Z) := Int.signed (Int.repr z)=z.
Definition repable_dec (z: Z) : {repable z}+{~repable z}.
Proof.
 intros. apply zeq.
Defined.

Definition add_ptr_int' (ty: type) (v: val) (i: Z) : val :=
  if repable_dec (sizeof ty * i)
   then match v with
      | Vptr b ofs => 
           Vptr b (Int.add ofs (Int.repr (sizeof ty * i)))
      | _ => Vundef
      end
  else Vundef.

Definition add_ptr_int (ty: type) (v: val) (i: Z) : val :=
           eval_binop Oadd (tptr ty) tint v (Vint (Int.repr i)).
Lemma repable_mult2:
  forall i j, i<>0 -> repable (i*j) -> repable j.
Admitted.
Lemma repable_mult1:
  forall i j, j<>0 -> repable (i*j) -> repable i.
Proof.
intros.
 rewrite Zmult_comm in H0.
 apply repable_mult2 in H0; auto.
Qed.

Lemma add_ptr_tint_eq:
  forall ty v i, repable (sizeof ty * i) ->
       add_ptr_int' ty v i = add_ptr_int ty v i.
Proof.
 intros.
 unfold add_ptr_int, add_ptr_int'.
 rewrite if_true by auto.
 destruct v; simpl; auto.
 unfold eval_binop; simpl; auto.
 f_equal. f_equal.
 destruct (eq_dec i 0).
    subst. rewrite Int.mul_zero. rewrite Zmult_0_r. auto.
 assert (repable (sizeof ty)). eapply repable_mult1; eauto.
 assert (repable i). apply repable_mult2 in H; auto.
        pose proof (sizeof_pos ty); omega.
 unfold repable in *.
 rewrite Int.mul_signed. 
 rewrite <- H.
 repeat rewrite Int.repr_signed.
 rewrite H0. rewrite H1. auto.
Qed.

Definition array_at (t: type) (sh: Share.t) (v: val) (i: Z) (e: reptype t) : mpred :=
   typed_mapsto t sh 0 (add_ptr_int t v i) e.

Definition array_at_range (t: type) (sh: Share.t) (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) :=
           rangespec lo hi (fun i => array_at t sh v i (f i)).

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f  zero (Zsucc lo) n')
 end.

Definition fold_range {A: Type} (f: Z -> A -> A) (zero: A) (lo hi: Z) : A :=
  fold_range' f zero lo (nat_of_Z (hi-lo)).

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
 assert (~ (i0 < size)); [ | omega]. 
 admit.  (* arithmetic proof *)
(* Prove that loop body preserves invariant *)
apply semax_pre_PQR with
 (PROP (0 <= i0 < size) 
  LOCAL (`(eq a0) (eval_id _a); `(eq (Vint (Int.repr i0))) (eval_id _i);
   `(eq (Vint (Int.repr size))) (eval_id _n); `denote_tc_isptr (eval_id _a);
   `(eq (Vint (fold_range (add_elem contents) Int.zero 0 i0))) (eval_id _s))
   SEP  (`(array_at_range tint sh contents 0 size) (eval_id _a))).
go_lower. subst. simpl in H2. apply andp_right; auto.
apply prop_right; repeat split; auto; try omega.
 admit.  (* arithmetic proof *)
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
 admit.  (* arithmetic proof *)
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

