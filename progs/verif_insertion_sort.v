Load loadpath.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.insertionsort.
Import ListNotations.

Local Open Scope logic.

Instance LS: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.


Fixpoint insert x xs :=
  match xs with
    | [] => [x]
    | h :: t => if Int.cmp Cle x h then x :: xs else h :: (insert x t)
  end.

Definition insert_spec :=
  DECLARE _insert
    WITH sh: share, contents : list int, v : int
    PRE [ _value OF tint, _sorted OF (tptr t_struct_list)]
        PROP ()
        LOCAL (`(eq (Vint v)) (eval_id _value); `isptr (eval_id _sorted))
        SEP (`(lseg LS sh contents) (eval_id _sorted) `nullval)
    POST [tptr t_struct_list]
        `(lseg LS sh (insert v contents)) retval `nullval.
        
Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := insert_spec :: nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma list_cell_eq: forall sh v i,
   list_cell LS sh v i = field_mapsto sh t_struct_list _head v (Vint i).
Proof.  reflexivity.  Qed.

Lemma lift_list_cell_eq:
  forall sh e v,
   `(list_cell LS sh) e v = `(field_mapsto sh t_struct_list _head) e (`Vint v).
Proof. reflexivity. Qed.

Check Forall.
Definition Ilt a b:=
Int.cmp Cle a b = true.
(*TODO: add local eval facts to the invariant *) 
Check logical_and_result.
Definition insert_invariant sh value contents :=
EX contents_lt: list int,
EX contents_rest: list int,
PROP (Forall (Ilt value) contents_lt; contents_lt ++ contents_rest = contents)
LOCAL ( `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list) 
           (eval_id _index) `tint
           (`(eval_binop Ogt tint tint) (eval_id _value)
              (eval_id _sortedvalue))))
SEP (`(lseg LS sh contents_lt) (eval_id _sorted) (eval_id _index);
     `(lseg LS sh contents_rest) (eval_id _index) `nullval;
      (var_block Tsh (_newitem, t_struct_list))).

Lemma lseg_cons_non_nill : forall {ls ll} LS sh h r v1 v2 , @lseg ls ll LS sh (h::r) v1 v2 = 
!!isptr v1 && @lseg ls ll LS sh (h::r) v1 v2.
intros.
apply pred_ext.
  + apply andp_right; auto. rewrite lseg_unfold.
     normalize. rewrite field_mapsto_isptr.
     normalize. 
  +  normalize.
Qed.

Lemma body_insert: semax_body Vprog Gtot f_insert insert_spec.
Proof.
start_function.
name value _value.
name index _index.
name sorted _sorted.
forward. (*  index = sorted; *)
focus_SEP 1.
apply semax_lseg_nonnull.
go_lower. normalize. intros h r y ?.
rewrite lift_list_cell_eq.
eapply semax_pre with 
(PROP  ()
      LOCAL 
      (`eq (eval_id _index)
         (eval_expr (Etempvar _sorted (tptr t_struct_list)));
      `(eq (Vint v)) (eval_id _value); `isptr (eval_id _sorted))
      SEP 
      (`(field_mapsto sh t_struct_list _head) (eval_id _index) (`Vint `h);
      `(field_mapsto sh t_struct_list _tail) (eval_id _sorted) `y;
      |>`(lseg LS sh r) `y `nullval; stackframe_of f_insert)).
go_lower. subst value index. normalize.
forward. (*sortedvalue = index -> head;*)
forward. (*guard' = index && (value > sortedvalue);*) 
  
forward. (*guard = guard'*) simpl typeof.
forward_while (insert_invariant sh v contents) (insert_invariant sh v contents);
  autorewrite with ret_assert.
(*pre implies invariant*)
unfold insert_invariant. apply (exp_right nil). eapply (exp_right contents). 
go_lower.
normalize.
{ repeat apply andp_right. 
  + apply prop_right. auto.
  + normalize. 
  + rewrite H1. normalize.
  + subst. apply prop_right. apply ptr_eq_refl. auto.
  + subst. rewrite (lseg_unfold LS sh (h::r) sorted nullval).
    normalize. apply (exp_right y).
    apply andp_right.
      - apply prop_right. destruct sorted; inv H6; auto.
      - cancel. }
(*guard typechecks*)
go_lower.
(*invariant implies post *)
unfold insert_invariant. normalize.
apply (exp_right contents_lt). 
apply (exp_right contents_rest).
entailer; normalize; cancel.
(*precondition across command *) 
forward.
(* unfold the remaining part of the list *)
focus_SEP 1. apply semax_lseg_nonnull.
{
  go_lower. destruct (eval_id _guard rho); inv H4.
  apply prop_right. normalize. destruct (eval_id _previous rho); inv TC0.
  unfold logical_and_result in *. simpl in H5. inv H5; inv H7. simpl; auto. 
}      
intros. 
forward. (*    index = index -> tail; *)
{ 
  entailer. rewrite isptr_force_ptr; normalize.
}
forward. (* if(index) *)
entailer; normalize; cancel. autorewrite with subst.
focus_SEP 2. apply semax_lseg_nonnull.
{
  entailer;normalize;cancel.
}
intros.
apply semax_pre with
     (PROP  (Forall (Ilt v) contents_lt;
      contents_lt ++ contents_rest = contents)
      LOCAL 
      (`(typed_true (typeof (Etempvar _index (tptr t_struct_list))))
         (eval_expr (Etempvar _index (tptr t_struct_list)));
      `eq (eval_id _index) `y0; `eq (eval_id _previous) `index0;
      `(typed_true (typeof (Etempvar _guard tint))) (eval_id _guard);
      `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list) 
           `index0 `tint
           (`(eval_binop Ogt tint tint) (eval_id _value)
              (eval_id _sortedvalue))))
      SEP  (`(list_cell LS sh) (eval_id _index) `h1;
      `(field_mapsto sh t_struct_list _tail) (eval_id _index) `y1;
      |>`(lseg LS sh r1) `y1 `nullval; `(list_cell LS sh) `index0 `h0;
      `(field_mapsto sh
          (Tstruct _struct_list
             (Fcons _head tint
                (Fcons _tail (Tcomp_ptr _struct_list noattr) Fnil)) noattr)
          _tail) `index0 `y0;
      `(lseg LS sh contents_lt) (eval_id _sorted) `index0;
      subst _index `index0
        (subst _previous `x (var_block Tsh (_newitem, t_struct_list))))).
entailer; normalize; cancel.
rewrite lift_list_cell_eq.
forward.
Admitted.


