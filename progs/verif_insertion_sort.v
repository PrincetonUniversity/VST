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
Definition insert_invariant sh value contents :=
EX contents_lt: list int,
EX contents_rest: list int,
PROP (Forall (Ilt value) contents_lt; contents_lt ++ contents_rest = contents)
LOCAL ()
SEP (`(lseg LS sh contents_lt) (eval_id _sorted) (eval_id _index);
     `(lseg LS sh contents_rest) (eval_id _index) `nullval;
      (var_block Tsh (_newitem, t_struct_list))).

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
forward. (*guard = index && (value > sortedvalue);*) 
  
forward. (*guard = guard'*)
forward_while (insert_invariant sh v contents) (insert_invariant sh v contents);
  autorewrite with ret_assert.
(*pre implies invariant*)
unfold insert_invariant. apply (exp_right nil). eapply (exp_right contents). go_lower.
normalize.
{ repeat apply andp_right. 
  + apply prop_right. auto.
  + normalize. 
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
go_lower.
apply (exp_right contents_lt). normalize.
apply (exp_right contents_rest). normalize.



SearchAbout lseg.

}

    
 forward.

forward0.
forward0.
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].
unfold Post0.
forward.
eapply semax_logical_and_PQR.
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].
intro rho. simpl. repeat apply andp_right; try apply prop_right; auto.
eapply semax_logical_and_PQR; auto 50 with closed.
simpl. reflexivity.
go_lower. subst index value. normalize.
forward. unfold Post. go_lower.

Admitted.



simpl overridePost.
unfold  overridePost.
simpl eq_dec.
simpl EqDec_exitkind.
cbv beta iota.
unfold insert_invariant. normalize.
apply (exp_right contents_lt). normalize.
apply (exp_right contents_rest).
go_lower.
 normalize.



SearchAbout lseg.

}

    
 forward.

forward0.
forward0.
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].
unfold Post0.
forward.
eapply semax_logical_and_PQR.
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].
intro rho. simpl. repeat apply andp_right; try apply prop_right; auto.
eapply semax_logical_and_PQR; auto 50 with closed.
simpl. reflexivity.
go_lower. subst index value. normalize.
forward. unfold Post. go_lower.

Admitted.


