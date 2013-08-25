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

Definition isptrb v := 
   match v with | Vptr _ _ => true | _ => false end.


Definition Igt a b:=
Int.cmp Cgt a b = true.

(*only two ex allowed? *)

Definition fst_3 {A B C} (a: A* B*C) := fst (fst a).
Definition snd_3 {A B C} (a: A * B * C) := snd (fst a).
Definition third_3 {A B C} (a: A * B * C) := snd a.

Definition insert_invariant sh value contents :=
EX contents_lt: list int,
EX contents_rest : list int,
EX sorted_val : int,
EX next_ptr : val,
PROP (Forall (Igt value) (contents_lt); 
      (contents_lt) ++ 
         (sorted_val)::(contents_rest) = contents)
LOCAL ( `(eq (Vint value)) (eval_id _value);
        `(eq (Vint (sorted_val))) (eval_id _sortedvalue);
  `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list) 
           (eval_id _index) `tint
           (`(eval_binop Ogt tint tint) (eval_id _value)
             (eval_id _sortedvalue))))
SEP (`(lseg LS sh (contents_lt)) (eval_id _sorted) (eval_id _index);
     `(list_cell LS sh) (eval_id _index) `(sorted_val);
      `(field_mapsto sh t_struct_list _tail) (eval_id _index) 
                           `(next_ptr);
      `(lseg LS sh (contents_rest)) `(next_ptr) `nullval;
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

Lemma Forall_app :
forall {A} P (l1 l2 :list A),
Forall P (l1 ++ l2) <->
Forall P l1 /\ Forall P l2.
intros.
split; induction l1; intros.
inv H. destruct l2; inv H0. auto.
split. auto. simpl in H2. inv H2.
constructor; auto.
split. inv H. constructor; auto. apply IHl1 in H3.
intuition.
inv H. apply IHl1 in H3. intuition.
simpl. intuition.
simpl. constructor.
destruct H. inv H. auto.
apply IHl1. intuition.
inv H0; auto.
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
go_lower. normalize. intros first_val tail_vals tail_ptr ?.
rewrite lift_list_cell_eq.
forward. (*sortedvalue = index -> head;*)
forward. (*guard' = index && (value > sortedvalue);*) 
  
forward. (*guard = guard'*) 
simpl typeof.
{






forward_while (insert_invariant sh v contents) (insert_invariant sh v contents).
(*pre implies invariant*)
unfold insert_invariant. apply (exp_right (nil, tail_vals)). 
eapply (exp_right (first_val,tail_ptr)). 
entailer.
{ apply andp_right. 
  + rewrite H1. apply prop_right. rewrite <- H3 in *. auto. 
  + normalize. 
}
(*guard typechecks*)
entailer.
(*invariant implies post *)
unfold insert_invariant.
apply (exp_right all_contents). 
apply (exp_right sorted_val__next_ptr).
entailer.
(*invariant across command *) 
forward. 
(* unfold the remaining part of the list *)
destruct sorted_val__next_ptr as [sorted_val next_ptr]. 
destruct all_contents as [contents_lt contents_rest]. 
unfold fst, snd.
forward. (*    index = index -> tail; *)
(* if(index) *)
forward_if 
     (EX index_val2 : elemtype LS,
      EX index_ptr2 : val,
      EX rest_index_vals : list (elemtype LS),
      EX old : val,
     PROP  (Forall (Igt v) contents_lt;
       (if( isptrb next_ptr) then
         contents_lt ++ sorted_val :: index_val2 :: rest_index_vals = contents
       else 
         contents_lt ++ sorted_val :: nil = contents);
      (if(isptrb next_ptr) then
         index_val2 :: rest_index_vals = contents_rest
       else 
         True))
      LOCAL  (`(eq next_ptr) (eval_id _index);
      `eq (eval_id _previous) `index0;
      `(typed_true (typeof (Etempvar _guard tint))) (eval_id _guard);
      `(eq (Vint v)) (eval_id _value);
      `(eq (Vint sorted_val)) `old;
      (if (isptrb next_ptr) then
        `(eq (Vint index_val2)) (eval_id _sortedvalue)
      else
        `(eq (Vint sorted_val)) (eval_id _sortedvalue));   
      `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list) 
           `index0 `tint
           (`(eval_binop Ogt tint tint) (eval_id _value)
              `old)))
      SEP  (`(list_cell LS sh) `index0 `sorted_val;
      `(field_mapsto sh t_struct_list _tail) `index0 `next_ptr;
      `(lseg LS sh contents_lt) (eval_id _sorted) `index0;
      (if (isptrb next_ptr) then
        (`(list_cell LS sh) `next_ptr `index_val2 *
         `(field_mapsto sh t_struct_list _tail) `next_ptr `index_ptr2 *
         `(lseg LS sh rest_index_vals) `index_ptr2 `nullval)
      else `emp);
      subst _index `index0
        (subst _previous `x (var_block Tsh (_newitem, t_struct_list))))).
entailer.
focus_SEP 3. apply semax_lseg_nonnull.
entailer.
intros index_val2 rest_index_vals2 index_ptr2 ?. 
apply semax_pre with 
(PROP  (Forall (Igt v) contents_lt;
      contents_lt ++ sorted_val :: contents_rest = contents)
      LOCAL 
      (`(typed_true (typeof (Etempvar _index (tptr t_struct_list))))
         (eval_expr (Etempvar _index (tptr t_struct_list)));
      `(eq next_ptr) (eval_id _index); `eq (eval_id _previous) `index0;
      `(typed_true (typeof (Etempvar _guard tint))) (eval_id _guard);
      `(eq (Vint v)) (eval_id _value);
      `(eq  (Vint sorted_val)) (eval_id _sortedvalue);
      `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list) 
           `index0 `tint
           (`(eval_binop Ogt tint tint) (eval_id _value)
               (eval_id _sortedvalue))))
      SEP  (`(list_cell LS sh) `next_ptr `index_val2;
      `(field_mapsto sh t_struct_list _tail) (eval_id _index) `index_ptr2;
      |>`(lseg LS sh rest_index_vals2) `index_ptr2 `nullval;
      `(lseg LS sh contents_lt) (eval_id _sorted) `index0;
      `(list_cell LS sh) `index0 `sorted_val;
      `(field_mapsto sh t_struct_list _tail) `index0 `next_ptr;
      subst _index `index0
        (subst _previous `x (var_block Tsh (_newitem, t_struct_list))))).
entailer.
(*needs work, most of this should be in forward *)
(*sortedvalue = index -> head;*)
{ rewrite lift_list_cell_eq.
  apply sequential'.
  hoist_later_in_pre.
  eapply semax_post_flipped.
  eapply (semax_load_field_37); try reflexivity.
  go_lower. apply prop_right; auto.
  entailer.
  cancel.
  intros. apply andp_left2.
  apply normal_ret_assert_derives'.
  apply (exp_right index_val2).
  apply (exp_right index_ptr2).
  apply (exp_right rest_index_vals2).
  apply (exp_left); intro old.
  apply (exp_right old).
  autorewrite with subst.
  entailer.
  destruct (eval_id _index rho); inv H4.
  simpl.
  entailer.
  cancel.
}
(*also needs work *)
(*skip*)
{
  apply sequential'.
  eapply semax_post_flipped.
  eapply semax_skip.
  intros. apply andp_left2.
  apply normal_ret_assert_derives'.
  apply (exp_right sorted_val).
  (*these don't matter *)
  apply (exp_right x).
  apply (exp_right contents_rest).
  (*this does*)
  apply (exp_right (Vint sorted_val)).
  go_lower.
  rewrite H2 in *.
  simpl in H7. rewrite H7 in *.
  entailer.
  cancel. 
}

abbreviate_semax.
apply extract_exists_pre; intro index_val2.
apply extract_exists_pre; intro index_ptr2.
apply extract_exists_pre; intro rest_index_vals2.
apply extract_exists_pre; intro old_sortedvalue.
forward.
admit. (* fix this*)
admit.
forward.
(*implies post*)
unfold insert_invariant.
unfold loop1_ret_assert.
unfold subst, fst_3, snd_3, fst, snd in *.
remember (isptrb next_ptr).
{ destruct b.
  + apply (exp_right (contents_lt ++ sorted_val :: [], rest_index_vals2)).
    apply (exp_right (index_val2, index_ptr2)).
    entailer.
    rewrite <- H4 in *.
    apply andp_right.
       - apply prop_right.
         split. rewrite Forall_app. split.
         auto.
         simpl in H5.
         simpl in H8.
         clear - H8 H7.
         destruct (eval_id _previous rho); inv H7.
         unfold logical_and_result in *.
         simpl in *. constructor. unfold Igt.
         replace (Int.lt sorted_val value) with
           (Int.cmp Clt sorted_val value) in * by auto.
         SearchAbout Int.cmp.
         remember (Int.cmp Clt sorted_val value).
         destruct b0; inv H8. SearchAbout Int.cmp.
         rewrite <- Int.swap_cmp in Heqb0. simpl swap_comparison in Heqb0.
         auto. auto. 
         split. 
         rewrite app_assoc_reverse. simpl. auto. 
         auto.
       - cancel. admit. (*seems reasonable *)
  + apply (exp_right (contents_lt , nil)).
    apply (exp_right (sorted_val, nullval)).
    entailer.
    rewrite <- H4 in *.
    apply andp_right.
      - apply prop_right.
         auto.
      - cancel. 
        

        


Admitted.
