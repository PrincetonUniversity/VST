Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.insertionsort.
Require Import Sorted.
Require Import Omega.
Require Import Coq.Sorting.Permutation.

Local Open Scope logic.

Instance LS: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.

Fixpoint insert x xs :=
  match xs with
    | [] => [x]
    | h :: t => if Int.cmp Cle x h then x :: xs else h :: (insert x t)
  end.

Definition insertion_sort xs :=
    fold_right insert [] xs.

Definition insert_spec :=
  DECLARE _insert
    WITH sh: share, contents : list int, insert_val : int, sorted_ptr : val, insert_ptr: val
    PRE [_insert_node OF (tptr t_struct_list), _sorted OF (tptr t_struct_list)]
        PROP (writable_share sh)
        LOCAL (temp _sorted sorted_ptr; temp _insert_node insert_ptr)
        SEP (lseg LS sh (map Vint contents) sorted_ptr nullval;
               data_at sh t_struct_list (Vint insert_val, nullval) insert_ptr)
    POST [tptr t_struct_list]
      EX v: val,
        PROP() LOCAL(temp ret_temp v)
        SEP(lseg LS sh (map Vint (insert insert_val contents)) v nullval).

Definition insertionsort_spec :=
  DECLARE  _insertionsort
    WITH sh: share, contents : list int, list_ptr : val
    PRE [_p OF (tptr t_struct_list)]
        PROP (writable_share sh)
        LOCAL (temp _p list_ptr)
        SEP (lseg LS sh (map Vint contents) list_ptr nullval)
    POST [tptr t_struct_list]
      EX v: val,
        PROP() LOCAL(temp ret_temp v)
        SEP(lseg LS sh (map Vint (insertion_sort contents)) v nullval).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs :=   ltac:(with_library prog
     [insert_spec; insertionsort_spec]).

Lemma list_cell_eq: forall sh,
   list_cell LS sh = field_at sh t_struct_list [StructField _head].
Proof. admit. Qed.

Definition isptrb v :=
   match v with | Vptr _ _ => true | _ => false end.

Definition Igt a b:=
Int.cmp Cgt a b = true.


Definition fst_3 {A B C} (a: A* B*C) := fst (fst a).
Definition snd_3 {A B C} (a: A * B * C) := snd (fst a).
Definition third_3 {A B C} (a: A * B * C) := snd a.

Definition insert_invariant sh insert_val contents :=
EX prev_ptr : val,
EX index_ptr : val,
EX sorted_val : int,
EX next_ptr : val,
EX prev_val : int,
EX contents_lt: list int,
EX contents_rest : list int,
PROP ( if (isptrb prev_ptr)
      then
        (Forall (Igt insert_val) (contents_lt ++ [prev_val]))
      else Forall (Igt insert_val) contents_lt;
      if (isptrb index_ptr)
      then
        if (isptrb prev_ptr)
        then
             (contents_lt) ++ (prev_val)::(sorted_val)::(contents_rest) = contents
        else sorted_val::contents_rest = contents
      else
        if (isptrb prev_ptr)
        then
          contents_lt ++ (prev_val :: nil) = contents
        else
          nil = contents)
LOCAL (temp _index index_ptr; temp _insert_value (Vint insert_val);
        if (isptrb index_ptr)
        then temp _sortedvalue (Vint (sorted_val))
        else `(next_ptr = nullval);
        `eq (eval_id _guard)
         (`logical_and_result `(tptr t_struct_list)
           (eval_id _index) `tint
           (`(eval_binop Ogt tint tint) (eval_id _insert_value)
             (eval_id _sortedvalue)));
        temp _previous prev_ptr;
        if (isptrb prev_ptr)
        then `True
        else temp _sorted index_ptr)
SEP (
     (if(isptrb index_ptr)
      then
       (list_cell LS sh (index_ptr) (Vint (sorted_val)) *
        field_at sh t_struct_list [StructField _tail] next_ptr index_ptr)
      else
         emp);
      (if(isptrb prev_ptr)
       then lseg LS sh (map Vint (contents_lt))) (eval_id _sorted) `(prev_ptr) *
             `(list_cell LS sh (prev_ptr) (Vint (prev_val))) *
             `(field_at sh t_struct_list [StructField _tail] index_ptr prev_ptr)
       else emp);
     `(lseg LS sh (map Vint (contents_rest))) `(next_ptr) `nullval;
     `(field_at sh t_struct_list [StructField _head] (Vint insert_val)) (eval_id _insert_node);
     `(field_at sh t_struct_list [StructField _tail] nullval) (eval_id _insert_node) ).

Definition insert_post sh insert_val contents :=
EX prev_ptr : val,
EX index_ptr : val,
EX sorted_val : int,
EX next_ptr : val,
EX prev_val : int,
EX contents_lt: list int,
EX contents_rest : list int,
PROP (
      if (isptrb prev_ptr)
      then
        (Forall (Igt insert_val) (contents_lt ++ [prev_val]))
      else Forall (Igt insert_val) contents_lt;
        if (isptrb index_ptr)
      then
        if (isptrb prev_ptr)
        then
             (contents_lt) ++ (prev_val)::(sorted_val)::(contents_rest) = contents
        else sorted_val::contents_rest = contents
      else
        if (isptrb prev_ptr)
        then
          contents_lt ++ (prev_val :: nil) = contents
        else
          nil = contents)
LOCAL ( lift1 (typed_false (typeof (Etempvar _guard tint)))
              (eval_expr (Etempvar _guard tint));
        `(eq index_ptr) (eval_id _index);
        `(eq (Vint insert_val)) (eval_id _insert_value);
        if (isptrb index_ptr)
        then
          `(eq (Vint (sorted_val))) (eval_id _sortedvalue)
        else
          `(next_ptr = nullval);
        `eq (eval_id _guard)
         (`logical_and_result `(tptr t_struct_list)
           (eval_id _index) `tint
           (`(eval_binop Ogt tint tint) (eval_id _insert_value)
             (eval_id _sortedvalue)));
        `(eq prev_ptr) (eval_id _previous);
      if (isptrb prev_ptr)
        then `True
        else `(eq index_ptr) (eval_id _sorted))
SEP (
     (if(isptrb index_ptr)
      then
        (*NOTE:: Can't use (eval_expr _index) here or it will be missed by go_lower *)
       (`(list_cell LS sh (index_ptr) (Vint sorted_val)) *
        `(field_at sh t_struct_list [StructField _tail] next_ptr index_ptr))
      else
         emp);
      (if(isptrb prev_ptr)
       then  `(lseg LS sh (map Vint (contents_lt))) (eval_id _sorted) `(prev_ptr) *
             `(list_cell LS sh (prev_ptr) (Vint prev_val)) *
             `(field_at sh t_struct_list [StructField _tail] index_ptr prev_ptr)
       else emp);
     `(lseg LS sh (map Vint contents_rest)) `(next_ptr) `nullval;
     `(field_at sh t_struct_list [StructField _head] (Vint insert_val)) (eval_id _insert_node);
     `(field_at sh t_struct_list [StructField _tail] nullval) (eval_id _insert_node)).

Lemma lseg_cons_non_nill : forall {ls ll} LS sh h r v1 v2 , @lseg ls ll LS sh (h::r) v1 v2 =
!!isptr v1 && @lseg ls ll LS sh (h::r) v1 v2.
intros.
apply pred_ext.
  + apply andp_right; auto. rewrite lseg_unfold.
     normalize. rewrite field_at_isptr.
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

Lemma lseg_is_ptr_or_null :
forall  sh c v1 v2 R,
@lseg t_struct_list _tail LS sh (c) v1 v2 * R |-- !!is_pointer_or_null v1 && (@lseg t_struct_list _tail LS sh c v1 v2)  * R.
Proof.
intros.
cancel.
apply andp_right.
rewrite lseg_unroll.
apply orp_left. rewrite andp_assoc.
unfold ptr_eq. destruct v1; normalize. destruct v2; normalize.
unfold Int.cmpu in *. simpl.
destruct H.
apply int_eq_e in H.
apply int_eq_e in H0.
subst. unfold Int.zero. entailer.
unfold lseg_cons. normalize.
assert (X := @list_cell_eq). entailer.
cancel.
Qed.

Lemma eval_id_initialized : forall v id rho t,
tc_val t v ->
v = eval_id id rho ->
denote_tc_initialized id t rho.
Proof.
intros.
unfold eval_id in *.
unfold denote_tc_initialized.
exists v. split.
destruct (Map.get (te_of rho) id).
simpl in H0. inv H0.
auto.
inv H0.
inv H.
auto.
Qed.

Ltac destruct_ptr :=
  match goal with
    | [ H: isptr (?X) |- _] => let v := fresh "pt" in (remember X as v; destruct v; inv H)
  end.

Lemma lt_lemma : forall v1 v2 b1 t1,
                   typed_true tint (logical_and_result t1 b1 tint
                                                (eval_binop Ogt tint tint
                                                (Vint v1) (Vint v2))) ->
                                    Forall (Igt v1) [v2].
Proof.
  intros.
  simpl in *.
  unfold logical_and_result in *.
  simpl in *. constructor. unfold Igt.
  replace (Int.lt v2 v1) with
  (Int.cmp Clt v2 v1) in * by auto.
  remember (Int.cmp Clt v2 v1).
  destruct b; inv H.
  rewrite <- Int.swap_cmp in Heqb. simpl swap_comparison in Heqb.
  auto. destruct (strict_bool_val b1 t1); inv H1. destruct b; simpl; inv H0.
  auto.
Qed.


Lemma body_insertionsort : semax_body Vprog Gprog f_insertionsort insertionsort_spec.
Proof.
start_function.
name p _p.
name sorted _sorted.
name index _index.
name next _next.

forward. (*  sorted = NULL; *)
forward. (*   index = p; *)

Definition body_invariant sh contents :=
EX sorted_list : list int,
EX unsorted_list : list int,
EX p: val, EX i: val,
PROP (contents = sorted_list ++ unsorted_list)
LOCAL (temp _sorted p; temp _index i)
SEP (`(lseg LS sh (map Vint (insertion_sort sorted_list)) p nullval);
     `(lseg LS sh (map Vint unsorted_list) i nullval)).

Definition body_post sh contents :=
EX p: val,
PROP ()
LOCAL (temp _sorted p)
SEP (`(lseg LS sh (map Vint (insertion_sort contents)) p nullval)).

forward_while
    (body_invariant sh contents)
    (body_post sh contents)
     [[[sorted_list unsorted_list] p0] i].

(*pre implies invariant*)
apply (exp_right nil).
apply (exp_right contents).
apply (exp_right (Vint (Int.repr 0))).
apply (exp_right list_ptr).
entailer!.

(*invariant implies tc *)
entailer.

(*invariant implies post *)
apply (exp_right p0).
entailer!.
destruct unsorted_list; inv H0.
rewrite <- app_nil_end. auto.

(*invariant across body *)
focus_SEP 1.
normalize.
apply semax_lseg_nonnull.
entailer!.
intros insert_val' unsorted_list2' ? ? ?.
simpl valinject.
assert (exists insert_val, exists unsorted_list2,
   insert_val' = Vint insert_val /\ unsorted_list2' = map Vint unsorted_list2
    /\ unsorted_list = insert_val :: unsorted_list2)
  as [insert_val [unsorted_list2 [? [? ?]]]].
clear - H0. admit.
unfold POSTCONDITION; subst.
abbreviate_semax.
rename unsorted_list2 into unsorted_list.
forward. (* next = index -> tail; *)
forward. (* index -> tail = NULL; *)
(* fold t_struct_list. *)
rewrite list_cell_eq.
(*put fact about sorted into pre so I can instantiate it with a value later *)
simpl.
clear H1.
apply semax_pre with
(EX v : val,
 PROP  ()
   LOCAL  (temp _next y;  temp _sorted v; temp _index i)
   SEP
   (`(data_at sh t_struct_list (Vint insert_val, nullval) i);
   `(lseg LS sh (map Vint unsorted_list) y nullval);
   `(lseg LS sh (map Vint (insertion_sort sorted_list)) v nullval))).
apply (exp_right p0).
go_lower. ent_iter. apply andp_right. apply prop_right; repeat split; auto.
unfold_data_at 1%nat.
entailer.

apply extract_exists_pre. intros sorted_val.
forward_call  (* sorted = insert(index, sorted); *)
  (sh, (insertion_sort sorted_list), insert_val, sorted_val, i).
Intros vret.
forward index_old. (* index = next;*)
unfold body_invariant.
entailer.
apply (exp_right (sorted_list ++ [insert_val],
                           unsorted_list, sorted, next)).
entailer!.
rewrite app_ass; reflexivity.

Lemma insert_reorder : forall v1 v2 l,
insert v1 (insert v2 (l)) = insert v2 (insert v1 l).
Proof.
induction l. simpl. remember (Int.lt v2 v1); remember (Int.lt v1 v2).
destruct b; destruct b0; auto.
replace (Int.lt v2 v1) with (Int.cmp Clt v2 v1) in * by auto.
replace (Int.lt v1 v2) with (Int.cmp Clt v1 v2) in * by auto.
rewrite <- Int.swap_cmp in Heqb. simpl swap_comparison in Heqb.
symmetry in Heqb.
rewrite <- negb_false_iff in Heqb.
rewrite <- Int.negate_cmp in Heqb.
simpl negate_comparison in *.
Admitted.

Lemma insert_insertion_sort : forall v l,
insert v (insertion_sort l) = insertion_sort (l ++ [v]).
intros.
induction l.
auto.
simpl.
rewrite insert_reorder. rewrite IHl. auto.
Qed.

rewrite insert_insertion_sort. cancel.
unfold body_post.
forward_intro sorted_list.
forward.
apply exp_right with sorted.
entailer!.
Qed.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
start_function.
name insert_value _insert_value.
name index _index.
name insert_node _insert_node.
name sorted _sorted.
forward. (*previous = NULL;*)
forward. (*insert_value = insert_node -> head;*)
forward. (*index = sorted; *)
normalize. simpl.
Abort.  (* done up to here, more or less *)
(*
forward_if
 (if isptrb sorted_ptr
  then
  (EX first_val : int, EX tail_vals : list int, EX tail_ptr : val,
   PROP  (contents = first_val :: tail_vals)
      LOCAL
      (`(eq sorted_ptr) (eval_id _index);
       `(eq nullval) (eval_id _previous);
      `(eq (Vint insert_val)) (eval_id _insert_value);
      `(eq (Vint first_val)) (eval_id _sortedvalue);
       `(eq sorted_ptr) (eval_id _sorted))
      SEP  (
         `(field_at sh t_struct_list _head (Vint first_val)) (eval_id _sorted);
         `(field_at sh t_struct_list _tail tail_ptr) (eval_id _sorted);
         `(lseg LS sh (map Vint tail_vals) tail_ptr nullval);
         `(field_at sh t_struct_list _tail nullval) (eval_id _insert_node)))
  else
  (PROP  ()
      LOCAL
      (`(eq sorted_ptr) (eval_id _index);
       `(eq nullval) (eval_id _previous);
      `(eq (Vint insert_val)) (eval_id _insert_value);
       `(eq sorted_ptr) (eval_id _sorted))
      SEP  (
       `(lseg LS sh (map Vint contents) nullval nullval);
      `(field_at sh t_struct_list _head (Vint insert_val)) (eval_id _insert_node);
      `(field_at sh t_struct_list _tail nullval) (eval_id _insert_node)))).
entailer.
{
apply semax_lseg_nonnull.
entailer.
intros first_val' tail_vals' tail_ptr ? ?.
assert (exists first_val, exists tail_vals,
   first_val' = Vint first_val /\ tail_vals' = map Vint tail_vals
    /\ contents = insert_val :: tail_vals)
  as [first_val [tail_vals [? [? ?]]]].
clear - H0. admit.
subst first_val' tail_vals'. clear H0. rename H4 into H0.
rewrite list_cell_eq. simpl.
forward. (*sortedvalue = index -> head;*)
(*  entailer. doesn't work because go_lower doesn't get all the vars in rho *)
go_lowerx.
 entailer!.
 replace (isptrb (eval_id _sorted rho)) with true by (clear - H12; destruct (eval_id _sorted rho); try contradiction; reflexivity).
  apply (exp_right insert_val).
  apply (exp_right tail_vals).
  apply (exp_right tail_ptr).
  entailer!.
  f_equal.  congruence. rewrite H7.

  apply sequential'.
  hoist_later_in_pre.
  eapply semax_post_flipped.
  eapply (semax_load_field''); try reflexivity.
  entailer.
  entailer!.
  intros.
 destruct contents; inv H0; apply I.
  apply andp_left2.
  apply normal_ret_assert_derives'.
  entailer. unfold subst in *.
  apply (exp_right first_val).
  apply (exp_right tail_vals).
  apply (exp_right tail_ptr).
  entailer.
  rewrite H2 in *.
  remember (eval_id _sorted rho).
  destruct (v); try inv H5; simpl;
  entailer!.
  rewrite <- Heqv in *.
  cancel.
}
{
  apply sequential'.
  eapply semax_post_flipped.
  eapply semax_skip.
  intros.
  apply andp_left2.
  apply normal_ret_assert_derives'.
  entailer!.
  rewrite H0 in *.
  rewrite <- H1. simpl.
  entailer!.
  apply (exp_right nil).
  apply (exp_right nullval).
  entailer!.

}

abbreviate_semax.


repeat intro_ex_semax.

forward. (*guard' = index && (value > sortedvalue);*)
admit. admit.   (* need closed lemma *)
entailer. destruct sorted_ptr; inv TC1; simpl in *.
entailer!. apply orp_right1. normalize.
entailer!. apply orp_right2.
apply prop_right.
apply eval_id_initialized with (Vint first_val); auto.

forward. (*guard = guard'*)

simpl typeof.
{
forward_while (insert_invariant sh insert_val contents)
              (insert_post sh insert_val contents).
(*pre implies invariant*)
remember (isptrb sorted_ptr).
{ destruct b; autorewrite with subst.
  + apply (exp_right nullval).
    apply (exp_right sorted_ptr).
    apply (exp_right first_val).
    apply (exp_right tail_ptr).
    apply (exp_right insert_val).
    apply (exp_right nil).
    apply (exp_right tail_vals).
    entailer.
    destruct sorted_ptr; inv Psorted_ptr.
    simpl.
    rewrite <- H1 in *.
    rewrite <- H4 in *.
    entailer!.
  + apply (exp_right nullval).
    apply (exp_right sorted_ptr).
    rewrite <- Heqb.
    apply (exp_right first_val).
    apply (exp_right nullval).
    apply (exp_right insert_val). (*whatever*)
    apply (exp_right nil).
    apply (exp_right nil).
    entailer!. rewrite <- H1 in *; auto.
}

(*guard typechecks*)
entailer.
(*invariant implies post *)
apply (exp_right prev_ptr).
apply (exp_right index_ptr).
apply (exp_right sorted_val).
apply (exp_right next_ptr).
apply (exp_right prev_val).
apply (exp_right contents_lt).
apply (exp_right contents_rest).
entailer!.
(*invariant across command *)

(*get rid of ifs because the index_ptr exists *)
eapply semax_pre with
 (PROP  (if isptrb prev_ptr
       then Forall (Igt insert_val) (contents_lt ++ [prev_val])
       else Forall (Igt insert_val) contents_lt;
      if isptrb prev_ptr
              then
               contents_lt ++ prev_val :: sorted_val :: contents_rest =
               contents
              else sorted_val :: contents_rest = contents)
      LOCAL
      (`(typed_true (typeof (Etempvar _guard tint)))
         (eval_expr (Etempvar _guard tint));
      `(eq index_ptr) (eval_id _index);
      `(eq (Vint insert_val)) (eval_id _insert_value);
      `(eq (Vint sorted_val)) (eval_id _sortedvalue);
      `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list)
           (eval_id _index) `tint
           (`(eval_binop Ogt tint tint) (eval_id _insert_value)
              (eval_id _sortedvalue))); `(eq prev_ptr) (eval_id _previous);
      if isptrb prev_ptr then `True else `(eq index_ptr) (eval_id _sorted))
      SEP  (if isptrb prev_ptr
      then
       `(lseg LS sh contents_lt) (eval_id _sorted) `prev_ptr *
       `(list_cell LS sh prev_ptr prev_val) *
       `(field_at sh t_struct_list _tail prev_ptr index_ptr)
      else emp;
           `(list_cell LS sh index_ptr sorted_val);
       `(field_at sh t_struct_list _tail index_ptr next_ptr);
       `(lseg LS sh contents_rest) `next_ptr `nullval;
      `(field_at sh t_struct_list _head) (eval_id _insert_node)
        `(Vint insert_val);
      `(field_at sh t_struct_list _tail) (eval_id _insert_node) `nullval)).
entailer. rewrite H5 in *. clear H5.
unfold logical_and_result in *.
destruct index; inv H3. destruct (Int.eq i Int.zero); inv H7.
simpl.
entailer!.
forward.  (* previous = index; *)
forward.  (* index = index -> tail; *)
(* if(index) *)
forward_if
     (EX index_val2 : elemtype LS,
      EX index_ptr2 : val,
      EX rest_index_vals : list (elemtype LS),
      EX old : val,
     PROP  (if isptrb prev_ptr
       then Forall (Igt insert_val) (contents_lt ++ [prev_val])
       else Forall (Igt insert_val) (contents_lt);
       (if (isptrb next_ptr)
        then
          if (isptrb prev_ptr)
          then contents_lt ++ prev_val :: sorted_val :: index_val2 :: rest_index_vals = contents
          else sorted_val :: index_val2 :: rest_index_vals = contents
        else
          if (isptrb prev_ptr)
          then contents_lt ++ prev_val :: sorted_val :: nil = contents
          else sorted_val :: nil = contents);
      (if(isptrb next_ptr) then
         index_val2 :: rest_index_vals = contents_rest
       else
         True))
      LOCAL  (`(eq next_ptr) (eval_id _index);
      `eq (eval_id _previous) `index0;
      `(eq index_ptr) `index0;
      `(typed_true (typeof (Etempvar _guard tint))) (eval_id _guard);
      `(eq (Vint insert_val)) (eval_id _insert_value);
      `(eq (Vint sorted_val)) `old;
      (if (isptrb next_ptr) then
        `(eq (Vint index_val2)) (eval_id _sortedvalue)
      else
        `(eq (Vint sorted_val)) (eval_id _sortedvalue));
      `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list)
           `index0 `tint
           (`(eval_binop Ogt tint tint) (eval_id _insert_value)
              `old));
if isptrb prev_ptr then `True else `(eq index_ptr) (eval_id _sorted))
      SEP  (`(list_cell LS sh) `index0 `sorted_val;
      `(field_at sh t_struct_list _tail) `index_ptr `next_ptr;
      (if isptrb prev_ptr
             then
              `(lseg LS sh contents_lt) (eval_id _sorted) `prev_ptr *
              `(list_cell LS sh prev_ptr prev_val) *
              `(field_at sh t_struct_list _tail prev_ptr index_ptr)
             else emp);
      (if (isptrb next_ptr) then
        (`(list_cell LS sh) `next_ptr `index_val2 *
         `(field_at sh t_struct_list _tail) `next_ptr `index_ptr2 *
         `(lseg LS sh rest_index_vals) `index_ptr2 `nullval)
      else `emp);
       `(field_at sh t_struct_list _head) (eval_id _insert_node)
        `(Vint insert_val);
      `(field_at sh t_struct_list _tail) (eval_id _insert_node) `nullval)).
entailer.
focus_SEP 3. apply semax_lseg_nonnull.
entailer.
intros index_val2 rest_index_vals2 index_ptr2 ?.
(*needs work, most of this should be in forward *)
(*sortedvalue = index -> head;*)
{ rewrite lift_list_cell_eq.
  apply sequential'.
  hoist_later_in_pre.
  eapply semax_post_flipped.
  eapply (semax_load_field''); try reflexivity.
  entailer!.
  entailer.
  cancel.
  intros. apply andp_left2.
  apply normal_ret_assert_derives'.
  apply (exp_left); intro old.
  apply (exp_right index_val2).
  apply (exp_right index_ptr2).
  apply (exp_right rest_index_vals2).
  apply (exp_right old).
  autorewrite with subst.
  entailer.
  destruct (eval_id _index rho); inv H4.
  simpl.
  entailer.
  cancel.
  destruct (isptrb x0); unfold subst; simpl; entailer!.
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
  entailer.
  rewrite H2 in *. simpl.
  rewrite <- H4 in *; rewrite <- H5 in *.
  simpl.
  entailer!.
  destruct (isptrb x0); auto. unfold subst. simpl.
  destruct (isptrb x0); entailer.
}

abbreviate_semax.
repeat intro_ex_semax.
rename old into old_sortedvalue.
forward. (* guard = index && (insert_value > sortedvalue); *)
admit.
admit.
go_lower.
subst. destruct index; inv TC1; simpl in *.
entailer!. apply orp_right1. normalize.
entailer!. compute. auto.
apply orp_right2. apply prop_right.
apply eval_id_initialized with (Vint index_val2); auto.

forward. (* guard' = guard *)

(*implies post*)

unfold insert_invariant. autorewrite with ret_assert.

apply (exp_right index0).
apply (exp_right next_ptr).

remember (isptrb next_ptr).
{ destruct b; autorewrite with subst.
    + remember (isptrb prev_ptr).
      destruct b; simpl PROPx;
      apply (exp_right (index_val2));
      apply (exp_right index_ptr2);
      apply (exp_right sorted_val).
        - apply (exp_right (contents_lt ++ prev_val :: nil)).
          apply (exp_right (rest_index_vals)).
          entailer. destruct_ptr. simpl.
          apply andp_right.
            * apply prop_right.
              split.
              simpl.
              repeat (rewrite Forall_app in *; auto; split; auto).
              try eapply lt_lemma; eauto.
              split.
              rewrite app_assoc_reverse. simpl. auto.
              rewrite <- H5 in *. rewrite <- H2 in *.
              auto.
            * unfold subst.
              rewrite eval_id_other; try solve [unfold _guard; unfold _sorted; congruence].
              remember ( field_at sh t_struct_list _tail (Vptr b i) index).
              rewrite Heqm at 1. cancel. rewrite Heqm.
              apply derives_trans with
              (list_cell LS sh prev_ptr prev_val *
               field_at sh t_struct_list _tail prev_ptr (Vptr b i) *
               lseg LS sh contents_lt (eval_id _sorted rho) prev_ptr *
               field_at sh t_struct_list _tail (Vptr b i) index
              ).
              cancel.
              apply @lseg_cons_right_neq.
        -  apply (exp_right (nil)).
           apply (exp_right (rest_index_vals)).
           entailer. unfold subst in H6. rewrite eval_id_other in H6.
           destruct_ptr. simpl.
           apply andp_right.
             * apply prop_right. simpl.
               split; auto.
               repeat (rewrite Forall_app; split; auto).
               eapply lt_lemma; eauto.
               split; auto. rewrite <- H5 in *. rewrite <- H2 in *.  auto.
             * cancel. rewrite <- H6. rewrite lseg_unfold. entailer.
               simpl. intuition. apply Int.eq_true.
             * unfold _guard. unfold _sorted. congruence.
    + apply (exp_right index_val2).
      apply (exp_right nullval).
      apply (exp_right sorted_val).
      remember (isptrb prev_ptr).
      destruct b. simpl PROPx.
           - apply (exp_right (contents_lt ++ [prev_val])).
             apply (exp_right nil).
             entailer!; destruct_ptr; simpl.
               * repeat (rewrite Forall_app in *; auto; split; auto).
                 try eapply lt_lemma; eauto.
               * rewrite app_assoc_reverse. auto.
               * rewrite <- H5 in *. rewrite <- H2 in *; auto.
               * auto.
               * simpl. unfold subst.
                 rewrite eval_id_other; try solve [unfold _guard; unfold _sorted; congruence].
                 remember ( field_at sh t_struct_list _tail (Vptr b i) index).
                 rewrite Heqm at 1. cancel. rewrite Heqm.
                 apply derives_trans with
                 (list_cell LS sh prev_ptr prev_val *
                  field_at sh t_struct_list _tail prev_ptr (Vptr b i) *
                  lseg LS sh contents_lt (eval_id _sorted rho) prev_ptr *
                  field_at sh t_struct_list _tail (Vptr b i) index
                 ).
                 cancel.
                 apply @lseg_cons_right_neq.
           - apply (exp_right nil).
             apply (exp_right nil).
             entailer. unfold subst in *.
             rewrite eval_id_other in H6.
             destruct_ptr; simpl.
             entailer!.
             eapply lt_lemma; eauto.
             rewrite <- H5 in *; rewrite H2 in *; auto.
             rewrite <- H6. simpl. intuition. apply Int.eq_true.
             unfold _guard, _sorted. congruence.
}

unfold insert_post.
repeat intro_ex_semax.
forward. (*insert_node -> tail = index*)
forward_if (
(PROP
    (Forall (Igt insert_val) contents_lt;
    if isptrb index_ptr
    then
      sorted_val :: contents_rest = contents
    else
      [] = contents)
    LOCAL
    (`(typed_false (typeof (Etempvar _previous (tptr t_struct_list))))
       (eval_expr (Etempvar _previous (tptr t_struct_list)));
    lift1 (typed_false (typeof (Etempvar _guard tint)))
      (eval_expr (Etempvar _guard tint)); `(eq index_ptr) (eval_id _index);
    `(eq (Vint insert_val)) (eval_id _insert_value);
    if isptrb index_ptr
    then `(eq (Vint sorted_val)) (eval_id _sortedvalue)
    else `(next_ptr = nullval);
    `eq (eval_id _guard)
      (`logical_and_result `(tptr t_struct_list) (eval_id _index)
         `tint
         (`(eval_binop Ogt tint tint) (eval_id _insert_value)
            (eval_id _sortedvalue))); `(eq prev_ptr) (eval_id _previous))
    SEP
    (if isptrb index_ptr
     then
      `(list_cell LS sh index_ptr sorted_val) *
      `(field_at sh t_struct_list _tail index_ptr next_ptr)
     else emp;
    `(lseg LS sh contents_rest) `next_ptr `nullval;
    `(field_at sh t_struct_list _head) (eval_id _insert_node)
      `(Vint insert_val);
    `(field_at sh
        (Tstruct _struct_list
           (Fcons _head tint
              (Fcons _tail (Tcomp_ptr _struct_list noattr) Fnil)) noattr)
        _tail)
      (eval_lvalue
         (Ederef (Etempvar _insert_node (tptr t_struct_list)) t_struct_list))
      (`(eval_cast (typeof (Etempvar _index (tptr t_struct_list)))
           (tptr t_struct_list))
         (eval_expr (Etempvar _index (tptr t_struct_list))))))
). (* if (previous) *)
entailer!.
{
  (*we know prev_ptr is true*)
  apply semax_pre with (
    (PROP
      (Forall (Igt insert_val) (contents_lt ++ [prev_val]);
      if isptrb index_ptr
      then
       contents_lt ++ prev_val :: sorted_val :: contents_rest = contents
       else
       contents_lt ++ [prev_val] = contents
      )
      LOCAL
      (`(typed_true (typeof (Etempvar _previous (tptr t_struct_list))))
         (eval_expr (Etempvar _previous (tptr t_struct_list)));
      lift1 (typed_false (typeof (Etempvar _guard tint)))
        (eval_expr (Etempvar _guard tint)); `(eq index_ptr) (eval_id _index);
      `(eq (Vint insert_val)) (eval_id _insert_value);
      if isptrb index_ptr
      then `(eq (Vint sorted_val)) (eval_id _sortedvalue)
      else `(next_ptr = nullval);
      `eq (eval_id _guard)
        (`logical_and_result `(tptr t_struct_list)
           (eval_id _index) `tint
           (`(eval_binop Ogt tint tint) (eval_id _insert_value)
              (eval_id _sortedvalue))); `(eq prev_ptr) (eval_id _previous))
      SEP
      (if isptrb index_ptr
       then
        `(list_cell LS sh index_ptr sorted_val) *
        `(field_at sh t_struct_list _tail index_ptr next_ptr)
       else emp;
       `(lseg LS sh contents_lt) (eval_id _sorted) `prev_ptr;
       `(list_cell LS sh prev_ptr prev_val);
       `(field_at sh t_struct_list _tail prev_ptr index_ptr);
       `(lseg LS sh contents_rest) `next_ptr `nullval;
       `(field_at sh t_struct_list _head) (eval_id _insert_node)
        `(Vint insert_val);
       `(field_at sh
          (Tstruct _struct_list
             (Fcons _head tint
                (Fcons _tail (Tcomp_ptr _struct_list noattr) Fnil)) noattr)
          _tail)
        (eval_lvalue
           (Ederef (Etempvar _insert_node (tptr t_struct_list)) t_struct_list))
        (`(eval_cast (typeof (Etempvar _index (tptr t_struct_list)))
             (tptr t_struct_list))
           (eval_expr (Etempvar _index (tptr t_struct_list))))))
  ).
remember (eval_id _sorted).
entailer!;
 destruct (eval_id _previous rho); try inversion H3; simpl in *; auto.
forward. (* previous->tail = insert_node; *)
forward. (* return sorted *)
entailer.
destruct index; inv TC1.
simpl in *.
cancel. fold t_struct_list.
rewrite H5. fold nullval.
apply derives_trans with
(lseg LS sh (contents_lt ++ [prev_val]) sorted insert_node *
 lseg LS sh contents_rest nullval nullval *
 field_at sh t_struct_list _head insert_node (Vint insert_value) *
 field_at sh t_struct_list _tail insert_node nullval).
remember (field_at sh t_struct_list _tail insert_node nullval).
rewrite Heqm at 1.
cancel.
rewrite Heqm.
apply derives_trans with
( list_cell LS sh (eval_id _previous rho) prev_val *
  field_at sh t_struct_list _tail (eval_id _previous rho) insert_node *
  lseg LS sh contents_lt sorted (eval_id _previous rho) *
  field_at sh t_struct_list _tail insert_node nullval
). cancel.
apply @lseg_cons_right_neq.
rewrite <- list_cell_eq.

Lemma insert_value_right : forall contents insert_value,
Forall (Igt insert_value) contents ->
insert insert_value contents = contents ++ [insert_value].
induction contents; intros.
auto.
simpl in *. inv H. remember (Int.lt a insert_value).
destruct b. simpl. rewrite IHcontents; auto.
unfold Igt in H2. clear - H2 Heqb.
 replace (Int.lt a insert_value) with
  (Int.cmp Clt a insert_value) in * by auto.
  rewrite <- Int.swap_cmp in Heqb. simpl swap_comparison in Heqb. congruence.
Qed.

apply insert_value_right in H1. subst. rewrite H1.

apply derives_trans with
(list_cell LS sh insert_node insert_value *
 field_at sh t_struct_list _tail insert_node nullval *
 lseg LS sh (contents_lt ++ [prev_val]) sorted insert_node).
cancel. rewrite lseg_eq. normalize. simpl. auto.
apply @lseg_cons_right_null.
simpl in *.
fold t_struct_list.

rewrite H6 in H4.
clear H6. unfold logical_and_result, typed_false in H4.
simpl in H4. rewrite <- H5 in H4. remember (Int.lt sorted_val insert_value).
destruct b0; inv H4.

Lemma insert_value_result : forall contents_lt insert_value next_value contents_rest,
Forall (Igt insert_value) (contents_lt) ->
false = Int.lt next_value insert_value ->
insert insert_value (contents_lt ++ next_value :: contents_rest) =
contents_lt ++ insert_value :: next_value :: contents_rest.
induction contents_lt;
intros. repeat rewrite app_nil_l.
simpl. rewrite <- H0. auto.
auto.
inv H. simpl.
remember (Int.lt a insert_value).
destruct b. simpl. rewrite IHcontents_lt; auto.
unfold Igt in *. clear - H3 Heqb.
 replace (Int.lt a insert_value) with
  (Int.cmp Clt a insert_value) in * by auto.
  rewrite <- Int.swap_cmp in Heqb. simpl swap_comparison in Heqb. congruence.
Qed.



rewrite app_cons.
rewrite insert_value_result.

apply derives_trans with
( list_cell LS sh (Vptr b i) sorted_val *
   field_at sh t_struct_list _tail (Vptr b i) next_ptr *
   lseg LS sh (contents_lt ++ [prev_val]) sorted insert_node *
   lseg LS sh contents_rest next_ptr nullval *
   field_at sh t_struct_list _head insert_node (Vint insert_value) *
   field_at sh t_struct_list _tail insert_node (Vptr b i)
).
remember (field_at sh t_struct_list _tail insert_node (Vptr b i)).
rewrite Heqm at 1.
cancel.
rewrite Heqm.
eapply derives_trans with
( list_cell LS sh (eval_id _previous rho) prev_val *
  field_at sh t_struct_list _tail (eval_id _previous rho) insert_node *
  lseg LS sh contents_lt sorted (eval_id _previous rho) *
  field_at sh t_struct_list _tail insert_node (Vptr b i)).
cancel.
apply @lseg_cons_right_neq.
apply derives_trans with
(  lseg LS sh (contents_lt ++ [prev_val]) sorted insert_node *
   lseg LS sh (sorted_val :: contents_rest) (Vptr b i) nullval *
   field_at sh t_struct_list _head insert_node (Vint insert_value) *
   field_at sh t_struct_list _tail insert_node (Vptr b i)).
cancel.
rewrite lseg_unfold with (contents :=sorted_val :: contents_rest).
entailer!. apply (exp_right next_ptr).
entailer!.
rewrite <- list_cell_eq.
apply derives_trans with
( lseg LS sh (contents_lt ++ [prev_val]) sorted insert_node *
   lseg LS sh (insert_value :: sorted_val :: contents_rest) insert_node nullval ).
cancel.
rewrite lseg_unfold with (contents := insert_value :: sorted_val :: contents_rest).
entailer.
apply (exp_right (Vptr b i)).
entailer!. destruct insert_node; inv Pinsert_node.
unfold ptr_eq. simpl. auto.
admit. (*believable, need lseg append lemma*) auto. auto.
}
(*skip*)
{
  apply sequential'.
  eapply semax_post_flipped.
  eapply semax_skip.
  intros. apply andp_left2.
  apply normal_ret_assert_derives'.
  entailer!; rewrite H2 in *; simpl in *; auto.
  unfold typed_false, nullval. auto.
}
abbreviate_semax.
forward.
entailer.
destruct index; inv TC1; simpl in *.
fold t_struct_list. subst. simpl.
fold nullval.
Check lseg_neq.
rewrite lseg_neq with (s := [insert_value]).
unfold lseg_cons. apply andp_right. destruct_ptr.
entailer.
apply (exp_right insert_value). apply (exp_right nil).
apply (exp_right nullval).
entailer!.
apply now_later.
destruct insert_node; inv Pinsert_node; unfold ptr_neq; auto.

fold t_struct_list.
subst.
rewrite <- (app_nil_l (sorted_val :: contents_rest)).
rewrite insert_value_result. simpl.
apply derives_trans with
(  lseg LS sh (sorted_val :: contents_rest) (Vptr b i) nullval *
   field_at sh t_struct_list _head insert_node (Vint insert_value) *
   field_at sh t_struct_list _tail insert_node (Vptr b i)
).
cancel.
rewrite lseg_unfold with (contents := (sorted_val :: contents_rest)).
entailer. apply (exp_right next_ptr).
entailer!. rewrite <- list_cell_eq.
apply derives_trans with
(  list_cell LS sh insert_node insert_value *
   field_at sh t_struct_list _tail insert_node (Vptr b i) *
lseg LS sh (sorted_val :: contents_rest) (Vptr b i) nullval
) .
cancel.
rewrite lseg_unfold with (contents := (insert_value :: sorted_val :: contents_rest)).
entailer. apply (exp_right (Vptr b i)).
entailer!. destruct insert_node; intuition.
constructor.
rewrite H6 in *.
clear H6.
rewrite <- H5 in *.
simpl in H4.
unfold typed_false, logical_and_result in *.
simpl in H4. destruct (Int.lt sorted_val insert_value); inv H4; auto.
}
Qed.

Lemma sorted_sound : forall xs, sorted xs = true <-> LocallySorted Zle xs.
intuition.
+  induction xs.
   - constructor.
   - simpl in H.
     destruct xs.
     * constructor.
     * constructor. simpl in H. apply IHxs. remember (a <=? z)%Z. destruct b.
       simpl. apply H. congruence.
       apply Z.leb_le. destruct (a <=? z)%Z; congruence.
+  induction xs.
   - auto.
   - simpl. destruct xs. auto.
     simpl. remember (a <=? z)%Z. destruct b.
     inv H. intuition.
     inv H. apply Z.leb_le in H4. congruence.
Qed.

Lemma insert_sorted : forall x xs, LocallySorted Zle xs -> LocallySorted Zle (insert x xs).
Proof.
intros.
induction xs.
+ constructor.
+ simpl. remember (x <=? a)%Z.
    destruct b.
  - constructor. auto. apply Z.leb_le. auto.
  - inv H.
      * simpl. constructor. constructor.
        apply Z.leb_le. remember (a <=? x)%Z. destruct b. auto.
        symmetry in Heqb, Heqb0. rewrite Z.leb_gt in *. omega.
      * simpl. remember ((x <=? b)%Z). destruct b0.
          repeat (constructor; simpl). auto. symmetry in Heqb.
          apply Z.leb_le. auto. symmetry in Heqb. rewrite Z.leb_gt in *.
          omega.
          constructor. simpl in IHxs. rewrite <- Heqb0 in IHxs. auto. auto.
Qed.

Lemma insertion_sort_sorted : forall xs, LocallySorted Zle (insertion_sort xs).
Proof.
induction xs.
  + constructor.
  + simpl. apply insert_sorted.  auto.

Qed.

Lemma insert_permutation : forall x xs , Permutation (x::xs) (insert x xs).
Proof.
intros.
induction xs.
+ auto.
+ simpl. destruct (x <=? a)%Z.
  - auto.
  - eapply perm_trans. eapply perm_swap. apply perm_skip. apply IHxs.
Qed.

Lemma insert_permutation2 : forall x xs x2, Permutation xs x2 ->
Permutation (x::xs) (insert x x2).
Proof.
intros.
induction xs.
destruct x2. auto. apply Permutation_nil in H. inv H.
apply Permutation_sym.
eapply perm_trans. eapply Permutation_sym. apply insert_permutation.
apply perm_skip. apply Permutation_sym. auto.
Qed.

Lemma insertion_sort_permutation : forall xs, Permutation xs (insertion_sort xs).
Proof.
intros.
induction xs.
+ auto.
+ simpl. apply insert_permutation2. auto.
Qed.

Lemma insertion_sort_sound : forall xs, LocallySorted Zle (insertion_sort xs) /\ Permutation xs (insertion_sort xs).
Proof.
intros.
split. apply insertion_sort_sorted.
apply insertion_sort_permutation.
Qed.
*)