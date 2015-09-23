Require Import floyd.proofauto.
Require Import progs.list_dt. Import LsegSpecial.
Require Import progs.merge.
Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  
Local Open Scope logic.

Instance LS: listspec _list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.

Definition t_struct_list := Tstruct _list noattr.

(* Specification of the function *)

Fixpoint merge l1 :=
  match l1 with
  | nil => (fun l2 => l2)
  | h1 :: t1 =>
      let fix merge_aux l2 :=
        match l2 with
        | nil => l1
        | h2 :: t2 =>
           if Int.cmp Cle h1 h2
           then h1 :: merge t1 l2
           else h2 :: merge_aux t2
        end
      in merge_aux
  end.

Definition tlist := tptr t_struct_list.

Definition merge_spec :=
 DECLARE _merge
  WITH sh : share, a : list int, b : list int, a_ : val, b_ : val
  PRE  [ _a OF tlist,  _b OF tlist ]
     PROP (writable_share sh)
     LOCAL (temp _a a_; temp _b b_)
     SEP (`(lseg LS sh (map Vint a) a_ nullval);
          `(lseg LS sh (map Vint b) b_ nullval))
  POST [ tlist ]
    EX pt:val,
     PROP ()
     LOCAL (temp ret_temp pt) 
     SEP (`(lseg LS sh (map Vint (merge a b)) pt nullval)).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := merge_spec :: nil.

Fixpoint last (l : list int) :=
  match l with
    | [] => Int.zero
    | [a] => a
    | _::l => last l
  end.

Fixpoint butlast (l : list int) :=
  match l with
    | [] => []
    | [a] => []
    | a::l => a :: butlast l
  end.

Lemma last_snoc h t : last (h ++ [t]) = t.
Proof.
  induction h; simpl; auto.
  rewrite IHh.
  remember (h ++ [t]) as l; if_tac; auto.
  destruct h; inversion Heql.
Qed.

Lemma butlast_snoc h t : butlast (h ++ [t]) = h.
Proof.
  induction h; simpl; auto.
  rewrite IHh.
  remember (h ++ [t]) as l; if_tac; auto.
  destruct h; inversion Heql.
Qed.

Lemma fold_data_at sh t v : field_at sh t [] v = data_at sh t v. Proof. reflexivity. Qed.
Lemma butlast_fold h t : match t with [] => [] | _ :: _ => h :: butlast t end = butlast (h :: t). Proof. auto. Qed.
Lemma last_fold h t : match t with [] => h | _ :: _ => last t end = last (h :: t). Proof. auto. Qed.

Lemma snoc (l : list int) : l <> [] -> l = butlast l ++ [last l].
Proof.
  intros E; destruct l as [|f l]; [elim E; auto | clear E].
  revert f; induction l as [|h l]; intros f; simpl; auto.
  f_equal; apply IHl.
Qed.

Definition telem := Tint I32 Signed noattr.

Definition merge_invariant _cond sh init_a init_b ret_ :=
  @exp (environ -> mpred) _ _ (fun cond : int =>
  @exp (environ -> mpred) _ _ (fun a : list int =>
  @exp (environ -> mpred) _ _ (fun b : list int =>
  @exp (environ -> mpred) _ _ (fun merged : list int =>
  @exp (environ -> mpred) _ _ (fun a_ : val =>
  @exp (environ -> mpred) _ _ (fun b_ : val =>
  @exp (environ -> mpred) _ _ (fun c_ : val =>    (* dummy pointer if merged=[] *)
  @exp (environ -> mpred) _ _ (fun begin : val => (* c_            if merged=[] *)
  PROP (merge init_a init_b = merged ++ merge a b;
        cond = Int.zero <-> (a_ = nullval \/ b_ = nullval)
       )
  LOCAL (temp _a a_;
         temp _b b_;
         temp _x (if merged then ret_ else field_address (Tstruct _list noattr) [StructField _tail] c_);
         lvar _ret tlist ret_;
         temp _cond (Vint cond)
        )
  SEP (`(lseg LS sh (map Vint a) a_ nullval);
       `(lseg LS sh (map Vint b) b_ nullval);
       `(data_at Tsh tlist (if merged then Vundef else begin) ret_);
       `(lseg LS sh (map Vint (butlast merged)) begin c_);
       `(if merged then emp else data_at sh t_struct_list (Vint (last merged), Vundef) c_)
))))))))).

Ltac Intro x :=
  try rewrite exp_andp1;
  try rewrite exp_andp2;
  apply extract_exists_pre; intro x.

Tactic Notation "Intros" := repeat (let x := fresh "x" in Intro x).
Tactic Notation "Intros" simple_intropattern(x0) :=
 Intro x0.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) :=
 Intro x0; Intro x1.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2) :=
 Intro x0; Intro x1; Intro x2.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) :=
 Intro x0; Intro x1; Intro x2; Intro x3.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10)
 simple_intropattern(x11) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; Intro x11.

Ltac Exists' a :=
  try rewrite exp_andp1;
  try rewrite exp_andp2;
  apply exp_right with a.

Tactic Notation "Exists" constr(x0) := Exists' x0.

Tactic Notation "Exists" constr(x0) constr(x1) :=
 Exists' x0; Exists x1.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) :=
 Exists x0; Exists' x1; Exists' x2.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) constr(x12) :=
 Exists' x0; Exists' x1; Exists x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11; Exists' x12.

Lemma merge_nil_r a : merge a nil = a.
Proof.
  induction a; simpl; auto.
Qed.

Lemma merge_nil_l a : merge nil a = a.
Proof.
  induction a; simpl; auto.
Qed.

Lemma lvar_align_compatible _a t p :
  local (lvar _a t p) = local (lvar _a t p) && !!align_compatible t p.
Proof.
  apply pred_ext; entailer; intuition.
  unfold lvar in *.
  remember (Map.get (ve_of rho) _a) as X.
  destruct X as [[p1 t1]|]; simpl in *; try tauto.
  if_tac in H; try tauto; subst.
  exists 0; auto.
Qed.

Lemma lvar_align_compatible_param P Q _a t p :
  P |-- local (lvar _a t p) ->
  (align_compatible t p -> P |-- Q) ->
  (P |-- Q).
Proof.
  intros.
  assert_PROP (align_compatible t p).
  eapply derives_trans; eauto.
  rewrite lvar_align_compatible; entailer.
  tauto.
Qed.

Lemma mapsto_data_at sh v p : 
  readable_share sh ->
  isptr p ->
  size_compatible tlist p ->
  align_compatible tlist p ->
  (v <> Vundef -> is_pointer_or_null v) ->
  mapsto sh tlist p v = data_at sh tlist v p.
Proof.
  intros SH P S A Iv.
  unfold data_at, field_at, at_offset, offset_val.
  destruct p; try inversion P.
  unfold tlist, t_struct_list, tptr in *; simpl in *.
  rewrite int_add_repr_0_r.
  unfold data_at', mapsto', offset_val; simpl.
  if_tac; [ | exfalso; tauto ].
  apply pred_ext; entailer.
  unfold field_compatible; simpl.
  unfold legal_alignas_type, nested_pred, local_legal_alignas_type, legal_cosu_type; simpl.
  unfold nested_pred, local_legal_alignas_type, legal_cosu_type; simpl.
  entailer.
Qed.

(* TODO-LTAC - is this a missing lemma of the theory of [list_cell]?*)
Lemma list_cell_field_at sh (v : val) p :
  list_cell LS sh v p = field_at sh list_struct [StructField _head] v p.
Admitted.
(* (* the compute induces an 'out of memory' *)
Proof.
  unfold list_cell, withspacer, field_at; simpl.
  apply pred_ext; entailer; apply prop_right;
  unfold field_compatible, legal_nested_field, legal_field in *; simpl.
  intuition.
  repeat constructor.
  intuition.
  simpl.
  compute; if_tac; tauto.
Qed.
*)
Lemma entail_rewrite A B : A |-- B -> A = A && B.
Proof.
  intros I.
  apply pred_ext.
  now apply andp_right; auto.
  now apply andp_left1; auto.
Qed.

Lemma list_append_null (cs : compspecs)
    (list_structid list_link : ident) (sh : share)
    (ls : listspec list_structid list_link) (hd mid : val)
    (ct1 ct2 : list (elemtype ls)) :
  lseg ls sh ct1 hd mid * lseg ls sh ct2 mid nullval
  |-- lseg ls sh (ct1 ++ ct2) hd nullval.
Proof.
  intros.
  assert (AP : forall P Q, P * emp |-- Q * emp -> P |-- Q).
    intros.
    eapply derives_trans; [ eapply derives_trans; [ | eassumption] | ]; cancel.
  apply AP; clear AP.
  apply (@list_append _ _ _ sh ls _ _ _ _ _ (fun _ => emp)).
  intros; unfold lseg_cell.
  rewrite (entail_rewrite _ _ (field_at_ptr_neq_null _ _ _ _ _)).
  rewrite field_at_isptr.
  entailer.
Qed.

Lemma body_merge: semax_body Vprog Gprog f_merge merge_spec.
Proof.
start_function.
name a__ _a.
name b__ _b.
name va__ _va.
name vb__ _vb.
name x__ _x.
name ret__ _ret.
name cond__ _cond.

(* TODO-LTAC
  - [fixup_local_var] should recognize [var_block] instead of requiring it
    unfolded.
  - [simpl_stackframe_of] should in fact do this work as well *)
simpl_stackframe_of.
unfold var_block.
fixup_local_var.
intro ret_.
normalize.
simpl.

(* replacing the memory_block with a data_at .. Vundef *)
forward.
replace_SEP 0 (`(data_at Tsh tlist Vundef ret_)).
assert_PROP (isptr ret_).
  entailer.
assert_PROP (size_compatible tlist ret_); [admit|].
(* [now rewrite (memory_block_size_compatible _ tlist);[entailer|reflexivity]|]. *)

apply lvar_align_compatible_param with _ret tlist ret_; [ entailer | intros H2 ].
rewrite (memory_block_mapsto_ _ tlist); auto.

rewrite <-mapsto_data_at; auto. 2:tauto.
unfold mapsto_.
(* now *) if_tac; [entailer | auto with *].

rewrite <-seq_assoc
(* remove the nested [Ssequence] introduced as the same time as the if *).

(* TODO-LTAC (vague) the first assignment [condition = ..] is
   converted into an if so we need to establish the postcondition
   ourselves.  The postcondition is only a slight change from the one
   we currently have (with some more PROP and LOCAL).  Maybe we should
   have a tactic like [forward_if] to which we say "the postcondition
   is like our precondition with this change".
   (maybe [apply semaret_post]?)
 *)

(* Current command: assigment [condition = a != NULL && b != NULL].
   It is converted into an if, so we need to establish the
   postcondition ourselves *)

match goal with [|-context[Sset ?tempvar _] ] =>
forward_if (merge_invariant tempvar sh a b ret_)
end.

(* First branch of the if: [a_ <> nullval] *)
forward.
assert_PROP (is_pointer_or_null b_); [ now entailer | ].
destruct b_; inversion H1; simpl force_val.
  (* b_ is null *)
  Exists Int.zero a b (@nil int) a_ nullval ret_ ret_.
  entailer.
  now entailer; apply andp_right; [ apply prop_right; intuition | cancel ].
  
  (* b_ <> null *)
  Exists Int.one a b (@nil int) a_ (Vptr b0 i) ret_ ret_.
  now entailer; apply andp_right; [ apply prop_right; intuition | cancel ].

(* a_ = null *)
forward.
Exists Int.zero a b (@nil int) a_ b_ ret_ ret_.
now entailer; apply andp_right; [ apply prop_right; intuition | cancel ].

(* finally the [condition] is given the value of the temporary variable 67. *)
(* TODO-LTAC here [normalize] should probably do [apply
   extract_exists_pre] for us. *)
rename a into init_a.
rename b into init_b.
clear a_ b_.
Intros cond a b merged a_ b_ c_ begin.
forward.

(* The loop *)

(* TODO-LTAC here [forward_while (`TT) (`TT) VARS] fails after a
normalize and I don't know why, so I use [semax_while] manually. *)

apply semax_pre with (merge_invariant _cond sh init_a init_b ret_).

(* Loop: precondition => invariant *)
Exists cond a b merged a_ b_ c_ begin.
entailer.

(* choosing the post condition *)
apply semax_seq with (merge_invariant _cond sh init_a init_b ret_ &&
  local (temp _cond (Vint Int.zero))).

apply semax_while.

(* Loop: type is bool *)
reflexivity.

(* Loop: condition has nice format *)
now entailer!.

(* Loop: invariant + neg condition => post condition *)
rewrite overridePost_normal'.
entailer.
apply prop_right.
destruct (eval_id _cond rho);
match goal with [ H : typed_false _ _ |- _] => inversion H end.
rewrite negb_false_iff in *.
match goal with [ H : Int.eq _ _ = _ |- _] => apply int_eq_e in H; subst end.
reflexivity.

(* Loop: body preserves invariant *)
clear -SH.
unfold merge_invariant at 1.
(* TODO-LTAC above I had
[local && EX x : _, ....] to which I do [normalize] to get
[EX x : _, local && ....] to which I do [apply extract_exists_pre] to get
[forall x, semax Delta (local && ....)] to which I do [intro x] to get
[local && ....] with [x] above the line, but then .... is of the for [EX y : _,..]
so I need to do again normalize, in total 7 times, which is very slow

UPDATE: I (JM) defined myself "Intros x y z" to get around this quickly
*)
Intros cond a b merged a_ b_ c_ begin.
normalize. renormalize.
assert_PROP (cond <> Int.zero).
  entailer.
  apply prop_right.
  apply int_eq_false_e, negb_true_iff; auto.
  unfold tint, typed_true, strict_bool_val in H2.
  inversion H2; auto.

assert_PROP (a_ <> nullval /\ b_ <> nullval).
  now apply prop_right; intuition.

destruct a as [|va a'].
  (* [a] cannot be empty *)
  rewrite lseg_unfold; simpl.
  normalize.
  now intuition.
  (* apply ptr_eq_e in H3. *)
  (* now intuition. *)

rewrite lseg_unfold; simpl.
normalize.
intros a_'.
normalize.
(* removing "(typed_true tint) (eval_id _cond)" from LOCAL -- maybe this bit is useless, but I should keep the ltac *)
match goal with
  [ |- context [PROPx nil (LOCALx (?a :: ?b) ?c) ] ] =>
    apply semax_pre with (PROPx nil (LOCALx b c))
end; [ entailer | ].

(* Now the command [va = a->head] can proceed *)
rewrite list_cell_field_at.
abbreviate_semax.
forward.

destruct b as [|vb b'].
  (* [b] cannot be empty *)
  rewrite lseg_unfold; simpl.
  normalize.
  (* apply ptr_eq_e in H5. *)
  now intuition.

rewrite (lseg_unfold LS _ (map Vint (vb :: b'))); simpl.
normalize.
intros b_'.
normalize.

(* [vb = b->head] *)
rewrite list_cell_field_at.
forward.

(* removing cond *)
match goal with
  [ |- context [PROPx nil (LOCALx (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: _) ?g) ] ] =>
  apply semax_pre with (PROPx nil (LOCALx (a :: b :: c :: d :: e :: f :: nil) g))
end; [ entailer | ].
clear cond H0 H1.

(* The main if : we split at the same time the Coq expression B and
the actual if. *)

simpl in H.
remember (negb (Int.lt vb va)) as B; destruct B ;
forward_if (
  @exp (environ -> mpred) _ _ (fun a : list int =>
  @exp (environ -> mpred) _ _ (fun b : list int =>
  @exp (environ -> mpred) _ _ (fun merged : list int =>
  @exp (environ -> mpred) _ _ (fun a_ : val =>
  @exp (environ -> mpred) _ _ (fun b_ : val =>
  @exp (environ -> mpred) _ _ (fun c_ : val =>
  @exp (environ -> mpred) _ _ (fun begin : val =>
  PROP (merge init_a init_b = merged ++ merge a b)
  LOCAL (temp _a a_;
         temp _b b_;
         temp _x (if merged then ret_ else field_address (Tstruct _list noattr) [StructField _tail] c_);
         lvar _ret tlist ret_
        )
  SEP (`(lseg LS sh (map Vint a) a_ nullval);
       `(lseg LS sh (map Vint b) b_ nullval);
       `(data_at Tsh tlist (if merged then Vundef else begin) ret_);
       `(lseg LS sh (map Vint (butlast merged)) begin c_);
       `(if merged then emp else data_at sh t_struct_list (Vint (last merged), Vundef) c_)
))))))))).

(* after the [forward_if], 3 new goals *)

(* COMMAND : [*x = a] *)
(* forward fails so we transform the SEP condition to get something accepted by [forward] *)

match goal with [ |- context [Sassign (Ederef ?e1 ?t) ?e2]] =>
set (E1:=e1); set (E2:=e2); set (T:=t) end.
abbreviate_semax.

(* the effect of [*x=a] on the invariant depends on whether
merged is nil or not *)
destruct merged as [|hmerge tmerge].

(* first iteration of the loop: [merged=nil] *)
forward.
(* @Andrew: with data_at, forward manages to work, instead of this with mapsto.
replace_SEP 6 (`(data_at Tsh tlist Vundef) (eval_expr Delta E1)); [ now entailer | ].
forward.
replace_SEP 6 (`(data_at Tsh tlist Vundef a_ x_)); [ now entailer | ].
*)

(* COMMAND : [x = &(a->tail)] *)

forward.

(* COMMAND : [a = a -> tail] *)

forward VAR.
Exists a' (vb::b') [va] a_' b_ a_ a_.
subst VAR.
name a__ _a.
name b__ _b.
name va__ _va.
name vb__ _vb.
name x__ _x.
name ret__ _ret.
name cond__ _cond.
entailer.

apply andp_right.
  apply prop_right.
    split.
      unfold field_address; simpl.
      if_tac; tauto.
      apply ptr_eq_refl; auto.

rewrite (lseg_unfold LS _ _ b__).
entailer.
Exists b_'.
rewrite list_cell_field_at.
apply andp_right; [now clear; entailer|].
cancel.
normalize.
unfold data_at.
unfold_field_at 5%nat.
cancel.
apply andp_right. apply prop_right.  now compute; if_tac; tauto.
now cancel.

(* we have now finished the case merged=nil, proceeding to the other case *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.

(* Command: *x = a *)
unfold data_at.
unfold_field_at 6%nat.
normalize.
(* we replace [field_at ...tail _c] with [data_at .. (field_adress ...tail _c)] for forward*)
focus_SEP 1.
rewrite field_at_data_at.
forward.
(* we put back the [field_at ...tail _c] *)
rewrite <-field_at_offset_zero.
rewrite fold_data_at.
rewrite <-field_at_data_at.

(* COMMAND : [x = &(a->tail)] *)
forward.

(* COMMAND : [a = a -> tail] *)
forward VAR.
subst VAR.
Exists a' (vb::b') (merged ++ [va]) a_' b_ a_ begin.
apply andp_right.  rewrite H; apply prop_right; simpl; intuition.  rewrite app_ass; auto.
apply andp_left2.
assert (N: merged ++ [va] <> []) by (destruct merged; try inversion Hm; subst; simpl; congruence).
remember (merged ++ [va]) as merged''.
if_tac; [congruence|].
match goal with
[ H: ?x :: merged'' <> [] |- _ ] => remember (x :: merged'') as merged'
end.
clear Heqmerged' merged''.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond.
entailer.
repeat rewrite butlast_fold, last_fold in *.
match goal with [ H: _ = eval_id _x _ |- _ ] => rewrite <- H end.
apply andp_right. now apply prop_right; unfold field_address; simpl; if_tac; [ reflexivity | tauto ].
cancel.

Ltac print t := let x := fresh "PRINT" in pose (x := t).
Ltac subst_entail :=
  match goal with [ H : ?big |-- ?small |- _ |-- ?rem * ?small ] =>
  apply derives_trans with (big * rem); cancel; try assumption
  end.

assert (AP: forall M1 M2 M3 M B1 B2 B3 B A1 A2 A, (A1 * A2 |-- A) ->
(B1 * B2 * B3 |-- B) -> (M1 * M2 * M3 * A2 |-- M * A2) -> M1 * M2 * B1 *
B2 * B3 * A1 * A2 * M3 |-- B * M * A).
  clear; intros.
  apply derives_trans with (B1 * B2 * B3 * M * A); cancel; auto.
  apply derives_trans with (A1 * (M * A2)); [ | cancel; auto ].
  apply derives_trans with (A1 * (M1 * M2 * M3 * A2)); [ cancel | ].
  now apply sepcon_derives; auto.
(* TODO-LTAC decision procedure for entailment *)

apply AP; clear AP a__ b__ va__ vb__ x__ ret__ cond__.

(* new last cell of merged *)
unfold data_at.
unfold_field_at 3%nat.
rewrite last_snoc.
cancel.
apply andp_right.  now apply prop_right; compute; if_tac; tauto.
now cancel.

(* put the b list back together *)
rewrite (lseg_unfold LS _ (Vint vb :: map Vint b')).
rewrite exp_andp2.
Exists b_'.
rewrite list_cell_field_at.
now entailer.

(* appending old last cell to merged list *)
rewrite butlast_snoc; auto; [].
rewrite (snoc merged) at 3; auto; [].
rewrite map_app.
simpl map.

remember (map Vint (butlast merged)) as l.
remember (Vint (last merged)) as x.

eapply derives_trans; [ | apply (lseg_cons_right_neq LS sh l begin x c_ (eval_id _a rho) a_) ; auto with *].
simpl.
rewrite list_cell_field_at.
now cancel.

(* other branch of the if: contradiction *)
rewrite H0 in HeqB.
inversion HeqB.

(* After the if, putting boolean value into "cond" *)
clear -SH.
(* TODO-LTAC I had no idea why this command failed -- we should tell "remove existential first", maybe *)
Intros a b merged a_ b_ c_ begin.
match goal with [|-context[Sset ?tempvar _] ] =>
forward_if (merge_invariant tempvar sh init_a init_b ret_)
end.
forward.

(* First branch of the if: [a_ <> nullval] *)
assert_PROP (is_pointer_or_null b_); [ now entailer | ].
destruct b_; inversion H1; simpl force_val.
  (* b_ is null *)
  Exists Int.zero a b merged a_ nullval c_ begin.
  now entailer; apply prop_right; intuition.
  
  (* b_ <> null *)
  Exists Int.one a b merged a_ (Vptr b0 i) c_ begin. 
  entailer.
  apply prop_right; intuition. discriminate. discriminate.

(* a_ = null *)
forward.
Exists Int.zero a b merged a_ b_ c_ begin.
entailer. apply prop_right; intuition.

(* setting value in cond *)
clear -SH.
Intros cond a b merged a_ b_ c_ begin.
forward.
Exists cond a b merged a_ b_ c_ begin.
now entailer.



(* * Other case: vb < va || Warning, below is mostly copy-pasted from above*)

(* first branch of the if: contradiction *)
rewrite H0 in HeqB.
inversion HeqB.


(* COMMAND : [*x = b] *)
(* forward fails so we transform the SEP condition to get something accepted by [forward] *)

match goal with [ |- context [Sassign (Ederef ?e1 ?t) ?e2]] =>
set (E1:=e1); set (E2:=e2); set (T:=t) end.
abbreviate_semax.

(* the effect of [*x=b] on the invariant depends on whether
merged is nil or not *)
destruct merged as [|hmerge tmerge].

(* first iteration of the loop: [merged=nil] *)
forward.
(* @Andrew: with data_at, forward manages to work, instead of this with mapsto.
replace_SEP 6 (`(data_at Tsh tlist Vundef) (eval_expr Delta E1)); [ now entailer | ].
forward.
replace_SEP 6 (`(data_at Tsh tlist Vundef a_ x_)); [ now entailer | ].
*)

(* COMMAND : [x = &(b->tail)] *)

forward.

(* COMMAND : [b = b -> tail] *)

forward VAR.
Exists (va::a') b' [vb] a_ b_' b_ b_.
subst VAR.
name a__ _a.
name b__ _b.
name va__ _va.
name vb__ _vb.
name x__ _x.
name ret__ _ret.
name cond__ _cond.
entailer.

apply andp_right.
  apply prop_right.
    split.
      unfold field_address; simpl.
      if_tac; tauto.
      apply ptr_eq_refl; auto.

rewrite (lseg_unfold LS _ _ a__).
entailer.
Exists a_'.
rewrite list_cell_field_at.
apply andp_right; [now clear; entailer|].
cancel.
normalize.
unfold data_at.
unfold_field_at 5%nat.
cancel.
apply andp_right. now apply prop_right; compute; if_tac; tauto.
now cancel.

(* we have now finished the case merged=nil, proceeding to the other case *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.

(* Command: *x = b *)
unfold data_at.
unfold_field_at 6%nat.
normalize.
(* we replace [field_at ...tail _c] with [data_at .. (field_adress ...tail _c)] for forward*)
focus_SEP 1.
rewrite field_at_data_at.
forward.
(* we put back the [field_at ...tail _c] *)
rewrite <-field_at_offset_zero.
rewrite fold_data_at.
rewrite <-field_at_data_at.

(* COMMAND : [x = &(b->tail)] *)
forward VAR.
subst VAR.

(* COMMAND : [b = b -> tail] *)
forward VAR.
subst VAR.
Exists (va::a') b' (merged ++ [vb]) a_ b_' b_ begin.
apply andp_right.  rewrite H; apply prop_right; simpl; intuition.  rewrite app_ass; auto.
apply andp_left2.
assert (N: merged ++ [vb] <> []) by (destruct merged; try inversion Hm; subst; simpl; congruence).
remember (merged ++ [vb]) as merged''.
if_tac; [congruence|].
match goal with
[ H: ?x :: merged'' <> [] |- _ ] => remember (x :: merged'') as merged'
end.
clear Heqmerged' merged''.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond.
entailer.
repeat rewrite butlast_fold, last_fold in *.
match goal with [ H: _ = eval_id _x _ |- _ ] => rewrite <- H end.
apply andp_right. now apply prop_right; unfold field_address; simpl; if_tac; [ reflexivity | tauto ].
cancel.

assert (AP: forall M1 M2 M3 M B1 B2 B A1 A2 A3 A, (B1 * B2 |-- B) ->
(A1 * A2 * A3 |-- A) -> (M1 * M2 * M3 * B2 |-- M * B2) -> M1 * M2 * B1
* B2 * A1 * A2 * A3 * M3 |-- A * M * B).
  clear; intros.
  apply derives_trans with (M * B * A1 * A2 * A3); cancel; auto.
  apply derives_trans with (B1 * (M * B2)); [|cancel; auto].
  apply derives_trans with (B1 * (M1 * M2 * M3 * B2)); [cancel|].
  now apply sepcon_derives; auto.

apply AP; clear AP a__ b__ va__ vb__ x__ ret__ cond__.

(* new last cell of merged *)
unfold data_at.
assert (merge init_a init_b = merged ++ vb :: merge (va :: a') b') as H'
by (clear -H; rewrite H; now auto); clear H; rename H' into H.
unfold_field_at 3%nat.
rewrite last_snoc.
cancel.
apply andp_right. apply prop_right.  now compute; if_tac; tauto.
now cancel.

(* put the a list back together *)
rewrite (lseg_unfold LS _ (Vint va :: map Vint a')).
rewrite exp_andp2.
Exists a_'.
rewrite list_cell_field_at.
now entailer.

(* appending old last cell to merged list *)
rewrite butlast_snoc; auto; [].
rewrite (snoc merged) at 3; auto; [].
rewrite map_app.
simpl map.

remember (map Vint (butlast merged)) as l.
remember (Vint (last merged)) as x.

eapply derives_trans; [ | apply (lseg_cons_right_neq LS sh l begin x c_ (eval_id _b rho) b_) ; auto with *].
simpl.
rewrite list_cell_field_at.
now cancel.

(* After the if, putting boolean value into "cond" *)
clear -SH.
Intros a b merged a_ b_ c_ begin.
match goal with [|-context[Sset ?tempvar _] ] =>
forward_if (merge_invariant tempvar sh init_a init_b ret_)
end.
forward.

(* First branch of the if: [a_ <> nullval] *)
assert_PROP (is_pointer_or_null b_); [ now entailer | ].
destruct b_; inversion H1; simpl force_val.
  (* b_ is null *)
  Exists Int.zero a b merged a_ nullval c_ begin.
  now entailer; apply prop_right; intuition.
  
  (* b_ <> null *)
  Exists Int.one a b merged a_ (Vptr b0 i) c_ begin. 
  entailer.
  apply prop_right; intuition. discriminate. discriminate.

(* a_ = null *)
forward.
Exists Int.zero a b merged a_ b_ c_ begin.
entailer. apply prop_right; intuition.

(* setting value in cond *)
clear -SH.
Intros cond a b merged a_ b_ c_ begin.
forward.
Exists cond a b merged a_ b_ c_ begin.
now entailer.


(* After the while *)
abbreviate_semax.
unfold merge_invariant.
clear -SH.
Intros cond a b merged a_ b_ c_ begin.
rewrite (andp_comm _ (local (temp _cond (Vint Int.zero)))).
rewrite insert_local.

forward_if (
  @exp (environ -> mpred) _ _ (fun a : list int =>
  @exp (environ -> mpred) _ _ (fun b : list int =>
  @exp (environ -> mpred) _ _ (fun merged : list int =>
  @exp (environ -> mpred) _ _ (fun ab_ : val =>
  @exp (environ -> mpred) _ _ (fun c_ : val =>
  @exp (environ -> mpred) _ _ (fun begin : val =>
  PROP (merge init_a init_b = merged ++ merge a b)
  LOCAL (temp _a a_;
         temp _b b_;
         temp _x (if merged then ret_ else field_address (Tstruct _list noattr) [StructField _tail] c_);
         lvar _ret tlist ret_
        )
  SEP (`(lseg LS sh (map Vint (merge a b)) ab_ nullval);
       `(data_at Tsh tlist (if merged then ab_ else begin) ret_);
       `(lseg LS sh (map Vint (butlast merged)) begin c_);
       `(if merged then emp else data_at sh t_struct_list (Vint (last merged), ab_) c_)
)))))))).

(* when a <> [] *)
assert_PROP (b_ = nullval).
  now entailer; apply prop_right; intuition.
subst b_.

assert_PROP (b = []).
  destruct b; [ apply prop_right; reflexivity | ].
  simpl map; rewrite lseg_unfold.
  entailer.
  discriminate.
subst b.

destruct merged as [|hmerge tmerge].

(* when a <> [] and merged = [] *)
forward.
Exists a (@nil int) (@nil int) a_ c_ begin.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond.
rewrite merge_nil_r in *.
unfold data_at.
now entailer.

(* when a <> [] and merged <> [] *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.
unfold data_at.
unfold_field_at 2%nat.
normalize.
(* we replace [field_at ...tail _c] with [data_at .. (field_adress ...tail _c)] for forward*)
focus_SEP 1.
rewrite field_at_data_at.
forward.
Exists a (@nil int) merged a_ c_ begin.
if_tac; [congruence|].
match goal with
[ H: ?x :: merged <> [] |- _ ] => remember (x :: merged) as merged'
end.
clear Heqmerged' merged.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond.
entailer.
unfold field_type; simpl.
rewrite merge_nil_r in *.
unfold_field_at 5%nat.
cancel.
(* @Andrew: same bug here, rewrite does not work directly but it does after
a pose *)

pose proof (field_at_data_at sh t_struct_list [StructField _tail] a__ c_) as R.
fold _tail.
rewrite R.
apply andp_right. apply prop_right.  now compute; if_tac; tauto.
now cancel.

(* when a = [] *)
assert_PROP (a = []).
  destruct a; [ apply prop_right; reflexivity | ].
  simpl map; rewrite lseg_unfold.
  subst a_; entailer.
  elim H3; clear; intuition.
subst a.

destruct merged as [|hmerge tmerge].

(* when a = [] and merged = [] *)
forward.
Exists (@nil int) b (@nil int) b_ c_ begin.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond.
now entailer.


(* when a = [] and merged <> [] *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.
unfold data_at.
unfold_field_at 2%nat.
normalize.
focus_SEP 1.
rewrite field_at_data_at.
forward.
Exists (@nil int) b merged b_ c_ begin.
if_tac; [congruence|].
match goal with
[ H: ?x :: merged <> [] |- _ ] => remember (x :: merged) as merged'
end.
clear Heqmerged' merged.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond.
entailer.
unfold field_type; simpl.
unfold_field_at 5%nat.
cancel.
pose proof (field_at_data_at sh t_struct_list [StructField _tail] b__ c_) as R.
fold _tail.
rewrite R.
apply andp_right. apply prop_right.  now compute; if_tac; tauto.
now cancel.

(* temp = ret *)
clear -SH.
Intros a b merged ab_ c_ begin.
forward.
now destruct merged; entailer.

(* return statement *)
destruct merged as [|hmerge tmerge].

(* when merged = [] *)
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond; name temp_ _temp.
forward.
Exists temp_; entailer.
apply sepcon_derives.

now simpl in H; rewrite <-H; cancel.

simpl_stackframe_of.
rewrite var_block_data_at_; try auto with *.
change (data_at Tsh tlist temp_ x__ |-- data_at_ Tsh tlist (eval_lvar _ret tlist rho)).
rewrite (lvar_eval_lvar _ _ _ _ H1).
now apply field_at_field_at_.

(* when merged <> [] *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond; name temp_ _temp.
forward.
Exists temp_; entailer.

(* to match the specification from the invariant, we split it into three parts: *)

assert (AP : forall M1 R1 M2 M3 M13 M R, R1 |-- R -> M1 * M3 |-- M13
-> M2 * M13 |-- M -> M1 * R1 * M2 * M3 |-- M * R).
  clear; intros.
  apply derives_trans with (M * R1); cancel; auto.
  now apply derives_trans with (M2 * M13); cancel; auto.
apply AP with (lseg LS sh (Vint (last merged) :: map Vint (merge a b)) c_ nullval); clear AP.


(* part 1: we deal with the stackframe *)
simpl_stackframe_of.
rewrite var_block_data_at_; try auto with *.
change (data_at Tsh tlist temp_ ret_ |-- data_at_ Tsh tlist (eval_lvar _ret tlist rho)).
rewrite (lvar_eval_lvar _ _ _ _ H1).
apply field_at_field_at_.

(* part 2 : we join the middle element and the right part of the list *)
idtac.
rewrite (lseg_unfold LS _ _ c_).
Exists ab_; entailer.
apply andp_right.
unfold data_at.
(* TODO-LTAC entailer should see that data_at ... _c implies that _c is not null*)
rewrite (entail_rewrite _ _ (@field_at_ptr_neq_null CompSpecs sh t_struct_list [] _ _)).
now entailer.

rewrite list_cell_field_at.
unfold data_at.
unfold_field_at 1%nat.
entailer.
now cancel.

(* part 3 : left part of the list *)
rewrite H.
replace (merged ++ merge a b)
with (butlast merged ++ (last merged :: merge a b)).
rewrite map_app.
apply list_append_null.
clear -Hm.
change (butlast merged ++ ([last merged] ++ merge a b) = merged ++ merge a b).
rewrite <-app_ass.
now rewrite <-snoc; auto.
Qed.
