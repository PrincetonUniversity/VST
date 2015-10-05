Require Import floyd.proofauto.
Require Import progs.merge.
Require Import progs.list_dt. Import LsegSpecial.

Definition CompSpecs' : compspecs.
Proof. make_compspecs1 prog. Defined.
Instance CompSpecs : compspecs.
Proof. make_compspecs2 CompSpecs'. Defined.

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
  unfold data_at', offset_val, mapsto; simpl.
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
Proof.
  unfold list_cell, withspacer, field_at; simpl.
  f_equal. f_equal. f_equal.
  apply prop_ext.
  unfold field_compatible, legal_nested_field, legal_field in *; simpl.
  intuition. repeat constructor.
  unfold field_type; simpl.
  unfold default_val. simpl.
  apply prop_ext; intuition.
Qed.

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
name a__ _a.
name b__ _b.
name va__ _va.
name vb__ _vb.
name x__ _x.
name ret_ _ret.
name cond__ _cond.
start_function.
forward.

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
* (* First branch of the if: [a_ <> nullval] *)
forward.
Exists (if Val.eq b_ nullval then Int.zero else Int.one)
 a b (@nil int) a_ b_ ret_ ret_.
 simpl map. rewrite @lseg_nil_eq.
Time entailer!.  (* 1.65 sec *)
 destruct b__; inv TC; simpl.
  rewrite if_true by auto;  intuition discriminate.
  rewrite if_false by (intro Hx; inv Hx); intuition discriminate.
* (* a_ = null *)
forward.
Exists Int.zero a b (@nil int) a_ b_ ret_ ret_.
 simpl map. rewrite @lseg_nil_eq.
entailer!. intuition.
* (* finally the [condition] is given the value of the temporary variable 67. *)
(* TODO-LTAC here [normalize] should probably do [apply
   extract_exists_pre] for us. *)
rename a into init_a.
rename b into init_b.
clear a_ b_.
Intros cond a b merged a_ b_ c_ begin.
 forward.


(* The loop *)
forward_while (merge_invariant _cond sh init_a init_b ret_)
  [[[[[[[cond0 a0] b0] merged0] a_0] b_0] c_0] begin0].
+ (* Loop: precondition => invariant *)
 Exists cond a b merged a_ b_ c_ begin; entailer!.
+ (* Loop: condition has nice format *)
now entailer!.
(*+ (* Loop: invariant + neg condition => post condition *)
 entailer!.
 Exists Int.zero a0 b0 merged0 a__ b__ c_0 begin0.
(* apply exp_right with (Int.zero, a0, b0, merged0, a__, b__, c_0, begin0).*)
 simpl.
 entailer!.
*)
+ (* Loop body preserves invariant *)
clear - SH HRE H1 H2.
rename cond0 into cond, a0 into a, b0 into b, merged0 into merged,
 a_0 into a_, b_0 into b_, c_0 into c_, begin0 into begin.
assert (a_ <> nullval) by intuition.
assert (b_ <> nullval) by intuition.
clear H2.
drop_LOCAL 4%nat. (* cond *)
clear cond HRE.
rewrite lseg_unfold.
destruct a as [|va a']; simpl.
  (* [a] cannot be empty *)
  normalize. now intuition.
normalize.
intros a_'.
normalize.
(* Now the command [va = a->head] can proceed *)
rewrite list_cell_field_at.
forward.

rewrite lseg_unfold with (v1:=b_).
destruct b as [|vb b']; simpl.
  (* [b] cannot be empty *)
  normalize; now intuition.
normalize.
intros b_'.
normalize.
clear H2 H3.  (* redundant *)

(* [vb = b->head] *)
rewrite list_cell_field_at.
forward.


(* The main if : we split at the same time the Coq expression B and
the actual if. *)
simpl in H1.
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

(* the effect of [*x=a] on the invariant depends on whether
merged is nil or not *)
destruct merged as [|hmerge tmerge].

(* first iteration of the loop: [merged=nil] *)
forward.

(* COMMAND : [x = &(a->tail)] *)

forward.

(* COMMAND : [a = a -> tail] *)

forward VAR. subst VAR.
Exists a' (vb::b') [va] a_' b_ a_ a_.
name a__ _a.
name b__ _b.
name va__ _va.
name vb__ _vb.
name x__ _x.
name ret__ _ret.
name cond__ _cond.
{

rewrite !@lseg_nil_eq.
rewrite (lseg_unfold LS _ _ b_).
Time entailer!. (* 24.7 sec *)
(*Time normalize. (* 5.6 sec *)*)
Exists b_'.
rewrite list_cell_field_at.
Time entailer!.  (* 12.6 sec *)
unfold data_at.
unfold_field_at 3%nat.
Time entailer!. (* 3.9 sec *) 
}

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
rewrite <- app_assoc. simpl app.
rewrite <- H1. clear H1.
destruct (merged ++ [va]) eqn:?.
destruct merged; inv Heql.
forget (i::l) as merged''; clear i l.
Time entailer!.  (* 42.3 sec *)
rewrite butlast_snoc. rewrite last_snoc.
rewrite (snoc merged) at 3 by auto.
rewrite map_app. simpl map.
match goal with |- ?A |-- _ => set (PQR := A);
  unfold data_at; unfold_field_at 1%nat;
  subst PQR
end.
normalize.
rewrite prop_true_andp by (repeat simplify_value_fits; auto).
match goal with |- ?A * ?B * ?C * ?D * ?E * ?F * ?G * ?H |-- _ =>
 apply derives_trans with ((B * A * H * G) * (C * D * E * F));
  [cancel | ]
end.
eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | ].
assert (LCR := lseg_cons_right_neq LS sh (map Vint (butlast merged)) begin (Vint (last merged)) c_ _id a_);
simpl in LCR. rewrite list_cell_field_at in LCR. apply LCR; auto.
rewrite @lseg_cons_eq.
normalize.
apply exp_right with b_'.
rewrite list_cell_field_at.
entailer!.

(* other branch of the if: contradiction *)
rewrite H2 in HeqB; inversion HeqB.

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
  now entailer!; intuition.
  
  (* b_ <> null *)
  Exists Int.one a b merged a_ (Vptr b0 i) c_ begin. 
  entailer!. intuition discriminate.
(* a_ = null *)
forward.
Exists Int.zero a b merged a_ b_ c_ begin.
entailer!; intuition.

(* setting value in cond *)
clear -SH.
Intros cond a b merged a_ b_ c_ begin.
forward.
Exists (cond, a, b, merged, a_, b_, c_, begin).
now entailer.

(* * Other case: vb < va || Warning, below is mostly copy-pasted from above*)

(* first branch of the if: contradiction *)
rewrite H2 in HeqB; inversion HeqB.

(* COMMAND : [*x = b] *)
(* forward fails so we transform the SEP condition to get something accepted by [forward] *)

(* the effect of [*x=b] on the invariant depends on whether
merged is nil or not *)
destruct merged as [|hmerge tmerge].

(* first iteration of the loop: [merged=nil] *)
forward.

(* COMMAND : [x = &(b->tail)] *)

forward.

(* COMMAND : [b = b -> tail] *)

forward VAR. subst VAR.
Exists (va::a') b' [vb] a_ b_' b_ b_.
name a__ _a.
name b__ _b.
name va__ _va.
name vb__ _vb.
name x__ _x.
name ret__ _ret.
name cond__ _cond.
simpl map. rewrite @lseg_cons_eq.
entailer!.
Exists a_'.
entailer!.
rewrite list_cell_field_at.
unfold data_at.
unfold_field_at 5%nat.
entailer!.

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
forward.

(* COMMAND : [b = b -> tail] *)
forward VAR. subst VAR.
Exists (va::a') b' (merged ++ [vb]) a_ b_' b_ begin.
destruct (merged ++ [vb]) eqn:?. destruct merged; inv Heql.
forget (i::l) as merged''; clear i l; subst merged''.
rewrite app_ass.
Time entailer!. (* 22 sec *)
rewrite butlast_snoc. rewrite last_snoc.
rewrite @lseg_cons_eq.
Time entailer!.  (* 17 sec *)
Exists a_'.
Time entailer!. (* 13 sec *)
pattern merged at 3; rewrite snoc by auto.
rewrite map_app. simpl map.
assert (LCR := lseg_cons_right_neq LS sh (map Vint (butlast merged)) begin (Vint (last merged)) c_ _id b_).
simpl in LCR. rewrite list_cell_field_at in LCR.
match goal with |- ?A |-- _ => set (PQR := A);
  unfold data_at; unfold_field_at 1%nat;
  subst PQR
end.
rewrite prop_true_andp.
normalize.
match goal with |- ?A * ?B * ?C * ?D * ?E * ?F |-- _ =>
 apply derives_trans with ((B * A * F * D) * (C * E)); [cancel | ]
end.
eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | ].
apply LCR; auto.
rewrite list_cell_field_at.
cancel.
normalize. repeat simplify_value_fits; auto.

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
  now entailer!; intuition.
  
  (* b_ <> null *)
  Exists Int.one a b merged a_ (Vptr b0 i) c_ begin. 
  entailer!; intuition discriminate.

(* a_ = null *)
forward.
Exists Int.zero a b merged a_ b_ c_ begin.
entailer!; intuition.

(* setting value in cond *)
clear -SH.
Intros cond a b merged a_ b_ c_ begin.
forward.
Exists (cond, a, b, merged, a_, b_, c_, begin).
simpl @fst; simpl @snd.
now entailer.

(* After the while *)
+
clear a b merged a_ b_ c_ cond H H0 begin.
rename cond0 into cond, a0 into a, b0 into b, merged0 into merged,
 a_0 into a_, b_0 into b_, c_0 into c_, begin0 into begin.
subst cond.
assert (a_ = nullval \/ b_ = nullval) by (clear - H2; intuition).
clear H2.

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
assert_PROP (b_ = nullval /\ b = []).
  entailer!; intuition. destruct b; inv H;  auto.
revert POSTCONDITION; destruct H2; subst b_ b; intro.

destruct merged as [|hmerge tmerge].

(* when a <> [] and merged = [] *)
forward.
Exists a (@nil int) (@nil int) a_ c_ begin.
rewrite merge_nil_r in *.
unfold data_at.
now entailer!.

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
rewrite merge_nil_r in *.
entailer!.
unfold field_type; simpl.
unfold data_at; unfold_field_at 3%nat. 
(* @Andrew: same bug here, rewrite does not work directly but it does after
a pose *)
pose proof (field_at_data_at sh t_struct_list [StructField _tail] a__ c_) as R.
fold _tail.
rewrite R.
entailer!.
repeat simplify_value_fits; auto.  (* why didn't entailer! do this? *)

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
now entailer!.

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
entailer!.
unfold field_type; simpl.
unfold data_at; unfold_field_at 3%nat.
pose proof (field_at_data_at sh t_struct_list [StructField _tail] b__ c_) as R.
fold _tail.
rewrite R.
entailer!.
repeat simplify_value_fits; auto.

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
Exists x__; entailer!.
Exists temp_; entailer!.
rewrite H; auto.

(* when merged <> [] *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.
name a__ _a; name b__ _b; name va__ _va; name vb__ _vb; name x__ _x; name ret__ _ret; name cond__ _cond; name temp_ _temp.
forward.
Exists ret_; entailer.
Exists temp_; entailer.

(* to match the specification from the invariant, we split it into three parts: *)

assert (AP : forall M1 R1 M2 M3 M13 M R, R1 |-- R -> M1 * M3 |-- M13
-> M2 * M13 |-- M -> M1 * R1 * M2 * M3 |-- M * R).
  clear; intros.
  apply derives_trans with (M * R1); cancel; auto.
  now apply derives_trans with (M2 * M13); cancel; auto.
apply AP with (lseg LS sh (Vint (last merged) :: map Vint (merge a b)) c_ nullval); clear AP.
cancel.

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
