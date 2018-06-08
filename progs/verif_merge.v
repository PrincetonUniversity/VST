Require Import VST.floyd.proofauto.
Require Import VST.progs.merge.
Require Import VST.progs.list_dt. Import LsegSpecial.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Instance LS: listspec _list _tail (fun _ _ => emp).
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
     SEP (lseg LS sh (map Vint a) a_ nullval;
            lseg LS sh (map Vint b) b_ nullval)
  POST [ tlist ]
    EX pt:val,
     PROP ()
     LOCAL (temp ret_temp pt)
     SEP (lseg LS sh (map Vint (merge a b)) pt nullval).

Definition Gprog : funspecs :=   ltac:(with_library prog [ merge_spec ]).

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
  remember (h ++ [t]) as l; destruct l; auto.
  destruct h; inversion Heql.
Qed.

Lemma butlast_snoc h t : butlast (h ++ [t]) = h.
Proof.
  induction h; simpl; auto.
  rewrite IHh.
  remember (h ++ [t]) as l; destruct l; auto.
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

Definition merge_invariant _cond sh init_a init_b v_ret :=
 (EX cond: int, EX a: list int, EX b: list int, EX merged: list int,
  EX a_: val, EX b_: val, EX c_: val, EX begin: val,
  PROP (merge init_a init_b = merged ++ merge a b;
        cond = Int.zero <-> (a_ = nullval \/ b_ = nullval)
       )
  LOCAL (temp _a a_;
         temp _b b_;
         temp _x (if merged then v_ret else field_address (Tstruct _list noattr) [StructField _tail] c_);
         lvar _ret tlist v_ret;
         temp _cond (Vint cond)
        )
  SEP (lseg LS sh (map Vint a) a_ nullval;
         lseg LS sh (map Vint b) b_ nullval;
         data_at Tsh tlist (if merged then Vundef else begin) v_ret;
         lseg LS sh (map Vint (butlast merged)) begin c_;
         if merged then emp else data_at sh t_struct_list (Vint (last merged), Vundef) c_
   ))%assert.

Lemma merge_nil_r a : merge a nil = a.
Proof.
  induction a; simpl; auto.
Qed.

Lemma merge_nil_l a : merge nil a = a.
Proof.
  induction a; simpl; auto.
Qed.

(* TODO-LTAC - is this a missing lemma of the theory of [list_cell]?*)
Lemma list_cell_field_at sh (v : val) p :
  list_cell LS sh v p = field_at sh list_struct [StructField _head] v p.
Proof.
  unfold list_cell, withspacer, field_at; simpl.
  f_equal.
  apply ND_prop_ext.
  unfold field_compatible, legal_nested_field, legal_field in *; simpl.
  intuition. repeat constructor.
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
    (ls : listspec list_structid list_link list_token) (hd mid : val)
    (ct1 ct2 : list (elemtype ls)) :
  lseg ls sh ct1 hd mid * lseg ls sh ct2 mid nullval
  |-- lseg ls sh (ct1 ++ ct2) hd nullval.
Proof.
  intros.
  assert (AP : forall P Q, P * emp |-- Q * emp -> P |-- Q).
    intros.
    eapply derives_trans; [ eapply derives_trans; [ | eassumption] | ]; cancel.
  apply AP; clear AP.
  apply (@list_append _ _ _ _ sh ls _ _ _ _ _ (fun _ => emp)).
  intros; unfold lseg_cell.
  rewrite (entail_rewrite _ _ (field_at_ptr_neq_null _ _ _ _ _)).
  rewrite field_at_isptr.
  entailer.
Qed.

Lemma body_merge: semax_body Vprog Gprog f_merge merge_spec.
Proof.
start_function.
forward.

(* TODO-LTAC (vague) the first assignment [condition = ..] is
   converted into an if so we need to establish the postcondition
   ourselves.  The postcondition is only a slight change from the one
   we currently have (with some more PROP and LOCAL).  Maybe we should
   have a tactic like [forward_if] to which we say "the postcondition
   is like our precondition with this change".
   (maybe [apply semax_post]?)
 *)

(* Current command: assigment [condition = a != NULL && b != NULL].
   It is converted into an if, so we need to establish the
   postcondition ourselves *)
match goal with [|-context[Sset ?tempvar _] ] =>
   forward_if (merge_invariant tempvar sh a b v_ret)
end.
* (* First branch of the if: [a_ <> nullval] *)
forward.
Exists (if Val.eq b_ nullval then Int.zero else Int.one)
 a b (@nil int) a_ b_ v_ret v_ret.
 simpl map. rewrite @lseg_nil_eq.
Time entailer!.  (* 1.65 sec *)
 destruct b_; inv PNb_; simpl.
  rewrite if_true by auto;  intuition discriminate.
  rewrite if_false by (intro Hx; inv Hx); intuition discriminate.
* (* a_ = null *)
forward.
Exists Int.zero a b (@nil int) a_ b_ v_ret v_ret.
 simpl map. rewrite @lseg_nil_eq.
entailer!. intuition.
* (* finally the [condition] is given the value of the temporary variable 67. *)
(* TODO-LTAC here [normalize] should probably do [apply
   extract_exists_pre] for us. *)
rename a into init_a.
rename b into init_b.
clear a_ b_.
unfold merge_invariant.
Intros cond a b merged a_ b_ c_ begin.
 forward.

(* The loop *)
forward_while (merge_invariant _cond sh init_a init_b v_ret).

(*  [[[[[[[cond0 a0] b0] merged0] a_0] b_0] c_0] begin0]. *)
+ (* Loop: precondition => invariant *)
 Exists cond a b merged a_ b_ c_ begin; entailer!.
+ (* Loop: condition has nice format *)
now entailer!.
+ (* Loop body preserves invariant *)
clear - SH HRE H1 H2.
rename cond0 into cond, a0 into a, b0 into b, merged0 into merged,
 a_0 into a_, b_0 into b_, c_0 into c_, begin0 into begin.
assert (a_ <> nullval) by intuition.
assert (b_ <> nullval) by intuition.
clear H2.
drop_LOCAL 4%nat; clear cond HRE.
rewrite lseg_unfold.
destruct a as [|va a']; simpl.
  (* [a] cannot be empty *)
  Intros; now intuition.
Intros a_'.
normalize.
(* Now the command [va = a->head] can proceed *)
rewrite list_cell_field_at.
forward.

rewrite lseg_unfold with (v1:=b_).
destruct b as [|vb b']; simpl.
  (* [b] cannot be empty *)
  Intros; now intuition.
Intros b_'.
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
  EX a: list int, EX b: list int, EX merged: list int,
  EX a_: val, EX b_: val, EX c_: val, EX begin: val,
  PROP (merge init_a init_b = merged ++ merge a b)
  LOCAL (temp _a a_;
         temp _b b_;
         temp _x (if merged then v_ret else field_address (Tstruct _list noattr) [StructField _tail] c_);
         lvar _ret tlist v_ret
        )
  SEP (lseg LS sh (map Vint a) a_ nullval;
         lseg LS sh (map Vint b) b_ nullval;
         data_at Tsh tlist (if merged then Vundef else begin) v_ret;
         lseg LS sh (map Vint (butlast merged)) begin c_;
         if merged then emp else data_at sh t_struct_list (Vint (last merged), Vundef) c_
   ))%assert.
(* after the [forward_if], 3 new goals *)
(* the effect of [*x=a] on the invariant depends on whether merged is nil or not *)
destruct merged as [|hmerge tmerge].
(* first iteration of the loop: [merged=nil] *)
forward. (* COMMAND : [*x = a] *)
forward. (* COMMAND : [x = &(a->tail)] *)
forward. (* COMMAND : [a = a -> tail] *)
Exists a' (vb::b') [va] a_' b_ a_ a_.
{

rewrite !@lseg_nil_eq.
rewrite (lseg_unfold LS _ _ b_).
Time entailer!. (* 24.7 sec -> 10.16 sec*)
Exists b_'.
rewrite list_cell_field_at.
unfold_data_at 1%nat.
Time entailer!.  (* 12.6 -> 3.2 sec *)
}

(* we have now finished the case merged=nil, proceeding to the other case *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.

(* Command: *x = a *)
forward.

forward. (* COMMAND : [x = &(a->tail)] *)
forward. (* COMMAND : [a = a -> tail] *)
Exists a' (vb::b') (merged ++ [va]) a_' b_ a_ begin.
rewrite <- app_assoc. simpl app.
rewrite <- H1. clear H1.
destruct (merged ++ [va]) eqn:?; [ now destruct merged; inv Heql | ].
forget (i::l) as merged''; clear i l.
Time entailer!.  (* 42.3 sec -> 13.9 sec -> 11.4 sec *)
rewrite butlast_snoc. rewrite last_snoc.
rewrite (snoc merged) at 3 by auto.
rewrite map_app. simpl map.
unfold_data_at 1%nat.
unfold_data_at 1%nat.
match goal with |- ?B * ?C * ?D * ?E * ?F * ?G * (?H * ?A) |-- _ =>
 apply derives_trans with ((H * A * G * C) * (B * D * E * F));
  [cancel | ]
end.
eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | ].
assert (LCR := lseg_cons_right_neq LS sh (map Vint (butlast merged)) begin (Vint (last merged)) c_ a_' a_);
simpl in LCR. rewrite list_cell_field_at, emp_sepcon in LCR. apply LCR; auto.
rewrite @lseg_cons_eq.
Exists b_'.
rewrite list_cell_field_at.
entailer!.

(* other branch of the if: contradiction *)
rewrite H2 in HeqB; inversion HeqB.
(* After the if, putting boolean value into "cond" *)
clear -SH.
(* TODO-LTAC I had no idea why this command failed -- we should tell "remove existential first", maybe *)
Intros a b merged a_ b_ c_ begin.
match goal with [|-context[Sset ?tempvar _] ] =>
forward_if (merge_invariant tempvar sh init_a init_b v_ret)
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
unfold merge_invariant.
Intros cond a b merged a_ b_ c_ begin.
forward.
Exists (cond, a, b, merged, a_, b_, c_, begin).
now entailer!.

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
forward. (* COMMAND : [x = &(b->tail)] *)
forward. (* COMMAND : [b = b -> tail] *)
Exists (va::a') b' [vb] a_ b_' b_ b_.
simpl map. rewrite @lseg_cons_eq.
Exists a_'.
rewrite list_cell_field_at.
entailer!.
unfold_data_at 1%nat.
entailer!.

(* we have now finished the case merged=nil, proceeding to the other case *)
remember (hmerge :: tmerge) as merged.
assert (Hm: merged <> []) by congruence.
clear hmerge tmerge Heqmerged.

(* Command: *x = b *)
forward.

(* COMMAND : [x = &(b->tail)] *)
forward.

(* COMMAND : [b = b -> tail] *)
forward.
Exists (va::a') b' (merged ++ [vb]) a_ b_' b_ begin.
destruct (merged ++ [vb]) eqn:?. destruct merged; inv Heql.
forget (i::l) as merged''; clear i l; subst merged''.
rewrite app_ass.
Time entailer!. (* 22 sec -> 17.33 sec *)
rewrite butlast_snoc. rewrite last_snoc.
rewrite @lseg_cons_eq.
Exists a_'.
Time entailer!. (* 14.3 sec *)
pattern merged at 3; rewrite snoc by auto.
rewrite map_app. simpl map.
assert (LCR := lseg_cons_right_neq LS sh (map Vint (butlast merged)) begin (Vint (last merged)) c_ b_' b_).
simpl in LCR. rewrite emp_sepcon, list_cell_field_at in LCR.
unfold_data_at 1%nat.
unfold_data_at 1%nat.
match goal with |- ?B * ?C * ?D * ?E * (?F * ?A) |-- _ =>
 apply derives_trans with ((F * A * E * D) * (B * C)); [cancel | ]
end.
eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | ].
apply LCR; auto.
rewrite list_cell_field_at.
cancel.

(* After the if, putting boolean value into "cond" *)
clear -SH.
Intros a b merged a_ b_ c_ begin.
match goal with [|-context[Sset ?tempvar _] ] =>
forward_if (merge_invariant tempvar sh init_a init_b v_ret)
end.
forward.

(* First branch of the if: [a_ <> nullval] *)
assert_PROP (is_pointer_or_null b_); [ now entailer! | ].
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
unfold merge_invariant.
Intros cond a b merged a_ b_ c_ begin.
forward.
Exists (cond, a, b, merged, a_, b_, c_, begin).
now entailer!.

(* After the while *)
+
clear a b merged a_ b_ c_ cond H H0 begin.
rename cond0 into cond, a0 into a, b0 into b, merged0 into merged,
 a_0 into a_, b_0 into b_, c_0 into c_, begin0 into begin.
subst cond.
assert (a_ = nullval \/ b_ = nullval) by (clear - H2; intuition).
clear H2.

forward_if (
  EX a: list int, EX b: list int, EX merged: list int,
  EX ab_: val, EX c_: val, EX begin: val,
  PROP (merge init_a init_b = merged ++ merge a b)
  LOCAL (temp _a a_;
         temp _b b_;
         temp _x (if merged then v_ret else field_address (Tstruct _list noattr) [StructField _tail] c_);
         lvar _ret tlist v_ret
        )
  SEP (lseg LS sh (map Vint (merge a b)) ab_ nullval;
         data_at Tsh tlist (if merged then ab_ else begin) v_ret;
         lseg LS sh (map Vint (butlast merged)) begin c_;
         if merged then emp else data_at sh t_struct_list (Vint (last merged), ab_) c_
   ))%assert.
 - (* when a <> [] *)
   assert_PROP (b_ = nullval /\ b = []).
    entailer!; intuition. destruct b; inv H;  auto.
    revert POSTCONDITION; destruct H2; subst b_ b; intro.
    destruct merged as [|hmerge tmerge].
     (* when a <> [] and merged = [] *)
    forward.
   Exists a (@nil int) (@nil int) a_ c_ begin.
   rewrite merge_nil_r in *.
    unfold data_at.
    entailer!. apply derives_refl. 
   (* when a <> [] and merged <> [] *)
remember (hmerge :: tmerge) as merged.
   assert (Hm: merged <> []) by congruence.
   clear hmerge tmerge Heqmerged.
   forward.
   Exists a (@nil int) merged a_ c_ begin.
   destruct merged; [congruence|].
   match goal with [ H: ?x :: merged <> [] |- _ ] => remember (x :: merged) as merged'
   end.
   clear Heqmerged' merged.
   rewrite merge_nil_r in *.
   entailer!.
   apply derives_refl.
 -  (* when a = [] *)
  assert_PROP (a = []). {
    destruct a; [ apply prop_right; reflexivity | ].
    simpl map; rewrite lseg_unfold.
    subst a_; entailer!.
    elim H6; clear; intuition.
  }
 subst a.

 destruct merged as [|hmerge tmerge].

  (* when a = [] and merged = [] *)
  forward.
  Exists (@nil int) b (@nil int) b_ c_ begin.
  entailer!. apply derives_refl.

  (* when a = [] and merged <> [] *)
remember (hmerge :: tmerge) as merged.
  assert (Hm: merged <> []) by congruence.
  clear hmerge tmerge Heqmerged.
  forward.
  Exists (@nil int) b merged b_ c_ begin.
  destruct merged; [congruence|].
  match goal with [ H: ?x :: merged <> [] |- _ ] => remember (x :: merged) as merged'
  end.
  clear Heqmerged' merged.
  entailer!.
  apply derives_refl.
 - (* temp = ret *)
 clear -SH.
 Intros a b merged ab_ c_ begin.
 forward.
 now destruct merged; entailer!.

 (* return statement *)
 forward.
 destruct merged as [|hmerge tmerge].
 (* when merged = [] *)
 assert (begin = c_) by intuition. subst c_.
 Exists ab_; entailer!.
 rewrite H; auto. apply derives_refl.

 (* when merged <> [] *)
 remember (hmerge :: tmerge) as merged.
 assert (Hm: merged <> []) by congruence.
 clear hmerge tmerge Heqmerged.
 Exists begin; entailer.

 (* to match the specification from the invariant, we split it into three parts: *)

  assert (AP : forall M1 R1 M2 M3 M13 M R, R1 |-- R -> M1 * M3 |-- M13
            -> M2 * M13 |-- M -> M1 * R1 * M2 * M3 |-- M * R). {
   clear; intros.
   apply derives_trans with (M * R1); cancel; auto.
   now apply derives_trans with (M2 * M13); cancel; auto.
  }
 apply AP with (lseg LS sh (Vint (last merged) :: map Vint (merge a b)) c_ nullval); clear AP.
 cancel.

 (* part 2 : we join the middle element and the right part of the list *)
 idtac.
 rewrite (lseg_unfold LS _ _ c_).
 Exists ab_; entailer!.
 rewrite list_cell_field_at.
 unfold_data_at 1%nat.
 simpl. cancel.

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
Time Qed. (* 199 sec -> 331 sec *)
