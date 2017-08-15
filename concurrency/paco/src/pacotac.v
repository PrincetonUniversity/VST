Require Import JMeq.
Require Import VST.concurrency.paco.src.hpattern.
Require Export VST.concurrency.paco.src.paconotation.

(** * Tactic support for [paco] library

    This file defines tactics for converting the conclusion to the right form so
    that the accumulation lemmas can be usefully applied. These tactics are used
    in both internal and external approaches.

    Our main tactic, [pcofix], is defined at the end of the file and
    works for predicates of arity up to 14.
*)

(** ** Internal tactics *)

Inductive _paco_mark := _paco_mark_cons.

Inductive _paco_foo := _paco_foo_cons.

Definition _paco_id {A} (a : A) : A := a.

Lemma paco_eq_JMeq: forall A (a b: A), a = b -> _paco_id (JMeq a b).
Proof. intros; subst; apply JMeq_refl. Defined.

Lemma paco_JMeq_eq: forall (A : Type) (x y : A), _paco_id (JMeq x y) -> _paco_id (x = y).
Proof. intros; apply JMeq_eq; auto. Defined.

Ltac simplJM :=
  repeat match goal with [H: ?x |- _] =>
    match x with
    | _paco_id (JMeq _ _) => apply paco_JMeq_eq in H
    | _paco_id (?a = _) => unfold _paco_id in H; subst a
    end
  end.

Ltac hrewrite_last e H := let x := fresh "_paco_x_" in
  first [try (set (x:=e) at 17; fail 1);
    first [try (set (x:=e) at 9; fail 1);
      first [try (set (x:=e) at 5; fail 1);
        first [try (set (x:=e) at 3; fail 1);
          first [try (set (x:=e) at 2; fail 1);
            try (hrewrite H at 1)
          | try (hrewrite H at 2) ]
        | first [try (set (x:=e) at 4; fail 1);
            try (hrewrite H at 3)
          | try (hrewrite H at 4) ] ]
      | first [try (set (x:=e) at 7; fail 1);
          first [try (set (x:=e) at 6; fail 1);
            try (hrewrite H at 5)
          | try (hrewrite H at 6)]
        | first [try (set (x:=e) at 8; fail 1);
            try (hrewrite H at 7)
          | try (hrewrite H at 8) ] ] ]
    | first [try (set (x:=e) at 13; fail 1);
        first [try (set (x:=e) at 11; fail 1);
          first [try (set (x:=e) at 10; fail 1);
            try (hrewrite H at 9)
          | try (hrewrite H at 10) ]
        | first [try (set (x:=e) at 12; fail 1);
            try (hrewrite H at 11)
          | try (hrewrite H at 12) ] ]
      | first [try (set (x:=e) at 15; fail 1);
          first [try (set (x:=e) at 14; fail 1);
            try (hrewrite H at 13)
          | try (hrewrite H at 14)]
        | first [try (set (x:=e) at 16; fail 1);
            try (hrewrite H at 15)
          | try (hrewrite H at 16) ] ] ] ]
  | first [try (set (x:=e) at 25; fail 1);
      first [try (set (x:=e) at 21; fail 1);
        first [try (set (x:=e) at 19; fail 1);
          first [try (set (x:=e) at 18; fail 1);
            try (hrewrite H at 17)
          | try (hrewrite H at 18) ]
        | first [try (set (x:=e) at 20; fail 1);
            try (hrewrite H at 19)
          | try (hrewrite H at 20) ] ]
      | first [try (set (x:=e) at 23; fail 1);
          first [try (set (x:=e) at 22; fail 1);
            try (hrewrite H at 21)
          | try (hrewrite H at 22)]
        | first [try (set (x:=e) at 24; fail 1);
            try (hrewrite H at 23)
          | try (hrewrite H at 24) ] ] ]
    | first [try (set (x:=e) at 29; fail 1);
        first [try (set (x:=e) at 27; fail 1);
          first [try (set (x:=e) at 26; fail 1);
            try (hrewrite H at 25)
          | try (hrewrite H at 26) ]
        | first [try (set (x:=e) at 28; fail 1);
            try (hrewrite H at 27)
          | try (hrewrite H at 28) ] ]
      | first [try (set (x:=e) at 31; fail 1);
          first [try (set (x:=e) at 30; fail 1);
            try (hrewrite H at 29)
          | try (hrewrite H at 30)]
        | first [try (set (x:=e) at 32; fail 1);
            try (hrewrite H at 31)
          | try (hrewrite H at 32) ] ] ] ] ]
.

Ltac paco_generalize_hyp mark :=
  let y := fresh "_paco_rel_" in
  match goal with
  | [x: ?A |- _] =>
    match A with
    | mark => clear x
    | _ => intro y;
      match type of y with
        | context[x] => revert x y;
          match goal with [|-forall x, @?f x -> _] =>
            intros x y; generalize (ex_intro f x y)
          end
        | _ => generalize (conj (ex_intro _ x _paco_foo_cons) y)
      end; clear x y; paco_generalize_hyp mark
    end
  end.

Ltac paco_convert e x EQ :=
  generalize (eq_refl e); generalize e at 2; intros x EQ;
  hrewrite_last e EQ; apply eq_sym, paco_eq_JMeq in EQ; revert x EQ.

Ltac paco_destruct_hyp mark :=
  match goal with
  | [x: ?A |- _] =>
    match A with
    | mark => idtac
    | _paco_foo => clear x; paco_destruct_hyp mark
    | exists n, ?p => let n' := fresh n in destruct x as (n', x); paco_destruct_hyp mark
    | ?p /\ ?q => let x' := fresh x in destruct x as (x,x'); paco_destruct_hyp mark
    end
  end.

Ltac paco_revert_hyp mark :=
  match goal with [x: ?A |- _] =>
  match A with
    | mark => clear x
    | _ => revert x; paco_revert_hyp mark
  end end.

Ltac paco_post_var INC pr cr := let TMP := fresh "_paco_tmp_" in
  repeat (
    match goal with [H: context f [pr] |-_] =>
      let cih := context f [cr] in rename H into TMP;
      assert(H : cih) by (repeat intro; eapply INC, TMP; eassumption); clear TMP
    end);
  clear INC pr.

Ltac paco_rename_last :=
  let x := fresh "_paco_xxx_" in match goal with [H: _|-_] => rename H into x end.

Ltac paco_simp_hyp CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    simplJM; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       try (apply paco_eq_JMeq; reflexivity);
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       eauto using paco_eq_JMeq, _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp CIH :=
  let CIH := fresh CIH in let TMP := fresh "_paco_TMP_" in
  intro CIH; paco_simp_hyp CIH;
  generalize _paco_mark_cons; intro TMP;
  repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
  simplJM; paco_revert_hyp _paco_mark.

Ltac paco_ren_r nr cr :=
  first [rename cr into nr | let nr := fresh nr in rename cr into nr].

Ltac paco_ren_pr pr cr := rename cr into pr.

(** *** Arity 0
*)

Ltac paco_cont0 :=
generalize _paco_foo_cons; paco_generalize_hyp _paco_mark.

Ltac paco_pre0 :=
generalize _paco_mark_cons; repeat intro; paco_cont0.

Ltac paco_post_match0 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| (pacoid _) -> _ => clear H; tac1 cr
| ?pr -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post0" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match0 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 1
*)

Ltac paco_cont1 e0 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
paco_convert e0 x0 EQ0;
intros x0 EQ0;
generalize EQ0; clear EQ0;
move x0 at top;
paco_generalize_hyp _paco_mark; revert x0.

Lemma _paco_pre1: forall T0 (gf: rel1 T0) x0
(X: let gf' := gf in gf' x0), gf x0.
Proof. intros; apply X. Defined.

Ltac paco_pre1 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre1; intro X;
match goal with
| |- _ ?e0 => unfold X; clear X; paco_cont1 e0
end.

Ltac paco_post_match1 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _, (pacoid _) _ -> _ => clear H; tac1 cr
| forall _, ?pr _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post1" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match1 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 2
*)

Ltac paco_cont2 e0 e1 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
generalize (conj EQ0 EQ1); clear EQ0 EQ1;
move x0 at top; move x1 at top;
paco_generalize_hyp _paco_mark; revert x0 x1.

Lemma _paco_pre2: forall T0 T1 (gf: rel2 T0 T1) x0 x1
(X: let gf' := gf in gf' x0 x1), gf x0 x1.
Proof. intros; apply X. Defined.

Ltac paco_pre2 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre2; intro X;
match goal with
| |- _ ?e0 ?e1 => unfold X; clear X; paco_cont2 e0 e1
end.

Ltac paco_post_match2 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _, (pacoid _) _ _ -> _ => clear H; tac1 cr
| forall _ _, ?pr _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post2" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match2 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 3
*)

Ltac paco_cont3 e0 e1 e2 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
generalize (conj EQ0 (conj EQ1 EQ2)); clear EQ0 EQ1 EQ2;
move x0 at top; move x1 at top; move x2 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2.

Lemma _paco_pre3: forall T0 T1 T2 (gf: rel3 T0 T1 T2) x0 x1 x2
(X: let gf' := gf in gf' x0 x1 x2), gf x0 x1 x2.
Proof. intros; apply X. Defined.

Ltac paco_pre3 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre3; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 => unfold X; clear X; paco_cont3 e0 e1 e2
end.

Ltac paco_post_match3 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _, (pacoid _) _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _, ?pr _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post3" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match3 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 4
*)

Ltac paco_cont4 e0 e1 e2 e3 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
generalize (conj EQ0 (conj EQ1 (conj EQ2 EQ3))); clear EQ0 EQ1 EQ2 EQ3;
move x0 at top; move x1 at top; move x2 at top; move x3 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3.

Lemma _paco_pre4: forall T0 T1 T2 T3 (gf: rel4 T0 T1 T2 T3) x0 x1 x2 x3
(X: let gf' := gf in gf' x0 x1 x2 x3), gf x0 x1 x2 x3.
Proof. intros; apply X. Defined.

Ltac paco_pre4 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre4; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 => unfold X; clear X; paco_cont4 e0 e1 e2 e3
end.

Ltac paco_post_match4 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _, (pacoid _) _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _, ?pr _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post4" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match4 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 5
*)

Ltac paco_cont5 e0 e1 e2 e3 e4 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 EQ4)))); clear EQ0 EQ1 EQ2 EQ3 EQ4;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4.

Lemma _paco_pre5: forall T0 T1 T2 T3 T4 (gf: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4
(X: let gf' := gf in gf' x0 x1 x2 x3 x4), gf x0 x1 x2 x3 x4.
Proof. intros; apply X. Defined.

Ltac paco_pre5 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre5; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 => unfold X; clear X; paco_cont5 e0 e1 e2 e3 e4
end.

Ltac paco_post_match5 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _, (pacoid _) _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _, ?pr _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post5" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match5 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 6
*)

Ltac paco_cont6 e0 e1 e2 e3 e4 e5 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 EQ5))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5.

Lemma _paco_pre6: forall T0 T1 T2 T3 T4 T5 (gf: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5), gf x0 x1 x2 x3 x4 x5.
Proof. intros; apply X. Defined.

Ltac paco_pre6 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre6; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 => unfold X; clear X; paco_cont6 e0 e1 e2 e3 e4 e5
end.

Ltac paco_post_match6 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _, ?pr _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post6" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match6 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 7
*)

Ltac paco_cont7 e0 e1 e2 e3 e4 e5 e6 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 EQ6)))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6.

Lemma _paco_pre7: forall T0 T1 T2 T3 T4 T5 T6 (gf: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6), gf x0 x1 x2 x3 x4 x5 x6.
Proof. intros; apply X. Defined.

Ltac paco_pre7 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre7; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 => unfold X; clear X; paco_cont7 e0 e1 e2 e3 e4 e5 e6
end.

Ltac paco_post_match7 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post7" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match7 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 8
*)

Ltac paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 EQ7))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7.

Lemma _paco_pre8: forall T0 T1 T2 T3 T4 T5 T6 T7 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7), gf x0 x1 x2 x3 x4 x5 x6 x7.
Proof. intros; apply X. Defined.

Ltac paco_pre8 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre8; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 => unfold X; clear X; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7
end.

Ltac paco_post_match8 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post8" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match8 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 9
*)

Ltac paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 EQ8)))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8.

Lemma _paco_pre9: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8), gf x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof. intros; apply X. Defined.

Ltac paco_pre9 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre9; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 => unfold X; clear X; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8
end.

Ltac paco_post_match9 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post9" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match9 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 10
*)

Ltac paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 EQ9))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

Lemma _paco_pre10: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof. intros; apply X. Defined.

Ltac paco_pre10 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre10; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 => unfold X; clear X; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
end.

Ltac paco_post_match10 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post10" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match10 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 11
*)

Ltac paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 EQ10)))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Lemma _paco_pre11: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof. intros; apply X. Defined.

Ltac paco_pre11 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre11; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 => unfold X; clear X; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
end.

Ltac paco_post_match11 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post11" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match11 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 12
*)

Ltac paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 EQ11))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Lemma _paco_pre12: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof. intros; apply X. Defined.

Ltac paco_pre12 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre12; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 => unfold X; clear X; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
end.

Ltac paco_post_match12 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post12" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match12 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 13
*)

Ltac paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
let x12 := fresh "_paco_v_" in let EQ12 := fresh "_paco_EQ_" in
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
intros x12 EQ12;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 EQ12)))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Lemma _paco_pre13: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof. intros; apply X. Defined.

Ltac paco_pre13 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre13; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 => unfold X; clear X; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
end.

Ltac paco_post_match13 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post13" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match13 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 14
*)

Ltac paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
let x12 := fresh "_paco_v_" in let EQ12 := fresh "_paco_EQ_" in
let x13 := fresh "_paco_v_" in let EQ13 := fresh "_paco_EQ_" in
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
intros x12 EQ12;
intros x13 EQ13;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 EQ13))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Lemma _paco_pre14: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof. intros; apply X. Defined.

Ltac paco_pre14 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre14; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 => unfold X; clear X; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
end.

Ltac paco_post_match14 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post14" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match14 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 15
*)

Ltac paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
let x12 := fresh "_paco_v_" in let EQ12 := fresh "_paco_EQ_" in
let x13 := fresh "_paco_v_" in let EQ13 := fresh "_paco_EQ_" in
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
intros x12 EQ12;
intros x13 EQ13;
intros x14 EQ14;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 EQ14)))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Lemma _paco_pre15: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof. intros; apply X. Defined.

Ltac paco_pre15 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre15; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 => unfold X; clear X; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
end.

Ltac paco_post_match15 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post15" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match15 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** ** External interface *)

(** We provide our main tactics:

    - [pcofix{n} ident using lemma with ident']


    where [ident] is the identifier used to name the generated coinduction hypothesis,
    [lemma] is an expression denoting which accumulation lemma is to be used, and
    [ident'] is the identifier used to name the accumulation variable.
*)

Tactic Notation "pcofix0" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre0; eapply lem; paco_post0 CIH with r.

Tactic Notation "pcofix1" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre1; eapply lem; paco_post1 CIH with r.

Tactic Notation "pcofix2" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre2; eapply lem; paco_post2 CIH with r.

Tactic Notation "pcofix3" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre3; eapply lem; paco_post3 CIH with r.

Tactic Notation "pcofix4" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre4; eapply lem; paco_post4 CIH with r.

Tactic Notation "pcofix5" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre5; eapply lem; paco_post5 CIH with r.

Tactic Notation "pcofix6" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre6; eapply lem; paco_post6 CIH with r.

Tactic Notation "pcofix7" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre7; eapply lem; paco_post7 CIH with r.

Tactic Notation "pcofix8" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre8; eapply lem; paco_post8 CIH with r.

Tactic Notation "pcofix9" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre9; eapply lem; paco_post9 CIH with r.

Tactic Notation "pcofix10" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre10; eapply lem; paco_post10 CIH with r.

Tactic Notation "pcofix11" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre11; eapply lem; paco_post11 CIH with r.

Tactic Notation "pcofix12" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre12; eapply lem; paco_post12 CIH with r.

Tactic Notation "pcofix13" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre13; eapply lem; paco_post13 CIH with r.

Tactic Notation "pcofix14" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre14; eapply lem; paco_post14 CIH with r.

Tactic Notation "pcofix15" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre15; eapply lem; paco_post15 CIH with r.

(** [pcofix] automatically figures out the appropriate index [n] from
    the type of the accumulation lemma [lem] and applies [pcofix{n}].
*)

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) "with" ident(nr) :=
  let N := fresh "_paco_N_" in let TMP := fresh "_paco_TMP_" in
  evar (N : nat);
  let P := type of lem in
  assert (TMP: False -> P) by
    (intro TMP; repeat intro; match goal with [H : _ |- _] => revert H end;
     match goal with
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 15)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 14)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 13)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 12)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 11)
     | [|- _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 10)
     | [|- _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 9)
     | [|- _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 8)
     | [|- _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 7)
     | [|- _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 6)
     | [|- _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 5)
     | [|- _ _ _ _ _ -> _] => revert N; instantiate (1 := 4)
     | [|- _ _ _ _ -> _] => revert N; instantiate (1 := 3)
     | [|- _ _ _ -> _] => revert N; instantiate (1 := 2)
     | [|- _ _ -> _] => revert N; instantiate (1 := 1)
     | [|- _ -> _] => revert N; instantiate (1 := 0)
     end; destruct TMP);
  clear TMP;
  revert N;
  match goal with
  | [|- let _ := 0 in _] => intros _; pcofix0 CIH using lem with nr
  | [|- let _ := 1 in _] => intros _; pcofix1 CIH using lem with nr
  | [|- let _ := 2 in _] => intros _; pcofix2 CIH using lem with nr
  | [|- let _ := 3 in _] => intros _; pcofix3 CIH using lem with nr
  | [|- let _ := 4 in _] => intros _; pcofix4 CIH using lem with nr
  | [|- let _ := 5 in _] => intros _; pcofix5 CIH using lem with nr
  | [|- let _ := 6 in _] => intros _; pcofix6 CIH using lem with nr
  | [|- let _ := 7 in _] => intros _; pcofix7 CIH using lem with nr
  | [|- let _ := 8 in _] => intros _; pcofix8 CIH using lem with nr
  | [|- let _ := 9 in _] => intros _; pcofix9 CIH using lem with nr
  | [|- let _ := 10 in _] => intros _; pcofix10 CIH using lem with nr
  | [|- let _ := 11 in _] => intros _; pcofix11 CIH using lem with nr
  | [|- let _ := 12 in _] => intros _; pcofix12 CIH using lem with nr
  | [|- let _ := 13 in _] => intros _; pcofix13 CIH using lem with nr
  | [|- let _ := 14 in _] => intros _; pcofix14 CIH using lem with nr
  | [|- let _ := 15 in _] => intros _; pcofix15 CIH using lem with nr
  end.

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) :=
  pcofix CIH using lem with r.

