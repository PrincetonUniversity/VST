Require Export VST.concurrency.paco.src.paconotation VST.concurrency.paco.src.pacotac VST.concurrency.paco.src.pacodef.
Set Implicit Arguments.

(** ** Type Class for acc, mult, fold and unfold
*)

Class paco_class (A : Prop) :=
{ pacoacctyp: Type
; pacoacc : pacoacctyp
; pacomulttyp: Type
; pacomult : pacomulttyp
; pacofoldtyp: Type
; pacofold : pacofoldtyp
; pacounfoldtyp: Type
; pacounfold : pacounfoldtyp
}.

Definition get_paco_cls {A} {cls: paco_class A} (a: A) := cls.

Create HintDb paco.

Ltac paco_class TGT method :=
  let typ := fresh "_typ_" in let lem := fresh "_lem_" in
  let TMP := fresh "_tmp_" in let X := fresh "_X_" in
  let CLS := fresh "_CLS_" in
  evar (typ: Type); evar (lem: typ);
  assert(TMP: TGT -> True) by (
    intros X; set (CLS := method _ (get_paco_cls X));
    repeat red in CLS; clear X; revert lem;
    match goal with [CLS := ?v |-_] => instantiate (1:= v) end;
    clear CLS; exact I);
  clear TMP; unfold typ in *; clear typ; revert lem.

(** ** pfold tactic
  - [pfold]
*)

Ltac pfold := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacofold) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.

(** ** punfold tactic
  - [punfold H]
*)

Ltac punfold H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end;
  eauto with paco.

(** ** pmult tactic
  - [pmult]
*)

Ltac pmult := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacomult) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.

(** ** pcofix tactic
  - [pcofix CIH [with r]]
*)

Tactic Notation "pcofix" ident(CIH) "with" ident(r) :=
  let x := fresh "_x_" in
  generalize _paco_mark_cons; repeat intro; repeat red;
  match goal with [|- ?G] =>
  paco_class G (@pacoacc); intro x;
  match goal with [x:=?lem|-_] => clear x;
    paco_revert_hyp _paco_mark;
    pcofix CIH using lem with r
  end end.

Tactic Notation "pcofix" ident(CIH) := pcofix CIH with r.

(** ** [pclearbot] simplifies all hypotheses of the form [upaco{n} gf bot{n}] to [paco{n} gf bot{n}].
*)

Ltac pclearbot :=
  let X := fresh "_X" in
  repeat match goal with
  | [H: context[pacoid] |- _] => red in H; destruct H as [H|X]; [|contradiction X]
  end.

(** ** [pdestruct H] and [pinversion H]
*)

Ltac pdestruct H := punfold H; destruct H; pclearbot.

Ltac pinversion H := punfold H; inversion H; pclearbot.

(** ** pmonauto tactic
  - [pmonauto]
*)

Ltac pmonauto :=
  let IN := fresh "IN" in try (repeat intro; destruct IN; eauto; fail).

(** Tactics for Internal Use Only *)

Ltac paco_cofix_auto :=
  cofix; repeat intro;
  match goal with [H: _ |- _] => destruct H end; econstructor;
  try (match goal with [H: _|-_] => apply H end); intros;
  lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end;
  repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10].

Ltac paco_revert :=
  match goal with [H: _ |- _] => revert H end.

Notation "p <_paco_0= q" :=
  (forall (PR: p : Prop), q : Prop)
  (at level 50, no associativity).

Notation "p <_paco_1= q" :=
  (forall _paco_x0 (PR: p _paco_x0 : Prop), q _paco_x0 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_2= q" :=
  (forall _paco_x0 _paco_x1 (PR: p _paco_x0 _paco_x1 : Prop), q _paco_x0 _paco_x1 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_3= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 (PR: p _paco_x0 _paco_x1 _paco_x2 : Prop), q _paco_x0 _paco_x1 _paco_x2 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_4= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_5= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_6= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_7= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_8= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_9= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_10= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_11= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_12= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_13= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_14= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_15= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 _paco_x14 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 _paco_x14 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 _paco_x14 : Prop)
  (at level 50, no associativity).

