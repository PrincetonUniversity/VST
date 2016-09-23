(** * Common notations and definitions *)

(** ** Types of dependent predicates *)

Definition rel0 :=
  Prop.
Implicit Arguments rel0 [].

Definition rel1 T0 :=
  forall (x0: T0), Prop.
Implicit Arguments rel1 [].

Definition rel2 T0 T1 :=
  forall (x0: T0) (x1: T1 x0), Prop.
Implicit Arguments rel2 [].

Definition rel3 T0 T1 T2 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1), Prop.
Implicit Arguments rel3 [].

Definition rel4 T0 T1 T2 T3 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2), Prop.
Implicit Arguments rel4 [].

Definition rel5 T0 T1 T2 T3 T4 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3), Prop.
Implicit Arguments rel5 [].

Definition rel6 T0 T1 T2 T3 T4 T5 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4), Prop.
Implicit Arguments rel6 [].

Definition rel7 T0 T1 T2 T3 T4 T5 T6 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5), Prop.
Implicit Arguments rel7 [].

Definition rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6), Prop.
Implicit Arguments rel8 [].

Definition rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7), Prop.
Implicit Arguments rel9 [].

Definition rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Prop.
Implicit Arguments rel10 [].

Definition rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Prop.
Implicit Arguments rel11 [].

Definition rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Prop.
Implicit Arguments rel12 [].

Definition rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Prop.
Implicit Arguments rel13 [].

Definition rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Prop.
Implicit Arguments rel14 [].

Definition rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), Prop.
Implicit Arguments rel15 [].

(** ** Bottom *)

Definition pacoid {A : Type} (a: A) : A := a.

Notation bot0 :=
  (pacoid(False)).

Notation bot1 :=
  (pacoid(fun _ => False)).

Notation bot2 :=
  (pacoid(fun _ _ => False)).

Notation bot3 :=
  (pacoid(fun _ _ _ => False)).

Notation bot4 :=
  (pacoid(fun _ _ _ _ => False)).

Notation bot5 :=
  (pacoid(fun _ _ _ _ _ => False)).

Notation bot6 :=
  (pacoid(fun _ _ _ _ _ _ => False)).

Notation bot7 :=
  (pacoid(fun _ _ _ _ _ _ _ => False)).

Notation bot8 :=
  (pacoid(fun _ _ _ _ _ _ _ _ => False)).

Notation bot9 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ => False)).

Notation bot10 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ _ => False)).

Notation bot11 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ _ _ => False)).

Notation bot12 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ _ _ _ => False)).

Notation bot13 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ _ _ _ _ => False)).

Notation bot14 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => False)).

Notation bot15 :=
  (pacoid(fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => False)).

(** ** Less than or equal *)

Notation "p <0= q" :=
  (forall (PR: p : Prop), q : Prop)
  (at level 50, no associativity, only parsing).

Notation "p <1= q" :=
  (forall x0 (PR: p x0 : Prop), q x0 : Prop)
  (at level 50, no associativity).

Notation "p <2= q" :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 50, no associativity).

Notation "p <3= q" :=
  (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop)
  (at level 50, no associativity).

Notation "p <4= q" :=
  (forall x0 x1 x2 x3 (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop)
  (at level 50, no associativity).

Notation "p <5= q" :=
  (forall x0 x1 x2 x3 x4 (PR: p x0 x1 x2 x3 x4 : Prop), q x0 x1 x2 x3 x4 : Prop)
  (at level 50, no associativity).

Notation "p <6= q" :=
  (forall x0 x1 x2 x3 x4 x5 (PR: p x0 x1 x2 x3 x4 x5 : Prop), q x0 x1 x2 x3 x4 x5 : Prop)
  (at level 50, no associativity).

Notation "p <7= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 (PR: p x0 x1 x2 x3 x4 x5 x6 : Prop), q x0 x1 x2 x3 x4 x5 x6 : Prop)
  (at level 50, no associativity).

Notation "p <8= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 : Prop)
  (at level 50, no associativity).

Notation "p <9= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop)
  (at level 50, no associativity).

Notation "p <10= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop)
  (at level 50, no associativity).

Notation "p <11= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop)
  (at level 50, no associativity).

Notation "p <12= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop)
  (at level 50, no associativity).

Notation "p <13= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop)
  (at level 50, no associativity).

Notation "p <14= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop)
  (at level 50, no associativity).

Notation "p <15= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop)
  (at level 50, no associativity).

(** ** Union *)

Notation "p \0/ q" :=
  (p \/ q)
  (at level 50, no associativity, only parsing).

Notation "p \1/ q" :=
  (fun x0 => p x0 \/ q x0)
  (at level 50, no associativity).

Notation "p \2/ q" :=
  (fun x0 x1 => p x0 x1 \/ q x0 x1)
  (at level 50, no associativity).

Notation "p \3/ q" :=
  (fun x0 x1 x2 => p x0 x1 x2 \/ q x0 x1 x2)
  (at level 50, no associativity).

Notation "p \4/ q" :=
  (fun x0 x1 x2 x3 => p x0 x1 x2 x3 \/ q x0 x1 x2 x3)
  (at level 50, no associativity).

Notation "p \5/ q" :=
  (fun x0 x1 x2 x3 x4 => p x0 x1 x2 x3 x4 \/ q x0 x1 x2 x3 x4)
  (at level 50, no associativity).

Notation "p \6/ q" :=
  (fun x0 x1 x2 x3 x4 x5 => p x0 x1 x2 x3 x4 x5 \/ q x0 x1 x2 x3 x4 x5)
  (at level 50, no associativity).

Notation "p \7/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 => p x0 x1 x2 x3 x4 x5 x6 \/ q x0 x1 x2 x3 x4 x5 x6)
  (at level 50, no associativity).

Notation "p \8/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 => p x0 x1 x2 x3 x4 x5 x6 x7 \/ q x0 x1 x2 x3 x4 x5 x6 x7)
  (at level 50, no associativity).

Notation "p \9/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8)
  (at level 50, no associativity).

Notation "p \10/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
  (at level 50, no associativity).

Notation "p \11/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
  (at level 50, no associativity).

Notation "p \12/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
  (at level 50, no associativity).

Notation "p \13/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
  (at level 50, no associativity).

Notation "p \14/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
  (at level 50, no associativity).

Notation "p \15/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
  (at level 50, no associativity).

