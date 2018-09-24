(* Lifted functions.
   By Jesper Bengtson, revised by Andrew W. Appel.
*)

Structure Lift := mkLift {
         lift_S: Type;
         lift_T: Type;
         lift_prod : Type;
         lift_last: Type;
         lifted:> Type;
         lift_curry: lift_T -> lift_prod -> lift_last;
         lift_uncurry_open: ((lift_S -> lift_prod) -> (lift_S -> lift_last)) -> lifted
}.

Definition Tend (S: Type) (A: Type) :=
    mkLift S A unit A
          (S -> A)
          (fun f _ => f)
          (fun f => f (fun _: S => tt)).

Set Warnings "-projection-no-head-constant".
Canonical Structure Tarrow (A: Type) (H: Lift) :=
    mkLift (lift_S H)
      (A -> lift_T H)
      (prod A (lift_prod H))
      (lift_last H)
      ((lift_S H -> A) -> lifted H)
      (fun f x => match x with (x1,x2) => lift_curry H (f x1) x2 end)
      (fun f x => lift_uncurry_open H (fun y: lift_S H -> lift_prod H => f (fun z => (x z, y z)))).
Set Warnings "+projection-no-head-constant".

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Definition lift S {A B} (f : A -> B) (a : S -> A) (x: S) : B := f (a x).

Definition liftx {H: Lift} (f: lift_T H) : lifted H :=
  lift_uncurry_open H (lift (lift_curry H f)).
Arguments liftx H f : simpl never.

(* NOTE: We want unfold_lift to unfold EVERYTHING related to lifting, but NOTHING else.
  Thus we have avoided using any library functions to implement lifting, so that
  we can unfold all of it without interfering with other things the user might be doing. *)

Tactic Notation "unfold_lift" :=
  unfold liftx;
  repeat match goal with(* This unfolds instances of Tend *)
  | |- context [lift_uncurry_open (?F _)] => unfold F
  | |- context [Tarrow _ (?F _)] => unfold F
  end;
  cbv delta [Tarrow Tend lift_S lift_T lift_prod lift_last lifted lift_uncurry_open lift_curry lift] beta iota.

Tactic Notation "unfold_lift" "in" hyp(H) := (* move this to veric/lift.v *)
  unfold liftx  in H;
  repeat match type of H with(* This unfolds instances of Tend *)
  | context [lift_uncurry_open (?F _)] => unfold F in H
  | context [Tarrow _ (?F _)] => unfold F in H
  end;
  cbv delta [Tarrow Tend lift_S lift_T lift_prod lift_last lifted lift_uncurry_open lift_curry lift] beta iota in H.

Tactic Notation "unfold_lift" "in" "*" :=
  unfold liftx in *;
  repeat match goal with (* This unfolds instances of Tend *)
             | H: context [lift_uncurry_open (?F _)] |- _ => unfold F in H
             | |- context [Tarrow _ (?F _)] => unfold F
             end;
  cbv delta [Tarrow Tend lift_S lift_T lift_prod lift_last lifted lift_uncurry_open lift_curry lift] beta iota in *.

(* The reason for writing   liftx(x : _) instead
  of just (liftx x)  is to get the case  `(fun v => ..v...) to work *)
Notation "'`' x" := (liftx x) (at level 10, x at next level). (* use level 10 for compatibility with coq/Theories/Program/Utils.v *)
Notation "'`(' x ')'" := (liftx (x : _)).

(*  EXAMPLES OF USE

Parameter environ : Type.

Canonical Structure LiftEnviron := Tend environ.

Definition foo (v : nat) := (v=O).
Check (`foo).
Check (`(fun v => v=O)).

(* Infix "-.>" := Tarrow (at level 80, right associativity).  (* The
      only purpose of this Infix is to make the error message slightly prettier,
      but they're not bad even without it. *) *)
(* Notation  "x '-.>[' y ] " := (Tarrow x (LiftEnviron y)) (at level 80, right associativity).  *)


Check `plus.
Check (`(plus 4)).

(* Goal (lifted (nat -.> (nat -.> LiftEnviron nat)) = ((environ -> nat) -> (environ -> nat) -> (environ -> nat))).
reflexivity.
Qed.
*)

Parameter f: environ -> nat.
Check (`plus f).
Check (`plus f f).
Check (`(@cons nat)).
Check (`(@cons nat) (`plus f f) `nil).
Check (`(@cons _) (`plus f f) `nil).     (* HA!  This line would not have worked using typeclasses for Lift;
            it does work using canonical structures *)
(* Check (`cons (`plus f f) `nil).     (* this line fails, which is OK; however, using the old 'coerce' appoach,
                                                           this would have worked.  *) *)


Example test_plus (s : environ) : (`plus `(4) `3) s = (`(7)) s.
  simpl.  (* doesn't unfold the backtick; this is a good thing, I think. *)
 unfold_lift. (* optional -- proof works with or without it *)
  reflexivity.
Qed.

Example test_plus' (s : environ) : (`plus `(4) `3) s = (`(7)) s.
  simpl.  (* doesn't unfold the backtick; this is a good thing, I think. *)
  reflexivity.
Qed.

Definition natfun := nat -> nat.
Opaque natfun.

Definition add : nat -> natfun := plus.

Goal forall rho, `add `(3) rho = (fun y => plus 3 y).
 intro rho.
 simpl.  (* doesn't unfold the backtick; this is a good thing, I think. *)
 unfold_lift. (* optional -- see what happens! *)
 reflexivity.
Qed.

(* Goal `add `3 = `plus `3.   (* This fails.  Indeed, it should fail.
       But the error message is reasonably informative! *)  *)

END EXAMPLES OF USE *)
