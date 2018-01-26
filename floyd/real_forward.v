Require Import VST.floyd.base2.
Require Import VST.floyd.forward.


Inductive FWD : Type :=
| FWD_end: FWD
| FWD_straight0: FWD -> FWD
| FWD_straight1: forall {A: Type}, (A -> FWD) -> FWD
| FWD_intro: forall {A: Type}, (A -> FWD) -> FWD
| FWD_while0: forall (P: environ->mpred), FWD -> FWD -> FWD
| FWD_while1: forall (P: environ->mpred) {A: Type}, (A -> FWD) -> FWD -> FWD.

Ltac go_FWD f :=
  match f with
  | FWD_end => idtac
  | FWD_straight0 ?f' => forward; [ .. | go_FWD f']
  | FWD_straight1 ?f1 =>
         let x := fresh "x" in forward x; [ .. |
         let y := constr:(f1 x) in let y' := (eval cbv beta in y) in
         go_FWD y']
  | FWD_intro ?f1 =>
         let x := fresh "x" in forward_intro x;
         let y := constr:(f1 x) in let y' := (eval cbv beta in y) in
         go_FWD y'
  | FWD_while0 ?P ?Q ?f1 ?f2 =>
          forward_while P (*Q*); [ | | | go_FWD f1 | go_FWD f2]
  | FWD_while1 ?P ?Q ?f1 ?f2 =>
            let x := fresh "x" in forward_while P (*x*);
             [ | |
             |  let y := constr:(f1 x) in let y' := (eval cbv beta in y) in
                 go_FWD y'
             | go_FWD f2]
  end.