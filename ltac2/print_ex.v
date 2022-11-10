Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.

(** * Ltac2 printing utilities / extensions *)

Ltac2 print_hyps () :=
    let rec aux (hyps : (ident * constr option * constr) list) :=
      match hyps with
      | [] => ()
      | h :: t =>
        let (id, value, type) := h in
        match value with
        | Some value => printf "let %I := %t : %t in " id value type
        | None => printf "forall (%I : %t), " id type
        end;
        aux t
      end in
    aux (Control.hyps ())
  .

Ltac2 print_goal () :=
  lazy_match! goal with
  | [ |- ?g ] => printf "%t" g
  end.

(** With these options:

    Set Printing Depth 1000.
    Set Printing Width 240.
    Unset Printing Notations.
    Set Printing Implicit.

print_context should produce something which Coq can parse as Goal.
*)

Ltac2 print_context () :=
    printf "Goal";
    print_hyps ();
    print_goal ();
    printf "."
  .
  