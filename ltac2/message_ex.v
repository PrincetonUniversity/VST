Require Import Ltac2.Ltac2.

(** * Ltac2 message utilities / extensions *)

Ltac2 list_to_message_flex (element_to_message : 'a -> message) (prefix : string) (separator : string) (postfix : string) (l : 'a list) : message :=
  let rec aux(l : 'a list) : message :=
    match l with
    | [] => Message.of_string postfix
    | h :: t => 
      match t with
      | [] => Message.concat (element_to_message h) (Message.of_string postfix)
      | _ :: _ => Message.concat (element_to_message h) (Message.concat (Message.of_string separator) (aux t))
      end
    end in
    Message.concat (Message.of_string prefix) (aux l).

Ltac2 list_to_message (element_to_message : 'a -> message) (l : 'a list) : message := list_to_message_flex element_to_message "[ " "; " " ]" l.

Ltac2 reference_to_message (ref  : Std.reference) : message :=
  let path := Env.path ref in
  list_to_message_flex Message.of_ident "" "." "" path.

(* Tests
Ltac2 Eval Message.print (list_to_message Message.of_string [ "A"; "B" ]).
Ltac2 Eval Message.print (reference_to_message reference:(S)).
*)
