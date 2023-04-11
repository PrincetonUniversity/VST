Require Import Ltac2.Ltac2.

(** * Ltac2 list utilities / extensions *)

(** ** Use list as unsorted sets of constr terms *)

Ltac2 rec constr_bag_add (ls : constr list) (e : constr) :=
  match ls with
  | [] => [e]
  | h :: tl => if Constr.equal h e then ls else h::(constr_bag_add tl e)
  end.

Ltac2 constr_bag_contains (ls : constr list) (e : constr) :=
  List.exist (fun x => Constr.equal x e) ls.

Ltac2 rec constr_bag_union (a : constr list) (b : constr list) :=
  match b with
  | [] => a
  | h :: tl => constr_bag_union (constr_bag_add a h) tl
  end.