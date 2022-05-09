Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.entailer.
Require Import VST.floyd.forward. (* must come after entailer because of Ltac override *)
Require Import VST.floyd.deadvars.

Ltac EExists_unify1 x P :=
 match P with
 | ?P1 /\ ?P2 => first [EExists_unify1 x P1 | EExists_unify1 x P2]
 | ?A = ?B =>
  match A with context [x] =>
  pattern (A=B);
  let y := fresh "y" in match goal with |- ?F _ => set (y:=F) end;
  autorewrite with entailer_rewrite;
  first  [subst x; match goal with |- _ (?A' = ?B') => unify A' B' end
  | match goal with
  | x:= ?u |- _ (Vint (Int.repr (x - ?i)) = Vint (Int.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vint (Int.repr (x + ?i)) = Vint (Int.repr ?j)) =>
        unify u (j-i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x - ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j+i); subst x
  | x:= ?u |- _ (Vlong (Int64.repr (x + ?i)) = Vlong (Int64.repr ?j)) =>
        unify u (j-i); subst x
  end];
  subst y; cbv beta
  end
end.

Ltac EExists_unify := 
  let T := fresh "T"  in
  let x := fresh "x" in
  evar (T:Type); evar (x:T); subst T; 
  Exists x;
  match goal with
  | |- _ |-- !! ?P && _ => EExists_unify1 x P
  | |- _ |-- !! ?P => EExists_unify1 x P
  end.

Ltac simpl_implicit :=
  simpl projT1.

Ltac step :=
  first
  [ progress Intros *
  | progress simpl_implicit
  | progress autorewrite with sublist in *|-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_lia | cstring' | Zlength_solve
  | match goal with |- ENTAIL _, _ |-- _ =>  go_lower end
  | EExists_unify
  | cstring1
  | deadvars!
  | solve [match goal with |- @derives mpred _ _ _ => cancel end]
  | solve [entailer!; try cstring']
  | list_solve
  ].

Tactic Notation "step!"  :=
  first
  [ progress Intros *
  | progress simpl_implicit
  | progress autorewrite with sublist in * |-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | forward
  | forward_if
  | forward_call
  | rep_lia
  | cstring'
  | Zlength_solve
  | EExists
  | cstring1
  | deadvars!
  | progress_entailer
  (* | match goal with |- _ /\ _ => split end *)
  | list_solve
  ].

Tactic Notation "info_step!" :=
  first
  [ progress Intros *; idtac "Intros *."
  | progress simpl_implicit; idtac "simpl_implicit."
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm."
  | forward; idtac "forward."
  | forward_if; idtac "forward_if."
  | forward_call; idtac "forward_call."
  | rep_lia; idtac "rep_lia."
  | cstring'; idtac "cstring'."
  | Zlength_solve; idtac "Zlength_solve."
  | EExists; idtac "EExists."
  | cstring1; idtac "cstring1."
  | deadvars!; idtac "deadvars!."
  | progress_entailer; idtac "progress_entailer."
  (* | match goal with |- _ /\ _ => split end; idtac "split." *)
  | list_solve; idtac "list_solve."
  ].
