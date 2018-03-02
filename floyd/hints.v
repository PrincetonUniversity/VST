Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.forward_lemmas VST.floyd.call_lemmas.
Require Import VST.floyd.extcall_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.loadstore_mapsto.
Require Import VST.floyd.loadstore_field_at.
Require Import VST.floyd.stronger.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.entailer.
Require Import VST.floyd.globals_lemmas.
Import Cop.
Import Cop2.

Ltac print_hint_forward c :=
match c with
| Ssequence ?c1 _ => print_hint_forward c1
| Scall _ _ _ => idtac "Hint: try 'forward_call x', where x is a value to instantiate the tuple of the function's WITH clause"
| Swhile _ _ => idtac "Hint: try 'forward_while'"
| Sifthenelse _ _ _ => idtac "Hint: try 'forward_if'"
| Sloop _ _ => idtac "Hint: try 'forward_loop' or 'forward_for_simple_bound'"
| Sfor _ _ _ _ => idtac "Hint: try 'forward_loop' or 'forward_for_simple_bound'"
| _ => idtac "Hint: try 'forward'"
end.

Ltac print_hint_semax D Pre c Post :=
 try match Pre with exp _ => idtac "Hint: try 'Intros x' where x is the name you want to give the variable bound by EX'"  end;
 try match Pre with PROPx (_::_) _ => idtac "Hint: use 'Intros' to move propositions above the line" end;
 try match Pre with PROPx nil (LOCALx _ (SEPx _)) =>
     let x := fresh "x" in
      tryif (try (Intro x; fail 1)) then fail
      else idtac "Hint: try 'Intros y' where y is the name you want to give the variable bound by EX'"
     end;
 try match Pre with PROPx nil (LOCALx _ (SEPx _)) =>
     tryif (try (progress Intro_prop; fail 1)) then fail
     else idtac "Hint: try 'Intros' to canonicalize your precondition"
   end;
 try match Pre with context [if ?A then _ else _] => 
        match type of A with
        | sumbool _ _ => idtac "Hint: perhaps  try 'destruct " A "' or, more concisely,  'if_tac'"
        | bool => idtac "Hint: perhaps try 'destruct " A " eqn:?'"
       end end;
 try match Pre with PROPx nil (LOCALx _ (SEPx _)) => print_hint_forward c end;
 idtac.

Ltac hint :=
 tryif (try (assert True; [ | solve [auto]]; fail 1)) then idtac
     else  idtac "Hint:  'auto' solves the goal";
 tryif (try (assert True; [ | solve [contradiction]]; fail 1)) then idtac
     else  idtac "Hint:  'contradiction' solves the goal";
 tryif (try (assert True; [ | discriminate]; fail 1)) then idtac
     else  idtac "Hint:  'discriminate' solves the goal";
 tryif (try (assert True; [ | solve [rep_omega]]; fail 1)) then idtac
     else  idtac "Hint:  'rep_omega' solves the goal";
 tryif (try (assert True; [ | progress entailer!]; fail 1)) then idtac
     else  idtac "Hint:  try 'entailer!'";
 tryif (try (progress autorewrite with sublist; fail 1)) then idtac
     else  idtac "Hint:  try 'autorewrite with sublist'";
 try match goal with H: ?p = nullval |- _ => idtac "Hint: try 'subst " p "'" end;
 try match goal with |- ?A |-- ?B =>
          tryif (try (assert True; [ | rewrite ?sepcon_emp, ?emp_sepcon; progress cancel]; fail 1)) then idtac
           else  idtac "Hint:  try 'cancel'"
       end;
 try match goal with |- _ |-- ?B =>
    match B with context [@exp _ _ ?t ] =>
       idtac "Hint: try 'Exists x', where x is a value of type (" t ") to instantiate the existential"
   end
  end;
 lazymatch goal with
 | D := @abbreviate tycontext _, Po := @abbreviate ret_assert _ |- semax ?D' ?Pre ?c ?Post =>
     constr_eq D D'; constr_eq Po Post; print_hint_semax D Pre c Post
 | |- semax _ _ _ _ => 
         idtac "Hint: use abbreviate_semax to put your proof goal into a more standard form"
 | |- ENTAIL _, _ |-- _ => idtac "Hint: try 'entailer!'"
 | |- _ => idtac
 end.

