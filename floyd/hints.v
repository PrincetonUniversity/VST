Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
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
Require Import VST.floyd.data_at_lemmas.
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
Require Import VST.floyd.functional_base.
Require Import VST.floyd.entailer.
Require Import VST.floyd.globals_lemmas.
Require Import VST.floyd.deadvars.
Require Import VST.zlist.list_solver.
Import Cop.
Import Cop2.
Import -(notations) compcert.lib.Maps.

Local Unset SsrRewrite.

Ltac hint_loop := 
  idtac "Hint: try 'forward_for_simple_bound N (EX i:Z, PROP... LOCAL...SEP...)%assert', where N is the upper bound of the loop, i is the loop iteration value,  and the LOCAL clause does NOT contain a 'temp' binding for the loop iteration variable";
  idtac "Hint: try 'forward_loop' and examine its error message to see what arguments it takes".

Ltac print_hint_forward c :=
match c with
| Ssequence ?c1 _ => print_hint_forward c1
| Scall _ _ _ => idtac "Hint: try 'forward_call x', where x is a value to instantiate the tuple of the function's WITH clause.  If you want more information about the _type_ of the argument that you must supply to forward_call, do 'forward' for information"
| Swhile _ _ => idtac "Hint: try 'forward_while Inv', where Inv is a loop invariant"
| Sifthenelse _ _ _ => idtac "Hint: try 'forward_if', which may inform you that you need to supply a postcondition"
| Sloop _ _ =>hint_loop
| Sfor _ _ _ _ => hint_loop
| Sreturn _ => idtac "Hint: try 'forward'"
| Sbreak =>  idtac "Hint: try 'forward'"
| Scontinue =>  idtac "Hint: try 'forward'"
| Sset _ _ =>  idtac "Hint: try 'forward'"
| _ =>  idtac "Hint: try 'forward', which may tell you (in an error message) additional information about what to do"
end.

Ltac check_temp_value Delta i v :=
let x := constr:(PTree.get i (temp_types Delta))
 in let x := eval hnf in x
   in match x with
       | Some (Tint _ _ _, _) => lazymatch v with Vint _ => idtac | Vbyte _ => idtac
                               | _ =>  idtac "Hint:  your LOCAL precondition binds temp " i " to a value " v " that is not of the form (Vint _) or (Vbyte _).  Although this is legal, Floyd's proof automation will not handle it as nicely.  See if you can rewrite that value so that it has Vint or Vbyte on the outside"
                              end
      | Some (Tlong _ _, _) =>  lazymatch v with Vlong _ => idtac
                               | _ =>  idtac "Hint:  your LOCAL precondition binds temp " i " to a value " v " that is not of the form (Vlong _).  Although this is legal, Floyd's proof automation will not handle it as nicely.  See if you can rewrite that value so that it has Vlong on the outside"
                              end
      | Some (Tfloat F64 _, _) =>  lazymatch v with Vfloat _ => idtac
                               | _ =>  idtac "Hint:  your LOCAL precondition binds temp " i " to a value " v " that is not of the form (Vfloat _).  Although this is legal, Floyd's proof automation will not handle it as nicely.  See if you can rewrite that value so that it has Vfloat on the outside"
                              end
      | Some (Tfloat F32 _, _) =>  lazymatch v with Vsingle _ => idtac
                               | _ =>  idtac "Hint:  your LOCAL precondition binds temp " i " to a value " v " that is not of the form (Vsingle _).  Although this is legal, Floyd's proof automation will not handle it as nicely.  See if you can rewrite that value so that it has Vsingle on the outside"
                              end
      | _ => idtac
      end.

Ltac print_hint_local Delta L :=
 lazymatch L with
 | temp ?i ?v => check_temp_value Delta i v
 | _ => idtac
 end.

Ltac print_hint_locals Delta L :=
 lazymatch L with
 | ?L1 :: ?LR => print_hint_local Delta L1; 
                         print_hint_locals Delta LR
 | _ => idtac
 end.

Ltac print_sumbool_hint Pre := 
 try match Pre with context [if ?A then _ else _] => 
        lazymatch type of A with
        | sumbool ?X ?Y => tryif (try (rewrite if_true by auto; fail 1))
                                    then tryif (try (rewrite if_false by auto; fail 1)) 
                                              then idtac "Hint: if you think " X " is provable, 'rewrite if_true'.
    If you think " Y " is provable, 'rewrite if_false'.
    If you need a case analysis, try 'destruct " A "' or, more concisely,  'if_tac'"
                                              else idtac "Hint: 'rewrite if_false by auto'"
                                    else idtac "Hint: 'rewrite if_true by auto'"
        | bool => idtac "Hint: perhaps try 'destruct " A " eqn:?'"
       end end.

Ltac hint_allp_left A := 
lazymatch A with
| @cons mpred ?B ?C => hint_allp_left B; hint_allp_left C
| @bi_sep (iPropI _) ?B ?C => hint_allp_left B; hint_allp_left C
| @bi_and (iPropI _) ?B ?C => hint_allp_left B; hint_allp_left C
| @bi_or (iPropI _) ?B ?C => hint_allp_left B; hint_allp_left C
| @bi_forall (iPropI _) ?T _ => 
   idtac "Hint: You can instantiate the universally quantified ";
   idtac "(ALL _:"T", _) in your precondition";
   idtac "using the tactic 'allp_left x',";
   idtac "where x is a value of type " T
| _ => idtac
end.

Ltac print_hint_semax D Pre c Post :=
 try (tryif (try (deadvars!; fail 1)) then fail
     else idtac "Hint: 'deadvars!' removes useless LOCAL definitions");
 try match Pre with bi_exist _ => idtac "Hint: try 'Intros x' where x is the name you want to give the variable bound by EX'"  end;
 try match Pre with PROPx (_::_) _ => idtac "Hint: use 'Intros' to move propositions above the line" end;
 try match Pre with PROPx nil (LOCALx _ (SEPx ?R)) =>
     try let x := fresh "x" in
           tryif (try (Intro x; fail 1)) then fail
           else idtac "Hint: try 'Intros y' where y is the name you want to give the variable bound by EX'";
     try tryif (try (progress Intro_prop; fail 1)) then fail
           else idtac "Hint: try 'Intros' to canonicalize your precondition";
     try hint_allp_left R
   end;
 print_sumbool_hint Pre;
 match Pre with
 | PROPx nil (LOCALx ?L (SEPx _)) => 
             print_hint_forward c;
             print_hint_locals D L
 | _ => idtac
 end.

Ltac print_sumbool_hint_hyp := 
 match goal with H: context [if ?A then _ else _] |- _ => 
        lazymatch type of A with
        | sumbool ?X ?Y => tryif (try (rewrite if_true in H by auto; fail 1))
                                    then tryif (try (rewrite if_false in H by auto; fail 1)) 
                                              then fail
                                              else idtac "Hint: 'rewrite if_false in"H"by auto'"
                                    else idtac "Hint: 'rewrite if_true in"H"by auto'"
       end end.

Ltac cancelable A :=
lazymatch A with
| @bi_sep (iPropI _) ?B ?C => cancelable B; cancelable C
| @bi_and (iPropI _) _ _ => fail
| @bi_or (iPropI _) _ _ => fail
| _ => idtac
end.

Ltac hint_simplify_value_fits :=
 try match goal with
 | H : value_fits _ _ |- _ => 
  tryif (try (progress simplify_value_fits in H; fail 1)) then idtac
     else  (idtac "Hint:  try 'simplify_value_fits in"H"'";
  idtac "    (this is not often useful, but it can tell you for example that the contents of an array has the right length.  To disable this hint, 'Ltac hint_simplify_value_fits ::= idtac.' ")
  end.

Ltac f_equal_cstring_hint_aux :=
  match goal with H: ~In Byte.zero _ |- _ => idtac end;
  lazymatch goal with
  | H1: Znth _ (app _ (Byte.zero::nil)) = Byte.zero |- _ => idtac 
  | H1: Znth _ (app _ (Byte.zero::nil)) <> Byte.zero |- _ => idtac
  end;
  try match goal with 
  | |- @eq ?t _ _ => unify t Z; fail 1
  end;
  repeat match goal with 
     | |- @eq ?t (?f _) (?g _) => (unify t Z; fail 1) || simple apply f_equal
     end;
  cstring.

Ltac hint_solves := 
 first [
    tryif (try (assert True; [ | solve [auto]]; fail 1))
     then tryif (try (assert True; [ | solve [auto with valid_pointer]]; fail 1))
              then fail
              else idtac "Hint:  'auto with valid_pointer' solves the goal"
     else  idtac "Hint:  'auto' solves the goal"
 | tryif (try (assert True; [ | solve [contradiction]]; fail 1)) then fail
     else  idtac "Hint:  'contradiction' solves the goal"
 | tryif (try (assert True; [ | discriminate]; fail 1)) then fail
     else  idtac "Hint:  'discriminate' solves the goal"
 | tryif (try (assert True; [ | solve [lia]]; fail 1)) then fail
     else  idtac "Hint:  'lia' solves the goal"
 | tryif (try (assert True; [ | solve [rep_lia]]; fail 1)) then fail
     else  idtac "Hint:  'rep_lia' solves the goal"
 | tryif (try (assert True; [ | solve [quick_list_solve]]; fail 1)) then fail
     else  idtac "Hint:  'list_solve' solves the goal"
 | tryif (try (assert True; [ | solve [cstring]]; fail 1)) then fail
     else  idtac "Hint:  'cstring' solves the goal"
 | tryif (try (assert True; [ | solve [f_equal_cstring_hint_aux]]; fail 1)) then fail
     else  idtac "Hint:  'f_equal' followed by 'cstring' solves the goal"
 | match goal with |- context [field_compatible] => idtac | |- context [field_compatible0] => idtac end;
       tryif (try (assert True; [ | solve [auto with field_compatible]]; fail 1)) then fail
       else  idtac "Hint:  'auto with field_compatible' solves the goal"
 | match goal with |- @bi_entails (iPropI _) _ _ =>
     tryif (try (assert True; [ | solve [cancel]]; fail 1)) then fail
     else  idtac "Hint:  'cancel' or 'entailer!' solves the goal"
   end
 | tryif (try (assert True; [ | solve [entailer!]]; fail 1)) then fail
     else  idtac "Hint:  'entailer!' solves the goal"
 | match goal with |- ?A ⊢ ?B => 
         timeout 1 (unify A B);
         idtac "Hint: 'apply derives_refl' solves the goal.  You might wonder why 'auto' or 'cancel' does not solve this goal; the reason is that the left and right sides of the entailment are equal but not identical, and sometimes the attempt to unify terms like this would be far too slow to build into 'auto' or 'cancel'"
   end
 ].

Ltac hint_exists :=
  try match goal with |- _ ⊢ ?B => match B with context [@bi_exist _ ?t ] =>
       idtac "Hint: try 'Exists x', where x is a value of type " t " to instantiate the existential"
   end end.

Ltac hint_field_address_offset' AB :=
match AB with
 | Some ?X = Some ?Y => hint_field_address_offset' (X = Y)
 | offset_val _ _ = field_address0 _ _ _ =>idtac "Hint:  try 'rewrite field_address0_offset'"
 | offset_val _ _ = field_address _ _ _ =>idtac "Hint:  try 'rewrite field_address_offset'"
 | ?p = field_address0 _ _ ?p' =>unify p p'; idtac "Hint:  try 'rewrite field_address0_offset'"
 | ?p = field_address _ _ ?p' =>unify p p; idtac "Hint:  try 'rewrite field_address_offset'"
 | offset_val ?N1 ?A = offset_val ?N2 ?B => 
      tryif (try (assert (N1=N2) by (simpl; lia); fail 1)) then fail
      else hint_field_address_offset' (A=B)
 | field_address0 ?a ?b ?c  = offset_val ?d ?e => 
       hint_field_address_offset' (field_address0 a b c  = offset_val d e)
 | field_address ?a ?b ?c  = offset_val ?d ?e => 
       hint_field_address_offset' (field_address a b c  = offset_val d e)
 | field_address0 ?a ?b ?c  = ?c' => 
       unify c c';
       hint_field_address_offset' (field_address0 a b c  = c)
 | field_address ?a ?b ?c  = ?c' => 
       unify c c';
       hint_field_address_offset' (field_address a b c  = c)
end.

Ltac hint_saturate_local' P :=
 lazymatch P with
 | ?F _ => hint_saturate_local' F
 | _ => idtac "Hint: Nothing found in the 'saturate_local' HintDb that matches the "P" conjunct; you might want to define one, or unfold "P
 end.

Ltac hint_saturate_local P :=
match P with
| @bi_sep (iPropI _) ?A ?B => hint_saturate_local A; hint_saturate_local B
| @bi_and (iPropI _) ?A ?B => hint_saturate_local A; hint_saturate_local B
| @bi_wand (iPropI _) _ _ => idtac
| @bi_or (iPropI _) _ _ => idtac
| @bi_emp _ => idtac
| @bi_pure (iPropI _) _ => idtac
| @bi_forall (iPropI _) _ _ => idtac
| @bi_exist (iPropI _) _ _ => idtac
| _ => tryif (try (let x := fresh "x" in evar (x: Prop); assert (P ⊢ ⌜x⌝);
                    [subst x; solve [eauto with saturate_local] | fail 1]))
               then hint_saturate_local' P
               else idtac
end.

Ltac cancel_frame_hint := 
match goal with
| |- @bi_entails (iPropI _) _ ?A =>
  match A with context [fold_right_sepcon ?Frame] =>
      match goal with F := ?G : list mpred |- _ => constr_eq F Frame; is_evar G end;
      match A with context [@bi_sep] => idtac end;
      idtac "Hint: In order for the 'cancel' tactic to automatically instantiate the Frame, it must be able to cancel all the other right-hand-side conjuncts against some left-hand-side conjuncts.  Right now the r.h.s. conjuncts do not exactly match l.h.s. conjuncts; perhaps you can unfold or rewrite on both sides of the ⊢ so that they do cancel."
  end
end.

Ltac hint_progress any n :=
 lazymatch n with 10%nat => constr_eq any true
 | _ =>
 tryif lazymatch n with
 | 0%nat => print_sumbool_hint_hyp
 | 1%nat => tryif (try (progress autorewrite with sublist; fail 1)) then fail
     else  idtac "Hint:  try 'autorewrite with sublist'"
 | 2%nat => tryif (try (progress autorewrite with sublist in *|-; fail 1)) then fail
     else  idtac "Hint:  try 'autorewrite with sublist in *|-'"
 | 3%nat => tryif (try (progress autorewrite with norm; fail 1)) then fail
     else  idtac "Hint:  try 'autorewrite with norm'"
 | 4%nat => match goal with H: ?p = nullval |- _ => idtac "Hint: try 'subst " p "'" end
 | 5%nat => match goal with |- ?A = ?B => hint_field_address_offset' (A=B) end
 | 6%nat => match goal with D := @abbreviate _ _ |- _ =>
                      tryif (try (clear D; fail 1)) then fail
                      else  idtac "Hint:  clear" D
                    end
 | 7%nat => tryif (try (progress rewrite if_true by (auto; lia); fail 1)) then fail
     else  idtac "Hint:  try 'rewrite if_true by auto' or 'rewrite if_true by lia'"
 | 8%nat => tryif (try (progress rewrite if_false by (auto; lia); fail 1)) then fail
     else  idtac "Hint:  try 'rewrite if_false by auto' or 'rewrite if_false by lia'"
 |9%nat => lazymatch goal with
   | D := @abbreviate tycontext _, Po := @abbreviate ret_assert _ |- semax ?E ?D' ?Pre ?c ?Post =>
     tryif (constr_eq D D'; constr_eq Po Post) then print_hint_semax D Pre c Post
     else idtac "Hint: use abbreviate_semax to put your proof goal into a more standard form"
   | |- semax _ _ _ _ _ => 
         idtac "Hint: use abbreviate_semax to put your proof goal into a more standard form"
   | |- ENTAIL _, ?Pre ⊢ _ => 
              print_sumbool_hint Pre;
              idtac "Hint: try 'entailer!'";
              try match Pre with PROPx _ (LOCALx _ (SEPx ?R)) => hint_allp_left R end
   | |- @bi_entails (iPropI _) ?A ?B =>
              cancelable A; cancelable B;
              tryif (try (assert True; [ | rewrite ?bi.sep_emp, ?bi.emp_sep; progress cancel]; fail 1)) 
                then cancel_frame_hint
                else  idtac "Hint:  try 'cancel'" 
   end
  end
  then hint_progress true (S n)
  else hint_progress any (S n)
 end.

Ltac progress_entailer :=
 match goal with |- ?A =>
    progress entailer!; 
   try (match goal with |- ?B => constr_eq A B end; fail 1)
  end.

Ltac try_redundant_lia H :=
  match type of H with ?P =>
   tryif (try (clear H; assert P by lia; fail 1)) then idtac
   else idtac "Hint: hypothesis" H "is redundant, perhaps clear it"
 end.

Ltac hint_whatever :=
 try match goal with  |- @bi_entails (iPropI _) ?A ?B =>
            hint_saturate_local A;
            tryif (try (assert True; [ | progress_entailer]; fail 1)) then idtac
              else  idtac "Hint:  try 'entailer!'";
            try hint_allp_left A;
            try print_sumbool_hint (A ⊢ B)
 end;
 try match goal with |- @eq mpred _ _ => 
              idtac "Hint: try 'iSplit'"
      end;
 try match goal with
 | H: ?A = ?B |- _ => unify A B; idtac "Hint: hypothesis" H "is a tautology, perhaps 'clear" H "'"
 end;
 try match goal with
 | H: is_int I8 Signed (Vbyte _) |- _ =>       
   idtac "Hint: hypothesis" H "is a tautology, perhaps 'clear" H "'"
 end;
 try match goal with
 | H: is_int I8 Signed (Vint (Int.repr (Byte.signed _))) |- _ =>
   idtac "Hint: hypothesis" H "is a tautology, perhaps 'clear" H "'"
 end;
 try match goal with
 | H: Forall (value_fits _) _ |- _ =>
   idtac "Hint: hypothesis" H "is a 'value_fits' fact; often these are not useful, _maybe_ 'clear" H "'"    
 end;
 try match goal with
     H: is_pointer_or_null ?A, H': field_compatible _ _ ?A |- _ =>
      idtac "Hint:" H' "implies" H ", perhaps 'clear" H "'"
    end;
 try lazymatch goal with
 | H: @eq Z _ _ |- _ => try_redundant_lia H
 | H: Z.le _ _ |- _ =>  try_redundant_lia H
 | H: Z.lt _ _ |- _ =>  try_redundant_lia H
 | H: Z.ge _ _ |- _ =>  try_redundant_lia H
 | H: Z.gt _ _ |- _ =>  try_redundant_lia H
 | H: Z.le _ _ /\ Z.le _ _ |- _ =>  try_redundant_lia H
 | H: Z.le _ _ /\ Z.lt _ _ |- _ =>  try_redundant_lia H
 | H: Z.lt _ _ /\ Z.le _ _ |- _ =>  try_redundant_lia H
 | H: Z.lt _ _ /\ Z.lt _ _ |- _ =>  try_redundant_lia H
 end;
 hint_simplify_value_fits;
 tryif (try (rewrite prop_sepcon; fail 1)) then idtac else idtac "Hint: try 'rewrite prop_sepcon'";
 tryif (try (rewrite prop_sepcon2; fail 1)) then idtac else idtac "Hint: try 'rewrite prop_sepcon2'";
 try match goal with
  | H: Forall ?F ?L |- ?F' (Znth _ ?L') => 
       constr_eq F F'; constr_eq L L'; idtac "Hint: try 'apply forall_Znth; auto'"
  end;
 try match goal with |- context [Znth ?i (@map ?T _ ?F _)] =>
  idtac "Hint: perhaps 'rewrite Znth_map'"
 end.

Ltac hint_special := idtac.

Ltac hint :=
   first [hint_solves | hint_special; hint_exists; first [hint_progress false O | hint_whatever]].
