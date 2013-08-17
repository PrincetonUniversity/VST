Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Local Open Scope logic.


Lemma and_solvable_left:
 forall P Q : Prop,   P -> (P /\ Q) = Q.
Proof. intros. apply prop_ext; intuition. Qed.

Ltac and_solvable_left_aux1 :=
  match goal with |- _ /\ _ => fail 1 | |- _ => solve [auto] end.

Lemma and_solvable_right:
 forall Q P : Prop,   Q -> (P /\ Q) = P.
Proof. intros. apply prop_ext; intuition. Qed.

Ltac and_solvable_left P :=
 match P with
  | ?P1 /\ ?P2 => try rewrite (and_solvable_left P1) by auto;
                           and_solvable_left P2
  | _ => match P with
             | _ /\ _ => fail 1 
             | _ => first [ rewrite (and_solvable_right P) by auto
                                | rewrite (prop_true_andp' P) by auto
                                | apply (prop_right P); solve [auto]
                                | idtac
                                ]
             end
  end.

Ltac entailer' :=
 autorewrite with gather_prop;
 repeat ((simple apply go_lower_lem1 || apply derives_extract_prop || apply derives_extract_prop'); intro);
 subst_any;
 match goal with
 |  |- _ |-- _ =>
   repeat rewrite <- sepcon_assoc;
   saturate_local;  subst_any; 
   change SEPx with SEPx'; unfold PROPx, LOCALx, SEPx', local, lift1;
   unfold_lift; simpl;
   autorewrite with gather_prop;
   normalize;
   autorewrite with gather_prop;
   repeat rewrite and_assoc';
   match goal with 
   | |- _ |-- !! ?P && _ => and_solvable_left P
   | |- _ |-- !! ?P => and_solvable_left P; 
                               prop_right_cautious; try apply TT_right
   | |- _ => idtac
   end;
   auto
 | |- _ => normalize
 end.

Ltac entailer :=
 match goal with
 | |- PROPx _ _ |-- _ => 
       go_lower; 
       match goal with |- _ |-- _ => entailer' 
                                 | |- _ => idtac 
       end
 | |- _ |-- _ => entailer'
 | |- _ => fail "The entailer tactic works only on entailments   _ |-- _ "
 end.

Tactic Notation "entailer" "!" := 
  entailer; 
    first [simple apply andp_right; [apply prop_right | cancel ]
           | apply prop_right
           | cancel ].
