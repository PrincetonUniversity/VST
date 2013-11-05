Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Local Open Scope logic.

Arguments sem_binarith sem_int sem_long sem_float !t1 !t2 / v1 v2.
Arguments Cop.sem_cast v !t1 !t2 / .

Ltac simpl_compare :=
 match goal with
 | H: Vint _ = _ |- _ => 
         revert H; simpl_compare; intro H;
         try (simpl in H; apply Vint_inj in H;
               match type of H with ?a = ?b => 
                  first [subst a | subst b | idtac]
               end)
 | H: typed_true _ _ |- _ =>
         revert H; simpl_compare; intro H;
         first [apply typed_true_ptr in H
                 | apply typed_true_of_bool in H;
                   first [apply (int_cmp_repr Clt) in H;
                            [ | repable_signed ..]; simpl in H
                          | apply (int_cmp_repr Ceq) in H;
                             [ | repable_signed ..]; simpl in H
                          | idtac ]
                 | discriminate H
                 | idtac ]
 | H: typed_false _ _ |- _ =>
         revert H; simpl_compare; intro H;
         first [ apply typed_false_ptr in H
                | apply typed_false_of_bool in H;
                   first [apply (int_cmp_repr' Clt) in H;
                            [ | repable_signed ..]; simpl in H
                          | apply (int_cmp_repr' Ceq) in H;
                            [ | repable_signed ..]; simpl in H
                          | idtac]
                 | discriminate H
                 | idtac ]
 | H : Int.lt _ _ = false |- _ => 
         revert H; simpl_compare; intro H;
         try (apply (int_cmp_repr' Clt) in H ;
                    [ | repable_signed ..]; simpl in H)
 | H : Int.lt _ _ = true |- _ =>
         revert H; simpl_compare;  intro H;
         try (apply (int_cmp_repr Clt) in H ;
                    [ | repable_signed ..]; simpl in H)
 | H : Int.eq _ _ = false |- _ => 
         revert H; simpl_compare;  intro H;
         try (apply (int_cmp_repr' Ceq) in H ;
                    [ | repable_signed ..]; simpl in H)
 | H : Int.eq _ _ = true |- _ => 
         revert H; simpl_compare;  intro H;
         try (apply (int_cmp_repr Ceq) in H ;
                    [ | repable_signed ..]; simpl in H)
 | |- _ => idtac
end.

Ltac no_evars P := (has_evar P; fail 1) || idtac.

Inductive computable: forall {A}(x: A), Prop :=
| computable_Zlt: forall x y, computable x -> computable y -> computable (Z.lt x y)
| computable_Zle: forall x y, computable x -> computable y -> computable (Z.le x y)
| computable_Zgt: forall x y, computable x -> computable y -> computable (Z.gt x y)
| computable_Zge: forall x y, computable x -> computable y -> computable (Z.ge x y)
| computable_eq: forall  A (x y: A), computable x -> computable y -> computable (eq x y)
| computable_ne: forall  A (x y: A), computable x -> computable y -> computable (x <> y)
| computable_Zpos: forall x, computable x -> computable (Zpos x)
| computable_Zneg: forall x, computable x -> computable (Zneg x)
| computable_Z0: computable Z0
| computable_xI: forall x, computable x -> computable (xI x)
| computable_xO: forall x, computable x -> computable (xO x)
| computable_xH: computable xH
| computable_Zadd: forall x y, computable x -> computable y -> computable (Z.add x y)
| computable_Zsub: forall x y, computable x -> computable y -> computable (Z.sub x y)
| computable_Zmul: forall x y, computable x -> computable y -> computable (Z.mul x y)
| computable_Zdiv: forall x y, computable x -> computable y -> computable (Z.div x y)
| computable_Zmod: forall x y, computable x -> computable y -> computable (Zmod x y)
| computable_Zopp: forall x, computable x -> computable (Z.opp x)
| computable_Inteq: forall x y, computable x -> computable y -> computable (Int.eq x y)
| computable_Intlt: forall x y, computable x -> computable y -> computable (Int.lt x y)
| computable_Intltu: forall x y, computable x -> computable y -> computable (Int.ltu x y)
| computable_Intadd: forall x y, computable x -> computable y -> computable (Int.add x y)
| computable_Intsub: forall x y, computable x -> computable y -> computable (Int.sub x y)
| computable_Intmul: forall x y, computable x -> computable y -> computable (Int.mul x y)
| computable_Intneg: forall x, computable x  -> computable (Int.neg x)
| computable_Ceq: computable Ceq
| computable_Cne: computable Cne
| computable_Clt: computable Clt
| computable_Cle: computable Cle
| computable_Cgt: computable Cgt
| computable_Cge: computable Cge
| computable_Intcmp: forall op x y, 
  computable op -> computable x -> computable y -> computable (Int.cmp op x y)
| computable_Intcmpu: forall op x y, 
  computable op -> computable x -> computable y -> computable (Int.cmpu op x y)
| computable_Intrepr: forall x, computable x -> computable (Int.repr x)
| computable_Intsigned: forall x, computable x -> computable (Int.signed x)
| computable_Intunsigned: forall x, computable x -> computable (Int.unsigned x).

Hint Constructors computable : computable. 

Hint Extern 5 (@computable _ _) => 
   match goal with d := ?x |- computable (?d) => 
         unfold d; auto 50 with computable 
    end : computable.

Ltac computable := match goal with |- ?x =>
 no_evars x;
 let H := fresh in assert (H: computable x) by auto 50 with computable; 
 clear H;
 compute; clear; auto; congruence
end.

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
  | ?P1 /\ ?P2 => try (no_evars P1; try rewrite (and_solvable_left P1) by (computable || auto));
                           and_solvable_left P2
  | _ => match P with
             | _ /\ _ => fail 1 
             | _ => first [ no_evars P; rewrite (and_solvable_right P) by (computable || auto)
                                | rewrite (prop_true_andp' P) by (computable || auto)
                                | apply (prop_right P); solve [(computable || auto)]
                                | idtac
                                ]
             end
  end.

Lemma prop_and_same_derives {A}{NA: NatDed A}:
  forall P Q, Q |-- !! P   ->   Q |-- !!P && Q.
Proof.
intros. apply andp_right; auto.
Qed.


Ltac ent_iter :=
    autorewrite with gather_prop;
    repeat (((repeat simple apply go_lower_lem1'; simple apply go_lower_lem1)
                || simple apply derives_extract_prop 
                || simple apply derives_extract_prop');
                fancy_intro);
   saturate_local;
   subst_any;
   simpl_compare;
   normalize.

Ltac entailer' :=  
 repeat (progress ent_iter);
(* ((progress ent_iter; fail 5 "bingo") || idtac); *)
 try simple apply prop_and_same_derives;
 repeat rewrite and_assoc';
 match goal with 
   | |- _ |-- !! ?P && _ => and_solvable_left P
   | |- _ |-- !! ?P => and_solvable_left P; 
                               prop_right_cautious; try apply TT_right;
                               repeat simple apply conj; (computable||auto)
   | |- _ => idtac
 end;
 auto.

Ltac entailer :=
 match goal with
 | |- ?P |-- _ => 
    match type of P with
    | ?T => unify T (environ->mpred); go_lower
    | _ => idtac
    end
 | |- _ => fail "The entailer tactic works only on entailments   _ |-- _ "
 end;
 entailer'.

Ltac prop_right_solve := 
apply prop_right; repeat simple apply conj; 
  (computable || auto). 
 
Tactic Notation "entailer" "!" := 
  entailer; 
    first [simple apply andp_right; [prop_right_solve | cancel ]
           | prop_right_solve
           | cancel
           | idtac ].

Ltac elim_hyps :=
 repeat match goal with
 | H: isptr ?x |- _ =>
     let x1 := fresh x "_b" in let x2 := fresh x "_ofs" in
     destruct x as [ | | | | x1 x2]; inv H
 | H: ptr_eq _ _ |- _ => apply ptr_eq_e in H; subst_any
 end.

Ltac aggressive :=
  repeat split; auto; elim_hyps; simpl; (computable || auto).

Ltac entailer1 :=
  entailer; 
    first [simple apply andp_right; 
               [apply prop_right; aggressive | cancel ]
           | apply prop_right; aggressive
           | cancel
           | aggressive ].

(**** try this out here, for now ****)

Hint Rewrite Int.signed_repr using repable_signed : norm.
Hint Rewrite Int.unsigned_repr using repable_signed : norm.

(************** TACTICS FOR GENERATING AND EXECUTING TEST CASES *******)

Definition EVAR (x: Prop) := x.
Lemma EVAR_e: forall x, EVAR x -> x. 
Proof. intros. apply H. Qed.

Ltac gather_entail :=
repeat match goal with
 | A := _ |- _ =>  clear A || (revert A; match goal with |- ?B => no_evars B end)
 | H : ?P |- _ =>
  match type of P with
  | Prop => match P with name _ => fail 2 | _ => revert H; match goal with |- ?B => no_evars B end end
  | _ => clear H || (revert H; match goal with |- ?B => no_evars B end)
  end
end;
repeat match goal with 
 | x := ?X |- _ => is_evar X; clearbody x; revert x; apply EVAR_e
end;
repeat match goal with
  | H : name _ |- _ => revert H
 end.

Lemma admit_dammit : forall P, P.
Admitted.

Lemma EVAR_i: forall P: Prop, P -> EVAR P.
Proof. intros. apply H. Qed.

Ltac ungather_entail :=
match goal with
  | |- EVAR (forall x : ?t, _) => 
       let x' := fresh x in evar (x' : t);
       let x'' := fresh x in apply EVAR_i; intro x'';
       replace x'' with x'; [ungather_entail; clear x'' | apply admit_dammit ]
  | |- _ => intros
 end.

