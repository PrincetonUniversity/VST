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
         simpl in H; revert H; simpl_compare; intro H;
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
         simpl in H; revert H; simpl_compare; intro H;
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
| computable_O: computable O
| computable_S: forall x, computable x -> computable (S x)
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
| computable_Zmax: forall x y, computable x -> computable y -> computable (Z.max x y)
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
| computable_Intunsigned: forall x, computable x -> computable (Int.unsigned x)
| computable_two_power_nat: forall x, computable x -> computable (two_power_nat x)
| computable_max_unsigned: computable (Int.max_unsigned)
| computable_align: forall x y, computable x -> computable y -> computable (align x y).

Hint Constructors computable : computable. 
Hint Extern 1 (computable ?A) => (unfold A) : computable.

(*
Hint Extern 5 (@computable _ _) => 
   match goal with d := ?x |- computable (?d) => 
         unfold d; auto 50 with computable 
    end : computable.
*)

Ltac computable := match goal with |- ?x =>
 no_evars x;
 let H := fresh in assert (H: computable x) by auto 80 with computable; 
 clear H;
 compute; clear; auto; congruence
end.

(*
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
*)

Lemma prop_and_same_derives {A}{NA: NatDed A}:
  forall P Q, Q |-- !! P   ->   Q |-- !!P && Q.
Proof.
intros. apply andp_right; auto.
Qed.

(* try_conjuncts.  The purpose of this is to avoid splitting any
  goal into two subgoals, for the reason that perhaps the 
  user wants to simplify things above the line before splitting.
   On the other hand, if the current goal is  A/\B/\C/\D
  where B and D are easily provable, one wants to leave the
  goal A/\C.
*)
Lemma try_conjuncts_lem2: forall A B : Prop,
   B -> A -> (A /\ B).
Proof. intuition. Qed.

Lemma try_conjuncts_lem: forall A B A' B' : Prop,
   (A -> A') -> (B -> B') -> (A /\ B -> A' /\ B').
Proof. intuition. Qed.

Lemma try_conjuncts_start: forall A B: Prop,
   (A -> B) -> (A -> B).
 Proof. intuition. Qed.

Ltac try_conjuncts_solver :=
    match goal with |- ?A => no_evars A end;
    first [apply I | computable | solve [auto] | omega ].

Ltac try_conjuncts :=
 first [ simple eapply conj;
                [try_conjuncts_solver | try_conjuncts ]
        | simple eapply try_conjuncts_lem2;
                [try_conjuncts_solver | match goal with H:_ |- _ => apply H end ]
        | simple eapply try_conjuncts_lem; 
            [intro; try_conjuncts | intro; try_conjuncts 
            |match goal with H:_ |- _ => apply H end ]
        | match goal with H:_ |- _ => instantiate (1:=True) in H; 
                try_conjuncts_solver
          end
        | match goal with H:_ |- _ => apply H end
        ].

Lemma try_conjuncts_prop_and:
  forall {A}{NA: NatDed A} (S: A) (P P': Prop) Q, 
      (P' -> P) ->
      S |-- !! P' && Q ->
      S |-- !! P && Q.
Proof. intros. 
 eapply derives_trans; [apply H0 |].
 apply andp_derives; auto.
 apply prop_derives; auto.
Qed.


Lemma try_conjuncts_prop:
  forall {A}{NA: NatDed A} (S: A) (P P': Prop), 
      (P' -> P) ->
      S |-- !! P' ->
      S |-- !! P .
Proof. intros. 
 eapply derives_trans; [apply H0 |].
 apply prop_derives; auto.
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
 first [simple eapply try_conjuncts_prop; 
              [intro; try_conjuncts 
              | cbv beta; repeat rewrite and_True; prop_right_cautious ]
         | simple eapply try_conjuncts_prop_and;
              [intro; try_conjuncts 
              | cbv beta; repeat rewrite and_True; try simple apply go_lower_lem1]
         | idtac];
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

Ltac prop_solve := 
  match goal with |- ?A => (has_evar A; repeat simple apply conj) || (repeat split) end;
  (computable || auto). 
 
Tactic Notation "entailer" "!" := 
  entailer; 
  first [simple apply andp_right; [apply prop_right; prop_solve | cancel ]
         | simple apply prop_right; prop_solve
         | match goal with |- _ |-- _ => try cancel end
         | prop_solve
         ].

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

(*** Omega stuff ***)
Ltac  add_nonredundant' F T G :=
   match G with
        | T -> _ => fail 1
        | _ -> ?G' => add_nonredundant' F T G' || fail 1
        | _ => generalize F
  end.

Ltac  add_nonredundant F :=
 match type of F with ?T =>
   match goal with |- ?G => add_nonredundant' F T G
   end
 end.

Lemma omega_aux: forall {A} (B C: A),
   B=C -> forall D, (B=C->D) -> D.
Proof. intuition. Qed.

Ltac is_const A :=
 match A with
 | Z0 => idtac
 | Zpos ?B => is_const B
 | Zneg ?B => is_const B
 | xH => idtac
 | xI ?B => is_const B
 | xO ?B => is_const B
 | O => idtac
 | S ?B => is_const B
 end.

Ltac simpl_const :=
  match goal with
   | |- context [Z.of_nat ?A] =>
     is_const A; 
     let H := fresh in set (H:= Z.of_nat A); simpl in H; unfold H; clear H
   | |- context [Z.to_nat ?A] =>
     is_const A; 
     let H := fresh in set (H:= Z.to_nat A); simpl in H; unfold H; clear H
  end.

Ltac Omega' L :=
repeat match goal with
 | H: @eq Z _ _ |- _ => revert H
 | H: @eq nat _ _ |- _ => revert H
 | H: @neq Z _ _ |- _ => revert H
 | H: @neq nat _ _ |- _ => revert H
 | H: Z.lt _ _ |- _ => revert H
 | H: Z.le _ _ |- _ => revert H
 | H: Z.gt _ _ |- _ => revert H
 | H: Z.ge _ _ |- _ => revert H
 | H: Z.le _ _ /\ Z.le _ _ |- _ => revert H
 | H: Z.lt _ _ /\ Z.le _ _ |- _ => revert H
 | H: Z.le _ _ /\ Z.lt _ _ |- _ => revert H
 | H: lt _ _ |- _ => revert H
 | H: le _ _ |- _ => revert H
 | H: gt _ _ |- _ => revert H
 | H: ge _ _ |- _ => revert H
 | H: le _ _ /\ le _ _ |- _ => revert H
 | H: lt _ _ /\ le _ _ |- _ => revert H
 | H: le _ _ /\ lt _ _ |- _ => revert H
 | H := ?A : Z |- _ => apply (omega_aux H A (eq_refl _)); clearbody H 
 | H := ?A : nat |- _ => apply (omega_aux H A (eq_refl _)); clearbody H 
 | H: _ |- _ => clear H
 end;
 clear;
 abstract (
   repeat (L || simpl_const);
   intros; omega).

Ltac Omega'' L :=
 first [ apply Nat2Z.inj_ge | apply Nat2Z.inj_gt
        | apply Nat2Z.inj_le | apply Nat2Z.inj_lt
        | idtac];
 repeat first
     [ simpl_const
     | rewrite Nat2Z.id
     | rewrite Nat2Z.inj_add
     | rewrite Z2Nat.id by Omega'' L
     | rewrite Nat2Z.inj_sub
       by (apply Nat2Z.inj_le; 
             repeat rewrite Nat2Z.inj_add; 
             rewrite Z2Nat.id by Omega'' L; Omega'' L)
     | rewrite Z2Nat.inj_sub by Omega'' L
     | rewrite Z2Nat.inj_add by Omega'' L
     ];
  Omega' L.

Tactic Notation "Omega" tactic(L) := Omega'' L.

Ltac helper1 := 
 match goal with
   | |- context [Zlength ?A] => add_nonredundant (Zlength_correct A)
   | |- context [Int.max_unsigned] => add_nonredundant int_max_unsigned_eq
   | |- context [Int.max_signed] => add_nonredundant int_max_signed_eq
   | |- context [Int.min_signed] => add_nonredundant int_min_signed_eq
  end. 

(*** End of Omega stuff *)
