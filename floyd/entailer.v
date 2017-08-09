Require Import floyd.base2.
Require Import floyd.client_lemmas.
Require Import floyd.go_lower.
Require Import floyd.reptype_lemmas.
Require Import floyd.data_at_rec_lemmas.
Require Import floyd.field_at floyd.nested_field_lemmas.
Require Import floyd.sublist.

Local Open Scope logic.

Lemma isptr_force_val_sem_cast_neutral :
  forall p, isptr p -> isptr (force_val (sem_cast_neutral p)).
Proof.
intros. destruct p; try contradiction; apply I.
Qed.
Hint Resolve isptr_force_val_sem_cast_neutral : norm.

Hint Rewrite (Znth_map Int.zero) (Znth_map Vundef)
    using (auto; rewrite ?Zlength_map in *; omega) : sublist.

Lemma FF_local_facts: forall {A}{NA: NatDed A}, (FF:A) |-- !!False.
Proof. intros. apply FF_left. Qed.
Hint Resolve @FF_local_facts: saturate_local.

(*** Omega stuff ***)

Ltac omegable' A :=
lazymatch A with
| @eq nat _ _ => idtac
| @eq Z _ _ => idtac
| Z.lt _ _ => idtac
| Z.le _ _ => idtac
| Z.gt _ _ => idtac
| Z.ge _ _ => idtac
| Peano.lt _ _ => idtac
| Peano.le _ _ => idtac
| Peano.gt _ _ => idtac
| Peano.ge _ _ => idtac
| ~ ?A => omegable' A
| ?A /\ ?B => omegable' A; omegable' B
end.

Ltac omegable := match goal with |- ?A => omegable' A end.

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
 | H: not (@eq Z _ _) |- _ => revert H
 | H: @neq nat _ _ |- _ => revert H
 | H: not (@eq nat _ _) |- _ => revert H
 | H: _ <> _ |- _ => revert H
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
  match goal with
  | |- (_ >= _)%nat => apply <- Nat2Z.inj_ge
  | |- (_ > _)%nat => apply <- Nat2Z.inj_gt
  | |- (_ <= _)%nat => apply <- Nat2Z.inj_le
  | |- (_ < _)%nat => apply <- Nat2Z.inj_lt
  | |- @eq nat _ _ => apply Nat2Z.inj
  | |- _ => idtac
  end;
 repeat first
     [ simpl_const
     | rewrite Nat2Z.id
     | rewrite Nat2Z.inj_add
     | rewrite Nat2Z.inj_mul
     | rewrite Z2Nat.id by Omega'' L
     | rewrite Nat2Z.inj_sub by Omega'' L
     | rewrite Z2Nat.inj_sub by Omega'' L
     | rewrite Z2Nat.inj_add by Omega'' L
     ];
  Omega' L.

Tactic Notation "Omega" tactic(L) := (omegable; Omega'' L).

Ltac helper1 :=
 match goal with
   | |- context [Zlength ?A] => add_nonredundant (Zlength_correct A)
   | |- context [Int.max_unsigned] => add_nonredundant int_max_unsigned_eq
   | |- context [Int.max_signed] => add_nonredundant int_max_signed_eq
   | |- context [Int.min_signed] => add_nonredundant int_min_signed_eq
  end.

Ltac Omega0 := Omega (solve [ helper1 ]).

(*** End of Omega stuff *)

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

Lemma prop_and_same_derives {A}{NA: NatDed A}:
  forall P Q, Q |-- !! P   ->   Q |-- !!P && Q.
Proof.
intros. apply andp_right; auto.
Qed.

Arguments denote_tc_isptr v / .
Arguments denote_tc_iszero !v .
Arguments denote_tc_nonzero !v .
Arguments denote_tc_igt i !v .
Arguments denote_tc_Zge z !v .
Arguments denote_tc_Zle z !v .
Arguments denote_tc_samebase !v1 !v2 .
Arguments denote_tc_nodivover !v1 !v2 .
Arguments denote_tc_initialized id ty rho / .

Ltac simpl_denote_tc :=
 simpl denote_tc_isptr;
 simpl denote_tc_iszero;
 simpl denote_tc_nonzero;
 simpl denote_tc_igt;
 simpl denote_tc_Zge;
 simpl denote_tc_Zle;
 simpl denote_tc_samebase;
 simpl denote_tc_nodivover;
 simpl denote_tc_initialized.

Lemma valid_pointer_weak:
 forall a, valid_pointer a |-- weak_valid_pointer a.
Proof.
intros.
unfold valid_pointer, weak_valid_pointer.
change predicates_hered.orp with orp. (* delete me *)
apply orp_right1.
auto.
Qed.

Lemma denote_tc_test_eq_split:
  forall P x y,
    P |-- valid_pointer x ->
    P |-- valid_pointer y ->
    P |-- denote_tc_test_eq x y.
Proof.
 intros.
 eapply derives_trans with (valid_pointer x && valid_pointer y).
 apply andp_right; auto.
 clear H H0.
 unfold denote_tc_test_eq, weak_valid_pointer.
change predicates_hered.orp with orp.
 destruct x; try (apply andp_left1; apply @FF_left); try apply @TT_right;
 destruct y; try (apply andp_left2; apply @FF_left); try apply @TT_right.
 apply andp_derives; try apply derives_refl.
 apply andp_derives; try apply derives_refl.
 apply orp_right1. apply derives_refl.
 rewrite andp_comm.
 apply andp_derives; try apply derives_refl.
 apply orp_right1. apply derives_refl.
 unfold test_eq_ptrs.
 if_tac; auto.
 apply andp_derives; apply valid_pointer_weak.
Qed.

Lemma valid_pointer_null:
  forall P, P |-- valid_pointer nullval.
Proof.
  intros. simpl valid_pointer.
 change predicates_hered.prop with prop. (* delete me *)
 normalize.
Qed.


Lemma extend_valid_pointer:
  forall p Q, valid_pointer p * Q |-- valid_pointer p.
Proof.
intros.
 unfold valid_pointer.
 pose proof (extend_tc.extend_valid_pointer' p 0).
 pose proof (predicates_hered.boxy_e _ _ H).

Admitted.

 Lemma sepcon_valid_pointer1:
     forall (P Q: mpred) p,
        P |-- valid_pointer p ->
        P * Q |-- valid_pointer p.
Proof.
intros.
 eapply derives_trans; [apply sepcon_derives; [eassumption | apply TT_right] |].
 clear H.
 apply extend_valid_pointer.
Qed.

 Lemma sepcon_valid_pointer2:
     forall (P Q: mpred) p,
        P |-- valid_pointer p ->
        Q * P |-- valid_pointer p.
Proof.
 intros. rewrite sepcon_comm; apply sepcon_valid_pointer1.
 auto.
Qed.

 Lemma andp_valid_pointer1:
     forall (P Q: mpred) p,
        P |-- valid_pointer p ->
        P && Q |-- valid_pointer p.
Proof.
intros.
 apply andp_left1; auto.
Qed.

 Lemma andp_valid_pointer2:
     forall (P Q: mpred) p,
        P |-- valid_pointer p ->
        Q && P |-- valid_pointer p.
Proof.
intros.
 apply andp_left2; auto.
Qed.

Lemma valid_pointer_zero:
  forall P, P |-- valid_pointer (Vint (Int.repr 0)).
Proof.
 intros.
 apply valid_pointer_null.
Qed.

Hint Resolve sepcon_valid_pointer1 sepcon_valid_pointer2 : valid_pointer.
Hint Resolve andp_valid_pointer1 andp_valid_pointer2 : valid_pointer.
Hint Resolve valid_pointer_null : valid_pointer.
Hint Resolve valid_pointer_zero : valid_pointer.

(* TODO: test_order need to be added *)
Ltac solve_valid_pointer :=
match goal with
| |- _ |-- denote_tc_test_eq _ _ && _ =>
           apply andp_right;
               [apply denote_tc_test_eq_split;
                solve [auto 50 with valid_pointer] | ]
| |- _ |-- valid_pointer _ && _ =>
           apply andp_right; [ solve [auto 50 with valid_pointer] | ]
| |- _ |-- weak_valid_pointer _ && _ =>
           apply andp_right; [ solve [auto 50 with valid_pointer] | ]
| |- _ |-- denote_tc_test_eq _ _ =>
              auto 50 with valid_pointer
| |- _ |-- valid_pointer _ =>
              auto 50 with valid_pointer
| |- _ |-- weak_valid_pointer _ =>
              auto 50 with valid_pointer
end.

Hint Rewrite (@TT_andp mpred _) : gather_prop.
Hint Rewrite (@andp_TT mpred _) : gather_prop.

Ltac pull_out_props :=
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
    autorewrite with gather_prop;
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true).

Ltac ent_iter :=
    autorewrite with gather_prop;
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
(*   saturate_local; *)
   repeat erewrite unfold_reptype_elim in * by (apply JMeq_refl; reflexivity);
   simpl_compare;
   simpl_denote_tc;
   subst_any;
   try autorewrite with entailer_rewrite in *;
   try solve_valid_pointer;
   repeat data_at_conflict_neq.

Lemma and_False: forall x, (x /\ False) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma and_True: forall x, (x /\ True) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma True_and: forall x, (True /\ x) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma False_and: forall x, (False /\ x) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.
Ltac splittable :=
 match goal with
 | |- _ <= _ < _ => fail 1
 | |- _ < _ <= _ => fail 1
 | |- _ <= _ <= _ => fail 1
 | |- _ < _ < _ => fail 1
 | |- _ <-> _ => fail 1
 | |- _ /\ _ => idtac
 end.

Lemma ptr_eq_refl: forall x, isptr x -> ptr_eq x x.
Proof.
destruct x; simpl; intros; try contradiction.
split; auto. apply Int.eq_true.
Qed.
Hint Resolve ptr_eq_refl : prove_it_now.

Hint Extern 4 (value_fits _ _ _) =>
   (rewrite ?proj_sumbool_is_true by auto;
    rewrite ?proj_sumbool_is_false by auto;
    repeat simplify_value_fits; auto) : prove_it_now.

Ltac prove_it_now :=
 first [ splittable; fail 1
        | computable
        | apply Coq.Init.Logic.I
        | reflexivity
        | Omega0
        | repeat match goal with H: ?A |- _ => has_evar A; clear H end;
          auto with prove_it_now field_compatible;
          autorewrite with norm entailer_rewrite; normalize;
          first [eapply field_compatible_nullval; eassumption
                 | eapply field_compatible_nullval1; eassumption
                 | eapply field_compatible_nullval2; eassumption
                 ]
         ].

Ltac try_prove_it_now :=
 first [match goal with H := _ |- _ => instantiate (1:=True) in H; prove_it_now end
       | eassumption].

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
    match goal with H:_ |- ?A =>
         no_evars A;
         clear H; try immediate; auto; prove_it_now; fail
    end.

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

Ltac prop_right_cautious :=
 try solve [simple apply prop_right; auto; prove_it_now].

Ltac prune_conjuncts :=
 repeat rewrite and_assoc';
 first [simple eapply try_conjuncts_prop;
              [intro; try_conjuncts
              | cbv beta; repeat rewrite and_True; prop_right_cautious ]
         | simple eapply try_conjuncts_prop_and;
              [intro; try_conjuncts
              | cbv beta; repeat rewrite and_True; try simple apply go_lower_lem1]
         | idtac].

Ltac entailer' :=
 repeat (progress (ent_iter; normalize));
 try simple apply prop_and_same_derives;
 prune_conjuncts;
 try rewrite (prop_true_andp True) by apply Coq.Init.Logic.I;
 try solve_valid_pointer;
 try first [apply derives_refl
              | simple apply FF_left
              | simple apply TT_right].

Ltac entailer :=
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 match goal with
 | |- ?P |-- _ =>
    match type of P with
    | ?T => unify T (environ->mpred); go_lower
    | _ => clear_Delta; pull_out_props
    end
 | |- _ => fail "The entailer tactic works only on entailments   _ |-- _ "
 end;
 saturate_local;
 entailer';
 rewrite <- ?sepcon_assoc.

Lemma my_auto_lem:
 forall (P Q: Prop), (P -> Q) -> (P -> Q).
Proof. auto. Qed.

Ltac my_auto_iter H :=
 first [instantiate (1:=True) in H;  prove_it_now
       | splittable;
         eapply try_conjuncts_lem;
            [let H1 := fresh in intro H1; my_auto_iter H1
            |let H1 := fresh in intro H1; my_auto_iter H1
            | apply H ]
       | apply H
       ].

Ltac all_True :=  solve [repeat simple apply conj; simple apply Coq.Init.Logic.I].

Ltac my_auto_reiter :=
 first [simple apply conj; [all_True | ]; my_auto_reiter
        |simple apply conj; [ | all_True]; my_auto_reiter
        |splittable; eapply try_conjuncts_lem;
                [intro; my_auto_reiter
                |intro; my_auto_reiter
                |eassumption]
        |eassumption].

Ltac my_auto :=
 rewrite ?isptr_force_ptr by auto;
 let H := fresh in eapply my_auto_lem; [intro H; my_auto_iter H | ];
 try all_True;
 (eapply my_auto_lem; [intro; my_auto_reiter | ]);
 normalize.

Lemma prop_and_same_derives' {A}{NA: NatDed A}:
  forall (P: Prop) Q,   P   ->   Q |-- !!P && Q.
Proof.
intros. apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma empTrue:
 @derives mpred Nveric (@emp mpred Nveric Sveric) (@prop mpred Nveric True).
Proof.
apply prop_right; auto.
Qed.

Ltac entailer_for_return :=
 go_lower;
 unfold main_post; simpl;
 try simple apply empTrue;
 saturate_local; ent_iter;
 normalize;
 repeat erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]);
 try match goal with 
 | |- _ |-- ?A =>
   match A with context [eval_id ?i (globals_only _)] =>
    fail 3 "Your postcondition refers to local variable " i 
     "but the only local variable that should appear in a function postcondition is ret_temp"
   end
 end;
 entailer';
 rewrite <- ?sepcon_assoc;
 try match goal with rho: environ |- _ => clear rho end.

Ltac entbang :=
 intros;
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 match goal with
 | |- local _ && ?P |-- _ => go_lower; try simple apply empTrue
 | |- ?P |-- _ =>
    match type of P with
    | ?T => unify T mpred; pull_out_props
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ |-- _ "
 end;
 saturate_local;
 ent_iter;
 first [ contradiction
        | simple apply prop_right; my_auto
        | match goal with |- ?Q |-- !! _ && ?Q' => constr_eq  Q Q';
                      simple apply prop_and_same_derives'; my_auto
          end
        | simple apply andp_right;
            [apply prop_right; my_auto 
            | cancel; rewrite <- ?sepcon_assoc; autorewrite with norm ]
        | normalize; cancel; rewrite <- ?sepcon_assoc
        ].

Tactic Notation "entailer" "!" := entbang.

Ltac elim_hyps :=  (* not in use anywhere? *)
 repeat match goal with
 | H: isptr ?x |- _ =>
     let x1 := fresh x "_b" in let x2 := fresh x "_ofs" in
     destruct x as [ | | | | | x1 x2]; inv H
 | H: ptr_eq _ _ |- _ => apply ptr_eq_e in H; subst_any
 end.

Ltac aggressive :=
  repeat split; auto; elim_hyps; simpl; (computable || auto).

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

Lemma ungather_admit : forall P, P.
Admitted. (* this is to be used only for test scaffolding. *)

Lemma EVAR_i: forall P: Prop, P -> EVAR P.
Proof. intros. apply H. Qed.

Ltac ungather_entail :=
match goal with
  | |- EVAR (forall x : ?t, _) =>
       let x' := fresh x in evar (x' : t);
       let x'' := fresh x in apply EVAR_i; intro x'';
       replace x'' with x'; [ungather_entail; clear x'' | apply ungather_admit ]
  | |- _ => intros
 end.

Lemma offset_val_sizeof_hack:
 forall cenv t i p,
   isptr p ->
   i=0 ->
   (offset_val (@sizeof cenv t * i) p = p) = True.
Proof.
intros.
subst.
destruct p; try contradiction.
simpl. rewrite Z.mul_0_r.
rewrite Int.add_zero.
apply prop_ext; intuition.
Qed.
Hint Rewrite offset_val_sizeof_hack : norm.

Lemma offset_val_sizeof_hack2:
 forall cenv t i j p,
   isptr p ->
   i=j ->
   (offset_val (@sizeof cenv t * i) p = offset_val (@sizeof cenv t * j) p) = True.
Proof.
intros.
subst.
apply prop_ext; intuition.
Qed.
Hint Rewrite offset_val_sizeof_hack2 : norm.

Lemma offset_val_sizeof_hack3:
 forall cenv t i p,
   isptr p ->
   i=1 ->
   (offset_val (@sizeof cenv t * i) p = offset_val (@sizeof cenv t) p) = True.
Proof.
intros.
subst.
rewrite Z.mul_1_r.
apply prop_ext; intuition.
Qed.
Hint Rewrite offset_val_sizeof_hack3 : norm.

Ltac make_Vptr c :=
  let H := fresh in assert (isptr c) by auto;
  destruct c; try (contradiction H); clear H.

Lemma Zmax0r: forall n, 0 <= n -> Z.max 0 n = n.
Proof.
intros. apply Z.max_r; auto.
Qed.
Hint Rewrite Zmax0r using (try computable; Omega0) : norm.
