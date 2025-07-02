Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at VST.floyd.nested_field_lemmas.

Local Open Scope logic.

Lemma ptrofs_of_ints_unfold: 
  forall x, Ptrofs.of_ints x = Ptrofs.repr (Int.signed x).
Proof. reflexivity. Qed.
#[export] Hint Rewrite ptrofs_of_ints_unfold : norm.

Lemma ptrofs_of_intu_unfold: 
  forall x, Ptrofs.of_intu x = Ptrofs.repr (Int.unsigned x).
Proof. reflexivity. Qed.
#[export] Hint Rewrite ptrofs_of_intu_unfold : norm.

Lemma isptr_force_val_sem_cast_neutral :
  forall p, isptr p -> isptr (force_val (sem_cast_pointer p)).
Proof.
intros. destruct p; try contradiction; apply I.
Qed.
#[export] Hint Resolve isptr_force_val_sem_cast_neutral : norm.

Lemma FF_local_facts: forall {A}{NA: NatDed A}, (FF:A) |-- !!False.
Proof. intros. apply FF_left. Qed.
#[export] Hint Resolve FF_local_facts: saturate_local.

Ltac simpl_compare :=
 match goal with
 | H: Vint _ = _ |- _ =>
         revert H; simpl_compare; intro H;
         try (apply Vint_inj in H;
               match type of H with ?a = ?b =>
                  first [safe_subst a | safe_subst b | idtac]
               end)
 | H: typed_true _ _ |- _ =>
         revert H; simpl_compare; intro H;
         first [apply typed_true_ptr in H
                 | apply typed_true_of_bool in H;
                   first [apply (int_cmp_repr Clt) in H;
                            [ | rep_lia ..]; red in H
                          | apply (int_cmp_repr Ceq) in H;
                             [ | rep_lia ..]; red in H
                          | idtac ]
                 | discriminate H
                 | idtac ]
 | H: typed_false _ _ |- _ =>
         revert H; simpl_compare; intro H;
         first [ apply typed_false_ptr in H
                | apply typed_false_of_bool in H;
                   first [apply (int_cmp_repr' Clt) in H;
                            [ | rep_lia ..]; unfold negate_comparison in H; red in H
                          | apply (int_cmp_repr' Ceq) in H;
                            [ | rep_lia ..]; unfold negate_comparison in H; red in H
                          | idtac]
                 | discriminate H
                 | idtac ]
 | H : Int.lt _ _ = false |- _ =>
         revert H; simpl_compare; intro H;
         try (apply (int_cmp_repr' Clt) in H ;
                    [ | rep_lia ..])
 | H : Int.lt _ _ = true |- _ =>
         revert H; simpl_compare;  intro H;
         try (apply (int_cmp_repr Clt) in H ;
                    [ | rep_lia ..])
 | H : Int.eq _ _ = false |- _ =>
         revert H; simpl_compare;  intro H;
         try (apply (int_cmp_repr' Ceq) in H ;
                    [ | rep_lia ..])
 | H : Int.eq _ _ = true |- _ =>
         revert H; simpl_compare;  intro H;
         try (apply (int_cmp_repr Ceq) in H ;
                    [ | rep_lia ..])
 | |- _ => idtac
end.

Lemma prop_and_same_derives {A}{NA: NatDed A}:
  forall P Q, (Q |-- !! P)   ->   Q |-- !!P && Q.
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
Arguments denote_tc_nosignedover op s v1 v2 / .
Ltac simpl_denote_tc :=
 repeat change (denote_tc_isptr ?v) with (!! isptr v);
 repeat change (denote_tc_iszero (Vint ?i)) with (!! is_true (Int.eq i Int.zero));
 repeat change (denote_tc_iszero (Vlong ?i)) with (!! is_true (Int64.eq i Int64.zero));
 repeat change (denote_tc_iszero _) with (@FF mpred _);
 repeat change (denote_tc_nonzero (Vint ?i)) with (!! (i <> Int.zero));
 repeat change (denote_tc_nonzero (Vlong ?i)) with (!! (i <> Int64.zero));
 repeat change (denote_tc_nonzero _) with (@FF mpred _);
 repeat change (denote_tc_igt ?i (Vint ?i1)) with (!! (Int.unsigned i1 < Int.unsigned i));
 repeat change (denote_tc_Zge ?z (Vfloat ?f)) with 
                     match Zoffloat f with Some n => !!(z>=n) | None => @FF mpred _ end;
 repeat change (denote_tc_Zge ?z (Vsingle ?f)) with 
                     match Zofsingle f with Some n => !!(z<=n) | None => @FF mpred _ end;
 repeat change (denote_tc_Zge ?z _) with  (@FF mpred _);
 repeat change (denote_tc_Zle ?z (Vfloat ?f)) with 
                     match Zoffloat f with Some n => !!(z<=n) | None => @FF mpred _ end;
 repeat change (denote_tc_Zle ?z (Vsingle ?f)) with 
                     match Zofsingle f with Some n => !!(z<=n) | None => @FF mpred _ end;
 repeat change (denote_tc_Zle ?z _) with  (@FF mpred _);
 repeat change (denote_tc_samebase ?v1 ?v2) with (!! is_true (sameblock v1 v2));
 repeat change (denote_tc_nodivover (Vint ?n1) (Vint ?n2))
            with (!! (~ (n1 = Int.repr Int.min_signed /\ n2 = Int.mone)));
 repeat change (denote_tc_nodivover (Vint ?n1) (Vlong _))
            with (@TT mpred _);
 repeat change (denote_tc_nodivover (Vlong ?n1) (Vint ?n2))
            with ( !! (~ (n1 = Int64.repr Int64.min_signed /\ n2 = Int.mone)));
 repeat change (denote_tc_nodivover (Vlong ?n1) (Vlong ?n2))
            with (!! (~ (n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone)));
 repeat change (denote_tc_nodivover _ _)
            with (@FF mpred _);
 repeat change (denote_tc_nosignedover ?op (Vint ?n1) (Vint ?n2)) with
          (!! (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed));
 repeat change (denote_tc_nosignedover ?op (Vint ?n1) (Vlong ?n2)) with
          (!! (Int64.min_signed <=
            op (Int.signed n1) (Int64.signed n2) <= Int64.max_signed));
 repeat change (denote_tc_nosignedover ?op (Vlong ?n1) (Vint ?n2)) with
          (!! (Int64.min_signed <=
            op (Int64.signed n1) (Int.signed n2) <=
            Int64.max_signed));
 repeat change (denote_tc_nosignedover ?op (Vlong ?n1) (Vlong ?n2)) with
          (!! (Int64.min_signed <=
            op (Int64.signed n1) (Int64.signed n2) <=
            Int64.max_signed));
 repeat change (denote_tc_nosignedover _ _)  with (@FF mpred _);
 simpl denote_tc_initialized.

Lemma denote_tc_test_eq_split:
  forall P x y,
    (P |-- valid_pointer x) ->
    (P |-- valid_pointer y) ->
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
 destruct (sameblock _ _); auto.
 apply andp_derives; apply valid_pointer_weak.
Qed.

Lemma valid_pointer_null:
  forall P, P |-- valid_pointer nullval.
Proof.
  intros. unfold nullval, valid_pointer, valid_pointer'. 
  destruct Archi.ptr64 eqn:Hp; simpl;
 change predicates_hered.prop with prop;
 normalize.
Qed.


Lemma extend_valid_pointer:
  forall p Q, valid_pointer p * Q |-- valid_pointer p.
Proof.
intros.
 unfold valid_pointer.
 pose proof (extend_tc.extend_valid_pointer' p 0).
 pose proof (predicates_hered.boxy_e _ _ H).
 constructor; change (predicates_hered.derives (valid_pointer' p 0 * Q) (valid_pointer' p 0)).
 intros ? (w1 & w2 & Hj & Hp & ?).
 apply (H0 w1); auto.
 hnf; eauto.
Qed.

Lemma extend_weak_valid_pointer:
  forall p Q, weak_valid_pointer p * Q |-- weak_valid_pointer p.
Proof.
  intros. unfold weak_valid_pointer.
  pose proof (extend_tc.extend_valid_pointer' p 0).
  pose proof (predicates_hered.boxy_e _ _ H). 
  pose proof (extend_tc.extend_valid_pointer' p (-1)).
  pose proof (predicates_hered.boxy_e _ _ H1).
  constructor; change
      (predicates_hered.derives
         (predicates_hered.orp (valid_pointer' p 0) (valid_pointer' p (-1)) * Q)
         (predicates_hered.orp (valid_pointer' p 0) (valid_pointer' p (-1)))).
  intros ? (w1 & w2 & Hj & Hp & ?). simpl in Hp |- * .
  destruct Hp; [left; apply (H0 w1) | right; apply (H2 w1)]; auto; hnf; eauto.
Qed.

Lemma sepcon_valid_pointer1:
     forall (P Q: mpred) p,
        (P |-- valid_pointer p) ->
        P * Q |-- valid_pointer p.
Proof.
intros.
 eapply derives_trans; [apply sepcon_derives; [eassumption | apply TT_right] |].
 clear H.
 apply extend_valid_pointer.
Qed.

 Lemma sepcon_valid_pointer2:
     forall (P Q: mpred) p,
        (P |-- valid_pointer p) ->
        Q * P |-- valid_pointer p.
Proof.
 intros. rewrite sepcon_comm; apply sepcon_valid_pointer1.
 auto.
Qed.

Lemma sepcon_weak_valid_pointer1: 
 forall (P Q : mpred) (p : val),
   (P |-- weak_valid_pointer p) -> P * Q |-- weak_valid_pointer p.
Proof.
  intros.
  eapply derives_trans; [ | apply (extend_weak_valid_pointer p Q)].
  apply sepcon_derives; auto.
Qed.

Lemma sepcon_weak_valid_pointer2:
  forall (P Q : mpred) (p : val),
    (P |-- weak_valid_pointer p) -> Q * P |-- weak_valid_pointer p.
Proof.
  intros. rewrite sepcon_comm.
  apply sepcon_weak_valid_pointer1; auto.
Qed.

 Lemma andp_valid_pointer1:
     forall (P Q: mpred) p,
        (P |-- valid_pointer p) ->
        P && Q |-- valid_pointer p.
Proof.
intros.
 apply andp_left1; auto.
Qed.

 Lemma andp_valid_pointer2:
     forall (P Q: mpred) p,
        (P |-- valid_pointer p) ->
        Q && P |-- valid_pointer p.
Proof.
intros.
 apply andp_left2; auto.
Qed.

Lemma valid_pointer_zero32:
  forall P, Archi.ptr64=false -> P |-- valid_pointer (Vint (Int.repr 0)).
Proof.
 intros.
 unfold valid_pointer, valid_pointer'. rewrite H.
 change predicates_hered.prop with prop;
 normalize.
Qed.

Lemma valid_pointer_zero64:
  forall P, Archi.ptr64=true -> P |-- valid_pointer (Vlong (Int64.repr 0)).
Proof.
 intros.
 unfold valid_pointer, valid_pointer'. rewrite H.
 change predicates_hered.prop with prop;
 normalize.
Qed.


#[export] Hint Resolve sepcon_valid_pointer1 sepcon_valid_pointer2 : valid_pointer.
#[export] Hint Resolve andp_valid_pointer1 andp_valid_pointer2 : valid_pointer.
#[export] Hint Resolve valid_pointer_null : valid_pointer.
#[export] Hint Resolve valid_pointer_zero32 : valid_pointer.
#[export] Hint Resolve valid_pointer_zero64 : valid_pointer.
#[export] Hint Resolve sepcon_weak_valid_pointer1: valid_pointer. 
#[export] Hint Resolve sepcon_weak_valid_pointer2: valid_pointer. 


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

#[export] Hint Rewrite (@TT_andp mpred _) : gather_prop.
#[export] Hint Rewrite (@andp_TT mpred _) : gather_prop.

Ltac pull_out_props :=
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
    gather_prop;
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true).

Ltac simplify_float2int :=
match goal with
| |- context [Zofsingle (Float32.of_bits (Int.repr ?A))] =>
   putable A; 
   let x := fresh "x" in (evar (x: Z));
   replace (Zofsingle (Float32.of_bits (Int.repr A))) with (Some x) by (subst x; reflexivity);
   compute in x; subst x
| |- context [Zoffloat (Float.of_bits (Int.repr ?A))] =>
   putable A; 
   let x := fresh "x" in (evar (x: Z));
   replace (Zoffloat (Float.of_bits (Int.repr A))) with (Some x) by (subst x; reflexivity);
   compute in x; subst x
end.

Ltac ent_iter :=
    try simple apply prop_True_right;
    repeat simplify_float2int;
    gather_prop;
    repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
   repeat erewrite unfold_reptype_elim in * by (apply JMeq_refl; reflexivity);
   simpl_compare;
   simpl_denote_tc;
   safe_subst_any;
   try autorewrite with entailer_rewrite in *;
   try solve_valid_pointer;
   repeat data_at_conflict_neq.

Lemma and_False: forall x, (x /\ False) = False.
Proof.
intros; apply prop_ext; tauto.
Qed.

Lemma and_True: forall x, (x /\ True) = x.
Proof.
intros; apply prop_ext; tauto.
Qed.

Lemma True_and: forall x, (True /\ x) = x.
Proof.
intros; apply prop_ext; tauto.
Qed.

Lemma False_and: forall x, (False /\ x) = False.
Proof.
intros; apply prop_ext; tauto.
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

Ltac prove_signed_range :=
  match goal with
  | |- Int.min_signed <= _ <= Int.max_signed => 
           normalize; rep_lia
  | |- Int64.min_signed <= _ <= Int64.max_signed => 
           normalize; rep_lia
  end.

Lemma ptr_eq_refl: forall x, isptr x -> ptr_eq x x.
Proof.
destruct x; simpl; intros; try contradiction.
split; auto. apply Ptrofs.eq_true.
Qed.
#[export] Hint Resolve ptr_eq_refl : prove_it_now.

Lemma ptr_eq_nullval: ptr_eq nullval nullval.
Proof.
Transparent Archi.ptr64.
unfold ptr_eq, nullval; simpl.
split3; auto.
Opaque Archi.ptr64.
Qed.

#[export] Hint Resolve ptr_eq_nullval : prove_it_now.

#[export] Hint Extern 4 (value_fits _ _ _) =>
   (rewrite ?proj_sumbool_is_true by auto;
    rewrite ?proj_sumbool_is_false by auto;
    repeat simplify_value_fits; auto) : prove_it_now.

Lemma intsigned_intrepr_bytesigned: forall i,
   Int.signed (Int.repr (Byte.signed i)) = Byte.signed i.
Proof.
 intros. rewrite Int.signed_repr; auto.
  destruct (Byte.signed_range i).
  split.
  eapply Z.le_trans; [ | eassumption]. compute; intros Hx; inv Hx.
  eapply Z.le_trans; [eassumption | ]. compute; intros Hx; inv Hx.
Qed.

#[export] Hint Rewrite intsigned_intrepr_bytesigned : rep_lia.

Ltac prove_it_now :=
 first [ splittable; fail 1
        | computable
        | apply Logic.I
        | reflexivity
        | rewrite ?intsigned_intrepr_bytesigned; rep_lia
        | prove_signed_range
        | congruence
        | repeat match goal with
                      | H: ?A |- _ => has_evar A; clear H 
                      | H: @value_fits _ _ _ |- _ => clear H  (* delete these because they can cause slowness in the 'auto' *)
                      end;
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

Definition conjuncts_marker (P: Prop) : Prop := P.
(* The purpose of this conjuncts marker is to try to address VST issue #745 *) 

Lemma try_conjuncts_lem2: forall A B : Prop,
   B -> A -> (A /\ B).
Proof. tauto. Qed.

Lemma try_conjuncts_lem: forall A B A' B' : Prop,
   (conjuncts_marker A -> A') -> (conjuncts_marker B -> B') -> ((A /\ B) -> A' /\ B').
Proof. unfold conjuncts_marker; tauto. Qed.

Lemma try_conjuncts_start: forall A B: Prop,
   (A -> B) -> (A -> B).
 Proof. tauto. Qed.

Ltac try_conjuncts_solver :=
    lazymatch goal with H:_ |- ?A =>
         no_evars A;
         clear H; try immediate; auto; prove_it_now; fail
    end.

Ltac try_conjuncts :=
 first [ simple apply conj;
                [try_conjuncts_solver | try_conjuncts ]
        | simple eapply try_conjuncts_lem2;
                [try_conjuncts_solver 
                | match goal with H: conjuncts_marker _ |- _ => red in H; apply H end ]
        | simple eapply try_conjuncts_lem;
            [intro; try_conjuncts | intro; try_conjuncts
            |match goal with H: conjuncts_marker _ |- _ => red in H; apply H end ]
        | match goal with H: conjuncts_marker _ |- _ => instantiate (1:=True) in H;
                try_conjuncts_solver
          end
        | match goal with H: conjuncts_marker _ |- _ => red in H; apply H end
        ].

Lemma try_conjuncts_prop_and:
  forall {A}{NA: NatDed A} (S: A) (P P': Prop) Q,
      (conjuncts_marker P' -> P) ->
      (S |-- !! P' && Q) ->
      S |-- !! P && Q.
Proof. intros.
 eapply derives_trans; [apply H0 |].
 apply andp_derives; auto.
 apply prop_derives; auto.
Qed.


Lemma try_conjuncts_prop:
  forall {A}{NA: NatDed A} (S: A) (P P': Prop),
      (conjuncts_marker P' -> P) ->
      (S |-- !! P') ->
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
 try rewrite (prop_true_andp True) by apply Logic.I;
 try solve_valid_pointer;
 try first [apply derives_refl
              | simple apply FF_left
              | simple apply TT_right].

Lemma empTrue:
 @derives mpred Nveric (@emp mpred Nveric Sveric) (@prop mpred Nveric True).
Proof.
apply prop_right; auto.
Qed.

Ltac clean_up_stackframe := idtac.

Lemma my_auto_lem:
 forall (P Q: Prop), (conjuncts_marker P -> Q) -> (P -> Q).
Proof. auto. Qed.

Ltac my_auto_iter H :=
 first [instantiate (1:=True) in H;  prove_it_now
       | splittable;
         eapply try_conjuncts_lem;
            [let H1 := fresh in intro H1; my_auto_iter H1
            |let H1 := fresh in intro H1; my_auto_iter H1
            | apply H ]
       | red in H (* remove conjuncts_marker*); apply H
       ].

Ltac all_True :=  solve [repeat simple apply conj; simple apply Logic.I].

Ltac my_auto_reiter :=
 first [simple apply conj; [all_True | ]; my_auto_reiter
        |simple apply conj; [ | all_True]; my_auto_reiter
        |splittable; eapply try_conjuncts_lem;
                [intro; my_auto_reiter
                |intro; my_auto_reiter
                |eassumption]
        |lazymatch goal with H: conjuncts_marker _ |- _ => red in H; apply H end].

Ltac my_auto :=
 repeat match goal with |- ?P -> _ => match type of P with Prop => intro end end;
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

Definition prop_and_same_derives_mpred := 
  @prop_and_same_derives mpred _.

Ltac entailer :=
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 lazymatch goal with
 | |- ?P |-- _ =>
    lazymatch type of P with
    | ?T => tryif unify T (environ->mpred)
                 then (clean_up_stackframe; go_lower)
                 else tryif unify T mpred
                    then (clear_Delta; pull_out_props)
                    else fail "Unexpected type of entailment, neither mpred nor environ->mpred"
    end
 | |- _ => fail  "The entailer tactic works only on entailments   _ |-- _ "
 end;
 try solve [simple apply prop_right; my_auto];
 try solve [simple apply prop_and_same_derives_mpred; my_auto];
 saturate_local;
 entailer';
 rewrite <- ?sepcon_assoc.


Ltac entbang :=
 intros;
 try lazymatch goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try lazymatch goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 lazymatch goal with
 | |- local _ && ?P |-- _ => clean_up_stackframe; go_lower;
          rewrite ?TT_andp, ?andp_TT; try apply TT_right
 | |- ?P |-- _ =>
    lazymatch type of P with
    | ?T => tryif unify T (environ->mpred)
                 then fail "entailer! found an (environ->mpred) entailment that is missing its 'local' left-hand-side part (that is, Delta)"
                 else tryif unify T mpred
                    then (clear_Delta; pull_out_props)
                    else fail "Unexpected type of entailment, neither mpred nor environ->mpred"
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ |-- _ "
 end;
 repeat lazymatch goal with
        | |- context [force_val (sem_binary_operation' ?op ?t1 ?t2 ?v1 ?v2)] =>
          progress 
              simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
                (force_val (sem_binary_operation' op t1 t2 v1 v2))
        end;
 simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
        sem_cast;
 lazymatch goal with 
   | H: bangbang |- _ => idtac
   | |- _ => saturate_local
 end;
 ent_iter;
 repeat change (mapsto_memory_block.spacer _ _ _ _) with emp;
 first [ contradiction
        | simple apply prop_right; my_auto
        | lazymatch goal with |- ?Q |-- !! _ && ?Q' => constr_eq  Q Q';
                      simple apply prop_and_same_derives'; my_auto
          end
        | simple apply andp_right;
            [apply prop_right; my_auto 
            | cancel; rewrite <- ?sepcon_assoc; autorewrite with norm ]
        | normalize; cancel; rewrite <- ?sepcon_assoc
        ].

Tactic Notation "entailer" "!" := entbang.

Ltac entbangbang :=
 let B := fresh "BangBang" in assert (BangBang :=bangbang_i);
 entbang;
 clear B.

Tactic Notation "entailer" "!!" := entbangbang.

Ltac elim_hyps :=  (* not in use anywhere? *)
 repeat lazymatch goal with
 | H: isptr ?x |- _ =>
     let x1 := fresh x "_b" in let x2 := fresh x "_ofs" in
     destruct x as [ | | | | | x1 x2]; inv H
 | H: ptr_eq _ _ |- _ => apply ptr_eq_e in H; safe_subst_any
 end.

(**** try this out here, for now ****)

#[export] Hint Rewrite Int.signed_repr using rep_lia : norm.
#[export] Hint Rewrite Int.unsigned_repr using rep_lia : norm.
#[export] Hint Rewrite Int64.signed_repr using rep_lia : norm.
#[export] Hint Rewrite Int64.unsigned_repr using rep_lia : norm.

(************** TACTICS FOR GENERATING AND EXECUTING TEST CASES *******)

Definition EVAR (x: Prop) := x.
Lemma EVAR_e: forall x, EVAR x -> x.
Proof. intros. apply H. Qed.

Ltac gather_entail :=
repeat match goal with
 | A := _ |- _ =>  clear A || (revert A; match goal with |- ?B => no_evars B end)
 | H : ?P |- _ =>
  match type of P with
  | Prop => revert H; match goal with |- ?B => no_evars B end
  | _ => clear H || (revert H; match goal with |- ?B => no_evars B end)
  end
end;
repeat match goal with
 | x := ?X |- _ => is_evar X; clearbody x; revert x; apply EVAR_e
end.

Lemma EVAR_i: forall P: Prop, P -> EVAR P.
Proof. intros. apply H. Qed.

Ltac ungather_entail :=
match goal with
  | |- EVAR (forall x : ?t, _) =>
       let x' := fresh x in evar (x' : t);
       let x'' := fresh x in apply EVAR_i; intro x'';
       replace x'' with x'; [ungather_entail; clear x'' | admit ]
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
rewrite Ptrofs.add_zero.
apply prop_ext; tauto.
Qed.
#[export] Hint Rewrite offset_val_sizeof_hack : norm.

Lemma offset_val_sizeof_hack2:
 forall cenv t i j p,
   isptr p ->
   i=j ->
   (offset_val (@sizeof cenv t * i) p = offset_val (@sizeof cenv t * j) p) = True.
Proof.
intros.
subst.
apply prop_ext; tauto.
Qed.
#[export] Hint Rewrite offset_val_sizeof_hack2 : norm.

Lemma offset_val_sizeof_hack3:
 forall cenv t i p,
   isptr p ->
   i=1 ->
   (offset_val (@sizeof cenv t * i) p = offset_val (@sizeof cenv t) p) = True.
Proof.
intros.
subst.
rewrite Z.mul_1_r.
apply prop_ext; tauto.
Qed.
#[export] Hint Rewrite offset_val_sizeof_hack3 : norm.

Ltac make_Vptr c :=
  let H := fresh in assert (isptr c) by auto;
  destruct c; try (contradiction H); clear H.

Lemma Zmax0r: forall n, 0 <= n -> Z.max 0 n = n.
Proof.
intros. apply Z.max_r; auto.
Qed.
#[export] Hint Rewrite Zmax0r using (try computable; rep_lia) : norm.

Import ListNotations.

Ltac progress_entailer :=
 lazymatch goal with
 | |- @derives mpred _ ?A ?B => 
     entailer!; try match goal with |- @derives mpred _ A B => fail 2 end
 | |- _ => progress entailer!
 end.

Lemma ptrofs_of_int64_int64_repr:
  Archi.ptr64=true ->
  forall i, Ptrofs.of_int64 (Int64.repr i) = Ptrofs.repr i.
Proof.
intros.
unfold Ptrofs.of_int64.
apply efield_lemmas.Ptrofs_repr_Int64_unsigned_special; auto.
Qed.

(* new experiment *)
(* #[export] Hint Rewrite ptrofs_of_int64_int64_repr using reflexivity : norm rep_lia. *)
#[export] Hint Rewrite Ptrofs.signed_repr using rep_lia : norm.
#[export] Hint Rewrite Ptrofs.unsigned_repr using rep_lia : norm. 
(* end new experiment *)
