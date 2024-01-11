Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at VST.floyd.nested_field_lemmas.

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

Lemma prop_and_same_derives :
  forall {prop:bi} (P:Prop) (Q:prop), (Q ⊢ ⌜P⌝)   ->   Q ⊢ (⌜P⌝ ∧ Q).
Proof.
intros. apply bi.and_intro; auto.
Qed.

Arguments denote_tc_isptr {_} {_} v / .
Arguments denote_tc_iszero {_} {_} !v .
Arguments denote_tc_nonzero {_} {_} !v .
Arguments denote_tc_igt {_} {_} i !v .
Arguments denote_tc_Zge {_} {_} z !v .
Arguments denote_tc_Zle {_} {_} z !v .
Arguments denote_tc_samebase {_} {_} !v1 !v2 .
Arguments denote_tc_nodivover {_} {_} !v1 !v2 .
Arguments denote_tc_initialized {_} {_} id ty rho / .
Arguments denote_tc_nosignedover {_} {_} op s v1 v2 / .


Local Notation "'False'" := (@bi_pure mpred (False%type)).

Ltac simpl_denote_tc :=
 repeat change (denote_tc_isptr ?v) with (@bi_pure mpred isptr v);
 repeat change (denote_tc_iszero (Vint ?i)) with (@bi_pure mpred is_true (Int.eq i Int.zero));
 repeat change (denote_tc_iszero (Vlong ?i)) with (@bi_pure mpred is_true (Int64.eq i Int64.zero));
 repeat change (denote_tc_iszero _) with (False);
 repeat change (denote_tc_nonzero (Vint ?i)) with (@bi_pure mpred (i <> Int.zero));
 repeat change (denote_tc_nonzero (Vlong ?i)) with (@bi_pure mpred (i <> Int64.zero));
 repeat change (denote_tc_nonzero _) with (False);
 repeat change (denote_tc_igt ?i (Vint ?i1)) with (@bi_pure mpred (Int.unsigned i1 < Int.unsigned i));
 repeat change (denote_tc_Zge ?z (Vfloat ?f)) with 
                     match Zoffloat f with Some n => @bi_pure mpred(z>=n) | None => False end;
 repeat change (denote_tc_Zge ?z (Vsingle ?f)) with 
                     match Zofsingle f with Some n => @bi_pure mpred(z<=n) | None => False end;
 repeat change (denote_tc_Zge ?z _) with  (False);
 repeat change (denote_tc_Zle ?z (Vfloat ?f)) with 
                     match Zoffloat f with Some n => @bi_pure mpred(z<=n) | None => False end;
 repeat change (denote_tc_Zle ?z (Vsingle ?f)) with 
                     match Zofsingle f with Some n => @bi_pure mpred(z<=n) | None => False end;
 repeat change (denote_tc_Zle ?z _) with  (False);
 repeat change (denote_tc_samebase ?v1 ?v2) with (@bi_pure mpred is_true (sameblock v1 v2));
 repeat change (denote_tc_nodivover (Vint ?n1) (Vint ?n2))
            with (@bi_pure mpred (~ (n1 = Int.repr Int.min_signed /\ n2 = Int.mone)));
 repeat change (denote_tc_nodivover (Vint ?n1) (Vlong _))
            with (@bi_pure mpred True);
 repeat change (denote_tc_nodivover (Vlong ?n1) (Vint ?n2))
            with ( @bi_pure mpred (~ (n1 = Int64.repr Int64.min_signed /\ n2 = Int.mone)));
 repeat change (denote_tc_nodivover (Vlong ?n1) (Vlong ?n2))
            with (@bi_pure mpred (~ (n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone)));
 repeat change (denote_tc_nodivover _ _)
            with (False);
 repeat change (denote_tc_nosignedover ?op (Vint ?n1) (Vint ?n2)) with
          (@bi_pure mpred (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed));
 repeat change (denote_tc_nosignedover ?op (Vint ?n1) (Vlong ?n2)) with
          (@bi_pure mpred (Int64.min_signed <=
            op (Int.signed n1) (Int64.signed n2) <= Int64.max_signed));
 repeat change (denote_tc_nosignedover ?op (Vlong ?n1) (Vint ?n2)) with
          (@bi_pure mpred (Int64.min_signed <=
            op (Int64.signed n1) (Int.signed n2) <=
            Int64.max_signed));
 repeat change (denote_tc_nosignedover ?op (Vlong ?n1) (Vlong ?n2)) with
          (@bi_pure mpred (Int64.min_signed <=
            op (Int64.signed n1) (Int64.signed n2) <=
            Int64.max_signed));
 repeat change (denote_tc_nosignedover _ _) with (False);
 simpl denote_tc_initialized.

Example simpl_denote_tc_test `{!heapGS Σ} : @bi_entails mpred False (denote_tc_iszero (Vint (Int.repr 1))).
intros. by simpl_denote_tc; apply derives_refl. Qed.

Section ENTAILER.

Context `{!heapGS Σ}.

Lemma denote_tc_test_eq_split:
  forall P x y,
    (P ⊢ valid_pointer x) ->
    (P ⊢ valid_pointer y) ->
    P ⊢ denote_tc_test_eq x y.
Proof.
 intros.
 trans (valid_pointer x ∧ valid_pointer y).
 apply bi.and_intro; auto.
 clear H H0.
 unfold denote_tc_test_eq, weak_valid_pointer.
 destruct x; try (iIntros "([] & _)"); try apply @bi.True_intro;
 destruct y; try (iIntros "(_ & [])"); try apply @bi.True_intro.
 apply bi.and_mono; try apply derives_refl.
 apply bi.and_mono; try apply derives_refl.
 apply bi.or_intro_l.
 rewrite bi.and_comm.
 apply bi.and_mono; try apply derives_refl. apply bi.or_intro_l.
 unfold test_eq_ptrs.
 destruct (sameblock _ _); auto.
 apply bi.and_mono; apply valid_pointer_weak.
Qed.

Lemma valid_pointer_null:
  forall P, P ⊢ valid_pointer nullval.
Proof.
  intros. unfold nullval, valid_pointer, valid_pointer'. 
  destruct Archi.ptr64 eqn:Hp; simpl;
 normalize.
Qed.


Lemma extend_valid_pointer:
  forall p Q, valid_pointer p ∗ Q ⊢ valid_pointer p.
Proof.
  intros. iIntros "[$ _]".
Qed.

Lemma extend_weak_valid_pointer:
  forall p Q, weak_valid_pointer p ∗ Q ⊢ weak_valid_pointer p.
Proof.
  intros. iIntros "[$ _]".
Qed.

Lemma sepcon_valid_pointer1:
     forall (P Q: mpred) p,
        (P ⊢ valid_pointer p) ->
        P ∗ Q ⊢ valid_pointer p.
Proof.
  intros. rewrite H; iIntros "[$ _]".
Qed.

 Lemma sepcon_valid_pointer2:
     forall (P Q: mpred) p,
        (P ⊢ valid_pointer p) ->
        Q ∗ P ⊢ valid_pointer p.
Proof.
 intros. rewrite H; iIntros "[_ $]".
Qed.

Lemma sepcon_weak_valid_pointer1: 
 forall (P Q : mpred) (p : val),
   (P ⊢ weak_valid_pointer p) -> P ∗ Q ⊢ weak_valid_pointer p.
Proof.
  intros. rewrite H; iIntros "[$ _]".
Qed.

Lemma sepcon_weak_valid_pointer2:
  forall (P Q : mpred) (p : val),
    (P ⊢ weak_valid_pointer p) -> Q ∗ P ⊢ weak_valid_pointer p.
Proof.
  intros. rewrite H; iIntros "[_ $]".
Qed.

 Lemma andp_valid_pointer1:
     forall (P Q: mpred) p,
        (P ⊢ valid_pointer p) ->
        P ∧ Q ⊢ valid_pointer p.
Proof.
  intros. rewrite H; iIntros "[$ _]".
Qed.

 Lemma andp_valid_pointer2:
     forall (P Q: mpred) p,
        (P ⊢ valid_pointer p) ->
        Q ∧ P ⊢ valid_pointer p.
Proof.
intros. rewrite H; iIntros "[_ $]".
Qed.

Lemma valid_pointer_zero32:
  forall P, Archi.ptr64=false -> P ⊢ valid_pointer (Vint (Int.repr 0)).
Proof.
 intros.
 unfold valid_pointer, valid_pointer'. rewrite H.
 normalize.
Qed.

Lemma valid_pointer_zero64:
  forall P, Archi.ptr64=true -> P ⊢ valid_pointer (Vlong (Int64.repr 0)).
Proof.
 intros.
 unfold valid_pointer, valid_pointer'. rewrite H.
 normalize.
Qed.
End ENTAILER.

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
| |- _ ⊢ denote_tc_test_eq _ _ ∧ _ =>
           apply bi.and_intro;
               [apply denote_tc_test_eq_split;
                solve [auto 50 with valid_pointer] | ]
| |- _ ⊢ valid_pointer _ ∧ _ =>
           apply bi.and_intro; [ solve [auto 50 with valid_pointer] | ]
| |- _ ⊢ weak_valid_pointer _ ∧ _ =>
           apply bi.and_intro; [ solve [auto 50 with valid_pointer] | ]
| |- _ ⊢ denote_tc_test_eq _ _ =>
              auto 50 with valid_pointer
| |- _ ⊢ valid_pointer _ =>
              auto 50 with valid_pointer
| |- _ ⊢ weak_valid_pointer _ =>
              auto 50 with valid_pointer
end.

#[export] Hint Rewrite @bi.True_and : gather_prop.
#[export] Hint Rewrite @bi.and_True : gather_prop.

Ltac pure_elim :=
  match goal with
  | |- ⌜_⌝ ∧ _ ⊢ _ => apply bi.pure_elim_l
  | |- _ ∧ ⌜_⌝ ⊢ _ => apply bi.pure_elim_r
  end.

Ltac pull_out_props :=
    repeat (pure_elim; fancy_intros true);
    gather_prop;
    repeat (pure_elim; fancy_intros true).

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
    try apply bi.True_intro;
    repeat simplify_float2int;
    gather_prop;
    repeat (pure_elim; fancy_intros true);
   repeat erewrite unfold_reptype_elim in * by (apply JMeq_refl; reflexivity);
   simpl_compare;
   simpl_denote_tc;
   safe_subst_any;
   try autorewrite with entailer_rewrite in *;
   try solve_valid_pointer;
   repeat data_at_conflict_neq.

Section ENTAILER.
Context `{!heapGS Σ}.
Implicit Type x:mpred.

Lemma and_False: forall x, (x ∧ False) ⊣⊢ False.
Proof.
  intros. rewrite bi.and_False. done.
Qed.

Lemma and_True: forall x, (x ∧ True) ⊣⊢ x.
Proof.
  intros. rewrite bi.and_True. done.
Qed.

Lemma True_and: forall x, (True ∧ x) ⊣⊢ x.
Proof.
  intros. rewrite bi.True_and //. 
Qed.

Lemma False_and: forall x, (False ∧ x) ⊣⊢ False.
Proof.
  intros. rewrite bi.False_and. done.
Qed.
End ENTAILER.

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
   (rewrite ->?proj_sumbool_is_true by auto;
    rewrite ->?proj_sumbool_is_false by auto;
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
        | apply Coq.Init.Logic.I
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
 first [match goal with H := _ |- _ => instantiate (1:=True%type) in H; prove_it_now end
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
Proof. tauto. Qed.

Lemma try_conjuncts_lem: forall A B A' B' : Prop,
   (A -> A') -> (B -> B') -> (A /\ B -> A' /\ B').
Proof. tauto. Qed.

Lemma try_conjuncts_start: forall A B: Prop,
   (A -> B) -> (A -> B).
 Proof. tauto. Qed.

Ltac try_conjuncts_solver :=
    lazymatch goal with H:_ |- ?A =>
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
        | match goal with H:_ |- _ => instantiate (1:=True%type) in H;
                try_conjuncts_solver
          end
        | match goal with H:_ |- _ => apply H end
        ].

Lemma try_conjuncts_prop_and:
  forall {A:bi} (S: A) (P P': Prop) Q,
      (P' -> P) ->
      (S ⊢ ⌜P'⌝ ∧ Q) ->
      S ⊢ ⌜P⌝ ∧ Q.
Proof. intros.
 rewrite H0.
 apply bi.and_mono; auto.
Qed.


Lemma try_conjuncts_prop:
  forall {A:bi} (S: A) (P P': Prop),
      (P' -> P) ->
      (S ⊢ ⌜P'⌝) ->
      S ⊢ ⌜P⌝ .
Proof. intros.
 rewrite H0.
 apply bi.pure_mono; done.
Qed.

Ltac prop_right_cautious :=
 try solve [apply bi.pure_intro; auto; prove_it_now].

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
 try rewrite ->(prop_true_andp True) by apply Coq.Init.Logic.I;
 try solve_valid_pointer;
 try first [apply derives_refl
              | simple apply bi.False_elim
              | simple apply bi.True_intro].

Lemma empTrue `{!heapGS Σ}: @bi_emp_valid mpred True.
Proof.
apply bi.pure_intro; auto.
Qed.

Ltac clean_up_stackframe := idtac.

Lemma my_auto_lem:
 forall (P Q: Prop), (P -> Q) -> (P -> Q).
Proof. auto. Qed.

Ltac my_auto_iter H :=
 first [instantiate (1:=True%type) in H;  prove_it_now
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
 repeat match goal with |- ?P -> _ => match type of P with Prop => intro end end;
 rewrite ->?isptr_force_ptr by auto;
 let H := fresh in eapply my_auto_lem; [intro H; my_auto_iter H | ];
 try all_True;
 (eapply my_auto_lem; [intro; my_auto_reiter | ]);
 normalize.

Lemma prop_and_same_derives' {prop:bi}:
  forall (P: Prop) (Q:prop), P -> Q ⊢ ⌜P⌝ ∧ Q.
Proof.
  intros. iIntros; iFrame. iPureIntro; done.
Qed.

Definition prop_and_same_derives_mpred `{heapGS0:!heapGS Σ} := 
  @prop_and_same_derives (@mpred Σ heapGS0).

Ltac entailer :=
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 lazymatch goal with
 | |- @bi_entails (monPredI environ_index (iPropI _)) _ _ => clean_up_stackframe; go_lower
 | |- ?P ⊢ _ =>
    lazymatch type of P with
    | ?T => tryif unify T mpred
            then (clear_Delta; pull_out_props)
            else fail "Unexpected type of entailment, neither mpred nor assert"
    end
 | |- _ => fail  "The entailer tactic works only on entailments   _ ⊢ _ "
 end;
 try solve [apply bi.pure_intro; my_auto];
 try solve [apply prop_and_same_derives_mpred; my_auto];
 saturate_local;
 entailer';
 (* TODO iris bi_sep is right assoc, so making the goal look like ((_∗_)∗_) introduces lots of parens. Do we want to change that? *)
 rewrite ?bi.sep_assoc.


Ltac entbang :=
 intros;
 try lazymatch goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try lazymatch goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 lazymatch goal with
 | |- local _ ∧ ?P ⊢ _ => clean_up_stackframe; go_lower;
          rewrite ->?bi.True_and, ?bi.and_True; try apply bi.True_intro
 | |- @bi_entails (monPredI environ_index (iPropI _)) _ _ =>
        fail "entailer! found an assert entailment that is missing its 'local' left-hand-side part (that is, Delta)"
 | |- ?P ⊢ _ =>
    lazymatch type of P with
    | ?T => tryif unify T mpred
            then (clear_Delta; pull_out_props)
            else fail "Unexpected type of entailment, neither mpred nor assert"
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ ⊢ _ "
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
        | simple apply bi.pure_intro; my_auto
        | lazymatch goal with |- ?Q ⊢ ⌜_⌝ ∧ ?Q' => constr_eq Q Q';
                      simple apply prop_and_same_derives'; my_auto
          end
        | simple apply bi.and_intro;
            [apply bi.pure_intro; my_auto 
            | cancel; rewrite ->?bi.sep_assoc; autorewrite with norm ]
        | normalize; cancel; rewrite ->?bi.sep_assoc
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
   (offset_val (@sizeof cenv t * i) p = p) = (True%type).
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
   (offset_val (@sizeof cenv t * i) p = offset_val (@sizeof cenv t * j) p) = (True%type).
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
   (offset_val (@sizeof cenv t * i) p = offset_val (@sizeof cenv t) p) = (True%type).
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

Definition cstring `{!heapGS Σ} {CS : compspecs} sh (s: list byte) p : mpred := 
  ⌜(~In Byte.zero s)⌝ ∧
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p.

Lemma cstring_local_facts: forall `{!heapGS Σ} {CS : compspecs} sh s p, 
  cstring sh s p ⊢ ⌜isptr p ∧ Zlength s + 1 < Ptrofs.modulus⌝.
Proof.
  intros; unfold cstring; entailer!.
  destruct H0 as [? [_ [? _]]].
  destruct p; try contradiction.
  red in H3.
  unfold sizeof, Ctypes.sizeof in H3; clear H1.
  rewrite ->Z.max_r in H3 by list_solve.
  fold Ctypes.sizeof in H3.
  change (Ctypes.sizeof tschar) with 1 in H3.
  pose proof (Ptrofs.unsigned_range i).
  lia. 
Qed.

#[export] Hint Resolve cstring_local_facts : saturate_local.

Lemma cstring_valid_pointer: forall `{!heapGS Σ} {CS : compspecs} sh s p, 
   sh <> Share.bot ->
   cstring sh s p ⊢ valid_pointer p.
Proof.
  intros; unfold cstring; Intros.
  apply data_at_valid_ptr; auto.
  unfold tarray, tschar, sizeof, Ctypes.sizeof.
  pose proof (Zlength_nonneg s).
  rewrite Z.max_r; lia.
Qed.

#[export] Hint Resolve cstring_valid_pointer : valid_pointer.

Definition cstringn `{!heapGS Σ} {CS : compspecs} sh (s: list byte) n p : mpred :=
  ⌜(~In Byte.zero s) ⌝ ∧
  data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero]) ++
    Zrepeat Vundef (n - (Zlength s + 1))) p.

Fixpoint no_zero_bytes (s: list byte) : bool :=
 match s with
 | nil => true
 | b :: s' => andb (negb (Byte.eq b Byte.zero)) (no_zero_bytes s')
 end.

Lemma data_at_to_cstring:
 forall `{!heapGS Σ} {CS: compspecs} sh n s p,
  no_zero_bytes s = true ->
 data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero])) p ⊢
 cstring sh s p.
Proof.
intros.
saturate_local. clear H0 H2.
rewrite ->Zlength_map, Zlength_app, Zlength_cons, Zlength_nil in H1.
simpl in H1.
destruct (Z.max_spec 0 n) as [[? ?]|[? ?]].
2:{ rewrite H2 in H1. pose proof (Zlength_nonneg s). lia. }
rewrite ->H2 in *.
clear H0 H2.
subst n.
unfold cstring.
apply bi.and_intro; auto.
apply bi.pure_intro.
intro.
induction s; simpl in *; auto.
rewrite andb_true_iff in H.
destruct H.
destruct H0; subst.
rewrite Byte.eq_true in H. inv H.
auto.
Qed.

Lemma cstringn_equiv : forall `{!heapGS Σ} {CS : compspecs} sh s p, cstring sh s p = cstringn sh s (Zlength s + 1) p.
Proof.
  intros; unfold cstring, cstringn.
  rewrite Zminus_diag app_nil_r; auto.
Qed.

Lemma cstringn_local_facts: forall `{!heapGS Σ} {CS : compspecs} sh s n p, 
   cstringn sh s n p ⊢ ⌜isptr p /\ Zlength s + 1 <= n <= Ptrofs.max_unsigned⌝.
Proof.
  intros; unfold cstringn; entailer!.
  rewrite ->!Zlength_app, !Zlength_map, Zlength_app in H1.
  assert (H8 := Zlength_nonneg s).
  destruct (zlt n (Zlength s + 1)).
  autorewrite with sublist in H1. lia.
  split. lia.
  autorewrite with sublist in *.
  destruct H0 as [? [_ [? _]]].
  destruct p; try contradiction.
  red in H3. 
  unfold sizeof, Ctypes.sizeof in H3;  fold Ctypes.sizeof in H3.
  rewrite ->Z.max_r in H3 by lia. change (Ctypes.sizeof tschar) with 1 in H3.
  pose proof (Ptrofs.unsigned_range i).
  rep_lia.
Qed.

#[export] Hint Resolve cstringn_local_facts : saturate_local.

Lemma cstringn_valid_pointer: forall `{!heapGS Σ} {CS : compspecs} sh s n p, 
     sh <> Share.bot ->
     cstringn sh s n p ⊢ valid_pointer p.
Proof.
  intros.
  entailer!. 
  unfold cstringn; Intros.
  apply data_at_valid_ptr; auto.
  unfold tarray, tschar, sizeof, Ctypes.sizeof; cbv beta iota zeta.
  pose proof (Zlength_nonneg s).
  rewrite Z.max_r; lia.
Qed.

#[export] Hint Resolve cstringn_valid_pointer : valid_pointer.


Lemma Znth_zero_zero:
  forall i, Znth i [Byte.zero] = Byte.zero.
Proof.
intros.
unfold Znth.
if_tac; auto. destruct (Z.to_nat i). reflexivity. destruct n; reflexivity.
Qed.


(* THIS TACTIC solves goals of the form,
    ~In 0 ls,  Znth i (ls++[0]) = 0 |-  (any lia consequence of)  i < Zlength ls
    ~In 0 ls,  Znth i (ls++[0]) <> 0 |-  (any lia consequence of)  i >= Zlength ls
*)
Ltac cstring :=
  lazymatch goal with
  | H: ~In Byte.zero _ |- _ => idtac
  | |- _ => fail "The cstring tactic expects to see a hypothesis above the line of the form, ~ In Byte.zero _"
  end;
 lazymatch goal with
 | H1: Znth _ (_++[Byte.zero]) = Byte.zero |- _ => idtac 
 | H1: Znth _ (_++[Byte.zero]) <> Byte.zero |- _ => idtac 
 | |- _ => fail "The cstring tactic expects to see one of the following hypotheses above the line:
Znth _ (_++[Byte.zero]) = Byte.zero
Znth _ (_++[Byte.zero]) <> Byte.zero"
 end;
 (pose_Zlength_nonneg;
  apply Classical_Prop.NNPP; intro;
  match goal with
  | H: ~In Byte.zero ?ls, H1: Znth ?i (?ls' ++ [Byte.zero]) = Byte.zero |- _ =>
     constr_eq ls ls'; apply H; rewrite <- H1;  
    rewrite ->app_Znth1 by lia; apply Znth_In; lia
  | H: ~In Byte.zero ?ls, H1: Znth ?i (?ls' ++ [Byte.zero]) <> Byte.zero |- _ =>
     constr_eq ls ls'; apply H1;
     rewrite ->app_Znth2 by lia; apply Znth_zero_zero
  end) || 
  match goal with |- @eq ?t (?f1 _) (?f2 _) =>
       (unify t Z || unify t nat) ||
       (constr_eq f1 f2;
        fail "The cstring tactic solves lia-style goals.
Your goal is an equality at type" t ", not type Z.
Try the [f_equal] tactic first.")
 end.

Ltac progress_entailer :=
 lazymatch goal with
 | |- @bi_entails mpred ?A ?B => 
     entailer!; try match goal with |- @bi_entails mpred A B => fail 2 end
 | |- _ => progress entailer!
 end.

Ltac cstring' := 
lazymatch goal with
| |- @eq Z _ _ => cstring
| |- ?A _ = ?B _ => constr_eq A B; f_equal; cstring'
| |- _ => cstring
end.

Ltac cstring1 :=
match goal with 
| H: 0 <= ?x < Zlength ?s + 1,
  H1: Znth ?x (?s ++ [Byte.zero]) = Byte.zero |- _ =>
  is_var x; assert  (x = Zlength s) by cstring; subst x
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
