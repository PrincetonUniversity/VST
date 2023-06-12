Require Import VST.floyd.base.
Require Import VST.floyd.val_lemmas.

#[export] Hint Rewrite <- @bi.pure_and : gather_prop.

Section PROP.

Context {PROP : bi}.

Implicit Types (P Q R : PROP).

Lemma gather_prop_left:
  forall (P Q : Prop) R,  ⌜P⌝ ∧ (⌜Q⌝ ∧ R) ⊣⊢ ⌜P /\ Q⌝ ∧ R.
Proof. intros. rewrite assoc -bi.pure_and //. Qed.

Lemma gather_prop_right:
  forall (P Q : Prop) R,  (R ∧ ⌜P⌝) ∧ ⌜Q⌝ ⊣⊢ ⌜P /\ Q⌝ ∧ R.
Proof. intros. rewrite -assoc -bi.pure_and bi.and_comm //. Qed.

Lemma andp_in_order1:
  forall P Q, P ∧ Q ⊣⊢ P ∧ (P → Q).
Proof.
  intros.
  iSplit; iIntros "H"; (iSplit; first rewrite bi.and_elim_l //).
  + iApply (bi.impl_intro_l with "H").
    rewrite !bi.and_elim_r //.
  + iApply (modus_ponens with "H").
Qed.

Lemma andp_in_order2:
  forall P Q, P ∧ Q ⊣⊢ Q ∧ (Q → P).
Proof.
  intros.
  rewrite comm.
  apply andp_in_order1.
Qed.

Lemma andp_right1:
  forall P Q R, (P ⊢ Q) -> (P ∧ Q ⊢ R) -> P ⊢ Q ∧ R.
Proof.
  intros.
  rewrite andp_in_order1.
  apply bi.and_intro; first done.
  by apply bi.impl_intro_r.
Qed.

Lemma andp_right2:
  forall P Q R, (P ⊢ R) -> (P ∧ R ⊢ Q) -> P ⊢ Q ∧ R.
Proof.
  intros.
  rewrite comm.
  apply andp_right1; auto.
Qed.

Definition not_a_prop P := True%type.

Lemma flip_prop: forall P (Q : Prop),
      not_a_prop P -> (P ∧ ⌜Q⌝ ⊣⊢ ⌜Q⌝ ∧ P).
Proof. intros; rewrite comm //. Qed.

Lemma gather_prop3:
  forall (P: Prop) Q R,  not_a_prop R -> not_a_prop Q -> R ∧ (⌜P⌝ ∧ Q) ⊣⊢ ⌜P⌝ ∧ (R ∧ Q).
Proof.
  intros. rewrite bi.and_comm. rewrite -bi.and_assoc.
  rewrite (bi.and_comm Q); auto.
Qed.

Lemma gather_prop4:
  forall (P: Prop) Q R,  not_a_prop R -> not_a_prop Q -> (⌜P⌝ ∧ R) ∧ Q ⊣⊢ ⌜P⌝ ∧ (R ∧ Q).
Proof.
  intros. rewrite -bi.and_assoc. auto.
Qed.

Lemma gather_prop5:
  forall (P: Prop) Q R,  not_a_prop R -> not_a_prop Q -> ((R ∧ ⌜P⌝) ∧ Q) ⊣⊢ ⌜P⌝ ∧ (R ∧ Q).
Proof.
  intros. rewrite -bi.and_assoc. rewrite bi.and_comm. rewrite -bi.and_assoc.
  f_equiv; apply bi.and_comm.
Qed.

Lemma go_lower_lem1:
  forall (P1 P: Prop) (QR PQR: PROP),
      (P1 -> ⌜P⌝ ∧ QR ⊢ PQR) ->
      (⌜P1 /\ P⌝ ∧ QR ⊢ PQR).
Proof.
 intros.
 apply bi.pure_elim_l; intros [? ?].
 trans (⌜P⌝ ∧ QR).
 apply bi.and_intro; auto.
 apply H; auto.
Qed.

Lemma go_lower_lem1':
  forall (P1 P2 P: Prop) (QR PQR: PROP),
      (⌜P1 /\ (P2 /\ P)⌝ ∧ QR ⊢ PQR) ->
      (⌜(P1 /\ P2) /\ P⌝ ∧ QR ⊢ PQR).
Proof.
 intros.
 rewrite -H and_assoc //.
Qed.

(* These versions can sometimes take minutes,
   when A and B can't be unified
#[export] Hint Extern 1 (_ ⊢ _) => (simple apply (@entails_refl PROP _) ) : cancel.
#[export] Hint Extern 1 (_ ⊢ |> _) => (simple apply (@now_later PROP _ _) ) : cancel.
*)

Lemma cancel1_start:
 forall P Q : PROP,
   (P ⊢ Q ∗ emp) ->
   P ⊢ Q.
Proof. intros. rewrite bi.sep_emp in H; auto.
Qed.

Lemma cancel1_here:
  forall P P' Q1 Q2 Q3 : PROP,
  (P' ⊢ Q2) ->
  (P ⊢ Q1 ∗ Q3) ->
  P ∗ P' ⊢ (Q1 ∗ Q2) ∗ Q3.
Proof.
intros. rewrite (bi.sep_comm Q1).
rewrite -bi.sep_assoc.  rewrite bi.sep_comm. apply bi.sep_mono; auto.
Qed.

Lemma cancel1_next:
  forall P Q1 Q2 Q3 : PROP,
   (P ⊢ Q1 ∗ (Q2 ∗ Q3)) ->
   P ⊢ (Q1 ∗ Q2) ∗ Q3.
Proof. intros. rewrite -bi.sep_assoc; auto. Qed.

Lemma cancel1_last:
  forall P P' Q2 Q3 : PROP,
  (P' ⊢ Q2) ->
  (P ⊢ Q3) ->
  P ∗ P' ⊢ Q2 ∗ Q3.
Proof.
 intros. rewrite bi.sep_comm; apply bi.sep_mono; auto.
Qed.

Lemma cancel1_finish1:
  forall P Q1 Q2 Q3 : PROP,
   (P ⊢ (Q1 ∗ Q2) ∗ Q3) ->
   P ⊢ Q1 ∗ (Q2 ∗ Q3).
Proof.
 intros. rewrite bi.sep_assoc. auto.
Qed.

Lemma cancel1_finish2:
  forall P Q : PROP,
    (P ⊢ Q) ->
   P ⊢ Q ∗ emp.
Proof. intros. rewrite bi.sep_emp; auto.
Qed.

Lemma cancel_frame0:
  (emp : PROP) ⊢ fold_right bi_sep emp nil.
Proof. done. Qed.

Lemma cancel_frame2: forall (P Q: PROP) F,
     (Q  ⊢ fold_right_sepcon F)  ->
    (P ∗ Q) ⊢ fold_right_sepcon (P::F).
Proof. intros. apply bi.sep_mono; auto.
Qed.

Lemma cancel_frame1: forall (P: PROP),
         P ⊢ fold_right_sepcon (P::nil).
Proof. intros. unfold fold_right_sepcon. rewrite bi.sep_emp //.
Qed.

Fixpoint fold_right_sepconx (l: list PROP) : PROP :=
match l with
| nil => emp
| a::nil => a
| a::b => a ∗ fold_right_sepconx b
end.

Definition fold_left_sepconx (l: list PROP) : PROP :=
match l with
| nil => emp
| a::l => (fix fold_left_sepconx (a: PROP) (l: list PROP) {struct l}: PROP :=
          match l with
          | nil => a
          | b :: l => fold_left_sepconx (bi_sep a b) l
          end) a l
end.

Lemma fold_right_sepconx_eq: forall l, fold_right_sepconx l ⊣⊢ fold_right_sepcon l.
Proof.
induction l; simpl; auto.
rewrite -IHl.
destruct l; simpl; auto. rewrite bi.sep_emp; auto.
Qed.

Lemma fold_left_sepconx_eq: forall l, fold_left_sepconx l ⊣⊢ fold_right_sepcon l.
Proof.
  intros; rewrite <- fold_right_sepconx_eq.
  destruct l; auto; simpl.
  revert b; induction l; intros; auto.
  simpl in *.
  rewrite <- IHl.
  clear IHl.
  revert b a; induction l; intros; auto.
  simpl.
  rewrite !IHl bi.sep_assoc //.
Qed.

Lemma fold_right_sepconx_eqx:
  forall A B, (A ⊢ fold_right_sepconx B) -> A ⊢ fold_right_sepcon B.
Proof.
intros.
rewrite <- fold_right_sepconx_eq; auto.
Qed.

Lemma cancel_left: forall P Q R: PROP,
   (Q ⊢ R) -> P ∗ Q ⊢ P ∗ R.
Proof.
intros; apply bi.sep_mono; auto.
Qed.

Lemma pull_left_special: forall A B C : PROP,
    (B ∗ (A ∗ C)) ⊣⊢ (A ∗ (B ∗ C)).
Proof.
intros. rewrite bi.sep_comm. rewrite -bi.sep_assoc. f_equiv.
 apply bi.sep_comm.
Qed.

Lemma pull_left_special0: forall A B : PROP,
    (B ∗ A) ⊣⊢ (A ∗ B).
Proof.
intros; apply bi.sep_comm.
Qed.

Lemma fun_equal: forall {A B} (f g : A -> B) (x y : A),
  f = g -> x = y -> f x = g y.
Proof. congruence. Qed.

Lemma fun_equal': forall {A B} (f g : forall (x:A), B x) (y : A),
  f = g -> f y = g y.
Proof. congruence. Qed.

Lemma if_congr: forall {T: Type} (a a': bool) (b b' c c' : T),
  a=a' -> b=b' -> c=c' -> (if a then b else c) = (if a' then b' else c').
Proof.
intros; subst; auto.
Qed.

End PROP.

Ltac not_a_prop := match goal with
  | |- not_a_prop  (⌜_⌝) => fail 1
  | |- _ => apply Coq.Init.Logic.I
end.

#[export] Hint Rewrite @gather_prop_left @gather_prop_right : gather_prop.
#[export] Hint Rewrite @flip_prop using not_a_prop : gather_prop.
#[export] Hint Rewrite @gather_prop3 using not_a_prop : gather_prop.
#[export] Hint Rewrite @gather_prop4 using not_a_prop : gather_prop.
#[export] Hint Rewrite @gather_prop5 using not_a_prop : gather_prop.
#[export] Hint Rewrite @sepcon_andp_prop @sepcon_andp_prop' : gather_prop gather_prop_core.
#[export] Hint Extern 2 (?A ⊢ ?B) => (constr_eq A B; simple apply entails_refl) : cancel.
#[export] Hint Extern 2 (?A ⊢ ▷ ?B) => (constr_eq A B; simple apply bi.later_intro) : cancel.

Ltac cancel1 :=
 first [
   simple apply cancel1_here; [
    try match goal with H := _ (*: list PROP*) |- _ => clear H end; (*
      this line is to work around Coq 8.4 bug,
      Anomaly: undefined_evars_of_term *)
    solve [eauto with nocore cancel]
   | ]
 | simple apply cancel1_next; cancel1
 | simple apply cancel1_last; [
    try match goal with H := _ (*: list PROP*) |- _ => clear H end; (*
      this line is to work around Coq 8.4 bug,
      Anomaly: undefined_evars_of_term *)
    solve [eauto with nocore cancel] | ]
 ].

Ltac cancel2 :=
  simple apply cancel1_start;
  cancel1;
  repeat simple apply cancel1_finish1;
  try simple apply cancel1_finish2.

Ltac lift1 a e1 rho  :=
 match e1 with
 | lift0 rho => constr:(a)
 | lift0 ?a1 => constr: (lift0 (a a1))
 | _ => constr:(lift1 a e1)
 end.

Ltac lift2 a e1 e2 rho :=
 match e1 with
 |  lift0 ?a1 => lift1 (a a1) e2 rho
 | _ => constr:(lift2 a e1 e2)
 end.

Ltac lift3 a e1 e2 e3 rho :=
 match e1 with
 |  lift0 ?a1 => lift2 (a a1) e2 e3 rho
 | _ => constr:(lift3 a e1 e2 e3)
 end.

Ltac lift4 a e1 e2 e3 e4 rho :=
 match e1 with
 |  lift0 ?a1 => lift3 (a a1) e2 e3 e4 rho
 | _ => constr:(lift4 a e1 e2 e3 e4)
 end.

Ltac abstract_env rho P :=
  match P with
   | @bi_emp ?PROP => constr:(@bi_emp (monPred environ_index PROP) _ _)
   | @bi_sep ?PROP ?e1 ?e2 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
       in constr:(@bi_sep (monPred environ_index PROP) _ _ e1' e2')
   | ?a0 ?a1 ?a2 ?e1 ?e2 ?e3 ?e4 =>
      let e1' := abstract_env rho e1  in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1 a2) e1' e2' e3' e4' rho
   | ?a0 ?a1 ?e1 ?e2 ?e3 ?e4 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1) e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 ?e4 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift4 a0 e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3
      in lift3 a0 e1' e2' e3' rho
   | ?a0 ?e1 ?e2 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
      in lift2 a0 e1' e2' rho
   | ?a0 ?e1 => let e1' := abstract_env rho e1 in lift1 a0 e1' rho
   | rho => constr: (lift1)
   | ?a => constr:(lift0 a)
   end.


Ltac fixup_lifts :=
 repeat
 match goal with
 | |- context[@lift0 ?PROP] => change (@lift0 PROP) with (@liftx (LiftEnviron PROP))
 | |- context[@lift1 ?A ?PROP] => change (@lift1 A PROP) with (@liftx (Tarrow A (LiftEnviron PROP)))
 | |- context[@lift2 ?A ?B ?PROP] =>  change (@lift2 A B PROP) with (@liftx (Tarrow A (Tarrow B (LiftEnviron PROP))))
 | |- context[@lift3 ?A ?B ?C ?PROP] => change (@lift3 A B C PROP) with (@liftx (Tarrow A (Tarrow B (Tarrow C (LiftEnviron PROP)))))
 | |- context[@lift4 ?A ?B ?C ?D ?PROP] => change (@lift4 A B C D PROP) with (@liftx (Tarrow A (Tarrow B (Tarrow C (Tarrow D (LiftEnviron PROP))))))
 end.

Ltac unfold_right_sepcon A :=
 lazymatch A with
 | (?B ∗ ?C) => let x := unfold_right_sepcon C
                               in let y := constr:(B :: x)
                               in y
 | ?D => let y := constr:(D::nil) in y
end.

Ltac cancel_frame :=
match goal with
| |- _ ⊢ fold_right_sepcon _  => (* setup *)
   rewrite -!bi.sep_assoc; cancel_frame
| F := ?v |- ?A ⊢ fold_right_sepcon ?F  => (* fast way *)
   is_evar v;
   apply fold_right_sepconx_eqx;
   let w := unfold_right_sepcon A
    in instantiate (1:=w) in (value of F);
    unfold F;
    unfold fold_right_sepconx;
    simple apply entails_refl
(*
| |- _ ⊢ fold_right_sepcon ?F  =>  (* slow way *)
   repeat apply cancel_frame2_low;
    try (unfold F; apply cancel_frame0_low);
    try (unfold F; apply cancel_frame1_low)
*)
| |- ?P ⊢ fold_right _ _ ?F ?rho  =>
     let P' := abstract_env rho P in
       change ( P' rho ⊢ fold_right bi_sep emp F rho);
   fixup_lifts; cbv beta;
    repeat rewrite -bi.sep_assoc;
   repeat match goal with |- (_ * _) _ ⊢ _ =>
                   apply cancel_frame2
                    end;
    try (unfold F; apply cancel_frame1);
    try (instantiate (1:=nil) in (value of F); unfold F; apply cancel_frame0)
 end.


Ltac pull_left A :=
 (* For some reason in Coq 8.4pl3 and perhaps other versions,
  this works better than the version in log_normalize
  which is simply,
   repeat rewrite <- (pull_right A) || rewrite <- (pull_right0 A)
  and which sometimes fails when the terms get complicated.
 *)
  repeat match goal with
  | |- context [?Q ∗ ?R ∗ A] => rewrite <- (pull_right A Q R)
  | |- context [?Q ∗ A] => rewrite <- (pull_right0 A Q)
  end.

Ltac qcancel P :=
 lazymatch P with
 | bi_sep ?A ?B => 
     match goal with |- _ ⊢ ?Q =>
       try match Q with context [A] =>
        let a := fresh "A" in set (a:=A);
         rewrite ?(pull_left_special0 a) ?(pull_left_special a);
         apply cancel_left;
         clear a
       end;
       qcancel B
     end
 | ?A => 
     try match goal with |- _ ⊢ ?Q =>
       lazymatch Q with context [A] =>
        let a := fresh "A" in set (a:=A);
         rewrite ?(pull_left_special0 a) ?(pull_left_special a);
         rewrite ?(pull_left_special0 A) ?(pull_left_special A);
         apply cancel_left;
         clear a
      end
     end
 end.

Ltac is_Type_or_type T :=
  match type of T with
  | Type => idtac
  | type => idtac
  end.


Ltac ecareful_unify :=
  match goal with
  | |- ?X = ?X' => first [is_Type_or_type X | is_evar X | is_evar X' | constr_eq X X']; reflexivity
  | |- ?F _ = ?F' _ => first [apply fun_equal | apply fun_equal' with (f := F)]; revgoals; solve[ecareful_unify]
  | |- (if _ then _ else _) = if _ then _ else _ => simple apply if_congr; solve[ecareful_unify]   
  end; idtac.


Ltac careful_unify :=
  match goal with
  | |- ?X = ?X' => first [is_Type_or_type X | constr_eq X X']; reflexivity
  | |- ?F _ = ?F' _ => first [apply fun_equal | apply fun_equal' with (f := F)]; revgoals; solve[careful_unify]
  | |- (if _ then _ else _) = if _ then _ else _ => simple apply if_congr; solve[careful_unify]   
  end; idtac.

Lemma entails_refl' {PROP : bi} : forall (P Q : PROP), P = Q -> P ⊢ Q.
Proof.
  by intros ?? ->.
Qed.

Ltac cancel :=
  rewrite -?bi.sep_assoc;
  repeat match goal with |- ?A * _ ⊢ ?B * _ => 
     constr_eq A B;  simple apply (cancel_left A)
  end;
  match goal with |- ?P ⊢ _ => qcancel P end;
  repeat first [rewrite bi.emp_sep | rewrite bi.sep_emp];
  try match goal with |- ?A ⊢ ?B => 
       constr_eq A B; simple apply (entails_refl A)
  end;
  match goal with |- ?P ⊢ _ =>
   (* The "emp" is a marker to notice when one complete pass has been made *)
   rewrite <- (bi.emp_sep P)
  end;
  repeat rewrite bi.sep_assoc;
  repeat match goal with
    | |- bi_sep _ emp ⊢ _ => fail 1
    | |- bi_sep _ True ⊢ _ => pull_left True%I
    | |- bi_sep _ ?P' ⊢ _ => first [ cancel2 | pull_left P' ]
   end;
  repeat first [rewrite bi.emp_sep | rewrite bi.sep_emp];
  pull_left True%I;
  first [ simpl; apply entails_refl'; solve [careful_unify]
            (* this is NOT a _complete_ tactic;
                 for example, "simple apply entails_refl" would be more complete.  But that
                 tactic can sometimes take minutes to discover that something doesn't unify;
                 what I have here is a compromise between reliable speed, and (in)completeness.
               *)
          | apply bi.True_intro
          | apply @bi.sep_True_2; solve [auto with nocore typeclass_instances]
          | apply @bi.True_sep_2; solve [auto with nocore typeclass_instances]
          | cancel_frame
          | idtac
          ].

Section PROP.

Context {PROP : bi}.

Local Notation fold_right_sepcon := (@fold_right_sepcon PROP).

Inductive syntactic_cancel: list PROP -> list PROP -> list PROP -> list PROP -> Prop :=
| syntactic_cancel_nil: forall R, syntactic_cancel R nil R nil
| syntactic_cancel_cons_succeed: forall n R0 R L0 L F Res,
    find_nth_preds (fun R0 => R0 ⊢ L0) R (Some (n, R0)) ->
    syntactic_cancel (delete_nth n R) L F Res ->
    syntactic_cancel R (L0 :: L) F Res
| syntactic_cancel_cons_fail: forall R L0 L F Res,
    find_nth_preds (fun R0 => R0 ⊢ L0) R None ->
    syntactic_cancel R L F Res ->
    syntactic_cancel R (L0 :: L) F (L0 :: Res).

Lemma syntactic_cancel_cons: forall nR0 R L0 L F Res,
  find_nth_preds (fun R0 => R0 ⊢ L0) R nR0 ->
  syntactic_cancel match nR0 with
                   | Some (n, _) => delete_nth n R
                   | None => R
                   end L F Res ->
  syntactic_cancel R (L0 :: L) F (let Res' := Res in
                                 match nR0 with
                                 | Some _ => Res'
                                 | None => L0 :: Res'
                                 end).
Proof.
  intros.
  destruct nR0 as [[? ?]|].
  + eapply syntactic_cancel_cons_succeed; eauto.
  + eapply syntactic_cancel_cons_fail; eauto.
Qed.

Lemma delete_nth_SEP: forall R n R0,
  nth_error R n = Some R0 ->
  fold_right_sepcon R ⊢ R0 ∗ fold_right_sepcon (delete_nth n R).
Proof.
  intros.
  revert R H; induction n; intros; destruct R; try solve [inv H].
  + inv H.
    simpl.
    auto.
  + simpl in H.
    apply IHn in H.
    simpl.
    rewrite bi.sep_assoc (bi.sep_comm _ b) -bi.sep_assoc.
    apply bi.sep_mono; auto.
Qed.

Lemma syntactic_cancel_solve1: forall F,
  fold_right_sepcon F ⊢ fold_right_sepcon nil ∗ fold_right_sepcon F.
Proof.
  intros.
  simpl; rewrite bi.emp_sep; auto.
Qed.

Lemma syntactic_cancel_solve2: forall G,
  fold_right_sepcon G ⊢ fold_right_sepcon nil ∗ True.
Proof.
  intros.
  simpl; rewrite bi.emp_sep.
  apply bi.True_intro.
Qed.

Lemma syntactic_cancel_spec1: forall G1 L1 G2 L2 F,
  syntactic_cancel G1 L1 G2 L2 ->
  (fold_right_sepcon G2 ⊢ fold_right_sepcon L2 ∗ F) ->
  fold_right_sepcon G1 ⊢ fold_right_sepcon L1 ∗ F.
Proof.
  intros.
  revert F H0; induction H; intros.
  + auto.
  + apply IHsyntactic_cancel in H1.
    simpl.
    rewrite -bi.sep_assoc.
    etrans; [| apply bi.sep_mono; [done | apply H1]].
    clear IHsyntactic_cancel H1.
    apply find_nth_preds_Some in H.
    destruct H.
    etrans; [apply delete_nth_SEP; eauto |].
    apply bi.sep_mono; auto.
  + simpl in H1.
    rewrite (bi.sep_comm L0) -bi.sep_assoc in H1.
    apply (IHsyntactic_cancel (L0∗F0)) in H1.
    etrans; [exact H1 |].
    simpl.
    rewrite bi.sep_assoc.
    apply bi.sep_mono; auto.
    rewrite bi.sep_comm; auto.
Qed.

Lemma syntactic_cancel_spec2: forall G1 L1 G2 L2 G3 L3 F,
  syntactic_cancel G1 L1 G2 L2 ->
  syntactic_cancel G2 L2 G3 L3 ->
  (fold_right_sepcon G3 ⊢ fold_right_sepcon L3 ∗ F) ->
  fold_right_sepcon G1 ⊢ fold_right_sepcon L1 ∗ F.
Proof.
  intros.
  eapply syntactic_cancel_spec1; eauto.
  eapply syntactic_cancel_spec1; eauto.
Qed.

Lemma syntactic_cancel_solve3:
  fold_right_sepcon nil ⊢ fold_right_sepcon nil.
Proof.
  auto.
Qed.

Lemma syntactic_cancel_spec3: forall G1 L1 G2 L2,
  syntactic_cancel G1 L1 G2 L2 ->
  (fold_right_sepcon G2 ⊢ fold_right_sepcon L2) ->
  fold_right_sepcon G1 ⊢ fold_right_sepcon L1.
Proof.
  intros.
  rewrite <- (bi.sep_emp (fold_right_sepcon L1)).
  eapply syntactic_cancel_spec1; eauto.
Qed.

Inductive merge_abnormal_PROP: PROP -> option PROP -> option PROP -> Prop :=
| merge_abnormal_PROP_None: forall P, merge_abnormal_PROP P None (Some P)
| merge_abnormal_PROP_TT_Some: forall P, merge_abnormal_PROP True (Some P) (Some P)
| merge_abnormal_PROP_Some_TT: forall P, merge_abnormal_PROP P (Some True) (Some P).

Inductive fold_abnormal_PROP: list PROP -> list PROP -> option PROP -> Prop :=
| fold_abnormal_PROP_nil:
    fold_abnormal_PROP nil nil None
| fold_abnormal_PROP_TT: forall R res R' res',
    fold_abnormal_PROP R R' res ->
    merge_abnormal_PROP True res res' ->
    fold_abnormal_PROP (True :: R) R' res'
| fold_abnormal_PROP_fold: forall F R res R' res',
    fold_abnormal_PROP R R' res ->
    merge_abnormal_PROP (fold_right_sepcon F) res res' ->
    fold_abnormal_PROP ((fold_right_sepcon F) :: R) R' res'
| fold_abnormal_PROP_normal: forall P R R' res,
    fold_abnormal_PROP R R' res ->
    fold_abnormal_PROP (P :: R) (P :: R') res.

Definition Some_or_emp (res: option PROP) := match res with | Some P => P | _ => emp end.

Lemma merge_abnormal_PROP_spec: forall P res res',
  merge_abnormal_PROP P res res' ->
  Some_or_emp res' ⊢ P ∗ Some_or_emp res.
Proof.
  intros.
  inv H; simpl.
  + rewrite bi.sep_emp; auto.
  + apply bi.True_sep_2.
  + apply bi.sep_True_2.
Qed.

Lemma fold_abnormal_PROP_spec: forall R R' res,
  fold_abnormal_PROP R R' res ->
  fold_right_sepcon R' ∗ Some_or_emp res ⊢ fold_right_sepcon R.
Proof.
  intros.
  induction H; simpl.
  + rewrite bi.emp_sep; auto.
  + apply merge_abnormal_PROP_spec in H0.
    etrans; [apply bi.sep_mono; [done | apply H0] |].
    rewrite bi.sep_assoc.
    rewrite (bi.sep_comm _ True).
    rewrite -bi.sep_assoc.
    apply bi.sep_mono; auto.
  + apply merge_abnormal_PROP_spec in H0.
    etrans; [apply bi.sep_mono; [done | apply H0] |].
    rewrite bi.sep_assoc.
    rewrite (bi.sep_comm _ (fold_right_sepcon F)).
    rewrite -bi.sep_assoc.
    apply bi.sep_mono; auto.
  + rewrite -bi.sep_assoc.
    apply bi.sep_mono; auto.
Qed.

Inductive construct_fold_right_sepcon_rec: PROP -> list PROP -> list PROP -> Prop :=
| construct_fold_right_sepcon_rec_sepcon: forall P Q R R' R'',
    construct_fold_right_sepcon_rec Q R R' ->
    construct_fold_right_sepcon_rec P R' R'' ->
    construct_fold_right_sepcon_rec (P ∗ Q) R R''
| construct_fold_right_sepcon_rec_emp: forall R,
    construct_fold_right_sepcon_rec emp R R
| construct_fold_right_sepcon_rec_single: forall P R,
    construct_fold_right_sepcon_rec P R (P :: R).

Local Unset Elimination Schemes. (* ensure that we avoid name collision with the above *)
Inductive construct_fold_right_sepcon: PROP -> list PROP-> Prop :=
| construct_fold_right_sepcon_constr: forall P R,
    construct_fold_right_sepcon_rec P nil R ->
    construct_fold_right_sepcon P R.
Scheme Minimality for construct_fold_right_sepcon Sort Prop.
Local Set Elimination Schemes.

Lemma construct_fold_right_sepcon_spec: forall P R,
  construct_fold_right_sepcon P R ->
  fold_right_sepcon R ⊣⊢ P.
Proof.
  intros.
  destruct H.
  rename R into R'.
  transitivity (fold_right_sepcon nil ∗ P).
  2:{
    simpl.
    rewrite !bi.emp_sep.
    auto.
  }
  forget (@nil PROP) as R.
  induction H.
  + etransitivity; [eassumption |].
    transitivity ((fold_right_sepcon R ∗ Q) ∗ P); [f_equiv; eassumption |].
    clear.
    rewrite (bi.sep_comm P).
    rewrite -!bi.sep_assoc; auto.
  + rewrite bi.sep_emp; auto.
  + simpl.
    rewrite (bi.sep_comm _ P).
    auto.
Qed.

Definition before_symbol_cancel (P Q: list PROP) (res: option PROP): Prop :=
  match res with
  | Some R => fold_right_sepcon P ⊢ fold_right_sepcon Q ∗ R
  | None => fold_right_sepcon P ⊢ fold_right_sepcon Q
  end.

Lemma symbolic_cancel_setup: forall P P' Q Q' Q'' Qr,
  construct_fold_right_sepcon P P' ->
  construct_fold_right_sepcon Q Q' ->
  fold_abnormal_PROP Q' Q'' Qr ->
  before_symbol_cancel P' Q'' Qr ->
  P ⊢ Q.
Proof.
  intros.
  apply construct_fold_right_sepcon_spec in H.
  apply construct_fold_right_sepcon_spec in H0.
  apply fold_abnormal_PROP_spec in H1.
  rewrite <- H, <- H0.
  etrans; [| exact H1].
  destruct Qr; auto.
Qed.

(*

Export ListNotations.

Goal forall A B C D E F G H I J K L: PROP,
  A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
  A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) ⊢
  (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
  (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G).
Proof.
  intros.
  Time
  do 4
  match goal with
  | |- ?P => assert (P /\ P /\ P); [| tauto]; split; [| split]
  end;
  (rewrite -?bi.sep_assoc;
  repeat match goal with |- ?A * _ ⊢ ?B * _ => 
     constr_eq A B;  simple apply (cancel_left A)
  end;
  match goal with |- ?P ⊢ _ => qcancel P end;
  repeat first [rewrite bi.emp_sep | rewrite bi.sep_emp];
  try match goal with |- ?A ⊢ ?B => 
       constr_eq A B; simple apply (entails_refl A)
  end;
  match goal with |- ?P ⊢ _ =>
   (* The "emp" is a marker to notice when one complete pass has been made *)
   rewrite <- (bi.emp_sep P)
  end;
  repeat rewrite bi.sep_assoc;
  repeat match goal with
    | |- sepcon _ emp ⊢ _ => fail 1
    | |- sepcon _ TT ⊢ _ => pull_left (@TT PROP _)
    | |- sepcon _ ?P' ⊢ _ => first [ cancel2 | pull_left P' ]
   end;
  repeat first [rewrite bi.emp_sep | rewrite bi.sep_emp];
  pull_left (@TT PROP _);
  first [ simpl; apply entails_refl'; solve [careful_unify]
            (* this is NOT a _complete_ tactic;
                 for example, "simple apply entails_refl" would be more complete.  But that
                 tactic can sometimes take minutes to discover that something doesn't unify;
                 what I have here is a compromise between reliable speed, and (in)completeness.
               *)
          | apply bi.True_intro
          | apply @bi.sep_True_2; solve [auto with nocore typeclass_instances]
          | apply @bi.True_sep_2; solve [auto with nocore typeclass_instances]
          | cancel_frame
          | idtac
          ]).


  cancel. (* New cancel: 8.983 9.199 8.599 *)
          (* Old cancel: 133.919 133.224 138.729 *)
Abort




Goal forall A B C D: PROP,
  A * B * (C * A) * B ⊢ B * (A * A) * TT.
Proof.
  intros.
  Time
  do 4
  match goal with
  | |- ?P => assert (P /\ P /\ P); [| tauto]; split; [| split]
  end;
(* cancel. (* 4.323 4.275 3.887 3.763 3.684 3.66 3.6 3.534 3.616 3.6 3.591 3.606 *) *)
(*  new_cancel. (* 0.615 0.656 0.655 0.653 0.687 *) *)

Goal forall A B C D: PROP,
  A * B * (C * fold_right_sepcon [A; B] * A) * B ⊢ B * (A * A) * fold_right_sepcon [A; B].
Proof.
  intros.
  cancel.

Goal forall A B C D: PROP,
  A * B * (C * A) * B ⊢ B * TT * (A * A).
Proof.
  intros.
  new_cancel.

Goal forall A B C D: PROP, exists F': list PROP,
  let F := F' in
  A * B * (C * A) * B ⊢ B * (A * A) * fold_right_sepcon F.
Proof.
  intros; eexists; intros.
  new_cancel.

Goal forall A B C D: PROP,
  A * B * (C * A) * B ⊢ B * (A * D).
Proof.
  intros.
  new_cancel.


Goal forall A B C D: PROP,
  fold_right_sepcon [A; B; C; A; B] ⊢ fold_right_sepcon [B; A; D].
Proof.
  intros.
  cancel_for_normal.

Goal forall A B C D: PROP,
  fold_right_sepcon [A; B; C; A; B] ⊢ fold_right_sepcon [B; A] * TT.
Proof.
  intros.
  cancel_for_TT.

Goal forall A B C D: PROP, exists F: list PROP,
  fold_right_sepcon [A; B; C; A; B] ⊢ fold_right_sepcon [B; A] * fold_right_sepcon F.
Proof.
  intros.
  eexists.
  cancel_for_evar_frame.
*)

Lemma wand_refl_cancel_right:
  forall (P: PROP), emp ⊢ P -∗ P.
Proof.
  iIntros; done.
Qed.

Lemma cancel_emp_wand:
  forall P Q R: PROP,
    (P ⊢ Q) ->
    P ⊢ Q ∗ (R -∗ R).
Proof.
  intros ??? ->.
  iIntros "$ $".
Qed.

Lemma allp_instantiate:
   forall {B} (P : B -> PROP) (x : B),
       (∀ y : B, P y) ⊢ P x.
Proof.
  intros; apply bi.forall_elim.
Qed.

(* these two lemmas work better with new sep_apply and sep_eapply *)
Lemma allp_instantiate': forall (B : Type) (P : B -> PROP) (x : B),
  bi_forall P ⊢ P x.
Proof. intros. apply allp_instantiate. Qed.

Lemma wand_frame_elim'': forall (P Q : PROP),
  (P -∗ Q) ∗ P ⊢ Q.
Proof. apply bi.wand_elim_l. Qed.

Lemma prop_sepcon: forall P (Q : PROP), ⌜P⌝ ∗ Q ⊣⊢ ⌜P⌝ ∧ (True ∗ Q).
Proof.
  intros.
  iSplit; iIntros "($ & $)"; done.
Qed.

Lemma prop_sepcon2: forall P (Q : PROP), Q ∗ ⌜P⌝ ⊣⊢ ⌜P⌝ ∧ (True ∗ Q).
Proof.
  intros.
  rewrite bi.sep_comm. apply prop_sepcon.
Qed.

End PROP.

Ltac local_cancel_in_syntactic_cancel unify_tac :=
  cbv beta;
  match goal with |- ?A ⊢ ?B => 
    solve [ constr_eq A B; simple apply (entails_refl A)
          | tryif first [has_evar A | has_evar B] then fail else auto with nocore cancel
          | apply entails_refl'; unify_tac ]
  end.

Ltac syntactic_cancel local_tac :=
  repeat first
         [ (*simple*) apply syntactic_cancel_nil
         | (*simple*) apply syntactic_cancel_cons;
           [ find_nth local_tac
           | cbv iota; unfold delete_nth; cbv zeta iota
           ]
         ].

(* To solve: Frame := ?Frame |- fold_right_sepcon G ⊢ fold_right_sepcon L * fold_right_sepcon Frame *)
Ltac cancel_for_evar_frame' local_tac :=
  eapply syntactic_cancel_spec1;
  [ syntactic_cancel local_tac
  | cbv iota; cbv zeta beta;
    first [ match goal with
            | |- _ ⊢ _ * fold_right_sepcon ?F => try unfold F
            end;
            simple apply syntactic_cancel_solve1
          | match goal with
            | |- fold_right_sepcon ?A ⊢ fold_right_sepcon ?B ∗ ?C =>
                  let a := fresh in let b := fresh in let c := fresh in 
                  pose (a:=A); pose (b:=B); pose (c:=C);
                  change (fold_right_sepcon a ⊢ fold_right_sepcon b ∗ c);
                  rewrite <- fold_left_sepconx_eq;
                  subst a b c
(*                  rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B) *)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].

(* To solve: |- fold_right_sepcon G ⊢ fold_right_sepcon L * TT *)
Ltac cancel_for_TT local_tac :=
  eapply syntactic_cancel_spec1;
  [ syntactic_cancel local_tac
  | cbv iota; cbv zeta beta;
    first [ simple apply syntactic_cancel_solve2
          | match goal with
            | |- fold_right_sepcon ?A ⊢ fold_right_sepcon ?B ∗ ?C =>
                  let a := fresh in let b := fresh in let c := fresh in 
                  pose (a:=A); pose (b:=B); pose (c:=C);
                  change (fold_right_sepcon a ⊢ fold_right_sepcon b ∗ c);
                  rewrite <- fold_left_sepconx_eq;
                  subst a b c
(* rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B) *)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].

Ltac cancel_for_normal local_tac :=
  eapply syntactic_cancel_spec3;
  [ syntactic_cancel local_tac
  | cbv iota; cbv zeta beta;
    first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A ⊢ fold_right_sepcon ?B =>
                  let a := fresh in let b := fresh in
                  pose (a:=A); pose (b:=B);
                  change (fold_right_sepcon a ⊢ fold_right_sepcon b);
                  rewrite <- fold_left_sepconx_eq;
                  subst a b
(*  rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B) *)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].


(* return Some true exists TT, return Some false if exists fold_right_sepcon. *)
(* unused?
Ltac Check_normal_PROP_list_rec L :=
  match L with
  | nil => constr:(@None bool)
  | cons TT _ => constr:(Some true)
  | cons (fold_right_sepcon _) _ => constr:(Some false)
  | cons _ ?L0 => Check_normal_PROP_list_rec L0
  end.

Ltac Check_pre_no_TT L :=
  let res := Check_normal_PROP_list_rec L in
  match res with
  | Some true => fail 1000 "No TT should appear in the SEP clause of a funcspec's precondition"
  | _ => idtac
  end.
*)

Ltac construct_fold_right_sepcon_rec :=
  match goal with
  | |- construct_fold_right_sepcon_rec (bi_sep _ _) _ _ =>
         eapply construct_fold_right_sepcon_rec_sepcon;
         [construct_fold_right_sepcon_rec | construct_fold_right_sepcon_rec]
  | |- construct_fold_right_sepcon_rec ?A ?X ?Y =>
         lazymatch A with emp => idtac | _ => 
             change (construct_fold_right_sepcon_rec emp X Y)
         end;
         apply construct_fold_right_sepcon_rec_emp
  | _ =>
         apply construct_fold_right_sepcon_rec_single
  end.

Ltac merge_abnormal_PROP :=
  first
  [ simple apply merge_abnormal_PROP_None
  | simple apply merge_abnormal_PROP_TT_Some
  | simple apply merge_abnormal_PROP_Some_TT
  | fail 1000 "There should not be two fold_right_sepcon in the right side."
  ].

Ltac construct_fold_right_sepcon :=
  apply construct_fold_right_sepcon_constr;
  construct_fold_right_sepcon_rec.

Ltac is_evar_def F := try first [is_var F; unfold F; fail 1 | fail 2 F "is not evar definition"].

Ltac fold_abnormal_PROP :=
  match goal with
  | |- fold_abnormal_PROP nil _ _ =>
         apply fold_abnormal_PROP_nil
  | |- fold_abnormal_PROP (?P :: _) _ _ =>
         match P with
         | True%I => eapply fold_abnormal_PROP_TT; [fold_abnormal_PROP | merge_abnormal_PROP]
         | ⌜True⌝ => eapply fold_abnormal_PROP_TT; [fold_abnormal_PROP | merge_abnormal_PROP]
         | fold_right_sepcon ?F =>
              is_evar_def F;
              eapply fold_abnormal_PROP_fold; [fold_abnormal_PROP | merge_abnormal_PROP]
         | _ => apply fold_abnormal_PROP_normal; fold_abnormal_PROP
         end
  end.

Ltac new_cancel local_tac :=
  match goal with
  | |- _ ⊢ _ => idtac
  | _ => fail "Tactic cancel can only handle proof goals with form _ ⊢ _ (unlifted version)."
  end;
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_PROP
  | match goal with
    | |- before_symbol_cancel _ _ None =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_normal local_tac
    | |- before_symbol_cancel _ _ (Some (fold_right_sepcon _)) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_evar_frame' local_tac
    | |- before_symbol_cancel _ _ (Some True) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_TT local_tac
    | |- before_symbol_cancel _ _ (Some ⌜True⌝) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_TT local_tac
    end
  ].

Ltac cancel_unify_tac :=
  autorewrite with cancel;
  careful_unify.

Ltac cancel_local_tac :=
  cbv beta;
  match goal with |- ?A ⊢ ?B =>
    solve [ constr_eq A B; simple apply (entails_refl A)
          | auto with nocore cancel
          | apply entails_refl'; cancel_unify_tac]
  end.

Ltac cancel ::= new_cancel cancel_local_tac.

Ltac no_evar_cancel_local_tac := local_cancel_in_syntactic_cancel cancel_unify_tac.
Ltac no_evar_cancel := new_cancel no_evar_cancel_local_tac.

Ltac ecancel_unify_tac :=
  autorewrite with cancel;
  ecareful_unify.

Ltac ecancel_local_tac := local_cancel_in_syntactic_cancel ecancel_unify_tac.
Ltac pure_ecancel := new_cancel ecancel_local_tac.
Ltac ecancel := no_evar_cancel; pure_ecancel.

Ltac old_local_tac := local_cancel_in_syntactic_cancel careful_unify.
Ltac cancel_for_evar_frame := cancel_for_evar_frame' ecancel_local_tac.

Ltac info_cancel_local_tac :=
  (tryif try (cancel_local_tac; gfail 1)
    then match goal with |- ?Goal => idtac Goal "fail" end
    else match goal with |- ?Goal => idtac Goal "success" end);
  cancel_local_tac.

Ltac info_cancel := new_cancel info_cancel_local_tac.

Ltac info_ecancel_local_tac :=
  (tryif try (ecancel_local_tac; gfail 1)
    then match goal with |- ?Goal => idtac Goal "fail" end
    else match goal with |- ?Goal => idtac Goal "success" end);
  ecancel_local_tac.

Ltac info_ecancel := info_cancel; new_cancel info_ecancel_local_tac.

Ltac apply_find_core X :=
 match X with
 | ?U -> ?V => match type of U with Prop => apply_find_core V end
 | _ ⊢ _ => constr:(X)
 | ?A = ?B => constr:(A ⊢ B)
 end.

Lemma adjust_sep_apply:  forall {PROP : bi} (Q: PROP) (P: Prop),
   (Q ⊢ ⌜P⌝) ->
   Q ⊢ ⌜P⌝ ∧ Q.
Proof. intros. apply bi.and_intro; auto. Qed.

Ltac adjust_sep_apply H :=
 match type of H with 
 | _ ⊢ ⌜_⌝ => constr:(adjust_sep_apply _ _ H)
 | _ => H
 end.

Ltac adjust2_sep_apply H :=
 let x := adjust_sep_apply H in
 match type of x with
 | _ = _ => constr:(entails_refl' _ _ x)
 | _ => x
 end.

Ltac cancel_for_sep_apply := ecancel.

Ltac sep_apply_aux2 H' := 
match type of H' with ?TH =>
     match apply_find_core TH with @bi_entails ?PROP ?C ?D =>
      let frame := fresh "frame" in evar (frame: list PROP);
       trans (C ∗ fold_right_sepcon frame);
             [ solve [cancel_for_sep_apply]
             | etrans; 
                [apply bi.sep_mono; [clear frame; apply H' | apply entails_refl] 
                |  let x := fresh "x" in set (x := fold_right_sepcon frame);
                  subst frame; unfold fold_right_sepcon in x; subst x; 
                  rewrite ?bi.sep_emp
                ]
             ]
     end
     end.

Ltac head_of_type_of H :=
 match type of H with ?A => apply_find_core A end.

Ltac sep_apply_aux1 H := 
 let B := head_of_type_of H in
 lazymatch B with
 | ?A ⊢ _ =>
   lazymatch A with
   | context [⌜?P⌝ ∧ _] =>
      let H' := fresh in
      assert (H' := H);
      rewrite ?(bi.and_assoc (⌜P⌝)) in H';
      let H := fresh in 
      assert (H:P);
       [ clear H' | rewrite -> (prop_true_andp P) in H' by apply H; clear H;
           sep_apply_aux1 H'; clear H' ]
   | _ => sep_apply_aux2 H
    end
 end.

Ltac sep_apply_aux0 H :=
 let B := head_of_type_of H in
 lazymatch B with
 | ?A ?D ⊢ _ =>
    tryif (match type of D with ?DT => constr_eq DT globals end)
   then
    (tryif (unfold A in H) then sep_apply_aux1 H
    else let H' := fresh in
         tryif (assert (H' := H); unfold A in H')
         then sep_apply_aux1 H'
         else sep_apply_aux1 H)
   else sep_apply_aux1 H
 | _ => sep_apply_aux1 H
 end.

Ltac sep_apply_in_entailment H :=
    match goal with |- _ ⊢ _ =>
     let H' := adjust2_sep_apply H in
         sep_apply_aux0 H'
    end.

Ltac my_unshelve_evar name T cb evar_tac :=
  let x := fresh name
  in
  unshelve evar (x:T); revgoals;
  [
    let x' := eval unfold x in x
    in
    clear x; cb x'
  |
    evar_tac x
  ].

Ltac new_sep_apply_in_entailment originalH evar_tac prop_tac :=
  let rec sep_apply_in_entailment_rec H :=
    lazymatch type of H with
    | forall x:?T, _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T);
           [ | sep_apply_in_entailment_rec (H H'); clear H'];
           [ prop_tac | .. ]
      | _ => my_unshelve_evar x T
        ltac:(fun x => sep_apply_in_entailment_rec (H x))
        evar_tac
      end
    | ?T -> _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T);
           [ | sep_apply_in_entailment_rec (H H'); clear H'];
           [ prop_tac | .. ]
      | _ => let x := fresh "arg" in
        my_unshelve_evar x T
          ltac:(fun x => sep_apply_in_entailment_rec (H x))
          evar_tac
      end
    | ?A ⊢ ?B => sep_apply_in_entailment H
    | ?A = ?B => sep_apply_in_entailment H
    | _ => fail 0 originalH "is not an entailment"
    end
  in
  sep_apply_in_entailment_rec originalH.

Ltac cancel_wand :=
  repeat
  match goal with |- _ ⊢ ?B =>
    match B with context [?A -∗ ?A] =>
    rewrite -?bi.sep_assoc;
    pull_right (A -∗ A);
    first [apply cancel_emp_wand | apply wand_refl_cancel_right]
    end
  end.

Ltac norm_rewrite := autorewrite with norm.
 (* New version: rewrite_strat (topdown hints norm).
     But this will have to wait for a future version of Coq
    in which rewrite_strat discharges side conditions.
    According to Matthieu Sozeau, in the Coq trunk as of June 5, 2013,
    rewrite_strat is documented AND discharges side conditions.
    It might be about twice as fast, or 1.7 times as fast, as the old autorewrite.
    And then, maybe use "bottomup" instead of "topdown", see if that's better.

   To test whether your version of Coq works, use this:
*)
Lemma TEST_L : forall n:nat, n=n -> (n + 1 = S n)%nat.
Proof. intros. rewrite <- plus_n_Sm ,<- plus_n_O. reflexivity.
Qed.
#[export] Hint Rewrite TEST_L using reflexivity : test888.
Goal forall n, S n = (n + 1)%nat.
intros.
rewrite_strat (topdown hints test888).
match goal with |- S n = S n => reflexivity end.
Qed.  (* Yes, this works in Coq 8.7.2 *)

Ltac normalize1 :=
         match goal with
            | |- bi_entails(PROP := monPredI _ _) _ _ => let rho := fresh "rho" in split => rho; monPred.unseal
            | |- context [((?P ∧ ?Q) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) by (auto with norm)
            | |- context [(?Q ∗ (?P ∧ ?R))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) by (auto with norm)
            | |- context [((?Q ∧ ?P) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) by (auto with norm)
            | |- context [(?Q ∗ (?R ∧ ?P))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) by (auto with norm)
            | |-  bi_entails ?A ?B => match A with
                   | False => apply bi.False_elim
                   | ⌜_⌝ => apply bi.pure_elim'
                   | bi_exist (fun y => _) => apply bi.exist_elim; (intro y || intro)
                   | ⌜_⌝ ∧ _ => apply bi.pure_elim_l
                   | _ ∧ ⌜_⌝ => apply bi.pure_elim_r
                   | context [ (⌜?P⌝ ∧ ?Q) ∧ ?R ] => rewrite -(bi.and_assoc (⌜P⌝) Q R)
                   | context [ ?Q ∧ (⌜?P⌝ ∧ ?R)] =>
                                  match Q with ⌜_⌝ => fail 2 | _ => rewrite (bi.and_assoc (⌜P⌝) Q R) end
                 (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                    preserves the name of the "y" variable *)
                   | context [(∃ y, _) ∧ _] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply bi.exist_elim; intro y
                   | context [_ ∧ (∃ y, _)] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply bi.exist_elim; intro y
                   | context [(∃ y, _) ∗ _] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply bi.exist_elim; intro y
                   | context [_ ∗ (∃ y, _)] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                                apply bi.exist_elim; intro y
                   | _ => simple apply bi.pure_intro
                   | _ => simple apply bi.True_intro
                   | _ => constr_eq A B; done
                   end
              | |- _ => solve [auto]
              | |- _ ⊢ ⌜?x = ?y⌝ ∧ _ =>
                            (apply pure_intro_l; first by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (apply pure_intro_l; first by (unfold x; reflexivity); unfold x in *; clear x)
              |  |- ?ZZ -> ?YY => match type of ZZ with
                                               | Prop => fancy_intros true || fail 1
                                               | _ => intros _
                                              end
              | |- ~ _ => fancy_intro true
              | |- _ => progress (norm_rewrite) (*; auto with typeclass_instances *)
              | |- forall _, _ => let x := fresh "x" in (intro x; repeat normalize1; try generalize dependent x)
              end.

Ltac normalize :=
   gather_prop;
   repeat (((repeat simple apply go_lower_lem1'; simple apply go_lower_lem1)
              || simple apply bi.pure_elim_l
              || simple apply bi.pure_elim_r);
              fancy_intros true);
   repeat normalize1; try contradiction.

Ltac allp_left x := 
 match goal with |- ?A ⊢ _ => match A with context [@bi_forall ?PROP ?B ?P] =>
   sep_apply_in_entailment (@allp_instantiate PROP B P x)
 end end.
