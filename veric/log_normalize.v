Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import VST.zlist.sublist.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import iris.bi.monpred.
Require Import iris.proofmode.proofmode.
From iris_ora.logic Require Import oupred.
Require Import VST.msl.Extensionality.

Local Open Scope bi_scope.

Create HintDb norm discriminated.

#[export] Hint Extern 0 (_ ⊢ _) => match goal with |- ?A ⊢ ?B => constr_eq A B; simple apply PreOrder_Reflexive end : core.

Ltac solve_andp' :=
  first [ apply PreOrder_Reflexive
        | rewrite bi.and_elim_l; solve_andp'
        | rewrite bi.and_elim_r; solve_andp'].

Ltac solve_andp := repeat apply bi.and_intro; solve_andp'.

Lemma TT_right: forall {PROP : bi} (P : PROP), P ⊢ True.
Proof. intros. apply bi.pure_intro, I. Qed.

Lemma False_left: forall {PROP : bi} (P : PROP), False ⊢ P.
Proof. intros. apply bi.pure_elim'; intuition. Qed.

#[export] Hint Resolve TT_right: norm.
#[export] Hint Resolve False_left : norm.

Ltac norm := auto with norm.

Lemma add_andp: forall {PROP : bi} (P Q : PROP), (P ⊢ Q) -> P ⊣⊢ P ∧ Q.
Proof.
  intros.
  apply bi.equiv_entails; split.
  + apply bi.and_intro; auto.
  + apply bi.and_elim_l; apply PreOrder_Reflexive.
Qed.

Section pred.

Context {M : uora}.
Implicit Types (P Q : ouPred M).

(* For efficiency, we would like to use eq instead of ⊣⊢ to relate equivalent predicates.
   Unfortunately, uPreds/ouPreds do not enjoy extensionality (even with prop_ext).
   Fortunately, most equivalences we want to rewrite with can be proved as equalities anyway.
   Note also that if we switched to uPred_alt, all equivalences would be equalities. *)

Lemma IProp_eq : forall a1 a2 b1 b2, a1 = a2 -> IProp M a1 b1 = IProp M a2 b2.
Proof.
  intros; subst; f_equal; apply proof_irr.
Qed.

Lemma True_and : forall P, (True ∧ P) = P.
Proof.
  intros.
  ouPred.unseal.
  destruct P.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  unfold oupred.ouPred_holds; simpl.
  tauto.
Qed.

Lemma and_True : forall P, (P ∧ True) = P.
Proof.
  intros.
  ouPred.unseal.
  destruct P.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  unfold oupred.ouPred_holds; simpl.
  tauto.
Qed.

Lemma True_or : forall P, (True ∨ P) = True.
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  unfold oupred.ouPred_holds; simpl.
  tauto.
Qed.

Lemma or_True : forall P, (P ∨ True) = True.
Proof.
  intros.
  ouPred.unseal.
  destruct P.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  unfold oupred.ouPred_holds; simpl.
  tauto.
Qed.

Lemma pure_True : forall (P : Prop), P -> (bi_pure(PROP := ouPred M) P) = True.
Proof.
  intros.
  f_equal.
  apply prop_ext; tauto.
Qed.

Lemma prop_true_andp : forall (P : Prop) Q, P -> (⌜P⌝ ∧ Q) = Q.
Proof.
  intros.
  rewrite pure_True // True_and //.
Qed.

Lemma False_and : forall P, (False ∧ P) = False.
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  unfold ouPred_holds.
  tauto.
Qed.

Corollary prop_false_andp : forall (P : Prop) Q, ~P -> (⌜P⌝ ∧ Q) = False.
Proof.
  intros.
  replace P with False%type; first apply False_and.
  apply prop_ext; tauto.
Qed.

Lemma pure_and : forall (P Q : Prop), bi_pure(PROP := ouPredI M) (P /\ Q) = (⌜P⌝ ∧ ⌜Q⌝).
Proof.
  intros.
  ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext; tauto.
Qed.

Lemma exp_comm : forall {B C} (P: B -> C -> ouPred M),
  (∃ x : B, ∃ y : C, P x y) = ∃ y : C, ∃ x : B, P x y.
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  split; intros (a & b & ?); exists b, a; auto.
Qed.

Lemma exp_unit: forall (P: unit -> ouPred M),
  (∃ x, P x) = P tt.
Proof.
  intros.
  ouPred.unseal.
  destruct (P tt) eqn: HP.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  split.
  + intros ([] & H); rewrite HP in H; auto.
  + intros; exists tt; rewrite HP; auto.
Qed.

Lemma allp_unit: forall (P: unit -> ouPred M),
  (∀ x, P x) = P tt.
Proof.
  intros.
  ouPred.unseal.
  destruct (P tt) eqn: HP.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  split.
  + intros H; specialize (H tt); rewrite HP in H; auto.
  + intros ? []; rewrite HP; auto.
Qed.

Definition modus_ponens := @bi.impl_elim_r.

Definition modus_ponens_wand := @bi.wand_elim_r.

Lemma wand_sepcon_wand: forall (P1 P2 Q1 Q2 : ouPred M),
  (P1 -∗ Q1) ∗ (P2 -∗ Q2) ⊢ P1 ∗ P2 -∗ Q1 ∗ Q2.
Proof.
  intros.
  apply bi.wand_intro_r.
  iIntros "((H1 & H2) & P1 & P2)"; iSplitL "H1 P1"; [iApply "H1" | iApply "H2"]; done.
Qed.

Lemma allp_forall: forall {B: Type} (P : B -> ouPred M) Q (x:B), (forall x:B, (P x ⊣⊢ Q)) -> ((∀ x, P x) ⊣⊢ Q).
Proof.
  intros.
  apply bi.equiv_entails; split.
  + rewrite (bi.forall_elim x) H //.
  + apply bi.forall_intro.
    intros.
    rewrite H //.
Qed.

Lemma allp_uncurry: forall (S T: Type) (P: S -> T -> ouPred M),
  (∀ x y, P x y) = ∀ st, P (fst st) (snd st).
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  split.
  + intros ? (?, ?); apply H.
  + intros ? s t; apply (H (s, t)).
Qed.

Lemma allp_depended_uncurry': forall {S: Type} {T: S -> Type} (P: forall s: S, T s -> ouPred M),
  (∀ s: S, (∀ t: T s, P s t)) = ∀ st: sigT T, P (projT1 st) (projT2 st).
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  split.
  + intros ? (?, ?); apply H.
  + intros ? s t; apply (H (existT s t)).
Qed.

Lemma allp_curry: forall (S T: Type) (P: S * T -> ouPred M),
  (∀ x, P x) = ∀ s t, P (s, t).
Proof.
  intros.
  rewrite allp_uncurry; f_equal; extensionality x; destruct x; auto.
Qed.

Lemma exp_uncurry: forall A B (F : A -> B -> ouPred M),
  (∃ a : A, ∃ b : B, F a b) = ∃ ab : A * B, F (fst ab) (snd ab).
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x.
  apply prop_ext.
  split.
  + intros (s & t & ?); exists (s, t); auto.
  + intros ((s, t) & ?); exists s, t; auto.
Qed.

Lemma exp_trivial :
  forall {T: Type} (any: T) P, (∃ x:T, P) = P.
Proof.
  intros.
  ouPred.unseal.
  destruct P; apply IProp_eq; extensionality n x.
  apply prop_ext.
  split; first intros (? & ?); eauto.
Qed.

Lemma allp_andp: forall {B: Type} (P Q: B -> ouPred M), (∀ x, P x ∧ Q x) = ((∀ x, P x) ∧ (∀ x, Q x)).
Proof.
  intros.
  ouPred.unseal.
  apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  + intros H; split; intros ?; apply H.
  + intros (? & ?) ?; split; auto.
Qed.

Lemma imp_right2: forall P Q, P ⊢ Q → P.
Proof.
  intros.
  apply bi.impl_intro_r, bi.and_elim_l.
Qed.

Lemma later_left2: forall A B C : ouPred M, (A ∧ B ⊢ C) -> A ∧ ▷ B ⊢ ▷C.
Proof.
  intros.
  rewrite -H bi.later_and; apply bi.and_mono; try done.
  apply bi.later_intro.
Qed.

Lemma andp_dup: forall P, (P ∧ P) = P.
Proof.
  intros.
  ouPred.unseal.
  destruct P; apply IProp_eq; extensionality n x; apply prop_ext; tauto.
Qed.

Lemma persistently_and_sep_assoc :
    forall P Q R, (<pers> P ∧ (Q ∗ R)) = ((<pers> P ∧ Q) ∗ R).
Proof.
  intros.
  ouPred.unseal;   apply IProp_eq; extensionality n x.
  apply prop_ext.
  split.
  - intros (? & a & b & ? & ? & ?).
    eexists (a ⋅ core x), b; split.
    { rewrite (ora_comm a) -{2}(ora_core_l x).
      rewrite -assoc !(ora_comm (core x)); apply ora_orderN_op; auto. }
    split; auto; split.
    + unfold ouPred_persistently_def, ouPred_holds in *.
      eapply ouPred_mono; eauto.
      rewrite comm; etrans; last apply ora_order_orderN, uora_core_order_op.
      rewrite ora_core_idemp //.
    + eapply (ouPred_mono _ _ _ _ (a ⋅ ε)); eauto.
      * rewrite right_id //.
      * rewrite !(ora_comm a); eapply ora_orderN_op, ora_order_orderN, uora_unit_order_core.
  - intros (a & ? & ? & (? & ?) & ?).
    split.
    + unfold ouPred_persistently_def, ouPred_holds in *.
      eapply ouPred_mono; eauto.
      etrans; last by apply ora_core_monoN.
      edestruct (ora_pcore_order_op a) as (? & Hcore & ?).
      { rewrite cmra_pcore_core //. }
      rewrite cmra_pcore_core in Hcore; inversion Hcore as [?? Heq |]; subst.
      rewrite Heq; by apply ora_order_orderN.
    + eexists _, _; eauto.
Qed.

Lemma persistent_and_sep_assoc' :
    forall {PROP : bi} (P Q R : PROP) {HP : Persistent Q} {HA : Absorbing Q}, P ∗ (Q ∧ R) ⊣⊢ Q ∧ (P ∗ R).
Proof.
  intros; rewrite comm -bi.persistent_and_sep_assoc bi.sep_comm //.
Qed.

Lemma sepcon_andp_prop :
     forall P (Q:Prop) R, (P ∗ (⌜Q⌝ ∧ R)) = (⌜Q⌝ ∧ (P ∗ R)).
Proof.
  intros.
  intros; ouPred.unseal.
  apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ? & ? & ? & ?); split; auto.
    eexists _, _; eauto.
  - intros (? & ? & ? & ? & ? & ?).
    eexists _, _; split; eauto; split; auto; split; auto.
Qed.

Lemma sepcon_andp_prop' :
     forall P (Q:Prop) R, ((⌜Q⌝ ∧ P) ∗ R) = (⌜Q⌝ ∧ (P ∗ R)).
Proof.
  intros.
  intros; ouPred.unseal.
  apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ? & (? & ?) & ?); split; auto.
    eexists _, _; eauto.
  - intros (? & ? & ? & ? & ? & ?).
    eexists _, _; split; eauto; split; auto; split; auto.
Qed.

Lemma wand_eq :
   forall P Q R, (P ⊣⊢ Q ∗ R) -> P ⊣⊢ Q ∗ (Q -∗ P).
Proof.
  intros.
  apply bi.equiv_entails; split; last apply modus_ponens_wand.
  rewrite H; iIntros "($ & $)".
  auto.
Qed.

Lemma forall_pred_ext: forall B (P Q: B -> ouPred M),
 (∀ x : B, (P x ↔ Q x)) ⊢ (∀ x : B, P x) ↔ (∀ x: B, Q x).
Proof.
  intros; apply bi.and_intro; apply bi.impl_intro_r, bi.forall_intro; intros x; rewrite !(bi.forall_elim x);
    rewrite /bi_iff; [rewrite (bi.and_elim_l (_ → _)) | rewrite (bi.and_elim_r (_ → _))]; apply bi.impl_elim_l.
Qed.

Lemma exists_pred_ext : forall B (P Q: B -> ouPred M),
 (∀ x : B, (P x ↔ Q x)) ⊢ (∃ x : B, P x) ↔ (∃ x: B, Q x).
Proof.
  intros; apply bi.and_intro; apply bi.impl_intro_r; rewrite bi.and_exist_l; apply bi.exist_elim; intros x;
    rewrite -(bi.exist_intro x) !(bi.forall_elim x);
    rewrite /bi_iff; [rewrite (bi.and_elim_l (_ → _)) | rewrite (bi.and_elim_r (_ → _))]; apply bi.impl_elim_l.
Qed.

Lemma modus_ponens': forall P Q, P ∧ (P → Q) ⊢ Q ∧ P.
Proof.
  intros; apply bi.and_intro; [apply modus_ponens | apply bi.and_elim_l].
Qed.

Lemma imp_pred_ext: forall B B' P Q,
       (B ↔ B') ∧ (B → (P ↔ Q)) ⊢ (B → P) ↔ (B' → Q).
Proof.
  intros; apply bi.and_intro; apply bi.impl_intro_r;
  rewrite /bi_iff; [rewrite (bi.and_elim_r (_ → _)) (bi.and_elim_l (P → Q)) | rewrite (bi.and_elim_l (_ → _)) (bi.and_elim_r (P → Q))];
    apply bi.impl_intro_l; rewrite !assoc modus_ponens'.
  - rewrite (comm _ B) -!assoc (assoc _ B) modus_ponens' -assoc modus_ponens bi.impl_elim_l bi.and_elim_r //.
  - rewrite -!assoc (assoc _ B) modus_ponens assoc (comm _ B') -assoc modus_ponens bi.impl_elim_l //.
Qed.

Lemma sep_comm : forall P Q, (P ∗ Q) = (Q ∗ P).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split; intros (a & b & ? & ? & ?); exists b, a; repeat (split; auto); by rewrite comm.
Qed.

Lemma sep_assoc : forall P Q R, (P ∗ (Q ∗ R)) = ((P ∗ Q) ∗ R).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (a & ? & ? & ? & b & c & ? & ? & ?).
    exists (a ⋅ b), c; repeat (split; auto).
    + rewrite -assoc.
      etrans; last done.
      rewrite !(ora_comm a); apply ora_orderN_op; auto.
    + exists a, b; auto.
  - intros (? & c & ? & (a & b & ? & ? & ?) & ?).
    exists a, (b ⋅ c); repeat (split; auto).
    + rewrite assoc.
      etrans; last done.
      apply ora_orderN_op; auto.
    + exists b, c; auto.
Qed.

Lemma pull_right: forall P Q R, ((Q ∗ P) ∗ R) = ((Q ∗ R) ∗ P).
Proof.
  intros; rewrite -!sep_assoc (sep_comm _ P) //.
Qed.

Lemma pull_right0: forall P Q, (P ∗ Q) = (Q ∗ P).
Proof.
  exact sep_comm.
Qed.

Lemma prop_imp: forall (P: Prop) Q, P -> (⌜P⌝ → Q) ⊣⊢ Q.
Proof.
  intros.
  rewrite bi.pure_True // bi.True_impl //.
Qed.

Lemma not_prop_right: forall P (Q: Prop), (Q -> P ⊢ False) -> P ⊢ ⌜not Q⌝.
Proof.
  intros.
  rewrite -bi.pure_impl_2; apply bi.impl_intro_l, bi.pure_elim_l; done.
Qed.

Lemma later_prop_andp_sepcon: forall (P: Prop) (Q R : ouPred M),
((▷ ⌜P⌝ ∧ Q) ∗ R) ⊣⊢ (▷ ⌜P⌝) ∧ (Q ∗ R).
Proof.
  intros.
  rewrite bi.persistent_and_sep_assoc //.
Qed.

Lemma andp_prop_derives: forall (P P': Prop) Q Q',
  (P <-> P') ->
  (P -> Q ⊢ Q') ->
  ⌜P⌝ ∧ Q ⊢ ⌜P'⌝ ∧ Q'.
Proof.
  intros.
  rewrite -H; apply bi.pure_elim_l; intros; rewrite bi.pure_True // bi.True_and; auto.
Qed.

Lemma andp_prop_ext:
 forall  (P P': Prop) Q Q',
  (P<->P') ->
  (P -> (Q ⊣⊢ Q')) ->
  ⌜P⌝ ∧ Q ⊣⊢ ⌜P'⌝ ∧ Q'.
Proof.
  intros.
  iSplit; iApply andp_prop_derives; auto; rewrite -?H; intros; rewrite H0 //.
Qed.

Lemma prop_and_same_derives :
  forall (P: Prop) Q, (Q ⊢ ⌜P⌝) -> Q ⊢ ⌜P⌝ ∧ Q.
Proof.
  intros. apply bi.and_intro; auto.
Qed.

Lemma guarded_sepcon_orp_distr: forall (P1 P2: Prop) (p1 p2 q1 q2 : ouPred M),
  (P1 -> P2 -> False) ->
  (⌜P1⌝ ∧ p1 ∨ ⌜P2⌝ ∧ p2) ∗ (⌜P1⌝ ∧ q1 ∨ ⌜P2⌝ ∧ q2) ⊣⊢ ⌜P1⌝ ∧ (p1 ∗ q1) ∨ ⌜P2⌝ ∧ (p2 ∗ q2).
Proof.
  intros.
  iSplit.
  - iIntros "([(% & H1) | (% & H1)] & [(% & H2) | (% & H2)])"; try solve [exfalso; auto];
      [iLeft | iRight]; iFrame; done.
  - iIntros "[(% & H1 & H2) | (% & H1 & H2)]"; iSplitL "H1"; auto.
Qed.

Definition mark (i: nat) (j: ouPred M) := j.

Lemma swap_mark1:
  forall i j Pi Pj B, (i<j)%nat -> ((B ∗ mark i Pi) ∗ mark j Pj) = ((B ∗ mark j Pj) ∗ mark i Pi).
Proof.
  intros; apply pull_right.
Qed.

Lemma swap_mark0:
  forall i j Pi Pj, (i<j)%nat -> (mark i Pi ∗ mark j Pj) = (mark j Pj ∗ mark i Pi).
Proof.
  intros; apply sep_comm.
Qed.

Ltac select_left n :=
  repeat match goal with
 | |- context [((_ ∗ mark ?i _) ∗ mark n _)%I] =>
      rewrite (swap_mark1 i n); [ | solve [simpl; auto]]
 | |- context [(mark ?i _ ∗ mark n _)%I] =>
      rewrite (swap_mark0 i n); [ | solve [simpl; auto]]
end.
Ltac select_all n := match n with
                                | O => idtac
                                | S ?n' => select_left n; select_all n'
                              end.
Ltac markem n P :=
   match P with
   | (?Y ∗ ?Z)%I =>
        (match goal with H: mark _ Z = Z |- _ => idtac end
        || assert (mark n Z = Z) by auto); markem (S n) Y
   | ?Z =>  match goal with H: mark _ Z = Z |- _ => idtac end
                || assert (mark n Z = Z) by auto
  end.

Ltac prove_assoc_commut :=
 clear;
 try (match goal with |- ?F _ -> ?G _ => replace G with F; auto end);
  (rewrite !sep_assoc;
   match goal with |- ?P = _ => markem O P end;
   let LEFT := fresh "LEFT" in match goal with |- ?P = _ => set (LEFT := P) end;
  match goal with H: mark ?n _ = _ |- _ =>
     repeat  match goal with H: mark ?n _ = ?P |- _ => rewrite <- H; clear H end;
     select_all n;
     reflexivity
   end).

Lemma test_prove_assoc_commut : forall A B C D E : ouPred M,
   (D ∗ E ∗ A ∗ C ∗ B) = (A ∗ B ∗ C ∗ D ∗ E).
Proof.
  intros.
  prove_assoc_commut.
Qed.

Lemma sep_emp : forall P, (P ∗ emp) = P.
Proof.
  intros; destruct P; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ? & ? & ?).
    eapply ouPred_mono; eauto.
    etrans; last done.
    etrans; last by rewrite !(ora_comm x0); apply ora_orderN_op.
    rewrite left_id //.
  - intros; exists x, ε; rewrite right_id; repeat split; auto.
    unfold oupred.ouPred_holds.
    reflexivity.
Qed.

Lemma emp_sep : forall P, (emp ∗ P) = P.
Proof.
  intros; rewrite sep_comm; apply sep_emp.
Qed.

Implicit Types (l : list (ouPred M)).

(* use [∗ list] instead of this whenever possible *)
Lemma sepcon_app:
   forall l1 l2, fold_right bi_sep emp (l1 ++ l2) =
  (fold_right bi_sep emp l1 ∗ fold_right bi_sep emp l2).
Proof.
  induction l1; simpl; intros.
  - rewrite emp_sep //.
  - rewrite IHl1 sep_assoc //.
Qed.

Lemma sepcon_rev:
  forall l, fold_right bi_sep emp (rev l) = fold_right bi_sep emp l.
Proof.
  induction l; simpl; auto.
  rewrite sepcon_app; simpl.
  rewrite sep_emp IHl sep_comm //.
Qed.

Global Instance bi_inhabitant : Inhabitant (ouPred M) := bi_emp.

Lemma extract_nth_sepcon : forall l i,
    (0 <= i < Zlength l)%Z ->
    fold_right bi_sep emp l = (Znth i l ∗ fold_right bi_sep emp (upd_Znth i l emp)).
Proof.
  intros.
  erewrite <- sublist_same with (al := l) at 1; auto.
  rewrite -> sublist_split with (mid := i); try lia.
  rewrite (sublist_next i); try lia.
  rewrite sepcon_app; simpl.
  rewrite sep_assoc (sep_comm _ (Znth i l)).
  unfold_upd_Znth_old; rewrite sepcon_app -sep_assoc; simpl.
  rewrite emp_sep //.
Qed.

Lemma replace_nth_sepcon : forall P l i,
    (0 <= i < Zlength l)%Z ->
    (P ∗ fold_right bi_sep emp (upd_Znth i l emp)) =
    fold_right bi_sep emp (upd_Znth i l P).
Proof.
  intros; unfold_upd_Znth_old.
  rewrite !sepcon_app; simpl.
  rewrite emp_sep !sep_assoc (sep_comm P) //.
Qed.

Lemma sepcon_derives_prop : forall P Q R, (P ⊢ ⌜R⌝) -> P ∗ Q ⊢ ⌜R⌝.
Proof.
  intros ??? ->; by iIntros "($ & _)".
Qed.

Lemma sepcon_map : forall {B} (P Q: B -> ouPred M) (l: list B),
    fold_right bi_sep emp (map (fun x => P x ∗ Q x) l) =
      (fold_right bi_sep emp (map P l) ∗ fold_right bi_sep emp (map Q l)).
Proof.
  induction l; simpl.
  - rewrite sep_emp //.
  - rewrite -!sep_assoc (sep_assoc (fold_right _ _ _) (Q a)) (sep_comm (fold_right _ _ _) (Q _)).
    rewrite IHl -sep_assoc //.
Qed.

Lemma sepcon_list_derives : forall l1 l2 (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall i, (0 <= i < Zlength l1)%Z -> Znth i l1 ⊢ Znth i l2),
  fold_right bi_sep emp l1 ⊢ fold_right bi_sep emp l2.
Proof.
  induction l1; destruct l2; auto; simpl; intros; rewrite -> ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite -> Zlength_correct in *; lia).
  apply bi.sep_mono.
  - specialize (Heq 0%Z); rewrite !Znth_0_cons in Heq; apply Heq.
    rewrite Zlength_correct; lia.
  - apply IHl1; [lia|].
    intros; specialize (Heq (i + 1)%Z); rewrite -> !Znth_pos_cons, !Z.add_simpl_r in Heq by lia.
    apply Heq; lia.
Qed.

Lemma sepcon_rotate : forall (lP: list (ouPred M)) m n,
    (0 <= n - m < Zlength lP)%Z ->
    fold_right bi_sep emp lP = fold_right bi_sep emp (sublist.rotate lP m n).
Proof.
  intros.
  unfold sublist.rotate.
  rewrite sepcon_app sep_comm -sepcon_app sublist_rejoin; [| lia..].
  rewrite -> sublist_same by lia; auto.
Qed.

Lemma sepcon_In : forall  l P,
    In P l -> exists Q, fold_right bi_sep emp l = (P ∗ Q).
Proof.
  induction l; [contradiction|].
  intros ? [|]; simpl; subst; eauto.
  destruct (IHl _ H) as [Q IH]; eexists; rewrite IH.
  rewrite sep_comm -sep_assoc; eauto.
Qed.

Lemma extract_wand_sepcon : forall l P, In P l ->
  fold_right bi_sep emp l ⊣⊢ P ∗ (P -∗ fold_right bi_sep emp l).
Proof.
  intros.
  destruct (sepcon_In _ _ H) as [? ->].
  eapply wand_eq; eauto.
Qed.

Global Instance fold_right_sep_proper : Proper (equiv ==> equiv) (fold_right bi_sep (bi_emp : ouPred M)).
Proof.
  intros l; induction l; simpl; intros ? H; inversion H as [| ???? H1 H2]; subst; clear H; auto.
  rewrite H1 IHl /= //.
Qed.

Lemma wand_sepcon_map : forall {B} (R : B -> ouPred M) (l : list B) (P Q : B -> ouPred M)
                          (HR : forall i, In i l -> R i ⊣⊢ P i ∗ Q i),
    fold_right bi_sep emp (map R l) ⊣⊢ fold_right bi_sep emp (map P l) ∗
    (fold_right bi_sep emp (map P l) -∗ fold_right bi_sep emp (map R l)).
Proof.
  intros; eapply wand_eq.
  setoid_rewrite <- sepcon_map.
  induction l; auto; simpl.
  rewrite HR; simpl; auto.
  f_equiv.
  { reflexivity. }
  apply IHl.
  intros; apply HR; simpl; auto.
Qed.

Lemma and_comm : forall P Q, (P ∧ Q) = (Q ∧ P).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext; tauto.
Qed.

Lemma and_assoc : forall P Q R, (P ∧ (Q ∧ R)) = ((P ∧ Q) ∧ R).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ?); repeat split; auto.
  - intros ((? & ?) & ?); repeat split; auto.
Qed.

Lemma andp_assoc' : forall P Q R, (Q ∧ (P ∧ R)) = (P ∧ (Q ∧ R)).
Proof. intros. rewrite and_comm -and_assoc (and_comm R) //. Qed.

Lemma or_comm : forall P Q, (P ∨ Q) = (Q ∨ P).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext; tauto.
Qed.

Lemma or_assoc : forall P Q R, (P ∨ (Q ∨ R)) = ((P ∨ Q) ∨ R).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  unfold ouPred_or_def, ouPred_holds; simpl; intuition auto.
Qed.

Lemma and_False : forall P, (P ∧ False) = False.
Proof.
  intros; rewrite and_comm; apply False_and.
Qed.

Lemma False_or : forall P, (P ∨ False) = P.
Proof.
  intros; destruct P; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  unfold ouPred_pure_def, oupred.ouPred_holds; intuition auto.
Qed.

Lemma or_False : forall P, (False ∨ P) = P.
Proof.
  intros; rewrite or_comm; apply False_or.
Qed.

Lemma False_sep : forall P, (P ∗ False) = False.
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ? & ? & []).
  - intros [].
Qed.

Lemma sep_False : forall P, (False ∗ P) = False.
Proof.
  intros; rewrite sep_comm False_sep //.
Qed.

Lemma sep_exist_l : forall A P (Q : A -> ouPred M), (P ∗ (∃ a, Q a)) = (∃ a, P ∗ Q a).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ? & ? & ? & ?).
    eexists _, _, _; eauto.
  - intros (? & ? & ? & ? & ? & ?).
    eexists _, _; split; eauto; split; auto; eexists; eauto.
Qed.

Lemma sep_exist_r : forall A P (Q : A -> ouPred M), ((∃ a, Q a) ∗ P) = (∃ a, Q a ∗ P).
Proof.
  intros; rewrite sep_comm sep_exist_l; f_equal; extensionality; rewrite sep_comm //.
Qed.

Lemma and_exist_l : forall A P (Q : A -> ouPred M), (P ∧ (∃ a, Q a)) = (∃ a, P ∧ Q a).
Proof.
  intros; ouPred.unseal; apply IProp_eq; extensionality n x; apply prop_ext.
  split.
  - intros (? & ? & ?).
    eexists; split; eauto.
  - intros (? & ? & ?).
    split; auto; eexists; eauto.
Qed.

Lemma and_exist_r : forall A P (Q : A -> ouPred M), ((∃ a, Q a) ∧ P) = (∃ a, Q a ∧ P).
Proof.
  intros; rewrite and_comm and_exist_l; f_equal; extensionality; rewrite and_comm //.
Qed.

End pred.

#[export] Hint Rewrite @False_sep @sep_False @True_and @and_True : norm.

Ltac immediate := (assumption || reflexivity).

#[export] Hint Rewrite @prop_true_andp using (solve [immediate]) : norm.

#[export] Hint Rewrite @pure_True using (solve [immediate]) : norm.

#[export] Hint Rewrite @andp_dup : norm.

#[export] Hint Rewrite @sep_emp @emp_sep @True_and @and_True
             @sep_exist_l @sep_exist_r
               @and_exist_l @and_exist_r
         @sepcon_andp_prop @sepcon_andp_prop'
     using (solve [auto with typeclass_instances])
        : norm.

Ltac pull_left A := repeat (rewrite <- (pull_right A) || rewrite <- (pull_right0 A)).

Ltac pull_right A := repeat (rewrite (pull_right A) || rewrite (pull_right0 A)).

Ltac normalize1 :=
         match goal with
            | |- _ => contradiction
            | |- bi_entails(PROP := monPredI _ _) _ _ => let rho := fresh "rho" in split => rho; monPred.unseal
(*            | |- context [((?P ∧ ?Q) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) by (auto with norm)
            | |- context [(?Q ∗ (?P ∧ ?R))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) by (auto with norm)
            | |- context [((?Q ∧ ?P) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) by (auto with norm)
            | |- context [(?Q ∗ (?R ∧ ?P))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) by (auto with norm)*)
            (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                preserves the name of the "y" variable *)
            | |- context [((∃ y, _) ∧ _)%I] =>
                autorewrite with norm; apply bi.exist_elim; intro y
            | |- context [(_ ∧ ∃ y , _)%I] =>
                autorewrite with norm; apply bi.exist_elim; intro y
            | |- context [((∃ y, _) ∗ _)%I] =>
               autorewrite with norm; apply bi.exist_elim; intro y
            | |- context [(_ ∗ ∃ y , _)%I] =>
                autorewrite with norm; apply bi.exist_elim; intro y

           | |-  bi_entails ?A   _ => match A with
                          | context [ ((⌜?P⌝ ∧ ?Q) ∧ ?R)%I ] => rewrite -(bi.and_assoc (⌜P⌝%I) Q R)
                          | context [ (?Q ∧ (⌜?P⌝ ∧ ?R))%I ] =>
                                         match Q with ⌜_⌝%I => fail 2 | _ => rewrite (andp_assoc' (⌜P⌝%I) Q R) end
                         end
            | |- _ => progress  (autorewrite with norm); auto with typeclass_instances
            | |- _ = ?x -> _ => intro; subst x
            | |- ?x = _ -> _ => intro; subst x
            |  |- ?ZZ -> _ => match type of ZZ with
                                               | Prop =>
                                                    let H := fresh in
                                                       ((assert (H:ZZ) by auto; clear H; intros _) || intro H)
                                               | _ => intros _
                                              end
            | |- forall _, _ => let x := fresh "x" in (intro x; normalize1; try generalize dependent x)
            | |- bi_exist _ ⊢ _ => apply bi.exist_elim
            | |- ⌜_⌝ ⊢ _ => apply bi.pure_elim'
            | |- ⌜_⌝ ∧ _ ⊢ _ => apply bi.pure_elim_l
            | |- _ ∧ ⌜_⌝ ⊢ _ => apply bi.pure_elim_r
            | |- _ ⊢ ⌜?x = ?y⌝ ∧ _ =>
                            (rewrite -> prop_true_andp with (P:= (x=y))
                                            by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (rewrite -> prop_true_andp with (P:=(x=y))
                                            by (unfold x; reflexivity); unfold x in *; clear x)
            | |- True ⊢ ⌜_⌝ => apply bi.pure_intro
            | |- _ => solve [auto with typeclass_instances]
            end.

Ltac normalize1_in Hx :=
             match type of Hx with
(*                 | context [@andp ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                         change (@andp A (@LiftNatDed T B C) D E F) with (D F ∧ E F)
                 | context [@later ?A  (@LiftNatDed ?T ?B ?C) (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5) ?D ?F] =>
                    change (@later A  (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5) D F)
                     with (@later B C X5 (D F))
                 | context [@sepcon ?A (@LiftNatDed ?B ?C ?D)
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))*)
                | bi_entails(PROP := monPredI _ _) _ _ => let Hx' := fresh "Hx" in inversion Hx as [Hx']; revert Hx'; monPred.unseal; intros Hx'
                | context [ ⌜?P⌝%I ] =>
                                    rewrite -> (bi.pure_True P) in Hx by auto with typeclass_instances
                | context [ (⌜?P⌝ ∧ ?Q)%I ] =>
                                    rewrite -> (prop_true_andp P Q) in Hx by auto with typeclass_instances
                | context [((?P ∧ ?Q) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) in Hx by (auto with norm)
                | context [(?Q ∗ (?P ∧ ?R))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) in Hx by (auto with norm)
                | context [((?Q ∧ ?P) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) in Hx by (auto with norm)
                | context [(?Q ∗ (?R ∧ ?P))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) in Hx by (auto with norm)
                | _ => progress  (autorewrite with norm in Hx); auto with typeclass_instances
                end.

Ltac normalize := repeat (auto with norm; normalize1).

Tactic Notation "normalize" "in" hyp(H) := repeat (normalize1_in H).
