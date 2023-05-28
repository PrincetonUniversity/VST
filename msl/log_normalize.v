Require Import VST.msl.simple_CCC.
Require Import VST.msl.Extensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import VST.zlist.sublist.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import iris.proofmode.proofmode.

Create HintDb norm discriminated.

#[export] Hint Extern 0 (_ ⊢ _) => match goal with |- ?A ⊢ ?B => constr_eq A B; simple apply PreOrder_Reflexive end : core.

Ltac solve_andp' :=
  first [ apply PreOrder_Reflexive
        | apply bi.and_elim_l; solve_andp'
        | apply bi.and_elim_r; solve_andp'].

Ltac solve_andp := repeat apply bi.and_intro; solve_andp'.

Lemma TT_right: forall {PROP : bi} (P : PROP), P ⊢ True.
Proof. intros. apply bi.pure_intro, I. Qed.

Lemma False_left: forall {PROP : bi} (P : PROP), False ⊢ P.
Proof. intros. apply bi.pure_elim'; intuition. Qed.

#[export] Hint Resolve TT_right: norm.
#[export] Hint Resolve False_left : norm.
#[export] Hint Rewrite @bi.False_sep @bi.sep_False @bi.True_and @bi.and_True : norm.

Ltac norm := auto with norm.

Section bi.

Context {PROP : bi}.
Implicit Types (P Q : bi_car PROP).

Lemma add_andp: forall P Q, (P ⊢ Q) -> P ⊣⊢ P ∧ Q.
Proof.
  intros.
  apply bi.equiv_entails; split.
  + apply bi.and_intro; auto.
  + apply bi.and_elim_l; apply PreOrder_Reflexive.
Qed.

Lemma exp_comm : forall {B C} (P: B -> C -> PROP),
  (∃ x : B, ∃ y : C, P x y) ⊣⊢ ∃ y : C, ∃ x : B, P x y.
Proof.
  intros; apply bi.equiv_entails; split; apply bi.exist_elim; intros x; apply bi.exist_elim; intros y;
    rewrite -(bi.exist_intro y); rewrite -(bi.exist_intro x); auto.
Qed.

Class CCCviaNatDed (prod expo: PROP -> PROP -> PROP): Prop :=
  isCCC: CartesianClosedCat.CCC PROP bi_entails equiv prod expo.

Lemma CCC_expo_derives: forall prod expo {CCC: CCCviaNatDed prod expo},
  forall P P' Q Q', (P' ⊢ P) -> (Q ⊢ Q') -> expo P Q ⊢ expo P' Q'.
Proof.
  intros.
  eapply CartesianClosedCat.expo_UMP; eauto.
  apply PreOrder_Transitive.
Qed.

Lemma CCC_exp_prod1:
  forall prod expo {CCC: CCCviaNatDed prod expo} B (P: B -> PROP) Q,
  prod (∃ x, P x) Q ⊣⊢ ∃ x, prod (P x) Q.
Proof.
  intros.
  pose proof isCCC.
  apply bi.equiv_entails; split.
  + apply (proj2 (CartesianClosedCat.adjoint _ _ _ _ _ _)).
    apply bi.exist_elim; intro x.
    apply (proj1 (CartesianClosedCat.adjoint _ _ _ _ _ _)).
    rewrite -(bi.exist_intro x).
    apply PreOrder_Reflexive.
  + apply bi.exist_elim; intro x.
    eapply CartesianClosedCat.prod_UMP; eauto.
Qed.

Lemma CCC_exp_prod2:
  forall prod expo {CCC: CCCviaNatDed prod expo} B P (Q: B -> PROP),
  prod P (∃ x, Q x) ⊣⊢ ∃ x, prod P (Q x).
Proof.
  intros.
  rewrite -> CartesianClosedCat.comm by eauto.
  erewrite CCC_exp_prod1 by eauto.
  f_equiv; intros x.
  rewrite -> CartesianClosedCat.comm by eauto.
  reflexivity.
Qed.

Lemma CCC_distrib_orp_prod:
  forall prod expo {CCC: CCCviaNatDed prod expo} P Q R,
    prod (P ∨ Q) R ⊣⊢ (prod P R) ∨ (prod Q R).
Proof.
  intros.
  pose proof isCCC.
  apply bi.equiv_entails; split.
  + apply (proj2 (CartesianClosedCat.adjoint _ _ _ _ _ _)).
    apply bi.or_elim.
    - apply (proj1 (CartesianClosedCat.adjoint _ _ _ _ _ _)).
      apply bi.or_intro_l.
    - apply (proj1 (CartesianClosedCat.adjoint _ _ _ _ _ _)).
      apply bi.or_intro_r.
  + apply bi.or_elim; eapply CartesianClosedCat.prod_UMP; eauto.
Qed.

Lemma CCC_False_prod:
  forall prod expo {CCC: CCCviaNatDed prod expo} P,
    prod False P ⊣⊢ False.
Proof.
  intros.
  pose proof isCCC.
  apply bi.equiv_entails; split.
  + apply (proj2 (CartesianClosedCat.adjoint _ _ _ _ _ _)).
    apply False_left.
  + apply False_left.
Qed.

Lemma CCC_prod_False:
  forall prod expo {CCC: CCCviaNatDed prod expo} P,
    prod P False ⊣⊢ False.
Proof.
  intros.
  pose proof isCCC.
  rewrite -> CartesianClosedCat.comm by eauto.
  eapply CCC_False_prod; eauto.
Qed.

#[global] Instance and_impl_CCC: CCCviaNatDed bi_and bi_impl.
Proof.
  constructor.
  - apply bi.and_comm.
  - intros; symmetry; apply bi.and_assoc.
  - intros; split.
    + apply bi.impl_intro_r.
    + apply bi.impl_elim_l'.
  - intros; apply bi.and_mono; auto.
Qed.

#[global] Instance sep_wand_CCC: CCCviaNatDed bi_sep bi_wand.
Proof.
  constructor.
  - apply bi.sep_comm.
  - intros; symmetry; apply bi.sep_assoc.
  - intros; split.
    + apply bi.wand_intro_r.
    + apply bi.wand_elim_l'.
  - intros; apply bi.sep_mono; auto.
Qed.

Lemma exp_unit: forall (P: unit -> PROP),
  (∃ x, P x) ⊣⊢ P tt.
Proof.
  intros.
  apply bi.equiv_entails; split.
  + apply bi.exist_elim; intro x.
    destruct x.
    auto.
  + apply (bi.exist_intro tt); auto.
Qed.

Lemma allp_unit: forall (P: unit -> PROP),
  (∀ x, P x) ⊣⊢ P tt.
Proof.
  intros.
  apply bi.equiv_entails; split.
  + apply (bi.forall_elim tt); auto.
  + apply bi.forall_intro; intro x.
    destruct x.
    auto.
Qed.

Definition modus_ponens := @bi.impl_elim_r.

Definition modus_ponens_wand := @bi.wand_elim_r.

Lemma wand_sepcon_wand: forall (P1 P2 Q1 Q2 : PROP),
  (P1 -∗ Q1) ∗ (P2 -∗ Q2) ⊢ P1 ∗ P2 -∗ Q1 ∗ Q2.
Proof.
  intros.
  apply bi.wand_intro_r.
  iIntros "((H1 & H2) & P1 & P2)"; iSplitL "H1 P1"; [iApply "H1" | iApply "H2"]; done.
Qed.

Lemma allp_forall: forall {B: Type} (P : B -> PROP) Q (x:B), (forall x:B, (P x ⊣⊢ Q)) -> ((∀ x, P x) ⊣⊢ Q).
Proof.
  intros.
  apply bi.equiv_entails; split.
  + rewrite (bi.forall_elim x) H //.
  + apply bi.forall_intro.
    intros.
    rewrite H //.
Qed.

Lemma allp_uncurry: forall (S T: Type) (P: S -> T -> PROP),
  (∀ x y, P x y) ⊣⊢ ∀ st, P (fst st) (snd st).
Proof.
  intros.
  apply bi.equiv_entails; split.
  + apply bi.forall_intro; intros [s t]; eauto.
  + iIntros "H" (x y); iApply ("H" $! (x, y)).
Qed.

Lemma allp_depended_uncurry': forall {S: Type} {T: S -> Type} (P: forall s: S, T s -> PROP),
  (∀ s: S, (∀ t: T s, P s t)) ⊣⊢ ∀ st: sigT T, P (projT1 st) (projT2 st).
Proof.
  intros.
  apply bi.equiv_entails; split.
  + iIntros "H" ((? & ?)); eauto.
  + iIntros "H" (s t); iApply ("H" $! (existT s t)).
Qed.

Lemma allp_curry: forall (S T: Type) (P: S * T -> PROP),
  (∀ x, P x) ⊣⊢ ∀ s t, P (s, t).
Proof.
  intros.
  apply bi.equiv_entails; split.
  + iIntros "H" (s t); iApply ("H" $! (s, t)).
  + iIntros "H" ((?, ?)); eauto.
Qed.

Lemma exp_uncurry: forall A B (F : A -> B -> PROP),
  (∃ a : A, ∃ b : B, F a b) ⊣⊢ ∃ ab : A * B, F (fst ab) (snd ab).
Proof.
  intros.
  apply bi.equiv_entails; split.
  - iIntros "(% & % & H)"; iExists (_, _); done.
  - iIntros "(%ab & H)"; destruct ab; eauto.
Qed.

Lemma exp_trivial :
  forall {T: Type} (any: T) P, (∃ x:T, P) ⊣⊢ P.
Proof.
  intros. apply bi.equiv_entails; split.
  - apply bi.exist_elim; auto.
  - rewrite -(bi.exist_intro any) //.
Qed.

Lemma allp_andp: forall {B: Type} (P Q: B -> PROP), (∀ x, P x ∧ Q x) ⊣⊢ (∀ x, P x) ∧ (∀ x, Q x).
Proof.
  intros.
  apply bi.equiv_entails; split.
  + iIntros "H"; iSplit; iIntros (x); iSpecialize ("H" $! x); [rewrite bi.and_elim_l | rewrite bi.and_elim_r]; done.
  + iIntros "H" (x); iSplit; [rewrite bi.and_elim_l | rewrite bi.and_elim_r]; eauto.
Qed.

Lemma imp_right2: forall P Q, P ⊢ Q → P.
Proof.
  intros.
  apply bi.impl_intro_r, bi.and_elim_l.
Qed.

Lemma later_left2: forall A B C : PROP, (A ∧ B ⊢ C) -> A ∧ ▷ B ⊢ ▷C.
Proof.
  intros.
  rewrite -H bi.later_and; apply bi.and_mono; try done.
  apply bi.later_intro.
Qed.

Lemma andp_dup: forall P, P ∧ P ⊣⊢ P.
Proof. intros; iSplit; [iIntros "[$ _]" | iIntros "$"]. Qed.

Lemma persistent_and_sep_assoc' :
    forall P Q R {HP : Persistent Q} {HA : Absorbing Q}, P ∗ (Q ∧ R) ⊣⊢ Q ∧ (P ∗ R).
Proof.
  intros; rewrite comm -bi.persistent_and_sep_assoc bi.sep_comm //.
Qed.

Lemma sepcon_andp_prop :
     forall P (Q:Prop) R, P ∗ (⌜Q⌝ ∧ R) ⊣⊢ ⌜Q⌝ ∧ (P ∗ R).
Proof with norm.
  intros; iSplit.
  - iIntros "($ & $ & $)".
  - iIntros "($ & $ & $)".
Qed.

Lemma sepcon_andp_prop' :
     forall P (Q:Prop) R, (⌜Q⌝ ∧ P) ∗ R ⊣⊢ ⌜Q⌝ ∧ (P ∗ R).
Proof with norm.
  intros; iSplit.
  - iIntros "(($ & $) & $)".
  - iIntros "($ & $ & $)".
Qed.

Lemma wand_eq :
   forall P Q R, (P ⊣⊢ Q ∗ R) -> P ⊣⊢ Q ∗ (Q -∗ P).
Proof.
  intros.
  apply bi.equiv_entails; split; last apply modus_ponens_wand.
  rewrite H; iIntros "($ & $)".
  auto.
Qed.

Lemma prop_true_andp:
  forall (P: Prop) Q,  P -> (⌜P⌝ ∧ Q ⊣⊢ Q).
Proof with norm.
  intros.
  rewrite bi.pure_True // bi.True_and //.
Qed.

Lemma forall_pred_ext: forall B (P Q: B -> PROP),
 (∀ x : B, (P x ↔ Q x)) ⊢ (∀ x : B, P x) ↔ (∀ x: B, Q x).
Proof.
  intros; apply bi.and_intro; apply bi.impl_intro_r, bi.forall_intro; intros x; rewrite !(bi.forall_elim x);
    rewrite /bi_iff; [rewrite (bi.and_elim_l (_ → _)) | rewrite (bi.and_elim_r (_ → _))]; apply bi.impl_elim_l.
Qed.

Lemma exists_pred_ext : forall B (P Q: B -> PROP),
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

Lemma pull_right: forall P Q R, ((Q ∗ P) ∗ R) ⊣⊢ ((Q ∗ R) ∗ P).
Proof.
  intros; rewrite -!assoc (comm _ P) //.
Qed.

Lemma pull_right0: forall P Q, (P ∗ Q) ⊣⊢ (Q ∗ P).
Proof.
  exact bi.sep_comm.
Qed.

Lemma prop_imp: forall (P: Prop) Q, P -> (⌜P⌝ → Q) ⊣⊢ Q.
Proof.
  intros.
  rewrite bi.pure_True // bi.True_impl //.
Qed.

Lemma not_prop_right `{BiPureForall PROP}: forall P (Q: Prop), (Q -> P ⊢ False) -> P ⊢ ⌜not Q⌝.
Proof.
  intros.
  rewrite -bi.pure_impl_2; apply bi.impl_intro_l, bi.pure_elim_l; done.
Qed.

Lemma later_prop_andp_sepcon: forall (P: Prop) (Q R : PROP),
((▷ ⌜P⌝ ∧ Q) ∗ R) ⊣⊢ (▷ ⌜P⌝) ∧ (Q ∗ R).
Proof.
  intros.
  rewrite bi.persistent_and_sep_assoc //.
Qed.

Lemma prop_false_andp:
 forall (P : Prop) Q, ~P -> ⌜P⌝ ∧ Q ⊣⊢ False.
Proof.
  intros; rewrite bi.pure_False // bi.False_and //.
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

Lemma guarded_sepcon_orp_distr: forall (P1 P2: Prop) (p1 p2 q1 q2 : PROP),
  (P1 -> P2 -> False) ->
  (⌜P1⌝ ∧ p1 ∨ ⌜P2⌝ ∧ p2) ∗ (⌜P1⌝ ∧ q1 ∨ ⌜P2⌝ ∧ q2) ⊣⊢ ⌜P1⌝ ∧ (p1 ∗ q1) ∨ ⌜P2⌝ ∧ (p2 ∗ q2).
Proof.
  intros.
  iSplit.
  - iIntros "([(% & H1) | (% & H1)] & [(% & H2) | (% & H2)])"; try solve [exfalso; auto];
      [iLeft | iRight]; iFrame; done.
  - iIntros "[(% & H1 & H2) | (% & H1 & H2)]"; iSplitL "H1"; auto.
Qed.

Definition mark (i: nat) (j: PROP) := j.

Lemma swap_mark1:
  forall i j Pi Pj B, (i<j)%nat -> (B ∗ mark i Pi) ∗ mark j Pj ⊣⊢ (B ∗ mark j Pj) ∗ mark i Pi.
Proof.
  intros; apply pull_right.
Qed.

Lemma swap_mark0:
  forall i j Pi Pj, (i<j)%nat -> mark i Pi ∗ mark j Pj ⊣⊢ mark j Pj ∗ mark i Pi.
Proof.
  intros; apply bi.sep_comm.
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
  (rewrite !bi.sep_assoc;
   match goal with |- ?P ⊣⊢ _ => markem O P end;
   let LEFT := fresh "LEFT" in match goal with |- ?P ⊣⊢ _ => set (LEFT := P) end;
  match goal with H: mark ?n _ = _ |- _ =>
     repeat  match goal with H: mark ?n _ = ?P |- _ => rewrite <- H; clear H end;
     select_all n;
     reflexivity
   end).

Lemma test_prove_assoc_commut : forall A B C D E : PROP,
   D ∗ E ∗ A ∗ C ∗ B ⊣⊢ A ∗ B ∗ C ∗ D ∗ E.
Proof.
  intros.
  prove_assoc_commut.
Qed.

Implicit Types (l : list PROP).

(* use [∗ list] instead of this whenever possible *)
Lemma sepcon_app:
   forall l1 l2, fold_right bi_sep emp (l1 ++ l2) ⊣⊢
  fold_right bi_sep emp l1 ∗ fold_right bi_sep emp l2.
Proof.
  induction l1; simpl; intros.
  - rewrite bi.emp_sep //.
  - rewrite IHl1 assoc //.
Qed.

Lemma sepcon_rev:
  forall l, fold_right bi_sep emp (rev l) ⊣⊢ fold_right bi_sep emp l.
Proof.
  induction l; simpl; auto.
  rewrite sepcon_app; simpl.
  rewrite bi.sep_emp IHl comm //.
Qed.

Global Instance bi_inhabitant : Inhabitant PROP := bi_emp.

Lemma extract_nth_sepcon : forall l i,
    (0 <= i < Zlength l)%Z ->
    fold_right bi_sep emp l ⊣⊢ Znth i l ∗ fold_right bi_sep emp (upd_Znth i l emp).
Proof.
  intros.
  erewrite <- sublist_same with (al := l) at 1; auto.
  rewrite -> sublist_split with (mid := i); try lia.
  rewrite (sublist_next i); try lia.
  rewrite sepcon_app; simpl.
  rewrite assoc (bi.sep_comm _ (Znth i l)).
  unfold_upd_Znth_old; rewrite sepcon_app -assoc; simpl.
  rewrite bi.emp_sep //.
Qed.

Lemma replace_nth_sepcon : forall P l i,
    (0 <= i < Zlength l)%Z ->
    P ∗ fold_right bi_sep emp (upd_Znth i l emp) ⊣⊢
    fold_right bi_sep emp (upd_Znth i l P).
Proof.
  intros; unfold_upd_Znth_old.
  rewrite !sepcon_app; simpl.
  rewrite bi.emp_sep !assoc (bi.sep_comm P) //.
Qed.

Lemma sepcon_derives_prop : forall P Q R, (P ⊢ ⌜R⌝) -> P ∗ Q ⊢ ⌜R⌝.
Proof.
  intros ??? ->; by iIntros "($ & _)".
Qed.

Lemma sepcon_map : forall {B} (P Q: B -> PROP) (l: list B),
    fold_right bi_sep emp (map (fun x => P x ∗ Q x) l) ⊣⊢
      fold_right bi_sep emp (map P l) ∗ fold_right bi_sep emp (map Q l).
Proof.
  induction l; simpl.
  - rewrite bi.sep_emp //.
  - rewrite -!assoc (bi.sep_assoc (fold_right _ _ _) (Q a)) (bi.sep_comm (fold_right _ _ _) (Q _)).
    rewrite IHl -bi.sep_assoc //.
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

Lemma sepcon_rotate : forall (lP: list PROP) m n,
    (0 <= n - m < Zlength lP)%Z ->
    fold_right bi_sep emp lP ⊣⊢ fold_right bi_sep emp (sublist.rotate lP m n).
Proof.
  intros.
  unfold sublist.rotate.
  rewrite sepcon_app bi.sep_comm -sepcon_app sublist_rejoin; [| lia..].
  rewrite -> sublist_same by lia; auto.
Qed.

Lemma sepcon_In : forall  l P,
    In P l -> exists Q, fold_right bi_sep emp l ⊣⊢ P ∗ Q.
Proof.
  induction l; [contradiction|].
  intros ? [|]; simpl; subst; eauto.
  destruct (IHl _ H) as [Q IH]; eexists; rewrite IH.
  rewrite bi.sep_comm -bi.sep_assoc; eauto.
Qed.

Lemma extract_wand_sepcon : forall l P, In P l ->
  fold_right bi_sep emp l ⊣⊢ P ∗ (P -∗ fold_right bi_sep emp l).
Proof.
  intros.
  destruct (sepcon_In _ _ H).
  eapply wand_eq; eauto.
Qed.

Global Instance fold_right_sep_proper : Proper (equiv ==> equiv) (fold_right bi_sep (bi_emp : PROP)).
Proof.
  intros l; induction l; simpl; intros ? H; inversion H as [| ???? H1 H2]; subst; clear H; auto.
  rewrite H1 IHl /= //.
Qed.

Lemma wand_sepcon_map : forall {B} (R : B -> PROP) (l : list B) (P Q : B -> PROP)
                          (HR : forall i, In i l -> R i ⊣⊢ P i ∗ Q i),
    fold_right bi_sep emp (map R l) ⊣⊢ fold_right bi_sep emp (map P l) ∗
    (fold_right bi_sep emp (map P l) -∗ fold_right bi_sep emp (map R l)).
Proof.
  intros; eapply wand_eq.
  rewrite fold_right_sep_proper; first apply sepcon_map.
  induction l; auto; simpl.
  rewrite HR; simpl; auto.
  f_equiv; first done.
  apply IHl.
  intros; apply HR; simpl; auto.
Qed.

Lemma andp_assoc': forall P Q R, Q ∧ (P ∧ R) ⊣⊢ P ∧ (Q ∧ R).
Proof. intros. rewrite comm -assoc (bi.and_comm R) //. Qed.

End bi.

Ltac immediate := (assumption || reflexivity).

#[export] Hint Rewrite @prop_true_andp using (solve [immediate]) : norm.

#[export] Hint Rewrite @bi.pure_True using (solve [immediate]) : norm.

#[export] Hint Rewrite @andp_dup : norm.

#[export] Hint Rewrite @bi.sep_emp @bi.emp_sep @bi.True_and @bi.and_True
             @bi.sep_exist_l @bi.sep_exist_r
               @bi.and_exist_l @bi.and_exist_r
         @sepcon_andp_prop @sepcon_andp_prop'
     using (solve [auto with typeclass_instances])
        : norm.

Ltac pull_left A := repeat (rewrite <- (pull_right A) || rewrite <- (pull_right0 A)).

Ltac pull_right A := repeat (rewrite (pull_right A) || rewrite (pull_right0 A)).

Check bi.persistent_and_sep_assoc.
Ltac normalize1 :=
         match goal with
            | |- _ => contradiction
(*            | |- context [bi_and ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                      change (@andp A (@LiftNatDed T B C) D E F) with (D F ∧ E F)
            | |- context [@later ?A  (@LiftNatDed ?T ?B ?C) (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5) ?D ?F] =>
                   change (@later A  (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5) D F)
                     with (@later B C X5 (D F))
            | |- context [@sepcon ?A (@LiftNatDed ?B ?C ?D)
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))*)
            | |- context [((?P ∧ ?Q) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) by (auto with norm)
            | |- context [(?Q ∗ (?P ∧ ?R))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) by (auto with norm)
            | |- context [((?Q ∧ ?P) ∗ ?R)%I] => rewrite <- (bi.persistent_and_sep_assoc P Q R) by (auto with norm)
            | |- context [(?Q ∗ (?R ∧ ?P))%I] => rewrite -> (persistent_and_sep_assoc' P Q R) by (auto with norm)
            (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                preserves the name of the "y" variable *)
            | |- context [(∃ y, _ ∧ _)%I] =>
                autorewrite with norm; apply bi.exist_elim; intro y
            | |- context [(_ ∧ ∃ y , _)%I] =>
                autorewrite with norm; apply bi.exist_elim; intro y
            | |- context [(∃ y, _ ∗ _)%I] =>
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
