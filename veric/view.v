(* modified from iris.algebra.view *)
(* this could potentially go in ORA *)

From iris.algebra Require Export updates local_updates agree view.
From iris.algebra Require Import proofmode_classes big_op.
From iris_ora.algebra Require Export ora agree dfrac.
From iris.prelude Require Import options.

Section ora.

  Context {A} {B : uora} (rel : view_rel A B).

  Lemma view_validN_both : forall n (a : view rel), ✓{n} a -> ✓{n} view_auth_proj a ∧ ✓{n} view_frag_proj a.
  Proof.
    rewrite view.view_validN_eq; intros.
    destruct (view_auth_proj a) as [(?, ?)|].
    - destruct H as (? & ? & -> & ?%view_rel_validN); done.
    - destruct H as (? & ?%view_rel_validN); done.
  Qed.

  Instance view_order : OraOrder (view rel) := λ x y, view_auth_proj x ≼ₒ view_auth_proj y ∧ view_frag_proj x ≼ₒ view_frag_proj y.
  Instance view_orderN : OraOrderN (view rel) := λ n x y, view_auth_proj x ≼ₒ{n} view_auth_proj y ∧ view_frag_proj x ≼ₒ{n} view_frag_proj y.

  (* having trouble phrasing an order that guarantees this, so adding it as a proof obligation instead *)
  Context (view_rel_order : ∀n a x y, x ≼ₒ{n} y → rel n a y → rel n a x).

  Lemma view_increasing : forall (a : view rel), Increasing a <-> Increasing (view_auth_proj a) /\ Increasing (view_frag_proj a).
  Proof.
    split.
    - split; intros y.
      + specialize (H (View y ε)); apply H.
      + specialize (H (View ε y)); apply H.
    - intros [Ha Hf] ?; split; [apply Ha | apply Hf].
  Qed.

  Definition view_ora_mixin : OraMixin (view rel).
  Proof using view_rel_order.
    apply ora_total_mixin; try done.
    - intros ??; split; try eapply @ora_core_increasing; apply _.
    - intros ???? [??].
      apply view_increasing in H as [??].
      split; eapply @ora_increasing_closed; eauto.
    - intros ? [??] [??] [??]; split; apply @ora_core_monoN; try done; apply _.
    - intros ???? [Hva Hvf]%view_validN_both [Ha Hf].
      eapply @ora_op_extend in Ha as (a1 & a2 & ? & ? & ?); last done.
      eapply (ora_op_extend(A := B)) in Hf as (f1 & f2 & ? & ? & ?); last done.
      exists (View a1 f1), (View a2 f2); destruct y1, y2; done.
    - intros ??? [Hva Hvf]%view_validN_both [Ha Hf].
      eapply ora_extend in Ha as (a & ? & ?); last done.
      eapply (ora_extend(A := B)) in Hf as (f & ? & ?); last done.
      exists (View a f); destruct y; done.
    - intros ??? [??]; split; apply ora_dist_orderN; auto.
    - intros ??? [??]; split; apply ora_orderN_S; auto.
    - intros ???? [??] [??]; split; etrans; eauto.
    - intros ???? [??]; split; apply @ora_orderN_op; auto.
    - intros ???? [Ha Hf].
      destruct (view_validN_both _ _ H) as [Hva Hvf].
      rewrite view.view_validN_eq in H |- *.
      destruct (view_auth_proj y) as [(?, ?)|].
      + destruct (view_auth_proj x) as [(?, ?)|]; try done.
        destruct H as (? & ? & ? & ?), Ha as [? Ha], Hva as [? Hva]; simpl in *.
        split; [eapply @ora_validN_orderN; eauto|].
        apply agree_order_dist in Ha; last done.
        setoid_rewrite Ha.
        eexists; split; first done; eauto.
      + destruct (view_auth_proj x) as [(?, ?)|].
        * destruct H as (? & ? & ? & ?); eauto.
        * destruct H; eauto.
    - split.
      + intros [??] ?; split; by apply ora_order_orderN.
      + intros; split; apply ora_order_orderN; intros; apply H.
    - rewrite view.view_pcore_eq; inversion 1 as [?? [Ha Hf]|]; subst.
      eexists; split; first done.
      split; simpl in *; [rewrite -Ha; apply @uora_core_order_op | ].
      eapply ora_order_proper; [symmetry; apply Hf | done |].
      apply uora_core_order_op.
  Qed.

  Local Canonical Structure viewR := Ora (view rel) view_ora_mixin.

  Global Instance view_auth_oracore_id a : OraCoreId (●V□ a).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_frag_oracore_id (b : B) : OraCoreId b → OraCoreId (◯V b).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_both_oracore_id a (b : B) : OraCoreId b → OraCoreId (●V□ a ⋅ ◯V b).
  Proof. do 2 constructor; simpl; auto. rewrite !left_id. apply: core_id_core. Qed.

  Global Instance view_ora_discrete :
    OfeDiscrete A → OraDiscrete B → ViewRelDiscrete rel →
    OraDiscrete viewR.
  Proof.
    intros; assert (CmraDiscrete viewR).
    { apply view_cmra_discrete; try apply _.
      apply @ora_cmra_discrete, _. }
    split; [apply _|..]; [move=> -[[[dq ag]|] b]; rewrite ?view_valid_eq ?view_validN_eq /=|].
    - rewrite -cmra_discrete_valid_iff //.
    - intros (? & ?); econstructor; eauto.
    - by intros ?? [??]; split; apply ora_discrete_order.
  Qed.

End ora.

Notation viewUR rel := (Uora (view rel) (view_ucmra_mixin rel)).


(** * Utilities to construct functors *)
(** Due to the dependent type [rel] in [view] we cannot actually define
instances of the functor structures [rFunctor] and [urFunctor]. Functors can
only be defined for instances of [view], like [auth]. To make it more convenient
to define functors for instances of [view], we define the map operation
[view_map] and a bunch of lemmas about it. *)
Definition view_map {A A' B B'}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') (x : view rel) : view rel' :=
  View (prod_map id (agree_map f) <$> view_auth_proj x) (g (view_frag_proj x)).
Lemma view_map_id {A B} {rel : nat → A → B → Prop} (x : view rel) :
  view_map id id x = x.
Proof. destruct x as [[[]|] ]; by rewrite // /view_map /= agree_map_id. Qed.
Lemma view_map_compose {A A' A'' B B' B''}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    {rel'' : nat → A'' → B'' → Prop}
    (f1 : A → A') (f2 : A' → A'') (g1 : B → B') (g2 : B' → B'') (x : view rel) :
  view_map (f2 ∘ f1) (g2 ∘ g1) x
  =@{view rel''} view_map f2 g2 (view_map (rel':=rel') f1 g1 x).
Proof. destruct x as [[[]|] ];  by rewrite // /view_map /= agree_map_compose. Qed.
Lemma view_map_ext  {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f1 f2 : A → A') (g1 g2 : B → B')
    `{!NonExpansive f1, !NonExpansive g1} (x : view rel) :
  (∀ a, f1 a ≡ f2 a) → (∀ b, g1 b ≡ g2 b) →
  view_map f1 g1 x ≡@{view rel'} view_map f2 g2 x.
Proof.
  intros. constructor; simpl; [|by auto].
  apply option_fmap_equiv_ext=> a; by rewrite /prod_map /= agree_map_ext.
Qed.
Global Instance view_map_ne {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') `{Hf : !NonExpansive f, Hg : !NonExpansive g} :
  NonExpansive (view_map (rel':=rel') (rel:=rel) f g).
Proof.
  intros n [o1 bf1] [o2 bf2] [??]; split; simpl in *; [|by apply Hg].
  apply option_fmap_ne; [|done]=> pag1 pag2 ?.
  apply prod_map_ne; [done| |done]. by apply agree_map_ne.
Qed.

Definition viewO_map {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A -n> A') (g : B -n> B') : viewO rel -n> viewO rel' :=
  OfeMor (view_map f g).
Lemma viewO_map_ne {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop} :
  NonExpansive2 (viewO_map (rel:=rel) (rel':=rel')).
Proof.
  intros n f f' Hf g g' Hg [[[p ag]|] bf]; split=> //=.
  do 2 f_equiv. by apply agreeO_map_ne.
Qed.

Lemma view_map_cmra_morphism {A A' B B'}
    {rel : view_rel A B} {rel' : view_rel A' B'}
    (f : A → A') (g : B → B') `{!NonExpansive f, !CmraMorphism g} :
  (∀ n a b, rel n a b → rel' n (f a) (g b)) →
  CmraMorphism (view_map (rel:=rel) (rel':=rel') f g).
Proof.
  intros Hrel. split.
  - apply _.
  - rewrite !view.view_validN_eq=> n [[[p ag]|] bf] /=;
      [|naive_solver eauto using cmra_morphism_validN].
    intros [? [a' [Hag ?]]]. split; [done|]. exists (f a'). split; [|by auto].
    by rewrite -agree_map_to_agree -Hag.
  - intros [o bf]. apply Some_proper; rewrite /view_map /=.
    f_equiv; by rewrite cmra_morphism_core.
  - intros [[[dq1 ag1]|] bf1] [[[dq2 ag2]|] bf2];
      try apply View_proper=> //=; by rewrite cmra_morphism_op.
Qed.

Lemma view_map_ora_morphism {A A'} {B B' : uora}
    {rel : view_rel A B} {rel' : view_rel A' B'}
    (Hrel : ∀n a x y, x ≼ₒ{n} y → rel n a y → rel n a x) (Hrel' : ∀n a x y, x ≼ₒ{n} y → rel' n a y → rel' n a x)
    (f : A → A') (g : B → B') `{!NonExpansive f, !OraMorphism g} :
  (∀ n a b, rel n a b → rel' n (f a) (g b)) →
  OraMorphism(A := viewR rel Hrel)(B := viewR rel' Hrel') (view_map (rel:=rel) (rel':=rel') f g).
Proof.
  intros Hfrel.
  split; first apply (view_map_cmra_morphism f g Hfrel).
  - intros ??? [??]; split; simpl; apply ora_morphism_orderN; try done.
    apply _.
  - intros ??.
    apply view_increasing in H as [??]; apply view_increasing; split; simpl; apply ora_morphism_increasing; try done.
    apply _.
Qed.
