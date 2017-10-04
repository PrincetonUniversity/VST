Load loadpath.
Require MSets.
Require Coq.Structures.Orders.
Require Coq.Structures.OrdersFacts.
Require Import Morphisms.
Require Import ProofIrrelevance.
Require Import List.
Require Import Relation_Definitions.
Require Import Sorting.
Require Recdef.
Require Omega.
Require Import VST.msl.Axioms VST.msl.Coqlib2.
Require Import NArith veristar.variables veristar.datatypes veristar.clauses.
Require Import veristar.fresh.
Require Import Finite_sets_facts.
Require Import VST.msl.base.


Definition list_bound {A: Type} (f: A -> Prop) (l: list A):=
  Forall f l /\  NoDup l.

Definition vset := Ensemble var.

Definition expr_bound (n: vset) (e: expr) :=
 match e with Nil => True | Var v => n v end.

Definition pure_bound (n: vset) (a : pure_atom) :=
 match a with
 | Eqv e e' => expr_bound n e /\ expr_bound n e'
 end.

Definition space_bound (n: vset) (a: space_atom) :=
 match a with
 | Next e e' =>  expr_bound n e /\ expr_bound n e'
 | Lseg e e' =>  expr_bound n e /\ expr_bound n e'
 end.

Definition pures_bound n := list_bound (pure_bound n).
Definition spaces_bound n := list_bound (space_bound n).

Definition pures_bound' n := Forall (pure_bound n).
Definition spaces_bound' n := Forall (space_bound n).

Definition clause_bound' (n: vset)  (cl: clause) :=
 match cl with
 | PureClause pi pi' _ _ =>  pures_bound' n pi /\ pures_bound' n pi'
 | PosSpaceClause pi pi' sigma =>
    pures_bound' n pi /\ pures_bound' n pi'/\ spaces_bound' n sigma
 | NegSpaceClause pi sigma pi' =>
    pures_bound' n pi /\ pures_bound' n pi'/\ spaces_bound' n sigma
 end.

Definition clause_bound (n: vset)  (cl: clause) :=
 match cl with
 | PureClause pi pi' _ _ =>  pures_bound n pi /\ pures_bound n pi'
 | PosSpaceClause pi pi' sigma =>
    pures_bound n pi /\ pures_bound n pi'/\ spaces_bound n sigma
 | NegSpaceClause pi sigma pi' =>
    pures_bound n pi /\ pures_bound n pi'/\ spaces_bound n sigma
 end.


Lemma expr_bound_more: forall  n n' e,
    Included _ n n' -> expr_bound n e -> expr_bound n' e.
Proof.
 unfold expr_bound; intros; auto.
 destruct e; auto. apply H; auto.
Qed.

Lemma pure_bound_more:
  forall n n' a, Included _ n n' -> pure_bound n a -> pure_bound n' a.
Proof.
 intros.
 unfold pure_bound in *.
 destruct a;  destruct H0; split; eapply expr_bound_more; eauto.
Qed.

Lemma pures_bound'_more:
  forall n n' gamma, Included _ n n' -> pures_bound' n gamma -> pures_bound' n' gamma.
Proof.
 unfold pures_bound'; intros.
 rewrite Forall_forall in *.
  intros.
 eapply pure_bound_more; eauto.
Qed.


Lemma space_bound_more:
  forall n n' a, Included _ n n' -> space_bound n a -> space_bound n' a.
Proof.
 intros.
 unfold space_bound in *.
 destruct a;  destruct H0; split; eapply expr_bound_more; eauto.
Qed.


Lemma spaces_bound'_more:
  forall n n' gamma, Included _ n n' -> spaces_bound' n gamma -> spaces_bound' n' gamma.
Proof.
 unfold spaces_bound'; intros.
 rewrite Forall_forall in *.
 intros.
 eapply space_bound_more; eauto.
Qed.

Lemma clause_bound'_more:
  forall n n' c, Included _ n n' -> clause_bound' n c -> clause_bound' n' c.
Proof.
 intros.
 destruct c; simpl in *.
  destruct H0; split; eapply pures_bound'_more; eauto.
  destruct H0 as [? [? ?]];
  split; [|split]; try  eapply pures_bound'_more; eauto;  eapply spaces_bound'_more; eauto.
  destruct H0 as [? [? ?]];
  split; [|split]; try  eapply pures_bound'_more; eauto;  eapply spaces_bound'_more; eauto.
Qed.

Definition var_upto (v: var): Ensemble var := fun x => Ile x v.

Lemma expr_bound_freshmax:
  forall e, expr_bound (var_upto (freshmax_expr e)) e.
 Proof.
 destruct e; intros; simpl; auto.
 right; reflexivity.
Qed.


Lemma S_nat_of_P_id2pos_le:
 forall x y, Ile x y -> S (nat_of_P (id2pos x)) <= S (nat_of_P (id2pos y)).
Proof.
 intros.
 generalize (nat_of_P_id2pos_le x y H); intro; omega.
Qed.

Lemma included_var_upto:
  forall a b, Ile a b -> Included _ (var_upto a) (var_upto b).
Proof. unfold var_upto; repeat intro; unfold In in *. eapply Ile_trans; eauto.
Qed.

Lemma pure_bound_freshmax:
 forall a, pure_bound (var_upto (freshmax_pure_atom a)) a.
 unfold pure_bound. destruct a.
 split.
 simpl.
 apply expr_bound_more with (var_upto (freshmax_expr e)).
 apply included_var_upto.  apply Ile_var_max1.
 apply expr_bound_freshmax.
 simpl.
 apply expr_bound_more with (var_upto (freshmax_expr e0)).
 apply included_var_upto.  apply Ile_var_max2.
  apply expr_bound_freshmax.
Qed.

Lemma pures_bound_freshmax:
  forall gamma,
  pures_bound' (var_upto (freshmax_list freshmax_pure_atom gamma)) gamma.
Proof.
 intros.
 unfold pures_bound'.
 induction gamma; simpl; intros.
 constructor.
 constructor; auto.
 eapply pure_bound_more; try apply pure_bound_freshmax.
 apply included_var_upto;  apply Ile_var_max1.
 rewrite Forall_forall in *; intros.
 specialize (IHgamma _ H).
 eapply pure_bound_more; try apply pure_bound_freshmax.
 apply included_var_upto;  eapply Ile_trans; [ | apply Ile_var_max2].
 revert H; clear; induction gamma; simpl; intros; auto.
 contradiction.
 destruct H; subst.
 apply Ile_var_max1.
 eapply Ile_trans; [ auto | apply Ile_var_max2].
Qed.

Lemma space_bound_freshmax:
 forall a, space_bound (var_upto (freshmax_space_atom a)) a.
 unfold space_bound. destruct a.
 split.
 simpl.
 apply expr_bound_more with (var_upto (freshmax_expr e)).
 apply included_var_upto; apply Ile_var_max1.
  apply expr_bound_freshmax.
 simpl.
 apply expr_bound_more with (var_upto (freshmax_expr e0)).
  apply included_var_upto; apply Ile_var_max2.
  apply expr_bound_freshmax.
 split.
 simpl.
 apply expr_bound_more with (var_upto (freshmax_expr e)).
  apply included_var_upto;  apply Ile_var_max1.
  apply expr_bound_freshmax.
 simpl.
 apply expr_bound_more with (var_upto (freshmax_expr e0)).
  apply included_var_upto;  apply Ile_var_max2.
  apply expr_bound_freshmax.
Qed.

Lemma spaces_bound'_freshmax:
  forall gamma,
  spaces_bound' (var_upto (freshmax_list freshmax_space_atom gamma)) gamma.
Proof.
 intros.
 unfold spaces_bound'.
 induction gamma; simpl; intros.
 constructor.
 constructor; auto.
 eapply space_bound_more; try apply space_bound_freshmax.
 apply included_var_upto;  apply Ile_var_max1.
 rewrite Forall_forall in *; intros.
 specialize (IHgamma _ H).
 eapply space_bound_more; try apply space_bound_freshmax.
 eapply included_var_upto; eapply Ile_trans; [ | apply Ile_var_max2].
 revert H; clear; induction gamma; simpl; intros; auto.
 contradiction.
 destruct H; subst.
 apply Ile_var_max1.
 eapply Ile_trans; [ | apply Ile_var_max2].
 auto.
Qed.

Lemma clause_bound'_freshmax:
  forall c, clause_bound' (var_upto (freshmax_clause c)) c.
Proof.
 intros.
 destruct c; simpl.
 split.
 apply pures_bound'_more with
   (var_upto (freshmax_list freshmax_pure_atom gamma)).
 apply included_var_upto.
 apply Ile_var_max1.
 apply pures_bound_freshmax.
 apply pures_bound'_more with
   (var_upto (freshmax_list freshmax_pure_atom delta)).
 apply included_var_upto.
 apply Ile_var_max2.
 apply pures_bound_freshmax.
 split; [|split].
 apply pures_bound'_more
   with (var_upto (freshmax_list freshmax_pure_atom gamma)).
 apply included_var_upto;  eapply Ile_trans; [ | apply Ile_var_max1].
 apply Ile_var_max1.
 apply pures_bound_freshmax.
 apply pures_bound'_more
   with (var_upto (freshmax_list freshmax_pure_atom delta)).
 apply included_var_upto;  eapply Ile_trans; [ | apply Ile_var_max1].
 apply Ile_var_max2.
 apply pures_bound_freshmax.
 apply spaces_bound'_more
   with (var_upto (freshmax_list freshmax_space_atom sigma)).
  apply included_var_upto;  apply Ile_var_max2.
 apply spaces_bound'_freshmax.
 split; [|split].
 apply pures_bound'_more
   with (var_upto (freshmax_list freshmax_pure_atom gamma)).
 apply included_var_upto;  eapply Ile_trans; [ | apply Ile_var_max1].
 apply Ile_var_max1.
 apply pures_bound_freshmax.
 apply pures_bound'_more
   with (var_upto (freshmax_list freshmax_pure_atom delta)).
 apply included_var_upto;  eapply Ile_trans; [ | apply Ile_var_max1].
 apply Ile_var_max2.
 apply pures_bound_freshmax.
 apply spaces_bound'_more
   with (var_upto (freshmax_list freshmax_space_atom sigma)).
  apply included_var_upto;  apply Ile_var_max2.
 apply spaces_bound'_freshmax.
Qed.

Module Type CLAUSE_UNIVERSE_FINITE.

 Axiom Finite_var_upto:  forall v, Finite _ (var_upto v).
 Axiom clause_bound_finite: forall n, Finite _ n -> Finite _ (clause_bound n).
End CLAUSE_UNIVERSE_FINITE.

Module ClauseUniverseFinite : CLAUSE_UNIVERSE_FINITE.

Require Import Image.

Implicit Arguments Finite.
Implicit Arguments Union.
Implicit Arguments Intersection.
Implicit Arguments Im.
Implicit Arguments In.
Implicit Arguments Add.
Implicit Arguments Subtract.
Implicit Arguments Singleton.
Implicit Arguments injective.
Implicit Arguments Included.
Implicit Arguments Power_set.

Ltac inv H := inversion H; clear H; subst.

Lemma finite_pair:
  forall U V (S : Ensemble U) (T: Ensemble V),
         Finite S -> Finite T ->
         Finite (fun xy => S (fst xy) /\ T (snd xy)).
Proof.
 intros.
 revert T H0; induction H; intros.
 replace (fun xy : U * V => Empty_set U (fst xy) /\ T (snd xy))
   with (Empty_set (U*V)).
 constructor.
 clear; extensionality x; apply prop_ext; split; intros H; inv H. inv H0.
 unfold Add.
  apply Finite_downward_closed
    with (Union (fun xy => A (fst xy) /\ T (snd xy))
                       (fun xy => Singleton x (fst xy) /\ T (snd xy))).
 apply Union_preserves_Finite.
 auto.
 apply Finite_downward_closed
    with (Im T (fun y => (x,y))).
 apply finite_image; auto.
 clear.
 intros [x' y] [? ?]. inv H. simpl in *. unfold In.
 econstructor; eauto.
 clear.
 intros [x' y] ?. unfold In in *.
 inv H; simpl in *.
 inv H0; [left | right]; unfold In in *; auto.
Qed.

Definition pures_bound2 n pi2 :=
      pures_bound n (fst pi2) /\ pures_bound n (snd pi2).


Lemma finite_unimage :
    forall {U V} (X:Ensemble U) (f:U -> V),
       injective f ->
       Finite (Im X f) -> Finite X.
Proof.
 intros.
 remember (Im X f) as Y.
 assert (Included (Im X f) Y).
subst; intros ? ?; auto.
clear HeqY.
 revert X H1; induction H0; intros.
 apply Finite_downward_closed with (Empty_set U).
 constructor.
 intros ? ?.
 unfold injective in H.
 assert (~ Im X f (f x)). intro.  apply H1 in H2. inv H2.
 contradiction H2.
 apply Im_intro with x; auto.
 apply Finite_downward_closed
   with  (Union (fun z => f z =x) (fun y : U => X y /\ f y <> x)).
 apply Union_preserves_Finite; auto.
 destruct (Classical_Prop.classic (exists z, f z = x)) as [[y ?]|?].
 apply Finite_downward_closed
   with (Singleton y).
 apply Singleton_is_finite.
 intros ? ?; unfold In in *.
 apply Singleton_intro; apply H. congruence.
 apply Finite_downward_closed with (Empty_set _).
 apply Empty_is_finite.
 intros ? ?. unfold In in H4. contradiction H3; eauto.
 apply IHFinite.
 intros ? ?. destruct H3.
 destruct H3.
 specialize (H2 y).
 subst.
 spec H2.
 apply Im_intro with x0; auto.
 unfold In, Add in H2. destruct H2; auto.
 apply Singleton_inv in H2. contradiction H5; auto.
 intros z ?.
 specialize (H2 (f z)).
 destruct (Classical_Prop.classic (x = f z)).
 subst. left. unfold In; auto.
 right.
 split; auto.
Qed.



Lemma Power_set_finite:
  forall U (F: Ensemble U), Finite F -> Finite (Power_set F).
Proof.
 intros.
 induction H.
 apply Finite_downward_closed
  with  (Singleton (Empty_set U)).
 apply Singleton_is_finite.
 intros ? ?. inv H. apply Singleton_intro.
 unfold Included in H0.
 extensionality y. apply prop_ext; intuition. apply H0 in H. inv H.
 apply Finite_downward_closed
   with (Union (Power_set A)
               (Im (Power_set A) (fun s => Add s x))).
 apply Union_preserves_Finite; auto.
 apply finite_image; auto.
 intros y ?.
 unfold In, Add in H1.
 destruct (Classical_Prop.classic (y x)); [right | left].
 unfold In.
 apply Im_intro with (Subtract y x).
Focus 2.
 clear - H2.
 extensionality z; unfold Add, Subtract. unfold Setminus.
 apply prop_ext; intuition.
 destruct (Classical_Prop.classic (x=z)). right. apply Singleton_intro; auto.
 left; auto. split; auto.  intro.  apply Singleton_inv in H1. contradiction.
 destruct H. destruct H. apply H. apply Singleton_inv in H. subst; auto.
 (* End Focus 2 *)
 clear - H1 H2 H0.
 inv H1. constructor.
 intros z ?. specialize (H z).
 unfold In, Subtract in H1. destruct H1.
 specialize (H H1).
 unfold In in H. destruct H; auto.
 contradiction.
 unfold In.
 constructor.
 inv H1.
 intros z H4; specialize (H3 _ H4).
 unfold In in *. destruct H3; auto.
 apply Singleton_inv in H1. subst. contradiction.
Qed.

Definition list2set {U} (l: list U) : Ensemble U :=
  fun x => List.In x l.

Program Definition ff U (F: Ensemble U) (l : sig (@NoDup (sig F))) : sig (@NoDup U) :=
 (map (@proj1_sig _ _) (proj1_sig l)).
 Next Obligation.
 induction H. constructor.
 simpl.
 constructor.
 contradict H.
 clear - H.
 induction l; simpl in H. contradiction.
 destruct H; simpl; [left | right].
 destruct a; destruct x; simpl. apply exist_ext; auto.
 apply IHl. auto.
 auto.
Qed.

Lemma NoDup_finite:
  forall U (F: Ensemble U), Finite F -> Finite (fun l: sig (@NoDup _) => Forall F (proj1_sig l)).
Proof.
intros.
 destruct (finite_cardinal _ _ H) as [n ?].
 apply Finite_downward_closed
  with (Im (fun l => length (proj1_sig l) <= n) (ff _ F)).
 apply finite_image.
 apply finite_unimage with (@proj1_sig _ _).
 intros ? ? ?. destruct x; destruct y; simpl in *; subst; apply exist_ext; auto.
 apply Finite_downward_closed
  with (fun l => length l <= n).
 clear H0.
 induction n.
 apply Finite_downward_closed with (Singleton nil).
 apply Singleton_is_finite.
 intros ? ?. unfold In in *. destruct x; inv H0.
 apply Singleton_intro; auto.
 pose (gg (_: sig F) := True).
 pose (hh (l: list (sig F)) := length l <= n).
 apply Finite_downward_closed
  with (Union (Singleton nil)
           (Im (fun xy => gg (fst xy) /\ hh (snd xy)) (fun xy => fst xy :: snd xy))).
 apply Union_preserves_Finite.
 apply Singleton_is_finite.
 apply finite_image.
 apply finite_pair.
 unfold gg.
 apply finite_unimage with (@proj1_sig _ _).
 intros ? ? ?. destruct x; destruct y; simpl in *; subst; apply exist_ext; auto.
 apply Finite_downward_closed with F; auto.
 intros ? ?.  unfold In in *.  inv H0.  destruct x0; simpl; auto.
 apply IHn.
 intros ? ?. unfold In in *.
 destruct x; [left | right].
 apply Singleton_intro; auto.
 unfold In. apply Im_intro with (s,x); simpl; auto.
 unfold hh, In. simpl.
 simpl in H0. unfold gg. split; auto; omega.
 intros ? ?.
 unfold In in *. inv H1. unfold In in *. auto.

 intros ? ?.
 unfold In in *.
 assert (exists x' : sig (@NoDup (sig F)),
                map (@proj1_sig _ _) (proj1_sig x') = proj1_sig x).
 clear - H1.
 destruct x as [l H].
 revert H H1; induction l; simpl; intros.
  exists (exist (@NoDup _) _ (NoDup_nil _)).
  simpl. auto.
 inv H. inv H1.
  specialize (IHl H4 H5).
 destruct IHl as [l' ?].
  assert (NoDup (exist F a H2 :: (proj1_sig l'))).
 constructor. contradict H3.
 clear - H H3.
 destruct l' as [l' H1].
 revert l H1 H4 H H3; induction l'; simpl; intros. contradiction.
 destruct H3.
 subst. simpl in *. left; auto.
 subst. simpl. right.
 inv H1.
 inv H4.
 apply (IHl' (map (@proj1_sig _ _) l') H6 H7).
 simpl. auto.
 simpl. auto.
 simpl in *. subst.
 clear - H4.
 revert H4; induction l'; simpl; intros; auto.
 exists (exist (@NoDup _) _ H0).
 simpl. f_equal. simpl in H; auto.
 destruct H2 as [x' ?].
 apply Im_intro with x'.
 2: unfold ff; destruct x as [x ?];  simpl in *; apply exist_ext; auto.
 unfold In.
 destruct x as [l' ?].
 simpl in *.
 replace (length (proj1_sig x')) with (length l') by (rewrite <- H2; apply map_length).
 clear - n0 H1 H0.
 rename l' into l.
 revert F n n0 H0 H1; induction l; simpl; intros.
 omega.
 inv n0. inv H1.
 assert (length l <= pred n).
  (apply (IHl (Subtract F a))); auto.
 apply card_soustr_1; auto.
 rewrite Forall_forall in H6|-*.
 intros.
 split; auto. apply H6; auto.
 intro. apply Singleton_inv in H1. subst. contradiction.
 assert (n >0).
 clear - H0 H5.
 eapply inh_card_gt_O; try eassumption. exists a; apply H5.
 omega.
Qed.

Lemma finite_list_bound:
 forall U (F: Ensemble U), Finite F -> Finite (list_bound F).
Proof.
 unfold list_bound; intros.
 apply Finite_downward_closed
    with   (Im (fun l: sig (@NoDup _) => Forall F (proj1_sig l)) (@proj1_sig _ _)).
 apply finite_image.
 apply NoDup_finite; auto.
 intros ? ?. destruct H0; unfold In;
     apply Im_intro with (exist (@NoDup _) x H1); [apply H0 |  reflexivity].
Qed.

Lemma finite_expr_bound:
  forall n, Finite n -> Finite (expr_bound n).
Proof.
 unfold expr_bound; intros.
 apply Finite_downward_closed
   with (Union (Singleton Nil) (Im n Var)).
 apply Union_preserves_Finite.
 apply Singleton_is_finite.
 apply finite_image; auto.
 intros ? ?. destruct x.
 left; apply Singleton_intro; auto.
 right. apply Im_intro with v; auto.
Qed.

Lemma finite_pure_bound: forall n, Finite n -> Finite (pure_bound n).
Proof.
 unfold pure_bound;  intros.
 apply Finite_downward_closed
    with (Im (fun xy => expr_bound n (fst xy) /\ expr_bound n (snd xy))
                  (fun xy => Eqv (fst xy) (snd xy))).
 apply finite_image.
 apply finite_pair; apply finite_expr_bound; auto.
 intros ? ?. destruct x. unfold In in H0. destruct H0.
 unfold In.
 apply Im_intro with (e,e0). split; auto. simpl; auto.
Qed.

Lemma finite_space_bound: forall n, Finite n -> Finite (space_bound n).
Proof. intros n FIN.
 unfold space_bound; intros.
 apply Finite_downward_closed
   with (Union
              (Intersection (space_bound n)
                         (fun a => match a with Next _ _ => True | _ => False end))
              (Intersection (space_bound n)
                         (fun a => match a with Lseg _ _ => True | _ => False end))).
 2: intros a H; unfold In in *; destruct a; [left | right]; unfold In; split; unfold In; simpl; auto.
 apply Union_preserves_Finite.
 apply Finite_downward_closed
    with  (Im (fun xy => expr_bound n (fst xy) /\ expr_bound n (snd xy))
                   (fun xy : expr * expr => Next (fst xy) (snd xy))).
 apply finite_image.
 apply finite_pair; apply finite_expr_bound; auto.
 intros ? ?; unfold In in *. destruct H. destruct x; simpl in H0; try contradiction.
 unfold In, space_bound in H; destruct H.
 apply Im_intro with (e,e0); split; auto.
 apply Finite_downward_closed
    with  (Im (fun xy => expr_bound n (fst xy) /\ expr_bound n (snd xy))
                   (fun xy : expr * expr => Lseg (fst xy) (snd xy))).
 apply finite_image.
 apply finite_pair; apply finite_expr_bound; auto.
 intros ? ?; unfold In in *. destruct H. destruct x; simpl in H0; try contradiction.
 unfold In, space_bound in H; destruct H.
 apply Im_intro with (e,e0); split; auto.
Qed.

Lemma finite_pures_bound: forall n, Finite n -> Finite (pures_bound n).
Proof.
intros. apply finite_list_bound.
apply finite_pure_bound; auto.
Qed.

Lemma finite_spaces_bound: forall n, Finite n -> Finite (spaces_bound n).
Proof.
intros. apply finite_list_bound.
apply finite_space_bound; auto.
Qed.

Lemma clause_bound_finite: forall n, Finite n -> Finite (clause_bound n).
Proof.
intros n FIN.
assert (clause_bound n =
               Union
                   (Intersection (clause_bound n)
                       (fun cl => match cl with PureClause _ _ _ _ => True | _ => False end))
               (Union
                  (Intersection (clause_bound n)
                           (fun cl => match cl with PosSpaceClause _ _ _ => True | _ => False end))
                (Intersection (clause_bound n)
                           (fun cl => match cl with NegSpaceClause _ _ _ => True | _ => False end)))).
 set (g:= clause_bound n); clearbody g.
 extensionality x.
 Hint Unfold In.
 apply prop_ext; destruct x; simpl; intuition. left. split; auto.
 repeat destruct H; auto.
 right; left; split; auto.
 repeat destruct H; auto.
 right; right; split; auto.
 repeat destruct H; auto.
 rewrite H.
 apply Union_preserves_Finite.
 apply Finite_downward_closed
    with  (Im (pures_bound2 n)
                             (fun pi2 : list pure_atom * list pure_atom =>
                                                mkPureClause (fst pi2) (snd pi2))).
  apply finite_image.
  apply finite_pair;   apply finite_pures_bound; auto.
  clear.
  intros x H;  destruct H; unfold In in *; destruct x; try contradiction; simpl in *.
  apply Im_intro with (gamma,delta); auto.
  simpl.
  apply pure_clause_ext.
  apply Union_preserves_Finite.
  apply Finite_downward_closed
    with (Im (fun pi3 => pures_bound2 n (fst pi3) /\ spaces_bound n (snd pi3))
                  (fun pi3 => PosSpaceClause  (fst (fst pi3)) (snd (fst pi3)) (snd pi3))).
   apply finite_image.
   apply finite_pair.
   apply finite_pair; apply finite_pures_bound; auto.
   apply finite_spaces_bound; auto.
   clear.
   intros x H;  destruct H; unfold In in *; destruct x; try contradiction; simpl in *.
  apply Im_intro with ((gamma,delta),sigma); auto.
  unfold In. simpl in H. simpl. unfold pures_bound2; intuition.
  apply Finite_downward_closed
    with (Im (fun pi3 => pures_bound2 n (fst pi3) /\ spaces_bound n (snd pi3))
                  (fun pi3 => NegSpaceClause  (fst (fst pi3)) (snd pi3) (snd (fst pi3)))).
   apply finite_image.
   apply finite_pair.
   apply finite_pair; apply finite_pures_bound; auto.
   apply finite_spaces_bound; auto.
  clear.
  intros x H;  destruct H; unfold In in *; destruct x; try contradiction; simpl in *.
  apply Im_intro with ((gamma,delta),sigma); auto.
  unfold In. simpl in H. simpl. unfold pures_bound2; intuition.
Qed.

Definition var2nat v := nat_of_P (id2pos v).

Lemma Finite_var_upto:
  forall v, Finite (var_upto v).
Proof.
 intros.
 apply finite_unimage with var2nat.
 intros ? ? ?. unfold var2nat in *.
 apply Pnat.nat_of_P_inj in H.
 apply id2pos_inj in H; auto.
 apply Finite_downward_closed
  with (fun i => i <= var2nat v).
remember (var2nat v) as n.
clear.
induction n.
apply Finite_downward_closed with (Add (Empty_set _) O).
repeat constructor.
intro H; inversion H.
intros ? ?; unfold In in *.
assert (x=0) by omega. subst. right. apply Singleton_intro; auto.
apply Finite_downward_closed with (Add (fun i => i<=n) (S n)).
constructor; auto.
unfold In; omega.
repeat intro. unfold In in *.
assert (x <= n \/ x = S n) by omega.
destruct H0; [ left | right]; auto.
apply Singleton_intro; auto.
repeat intro; unfold In in *.
inversion H; clear H; subst.
unfold In, var_upto in *.
apply S_nat_of_P_id2pos_le in H0.
unfold var2nat; omega.
Qed.

End ClauseUniverseFinite.







