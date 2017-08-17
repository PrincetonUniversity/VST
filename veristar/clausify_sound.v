Load loadpath.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Sorting.Permutation
               Coq.Logic.Classical.
Require Import VST.msl.Axioms VST.msl.predicates_sa.
Require Import veristar.datatypes veristar.clauses veristar.list_denote
               veristar.model_type veristar.model veristar.spred_lemmas
               veristar.basic.

Module Type CLAUSIFY_SOUND.
Declare Module VSM : VERISTAR_MODEL.
Import VSM VeriStarLogic.

Axiom cnf_correct : forall (e : entailment),
  entailment_denote e =
  forall s, ~ list_denote clause_denote (@andp state) TT (cnf e) s.

End CLAUSIFY_SOUND.

Module Clausify_Sound (VSM : VERISTAR_MODEL) : CLAUSIFY_SOUND
  with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Module SPredLems := SPredLemmas VSM. Import SPredLems.

Lemma clausify_single_purepos : forall purea,
  listd pure_atom_denote (@andp state) TT (purea :: nil) =
  clause_denote (mkPureClause nil (order_eqv_pure_atom purea :: nil)).
Proof.
intros; extensionality s; simpl.
apply prop_ext; split; intros.
destruct H. left.
rewrite <- pure_atom_denote_order_eqv_pure_atom. auto.
destruct H. auto.
repeat split; auto.
rewrite <- pure_atom_denote_order_eqv_pure_atom in H. auto.
destruct H.
Qed.

Lemma clausify_single_pureneg : forall purea,
  list_denote (neg oo pure_atom_denote) (@andp state) TT (purea :: nil) =
  clause_denote (mkPureClause (order_eqv_pure_atom purea :: nil) nil).
Proof.
intros. extensionality s. simpl.
apply prop_ext; split; intros.
destruct H. destruct H0. destruct H.
rewrite <- pure_atom_denote_order_eqv_pure_atom in H0. auto.
repeat split; auto. unfold neg,compose. intro Contra.
destruct H.
rewrite <- pure_atom_denote_order_eqv_pure_atom.
split; auto.
Qed.

Lemma clausify_purepos : forall l : list pure_atom,
  list_denote pure_atom_denote (@andp state) TT l =
  list_denote clause_denote (@andp state) TT
    (map (fun a => mkPureClause nil (order_eqv_pure_atom a::nil)) l).
Proof.
intros. extensionality s.
induction l; simpl; apply prop_ext; split; intros; auto.
split. rewrite <- clausify_single_purepos. simpl.
destruct H as [H _]. repeat split; auto.
rewrite <- IHl.
destruct H as [_ H]. repeat split; auto.
destruct H. rewrite <- clausify_single_purepos in H. simpl in H.
destruct H. rewrite <- IHl in H0.
repeat split; auto.
Qed.

Lemma clausify_pureposP : forall (l : list pure_atom) P,
  list_denote pure_atom_denote (@andp state) P l =
  list_denote clause_denote (@andp state) P
    (map (fun a => mkPureClause nil (order_eqv_pure_atom a::nil)) l).
Proof.
intros. extensionality s.
induction l; simpl; apply prop_ext; split; intros; auto.
split. rewrite <- clausify_single_purepos. simpl.
destruct H as [H _]. repeat split; auto.
rewrite <- IHl.
destruct H as [_ H]. repeat split; auto.
destruct H. rewrite <- clausify_single_purepos in H. simpl in H.
destruct H. rewrite <- IHl in H0.
repeat split; auto.
Qed.

Lemma clausify_pureneg : forall l : list pure_atom,
  list_denote (neg oo pure_atom_denote) (@andp state) TT l =
  list_denote clause_denote (@andp state) TT
    (map (fun a => mkPureClause (order_eqv_pure_atom a::nil) nil) l).
Proof.
intros. extensionality s.
induction l; simpl; apply prop_ext; split; intros; auto.
split. rewrite <- clausify_single_pureneg. simpl.
destruct H as [H _]. split; auto.
rewrite <- IHl. simpl. destruct H; auto.
destruct H. rewrite <- clausify_single_pureneg in H.
destruct H. rewrite <- IHl in H0. split; auto.
Qed.

Lemma clausify_space : forall l : list space_atom,
  space_denote l = clause_denote (PosSpaceClause nil nil l).
Proof.
intros. extensionality s.
apply prop_ext; split; intros.
simpl in *; auto.
simpl in *. apply H; auto.
Qed.

Lemma pure_atom_list_neg2 : forall (l: list pure_atom) s,
  (~(list_denote pure_atom_denote (@orp state) FF l s)) =
  list_denote (neg oo pure_atom_denote) (@andp state) TT l s.
Proof.
intros. apply prop_ext; split; intros.
induction l; simpl in *; auto.
unfold neg,compose in * |-.
assert (~pure_atom_denote a s /\
        ~list_denote pure_atom_denote (@orp state) FF l s).
  clear IHl. firstorder.
  destruct H0; split; auto.
intro Contra. induction l; simpl in *; auto. apply H; auto.
destruct Contra; auto.
exfalso. destruct H. apply IHl; auto.
Qed.

Lemma mk_pureR_denote1: forall pnatoms purepos pureneg P s,
  mk_pureR pnatoms = (purepos, pureneg) ->
  listd pn_atom_denote inter P pnatoms s ->
  (listd pure_atom_denote inter P purepos s /\
    ~listd pure_atom_denote (@orp state) FF pureneg s).
Proof.
intros pnatoms.
induction pnatoms; intros.
  inversion H; subst. simpl. split. trivial.
  intros N. apply N.
destruct H0 as [HD TL].
  simpl in *.
  remember (mk_pureR pnatoms) as mkP. destruct mkP.
  destruct (IHpnatoms _ _ _ _ (eq_refl _) TL) as [IHP IHN]. clear IHpnatoms TL.
  destruct a. inversion H; subst. clear H.
    simpl. split; trivial.
    split. generalize (pure_atom_denote_order_eqv_pure_atom (Eqv e e0)) as H1; intro.
           unfold order_eqv_pure_atom in H1. rewrite <-H1.
           apply HD. apply IHP.
  inversion H; subst. clear H.
    simpl. split; trivial.
     intros N. destruct N. simpl in HD. apply HD.
         generalize (pure_atom_denote_order_eqv_pure_atom (Eqv e e0)) as H1; intro.
         unfold order_eqv_pure_atom in H1. rewrite <-H1 in H; auto.
         apply IHN. apply H.
Qed.

Lemma mk_pureR_denote2: forall pnatoms purepos pureneg P s,
  mk_pureR pnatoms = (purepos, pureneg) ->
  listd pure_atom_denote inter P purepos s ->
  ~ listd pure_atom_denote (@orp state) FF pureneg s ->
  listd pn_atom_denote inter P pnatoms s.
Proof.
intros pnatoms.
induction pnatoms; simpl; intros.
  inversion H; subst. trivial.
remember (mk_pureR pnatoms) as mkP. destruct mkP.
destruct a. inversion H; subst. clear H. simpl in *.
  destruct H0. split.
  generalize (pure_atom_denote_order_eqv_pure_atom (Eqv e e0)) as H2; intro.
    unfold order_eqv_pure_atom in H2. rewrite <-H2 in H; auto.
  eapply  IHpnatoms. reflexivity. assumption.
  apply H1.
inversion H; subst. clear H.
  rewrite pure_atom_list_neg2 in H1.
  simpl in *. destruct H1.
  split. unfold compose in H.
    generalize (pure_atom_denote_order_eqv_pure_atom (Eqv e e0)) as H2; intro.
    unfold order_eqv_pure_atom in H2. rewrite <-H2 in H; auto.
  eapply IHpnatoms; clear IHpnatoms. reflexivity. apply H0.
  rewrite pure_atom_list_neg2. apply H1.
Qed.

Lemma mk_pureR_denote: forall pnatoms purepos pureneg P s,
  mk_pureR pnatoms = (purepos, pureneg) ->
  listd pn_atom_denote inter P pnatoms s =
  (listd pure_atom_denote inter P purepos s /\
    ~listd pure_atom_denote (@orp state) FF pureneg s).
Proof.
intros.
apply prop_ext.
split; intros.
  eapply (mk_pureR_denote1 _ _ _ _ _ H H0).
destruct H0.
  eapply (mk_pureR_denote2 _ _ _ _ _ H H0 H1).
Qed.

Lemma mk_pureR_denote3: forall pnatoms purepos pureneg P s,
  mk_pureR pnatoms = (purepos, pureneg) ->
  listd pure_atom_denote inter P purepos s ->
  ~ listd pn_atom_denote inter P pnatoms s ->
  listd pure_atom_denote (@orp state) FF pureneg s.
Proof.
intros.
rewrite (mk_pureR_denote _ _ _ _ s H) in H1.
apply not_and_or in H1.
destruct H1.
apply Decidable.not_not; auto.
apply classic.
apply Decidable.not_not; auto.
apply classic.
Qed.

Lemma clausify_succ : forall pnatoms (purepos pureneg : list pure_atom)
  (space : list space_atom) (s : state)
  (Hyp: mk_pureR pnatoms = (purepos, pureneg)),
  (~assertion_denote (Assertion pnatoms space) s) =
  (clause_denote (NegSpaceClause purepos space pureneg) s).
Proof.
intros. simpl.
rewrite (@listd_unfold_inter _ state).
pattern (list_denote (neg oo pure_atom_denote) (@andp state)
  (space_denote space) pureneg).
rewrite (@listd_unfold_inter _ state).
pattern (list_denote pure_atom_denote (@andp state) (space_denote space) purepos).
rewrite (@listd_unfold_inter _ state).
apply prop_ext; split; intros.
destruct H0.
apply Decidable.not_and in H.
2: apply classic.
destruct H.
  eapply mk_pureR_denote3. apply Hyp. apply H0. apply H.
destruct (H H1).

intros N. destruct N.
  destruct (mk_pureR_denote1 _ _ _ _ s Hyp H0). clear H0.
  apply H3. apply H. split; assumption.
Qed.

Lemma clausify_succClassic : forall pnatoms (purepos pureneg : list pure_atom)
  (space : list space_atom) (s : state)
  (Hyp: mk_pureR pnatoms = (purepos, pureneg)),
   (assertion_denote (Assertion pnatoms space) s) =
  (~clause_denote (NegSpaceClause purepos space pureneg) s).
Proof.
intros. rewrite <- (clausify_succ pnatoms).
apply prop_ext; split; intros.
  intros N. apply (N H).
apply Decidable.not_not; auto.
 apply classic.
assumption.
Qed.

Lemma mk_pureL_denote: forall a s,
  clause_denote (mk_pureL a) s -> pn_atom_denote a s.
Proof.
intros.
destruct a; simpl in *.
  assert (T : TT s). trivial.
  assert (HH := H T). clear H T.
  remember (expr_cmp e e0) as b; destruct b; simpl in *.
    destruct HH. assumption. contradiction.
    destruct HH. apply var_eq_sym. apply H. contradiction.
    destruct HH. assumption. contradiction.
intros N. apply H. clear H.
  remember (expr_cmp e e0) as b; destruct b; simpl in *.
    split; trivial.
    split; trivial. apply var_eq_sym. assumption.
    split; trivial.
Qed.

Lemma mk_pureL_denoteInv: forall a s,
  pn_atom_denote a s -> clause_denote (mk_pureL a) s.
Proof.
intros.
destruct a; simpl in *. intros X. clear X.
  remember (expr_cmp e e0) as b; destruct b; simpl in *.
    left; trivial.
    left. apply var_eq_sym. assumption.
    left. trivial.
  intros HH. apply H. clear H.
  remember (expr_cmp e e0) as b; destruct b; simpl in *.
    destruct HH. assumption.
    destruct HH. apply var_eq_sym. apply H.
    destruct HH. assumption.
Qed.

Lemma mk_pureL_denoteEq: forall a,
  pn_atom_denote a = clause_denote (mk_pureL a).
Proof.
intros.
apply extensionality. intros s.
apply prop_ext; split; intros.
 apply mk_pureL_denoteInv. apply H.
  apply mk_pureL_denote. apply H.
Qed.

Lemma mk_pureL_clause_denote: forall pi P s,
  listd clause_denote inter P (map mk_pureL pi) s ->
  listd pn_atom_denote inter P pi s.
Proof.
intros pi.
induction pi; intros; simpl in *. trivial.
destruct H.
split. apply (mk_pureL_denote _ _ H).
apply IHpi. apply H0.
Qed.

Lemma mk_pureL_clause_denoteInv: forall pi P s,
  listd pn_atom_denote inter P pi s ->
  listd clause_denote inter P (map mk_pureL pi) s.
Proof.
intros pi.
induction pi; intros; simpl in *. trivial.
destruct H.
split. apply (mk_pureL_denoteInv _ _ H).
apply IHpi. apply H0.
Qed.

Lemma mk_pureL_clause_denoteEq:forall pi P,
  listd pn_atom_denote inter P pi =
  listd clause_denote inter P (map mk_pureL pi).
Proof.
intros.
apply extensionality. intros s.
apply prop_ext; split; intros.
 apply mk_pureL_clause_denoteInv. apply H.
  apply mk_pureL_clause_denote. apply H.
Qed.

Lemma listd_pure_atoms_heap_expand atms :
  listd pure_atom_denote inter emp atms |--
  listd pure_atom_denote inter TT atms.
Proof with simpl; auto.
induction atms... intros s [H1 H2]. split...
Qed.

Theorem cnf_correct1 : forall (e : entailment),
  entailment_denote e ->
  forall s, ~ list_denote clause_denote (@andp state) TT (cnf e) s.
Proof.
intros.
destruct e. unfold entailment_denote.
intro.
unfold cnf in H0.
destruct a. destruct a0 as [pi' sigma'].
remember (mk_pureR pi') as mkR. destruct mkR as[purepos pureneg].
repeat rewrite listd_app in H0.
repeat rewrite (@listd_separate _ _ state) in H0.
destruct H0.
destruct H1. simpl in H1.
destruct H1. simpl in H1.
destruct sigma' as [|s0' sigma'].
(* sigma' nil case *)
destruct sigma as [|s0 sigma].
destruct H2. simpl in H2.
assert (H5 : assertion_denote (Assertion pi' nil) s).
  apply H. unfold assertion_denote; simpl.
  rewrite (@listd_unfold_inter _ state); split; auto.
  rewrite mk_pureL_clause_denoteEq; auto. apply H1; auto.
rewrite clausify_succClassic with (purepos:=purepos)(pureneg:=pureneg) in H5; auto.
apply H5; simpl in H5; simpl; intro H6. apply H2.
apply listd_pure_atoms_heap_expand; auto.
destruct H2.
assert (H11 := H1 H3). clear H1.
clear H3 H4.
apply eq_sym in HeqmkR.
rewrite <- (clausify_succ _ _ _ nil s HeqmkR) in H2.
apply H2. apply H. clear H2 H.
simpl.
assert (Q: (andp (listd pn_atom_denote inter TT pi) (space_denote (s0::sigma)))%pred s).
  split. apply (mk_pureL_clause_denote _ _ _ H0).
  apply H11.
assert (XX: ((listd pn_atom_denote inter (space_denote (s0::sigma)) pi s) =
    (listd pn_atom_denote inter TT pi && space_denote (s0::sigma))%pred s)).
  assert (X:= (@listd_unfold_inter pn_atom state pn_atom_denote (space_denote (s0::sigma)) pi)).
  unfold pred in X. rewrite X.
  trivial.
simpl in XX. rewrite XX. apply Q.
(* sigma' cons case *)
  (* sigma nil case *)
destruct sigma as [|s0 sigma].
destruct H2.
assert (H11 := H1 H3). clear H1.
clear H3 H4.
apply eq_sym in HeqmkR.
rewrite <- (clausify_succ _ _ _ (s0'::sigma') s HeqmkR) in H2.
apply H2. apply H. clear H2 H.
simpl.
assert (Q: (andp (listd pn_atom_denote inter TT pi) (space_denote nil))%pred s).
  split. apply (mk_pureL_clause_denote _ _ _ H0).
  apply H11.
assert (XX: ((listd pn_atom_denote inter (space_denote nil) pi s) =
    (listd pn_atom_denote inter TT pi && space_denote nil)%pred s)).
  assert (X:= (@listd_unfold_inter pn_atom state pn_atom_denote (space_denote nil) pi)).
  unfold pred in X. rewrite X.
  trivial.
simpl in XX. rewrite XX. apply Q.
  (* sigma cons case *)
destruct H2.
assert (H11 := H1 H3). clear H1.
clear H3 H4.
apply eq_sym in HeqmkR.
rewrite <- (clausify_succ _ _ _ (s0'::sigma') s HeqmkR) in H2.
apply H2. apply H. clear H2 H.
simpl.
assert (Q: (andp (listd pn_atom_denote inter TT pi) (space_denote (s0::sigma)))%pred s).
  split. apply (mk_pureL_clause_denote _ _ _ H0).
  apply H11.
assert (XX: ((listd pn_atom_denote inter (space_denote (s0::sigma)) pi s) =
    (listd pn_atom_denote inter TT pi && space_denote (s0::sigma))%pred s)).
  assert (X:= (@listd_unfold_inter pn_atom state pn_atom_denote (space_denote (s0::sigma)) pi)).
  unfold pred in X. rewrite X.
  trivial.
simpl in XX; rewrite XX. apply Q.
Qed.

Theorem cnf_correct2 : forall (e : entailment),
  (forall s, ~ list_denote clause_denote (@andp state) TT (cnf e) s) ->
   entailment_denote e.
Proof.
intros.
destruct e; simpl.
intros s K. specialize (H s).
destruct (classic (assertion_denote a0 s)); auto.
contradict H.
unfold cnf.
destruct a. destruct a0 as [pi' sigma'].
remember (mk_pureR pi') as mkR. destruct mkR as[purepos' pureneg'].
repeat rewrite listd_app.
repeat rewrite (@listd_separate _ _ state).
simpl in H0.
assert (XL : ~ listd clause_denote inter (space_denote sigma') (map mk_pureL pi') s).
  rewrite (mk_pureL_clause_denoteEq) in H0. assumption.
apply eq_sym in HeqmkR.
rewrite (mk_pureR_denote _ _ _ _ _ HeqmkR) in H0.
simpl in *.
repeat rewrite andp_TT.
rewrite (mk_pureL_clause_denoteEq) in K.
rewrite (@listd_prop clause state clause_denote) in K.
destruct K as [K1 K2].
split. assumption.
split. rewrite clausify_space in K2. apply K2.

destruct sigma. destruct sigma'.
  simpl. split; auto. intros HH.
assert (H1: listd pure_atom_denote inter emp purepos' s).
  simpl in K2. rewrite (@listd_unfold_inter _ state). split; auto.
apply Decidable.not_and in H0.
destruct H0. destruct (H H1).
   apply Decidable.not_not in H. apply H.
   apply classic.
apply classic.
remember (s0 :: sigma') as sigma''.
simpl. split; auto. intros HH.
apply Decidable.not_and in H0.
destruct H0. destruct (H HH).
   apply Decidable.not_not in H. apply H.
   apply classic.
apply classic.
apply Decidable.not_and in H0.
destruct H0. simpl. split; auto. intros HH. destruct (H HH).
   apply Decidable.not_not in H.
   split; simpl; auto.
   apply classic.
apply classic.
Qed.

Theorem cnf_correct : forall (e : entailment),
  entailment_denote e =
  forall s, ~ list_denote clause_denote (@andp state) TT (cnf e) s.
Proof.
intros.
apply prop_ext.
split; intros.
  eapply cnf_correct1. apply H.
 eapply cnf_correct2. apply H.
Qed.

End Clausify_Sound.

