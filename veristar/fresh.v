Load loadpath.
Require Import Coq.Lists.List.
Require Import veristar.variables veristar.datatypes.
Require Import Coqlib.
Require Import VST.msl.Coqlib2.
Require Import ZArith.
Require Import veristar.compare.
Require Import veristar.clauses.


Fixpoint freshmax_expr (e: expr) : var :=
  match e with
  | Nil => minid
  | Var v => v
  end.

Definition var_max (x y : var) : var :=
 match Ident.compare x y with Lt => y | _ => x end.

Definition freshmax_pn_atom (a: pn_atom) : var :=
  match a with
  | Equ e1 e2 => var_max (freshmax_expr e1) (freshmax_expr e2)
  | Nequ e1 e2 => var_max (freshmax_expr e1) (freshmax_expr e2)
  end.

Definition freshmax_space_atom (a: space_atom) : var :=
  match a with
  | Next e1 e2 =>  var_max (freshmax_expr e1) (freshmax_expr e2)
  | Lseg e1 e2 =>  var_max (freshmax_expr e1) (freshmax_expr e2)
 end.

Definition freshmax_list {A} (f: A -> var) (l: list A) : var :=
  fold_right (fun a i => var_max (f a) i) minid l.

Definition freshmax_assertion (a: assertion) : var :=
  match a with
  | Assertion pi sigma =>
     var_max (freshmax_list freshmax_pn_atom pi)
            (freshmax_list freshmax_space_atom sigma)
  end.

Definition freshmax_pure_atom (a: pure_atom) : var :=
  match a with
  | Eqv e1 e2 => var_max (freshmax_expr e1) (freshmax_expr e2)
  end.

Definition freshmax_clause (c : clause) : var :=
 match c with
 | PureClause pi pi' _ _ =>  var_max (freshmax_list freshmax_pure_atom pi)
                                     (freshmax_list freshmax_pure_atom pi')
 | PosSpaceClause pi pi' sigma =>
     var_max (var_max (freshmax_list freshmax_pure_atom pi)
                                     (freshmax_list freshmax_pure_atom pi'))
                       (freshmax_list freshmax_space_atom sigma)
 | NegSpaceClause pi sigma pi' =>
     var_max (var_max (freshmax_list freshmax_pure_atom pi)
                                     (freshmax_list freshmax_pure_atom pi'))
                       (freshmax_list freshmax_space_atom sigma)
 end.


Lemma varmax_minid: forall x, var_max minid x = x.
Proof.
intros; unfold var_max.
id_compare minid x; auto.
apply minid_min in l; contradiction.
Qed.

Lemma varmax_minid': forall x, var_max x minid = x.
Proof.
intros; unfold var_max.
id_compare x minid; auto.
apply minid_min in l; contradiction.
Qed.


Lemma var_max_intro:
  forall a b c, Ident.lt a c -> Ident.lt b c -> Ident.lt (var_max a b) c.
Proof.
unfold var_max; intros; auto.
id_compare a b; auto.
Qed.

Lemma Ile_var_max1:  forall a b, Ile a (var_max a b).
Proof.
intros.
 unfold Ile, var_max.
 id_compare a b; subst; auto;  right; apply Ident.eq_equiv.
Qed.

Lemma Ile_var_max2:  forall a b, Ile b (var_max a b).
Proof.
intros.
 unfold Ile, var_max.
 id_compare a b; subst; auto;  right; apply Ident.eq_equiv.
Qed.

Lemma Ile_trans: forall a b c, Ile a b -> Ile b c -> Ile a c.
Proof.
 unfold Ile; intros.
 destruct H. left; destruct H0. eapply Ilt_trans; eauto.
 rewrite <- H0; auto. rewrite H in *; auto.
Qed.

Lemma Ile_minid: forall m, Ile minid m.
Proof.
 unfold Ile; intros.
 id_compare minid m. subst. right; apply Ident.eq_equiv.
 auto. apply minid_min in l; contradiction.
Qed.

Lemma var_max_intro':
  forall a b c, Ile a c -> Ile b c -> Ile (var_max a b) c.
Proof.
unfold var_max; intros; auto.
id_compare a b; auto.
Qed.

Lemma var_max_split': forall a b c, Ile (var_max a b) c -> Ile a c /\ Ile b c.
Proof.
unfold var_max; intros.
id_compare a b; subst; intuition.
destruct H. left; eapply Ilt_trans; eauto.
rewrite H in *. left; auto.
destruct H.
left; eapply Ilt_trans; eauto.
rewrite H in *.
left; auto.
Qed.


Lemma id_compare_refl: forall z, Ident.compare z z = Eq.
Proof. intro. id_compare z z; auto; contradiction (Ilt_irrefl l).
Qed.

Lemma id_compare_lt: forall x y, Ident.lt x y -> Ident.compare x y = Lt.
Proof. intros. id_compare x y; auto. subst; contradiction (Ilt_irrefl H).
contradiction (Ilt_irrefl (Ilt_trans H l)).
Qed.

Lemma id_compare_gt: forall x y, Ident.lt y x -> Ident.compare x y = Gt.
Proof. intros. id_compare x y; auto. subst; contradiction (Ilt_irrefl H).
contradiction (Ilt_irrefl (Ilt_trans l H)).
Qed.

Lemma var_max_assoc: forall x y z, var_max x (var_max y z) = var_max (var_max x y) z.
Proof.
intros.
unfold var_max.
id_compare x y.
subst. id_compare y z. subst.
rewrite id_compare_refl; auto.

rewrite id_compare_lt; auto.
rewrite id_compare_refl; auto.
id_compare y z; auto. subst. rewrite id_compare_lt; auto.
rewrite id_compare_lt; auto. eapply Ilt_trans; eauto.
id_compare x y; auto.
contradiction (Ilt_irrefl (Ilt_trans l1 l)).
id_compare y z; auto.
subst.
rewrite id_compare_gt; auto.
rewrite id_compare_gt; auto.
rewrite id_compare_gt; auto.
eapply Ilt_trans; eauto.
Qed.


Lemma var_max_com: forall x y, var_max x y = var_max y x.
Proof.
intros.
unfold var_max.
id_compare x y; auto.
subst; rewrite id_compare_refl; auto.
rewrite id_compare_gt; auto.
rewrite id_compare_lt; auto.
Qed.

Lemma var_max_split: forall a b c, Ident.lt (var_max a b) c -> Ident.lt a c /\ Ident.lt b c.
Proof.
unfold var_max; intros.
id_compare a b; subst; intuition.
transitivity b; auto.
transitivity a; auto.
Qed.



Lemma freshmax_list_app:
 forall {A} (f: A -> var) l1 l2,
    freshmax_list f (l1++l2) = var_max (freshmax_list f l1) (freshmax_list f l2).
Proof.
intros.
induction l1; simpl.
rewrite varmax_minid. auto.
rewrite IHl1.
rewrite var_max_assoc; auto.
Qed.

Lemma freshmax_list_rev:
 forall {A} (f: A -> var) l,
    freshmax_list f (rev l) = freshmax_list f l.
Proof.
induction l; simpl; auto.
rewrite freshmax_list_app.
rewrite IHl.
simpl.
rewrite (var_max_com (f a)).
rewrite varmax_minid.
apply var_max_com.
Qed.

Lemma Ile_freshmax_i3:
  forall s m,
    (forall x, M.In x s -> Ile (freshmax_clause x) m) ->
     Ile (freshmax_list freshmax_clause (M.elements s)) m.
Proof.
  intros.
  assert (forall x, List.In x (M.elements s) -> Ile (freshmax_clause x) m).
  intros. rewrite Melements_spec1 in H0. auto.
  clear H.
  revert H0; induction (M.elements s); simpl; intros.
  apply Ile_minid.
  apply var_max_intro'.
  apply H0; auto.
  apply IHl.
   intros; auto.
Qed.

Lemma merge_nil1:
  forall {A} (f: A -> A -> comparison) l, merge f nil l = l.
Proof.
 intros. induction l; simpl; auto.
Qed.

Lemma freshmax_list_merge:
  forall m al bl,
     Ile (freshmax_list freshmax_pure_atom al) m ->
     Ile (freshmax_list freshmax_pure_atom bl) m ->
     Ile (freshmax_list freshmax_pure_atom (merge pure_atom_cmp al bl)) m.
Proof.
 intros.
  revert bl H H0; induction al; simpl; intros; auto.
  revert H0; induction bl; simpl; intros; auto.
  apply var_max_split' in H; destruct H.
assert (IHal':
  forall bl, Ile (freshmax_list freshmax_pure_atom bl) m ->
       Ile (freshmax_list freshmax_pure_atom (merge pure_atom_cmp al bl)) m).
 intros; apply IHal; auto.
  clear IHal.
  revert H0; induction bl; intros.
  apply var_max_intro'; auto.
  apply var_max_split' in H0; destruct H0.
  destruct (pure_atom_cmp a a0).
  apply var_max_intro'; auto.
 apply IHal'; auto.
  apply var_max_intro'; auto.
  apply var_max_intro'; auto.
  apply IHal'.
  apply var_max_intro'; auto.
Qed.


Lemma Ile_freshmax_list:
  forall A (f: A -> var) m (s: list A),
    Ile (freshmax_list f s) m <-> (forall x, List.In x s -> Ile (f x) m).
Proof.
  intros.
  split; induction s; simpl; intros; try contradiction.
  destruct H0; subst.
  apply var_max_split' in H. destruct H; auto.
  apply var_max_split' in H. destruct H; auto.
  apply Ile_minid.
  simpl.
  apply var_max_intro'.
  apply H; simpl; auto.
  apply IHs; auto.
Qed.

Lemma freshmax_list_insu:
   forall A (f: A -> var) (cmp: A -> A -> comparison)
      (CMP_EQ: forall a b, a=b <-> Eq = cmp a b)
      a s,
      freshmax_list f (insert_uniq cmp a s) = var_max (f a) (freshmax_list f s).
Proof.
 induction s; simpl; intros; auto.
 case_eq (cmp a a0); intros.
 symmetry in H; apply CMP_EQ in H; subst a0.
 simpl.
 rewrite var_max_assoc.
 f_equal; auto.
 unfold var_max. destruct (Ident.compare (f a) (f a)); auto.
 simpl. rewrite IHs.
 repeat rewrite var_max_assoc.
 f_equal. apply var_max_com.
 simpl. auto.
Qed.

Lemma freshmax_list_sort:
  forall A (f: A -> var) (cmp: A -> A -> comparison)
      (CMP_EQ: forall a b, a=b <-> Eq = cmp a b)
      (s: list A),
    freshmax_list f (rsort_uniq cmp s) = freshmax_list f s.
Proof.
  induction s; simpl; intros; auto.
  rewrite freshmax_list_insu; auto.
  rewrite IHs; auto.
Qed.

Lemma freshmax_insu:
  forall m a pi,
       Ile (freshmax_pure_atom a) m ->
       Ile (freshmax_list freshmax_pure_atom pi) m ->
       Ile (freshmax_list freshmax_pure_atom
              (insert_uniq pure_atom_cmp a pi)) m.
Proof.
 intros. rewrite freshmax_list_insu; auto.
 apply var_max_intro'; auto.
Qed.






