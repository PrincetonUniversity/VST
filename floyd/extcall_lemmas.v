Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Local Open Scope logic.

Definition compute_funspecs_norepeat (l : list (ident*funspec)) :=
  compute_list_norepet (fst (split l)).

Lemma not_in_funspecs_by_id_i i f l l0 l1 :
  split l = (l0,l1) -> 
  ~In i l0 -> 
  ~in_funspecs_by_id (i,f) l.
Proof.
revert l0 l1 i f. induction l. simpl; auto. intros. intros Contra.
inv Contra. 
+ simpl in H1. subst. simpl in H. 
  destruct a. destruct (split l). simpl in *. inv H.
  apply H0. left; auto.
+ destruct a. simpl in *. destruct (split l). simpl in *. inv H.
  cut (~In i l2). intro. eapply IHl; eauto. 
  intros H. apply H0. right; auto.
Qed.

Lemma compute_funspecs_norepeat_e l : 
  compute_funspecs_norepeat l = true -> 
  funspecs_norepeat l.
Proof.
intros H. unfold compute_funspecs_norepeat in H.
revert H; induction l; simpl; auto.
destruct a; revert IHl; case_eq (split l); simpl in *; intros.
revert H0; case_eq (id_in_list i l0); intros. congruence.
split; auto.
eapply not_in_funspecs_by_id_i; eauto.
apply id_in_list_false in H0; auto.
Qed.
