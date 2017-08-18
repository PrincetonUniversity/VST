Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Local Open Scope logic.

Definition compute_funspecs_norepeat (l : list (ident*funspec)) :=
  compute_list_norepet (fst (split l)).

Lemma not_in_funspecs_by_id_i {A B} i (l : list (A * B)) l0 l1 :
  split l = (l0,l1) ->
  ~In i l0 ->
  ~In i (map fst l).
Proof.
  revert i l0 l1.
  induction l as [|[a b] l]; intros a' [|a'' la] [|b' lb] E; simpl in *;
    try destruct (split l); congruence || auto.
  injection E; intros; subst; intuition.
  eapply IHl; eauto.
Qed.

Lemma compute_funspecs_norepeat_e l :
  compute_funspecs_norepeat l = true ->
  funspecs_norepeat l.
Proof.
  intros H; hnf.
  rewrite <-semax_call.fst_split.
  apply compute_list_norepet_e, H.
Qed.
