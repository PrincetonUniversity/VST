Require Import language.
Require Import msl.msl_direct.
Require Import msl.env.

Import EnvSA EnvSL.

Definition world := (env var adr * env adr adr)%type.

Instance Join_world: Join world := _.
Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Perm_alg world := _.
Instance Canc_world : Perm_alg world := _.
Instance Disj_world : Perm_alg world := _.

Fixpoint den_env {key}{A}{KE: EqDec key} (rho: table key A)  : env key A :=
  match rho with
  | (x,v)::xs => env_set x v (den_env xs)
  | nil => empty_env
  end.

Definition den (s: state) : world := (den_env (fst s), den_env (snd s)).

Definition world_op (P: pred (env var adr)) (Q: pred (env adr adr)) : pred world :=
    fun w => P (fst w) /\ Q (snd w).

Notation "'^stk' e" := (world_op e emp) (at level 30, no associativity): pred.
Notation "'^hp' e" := (world_op emp e) (at level 30, no associativity): pred.

Definition world_op_sepcon:
     forall P P' Q Q',
       (world_op P P' * world_op Q Q' = world_op (P*Q) (P'*Q'))%pred.
Proof.
 repeat intro.
 apply pred_ext.
 intros [s h] [[s1 h1] [[s2 h2] [[? ?] [[? ?] [? ?]]]]]; simpl in *.
 split.
 exists s1; exists s2; repeat split; auto.
 exists h1; exists h2; repeat split; auto.
 intros [s h] [[s1 [s2 [? [? ?]]]] [h1 [h2 [? [? ?]]]]].
 exists (s1,h1); exists (s2,h2); repeat split; auto.
Qed.

Definition eval_var (x: var) (y: adr) : pred world :=
   (EX sh: share, (^stk env_mapsto x sh y) * TT)%pred.

Notation "x '=#' v" := (eval_var x v) (at level 25, no associativity): pred.

Definition defined (x: var) : pred world := (EX v:adr, x =# v)%pred.

Definition subst (x: var) (v: option (pshare * adr)) (P: pred world) : pred world :=
   fun w => P (env_set_sh x v (fst w), snd w).

(*
Definition equal (x y: var) : pred world :=
            fun w => env_get (fst w) x = env_get (fst w) y.
*)

Inductive modvars : command -> var -> Prop :=
| mod_assign: forall x y, modvars (Assign x y) x
| mod_load: forall x y, modvars (Load x y) x
| mod_seq1: forall x c1 c2, modvars c1 x -> modvars (Seq c1 c2) x
| mod_seq2: forall x c1 c2, modvars c2 x -> modvars (Seq c1 c2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall v, P |-- subst x v P.

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.

Definition semax (P: pred world) (c: command) (Q: pred world) : Prop :=
  forall F s,
    (P*F)%pred (den s) -> exists s', exec c s = Some s' /\ (Q*F)%pred (den s').

Lemma env_get_den {A B}{AE: EqDec A}:  forall s (y: A) sh (v: B), env_get (den_env s) y = Some (sh,v) ->
             table_get s y = Some v /\ sh = pfullshare.
Proof.
Admitted.

Lemma eval_var_get: forall s x v, (x =# v)%pred s ->
     exists sh, env_get (fst s) x = Some (sh,v).
Admitted.

Definition own (x: var) : pred world := (^stk (own_var pfullshare x) * TT) %pred.

Lemma env_get_own:
  forall x s, (own x * TT)%pred s -> exists v, env_get (fst s) x = Some (pfullshare, v).
Admitted.

Lemma semax_assign: forall P x y v,
      semax (y =# v && (own x * TT) && subst x (Some(pfullshare, v)) P) (Assign x y) P.
Proof.
  intros.  intros F s H.
  destruct H as [[stk1 hp1] [[stk2 hp2] [? [[[? OWN] ?] ?]]]].
  simpl in *.
  destruct H as [H H']. simpl in H,H'.
  exists (table_set x v (fst s), snd s).
   assert (H0': (y =# v)%pred (den s)).
   admit.  (* easy, need to prove =# extendM *)
   apply eval_var_get in H0'.
   destruct H0' as [sh ?].
  destruct s as [s h]. simpl in *.
  apply env_get_den in H3. destruct H3; subst sh.
  change nat with var in H3. rewrite H3.
  simpl. split; auto.
  unfold subst in H1. simpl in H1.
  unfold den; simpl.
  econstructor; econstructor; repeat split; try apply H1; try apply H2; simpl; auto.
  intro i. specialize (H i).
  destruct (eq_dec i x). subst.  rewrite env_gss. rewrite env_gss_sh.
  apply env_get_own in OWN; destruct OWN as [v' OWN]. simpl in OWN.
  change nat with var in OWN.
  rewrite OWN in H.
  inv H; try pfullshare_join. constructor.
  rewrite env_gso; auto. rewrite env_gso_sh; auto.
Qed.

Lemma semax_load: forall x y p v v0 sh sh',
       semax (^stk env_mapsto x Share.top v0 * ^stk (env_mapsto y sh p) *
                    ^hp env_mapsto p sh' v)
                  (Load x y)
                  (^stk env_mapsto x Share.top v * ^stk (env_mapsto y sh p) *
                    ^hp env_mapsto p sh' v).
Proof.
 intros.
 repeat rewrite world_op_sepcon.
 repeat rewrite sepcon_emp; repeat rewrite emp_sepcon.
 hnf; intros.
 destruct s as [s h].
 exists (table_set x v s, h).
 unfold den in *; simpl in *.
 assert (table_get s y = Some p).
 admit.  (* easy enough *)
 assert (table_get h p = Some v).
 admit.  (* easy enough *)
 rewrite H0. simpl. rewrite H1. simpl. split; auto.
 rewrite <- (emp_sepcon (env_mapsto p sh' v)) in H|-*.
 rewrite <- @world_op_sepcon in H|-*.
 rewrite sepcon_assoc in H|-*.
 destruct H as [[s1 h1] [[s2 h2] [[? ?] [[? ?] ?]]]]; simpl in *.
 exists (env_set x v s1, h1).
 exists (s2,h2).
 repeat split; simpl; auto.
 intro i. specialize (H i). destruct (eq_dec i x).
 subst. repeat rewrite env_gss. apply env_mapsto_get in H3. destruct H3.
 change nat with var in H3; rewrite H3 in H.
 inv H; try pfullshare_join. constructor.
 repeat rewrite env_gso; auto.
 replace (env_set x v s1) with (env_set x v empty_env).
 apply env_mapsto_set.
 clear - H3.
 apply env_ext. extensionality i.
 destruct (eq_dec i x).
 subst; repeat rewrite env_gss. auto.
 subst; repeat rewrite env_gso; auto.
 rewrite env_get_empty.
 symmetry.
 eapply env_mapsto_get_neq; eauto.
Qed.

Lemma semax_store: forall x y p v v0 sh sh',
       semax (^stk env_mapsto x sh p * ^stk (env_mapsto y sh' v) *
                    ^hp env_mapsto p Share.top v0)
                  (Store x y)
                  (^stk env_mapsto x sh p * ^stk (env_mapsto y sh' v) *
                    ^hp env_mapsto p Share.top v).
Proof.
 intros. hnf; intros.
 exists (fst s, table_set p v (snd s)).
 destruct s as [s h].
 simpl.
 assert (table_get s y = Some v).
 admit. (* easy *)
 assert (table_get s x = Some p).
 admit. (* easy *)
 rewrite H0. simpl. rewrite H1. simpl. split; auto.
 rewrite sepcon_assoc in H|-*.
 rewrite <- (sepcon_comm F) in H|-*.
 rewrite <- sepcon_assoc in H|-*.
 destruct H as [[s1 h1] [[s2 h2] [[? ?] [? ?]]]].
 simpl in *.
 exists (s1,h1).
 exists (s2, env_set p v h2).
 split; [|split]; auto.
 split; auto. simpl.
 destruct H4 as [_ ?].
 clear - H2 H4.
 admit. (* straightforward *)
 destruct H4; split; auto.
 simpl in *.
 clear - H5.
 replace (env_set p v h2) with (env_set p v empty_env).
 apply env_mapsto_set.
 apply env_ext. extensionality i.
 destruct (eq_dec i p).
 subst; repeat rewrite env_gss. auto.
 subst; repeat rewrite env_gso; auto.
 rewrite env_get_empty.
 symmetry.
 eapply env_mapsto_get_neq; eauto.
Qed.

Lemma semax_seq: forall P c1 Q c2 R,
  semax P c1 Q -> semax Q c2 R -> semax P (Seq c1 c2) R.
Proof.
 unfold semax; intros.
 destruct (H F s) as [s1 [? ?]]; auto.
 destruct (H0 F s1) as [s2 [? ?]]; auto.
 exists s2; split; auto.
 simpl. rewrite H2; simpl. auto.
Qed.

Lemma frame: forall F P c Q,
    semax P c Q -> semax (P * F) c (Q * F).
Proof.
 repeat intro.
 rewrite sepcon_assoc in H0|-*.
 apply H in H0. auto.
Qed.
