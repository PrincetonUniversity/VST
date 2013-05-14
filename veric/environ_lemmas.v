Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.


Lemma eqb_type_eq: forall t1 t2, eqb_type t1 t2 = proj_sumbool (type_eq t1 t2).
Proof.
intros.
case_eq (eqb_type t1 t2); intros.
apply eqb_type_true in H; subst; simpl; auto.
rewrite proj_sumbool_is_true; auto.
destruct (type_eq t1 t2); simpl; subst.
rewrite eqb_type_refl in H; auto.
auto. 
Qed.

Lemma In_fst_split : forall A B i (l: list (A * B)), In i (fst (split l)) <-> exists b : B, In (i,b) l.  
Proof. 
intros. split; intros. induction l. inv H. simpl in H. remember (split l). destruct p. destruct a. 
simpl in *. destruct H. subst. clear IHl. eauto.
destruct IHl. auto. exists x. auto. 

induction l. destruct H. inv H. simpl in *. destruct H. destruct H. destruct a. inv H.
clear IHl. destruct (split l). simpl. auto. destruct (split l). destruct a. simpl. 
right. apply IHl. eauto. 
Qed.

Lemma eqb_type_false: forall a b, eqb_type a b = false <-> a<>b.
Admitted. 

Lemma join_te_denote : forall te1 te2 id b t1,
(join_te te1 te2) ! id = Some (t1, b) ->
  (exists b1, te1 ! id = Some (t1, b || b1)) /\ 
  match te2 ! id with Some (t2,b2) => b = b && b2 | None => True end.
Proof.
intros.
 
unfold join_te in *. rewrite PTree.fold_spec in *.
rewrite  <- fold_left_rev_right in *.

assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto.

assert (NOREP := PTree.elements_keys_norepet (te1)).

induction (rev (PTree.elements te1)). simpl in *.
rewrite PTree.gempty in *. congruence.

simpl in *. destruct a as [p [t b0]]. simpl in *.
destruct (te2 ! p) eqn:?.  destruct p0.
rewrite PTree.gsspec in H.
if_tac in H. subst. specialize (H0 (t,b0)). inv H.
 spec H0; auto.
 split. exists b0. rewrite H0. repeat f_equal. destruct b0,b1; simpl; auto.
 rewrite Heqo. destruct b0; simpl; auto. destruct b1; simpl; auto.

 auto. auto.
Qed. 

Lemma typecheck_environ_join1:
  forall rho Delta1 Delta2, 
        var_types Delta1 = var_types Delta2 ->
        glob_types Delta1 = glob_types Delta2 ->
    
        typecheck_environ Delta1 rho ->
        typecheck_environ (join_tycon Delta1 Delta2) rho.
Proof. intros.
 unfold typecheck_environ in *. 
destruct H1 as [? [? [? ?]]]. repeat split. clear H2 H3 H4.  
destruct rho. simpl in *. 
unfold typecheck_temp_environ in *. intros. unfold temp_types in *.
destruct Delta2. destruct p. destruct p. simpl in *. destruct Delta1.
destruct p. destruct p. simpl in *. apply join_te_denote in H2.
destruct H2. destruct H2.
edestruct H1. eauto. destruct H4. destruct H5. 
destruct b; intuition. simpl in *. eauto. eauto. 
unfold join_tycon. destruct Delta2. 
destruct p. destruct p. destruct Delta1. destruct p. destruct p.
unfold join_te. unfold var_types in *.  simpl in *. subst. auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta1.
repeat destruct p. unfold glob_types in *; simpl in *; subst; auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta1.
repeat destruct p. simpl in *. subst. unfold same_env in *. 
simpl in *. intros. specialize (H4 id t3 H0). auto.  
Qed. 

Definition tycontext_evolve (Delta Delta' : tycontext) :=
 (forall id, match (temp_types Delta) ! id, (temp_types Delta') ! id with
                | Some (t,b), Some (t',b') => t=t' /\ (orb (negb b) b' = true)
                | None, None => True
                | _, _ => False
               end)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, (glob_types Delta) ! id = (glob_types Delta') ! id).

Lemma initialized_tycontext_evolve:
  forall i Delta, tycontext_evolve Delta (initialized i Delta).
Proof.
intros i [[[A B] C] D].
 unfold initialized;
 split; [| split; [|split]]; intros; unfold temp_types, var_types, glob_types, ret_type;
 simpl.
 destruct (A ! id) as [[? ?]|] eqn:?; simpl.
 destruct (A!i) as [[? ?]|] eqn:?; simpl.
 destruct (eq_dec i id). subst. rewrite PTree.gss. inversion2 Heqo Heqo0.
 split; auto. destruct b; reflexivity.
 rewrite PTree.gso by auto. rewrite Heqo. split; auto.
 destruct b; simpl; auto. rewrite Heqo. destruct b; simpl; auto.
 destruct (A!i) as [[? ?]|] eqn:?; simpl.
 destruct (eq_dec i id). subst. congruence.
 rewrite PTree.gso by auto. rewrite Heqo. auto.
 rewrite Heqo. auto.
 destruct (A!i) as [[? ?]|]; reflexivity.
 destruct (A!i) as [[? ?]|]; reflexivity.
 destruct (A!i) as [[? ?]|]; reflexivity.
Qed.

Lemma tycontext_evolve_trans: forall Delta1 Delta2 Delta3,
   tycontext_evolve Delta1 Delta2 ->
   tycontext_evolve Delta2 Delta3 ->
   tycontext_evolve Delta1 Delta3.
Proof.
intros [[[A B] C] D] [[[A1 B1] C1] D1] [[[A2 B2] C2] D2]
  [S1 [S2 [S3 S4]]]  [T1 [T2 [T3 T4]]];
 split; [| split; [|split]];
 unfold temp_types,var_types, ret_type in *; simpl in *;
 try congruence.
 clear - S1 T1.
 intro id; specialize (S1 id); specialize (T1 id).
 destruct (A!id) as [[? ?]|].
 destruct (A1!id) as [[? ?]|]; [ | contradiction]. destruct S1; subst t0.
 destruct (A2!id) as [[? ?]|]; [ | contradiction]. destruct T1; subst t0.
 split; auto. destruct b; inv H0; auto. destruct b0; inv H; simpl in H1. auto.
 destruct (A1!id) as [[? ?]|]; [ contradiction| ].
 auto.
Qed.

Lemma typecheck_environ_join2:
  forall rho Delta Delta1 Delta2, 
        tycontext_evolve Delta Delta1 ->
        tycontext_evolve Delta Delta2 ->
        typecheck_environ Delta2 rho ->
        typecheck_environ (join_tycon Delta1 Delta2) rho.
Proof.
intros [ge ve te] [[[A B] C] D] [[[A1 B1] C1] D1] [[[A2 B2] C2] D2]
  [S1 [S2 [S3 S4]]]  [T1 [T2 [T3 T4]]]
  [U1 [U2 [U3 U4]]];
 split; [| split; [|split]];
 unfold temp_types,var_types, ret_type in *; simpl in *;
 subst C1 C2.
* clear - S1 T1 U1; unfold typecheck_temp_environ in *.
  intros.
  specialize (S1 id); specialize (T1 id); specialize (U1 id).
  apply join_te_denote in H. destruct H as [[b1 ?] ?].
  rewrite H in *. clear A1 H.
 destruct (A ! id) as [[? ?]|]; [ | contradiction].
 destruct S1; subst ty.
 destruct (A2!id) as [[? ?]|]; [ | contradiction].
 destruct T1; subst t0.
 destruct (U1 _ _ (eq_refl _)) as [v [? ?]].
 exists v; split; auto.
 destruct H3; auto; left.
 unfold is_true.
 destruct b; auto. destruct b2; inv H0. rewrite H3; auto.
* unfold typecheck_var_environ in *; intros.
  rewrite <- S2 in H. rewrite T2 in H. apply U2 in H. auto.
* unfold typecheck_glob_environ in *; intros.
  rewrite <- S4 in H. rewrite T4 in H. apply U3 in H. auto.
* unfold same_env in *; intros.
 unfold glob_types in *. simpl in *.
 rewrite <- S4 in H. rewrite T4 in H. apply U4 in H.
 destruct H; auto; right.
 destruct H as [t1 ?]. exists t1.
 unfold var_types in *; simpl in *; auto. congruence.
Qed.

Lemma typecheck_val_ptr_lemma:
   forall rho Delta id t a,
   typecheck_environ Delta rho ->
   denote_tc_assert (typecheck_expr Delta (Etempvar id (Tpointer t a))) rho ->
   (*(temp_types Delta) ! id =  Some (Tpointer t a, init) ->*) (*modified for init changes*)
   strict_bool_val (eval_id id rho) (Tpointer t a) = Some true ->
   typecheck_val (eval_id id rho) (Tpointer t a) = true.
Proof. 
intros. unfold strict_bool_val in *. unfold typecheck_val.
simpl in H0. if_tac in H0; simpl in *; intuition.
remember ((temp_types Delta) ! id). destruct o; simpl in *; intuition.
destruct p. simpl in *.  
unfold eval_id. destruct rho.  
destruct H as [? _]. unfold typecheck_temp_environ in *.
edestruct H; eauto. destruct H2.  simpl.  simpl in H2. rewrite H2.
simpl.
destruct H3.
destruct b; simpl in *; try congruence.
remember (is_pointer_type t0). repeat (if_tac in H0; intuition). 
simpl in H0. unfold denote_tc_initialized in *. destruct H0. 
destruct H0. simpl in H0.  rewrite H0 in H2. inv H2. 
destruct x; simpl in *; try congruence. 
destruct x; simpl in *; try congruence. 
destruct t0; simpl in *; try congruence; intuition.
destruct t0; simpl in *; try congruence; intuition.
destruct t0; simpl in *; try congruence; intuition.
Qed. 


Lemma typecheck_environ_put_te : forall ge te ve Delta id v ,
typecheck_environ  Delta (mkEnviron ge ve te) ->
(forall t , ((temp_types Delta) ! id = Some t ->
  (typecheck_val v (fst t)) = true)) ->
typecheck_environ  Delta (mkEnviron ge ve (Map.set id v te)).
Proof. 
intros. unfold typecheck_environ in *. simpl in *. 
intuition. clear H H2 H4. destruct Delta. destruct p. 
destruct p. unfold temp_types in *; simpl in *.
unfold typecheck_temp_environ. 
intros. edestruct H1; eauto. destruct H2. rewrite Map.gsspec.
if_tac. subst. exists v; intuition. specialize (H0 (ty,b)). 
simpl in *. right. 
apply H0. auto. 

simpl in *. exists x. intuition.


Qed.


Lemma typecheck_environ_put_te' : forall ge te ve Delta id v ,
typecheck_environ  Delta (mkEnviron ge ve te) ->
(forall t , ((temp_types Delta) ! id = Some t ->
  (typecheck_val v (fst t)) = true)) ->
typecheck_environ (initialized id Delta) (mkEnviron ge ve (Map.set id v te)).
Proof.
intros. 
assert (typecheck_environ Delta (mkEnviron ge ve (Map.set id v te))).
apply typecheck_environ_put_te; auto.

unfold typecheck_environ in *. simpl in *.
intuition.  

destruct Delta. destruct p. destruct p.  unfold initialized. unfold temp_types in *.
clear H1 H3 H4 H5 H8 H7. simpl in *. 
unfold typecheck_temp_environ in *. 
intros. remember (t1 ! id).
destruct o; try congruence; auto. destruct p. simpl in *.
rewrite PTree.gsspec in *.
if_tac in H1. inv H1. 
edestruct H; eauto. destruct H1. destruct H3; eauto. exists v.
split. rewrite Map.gsspec in *. unfold ident_eq in *. rewrite peq_true in *. auto. 
specialize (H0 (ty, b0)). right.  apply H0. auto. 
eauto.


unfold var_types in *. destruct Delta. destruct p. destruct p. simpl in *.
unfold initialized. simpl. destruct ((temp_types (t1, t2, t0, t))!id).
destruct p. simpl. unfold var_types. auto. auto.

destruct Delta. destruct p. destruct p. simpl in *. unfold initialized.
destruct ((temp_types (t1, t2, t0, t)) ! id); try destruct p; simpl in *; auto.

unfold same_env in *. 
intros. simpl in *. unfold initialized in *. 
destruct Delta. simpl in *. destruct p. destruct p. 
unfold var_types, temp_types in *. simpl in *. 
destruct (t2 ! id); try destruct p; eauto. 
Qed. 

Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.
