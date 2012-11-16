Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.

(*Environment typechecking soundness statements*)

Definition tc_te_denote (te: tenviron) (tc: PTree.t (type * bool)) :=
forall id ty b, tc ! id = Some (ty,b) -> exists v, (Map.get te id = Some v /\ typecheck_val v ty = true). 

Definition tc_ve_denote (ve: venviron) (tc: PTree.t type) :=
forall id ty, tc ! id = Some (ty) ->
exists v, Map.get ve id = Some(v,ty).

Definition tc_mode_denote (rho:environ) (Delta:tycontext)  :=
forall id t, (glob_types Delta) ! id = Some t ->
(ve_of rho) id = None \/ exists t,  (var_types Delta) ! id = Some t. 


Definition tc_ge_denote (ge: genviron) (tc: PTree.t global_spec) :=
forall id  t,  tc ! id = Some t -> 
((exists b, exists i, 
(ge id = Some (Vptr b i, globtype t) /\ typecheck_val (Vptr b i) (globtype t) = true))).

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


Lemma typecheck_mode_eqv : forall rho Delta,
same_env rho Delta (all_var_ids Delta) = true <->
tc_mode_denote rho Delta. 
Proof.
intros. split; intros. unfold all_var_ids in H.
intro. intros.
assert (In id  (fst (split (PTree.elements (glob_types Delta))))). 
rewrite In_fst_split. exists t. apply PTree.elements_correct. auto. 

induction (fst (split (PTree.elements (glob_types Delta)))). unfold same_env in *. 

simpl in *. inv H1. 

simpl in H. rewrite andb_true_iff in *. destruct H. 
simpl in H1. destruct H1. subst. unfold same_mode in H. 
remember ((var_types Delta) ! id). destruct o. eauto.
remember ((glob_types Delta) ! id). destruct o. 
remember (ve_of rho id). destruct o; try congruence. auto. congruence.
destruct IHl; auto. 

unfold tc_mode_denote in *. unfold all_var_ids in *. 
assert (forall id, In id  (fst (split (PTree.elements (glob_types Delta)))) ->
    exists t, ((glob_types Delta) ! id) = Some t).
intros. rewrite In_fst_split in H0. destruct H0. 
apply PTree.elements_complete in H0. eauto.

induction  (fst (split (PTree.elements (glob_types Delta)))). 
auto.  simpl in *. rewrite IHl; auto. rewrite andb_true_iff; intuition. 
specialize (H0 a). destruct H0; auto. unfold same_mode.
specialize (H _ _ H0). destruct H. rewrite H. rewrite H0. destruct ((var_types Delta) ! a).
auto. auto. destruct H. rewrite H. auto. 
Qed. 


Lemma typecheck_ve_eqv : forall dv ve,
typecheck_var_environ (PTree.elements dv) ve  = true <->
tc_ve_denote ve dv.
Proof.
intros; split; intros.
unfold tc_ve_denote. intros.   
assert (In (id, ty) (PTree.elements dv)). apply PTree.elements_correct.
auto.
assert (forall t: type, In (id,t) (PTree.elements dv) -> dv ! id = Some t).
intros. apply PTree.elements_complete. auto.
 induction (PTree.elements dv). 
  inv H1. 
  simpl in H. destruct a. simpl in *.
    remember (Map.get ve p). destruct o. 
       destruct p0.
             remember (eqb_type t t0). destruct b0.
             symmetry in Heqb0. apply eqb_type_true in Heqb0. subst.
             destruct H1. inv H1. specialize (H2 ty). intuition; eauto.

             apply IHl; eauto.

             simpl in *; congruence.

       simpl in *. congruence.


 
(*other way now...*)
assert (forall t1 id, In (id,t1) (PTree.elements dv) -> dv ! id = Some t1).
intros. apply PTree.elements_complete. auto.
induction (PTree.elements dv).
  auto.

  simpl in *. destruct a. 
    remember (Map.get ve p). destruct o. 
      destruct p0.
        simpl in *. unfold tc_ve_denote in H.

        assert (forall (t1 : type) (id : positive),
          (p, t) = (id, t1) \/ In (id, t1) l -> dv ! id = Some t1) by auto.
        specialize (H0 t p). intuition. specialize (H _ _ H0).
        destruct H.  rewrite H in Heqo.  inv Heqo.
        rewrite eqb_type_refl. simpl. apply IHl. intros. apply H1. auto.

      simpl. spec IHl. intros. apply H0. auto. unfold tc_ve_denote in H.
          edestruct H. auto. congruence. Qed.
 
Lemma typecheck_ge_eqv : forall dv ge,
typecheck_glob_environ (PTree.elements dv) ge = true <-> tc_ge_denote ge dv.
Proof.
intros.  

split; intros. 
  unfold tc_ge_denote. intros. 
   assert (In (id,t)  (PTree.elements dv)). 
        apply PTree.elements_correct. auto. 
   assert (forall t: global_spec, In (id,t) (PTree.elements dv) -> dv ! id = Some t).
    intros. apply PTree.elements_complete. auto. 
   
   induction (PTree.elements dv). 
    inv H1. 
    simpl in H1. destruct a. simpl in H. remember (ge p). destruct o; try congruence.
    destruct p0. destruct v; try congruence. remember (eqb_type (globtype g) t0).
    destruct b0; simpl in H; try congruence. 
    symmetry in Heqb0. apply eqb_type_true in Heqb0. subst. 
    assert (typecheck_glob_environ l ge = true).
      simpl in H.  if_tac in H; try congruence. 
    destruct H1.  
      inv H1. rewrite <- Heqo. eexists;  eexists. split. auto. 
      remember (globtype t). destruct t0; simpl in H; try congruence; auto. 
    destruct IHl; auto. intros. apply H2. simpl; auto.
    destruct H4. destruct H4. eauto. 

   unfold tc_ge_denote in *. 
   assert (forall t1 id, In (id,t1) (PTree.elements dv) -> dv ! id = Some t1).
    intros. apply PTree.elements_complete. auto.
   induction (PTree.elements dv). 
     auto. 
     
     simpl. destruct a. rewrite IHl; auto. 
     clear IHl. unfold Map.get in H. edestruct H.  apply H0. simpl. left.
     auto. destruct H1 as [i [? ?]]. rewrite H1. rewrite eqb_type_refl.
     simpl. destruct (globtype g); simpl in H2; try congruence; auto. 

     intros; auto. 
     apply H0; auto. simpl; auto. 
Qed. 
     
    
Lemma typecheck_te_eqv : forall t te, typecheck_temp_environ (PTree.elements t) te = true
<-> tc_te_denote te t.
Proof. intros.
split. intros. unfold tc_te_denote. intros.
assert (In (id, (ty,b)) (PTree.elements t)).
apply PTree.elements_correct. auto.
induction (PTree.elements t). simpl in *.

destruct H1. 

simpl in *. destruct a. destruct p0.
remember (Map.get te p). destruct o; try solve [inv H].
remember (typecheck_val v t0). destruct b1; try congruence.
destruct H1; [ inv H1 | ]; eauto. 

intros. unfold tc_te_denote in *. 
assert (forall t1 id, In (id,t1) (PTree.elements t) -> t ! id = Some t1).
intros. apply PTree.elements_complete. auto.
induction (PTree.elements t). auto.

simpl in *. 
assert (forall (t1 : type * bool) (id : positive),
     In (id, t1) (a :: l) -> t ! id = Some t1) by auto.
destruct a. destruct p0.
specialize (H0 (t0, b) p). spec H0; auto. 
specialize (H p t0 b). spec H; auto. destruct H.
destruct H. rewrite H. rewrite H2. apply IHl. intros.
simpl in H1. specialize (H1 t1 id). intuition.

Qed.


Lemma typecheck_environ_sound : forall ge te ve Delta,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
tc_te_denote te (temp_types Delta) /\ tc_ve_denote ve (var_types Delta) /\ 
tc_ge_denote ge (glob_types Delta).
Proof.
intros.
unfold typecheck_environ in *. destruct Delta. destruct p.

unfold temp_types in *. simpl in *. repeat rewrite andb_true_iff in *. intuition.
destruct p. simpl in *. apply typecheck_te_eqv; auto.

apply typecheck_ve_eqv; auto.

apply typecheck_ge_eqv; auto.

Qed.


Lemma join_te_denote : forall te1 te2 id b t1,
(join_te te1 te2) ! id = Some (t1,b) ->
(exists b1, te1 ! id = Some (t1, orb b b1)) /\ (exists b2, te2 ! id = Some (t1, orb b b2)).
Proof.
intros.
 
unfold join_te in *. rewrite PTree.fold_spec in *.
rewrite  <- fold_left_rev_right in *.

assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto.

assert (NOREP := PTree.elements_keys_norepet (te1)).

induction (rev (PTree.elements te1)). simpl in *.
rewrite PTree.gempty in *. congruence.

simpl in *. destruct a. destruct p0. simpl in *.
remember (te2 ! p). destruct o. destruct p0.
destruct (eq_dec t t0). subst. rewrite PTree.gsspec in *.
destruct (peq id p). subst. specialize (H0 (t0,b0)). inv H.

remember (andb b0 b1). destruct b. symmetry in Heqb. 
rewrite andb_true_iff in *. destruct Heqb; subst. 
split; exists false; intuition; eauto.

symmetry in Heqb.
rewrite andb_false_iff in *. destruct Heqb; subst. intuition; eauto.

intuition; eauto.

apply IHl; eauto.

apply IHl; eauto.
apply IHl; eauto.
Qed.


Lemma same_env_ignores_t_ret : forall e0 e1 e2 e3 e4 e5 rho,
same_env rho (e1,e2,e3,e4) (all_var_ids (e1,e2,e3,e4)) =
 same_env rho (e0,e2,e5,e4) (all_var_ids (e0,e2,e5,e4)).  
intros. unfold all_var_ids. simpl. induction (fst (split (PTree.elements e4))). 
auto. simpl. rewrite IHl.  auto. Qed.


Lemma same_env_ignores_te : forall te te1 ve ge Delta,
same_env (mkEnviron ge ve te) Delta (all_var_ids Delta) =
same_env (mkEnviron ge ve te1) Delta (all_var_ids Delta). 
intros. induction (all_var_ids Delta). auto.
simpl. rewrite IHl. auto.
Qed.

Lemma typecheck_environ_join1:
  forall rho Delta1 Delta2, 
        var_types Delta1 = var_types Delta2 ->
        glob_types Delta1 = glob_types Delta2 ->
    
        typecheck_environ rho Delta1 = true ->
        typecheck_environ rho (join_tycon Delta1 Delta2) = true.
Proof. intros.
 unfold typecheck_environ in *. repeat rewrite andb_true_iff in *.
destruct H1 as [[[? ?] ?] ?]. repeat split. clear H2 H3 H4.  
destruct rho. simpl in *. 
rewrite  typecheck_te_eqv in *.  
unfold tc_te_denote in *. intros. unfold temp_types in *.
destruct Delta2. destruct p. destruct p. simpl in *. destruct Delta1.
destruct p. destruct p. simpl in *. apply join_te_denote in H2.
destruct H2. destruct H2. destruct H3. 
eapply H1. eauto.  
unfold join_tycon. destruct Delta2. 
destruct p. destruct p. destruct Delta1. destruct p. destruct p.
unfold join_te. unfold var_types in *.  simpl in *. subst. auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta1.
repeat destruct p. unfold glob_types in *; simpl in *; subst; auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta1.
repeat destruct p. erewrite same_env_ignores_t_ret. eauto. 
Qed. 


Lemma typecheck_environ_join2:
  forall rho Delta1 Delta2, 
        var_types Delta1 = var_types Delta2 ->
        glob_types Delta1 = glob_types Delta2 ->
        typecheck_environ rho Delta2 = true ->
        typecheck_environ rho (join_tycon Delta1 Delta2) = true.
Proof.
intros.
 unfold typecheck_environ in *. repeat rewrite andb_true_iff in *. intuition.
destruct rho. simpl in *. 
rewrite  typecheck_te_eqv in *. clear H4 H5. 
unfold tc_te_denote in *. intros. unfold temp_types in *.
destruct Delta2. destruct p. destruct p. simpl in *. destruct Delta1.
destruct p. destruct p. simpl in *. apply join_te_denote in H1.
destruct H1. destruct H1. destruct H4. 
eauto. 
unfold join_tycon. destruct Delta2. 
destruct p. destruct p. destruct Delta1. destruct p. destruct p.
unfold join_te. unfold var_types in *.  simpl in *. subst. auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta1.
repeat destruct p. unfold glob_types in *; simpl in *; subst; auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta1.
repeat destruct p. unfold var_types in *. simpl in H. subst. unfold glob_types in *.
simpl in *. subst.  erewrite same_env_ignores_t_ret. eauto.

Qed.

Lemma typecheck_val_ptr_lemma:
   forall rho Delta id t a init,
   typecheck_environ rho Delta = true ->
   (temp_types Delta) ! id =  Some (Tpointer t a, init) ->
   strict_bool_val (eval_id id rho) (Tpointer t a) = Some true ->
   typecheck_val (eval_id id rho) (Tpointer t a) = true.
Proof. 
intros. unfold bool_val in *. unfold typecheck_val.
unfold eval_id. destruct rho.  apply typecheck_environ_sound in H.
destruct H as [? _]. unfold tc_te_denote in *.
edestruct H; eauto. destruct H2.  simpl.  rewrite H2. destruct x; simpl in *; congruence.
Qed. 


Lemma typecheck_environ_put_te : forall ge te ve Delta id v ,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
(forall t , ((temp_types Delta) ! id = Some t ->
  (typecheck_val v (fst t)) = true)) ->
typecheck_environ (mkEnviron ge ve (Map.set id v te)) Delta = true.
Proof. 
intros. unfold typecheck_environ in *. simpl in *. repeat rewrite andb_true_iff in *.
intuition. clear H2 H3. destruct Delta. destruct p. 
destruct p. unfold temp_types in *; simpl in *.
rewrite typecheck_te_eqv in *. unfold tc_te_denote in *.
intros. edestruct H1; eauto. destruct H2. rewrite Map.gsspec.
if_tac. subst. exists v; intuition. specialize (H0 (ty, b)). apply H0. auto. 

simpl in *. exists x. intuition.

erewrite same_env_ignores_te. eauto. 


Qed.


Lemma typecheck_environ_put_te' : forall ge te ve Delta id v ,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
(forall t , ((temp_types Delta) ! id = Some t ->
  (typecheck_val v (fst t)) = true)) ->
typecheck_environ (mkEnviron ge ve (Map.set id v te)) (initialized id Delta) = true.
Proof.
intros. 
assert (typecheck_environ (mkEnviron ge ve (Map.set id v te)) Delta = true).
apply typecheck_environ_put_te; auto.

unfold typecheck_environ in *. simpl in *. repeat rewrite andb_true_iff in *. 
destruct H as [[[? ?] ?] ?]. destruct H1 as [[[? ?] ?] ?]. 
repeat split. 


destruct Delta. destruct p. destruct p.  unfold initialized. unfold temp_types in *.
clear H2 H3 H4 H5 H6 H7. simpl in *. 
rewrite typecheck_te_eqv in *. unfold tc_te_denote in *. intros. remember (t1 ! id).
destruct o; try congruence; auto. destruct p. simpl in *. rewrite PTree.gsspec in *.
if_tac in H2. inv H2. eauto. eauto. eauto.


unfold var_types in *. destruct Delta. destruct p. destruct p. simpl in *.
unfold initialized. simpl. destruct ((temp_types (t1, t2, t0, t))!id).
destruct p. simpl. unfold var_types. auto. auto.

destruct Delta. destruct p. destruct p. simpl in *. unfold initialized.
destruct ((temp_types (t1, t2, t0, t)) ! id); try destruct p; simpl in *; auto.

erewrite same_env_ignores_te; eauto. unfold initialized.
destruct Delta. simpl in *.  destruct p. destruct p. 
unfold var_types, temp_types in *. simpl in *. 
destruct (t1 ! id); try destruct p;
try erewrite same_env_ignores_t_ret;  eauto.

Qed. 

Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.