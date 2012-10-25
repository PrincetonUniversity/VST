Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.


(*Definitions of some environments*)
Definition mkEnviron' (ge: Clight.genv) (ve: venviron) (te: tenviron) :=
  mkEnviron (filter_genv ge) ve te.

Definition empty_genv := (Globalenvs.Genv.empty_genv fundef type).
Definition empty_tenv := PTree.empty val.

Definition empty_environ : environ :=
mkEnviron (filter_genv empty_genv) (Map.empty _) (Map.empty _).

Definition Delta1 : tycontext := (PTree.set 1%positive (type_int32s, false) 
                                 (PTree.empty (type * bool)),
                                 PTree.empty type, Tvoid,PTree.empty _).

Lemma Zlt_bool_rev: forall x y, Zlt_bool x y = Zgt_bool y x.
Proof.
intros. pose proof (Zlt_cases x y). pose proof (Zgt_cases y x).
destruct (Zlt_bool x y); destruct (Zgt_bool y x); auto;
elimtype False; omega.
Qed.

Lemma Zle_bool_rev: forall x y, Zle_bool x y = Zge_bool y x.
Proof.
intros. pose proof (Zle_cases x y). pose proof (Zge_cases y x).
destruct (Zle_bool x y); destruct (Zge_bool y x); auto;
elimtype False; omega.
Qed.

Lemma Zlt_bool_opp: forall x y, Zlt_bool x y = negb (Zge_bool x y).
Proof.
intros. pose proof (Zlt_cases x y). pose proof (Zge_cases x y).
destruct (Zlt_bool x y); destruct (Zge_bool x y); auto.
elimtype False; omega.
Qed.

Lemma Zgt_bool_opp: forall x y, Zgt_bool x y = negb (Zle_bool x y).
Proof.
intros. pose proof (Zgt_cases x y). pose proof (Zle_cases x y).
destruct (Zgt_bool x y); destruct (Zle_bool x y); auto.
elimtype False; omega.
Qed.


(*Simplification soundness*)
Lemma tc_assert_simpl_sound : forall asn rho, 
denote_tc_assert asn rho -> denote_tc_assert (tc_assert_simpl asn) rho.
Proof.
intros. induction asn; simpl; auto.

simpl in *. intuition.
destruct H.
remember (tc_assert_simpl asn1).
remember (tc_assert_simpl asn2).
 destruct t; destruct t0; simpl in *; unfold lift0,lift1,lift2 in *; auto.

destruct e; auto. simpl in *.
 unfold lift0,lift1,lift2, denote_tc_nonzero in *.
destruct (Int.eq i Int.zero); intuition.

destruct e; auto. simpl in *. unfold lift0,lift1,lift2, denote_tc_igt in *.
simpl in *. destruct (Int.ltu i0 i); hnf in H|-*; intuition.

destruct e; auto. simpl in *. unfold lift0,lift1,lift2, denote_tc_Zge in *.
simpl in *. destruct (Float.Zoffloat f); intuition. hnf in H|-*.
rewrite Zle_bool_rev. rewrite H. hnf; auto.

destruct e; auto. simpl in *. unfold lift0,lift1,lift2, denote_tc_Zge in *.
simpl in *. destruct (Float.Zoffloat f); intuition. hnf in H|-*.
rewrite H. hnf; auto.
Qed.

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

(*((exists v, (Map.get ve  id = Some(v, ty))) \/
((exists b, exists i, 
(ge id = Some (Vptr b i, ty) /\ typecheck_val (Vptr b i) ty = true)
 /\ (exists v, (Map.get ve id = Some(v, ty)))) \/
((exists b, exists i, 
(ge id = Some (Vptr b i, ty) /\ typecheck_val (Vptr b i) ty = true)
 /\ (Map.get ve  id = None)))))
.*)

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



(*Lemma typecheck_vl_eqv : forall vl ve, 
typecheck_non_var_list vl ve = true <->
tc_vl_denote ve vl.
Proof.
intros. split; intros; unfold tc_vl_denote. intros.

unfold typecheck_non_var_list in *. 
rewrite forallb_forall in H.
induction vl.

inv H0.

simpl in H0. destruct H0. subst. simpl in *. specialize (H id).
intuition. destruct (Map.get ve id); try congruence; auto.
apply IHvl; auto. intros. simpl in H. specialize (H x). intuition.

unfold tc_vl_denote in *. unfold typecheck_non_var_list. rewrite forallb_forall.
intros. specialize (H x). intuition. rewrite H1. auto.
Qed.
*)

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
congruence.

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
simpl in *.  (*SDLFKJSDFLKJ:DSKLGJS:LDKJ:GDLkj check use before I hack at this mroe*)
Admitted.

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
intuition. inv H2. exists v; auto. 

intros. unfold tc_te_denote in *. 
assert (forall t1 id, In (id,t1) (PTree.elements t) -> t ! id = Some t1).
intros. apply PTree.elements_complete. auto.
induction (PTree.elements t). auto.

simpl in *. 
assert (forall (t1 : type * bool) (id : positive),
     In (id, t1) (a :: l) -> t ! id = Some t1) by auto.
destruct a. destruct p0.
specialize (H0 (t0, b) p). intuition. clear H3.
specialize (H p t0 b). intuition. destruct H2.
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


(*Lemmas about soundness of environment join*)
(*
Lemma join_ve_denote : forall ve1 ve2 id v1,
(join_ve ve1 ve2) ! id = Some (v1) ->
ve1 ! id = Some (v1) /\ ve2 ! id = Some (v1).
Proof.
intros. unfold join_ve in *.

rewrite PTree.fold_spec in *.
rewrite  <- fold_left_rev_right in *.

assert (forall t : type, In (id, t) (rev (PTree.elements ve1)) -> ve1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto.

assert (NOREP := PTree.elements_keys_norepet (ve1)).

induction (rev (PTree.elements ve1)). simpl in H. rewrite PTree.gempty in *.
congruence.

destruct a. simpl in H. remember (ve2 ! p). destruct o. simpl in *.
if_tac in H. subst. rewrite PTree.gsspec in H. if_tac in H. subst.
specialize (H0 t0). inv H. intuition.

apply IHl; eauto.
apply IHl; eauto.
apply IHl; eauto. intros. apply H0. simpl. eauto.
Qed.
*)

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

(*
Lemma join_vl_denote :  forall vl1 vl2 id,
In id (join_ve_list vl1 vl2) -> In id vl1 /\ In id vl2.
Proof.
intros. intros.
induction vl1. simpl in *. inv H. simpl in *. if_tac in H. simpl in *; intuition.
subst; auto. intuition.

Qed.
*)

(*Lemma join_ve_same : forall ve,
join_ve ve ve = ve. *)


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
 unfold typecheck_environ in *. repeat rewrite andb_true_iff in *. intuition.
destruct rho. simpl in *. 
rewrite  typecheck_te_eqv in *. clear H3 H4 H5. 
unfold tc_te_denote in *. intros. unfold temp_types in *.
destruct Delta2. destruct p. destruct p. simpl in *. destruct Delta0.
destruct p. destruct p. simpl in *. apply join_te_denote in H1.
destruct H1. destruct H1. destruct H3. 
eapply H2. eauto.  
unfold join_tycon. destruct Delta2. 
destruct p. destruct p. destruct Delta0. destruct p. destruct p.
unfold join_te. unfold var_types in *.  simpl in *. subst. auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta0.
repeat destruct p. unfold glob_types in *; simpl in *; subst; auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta0.
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
destruct Delta2. destruct p. destruct p. simpl in *. destruct Delta0.
destruct p. destruct p. simpl in *. apply join_te_denote in H1.
destruct H1. destruct H1. destruct H4. 
eauto. 
unfold join_tycon. destruct Delta2. 
destruct p. destruct p. destruct Delta0. destruct p. destruct p.
unfold join_te. unfold var_types in *.  simpl in *. subst. auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta0.
repeat destruct p. unfold glob_types in *; simpl in *; subst; auto. 

unfold join_tycon. destruct Delta2. destruct p. destruct p. destruct Delta0.
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

unfold typecheck_environ in *. simpl in *. repeat rewrite andb_true_iff in *. intuition.

destruct Delta. destruct p. destruct p.  unfold initialized. unfold temp_types in *.
clear H4 H3 H5 H6 H7 H8. simpl in *. 
rewrite typecheck_te_eqv in *. unfold tc_te_denote in *. intros. remember (t1 ! id).
destruct o; try congruence; auto. destruct p. simpl in *. rewrite PTree.gsspec in H2.
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

Ltac of_bool_destruct :=
match goal with
  | [ |- context[Val.of_bool ?X] ] => destruct X
end.


Lemma classify_add_int_cases_both : forall i1 s1 a1 i2 s2 a2,
exists s3,
classify_add (Tint i1 s1 a1) (Tint i2 s2 a2) 
= add_case_ii s3.
Proof.
intros; destruct i1; destruct s1; destruct i2; destruct s2; eexists;  
unfold classify_add; simpl; eauto.
Qed.

Lemma undef_not_typecheck : forall t, typecheck_val Vundef t = false.
intros.
destruct t; auto.
Qed.

Ltac st:= simpl in *.

Lemma is_true_true : forall b, is_true b -> b = true.
Proof.
auto.
Qed.

Ltac tc_assert_ext := 
repeat match goal with
| [H : _ /\ _ |- _] => destruct H
end.

Ltac revert_all := repeat match goal with
| [H: _ |- _] => revert H
end.

Lemma orb_if : forall {D} b c (d:D) (e:D), (if (b || c) then d else e) = if b then d else if c then d else e.
intros.
remember (b || c). destruct b0; auto. symmetry in Heqb0. rewrite orb_true_iff in Heqb0.
intuition; subst; auto. destruct b; auto. symmetry in Heqb0; rewrite orb_false_iff in Heqb0.
intuition; subst; auto.
Qed.

Lemma andb_if : forall {D} b c (d:D) (e:D), (if (b && c) then d else e) = if b then (if c then d else e) else e.
Proof.
intros.
remember (b&&c). destruct b0; symmetry in Heqb0; try rewrite andb_true_iff in *; try rewrite andb_false_iff in *; if_tac; auto; intuition;
destruct c; auto; intuition.
Qed.


(*Typechecking soundness*)

Lemma eval_lvalue_ptr : forall rho e (Delta: tycontext) te ve ge,
mkEnviron ge ve te = rho -> 
tc_ve_denote ve (var_types Delta) -> 
tc_ge_denote ge (glob_types Delta) ->
denote_tc_assert (typecheck_lvalue Delta e) rho ->
eval_lvalue e rho = Vundef \/ exists base, exists ofs, eval_lvalue e rho  = Vptr base ofs.
Proof. 
intros.
induction e; eauto.
simpl. unfold eval_var. 
remember (Map.get (ve_of rho) i). destruct o; try rewrite eqb_type_eq; intuition;
try destruct p; try rewrite eqb_type_eq; simpl; try remember (type_eq t t0); try destruct s;
simpl; try remember (negb (type_is_volatile t0));try destruct b0; auto;
try solve[right; eauto].
remember (ge_of rho i); try rewrite eqb_type_eq; simpl.
destruct o; try rewrite eqb_type_eq; simpl; eauto.
destruct p; try rewrite eqb_type_eq; simpl; eauto.
if_tac; eauto.
unfold tc_ve_denote in *. simpl in H2.
unfold get_var_type in *. 
remember ((var_types Delta) ! i).
destruct o. subst. simpl in H2.
unfold lift2 in *.
try rewrite eqb_type_eq in *; simpl in *; intuition.
symmetry in Heqo1.
specialize (H0 i t1 Heqo1).
destruct H0. congruence.
remember ((glob_types Delta) ! i). destruct o; simpl in *; try congruence. 
unfold lift2 in *. right. unfold tc_ge_denote in H1.
symmetry in Heqo2. 
specialize (H1 _ _ Heqo2). destruct H1 as [b [i0 [? ?]]].
rewrite <- H in *.  simpl ge_of in Heqo0. rewrite H1 in *.
inv Heqo0. eauto. inv H2. 



simpl in *. intuition. unfold lift1,lift2,lift0,force_ptr in *. 
destruct (eval_expr e rho); eauto.

simpl in *. unfold lift1,lift0,lift2 in *. intuition.
unfold eval_field. unfold eval_struct_field.
destruct (eval_lvalue e rho); eauto; intuition;
destruct (typeof e); try congruence; auto.
destruct (field_offset i f); eauto.
unfold eval_field. unfold eval_struct_field.
destruct (eval_lvalue e rho); eauto; intuition;
destruct (typeof e); try congruence; auto;
try destruct (field_offset i f); eauto.
try destruct (field_offset i f0); eauto.
Qed. 

Lemma typecheck_binop_sound:
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type),
denote_tc_assert (typecheck_expr Delta (Ebinop b e1 e2 t)) rho ->
(denote_tc_assert (typecheck_expr Delta e1) rho ->
 typecheck_val (eval_expr e1 rho) (typeof e1) = true) ->
(denote_tc_assert (typecheck_expr Delta e2) rho ->
 typecheck_val (eval_expr e2 rho) (typeof e2) = true) ->
typecheck_val (eval_expr (Ebinop b e1 e2 t) rho) (typeof (Ebinop b e1 e2 t)) =
true.
Proof.
Admitted.
(*intros. st. intuition.
destruct b; st;
match goal with 
| [ |- typecheck_val ( force_val (?X _ _ _ _)) _ = true ] => unfold X in *
| [ |- typecheck_val ( force_val (?X _ _ _ _ _)) _ = true ] => unfold X in *
| [ |- typecheck_val ( force_val (?X _ _ _ _ _ _)) _ = true ] => unfold X in *
end;

destruct (typeof e1); destruct (typeof e2); st; auto;

try solve [try destruct i; try destruct s; try destruct i0; try destruct s0; 
st;  
destruct (eval_expr rho e1); destruct (eval_expr rho e2); auto; destruct t;
tc_assert_ext; st; auto; repeat (try rewrite orb_if; rewrite andb_if); try repeat if_tac; st; 
try of_bool_destruct; auto].
Qed.*)

Transparent Float.intoffloat.
Transparent Float.intuoffloat.

Ltac unfold_tc_denote :=
unfold denote_tc_nonzero in *;
unfold denote_tc_isptr in *;
unfold denote_tc_igt in *;
unfold denote_tc_Zle in *;
unfold denote_tc_Zge in *;
unfold denote_tc_samebase in *;
unfold denote_tc_nodivover in *;
unfold denote_tc_initialized in *.

Lemma typecheck_both_sound: 
  forall Delta rho e , 
             typecheck_environ rho Delta = true ->
             (denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr e rho) (typeof e) = true) /\
             (forall pt, 
             denote_tc_assert (typecheck_lvalue Delta e) rho ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue e rho) pt=true).
Proof.

intros. induction e; split; intros; try solve[subst; auto].

(*Const int*)
simpl. subst; destruct t; auto; simpl in H0; inv H0; intuition.

(*Const float*)
simpl in *. subst; destruct t; intuition. 

(*Var*)
simpl in *. unfold eval_var.

assert (tc_mode_denote rho Delta ) as SM. unfold typecheck_environ in H. 
rewrite andb_true_iff in H; intuition. apply typecheck_mode_eqv in H3. auto.
destruct rho. 
apply typecheck_environ_sound in H. destruct H as [_ [? ?]].
unfold tc_ve_denote in *. unfold get_var_type in *. 

remember ((var_types Delta) ! i).
destruct o; try rewrite eqb_type_eq in *; simpl in *; intuition. 
unfold lift2 in H0.
remember (type_eq t t0). destruct s; intuition. 
subst. remember (negb(type_is_volatile t0)). destruct b; intuition. 
clear H3. symmetry in Heqo.
specialize (H i t0 Heqo).

destruct H. 
rewrite H in *. rewrite <- Heqb. rewrite eqb_type_refl in *. destruct pt; auto.
remember ((glob_types Delta) ! i). destruct o; try congruence. 
simpl in *. unfold lift2 in H0. destruct H0. remember (eqb_type t (globtype g)).
symmetry in Heqb. destruct b; simpl in *; try congruence. apply eqb_type_true in Heqb.
subst. unfold tc_mode_denote in *. symmetry in Heqo0.  specialize (SM _ _ Heqo0). 
destruct SM. simpl in H4. unfold Map.get. rewrite H4. 
unfold tc_ge_denote in *. edestruct H2; eauto. destruct H5. destruct H5. 
rewrite H5. rewrite eqb_type_refl. auto. destruct H4; congruence.  

inv H0. inv H0. 

(*Temp*)
Focus 1.
simpl in *. destruct rho. apply typecheck_environ_sound in H. intuition.
clear H H3.  
unfold tc_te_denote in *. 
unfold eval_id in *. 

simpl. unfold force_val.
destruct Delta. destruct p. destruct p. 
unfold temp_types in *. simpl in *.
remember (t2 ! i). destruct o.
  symmetry in Heqo.  
  destruct p. specialize (H1 i _ b Heqo). simpl in *.
  rewrite eqb_type_eq in *. destruct H1 as [? [? ?]].
  rewrite H. if_tac in H0; simpl in *; try solve [inv H0].
  destruct (type_eq t t4); try solve [inv H0]. subst; auto.
  if_tac in H0; inv H0.

(*deref*)  
simpl in *. unfold lift2 in *. intuition. specialize (H3 pt).
unfold_tc_denote. unfold lift1 in *.
remember (eval_expr e rho); destruct v;
simpl in *; unfold lift2 in *;
remember (typeof e); destruct t0; intuition; destruct pt; auto.

(*addrof*)
st.  intuition. destruct H0. 
destruct t; auto.


(*Unop*)
intuition; simpl in *. destruct H0. intuition.
unfold eval_unop, lift1. 
destruct u; simpl in *. 

unfold sem_notbool in *.
remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; st; destruct (eval_expr e rho); intuition;
try of_bool_destruct; try destruct t; intuition.

unfold sem_notint.

remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; st; destruct (eval_expr e rho); intuition;
try of_bool_destruct; try destruct t; intuition.


unfold sem_neg.

remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; st; destruct (eval_expr e rho); intuition;
try of_bool_destruct; try destruct t; intuition.

(*binop*)
repeat rewrite andb_true_iff in *; intuition.
clear H4. clear H2. clear H. 
eapply typecheck_binop_sound; eauto.

(* cast *)
st. intuition.
unfold lift1,eval_cast.
remember (eval_expr e rho). 
remember (typeof e).
destruct H0.
destruct v; destruct t0; intuition; destruct t; try solve [ intuition;
try destruct i; try destruct i0; try destruct i1; intuition;
unfold sem_cast, classify_cast, cast_float_int, 
    Float.intoffloat, Float.intuoffloat;
 destruct s; auto; try (destruct H3 as [H3a H3b]; hnf in H3a,H3b);
 try rewrite <- Heqv in *; repeat invSome;
 inversion2 H3b H3a;
 hnf in H3b0, H3a0;
 rewrite H3a0; rewrite Zle_bool_rev; rewrite H3b0; auto |

simpl in H3; hnf in H3; simpl; rewrite <- Heqv in *; auto |
destruct i0; destruct s; simpl in *; auto; hnf in H3; try rewrite <- Heqv in *; try contradiction]. 


(*condition*)
admit. (*condition might go away*)
(*st. repeat rewrite andb_true_iff in *; intuition.
remember (eval_expr rho e2).
remember (eval_expr rho e3).

destruct (eval_expr rho e1); intuition.
remember (typeof e1); destruct t0; intuition. simpl.
destruct (negb (Int.eq i Int.zero)). destruct v; intuition; remember (typeof e2);
destruct t0; intuition; destruct t; intuition; try destruct i2; try destruct s0; intuition;
try destruct i3; try destruct s0; try destruct s1; try destruct i1; intuition.
destruct v0; intuition; remember (typeof e3); destruct t0; intuition; destruct t; intuition; 
try destruct i2; try destruct s0; intuition;
try destruct i3; try destruct s0; try destruct s1; try destruct i1; intuition.
remember (typeof e1); destruct t0; intuition. simpl.
destruct (negb (Float.cmp Ceq f Float.zero)).
remember (typeof e2). destruct v; destruct t0; destruct t; intuition;
try destruct i0; try destruct s; intuition; try destruct i1; try destruct s0; try destruct i; intuition.
remember (typeof e3). destruct v0; destruct t0; destruct t; intuition; 
try destruct i0; try destruct s; intuition; try destruct i1; try destruct s0; try destruct i; intuition.
remember (typeof e1). unfold bool_val. destruct t0; intuition.*)

(*EField*)
st. unfold lift2,eval_field,eval_struct_field,lift1 in *; intuition. 
specialize  (H3 pt). intuition. remember rho.
destruct e0.
apply typecheck_environ_sound in H. intuition. clear H4.
rewrite Heqe0 in H0.
assert (PTR := eval_lvalue_ptr _ e _ _ _ _ Heqe0 H H8).
rewrite Heqe0 in *. clear Heqe0.
intuition. 
remember (eval_lvalue e rho). unfold denote_tc_isptr in *.
destruct v; intuition; try congruence.
remember (eval_lvalue e rho). destruct H7. destruct H4.
destruct v; intuition; try congruence.
inv H4.
destruct (typeof e); intuition. 
destruct (field_offset i f); intuition.
Qed. 

Definition defined_val v :=
match v with
Vundef => False
| _ => True
end.

Lemma typecheck_both_bool_sound : forall Delta rho e,
 typecheck_environ rho Delta = true ->
 (typecheck_b Delta e= true ->
  defined_val (eval_expr e rho) ->
  typecheck_val (eval_expr e rho) (typeof e)=true)
 /\
 (forall pt, tc_might_be_true (typecheck_lvalue Delta e) =true ->
  defined_val (eval_lvalue e rho) ->
  is_pointer_type pt =true ->
  typecheck_val (eval_lvalue e rho) pt=true).
Proof. 
Admitted. (*Not used
intros. unfold typecheck_b. induction e; intuition.

(*int*)
destruct t; auto; st; try congruence.  

(*float*)
destruct t; auto; st; try congruence.

(*var*)
st. remember ((ve_of rho) ! i). destruct o.
  destruct p; try rewrite eqb_type_eq in *; simpl in *; repeat if_tac; destruct pt; auto.

  remember (ge_of rho i). destruct o; try rewrite eqb_type_eq in *; simpl in *.
    destruct p; try rewrite eqb_type_eq in *; simpl in *.
    if_tac. remember ((var_types Delta) ! i).
    destruct o; try rewrite eqb_type_eq in *; simpl in *. subst.
   destruct (type_eq t t1); st; try congruence.
    subst. apply typecheck_environ_sound in H. 
    intuition. clear H3. unfold ve_correct in *.
    rewrite Forall_forall in *. symmetry in Heqo1. 
    apply PTree.elements_correct in Heqo1.
    specialize (H4 (i,t1)). intuition. simpl in H; rewrite <- Heqo in H;
    rewrite <- Heqo0 in H. destruct v; try congruence; auto;
    destruct pt; simpl in *; try congruence. 
    destruct pt; simpl in *; try congruence. intuition.
    intuition. 

(*temp*)
simpl in *. unfold defined_val in *.
unfold eval_id in *. unfold force_val.
 remember ((temp_types Delta) ! i).
destruct o; try rewrite eqb_type_eq in *; simpl in *.
  apply typecheck_environ_sound in H. intuition. 
  remember ((te_of rho) ! i); destruct o; auto. clear H3. symmetry in Heqo.
  apply PTree.elements_correct in Heqo. unfold te_correct in *.
  rewrite Forall_forall in *. specialize (H2 (i,p)). if_tac in H0; intuition.
  st. destruct p. rewrite <- Heqo0 in H. st.
  destruct (type_eq t t0); simpl in *; subst; auto. discriminate.
  if_tac in H0. simpl in H0. inv H0. inv H0.
 
(*deref*)
st. remember (eval_expr rho e). destruct v; auto. 

(*addrof*)
st. rewrite andb_true_iff in *. intuition. specialize (H1 t).
intuition. apply H1. destruct t; auto.

(*unop*)
st. rewrite andb_true_iff in *. intuition. clear H1.
destruct u; st;
match goal with [ |- context[force_val (?H _ _)]] => unfold H in * end;
  remember (typeof e); destruct t0; st; try congruence; 
  try destruct i; try destruct s; st; try congruence; auto;
  destruct (eval_expr rho e); auto; st; try (of_bool_destruct); destruct t; auto;
  st; try congruence.

(*binop*)
admit.

(*cast*)
admit.

(*condition*)
admit.

(*field*)
st. remember (eval_lvalue rho e). destruct v; auto.
remember (typeof e). destruct t0; auto. remember (field_offset i f).
destruct r; auto. 

Qed. (*admits, not done, should work ==================================================================*)
    *)

Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ rho Delta = true -> 
              denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr e rho) (typeof e) = true.
Proof. intros. 
assert (TC := typecheck_both_sound Delta rho e). intuition. Qed.


Lemma typecheck_lvalue_sound : forall Delta rho e,
  typecheck_environ rho Delta = true ->
  denote_tc_assert (typecheck_lvalue Delta e) rho ->
  (forall pt, 
    is_pointer_type pt = true -> 
    typecheck_val (eval_lvalue e rho) pt=true).
intros. edestruct (typecheck_both_sound _ _ e H).
apply H3; eauto.
Qed.

Lemma get_typed_int:
    forall v att, typecheck_val v (Tint I32 Signed att) = true -> 
                      exists i:int, v = Vint i.
intros; destruct v; inv H; eauto.
Qed.

Definition is_ptr_type (ty: type) : bool :=
  match ty with
  | Tpointer _ _ => true
  | Tarray _ _ _ => true
  | Tfunction _ _ => true
  | Tstruct _ _ _ => true
  | Tunion _ _ _ => true
  | _ => false
end.

(*Not going to work because of null pointer
Lemma get_typed_ptr:
   forall v ty, 
                   typecheck_val v ty = true -> 
                   is_ptr_type ty = true ->
                      exists b, exists ofs, v = Vptr b ofs.
Proof.
intros; destruct v; destruct ty; inv H; eauto; inv H0.
Qed.*)




Lemma tc_binaryop_nomem : forall b e1 e2 m1 m2 t rho,
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m1) =
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (m2).
Proof.
intros.
destruct b; st; auto;
 unfold sem_cmp; destruct (classify_cmp (typeof e1) (typeof e2));
   try destruct i; try destruct s; auto; contradiction.
Qed. 

Definition some_pt_type := Tpointer Tvoid noattr.

Lemma filter_genv_zero_ofs : forall ge ge2 b i t,
  filter_genv ge = ge2 ->
    (forall id, ge2 id = Some (Vptr b i, t) ->
      i = Int.zero).
Proof.
intros. unfold filter_genv in *. rewrite <- H in H0.
remember (Genv.find_symbol ge id). destruct o. 
destruct (type_of_global ge b0); inv H0; auto.
inv H0.
Qed.

Ltac ftn := try solve [st; try congruence; try contradiction]. 


Lemma eval_binop_relate_fail :
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) (m : mem),
typecheck_environ rho Delta = true ->
forall (ge : genv) te ve,
rho = construct_rho (filter_genv ge) ve te ->
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
denote_tc_assert (typecheck_expr Delta e1) rho ->
None =
sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
  (typeof e2) (fun (_ : block) (_ : Z) => false) ->
Clight_sem.eval_expr ge ve te m e2 (eval_expr e2 rho) ->
Clight_sem.eval_expr ge ve te m e1 (eval_expr e1 rho) ->
Clight_sem.eval_expr ge ve te m (Ebinop b e1 e2 t) Vundef.
Proof.
Admitted. (*Memory
intros. assert (TC1 := typecheck_expr_sound _ _ _ H H1).
assert (TC2 := typecheck_expr_sound _ _ _ H H3).
st. 
unfold sem_binary_operation in *. destruct b; 
st; 
remember (typeof e1); remember (typeof e2);
remember (eval_expr rho e1); remember (eval_expr rho e2);

(try match goal with
| [H : None = ?X _ _ _ _ |- _] => unfold X in *
| [H : None = ?X _ _ _ _ _ _ |- _ ] => unfold X in *
end; 

destruct v0; destruct t1; ftn; destruct v; destruct t0; ftn;
try destruct i1; try destruct s; ftn; try destruct i2; try destruct s0; ftn;
try destruct i0; ftn; st; try (rewrite <- Heqv in *; intuition);
try rewrite <- Heqv0 in *; intuition; 
try (repeat rewrite andb_if in H4); try (repeat rewrite orb_if in H4); repeat if_tac in H4; ftn).
*)



Lemma eval_both_relate:
  forall Delta ge te ve rho e m, 
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight_sem.eval_expr ge ve te m e  (eval_expr e rho))
           /\
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight_sem.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
Proof. 
intros. generalize dependent ge. induction e; intros;
try solve[intuition; constructor; auto | subst; inv H1]; intuition.

(* var*)
assert (TC_Sound:= typecheck_lvalue_sound).
specialize (TC_Sound Delta rho (Evar i t) H0 H1).
specialize (TC_Sound some_pt_type). simpl in TC_Sound.
specialize (TC_Sound (eq_refl _)). 
 
simpl in *. unfold eval_var in *. 
remember (Map.get (ve_of rho) i); destruct o; try destruct p; 
try rewrite eqb_type_eq in *; simpl in *.
destruct (type_eq t t0); simpl in *; intuition.
subst t0. if_tac; intuition.
exists b. exists Int.zero. intuition. constructor.
unfold Map.get in Heqo. unfold construct_rho in *.
destruct rho; inv H; simpl in *;  auto. 

remember (ge_of rho i). destruct o; try destruct p; auto;
try rewrite eqb_type_eq in *; simpl in *; intuition.
destruct (type_eq t t0); simpl in *. subst t0.

unfold get_var_type in *. 
remember ((var_types Delta) ! i). 
destruct o; try rewrite eqb_type_eq in *; simpl in *; unfold lift2 in *; intuition.
destruct (type_eq t t0); simpl in *; [ | contradiction]. subst t0.
symmetry in Heqo1.
destruct rho.  
apply typecheck_environ_sound in H0.
intuition. unfold tc_ve_denote in *. 
unfold tc_ge_denote in *. 
specialize (H0 i t Heqo1). unfold ge_of in *. unfold Map.get in *. 
destruct H0. simpl in Heqo. congruence.

destruct rho. 
apply typecheck_environ_sound in H0. intuition. unfold tc_ge_denote in *. 
remember ((glob_types Delta) ! i). destruct o; simpl in H1; try congruence.
unfold lift2 in *. destruct H1. 
symmetry in Heqo2. specialize (H4 _ _ Heqo2).  destruct H4. destruct H4. 
destruct H4. simpl in Heqo0. rewrite H4 in *. inv Heqo0. exists x. exists x0. split; auto. 
unfold construct_rho in *. inv H. simpl in Heqo. clear H1. 
remember (filter_genv ge). symmetry in Heqg0. 
assert (ZO := filter_genv_zero_ofs _ _ _ _ _ Heqg0 _ H4).  subst.
apply Clight_sem.eval_Evar_global. auto.  unfold filter_genv in H4.
destruct (Genv.find_symbol ge i). destruct (type_of_global ge b); inv H4; auto. 
congruence.  

unfold filter_genv in H4.
remember (Genv.find_symbol ge i).  destruct o; try congruence.  
assert (x = b). destruct (type_of_global ge b); inv H4; auto. subst.
destruct (type_of_global ge b). inv H4; auto. inv H4. rewrite <- H1 in *. simpl in *.
congruence. 
intuition. congruence. 

(*temp*)  
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (Etempvar i t)). simpl in *. 
intuition.  
constructor. unfold eval_id in *. remember (Map.get (te_of rho)  i);
destruct o;  auto. destruct rho; inv H; unfold make_tenv in *.
unfold Map.get in *. auto. 
simpl in *. congruence.

(*deref*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). intuition. simpl in H1.
intuition. simpl. unfold lift1,lift2 in *; unfold_tc_denote.
 remember (eval_expr e rho); destruct v;
intuition. 
exists b. exists i. st. intuition. constructor.
auto.

(*addrof*)

simpl in H1. unfold lift2 in *.
assert (ISPTR := eval_lvalue_ptr rho e Delta (te_of rho) (ve_of rho) (ge_of rho)).
specialize (IHe ge).
assert (mkEnviron (ge_of rho) (ve_of rho) (te_of rho) = rho). destruct rho; auto.
destruct rho. 
intuition; apply typecheck_environ_sound in H0. intuition. 
simpl. destruct H7. destruct H7. intuition. congruence. 
destruct H7. destruct H7. destruct H7. destruct H1. destruct H1.  simpl in *.
intuition. rewrite H8 in *. constructor. inv H1. auto.

(*unop*)
simpl in *. unfold lift1,lift2,eval_unop in *. intuition. unfold force_val. 
remember (sem_unary_operation u (eval_expr e rho) (typeof e)).
destruct o. eapply Clight_sem.eval_Eunop. eapply IHe; eauto. rewrite Heqo. auto.
apply typecheck_expr_sound in H3; auto. unfold sem_unary_operation in *.
destruct u. st. remember (typeof e); destruct t0; try inv H2;
try destruct i;try destruct s; try inv H2; st; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_notbool in *;
st; inv Heqo. 

st. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inversion H3; st; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_notint in *;
st; inv Heqo. 

st. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inversion H3; st; destruct t; intuition;
destruct (eval_expr e rho); intuition; unfold sem_neg in *;
st; inv Heqo.

(*binop*)
simpl in *. unfold lift2,eval_binop in *; intuition. unfold force_val.
remember (sem_binary_operation b (eval_expr e1 rho) (typeof e1) (eval_expr e2 rho)
(typeof e2) (fun (_ : block) (_ : Z) => false)).
destruct o. eapply Clight_sem.eval_Ebinop. eapply IHe1; eauto.
eapply IHe2. apply H. apply H3. auto. apply typecheck_expr_sound in H3; auto.
rewrite Heqo.

apply tc_binaryop_nomem with (t:=t); auto.
specialize (IHe1 ge). specialize (IHe2 ge). intuition.
clear H6 H8. 
eapply eval_binop_relate_fail; eauto.

(*Cast*)
assert (TC := typecheck_expr_sound _ _ _ H0 H1).
simpl in *; unfold lift2,lift1,eval_cast in *; intuition.
unfold force_val. remember (sem_cast (eval_expr e rho) (typeof e) t).
destruct o. eapply Clight_sem.eval_Ecast. eapply IHe. auto. apply H2. auto.


specialize (IHe ge). intuition. (*seems too easy, maybe functions are exactly the same?
still suprising to not deal with float case, commented below*)
(*
apply typecheck_expr_sound in H2; auto. 
remember (typeof e). remember (eval_expr rho e). destruct v; intuition; st;
destruct t0; intuition; destruct t; intuition; try destruct i0; try destruct s;
try destruct i1;try destruct s0; intuition;try solve [inv Heqo]; try destruct i; intuition;
st; try rewrite <- Heqv in H3; unfold sem_cast in *;
try solve [st; intuition; try unfold Float.intoffloat in *; try unfold Float.intuoffloat in *;
destruct (Float.Zoffloat f); intuition;
rewrite H1 in Heqo; rewrite H4 in Heqo; st; inv Heqo; 
destruct i; intuition]. inv Heqo. inv Heqo. *)

admit. (*Pass for now, since cond might go away.....======================================================*)

(*Field*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). specialize (TC some_pt_type). intuition. simpl in H1. intuition.
st. unfold lift2,lift1,eval_field,eval_struct_field in *; remember (eval_lvalue e rho).
destruct H1. destruct H1. specialize (H4 H1).
destruct H4 as [b [ofs H4]].
remember (typeof e) as t0. destruct t0; intuition.
remember (field_offset i f) as r.
destruct r; intuition.
 destruct v; intuition. st. exists b. exists (Int.add ofs (Int.repr z)). 
intuition. inv H8.
 eapply Clight_sem.eval_Efield_struct; auto.
eapply Clight_sem.eval_Elvalue in H7. apply H7.
rewrite <- Heqt0. auto. apply Csem.deref_loc_copy. rewrite <- Heqt0.  auto.
rewrite <- Heqt0; reflexivity. auto.
inv H8; auto.
subst v.
exists b, ofs. rewrite H8. simpl. split; auto.
eapply Clight_sem.eval_Efield_union; eauto.
eapply Clight_sem.eval_Elvalue; eauto.
rewrite <- Heqt0. auto. rewrite <- Heqt0. apply Csem.deref_loc_copy.
auto. 
Qed. 

Lemma eval_expr_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight_sem.eval_expr ge ve te m e  (eval_expr e rho)).
Proof.
intros.
edestruct eval_both_relate; eauto.
Qed.



Lemma eval_lvalue_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight_sem.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
apply eval_both_relate.
Qed.

Lemma tc_lvalue_nonvol : forall rho Delta e,
(denote_tc_assert (typecheck_lvalue Delta e) rho) ->
type_is_volatile (typeof e) = false.
Proof.
intros.
destruct e; intuition; simpl in *. 
unfold get_var_type in *. 

destruct ((var_types Delta) ! i); intuition; simpl in *. unfold lift2 in *;
intuition. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; simpl in *; unfold lift2 in *; intuition.

unfold lift2 in *; intuition. unfold tc_bool in *. rewrite if_negb in *.
destruct ((glob_types Delta) ! i). simpl in *. unfold lift2 in *. 
destruct H. if_tac in H0; auto; inv H0. inv H. 

unfold lift2 in *; intuition. clear - H1. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; intuition.

unfold lift2 in *. intuition. unfold tc_bool in *.  rewrite if_negb in *. 
if_tac in H1; auto. inv H1. 
Qed.

(*Proof for "backwards environment checking" that an environment that typechecks
must have come from an update on an environment that typechecks. 
TODO: These Lemmas
should eventually be put in more meaningful places in this file. *)

Lemma join_te_eqv :forall te1 te2 id b1 b2 t1,
te1 ! id = Some (t1, b1) -> te2 ! id = Some (t1, b2) ->
(join_te te1 te2) ! id = Some (t1,andb b1 b2).
Proof.
intros. 
unfold join_te. rewrite PTree.fold_spec. rewrite <- fold_left_rev_right.
assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto. 
assert (forall t, te1 ! id = Some t -> In (id, t) (rev (PTree.elements te1))).
intros. apply In_rev. rewrite rev_involutive. apply PTree.elements_correct.
auto.

induction (rev (PTree.elements te1)). simpl in *.
apply H2 in H. inv H.

simpl in *. destruct a. simpl in *. destruct p0. simpl.
remember (te2 ! p). destruct o. destruct p0.
if_tac. subst. rewrite PTree.gsspec. if_tac. subst. specialize (H1 (t0,b)).
intuition. rewrite H1 in *. inv H.
 rewrite <- Heqo in *. inv H0. auto.
apply IHl; auto. intros. specialize (H2 (t1,b1)). intuition. inv H2. destruct H3; auto. 
specialize (H1 (t1,b1)). intuition.
rewrite H1 in H4. inv H4. auto.
apply IHl; auto.
intros. rewrite H in H4. inv H4. edestruct H2. apply H. inv H4. rewrite H0 in *.
inv Heqo. destruct H3; auto. auto.
apply IHl; auto; intros. rewrite H in *. inv H3. specialize (H2 (t1, b1)).
intuition. inv H2. congruence.
Qed.

(* Should be unneeded, we never change ve on join
Lemma join_ve_eqv :forall ve1 ve2 id v,
ve1 ! id = Some v -> ve2 ! id = Some v ->
(join_ve ve1 ve2) ! id = Some v.
Proof.
intros. unfold join_ve. rewrite PTree.fold_spec. rewrite <- fold_left_rev_right.
assert (forall v, In (id, v) (rev (PTree.elements ve1)) -> ve1 ! id = Some v).
intros. apply PTree.elements_complete; apply in_rev; auto.
assert (forall t, ve1 ! id = Some t -> In (id, t) (rev (PTree.elements ve1))).
intros. apply In_rev. rewrite rev_involutive. apply PTree.elements_correct.
auto.

induction (rev (PTree.elements ve1)). apply H2 in H. inv H.

simpl in *. destruct a. simpl in *. remember (ve2 ! p). destruct o.
if_tac. subst. rewrite PTree.gsspec. if_tac. subst. specialize (H1 t0). 
intuition. rewrite H1 in *. inv H.
rewrite <- Heqo in *. inv H0. auto.
apply IHl; auto. intros. specialize (H2 t). intuition. inv H2. destruct H3; auto. 
apply IHl; auto.
intros. rewrite H in H4. inv H4. edestruct H2. apply H. inv H4. rewrite H0 in *.
inv Heqo. destruct H3; auto. auto.
apply IHl; auto; intros. rewrite H in *. inv H3. specialize (H2 t0).
intuition. inv H2. congruence.

Qed.
*)

Lemma temp_types_same_type : forall id i t b Delta,
(temp_types Delta) ! id = Some (t, b) ->
exists b0 : bool,
  (temp_types (initialized i Delta)) ! id = Some (t, b0).
Proof.
intros.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o.
destruct p. unfold temp_types in *. simpl. rewrite PTree.gsspec.
if_tac. subst. rewrite H in *. inv Heqo. eauto. eauto.
eauto.
Qed.

Lemma temp_types_update_dist : forall d1 d2 ,
(temp_types (join_tycon (d1) (d2))) =
join_te (temp_types (d1)) (temp_types (d2)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold temp_types. simpl. auto.
Qed.

Lemma var_types_update_dist : forall d1 d2 ,
(var_types (join_tycon (d1) (d2))) =
(var_types (d1)).
Proof.
intros.
destruct d1; destruct d2. destruct p; destruct p0. destruct p0; destruct p.
simpl. unfold var_types. simpl. auto.
Qed.


Lemma var_types_update_tycon:
  forall c Delta, var_types (update_tycon Delta c) = var_types Delta.
Proof.
assert (forall i Delta, var_types (initialized i Delta) = var_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); auto. destruct p; auto. 
induction c; intros; simpl; auto.
destruct o; auto.
rewrite IHc2; auto.
rewrite var_types_update_dist. auto.
admit. 
Qed.
 
Lemma glob_types_update_tycon:
  forall c Delta, glob_types (update_tycon Delta c) = glob_types Delta.
Admitted. 


Lemma update_tycon_te_same : forall c Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b, (temp_types (update_tycon Delta c)) ! id = Some (t, b)

with update_labeled_te_same : forall ls Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b, (temp_types (join_tycon_labeled ls Delta)) ! id = Some (t,b) .
destruct c; intros; simpl; eauto. simpl. eapply temp_types_same_type; eauto.

simpl. destruct o; eauto. simpl. eapply temp_types_same_type; eauto.


assert (forall (c : statement) (Delta : tycontext)
                         (id : positive) (t : type) (b : bool),
                       (temp_types Delta) ! id = Some (t, b) ->
                       exists b0 : bool,
                         (temp_types (update_tycon Delta c)) ! id =
                         Some (t, b0)) by auto.
edestruct update_tycon_te_same. apply H.
specialize (update_tycon_te_same c2 _ _ _ _ H1). eauto.

simpl. rewrite temp_types_update_dist.

edestruct (update_tycon_te_same c1). apply H.
edestruct (update_tycon_te_same c2). apply H. 
erewrite join_te_eqv;
eauto. 

intros. destruct ls. simpl. eauto.
simpl. rewrite temp_types_update_dist.
edestruct update_tycon_te_same. apply H.
edestruct update_labeled_te_same. apply H.
erewrite join_te_eqv. eauto.
apply H0.
apply H1.
Qed.


Lemma typecheck_environ_update_te:
  forall rho c Delta, tc_te_denote (te_of rho) (temp_types (update_tycon Delta c)) ->
tc_te_denote (te_of rho) (temp_types Delta)

with typecheck_ls_update_te : forall Delta ty b id l,
(temp_types Delta) ! id = Some (ty, b) -> 
exists b2, (temp_types (join_tycon_labeled l Delta)) ! id = Some (ty, b2).
Proof.
intros. unfold tc_te_denote in *.
destruct c; intros; simpl in *; try solve[eapply H; apply H0].

destruct (eq_dec id i). subst. eapply H; auto.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. inv H0. 
rewrite PTree.gsspec. rewrite peq_true. eauto. congruence.
eapply H. unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto.

destruct o.
destruct (eq_dec id i). subst. eapply H; auto.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. inv H0. 
rewrite PTree.gsspec. rewrite peq_true. eauto. congruence.
eapply H. unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto. eauto.

destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H1).
eapply H. apply H2. 

destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H0).
 eapply H. unfold join_tycon. remember (update_tycon Delta c1).
destruct t. destruct p. destruct p. remember (update_tycon Delta c2).
destruct t3. destruct p. destruct p. unfold temp_types in *.
unfold update_tycon. simpl in *.

apply join_te_eqv; eauto.    

destruct (update_tycon_te_same c _ _ _ _ H0). 
eapply H. apply H1. 
 
edestruct update_labeled_te_same. apply H0.
eapply H. apply H1.

intros. destruct l; simpl in *.
destruct (update_tycon_te_same s _ _ _ _ H).
eauto.

 destruct (update_tycon_te_same s _ _ _ _ H).
edestruct typecheck_ls_update_te. apply H.
rewrite temp_types_update_dist. erewrite join_te_eqv; eauto.
Qed.

Lemma set_temp_ve : forall Delta i,
var_types (initialized i Delta) = var_types (Delta).
Proof.
intros. destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed. 

Lemma set_temp_ge : forall Delta i,
glob_types (initialized i Delta) = glob_types (Delta).
Proof.
intros. destruct Delta. destruct p. destruct p. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (t1 ! i); auto. destruct p; auto.
Qed. 

Lemma update_tycon_same_ve : forall Delta c id v,
(var_types (update_tycon Delta c)) ! id = Some v <->
(var_types (Delta)) ! id = Some v


with update_le_same_ve : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = Some v <->
(var_types Delta) ! id = Some v.
Proof.
intros; split; intros.
destruct c; simpl in *; try apply H.
rewrite set_temp_ve in H. auto.
destruct o. rewrite set_temp_ve in H. auto.
auto.
eapply update_tycon_same_ve. rewrite <- update_tycon_same_ve. apply H.

rewrite var_types_update_dist in H.
rewrite update_tycon_same_ve in H. auto.
rewrite update_tycon_same_ve in H. apply H.
erewrite update_le_same_ve in H. apply H.

destruct c; simpl in *; try apply H. rewrite set_temp_ve. apply H.
destruct o. rewrite set_temp_ve. apply H.
apply H. rewrite update_tycon_same_ve. rewrite update_tycon_same_ve.
apply H. rewrite var_types_update_dist. 
rewrite update_tycon_same_ve. apply H. rewrite update_tycon_same_ve.
apply H. 
rewrite update_le_same_ve. apply H.

intros. split. intros.
 destruct l. simpl in *. rewrite update_tycon_same_ve in H.
apply H. simpl in *. rewrite var_types_update_dist in H.
rewrite update_tycon_same_ve in H. apply H.

intros. destruct l; simpl in *.
rewrite update_tycon_same_ve. apply H.
rewrite var_types_update_dist.  rewrite update_tycon_same_ve.
apply H.
Qed.   


Lemma glob_types_update_dist :
 forall d1 d2 : tycontext, glob_types (join_tycon d1 d2) = glob_types d1.
destruct d1; destruct d2.  destruct p. destruct p. destruct p0. destruct p. 
auto. 
Qed.

Lemma update_tycon_same_ge : forall Delta c id v,
(glob_types (update_tycon Delta c)) ! id = Some v <->
(glob_types (Delta)) ! id = Some v


with update_le_same_ge : forall (l : labeled_statements) (id : positive) (v : global_spec) Delta,
(glob_types (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_types Delta) ! id = Some v.
Proof.
intros; split; intros.
destruct c; simpl in *; try apply H.
rewrite set_temp_ge in H. auto.
destruct o. rewrite set_temp_ge in H. auto.
auto.
eapply update_tycon_same_ge. rewrite <- update_tycon_same_ge. apply H.

rewrite glob_types_update_dist in H.
rewrite update_tycon_same_ge in H. auto.
rewrite update_tycon_same_ge in H. apply H.
erewrite update_le_same_ge in H. apply H.

destruct c; simpl in *; try apply H. rewrite set_temp_ge. apply H.
destruct o. rewrite set_temp_ge. apply H.
apply H. rewrite update_tycon_same_ge. rewrite update_tycon_same_ge.
apply H. rewrite glob_types_update_dist. 
rewrite update_tycon_same_ge. apply H. rewrite update_tycon_same_ge.
apply H. 
rewrite update_le_same_ge. apply H.

intros. split. intros.
 destruct l. simpl in *. rewrite update_tycon_same_ge in H.
apply H. simpl in *. rewrite glob_types_update_dist in H.
rewrite update_tycon_same_ge in H. apply H.

intros. destruct l; simpl in *.
rewrite update_tycon_same_ge. apply H.
rewrite glob_types_update_dist.  rewrite update_tycon_same_ge.
apply H.
Qed.   

(*should be unneeded now
Lemma ve_join_update :
(forall (rho : environ) (c : statement) (Delta : tycontext),
 tc_ve_denote (ve_of rho) (ge_of rho) (var_types (update_tycon Delta c)) ->
 tc_ve_denote (ve_of rho) (ge_of rho) (var_types Delta)) ->
forall rho : environ,
forall (c1 c2 : statement) (Delta : tycontext),
tc_ve_denote (ve_of rho) (ge_of rho)
  (join_ve (var_types (update_tycon Delta c1))
     (var_types (update_tycon Delta c2))) ->
tc_ve_denote (ve_of rho) (ge_of rho) (var_types Delta).
Proof.
intros. unfold tc_ve_denote in *. intros. apply H0.
clear H0. 
 
unfold join_tycon in *. remember (update_tycon Delta c1).
destruct t. destruct p. destruct p. remember (update_tycon Delta c2).
destruct t2. destruct p. destruct p. unfold var_types in *. simpl in *.
unfold tc_ve_denote in *. intros.
apply join_ve_eqv. assert (t1 = var_types (update_tycon Delta c1)).
rewrite <- Heqt. unfold var_types. auto. subst.
rewrite update_tycon_same_ve. apply H1.
assert (t4 = var_types (update_tycon Delta c2)).
rewrite <- Heqt2; unfold var_types; auto. subst.
rewrite update_tycon_same_ve. apply H1.
Qed.*)


Lemma typecheck_environ_update_ve : forall (rho : environ) (c : statement) (Delta : tycontext),
tc_ve_denote (ve_of rho) (var_types (update_tycon Delta c)) ->
tc_ve_denote (ve_of rho) (var_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ve in *; try apply H;
unfold tc_ve_denote in *; intros; apply H; try rewrite var_types_update_dist; 
try apply join_ve_eqv;
repeat rewrite update_tycon_same_ve in *; try rewrite update_le_same_ve;
auto.
Qed. 



Lemma typecheck_environ_update_ge : forall (rho : environ) (c : statement) (Delta : tycontext),
tc_ge_denote (ge_of rho) (glob_types (update_tycon Delta c)) ->
tc_ge_denote (ge_of rho) (glob_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ge in *; try apply H;
unfold tc_ge_denote in *; intros; apply H; try rewrite glob_types_update_dist; 
try apply join_ge_eqv;
repeat rewrite update_tycon_same_ge in *; try rewrite update_le_same_ge;
auto.
Qed. 

Lemma typecheck_environ_update:
  forall rho c Delta, typecheck_environ rho (update_tycon Delta c) = true ->
       typecheck_environ rho Delta = true.
Proof.
intros. unfold typecheck_environ in *. repeat rewrite andb_true_iff in *. 
destruct H. destruct H. destruct H.  split. split. split. clear H0 H1 H2.
rewrite typecheck_te_eqv in *.  intuition.  eapply typecheck_environ_update_te; eauto.

clear H H0 H1. 
rewrite typecheck_ve_eqv in *. eapply typecheck_environ_update_ve.
eauto.

clear H H0 H2. rewrite typecheck_ge_eqv in *. eapply typecheck_environ_update_ge.
eauto.  

clear -H0.  assert (TM := typecheck_mode_eqv rho Delta). apply TM.  
admit.  (* rewrite typecheck_mode_eqv. *)

Qed.

Lemma typecheck_bool_val:
  forall v t, typecheck_val v t = true -> bool_type t = true ->
      exists b, strict_bool_val v t = Some b.
Proof.
intros.
destruct t; inv H0;
destruct v; inv H; simpl; try rewrite H1; eauto. 
Qed.

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite PTree.gsspec; auto.
Qed.

Lemma cast_exists : forall Delta e2 t rho 
(TC: typecheck_environ rho Delta = true), 
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isCastResultType (typeof e2) t t e2)
  rho ->
sem_cast (eval_expr e2 rho) (typeof e2) t =
Some (force_val (sem_cast (eval_expr e2 rho) (typeof e2) t)).
Proof.
intros. 
assert (exists v, sem_cast (eval_expr e2 rho) (typeof e2) t= Some v).

apply typecheck_expr_sound in H.
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent Float.intoffloat.
Transparent Float.intuoffloat.
destruct t; destruct v; destruct t0; simpl in *;
try congruence; try contradiction; eauto;
try solve [
unfold Float.intoffloat, Float.intuoffloat; repeat invSome;
inversion2 H1 H0; hnf in H2,H3; rewrite H3; rewrite Zle_bool_rev; rewrite H2;
simpl; eauto];
try solve [
try destruct i; try destruct s; try destruct i0; try destruct i1; try destruct s0; eauto |

destruct i; destruct s; unfold lift2 in *; try solve[simpl in *; 
  unfold lift2,lift1 in *;  unfold_tc_denote; destruct H0; 
try rewrite <- Heqv in *; 
unfold Float.intoffloat; 
destruct (Float.Zoffloat f0); try contradiction;
try rewrite H0; try rewrite H1; simpl; eauto | 
simpl in *;  unfold Float.intuoffloat; destruct H0;
unfold_tc_denote; try rewrite <- Heqv in *; destruct (Float.Zoffloat f0);
try rewrite H0; try rewrite H1; simpl; eauto; try contradiction] |

try destruct i0; try destruct i1; destruct s; simpl in *; try contradiction; try rewrite H; eauto ].

destruct i; destruct s; unfold lift2 in *;
simpl in *; unfold lift2,lift1 in *;
unfold Float.intoffloat, Float.intuoffloat;
try (
destruct H0 as [H0 H1]; hnf in H0,H1; rewrite <- Heqv in *;
destruct (Float.Zoffloat f0); try contradiction;
hnf in H0,H1; rewrite H0; rewrite Zle_bool_rev; rewrite H1;
simpl; eauto);
simpl; eauto.

auto.
Opaque Float.intoffloat.
Opaque Float.intuoffloat.

destruct H1. rewrite H1. auto.
Qed.


Lemma typecheck_val_eval_cast: 
  forall t2 e2 rho Delta,
      typecheck_environ rho Delta = true ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2 t2 e2) rho ->
      typecheck_val (eval_cast (typeof e2) t2 (eval_expr e2 rho)) t2 = true.
Proof. intros ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ H2 H5 H6).
assert (H8 := typecheck_expr_sound _ _ _ H2 H5).
clear - H7 H6 H8.
revert H7; case_eq (sem_cast (eval_expr e2 rho) (typeof e2) t2); intros; inv H7.
unfold eval_cast. rewrite H. simpl.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2; inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2); inv H2; inv H1; auto;
try (unfold sem_cast in H0; simpl in H0;
      destruct i0; simpl in*; destruct s; inv H0; simpl; auto).
simpl in *. unfold lift1 in H6. rewrite H99 in *. inv H6. auto.
simpl in *. unfold isCastResultType in H6. simpl in H6.
unfold sem_cast in H0. 
simpl in H0.
destruct i; simpl in*; destruct s; try destruct f; inv H0; simpl; auto;
invSome; simpl; auto.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
Qed.
 