Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.local2ptree.
Local Open Scope logic.

Fixpoint argtypes (al: list (ident * type)) : list type :=
 match al with (_,t)::al' => t :: argtypes al' | nil => nil end.

Lemma argtypes_eq: forall al, argtypes al = snd (split al).
Proof.
 induction al; try destruct a; simpl; auto.
 destruct (split al). simpl in *. subst; auto.
Qed.

Definition maybe_retval (Q: environ -> mpred) retty ret :=
 match ret with
 | Some id => fun rho => Q (get_result1 id rho)
 | None => 
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.

Definition substopt_localdef (ret: option ident) (v: val) (P: localdef)  : localdef :=
   match ret with
   | Some id => subst_localdef id v P
   | None => P
   end.


Lemma semax_call': forall Espec {cs: compspecs} Delta A (Pre Post: A -> environ->mpred) (x: A) ret argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc_default ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, _ => True
   end ->
   tc_fn_return Delta ret retsig ->
  forallb subst_localdef_ok Q = true ->
  @semax cs Espec Delta
          (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl 
           && 
   (`(Pre x) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) *
                      `(func_ptr' (mk_funspec (argsig,retsig) A Pre Post)) (eval_expr a) 
     * PROPx P (LOCALx Q (SEPx R))))
          (Scall ret a bl)
          (normal_ret_assert 
            (EX old:val, 
              (maybe_retval (Post x) retsig ret *
               PROPx P (LOCALx (map (substopt_localdef ret old) Q) (SEPx R))))).
Proof.
 intros. rename H1 into Hret. rename H2 into OK.
 rewrite argtypes_eq.
eapply semax_pre_post ; [ | | 
   apply (semax_call Delta A Pre Post x (PROPx P (LOCALx Q (SEPx R))) ret argsig retsig a bl H); auto].
 Focus 3. {
 clear - H0.
 destruct retsig; destruct ret; simpl in *; try contradiction; 
   intros; congruence.
 } Unfocus.
clear Hret.
unfold_lift; unfold local, lift1. unfold func_ptr'. intro rho; simpl.
   normalize;
   progress (autorewrite with subst norm1 norm2; normalize).
apply andp_derives; auto.
rewrite !sepcon_assoc.
rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
rewrite sepcon_comm. rewrite emp_sepcon.
rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
apply derives_refl.
intros.
autorewrite with ret_assert.
repeat rewrite normal_ret_assert_eq.
normalize.
apply exp_right with old; destruct ret; normalize.
autorewrite with subst.
rewrite subst_PROP by auto.
intro rho; simpl; normalize.
autorewrite with norm1 norm2; normalize.
rewrite sepcon_comm; auto.
intro rho; simpl; normalize.
rewrite sepcon_comm; auto.
unfold substopt.
repeat rewrite list_map_identity.
normalize.
autorewrite with norm1 norm2; normalize.
Qed.

Lemma semax_call1: forall Espec {cs: compspecs} Delta A (Pre Post: A -> environ->mpred) (x: A) id argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc_default ->
   match retsig with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some id) retsig ->
  forallb subst_localdef_ok Q = true ->
  @semax cs Espec Delta
         (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl 
           && (`(Pre x) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) *
                 `(func_ptr' (mk_funspec (argsig,retsig) A Pre Post)) (eval_expr a) *
                  PROPx P (LOCALx Q (SEPx R))))
          (Scall (Some id) a bl)
          (normal_ret_assert 
            (EX old:val, 
              `(Post x) (get_result1 id)
               * PROPx P (LOCALx (map (subst_localdef id old) Q) (SEPx R)))).
Proof.
intros.
apply semax_call'; auto.
Qed.

Definition ifvoid {T} t (A B: T) :=
 match t with Tvoid => A | _ => B end.

Lemma semax_call0: forall Espec {cs: compspecs} Delta A (Pre Post: A -> environ->mpred) (x: A) 
      argsig retty a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc_default ->
  @semax cs Espec Delta
         (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl 
           && (`(Pre x) ( (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)))
                 * `(func_ptr' (mk_funspec (argsig,retty) A Pre Post)) (eval_expr a)
                 * PROPx P (LOCALx Q (SEPx R))))
          (Scall None a bl)
          (normal_ret_assert 
            (ifvoid retty (`(Post x) (make_args nil nil))
                                                        (EX v:val, `(Post x) (make_args (ret_temp::nil) (v::nil)))
            * PROPx P (LOCALx Q (SEPx R)))).
Proof.
intros.
rewrite argtypes_eq.
eapply semax_pre_post ; [ | | 
   apply (semax_call Delta A Pre Post x (PROPx P (LOCALx Q (SEPx R))) None argsig retty a bl H)].
 Focus 3.
 split; intros; congruence.
 intro rho; normalize.
 autorewrite with norm1 norm2; normalize.
unfold func_ptr'.
rewrite !sepcon_assoc.
rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon, sepcon_comm. 
rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
apply derives_refl.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
normalize.
unfold SeparationLogic.maybe_retval.
autorewrite with subst norm ret_assert.
destruct retty; auto; rewrite sepcon_comm; apply derives_refl.
apply Coq.Init.Logic.I.
Qed.

Lemma semax_fun_id':
      forall id f TC
              Espec {cs: compspecs} Delta (PQR: environ->mpred) PostCond c
            (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some f ->
       (glob_types Delta) ! id = Some (type_of_funspec f) ->
       @semax cs Espec Delta 
        (TC && (local (tc_environ Delta) && 
                     (`(func_ptr' f) (eval_var id (type_of_funspec f))
                     * PQR)))
                              c PostCond ->
       @semax cs Espec Delta (TC && PQR) c PostCond.
Proof.
intros. 
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply H1.
rewrite <- !andp_assoc.
rewrite (andp_comm (local _)).
rewrite !andp_assoc.
apply andp_derives; auto.
apply andp_derives; auto.
clear H1.
unfold_lift. unfold func_ptr'.
intro rho; simpl; normalize.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite andp_comm.
apply andp_derives; auto.
rewrite emp_sepcon; auto.
intros.
apply andp_left2; auto.
Qed.

Lemma eqb_typelist_refl: forall tl, eqb_typelist tl tl = true.
Proof.
induction tl; simpl; auto.
apply andb_true_iff.
split; auto.
apply eqb_type_refl.
Qed.

Lemma semax_call_id0:
 forall Espec {cs: compspecs} Delta P Q R id bl argsig retty A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
  @semax cs Espec Delta (tc_exprlist Delta (argtypes argsig) bl
                  && (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)) 
                         * PROPx P (LOCALx Q (SEPx R))))
    (Scall None (Evar id (Tfunction (type_of_params argsig) retty cc_default)) bl)
    (normal_ret_assert 
       ((ifvoid retty (`(Post x) (make_args nil nil))
                                                   (EX v:val, `(Post x) (make_args (ret_temp::nil) (v::nil))))
         * PROPx P (LOCALx Q (SEPx R)))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Evar id (Tfunction (type_of_params argsig) retty cc_default)))=
               Cop.fun_case_f (type_of_params argsig) retty cc_default).
simpl. subst. reflexivity.
apply (semax_fun_id' id (mk_funspec (argsig,retty) A Pre Post)  
  (tc_exprlist Delta (argtypes argsig) bl)); auto.
subst. 

eapply semax_pre_simple; [ | apply (@semax_call0 Espec cs Delta A Pre Post x argsig _ _ bl P Q R)].
apply andp_right.
apply andp_right.
apply andp_left1.
intro rho; unfold tc_expr; simpl.
subst.
norm_rewrite. apply prop_left; intro.
unfold get_var_type. rewrite GLBL. rewrite H0.
rewrite denote_tc_assert_bool. apply prop_right.
simpl.
rewrite eqb_typelist_refl.
simpl. auto.
unfold_lift; auto.
rewrite eqb_type_refl. simpl.
reflexivity.
apply andp_left2; apply andp_left1; auto.
apply andp_left2; apply andp_left2; auto.
apply andp_left2. 
rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
rewrite sepcon_comm.
auto.
auto.
Qed.

Lemma semax_call_id1:
 forall Espec {cs: compspecs} Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
  forallb subst_localdef_ok Q = true ->
  @semax cs Espec Delta (tc_exprlist Delta (argtypes argsig) bl && 
                (`(Pre x) (make_args' (argsig,Tvoid) (eval_exprlist (argtypes argsig) bl)) 
                  * PROPx P (LOCALx Q (SEPx R))))
    (Scall (Some ret)
             (Evar id (Tfunction (type_of_params argsig) retty cc_default))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          (`(Post x) (get_result1 ret) 
           * PROPx P (LOCALx (map (subst_localdef ret old) Q) (SEPx R))))).
Proof.
intros. rename H0 into Ht. rename H1 into H0.
 rename H2 into Hret.
assert (Cop.classify_fun (typeof (Evar id (Tfunction (type_of_params argsig) retty cc_default)))=
               Cop.fun_case_f (type_of_params argsig) retty cc_default).
subst; reflexivity.
apply (semax_fun_id' id (mk_funspec (argsig,retty)  A Pre Post)); auto.
subst. 
eapply semax_pre_simple; [ | apply (semax_call1 Espec Delta A Pre Post x ret argsig retty _ bl P Q R H1 H0); auto].
apply andp_right.
apply andp_right.
apply andp_left1.
intro rho; unfold tc_expr, local,lift1; simpl.
subst.
norm_rewrite. 
unfold get_var_type. rewrite GLBL. rewrite Ht.
rewrite denote_tc_assert_bool.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. apply prop_right; reflexivity.
apply andp_left2.
apply andp_left1.
auto.
apply andp_left2.
apply andp_left2.
apply andp_left2.
rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
rewrite sepcon_comm.
auto.
Qed.

Inductive extract_trivial_liftx {A}: list (environ->A) -> list A -> Prop :=
| ETL_nil: extract_trivial_liftx nil nil
| ETL_cons: forall a al bl,
             extract_trivial_liftx al bl ->
             extract_trivial_liftx (`a :: al) (a::bl).

Lemma fold_right_and_app_low:
  forall (Q1 Q2 : list Prop),
  fold_right and True (Q1 ++ Q2)  =
  (fold_right and True Q1  /\ fold_right and True Q2).
Proof.
induction Q1; intros; simpl; auto.
apply prop_ext; intuition.
rewrite IHQ1.
apply prop_ext; intuition.
Qed.

Lemma fold_right_and_app_lifted:
  forall (Q1 Q2: list (environ -> Prop)),
  fold_right `and `True (Q1 ++ Q2)  =
  `and (fold_right `and `True Q1) (fold_right `and `True Q2).
Proof.
induction Q1; intros; simpl; auto.
extensionality rho; apply prop_ext; intuition.
split; auto.
destruct H; auto.
rewrite IHQ1.
extensionality rho; apply prop_ext; intuition.
destruct H. destruct H0. repeat split; auto.
destruct H. destruct H. repeat split; auto.
Qed.

Definition check_one_temp_spec (Q: PTree.t val) (idv: ident * val) : Prop :=
   (Q ! (fst idv)) = Some (snd idv).

Definition check_one_var_spec (Q: PTree.t vardesc) (idv: ident * vardesc) : Prop :=
   match Q ! (fst idv), snd idv with
   | Some (vardesc_local_global t v1 v2) , vardesc_visible_global v2'  =>
             v2=v2'
   | Some (vardesc_visible_global v2) , vardesc_visible_global v2'  =>
             v2=v2'
   | Some (vardesc_shadowed_global v2) , vardesc_visible_global v2'  =>
             v2=v2'
   | Some (vardesc_visible_global v2) , vardesc_shadowed_global v2'  =>
             v2=v2'
   | Some (vardesc_shadowed_global v2) , vardesc_shadowed_global v2'  =>
             v2=v2'
   | _, _ => False
   end.

Definition check_one_var_spec' (Q: PTree.t vardesc) (idv: ident * vardesc) : Prop :=
   (Q ! (fst idv)) = Some (snd idv).

Definition strong_cast (t1 t2: type) (v: val) : val :=
 force_val (sem_cast t1 t2 v).

Lemma extract_trivial_liftx_e:
  forall (R: list (environ->mpred)) (R': list mpred), 
     extract_trivial_liftx R R' -> R = map liftx R'.
Proof.
intros.
induction H; simpl.
auto.
f_equal; auto.
Qed.

(*
 Lemma fold_right_sepcon_liftx: 
    forall (R: list mpred) rho, fold_right sepcon emp (map liftx R) rho =
                    fold_right sepcon emp R.
Proof.
 intros.
 induction R; simpl; f_equal; auto.
Qed.
*)

Lemma isolate_LOCAL_lem1:
  forall Q, PROPx nil (LOCALx Q (SEPx (TT::nil))) = local (fold_right `and `True (map locald_denote Q)).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, SEPx.
 normalize.
 autorewrite with norm1 norm2; normalize.
Qed.

Lemma fold_right_and_LocalD_i {cs: compspecs}:
  forall T1 T2 Q rho,
  (forall i v, T1 ! i = Some v -> locald_denote (temp i v) rho) ->
  (forall i vd, T2 ! i = Some vd -> fold_right `and `True (map locald_denote (denote_vardesc nil i vd)) rho) ->
  (fold_right `and `True (map locald_denote Q) rho) ->
  fold_right `and `True (map locald_denote (LocalD T1 T2 Q)) rho.
Proof.
 intros.
 unfold LocalD.
 repeat rewrite PTree.fold_spec.
 repeat rewrite <- fold_left_rev_right.
 remember (rev (PTree.elements T2)) as L2.
 remember (rev (PTree.elements T1)) as L1.
 change L2 with (nil ++ L2) in HeqL2.
 change L1 with (nil ++ L1) in HeqL1.
 remember (@nil (positive * vardesc)) as E2.
 remember (@nil (positive * val)) as E1.
 clear HeqE1 HeqE2.
 revert E1 T1 HeqL1 H; induction L1; simpl; intros.
* 
 revert E2 T2 HeqL2 H0; induction L2; simpl; intros.
 auto.
 destruct a as [i vd].
 assert (H8: T2 ! i = Some vd).
    apply PTree.elements_complete.
    rewrite in_rev. rewrite <- HeqL2.
   rewrite in_app. right; left; auto.
 specialize (IHL2 (E2++((i,vd)::nil)) T2).
 rewrite app_ass in IHL2; specialize (IHL2 HeqL2).
 destruct vd.
 split3; auto. apply (H0 _ _ H8). apply (H0 _ _ H8).
 split; auto.  apply (H0 _ _ H8).
 split; auto.  apply (H0 _ _ H8).
 split; auto.  apply (H0 _ _ H8).
*
 destruct a as [i v]; simpl in *; unfold_lift; split.
 apply H.
 apply PTree.elements_complete.
 rewrite in_rev. rewrite <- HeqL1.
 rewrite in_app. right; left; auto.
 apply (IHL1 (E1++((i,v)::nil)) T1).
 rewrite app_ass. auto.
 auto.
Qed.

Lemma fold_right_and_LocalD_e {cs: compspecs}:
  forall T1 T2 Q rho,
  fold_right `and `True (map locald_denote (LocalD T1 T2 Q)) rho ->
  (forall i v, T1 ! i = Some v -> locald_denote (temp i v) rho) /\
  (forall i vd, T2 ! i = Some vd -> fold_right `and `True (map locald_denote (denote_vardesc nil i vd)) rho) /\
  (fold_right `and `True (map locald_denote Q) rho).
Proof.
unfold LocalD; intros.
 repeat rewrite PTree.fold_spec in H.
 repeat rewrite <- fold_left_rev_right in H.
 split3; intros.
*
 forget (fold_right
            (fun (y : positive * vardesc) (x : list localdef) =>
             denote_vardesc x (fst y) (snd y)) Q (rev (PTree.elements T2)))
   as Q'.
 apply PTree.elements_correct in H0.
 rewrite in_rev in H0.
 forget (rev (PTree.elements T1)) as L1.
 clear - H H0.
 revert H H0; induction L1; intros. inv H0.
 destruct a as [i' v']; destruct H0. inv H0.
 destruct H. apply H.
 destruct H.
 apply IHL1. apply H1. auto.
*
 induction  (rev (PTree.elements T1)).
 simpl in H.
 apply PTree.elements_correct in H0.
 rewrite in_rev in H0.
 forget (rev (PTree.elements T2)) as L2.
 clear - H H0.
 revert H H0; induction L2; intros. inv H0.
 destruct H0. subst a.
 destruct vd; simpl in H.
 destruct H as [? [? ?]]. split3; auto. apply Coq.Init.Logic.I.
 destruct H; split; auto; apply Coq.Init.Logic.I.
 destruct H; split; auto; apply Coq.Init.Logic.I.
 destruct H; split; auto; apply Coq.Init.Logic.I.
 apply IHL2; auto.
 clear - H.
 destruct a as [i vd]; destruct vd; destruct H; auto. destruct H0; auto.
 destruct H. auto.
*
 induction (rev (PTree.elements T1)).
 induction (rev (PTree.elements T2)).
 apply H.
 apply IHl.
 destruct a as [i [?|?|?|?]]; destruct H; try destruct H0; auto.
 destruct H. auto.
Qed.

Lemma Forall_ptree_elements_e:
  forall A (F: ident * A -> Prop) m i v,
   Forall F (PTree.elements m) ->
   m ! i = Some v ->
   F (i,v).
Proof.
 intros.
 apply PTree.elements_correct in H0.
 induction (PTree.elements m).
 inv H0.
 inv H. inv H0; auto.
Qed.

Lemma pTree_from_elements_e1:
   forall rho fl vl i v, 
    (pTree_from_elements (combine fl vl)) ! i = Some v ->
    v = eval_id i (make_args fl vl rho).
Proof.
 intros.
 revert vl H; induction fl; intros.
* simpl in H.
  unfold pTree_from_elements in H. simpl in H.
  rewrite PTree.gempty in H; inv H.
*
  destruct vl.
  simpl in *.
  unfold pTree_from_elements in H. simpl in H.
  rewrite PTree.gempty in H; inv H.
  simpl in H.
  unfold pTree_from_elements in H.
  simpl in H.
  destruct (ident_eq i a).
  subst a. rewrite PTree.gss in H. inv H.
  rewrite unfold_make_args_cons.
  unfold eval_id.  simpl. rewrite Map.gss. reflexivity.
  rewrite PTree.gso in H by auto.
  apply IHfl in H.
  rewrite unfold_make_args_cons.  
  unfold eval_id.  simpl. rewrite Map.gso by auto. apply H. 
Qed.

 Lemma ve_of_make_args: forall i fl vl rho ,
     length fl = length vl ->
     Map.get (ve_of (make_args fl vl rho)) i = None.
Proof.
 unfold Map.get, ve_of.
 induction fl; destruct vl; simpl; intros; try reflexivity.
 inv H. inv H.
 inversion H. apply (IHfl _ _ H1).
Qed.

Lemma ge_of_make_args: forall i fl vl rho, 
    ge_of (make_args fl vl rho) i = ge_of rho i.
Proof.
 induction fl; destruct vl; simpl; auto.
Qed.

Lemma check_specs_lemma {cs: compspecs}:
  forall Qtemp Qpre_temp Qvar Qpre_var rho fl vl
    (LEN: length fl = length vl),
    Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) ->
   Forall (check_one_temp_spec (pTree_from_elements (combine fl vl)))
          (PTree.elements Qpre_temp) ->
   fold_right `and `True (map locald_denote (LocalD Qtemp Qvar nil)) rho ->  
  fold_right `and `True (map locald_denote (LocalD Qpre_temp Qpre_var nil)) (make_args fl vl rho).
Proof.
 intros.
 apply fold_right_and_LocalD_e in H1.
 destruct H1 as [? [? ?]].
 apply fold_right_and_LocalD_i; [ | | auto]; clear H3; intros.
*
 hnf. 
 clear - H0 H3.
 pose proof (Forall_ptree_elements_e _ _ _ _ _ H0 H3).
 hnf in H. simpl in H.
 clear - H.
 eapply pTree_from_elements_e1; eauto.
*
 clear - LEN H H2 H3.
 pose proof (Forall_ptree_elements_e _ _ _ _ _ H H3).
 clear H H3.
 destruct vd; simpl in *; unfold_lift; repeat split; auto; 
   hnf in H0; simpl in H0; destruct (Qvar ! i) as [[?|?|?|?]|] eqn:?; try contradiction;
    subst.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo as [? [? _]].
  hnf in H,H0|-*.
  rewrite (ve_of_make_args _ _ _ _ LEN).
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo.  
  hnf in H|-*.
  rewrite (ve_of_make_args _ _ _ _ LEN).
  destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo. 
  hnf in H|-*.
  rewrite (ve_of_make_args _ _ _ _ LEN).
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo. 
  hnf in H|-*.
  destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo. 
  hnf in H|-*.
  rewrite ge_of_make_args. auto.
Qed.

Lemma check_specs_lemma' :
  forall Ptemp Pvar Qtemp Qvar rho,
    Forall (check_one_var_spec' Pvar) (PTree.elements Qvar) ->
    Forall (check_one_temp_spec Ptemp) (PTree.elements Qtemp) ->
    fold_right `and `True (map locald_denote (LocalD Ptemp Pvar nil)) rho ->
    fold_right `and `True (map locald_denote (LocalD Qtemp Qvar nil)) rho.
Proof.
  intros.
  apply local_ext_rev.
  intros.
  apply local_ext with (map locald_denote (LocalD Ptemp Pvar nil)); auto.
  apply in_map_iff in H2. apply in_map_iff.
  destruct H2 as [Q0' [H2' H2]]; exists Q0'; split; auto.
  apply LocalD_complete in H2.
  apply LocalD_sound.
  rewrite Forall_forall in H.
  rewrite Forall_forall in H0.
  destruct H2; [left | right; destruct H2; [left | right; destruct H2; [left | right; destruct H2; [left | right; destruct H2; [left | right; destruct H2; [left | right]]]]]].
  + destruct H2 as [i [v [? ?]]].
    exists i, v; split; auto.
    specialize (H0 (i, v)).
    apply H0.
    apply PTree.elements_correct; auto.
  + destruct H2 as [i [t [v [v' [? ?]]]]].
    exists i, t, v, v'; split; auto.
    specialize (H (i, vardesc_local_global t v v')).
    apply H.
    apply PTree.elements_correct; auto.
  + destruct H2 as [i [t [v [v' [? ?]]]]].
    exists i, t, v, v'; split; auto.
    specialize (H (i, vardesc_local_global t v v')).
    apply H.
    apply PTree.elements_correct; auto.
  + destruct H2 as [i [t [v [? ?]]]].
    exists i, t, v; split; auto.
    specialize (H (i, vardesc_local t v)).
    apply H.
    apply PTree.elements_correct; auto.
  + destruct H2 as [i [v [? ?]]].
    exists i, v; split; auto.
    specialize (H (i, vardesc_visible_global v)).
    apply H.
    apply PTree.elements_correct; auto.
  + destruct H2 as [i [v [? ?]]].
    exists i, v; split; auto.
    specialize (H (i, vardesc_shadowed_global v)).
    apply H.
    apply PTree.elements_correct; auto.
  + auto.
Qed.


Lemma PROP_combine:
 forall P P' Q Q' R R',
  PROPx P (LOCALx Q (SEPx R)) * PROPx P' (LOCALx Q' (SEPx R')) =
  PROPx (P++P') (LOCALx (Q++Q') (SEPx (R++R'))).
Proof.
intros.
unfold PROPx, LOCALx, SEPx, local, lift1.
extensionality rho. simpl.
normalize.
f_equal. rewrite map_app.
rewrite fold_right_and_app.
rewrite fold_right_and_app_low.
f_equal. apply prop_ext; intuition.
rewrite fold_right_sepcon_app.
auto.
Qed.

Inductive Parameter_types_in_funspec_different_from_call_statement : Prop := .
Inductive Result_type_in_funspec_different_from_call_statement : Prop := .

Definition check_retty t := 
    match t with Tvoid => Result_type_in_funspec_different_from_call_statement
                      |  Tarray _ _ _ => Result_type_in_funspec_different_from_call_statement
                       | _ => True 
    end.

Lemma PROP_LOCAL_SEP_f:
  forall P Q R f, `(PROPx P (LOCALx Q (SEPx R))) f =
     local (fold_right `and `True (map (fun q : environ -> Prop => `q f) (map locald_denote Q)))
     && PROPx P (LOCALx nil (SEPx R)).
Proof. intros. extensionality rho.
cbv delta [PROPx LOCALx SEPx local lift lift1 liftx]; simpl.
normalize.
f_equal. f_equal.
replace (fold_right (fun (x x0 : environ -> Prop) (x1 : environ) => x x1 /\ x0 x1)
   (fun _ : environ => True) (map locald_denote Q) (f rho))
  with (fold_right (fun (x x0 : environ -> Prop) (x1 : environ) => x x1 /\ x0 x1)
   (fun _ : environ => True)
   (map (fun (q : environ -> Prop) (x : environ) => q (f x))
      (map locald_denote Q)) rho);  [apply prop_ext; intuition | ].
induction Q; simpl; auto. f_equal; auto.
Qed.
Hint Rewrite PROP_LOCAL_SEP_f: norm2.

Lemma local2ptree_aux_OKsubst:
forall Q (Qt : PTree.tree val) (Qv : PTree.tree vardesc) (P0 : list Prop)
  (Q0 : list localdef) (Qtemp : PTree.t val) (Qvar : PTree.t vardesc)
  (P : list Prop),
  local2ptree_aux Q Qt Qv P0 Q0 = (Qtemp, Qvar, P, nil) ->
  forallb subst_localdef_ok Q = true /\ Q0=nil.
Proof.
induction Q; intros.
inv H. split; reflexivity.
destruct a; simpl in H|-*;
 try now (destruct (Qv!i); try destruct v0; eauto). 
destruct (Qt!i); eauto.
apply IHQ in H.
destruct H; discriminate.
apply IHQ in H. auto.
Qed.

Lemma local2ptree_OKsubst:
  forall Q Qtemp Qvar P, 
     local2ptree Q = (Qtemp, Qvar, P, nil) ->
     forallb subst_localdef_ok Q = true.
Proof.
intros.
apply local2ptree_aux_OKsubst in H.
destruct H; auto.
Qed.

Lemma semax_call_id1_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type) 
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: check_retty retty)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (DELETE: delete_temp_from_locals ret Q = Qnew)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret)
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id1 with (x:=witness) (P:=P)(Q:=Q) (R := Frame)
   ];
   try eassumption; try (eapply local2ptree_OKsubst; eauto);
   [ | 
   | clear - OKretty; destruct retty; inv OKretty; apply I
   | hnf; clear - TYret; unfold typeof_temp in TYret;
      destruct ((temp_types Delta) ! ret) as [[? ?] | ]; inv TYret; auto 
    ].
*
 rewrite insert_tce.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- insert_prop; apply andp_right; auto | ]
 end.
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl; 
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
apply derives_extract_PROP; intro LEN.
progress (autorewrite with norm1 norm2); normalize.
rewrite map_map. 
 clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
rewrite PROP_combine.
rewrite andp_comm.
apply andp_right.
apply andp_right.
apply andp_left1.
rewrite fold_right_and_app_low.
apply prop_derives; intros; split; auto.
 clear - PPRE.
 revert PPRE; induction Ppre; simpl; intuition.
apply andp_left2.
apply andp_derives.
intro rho. 
 unfold local, lift1. unfold_lift. simpl.
normalize.
intro rho.
unfold SEPx.
rewrite fold_right_sepcon_app.
auto.
 intro rho.
 unfold local, lift1. unfold_lift. simpl.
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=R)(Q:=nil) in MSUBST.
 rewrite <- insert_tce; rewrite PTREE.
 simpl. apply andp_left2.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 unfold local at 1, lift1.
 simpl.
 apply derives_extract_prop; intro. unfold_lift in H. subst vl.
 unfold PROPx, LOCALx, SEPx. simpl.
apply andp_left2. apply andp_left1.
 assert (LEN': length (var_names argsig) = length (eval_exprlist (argtypes argsig) bl rho)).
 clear - LEN.
  revert bl LEN; induction argsig as [ | [? ?]]; destruct bl; 
    simpl; intros; auto.
 inv LEN.
 forget (argtypes argsig) as tys.
 cut (local (fold_right `and `True (map locald_denote (LocalD Qtemp Qvar nil))) rho |-- `(local (fold_right `and `True (map locald_denote Qpre)))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 unfold_lift. unfold local, lift1. apply prop_derives.
 clear.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 eapply check_specs_lemma; try eassumption.
*
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 unfold normal_ret_assert. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1. 
 apply derives_trans with
   (EX  vret : B,
    `(PROPx (Ppost vret) 
     (LOCAL  (temp ret_temp (F vret))
      (SEPx (Rpost vret)))) (get_result1 ret)
     * PROPx P (LOCALx (tc_env (initialized ret Delta) :: map (subst_localdef ret old) Q) (SEPx Frame))).
 clear.
 go_lowerx. normalize. apply exp_right with x; normalize.
 apply exp_left; intro vret. apply exp_right with vret.
 normalize.
 progress (autorewrite with norm1 norm2); normalize.
 rewrite PROP_combine.
 unfold fold_right.
 go_lowerx.
 repeat apply andp_right; try apply prop_right; auto.
 rewrite !fold_right_and_app_low.
 rewrite !fold_right_and_app_low in H1. destruct H1; split; auto.
 split; auto.
 apply local2ptree_soundness'' in PTREE.
 unfold LOCALx in PTREE. rewrite !andp_TT in PTREE.
 simpl app. 
 clear - H3. rename H3 into H.
 induction Q; simpl in *; auto.
 destruct H, a; specialize (IHQ H0); try now (simpl; split; auto).
 hnf in H. unfold subst_localdef in H. 
 if_tac; [rewrite if_true in H by auto | rewrite if_false in H by auto]; simpl; auto.
Qed.

Lemma semax_call_id1_x_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret ret' id (paramty: typelist) (retty retty': type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type) 
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty') A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty') A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty) 
   (RETinit: (temp_types Delta) ! ret' = Some (retty', false))
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true) 
   (NEret: ret <> ret')
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
             |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar)
         (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) 
       |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
       |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (DELETE: delete_temp_from_locals ret Q = Qnew)
   (DELETE' : delete_temp_from_locals ret' Q = Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
   (Ssequence (Scall (Some ret')
             (Evar id (Tfunction paramty retty' cc_default))
             bl)
      (Sset ret (Ecast (Etempvar ret' retty') retty)))
    (normal_ret_assert Post2).     
Proof.
intros.
eapply semax_seq'.
eapply semax_call_id1_wow; try eassumption; auto.
  unfold typeof_temp; rewrite RETinit; reflexivity.
 simpl update_tycon.
 apply extract_exists_pre; intro vret.
*
 eapply semax_pre_post;
 [ | | apply semax_set_forward].
 +
 eapply derives_trans; [ | apply now_later ].
 instantiate (1:= (PROPx (P ++ Ppost vret)
  (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
 apply andp_right.
 apply andp_right.
 unfold tc_expr.
 unfold typecheck_expr; simpl.
 simpl denote_tc_assert.
 rewrite tycontext.temp_types_same_type'. rewrite RETinit.
 simpl @fst.
 replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
   with true
  by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; 
    reflexivity).
 simpl @snd. cbv iota.
 go_lowerx. simpl.
 apply neutral_isCastResultType; auto.
 unfold tc_temp_id, typecheck_temp_id.
 rewrite <- tycontext.initialized_ne by auto.
 unfold typeof_temp in TYret.
 destruct ((temp_types Delta) ! ret) as [[? ?]  | ]; inversion TYret; clear TYret; try subst t.
 go_lowerx.
 repeat rewrite denote_tc_assert_andp.
 rewrite denote_tc_assert_bool.
 assert (is_neutral_cast (implicit_deref retty) retty = true)
  by (destruct retty as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; simpl; auto;
        destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; inv NEUTRAL).
 apply andp_right. apply prop_right; auto.
 apply neutral_isCastResultType; auto.
 go_lowerx. normalize. apply andp_right; auto. apply prop_right.
 subst Qnew; clear - H4. rename H4 into H.
 induction Q; simpl in *; auto.
 destruct H, a; specialize (IHQ H0); try now (simpl; split; auto).
 hnf in H.
 if_tac; simpl; auto.
+
 intros. subst Post2.
 unfold normal_ret_assert.
 normalize. simpl exit_tycon.
 apply exp_right with vret; normalize.
 autorewrite with subst.
 go_lowerx.
 normalize. apply andp_right; auto.
 apply prop_right; split; auto.
 hnf. rewrite H1; unfold_lift.
 assert (eqb_ident ret ret' = false) 
 by (clear - NEret; pose proof (eqb_ident_spec ret ret');
       destruct (eqb_ident ret ret'); auto;
      contradiction NEret; intuition).
 rewrite H5 in *.
 hnf in H3. rewrite H3. 
 assert (tc_val retty' (eval_id ret' rho)).
 eapply tc_eval_id_i; try eassumption.
 rewrite <- initialized_ne by auto.
  rewrite temp_types_same_type'.
 rewrite RETinit. auto.
 assert (H7 := expr2.neutral_cast_lemma); 
   unfold eval_cast in H7. rewrite H7 by auto.
 unfold eval_id, env_set. simpl. rewrite Map.gso by auto. reflexivity.
 apply local2ptree_OKsubst in PTREE.
 subst Qnew; clear - H4 PTREE. rename H4 into H.
 induction Q; simpl in *; auto.
 destruct a; try now (destruct H; simpl in *; split; auto).
 if_tac; simpl in *; auto.
 destruct H; split; auto.
 hnf in H|-*; subst. unfold eval_id, env_set. simpl.
 rewrite Map.gso by auto. auto.
Qed.

Lemma semax_call_id1_y_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret ret' id (paramty: typelist) (retty retty': type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty') A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty') A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty) 
   (RETinit: (temp_types Delta) ! ret' = Some (retty', false))
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true) 
   (NEret: ret <> ret')
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
             |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar)
         (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) 
       |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
       |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (DELETE: delete_temp_from_locals ret Q = Qnew)
   (DELETE' : delete_temp_from_locals ret' Q = Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
   (Ssequence (Scall (Some ret')
             (Evar id (Tfunction paramty retty' cc_default))
             bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert Post2).  
Proof.
intros.
eapply semax_seq'.
eapply semax_call_id1_wow; try eassumption; auto;
  unfold typeof_temp; rewrite RETinit; reflexivity.
 simpl update_tycon.
 apply extract_exists_pre; intro vret.
*
 eapply semax_pre_post;
 [ | | apply semax_set_forward].
 +
 eapply derives_trans; [ | apply now_later ].
 instantiate (1:= (PROPx (P ++ Ppost vret)
  (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
 apply andp_right.
 apply andp_right.
 unfold tc_expr.
match goal with |- _ |-- ?A =>
  set (aa:=A); unfold denote_tc_assert in aa; simpl in aa; subst aa
end.
 rewrite tycontext.temp_types_same_type'. rewrite RETinit.
 simpl @fst.
 replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
   with true
  by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; 
    reflexivity).
 simpl @snd. cbv iota.
 apply @TT_right.
 unfold tc_temp_id, typecheck_temp_id.
 rewrite <- tycontext.initialized_ne by auto.
 unfold typeof_temp in TYret.
 destruct ((temp_types Delta) ! ret) as [[? ?]  | ]; inversion TYret; clear TYret; try subst t.
 go_lowerx.
 repeat rewrite denote_tc_assert_andp.
 rewrite denote_tc_assert_bool.
 assert (is_neutral_cast (implicit_deref retty') retty = true).
 replace (implicit_deref retty') with retty'
 by (destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; reflexivity).
 auto.
 apply andp_right. apply prop_right; auto.
 apply neutral_isCastResultType; auto.
 go_lowerx. normalize. apply andp_right; auto. apply prop_right.
 subst Qnew; clear - H4. rename H4 into H.
 induction Q; simpl in *; auto.
 destruct H, a; specialize (IHQ H0); try now (simpl; split; auto).
 hnf in H.
 if_tac; simpl; auto.
+
 intros. subst Post2.
 unfold normal_ret_assert.
 normalize. simpl exit_tycon.
 apply exp_right with vret; normalize.
 autorewrite with subst.
 go_lowerx.
 normalize. apply andp_right; auto.
 apply prop_right; split; auto.
 hnf. rewrite H1; unfold_lift.
 assert (eqb_ident ret ret' = false) 
 by (clear - NEret; pose proof (eqb_ident_spec ret ret');
       destruct (eqb_ident ret ret'); auto;
      contradiction NEret; intuition).
 rewrite H5 in *.
 hnf in H3. rewrite H3. unfold eval_id, env_set; simpl. rewrite Map.gso; auto.
 apply local2ptree_OKsubst in PTREE.
 subst Qnew; clear - H4 PTREE. rename H4 into H.
 induction Q; simpl in *; auto.
 destruct a; try now (destruct H; simpl in *; split; auto).
 if_tac; simpl in *; auto.
 destruct H; split; auto.
 hnf in H|-*; subst. unfold eval_id, env_set. simpl.
 rewrite Map.gso by auto. auto.
Qed.

Lemma semax_call_id01_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)))
   (_: check_retty retty)
         (* this hypothesis is not needed for soundness, just for selectivity *)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id0 with (x:=witness) (P:=P)(Q:=Q) (R := Frame)
   ];
   try eassumption.
*
 rewrite insert_tce.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- insert_prop; apply andp_right; auto | ]
 end.
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl; 
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
apply derives_extract_PROP; intro LEN.
 clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 normalize.
 progress (autorewrite with norm1 norm2); normalize.
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
rewrite PROP_combine.
rewrite andp_comm.
apply andp_right.
apply andp_right.
apply andp_left1.
rewrite fold_right_and_app_low.
apply prop_derives; intros; split; auto.
 clear - PPRE.
 revert PPRE; induction Ppre; simpl; intuition.
rewrite <- insert_tce.
apply andp_left2.
apply andp_left2.
apply andp_derives.
apply derives_refl.
intro rho; unfold SEPx.
 rewrite fold_right_sepcon_app.
 assumption.
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=R)(Q:=nil) in MSUBST.
 rewrite <- insert_tce; rewrite PTREE.
 apply andp_left2.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 unfold local at 1, lift1.
 intro rho;  simpl.
 apply  derives_extract_prop; intro. unfold_lift in H. subst vl.
 unfold PROPx, LOCALx, SEPx. simpl.
apply andp_left2. apply andp_left1.
 assert (LEN': length (var_names argsig) = length (eval_exprlist (argtypes argsig) bl rho)).
 clear - LEN.
  revert bl LEN; induction argsig as [ | [? ?]]; destruct bl; 
    simpl; intros; auto.
 inv LEN.
 forget (argtypes argsig) as tys.
 cut (local (fold_right `and `True (map locald_denote (LocalD Qtemp Qvar nil))) rho |-- 
                 `(local (fold_right `and `True (map locald_denote Qpre)))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 eapply check_specs_lemma; try eassumption.
*
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 unfold normal_ret_assert. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 match goal with |- context [ifvoid retty ?A ?B] =>
   replace (ifvoid retty A B) with B
   by (destruct retty; try contradiction; auto)
 end.
 go_lowerx. normalize. apply exp_right with x0; normalize.
 apply andp_right; auto.
 apply prop_right.
 rewrite fold_right_and_app_low. split; auto.
 rename x0 into vret.
 clear.
 rewrite fold_right_sepcon_app. auto.
Qed.

Lemma semax_call_id00_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R id (paramty: typelist) (bl: list expr)
                  (argsig: list (ident * type)) (retty: type) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,Tvoid) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)))
   (RETTY: retty = Tvoid)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
          |-- (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R |-- fold_right sepcon emp Rpre * fold_right sepcon emp Frame)
   (POST1: Post witness = (EX vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty Tvoid cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id0 with (x:=witness) (P:=P)(Q:=Q) (R := Frame)
   ];
   try eassumption.
*
 rewrite insert_tce.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- insert_prop; apply andp_right; auto | ]
 end.
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx. 
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl; 
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
apply derives_extract_PROP; intro LEN.
 clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 normalize.
 progress (autorewrite with norm1 norm2); normalize.
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
rewrite PROP_combine.
rewrite andp_comm.
apply andp_right.
apply andp_right.
apply andp_left1.
rewrite fold_right_and_app_low.
apply prop_derives; intros; split; auto.
 clear - PPRE.
 revert PPRE; induction Ppre; simpl; intuition.
rewrite <- insert_tce.
apply andp_left2.
apply andp_left2.
apply andp_derives.
apply derives_refl.
intro rho; unfold SEPx.
 rewrite fold_right_sepcon_app.
 assumption.
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=R)(Q:=nil) in MSUBST.
 rewrite <- insert_local; rewrite PTREE.
 intro rho.
 unfold local, lift1. unfold_lift. simpl.
 apply andp_left2.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 unfold local at 1, lift1.
 simpl.
 apply derives_extract_prop; intro. unfold_lift in H. subst vl.
 unfold PROPx, LOCALx, SEPx. simpl.
apply andp_left2. apply andp_left1.
 assert (LEN': length (var_names argsig) = length (eval_exprlist (argtypes argsig) bl rho)).
 clear - LEN.
  revert bl LEN; induction argsig as [ | [? ?]]; destruct bl; 
    simpl; intros; auto.
 inv LEN.
 forget (argtypes argsig) as tys.
 cut (local (fold_right `and `True (map locald_denote (LocalD Qtemp Qvar nil))) rho |--
            `(local (fold_right `and `True (map locald_denote Qpre)))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 eapply check_specs_lemma; try eassumption.
*
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 unfold normal_ret_assert. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 unfold ifvoid.
 go_lowerx. normalize.
 apply exp_right with x.
 apply andp_right.
 apply prop_right.
 split; auto.
 normalize.
 rewrite fold_right_and_app_low.
 rewrite prop_true_andp by (split; auto).
 rewrite fold_right_sepcon_app. auto.
Qed.  

Lemma no_post_exists:
 forall v P Q R,
   PROPx P (LOCALx (temp ret_temp v :: Q) (SEPx R)) =
   EX x:val, PROPx ((x=v) :: P) (LOCALx (temp ret_temp x :: Q) (SEPx R)).
Proof.
intros.
apply pred_ext.
apply exp_right with v.
apply andp_derives; auto.
apply prop_derives.
simpl. intuition.
apply exp_left; intro.
unfold PROPx.
simpl fold_right.
normalize.
Qed.

Lemma no_post_exists0:
 forall P Q R,
   PROPx P (LOCALx Q (SEPx R)) =
   EX x:unit, PROPx ((fun _ => P) x) (LOCALx Q (SEPx ((fun _ => R) x))).
Proof.
intros.
apply pred_ext.
apply exp_right with tt.
apply andp_derives; auto.
apply exp_left; auto.
Qed.
