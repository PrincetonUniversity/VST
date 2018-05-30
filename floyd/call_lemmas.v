Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
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

Definition removeopt_localdef (ret: option ident) (l: list localdef) : list localdef :=
  match ret with
   | Some id => remove_localdef_temp id l
   | None => l
   end.

Lemma semax_call': forall Espec {cs: compspecs} Delta A Pre Post NEPre NEPost ts x ret argsig retsig cc a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, _ => True
   end ->
   tc_fn_return Delta ret retsig ->
  @semax cs Espec Delta
          (|>(tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl)
           &&
   (|>`(Pre ts x: environ -> mpred) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) *
                      `(func_ptr' (mk_funspec (argsig,retsig) cc A Pre Post NEPre NEPost)) (eval_expr a)
     * |>PROPx P (LOCALx Q (SEPx R))))
          (Scall ret a bl)
          (normal_ret_assert
            (maybe_retval (Post ts x) retsig ret *
               PROPx P (LOCALx (removeopt_localdef ret Q) (SEPx R)))).
Proof.
  intros. rename H1 into Hret.
  rewrite argtypes_eq.
  eapply semax_pre_post'; [ | |
    apply (semax_call Delta A Pre Post NEPre NEPost ts x (PROPx P (LOCALx Q (SEPx R))) ret argsig retsig cc a bl H); auto].
  Focus 3. {
    clear - H0.
    destruct retsig; destruct ret; simpl in *; try contradiction;
    intros; congruence.
  } Unfocus.
  + clear Hret.
    unfold_lift; unfold local, lift1. unfold func_ptr'. intro rho; simpl.
    normalize;
    progress (autorewrite with subst norm1 norm2; normalize).
    apply andp_derives; auto.
    rewrite sepcon_assoc, sepcon_comm.
    rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
    rewrite sepcon_comm. rewrite emp_sepcon.
    apply andp_derives; auto.
    rewrite sepcon_comm, <- later_sepcon.
    progress (autorewrite with subst norm1 norm2; normalize).
  + intros.
    autorewrite with ret_assert.
    normalize.
    destruct ret.
    - eapply derives_trans; [| apply sepcon_derives; [apply derives_refl | apply remove_localdef_temp_PROP]].
      normalize.
      apply exp_right with old.
      autorewrite with subst.
      intro rho; simpl; normalize.
      autorewrite with norm1 norm2; normalize.
      rewrite sepcon_comm; auto.
    - intro rho; simpl; normalize.
      rewrite sepcon_comm; auto.
      unfold substopt.
      repeat rewrite list_map_identity.
      normalize.
      autorewrite with norm1 norm2; normalize.
Qed.

Lemma semax_call1: forall Espec {cs: compspecs} Delta A Pre Post NEPre NEPost ts x id argsig retsig cc a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc ->
   match retsig with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some id) retsig ->
  @semax cs Espec Delta
         (|>(tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl)
           && (|>`(Pre ts x: environ -> mpred) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) *
                 `(func_ptr' (mk_funspec (argsig,retsig) cc A Pre Post NEPre NEPost)) (eval_expr a) *
                  |>PROPx P (LOCALx Q (SEPx R))))
          (Scall (Some id) a bl)
          (normal_ret_assert
            (`(Post ts x: environ -> mpred) (get_result1 id)
               * PROPx P (LOCALx (remove_localdef_temp id Q) (SEPx R)))).
Proof.
intros.
apply semax_call'; auto.
Qed.

Definition ifvoid {T} t (A B: T) :=
 match t with Tvoid => A | _ => B end.

Lemma semax_call0: forall Espec {cs: compspecs} Delta A Pre Post NEPre NEPost ts x
      argsig retty cc a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc ->
  @semax cs Espec Delta
         (|>(tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl)
           && (|>`(Pre ts x: environ -> mpred) ( (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)))
                 * `(func_ptr' (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost)) (eval_expr a)
                 * |>PROPx P (LOCALx Q (SEPx R))))
          (Scall None a bl)
          (normal_ret_assert
            (ifvoid retty (`(Post ts x: environ -> mpred) (make_args nil nil))
                                                        (EX v:val, `(Post ts x: environ -> mpred) (make_args (ret_temp::nil) (v::nil)))
            * PROPx P (LOCALx Q (SEPx R)))).
Proof.
intros.
rewrite argtypes_eq.
eapply semax_pre_post'; [ | |
   apply (semax_call Delta A Pre Post NEPre NEPost ts x (PROPx P (LOCALx Q (SEPx R))) None argsig retty cc a bl H)].
 Focus 3.
 split; intros; congruence.
 intro rho; normalize.
 autorewrite with norm1 norm2; normalize.
unfold func_ptr'.
rewrite !sepcon_assoc.
apply andp_derives; auto.
rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon, sepcon_comm.
rewrite !corable_andp_sepcon1 by apply corable_func_ptr.
apply andp_derives; auto.
rewrite later_sepcon; apply derives_refl.
intros.
apply andp_left2.
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
        (|>TC && (local (tc_environ Delta) &&
                     (`(func_ptr' f) (eval_var id (type_of_funspec f))
                     * |>PQR)))
                              c PostCond ->
       @semax cs Espec Delta (|>(TC && PQR)) c PostCond.
Proof.
intros.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply H1;
 try (apply andp_left2; apply derives_refl).
apply andp_right.
rewrite later_andp.
rewrite <- !andp_assoc.
rewrite !andp_assoc; apply andp_left2, andp_left1; auto.
apply andp_derives; auto.
clear H1.
rewrite later_andp.
unfold_lift. unfold func_ptr'.
intro rho; simpl; normalize.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite andp_comm.
apply andp_derives; auto.
rewrite emp_sepcon; auto.
apply andp_left2; auto.
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

Lemma eqb_calling_convention_refl:
  forall cc, eqb_calling_convention cc cc = true.
Proof.
intros.
unfold eqb_calling_convention.
destruct cc; simpl.
destruct cc_vararg, cc_unproto, cc_structret; reflexivity.
Qed.

(* TODO: Change argument order. ==> A Pre Post NEPre NEPost ts x *)
Lemma semax_call_id0:
 forall Espec {cs: compspecs} Delta P Q R id bl argsig retty cc A ts x Pre Post NEPre NEPost
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost)) ->
  @semax cs Espec Delta (|> (tc_exprlist Delta (argtypes argsig) bl
                  && (`(Pre ts x: environ -> mpred) (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl))
                         * PROPx P (LOCALx Q (SEPx R)))))
    (Scall None (Evar id (Tfunction (type_of_params argsig) retty cc)) bl)
    (normal_ret_assert
       ((ifvoid retty (`(Post ts x: environ -> mpred) (make_args nil nil))
                                                   (EX v:val, `(Post ts x: environ -> mpred) (make_args (ret_temp::nil) (v::nil))))
         * PROPx P (LOCALx Q (SEPx R)))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Evar id (Tfunction (type_of_params argsig) retty cc)))=
               Cop.fun_case_f (type_of_params argsig) retty cc).
simpl. subst. reflexivity.
apply (semax_fun_id' id (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost)
  (tc_exprlist Delta (argtypes argsig) bl)); auto.
subst.

eapply semax_pre_simple; [ | apply (@semax_call0 Espec cs Delta A Pre Post NEPre NEPost ts x argsig _ cc _ bl P Q R)].
rewrite later_andp.
apply andp_right.
apply andp_right.
eapply derives_trans, now_later.
apply andp_left1.
intro rho; unfold tc_expr; simpl.
subst.
norm_rewrite. apply prop_left; intro.
unfold get_var_type. rewrite GLBL. rewrite H0.
rewrite denote_tc_assert_bool; simpl. apply prop_right.
simpl.
rewrite eqb_typelist_refl.
simpl. auto.
unfold_lift; auto.
rewrite eqb_type_refl. simpl.
apply eqb_calling_convention_refl.
apply andp_left2, andp_left1; auto.
apply andp_left2, andp_left2, andp_left2.
intro; simpl.
rewrite later_sepcon, <- sepcon_assoc.
apply sepcon_derives; auto.
rewrite sepcon_comm; apply derives_refl.
auto.
Qed.

Lemma semax_call_id1:
 forall Espec {cs: compspecs} Delta P Q R ret id retty cc bl argsig A ts x Pre Post NEPre NEPost
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
  @semax cs Espec Delta (|>(tc_exprlist Delta (argtypes argsig) bl &&
                (`(Pre ts x: environ -> mpred) (make_args' (argsig,Tvoid) (eval_exprlist (argtypes argsig) bl))
                  * PROPx P (LOCALx Q (SEPx R)))))
    (Scall (Some ret)
             (Evar id (Tfunction (type_of_params argsig) retty cc))
             bl)
    (normal_ret_assert
       ((`(Post ts x: environ -> mpred) (get_result1 ret)
           * PROPx P (LOCALx (remove_localdef_temp ret Q) (SEPx R))))).
Proof.
intros. rename H0 into Ht. rename H1 into H0.
 rename H2 into Hret.
assert (Cop.classify_fun (typeof (Evar id (Tfunction (type_of_params argsig) retty cc)))=
               Cop.fun_case_f (type_of_params argsig) retty cc).
subst; reflexivity.
apply (semax_fun_id' id (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost)); auto.
subst.
eapply semax_pre_simple; [ | apply (semax_call1 Espec Delta A Pre Post NEPre NEPost ts x ret argsig retty cc _ bl P Q R H1 H0); auto].
apply andp_right.
rewrite later_andp; apply andp_right.
eapply derives_trans, now_later.
apply andp_left1.
intro rho; unfold tc_expr, local,lift1; simpl.
subst.
norm_rewrite.
unfold get_var_type. rewrite GLBL. rewrite Ht.
rewrite denote_tc_assert_bool.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. apply prop_right; apply eqb_calling_convention_refl.
apply andp_left2.
apply andp_left1.
auto.
apply andp_left2.
apply andp_left2.
apply andp_left2.
rewrite later_sepcon, <- sepcon_assoc.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply derives_refl.
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
  fold_right `(and) `(True) (Q1 ++ Q2)  =
  `(and) (fold_right `(and) `(True) Q1) (fold_right `(and) `(True) Q2).
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

Lemma isolate_LOCAL_lem1:
  forall Q, PROPx nil (LOCALx Q (SEPx (TT::nil))) = local (fold_right `(and) `(True) (map locald_denote Q)).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, SEPx.
 simpl fold_right_sepcon.
 normalize.
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
    Map.get (ge_of (make_args fl vl rho)) i = Map.get (ge_of rho) i.
Proof.
 induction fl; destruct vl; simpl; auto.
Qed.

Lemma check_specs_lemma:
  forall Qtemp Qpre_temp Qvar G Qpre_var rho fl vl
    (LEN: length fl = length vl),
    Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) ->
    Forall (check_one_temp_spec (pTree_from_elements (combine fl vl)))
           (PTree.elements Qpre_temp) ->
    fold_right `(and) `(True) (map locald_denote (LocalD Qtemp Qvar (map gvars G))) rho ->
    fold_right `(and) `(True) (map locald_denote (map gvars G)) rho ->
    fold_right `(and) `(True) (map locald_denote (LocalD Qpre_temp Qpre_var (map gvars G))) (make_args fl vl rho).
Proof.
  intros.
  apply local_ext_rev.
  specialize (fun (Q0: environ -> Prop) H => local_ext Q0 _ _ H H1).
  clear H1; intros.
  specialize (fun (Q0: localdef) H => H1 (locald_denote Q0) (in_map _ _ _ H)).
  specialize (fun (Q0: localdef) H => H1 Q0 (LocalD_sound _ _ _ _ H)).
  assert (ASSU1: forall i v, Qtemp ! i = Some v -> locald_denote (temp i v) rho) by (intros; apply H1; firstorder).
  assert (ASSU2: forall i t v v', Qvar ! i = Some (vardesc_local_global t v v') -> locald_denote (lvar i t v) rho) by (intros; apply H1; eauto 50).
  assert (ASSU3: forall i t v v', Qvar ! i = Some (vardesc_local_global t v v') -> locald_denote (sgvar i v') rho) by (intros; apply H1; eauto 50).
  assert (ASSU4: forall i t v, Qvar ! i = Some (vardesc_local t v) -> locald_denote (lvar i t v) rho) by (intros; apply H1; eauto 50).
  assert (ASSU5: forall i v, Qvar ! i = Some (vardesc_visible_global v) -> locald_denote (gvar i v) rho) by (intros; apply H1; eauto 50).
  assert (ASSU6: forall i v, Qvar ! i = Some (vardesc_shadowed_global v) -> locald_denote (sgvar i v) rho) by (intros; apply H1; eauto 50).
  assert (ASSU7: forall Q0, In Q0 (map gvars G) -> locald_denote Q0 rho) by (intros; apply H1; eauto 50).
  clear H1.
  apply list_in_map_inv in H3.
  destruct H3 as [Q0' [? ?]]; subst; rename Q0' into Q0.
  apply LocalD_complete in H3.
  destruct H3 as [ [i [v [?H ?H]]]
                 |[ [i [t [v [v' [?H ?H]]]]]
                 |[ [i [t [v [v' [?H ?H]]]]]
                 |[ [i [t [v [?H ?H]]]]
                 |[ [i [v [?H ?H]]]
                 |[ [i [v [?H ?H]]]
                 | ?H ]]]]]];
    [subst; unfold locald_denote; unfold_lift .. |].
  + clear - H0 H1.
    pose proof (Forall_ptree_elements_e _ _ _ _ _ H0 H1).
    hnf in H. simpl in H.
    clear - H.
    eapply pTree_from_elements_e1; eauto.
  + pose proof (Forall_ptree_elements_e _ _ _ _ _ H H1).
    hnf in H3; simpl in H3.
    destruct (Qvar ! i) as [[?|?|?|?]|]; inv H3.
  + pose proof (Forall_ptree_elements_e _ _ _ _ _ H H1).
    hnf in H3; simpl in H3.
    destruct (Qvar ! i) as [[?|?|?|?]|]; inv H3.
  + pose proof (Forall_ptree_elements_e _ _ _ _ _ H H1).
    hnf in H3; simpl in H3.
    destruct (Qvar ! i) as [[?|?|?|?]|]; inv H3.
  + pose proof (Forall_ptree_elements_e _ _ _ _ _ H H1).
    hnf in H3; simpl in H3.
    destruct (Qvar ! i) as [[?|?|?|?]|] eqn:?H; inv H3.
    - specialize (ASSU2 i t _ _ H4).
      specialize (ASSU3 i t _ _ H4).
      hnf in ASSU2, ASSU3 |- *.
      rewrite (ve_of_make_args _ _ _ _ LEN).
      rewrite ge_of_make_args. auto.
    - specialize (ASSU5 i _ H4).
      hnf in ASSU5 |- *.
      rewrite (ve_of_make_args _ _ _ _ LEN).
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      rewrite ge_of_make_args. auto.
    - specialize (ASSU6 i _ H4).
      hnf in ASSU6 |- *.
      rewrite (ve_of_make_args _ _ _ _ LEN).
      rewrite ge_of_make_args. auto.
  + pose proof (Forall_ptree_elements_e _ _ _ _ _ H H1).
    hnf in H3; simpl in H3.
    destruct (Qvar ! i) as [[?|?|?|?]|] eqn:?H; inv H3.
    - specialize (ASSU5 i _ H4).
      hnf in ASSU5 |- *.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      rewrite ge_of_make_args. auto.
    - specialize (ASSU6 i _ H4).
      hnf in ASSU6 |- *.
      rewrite ge_of_make_args. auto.
  + specialize (ASSU7 _ H1).
    apply list_in_map_inv in H1.
    destruct H1 as [gv [? ?]]; subst.
    hnf in ASSU7 |- *. subst.
    extensionality i. rewrite ge_of_make_args. auto.
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
     local (fold_right `(and) `(True) (map (fun q : environ -> Prop => `q f) (map locald_denote Q)))
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

Definition global_funspec Delta id argsig retty cc A Pre Post NEPre NEPost :=
   (var_types Delta) ! id = None /\
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) /\
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost)).

Lemma lookup_funspec:
  forall Delta id argsig retty cc A Pre Post NEPre NEPost,
   (var_types Delta) ! id = None ->
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) ->
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost)) ->
   global_funspec Delta id argsig retty cc A Pre Post NEPre NEPost.
Proof.
intros.
split3; auto.
Qed.


Lemma func_ptr'_func_ptr_lifted:
forall (fs: funspec) (e: environ->val) (B: environ->mpred),
 `(func_ptr' fs) e * B = `(func_ptr fs) e && B.
Proof.
intros.
extensionality rho.
unfold_lift. unfold func_ptr'.
simpl.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon; auto.
Qed.

Definition can_assume_funcptr cs Delta P Q R a fs :=
 forall Espec c Post,
 @semax cs Espec Delta ((EX v: val, (lift0 (func_ptr fs v) && local (`(eq v) (eval_expr a)))) &&
                   PROPx P (LOCALx Q (SEPx R))) c Post -> 
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.

Definition call_setup1 
  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
 :=
  local2ptree Q = (Qtemp, Qvar, nil, map gvars G) /\
  can_assume_funcptr  cs Delta P Q R' a (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) /\
  PROPx P (LOCALx Q (SEPx R')) |-- |> PROPx P (LOCALx Q (SEPx R)) /\
  Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
         |-- (tc_expr Delta a)  /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl) /\
  force_list (map (msubst_eval_expr Qtemp Qvar)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl /\
  pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals.

Lemma call_setup1_i:
 forall (cs: compspecs) Delta P Q R R' (a: expr) (bl: list expr)
   Qtemp Qvar G (v: val)   
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (vl : list val)
  (Qactuals : PTree.t _),
  local2ptree Q = (Qtemp, Qvar, nil, map gvars G) ->
  msubst_eval_expr Qtemp Qvar a = Some v ->
  fold_right_sepcon R' |--  func_ptr (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) v ->
  fold_right_sepcon R' |-- |> fold_right_sepcon R ->
  Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
         |-- (tc_expr Delta a)  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl) ->
  force_list (map (msubst_eval_expr Qtemp Qvar)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl ->
  pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
 call_setup1 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals.
Proof. intros.
assert (H8 := @msubst_eval_expr_eq cs P Qtemp Qvar (map gvars G) R' a v H0).
assert (H9 := local2ptree_soundness P Q R' Qtemp Qvar nil (map gvars G) H).
repeat split; auto.
hnf; intros.
eapply semax_pre; [ | eassumption].
clear c Post0 H10.
Exists v.
apply andp_right; [ | apply andp_left2; auto].
apply andp_right.
repeat apply andp_left2.
intro rho; unfold SEPx, lift0.
apply H1.
rewrite H9.
simpl app.
apply andp_left2, H8.
unfold PROPx, LOCALx.
rewrite <- !andp_assoc, later_andp; apply andp_derives; [apply now_later|].
unfold SEPx; simpl; auto.
Qed.

Lemma call_setup1_i2:
 forall (cs: compspecs) Delta P Q R R' (id: ident) (ty: type) (bl: list expr)
   Qtemp Qvar G
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (vl : list val)
  (Qactuals : PTree.t _),
  local2ptree Q = (Qtemp, Qvar, nil, map gvars G) ->
  can_assume_funcptr  cs Delta P Q R' (Evar id ty) (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) ->
  PROPx P (LOCALx Q (SEPx R')) |-- |> PROPx P (LOCALx Q (SEPx R)) ->
  Cop.classify_fun ty = Cop.fun_case_f (type_of_params argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
         |-- (tc_expr Delta (Evar id ty))  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl) ->
  force_list (map (msubst_eval_expr Qtemp Qvar)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl ->
  pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
 call_setup1 cs Qtemp Qvar G (Evar id ty) Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals.
Proof. intros.
 repeat split; auto.
Qed.

Lemma can_assume_funcptr1:
  forall  cs Delta P Q R a fs v Qtemp Qvar,
  local2ptree Q = (Qtemp, Qvar, nil, nil) ->
  msubst_eval_expr Qtemp Qvar a = Some v ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- lift0(func_ptr fs v) ->
   can_assume_funcptr cs Delta P Q R a fs.
Proof.
intros.
unfold can_assume_funcptr; intros.
eapply semax_pre; [ | eassumption].
apply andp_right; [ | apply andp_left2; auto].
Exists v.
apply andp_right; auto.
assert (H8 := @msubst_eval_expr_eq cs P Qtemp Qvar nil R a v H0).
eapply local2ptree_soundness' in H.
simpl in H; rewrite <- H in H8.
eapply derives_trans, H8.
apply andp_left2.
unfold LocalD.
rewrite !PTree.fold_spec. simpl fold_left. rewrite app_nil_r; auto.
Qed.

Lemma can_assume_funcptr2:
  forall id ty cs Delta P Q R fs ,
   (var_types Delta) ! id = None ->
   (glob_specs Delta) ! id = Some fs ->
   (glob_types Delta) ! id = Some (type_of_funspec fs) ->
   ty = (type_of_funspec fs) ->
   can_assume_funcptr cs Delta P Q R (Evar id ty) fs.
Proof.
unfold can_assume_funcptr; intros.
eapply (semax_fun_id id); try eassumption.
eapply semax_pre; try apply H3. clear H3.
apply andp_right; [ | apply andp_left2; apply andp_left1; auto].
apply andp_left2.
apply andp_left2.
intro rho.
unfold_lift.
unfold local, lift0, lift1.
simpl.
Exists (eval_var id (type_of_funspec fs) rho).
apply andp_right; auto.
apply prop_right.
subst ty.
auto.
Qed.

Definition call_setup2 
  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
  (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  (Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G':=
 call_setup1 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals /\
  Pre nil witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) /\
  local2ptree Qpre = (Qpre_temp, Qpre_var, nil, map gvars G') /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) /\
  Forall (fun x => In x G) G' /\
  fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame.

Lemma call_setup2_i:
 forall  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
  (SETUP1: call_setup1 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals)
  (witness': functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  (Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G',
  Pre nil witness' = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ->
  local2ptree Qpre = (Qpre_temp, Qpre_var, nil, map gvars G') ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var)  ->
  Forall (fun x => In x G) G' ->
  fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame ->
  call_setup2 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness' Frame Ppre Qpre Rpre Qpre_temp Qpre_var G'.
Proof.
 intros. split. auto. repeat split; auto.
Qed.

Lemma in_gvars_sub:
  forall rho G G', Forall (fun x : globals => In x G) G' ->
  fold_right `(and) `(True) (map locald_denote (map gvars G)) rho ->
  fold_right `(and) `(True) (map locald_denote (map gvars G')) rho.
Proof.
intros.
pose proof (proj1 (Forall_forall _ G') H).
clear H.
revert H1; induction G'; simpl; intros; constructor.
assert (In a G).
apply H1; auto.
clear - H0 H.
induction G; destruct H. subst. destruct H0. auto.
destruct H0.
auto.
apply IHG'.
intros.
apply H1. right; auto.
Qed.

Lemma semax_call_aux55:
 forall (cs: compspecs) (Qtemp: PTree.t val) (Qvar: PTree.t vardesc) G (a: expr)
     Delta P Q R argsig retty cc A Pre Post NEPre NEPost 
    witness Frame bl Ppre Qpre Rpre Qactuals Qpre_temp G' Qpre_var vl
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, map gvars G))
 (TC0 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta a)
 (TC1 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
             |-- tc_exprlist Delta (argtypes argsig) bl)
 (MSUBST : force_list (map (msubst_eval_expr Qtemp Qvar)
              (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
 (PTREE'' : pTree_from_elements (combine (var_names argsig) vl) = Qactuals)
 (PRE1 : Pre nil witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
 (PTREE' : local2ptree Qpre = (Qpre_temp, Qpre_var, nil, map gvars G')) 
 (CHECKTEMP : Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
 (CHECKVAR : Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
 (CHECKG: Forall (fun x => In x G) G')
 (FRAME : fold_right_sepcon R
           |-- fold_right_sepcon Rpre * fold_right_sepcon Frame)
 (PPRE : fold_right_and True Ppre)
 (LEN : length (argtypes argsig) = length bl),
ENTAIL Delta,
(EX v : val,
 lift0 (func_ptr (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) v) &&
 local (` (eq v) (eval_expr a))) && |>PROPx P (LOCALx Q (SEPx R))
|-- |> (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl) &&
    (|> ` (Pre nil witness)
       (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) *
     ` (func_ptr' (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost))
       (eval_expr a) * |>PROPx P (LOCALx Q (SEPx Frame))).
Proof.
intros.
rewrite !exp_andp1. Intros v.
rewrite later_andp; repeat apply andp_right; auto.
{ eapply derives_trans, later_derives, TC0.
  rewrite later_andp; apply andp_derives; [apply now_later|].
  apply andp_left2, derives_refl. }
{ eapply derives_trans, later_derives, TC1.
  rewrite later_andp; apply andp_derives; [apply now_later|].
  apply andp_left2, derives_refl. }
rewrite PRE1.
match goal with |- _ |-- ?A * ?B * ?C => pull_right B end.
rewrite sepcon_comm.
rewrite func_ptr'_func_ptr_lifted.
apply ENTAIL_trans with
 (`(func_ptr (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost)) (eval_expr a) &&
      |>PROPx P (LOCALx Q (SEPx R))).
apply andp_left2.
apply andp_right; [  | apply andp_left2; auto].
apply andp_left1.
intro rho; unfold_lift; unfold local, lift0, lift1; simpl. normalize.
apply andp_right.
apply andp_left2; apply andp_left1; auto.
eapply derives_trans;[ apply andp_derives; [apply derives_refl | apply andp_left2; apply derives_refl] |].
subst Qactuals.
clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP CHECKG.
rewrite <- later_sepcon.
 progress (autorewrite with norm1 norm2).
rewrite PROP_combine.
rewrite (andp_comm (local (fold_right _ _ _))).
rewrite later_andp; apply andp_right.
+
apply andp_left2.
apply later_derives.
apply andp_right.
apply andp_left1.
rewrite fold_right_and_app_low.
apply prop_derives; intros; split; auto.
 clear - PPRE.
 revert PPRE; induction Ppre; simpl; intuition.
apply andp_left2.
apply andp_derives.
apply derives_refl.
intro rho; unfold SEPx.
 rewrite fold_right_sepcon_app.
 assumption.
+
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=R)(Q:=map gvars G) in MSUBST.
 rewrite PTREE.
 intro rho.
 unfold local, lift1. unfold_lift. simpl.
 apply andp_left2, later_derives.
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
 cut (local (fold_right `(and) `(True) (map locald_denote (LocalD Qtemp Qvar (map gvars G)))) rho |--
            `(local (fold_right `(and) `(True) (map locald_denote Qpre)))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |].
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 eapply check_specs_lemma; try eassumption.
 instantiate (1:=Qtemp).
 -
  clear - CHECKG H.
  apply local_ext_rev.
  specialize (fun (Q0: environ -> Prop) HH => local_ext Q0 _ _ HH H).
  clear H; intros.
  apply (H Q0); clear H.
  apply list_in_map_inv in H0.
  destruct H0 as [? [? ?]]; subst.
  apply in_map.
  apply LocalD_sound; apply LocalD_complete in H0.
  rewrite Forall_forall in CHECKG.
  destruct H0 as [| [| [| [| [| [|]]]]]]; auto 50.
  repeat right.
  apply list_in_map_inv in H.
  destruct H as [? [? ?]]; subst.
  apply in_map.
  apply CHECKG; auto.
 -
  clear - CHECKG H.
  apply local_ext_rev.
  specialize (fun (Q0: environ -> Prop) HH => local_ext Q0 _ _ HH H).
  clear H; intros.
  apply (H Q0); clear H.
  apply list_in_map_inv in H0.
  destruct H0 as [? [? ?]]; subst.
  apply in_map.
  apply LocalD_sound.
  rewrite Forall_forall in CHECKG.
  repeat right.
  apply list_in_map_inv in H0.
  destruct H0 as [? [? ?]]; subst.
  apply in_map.
  apply CHECKG; auto.
Qed.

Lemma tc_exprlist_len : forall {cs : compspecs} Delta argsig bl,
  tc_exprlist Delta (argtypes argsig) bl |-- !!(length (argtypes argsig) = length bl).
Proof.
 intros.
 go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl;
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. simpl. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
Qed.

Lemma semax_call_id00_wow:
 forall  
  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var G')
  Espec 
             (Post2: environ -> mpred)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpost: B -> list mpred)
   (RETTY: retty = Tvoid)
   (POST1: Post nil witness = (EX vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof.
intros.
destruct SETUP as [[PTREE [SPEC [HR' [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]]]
                            [PRE1 [PTREE' [CHECKTEMP [CHECKVAR [CHECKG FRAME]]]]]].
apply SPEC. clear SPEC.
eapply semax_pre; [apply andp_right; [apply andp_left2, andp_left1, derives_refl|]|].
{ rewrite <- andp_assoc, andp_comm.
  rewrite <- andp_assoc; apply andp_left1.
  rewrite andp_comm.
  eapply derives_trans; [apply andp_derives, HR'; apply derives_refl|].
  apply later_left2.
  apply andp_right, andp_left2, derives_refl.
  apply andp_right, CHECKTEMP.
  apply andp_right, CHECKVAR.
  eapply derives_trans, tc_exprlist_len; apply TC1. }
rewrite later_andp, andp_comm, andp_assoc.
rewrite <- !prop_and.
apply semax_extract_later_prop; intros [[]].
rewrite andp_comm.
eapply semax_pre_post' ; [ | |
   apply (@semax_call0 Espec cs Delta A Pre Post NEPre NEPost 
              nil witness argsig retty cc a bl P Q Frame)].
*
eapply semax_call_aux55; eauto.
*
 subst.
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 unfold ifvoid.
 go_lowerx. normalize.
 apply exp_right with x.
 rewrite fold_right_and_app_low.
 rewrite fold_right_sepcon_app.
 apply andp_right.
 apply prop_right.
 split; auto.
 normalize.
*
assumption.
Qed.

Lemma semax_call_id1_wow:
 forall  
  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var G')
   ret (Post2: environ -> mpred)  (Qnew: list localdef)
    (B: Type) (Ppost: B -> list Prop) (F: B -> val) (Rpost: B -> list mpred) Espec
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: check_retty retty)
   (POST1: Post nil witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall (Some ret) a bl)
    (normal_ret_assert Post2).
Proof.
intros.
destruct SETUP as [[PTREE [SPEC [HR' [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]]]
                            [PRE1 [PTREE' [CHECKTEMP [CHECKVAR [CHECKG FRAME]]]]]].
apply SPEC. clear SPEC.
eapply semax_pre; [apply andp_right; [apply andp_left2, andp_left1, derives_refl|]|].
{ rewrite <- andp_assoc, andp_comm.
  rewrite <- andp_assoc; apply andp_left1.
  rewrite andp_comm.
  eapply derives_trans; [apply andp_derives, HR'; apply derives_refl|].
  apply later_left2.
  apply andp_right, andp_left2, derives_refl.
  apply andp_right, CHECKTEMP.
  apply andp_right, CHECKVAR.
  eapply derives_trans, tc_exprlist_len; apply TC1. }
rewrite later_andp, andp_comm, andp_assoc.
rewrite <- !prop_and.
apply semax_extract_later_prop; intros [[]].
rewrite andp_comm.
eapply semax_pre_post'; [ | |
   apply (@semax_call1 Espec cs Delta A Pre Post NEPre NEPost 
              nil witness ret argsig retty cc a bl P Q Frame)];
 [ | 
 | assumption
 | clear - OKretty; destruct retty; inv OKretty; apply I
 | hnf; clear - TYret; unfold typeof_temp in TYret;
      destruct ((temp_types Delta) ! ret) as [[? ?] | ]; inv TYret; auto
 ].
*
eapply semax_call_aux55; eauto.
*
 subst.
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 apply derives_trans with
   (EX  vret : B,
    `(PROPx (Ppost vret)
     (LOCAL  (temp ret_temp (F vret))
      (SEPx (Rpost vret))))%assert (get_result1 ret)
     * (local (tc_environ (initialized ret Delta)) && PROPx P (LOCALx (remove_localdef_temp ret Q) (SEPx Frame)))).
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
 rewrite !fold_right_and_app_low in H5. destruct H5; split; auto.
Qed.

Lemma semax_call_id1_x_wow:
 forall  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty' cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar G a Delta P Q R R' argsig retty' cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var G')
   retty  Espec ret ret'
             (Post2: environ -> mpred)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) ! ret' = Some (retty', false))
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true)
   (NEret: ret <> ret')
   (POST1: Post nil witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R')))
   (Ssequence (Scall (Some ret') a bl)
      (Sset ret (Ecast (Etempvar ret' retty') retty)))
    (normal_ret_assert Post2).
Proof.
  intros.
  eapply semax_seq'.
  eapply semax_call_id1_wow; try eassumption; auto.
  unfold typeof_temp; rewrite RETinit; reflexivity.
  simpl update_tycon.
  apply extract_exists_pre; intro vret.
  eapply semax_pre_post';
    [ | | apply semax_set_forward].
  + eapply derives_trans; [ | apply now_later ].
    instantiate (1:= (PROPx (P ++ Ppost vret)
      (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
    apply andp_right; [apply andp_right |].
    - unfold tc_expr.
      unfold typecheck_expr; simpl.
      simpl denote_tc_assert.
      rewrite tycontext.temp_types_same_type'. rewrite RETinit.
      simpl @fst.
      replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
        with true
        by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; unfold is_neutral_cast; rewrite ?eqb_type_refl; reflexivity).
      simpl @snd. cbv iota.
      go_lowerx. simpl.
      apply neutral_isCastResultType; auto.
    - unfold tc_temp_id, typecheck_temp_id.
      rewrite <- tycontext.initialized_ne by auto.
      unfold typeof_temp in TYret.
      destruct ((temp_types Delta) ! ret) as [[? ?]  | ]; inversion TYret; clear TYret; try subst t.
      go_lowerx.
      repeat rewrite denote_tc_assert_andp; simpl.
      rewrite denote_tc_assert_bool.
      assert (is_neutral_cast (implicit_deref retty) retty = true).
      {
        destruct retty as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; try reflexivity;
        destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; 
        try solve [inv NEUTRAL].
        unfold implicit_deref, is_neutral_cast. rewrite eqb_type_refl; reflexivity.
      }
      simpl; apply andp_right. apply prop_right; auto.
      apply neutral_isCastResultType; auto.
    - go_lowerx. normalize. apply andp_right; auto. apply prop_right.
      subst Qnew; clear - H3. rename H3 into H.
      induction Q; simpl in *; auto.
      destruct H, a; specialize (IHQ H0); try now (simpl; split; auto).
      hnf in H.
      if_tac; simpl; auto.
+
 intros. subst Post2.
 normalize. simpl exit_tycon.
 apply exp_right with vret; normalize.
 autorewrite with subst.
 go_lowerx.
 normalize. apply andp_right; auto.
 apply prop_right; split; auto.
 hnf. rewrite H0; unfold_lift.
 assert (eqb_ident ret ret' = false)
 by (clear - NEret; pose proof (eqb_ident_spec ret ret');
       destruct (eqb_ident ret ret'); auto;
      contradiction NEret; intuition).
 rewrite H4 in *. apply Pos.eqb_neq in H4.
  unfold_lift in H2.
  rewrite eval_id_other in H2 by auto.
 hnf in H2. rewrite H2.
 assert (tc_val retty' (eval_id ret' rho)).
 eapply tc_eval_id_i; try eassumption.
 rewrite <- initialized_ne by auto.
  rewrite temp_types_same_type'.
 rewrite RETinit. auto.
 assert (H7 := expr2.neutral_cast_lemma);
   unfold eval_cast in H7. rewrite H7 by auto.
 unfold eval_id, env_set, Map.get. auto.
 subst Qnew; clear - H3. rename H3 into H.
 induction Q; simpl in *; auto.
 destruct a; try now (destruct H; simpl in *; split; auto).
 if_tac; simpl in *; auto.
 destruct H; split; auto.
 hnf in H|-*; subst.
 rewrite eval_id_other by auto.
 auto.
Qed.

Lemma semax_call_id1_y_wow:
 forall  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty' cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar G a Delta P Q R R' argsig retty' cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var G')
    Espec ret ret' (retty: type) 
             (Post2: environ -> mpred)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) ! ret' = Some (retty', false))
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true)
   (NEret: ret <> ret')
   (POST1: Post nil witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R')))
   (Ssequence (Scall (Some ret') a bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert Post2).
Proof.
  intros.
  eapply semax_seq'.
  eapply semax_call_id1_wow; try eassumption; auto;
    unfold typeof_temp; rewrite RETinit; reflexivity.
  simpl update_tycon.
  apply extract_exists_pre; intro vret.
  eapply semax_pre_post';
    [ | | apply semax_set_forward].
  + eapply derives_trans; [ | apply now_later ].
    instantiate (1:= (PROPx (P ++ Ppost vret)
      (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
    apply andp_right; [apply andp_right |].
    - unfold tc_expr.
      match goal with |- _ |-- ?A =>
        set (aa:=A); unfold denote_tc_assert in aa; simpl in aa; subst aa
      end.
      rewrite tycontext.temp_types_same_type'. rewrite RETinit.
      simpl @fst.
      replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
        with true
        by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; unfold is_neutral_cast; rewrite ?eqb_type_refl; reflexivity).
      simpl @snd. cbv iota.
      apply @TT_right.
    - unfold tc_temp_id, typecheck_temp_id.
      rewrite <- tycontext.initialized_ne by auto.
      unfold typeof_temp in TYret.
      destruct ((temp_types Delta) ! ret) as [[? ?]  | ]; inversion TYret; clear TYret; try subst t.
      go_lowerx.
      repeat rewrite denote_tc_assert_andp; simpl.
      rewrite denote_tc_assert_bool.
      assert (is_neutral_cast (implicit_deref retty') retty = true).
      * replace (implicit_deref retty') with retty'
          by (destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; reflexivity).
        auto.
      * simpl; apply andp_right. apply prop_right; auto.
        apply neutral_isCastResultType; auto.
    - go_lowerx. normalize. apply andp_right; auto. apply prop_right.
      subst Qnew; clear - H3. rename H3 into H.
      induction Q; simpl in *; auto.
      destruct H, a; specialize (IHQ H0); try now (simpl; split; auto).
      hnf in H.
      if_tac; simpl; auto.
+
 intros. subst Post2.
 normalize. simpl exit_tycon.
 apply exp_right with vret; normalize.
 autorewrite with subst.
 go_lowerx.
 normalize. apply andp_right; auto.
 apply prop_right; split; auto.
 hnf. rewrite H0; unfold_lift.
 assert (eqb_ident ret ret' = false)
 by (clear - NEret; pose proof (eqb_ident_spec ret ret');
       destruct (eqb_ident ret ret'); auto;
      contradiction NEret; intuition).
 rewrite H4 in *.  apply Pos.eqb_neq in H4.
 unfold_lift in H2.
 rewrite eval_id_other in H2 by auto.
 hnf in H2. rewrite H2. auto.
 subst Qnew; clear - H3. rename H3 into H.
 induction Q; simpl in *; auto.
 destruct a; try now (destruct H; simpl in *; split; auto).
 if_tac; simpl in *; auto.
 destruct H; split; auto.
 hnf in H|-*; subst.
 rewrite eval_id_other by auto.
 auto.
Qed.

Lemma semax_call_id01_wow:
 forall  
  (cs: compspecs) Qtemp Qvar G a Delta P Q R R'
   argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) G'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar G a Delta P Q R R' argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var G')
   Espec
             (Post2: environ -> mpred)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (_: check_retty retty)
         (* this hypothesis is not needed for soundness, just for selectivity *)
   (POST1: Post nil witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof.
intros.
destruct SETUP as [[PTREE [SPEC [HR' [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]]]
                            [PRE1 [PTREE' [CHECKTEMP [CHECKVAR [CHECKG FRAME]]]]]].
apply SPEC. clear SPEC.
eapply semax_pre; [apply andp_right; [apply andp_left2, andp_left1, derives_refl|]|].
{ rewrite <- andp_assoc, andp_comm.
  rewrite <- andp_assoc; apply andp_left1.
  rewrite andp_comm.
  eapply derives_trans; [apply andp_derives, HR'; apply derives_refl|].
  apply later_left2.
  apply andp_right, andp_left2, derives_refl.
  apply andp_right, CHECKTEMP.
  apply andp_right, CHECKVAR.
  eapply derives_trans, tc_exprlist_len; apply TC1. }
rewrite later_andp, andp_comm, andp_assoc.
rewrite <- !prop_and.
apply semax_extract_later_prop; intros [[]].
rewrite andp_comm.
eapply semax_pre_post';
   [ |
   | apply semax_call0 with (A:= A) (ts := nil)(x:=witness) (P:=P)(Q:=Q)(NEPre :=NEPre) (NEPost := NEPost)(R := Frame)
   ];
   try eassumption.
*
eapply semax_call_aux55; eauto.
*
 subst.
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 normalize.
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


Lemma match_funcptr'_funcptr:
 forall fs v B, 
  func_ptr' fs v * B |-- func_ptr fs v.
Proof.
intros. unfold func_ptr'. 
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
apply andp_left1; auto.
Qed.

Lemma nomatch_funcptr'_funcptr:
  forall fs v A B,
   B |-- func_ptr fs v ->
  A * B |-- func_ptr fs v.
Proof.
intros.
rewrite <- (corable_sepcon_TT _ (corable_func_ptr fs v)).
rewrite sepcon_comm. apply sepcon_derives; auto.
Qed.

Ltac match_funcptr'_funcptr :=
 first [apply match_funcptr'_funcptr 
        | apply nomatch_funcptr'_funcptr; match_funcptr'_funcptr].

Ltac prove_func_ptr := 
    match goal with |- fold_right_sepcon ?A |-- func_ptr ?F ?V =>
       match A with context [func_ptr' ?G V] =>
         unify F G
       end
     end; 
   unfold fold_right_sepcon; 
   match_funcptr'_funcptr.

Definition eq_no_post (x v: val) : Prop := x=v.
(* The purpose of eq_no_post is to "mark" the proposition
  in forward_call_idxxx lemmas so that the after-the-call
  can treat this one specially *)

Lemma no_post_exists:
 forall v P Q R,
   PROPx P (LOCALx (temp ret_temp v :: Q) (SEPx R)) =
   EX x:val, PROPx (eq_no_post x v :: P) (LOCALx (temp ret_temp x :: Q) (SEPx R)).
Proof.
intros. unfold eq_no_post.
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
