Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.subsume_funspec.
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

Lemma semax_call': forall Espec {cs: compspecs} Delta fs A Pre Post NEPre NEPost ts x ret argsig retsig cc a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, _ => True
   end ->
   forall (Hret: tc_fn_return Delta ret retsig)
   (Hsub: subsume_funspec fs (mk_funspec (argsig,retsig) cc A Pre Post NEPre NEPost))
(*   (HAB: forall ts : list Type,
       Inhabitant (functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts
                           (withtype_of_funspec fs)) mpred)) *),
  @semax cs Espec Delta
          (|>(tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl)
           &&
   (|>`(Pre ts x: environ -> mpred) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) *
                      `(func_ptr' fs) (eval_expr a)
     * |>PROPx P (LOCALx Q (SEPx R))))
          (Scall ret a bl)
          (normal_ret_assert
            (maybe_retval (Post ts x) retsig ret *
               PROPx P (LOCALx (removeopt_localdef ret Q) (SEPx R)))).
Proof.
  intros. 
  rewrite argtypes_eq.
  eapply semax_pre_post'; [ | |
    apply (semax_call_subsume fs A Pre Post NEPre NEPost argsig retsig cc
    Hsub Delta ts x (PROPx P (LOCALx Q (SEPx R))) ret a bl H); auto].
  3:{
    clear - H0.
    destruct retsig; destruct ret; simpl in *; try contradiction;
    intros; congruence.
  }
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

Lemma semax_call1: forall Espec {cs: compspecs} Delta fs A Pre Post NEPre NEPost ts x id argsig retsig cc a bl P Q R
   (Hsub: subsume_funspec fs (mk_funspec (argsig,retsig) cc A Pre Post NEPre NEPost)),
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc ->
   match retsig with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some id) retsig ->
  @semax cs Espec Delta
         (|>(tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl)
           && (|>`(Pre ts x: environ -> mpred) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) *
                 `(func_ptr' fs) (eval_expr a) *
                  |>PROPx P (LOCALx Q (SEPx R))))
          (Scall (Some id) a bl)
          (normal_ret_assert
            (`(Post ts x: environ -> mpred) (get_result1 id)
               * PROPx P (LOCALx (remove_localdef_temp id Q) (SEPx R)))).
Proof.
intros.
apply (@semax_call' Espec cs Delta fs A Pre Post NEPre NEPost ts x (Some id) argsig retsig cc a bl P Q R); auto.
Qed.

Definition ifvoid {T} t (A B: T) :=
 match t with Tvoid => A | _ => B end.

Lemma semax_call0: forall Espec {cs: compspecs} Delta fs A Pre Post NEPre NEPost ts x
      argsig retty cc a bl P Q R
   (Hsub: subsume_funspec fs (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost)),
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc ->
  @semax cs Espec Delta
         (|>(tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl)
           && (|>`(Pre ts x: environ -> mpred) ( (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)))
                 * `(func_ptr' fs) (eval_expr a)
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
   apply (semax_call_subsume fs A Pre Post NEPre NEPost argsig retty cc Hsub
               Delta ts x (PROPx P (LOCALx Q (SEPx R))) None a bl H)].
3:{
 split; intros; congruence.
}
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

Lemma type_of_subsume_funspec: (* move to subsume_funspec.v *)
  forall fs1 fs2, subsume_funspec fs1 fs2 ->
  type_of_funspec fs1 = type_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [? [? _]]. subst; simpl; auto.
Qed.

(* TODO: Change argument order. ==> A Pre Post NEPre NEPost ts x *)
Lemma semax_call_id0:
 forall Espec {cs: compspecs} Delta P Q R id bl fs argsig retty cc A ts x Pre Post NEPre NEPost
   (Hsub: subsume_funspec fs (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost))
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some fs ->
       (glob_types Delta) ! id = Some (type_of_funspec fs) ->
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
apply (semax_fun_id' id fs (tc_exprlist Delta (argtypes argsig) bl)); auto.
subst.

eapply semax_pre_simple; [ | apply (@semax_call0 Espec cs Delta fs A Pre Post NEPre NEPost ts x argsig _ cc _ bl P Q R Hsub); auto].
rewrite later_andp.
apply andp_right; [apply andp_right | ].
*
eapply derives_trans, now_later.
apply andp_left1.
intro rho; unfold tc_expr; simpl.
subst.
norm_rewrite. apply prop_left; intro.
unfold get_var_type. rewrite GLBL. rewrite H0.
rewrite denote_tc_assert_bool; simpl. apply prop_right.
simpl.
rewrite (type_of_subsume_funspec _ _ Hsub).
simpl; auto.
rewrite eqb_typelist_refl.
simpl. auto.
unfold_lift; auto.
rewrite eqb_type_refl. simpl.
apply eqb_calling_convention_refl.
*
apply andp_left2, andp_left1; auto.
*
apply andp_left2, andp_left2, andp_left2.
intro; simpl.
rewrite later_sepcon, <- sepcon_assoc.
apply sepcon_derives; auto.
rewrite (type_of_subsume_funspec _ _ Hsub).
rewrite sepcon_comm; apply derives_refl.
Qed.

Lemma semax_call_id1:
 forall Espec {cs: compspecs} Delta P Q R ret id fs retty cc bl argsig A ts x Pre Post NEPre NEPost
   (Hsub: subsume_funspec fs (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost))
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some fs ->
       (glob_types Delta) ! id = Some (type_of_funspec fs) ->
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
apply (semax_fun_id' id fs); auto.
subst.
eapply semax_pre_simple; [ | apply (semax_call1 Espec Delta fs A Pre Post NEPre NEPost ts x ret argsig retty cc _ bl P Q R Hsub H1 H0); auto].
apply andp_right.
rewrite later_andp; apply andp_right.
eapply derives_trans, now_later.
apply andp_left1.
intro rho; unfold tc_expr, local,lift1; simpl.
subst.
norm_rewrite.
unfold get_var_type. rewrite GLBL. rewrite Ht.
rewrite (type_of_subsume_funspec _ _ Hsub).
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
rewrite (type_of_subsume_funspec _ _ Hsub).
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

Definition check_gvars_spec (GV: option globals) (GV': option globals) : Prop :=
  match GV' with Some _ => GV = GV' | _ => True end.

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
    Forall (fun v => v <> Vundef) vl ->
    (pTree_from_elements (combine fl vl)) ! i = Some v ->
    v = eval_id i (make_args fl vl rho) /\ v <> Vundef.
Proof.
 intros.
 revert vl H H0; induction fl; intros.
 + simpl in H0.
   unfold pTree_from_elements in H0. simpl in H0.
   rewrite PTree.gempty in H0; inv H0.
 + destruct vl.
   - simpl in *.
     unfold pTree_from_elements in H0. simpl in H0.
     rewrite PTree.gempty in H0; inv H0.
   - simpl in H0.
     unfold pTree_from_elements in H0.
     simpl in H0.
     destruct (ident_eq i a).
     * subst a. rewrite PTree.gss in H0. inv H0.
       rewrite unfold_make_args_cons.
       unfold eval_id.  simpl. rewrite Map.gss.
       split; [reflexivity | inv H; auto].
     * rewrite PTree.gso in H0 by auto.
       apply IHfl in H0.
       rewrite unfold_make_args_cons.
       unfold eval_id.  simpl. rewrite Map.gso by auto. apply H0.
       inv H; auto.
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
  forall Qtemp Qpre_temp Qvar GV GV' rho fl vl
         (LEN: length fl = length vl)
         (UNDEF: Forall (fun v => v <> Vundef) vl),
    check_gvars_spec GV GV' ->
    Forall (check_one_temp_spec (pTree_from_elements (combine fl vl)))
           (PTree.elements Qpre_temp) ->
    fold_right `(and) `(True) (map locald_denote (LocalD Qtemp Qvar GV)) rho ->
    fold_right `(and) `(True) (map locald_denote (LocalD Qpre_temp (PTree.empty _) GV')) (make_args fl vl rho).
Proof.
  intros.
  apply local_ext_rev.
  specialize (fun (Q0: environ -> Prop) H => local_ext Q0 _ _ H H1).
  clear H1; intros.
  specialize (fun (Q0: localdef) H => H1 (locald_denote Q0) (in_map _ _ _ H)).
  specialize (fun (Q0: localdef) H => H1 Q0 (LocalD_sound _ _ _ _ H)).
  assert (ASSU1: forall i v, Qtemp ! i = Some v -> locald_denote (temp i v) rho) by (intros; apply H1; firstorder).
  assert (ASSU2: forall i t v, Qvar ! i = Some (t, v) -> locald_denote (lvar i t v) rho) by (intros; apply H1; eauto 50).
  assert (ASSU3: forall gv, GV = Some gv -> locald_denote (gvars gv) rho) by (intros; apply H1; eauto 50).
  clear H1.
  apply list_in_map_inv in H2.
  destruct H2 as [Q0' [? ?]]; subst; rename Q0' into Q0.
  apply LocalD_complete in H2.
  destruct H2 as [ [i [v [?H ?H]]]
                 |[ [i [t [v [?H ?H]]]]
                 |  [gv [?H ?H]]]];
    subst; unfold locald_denote; unfold_lift.
  + hnf.
    clear - H0 H1 UNDEF.
    pose proof (Forall_ptree_elements_e _ _ _ _ _ H0 H1).
    hnf in H. simpl in H.
    clear - H UNDEF.
    eapply pTree_from_elements_e1; auto.
  + rewrite PTree.gempty in H1; inv H1.
  + destruct GV; [| inv H].
    simpl in H; inv H.
    specialize (ASSU3 _ eq_refl).
    hnf in ASSU3 |- *. subst.
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
  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
 :=
  local2ptree Q = (Qtemp, Qvar, nil, GV) /\
  subsume_funspec fs (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) /\
  can_assume_funcptr  cs Delta P Q R' a fs /\
  PROPx P (LOCALx Q (SEPx R')) |-- |> PROPx P (LOCALx Q (SEPx R)) /\
  Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
         |-- (tc_expr Delta a)  /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl) /\
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl /\
  pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals.

Lemma call_setup1_i:
 forall (cs: compspecs) Delta P Q R R' (a: expr) (bl: list expr)
   Qtemp Qvar GV (v: val)
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (vl : list val)
  (Qactuals : PTree.t _),
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  msubst_eval_expr Delta Qtemp Qvar GV a = Some v ->
  fold_right_sepcon R' |--  func_ptr fs v ->
  subsume_funspec fs (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) ->
  fold_right_sepcon R' |-- |> fold_right_sepcon R ->
  Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
         |-- (tc_expr Delta a)  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl) ->
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl ->
  pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
 call_setup1 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals.
Proof. intros.
assert (H18 := @msubst_eval_expr_eq cs Delta P Qtemp Qvar GV R' a v H0).
assert (H19 := local2ptree_soundness P Q R' Qtemp Qvar nil GV H).
repeat split; auto.
hnf; intros.
eapply semax_pre; [ | eassumption].
clear c Post0 H9.
Exists v.
apply andp_right; [ | apply andp_left2; auto].
apply andp_right.
repeat apply andp_left2.
intro rho; unfold SEPx, lift0.
apply H1.
rewrite H19.
simpl app.
apply H18.
unfold PROPx, LOCALx.
rewrite <- !andp_assoc, later_andp; apply andp_derives; [apply now_later|].
unfold SEPx; simpl; auto.
Qed.

Lemma call_setup1_i2:
 forall (cs: compspecs) Delta P Q R R' (id: ident) (ty: type) (bl: list expr)
   Qtemp Qvar GV
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (vl : list val)
  (Qactuals : PTree.t _),
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  can_assume_funcptr  cs Delta P Q R' (Evar id ty) fs ->
  subsume_funspec fs (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost) ->
  PROPx P (LOCALx Q (SEPx R')) |-- |> PROPx P (LOCALx Q (SEPx R)) ->
  Cop.classify_fun ty = Cop.fun_case_f (type_of_params argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
         |-- (tc_expr Delta (Evar id ty))  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl) ->
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl ->
  pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
 call_setup1 cs Qtemp Qvar GV (Evar id ty) Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals.
Proof. intros.
 repeat split; auto.
Qed.

Lemma can_assume_funcptr1:
  forall  cs Delta P Q R a fs v Qtemp Qvar GV,
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  msubst_eval_expr Delta Qtemp Qvar GV a = Some v ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- lift0(func_ptr fs v) ->
   can_assume_funcptr cs Delta P Q R a fs.
Proof.
intros.
unfold can_assume_funcptr; intros.
eapply semax_pre; [ | eassumption].
apply andp_right; [ | apply andp_left2; auto].
Exists v.
apply andp_right; auto.
assert (H8 := @msubst_eval_expr_eq cs Delta P Qtemp Qvar GV R a v H0).
eapply local2ptree_soundness' in H.
simpl in H; rewrite <- H in H8.
eapply derives_trans, H8.
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
  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
  (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  (Qpre_temp : PTree.t _) GV':=
 call_setup1 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals /\
  Pre nil witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) /\
  local2ptree Qpre = (Qpre_temp, PTree.empty _, nil, GV') /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) /\
  check_gvars_spec GV GV' /\
  fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame.

Lemma call_setup2_i:
 forall  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
  (SETUP1: call_setup1 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals)
  (witness': functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  (Qpre_temp : PTree.t _) GV',
  Pre nil witness' = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ->
  local2ptree Qpre = (Qpre_temp, PTree.empty _, nil, GV') ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) ->
  check_gvars_spec GV GV' ->
  fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame ->
  call_setup2 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness' Frame Ppre Qpre Rpre Qpre_temp GV'.
Proof.
 intros. split. auto. repeat split; auto.
Qed.

Lemma actual_value_not_Vundef:
 forall (cs: compspecs) (Qtemp: PTree.t val) (Qvar: PTree.t (type * val))
     Delta P Q R tl bl vl GV
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, GV))
 (TC : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
             |-- tc_exprlist Delta tl bl)
 (MSUBST : force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                           (explicit_cast_exprlist tl bl)) = Some vl),
 local (tc_environ Delta) && |> PROPx P (LOCALx Q (SEPx R)) = local (tc_environ Delta) && |> (PROPx P (LOCALx Q (SEPx R)) && !! Forall (fun v : val => v <> Vundef) vl).
Proof.
  intros.
  eapply (msubst_eval_exprlist_eq Delta P Qtemp Qvar GV R) in MSUBST.
  apply (local2ptree_soundness P Q R) in PTREE; simpl app in PTREE.
  rewrite <- PTREE in MSUBST; clear PTREE; rename MSUBST into EVAL.
  apply pred_ext; [| apply andp_derives; auto; apply later_derives; normalize].
  rewrite later_andp, <- andp_assoc.
  apply andp_right; auto.
  apply later_left2.
  unfold tc_exprlist in TC.
  rewrite (add_andp _ _ TC), (add_andp _ _ EVAL); clear TC EVAL.
  rewrite (andp_comm _ (PROPx _ _)), !andp_assoc.
  apply andp_left2.
  go_lowerx.
  revert bl vl H0; induction tl; intros.
  + destruct bl; simpl; [| apply FF_left].
    apply prop_right.
    subst; simpl; constructor.
  + Opaque typecheck_expr. destruct bl; simpl; [apply FF_left |].
    rewrite denote_tc_assert_andp.
    subst vl. simpl. Transparent typecheck_expr.
    eapply derives_trans; [apply andp_derives; [apply typecheck_expr_sound; auto | apply IHtl; reflexivity] |].
    normalize.
    simpl in H0.
    unfold_lift in H0; unfold_lift.
    constructor; auto.
    intro.
    unfold force_val1 in H0; unfold Basics.compose in H2.
    rewrite H2 in H0; clear H2.
    apply tc_val_Vundef in H0; auto.
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
 forall (cs: compspecs) (Qtemp: PTree.t val) (Qvar: PTree.t (type * val)) GV (a: expr)
     Delta P Q R fs argsig retty (*cc*) 
    (A : rmaps.TypeTree)
         (Pre
          Post : forall ts : list Type,
              functors.MixVariantFunctor._functor
                (rmaps.dependent_type_functor_rec
                   ts (AssertTT A)) mpred) (* NEPre NEPost *) 
    witness Frame bl Ppre Qpre Rpre Qactuals Qpre_temp GV' vl
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, GV))
 (TC0 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta a)
 (TC1 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
             |-- tc_exprlist Delta (argtypes argsig) bl)
 (MSUBST : force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
              (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
 (PTREE'' : pTree_from_elements (combine (var_names argsig) vl) = Qactuals)
 (PRE1 : Pre nil witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
 (PTREE' : local2ptree Qpre = (Qpre_temp, PTree.empty _, nil, GV')) 
 (CHECKTEMP : Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
 (CHECKG: check_gvars_spec GV GV')
 (FRAME : fold_right_sepcon R
           |-- fold_right_sepcon Rpre * fold_right_sepcon Frame)
 (PPRE : fold_right_and True Ppre)
 (LEN : length (argtypes argsig) = length bl),
ENTAIL Delta,
(EX v : val,
 lift0 (func_ptr fs (* (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) *) v) &&
 local (` (eq v) (eval_expr a))) && |>PROPx P (LOCALx Q (SEPx R))
|-- |> (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl) &&
    (|> @liftx (Tarrow environ (LiftEnviron mpred)) (Pre nil witness)
       (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) *
     ` (func_ptr' fs (* (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) *) )
       (eval_expr a) * |>PROPx P (LOCALx Q (SEPx Frame))).
Proof.
intros.
pose proof actual_value_not_Vundef _ _ _ _ _ _ _ _ _ _ _ PTREE TC1 MSUBST as VUNDEF.
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
 (`(func_ptr fs) (eval_expr a) &&
      |>PROPx P (LOCALx Q (SEPx R))).
apply andp_left2.
apply andp_right; [  | apply andp_left2; auto].
apply andp_left1.
intro rho; unfold_lift; unfold local, lift0, lift1; simpl. normalize.
apply andp_right.
apply andp_left2; apply andp_left1; auto.
eapply derives_trans;[ apply andp_derives; [apply derives_refl | apply andp_left2; apply derives_refl] |].
subst Qactuals.
clear - PTREE LEN PTREE' MSUBST FRAME PPRE CHECKTEMP CHECKG VUNDEF.
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
 rewrite VUNDEF.
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P0:=P)(R0:=R)(GV0:=GV) in MSUBST.
 rewrite PTREE.
 apply later_left2.
 normalize. clear VUNDEF; rename H into VUNDEF.
 apply derives_trans with (local ((` (eq vl)) (eval_exprlist (argtypes argsig) bl)) && PROPx P (LOCALx (LocalD Qtemp Qvar GV) (SEPx R))); [rewrite (add_andp _ _ MSUBST); solve_andp |].
 clear MSUBST.
 intro rho.
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
 cut (local (fold_right `(and) `(True) (map locald_denote (LocalD Qtemp Qvar GV))) rho |--
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
  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) GV'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp GV')
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
destruct SETUP as [[PTREE [Hsub [SPEC [HR' [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]]]]
                            [PRE1 [PTREE' [CHECKTEMP [CHECKG FRAME]]]]].
apply SPEC. clear SPEC.
eapply semax_pre; [apply andp_right; [apply andp_left2, andp_left1, derives_refl|]|].
{ rewrite <- andp_assoc, andp_comm.
  rewrite <- andp_assoc; apply andp_left1.
  rewrite andp_comm.
  eapply derives_trans; [apply andp_derives, HR'; apply derives_refl|].
  apply later_left2.
  apply andp_right, andp_left2, derives_refl.
  apply andp_right, CHECKTEMP.
  eapply derives_trans, tc_exprlist_len; apply TC1. }
rewrite later_andp, andp_comm, andp_assoc.
rewrite <- !prop_and.
apply semax_extract_later_prop; intros [].
rewrite andp_comm.
eapply semax_pre_post' ; [ | |
   apply (@semax_call0 Espec cs Delta fs A Pre Post NEPre NEPost 
              nil witness argsig retty cc a bl P Q Frame Hsub)].
*
eapply semax_call_aux55; eauto.
*
 subst.
 clear CHECKTEMP TC1 PRE1 PPRE.
 intros. normalize.
 rewrite POST1; clear POST1.
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
  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) GV'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp GV')
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
destruct SETUP as [[PTREE [Hsub [SPEC [HR' [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]]]]
                            [PRE1 [PTREE' [CHECKTEMP [CHECKG FRAME]]]]].
apply SPEC. clear SPEC.
eapply semax_pre; [apply andp_right; [apply andp_left2, andp_left1, derives_refl|]|].
{ rewrite <- andp_assoc, andp_comm.
  rewrite <- andp_assoc; apply andp_left1.
  rewrite andp_comm.
  eapply derives_trans; [apply andp_derives, HR'; apply derives_refl|].
  apply later_left2.
  apply andp_right, andp_left2, derives_refl.
  apply andp_right, CHECKTEMP.
  eapply derives_trans, tc_exprlist_len; apply TC1. }
rewrite later_andp, andp_comm, andp_assoc.
rewrite <- !prop_and.
apply semax_extract_later_prop; intros [].
rewrite andp_comm.
eapply semax_pre_post'; [ | |
   apply (@semax_call1 Espec cs Delta fs A Pre Post NEPre NEPost 
              nil witness ret argsig retty cc a bl P Q Frame Hsub)];
 [ | 
 | assumption
 | clear - OKretty; destruct retty; inv OKretty; apply I
 | hnf; clear - TYret; unfold typeof_temp in TYret;
      destruct ((temp_types Delta) ! ret); inv TYret; auto
 ].
*
eapply semax_call_aux55; eauto.
*
 subst.
 clear CHECKTEMP TC1 PRE1 PPRE.
 intros.
 normalize.
 rewrite POST1; clear POST1.
 apply derives_trans with
   (EX  vret : B,
    `(PROPx (Ppost vret)
     (LOCAL  (temp ret_temp (F vret))
      (SEPx (Rpost vret))))%assert (get_result1 ret)
     * (local (tc_environ Delta) && PROPx P (LOCALx (remove_localdef_temp ret Q) (SEPx Frame)))).
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
 rewrite !fold_right_and_app_low in H4. destruct H4; split; auto.
Qed.

Lemma semax_call_id1_x_wow:
 forall  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty' cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) GV'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty' cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp GV')
   retty  Espec ret ret'
             (Post2: environ -> mpred)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) ! ret' = Some retty')
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
  apply extract_exists_pre; intro vret.
  eapply semax_pre_post';
    [ | | apply semax_set_forward].
  + eapply derives_trans; [ | apply now_later ].
    instantiate (1:= (PROPx (P ++ Ppost vret)
      (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
    apply andp_right; [apply andp_right |].
    - unfold tc_expr.
      simpl typecheck_expr.
      rewrite RETinit.
      simpl @fst.
      replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
        with true
        by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; unfold is_neutral_cast; rewrite ?eqb_type_refl; reflexivity).
      rewrite denote_tc_assert_andp.
      apply andp_right; [| intros rho; apply neutral_isCastResultType; auto].
      apply PQR_denote_tc_initialized; auto.
    - unfold tc_temp_id, typecheck_temp_id.
      unfold typeof_temp in TYret.
      destruct ((temp_types Delta) ! ret); inversion TYret; clear TYret; try subst t.
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
    - rewrite <- !insert_local. apply andp_left2.
      apply andp_derives; auto.
      subst Qnew; apply derives_remove_localdef_PQR.
  + intros. subst Post2.
    normalize.
    apply exp_right with vret; normalize.
    rewrite <- !insert_local.
    autorewrite with subst.
    rewrite <- !andp_assoc.
    apply andp_derives; [| subst Qnew; apply subst_remove_localdef_PQR].
    go_lowerx.
    unfold_lift.
    normalize.
    assert (eqb_ident ret ret' = false)
    by (clear - NEret; pose proof (eqb_ident_spec ret ret');
        destruct (eqb_ident ret ret'); auto;
        contradiction NEret; intuition).
    rewrite H3 in *. apply Pos.eqb_neq in H3.
    unfold_lift in H0.
    assert (tc_val retty' (eval_id ret' rho))
      by (eapply tc_eval'_id_i; try eassumption; congruence).
    assert (H7 := expr2.neutral_cast_lemma); unfold eval_cast in H7.
    rewrite H7 in H0 by auto; clear H7.
    split; congruence.
Qed.

Lemma semax_call_id1_y_wow:
 forall  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty' cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) GV'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty' cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp GV')
    Espec ret ret' (retty: type) 
             (Post2: environ -> mpred)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) ! ret' = Some retty')
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
      rewrite RETinit.
      simpl @fst.
      replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
        with true
        by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; unfold is_neutral_cast; rewrite ?eqb_type_refl; reflexivity).
      simpl @snd. cbv iota.
      apply PQR_denote_tc_initialized; auto.
    - unfold tc_temp_id, typecheck_temp_id.
      unfold typeof_temp in TYret.
      destruct ((temp_types Delta) ! ret); inversion TYret; clear TYret; try subst t.
      go_lowerx.
      repeat rewrite denote_tc_assert_andp; simpl.
      rewrite denote_tc_assert_bool.
      assert (is_neutral_cast (implicit_deref retty') retty = true).
      * replace (implicit_deref retty') with retty'
          by (destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; reflexivity).
        auto.
      * simpl; apply andp_right. apply prop_right; auto.
        apply neutral_isCastResultType; auto.
    - rewrite <- !insert_local. apply andp_left2.
      apply andp_derives; auto.
      subst Qnew; apply derives_remove_localdef_PQR.
  + intros. subst Post2.
    unfold normal_ret_assert.
    normalize.
    apply exp_right with vret; normalize.
    rewrite <- !insert_local.
    autorewrite with subst.
    rewrite <- !andp_assoc.
    apply andp_derives; [| subst Qnew; apply subst_remove_localdef_PQR].
    go_lowerx.
    unfold_lift.
    normalize.
    assert (eqb_ident ret ret' = false)
    by (clear - NEret; pose proof (eqb_ident_spec ret ret');
        destruct (eqb_ident ret ret'); auto;
        contradiction NEret; intuition).
    rewrite H3 in *. apply Pos.eqb_neq in H3.
    split; congruence.
Qed.

Lemma semax_call_id01_wow:
 forall  
  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) GV'
   (vl : list val)
   (SETUP: call_setup2 cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp GV')
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
destruct SETUP as [[PTREE [Hsub [SPEC [HR' [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]]]]
                            [PRE1 [PTREE' [CHECKTEMP [CHECKG FRAME]]]]].
apply SPEC. clear SPEC.
eapply semax_pre; [apply andp_right; [apply andp_left2, andp_left1, derives_refl|]|].
{ rewrite <- andp_assoc, andp_comm.
  rewrite <- andp_assoc; apply andp_left1.
  rewrite andp_comm.
  eapply derives_trans; [apply andp_derives, HR'; apply derives_refl|].
  apply later_left2.
  apply andp_right, andp_left2, derives_refl.
  apply andp_right, CHECKTEMP.
  eapply derives_trans, tc_exprlist_len; apply TC1. }
rewrite later_andp, andp_comm, andp_assoc.
rewrite <- !prop_and.
apply semax_extract_later_prop; intros [].
rewrite andp_comm.
eapply semax_pre_post';
   [ |
   | apply semax_call0 with (fs:=fs)(cc:=cc)(A:= A) (ts := nil)(x:=witness) (P:=P)(Q:=Q)(NEPre :=NEPre) (NEPost := NEPost)(R := Frame)
   ];
   try eassumption.
* eapply semax_call_aux55; eauto.
*
 subst.
 clear CHECKTEMP TC1 PRE1 PPRE.
 intros.
 normalize.
 rewrite POST1; clear POST1.
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
