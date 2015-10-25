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

Lemma semax_call': forall Espec {cs: compspecs} Delta A (Pre Post: A -> environ->mpred) (x: A) ret argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc_default ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, _ => True
   end ->
   tc_fn_return Delta ret retsig ->
  @semax cs Espec Delta
          (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl 
           && PROPx P (LOCALx Q
            (SEPx (`(Pre x) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) ::
                      `(func_ptr' (mk_funspec (argsig,retsig) A Pre Post)) (eval_expr a) :: R))))
          (Scall ret a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (substopt ret (`old)) Q) 
                (SEPx (maybe_retval (Post x) retsig ret :: map (substopt ret (`old)) R))))).
Proof.
 intros. rename H1 into Hret.
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
intro rho; normalize.
autorewrite with norm1 norm2; normalize.
rewrite sepcon_comm; auto.
intro rho; normalize.
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
  @semax cs Espec Delta
         (tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl 
           && PROPx P (LOCALx Q
            (SEPx (`(Pre x) ( (make_args' (argsig,retsig) (eval_exprlist (argtypes argsig) bl))) ::
                      `(func_ptr' (mk_funspec (argsig,retsig) A Pre Post)) (eval_expr a) :: R))))
          (Scall (Some id) a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (subst id (`old)) Q) 
                (SEPx (`(Post x) (get_result1 id) :: map (subst id (`old)) R))))).
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
           && PROPx P (LOCALx Q
            (SEPx (`(Pre x) ( (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl))) ::
                      `(func_ptr' (mk_funspec (argsig,retty) A Pre Post)) (eval_expr a) :: R))))
          (Scall None a bl)
          (normal_ret_assert 
            (PROPx P (LOCALx Q (SEPx (ifvoid retty (`(Post x) (make_args nil nil))
                                                        (EX v:val, `(Post x) (make_args (ret_temp::nil) (v::nil)))
                                                        :: R))))).
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
destruct retty; auto; rewrite sepcon_comm; rewrite insert_SEP; apply derives_refl.
apply Coq.Init.Logic.I.
Qed.

Lemma semax_fun_id':
      forall id f TC
              Espec {cs: compspecs} Delta P Q R PostCond c
            (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some f ->
       (glob_types Delta) ! id = Some (type_of_funspec f) ->
       @semax cs Espec Delta 
        (TC && PROPx P (LOCALx (tc_environ Delta :: Q) 
        (SEPx (`(func_ptr' f) (eval_var id (type_of_funspec f)) :: R))))
                              c PostCond ->
       @semax cs Espec Delta (TC && PROPx P (LOCALx Q (SEPx R))) c PostCond.
Proof.
intros. 
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply H1.
rewrite <- !andp_assoc.
rewrite (andp_comm (local _)).
do 2 rewrite andp_assoc.
apply andp_derives; auto.
rewrite <- andp_assoc. rewrite insert_local.
clear H1.
unfold PROPx,LOCALx,SEPx,local, lift1; unfold_lift; simpl;
intro rho; normalize.
unfold func_ptr'.
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
                  && PROPx P (LOCALx Q
                 (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Scall None (Evar id (Tfunction (type_of_params argsig) retty cc_default)) bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q (SEPx (ifvoid retty (`(Post x) (make_args nil nil))
                                                   (EX v:val, `(Post x) (make_args (ret_temp::nil) (v::nil)))
                                                    :: R))))).
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
rewrite <- insert_local; apply andp_left2. 
apply andp_derives; auto.
apply andp_derives; auto.
unfold SEPx.
intro rho.
simpl.
rewrite sepcon_comm.
rewrite sepcon_assoc.
norm_rewrite.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
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
  @semax cs Espec Delta (tc_exprlist Delta (argtypes argsig) bl && 
                PROPx P (LOCALx Q
                 (SEPx (`(Pre x) (make_args' (argsig,Tvoid) (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction (type_of_params argsig) retty cc_default))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
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
rewrite <- insert_local; apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
unfold SEPx.
simpl.
intro rho.
rewrite sepcon_comm.
rewrite sepcon_assoc.
norm_rewrite.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
Qed.

Lemma semax_call_id0_alt:
 forall Espec {cs: compspecs} Delta P Q R id bl argsig paramty retty A witness Frame Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   paramty = type_of_params argsig ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- tc_exprlist Delta (argtypes argsig) bl ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
  PROPx nil (LOCALx nil 
     (SEPx (`(Pre witness) (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) :: Frame))) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) 
    (Scall None (Evar id (Tfunction paramty retty cc_default)) bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q (SEPx (ifvoid retty (`(Post witness) (make_args nil nil))
                                                   (EX v:val, `(Post witness) (make_args (ret_temp::nil) (v::nil)))
                                                   :: Frame))))).
Proof.
intros. subst paramty.
eapply semax_pre_post;
 [ rewrite insert_local
 | intros; apply andp_left2; apply derives_refl
 | apply semax_call_id0; try eassumption].
apply andp_right; [apply H2 | ].
eapply derives_trans; [apply andp_right; [apply derives_refl | apply H3] | ].
apply andp_right.
repeat apply andp_left1; auto.
apply andp_right.
apply andp_left1; rewrite <- insert_local; apply andp_left2; apply andp_left2; apply andp_left1; auto.
repeat apply andp_left2; auto.
Qed.

Lemma semax_call_id1_alt:
 forall Espec {cs: compspecs} Delta P Q R ret id paramty retty bl argsig A Pre Post witness Frame
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
   paramty = type_of_params argsig ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         tc_exprlist Delta (argtypes argsig) bl ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
  PROPx nil (LOCALx nil 
       (SEPx (`(Pre witness) (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) :: Frame))) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret) (Evar id (Tfunction paramty retty cc_default)) bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post witness) (get_result1 ret) :: map (subst ret (`old)) Frame))))).
Proof.
intros. subst paramty.
eapply semax_pre;  [ | apply semax_call_id1; eauto].
apply andp_right; auto.
eapply derives_trans; [apply andp_right; [apply derives_refl | apply H5 ] | ].
apply andp_right.
repeat apply andp_left1; auto.
apply andp_right.
apply andp_left1; rewrite <- insert_local; apply andp_left2; apply andp_left2; apply andp_left1; auto.
repeat apply andp_left2; auto.
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

(*
Definition check_one_var_spec (Q: PTree.t vardesc) (idv: ident * vardesc) : Prop :=
   match Q ! (fst idv), snd idv with
   | Some (vardesc_local_global t v1 v2), vardesc_local_global t' v1' v2' =>
             t=t' /\ v1=v1' /\ v2=v2'
   | Some (vardesc_local_global t v1 v2), vardesc_local t' v1'  =>
             t=t' /\ v1=v1'
   | Some (vardesc_local t v1) , vardesc_local t' v1'  =>
             t=t' /\ v1=v1'
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
*)

Inductive delete_temp_from_locals {cs} (id: ident) : list (environ -> Prop) -> list (environ -> Prop) -> Prop :=
| dtfl_nil: delete_temp_from_locals id nil nil
| dtfl_here: forall v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (temp id v :: Q) Q'
| dtfl_cons: forall j v Q Q',
                j<>id ->
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (temp j v :: Q) (temp j v :: Q')
| dtfl_lvar: forall j t v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (lvar j t v :: Q) (@lvar cs j t v :: Q')
| dtfl_gvar: forall j v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (gvar j v :: Q) (gvar j v :: Q')
| dtfl_sgvar: forall j v Q Q',
                delete_temp_from_locals id Q Q' ->
                delete_temp_from_locals id (sgvar j v :: Q) (sgvar j v :: Q').      

Definition strong_cast (t1 t2: type) (v: val) : val :=
(* if is_neutral_cast t1 t2 then v else*) 
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

 Lemma fold_right_sepcon_liftx: 
    forall (R: list mpred) rho, fold_right sepcon emp (map liftx R) rho =
                    fold_right sepcon emp R.
Proof.
 intros.
 induction R; simpl; f_equal; auto.
Qed.

Lemma isolate_LOCAL_lem1:
  forall Q, PROPx nil (LOCALx Q (SEPx (TT::nil))) = local (fold_right `and `True Q).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, SEPx.
 normalize.
 autorewrite with norm1 norm2; normalize.
Qed.

Lemma fold_right_and_LocalD_i {cs: compspecs}:
  forall T1 T2 Q rho,
  (forall i v, T1 ! i = Some v -> temp i v rho) ->
  (forall i vd, T2 ! i = Some vd -> fold_right `and `True (denote_vardesc nil i vd) rho) ->
  (fold_right `and `True Q rho) ->
  fold_right `and `True (LocalD T1 T2 Q) rho.
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
  fold_right `and `True (LocalD T1 T2 Q) rho ->
  (forall i v, T1 ! i = Some v -> temp i v rho) /\
  (forall i vd, T2 ! i = Some vd -> fold_right `and `True (denote_vardesc nil i vd) rho) /\
  (fold_right `and `True Q rho).
Proof.
unfold LocalD; intros.
 repeat rewrite PTree.fold_spec in H.
 repeat rewrite <- fold_left_rev_right in H.
 split3; intros.
*
 forget (fold_right
            (fun (y : positive * vardesc) (x : list (environ -> Prop)) =>
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
   fold_right `and `True (LocalD Qtemp Qvar nil) rho ->  
  fold_right `and `True (LocalD Qpre_temp Qpre_var nil) (make_args fl vl rho).
Proof.
 intros.
 apply fold_right_and_LocalD_e in H1.
 destruct H1 as [? [? ?]].
 apply fold_right_and_LocalD_i; [ | | auto]; clear H3; intros.
*
 unfold temp; unfold_lift.
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
  unfold sgvar, gvar in *.
  rewrite (ve_of_make_args _ _ _ _ LEN).
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo.
  unfold sgvar, gvar in *.
  rewrite (ve_of_make_args _ _ _ _ LEN).
  destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo.
  unfold sgvar, gvar in *.
  rewrite (ve_of_make_args _ _ _ _ LEN).
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo.
  unfold sgvar, gvar in *.
  destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
  rewrite ge_of_make_args. auto.
 +
  apply H2 in Heqo; simpl in Heqo; unfold_lift in Heqo. 
  destruct Heqo.
  unfold sgvar, gvar in *.
  rewrite ge_of_make_args. auto.
Qed.

Lemma check_specs_lemma' {cs: compspecs}:
  forall Ptemp Pvar Qtemp Qvar rho,
    Forall (check_one_var_spec' Pvar) (PTree.elements Qvar) ->
    Forall (check_one_temp_spec Ptemp) (PTree.elements Qtemp) ->
    fold_right `and `True (LocalD Ptemp Pvar nil) rho ->
    fold_right `and `True (LocalD Qtemp Qvar nil) rho.
Proof.
  intros.
  apply local_ext_rev.
  intros.
  apply local_ext with ((LocalD Ptemp Pvar nil)); auto.
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

(*
Lemma lvar_make_args:
  forall i t v rho fl vl, lvar i t v rho -> lvar i t v (make_args fl vl rho).
Proof.
induction fl; destruct vl; simpl.
unfold lvar.
simpl.
destr
 clear - H0.
 revert rho vl H0; unfold var; unfold_lift; induction fl; destruct vl; simpl; intros; auto.
 admit.  (* problem with globals_only *)
 apply (IHfl _ vl H0).
Qed.
*)

Lemma derives_extract_PROP : 
  forall (P1: Prop) P QR S, 
     (P1 -> PROPx P QR |-- S) ->
     PROPx (P1::P) QR |-- S.
Proof.
intros.
rewrite <- canonicalize.canon17.
normalize.
Qed.

Lemma semax_call_id1_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type) 
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: match retty with Tvoid => False | Tarray _ _ _ => False | _ => True end)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (DELETE: delete_temp_from_locals ret Q Qnew)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (map liftx (Rpost' vret ++ Frame)))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret)
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
apply extract_trivial_liftx_e in EXTRACT.
apply extract_trivial_liftx_e in EXTRACT'.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id1 with (x:=witness) (P:=P)(Q:=Q) (R := map liftx Frame)
   ];
   try eassumption;
   [ | 
   | clear - OKretty; destruct retty; intuition 
   | hnf; clear - TYret; unfold typeof_temp in TYret;
      destruct ((temp_types Delta) ! ret) as [[? ?] | ]; inv TYret; auto 
    ].
*
 rewrite insert_local.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- canonicalize.canon17; apply andp_right; auto | ]
 end.
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl; 
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
 progress (autorewrite with norm1 norm2); normalize.
apply derives_extract_PROP; intro LEN.
 clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 normalize.
replace (@map (environ -> mpred) (LiftEnviron mpred)
               (fun r : environ -> mpred =>
                `r
                  (make_args' (argsig, Tvoid)
                     (eval_exprlist (argtypes argsig) bl)))
               (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)
                  (@liftx (LiftEnviron mpred)) Rpre'))
  with (map liftx Rpre')
  by (rewrite map_map; reflexivity).
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
 apply andp_right. apply andp_left1.
 rewrite fold_right_and_app_low.
 clear - PPRE; apply prop_derives; intuition.
 revert PPRE; induction Ppre; simpl; intuition.
 clear PPRE Ppre.
 rewrite <- insert_local. apply andp_left2. 
 apply andp_right.
2: do 2 apply andp_left2;  unfold SEPx;
  rewrite fold_right_sepcon_app;
  intro rho;  normalize; 
 progress (autorewrite with norm1 norm2); normalize;
  repeat rewrite fold_right_sepcon_liftx; auto.
 clear FRAME Frame Rpre'.
 rewrite fold_right_and_app_lifted, local_lift2_and.
 apply andp_right.  apply andp_left2. apply andp_left1. auto.
 apply (local2ptree_soundness P _ (map liftx R')) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=map liftx R')(Q:=nil) in MSUBST.
 rewrite PTREE.
 clear PTREE Q.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 intro rho.
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
 cut (local (fold_right `and `True (LocalD Qtemp Qvar nil)) rho |-- `(local (fold_right `and `True Qpre))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 clear - CVAR CTEMP H LEN'.
 eapply check_specs_lemma; try eassumption.
*
 clear CHECKVAR CHECKTEMP TC1 PRE1 PPRE.
 intros.
 unfold normal_ret_assert. normalize.
 simpl exit_tycon. rewrite POST1; clear POST1.
 apply derives_trans with
  (EX vret: B,
  PROPx (P ++ Ppost vret)
  (LOCALx (tc_environ (initialized ret Delta) :: map (subst ret `old) Q)
     (SEPx
        (`(PROPx nil
             LOCAL  (temp ret_temp (F vret))  (SEPx (Rpost vret)))
           (get_result1 ret) :: map (subst ret `old) (map liftx Frame))))).
 clear.
 go_lowerx. normalize. apply exp_right with x; normalize.
 apply andp_right; auto.
 apply prop_right; split; auto.
 rewrite fold_right_and_app_low. split; auto.
 apply exp_left; intro vret. apply exp_right with vret.
 normalize.
 progress (autorewrite with norm1 norm2); normalize.
 rewrite <- app_nil_end.
 specialize (EXTRACT'' vret).
 apply extract_trivial_liftx_e in EXTRACT''. rewrite EXTRACT''.
 clear EXTRACT''.
 replace (map (fun r : environ -> mpred => `r (get_result1 ret)) (map liftx (Rpost' vret)))
      with (map liftx (Rpost' vret)) 
  by (rewrite map_map; reflexivity).
 replace (map (subst ret `old) (map liftx Frame))
     with (map liftx Frame)
  by (rewrite map_map; reflexivity).
 clear R' FRAME.
 simpl app.
 rewrite <- insert_local.  apply andp_left2.
 forget (P ++ Ppost vret) as P1.
 rewrite <- map_app.
change  (@map mpred (environ -> mpred))
 with (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)).
 forget (map liftx (Rpost' vret ++ Frame)) as R.
 clear - PTREE DELETE.
 apply (local2ptree_soundness P1 _ R) in PTREE.
 apply andp_derives; auto.
 apply andp_derives; auto.
 intro rho.
 apply prop_derives; intro.
 rewrite fold_right_and_app in H.
 destruct H.
 destruct H0. clear H1.
 unfold_lift in H0. unfold temp, get_result1 in H0.
 normalize in H0. subst.
 split.
 rewrite H0; hnf; reflexivity.
 clear - DELETE H.
 induction DELETE.
 + apply Coq.Init.Logic.I.
 + destruct H. auto.
 + destruct H; split; auto.
     clear - H H0.
     autorewrite with subst in H. auto.
 + destruct H; split; auto.
 + destruct H; split; auto.
 + destruct H; split; auto.
Qed.

Lemma subst_liftx:
  forall id v (R: list mpred) ,
  map (subst id v) (map liftx R) = (map liftx R).
Proof.
 intros.
  rewrite map_map. reflexivity.
Qed.

Lemma semax_call_id1_x_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret ret' id (paramty: typelist) (retty retty': type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type) 
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty') A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty') A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty) 
   (RETinit: (temp_types Delta) ! ret' = Some (retty', false))
   (OKretty: match retty with Tvoid => False |  Tarray _ _ _ => False | _ => True end)
   (OKretty': match retty' with Tvoid => False |  Tarray _ _ _ => False | _ => True end)
   (NEUTRAL: is_neutral_cast retty' retty = true) 
   (NEret: ret <> ret')
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
             |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar)
         (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
       |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (DELETE: delete_temp_from_locals ret Q Qnew)
   (DELETE' : delete_temp_from_locals ret' Q Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (map liftx (Rpost' vret ++ Frame)))))
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
  (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (map liftx (Rpost' vret ++ Frame)))))).
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
 destruct ((temp_types Delta) ! ret) as [[? ?]  | ]; inv TYret.
 go_lowerx.
 repeat rewrite denote_tc_assert_andp.
 rewrite denote_tc_assert_bool.
 assert (is_neutral_cast (implicit_deref retty) retty = true)
  by (destruct retty as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; simpl; auto;
        destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; inv NEUTRAL).
 apply andp_right. apply prop_right; auto.
 apply neutral_isCastResultType; auto.
 go_lowerx. normalize. apply andp_right; auto. apply prop_right.
 clear - H4 DELETE. rename H4 into H3.
   induction DELETE. constructor. destruct H3. auto. destruct H3; constructor; auto.
       destruct H3; constructor; auto.  destruct H3; constructor; auto. destruct H3; constructor; auto. 
+
 intros. subst Post2.
 unfold normal_ret_assert.
 normalize. simpl exit_tycon.
 apply exp_right with vret; normalize.
 autorewrite with subst.
 rewrite subst_liftx.
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
 auto.
 clear - DELETE H4.
 induction DELETE; auto.
 destruct H4; constructor; auto.
 autorewrite with subst in H0. auto.
 destruct H4; constructor; auto.
 destruct H4; constructor; auto.
 destruct H4; constructor; auto.
Qed.

Lemma semax_call_id1_y_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R ret ret' id (paramty: typelist) (retty retty': type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty') A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty') A Pre Post)))
   (TYret: typeof_temp Delta ret = Some retty) 
   (RETinit: (temp_types Delta) ! ret' = Some (retty', false))
   (OKretty: match retty with Tvoid => False |  Tarray _ _ _ => False | _ => True end)
   (OKretty': match retty' with Tvoid => False | Tarray _ _ _ => False | _ => True end)
   (NEUTRAL: is_neutral_cast retty' retty = true) 
   (NEret: ret <> ret')
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
             |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar)
         (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
       |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (DELETE: delete_temp_from_locals ret Q Qnew)
   (DELETE' : delete_temp_from_locals ret' Q Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (map liftx (Rpost' vret ++ Frame)))))
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
  (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (map liftx (Rpost' vret ++ Frame)))))).
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
 destruct ((temp_types Delta) ! ret) as [[? ?]  | ]; inv TYret.
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
 clear - H4 DELETE. rename H4 into H3.
   induction DELETE. constructor. destruct H3. auto. destruct H3; constructor; auto.
       destruct H3; constructor; auto.  destruct H3; constructor; auto.  destruct H3; constructor; auto. 
+
 intros. subst Post2.
 unfold normal_ret_assert.
 normalize. simpl exit_tycon.
 apply exp_right with vret; normalize.
 autorewrite with subst.
 rewrite subst_liftx.
 go_lowerx.
 normalize. apply andp_right; auto.
 apply prop_right; split; auto.
 hnf. rewrite H1; unfold_lift.
 assert (eqb_ident ret ret' = false) 
 by (clear - NEret; pose proof (eqb_ident_spec ret ret');
       destruct (eqb_ident ret ret'); auto;
      contradiction NEret; intuition).
 rewrite H5 in *.
 hnf in H3. rewrite H3. auto.
 clear - DELETE H4.
 induction DELETE; auto.
 destruct H4; constructor; auto.
 autorewrite with subst in H0. auto.
 destruct H4; constructor; auto.
 destruct H4; constructor; auto.
 destruct H4; constructor; auto.
Qed.

Lemma semax_call_id01_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)))
   (_: match retty with Tvoid => False | Tarray _ _ _ => False | _ => True end)
         (* this hypothesis is not needed for soundness, just for selectivity *)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (map liftx (Rpost' vret ++ Frame)))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
apply extract_trivial_liftx_e in EXTRACT.
apply extract_trivial_liftx_e in EXTRACT'.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id0 with (x:=witness) (P:=P)(Q:=Q) (R := map liftx Frame)
   ];
   try eassumption.
*
 rewrite insert_local.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- canonicalize.canon17; apply andp_right; auto | ]
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
replace (@map (environ -> mpred) (LiftEnviron mpred)
               (fun r : environ -> mpred =>
                `r
                  (make_args' (argsig, Tvoid)
                     (eval_exprlist (argtypes argsig) bl)))
               (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)
                  (@liftx (LiftEnviron mpred)) Rpre'))
  with (map liftx Rpre')
  by (rewrite map_map; reflexivity).
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
 apply andp_right. apply andp_left1.
 rewrite fold_right_and_app_low.
 clear - PPRE; apply prop_derives; intuition.
 revert PPRE; induction Ppre; simpl; intuition.
 clear PPRE Ppre.
 rewrite <- insert_local. apply andp_left2. 
 apply andp_right.
2: do 2 apply andp_left2;  unfold SEPx;
  rewrite fold_right_sepcon_app;
  intro rho;  normalize; 
 progress (autorewrite with norm1 norm2); normalize;
  repeat rewrite fold_right_sepcon_liftx; auto.
 clear FRAME Frame Rpre'.
 rewrite fold_right_and_app_lifted, local_lift2_and.
 apply andp_right.  apply andp_left2. apply andp_left1. auto.
 apply (local2ptree_soundness P _ (map liftx R')) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=map liftx R')(Q:=nil) in MSUBST.
 rewrite PTREE.
 clear PTREE Q.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 intro rho.
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
 cut (local (fold_right `and `True (LocalD Qtemp Qvar nil)) rho |-- `(local (fold_right `and `True Qpre))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 clear - CVAR CTEMP H LEN'.
 eapply check_specs_lemma; try eassumption.
eapply derives_trans; [apply FRAME | ].
apply sepcon_derives; auto.
clear.
apply derives_refl'.
unfold_lift.
induction Rpre'; simpl; auto.
f_equal; auto.
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
 specialize (EXTRACT'' vret).
 apply extract_trivial_liftx_e in EXTRACT''. rewrite EXTRACT''.
 clear EXTRACT''.
 clear.
 unfold_lift. simpl.
 induction (Rpost' vret); simpl.
 normalize.
 normalize. rewrite sepcon_assoc.
 apply sepcon_derives; auto.
Qed.

Lemma semax_call_id00_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec {cs: compspecs} Delta P Q R id (paramty: typelist) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpre: list (environ -> mpred))
             (Rpost: B -> list (environ -> mpred))
             (Rpost': B -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None)
   (GLOBS: (glob_specs Delta) ! id = Some (mk_funspec (argsig,Tvoid) A Pre Post))
   (GLOBT: (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,Tvoid) A Pre Post)))
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q Qtemp Qvar nil nil)
   (EXTRACT: extract_trivial_liftx R R')
   (TC1: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
          |-- (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre Qpre_temp Qpre_var nil nil)
   (EXTRACT': extract_trivial_liftx Rpre Rpre')
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame)
   (POST1: Post witness = (EX vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (EXTRACT'': forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (map liftx (Rpost' vret ++ Frame)))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty Tvoid cc_default))
             bl)
    (normal_ret_assert Post2).
Proof.
intros.
apply extract_trivial_liftx_e in EXTRACT.
apply extract_trivial_liftx_e in EXTRACT'.
subst.
eapply semax_pre_post; 
   [ | 
   | apply semax_call_id0 with (x:=witness) (P:=P)(Q:=Q) (R := map liftx Frame)
   ];
   try eassumption.
*
 rewrite insert_local.
 apply andp_right; auto.
 rewrite PRE1.
 match goal with |- PROPx ?A ?B |-- ?C =>
  apply derives_trans with (PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- canonicalize.canon17; apply andp_right; auto | ]
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
replace (@map (environ -> mpred) (LiftEnviron mpred)
               (fun r : environ -> mpred =>
                `r
                  (make_args' (argsig, Tvoid)
                     (eval_exprlist (argtypes argsig) bl)))
               (@map (lift_T (LiftEnviron mpred)) (LiftEnviron mpred)
                  (@liftx (LiftEnviron mpred)) Rpre'))
  with (map liftx Rpre')
  by (rewrite map_map; reflexivity).
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
 apply andp_right. apply andp_left1.
 rewrite fold_right_and_app_low.
 clear - PPRE; apply prop_derives; intuition.
 revert PPRE; induction Ppre; simpl; intuition.
 clear PPRE Ppre.
 rewrite <- insert_local. apply andp_left2. 
 apply andp_right.
2: do 2 apply andp_left2;  unfold SEPx;
  rewrite fold_right_sepcon_app;
  intro rho;  normalize; 
 progress (autorewrite with norm1 norm2); normalize;
  repeat rewrite fold_right_sepcon_liftx; auto.
 clear FRAME Frame Rpre'.
 rewrite fold_right_and_app_lifted, local_lift2_and.
 apply andp_right.  apply andp_left2. apply andp_left1. auto.
 apply (local2ptree_soundness P _ (map liftx R')) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=map liftx R')(Q:=nil) in MSUBST.
 rewrite PTREE.
 clear PTREE Q.
 eapply derives_trans. apply andp_right. apply MSUBST. apply derives_refl.
 clear MSUBST.
 apply (local2ptree_soundness nil _ (TT::nil)) in PTREE'.
 simpl app in PTREE'.
 rewrite !isolate_LOCAL_lem1 in PTREE'.
 intro rho.
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
 cut (local (fold_right `and `True (LocalD Qtemp Qvar nil)) rho |-- `(local (fold_right `and `True Qpre))
               (fun rho => (make_args (var_names argsig) (eval_exprlist tys bl rho) rho)) rho).
 intro. eapply derives_trans; [apply H  |]. 
 unfold make_args'. simpl @fst. change (map fst argsig) with (var_names argsig).
 clear.  unfold_lift. unfold local, lift1. apply prop_derives.
 induction Qpre; simpl; auto.  intros [? ?]. split; auto.
 rewrite PTREE'. clear PTREE' Qpre.
 apply prop_derives; intro. forget (var_names argsig) as fl.
 forget (eval_exprlist tys bl rho) as vl.
 clear - CVAR CTEMP H LEN'.
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
 specialize (EXTRACT'' x).
 apply extract_trivial_liftx_e in EXTRACT''. rewrite EXTRACT''.
 clear EXTRACT''.
 clear.
 unfold_lift. simpl.
 induction Rpost'; simpl.
 normalize.
 normalize. rewrite sepcon_assoc.
 apply sepcon_derives; auto.
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
