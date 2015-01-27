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

Lemma semax_call': forall Espec Delta A (Pre Post: A -> environ->mpred) (x: A) ret argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc_default ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, _ => True
   end ->
   tc_fn_return Delta ret retsig ->
  @semax Espec Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (argtypes argsig) bl :: Q)
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
 Focus 3.
 clear - H0.
 destruct retsig; destruct ret; simpl in *; try contradiction; 
   intros; congruence.
clear Hret.
unfold_lift; unfold local, lift1. intro rho; simpl. normalize.
unfold func_ptr'.
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite sepcon_comm. rewrite emp_sepcon.
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
apply derives_refl.
intros.
autorewrite with ret_assert.
repeat rewrite normal_ret_assert_eq.
normalize.
apply exp_right with old; destruct ret; normalize.
autorewrite with subst.
intro rho; normalize.
rewrite sepcon_comm; auto.
intro rho; normalize.
rewrite sepcon_comm; auto.
unfold substopt.
repeat rewrite list_map_identity.
normalize.
Qed.

Lemma semax_call1: forall Espec Delta A (Pre Post: A -> environ->mpred) (x: A) id argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc_default ->
   match retsig with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some id) retsig ->
  @semax Espec Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (argtypes argsig) bl :: Q)
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

Lemma semax_call0: forall Espec Delta A (Pre Post: A -> environ->mpred) (x: A) 
      argsig retty a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retty cc_default ->
  @semax Espec Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (argtypes argsig) bl :: Q)
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
unfold func_ptr'.
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon, sepcon_comm. 
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
apply derives_refl.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
normalize.
unfold SeparationLogic.maybe_retval.
autorewrite with subst norm ret_assert.
destruct retty; auto; rewrite sepcon_comm; rewrite insert_SEP; apply derives_refl.
apply I.
Qed.

Lemma semax_fun_id':
      forall id f
              Espec Delta P Q R PostCond c
            (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some f ->
       (glob_types Delta) ! id = Some (type_of_funspec f) ->
       @semax Espec Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(func_ptr' f) (eval_var id (type_of_funspec f)) :: R))))
                              c PostCond ->
       @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c PostCond.
Proof.
intros. 
apply (semax_fun_id id f Delta); auto.
eapply semax_pre0; [ | apply H1].
unfold PROPx,LOCALx,SEPx,local, lift1; unfold_lift; simpl;
intro rho; normalize.
rewrite andp_comm.
unfold func_ptr'.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon; auto.
Qed.

Lemma eqb_typelist_refl: forall tl, eqb_typelist tl tl = true.
Proof.
induction tl; simpl; auto.
apply andb_true_iff.
split; auto.
apply eqb_type_refl.
Qed.

Lemma semax_call_id0:
 forall Espec Delta P Q R id bl argsig retty A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q)
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
apply semax_fun_id' with id (mk_funspec (argsig,retty) A Pre Post); auto.
subst. 

eapply semax_pre_simple; [ | apply (@semax_call0 Espec Delta A Pre Post x argsig _ _ bl P Q R H1)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
norm_rewrite. repeat rewrite prop_and.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H0.
simpl.
rewrite eqb_typelist_refl.
simpl. auto.
unfold_lift; auto.
rewrite eqb_type_refl. simpl. apply I.
auto.
unfold SEPx.
intro rho.
simpl.
rewrite sepcon_comm.
rewrite sepcon_assoc.
norm_rewrite.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
Qed.

Lemma semax_call_id1:
 forall Espec Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q) 
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
apply semax_fun_id' with id (mk_funspec (argsig,retty)  A Pre Post); auto.
subst. 
eapply semax_pre_simple; [ | apply (semax_call1 Espec Delta A Pre Post x ret argsig retty _ bl P Q R H1 H0); auto].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
norm_rewrite. repeat rewrite prop_and.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite Ht.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. split; hnf; auto.
auto.
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
 forall Espec Delta P Q R id bl argsig paramty retty A witness Frame Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   paramty = type_of_params argsig ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
  PROPx nil (LOCALx (tc_exprlist Delta (argtypes argsig) bl ::nil) 
     (SEPx (`(Pre witness) (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) :: Frame))) ->
  @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) 
    (Scall None (Evar id (Tfunction paramty retty cc_default)) bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q (SEPx (ifvoid retty (`(Post witness) (make_args nil nil))
                                                   (EX v:val, `(Post witness) (make_args (ret_temp::nil) (v::nil)))
                                                   :: Frame))))).
Proof.
intros. subst paramty.
eapply semax_pre;  [ | apply semax_call_id0; eauto].
rewrite <- (insert_local (tc_exprlist _ _ _)).
apply andp_right.
eapply derives_trans; [ eassumption | ].
apply andp_left2. apply andp_left1.
go_lowerx; intros [? ?]. apply prop_right; auto.
apply andp_right.
apply andp_left1. auto.
apply andp_right.
rewrite <- insert_local.
apply andp_left2.  apply andp_left2. apply andp_left1.
go_lowerx; intro; apply prop_right; auto.
eapply derives_trans; [ eassumption  | ].
apply andp_left2; apply andp_left2; auto.
Qed.

Lemma semax_call_id1_alt:
 forall Espec Delta P Q R ret id paramty retty bl argsig A Pre Post witness Frame
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
  PROPx nil (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: nil) 
       (SEPx (`(Pre witness) (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) :: Frame))) ->
  @semax Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret) (Evar id (Tfunction paramty retty cc_default)) bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post witness) (get_result1 ret) :: map (subst ret (`old)) Frame))))).
Proof.
intros. subst paramty.
eapply semax_pre;  [ | apply semax_call_id1; eauto].
clear H GLBL H0 H1.
rewrite <- (insert_local (tc_exprlist _ _ _)).
apply andp_right.
eapply derives_trans; [ eassumption | ].
apply andp_left2. apply andp_left1.
go_lowerx; intros [? ?]. apply prop_right; auto.
apply andp_right.
apply andp_left1. auto.
apply andp_right.
rewrite <- insert_local.
apply andp_left2.  apply andp_left2. apply andp_left1.
go_lowerx; intro; apply prop_right; auto.
eapply derives_trans; [ eassumption  | ].
apply andp_left2; apply andp_left2; auto.
Qed.


Lemma semax_call_id1':
 forall Espec Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
  forall 
   (CLOSQ: Forall (closed_wrt_vars (eq ret)) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret)) R),
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q)
            (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction (type_of_params argsig) retty cc_default))
             bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q   (SEPx (`(Post x) (get_result1 ret) ::  R))))).
Proof.
intros. rename H2 into Hret.
eapply semax_post;
  [ | apply (semax_call_id1 Espec Delta P Q R ret id retty bl argsig A x Pre Post 
     GLBL H H0 H1 Hret)].
intros ek vl.
apply andp_left2.
unfold normal_ret_assert.
apply andp_derives; auto.
apply andp_derives; auto.
apply exp_left; intro v.
apply andp_derives; auto.
apply andp_derives.
unfold local, lift1 ;intro rho.
clear - CLOSQ.
apply prop_left. intro.
apply prop_right.
induction Q; simpl; auto.
inv CLOSQ.
destruct H.
split.
rewrite closed_wrt_subst in H; auto.
auto.
clear - CLOSR.
unfold SEPx. intro rho.
simpl.
apply sepcon_derives; auto.
induction R; simpl; auto.
inv CLOSR.
apply sepcon_derives.
rewrite closed_wrt_subst; auto.
apply IHR; auto.
Qed.

Lemma semax_call_id1_Eaddrof:
 forall Espec Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) A Pre Post) ->
       (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig, retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q) 
               (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Scall (Some ret)
             (Eaddrof (Evar id (Tfunction (type_of_params argsig) retty cc_default)) (Tpointer (Tfunction (type_of_params argsig) retty cc_default) noattr))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
intros. rename H2 into Hret.
assert (Cop.classify_fun (typeof (Eaddrof (Evar id (Tfunction (type_of_params argsig) retty cc_default)) (Tpointer (Tfunction (type_of_params argsig) retty cc_default) noattr)))=
               Cop.fun_case_f (type_of_params argsig) retty cc_default).
subst; reflexivity.
apply semax_fun_id' with id (mk_funspec (argsig,retty) A Pre Post); auto.
subst. 
eapply semax_pre_simple; [ | apply (semax_call1 Espec Delta A Pre Post x ret argsig retty _ bl P Q R H2 H1 Hret)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
norm_rewrite. repeat rewrite prop_and.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H0.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. apply I.
auto.
unfold SEPx.
simpl.
intro rho.
cancel.
Qed.


Lemma semax_call_id_aux1: forall P Q1 Q R S,
     PROPx P (LOCALx (Q1::Q) R) |-- S -> local Q1 && PROPx P (LOCALx Q R) |-- S.
Proof. intros. eapply derives_trans; try apply H.
  intro rho; normalize.
 unfold PROPx. simpl.
 apply andp_derives; auto.
 unfold LOCALx. simpl.
 unfold local,lift2,lift1.
 apply derives_extract_prop; intro.
 apply andp_right; auto.
 apply prop_right; split; auto.
Qed.

Inductive extract_trivial_liftx {A}: list (environ->A) -> list A -> Prop :=
| ETL_nil: extract_trivial_liftx nil nil
| ETL_cons: forall a al bl,
             extract_trivial_liftx al bl ->
             extract_trivial_liftx (`a :: al) (a::bl).

Fixpoint explicit_cast_exprlist (et: list type) (el: list expr) {struct et} : list expr :=
 match et, el with
 | t::et', e::el' => Ecast e t :: explicit_cast_exprlist et' el'
 | _, _ => nil
 end.

Definition pTree_from_elements {A} (el: list (positive * A)) : PTree.t A :=
 fold_left (fun t ia => PTree.set (fst ia) (snd ia) t) el (PTree.empty _).

Fixpoint force_list {A} (al: list (option A)) : option (list A) :=
 match al with 
 | Some a :: al' => match force_list al' with Some bl => Some (a::bl) | _ => None end
 | nil => Some nil
 | _ => None
 end.

Definition check_one_temp_spec (Q: PTree.t val) (idv: ident * val) : Prop :=
   (Q ! (fst idv)) = Some (snd idv).

Definition check_one_var_spec (Q: PTree.t (type*val)) (idv: ident * (type*val)) : Prop :=
   (Q ! (fst idv)) = Some (snd idv).

Lemma exp_congr:
 forall A NA T X Y, 
    (forall v, X v = Y v) -> @exp A NA T X = @exp A NA T Y.
Proof.
intros. f_equal. extensionality v; auto.
Qed.

Lemma semax_call_id1_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec Delta P Q R ret id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t (type*val))
             (Ppost: val -> list Prop)
             (Rpre: list (environ -> mpred))
             (Rpost: val -> list (environ -> mpred))
             (Rpost': val -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None),
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post) ->
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)) ->
   typeof_temp Delta ret = Some retty -> 
   match retty with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end ->
   paramty = type_of_params argsig ->
   local2ptree Q Qtemp Qvar nil nil ->
   extract_trivial_liftx R R' ->
   (Qtemp ! ret) = None ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_exprlist Delta (argtypes argsig) bl) ->
   Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ->
   local2ptree Qpre Qpre_temp Qpre_var nil nil ->
   extract_trivial_liftx Rpre Rpre' ->
   force_list (map (msubst_eval_expr Qtemp Qvar) (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl ->
   pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) ->
   fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame ->
   Post witness = EX vret:val, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp vret :: nil) 
                              (SEPx (Rpost vret))) ->
   (forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret)) ->
   Post2 = EX vret:val, PROPx (P++ Ppost vret) (LOCALx (temp ret vret :: Q)
             (SEPx (map liftx (Rpost' vret ++ Frame)))) ->
   fold_right_and True Ppre ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret)
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).       
Admitted.


Lemma semax_call_id01_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec Delta P Q R id (paramty: typelist) (retty: type) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t (type*val))
             (Ppost: val -> list Prop)
             (Rpre: list (environ -> mpred))
             (Rpost: val -> list (environ -> mpred))
             (Rpost': val -> list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None),
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,retty) A Pre Post) ->
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,retty) A Pre Post)) ->
   match retty with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end -> (* this hypothesis is not needed for soundness, just for selectivity *)
   paramty = type_of_params argsig ->
   local2ptree Q Qtemp Qvar nil nil ->
   extract_trivial_liftx R R' ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_exprlist Delta (argtypes argsig) bl) ->
   Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ->
   local2ptree Qpre Qpre_temp Qpre_var nil nil ->
   extract_trivial_liftx Rpre Rpre' ->
   force_list (map (msubst_eval_expr Qtemp Qvar) (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl ->
   pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) ->
   fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame ->
   Post witness = EX vret:val, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp vret :: nil) 
                              (SEPx (Rpost vret))) ->
   (forall vret, extract_trivial_liftx (Rpost vret) (Rpost' vret)) ->
   Post2 = EX vret:val, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (map liftx (Rpost' vret ++ Frame)))) ->
   fold_right_and True Ppre ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty retty cc_default))
             bl)
    (normal_ret_assert Post2).       
Admitted.


Lemma semax_call_id00_wow:
 forall  {A} (witness: A) (Frame: list mpred) 
           Espec Delta P Q R id (paramty: typelist) (bl: list expr)
                  (argsig: list (ident * type)) (Pre Post: A -> environ -> mpred)
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre: list (environ -> Prop))
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t (type*val))
             (Ppost: list Prop)
             (Rpre: list (environ -> mpred))
             (Rpost: list (environ -> mpred))
             (Rpost': list mpred)
             (R' Rpre' : list mpred)
             (vl : list val)
   (GLBL: (var_types Delta) ! id = None),
   (glob_specs Delta) ! id = Some (mk_funspec (argsig,Tvoid) A Pre Post) ->
   (glob_types Delta) ! id = Some (type_of_funspec (mk_funspec (argsig,Tvoid) A Pre Post)) ->
   paramty = type_of_params argsig ->
   local2ptree Q Qtemp Qvar nil nil ->
   extract_trivial_liftx R R' ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_exprlist Delta (argtypes argsig) bl) ->
   Pre witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ->
   local2ptree Qpre Qpre_temp Qpre_var nil nil ->
   extract_trivial_liftx Rpre Rpre' ->
   force_list (map (msubst_eval_expr Qtemp Qvar) (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl ->
   pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) ->
   fold_right sepcon emp R' |-- fold_right sepcon emp Rpre' * fold_right sepcon emp Frame ->
   Post witness = PROPx Ppost
                              (LOCALx nil
                              (SEPx (Rpost))) ->
   extract_trivial_liftx Rpost Rpost' ->
   Post2 = PROPx (P++ Ppost) (LOCALx Q
             (SEPx (map liftx (Rpost' ++ Frame)))) ->
   fold_right_and True Ppre ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar id (Tfunction paramty Tvoid cc_default))
             bl)
    (normal_ret_assert Post2).       
Admitted.


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
destruct H. subst x.
apply andp_right; auto.
apply prop_right; auto.
Qed.
