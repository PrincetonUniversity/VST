Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.subsume_funspec.
Import LiftNotation.

Fixpoint argtypes (al: list (ident * type)) : list type :=
 match al with (_,t)::al' => t :: argtypes al' | nil => nil end.

Lemma argtypes_eq: forall al, argtypes al = snd (split al).
Proof.
 induction al; try destruct a; simpl; auto.
 destruct (split al). simpl in *. subst; auto.
Qed.

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {CS: compspecs}.

Definition maybe_retval (Q: @assert Σ) retty ret : assert :=
 match ret with
 | Some id => assert_of (fun rho => Q (get_result1 id rho))
 | None =>
    match retty with
    | Tvoid => assert_of (fun rho => Q (globals_only rho))
    | _ => assert_of (fun rho => ∃ v: val, Q (make_args (ret_temp::nil) (v::nil) rho))
    end
 end.

Definition removeopt_localdef (ret: option ident) (l: list localdef) : list localdef :=
  match ret with
   | Some id => remove_localdef_temp id l
   | None => l
   end.

Lemma semax_call': forall Delta fs A E Pre Post x ret argsig retsig cc a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, _ => True
   end ->
   forall (Hret: tc_fn_return Delta ret retsig)
   (Hsub: funspec_sub fs (mk_funspec (argsig,retsig) cc A E Pre Post)),
  semax (E x) Delta
          ((tc_expr Delta a ∧ tc_exprlist Delta argsig bl)
           ∧
   (▷ assert_of (fun rho => (Pre x (ge_of rho, eval_exprlist argsig bl rho))) ∗
                      assert_of (`(func_ptr fs) (eval_expr a))
     ∗ ▷PROPx P (LOCALx Q (SEPx R))))
          (Scall ret a bl)
          (normal_ret_assert
            (maybe_retval (assert_of (Post x)) retsig ret ∗
               PROPx P (LOCALx (removeopt_localdef ret Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_pre_post'; [ | |
    apply (semax_call_subsume fs A E Pre Post argsig retsig cc
    Hsub Delta x (PROPx P (LOCALx Q (SEPx R))) ret a bl H); auto].
  3:{
    clear - H0.
    destruct retsig; destruct ret; simpl in *; try contradiction;
    intros; congruence.
  }
  + clear Hret.
    rewrite bi.and_elim_r; apply bi.and_mono; first done.
    iIntros "($ & $ & $)".
  + rewrite bi.and_elim_r.
    rewrite /semax_call.maybe_retval; destruct ret; simpl.
    - iIntros "H"; iDestruct "H" as (?) "(H & ?)".
      iSplitR "H".
      * iStopProof; split => rho; simpl.
        iIntros "(_ & $)".
      * iApply remove_localdef_temp_PROP; eauto.
    - split => rho; monPred.unseal.
      iIntros "H"; iDestruct "H" as (?) "($ & ?)".
      iStopProof.
      destruct retsig; try done; simpl; apply bi.exist_mono; intros; iIntros "(_ & $)".
Qed.

Lemma semax_call1: forall Delta fs A E Pre Post x id argsig retsig cc a bl P Q R
   (Hsub: funspec_sub fs (mk_funspec (argsig,retsig) cc A E Pre Post)),
   Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retsig cc  ->
   match retsig with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some id) retsig ->
  semax (E x) Delta
         ((tc_expr Delta a ∧ tc_exprlist Delta argsig bl)
           ∧ (▷assert_of (fun rho => Pre x (ge_of rho, eval_exprlist argsig bl rho)) ∗
                 assert_of (`(func_ptr fs) (eval_expr a)) ∗
                  ▷PROPx P (LOCALx Q (SEPx R))))
          (Scall (Some id) a bl)
          (normal_ret_assert
            (assert_of (fun rho => Post x (get_result1 id rho))
               ∗ PROPx P (LOCALx (remove_localdef_temp id Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_pre_post', semax_call'; try done; rewrite bi.and_elim_r //.
Qed.

Definition ifvoid {T} t (A B: T) :=
 match t with Tvoid => A | _ => B end.

Lemma semax_call0: forall Delta fs A E Pre Post x
      argsig retty cc a bl P Q R
   (Hsub: funspec_sub fs (mk_funspec (argsig,retty) cc A E Pre Post)),
   Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retty cc->
  semax (E x) Delta
         ((*▷*)(tc_expr Delta a ∧ tc_exprlist Delta argsig bl)
           ∧ (▷assert_of (fun rho => Pre x (ge_of rho, eval_exprlist argsig bl rho))
                 ∗ assert_of (`(func_ptr fs) (eval_expr a))
                 ∗ ▷PROPx P (LOCALx Q (SEPx R))))
          (Scall None a bl)
          (normal_ret_assert
            (ifvoid retty (assert_of (`(Post x: environ -> mpred) (make_args nil nil)))
                                                        (∃ v:val, assert_of (`(Post x: environ -> mpred) (make_args (ret_temp::nil) (v::nil))))
            ∗ PROPx P (LOCALx Q (SEPx R)))).
Proof.
intros.
eapply semax_pre_post'; [ | |
   apply (semax_call_subsume fs A E Pre Post argsig retty cc Hsub
               Delta x (PROPx P (LOCALx Q (SEPx R))) None a bl H)].
3:{ split; intros; congruence. }
3:{ apply Coq.Init.Logic.I. }
+ rewrite bi.and_elim_r; apply bi.and_mono; first done.
  iIntros "($ & $ & $)".
+ rewrite /semax_call.maybe_retval /= bi.and_elim_r.
  split => rho; monPred.unseal.
  iIntros "H"; iDestruct "H" as (?) "($ & ?)".
  iStopProof.
  destruct retty; simpl; try done; apply bi.exist_mono; intros; iIntros "(_ & $)".
Qed.

Lemma semax_fun_id':
      forall id f TC
              E Delta (PQR: assert) PostCond c
            (GLBL: (var_types Delta) !! id = None),
       (glob_specs Delta) !! id = Some f ->
       (glob_types Delta) !! id = Some (type_of_funspec f) ->
       semax E Delta
        (TC ∧ (local (tc_environ Delta) ∧
                     (assert_of (`(func_ptr f) (eval_var id (type_of_funspec f)))
                     ∗ ▷PQR)))
                              c PostCond ->
       semax E Delta (TC ∧ ▷ PQR) c PostCond.
Proof.
  intros.
  apply (semax_fun_id id f E Delta); auto.
  eapply semax_pre_post; try apply H1; intros; try by rewrite bi.and_elim_r.
  iIntros "(? & ? & ?)"; iSplit.
  { rewrite bi.and_elim_l; iFrame.
    iStopProof; split => rho; monPred.unseal; auto. }
  rewrite bi.and_elim_r; iFrame.
Qed.

Lemma eqb_typelist_refl: forall tl, eqb_typelist tl tl = true.
Proof.
induction tl; simpl; auto.
apply andb_true_iff.
split; auto.
apply eqb_type_refl.
Qed.

Lemma semax_call_id0:
 forall Delta P Q R id bl fs argsig retty cc A E Pre Post x
   (Hsub: funspec_sub fs (mk_funspec (argsig,retty) cc A E Pre Post))
   (GLBL: (var_types Delta) !! id = None),
       (glob_specs Delta) !! id = Some fs ->
       (glob_types Delta) !! id = Some (type_of_funspec fs) ->
  semax (E x) Delta ((*▷*) (tc_exprlist Delta argsig bl
                  ∧ ▷ (assert_of (fun rho => Pre x (ge_of rho, eval_exprlist argsig bl rho))
                         ∗ PROPx P (LOCALx Q (SEPx R)))))
    (Scall None (Evar id (Tfunction (typelist_of_type_list argsig) retty cc)) bl)
    (normal_ret_assert
       ((ifvoid retty (assert_of (`(Post x: environ -> mpred) (make_args nil nil)))
                                                   (∃ v:val, assert_of (`(Post x: environ -> mpred) (make_args (ret_temp::nil) (v::nil)))))
         ∗ PROPx P (LOCALx Q (SEPx R)))).
Proof.
  intros.
  apply (semax_fun_id' id fs (tc_exprlist Delta argsig bl) (E x) Delta); auto.
  eapply semax_pre_simple; [ | apply (semax_call0 Delta fs A E Pre Post x argsig _ cc _ bl P Q R Hsub); auto].
  rewrite bi.and_elim_r; apply bi.and_mono.
  { apply bi.and_intro; last done.
    rewrite /tc_expr /typecheck_expr /= /get_var_type GLBL H0 denote_tc_assert_bool.
    apply bi.pure_intro.
    rewrite (type_of_funspec_sub _ _ Hsub) /=.
    rewrite eqb_typelist_refl eqb_type_refl eqb_calling_convention_refl //. }
  iIntros "(_ & ? & $ & $)".
  rewrite (type_of_funspec_sub _ _ Hsub) //.
Qed.

Lemma semax_call_id1:
 forall Delta P Q R ret id fs retty cc bl argsig A E Pre Post x
   (Hsub: funspec_sub fs (mk_funspec (argsig,retty) cc A E Pre Post))
   (GLBL: (var_types Delta) !! id = None)
   (H: (glob_specs Delta) !! id = Some fs)
   (Ht: (glob_types Delta) !! id = Some (type_of_funspec fs))
   (H0: match retty with
   | Tvoid => False
   | _ => True
   end)
   (Hret: tc_fn_return Delta (Some ret) retty),
  semax (E x) Delta ((tc_exprlist Delta argsig bl ∧
                ▷(assert_of (fun rho => Pre x (ge_of rho, eval_exprlist argsig bl rho))
                  ∗ PROPx P (LOCALx Q (SEPx R)))))
    (Scall (Some ret)
             (Evar id (Tfunction (typelist_of_type_list argsig) retty cc))
             bl)
    (normal_ret_assert
       ((assert_of (`(Post x: environ -> mpred) (get_result1 ret))
           ∗ PROPx P (LOCALx (remove_localdef_temp ret Q) (SEPx R))))).
Proof.
  intros.
  apply (semax_fun_id' id fs); auto.
  eapply semax_pre_simple; [ | apply (semax_call1 Delta fs A E Pre Post x ret argsig retty cc _ bl P Q R Hsub); auto].
  rewrite bi.and_elim_r; apply bi.and_mono.
  { apply bi.and_intro; last done.
    rewrite /tc_expr /typecheck_expr /= /get_var_type GLBL Ht denote_tc_assert_bool.
    apply bi.pure_intro.
    rewrite (type_of_funspec_sub _ _ Hsub) /=.
    rewrite eqb_typelist_refl eqb_type_refl eqb_calling_convention_refl //. }
  iIntros "(_ & ? & $ & $)".
  rewrite (type_of_funspec_sub _ _ Hsub) //.
Qed.

Inductive extract_trivial_liftx {A}: list (environ->A) -> list A -> Prop :=
| ETL_nil: extract_trivial_liftx nil nil
| ETL_cons: forall a al bl,
             extract_trivial_liftx al bl ->
             extract_trivial_liftx (`a :: al) (a::bl).

Lemma fold_right_and_app_low:
  forall (Q1 Q2 : list Prop),
  fold_right and True%type (Q1 ++ Q2) ≡
  (fold_right and True%type Q1  /\ fold_right and True%type Q2).
Proof.
  induction Q1; intros; simpl; first by hnf; tauto.
  rewrite IHQ1.
  hnf; tauto.
Qed.

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

(*Lemma isolate_LOCAL_lem1:
  forall Q, (PROPx(Σ := Σ)) nil (LOCALx Q (SEPx (True::nil))) = local (fold_right `(and) `(True%type) (map locald_denote Q)).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, SEPx.
 simpl fold_right_sepcon.
 normalize.
Qed.*)

Lemma Forall_ptree_elements_e:
  forall A (F: ident * A -> Prop) m i v,
   Forall F (PTree.elements m) ->
   m !! i = Some v ->
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
    (pTree_from_elements (combine fl vl)) !! i = Some v ->
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
     * rewrite -> PTree.gso in H0 by auto.
       apply IHfl in H0.
       rewrite unfold_make_args_cons.
       unfold eval_id.  simpl. rewrite -> Map.gso by auto. apply H0.
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

Lemma PROP_combine:
 forall P P' Q Q' R R',
  PROPx(Σ := Σ) P (LOCALx Q (SEPx R)) ∗ PROPx P' (LOCALx Q' (SEPx R')) ⊣⊢
  PROPx (P++P') (LOCALx (Q++Q') (SEPx (R++R'))).
Proof.
  intros.
  unfold PROPx, LOCALx, SEPx, local, lift1.
  split => rho; monPred.unseal.
  normalize.
  f_equiv.
  - rewrite map_app fold_right_and_app_low fold_right_and_app.
    f_equiv; tauto.
  - rewrite fold_right_sepcon_app //.
Qed.

Inductive Parameter_types_in_funspec_different_from_call_statement : Prop := .
Inductive Result_type_in_funspec_different_from_call_statement : Prop := .

Definition check_retty t :=
    match t with Tvoid => Result_type_in_funspec_different_from_call_statement
                      |  Tarray _ _ _ => Result_type_in_funspec_different_from_call_statement
                      | _ => True%type
    end.

(*Lemma PROP_LOCAL_SEP_f:
  forall P Q R f, `(PROPx P (LOCALx Q (SEPx R))) f =
     local (fold_right `(and) `(True) (map (fun q : environ -> Prop => `q f) (map locald_denote Q)))
     ∧ PROPx P (LOCALx nil (SEPx R)).
Proof. intros. extensionality rho.
cbv delta [PROPx LOCALx SEPx local lift lift1 liftx]; simpl.
normalize.
f_equal. f_equal.
replace (fold_right (fun (x x0 : environ -> Prop) (x1 : environ) => x x1 /\ x0 x1)
   (fun _ : environ => True) (map locald_denote Q) (f rho))
  with (fold_right (fun (x x0 : environ -> Prop) (x1 : environ) => x x1 /\ x0 x1)
   (fun _ : environ => True)
   (map (fun (q : environ -> Prop) (x : environ) => q (f x))
      (map locald_denote Q)) rho);  [apply prop_ext; tauto | ].
induction Q; simpl; auto. f_equal; auto.
Qed.
#[export] Hint Rewrite PROP_LOCAL_SEP_f: norm2.*)

Definition global_funspec Delta id argsig retty cc A E Pre Post :=
   (var_types Delta) !! id = None /\
   (glob_specs Delta) !! id = Some (mk_funspec (argsig,retty) cc A E Pre Post) /\
   (glob_types Delta) !! id = Some (type_of_funspec (mk_funspec (argsig,retty) cc A E Pre Post)).

Lemma lookup_funspec:
  forall Delta id argsig retty cc A E Pre Post,
   (var_types Delta) !! id = None ->
   (glob_specs Delta) !! id = Some (mk_funspec (argsig,retty) cc A E Pre Post) ->
   (glob_types Delta) !! id = Some (type_of_funspec (mk_funspec (argsig,retty) cc A E Pre Post)) ->
   global_funspec Delta id argsig retty cc A E Pre Post.
Proof.
intros.
split3; auto.
Qed.


Definition can_assume_funcptr E Delta P Q R a fs :=
 forall c Post,
 semax E Delta ((∃ v: val, ⎡func_ptr fs v⎤ ∧ local (`(eq v) (eval_expr a))) ∗
                   PROPx P (LOCALx Q (SEPx R))) c Post ->
 semax E Delta (PROPx P (LOCALx Q (SEPx R))) c Post.

Definition OLDcall_setup1
  E Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (bl: list expr) (vl : list val)
 :=
  local2ptree Q = (Qtemp, Qvar, nil, GV) /\
  funspec_sub fs (mk_funspec (argsig,retty) cc A Ef Pre Post) /\

  can_assume_funcptr E Delta P Q R' a fs /\
  (PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R))) /\

  Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retty cc /\
  (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
         ⊢ (tc_expr Delta a))  /\
  (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          ⊢  (tc_exprlist Delta argsig bl)) /\
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist argsig bl))
                = Some vl.

Definition call_setup1
  E Qtemp Qvar GV a Delta P Q R (*R'*)
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (bl: list expr) (vl : list val)
 :=
  local2ptree Q = (Qtemp, Qvar, nil, GV) /\
  funspec_sub fs (mk_funspec (argsig,retty) cc A Ef Pre Post) /\

  can_assume_funcptr E Delta P Q R a fs /\

  Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retty cc /\
  (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
         ⊢ (tc_expr Delta a) ) /\
  (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          ⊢  (tc_exprlist Delta argsig bl)) /\
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist argsig bl))
                = Some vl.

Lemma OLDcall_setup1_i:
 forall E Delta P Q R R' (a: expr) (bl: list expr)
   Qtemp Qvar GV (v: val)
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (vl : list val),
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  msubst_eval_expr Delta Qtemp Qvar GV a = Some v ->

  (fold_right_sepcon R' ⊢ <absorb> func_ptr fs v) ->

  funspec_sub fs (mk_funspec (argsig,retty) cc A Ef Pre Post) ->

  (fold_right_sepcon R' ⊢ ▷ fold_right_sepcon R) ->

  Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
         ⊢ (tc_expr Delta a)  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          ⊢  (tc_exprlist Delta argsig bl) ->
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist argsig bl))
                = Some vl ->
 OLDcall_setup1 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*).
Proof.
  intros.
  assert (H18 := msubst_eval_expr_eq Delta P Qtemp Qvar GV R' a v H0).
  assert (H19 := local2ptree_soundness P Q R' Qtemp Qvar nil GV H).
  split; repeat match goal with |- _ /\ _ => split end; auto.
  2: { iIntros "(? & ? & ?)"; rewrite /SEPx H3; repeat (iSplit; auto). }
  hnf; intros.
  eapply semax_pre; [ | eassumption].
  clear c Post0 H8.
  Exists v.
  iIntros "(#? & H)"; iSplit; last done.
  iAssert (local ((` (eq v)) (eval_expr a))) with "[-]" as "#?".
  - rewrite -H18.
    iSplit; first done.
    by iApply H19.
  - iDestruct "H" as "(_ & _ & H)".
    rewrite /SEPx H1 embed_absorbingly.
    rewrite bi.persistent_and_affinely_sep_r bi.absorbingly_sep; iFrame; auto.
Qed.

Lemma call_setup1_i:
 forall E Delta P Q R (a: expr) (bl: list expr)
   Qtemp Qvar GV (v: val)
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (vl : list val),
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  msubst_eval_expr Delta Qtemp Qvar GV a = Some v ->

  (fold_right_sepcon R ⊢ <absorb> func_ptr fs v) ->

  funspec_sub fs (mk_funspec (argsig,retty) cc A Ef Pre Post) ->

  Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
         ⊢ (tc_expr Delta a)  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          ⊢  (tc_exprlist Delta argsig bl) ->
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist argsig bl))
                = Some vl ->
 call_setup1 E Qtemp Qvar GV a Delta P Q R (*R'*) fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*).
Proof.
  intros.
  assert (H18 := msubst_eval_expr_eq Delta P Qtemp Qvar GV R a v H0).
  assert (H19 := local2ptree_soundness P Q R Qtemp Qvar nil GV H).
  split; repeat match goal with |- _ /\ _ => split end; auto.
  hnf; intros.
  eapply semax_pre; [ | eassumption].
  clear c Post0 H7.
  Exists v.
  iIntros "(#? & H)"; iSplit; last done.
  iAssert (local ((` (eq v)) (eval_expr a))) with "[-]" as "#?".
  - rewrite -H18.
    iSplit; first done.
    by iApply H19.
  - iDestruct "H" as "(_ & _ & H)".
    rewrite /SEPx H1 embed_absorbingly.
    rewrite bi.persistent_and_affinely_sep_r bi.absorbingly_sep; iFrame; auto.
Qed.

Lemma OLDcall_setup1_i2:
 forall E Delta P Q R R' (id: ident) (ty: type) (bl: list expr)
   Qtemp Qvar GV
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (vl : list val),
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->

  can_assume_funcptr E Delta P Q R' (Evar id ty) fs ->

  funspec_sub fs (mk_funspec (argsig,retty) cc A Ef Pre Post) ->

  (PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R))) ->

  Cop.classify_fun ty = Cop.fun_case_f (typelist_of_type_list argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
         ⊢ (tc_expr Delta (Evar id ty))  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          ⊢  (tc_exprlist Delta argsig bl) ->
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist argsig bl))
                = Some vl ->
 OLDcall_setup1 E Qtemp Qvar GV (Evar id ty) Delta P Q R R' fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*).
Proof.
  intros.
  split; repeat match goal with |- _ /\ _ => split end; auto.
Qed.

Lemma call_setup1_i2:
 forall E Delta P Q R  (id: ident) (ty: type) (bl: list expr)
   Qtemp Qvar GV
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (vl : list val),
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->

  can_assume_funcptr E Delta P Q R (Evar id ty) fs ->

  funspec_sub fs (mk_funspec (argsig,retty) cc A Ef Pre Post) ->

  Cop.classify_fun ty = Cop.fun_case_f (typelist_of_type_list argsig) retty cc ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
         ⊢ (tc_expr Delta (Evar id ty))  ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          ⊢  (tc_exprlist Delta argsig bl) ->
  force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                    (explicit_cast_exprlist argsig bl))
                = Some vl ->
 call_setup1 E Qtemp Qvar GV (Evar id ty) Delta P Q R fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*).
Proof.
  intros.
  split; repeat match goal with |- _ /\ _ => split end; auto.
Qed.

Lemma can_assume_funcptr1:
  forall E Delta P Q R a fs v Qtemp Qvar GV,
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  msubst_eval_expr Delta Qtemp Qvar GV a = Some v ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ <absorb> ⎡func_ptr fs v⎤ ->
   can_assume_funcptr E Delta P Q R a fs.
Proof.
  intros.
  unfold can_assume_funcptr; intros.
  eapply semax_pre; [ | eassumption].
  Exists v.
  iIntros "(#? & H)"; iSplit; last done.
  iAssert (local ((` (eq v)) (eval_expr a))) with "[-]" as "#?".
  - assert (H8 := msubst_eval_expr_eq Delta P Qtemp Qvar GV R a v H0).
    eapply local2ptree_soundness' in H.
    simpl in H; rewrite <- H in H8.
    rewrite -H8 app_nil_r; auto.
  - rewrite bi.persistent_and_affinely_sep_r bi.absorbingly_sep; iSplit; auto.
    iApply H1; auto.
Qed.

Lemma can_assume_funcptr2:
  forall id ty cs Delta P Q R fs ,
   (var_types Delta) !! id = None ->
   (glob_specs Delta) !! id = Some fs ->
   (glob_types Delta) !! id = Some (type_of_funspec fs) ->
   ty = (type_of_funspec fs) ->
   can_assume_funcptr cs Delta P Q R (Evar id ty) fs.
Proof.
  unfold can_assume_funcptr; intros.
  eapply (semax_fun_id id); try eassumption.
  eapply semax_pre; try apply H3. clear H3.
  rewrite bi.and_elim_r.
  split => rho; monPred.unseal.
  rewrite comm; apply bi.sep_mono; last done.
  Exists (eval_var id (type_of_funspec fs) rho).
  iIntros "$"; iPureIntro.
  subst ty; unfold_lift; auto.
Qed.

Lemma local2ptree_aux_gvarsSome: forall gs T1 T2 P a,
   local2ptree_aux (map gvars gs) T1 T2 P (Some a)
   = (T1, T2, (rev(map (eq a) gs)) ++ P, Some a).
Proof.
induction gs; simpl; intros. trivial.
rewrite IHgs. rewrite <- app_assoc. trivial.
Qed.

Lemma local2ptree_aux_gvarsNone {gs T1 T2 P}:
   local2ptree_aux (map gvars gs) T1 T2 P None
   = match gs with nil => (T1, T2, P, None)
     | a :: gs' => (T1, T2, (rev(map (eq a) gs')) ++ P, Some a)
     end.
Proof. destruct gs. trivial. apply local2ptree_aux_gvarsSome. Qed.

Lemma local2ptree_gvars {gs}:
   local2ptree (map gvars gs)
   = match gs with nil => (PTree.empty _, PTree.empty _, nil, None)
     | a :: gs' => (PTree.empty _, PTree.empty _, rev(map (eq a) gs'), Some a)
     end.
Proof.
  unfold local2ptree; rewrite local2ptree_aux_gvarsNone.
  destruct gs; try rewrite app_nil_r; trivial.
Qed.

Definition call_setup2
  E Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (bl: list expr) (vl : list val)
  witness
  (Frame: list mpred)
  (Ppre: list Prop) (Rpre: list mpred)
  GV' gv args :=
 call_setup1 E Qtemp Qvar GV a Delta P Q R' fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*) /\
  (PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R))) /\
  Ef witness ⊆ E /\
  Pre witness = PROPx Ppre (LAMBDAx gv args (SEPx Rpre)) /\
  local2ptree (map gvars gv) = (PTree.empty _, PTree.empty _, nil, GV') /\
  (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) ⊢ ⌜firstn (length argsig) vl=args⌝) /\
  check_gvars_spec GV GV' /\
  (fold_right_sepcon R ⊢ fold_right_sepcon Rpre ∗ fold_right_sepcon Frame).

Lemma call_setup2_i:
 forall E Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: TypeTree) Ef Pre Post
  (bl: list expr) (vl : list val)
  (SETUP1: call_setup1 E Qtemp Qvar GV a Delta P Q R' fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*))
  witness'
  (Frame: list mpred)
  (Ppre: list Prop) (Rpre: list mpred)
  GV' gv args,
  Ef witness' ⊆ E ->
  Pre witness' = PROPx Ppre (LAMBDAx gv args (SEPx Rpre)) ->
  local2ptree (map gvars gv) = (PTree.empty _, PTree.empty _, nil, GV') ->

  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) ⊢ ⌜firstn (length argsig) vl=args⌝ ->

  (PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R))) ->
  check_gvars_spec GV GV' ->
  (fold_right_sepcon R ⊢ fold_right_sepcon Rpre ∗ fold_right_sepcon Frame) ->
  call_setup2 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Ef Pre Post bl vl (*Qactuals*)
      witness' Frame Ppre Rpre GV' gv args.
Proof.
  intros. split. auto. split; repeat match goal with |- _ /\ _ => split end; auto.
Qed.

(*Definition call_setup2_nil
  E Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: TypeTree)  Pre Post
  (bl: list expr) (vl : list val)
  witness
  (Frame: list mpred)
  (Ppre: list Prop) (Rpre: list mpred)
  GV' gv args:=
 call_setup1 E Qtemp Qvar GV a Delta P Q R' fs argsig retty cc A Pre Post bl vl (*Qactuals*) /\
  (PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R))) /\
  Pre witness = PROPx Ppre (LAMBDAx gv args (SEPx Rpre)) /\
  local2ptree (map gvars gv) = (PTree.empty _, PTree.empty _, nil, GV') /\

  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) ⊢ ⌜firstn (length argsig) vl=args⌝ /\

  check_gvars_spec GV GV' /\
  (fold_right_sepcon R ⊢ fold_right_sepcon Rpre ∗ fold_right_sepcon Frame).

Lemma call_setup2_nil_equiv:
  forall (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: TypeTree)  Pre Post
  (bl: list expr) (vl : list val)
  witness
  (Frame: list mpred)
  (Ppre: list Prop) (Rpre: list mpred)
   GV' gv args,
    call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R'
                    fs argsig retty cc A Pre Post bl vl
                    witness Frame Ppre Rpre GV' gv args =
    call_setup2 cs Qtemp Qvar GV a Delta P Q R R'
                    fs argsig retty cc nil A Pre Post bl vl
                    witness Frame Ppre Rpre GV' gv args.
reflexivity. Qed.

Lemma call_setup2_i_nil:
 forall  (cs: compspecs) Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc (A: TypeTree)  Pre Post
  (bl: list expr) (vl : list val)
  (SETUP1: call_setup1 cs Qtemp Qvar GV a Delta P Q (*R*)R' fs argsig retty cc A Pre Post bl vl (*Qactuals*))
  (witness': functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  GV' gv args,
  Pre nil witness' = PROPx Ppre (LAMBDAx gv args (SEPx Rpre)) ->
  local2ptree (map gvars gv) = (PTree.empty _, PTree.empty _, nil, GV')  ->

  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) ⊢ ⌜firstn (length argsig) vl=args⌝ ->

  PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R)) ->
  check_gvars_spec GV GV' ->
  fold_right_sepcon R ⊢ fold_right_sepcon Rpre ∗ fold_right_sepcon Frame ->
  call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post bl vl (*Qactuals*)
      witness' Frame Ppre Rpre GV' gv args.
Proof.
 intros. split. auto. split; repeat match goal with |- _ /\ _ => split end; auto.
Qed.*)

Lemma actual_value_not_Vundef:
 forall (cs: compspecs) (Qtemp: PTree.t val) (Qvar: PTree.t (type * val))
     Delta P Q R tl bl vl GV
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, GV))
 (MSUBST : force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
                           (explicit_cast_exprlist tl bl)) = Some vl),
   (tc_exprlist Delta tl bl) ∧ local (tc_environ Delta) ∧ ▷ PROPx P (LOCALx Q (SEPx R))
   ⊣⊢ (tc_exprlist Delta tl bl) ∧ local (tc_environ Delta) ∧ ▷ (PROPx P (LOCALx Q (SEPx R)) ∧ ⌜Forall (fun v : val => v <> Vundef) vl⌝).
Proof.
  intros.
  eapply (msubst_eval_exprlist_eq Delta P Qtemp Qvar GV R) in MSUBST.
  apply (local2ptree_soundness P Q R) in PTREE; simpl app in PTREE.
  rewrite <- PTREE in MSUBST; clear PTREE; rename MSUBST into EVAL.
  apply bi.equiv_entails_2.
  2: { apply bi.and_mono, bi.and_mono; [done..|]; iIntros "($ & _)". }
  rewrite assoc (bi.and_comm (tc_exprlist _ _ _) (local _)) -assoc.
  iIntros "(#? & H)".
  iSplit; first rewrite bi.and_elim_l //.
  iSplit; first done.
  iIntros "!>"; iSplit; first rewrite bi.and_elim_r //.
  iPoseProof (EVAL with "[-]") as "#H1".
  { rewrite bi.and_elim_r; auto. }
  rewrite bi.and_elim_l.
  iStopProof.
  split => rho; monPred.unseal; rewrite monPred_at_intuitionistically.
  unfold_lift; simpl.
  iIntros "((% & ->) & ?)".
  iPoseProof (tc_eval_exprlist with "[-]") as "%"; [done..|].
  iPureIntro.
  eapply tc_vals_Vundef; eauto.
Qed.

Lemma in_gvars_sub:
  forall rho G G', Forall (fun x : globals => In x G) G' ->
  fold_right `(and) `(True%type) (map locald_denote (map gvars G)) rho ->
  fold_right `(and) `(True%type) (map locald_denote (map gvars G')) rho.
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

Lemma rev_nil_elim {A} {l:list A}: rev l = nil -> l=nil.
Proof. induction l; simpl; trivial.
intros. exfalso. eapply app_cons_not_nil. symmetry. apply H. Qed.

Lemma local2ptree_aux_elim: forall Q rho
(H: fold_right (` and) (` True%type) (map locald_denote Q) rho) T1 T2 P X Qtemp Qvar PP g
(L: local2ptree_aux Q T1 T2 P X = (Qtemp, Qvar, PP, Some g))
(HX: match X with
      Some gg => (` and) (gvars_denote gg) (` True%type)
                 (mkEnviron (ge_of rho) (Map.empty (block * type)) (Map.empty val))
    | None => True
     end),
(` and) (gvars_denote g) (` True%type)
  (mkEnviron (ge_of rho) (Map.empty (block * type)) (Map.empty val)).
Proof.
intros ? ? ?.
induction Q; intros.
+ simpl in L. inv L. trivial.
+ destruct H. destruct a; simpl in L.
  * destruct (T1 !! i).
    - apply IHQ in L; clear IHQ; trivial.
    - apply IHQ in L; clear IHQ; trivial.
  * destruct (T2 !! i).
    - destruct p; apply IHQ in L; clear IHQ; trivial.
    - apply IHQ in L; clear IHQ; trivial.
  * destruct X.
    - apply IHQ in L; clear IHQ; trivial.
    - apply IHQ in L; clear IHQ; trivial.
      clear - H. unfold locald_denote in H. split. apply H. unfold_lift; trivial.
Qed.

Lemma semax_call_aux55:
 forall (Qtemp: PTree.t val) (Qvar: PTree.t (type * val)) GV (a: expr)
     Delta P Q R R' fs argsig (A : TypeTree)
     (Pre : dtfr (ArgsTT A))
    witness Frame bl Ppre Rpre GV' vl gv args
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, GV))
 (MSUBST : force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
              (explicit_cast_exprlist argsig bl)) = Some vl)

 (PRE1: Pre witness = PROPx Ppre (LAMBDAx gv args (SEPx Rpre)))
 (PTREE': local2ptree (map gvars gv) = (PTree.empty _, PTree.empty _, nil, GV'))
 (CHECKTEMP : firstn (length argsig) vl=args)

 (CHECKG: check_gvars_spec GV GV' )
 (HR': PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R)))
 (FRAME : fold_right_sepcon R
           ⊢ fold_right_sepcon Rpre ∗ fold_right_sepcon Frame)
 (PPRE : fold_right_and True Ppre)
 (LEN : length argsig = length bl),
ENTAIL Delta, (tc_expr Delta a ∧ tc_exprlist Delta argsig bl ∧
(∃ v : val,
 ⎡func_ptr fs v⎤ ∧
 local (` (eq v) (eval_expr a))) ∗ PROPx P (LOCALx Q (SEPx R')))
⊢((tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
    (▷ (assert_of (fun rho => Pre witness (ge_of rho, eval_exprlist argsig bl rho))) ∗
     assert_of (` (func_ptr fs)
       (eval_expr a)) ∗ ▷PROPx P (LOCALx Q (SEPx Frame)))).
Proof.
  intros; subst args.
  pose proof actual_value_not_Vundef _ _ _ _ P _ R _ _ _ _ PTREE MSUBST as VUNDEF.
  Intros v.
  apply bi.and_intro.
  { rewrite bi.and_elim_r assoc bi.and_elim_l //. }
  rewrite bi.sep_assoc (bi.sep_comm (▷ _)) -assoc -bi.later_sep.
  iIntros "(#TC & _ & _ & #(FP & A) & H)"; iSplitL "".
  - iClear "TC"; iStopProof; split => rho; monPred.unseal.
    rewrite monPred_at_intuitionistically /= /lift1. unfold_lift. by iIntros "(#H & ->)".
  - rewrite HR'; iNext.
    iAssert (local ((` (eq vl)) (eval_exprlist argsig bl))) with "[-]" as "#?".
    { apply (local2ptree_soundness P _ R) in PTREE. simpl app in PTREE.
      apply @msubst_eval_exprlist_eq with (P:=P)(R:=R)(GV:=GV) in MSUBST.
      iApply MSUBST; rewrite PTREE; auto. }
    iClear "TC FP A".
    iDestruct "H" as "(#? & #? & H)".
    rewrite PRE1 /SEPx FRAME.
    iDestruct "H" as "(Pre & Frame)"; iSplitL "Pre".
    + iStopProof; split => rho; monPred.unseal.
      rewrite monPred_at_intuitionistically /PROPx /PARAMSx /GLOBALSx /LOCALx /=; monPred.unseal.
      unfold_lift.
      iIntros "(#(-> & % & %) & H)".
      iSplit.
      { iPureIntro; clear - PPRE; induction Ppre; auto; simpl in *.
        destruct PPRE; auto. }
      rewrite LEN -(eval_exprlist_length argsig bl rho) // take_ge //.
      iSplit; first done.
      rewrite /lift1; iFrame; iPureIntro; split; last done.
      rewrite local2ptree_gvars in PTREE'.
      destruct gv; inv PTREE'.
      * simpl; auto.
      * simpl in CHECKG; subst. apply rev_nil_elim in H2. apply map_eq_nil in H2.
        subst. simpl.
        apply (local2ptree_aux_elim _ _ H0 _ _ _ _ _ _ _ _ PTREE); trivial.
    + rewrite /PROPx /LOCALx; auto.
Qed.

(*Lemma semax_call_aux55_nil:
 forall (cs: compspecs) (Qtemp: PTree.t val) (Qvar: PTree.t (type * val)) GV (a: expr)
     Delta P Q R R' fs argsig
    (A : TypeTree)
         (Pre: forall ts : list Type,
              functors.MixVariantFunctor._functor
                (rmaps.dependent_type_functor_rec
                   ts (ArgsTrue A)) mpred)
          (Post : forall ts : list Type,
              functors.MixVariantFunctor._functor
                (rmaps.dependent_type_functor_rec
                   ts (AssertTrue A)) mpred)
    witness Frame bl Ppre Rpre GV' vl gv args
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, GV))
 (MSUBST : force_list (map (msubst_eval_expr Delta Qtemp Qvar GV)
              (explicit_cast_exprlist argsig bl)) = Some vl)
 (PRE1: Pre nil witness = PROPx Ppre (LAMBDAx gv args (SEPx Rpre)))
 (PTREE': local2ptree (map gvars gv) = (PTree.empty _, PTree.empty _, nil, GV'))
  (CHECKTEMP : firstn (length argsig) vl =args)

 (CHECKG: check_gvars_spec GV GV')
 (HR': PROPx P (LOCALx Q (SEPx R')) ⊢ ▷ PROPx P (LOCALx Q (SEPx R)))
 (FRAME : fold_right_sepcon R
           ⊢ fold_right_sepcon Rpre ∗ fold_right_sepcon Frame)
 (PPRE : fold_right_and True Ppre)
 (LEN : length argsig = length bl),
ENTAIL Delta, tc_expr Delta a ∧ tc_exprlist Delta argsig bl ∧
(∃ v : val,
 lift0 (func_ptr fs v) ∧
 local (` (eq v) (eval_expr a))) ∧ PROPx P (LOCALx Q (SEPx R'))
⊢ (tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
    (▷ (fun rho => Pre nil witness (ge_of rho, eval_exprlist argsig bl rho)) ∗
     ` (func_ptr fs)
       (eval_expr a) ∗ ▷PROPx P (LOCALx Q (SEPx Frame))).
Proof. intros. eapply semax_call_aux55 with (ts:=nil); eassumption. Qed.*)

Lemma tc_exprlist_len : forall Delta argsig bl,
  tc_exprlist Delta argsig bl ⊢ ⌜length argsig = length bl⌝.
Proof.
 intros.
 go_lowerx.
 unfold tc_exprlist.
 revert bl; induction argsig; destruct bl;
   simpl; auto.
 rewrite expr2.denote_tc_assert_andp bi.and_elim_r IHargsig; auto.
Qed.

Lemma semax_pre_setup2 E Delta fs a bl argsig P Q R' Post2 rv (vl args:list val)
      (TC0 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) ⊢ tc_expr Delta a)
      (TC1 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R')) ⊢ tc_exprlist Delta argsig bl)
      (CHECKTEMP : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R'))
                                       ⊢ ⌜firstn (length argsig) vl=args⌝):
  semax E Delta
         (⌜Datatypes.length argsig = Datatypes.length bl⌝ ∧
             ⌜firstn (length argsig) vl=args⌝ ∧
             (PROPx P (LOCALx Q (SEPx R')) ∧ (tc_expr Delta a ∧ tc_exprlist Delta argsig bl)) ∗
             (∃ v : val, ⎡func_ptr fs v⎤ ∧ local ((` (eq v)) (eval_expr a)))%assert)
         (Scall rv a bl) (normal_ret_assert Post2) ->

  semax E Delta
         ((∃ v : val, ⎡func_ptr fs v⎤ ∧ local ((` (eq v)) (eval_expr a)))%assert ∗
         PROPx P (LOCALx Q (SEPx R'))) (Scall rv a bl) (normal_ret_assert Post2).
Proof.
  intros.
  eapply semax_pre, H.
  iIntros "(#? & $ & ?)".
  iSplit.
  { iApply tc_exprlist_len; iApply TC1; auto. }
  iSplit.
  { iApply CHECKTEMP; auto. }
  iSplit; first done.
  iSplit; [iApply TC0 | iApply TC1]; auto.
Qed.

Lemma semax_call_id00_wow:
 forall {E} {Qtemp Qvar a GV Delta P Q R R'
   fs argsig retty cc} {A: TypeTree} {Ef: dtfr (MaskTT A)} {Pre: dtfr (ArgsTT A)} {Post: dtfr (AssertTT A)}
   {witness}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred} {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Ef Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
             (Post2: assert)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpost: B -> list mpred)
   (RETrueY: retty = Tvoid)
   (POST1: assert_of (Post witness) ⊣⊢ (∃ vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (POST2: Post2 ⊣⊢ ∃ vret:B, PROPx (P ++ Ppost vret) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof.
  intros.
  destruct SETUP as [[PTREE [Hsub [SPEC [ATY [TC0 [TC1 MSUBST]]]]]]
                            [HR' [HE [PRE1 [PTREE' [CHECKTEMP [CHECKG FRAME]]]]]]].
  apply SPEC. clear SPEC.
  eapply semax_pre_setup2; try eassumption.
  clear CHECKTEMP.
  remember (tc_expr Delta a ∧ tc_exprlist Delta argsig bl) as TChecks.
  apply semax_extract_prop; intros.
  apply semax_extract_prop; intros.
  eapply semax_mask_mono; first done.
  eapply semax_pre_post', (semax_call0 Delta fs A Ef Pre Post
              witness argsig retty cc a bl P Q Frame Hsub).
  * subst TChecks. rewrite -semax_call_aux55 //.
    iIntros "(? & H)"; iSplit; auto.
    iSplit.
    { iDestruct "H" as "((_ & $ & _) & _)". }
    iSplit.
    { iDestruct "H" as "((_ & _ & $) & _)". }
    rewrite bi.and_elim_l comm //.
  * subst.
    clear  TC1 PRE1 PPRE.
    rewrite POST2.
    go_lowerx.
    eapply monPred_in_equiv in POST1.
    simpl in POST1.
    rewrite POST1; clear POST1.
    unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift. monPred.unseal. normalize.
    Exists x.
    rewrite fold_right_and_app_low.
    rewrite fold_right_sepcon_app.
    normalize.
  * assumption.
Qed.

(*Lemma semax_call_id00_wow_nil:
 forall {cs: compspecs} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc} {A: TypeTree} {Pre Post}
   {witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred} {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
  Espec
             (Post2: assert)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpost: B -> list mpred)
   (RETrueY: retty = Tvoid)
   (POST1: Post nil witness = (∃ vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (POST2: Post2 = ∃ vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof. intros. rewrite call_setup2_nil_equiv in SETUP. eapply semax_call_id00_wow; eassumption. Qed.*)

Lemma semax_call_id1_wow:
 forall {E} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc} {A: TypeTree} {Ef} {Pre Post}
   {witness}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred} {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Ef Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
   ret (Post2: assert)  (Qnew: list localdef)
    (B: Type) (Ppost: B -> list Prop) (F: B -> val) (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: check_retty retty)
   (POST1: assert_of (Post witness) ⊣⊢ ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (H0: Post2 ⊣⊢ ∃ vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall (Some ret) a bl)
    (normal_ret_assert Post2).
Proof.
  intros.
  destruct SETUP as [[PTREE [Hsub [SPEC [ATY [TC0 [TC1 MSUBST ]]]]]]
                       [HR' [HE [PRE1 [PTREE' [CHECKTEMP [CHECKG FRAME]]]]]]].
  apply SPEC. clear SPEC.
  eapply semax_pre_setup2; try eassumption.
  remember (tc_expr Delta a ∧ tc_exprlist Delta argsig bl) as TChecks.
  apply semax_extract_prop; intros.
  apply semax_extract_prop; intros.
  eapply semax_mask_mono; first done.
  eapply semax_pre_post', (semax_call1 Delta fs A Ef Pre Post
              witness ret argsig retty cc a bl P Q Frame Hsub);
    [ |
    | assumption
    | clear - OKretty; destruct retty; inv OKretty; apply I
    | hnf; clear - TYret; unfold typeof_temp in TYret;
      destruct ((temp_types Delta) !! ret); inv TYret; auto
    ].
  * subst TChecks. rewrite -semax_call_aux55 //.
    iIntros "(? & H)"; iSplit; auto; iSplit.
    { iDestruct "H" as "((_ & $ & _) & _)". }
    iSplit.
    { iDestruct "H" as "((_ & _ & $) & _)". }
    rewrite bi.and_elim_l comm //.
  * subst.
    clear  TC1 PRE1 PPRE.

    rewrite H0.
    go_lowerx.
    eapply monPred_in_equiv in POST1.
    simpl in POST1.
    rewrite POST1; clear POST1.
    unfold ifvoid.
    unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift. monPred.unseal.
    unfold_lift. normalize.
    Exists x.
    rewrite fold_right_and_app_low.
    rewrite fold_right_sepcon_app.
    normalize.
Qed.

(*Lemma semax_call_id1_wow_nil:
 forall {cs: compspecs} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc} {A: TypeTree} {Pre Post}
   {witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred} {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
   ret (Post2: assert)  (Qnew: list localdef)
    (B: Type) (Ppost: B -> list Prop) (F: B -> val) (Rpost: B -> list mpred) Espec
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: check_retty retty)
   (POST1: Post nil witness = ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (H0: Post2 = ∃ vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall (Some ret) a bl)
    (normal_ret_assert Post2).
Proof. intros. rewrite call_setup2_nil_equiv in SETUP. eapply semax_call_id1_wow; eassumption. Qed.*)

(* up *)
Global Instance subst_proper `{Equiv A} : Proper (eq ==> eq ==> pointwise_relation _ equiv ==> eq ==> equiv) (@subst A).
Proof.
  intros ?? -> ?? -> ????? ->.
  rewrite /subst //.
Qed.

Global Instance assert_of_proper : Proper (pointwise_relation _ equiv ==> equiv) (@assert_of Σ).
Proof.
  intros ???.
  apply bi.equiv_entails_2; split => rho; simpl; rewrite H //.
Qed.

Lemma semax_call_id1_x_wow:
 forall {E} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty' cc} {A: TypeTree} {Ef} {Pre Post}
   {witness}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred} {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty' cc A Ef Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
   retty ret ret'
             (Post2: assert)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) !! ret' = Some retty')
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true)
   (NEret: ret <> ret')
   (POST1: assert_of (Post witness) ⊣⊢ ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (HPOST2: Post2 ⊣⊢ ∃ vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
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
  + instantiate (1 := (PROPx (P ++ Ppost vret)
      (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
    iIntros "(#? & H) !>"; iSplit; [|iSplit].
    - rewrite /tc_expr /typecheck_expr.
      rewrite RETinit.
      replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
        with true
        by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; unfold is_neutral_cast; rewrite ?eqb_type_refl; reflexivity).
      rewrite denote_tc_assert_andp.
      iSplit; last by iApply (neutral_isCastResultType with "H").
      iApply PQR_denote_tc_initialized; eauto.
    - unfold tc_temp_id, typecheck_temp_id.
      unfold typeof_temp in TYret.
      destruct ((temp_types Delta) !! ret); inversion TYret; clear TYret; try subst t.
      rewrite !denote_tc_assert_andp /=.
      rewrite denote_tc_assert_bool.
      assert (is_neutral_cast (implicit_deref retty) retty = true).
      {
        destruct retty as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; try reflexivity;
        destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction;
        try solve [inv NEUTRAL].
        unfold implicit_deref, is_neutral_cast. rewrite eqb_type_refl; reflexivity.
      }
      iSplit; first done.
      iApply (neutral_isCastResultType with "H"); auto.
    - rewrite <- !insert_local.
      iDestruct "H" as "(? & H)"; iSplit; first done.
      subst Qnew; by iApply derives_remove_localdef_PQR.
  + intros.
    rewrite HPOST2.
    Exists vret.
    iIntros "(#? & % & #? & H)".
    iAssert (local (subst ret (`old) (locald_denote (temp ret' (F vret)))) ∧
      assert_of (subst ret (`old) (PROPx (P ++ Ppost vret)
                 (LOCALx (Qnew) (SEPx (Rpost vret ++ Frame)))))) with "[-]" as "H".
    { rewrite !subst_PROP_LOCAL_SEP; simpl.
      iDestruct "H" as "($ & #H & $)".
      autorewrite with subst.
      rewrite !local_lift2_and.
      iDestruct "H" as "(($ & $) & $)". }
    rewrite -insert_local.
    iSplit; [|subst Qnew; rewrite subst_remove_localdef_PQR bi.and_elim_r //].
    iDestruct "H" as "(? & _)".
    iStopProof.
    split => rho; monPred.unseal; rewrite monPred_at_intuitionistically.
    rewrite /= /lift1; unfold_lift.
    iIntros "((% & %) & %)"; iPureIntro.
    unfold subst in *.
    destruct H1; split; auto.
    rewrite eval_id_other // in H0, H1.
    assert (tc_val retty' (eval_id ret' rho))
      by (eapply tc_eval'_id_i; try eassumption; congruence).
    assert (H7 := expr2.neutral_cast_lemma); unfold eval_cast in H7.
    rewrite -> H7 in H0 by auto; congruence.
Qed.

(*Lemma semax_call_id1_x_wow_nil:
 forall {cs: compspecs} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty' cc} {A: TypeTree} {Pre Post}
   {witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred}
   {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty' cc A Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
   retty  Espec ret ret'
             (Post2: assert)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) !! ret' = Some retty')
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true)
   (NEret: ret <> ret')
   (POST1: Post nil witness = ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (H0: Post2 = ∃ vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
   (Ssequence (Scall (Some ret') a bl)
      (Sset ret (Ecast (Etempvar ret' retty') retty)))
    (normal_ret_assert Post2).
Proof. intros. rewrite call_setup2_nil_equiv in SETUP. eapply semax_call_id1_x_wow; eassumption. Qed.*)

Lemma semax_call_id1_y_wow:
 forall {E} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty' cc} {A: TypeTree} {Ef} {Pre: dtfr (ArgsTT A)} {Post: dtfr (AssertTT A)}
   {witness}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred}
   {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty' cc A Ef Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
    ret ret' (retty: type)
             (Post2: assert)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) !! ret' = Some retty')
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true)
   (NEret: ret <> ret')
   (POST1: assert_of (Post witness) ⊣⊢ ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (HPOST2: Post2 ⊣⊢ ∃ vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
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
  + instantiate (1 := (PROPx (P ++ Ppost vret)
      (LOCALx (temp ret' (F vret) :: Qnew) (SEPx (Rpost vret ++ Frame))))).
    iIntros "(#? & H) !>"; iSplit; [|iSplit].
    - rewrite /tc_expr /typecheck_expr.
      rewrite RETinit.
      replace ((is_neutral_cast retty' retty' || same_base_type retty' retty')%bool)
        with true
        by (clear- OKretty'; destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; unfold is_neutral_cast; rewrite ?eqb_type_refl; reflexivity).
      iApply PQR_denote_tc_initialized; eauto.
    - unfold tc_temp_id, typecheck_temp_id.
      unfold typeof_temp in TYret.
      destruct ((temp_types Delta) !! ret); inversion TYret; clear TYret; try subst t.
      rewrite !denote_tc_assert_andp /=.
      rewrite denote_tc_assert_bool.
      assert (is_neutral_cast (implicit_deref retty') retty = true).
      {
        replace (implicit_deref retty') with retty'
          by (destruct retty' as [ | [ | | |] [| ]| [|] | [ | ] |  | | | | ]; try contradiction; reflexivity).
        auto.
      }
      iSplit; first done.
      iApply (neutral_isCastResultType with "H"); auto.
    - rewrite <- !insert_local.
      iDestruct "H" as "(? & H)"; iSplit; first done.
      subst Qnew; by iApply derives_remove_localdef_PQR.
  + intros. rewrite HPOST2.
    Exists vret.
    iIntros "(#? & % & #? & H)".
    iAssert (local (subst ret (`old) (locald_denote (temp ret' (F vret)))) ∧
      assert_of (subst ret (`old) (PROPx (P ++ Ppost vret)
                 (LOCALx (Qnew) (SEPx (Rpost vret ++ Frame)))))) with "[-]" as "H".
    { rewrite !subst_PROP_LOCAL_SEP; simpl.
      iDestruct "H" as "($ & #H & $)".
      autorewrite with subst.
      rewrite !local_lift2_and.
      iDestruct "H" as "(($ & $) & $)". }
    rewrite -insert_local.
    iSplit; [|subst Qnew; rewrite subst_remove_localdef_PQR bi.and_elim_r //].
    iDestruct "H" as "(? & _)".
    iStopProof.
    split => rho; monPred.unseal; rewrite monPred_at_intuitionistically.
    rewrite /= /lift1; unfold_lift.
    iIntros "((% & %) & %)"; iPureIntro.
    unfold subst in *.
    destruct H1; split; auto.
    rewrite eval_id_other // in H0, H1.
    congruence.
Qed.

(*Lemma semax_call_id1_y_wow_nil:
 forall {cs: compspecs} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty' cc} {A: TypeTree} {Pre Post}
   {witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred}
   {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty' cc A Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
    Espec ret ret' (retty: type)
             (Post2: assert)
             (Qnew: list localdef)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (TYret: typeof_temp Delta ret = Some retty)
   (RETinit: (temp_types Delta) !! ret' = Some retty')
   (OKretty: check_retty retty)
   (OKretty': check_retty retty')
   (NEUTRAL: is_neutral_cast retty' retty = true)
   (NEret: ret <> ret')
   (POST1: Post nil witness = ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (H0: Post2 = ∃ vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
   (Ssequence (Scall (Some ret') a bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert Post2).
Proof. intros. rewrite call_setup2_nil_equiv in SETUP. eapply semax_call_id1_y_wow; eassumption. Qed.*)

Lemma semax_call_id01_wow:
 forall {E} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc} {A: TypeTree} {Ef} {Pre Post}
   {witness}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred} {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2 E Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Ef Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
             (Post2: assert)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (_: check_retty retty)
         (* this hypothesis is not needed for soundness, just for selectivity *)
   (POST1: assert_of (Post witness) ⊣⊢ ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (POST2: Post2 ⊣⊢ ∃ vret:B, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof.
  intros.
  destruct SETUP as [[PTREE [Hsub [SPEC [ATY [TC0 [TC1 MSUBST ]]]]]]
                       [HR' [HE [PRE1 [PTREE' [CHECKTEMP [CHECKG FRAME]]]]]]].
  apply SPEC. clear SPEC.
  eapply semax_pre_setup2; try eassumption.
  remember (tc_expr Delta a ∧ tc_exprlist Delta argsig bl) as TChecks.
  apply semax_extract_prop; intros.
  apply semax_extract_prop; intros.
  eapply semax_mask_mono; first done.
  eapply semax_pre_post', semax_call0 with (fs:=fs)(cc:=cc)(A:= A)(x:=witness) (P:=P)(Q:=Q)(R := Frame);
     try eassumption.
  * subst TChecks. rewrite -semax_call_aux55 //.
    iIntros "(? & H)"; iSplit; auto; iSplit.
    { iDestruct "H" as "((_ & $ & _) & _)". }
    iSplit.
    { iDestruct "H" as "((_ & _ & $) & _)". }
    rewrite bi.and_elim_l comm //.
  * subst.
    clear CHECKTEMP TC1 PRE1 PPRE.
    match goal with |- context [ifvoid retty ?A ?B] =>
          replace (ifvoid retty A B) with B
          by (destruct retty; try contradiction; auto)
    end.
    go_lowerx; normalize.
    eapply monPred_in_equiv in POST1.
    simpl in POST1.
    rewrite POST1 POST2; clear POST1 POST2.
    unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift. monPred.unseal.
    Intros a0; Exists a0.
    rewrite fold_right_and_app_low.
    rewrite fold_right_sepcon_app.
    normalize.
Qed.

(*Lemma semax_call_id01_wow_nil:
 forall {cs: compspecs} {Qtemp Qvar GV a Delta P Q R R'
   fs argsig retty cc} {A: TypeTree} {Pre Post}
   {witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred}
   {Frame: list mpred}
   {bl: list expr}
   {Ppre: list Prop} {Rpre: list mpred}
   {GV' gv args}
   {vl : list val}
   (SETUP: call_setup2_nil cs Qtemp Qvar GV a Delta P Q R R' fs argsig retty cc A Pre Post bl vl
      witness Frame Ppre Rpre GV' gv args)
   Espec
             (Post2: assert)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (_: check_retty retty)
         (* this hypothesis is not needed for soundness, just for selectivity *)
   (POST1: Post nil witness = ∃ vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (POST2: Post2 = ∃ vret:B, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   semax E Delta (PROPx P (LOCALx Q (SEPx R')))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof. intros. rewrite call_setup2_nil_equiv in SETUP. eapply semax_call_id01_wow; eassumption. Qed.*)

Lemma match_funcptr'_funcptr:
 forall fs v B,
  func_ptr fs v ∗ B ⊢ <absorb> func_ptr fs v.
Proof.
  intros; iIntros "($ & ?)".
Qed.

Lemma nomatch_funcptr'_funcptr:
  forall fs v A B,
   (B ⊢ <absorb> func_ptr fs v) ->
  A ∗ B ⊢ <absorb> func_ptr fs v.
Proof.
  intros ???? ->; iIntros "(? & $)".
Qed.

Definition eq_no_post (x v: val) : Prop := x=v.
(* The purpose of eq_no_post is to "mark" the proposition
  in forward_call_idxxx lemmas so that the after-the-call
  can treat this one specially *)

Lemma no_post_exists:
 forall v P Q R,
   PROPx(Σ := Σ) P (LOCALx (temp ret_temp v :: Q) (SEPx R)) ⊣⊢
   ∃ x:val, PROPx (eq_no_post x v :: P) (LOCALx (temp ret_temp x :: Q) (SEPx R)).
Proof.
  intros. unfold eq_no_post.
  apply bi.equiv_entails_2.
  - rewrite -(bi.exist_intro v).
    apply bi.and_mono; last done.
    apply bi.pure_mono; simpl; auto.
  - apply bi.exist_elim; intros.
    rewrite /PROPx /=.
    split => rho; monPred.unseal.
    normalize.
Qed.

Lemma no_post_exists0:
 forall P Q R,
   PROPx(Σ := Σ) P (LOCALx Q (SEPx R)) ⊣⊢
   ∃ x:unit, PROPx ((fun _ => P) x) (LOCALx Q (SEPx ((fun _ => R) x))).
Proof.
  intros.
  apply bi.equiv_entails_2.
  - rewrite -(bi.exist_intro tt) //.
  - apply bi.exist_elim; intros; done.
Qed.

Import ListNotations.

Lemma void_ret : ifvoid tvoid (assert_of(Σ := Σ) (` (monPred_at (PROP ( )  LOCAL ()  SEP ())) (make_args [] [])))
  (∃ v : val, assert_of (` (monPred_at (PROP ( )  LOCAL ()  SEP ())) (make_args [ret_temp] [v]))) ⊣⊢ emp.
Proof.
  split => rho; unfold_lift; simpl.
  rewrite /PROPx /LOCALx /SEPx /=; monPred.unseal.
  iSplit; auto.
Qed.

End mpred.

Ltac match_funcptr'_funcptr :=
 first [simple apply match_funcptr'_funcptr
        | simple apply nomatch_funcptr'_funcptr; match_funcptr'_funcptr].

Ltac prove_func_ptr :=
    match goal with |- fold_right_sepcon ?A ⊢ <absorb> func_ptr ?F ?V =>
       match A with context [func_ptr ?G V] =>
         unify F G
       end
     end;
   unfold fold_right_sepcon;
   match_funcptr'_funcptr.
