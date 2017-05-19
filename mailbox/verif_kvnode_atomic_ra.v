Require Import veric.rmaps.
Require Import progs.ghost.
Require Import mailbox.general_atomics.
Require Import mailbox.acq_rel_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.kvnode_atomic_ra.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition load_acq_spec := DECLARE _load_acq load_acq_spec.
Definition store_rel_spec := DECLARE _store_rel store_rel_spec.

Definition tnode := Tstruct _node noattr.

Definition has_size : {x : Z | x = 8}.
Proof.
  eexists; eauto.
Qed.

Definition size := proj1_sig has_size.
Lemma size_def : size = 8.
Proof.
  apply (proj2_sig has_size).
Qed.

(* Store a map from known version numbers to values. *)
Instance version_PCM : PCM (Z -> option Z) := { join a b c :=
  forall v1 v2, c v1 = Some v2 <-> a v1 = Some v2 \/ b v1 = Some v2 }.
Proof.
  - intros.
    rewrite Hjoin; tauto.
  - intros.
    exists (fun v => match b v with Some v' => Some v' | None => d v end).
    assert (forall v v1 v2, b v = Some v1 -> d v = Some v2 -> v1 = v2) as Hbd.
    { intros ??? Hb Hd.
      specialize (Hjoin1 v v1).
      destruct Hjoin1 as (_ & Hc); lapply Hc; auto; intro Hc'.
      generalize (Hjoin2 v v1); intros (_ & He); lapply He; auto; intro He1.
      specialize (Hjoin2 v v2); destruct Hjoin2 as (_ & Hjoin2); lapply Hjoin2; auto; intro He2.
      rewrite He1 in He2; inv He2; auto. }
    split; intros; specialize (Hjoin1 v1 v2); specialize (Hjoin2 v1 v2).
    + destruct (b v1) eqn: Hb; split; auto; intros [|]; auto; try discriminate.
      exploit Hbd; eauto.
    + rewrite Hjoin2, Hjoin1.
      destruct (b v1) eqn: Hb; split; auto; intros [|]; auto.
      * specialize (Hbd _ _ _ Hb H); subst; auto.
      * destruct H; auto; discriminate.
Defined.

Definition log_incl (a b : Z -> option Z) := forall v1 v2, a v1 = Some v2 -> b v1 = Some v2.

Instance version_order : PCM_order log_incl.
Proof.
  constructor.
  - repeat intro; auto.
  - repeat intro; auto.
  - split; repeat intro; specialize (H v1 v2); rewrite H; auto.
  - split; auto; intros [|]; auto.
Defined.

Definition log_latest s (v1 v2 : Z) := s v1 = Some v2 /\ forall v', v1 < v' -> s v' = None.

Definition version_T (s v : Z) := !!(v = s) && emp.

Definition data_T version g g' s (v : Z) := EX ver : Z, !!(Z.even ver = true /\ log_latest s ver v) &&
  protocol_R version g g' (ver - 1) Z.le version_T.

Definition node_entry v vs version locs g g' lg lg' i := EX log : _, !!(log_latest log v (Znth i vs 0)) &&
  protocol_R (Znth i locs Vundef) (Znth i lg Vundef) (Znth i lg' Vundef) log log_incl (data_T version g g').

Definition node_state v vs version locs g g' lg lg' := !!(Z.even v = true) &&
  protocol_R version g g' v Z.le version_T *
  fold_right sepcon emp (map (node_entry v vs version locs g g' lg lg') (upto (Z.to_nat size))).

Program Definition write_spec := DECLARE _write atomic_spec
  (ConstType (val * val * share * share * val * list val * list Z * val * val * list val * list val * Z * list Z))
  (0, []) [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, lg', v0, vs0) => temp _n n;
   fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, lg', v0, vs0) => temp _in input]
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, lg', v0, vs0) => !!(readable_share sh /\
     readable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\
     Forall repable_signed vals /\ Z.even v0 = true /\ Zlength vs0 = size) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   protocol_W version g g' v0 Z.le version_T * fold_right sepcon emp (map (fun i =>
     EX log : _, !!(log_latest log v0 (Znth i vs0 0)) &&
       protocol_W (Znth i locs Vundef) (Znth i lg Vundef) (Znth i lg' Vundef) log log_incl (data_T version g g'))
     (upto (Z.to_nat size))))
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, lg', v0, vs0) '(v, vs) =>
   node_state v vs version locs g g' lg lg')
  tt []
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, lg', v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   protocol_W version g g' (v0 + 2) Z.le version_T * fold_right sepcon emp (map (fun i =>
     EX log : _, !!(log_latest log (v0 + 2) (Znth i vals 0)) &&
       protocol_W (Znth i locs Vundef) (Znth i lg Vundef) (Znth i lg' Vundef) log log_incl (data_T version g g'))
     (upto (Z.to_nat size))))
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, lg', v0, vs0) '(v, vs) _ =>
   (* !!(v = v0 /\ vs = vs0) && *) node_state (v0 + 2) vals version locs g g' lg lg')
  _ _ _ _ _ _.
(* We can prove the stronger postcondition, but the writer doesn't really care what it overwrites. *)
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.

(* The state we've read by the end may be older than the state in the invariant, so we need a history to get
   anything useful out of the read. *)
(* On the one hand, it seems like we should be able to know we've gotten the most recent version. On the other
   hand, that leads directly to SC issues if extended to multiple locations. *)
Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * share * val * list val * val * val * list val * list val * Z * list Z))
  (0, []) [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, shi, version, locs, g, g', lg, lg', v0, vs0) => temp _n n;
   fun _ '(n, out, sh, shi, version, locs, g, g', lg, lg', v0, vs0) => temp _out out]
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, lg', v0, vs0) => !!(readable_share sh /\
     writable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\ Zlength vs0 = size) &&
   data_at sh tnode (version, locs) n * data_at_ shi (tarray tint size) out *
   node_state v0 vs0 version locs g g' lg lg')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, lg', v0, vs0) '(v, vs) =>
   node_state v vs version locs g g' lg lg')
  (0, []) []
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, lg', v0, vs0) '(v, vs) '(v', vals) =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) out *
   node_state v' vals version locs g g' lg lg')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, lg', v0, vs0) '(v, vs) '(v', vals) =>
   !!(Z.even v' = true /\ v' <= v) && node_state v vs version locs g g' lg lg')
  _ _ _ _ _ _.
(* We can prove the stronger postcondition, but the writer doesn't really care what it overwrites. *)
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [load_acq_spec; store_rel_spec; read_spec; write_spec]).

Lemma land_1 : forall i, Z.land i 1 = i mod 2.
Proof.
  intros; apply Z.land_ones with (n := 1); omega.
Qed.

Existing Instance max_PCM.

(* up *)
Lemma Znth_repeat' : forall {A} (d x : A) n i, 0 <= i < Z.of_nat n -> Znth i (repeat x n) d = x.
Proof.
  induction n; intros; [simpl in *; omega|].
  rewrite Nat2Z.inj_succ in H; simpl.
  destruct (eq_dec i 0).
  - subst; apply Znth_0_cons.
  - rewrite Znth_pos_cons by omega; apply IHn; omega.
Qed.

(* automation for dependent funspecs *)
Definition call_setup2'
  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty cc ts (A: rmaps.TypeTree)  Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
  (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  (Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc) :=
 call_setup1 cs Qtemp Qvar a Delta P Q R argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals /\
  Pre ts witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) /\
  local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil) /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) /\
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var) /\
  fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame.

Lemma call_setup2'_i:
 forall  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty cc ts (A: rmaps.TypeTree) Pre Post NEPre NEPost
  (bl: list expr) (vl : list val)
  (Qactuals : PTree.t _)
  (SETUP1: call_setup1 cs Qtemp Qvar a Delta P Q R argsig retty cc A Pre Post NEPre NEPost bl vl Qactuals)
  (witness': functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred)
  (Frame: list mpred)
  (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
  (Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc),
  Pre ts witness' = PROPx Ppre (LOCALx Qpre (SEPx Rpre)) ->
  local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var)  ->
  fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame ->
  call_setup2' cs Qtemp Qvar a Delta P Q R argsig retty cc ts A Pre Post NEPre NEPost bl vl Qactuals
      witness' Frame Ppre Qpre Rpre Qpre_temp Qpre_var.
Proof.
 intros. split. auto. repeat split; auto.
Qed.

Ltac check_witness_type' ts A witness :=
  (unify A (rmaps.ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             elimtype False)
 ||
 let TA := constr:(functors.MixVariantFunctor._functor
     (rmaps.dependent_type_functor_rec ts A) mpred) in
  let TA' := eval cbv 
     [functors.MixVariantFunctor._functor
      functors.MixVariantFunctorGenerator.fpair
      functors.MixVariantFunctorGenerator.fconst
      functors.MixVariantFunctorGenerator.fidentity
      rmaps.dependent_type_functor_rec
      functors.GeneralFunctorGenerator.CovariantBiFunctor_MixVariantFunctor_compose
      functors.CovariantFunctorGenerator.fconst
      functors.CovariantFunctorGenerator.fidentity
      functors.CovariantBiFunctor._functor
      functors.CovariantBiFunctorGenerator.Fpair
      functors.GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor
      functors.CovariantFunctor._functor
      functors.MixVariantFunctor.fmap
      ] in TA
 in let TA'' := eval simpl in TA'
  in match type of witness with ?T => 
       unify T TA''
      + (fail "Type of witness does not match type required by funspec WITH clause.
Witness value: " witness "
Witness type: " T "
Funspec type: " TA'')
     end.

Ltac prove_call_setup' ts witness :=
 prove_call_setup1;
 [ .. | 
 match goal with |- call_setup1 _ _ _ _ _ _ _ _ _ _ _ ?A _ _ _ _ _ _ _ -> _ =>
      check_witness_type' ts A witness
 end;
 let H := fresh in
 intro H;
 let Frame := fresh "Frame" in evar (Frame: list mpred);
 exploit (call_setup2'_i _ _ _ _ _ _ _ _ _ _ _ ts _ _ _ _ _ _ _ _ H witness Frame); clear H;
 simpl functors.MixVariantFunctor._functor;
 [ reflexivity
 | check_prove_local2ptree
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel_for_forward_call
 | 
 ]].

Lemma semax_call_aux55:
 forall (cs: compspecs) (Qtemp: PTree.t val) (Qvar: PTree.t vardesc) (a: expr)
     Delta P Q R argsig retty cc ts A Pre Post NEPre NEPost 
    witness Frame bl Ppre Qpre Rpre Qactuals Qpre_temp Qpre_var vl
 (PTREE : local2ptree Q = (Qtemp, Qvar, nil, nil))
 (TC0 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta a)
 (TC1 : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
             |-- tc_exprlist Delta (argtypes argsig) bl)
 (MSUBST : force_list (map (msubst_eval_expr Qtemp Qvar)
              (explicit_cast_exprlist (argtypes argsig) bl)) = Some vl)
 (PTREE'' : pTree_from_elements (combine (var_names argsig) vl) = Qactuals)
 (PRE1 : Pre ts witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
 (PTREE' : local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil)) 
 (CHECKTEMP : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
            |-- !! Forall (check_one_temp_spec Qactuals)
                     (PTree.elements Qpre_temp))
 (CHECKVAR : ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
 (FRAME : fold_right_sepcon R
           |-- fold_right_sepcon Rpre * fold_right_sepcon Frame)
 (PPRE : fold_right_and True Ppre),
ENTAIL Delta,
(EX v : val,
 lift0 (func_ptr (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) v) &&
 local (` (eq v) (eval_expr a))) && PROPx P (LOCALx Q (SEPx R))
|-- tc_expr Delta a && tc_exprlist Delta (argtypes argsig) bl &&
    (` (Pre ts witness)
       (make_args' (argsig, retty) (eval_exprlist (argtypes argsig) bl)) *
     ` (func_ptr' (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost))
       (eval_expr a) * PROPx P (LOCALx Q (SEPx Frame))).
Proof.
intros.
rewrite !exp_andp1. Intros v.
repeat apply andp_right; auto.
eapply derives_trans; [apply andp_derives; [apply derives_refl | apply andp_left2; apply derives_refl ] | auto].
eapply derives_trans; [apply andp_derives; [apply derives_refl | apply andp_left2; apply derives_refl ] | auto].
(*
normalize.
assert (H0 := @msubst_eval_expr_eq cs P Qtemp Qvar nil R a v).
assert (H1 := local2ptree_soundness P Q R Qtemp Qvar nil nil PTREE).
simpl app in H1. rewrite <- H1 in H0. apply H0 in EVAL. 
clear H0 H1.
*)
rewrite PRE1.
match goal with |- _ |-- ?A * ?B * ?C => pull_right B end.
rewrite sepcon_comm.
rewrite func_ptr'_func_ptr_lifted.
apply ENTAIL_trans with
 (`(func_ptr (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost)) (eval_expr a) &&
      PROPx P (LOCALx Q (SEPx R))).
apply andp_left2.
apply andp_right; [  | apply andp_left2; auto].
apply andp_left1.
intro rho; unfold_lift; unfold local, lift0, lift1; simpl. normalize.
apply andp_right.
apply andp_left2; apply andp_left1; auto.
eapply derives_trans;[ apply andp_derives; [apply derives_refl | apply andp_left2; apply derives_refl] |].
 match goal with |- ?D && PROPx ?A ?B |-- ?C =>
  apply derives_trans with (D && PROPx ((length (argtypes argsig) = length bl) :: A) B);
    [ rewrite <- insert_prop | ]
 end.
 apply andp_right; [apply andp_left1; auto | ].
 apply andp_right; [| apply andp_left2; auto].
 eapply derives_trans; [apply TC1 | ].
 clear. go_lowerx.
 unfold tc_exprlist.
 revert bl; induction (argtypes argsig); destruct bl;
   simpl; try apply @FF_left.
 apply prop_right; auto.
 repeat rewrite denote_tc_assert_andp. apply andp_left2.
 eapply derives_trans; [ apply IHl | ]. normalize.
apply derives_extract_PROP; intro LEN.
subst Qactuals. 
clear - PTREE LEN PTREE' MSUBST CHECKVAR FRAME PPRE CHECKTEMP.
 progress (autorewrite with norm1 norm2); normalize.
 eapply derives_trans.
 apply andp_right. apply andp_right. apply CHECKVAR. apply CHECKTEMP. apply derives_refl.
 rewrite andp_assoc. apply derives_extract_prop; intro CVAR.
 apply derives_extract_prop; intro CTEMP.
 clear CHECKTEMP CHECKVAR.
rewrite PROP_combine.
rewrite (andp_comm (local (fold_right _ _ _))).
apply andp_right.
+
apply andp_right.
apply andp_left2.
apply andp_left1.
rewrite fold_right_and_app_low.
apply prop_derives; intros; split; auto.
 clear - PPRE.
 revert PPRE; induction Ppre; simpl; intuition.
apply andp_left2.
apply andp_left2.
apply andp_derives.
apply derives_refl.
intro rho; unfold SEPx.
 rewrite fold_right_sepcon_app.
 assumption.
+
 apply (local2ptree_soundness P _ R) in PTREE.
 simpl app in PTREE.
 apply msubst_eval_exprlist_eq with (P:=P)(R:=R)(Q:=nil) in MSUBST.
 rewrite PTREE.
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
Qed.

Lemma semax_call_id00_wow:
 forall  
  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty cc ts (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc)
   (vl : list val)
   (SETUP: call_setup2' cs Qtemp Qvar a Delta P Q R argsig retty cc ts A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var)
  Espec 
             (Post2: environ -> mpred)
             (B: Type)
             (Ppost: B -> list Prop)
             (Rpost: B -> list mpred)
   (RETTY: retty = Tvoid)
   (POST1: Post ts witness = (EX vret:B, PROPx (Ppost vret) (LOCALx nil (SEPx (Rpost vret)))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret ) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof.
intros.
destruct SETUP as [[PTREE [SPEC [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]] 
                            [PRE1 [PTREE' [CHECKTEMP [CHECKVAR FRAME]]]]].
apply SPEC. clear SPEC.
eapply semax_pre_post; [ | |
   apply (@semax_call0 Espec cs Delta A Pre Post NEPre NEPost 
              ts witness argsig retty cc a bl P Q Frame)].
*
eapply semax_call_aux55; eauto.
*
 subst.
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
*
assumption.
Qed.

Lemma semax_call_id1_wow:
 forall  
  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty cc ts (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc)
   (vl : list val)
   (SETUP: call_setup2' cs Qtemp Qvar a Delta P Q R argsig retty cc ts A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var)
   ret (Post2: environ -> mpred)  (Qnew: list localdef)
    (B: Type) (Ppost: B -> list Prop) (F: B -> val) (Rpost: B -> list mpred) Espec
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: check_retty retty)
   (POST1: Post ts witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall (Some ret) a bl)
    (normal_ret_assert Post2).
Proof.
intros. 
destruct SETUP as [[PTREE [SPEC [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]] 
                            [PRE1 [PTREE' [CHECKTEMP [CHECKVAR FRAME]]]]].
apply SPEC. clear SPEC.
eapply semax_pre_post; [ | |
   apply (@semax_call1 Espec cs Delta A Pre Post NEPre NEPost 
              ts witness ret argsig retty cc a bl P Q Frame)];
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
 unfold normal_ret_assert. normalize.
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
 rewrite !fold_right_and_app_low in H2. destruct H2; split; auto.
Qed.

Lemma semax_call_id1_x_wow:
 forall  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty' cc ts (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc)
   (vl : list val)
   (SETUP: call_setup2' cs Qtemp Qvar a Delta P Q R argsig retty' cc ts A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var)
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
   (POST1: Post ts witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
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
 subst Qnew; clear - H3. rename H3 into H.
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
 forall  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty' cc ts (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc)
   (vl : list val)
   (SETUP: call_setup2' cs Qtemp Qvar a Delta P Q R argsig retty' cc ts A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var)
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
   (POST1: Post ts witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (DELETE: remove_localdef_temp ret Q = Qnew)
   (DELETE' : remove_localdef_temp ret' Q = Q)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret)
                   (LOCALx (temp ret (F vret) :: Qnew)
                    (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
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
 subst Qnew; clear - H3. rename H3 into H.
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
  (cs: compspecs) Qtemp Qvar a Delta P Q R  
   argsig retty cc ts (A: rmaps.TypeTree)  Pre Post NEPre NEPost
   (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred) 
   (Frame: list mpred)
   (bl: list expr)
   (Ppre: list Prop) (Qpre : list localdef) (Rpre: list mpred)
   (Qactuals Qpre_temp : PTree.t _) (Qpre_var: PTree.t vardesc)
   (vl : list val)
   (SETUP: call_setup2' cs Qtemp Qvar a Delta P Q R argsig retty cc ts A Pre Post NEPre NEPost bl vl Qactuals
      witness Frame Ppre Qpre Rpre Qpre_temp Qpre_var)
   Espec
             (Post2: environ -> mpred)
             (B: Type)
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpost: B -> list mpred)
   (_: check_retty retty)
         (* this hypothesis is not needed for soundness, just for selectivity *)
   (POST1: Post ts witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil)
                              (SEPx (Rpost vret))))
   (POST2: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx Q
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre),
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Scall None a bl)
    (normal_ret_assert Post2).
Proof.
intros.
destruct SETUP as [[PTREE [SPEC [ATY [TC0 [TC1 [MSUBST PTREE'']]]]]] 
                            [PRE1 [PTREE' [CHECKTEMP [CHECKVAR FRAME]]]]].
apply SPEC. clear SPEC.
eapply semax_pre_post;
   [ |
   | apply semax_call0 with (A:= A) (ts := ts)(x:=witness) (P:=P)(Q:=Q)(NEPre :=NEPre) (NEPost := NEPost)(R := Frame)
   ];
   try eassumption.
*
eapply semax_call_aux55; eauto.
*
 subst.
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

Ltac  forward_call_id1_wow' := 
let H := fresh in intro H;
eapply (semax_call_id1_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H);
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [check_result_type
 |apply Logic.I
 | cbv beta iota zeta; unfold_post; extensionality rho;
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id1_x_wow' :=
let H := fresh in intro H;
eapply (semax_call_id1_x_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | cbv beta iota zeta; unfold_post; extensionality rho;
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].


Ltac forward_call_id1_y_wow' :=
let H := fresh in intro H;
eapply (semax_call_id1_y_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity
 | (clear; let H := fresh in intro H; inversion H)
 | cbv beta iota zeta; unfold_post; extensionality rho;
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id01_wow' :=
let H := fresh in intro H;
eapply (semax_call_id01_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ apply Coq.Init.Logic.I 
 | cbv beta iota zeta; unfold_post; extensionality rho;
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id00_wow'  :=
let H := fresh in intro H;
eapply (semax_call_id00_wow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); 
 clear H;
 lazymatch goal with Frame := _ : list mpred |- _ => try clear Frame end;
 [ check_result_type 
 | cbv beta iota zeta; unfold_post; extensionality rho;
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0;
    repeat rewrite exp_unfold;
    first [reflexivity | extensionality; simpl; reflexivity | give_EX_warning]
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac fwd_call'_dep ts witness :=
lazymatch goal with
| |- semax _ _ (Ssequence (Scall _ _ _) _) _ =>
  eapply semax_seq';
    [prove_call_setup' ts witness;
     clear_Delta_specs; clear_MORE_POST;
     [ .. | 
      lazymatch goal with
      | |- _ -> semax _ _ (Scall (Some _) _ _) _ =>
         forward_call_id1_wow
      | |- call_setup2' _ _ _ _ _ _ _ _ _ ?retty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> 
                semax _ _ (Scall None _ _) _ =>
        tryif (unify retty Tvoid)
        then forward_call_id00_wow'
        else forward_call_id01_wow'
     end]
   | after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Ecast (Etempvar ?ret'2 _) _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup' ts witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_x_wow' ]
         |  after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Etempvar ?ret'2 _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup' ts witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_y_wow' ]
         |  after_forward_call ]
| |- _ => rewrite <- seq_assoc; fwd_call'_dep ts witness
end.

Ltac fwd_call_dep ts witness :=
 try lazymatch goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat lazymatch goal with
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end;
lazymatch goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  lazymatch C with context [Scall _ _ _] =>
         fwd_call'_dep ts witness
    end
end.

Tactic Notation "forward_call_dep" constr(ts) constr(witness) := fwd_call_dep ts witness.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((((n, out), sh), shi), version), locs), g), g'), lg), lg'), v0), vs0); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  assert (0 <= size) by (rewrite size_def; computable).
  apply semax_pre with (P' := EX v : Z, EX vers : list Z,
    PROP (Forall (fun v' => Z.even v' = true /\ v' - 1 <= v) vers; Zlength vers = size)
    LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ Tsh (tarray tint size) out;
         protocol_R version g g' v (version_T lg); fold_right sepcon emp (map (fun i =>
           protocol_R (Znth i locs Vundef) (Znth i lg Vundef) (Znth i lg' Vundef) (Znth i vers 0) (data_T g))
             (upto (Z.to_nat size))))).
  { Exists v0 (repeat v0 (Z.to_nat size)); entailer!.
    { split; [apply Forall_repeat; split; auto; omega | rewrite Zlength_repeat, Z2Nat.id; auto]. }
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; rewrite Znth_repeat'; auto. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  Intros v vers.
  repeat forward.
  forward_call (version, g, g', v, version_T lg, fold_right sepcon emp (map (fun i =>
      protocol_R (Znth i locs Vundef) (Znth i lg Vundef) (Znth i lg' Vundef) (Znth i vers 0) (data_T g)) (upto (Z.to_nat size))),
    fun s v : Z => !!(if Z.even v then v = s else True) && fold_right sepcon emp (map (fun i =>
      protocol_R (Znth i locs Vundef) (Znth i lg Vundef) (Znth i lg' Vundef)
        (if Z.even v then s else Znth i vers 0) (data_T g)) (upto (Z.to_nat size)))).
  { split.
    intros; unfold version_T.
    apply derives_view_shift.
    Intros; destruct (Z.even v1) eqn: Heven; [|entailer!].
    apply andp_right.
    { entailer!.
      match goal with H : _ \/ _ |- _ => destruct H; auto; subst end.
      rewrite Z.even_add in Heven; replace (Z.even s') with true in Heven; discriminate. }
    setoid_rewrite (list_Znth_eq Vundef lg) at 2.
    setoid_rewrite (list_Znth_eq Vundef lg) at 4.
    replace (length lg) with (Z.to_nat size) by (symmetry; rewrite <- Zlength_length; auto).
    rewrite !map_map, <- !sepcon_map.
    erewrite map_ext_in; eauto; intros; simpl.
    unfold protocol_R.
    rewrite <- sepcon_assoc, (sepcon_comm (ghost_snap _ _)), !sepcon_assoc, !ghost_snap_join', !Z.max_r; auto.
    { omega. }
    { eapply Forall_Znth, Forall_impl; eauto; simpl.
      { rewrite In_upto, Z2Nat.id in * by auto; omega. }
      intros a0 (Heven' & ?).
      destruct (eq_dec a0 (v + 1)); try omega; subst.
      destruct (eq_dec v s'); try omega; subst.
      rewrite Z.even_add in Heven'; replace (Z.even s') with true in Heven'; discriminate. }
    { intros; apply prop_duplicable, sepcon_list_duplicable.
      rewrite Forall_map, Forall_forall; intros; simpl.
      apply protocol_R_duplicable. } }
  Intros x; destruct x as (v1', v1); simpl in *.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP (Z.even v1' = true) (LOCALx Q (SEPx R))) end.
  { eapply semax_pre; [|apply semax_continue].
    unfold POSTCONDITION, abbreviate, overridePost.
    destruct (eq_dec EK_continue EK_normal); [discriminate|].
    unfold loop1_ret_assert.
    go_lower.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1'); auto; try contradiction.
    Exists v1 vers; entailer!.
    eapply Forall_impl; [|eauto].
    intros ? []; split; auto; omega. }
  { forward.
    entailer!.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1'); auto; discriminate. }
  Intros.
  replace (Z.even v1') with true.
  match goal with H : Z.even _ = _ |- _ => rewrite H in *; subst end.
  forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i)
    LOCAL (temp _snap (vint v1); temp _ver version; temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n;
         data_at Tsh (tarray tint size) (map (fun x => vint x) vals ++ repeat Vundef (Z.to_nat (size - i))) out;
         EX vers' : list Z, !!(Zlength vers' = i /\ Forall (fun v => Z.even v = true /\ v1 <= v) vers') &&
           protocol_R version g g' (list_max v1 (map (fun x => x - 1) vers')) (version_T lg) *
           fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (Znth i lg Vundef)
             (Znth i lg' Vundef) (Znth i vers' 0) (data_T g)) (sublist 0 i (upto (Z.to_nat size))));
         fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (Znth i lg Vundef)
           (Znth i lg' Vundef) v1 (data_T g)) (sublist i size (upto (Z.to_nat size)))))).
  { Exists (@nil Z) (@nil Z).
    rewrite data_at__eq; unfold default_val; simpl data_at.
    rewrite repeat_list_repeat, Z.sub_0_r; entailer!.
    rewrite sublist_same by (auto; rewrite Zlength_upto, Z2Nat.id; auto); auto. }
  - Intros vers'.
    match goal with H : 0 <= i < _ |- _ => rewrite <- size_def in H end.
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    { rewrite <- size_def; apply prop_right; auto. }
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    forward_call (Znth i locs Vundef, Znth i lg Vundef, Znth i lg' Vundef, v1, data_T g,
      protocol_R version g g' (list_max v1 (map (fun x => x - 1) vers')) (version_T lg),
      fun s v : Z => !!(Z.even s = true) &&
        protocol_R version g g' (list_max v1 (map (fun x => x - 1) (vers' ++ [s]))) (version_T lg)).
    { split; [|intros; apply prop_duplicable, protocol_R_duplicable].
      intros; unfold data_T.
      apply derives_view_shift.
      Intros; apply andp_right.
      { apply prop_right; auto. }
      unfold protocol_R.
      rewrite <- sepcon_assoc, (sepcon_comm (ghost_snap _ _)), !sepcon_assoc, !ghost_snap_join'.
      rewrite map_app, list_max_app; simpl.
      rewrite Z.max_comm, !list_max_max.
      rewrite Z.max_assoc, Z.max_id; auto. }
    Intros y; destruct y as (d, v'); simpl in *.
    forward.
    go_lower; Exists (x ++ [d]) (vers' ++ [v']); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    rewrite <- size_def, upd_init, !map_app, <- app_assoc by (rewrite ?Zlength_map; omega); entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    rewrite sublist_split with (mid := Zlength x)(hi := Zlength x + 1) by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    erewrite sublist_len_1, Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    rewrite map_app, sepcon_app; simpl.
    rewrite !app_Znth2 by omega.
    replace (Zlength vers') with (Zlength x); rewrite Zminus_diag, !Znth_0_cons; simpl; cancel.
    apply sepcon_list_derives; rewrite !Zlength_map; auto.
    intros ? Hi; erewrite !Znth_map by auto.
    rewrite Zlength_sublist in Hi by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    rewrite !Znth_sublist, !Znth_upto by (rewrite ?Z2Nat.id; simpl; omega).
    rewrite !app_Znth1 by omega; auto.
  - Intros vals vers'; rewrite <- size_def in *.
    rewrite Zminus_diag, app_nil_r, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    forward_call (version, g, g', list_max v1 (map (fun x => x - 1) vers'), version_T lg, emp,
      fun s v : Z => !!(if Z.even v then v = s else True) && emp).
    { split; [|auto with dup].
      intros; unfold version_T.
      apply derives_view_shift; entailer!.
      match goal with H : _ \/ _ |- _ => destruct H; subst; [if_tac; auto|] end.
      rewrite Z.even_add; replace (Z.even s') with true; simpl; auto. }
    Intros x; destruct x as (v2', v2); simpl in *.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v2' <> v1) (LOCALx Q (SEPx R))) end.
    + subst.
      match goal with H : Z.even v1 = _ |- _ => rewrite H in *; subst end.
      forward.
      Exists v2 vals; unfold node_state; entailer!.
      erewrite map_ext_in; eauto; simpl; intros.
      replace (Znth a vers' 0) with v2; auto.
      rewrite In_upto, Z2Nat.id in * by auto.
      assert (0 <= a < Zlength vers') by omega.
      match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i := a)(d := 0) in H; auto;
        destruct H as (Heven & ?) end.
      destruct (list_max_spec v2 (map (fun x => x - 1) vers')) as (_ & Hle).
      rewrite Forall_map in Hle; apply Forall_Znth with (i := a)(d := 0) in Hle; auto.
      simpl in Hle.
      destruct (eq_dec (Znth a vers' 0) (v2 + 1)); try omega.
      rewrite e, Z.even_add in Heven.
      replace (Z.even v2) with true in Heven; discriminate.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; go_lower; Exists v2 vers'; entailer!.
      rewrite Forall_forall; intros ? Hin.
      split; [match goal with H : Forall _ vers' |- _ => rewrite Forall_forall in H; apply H; auto end|].
      destruct (list_max_spec v1 (map (fun x => x - 1) vers')) as (_ & Hle).
      rewrite Forall_map, Forall_forall in Hle; specialize (Hle _ Hin); simpl in Hle; omega.
Qed.

(* up *)
Definition map_upd (H : Z -> option Z) k v k' := if eq_dec k' k then Some v else H k'.

Lemma log_latest_upd : forall log v1 v2 v1' v2', log_latest log v1 v2 -> v1 < v1' ->
  log_incl log (map_upd log v1' v2') /\ log_latest (map_upd log v1' v2') v1' v2'.
Proof.
  intros; destruct H as (? & Hlast); unfold map_upd; split.
  - repeat intro; if_tac; auto.
    subst; rewrite (Hlast v1') in *; auto; discriminate.
  - split; [rewrite eq_dec_refl; auto|].
    intros v' ?; lapply (Hlast v'); [|omega].
    intro; if_tac; auto; omega.
Qed.

(* up *)
Lemma sepcon_list_view_shift : forall l1 l2 (Hlen : Zlength l1 = Zlength l2)
  (Hi : forall i, 0 <= i < Zlength l1 -> view_shift (Znth i l1 FF) (Znth i l2 FF)),
  view_shift (fold_right sepcon emp l1) (fold_right sepcon emp l2).
Proof.
  induction l1; intros.
  - symmetry in Hlen; apply Zlength_nil_inv in Hlen; subst; reflexivity.
  - destruct l2; [apply Zlength_nil_inv in Hlen; discriminate|].
    rewrite !Zlength_cons in *; simpl.
    apply view_shift_sepcon, IHl1; try omega.
    + lapply (Hi 0); [|pose proof (Zlength_nonneg l1); omega].
      rewrite !Znth_0_cons; auto.
    + intros; lapply (Hi (i + 1)); [|omega].
      rewrite !Znth_pos_cons, Z.add_simpl_r by omega; auto.
Qed.

Lemma update_entries : forall v v' vs vals version locs g g' lg lg', view_shift
  (fold_right sepcon emp (map (fun j => EX log : _, !! log_latest log v' (Znth j vals 0) &&
     protocol_W (Znth j locs Vundef) (Znth j lg Vundef) (Znth j lg' Vundef) log log_incl (data_T version g g'))
     (upto (Z.to_nat size))) *
   fold_right sepcon emp (map (node_entry v vs version locs g g' lg lg') (upto (Z.to_nat size))))
  (fold_right sepcon emp (map (fun j => EX log : _, !! log_latest log v' (Znth j vals 0) &&
     protocol_W (Znth j locs Vundef) (Znth j lg Vundef) (Znth j lg' Vundef) log log_incl (data_T version g g'))
     (upto (Z.to_nat size))) *
   fold_right sepcon emp (map (node_entry v' vals version locs g g' lg lg') (upto (Z.to_nat size)))).
Proof.
  intros.
  rewrite <- !sepcon_map.
  apply sepcon_list_view_shift; rewrite !Zlength_map; auto; intros.
  erewrite !Znth_map, !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
  unfold node_entry.
  view_shift_intro log'; view_shift_intro log; view_shift_intros.
  etransitivity; [apply protocol_R_W|].
  view_shift_intros; etransitivity; [apply protocol_W_R|].
  apply derives_view_shift; Exists log' log'; entailer!.
Qed.

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((((((n, input), sh), shi), version), locs), vals), g), g'), lg), lg'), v0), vs0); Intros.
  destruct H as (HP0 & HP & HQ).
  forward.
  rewrite map_map in HP, HQ.
  focus_SEP 2; apply protocol_W_R.
  forward_call_dep [(Z : Type)] (version, g, g', v0, Z.le, version_T, protocol_W version g g' v0 Z.le version_T,
    fun s v : Z => !!(v = s) && emp).
  { split; [|auto with dup].
    intros.
    apply derives_view_shift; unfold version_T; entailer!. }
  Intros x; destruct x as (?, v); simpl in *; subst.
  gather_SEP 1 0; apply protocol_R_W; Intros.
  assert (v = v0) by omega; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call_dep [(Z : Type)] (version, v0 + 1, g, g', v0, v0 + 1, Z.le, version_T, emp, emp).
  { split; [auto | split; [|omega]].
    intros.
    apply derives_view_shift; unfold version_T; entailer!. }
  assert (0 <= size) by (rewrite size_def; computable).
  assert_PROP (Zlength (map (fun x => vint x) vals) = size) by entailer!.
  assert (Z.even (v0 + 2) = true) by (rewrite Z.even_add; replace (Z.even v0) with true; auto).
  rewrite <- seq_assoc.
  focus_SEP 4.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
  forward_for_simple_bound 8 (EX i : Z, PROP () (LOCALx Q
    (SEPx (fold_right sepcon emp (map (fun j => EX log : _, !!(log_latest log (v0 + 2) (Znth j vals 0)) &&
             protocol_W (Znth j locs Vundef) (Znth j lg Vundef) (Znth j lg' Vundef) log log_incl (data_T version g g'))
             (sublist 0 i (upto (Z.to_nat size)))) ::
           fold_right sepcon emp (map (fun j => EX log : _, !!(log_latest log v0 (Znth j vs0 0)) &&
             protocol_W (Znth j locs Vundef) (Znth j lg Vundef) (Znth j lg' Vundef) log log_incl (data_T version g g'))
             (sublist i size (upto (Z.to_nat size)))) :: R)))) end.
  { rewrite sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    entailer!. }
  - (* loop body *)
    forward; rewrite <- size_def in *.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward.
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    Intros log.
    rewrite Zlength_map in *.
    destruct (log_latest_upd log v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
    forward_call_dep [(Z -> option Z : Type)] (Znth i locs Vundef, Znth i vals 0, Znth i lg Vundef,
      Znth i lg' Vundef, log, map_upd log (v0 + 2) (Znth i vals 0), log_incl, data_T version g g',
      protocol_W version g g' (v0 + 1) Z.le version_T, protocol_W version g g' (v0 + 1) Z.le version_T).
    { split; [apply Forall_Znth; auto; omega|].
      destruct (log_latest_upd log v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
      split; auto; intros.
      unfold data_T.
      view_shift_intro ver; view_shift_intros.
      etransitivity; [apply protocol_R_W|].
      view_shift_intros.
      etransitivity; [apply protocol_W_R|].
      apply derives_view_shift; Exists (v0 + 2); rewrite <- Z.add_sub_assoc; entailer!. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl fold_right.
    rewrite <- size_def; Exists (map_upd log (v0 + 2) (Znth i vals 0)); entailer!.
  - rewrite <- size_def, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    assert (repable_signed (v0 + 2)) by admit.
    forward_call_dep [(Z : Type)] (version, v0 + 2, g, g', v0 + 1, v0 + 2, Z.le, version_T, emp, emp).
    { fast_cancel. }
    { split; [auto | split; [|omega]].
      intros.
      apply derives_view_shift; unfold version_T; entailer!. }
    rewrite <- (map_map II).
    gather_SEP 0 2 7 6; rewrite <- !sepcon_assoc; apply invariants_view_shift with
      (Q0 := protocol_W version g g' (v0 + 2) Z.le version_T * fold_right sepcon emp (map (fun j =>
        EX log : _, !!(log_latest log (v0 + 2) (Znth j vals 0)) &&
          protocol_W (Znth j locs Vundef) (Znth j lg Vundef) (Znth j lg' Vundef) log log_incl (data_T version g g'))
        (upto (Z.to_nat size))) * EX v : Z, EX vs : list Z, Q (v, vs) tt).
    { rewrite !map_map, !sepcon_assoc, (sepcon_comm P), <- sepcon_assoc.
      etransitivity; [apply view_shift_sepcon2, HP|].
      view_shift_intro x; destruct x as (v, vs).
      rewrite <- !exp_sepcon2, <- exp_sepcon1, <- !sepcon_assoc.
      rewrite !(sepcon_assoc (_ * _)), (sepcon_comm (exp _)), <- sepcon_assoc.
      etransitivity; [|apply view_shift_sepcon2; etransitivity; [apply (HQ (v, vs) tt) |
        apply derives_view_shift; Exists v vs; auto]].
      unfold node_state; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_R _ _ _ _ _ _)), <- sepcon_assoc, 2sepcon_assoc.
      rewrite (sepcon_comm (protocol_R _ _ _ _ _ _)).
      etransitivity; [apply view_shift_sepcon1, protocol_R_W|].
      view_shift_intros; etransitivity; [apply view_shift_sepcon1, protocol_W_R|].
      rewrite sepcon_comm, <- !sepcon_assoc, 2sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, update_entries|].
      apply derives_view_shift; entailer!. }
    forward.
    rewrite map_map; Exists tt (v, vs); entailer!.
Admitted.
