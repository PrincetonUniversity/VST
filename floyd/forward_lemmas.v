Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
(* Require Import VST.floyd.closed_lemmas. *)
Import Cop.
Import LiftNotation.
Import -(notations) compcert.lib.Maps.

Lemma semax_while_peel: 
  forall `{heapGS Σ} {CS: compspecs} {Espec: OracleKind} `{!externalGS OK_ty Σ} Inv E Delta P expr body R,
  semax E Delta P (Ssequence (Sifthenelse expr Sskip Sbreak) body) 
                            (loop1_ret_assert Inv R) ->
  semax E Delta Inv (Swhile expr body) R ->
  semax E Delta P (Swhile expr body) R.
Proof.
intros.
apply semax_loop_unroll1 with (P' := Inv) (Q := Inv); auto.
eapply semax_pre; [ |  apply sequential; apply semax_skip].
destruct R; apply ENTAIL_refl.
Qed.

Lemma typelist2list_arglist: forall l i, map snd (arglist i l) = typelist2list l.
Proof. induction l. simpl; intros; trivial.
intros. simpl. f_equal. apply IHl.
Qed. 

Lemma semax_func_cons_ext_vacuous:
     forall `{heapGS Σ} {Espec: OracleKind} `{!externalGS OK_ty Σ} 
         (V : varspecs) (G : funspecs) (C : compspecs) ge E
         (fs : list (ident * Clight.fundef)) (id : ident) (ef : external_function)
         (argsig : typelist) (retsig : type)
         (G' : funspecs) cc b,
       (id_in_list id (map fst fs)) = false ->
       ef_sig ef =
       {|
         sig_args := typlist_of_typelist argsig;
         sig_res := rettype_of_type retsig;
         sig_cc := cc_of_fundef (External ef argsig retsig cc) |} ->
       Genv.find_symbol ge id = Some b ->
       Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
       semax_func V G ge E fs G' ->
       semax_func V G ge E ((id, External ef argsig retsig cc) :: fs)
         ((id, vacuous_funspec (External ef argsig retsig cc)) :: G').
Proof.
intros.

specialize (semax_func_cons_ext V G ge E fs id ef argsig retsig
  (ConstType Impossible) 
).
simpl.
intros HH; eapply HH; clear HH; try assumption; trivial.
* rewrite <-(typelist2list_arglist _ 1). reflexivity.
* right. clear. hnf. intros x. inv x.
* intros. unfold monPred_at. done. 
* eassumption.
* assumption.
* pose proof (semax_external_FF E ef (ConstType Impossible)) as Hvac.
  simpl in Hvac. match goal with H : ?f |- ?g => assert (f = g) as <-; last done end.
  repeat f_equal; apply proof_irr.
Qed.

Lemma semax_func_cons_int_vacuous
  `{heapGS0: heapGS Σ} (Espec : OracleKind) `{externalGS0: !externalGS OK_ty Σ}
  (V : varspecs) (G : funspecs) 
    (cs : compspecs) (ge : Genv.t (fundef function) type) E
    (fs : list (ident * Clight.fundef)) (id : ident) ifunc
    (b : block) G'
  (ID: id_in_list id (map fst fs) = false)
  (ID2: id_in_list id (map fst G) = true)
  (GfsB: Genv.find_symbol ge id = Some b)
  (GffpB: Genv.find_funct_ptr ge b = Some (Internal ifunc))
  (CTvars: Forall (fun it : ident * type => complete_type cenv_cs (snd it) = true) (fn_vars ifunc))
  (LNR_PT: list_norepet (map fst (fn_params ifunc) ++ map fst (fn_temps ifunc)))
  (LNR_Vars: list_norepet (map fst (fn_vars ifunc)))
  (VarSizes: @semax.var_sizes_ok cenv_cs (fn_vars ifunc))
  (Sfunc: @semax_func _ _ Espec _ V G cs ge E fs G'):
  @semax_func _ _ Espec _ V G cs ge E ((id, Internal ifunc) :: fs)
    ((id, vacuous_funspec (Internal ifunc)) :: G').
Proof.
eapply semax_func_cons; try eassumption.
+ rewrite ID ID2. simpl. unfold semax_body_params_ok.
  apply compute_list_norepet_i in LNR_PT. rewrite LNR_PT.
  apply compute_list_norepet_i in LNR_Vars. rewrite LNR_Vars. trivial.
+ destruct ifunc; simpl; trivial.
+ red; simpl. split3.
  - destruct ifunc; simpl; trivial.
  - destruct ifunc; simpl; trivial.
  - intros Impos. inv Impos.
Qed.

Lemma semax_prog_semax_func_cons_int_vacuous
  `{heapGS0: heapGS Σ} (Espec : OracleKind) `{externalGS0: !externalGS OK_ty Σ}
  (V : varspecs) (G : funspecs) 
    (cs : compspecs) (ge : Genv.t (fundef function) type) E
    (fs : list (ident * Clight.fundef)) (id : ident) ifunc
    (b : block) G'
  (ID: id_in_list id (map fst fs) = false)
  (GfsB: Genv.find_symbol ge id = Some b)
  (GffpB: Genv.find_funct_ptr ge b = Some (Internal ifunc))
  (CTvars: Forall (fun it : ident * type => complete_type cenv_cs (snd it) = true) (fn_vars ifunc))
  (LNR_PT: list_norepet (map fst (fn_params ifunc) ++ map fst (fn_temps ifunc)))
  (LNR_Vars: list_norepet (map fst (fn_vars ifunc)))
  (VarSizes: @semax.var_sizes_ok cenv_cs (fn_vars ifunc))
  (Sfunc: @semax_prog.semax_func _ _ Espec _ V G cs ge E fs G'):
  @semax_prog.semax_func _ _ Espec _ V G cs ge E ((id, Internal ifunc) :: fs)
    ((id, vacuous_funspec (Internal ifunc)) :: G').
Proof.
apply id_in_list_false in ID. destruct Sfunc as [Hyp1 [Hyp2 Hyp3]].
split3.
{ constructor. 2: apply Hyp1. simpl. destruct ifunc; simpl.
  unfold type_of_function. simpl. rewrite TTL1; trivial. }
{ clear Hyp3. red; intros j fd J. destruct J; [ inv H | auto].
  exists b; split; trivial. }
intros. specialize (Hyp3 _ Gfs Gffp).
iIntros (v sig cc A P Q CL).
hnf in CL.
destruct CL as [j [J GJ]]. simpl in J.
rewrite PTree.gsspec in J.
destruct (peq j id); subst.
+ 
  destruct GJ as [bb [BB VV]]. inv J.
  assert (bb = b). 
  { clear - GfsB Gfs BB. specialize (Gfs id); unfold sub_option, Clight.fundef in *.
    rewrite GfsB in Gfs. destruct ge'. simpl in *. rewrite Gfs in BB. inv BB; trivial. }
  subst bb. iRight. unfold believe_internal. iExists b, ifunc.
  specialize (Gffp b).
  unfold Clight.fundef in *. simpl in *. rewrite GffpB in Gffp. simpl in Gffp.
  iSplit.
  iPureIntro.
  repeat split; trivial.
  destruct ifunc; trivial.
  destruct ifunc; trivial.
  iIntros (???? []).
+ iApply Hyp3; iPureIntro.
  exists j; split. apply J. apply GJ.
Qed.

Lemma int_eq_false_e:
  forall i j, Int.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int.eq_true in H; inv H.
Qed.

Lemma int64_eq_false_e:
  forall i j, Int64.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int64.eq_true in H; inv H.
Qed.

Lemma ptrofs_eq_false_e:
  forall i j, Ptrofs.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Ptrofs.eq_true in H; inv H.
Qed.

Lemma derives_trans: forall {prop:bi} (P Q R:prop),
  (P -∗ Q) -> (Q -∗ R) -> (P -∗ R).
Proof. intros. rewrite H H0 //. Qed.

Lemma semax_ifthenelse_PQR' :
   forall `{heapGS Σ} {CS: compspecs} {Espec: OracleKind} `{!externalGS OK_ty Σ} (v: val) E Delta P Q R (b: expr) c d Post,
      bool_type (typeof b) = true ->
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
         (tc_expr Delta (Eunop Cop.Onotbool b tint))  ->
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢
        local (`(eq v) (eval_expr b)) ->
     semax E Delta (PROPx (typed_true (typeof b) v :: P) (LOCALx Q (SEPx R)))
                        c Post ->
     semax E Delta (PROPx (typed_false (typeof b) v :: P) (LOCALx Q (SEPx R)))
                        d Post ->
     semax E Delta (▷ PROPx P (LOCALx Q (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply semax_pre;  [ | apply semax_ifthenelse]; auto.
 - instantiate (1:=(local (`(eq v) (eval_expr b)) ∧ PROPx P (LOCALx Q (SEPx R)))).
   eapply derives_trans; [apply bi.and_mono, derives_refl; apply bi.later_intro|].
   rewrite -bi.later_and; apply bi.later_mono.
   apply bi.and_intro; try assumption. apply bi.and_intro; try assumption.
   apply bi.and_elim_r; auto.
 - eapply semax_pre; [ | eassumption].
   rewrite <- insert_prop.
   forget ( PROPx P (LOCALx Q (SEPx R))) as PQR.
   go_lowerx. normalize. apply bi.and_intro; auto.
   subst; apply bi.pure_intro; repeat split; auto.
 - eapply semax_pre; [ | eassumption].
   rewrite <- insert_prop.
   forget ( PROPx P (LOCALx Q (SEPx R))) as PQR.
   go_lowerx. normalize. apply bi.and_intro; auto.
   subst; apply bi.pure_intro; repeat split; auto.
Qed.

Definition logical_and_result v1 t1 v2 t2 :=
match (strict_bool_val t1 v1) with
| Some b1 => if b1 then match (strict_bool_val t2 v2) with
                            | Some b2 => if b2 then  Vint Int.one
                                         else Vint Int.zero
                            | None => Vundef end
                   else Vint Int.zero
| None => Vundef
end.

Definition logical_or_result v1 t1 v2 t2 :=
match (strict_bool_val t1 v1) with
| Some b1 => if b1 then Vint Int.one
                   else match (strict_bool_val t2 v2) with
                            | Some b2 => if b2 then  Vint Int.one
                                         else Vint Int.zero
                            | None => Vundef end
| None => Vundef
end.

Definition logical_or tid e1 e2 :=
(Sifthenelse e1
             (Sset tid (Econst_int (Int.repr 1) tint))
             (Ssequence
                (Sset tid (Ecast e2 tbool))
                (Sset tid (Ecast (Etempvar tid tint) tint)))).



Definition logical_and tid e1 e2 :=
(Sifthenelse e1
            (Ssequence
              (Sset tid (Ecast e2 tbool))
              (Sset tid (Ecast (Etempvar tid tint) tint)))
            (Sset tid (Econst_int (Int.repr 0) tint))).


(* TODO move to mpred.v *)
Section MPRED.
Definition massert' `{heapGS Σ} := environ -> mpred.
Program Definition assert_of_m `{heapGS Σ} (P : massert') : assert' := P.
Fail Example bi_of_massert'_test `{heapGS Σ} : forall (P Q : massert'), P ∗ Q ⊢ Q ∗ P.
Global Coercion assert_of_m : massert' >-> assert'.
Example bi_of_massert'_test `{heapGS Σ} : forall (P Q : massert'), P ∗ Q ⊢ Q ∗ P.
Proof. intros. rewrite bi.sep_comm. done. Qed.

(* FIXME can this be avoided? *)

Context `{heapGS Σ}.
Lemma bi_assert_id : forall P,  bi_assert(Σ:=Σ) P ⊣⊢ P.
Proof. intros. unfold bi_assert. constructor. intros simpl. constructor. intros.
       split; intros; simpl; done.
Qed.
End MPRED.

Lemma semax_pre_flipped :
 forall `{heapGS0: heapGS Σ} (P' : massert') (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs}
        E (Delta : tycontext) (P1 : list Prop) (P2 : list localdef)
         (P3 : list mpred) (c : statement)
         (R : ret_assert),
       semax E Delta P' c R ->
       ENTAIL Delta, PROPx P1 (LOCALx P2 (SEPx P3)) ⊢ P' ->
       semax E Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof. intros.
eapply semax_pre. apply H0.  rewrite bi_assert_id. apply H.
Qed.

Lemma semax_while :
 forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs}
     E Delta Q test body (R: ret_assert),
     bool_type (typeof test) = true ->
     (local (tc_environ Delta) ∧ Q ⊢  (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (local (tc_environ Delta) ∧ local (lift1 (typed_false (typeof test)) (eval_expr test)) ∧ Q ⊢ RA_normal R) ->
     semax E Delta (local (`(typed_true (typeof test)) (eval_expr test)) ∧ Q)  body (loop1_ret_assert Q R) ->
     semax E Delta Q (Swhile test body) R.
Proof.
intros ? ? ? ? ? ? ? ? ? ? ? BT TC Post H.
unfold Swhile.
apply (semax_loop E Delta Q Q).
2:{
 clear. eapply semax_post_flipped. apply semax_skip.
 all: try (intros; rewrite bi.and_elim_r; destruct R; apply derives_refl).
 intros. rewrite bi.and_elim_r. destruct R; simpl. normalize.
 intros. rewrite bi.and_elim_r. destruct R; simpl. normalize.
} 
apply semax_seq with
 (local (`(typed_true (typeof test)) (eval_expr test)) ∧ Q).
apply semax_pre_simple with (▷( (tc_expr Delta (Eunop Cop.Onotbool test tint)) ∧ Q)).
eapply derives_trans, bi.later_intro.
apply bi.and_intro. apply TC.
apply bi.and_elim_r.
clear H.
apply semax_ifthenelse; auto.
eapply semax_post_flipped. apply semax_skip.
destruct R as [?R ?R ?R ?R].
simpl RA_normal in *. rewrite bi.and_elim_r. raise_rho; simpl. rewrite bi.and_comm. auto.
all: try (raise_rho; simpl; normalize).
eapply semax_pre_simple; [ | apply semax_break].
rewrite (bi.and_comm Q).
eapply derives_trans; try apply Post.
destruct R; simpl; auto.
Qed.

Lemma semax_while_3g1 :
 forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ}  {cs: compspecs}
     {A} (v: A -> val) E Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢ (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢ local (`(eq (v a)) (eval_expr test))) ->
     (forall a, semax E Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1_ret_assert (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
                           (overridePost
                            (∃ a:A, PROPx (typed_false (typeof test) (v a) :: P a)  (LOCALx (Q a) (SEPx (R a))))
                            Post))) ->
     semax E Delta (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
                 (Swhile test body)
                 (overridePost
                   (∃ a:A, PROPx (typed_false (typeof test) (v a) :: P a)  (LOCALx (Q a) (SEPx (R a))))
                   Post).
Proof.
intros.
apply semax_while; auto.
*
 rewrite bi.and_exist_l. apply bi.exist_elim; intro a.
 eapply derives_trans; [ | apply H0].
 apply derives_refl.
*
repeat rewrite  bi.and_exist_l. apply bi.exist_elim; intro a.
rewrite overridePost_normal'.
apply bi.exist_intro' with a.
eapply derives_trans.
apply bi.and_intro; [ | apply derives_refl].
eapply derives_trans; [ | apply (H1 a)].
rewrite (bi.and_comm (local _)).
rewrite -bi.and_assoc. rewrite bi.and_elim_r. rewrite bi.and_comm. auto.
go_lowerx; normalize.
repeat apply bi.and_intro; auto.
apply bi.pure_intro; split; auto.
rewrite H3; auto.
*
 repeat rewrite  bi.and_exist_l.
 apply extract_exists_pre; intro a.
 eapply semax_pre_post; try apply (H2 a).
 +
 rewrite bi.and_assoc.
 rewrite <- insert_prop.
 apply bi.and_intro; [ | apply bi.and_elim_r; auto].
 rewrite (bi.and_comm (local _)). rewrite -bi.and_assoc.
 eapply derives_trans.
 apply bi.and_intro; [ | apply derives_refl].
 rewrite (H1 a). apply bi.and_elim_r.
 rewrite bi.and_assoc.
 rewrite bi.and_elim_l.
 go_lowerx. intro; apply bi.pure_intro. rewrite H3; auto.
 + apply bi.and_elim_r.
 + apply bi.and_elim_r.
 + apply bi.and_elim_r.
 + intros; apply bi.and_elim_r.
Qed.

Lemma semax_for_x :
 forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs}
     E Delta Q test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     (local (tc_environ Delta) ∧ Q ⊢ (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (local (tc_environ Delta)
      ∧ local (`(typed_false (typeof test)) (eval_expr test))
      ∧ Q ⊢ RA_normal Post) ->
     semax E Delta (local (`(typed_true (typeof test)) (eval_expr test)) ∧ Q)
             body (loop1_ret_assert PreIncr Post) ->
     semax E Delta PreIncr incr (normal_ret_assert Q) ->
     semax E Delta Q
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_loop with PreIncr.
apply semax_seq with (local (tc_environ Delta) ∧
   (Q ∧ local (` (typed_true (typeof test)) (eval_expr test)))) .
apply semax_pre_simple with (▷ ((tc_expr Delta (Eunop Cop.Onotbool test tint)) ∧ Q)).
eapply derives_trans, bi.later_intro.
apply bi.and_intro; auto.
apply bi.and_elim_r; auto.
apply semax_ifthenelse; auto.
*
eapply semax_post_flipped; [ apply semax_skip | .. ].
destruct Post as [?P ?P ?P ?P]; simpl; normalize.
destruct Post as [?P ?P ?P ?P]; simpl; normalize.
destruct Post as [?P ?P ?P ?P]; simpl; normalize.
intros vl; destruct Post as [?P ?P ?P ?P]; simpl; normalize.
*
eapply semax_pre_simple; [ | apply semax_break].
destruct Post as [?P ?P ?P ?P]; simpl; normalize.
eapply derives_trans; [ | apply H1].
rewrite (bi.and_comm (Q rho)).
simpl.
raise_rho.
done.
*
eapply semax_pre_simple; [ | apply H2].
rewrite bi.and_elim_r.
rewrite bi.and_elim_r.
rewrite bi.and_comm. auto.
*
eapply semax_post_flipped. apply H3.
rewrite bi.and_elim_r; raise_rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
rewrite bi.and_elim_r; raise_rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
normalize.
rewrite bi.and_elim_r; raise_rho; destruct Post as [?P ?P ?P ?P]; simpl. apply bi.False_elim.
intro; rewrite bi.and_elim_r; raise_rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
normalize.
Qed.

Lemma semax_for :
 forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs}
     {A:Type} (v: A -> val) E Delta P Q R test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     (forall a:A, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))
           ⊢ tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     (forall a:A, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢  local (`(eq (v a)) (eval_expr test))) ->
     (forall a:A,
        semax E Delta (PROPx (typed_true (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a))))
             body (loop1_ret_assert (PreIncr a) Post)) ->
     (forall a, semax E Delta (PreIncr a) incr (normal_ret_assert (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))) ->
     (forall a:A, ENTAIL Delta, PROPx (typed_false (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a)))
          ⊢ RA_normal Post) ->
     semax E Delta (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_for_x with (∃ a:A, PreIncr a); auto.
- rewrite bi.and_exist_l. apply bi.exist_elim. apply H0.
- clear - H4 H1. rewrite !bi.and_exist_l. apply bi.exist_elim. intro a; eapply derives_trans; [| apply H4].
  iIntros "(H1 & H2 & H3 & H4 & H5)". repeat iSplit; try done. 
  iPoseProof (H1 with "[-]") as "#H6". { repeat iSplit; try done.  }
  iDestruct "H6" as "-# H6". (* by moving to spatail context, H6 gets an affine modality when exiting ipm,
                                and allows normalize to extract info from it instead of just throwing it away *)
  iStopProof. unfold local.  super_unfold_lift. raise_rho. normalize. rewrite H5. done.
- normalize.
  apply extract_exists_pre; intro a.
  eapply semax_pre_post; try apply (H2 a).
  + rewrite <- insert_prop.
    eapply derives_trans; [ | eapply derives_trans].
    eapply bi.and_intro; [ | apply derives_refl].
    eapply derives_trans; [ | apply (H1 a)].
    apply bi.and_mono; auto.
    apply bi.and_elim_r; auto.
    apply derives_refl.
    rewrite 2![in X in (X-∗_)]bi.and_assoc.
    apply bi.and_mono; auto.
    raise_rho; unfold local, lift1; unfold_lift.
    iIntros "((%H5 & %H6) & %H7)". rewrite H5; done.
  + rewrite bi.and_elim_r.
    unfold loop1_ret_assert.
    destruct Post as [?P ?P ?P ?P]; apply bi.exist_intro'  with a; apply derives_refl.
  + destruct Post as [?P ?P ?P ?P]; apply bi.and_elim_r; apply derives_refl.
  + destruct Post as [?P ?P ?P ?P]; apply bi.exist_intro'  with a; apply bi.and_elim_r; simpl; auto.
  + intros vl; destruct Post as [?P ?P ?P ?P]; apply bi.and_elim_r; apply derives_refl.
- apply extract_exists_pre; intro a.
  eapply semax_post'; try apply (H3 a).
  apply bi.exist_intro'  with a; auto.
  apply bi.and_elim_r; auto.
Qed.

Lemma forward_setx':
  forall `{!heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs}
  E Delta P id e,
  (P ⊢ (tc_expr Delta e) ∧ (tc_temp_id id (typeof e) Delta e) ) ->
  semax E Delta
             P
             (Sset id e)
             (normal_ret_assert
                  (∃ old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) ∧
                              ( (assert_of (subst id (`old) P))))).
Proof.
intros.
eapply semax_pre.
2:{  specialize (semax_set_forward E Delta P id e) as HH.
     instantiate (1:=(▷ (tc_expr Delta e ∧ tc_temp_id id (typeof e) Delta e ∧ P))).
     apply HH. }
+ eapply derives_trans ; [ | apply bi.later_intro ].
   rewrite bi.and_elim_r. rewrite bi.and_assoc. apply bi.and_intro; auto.
Qed.

Lemma semax_switch_PQR: 
  forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {CS: compspecs} ,
  forall n E Delta (Pre: environ->mpred) a sl (Post: ret_assert),
     is_int_type (typeof a) = true ->
     ENTAIL Delta, (assert_of Pre) ⊢ tc_expr Delta a ->
     ENTAIL Delta, (assert_of Pre) ⊢ local (`(eq (Vint (Int.repr n))) (eval_expr a)) ->
     semax E Delta 
               (assert_of Pre)
               (seq_of_labeled_statement (select_switch (Int.unsigned (Int.repr n)) sl))
               (switch_ret_assert Post) ->
     semax E Delta (assert_of Pre) (Sswitch a sl) Post.
Proof.
intros.
eapply semax_pre.
apply derives_refl.
apply (semax_switch); auto.
intro n'.
assert_PROP (n' = Int.repr n). {
apply derives_trans with (local (`( eq (Vint (Int.repr n))) (eval_expr a)) ∧ local (` eq (eval_expr a) `(Vint n'))).
apply bi.and_intro.
eapply derives_trans; [ | eassumption].
raise_rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
raise_rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
raise_rho.
unfold local, lift1, liftx, lift; simpl.
(* FIXME change to normalize when normalize patch is merged *)
iIntros "(%H3 & %H4)". iPureIntro. 
rewrite <- H3 in H4.
apply Vint_inj in H4.
auto.
}
subst n'.
eapply semax_pre; [ | eassumption].
rewrite !bi.and_elim_r //.
Qed.

Lemma modulo_samerepr:
 forall x y, 
  Z.modulo x Int.modulus = Z.modulo y Int.modulus -> 
  Int.repr x = Int.repr y.
Proof.
intros.
apply Int.eqm_samerepr.
apply Zmod_divide_minus in H; [ | reflexivity].
unfold Int.eqm.
unfold Zbits.eqmod.
set (m := Int.modulus) in *.
destruct H as [z ?].
assert (x = y mod m + z * m) by lia.
clear H. subst x.
pose proof (Z.div_mod y m).
spec H. intro Hx; inv Hx.
evar (k: Z).
exists k.
rewrite {2}H; clear H.
rewrite (Z.mul_comm m).
assert (z * m = k*m + (y/m*m))%Z; [ | lia].
rewrite <- Z.mul_add_distr_r.
f_equal.
assert (k = z - y/m); [ | lia].
subst k.
reflexivity.
Qed.

Lemma select_switch_case_signed:
 forall y n x c sl,
 Z.modulo x Int.modulus = Z.modulo y Int.modulus ->
 0 <= x < Int.modulus ->
 select_switch_case n (LScons (Some x) c sl) = 
 if zeq (Int.unsigned (Int.repr y)) n then Some (LScons (Some x) c sl)
 else select_switch_case n sl.
Proof.
intros.
simpl.
apply modulo_samerepr in H.
rewrite <- H.
rewrite -> Int.unsigned_repr by rep_lia.
auto.
Qed.

Definition signof (e: expr) := 
  match typeof e with
  | Tint _ s _ => s
  | Tlong s _ => s 
  | _ =>  Unsigned
  end.

Definition adjust_for_sign (s: signedness) (x: Z) :=
 match s with
 | Unsigned => x 
 | Signed => if (zlt x Int.half_modulus) then x else x - Int.modulus 
 end.

Lemma semax_for_3g1 :
 forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs} {A} (PQR: A -> environ -> mpred) (v: A -> val)
     E Delta P Q R test body incr Post,
     bool_type (typeof test) = true ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢ (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢ local (`(eq (v a)) (eval_expr test))) ->
     (forall a, semax E Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1_ret_assert  (∃ a:A, assert_of (PQR a)) Post)) ->
     (forall a, semax E Delta (assert_of (PQR a)) incr
                         (normal_ret_assert (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))) ->
     (forall a, ENTAIL Delta, PROPx (typed_false (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))) 
                             ⊢ RA_normal Post) ->
     semax E Delta (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
                 (Sloop (Ssequence (Sifthenelse test Sskip Sbreak)  body) incr)
                 Post.
Proof.
intros.
apply semax_loop with (Q':= (∃ a:A, assert_of (PQR a))).
*
 apply extract_exists_pre; intro a.
 apply @semax_seq with (Q := PROPx (typed_true (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a)))).
 apply semax_pre with (▷ (tc_expr Delta (Eunop Onotbool test (Tint I32 Signed noattr)) 
                                        ∧ (local (`(eq (v a)) (eval_expr test)) ∧ (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))));
   [ | apply semax_ifthenelse; auto].
 eapply derives_trans, bi.later_intro .
 apply bi.and_intro; auto.
 apply bi.and_intro; auto.
 apply bi.and_elim_r; auto.
 apply sequential.
 eapply semax_post_flipped; [apply semax_skip | | | | ].
+
 rewrite bi.and_elim_r.
 destruct Post; simpl_ret_assert.
 clear.
 rewrite <- insert_prop.
 forget (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) as PQR.
 raise_rho.  simpl. unfold_lift.  unfold local, lift1. normalize.
 rewrite H0. normalize.
+
 destruct Post; simpl_ret_assert. apply bi.and_elim_r; auto.
+
 destruct Post; simpl_ret_assert. apply bi.and_elim_r; auto.
+
 intros; destruct Post; simpl_ret_assert. apply bi.and_elim_r; auto.
+
 eapply semax_pre; [ | apply semax_break].
 autorewrite with ret_assert.
 eapply derives_trans; [ | apply (H4 a)]. clear.
 apply bi.and_mono; auto.
 rewrite <- insert_prop.
 clear.
 forget (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) as PQR.
 raise_rho.  simpl. unfold_lift.  unfold local, lift1. normalize.
 rewrite H0. normalize.
+
 eapply semax_post_flipped.
 apply H2.
 all: intros; apply bi.and_elim_r; auto.
*
 make_sequential.
 apply extract_exists_pre. intro a.
 eapply semax_post_flipped. apply H3.
 all: intros; destruct Post; simpl_ret_assert; apply bi.and_elim_r; auto.
Qed.

Lemma semax_for_3g2:  (* no break statements in loop *)
 forall `{heapGS0: heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ} {cs: compspecs} 
     {A} (PQR: A -> environ -> mpred) (v: A -> val) E Delta P Q R test body incr Post,
     bool_type (typeof test) = true ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢ (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) ⊢ local (`(eq (v a)) (eval_expr test))) ->
     (forall a, semax E Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1x_ret_assert (∃ a:A, assert_of (PQR a)) Post)) ->
     (forall a, semax E Delta (assert_of (PQR a)) incr
                         (normal_ret_assert (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))) ->
     semax E Delta (∃ a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
                 (Sloop (Ssequence (Sifthenelse test Sskip Sbreak)  body) incr)
                 (overridePost
                      (∃ a:A, PROPx (typed_false (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                  Post).
Proof.
intros.
eapply semax_for_3g1; try eassumption.
*
 intro a.  eapply semax_post_flipped. apply H2.
 all: intros; destruct Post; simpl_ret_assert; rewrite bi.and_elim_r; auto.
 apply bi.False_elim.
*
 intro a.
 rewrite bi.and_elim_r. destruct Post; simpl_ret_assert. apply (bi.exist_intro' _ _ a). auto.
Qed.

Transparent tc_andp.  (* ? should leave it opaque, maybe? *) 

