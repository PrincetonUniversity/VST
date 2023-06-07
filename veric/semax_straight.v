Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas (*VST.veric.juicy_mem_ops*).
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.expr_lemmas4.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.semax_conseq.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.binop_lemmas.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas4.
Require Import VST.veric.valid_pointer.
Import LiftNotation.

Transparent intsize_eq.

Section extensions.
  Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs}.

Lemma semax_straight_simple:
 forall E Delta (B P: assert) c (Q: assert)
  (EB : Absorbing B)
  (Hc : forall m Delta' ge ve te rho k F f,
              tycontext_sub E Delta Delta' ->
              guard_environ Delta' f rho ->
              closed_wrt_modvars c F ->
              rho = construct_rho (filter_genv ge) ve te  ->
              cenv_sub cenv_cs (genv_cenv ge) ->
              mem_auth m ∗ (B rho ∧ (F rho ∗ ▷P rho)) ⊢
                ◇ ∃m' te' rho', ⌜rho' = mkEnviron (ge_of rho) (ve_of rho) (make_tenv te') ∧
                  guard_environ Delta' f rho' ∧ cl_step ge (State f c k ve te) m
                                 (State f Sskip k ve te') m'⌝ ∧
               |={E}=> (mem_auth m' ∗ ▷ (F rho' ∗ Q rho'))),
  semax Espec E Delta (B ∧ ▷ P) c (normal_ret_assert Q).
Proof.
intros until Q; intros EB Hc.
rewrite semax_unfold.
intros psi Delta' CS' TS [CSUB HGG'].
iIntros "#believe" (???) "[% #Hsafe]".
iIntros (te ve) "!> (% & P & fun)".
specialize (cenv_sub_trans CSUB HGG'); intros HGG.
iIntros (ora _).
monPred.unseal.
iApply jsafe_step.
rewrite /jstep_ex.
iIntros (m) "[Hm ?]".
iMod (Hc with "[P $Hm]") as (??? Hstep) ">Hc"; first done.
{ rewrite bi.sep_and_l; iFrame.
  iSplit; last iDestruct "P" as "[_ $]".
  iDestruct "P" as "[(_ & $) _]". }
iIntros "!>".
destruct Hstep as (? & ? & ?); iExists _, m'; iSplit; first by iPureIntro; eauto.
iDestruct "Hc" as "(? & Q)"; iFrame.
iNext.
iSpecialize ("Hsafe" $! EK_normal None te' ve).
iPoseProof ("Hsafe" with "[Q $fun]") as "Hsafe'".
{ simpl; subst; iSplit; try done.
  monPred.unseal; by iDestruct "Q" as "[$ $]". }
rewrite assert_safe_jsafe'; iFrame; by iPureIntro.
Qed.

Definition force_valid_pointers m v1 v2 :=
match v1, v2 with
| Vptr b1 ofs1, Vptr b2 ofs2 =>
    (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
    Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2))%bool
| _, _ => false
end.

Definition blocks_match op v1 v2 :=
match op with Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
  match v1, v2 with
    Vptr b _, Vptr b2 _ => b=b2
    | _, _ => False%type
  end
| _ => True%type
end.

Lemma mapsto_valid_pointer : forall b o sh t m,
  sh <> Share.bot ->
  mem_auth m ∗ mapsto_ sh t (Vptr b o) ⊢
  ⌜Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝.
Proof.
intros; iIntros "[Hm H]".
iAssert ⌜exists ch, access_mode t = By_value ch⌝ with "[H]" as %(ch & Hch).
{ rewrite /mapsto_ /mapsto.
  destruct (access_mode t) eqn: ?; try done.
  destruct (type_is_volatile t) eqn: ?; try done.
  eauto. }
rewrite /mapsto_ (mapsto_valid_pointer1 _ _ _ _ 0) /offset_val //.
rewrite Ptrofs.add_zero.
iMod "H"; iDestruct (valid_pointer_dry with "[$Hm $H]") as %Hvalid.
by rewrite Z.add_0_r in Hvalid.
{ pose proof (Ptrofs.unsigned_range o); lia. }
{ rewrite /sizeof (size_chunk_sizeof _ _ _ Hch).
  pose proof (size_chunk_pos ch); lia. }
Qed.

Lemma mapsto_is_pointer : forall sh t v, mapsto_ sh t v ⊢ ⌜exists b, exists o, v = Vptr b o⌝.
Proof.
intros. unfold mapsto_, mapsto.
destruct (access_mode t); try iIntros "[]";
destruct (type_is_volatile t); try iIntros "[]".
destruct v; try iIntros "[]".
iIntros; iPureIntro; eauto.
Qed.

Lemma pointer_cmp_eval:
  forall (Delta : tycontext) ve te (cmp : Cop.binary_operation) (e1 e2 : expr) ty sh1 sh2 ge
         (GE: cenv_sub cenv_cs (genv_cenv ge)),
   is_comparison cmp = true ->
   forall m (rho : environ) (Hrho : rho = construct_rho (filter_genv ge) ve te),
   typecheck_environ Delta rho ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   sh1 <> Share.bot -> sh2 <> Share.bot ->
   mem_auth m ∗ tc_expr Delta e1 rho ∧ tc_expr Delta e2 rho ∧
   ⌜blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho)⌝ ∧
   <absorb> mapsto_ sh1 (typeof e1) (eval_expr e1 rho) ∧
   <absorb> mapsto_ sh2 (typeof e2) (eval_expr e2 rho) ⊢
   ⌜Clight.eval_expr ge ve te m (Ebinop cmp e1 e2 ty) (eval_expr (Ebinop cmp e1 e2 ty) rho)⌝.
Proof.
intros until rho. intros ?? NE1 NE2 ??.
iIntros "[Hm H]".
iDestruct (eval_expr_relate with "[$Hm H]") as %He1.
{ iDestruct "H" as "[$ _]". }
iDestruct (eval_expr_relate with "[$Hm H]") as %He2.
{ iDestruct "H" as "(_ & $ & _)". }
rewrite /tc_expr /= !typecheck_expr_sound; [| done..].
iDestruct "H" as (???) "H".
iAssert ⌜∃ ch b o, access_mode (typeof e1) = By_value ch ∧ eval_expr e1 rho = Vptr b o ∧ Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝ with "[-]" as %(ch1 & b1 & o1 & ? & Hv1 & MT_1).
{ iDestruct "H" as "(>H & _)".
  iDestruct (mapsto_pure_facts with "H") as %((? & ?) & ?).
  destruct (eval_expr e1 rho); try contradiction.
  iDestruct (mapsto_valid_pointer with "[$]") as %?; eauto 7. }
iAssert ⌜∃ ch b o, access_mode (typeof e2) = By_value ch ∧ eval_expr e2 rho = Vptr b o ∧ Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝ with "[-]" as %(ch2 & b2 & o2 & ? & Hv2 & MT_2).
{ iDestruct "H" as "(_ & >H)".
  iDestruct (mapsto_pure_facts with "H") as %((? & ?) & ?).
  destruct (eval_expr e2 rho); try contradiction.
  iDestruct (mapsto_valid_pointer with "[$]") as %?; eauto 7. }
iPureIntro.
econstructor; eauto.
simpl; unfold_lift.
rewrite -> Hv1, Hv2 in *.
forget (typeof e1) as t1.
forget (typeof e2) as t2.
clear e1 e2 He1 He2 Hv1 Hv2.
rewrite /sem_binary_operation /sem_binary_operation' /sem_cmp /Cop.sem_cmp /cmp_ptr /sem_cmp_pp /Val.cmpu_bool /Val.cmplu_bool.
rewrite MT_1 MT_2.
simpl.
clear MT_1 MT_2.
rewrite bool2val_eq.
destruct t1; try solve [simpl in *; try destruct f; try tauto; congruence].
destruct t2; try solve [simpl in *; try destruct f; try tauto; congruence].
rewrite NE1 NE2 /=.
destruct cmp; try discriminate; subst; simpl; destruct Archi.ptr64  eqn:Hp;
try rewrite -> if_true by auto;
try solve [if_tac; subst; eauto]; rewrite ?peq_true; eauto.
Qed.

Lemma is_int_of_bool:
  forall i s b, is_int i s (Val.of_bool b).
Proof.
Transparent Int.repr.
destruct i,s,b; simpl; auto;
compute; try split; congruence.
Opaque Int.repr.
Qed.

Lemma pointer_cmp_no_mem_bool_type:
   forall (Delta : tycontext) cmp (e1 e2 : expr) b1 o1 b2 o2 i3 s3 a,
   is_comparison cmp = true->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   forall (rho : environ),
   eval_expr e1 rho = Vptr b1 o1 ->
   eval_expr e2 rho = Vptr b2 o2 ->
   blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho) ->
   tc_val (typeof e1) (eval_expr e1 rho) ->
   tc_val (typeof e2) (eval_expr e2 rho) ->
   typecheck_environ Delta rho ->
    tc_val' (Tint i3 s3 a)
     (force_val
        (sem_binary_operation' cmp (typeof e1) (typeof e2)
           (eval_expr e1 rho)
           (eval_expr e2 rho))).
Proof.
intros until 1. intros NE1 NE2; intros.
rewrite -> H0, H1 in *.
unfold sem_binary_operation'.
forget (typeof e1) as t1.
forget (typeof e2) as t2.
clear e1 e2 H0 H1.
unfold sem_cmp, sem_cmp_pp, cmp_ptr, Val.cmpu_bool, Val.cmplu_bool.
rewrite NE1 NE2.
destruct Archi.ptr64 eqn:Hp;
destruct cmp; inv H; destruct (classify_cmp t1 t2) eqn: Hclass;
simpl; unfold sem_cmp_pp;
rewrite /= ?Hp /=; auto; try if_tac; auto;
try apply tc_val_tc_val', binop_lemmas2.tc_bool2val;
subst;
try match goal with |- context [Z.b2z ?A] => destruct A end; try by intros ?.
all: rewrite /sem_binarith /both_int /both_long /both_float /both_single; destruct (classify_binarith t1 t2); simpl;
  repeat match goal with |-context[match ?A with _ => _ end] => destruct A end; try apply tc_val_tc_val', binop_lemmas2.tc_bool2val; try by intros ?.
Qed.

Definition weak_mapsto_ sh e rho :=
match (eval_expr e rho) with
| Vptr b o => (mapsto_ sh (typeof e) (Vptr b o)) ∨
              (mapsto_ sh (typeof e) (Vptr b o))
| _ => False
end.

Lemma closed_wrt_modvars_set : forall F id e v ge ve te rho
  (Hclosed : closed_wrt_modvars (Sset id e) F)
  (Hge : rho = construct_rho (filter_genv ge) ve te),
  F rho ⊣⊢ F (mkEnviron (ge_of rho) (ve_of rho)
       (make_tenv (Maps.PTree.set id v te))).
Proof.
  intros.
  apply Hclosed; intros.
  destruct (eq_dec i id).
  - rewrite /modifiedvars /modifiedvars' /insert_idset.
    subst; rewrite /lookup /ptree_lookup Maps.PTree.gss /=; auto.
  - rewrite -map_ptree_rel Map.gso; subst; auto.
Qed.

Lemma subst_set : forall {A} id v (P : environ -> A) v' ge ve te rho
  (Hge : rho = construct_rho (filter_genv ge) ve te)
  (Hid : Map.get (te_of rho) id = Some v),
  subst id (λ _ : environ, eval_id id rho) P
       (mkEnviron (ge_of rho) (ve_of rho)
          (make_tenv (Maps.PTree.set id v' te))) = P rho.
Proof.
  intros; subst rho; rewrite /subst /env_set /construct_rho -map_ptree_rel /=; unfold_lift.
  rewrite Map.override Map.override_same; auto.
  by rewrite /eval_id Hid.
Qed.

Lemma semax_ptr_compare:
forall E (Delta: tycontext) (P: assert) id cmp e1 e2 ty sh1 sh2,
    sh1 <> Share.bot -> sh2 <> Share.bot ->
    is_comparison cmp = true  ->
    eqb_type (typeof e1) int_or_ptr_type = false ->
    eqb_type (typeof e2) int_or_ptr_type = false ->
    (typecheck_tid_ptr_compare Delta id = true) ->
    semax Espec E Delta
        (▷ (tc_expr Delta e1 ∧ tc_expr Delta e2 ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          <absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)) ∧
          <absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2)) ∧
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (∃ old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) ∧
                            assert_of (subst id (liftx old) P))).
Proof.
  intros until sh2. intros ?? CMP NE1 NE2 TCid.
  apply semax_pre with (
      ((▷ tc_expr Delta e1 ∧
        ▷ tc_expr Delta e2 ∧
        ▷ local (fun rho => blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho)) ∧
        ▷ <absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)) ∧
        ▷ <absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
        ▷ P)), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  eapply typecheck_tid_ptr_compare_sub in TCid; last done.
  iIntros "H"; iExists m, (Maps.PTree.set id (eval_expr (Ebinop cmp e1 e2 ty) rho) te), _.
  monPred.unseal; rewrite !monPred_at_absorbingly; unfold_lift; simpl.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite !mapsto_is_pointer /tc_expr /= !typecheck_expr_sound; [| done..].
    iDestruct "H" as "(? & (>%TC1 & >%TC2 & >% & >%Hv1 & >%Hv2) & _)".
    destruct Hv1 as (? & ? & ?), Hv2 as (? & ? & ?).
    simpl. rewrite <- map_ptree_rel.
    iPureIntro; apply guard_environ_put_te'; [subst; auto|].
    intros ? Ht.
    rewrite /typecheck_tid_ptr_compare Ht in TCid; destruct t; try discriminate.
    eapply pointer_cmp_no_mem_bool_type; eauto.
  + iAssert (▷ ⌜Clight.eval_expr ge ve te m (Ebinop cmp e1 e2 ty) (eval_expr (Ebinop cmp e1 e2 ty) rho)⌝) with "[H]" as ">%";
      last by iPureIntro; constructor.
    iNext.
    iDestruct "H" as "(Hm & [H _])"; iCombine "Hm H" as "H".
    iApply (pointer_cmp_eval with "H").
  + iIntros "!> !>".
    iDestruct "H" as "($ & [_ (F & P)])".
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iExists (eval_id id rho).
    destruct TC as [[TC _] _].
    unfold typecheck_tid_ptr_compare, typecheck_temp_environ in *.
    destruct (temp_types Delta' !! id) eqn: Hid; try discriminate.
    destruct (TC _ _ Hid) as (? & ? & ?).
    unfold lift1; erewrite !subst_set by eauto; iFrame.
    super_unfold_lift.
    rewrite /eval_id /force_val -map_ptree_rel Map.gss //.
Qed.

Lemma semax_set_forward:
forall E (Delta: tycontext) (P: assert) id e,
    semax Espec E Delta
        (▷ (tc_expr Delta e ∧ (tc_temp_id id (typeof e) Delta e) ∧ P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val,
                 local (fun rho => eval_id id rho = subst id (liftx old) (eval_expr e) rho) ∧
                            assert_of (subst id (`old) P))).
Proof.
  intros.
  apply semax_pre with (
     (▷ tc_expr Delta e ∧
      ▷ tc_temp_id id (typeof e) Delta e) ∧
      ▷ P), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iIntros "(Hm & H)".
  iExists m, (Maps.PTree.set id (eval_expr e rho) te), _.
  monPred.unseal. setoid_rewrite tc_temp_id_sub; last done. rewrite /tc_temp_id /typecheck_temp_id /=.
  destruct (temp_types Delta' !! id) eqn: Hid.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite !denote_tc_assert_andp tc_bool_e.
    iAssert (▷ ⌜tc_val t (eval_expr e rho)⌝) with "[H]" as ">%".
    { iNext.
      rewrite (bi.and_elim_l (_ ∧ _)) (bi.and_elim_l (bi_pure _)).
      iDestruct "H" as "[H %]".
      by iApply neutral_cast_tc_val. }
    iPureIntro.
    simpl in *. simpl. rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; [subst; auto|].
    intros ? Hid'; rewrite Hid' in Hid; inv Hid.
    by apply tc_val_tc_val'.
  + iAssert (▷ ⌜Clight.eval_expr ge ve te m e (eval_expr e rho)⌝) with "[-]" as ">%"; last by iPureIntro; constructor.
    iNext; iApply eval_expr_relate.
    iDestruct "H" as "(($ & _) & _)"; iFrame.
  + iIntros "!> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iNext; iExists (eval_id id rho).
    destruct TC as [[TC _] _].
    destruct (TC _ _ Hid) as (? & ? & ?).
    super_unfold_lift; erewrite !subst_set by eauto; iFrame.
    rewrite /eval_id /force_val -map_ptree_rel Map.gss //.
  + iDestruct "H" as "((_ & >[]) & _)".
Qed.

Lemma semax_set_forward':
forall E (Delta: tycontext) (P: assert) id e t,
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e) t = true ->
    semax Espec E Delta
        (▷ (tc_expr Delta e ∧ P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val,
                 local (fun rho => eval_id id rho = subst id (liftx old) (eval_expr e) rho) ∧
                            assert_of (subst id (`old) P))).
Proof.
intros.
eapply semax_pre, semax_set_forward.
iIntros "[TC H] !>".
iSplit; first iDestruct "H" as "[$ _]".
iSplit; last iDestruct "H" as "[_ $]".
rewrite /tc_temp_id /typecheck_temp_id /=.
unfold typeof_temp in H.
destruct (temp_types Delta !! id) eqn: Ht; inv H.
iStopProof; monPred.unseal; split => rho.
rewrite Ht. setoid_rewrite denote_tc_assert_andp.
assert (implicit_deref (typeof e) = typeof e) as -> by (by destruct (typeof e)).
rewrite H0; iIntros "?"; iSplit; auto.
iApply (neutral_isCastResultType with "[$]").
Qed.

Lemma semax_cast_set:
forall E (Delta: tycontext) (P: assert) id e t
    (H99 : typeof_temp Delta id = Some t),
    semax Espec E Delta
        (▷ (tc_expr Delta (Ecast e t) ∧ P))
          (Sset id (Ecast e t))
        (normal_ret_assert
          (∃ old:val,
                 local (fun rho => eval_id id rho = subst id (liftx old) (eval_expr (Ecast e t)) rho) ∧
                            assert_of (subst id (`old) P))).
Proof.
  intros.
  apply semax_pre with (▷ tc_expr Delta (Ecast e t) ∧ ▷ P), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iIntros "(Hm & H)".
  iExists m, (Maps.PTree.set id (eval_expr (Ecast e t) rho) te), _.
  destruct TS as [TS _]; specialize (TS id).
  unfold typeof_temp in H99.
  destruct (temp_types Delta !! id) eqn: Hid; inversion H99; subst t0; clear H99.
  monPred.unseal.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite (bi.and_elim_l (▷ _)) /tc_expr /= typecheck_cast_sound; last apply typecheck_expr_sound; try done.
    iDestruct "H" as ">%"; iPureIntro.
    simpl in *. rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; [subst; auto|].
    intros ? Hid'; rewrite Hid' in TS; inv TS.
    by apply tc_val_tc_val'.
  + iAssert (▷ ⌜Clight.eval_expr ge ve te m (Ecast e t) (eval_expr (Ecast e t) rho)⌝) with "[-]" as ">%"; last by iPureIntro; constructor.
    iNext; iApply eval_expr_relate.
    iDestruct "H" as "($ & _)"; iFrame.
  + iIntros "!> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iNext; iExists (eval_id id rho).
    destruct TC as [[TC _] _].
    destruct (temp_types Delta' !! id) eqn: Hid'; inv TS.
    destruct (TC _ _ Hid') as (? & ? & ?).
    super_unfold_lift; erewrite !subst_set by eauto; iFrame.
    rewrite /eval_id /force_val -map_ptree_rel Map.gss //.
Qed.

Lemma eval_cast_Vundef:
 forall t1 t2, eval_cast t1 t2 Vundef = Vundef.
Proof.
 intros.
 unfold eval_cast, sem_cast, classify_cast.
 destruct (eqb_type t1 int_or_ptr_type);
 destruct (eqb_type t2 int_or_ptr_type);
 destruct t1,t2;
 try destruct i; try destruct s; try destruct f;
 try destruct i0; try destruct s0; try destruct f0;
 reflexivity.
Qed.

Lemma eqb_attr_true:
  forall a a', eqb_attr a a' = true -> a=a'.
Proof.
intros.
destruct a as [v a],a' as [v' a'].
simpl in H.
apply andb_true_iff in H.
destruct H.
destruct v,v'; inv  H;
destruct a,a'; inv H0; auto;
apply Neqb_ok in H1; subst n0; auto.
Qed.

Lemma semax_load:
forall E (Delta: tycontext) sh id (P: assert) e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
   (local (typecheck_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax Espec E Delta
       (▷
        (tc_lvalue Delta e1
        ∧ (⌜tc_val (typeof e1) v2⌝ ∧ P)))
       (Sset id e1)
       (normal_ret_assert (
        ∃ old:val, (local (fun rho => eval_id id rho = v2) ∧
                         assert_of (subst id (`old) P)))).
Proof.
  intros until v2.
  intros Hid0 TC1 H_READABLE H99.
  apply semax_pre with (
     (▷ tc_lvalue Delta e1 ∧
      ▷ ⌜tc_val (typeof e1) v2⌝) ∧
      ▷ P), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H)".
  monPred.unseal.
  rewrite (bi.and_comm _ (▷⌜_⌝)) -assoc; iDestruct "H" as "(>% & H)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iExists m, (Maps.PTree.set id v2 te), _.
  destruct TS as [TS _]; specialize (TS id).
  unfold typeof_temp in Hid0.
  destruct (temp_types Delta !! id) eqn: Hid; inversion Hid0; subst t; clear Hid0.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite (bi.and_elim_l (▷ _)) /tc_lvalue /= typecheck_lvalue_sound; try done.
    iDestruct "H" as ">%"; iPureIntro.
    rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; [subst; auto|].
    intros ? Hid'; rewrite Hid' in TS; inv TS.
    by eapply tc_val_tc_val', neutral_cast_subsumption.
  + iCombine "Hm H" as "H"; rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & H & _)"; iApply (eval_lvalue_relate with "[$Hm $H]").
    iDestruct "H" as "((Hm & H) & >%Heval)".
    destruct Heval as (b & ofs & ? & He1).
    iAssert (▷ <absorb> mapsto sh (typeof e1) (eval_lvalue e1 rho) v2) with "[H]" as "H".
    { iNext; iDestruct "H" as "(_ & _ & H)".
      inversion H99 as [H']. setoid_rewrite monPred_at_absorbingly in H'; iApply H'; monPred.unseal; auto. }
    rewrite (add_and (▷ _) (▷ _)); last by rewrite mapsto_pure_facts.
    iDestruct "H" as "(H & >%Hty)".
    destruct Hty as ((ch & ?) & ?).
    rewrite He1 mapsto_core_load; try done.
    iAssert (▷ ⌜load ch m b (Ptrofs.unsigned ofs) = Some v2⌝) with "[-]" as ">%".
    { iNext; rewrite absorbing; iApply core_load_load'; iFrame. }
    iPureIntro; constructor; econstructor; eauto.
    eapply Clight.deref_loc_value; eauto.
    { by intros ->; eapply tc_val_Vundef. }
  + iIntros "!> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iNext; iExists (eval_id id rho); iSplit.
    * rewrite /lift1 /eval_id -map_ptree_rel /= Map.gss //.
    * destruct TC as [[TC _] _].
      destruct (temp_types Delta' !! id) eqn: Hid'; inv TS.
      destruct (TC _ _ Hid') as (? & ? & ?).
      super_unfold_lift; erewrite !subst_set by eauto; iFrame.
Qed.

Lemma mapsto_tc' : forall sh t p v, mapsto sh t p v ⊢ ⌜tc_val' t v⌝.
Proof.
  intros; rewrite /mapsto.
  iIntros "H".
  destruct (access_mode t); try done.
  destruct (type_is_volatile t); try done.
  destruct p; try done.
  if_tac.
  - iDestruct "H" as "[(% & _) | (% & _)]"; iPureIntro; by [apply tc_val_tc_val' | subst; apply tc_val'_Vundef].
  - iDestruct "H" as "(($ & _) & _)".
Qed.

Lemma mapsto_tc : forall sh t p v, v <> Vundef -> mapsto sh t p v ⊢ ⌜tc_val t v⌝.
Proof.
  intros; rewrite mapsto_tc'; iPureIntro.
  by intros X; apply X.
Qed.

Lemma semax_cast_load:
forall E (Delta: tycontext) sh id (P: assert) e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
   (local (typecheck_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax Espec E Delta
       (▷
        (tc_lvalue Delta e1
        ∧ local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2)))
        ∧ P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (
        ∃ old:val, local (fun rho => eval_id id rho = (`(eval_cast (typeof e1) t1 v2)) rho) ∧
                         assert_of (subst id (`old) P))).
Proof.
  intros until v2.
  intros Hid0 HCAST H_READABLE H99.
  apply semax_pre with (
     (▷ tc_lvalue Delta e1 ∧
      ▷ local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2)))) ∧
      ▷ P), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H)".
  monPred.unseal.
  rewrite (bi.and_comm _ (▷⌜_⌝)) -assoc; iDestruct "H" as "(>% & H)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iExists m, (Maps.PTree.set id (eval_cast (typeof e1) t1 v2) te), _.
  destruct TS as [TS _]; specialize (TS id).
  unfold typeof_temp in Hid0.
  destruct (temp_types Delta !! id) eqn: Hid; inversion Hid0; subst t; clear Hid0.
  iSplit; [iSplit; first done; iSplit|].
  + iPureIntro.
    rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; [subst; auto|].
    intros ? Hid'; rewrite Hid' in TS; inv TS.
    by eapply tc_val_tc_val'.
  + iCombine "Hm H" as "H"; rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & H & _)"; iApply (eval_lvalue_relate with "[$Hm $H]").
    iDestruct "H" as "((Hm & H) & >%Heval)".
    destruct Heval as (b & ofs & ? & He1).
    iAssert (▷ <absorb> mapsto sh (typeof e1) (eval_lvalue e1 rho) v2) with "[H]" as "H".
    { iNext; iDestruct "H" as "(_ & _ & H)".
      inversion H99 as [H']. setoid_rewrite monPred_at_absorbingly in H'; iApply H'; monPred.unseal; auto. }
    rewrite (add_and (▷ _) (▷ _)); last by rewrite mapsto_pure_facts.
    iDestruct "H" as "(H & >%Hty)".
    destruct Hty as ((ch & ?) & ?).
    super_unfold_lift.
    assert (v2 <> Vundef) by (intros ->; setoid_rewrite eval_cast_Vundef in H; eapply tc_val_Vundef; eauto).
    rewrite (add_and (▷ _) (▷ _)); last by rewrite mapsto_tc.
    iDestruct "H" as "(H & >%)".
    rewrite He1 mapsto_core_load; try done.
    iAssert (▷ ⌜load ch m b (Ptrofs.unsigned ofs) = Some v2⌝) with "[-]" as ">%".
    { iNext; rewrite absorbing; iApply core_load_load'; iFrame. }
    iPureIntro. constructor; econstructor; [econstructor|]; eauto.
    * eapply Clight.deref_loc_value; eauto.
    * unfold eval_cast, force_val1 in *; super_unfold_lift.
      destruct ((sem_cast (typeof e1) t1) v2) eqn: Hcast; last by apply tc_val_Vundef in H.
      apply sem_cast_e1; auto.
  + iIntros "!> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iNext; iExists (eval_id id rho); iSplit.
    * rewrite /lift1 /eval_id -map_ptree_rel /= Map.gss //.
    * destruct TC as [[TC _] _].
      destruct (temp_types Delta' !! id) eqn: Hid'; inv TS.
      destruct (TC _ _ Hid') as (? & ? & ?).
      super_unfold_lift; erewrite !subst_set by eauto; iFrame.
Qed.

Lemma writable0_lub_retainer_Rsh:
 forall sh, writable0_share sh ->
  Share.lub (retainer_part sh) Share.Rsh = sh.
  intros. symmetry.
  unfold retainer_part.
  rewrite -> (comp_parts comp_Lsh_Rsh sh) at 1.
  f_equal; auto.
  unfold writable0_share in H.
  apply leq_join_sub in H.  apply Share.ord_spec1 in H. auto.
Qed.

Theorem load_store_similar':
   forall (chunk : memory_chunk) (m1 : Memory.mem)
         (b : Values.block) (ofs : Z) (v : val) (m2 : Memory.mem),
       store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  (align_chunk chunk' | ofs) ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk' b ofs).
  split; auto.
  destruct (store_valid_access_1 _ _ _ _ _ _ H _ _ _ _ (store_valid_access_3 _ _ _ _ _ _ H)).
  rewrite H0.
  eapply range_perm_implies; eauto. constructor.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B.
  rewrite (store_mem_contents _ _ _ _ _ _ H).
  rewrite Maps.PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H0.
  apply Nat2Z.inj; auto.
Qed.

Lemma mapsto_can_store : forall sh t ch b o v v' m (Hwrite : writable0_share sh) (Hch : access_mode t = By_value ch),
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ ⌜∃ m', Mem.store ch m b (Ptrofs.unsigned o) v' = Some m'⌝.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; iApply (mapsto_can_store with "[$]").
Qed.

Lemma mapsto_store': forall t t' m ch ch' v v' sh b o m' (Hsh : writable0_share sh)
  (Hch : access_mode t = By_value ch) (Hch' : access_mode t' = By_value ch')
  (Hdec : decode_encode_val_ok ch ch') (Ht' : type_is_volatile t' = false)
  (Halign : (align_chunk ch' | Ptrofs.unsigned o)%Z) (Htc : tc_val' t' (decode_val ch' (encode_val ch v'))),
  Mem.store ch m b (Ptrofs.unsigned o) v' = Some m' ->
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ |==> mem_auth m' ∗ ∃ v'', ⌜decode_encode_val v' ch ch' v''⌝ ∧ mapsto sh t' (Vptr b o) v''.
Proof.
  intros; rewrite /mapsto Hch Hch' Ht'.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> !if_true by auto.
  setoid_rewrite if_true; last auto.
  assert (forall v'', decode_encode_val v' ch ch' v'' -> tc_val' t' v'') as Htc'.
  { intros ? Hv''; eapply decode_encode_val_fun in Hv''; last apply decode_encode_val_general; subst; auto. }
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; iMod (mapsto_store' _ _ _ _ v' with "[$]") as "[$ (% & %Hv'' & H)]"; iIntros "!>";
    iExists _; (iSplit; first done; destruct (eq_dec v'' Vundef); [iRight | specialize (Htc' _ Hv'' n); iLeft]); eauto.
Qed.

Lemma mapsto_store: forall t m ch v v' sh b o m' (Hsh : writable0_share sh)
  (Htc : tc_val' t v') (Hch : access_mode t = By_value ch),
  Mem.store ch m b (Ptrofs.unsigned o) v' = Some m' ->
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ |==> mem_auth m' ∗ mapsto sh t (Vptr b o) v'.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> !if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; iMod (mapsto_store _ _ _ v' with "[$]") as "[$ H]";
    (destruct (eq_dec v' Vundef); [iRight | specialize (Htc n); iLeft]); eauto.
Qed.

Ltac dec_enc :=
match goal with
[ |- decode_val ?CH _ = ?V] => assert (DE := decode_encode_val_general V CH CH);
                               apply decode_encode_val_similar in DE; auto
end.

Lemma load_cast:
 forall (t: type) (e2 : expr) (ch : memory_chunk) rho m,
   tc_val (typeof e2) (eval_expr e2 rho) ->
   access_mode t = By_value ch ->
   mem_auth m ∗ denote_tc_assert (isCastResultType (typeof e2) t e2) rho ⊢
   ⌜Val.load_result ch
      (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) t m)) =
    force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) t m)⌝.
Proof.
intros.
assert (size_chunk ch = sizeof t) by (symmetry; apply size_chunk_sizeof; auto).
unfold sizeof in *.
iIntros "[Hm H]".
destruct ch;
 destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; try done;
simpl in *;
 destruct (eval_expr e2 rho);
 destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ] ;
 try done;
unfold Cop.sem_cast; simpl;
destruct Archi.ptr64 eqn:Hp;
try destruct (Float.to_int f);
try destruct (Float.to_intu f);
try destruct (Float.to_long f);
try destruct (Float.to_longu f);
try destruct (Float32.to_int f);
try destruct (Float32.to_intu f);
try destruct (Float32.to_long f);
try destruct (Float32.to_longu f);
 auto; simpl;
try solve [try rewrite Int.sign_ext_idem; auto; simpl; lia];
try rewrite Int.zero_ext_idem; auto; simpl; try lia;
try solve [simple_if_tac; auto].
Qed.

(* up? *)
Lemma big_sepL_timeless' {A} (f : nat -> A -> mpred) l `(∀ k v, Timeless (f k v)) : l ≠ [] -> Timeless ([∗ list] k↦v ∈ l, f k v).
Proof.
  revert dependent f; induction l; first done; simpl; intros.
  destruct l.
  - rewrite /= right_id //.
  - apply bi.sep_timeless; first done.
    by apply IHl.
Qed.

Global Instance mapsto_val_timeless l dq v : Timeless (l ↦{dq} VAL v).
Proof.
  rewrite gen_heap.mapsto_unseal /gen_heap.mapsto_def.
  rewrite resource_map.resource_map_elem_unseal /resource_map.resource_map_elem_def.
  apply _.
Qed.

Global Instance mapsto_no_timeless l dq : Timeless (mapsto_no l dq).
Proof.
  rewrite gen_heap.mapsto_no_unseal /gen_heap.mapsto_no_def.
  rewrite resource_map.resource_map_elem_no_unseal /resource_map.resource_map_elem_no_def.
  apply _.
Qed.

Global Instance address_mapsto_timeless ch v sh l : Timeless (address_mapsto ch v sh l).
Proof.
  rewrite /address_mapsto.
  apply bi.exist_timeless; intros.
  rewrite /Timeless.
  rewrite bi.later_and; iIntros "(>(% & % & %) & H)".
  iSplit; first done.
  iApply (timeless with "H").
  apply big_sepL_timeless'; first apply _.
  destruct (size_chunk_nat_pos ch); destruct x; try done; simpl in *; lia.
Qed.

Global Instance mapsto_timeless sh t v1 v2 : Timeless (mapsto sh t v1 v2).
Proof.
  rewrite /mapsto.
  destruct (access_mode t); try apply _.
  destruct (type_is_volatile t); try apply _.
  destruct v1; try apply _.
  if_tac; try apply _.
  rewrite /nonlock_permission_bytes.
  apply bi.and_timeless; first apply _.
  apply big_sepL_timeless'.
  intros; if_tac; try apply _.
  { destruct (Z.to_nat _) eqn: Hn; try done.
    pose proof (size_chunk_pos m); lia. }
Qed.

Lemma semax_store:
 forall E Delta e1 e2 sh P (WS : writable0_share sh),
   semax Espec E Delta
          (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ P)))
          (Sassign e1 e2)
          (normal_ret_assert (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) ∗ P)).
Proof.
  intros.
  apply semax_pre with
    (∃ v3: val,
      (▷ tc_lvalue Delta e1 ∧ ▷ tc_expr Delta (Ecast e2 (typeof e1))) ∧
      ▷ (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v3)) ∗ P)).
  { intros; iIntros "[? H]".
    rewrite /mapsto_ !bi.later_and; eauto. }
  apply extract_exists_pre; intro v3.
  apply semax_straight_simple; auto.
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  monPred.unseal; unfold_lift.
  rewrite (add_and (_ ∧ (_ ∗ _)) (▷ ⌜_⌝)).
  2: { iIntros "(_ & _ & ? & _) !>"; iApply (mapsto_pure_facts with "[$]"). }
  iDestruct "H" as "(H & >%H)".
  destruct H as ((ch & ?) & ?); destruct (eval_lvalue e1 rho) eqn: He1; try contradiction.
  iCombine "Hm H" as "H".
  rewrite (add_and (_ ∗ _) (▷ ⌜_⌝)).
  2: { iIntros "(? & _ & _ & ? & _) !>".
       iApply (mapsto_can_store with "[$]"). }
  iDestruct "H" as "((Hm & H) & >%Hstore)".
  destruct Hstore as (m' & Hstore).
  iExists m', te, rho.
  iSplit.
  + iSplit; first by subst.
    iSplit; first done.
    iCombine "Hm H" as "H"; rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (H & _) & _)"; iApply (eval_lvalue_relate with "[$Hm $H]").
    iDestruct "H" as "(H & >%He1')".
    destruct He1' as (? & ? & ? & He1'); rewrite He1' in He1; inv He1.
    rewrite /tc_expr /typecheck_expr /=; fold typecheck_expr.
    rewrite denote_tc_assert_andp.
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (_ & H & _) & _)"; iApply (eval_expr_relate with "[$Hm $H]").
    iDestruct "H" as "(H & >%He2)".
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(? & (_ & H) & _)"; iApply (cast_exists with "[$H]").
    iDestruct "H" as "(H & >%Hcast)".
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(? & (_ & H & _) & _)"; iApply (typecheck_expr_sound with "[$H]").
    iDestruct "H" as "(H & >%)".
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (_ & _ & H) & _)"; iApply (cop2_sem_cast' with "[$Hm $H]").
    iDestruct "H" as "(H & >%Hcast')".
    rewrite Hcast in Hcast'.
    iPureIntro; econstructor; eauto.
    eapply assign_loc_value; eauto.
  + iIntros "!>".
    rewrite /tc_expr /= typecheck_expr_sound //.
    rewrite (bi.and_elim_r (▷ tc_lvalue _ _ _)).
    iDestruct "H" as "(>%Htc & F & >Hmapsto & P)".
    subst; iPoseProof (mapsto_store with "[$Hm $Hmapsto]") as ">[? ?]".
    { by apply tc_val_tc_val'. }
    rewrite He1; by iFrame.
Qed.

Definition numeric_type (t: type) : bool :=
match t with
| Tint IBool _ _ => false
| Tint _ _ _ => true
| Tlong _ _ => true
| Tfloat _ _ => true
| _ => false
end.

Lemma semax_store_union_hack:
     forall
         E (Delta : tycontext) (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : assert),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax Espec E Delta
         (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
              ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1)))
               ∗ P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (∃ v':val,
              (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) ∧
              (assert_of ((` (mapsto sh t2)) (eval_lvalue e1) (`v')) ∗ P))).
Proof.
  intros until P. intros NT AM0 AM' OK WS.
  assert (SZ := decode_encode_val_size _ _ OK).
  apply semax_pre with
  (∃ v3: val,
      (▷ tc_lvalue Delta e1 ∧ ▷ tc_expr Delta (Ecast e2 (typeof e1))) ∧
      ▷ ((assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v3))
                ∧ assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v3))) ∗ P)).
  { intros; iIntros "[? H]".
    rewrite /mapsto_ !bi.later_and; eauto. }
  apply extract_exists_pre; intro v3.
  apply semax_straight_simple; auto.
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  monPred.unseal; unfold_lift.
  rewrite (add_and (_ ∧ (_ ∗ _)) (▷ ⌜_⌝)).
  2: { iIntros "(_ & _ & (_ & ?) & _) !>"; iApply (mapsto_pure_facts with "[$]"). }
  iDestruct "H" as "(H & >%H)".
  destruct H as (_ & ?); destruct (eval_lvalue e1 rho) eqn: He1; try contradiction.
  iCombine "Hm H" as "H".
  rewrite (add_and (_ ∗ _) (▷ ⌜_⌝)).
  2: { iIntros "(? & _ & _ & (? & _) & _) !>".
       iApply (mapsto_can_store with "[$]"); auto. }
  iDestruct "H" as "((Hm & H) & >%Hstore)".
  destruct Hstore as (m' & Hstore).
  iExists m', te, rho.
  iSplit.
  + iSplit; first by subst.
    iSplit; first done.
    iCombine "Hm H" as "H"; rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (H & _) & _)"; iApply (eval_lvalue_relate with "[$Hm $H]").
    iDestruct "H" as "(H & >%He1')".
    destruct He1' as (? & ? & ? & He1'); rewrite He1' in He1; inv He1.
    rewrite /tc_expr /typecheck_expr /=; fold typecheck_expr.
    rewrite denote_tc_assert_andp.
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (_ & H & _) & _)"; iApply (eval_expr_relate with "[$Hm $H]").
    iDestruct "H" as "(H & >%He2)".
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(? & (_ & H) & _)"; iApply (cast_exists with "[$H]").
    iDestruct "H" as "(H & >%Hcast)".
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(? & (_ & H & _) & _)"; iApply (typecheck_expr_sound with "[$H]").
    iDestruct "H" as "(H & >%)".
    rewrite (add_and (_ ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & (_ & _ & H) & _)"; iApply (cop2_sem_cast' with "[$Hm $H]").
    iDestruct "H" as "(H & >%Hcast')".
    rewrite Hcast in Hcast'.
    iPureIntro; econstructor; eauto.
    eapply assign_loc_value; eauto.
  + iIntros "!>".
    rewrite /tc_expr /= typecheck_expr_sound //.
    rewrite (bi.and_elim_r (▷ tc_lvalue _ _ _)); iDestruct "H" as "(>%Htc & F & >H & P)".
    iAssert ⌜type_is_volatile t2 = false ∧ (align_chunk ch' | Ptrofs.unsigned i)%Z⌝ with "[H]" as %[??].
    { iDestruct "H" as "[_ H]"; rewrite /mapsto AM'.
      destruct (type_is_volatile t2); first done.
      rewrite -> if_true by auto.
      iDestruct "H" as "[(% & H) | (% & % & H)]"; rewrite address_mapsto_align; iDestruct "H" as "[_ %]"; done. }
    iDestruct "H" as "[Hmapsto _]".
    rewrite /= /force_val1 in Htc; super_unfold_lift.
    subst; iPoseProof (mapsto_store' with "[$Hm $Hmapsto]") as ">[$ ?]"; auto.
    { set (v := force_val _) in *.
      rewrite andb_true_iff in NT; destruct NT as [NT NT'].
      destruct ch, ch'; try contradiction OK;
        destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv NT; inv AM0;
        destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv NT'; inv AM';
        destruct v; simpl in *; subst; try contradiction;
        try apply I;
        try (apply tc_val_Vundef in TCv; contradiction);
        rewrite /decode_val proj_inj_bytes; intros ?;
        match goal with
        | |- context [Int.sign_ext ?n] => apply (sign_ext_range' n); compute; split; congruence
        | |- context [Int.zero_ext ?n] => apply (zero_ext_range' n); compute; split; congruence
        | |- _ => idtac
        end; done. }
    rewrite He1; by iFrame.
Qed.

End extensions.
