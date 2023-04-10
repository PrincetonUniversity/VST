Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas (*VST.veric.juicy_mem_ops*) VST.veric.juicy_view.
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
  Context {CS: compspecs} `{!heapGS Σ} {Espec: OracleKind} `{!externalGS OK_ty Σ}.

Lemma semax_straight_simple:
 forall E Delta (B: environ -> mpred) P c Q
  (EB : forall rho, Absorbing (B rho))
  (Hc : forall m Delta' ge ve te rho k F f,
              tycontext_sub Delta Delta' ->
              guard_environ Delta' f rho ->
              closed_wrt_modvars c F ->
              rho = construct_rho (filter_genv ge) ve te  ->
              cenv_sub cenv_cs (genv_cenv ge) ->
              mem_auth m ∗ (B rho ∧ (F rho ∗ ▷P rho)) ∗ funassert Delta' rho ⊢
                ◇ ∃m' te' rho', ⌜rho' = mkEnviron (ge_of rho) (ve_of rho) (make_tenv te') ∧
                  guard_environ Delta' f rho' ∧ cl_step ge (State f c k ve te) m
                                 (State f Sskip k ve te') m'⌝ ∧
               ▷ |={E}=> (mem_auth m' ∗ (F rho' ∗ Q rho'))),
  semax Espec E Delta (fun rho => B rho ∧ ▷ P rho) c (normal_ret_assert Q).
Proof.
intros until Q; intros EB Hc.
rewrite semax_unfold.
intros psi Delta' CS' TS [CSUB HGG'].
iIntros "#believe" (???) "[% #Hsafe]".
iIntros (te ve) "!> (% & P & #?)".
specialize (cenv_sub_trans CSUB HGG'); intros HGG.
iIntros (ora _).
iApply jsafe_step.
rewrite /jstep_ex.
iIntros (m) "[Hm ?]".
iMod (Hc with "[P $Hm]") as (??? Hstep) "Hc"; first done.
{ rewrite bi.sep_and_l; iFrame "#".
  iSplit; last iDestruct "P" as "[_ $]".
  rewrite bi.sep_elim_r; iDestruct "P" as "[$ _]". }
destruct Hstep as (? & ? & ?); iExists _, m'; iSplit; first by iPureIntro; eauto.
iIntros "!> !>"; iMod "Hc" as "(? & Q)".
iSpecialize ("Hsafe" $! EK_normal None te' ve).
iPoseProof ("Hsafe" with "[Q]") as "Hsafe'".
{ rewrite proj_frame /=; subst; iSplit; [|iSplit]; try done.
  by iDestruct "Q" as "[$ $]". }
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
  mem_auth m ∗ mapsto_ sh t (Vptr b o) ⊢
  ⌜Mem.valid_pointer m b (Ptrofs.unsigned o) = true⌝.
Proof.
intros; iIntros "[Hm H]".
iAssert ⌜exists ch, access_mode t = By_value ch⌝ with "[H]" as %(ch & H).
{ rewrite /mapsto_ /mapsto.
  destruct (access_mode t) eqn: ?; try done.
  destruct (type_is_volatile t) eqn: ?; try done.
  eauto. }
rewrite /mapsto_ (mapsto_valid_pointer1 _ _ _ _ 0) /offset_val.
rewrite Ptrofs.add_zero.
iMod "H"; iDestruct (valid_pointer_dry with "[$Hm $H]") as %Hvalid.
by rewrite Z.add_0_r in Hvalid.
{ pose proof (Ptrofs.unsigned_range o); lia. }
{ rewrite /sizeof (size_chunk_sizeof _ _ _ H).
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
   mem_auth m ∗ tc_expr Delta e1 rho ∧ tc_expr Delta e2 rho ∧
   ⌜blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho)⌝ ∧
   <absorb> mapsto_ sh1 (typeof e1) (eval_expr e1 rho) ∧
   <absorb> mapsto_ sh2 (typeof e2) (eval_expr e2 rho) ⊢
   ⌜Clight.eval_expr ge ve te m (Ebinop cmp e1 e2 ty) (eval_expr (Ebinop cmp e1 e2 ty) rho)⌝.
Proof.
intros until rho. intros ?? NE1 NE2.
iIntros "[Hm H]".
iDestruct (eval_expr_relate with "[$Hm H]") as %He1.
{ iDestruct "H" as "[$ _]". }
iDestruct (eval_expr_relate with "[$Hm H]") as %He2.
{ iDestruct "H" as "(_ & $ & _)". }
rewrite /tc_expr !typecheck_expr_sound; [| done..].
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
  F rho = F (mkEnviron (ge_of rho) (ve_of rho)
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
  subst id (liftx (eval_id id rho)) P
       (mkEnviron (ge_of rho) (ve_of rho)
          (make_tenv (Maps.PTree.set id v' te))) = P rho.
Proof.
  intros; subst rho; rewrite /subst /env_set /construct_rho -map_ptree_rel /=; unfold_lift.
  rewrite Map.override Map.override_same; auto.
  by rewrite /eval_id Hid.
Qed.

Lemma semax_ptr_compare:
forall E (Delta: tycontext) (P: environ -> mpred) id cmp e1 e2 ty sh1 sh2,
    is_comparison cmp = true  ->
    eqb_type (typeof e1) int_or_ptr_type = false ->
    eqb_type (typeof e2) int_or_ptr_type = false ->
    (typecheck_tid_ptr_compare Delta id = true) ->
    semax Espec E Delta
        (fun rho =>
          ▷ (tc_expr Delta e1 rho ∧ tc_expr Delta e2 rho  ∧
          ⌜blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho)⌝ ∧
          <absorb> mapsto_ sh1 (typeof e1) (eval_expr e1 rho) ∧
          <absorb> mapsto_ sh2 (typeof e2) (eval_expr e2 rho) ∧
          P rho))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (fun rho => (∃ old:val,
                 ⌜eval_id id rho = subst id (liftx old)
                     (eval_expr (Ebinop cmp e1 e2 ty)) rho⌝ ∧
                            subst id (liftx old) P rho))).
Proof.
  intros until sh2. intros CMP NE1 NE2 TCid.
  apply semax_pre with (fun rho =>
      ((▷ tc_expr Delta e1 rho ∧
        ▷ tc_expr Delta e2 rho ∧
        ▷ ⌜blocks_match cmp (eval_expr e1 rho) (eval_expr e2 rho)⌝ ∧
        ▷ <absorb> mapsto_ sh1 (typeof e1) (eval_expr e1 rho) ∧
        ▷ <absorb> mapsto_ sh2 (typeof e2) (eval_expr e2 rho)) ∧
        ▷ P rho)), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  eapply typecheck_tid_ptr_compare_sub in TCid; last done.
  iIntros "H"; iExists m, (Maps.PTree.set id (eval_expr (Ebinop cmp e1 e2 ty) rho) te), _.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite !mapsto_is_pointer /tc_expr !typecheck_expr_sound; [| done..].
    iDestruct "H" as "(? & ((>%TC1 & >%TC2 & >% & >%Hv1 & >%Hv2) & _) & ?)".
    destruct Hv1 as (? & ? & ?), Hv2 as (? & ? & ?).
    simpl. rewrite <- map_ptree_rel.
    iPureIntro; apply guard_environ_put_te'; [subst; auto|].
    intros ? Ht.
    rewrite /typecheck_tid_ptr_compare Ht in TCid; destruct t; try discriminate.
    eapply pointer_cmp_no_mem_bool_type; eauto.
  + iAssert (▷ ⌜Clight.eval_expr ge ve te m (Ebinop cmp e1 e2 ty) (eval_expr (Ebinop cmp e1 e2 ty) rho)⌝) with "[H]" as ">%";
      last by iPureIntro; constructor.
    iNext.
    iApply pointer_cmp_eval.
    iDestruct "H" as "($ & [$ _] & _)".
  + iIntros "!> !>".
    iDestruct "H" as "($ & [_ (F & P)] & #?)".
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iExists (eval_id id rho).
    destruct TC as [[TC _] _].
    unfold typecheck_tid_ptr_compare, typecheck_temp_environ in *.
    destruct (temp_types Delta' !! id) eqn: Hid; try discriminate.
    destruct (TC _ _ Hid) as (? & ? & ?).
    erewrite !subst_set by eauto; iFrame.
    super_unfold_lift.
    rewrite /eval_id /force_val -map_ptree_rel Map.gss //.
Qed.

Lemma semax_set_forward:
forall E (Delta: tycontext) (P: environ -> mpred) id e,
    semax Espec E Delta
        (fun rho =>
          ▷ (tc_expr Delta e rho ∧ (tc_temp_id id (typeof e) Delta e rho) ∧ P rho))
          (Sset id e)
        (normal_ret_assert
          (fun rho => (∃ old:val,
                 ⌜eval_id id rho =  subst id (liftx old) (eval_expr e) rho⌝ ∧
                            subst id (`old) P rho))).
Proof.
  intros.
  apply semax_pre with (fun rho =>
     (▷ tc_expr Delta e rho ∧
      ▷ tc_temp_id id (typeof e) Delta e rho) ∧
      ▷ P rho), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iIntros "(Hm & H & #?)".
  iExists m, (Maps.PTree.set id (eval_expr e rho) te), _.
  rewrite tc_temp_id_sub /tc_temp_id /typecheck_temp_id; last done.
  destruct (temp_types Delta' !! id) eqn: Hid.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite !denote_tc_assert_andp tc_bool_e.
    iAssert (▷ ⌜tc_val t (eval_expr e rho)⌝) with "[H]" as ">%".
    { iNext.
      rewrite bi.and_elim_l (bi.and_elim_l (bi_pure _)).
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
  + iIntros "!> !> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iExists (eval_id id rho).
    destruct TC as [[TC _] _].
    destruct (TC _ _ Hid) as (? & ? & ?).
    erewrite !subst_set by eauto; iFrame.
    super_unfold_lift.
    rewrite /eval_id /force_val -map_ptree_rel Map.gss //.
  + iDestruct "H" as "((_ & >[]) & _)".
Qed.

Lemma semax_set_forward':
forall E (Delta: tycontext) (P: assert) id e t,
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e) t = true ->
    semax Espec E Delta
        (fun rho =>
          ▷ ((tc_expr Delta e rho) ∧ P rho))
          (Sset id e)
        (normal_ret_assert
          (fun rho => (∃ old:val,
                 ⌜eval_id id rho =  subst id (liftx old) (eval_expr e) rho⌝ ∧
                            subst id (`old) P rho))).
Proof.
intros.
eapply semax_pre, semax_set_forward.
intros; iIntros "[%TC H] !>".
iSplit; first iDestruct "H" as "[$ _]".
iSplit; last iDestruct "H" as "[_ $]".
rewrite /tc_temp_id /typecheck_temp_id.
unfold typeof_temp in H.
destruct (temp_types Delta !! id) eqn: Ht; inv H.
rewrite Ht denote_tc_assert_andp.
assert (implicit_deref (typeof e) = typeof e) as -> by (by destruct (typeof e)).
rewrite H0; iSplit; auto.
iApply neutral_isCastResultType.
Qed.

Lemma semax_cast_set:
forall E (Delta: tycontext) (P: environ -> mpred) id e t
    (H99 : typeof_temp Delta id = Some t),
    semax Espec E Delta
        (fun rho =>
          ▷ ((tc_expr Delta (Ecast e t) rho) ∧ P rho))
          (Sset id (Ecast e t))
        (normal_ret_assert
          (fun rho => (∃ old:val,
                 ⌜eval_id id rho = subst id (liftx old) (eval_expr (Ecast e t)) rho⌝ ∧
                            subst id (`old) P rho))).
Proof.
  intros.
  apply semax_pre with (fun rho => ▷ tc_expr Delta (Ecast e t) rho ∧ ▷ P rho), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iIntros "(Hm & H & #?)".
  iExists m, (Maps.PTree.set id (eval_expr (Ecast e t) rho) te), _.
  destruct TS as [TS _]; specialize (TS id).
  unfold typeof_temp in H99.
  destruct (temp_types Delta !! id) eqn: Hid; inversion H99; subst t0; clear H99.
  rewrite Hid in TS.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite bi.and_elim_l /tc_expr typecheck_cast_sound; last apply typecheck_expr_sound; try done.
    iDestruct "H" as ">%"; iPureIntro.
    simpl in *. rewrite <- map_ptree_rel.
    apply guard_environ_put_te'; [subst; auto|].
    intros ? Hid'; rewrite Hid' in TS; inv TS.
    by apply tc_val_tc_val'.
  + iAssert (▷ ⌜Clight.eval_expr ge ve te m (Ecast e t) (eval_expr (Ecast e t) rho)⌝) with "[-]" as ">%"; last by iPureIntro; constructor.
    iNext; iApply eval_expr_relate.
    iDestruct "H" as "($ & _)"; iFrame.
  + iIntros "!> !> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iExists (eval_id id rho).
    destruct TC as [[TC _] _].
    destruct (temp_types Delta' !! id) eqn: Hid'; rewrite Hid' in TS; inv TS.
    destruct (TC _ _ Hid') as (? & ? & ?).
    erewrite !subst_set by eauto; iFrame.
    super_unfold_lift.
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
  forall a a',  eqb_attr a a' = true  -> a=a'.
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
forall E (Delta: tycontext) sh id P e1 t2 v2,
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ P rho ⊢ <absorb> mapsto sh (typeof e1) (eval_lvalue e1 rho) v2) ->
    semax Espec E Delta
       (fun rho => ▷
        (tc_lvalue Delta e1 rho
        ∧ (⌜tc_val (typeof e1) v2⌝ ∧ P rho)))
       (Sset id e1)
       (normal_ret_assert (fun rho =>
        ∃ old:val, (⌜eval_id id rho = v2⌝ ∧
                         (subst id (`old) P rho)))).
Proof.
  intros until v2.
  intros Hid0 TC1 H_READABLE H99.
  apply semax_pre with (fun rho =>
     (▷ tc_lvalue Delta e1 rho ∧
      ▷ ⌜tc_val (typeof e1) v2⌝) ∧
      ▷ P rho), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H & #?)".
  rewrite (bi.and_comm _ (▷⌜_⌝)) -assoc; iDestruct "H" as "(>% & H)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iExists m, (Maps.PTree.set id v2 te), _.
  destruct TS as [TS _]; specialize (TS id).
  unfold typeof_temp in Hid0.
  destruct (temp_types Delta !! id) eqn: Hid; inversion Hid0; subst t; clear Hid0.
  rewrite Hid in TS.
  iSplit; [iSplit; first done; iSplit|].
  + rewrite bi.and_elim_l /tc_lvalue typecheck_lvalue_sound; try done.
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
      iApply H99; auto. }
    rewrite (add_and (▷ _) (▷ _)); last by rewrite mapsto_pure_facts.
    iDestruct "H" as "(H & >%Hty)".
    destruct Hty as ((ch & ?) & ?).
    rewrite He1 mapsto_core_load; try done.
    iAssert (▷ ⌜load ch m b (Ptrofs.unsigned ofs) = Some v2⌝) with "[-]" as ">%".
    { iNext; rewrite absorbing; iApply core_load_load'; iFrame. }
    iPureIntro; constructor; econstructor; eauto.
    eapply Clight.deref_loc_value; eauto.
    { by intros ->; eapply tc_val_Vundef. }
  + iIntros "!> !> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iExists (eval_id id rho); iSplit.
    * rewrite /eval_id -map_ptree_rel /= Map.gss //.
    * destruct TC as [[TC _] _].
      destruct (temp_types Delta' !! id) eqn: Hid'; rewrite Hid' in TS; inv TS.
      destruct (TC _ _ Hid') as (? & ? & ?).
      erewrite !subst_set by eauto; iFrame.
Qed.

Lemma mapsto_tc : forall sh t p v, readable_share sh -> v <> Vundef -> mapsto sh t p v ⊢ ⌜tc_val t v⌝.
Proof.
  intros; rewrite /mapsto.
  iIntros "H".
  destruct (access_mode t); try done.
  destruct (type_is_volatile t); try done.
  destruct p; try done.
  rewrite -> if_true by auto.
  by iDestruct "H" as "[($ & _) | (% & _)]".
Qed.

Lemma semax_cast_load:
forall E (Delta: tycontext) sh id P e1 t1 v2,
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ P rho ⊢ <absorb> mapsto sh (typeof e1) (eval_lvalue e1 rho) v2) ->
    semax Espec E Delta
       (fun rho => ▷
        (tc_lvalue Delta e1 rho
        ∧ ⌜tc_val t1 (`(eval_cast (typeof e1) t1 v2) rho)⌝
        ∧ P rho))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (fun rho =>
        ∃ old:val, (⌜eval_id id rho = (`(eval_cast (typeof e1) t1 v2)) rho⌝ ∧
                         (subst id (`old) P rho)))).
Proof.
  intros until v2.
  intros Hid0 HCAST H_READABLE H99.
  apply semax_pre with (fun rho =>
     (▷ tc_lvalue Delta e1 rho ∧
      ▷ ⌜tc_val t1 (`(eval_cast (typeof e1) t1 v2) rho)⌝) ∧
      ▷ P rho), semax_straight_simple.
  { intros. rewrite bi.and_elim_r !bi.later_and !assoc //. }
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H & #?)".
  rewrite (bi.and_comm _ (▷⌜_⌝)) -assoc; iDestruct "H" as "(>% & H)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  iExists m, (Maps.PTree.set id (eval_cast (typeof e1) t1 v2) te), _.
  destruct TS as [TS _]; specialize (TS id).
  unfold typeof_temp in Hid0.
  destruct (temp_types Delta !! id) eqn: Hid; inversion Hid0; subst t; clear Hid0.
  rewrite Hid in TS.
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
      iApply H99; auto. }
    rewrite (add_and (▷ _) (▷ _)); last by rewrite mapsto_pure_facts.
    iDestruct "H" as "(H & >%Hty)".
    destruct Hty as ((ch & ?) & ?).
    assert (v2 <> Vundef) by (intros ->; rewrite eval_cast_Vundef in H; eapply tc_val_Vundef; eauto).
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
  + iIntros "!> !> !>".
    iDestruct "H" as "(_ & F & P)"; iFrame.
    erewrite (closed_wrt_modvars_set F) by eauto; iFrame.
    iExists (eval_id id rho); iSplit.
    * rewrite /eval_id -map_ptree_rel /= Map.gss //.
    * destruct TC as [[TC _] _].
      destruct (temp_types Delta' !! id) eqn: Hid'; rewrite Hid' in TS; inv TS.
      destruct (TC _ _ Hid') as (? & ? & ?).
      erewrite !subst_set by eauto; iFrame.
Qed.

(*Lemma res_option_core: forall r, res_option (core r) = None.
Proof.
 destruct r. rewrite core_NO; auto. rewrite core_YES; auto. rewrite core_PURE; auto.
Qed.*)

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

Lemma decode_encode_val_fun:
  forall ch1 ch2, decode_encode_val_ok ch1 ch2 ->
  forall v v1 v2,
     decode_encode_val v ch1 ch2 v1 ->
     decode_encode_val v ch1 ch2 v2 ->
     v1=v2.
Proof.
intros.
destruct ch1, ch2; try contradiction;
destruct v; simpl in *; subst; auto.
Qed.

Lemma decode_encode_val_size:
  forall ch1 ch2, decode_encode_val_ok ch1 ch2 ->
   size_chunk ch1 = size_chunk ch2.
Proof.
intros.
destruct ch1, ch2; try contradiction;
simpl in *; subst; auto.
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

Lemma mapsto_store: forall t m ch v v' sh b o m' (Hsh : writable0_share sh)
  (Htc : tc_val t v') (Hch : access_mode t = By_value ch),
  Mem.store ch m b (Ptrofs.unsigned o) v' = Some m' ->
  mem_auth m ∗ mapsto sh t (Vptr b o) v ⊢ |==> mem_auth m' ∗ mapsto sh t (Vptr b o) v'.
Proof.
  intros; rewrite /mapsto Hch.
  iIntros "[Hm H]".
  destruct (type_is_volatile t); try done.
  rewrite -> !if_true by auto.
  iDestruct "H" as "[(% & ?) | (% & % & ?)]"; iPoseProof (mapsto_store _ _ _ v' with "[$]") as ">[$ H]"; iLeft; by iFrame.
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


Lemma semax_store:
 forall E Delta e1 e2 sh P (WS : writable0_share sh),
   semax Espec E Delta
          (fun rho =>
          ▷ (tc_lvalue Delta e1 rho ∧ tc_expr Delta (Ecast e2 (typeof e1)) rho ∧
             (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) ∗ P rho)))
          (Sassign e1 e2)
          (normal_ret_assert (fun rho => mapsto sh (typeof e1) (eval_lvalue e1 rho)
                                           (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho))) ∗ P rho)).
Proof.
  intros.
  apply semax_pre with
    (fun rho : environ => ∃ v3: val,
      (▷ tc_lvalue Delta e1 rho ∧ ▷ tc_expr Delta (Ecast e2 (typeof e1)) rho) ∧
      ▷ (mapsto sh (typeof e1) (eval_lvalue e1 rho) v3 ∗ P rho)).
  { intros; iIntros "[% H]".
    rewrite /mapsto_ !bi.later_and assoc; eauto. }
  apply extract_exists_pre; intro v3.
  apply semax_straight_simple; auto.
  { apply _. }
  intros until f; intros TS TC Hcl Hge HGG.
  iIntros "(Hm & H & #?)".
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  rewrite (add_and (_ ∧ _) (▷ ⌜_⌝)).
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
    rewrite /tc_expr /typecheck_expr; fold typecheck_expr.
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
  + iIntros "!> !>".
    rewrite /tc_expr typecheck_expr_sound //.
    rewrite (bi.and_elim_r (tc_lvalue _ _ _)).
    iDestruct "H" as "(%Htc & F & Hmapsto & P)".
    rewrite /= /force_val1 in Htc; super_unfold_lift.
    subst; iPoseProof (mapsto_store with "[$Hm $Hmapsto]") as ">[$ ?]".
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
         (Delta : tycontext) (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : LiftEnviron mpred),
       (numeric_type (typeof e1) ∧ numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax Espec Delta
         (fun rho =>
           ▷ (tc_lvalue Delta e1 rho ∧ tc_expr Delta (Ecast e2 (typeof e1)) rho ∧
              ( (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) ∧ mapsto_ sh t2 (eval_lvalue e1 rho))
               * P rho)))
         (Sassign e1 e2)
         (normal_ret_assert
            (fun rho => (∃ v':val,
              andp (!! (decode_encode_val  (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho
))) ch ch' v'))
              (mapsto sh t2 (eval_lvalue e1 rho) v' * P rho)))).
Proof.
intros until P. intros NT AM0 AM' OK WS.
assert (SZ := decode_encode_val_size _ _ OK).
apply semax_pre with
  (fun rho : environ =>
   ∃ v3: val,
      ▷ tc_lvalue Delta e1 rho ∧ ▷ tc_expr Delta (Ecast e2 (typeof e1)) rho ∧
      ▷ ((mapsto sh (typeof e1) (eval_lvalue e1 rho) v3 ∧ mapsto sh t2 (eval_lvalue e1 rho) v3) * P rho)).
intro. apply andp_left2.
unfold mapsto_.
apply exp_right with Vundef.
repeat rewrite later_andp; auto.
apply extract_exists_pre; intro v3.
apply semax_straight_simple; auto.
intros jm jm1 Delta' ge ve te rho k F f TS [TC1 TC2] TC4 Hcl Hge Hage [H0 H0'] HGG'.
specialize (TC1 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
specialize (TC2 (m_phi jm1) (age_laterR (age_jm_phi Hage))).
assert (typecheck_environ Delta rho) as TC.
{ destruct TC4. eapply typecheck_environ_sub; eauto. }
pose proof TC1 as TC1'.
pose proof TC2 as TC2'.
apply (tc_lvalue_sub _ _ _ TS) in TC1'; [| auto].
apply (tc_expr_sub _ _ _ TS) in TC2'; [| auto].
unfold tc_expr in TC2, TC2'; simpl in TC2, TC2'.
rewrite denote_tc_assert_andp in TC2, TC2'.
simpl in TC2,TC2'; super_unfold_lift.
destruct TC2 as [TC2 TC3].
destruct TC2' as [TC2' TC3'].
apply later_sepcon2 in H0.
specialize (H0 _ (age_laterR (age_jm_phi Hage))).
pose proof I.
destruct H0 as [?w [?w [? [? [?w [?w [H3 [H4 H5]]]]]]]].
destruct H4 as [H4 H4x].
unfold mapsto in H4.
revert H4; case_eq (access_mode (typeof e1)); intros; try contradiction.
rename H2 into Hmode.
rewrite Hmode in AM0; inversion AM0; clear AM0; subst m.
destruct (eval_lvalue_relate _ _ _ _ _ e1 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC4)) as [b0 [i [He1 He1']]]; auto.
rewrite He1' in *.
destruct (join_assoc H3 (join_comm H0)) as [?w [H6 H7]].
destruct (type_is_volatile (typeof e1)) eqn:NONVOL; try contradiction.
rewrite if_true in H4 by auto.
assert (exists v, address_mapsto ch v
             sh
        (b0, Ptrofs.unsigned i) w1)
       by (destruct H4 as [[H4' H4] |[? [? ?]]]; eauto).
assert (H77: (align_chunk ch' | Ptrofs.unsigned i) /\ type_is_volatile t2 = false). {
  clear - H4x AM'.
  unfold mapsto  in H4x.
  rewrite AM' in H4x.
  destruct(type_is_volatile t2); try contradiction. split; auto.
  if_tac in H4x.
  destruct H4x as [[_ ?] | [_ ?]].
  rewrite address_mapsto_align in H0; destruct H0 as [_ H0]; simpl in H0; auto.
  destruct H0 as [? ?].
  rewrite address_mapsto_align in H0; destruct H0 as [_ H0]; simpl in H0; auto.
  destruct H4x as [[_ ?] _]. auto.
}
clear H4x.
clear v3 H4; destruct H2 as [v3 H4].

assert (H11': (res_predicates.address_mapsto ch v3 sh
        (b0, Ptrofs.unsigned i) * TT)%pred (m_phi jm1))
 by (exists w1; exists w3; split3; auto).
assert (H11: (res_predicates.address_mapsto ch v3  sh
        (b0, Ptrofs.unsigned i) * exactly w3)%pred (m_phi jm1)).
{ exists w1; exists w3; split3; auto.
  hnf; eauto. }
apply address_mapsto_can_store'
   with (ch':=ch') (v':=((force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))))) in H11;
  auto.
2: apply H77.
destruct H11 as [m' [H11 AM]].
exists (store_juicy_mem _ _ _ _ _ _ H11).
exists (te);  exists rho; split3; auto.
subst; simpl; auto.
rewrite level_store_juicy_mem. apply age_level; auto.
split; auto.
split.
split3; auto.
generalize (eval_expr_relate _ _ _ _ _ e2 jm1 HGG' Hge (guard_environ_e1 _ _ _ TC4)); intro.
spec H2; [ assumption | ].
rewrite <- (age_jm_dry Hage) in H2, He1.
econstructor; try eassumption.
unfold tc_lvalue in TC1. simpl in TC1.
auto.
instantiate (1:=(force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm)))).
rewrite (age_jm_dry Hage).
rewrite cop2_sem_cast'; auto.
2: eapply typecheck_expr_sound; eauto.
eapply cast_exists; eauto. destruct TC4; auto.
eapply Clight.assign_loc_value.
apply Hmode.
unfold tc_lvalue in TC1. simpl in TC1.
auto.
unfold Mem.storev.
simpl m_dry.
rewrite (age_jm_dry Hage).
auto.
apply (resource_decay_trans _ (nextblock (m_dry jm1)) _ (m_phi jm1)).
rewrite (age_jm_dry Hage); lia.
apply (age1_resource_decay _ _ Hage).
apply resource_nodecay_decay.
apply juicy_store_nodecay.
{intros.
 clear - H11' H2 WS.
 destruct H11' as [phi1 [phi2 [? [? ?]]]].
 destruct H0 as [bl [_ ?]]. specialize  (H0 (b0,z)).
 hnf in H0. rewrite if_true in H0 by (split; auto; lia).
 destruct H0. hnf in H0.
 apply (resource_at_join _ _ _ (b0,z)) in H.
 rewrite H0 in H.
 inv H; simpl; apply join_writable01 in RJ; auto;
 unfold perm_of_sh; rewrite if_true by auto; if_tac; constructor.
}
rewrite level_store_juicy_mem. split; [apply age_level; auto|].
simpl. unfold inflate_store; rewrite ghost_of_make_rmap.
apply age1_ghost_of, age_jm_phi; auto.
split.
2 : {
      eapply (corable_core _ (m_phi jm1)), pred_hereditary; eauto; [|apply age_jm_phi; auto].
      symmetry.
      forget (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))) as v.
      apply rmap_ext.
      do 2 rewrite level_core.
      rewrite <- level_juice_level_phi; rewrite level_store_juicy_mem.
      reflexivity.
      intro loc.
      unfold store_juicy_mem. simpl.
      rewrite <- core_resource_at. unfold inflate_store.
      rewrite resource_at_make_rmap. rewrite <- core_resource_at.
      case_eq (m_phi jm1 @ loc); intros; auto.
      destruct k0; simpl resource_fmap; repeat rewrite core_YES; auto.
      simpl.
      rewrite !ghost_of_core.
      unfold inflate_store; rewrite ghost_of_make_rmap; auto.
}

assert (TCv: tc_val (typeof e1)  (force_val (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho)))).
  eapply tc_val_sem_cast; eauto.
erewrite <- cop2_sem_cast' in *; try eassumption;
   try (eapply typecheck_expr_sound; eauto).
forget (force_val (Cop.sem_cast (eval_expr e2 rho) (typeof e2) (typeof e1) (m_dry jm1))) as v.
rewrite sepcon_comm.
destruct  (load_store_similar' _ _ _ _ _ _ H11 ch') as [v' [? ?]].
auto.
auto.
apply H77.
rewrite exp_sepcon1.
exists v'.
rewrite prop_true_andp by auto.
rewrite sepcon_assoc.
eapply sepcon_derives; try apply AM; auto.
unfold mapsto.
destruct TC4 as [TC4 _].

rewrite AM'.
rewrite He1'.
*
apply exp_left; intro v''.
apply prop_andp_left; intro.
pose proof (decode_encode_val_fun _ _  OK _ _ _  H8 H9).
subst v''; clear H9.
rewrite (proj2 H77).
rewrite if_true by auto.
apply orp_right1.
apply andp_right; auto.
intros ? ?.
simpl.
clear - H8 NT OK Hmode AM' TCv.
rewrite andb_true_iff in NT; destruct NT as [NT NT'].
destruct ch, ch'; try contradiction OK;
destruct (typeof e1) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv NT; inv Hmode;
destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ]; inv NT'; inv AM';
destruct v; simpl in H8; subst; try contradiction;
try apply I;
try (apply tc_val_Vundef in TCv; contradiction);
match goal with
 | |- context [Int.sign_ext ?n] => apply (sign_ext_range' n); compute; split; congruence
 | |- context [Int.zero_ext ?n] => apply (zero_ext_range' n); compute; split; congruence
 | |- _ => idtac
end.
*
intros ? ?.
clear - H9 H6 H1 H5.
destruct H9 as (? & H9 & ?).
destruct (nec_join2 H6 H9) as [w2' [w' [? [? ?]]]].
eapply pred_upclosed; eauto.
exists w2'; exists w'; split3; auto; eapply pred_nec_hereditary; eauto.
Qed.


End extensions.
