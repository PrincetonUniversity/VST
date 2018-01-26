Require Import VST.floyd.proofauto.
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Require Export mc_reify.reify.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
Require Import mc_reify.typ_eq.
Require Import mc_reify.func_defs.
Require Import mc_reify.rtac_base.

Lemma semax_set_localD:
    forall temp var ret gt
      id (e: Clight.expr) ty gs P T1 T2 R Post v,
  forall {Espec: OracleKind},
      typeof_temp (mk_tycontext temp var ret gt gs) id = Some ty ->
      is_neutral_cast (implicit_deref (typeof e)) ty = true ->
      msubst_eval_LR T1 T2 e RRRR = Some v ->
      tc_expr_b_norho (mk_tycontext temp var ret gt gs) e = true ->
      assertD P (localD (PTree.set id v T1) T2) R = Post ->
      semax (mk_tycontext temp var ret gt gs) (|> (assertD P (localD T1 T2) R))
        (Sset id e)
          (normal_ret_assert Post).
Proof.
  intros.
  subst Post.
  eapply semax_PTree_set; eauto.
  intro rho.
  apply tc_expr_b_sound with (rho := rho) in H2.
  normalize.
Qed.

Definition set_lemma (temp : PTree.t (type * bool)) (var : PTree.t type)
         (ret : type) (gt : PTree.t type) (id : ident)
         (e : Clight.expr) (ty : type): my_lemma.
reify_lemma reify_vst (semax_set_localD temp var ret gt id e ty).
Defined.

Lemma tc_LR_b_sound: forall Delta P T1 T2 R e1 lr p,
  msubst_eval_LR T1 T2 e1 lr = Some p ->
  assertD P (localD T1 T2) R |-- !! (isptr p) ->
  tc_LR_b_norho Delta e1 lr = true ->
  assertD P (localD T1 T2) R |-- local (tc_LR Delta e1 lr).
Proof.
  intros.
  pose proof msubst_eval_LR_eq P T1 T2 nil (map liftx R) e1 p _ H.
  change (PROPx P (LOCALx (LocalD T1 T2 []) (SEPx (map liftx R)))) with
    (assertD P (localD T1 T2) R) in H2.
  destruct lr; simpl tc_LR in *; simpl tc_LR_b_norho in *; simpl eval_LR in *.
  + rewrite (add_andp _ _ H2).
    rewrite (add_andp _ _ H0).
    rewrite andp_assoc.
    apply andp_left2.
    unfold local, lift1; intro rho; normalize.
    apply tc_lvalue_b'_sound; auto.
  + rewrite (add_andp _ _ H2).
    apply andp_left2.
    unfold local, lift1; intro rho; normalize.
    apply tc_expr_b_sound; auto.
Qed.

Lemma nth_error_prop:
  forall P T1 T2 R Rn (n : nat) S,
  assertD P (localD T1 T2) [Rn] |-- !! S ->
  nth_error R n = Some Rn ->
  assertD P (localD T1 T2) R |-- !! S.
Proof.
  intros.
  unfold assertD in *.
  unfold map in H.
  eapply derives_trans.
  + eapply nth_error_SEP_sepcon_TT with (n := n); [exact H |].
    apply map_nth_error, H0.
  + unfold TT.
    intro rho.
    simpl.
    rewrite @sepcon_prop_prop.
    normalize.
Qed.

Lemma semax_load_localD:
forall (temp : PTree.t (type * bool)) (var : PTree.t type)
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr)
     (efs : list efield) (tts : list type)
     (e : type_id_env) (lr : LLRR) (n: nat)
     (gs : PTree.t funspec) (sh : Share.t)
     (P : list Prop) (T1 : PTree.t val) (T2 : PTree.t (type * val))
     (R : list mpred) (Post : environ -> mpred)
     (gfs : list gfield)
     (p p' v : val) (v' : reptype t_root)
     (Espec : OracleKind),
  typeof_temp (mk_tycontext temp var ret gt gs) id = Some t ->
  is_neutral_cast (typeof e0) t = true ->
  msubst_efield_denote T1 T2 efs = Some gfs ->
  legal_nested_efield e t_root e1 gfs tts lr = true ->
  tc_efield_b_norho (mk_tycontext temp var ret gt gs) efs = true ->

  msubst_eval_LR T1 T2 e1 lr = Some p ->
  tc_LR_b_norho (mk_tycontext temp var ret gt gs) e1 lr = true ->
  (@eq (option mpred)) (nth_error R n) (Some (data_at sh t_root v' p')) ->
  (forall rho,
      !!(tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |-- !! (p = p')) ->
  proj_val t_root gfs v' = v ->
  assertD P (localD (PTree.set id v T1) T2) R = Post ->
  nested_efield e1 efs tts = e0 ->

  (forall rho,
      !! (tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |--
        !! (tc_val (typeof e0) v) &&
        !! (legal_nested_field t_root gfs)) ->
 semax (mk_tycontext temp var ret gt gs) (|> assertD P (localD T1 T2) R)
        (Sset id e0)
          (normal_ret_assert Post).
Proof.
  intros.
  subst Post e0.
  eapply semax_extract_later_prop'.
  Focus 1. {
    rewrite <- insert_local.
    exact H7.
  } Unfocus.
  intro; subst; clear H7.
  eapply semax_PTree_load with (gfs2 := gfs) (gfs0 := nil) (gfs1 := gfs) (t_root0 := t_root) (sh0 := sh);  eauto.
  + rewrite app_nil_r; reflexivity.
  + unfold assertD, localD, LocalD; simpl; intros. entailer!.
  + reflexivity.
  + repeat apply andp_right.
    - apply andp_left2. eapply tc_LR_b_sound; [eauto | | eauto].
      eapply nth_error_prop with (n := n); eauto.
      rewrite data_at_isptr.
      unfold assertD; entailer!.
    - intros rho.
      apply (derives_trans _ _ _ (H11 rho)).
      normalize.
    - intro rho.
      unfold local, lift1; simpl; apply prop_right.
      apply tc_efield_b_sound; auto.
  + intros rho.
    apply (derives_trans _ _ _ (H11 rho)).
    normalize.
Qed.

Definition load_lemma (temp : PTree.t (type * bool)) (var : PTree.t type)
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr)
    (efs: list efield) (tts : list type) (e : type_id_env) (lr : LLRR)
    (n: nat): my_lemma.
reify_lemma reify_vst (semax_load_localD temp var ret gt id t t_root e0 e1 efs tts e lr n).
Defined.

Lemma semax_store_localD:
    forall (temp : PTree.t (type * bool)) (var : PTree.t type)
     (ret : type) (gt : PTree.t type) (t t_root : type) (e0 e1 e2: Clight.expr)
     (efs : list efield) (tts : list type)
     (e : type_id_env) (lr : LLRR) (n: nat)
     sh P T1 T2 R gs Post
      (gfs: list gfield)
      (p p': val) (v0: val) (v': reptype t_root),
  forall {Espec: OracleKind},
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t = true ->
      tc_LR_b_norho (mk_tycontext temp var ret gt gs) e1 lr = true ->
      tc_LR_b_norho (mk_tycontext temp var ret gt gs) (Ecast e2 (typeof (nested_efield e1 efs tts))) RRRR = true ->
      tc_efield_b_norho (mk_tycontext temp var ret gt gs) efs = true ->
      msubst_efield_denote T1 T2 efs = Some gfs ->
      msubst_eval_LR T1 T2 e1 lr = Some p ->
      msubst_eval_LR T1 T2 (Ecast e2 t) RRRR = Some v0 ->
      legal_nested_efield e t_root e1 gfs tts lr = true ->

      (@eq (option mpred)) (nth_error R n) (Some (data_at sh t_root v' p')) ->
  (forall rho,
      !!(tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |-- !! (p = p')) ->
  (forall rho,
      !! (tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |--
        !! (legal_nested_field t_root gfs)) ->
  (assertD P (localD T1 T2)
                  (replace_nth n R
                    (data_at sh t_root
                      (upd_val t_root gfs v' v0) p))) = Post -> (* need to add replace_nth *)
      writable_share sh ->
  nested_efield e1 efs tts = e0 ->

      semax (mk_tycontext temp var ret gt gs) (|>assertD P (localD T1 T2) R)
        (Sassign e0 e2)
          (normal_ret_assert Post).
Proof.
  intros.
  assert (Post = assertD P (localD T1 T2)
          (replace_nth n R
             (field_at sh t_root []
                (upd_reptype (nested_field_type2 t_root nil) gfs v'
                   (valinject _ v0)) p))); [| clear H11].
  Focus 1. {
    unfold upd_val in H11.
    rewrite <- data_at_field_at.
    subst Post.
    f_equal.
  } Unfocus.
  subst Post e0.
  eapply semax_extract_later_prop'.
  Focus 1. {
    rewrite <- insert_local.
    exact H9.
  } Unfocus.
  intro; subst; clear H9.
  unfold upd_val.
  eapply semax_PTree_store with (gfs2 := gfs) (gfs0 := nil) (gfs1 := gfs) (t_root0 := t_root) (sh0 := sh);  eauto.
  + rewrite app_nil_r; reflexivity.
  + unfold assertD, localD, LocalD; simpl; intros. entailer!.
  + repeat apply andp_right.
    - apply andp_left2. eapply tc_LR_b_sound; [eauto | | eauto].
      eapply nth_error_prop with (n := n); eauto.
      rewrite data_at_isptr.
      unfold assertD; entailer!.
    - intro rho.
      apply prop_right.
      eapply tc_expr_b_sound; auto.
    - intro rho.
      unfold local, lift1; simpl; apply prop_right.
      apply tc_efield_b_sound; auto.
Qed.

Definition store_lemma (temp : PTree.t (type * bool)) (var : PTree.t type)
     (ret : type) (gt : PTree.t type) (t t_root : type) (e0 e1 e2: Clight.expr)
     (efs : list efield) (tts : list type)
     (e : type_id_env) (lr : LLRR) (n: nat): my_lemma.
reify_lemma reify_vst (semax_store_localD temp var ret gt t t_root e0 e1 e2 efs tts e lr n).
Defined.

(* Print store_lemma. *)

Section tbled.
Variable n : nat.
Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.


Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Let ExprVar_expr := @ExprVariables.ExprVar_expr typ func.
Existing Instance ExprVar_expr.

Existing Instance MA.

Existing Instance rtac_base.MentionsAnyOk.

Lemma load_store_sound_aux:
  forall t_root, (@funcAs typ func RType_typ
              (func_defs.RSym_sym tbl)
              (@inr
                 (sum
                    (sum SymEnv.func
                       (ModularFunc.ILogicFunc.ilfunc
                       typ))
                    (BILogicFunc.bilfunc typ))
                 func' (Sep (fdata_at t_root)))
              (tyArr tyshare
                 (tyArr
                    (reptyp t_root)
                    (tyArr tyval tympred))) =
            Some
              (fun (sh : share) (rt : typD (reptyp t_root)) (v : val) =>
               data_at sh t_root (reptyp_reptype t_root rt) v)).
Proof.
  intros.
  unfold funcAs; simpl.
  assert (forall pl: (fun t0 : typ =>
    {tyArr t0 (tyArr (reptyp t_root) (tyArr tyval tympred)) =
     tyArr tyshare (tyArr (reptyp t_root) (tyArr tyval tympred))} +
    {tyArr t0 (tyArr (reptyp t_root) (tyArr tyval tympred)) <>
     tyArr tyshare (tyArr (reptyp t_root) (tyArr tyval tympred))})
     tyshare, pl = left eq_refl).
  Focus 1. {
    intros.
    destruct pl; [f_equal; apply proof_irr | congruence].
  } Unfocus.
  match goal with
  | [ |- context [match (match ?e with _ => _ end) with _ => _ end] ] => rewrite (H e)
  end.
  unfold Rcast; simpl.
  reflexivity.
Qed.

Lemma APPLY_sound_store_lemma: forall (temp : PTree.t (type * bool)) (var : PTree.t type)
  (ret : type) (gt : PTree.t type) (t t_root : type)
  (e0 e1 e2 : Clight.expr) (efs : list efield) (tts : list type)
  (e : type_id_env) (lr : LLRR) (n : nat),
  rtac_sound (EAPPLY typ func (store_lemma temp var ret gt t t_root e0 e1 e2 efs tts e lr n)).
Proof.
  intros.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env, Lemma.lemmaD'. simpl.
    unfold exprD'_typ0. simpl.
    unfold exprD'. simpl.

    rewrite (load_store_sound_aux t_root); simpl.
    assert (@funcAs typ func RType_typ
                (func_defs.RSym_sym tbl)
                (@inr
                (sum
                (sum SymEnv.func
                (ILogicFunc.ilfunc typ))
                (BILogicFunc.bilfunc typ))
                func'
                (Sep (fupd_val t_root)))
                (tyArr
                (tylist tygfield)
                (tyArr
                (reptyp t_root)
                (tyArr tyval
                (reptyp t_root))))
      = Some
         (fun (gfs : list gfield) (v : typD (reptyp t_root)) (v0 : val) =>
          reptype_reptyp t_root (upd_val t_root gfs (reptyp_reptype t_root v) v0))).
    Focus 1. {
      intros.
      unfold funcAs.
      simpl.
      assert (forall pl: (fun t0 : typ =>
        {tyArr t0 (tyArr (reptyp t_root) (tyArr tyval (reptyp t_root))) =
         tyArr (tylist tygfield)
           (tyArr (reptyp t_root) (tyArr tyval (reptyp t_root)))} +
        {tyArr t0 (tyArr (reptyp t_root) (tyArr tyval (reptyp t_root))) <>
         tyArr (tylist tygfield)
           (tyArr (reptyp t_root) (tyArr tyval (reptyp t_root)))})
         (tylist tygfield), pl = left eq_refl).
      Focus 1. {
        intros.
        destruct pl; [f_equal; apply proof_irr | congruence].
      } Unfocus.
      match goal with
      | [ |- context [match (match ?e with _ => _ end) with _ => _ end] ] => rewrite (H e)
      end.
      unfold Rcast; simpl.
      reflexivity.
    } Unfocus.
    rewrite H. simpl. clear H.
    intros.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    unfold ModularFunc.ILogicFunc.typ2_cast_quant, ModularFunc.ILogicFunc.typ2_cast_bin in *; simpl in *.
    eapply semax_store_localD; eauto.
    rewrite reptyp_reptype_reptype_reptyp in H11.
    exact H11.
Qed.

Lemma APPLY_sound_load_lemma: forall (temp : PTree.t (type * bool)) (var : PTree.t type)
  (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type)
  (e0 e1 : Clight.expr) (efs : list efield) (tts : list type)
  (e : type_id_env) (lr : LLRR) (n : nat),
  rtac_sound (EAPPLY typ func (load_lemma temp var ret gt id t t_root e0 e1 efs tts e lr n)).
Proof.
  intros.
  apply EAPPLY_sound; auto with typeclass_instances.
  + apply APPLY_condition1.
  + apply APPLY_condition2.
  + unfold Lemma.lemmaD, split_env, Lemma.lemmaD'. simpl.
(* Set Printing Depth 200. *)
    unfold exprD'_typ0. simpl.
    unfold exprD'. simpl.
    rewrite (load_store_sound_aux t_root); simpl.
    assert (exprT_GetVAs []
                  [tyOracleKind;
                reptyp t_root; tyval; tyval; tyval;
                tylist tygfield;
                tyArr tyenviron tympred;
                tylist tympred;
                typtree (typrod tyc_type tyval);
                typtree tyval;
                tylist typrop; tyshare;
                typtree tyfunspec] 1
                (reptyp t_root) = Some
      (fun (_ : HList.hlist typD [])
         (vs : HList.hlist typD
                [tyOracleKind; reptyp t_root; tyval; tyval; tyval;
                tylist tygfield; tyArr tyenviron tympred;
                tylist tympred; typtree (typrod tyc_type tyval);
                typtree tyval; tylist typrop; tyshare;
                typtree tyfunspec]) => HList.hlist_hd (HList.hlist_tl vs))).
    Focus 1. {
      intros.
      unfold exprT_GetVAs. simpl.
      destruct (typ_eq_dec (reptyp t_root) (reptyp t_root)); [ |congruence].
      assert (e2 = eq_refl) by apply proof_irr.
      subst.
      unfold Rcast_val, Rcast; simpl.
    reflexivity.
    } Unfocus.
    rewrite H. simpl; clear H.
    intros.
    unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
    unfold ModularFunc.ILogicFunc.typ2_cast_quant, ModularFunc.ILogicFunc.typ2_cast_bin in *; simpl in *.
    eapply semax_load_localD; eauto.
Qed.

End tbled.
