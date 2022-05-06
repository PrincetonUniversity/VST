Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.own.
Require Import VST.veric.fupd.
Import compcert.lib.Maps.

Import Ctypes Clight_core.

Local Open Scope nat_scope.
Local Open Scope pred.

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.

Definition jsafeN {Z} (Hspec : juicy_ext_spec Z) (ge: genv) :=
  @jsafeN_ genv _ _ genv_symb_injective 
               (cl_core_sem ge) Hspec ge.

Definition ext_compat {Z} (ora : Z) (w : rmap) :=
  joins (ghost_of w) (Some (ghost_PCM.ext_ref ora, NoneP) :: nil).

Lemma ext_compat_unage : forall {Z} (ora : Z) w w', age w w' ->
  ext_compat ora w' -> ext_compat ora w.
Proof.
  unfold ext_compat; intros.
  erewrite age1_ghost_of in H0 by eauto.
  eapply ext_join_unapprox; eauto.
Qed.

Lemma ext_compat_unext : forall {Z} (ora : Z) w w', ext_order w w' ->
  ext_compat ora w' -> ext_compat ora w.
Proof.
  unfold ext_compat; intros.
  apply rmap_order in H as (? & ? & ?).
  eapply join_sub_joins_trans; eauto.
Qed.

Inductive contx :=
| Stuck
| Cont: cont -> contx
| Ret: option val -> cont -> contx.


Definition assert_safe'_ 
     (Espec : OracleKind)
     (ge: genv) (f: function) (ve: env) (te: temp_env) (ctl: contx) (rho: environ) 
     (w : rmap) :=
       forall ora (jm:juicy_mem),
       ext_compat ora w ->
       rho = construct_rho (filter_genv ge) ve te ->
       m_phi jm = w ->
       forall (LW: level w > O),
       match ctl with
       | Stuck => jm_fupd ora Ensembles.Full_set Ensembles.Full_set (fun _ => False) jm
       | Cont (Kseq s ctl') => 
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f s ctl' ve te)) jm
       | Cont (Kloop1 body incr ctl') =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f Sskip (Kloop1 body incr ctl') ve te)) jm
       | Cont (Kloop2 body incr ctl') =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f (Sloop body incr) ctl' ve te)) jm
       | Cont (Kcall id' f' ve' te' k') => 
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)) jm
       | Cont Kstop =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f (Sreturn None) Kstop ve te)) jm
       | Cont _ => jm_fupd ora Ensembles.Full_set Ensembles.Full_set (fun _ => False) jm
       | Ret None ctl' =>
                jsafeN (@OK_spec Espec) ge ora (State f (Sreturn None) ctl' ve te) jm
       | Ret (Some v) ctl' => forall e v',
                  Clight.eval_expr ge ve te (m_dry jm) e v' ->
                  Cop.sem_cast v' (typeof e) (fn_return f) (m_dry jm) = Some v ->
              jsafeN (@OK_spec Espec) ge ora (State f (Sreturn (Some e)) ctl' ve te) jm
       end.
(* upd in assert_safe'_, everywhere except ret? *)

Notation fupd := (fupd Ensembles.Full_set Ensembles.Full_set).

Program Definition assert_safe
     (Espec : OracleKind) (ge: genv) (f: function) (ve: env) (te: temp_env) 
     (ctl: contx) : assert :=
  fun rho => assert_safe'_ (Espec : OracleKind) ge f ve te ctl rho.
Next Obligation.
  split; repeat intro.
   subst.
   destruct (oracle_unage _ _ H) as [jm0 [? ?]].
   specialize (H0 ora jm0).
   spec H0.
   { eapply ext_compat_unage; eauto. }
   specialize (H0 (eq_refl _) H3).
   spec H0. apply age_level in H. lia.
  subst.
  destruct ctl; [|destruct c|]; try (eapply jm_fupd_age; eauto).
  destruct o; intros; auto;
  eapply age_safe; eauto.
  rewrite (age_jm_dry H2) in *.
  eapply H0; eauto.

  subst. destruct (ext_ord_juicy_mem' _ _ H) as (? & Hd & Ha).
  destruct (proj1 (rmap_order _ _) H) as (Hl & Hr & Hg).
  destruct (juicy_mem_resource jm a) as (jm0 & Hjm & Hdry).
  { congruence. }
  specialize (H0 ora jm0).
   spec H0.
   { eapply ext_compat_unext; eauto. }
   specialize (H0 (eq_refl _) Hjm).
   spec H0. rewrite Hl; auto.
  subst.
  rewrite <- Hjm in *.
  assert (ext_order jm0 jm) by (split; auto; congruence).
  destruct ctl; [|destruct c|];
    try (eapply jm_fupd_ext; eauto; intros; eapply ext_safe; eauto).
  destruct o; intros; auto;
  eapply ext_safe; eauto.
  rewrite Hdry in *; eapply H0; eauto.
Qed.

Lemma assert_safe_derives : forall (Espec : OracleKind) (ge ge': genv) (f f': function) (ve ve': env) (te te': temp_env)
     (ctl ctl': contx) rho rho',
  (forall w ora (jm:juicy_mem),
       ext_compat ora w ->
       rho' = construct_rho (filter_genv ge') ve' te' ->
       m_phi jm = w ->
       forall (LW: level w > O), rho = construct_rho (filter_genv ge) ve te /\
      ((match ctl with
       | Stuck => jm_fupd ora Ensembles.Full_set Ensembles.Full_set (fun _ => False) jm
       | Cont (Kseq s ctl') => 
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f s ctl' ve te)) jm
       | Cont (Kloop1 body incr ctl') =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f Sskip (Kloop1 body incr ctl') ve te)) jm
       | Cont (Kloop2 body incr ctl') =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f (Sloop body incr) ctl' ve te)) jm
       | Cont (Kcall id' f' ve' te' k') => 
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)) jm
       | Cont Kstop =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge ora (State f (Sreturn None) Kstop ve te)) jm
       | Cont _ => jm_fupd ora Ensembles.Full_set Ensembles.Full_set (fun _ => False) jm
       | Ret None ctl' =>
                jsafeN (@OK_spec Espec) ge ora (State f (Sreturn None) ctl' ve te) jm
       | Ret (Some v) ctl' => forall e v',
                  Clight.eval_expr ge ve te (m_dry jm) e v' ->
                  Cop.sem_cast v' (typeof e) (fn_return f) (m_dry jm) = Some v ->
              jsafeN (@OK_spec Espec) ge ora (State f (Sreturn (Some e)) ctl' ve te) jm
       end) ->
       match ctl' with
       | Stuck => jm_fupd ora Ensembles.Full_set Ensembles.Full_set (fun _ => False) jm
       | Cont (Kseq s ctl') => 
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge' ora (State f' s ctl' ve' te')) jm
       | Cont (Kloop1 body incr ctl') =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge' ora (State f' Sskip (Kloop1 body incr ctl') ve' te')) jm
       | Cont (Kloop2 body incr ctl') =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge' ora (State f' (Sloop body incr) ctl' ve' te')) jm
       | Cont (Kcall id' f'' ve'' te'' k') => 
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge' ora (State f' (Sreturn None) (Kcall id' f'' ve'' te'' k') ve' te')) jm
       | Cont Kstop =>
             jm_fupd ora Ensembles.Full_set Ensembles.Full_set (jsafeN (@OK_spec Espec) ge' ora (State f' (Sreturn None) Kstop ve' te')) jm
       | Cont _ => jm_fupd ora Ensembles.Full_set Ensembles.Full_set (fun _ => False) jm
       | Ret None ctl' =>
                jsafeN (@OK_spec Espec) ge' ora (State f' (Sreturn None) ctl' ve' te') jm
       | Ret (Some v) ctl' => forall e v',
                  Clight.eval_expr ge' ve' te' (m_dry jm) e v' ->
                  Cop.sem_cast v' (typeof e) (fn_return f') (m_dry jm) = Some v ->
              jsafeN (@OK_spec Espec) ge' ora (State f' (Sreturn (Some e)) ctl' ve' te') jm
       end)) ->
  assert_safe Espec ge f ve te ctl rho |-- assert_safe Espec ge' f' ve' te' ctl' rho'.
Proof.
  repeat intro.
  edestruct H as [? Hsafe]; eauto.
  apply Hsafe, H0; auto.
Qed.

Definition list2opt {T: Type} (vl: list T) : option T :=
 match vl with nil => None | x::_ => Some x end.

Definition match_venv (ve: venviron) (vars: list (ident * type)) :=
 forall id, match ve id with Some (b,t) => In (id,t) vars | _ => True end.

Definition guard_environ (Delta: tycontext) (f: function) (rho: environ) : Prop :=
   typecheck_environ Delta rho /\
    match_venv (ve_of rho) (fn_vars f)
   /\ ret_type Delta = fn_return f.

Lemma guard_environ_e1:
   forall Delta f rho, guard_environ Delta f rho ->
     typecheck_environ Delta rho.
Proof. intros. destruct H; auto. Qed.

Definition _guard (Espec : OracleKind)
    (gx: genv) (Delta: tycontext) (f: function) (P : assert) (ctl: contx) : pred nat :=
     ALL tx : Clight.temp_env, ALL vx : env,
          let rho := construct_rho (filter_genv gx) vx tx in
          !! guard_environ Delta f rho
                  && P rho && funassert Delta rho
             >=> assert_safe Espec gx f vx tx ctl rho.

Definition guard (Espec : OracleKind)
    (gx: genv) (Delta: tycontext) f (P : assert)  (ctl: cont) : pred nat :=
  _guard Espec gx Delta f P (Cont ctl).

Fixpoint break_cont (k: cont) :=
match k with
| Kseq _ k' => break_cont k'
| Kloop1 _ _ k' => Cont k'
| Kloop2 _ _ k' => Cont k'
| Kswitch k' => Cont k'
| _ => Stuck
end.

Fixpoint continue_cont (k: cont) :=
match k with
| Kseq _ k' => continue_cont k'
| Kloop1 s1 s2 k' => Cont (Kseq s2 (Kloop2 s1 s2 k'))
| Kswitch k' => continue_cont k'
| _ => Stuck
end.

Definition exit_cont (ek: exitkind) (vl: option val) (k: cont) : contx :=
  match ek with
  | EK_normal => match vl with None => Cont k | Some _ => Stuck end
  | EK_break => break_cont k
  | EK_continue => continue_cont k
  | EK_return => Ret vl (call_cont k)
  end.

Definition rguard (Espec : OracleKind)
    (gx: genv) (Delta: tycontext) (f: function) (R : ret_assert) (ctl: cont) : pred nat :=
  ALL ek: exitkind, ALL vl: option val,
    _guard Espec gx Delta f (proj_ret_assert R ek vl)  (exit_cont ek vl ctl).

Record semaxArg :Type := SemaxArg {
 sa_cs: compspecs;
 sa_Delta: tycontext;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.

Program Definition ext_spec_pre' (Espec: OracleKind) (ef: external_function)
   (x': ext_spec_type OK_spec ef) (ge_s: injective_PTree block)
   (ts: list typ) (args: list val) (z: OK_ty) : pred juicy_mem :=
  fun jm => ext_compat z (m_phi jm) -> ext_spec_pre OK_spec ef x' ge_s ts args z jm.
Next Obligation.
Proof.
  split; repeat intro.
  - eapply ext_compat_unage in H1; [|eapply age_jm_phi; eauto].
    eapply JE_pre_hered; eauto.
  - eapply JE_pre_ext, H0; auto.
    destruct H; eapply ext_compat_unext; eauto.
Qed.

Program Definition ext_spec_post' (Espec: OracleKind)
   (ef: external_function) (x': ext_spec_type OK_spec ef) (ge_s: injective_PTree block)
   (tret: rettype) (ret: option val) (z: OK_ty) : pred juicy_mem :=
  exist (fun p => hereditary age p /\ hereditary ext_order p)
   (ext_spec_post OK_spec ef x' ge_s tret ret z)
     (conj (JE_post_hered _ _ _ _ _ _ _ _) (JE_post_ext _ _ _ _ _ _ _ _) ).

(*Definition juicy_mem_pred (P : pred rmap) (jm: juicy_mem): pred nat :=
     # diamond fashionM (exactly (m_phi jm) && P).*)

Definition make_ext_rval  (gx: genviron) (tret: rettype) (v: option val):=
  match tret with AST.Tvoid => mkEnviron gx (Map.empty _) (Map.empty _) 
 | _ => 
  match v with
  | Some v' =>  mkEnviron gx (Map.empty _)
                              (Map.set 1%positive v' (Map.empty _))
  | None => mkEnviron gx (Map.empty _) (Map.empty _)
  end end.

(*Program Definition if_ext_compat {Z} (z : Z) (P : pred juicy_mem) : pred juicy_mem :=
  fun jm => ext_compat z (m_phi jm) -> P jm.
Next Obligation.
Proof.
  unfold ext_compat; split; repeat intro.
  - eapply pred_hereditary, H0; auto.
    erewrite age1_ghost_of in H1 by (apply age1_juicy_mem_Some; eauto).
    apply ext_join_unapprox in H1; auto.
  - eapply pred_upclosed, H0; auto.
    rewrite rmap_order in H; destruct H as (_ & _ & _ & ?).
    eapply join_sub_joins_trans; eauto.
Qed.*)

Definition semax_external
  (Hspec: OracleKind) ef
  (A: TypeTree)
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred):
        pred nat :=
 ALL gx: genv, ALL Ts: list Type,
 ALL x: (dependent_type_functor_rec Ts A (pred rmap)),
   |>  ALL F: pred rmap, ALL ts: list typ,
   ALL args: list val,
   !!Val.has_type_list args (sig_args (ef_sig ef)) &&
   juicy_mem_op (P Ts x (filter_genv gx, args) * F) >=>
   EX x': ext_spec_type OK_spec ef,
    (ALL z:_, ext_spec_pre' Hspec ef x' (genv_symb_injective gx) ts args z) &&
     ! ALL tret: rettype, ALL ret: option val, ALL z': OK_ty,
      ext_spec_post' Hspec ef x' (genv_symb_injective gx) tret ret z' >=>
          juicy_mem_op (Q Ts x (make_ext_rval (filter_genv gx) tret ret) * F).

Lemma Forall2_implication {A B} (P Q:A -> B -> Prop) (PQ:forall a b, P a b -> Q a b):
  forall l t, Forall2 P l t -> Forall2 Q l t.
Proof. intros. induction H; constructor; auto. Qed.
Lemma has_type_list_Forall2: forall vals ts, Val.has_type_list vals ts <-> Forall2 Val.has_type vals ts.
Proof.
  induction vals; destruct ts; simpl; split; intros; trivial; try contradiction.
  inv H. inv H.
  destruct H. apply IHvals in H0. constructor; trivial. 
  inv H. apply IHvals in H5. split; trivial.
Qed.

Lemma semax_external_funspec_sub
  (DISABLE: False)
  {Espec argtypes rtype cc ef A1 P1 Q1 P1ne Q1ne A P Q Pne Qne}
  (Hsub: funspec_sub (mk_funspec (argtypes, rtype) cc A1 P1 Q1 P1ne Q1ne) 
                     (mk_funspec (argtypes, rtype) cc A P Q Pne Qne))
  (HSIG: ef_sig ef = 
         mksignature
                     (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc):
  @semax.semax_external Espec ef A1 P1 Q1 |-- @semax.semax_external Espec ef A P Q.
  (* This needs a fupd, but it's unclear how, since it's a pred nat. *)
Proof.
apply allp_derives; intros g.
apply allp_right; intros ts.
apply allp_right; intros x.
destruct Hsub as [_ H]; simpl in H.
intros n N m NM F typs vals y MY ? z YZ EZ [HT HP].
simpl in HP.
rewrite HSIG in HT; simpl in HT.
eapply sepcon_derives, fupd_frame_r in HP; [| intros ??; eapply H; split; eauto | apply derives_refl].
2: { clear -HT. 
  apply has_type_list_Forall2 in HT.
  eapply Forall2_implication; [ | apply HT]; auto.
}
clear H. (*
edestruct HP as (? & ? & z0 & ? & ? & ? & H); subst.
{ eexists. rewrite ghost_fmap_core. apply join_comm, core_unit. }
destruct H as [z1 [z2 [JZ [[ts1 [x1 [FRM [[z11 [z12 [JZ1 [H_FRM H_P1]]]] HQ]]]] Z2]]]].
specialize (N ts1 x1). apply join_comm in JZ1.
destruct (join_assoc JZ1 JZ) as [zz [JJ JJzz]]. apply join_comm in JJ.
destruct (juicy_mem_resource _ _ H2) as (jm0 & ? & ?); subst.
edestruct (N _ NM (sepcon F FRM) typs vals jm0) as [est [EST1 EST2]]; clear N; eauto.
{ apply necR_level in YZ. destruct EZ as [_ EZ%ext_level]. rewrite !level_juice_level_phi in *. lia. }
{ rewrite HSIG; simpl. split; trivial.
  exists z12, zz; split3. trivial. trivial.
  exists z2, z11; split3; trivial. }
exists est; split.
{ simpl. intros. apply EST1; auto. apply necR_trans with z; auto.*)
contradiction DISABLE.  (* 
    This lemma is not true as written because it needs a ghost-state
    update operator somewhere.  
*)
  (*rewrite age_to.necR_age_to_iff. admit.
simpl; intros.
destruct (EST2 b b0 b1 _ H _ H0 H1) as [u1 [u2 [JU [U1 U2]]]]; clear EST2.
destruct U2 as [w1 [w2 [JW [W1 W2]]]]. apply join_comm in JU.
destruct (join_assoc JW JU) as [v [JV V]]. apply join_comm in V.
exists v, w1; split3; trivial.
apply HQ; clear HQ; split.
+ simpl. destruct b,b0; reflexivity.
+ exists w2, u1; split3; trivial.*)
Qed.

Definition tc_option_val (sig: type) (ret: option val) :=
  match sig, ret with
    | Tvoid, _ => True
    | ty, Some v => tc_val ty v
    | _, _ => False
  end.

Fixpoint zip_with_tl {A : Type} (l1 : list A) (l2 : typelist) : list (A*type) :=
  match l1, l2 with
    | a::l1', Tcons b l2' => (a,b)::zip_with_tl l1' l2'
    | _, _ => nil
  end.

Definition withtype_empty (A: TypeTree) : Prop :=
  forall ts (x: dependent_type_functor_rec ts A (pred rmap)), False.
Definition believe_external (Hspec: OracleKind) (gx: genv) (v: val) (fsig: typesig) cc
  (A: TypeTree)
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred):
  pred nat :=
  match Genv.find_funct gx v with
  | Some (External ef sigargs sigret cc') =>
        !! (fsig = (typelist2list sigargs, sigret) /\ cc'=cc
           /\ ef_sig ef = mksignature
                           (typlist_of_typelist (typelist_of_type_list (fst fsig)))
                           (rettype_of_type (snd fsig)) cc
           /\ (ef_inline ef = false \/ withtype_empty A))
        && semax_external Hspec ef A P Q
        && ! (ALL ts: list Type,
              ALL x: dependent_type_functor_rec ts A (pred rmap),
              ALL ret:option val,
                Q ts x (make_ext_rval (filter_genv gx) (rettype_of_type (snd fsig)) ret)
                  && !!Builtins0.val_opt_has_rettype ret (rettype_of_type (snd fsig))
                  >=> !! tc_option_val sigret ret)
  | _ => FF
  end.

Lemma believe_external_funspec_sub {Espec gx v sig cc A P Q Pne Qne A' P' Q' Pne' Qne'}
      (Hsub: funspec_sub (mk_funspec sig cc A P Q Pne Qne)(mk_funspec sig cc A' P' Q' Pne' Qne') )
      (WTE: withtype_empty A -> withtype_empty A'):
      believe_external Espec gx v sig cc A P Q |-- believe_external Espec gx v sig cc A' P' Q'.
Proof.
  unfold believe_external; intros n N.
  destruct (Genv.find_funct gx v); trivial.
  destruct f; trivial. destruct sig as [argtypes rtype].
  destruct N as [[[N1a [N1b [N1c N1d]]] N2] N3].
  inv N1a. simpl in N1c; rewrite TTL2 in *; split.
+ split.
  - split3; trivial. split; trivial.
    destruct N1d; [ left; trivial | right; auto].
  - eapply semax_external_funspec_sub; try eassumption.
     admit.
+ simpl; intros. simpl in N3. simpl in Hsub.
  destruct Hsub as [_ Hsub].
  specialize (Hsub b b0).
Abort.

Definition fn_funsig (f: function) : funsig := (fn_params f, fn_return f).

Definition var_sizes_ok (cenv: composite_env) (vars: list (ident*type)) :=
   Forall (fun var : ident * type => @sizeof cenv (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type) (rho: environ): mpred :=
  !! (sizeof (snd idt) <= Ptrofs.max_unsigned)%Z &&
  (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) : assert :=
  fold_right (fun P Q rho => P rho * Q rho) (fun rho => emp)
     (map (fun idt => var_block' Share.top cenv idt) (Clight.fn_vars f)).

Definition believe_internal_ CS
  (semax:semaxArg -> pred nat)
  (gx: genv) (Delta: tycontext) v (fsig: typesig) cc (A: TypeTree)
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred) : pred nat :=
  let ce := (@cenv_cs CS) in
  (EX b: block, EX f: function,
   let specparams := fst fsig in 
   let fparams := fn_params f in
   prop (v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ specparams = map snd fparams
                 /\ snd fsig = snd (fn_funsig f)
                 /\ f.(fn_callconv) = cc)
  &&
   ALL Delta':tycontext, ALL CS':compspecs,
   imp (prop (forall f, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta')))
     (imp (prop (cenv_sub (@cenv_cs CS) (@cenv_cs CS'))) 
      (ALL ts: list Type,
       ALL x : dependent_type_functor_rec ts A (pred rmap),
        |> semax (SemaxArg CS' (func_tycontext' f Delta')
                         (fun rho => (bind_args (f.(fn_params)) (P ts x) rho 
                                              * stackframe_of' (@cenv_cs CS') f rho)
                                        && funassert (func_tycontext' f Delta') rho)
                          (f.(fn_body))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) 
              (stackframe_of' (@cenv_cs CS') f)))) )).

Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Definition claims (ge: genv) (Delta: tycontext) v fsig cc A P Q : Prop :=
  exists id HP HQ, (glob_specs Delta)!id = Some (mk_funspec fsig cc A P Q HP HQ) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero.

Definition believepred CS (Espec: OracleKind) (semax: semaxArg -> pred nat)
              (Delta: tycontext) (gx: genv)  (Delta': tycontext) : pred nat :=
  ALL v:val, ALL fsig: typesig, ALL cc: calling_convention,
  ALL A: TypeTree,
  ALL P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred,
  ALL Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred,
       !! claims gx Delta' v fsig cc A P Q  -->
      (believe_external Espec gx v fsig cc A P Q
        || believe_internal_ CS semax gx Delta v fsig cc A P Q).

Definition semax_ (Espec: OracleKind)
       (semax: semaxArg -> pred nat) (a: semaxArg) : pred nat :=
 match a with SemaxArg CS Delta P c R =>
  ALL gx: genv, ALL Delta': tycontext,ALL CS':compspecs,
       !! (tycontext_sub Delta Delta' 
            /\ cenv_sub (@cenv_cs CS) (@cenv_cs CS') 
            /\ cenv_sub (@cenv_cs CS') (genv_cenv gx)) -->
      (believepred CS' Espec semax Delta' gx Delta') -->
     ALL k: cont, ALL F: assert, ALL f:function,
       (!! (closed_wrt_modvars c F) &&
              rguard Espec gx Delta' f (frame_ret_assert R F) k) -->
        guard Espec gx Delta' f (fun rho => F rho * P rho) (Kseq c k)
  end.

Definition semax'  {CS: compspecs} (Espec: OracleKind) Delta P c R : pred nat :=
     HORec (semax_ Espec) (SemaxArg CS Delta P c R).

Definition believe_internal {CS: compspecs} (Espec:  OracleKind)
  (gx: genv) (Delta: tycontext) v (fsig: typesig) cc (A: TypeTree)
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): pred nat :=
  let ce := @cenv_cs CS in
  (EX b: block, EX f: function,
   let specparams := fst fsig in 
   let fparams := fn_params f in
   prop (v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ specparams = map snd fparams
                 /\ snd fsig = snd (fn_funsig f)
                 /\ f.(fn_callconv) = cc)
  && 
    ALL Delta':tycontext,ALL CS':compspecs,
     imp (prop (forall f, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta')))
      (imp (prop (cenv_sub (@cenv_cs CS) (@cenv_cs CS')))
       (ALL ts: list Type,
     ALL x : dependent_type_functor_rec ts A (pred rmap),
     |> @semax' CS' Espec (func_tycontext' f Delta')
                                (fun rho => (bind_args (f.(fn_params)) (P ts x) rho * stackframe_of' (@cenv_cs CS') f rho)
                                             && funassert (func_tycontext' f Delta') rho)
                               (f.(fn_body))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of' (@cenv_cs CS') f))))).

Definition believe {CS: compspecs} (Espec:OracleKind)
              (Delta: tycontext) (gx: genv) (Delta': tycontext): pred nat :=
  ALL v:val, ALL fsig: typesig, ALL cc: calling_convention,
  ALL A: TypeTree,
  ALL P: (forall ts, dependent_type_functor_rec ts (ArgsTT A) (pred rmap)),
  ALL Q: (forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)),
       !! claims gx Delta' v fsig cc A P Q  -->
      (believe_external Espec gx v fsig cc A P Q
        || believe_internal Espec gx Delta v fsig cc A P Q).

Lemma semax_fold_unfold : forall {CS: compspecs} (Espec : OracleKind),
  semax' Espec = fun Delta P c R =>
  ALL gx: genv, ALL Delta': tycontext,ALL CS':compspecs,
       !! (tycontext_sub Delta Delta'
           /\ cenv_sub (@cenv_cs CS) (@cenv_cs CS')
           /\ cenv_sub (@cenv_cs CS') (genv_cenv gx)) -->
       @believe CS' Espec Delta' gx Delta' -->
     ALL k: cont, ALL F: assert, ALL f: function,
        (!! (closed_wrt_modvars c F) && rguard Espec gx Delta' f (frame_ret_assert R F) k) -->
        guard Espec gx Delta' f (fun rho => F rho * P rho) (Kseq c k).
Proof.
intros ? ?.
extensionality G P. extensionality c R.
unfold semax'.
pattern (HORec (semax_ Espec)) at 1; rewrite HORec_fold_unfold.
reflexivity.
apply prove_HOcontractive.
intros.
unfold semax_.
clear.
sub_unfold.
do 3 (apply subp_allp; intros).
apply subp_imp; [auto with contractive | ].
apply subp_imp; [ | auto 50 with contractive].
apply subp_allp; intros.
apply subp_allp; intros.
apply subp_allp; intros.
apply subp_allp; intros.
apply subp_allp; intros.
apply subp_allp; intros.
apply subp_imp; intros; [ auto 50 with contractive | ].
apply subp_orp; [ auto 50 with contractive | ].
apply subp_exp; intros.
apply subp_exp; intros.
auto 50 with contractive.
Qed.

Lemma semax'_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Espec Delta P c R:
      @semax' CS Espec Delta P c R |-- @semax' CS' Espec Delta P c R.
Proof.
  rewrite 2 semax_fold_unfold.
  apply allp_derives; intros gx.
  apply allp_derives; intros Delta'.
  apply allp_derives; intros CS''.
  apply imp_derives; auto.
  intros ? [TC [M1 M2]].
  split. apply TC. split; trivial. intros i. eapply sub_option_trans. apply CSUB. apply M1.
Qed.
Lemma semax'_cssub {CS CS'} (CSUB: cspecs_sub  CS CS') Espec Delta P c R:
      @semax' CS Espec Delta P c R |-- @semax' CS' Espec Delta P c R.
Proof.
  destruct CSUB as [CSUB _].
  apply (@semax'_cenv_sub _ _ CSUB).
Qed.

Opaque semax'.

Definition semax {CS: compspecs} (Espec: OracleKind) (Delta: tycontext) P c Q :=
  forall n, semax' Espec Delta P c Q n.

Lemma any_level_pred_nat: forall P: pred nat, (forall n, P n) <-> (TT |-- P).
Proof.
  intros.
  split; intros.
  + hnf; intros; auto.
  + hnf in H; auto.
Qed.

Lemma fash_TT: forall {A} {agA: ageable A} {EO: Ext_ord A}, @unfash A agA EO TT = TT.
Proof.
intros.
apply pred_ext; intros ? ?; apply I.
Qed.

Lemma allp_andp: 
  forall {A} {NA: ageable A} {EO: Ext_ord A} {B: Type} (b0: B) (P: B -> pred A) (Q: pred A),
   (allp P && Q = allp (fun x => P x && Q))%pred.
Proof.
intros.
apply pred_ext.
intros ? [? ?] b. split; auto.
intros ? ?.
split.
intro b. apply (H b).
apply (H b0).
Qed.

Lemma unfash_prop_imp:
  forall {A} {agA: ageable A} {EO: Ext_ord A} (P: Prop) (Q: pred nat),
  (@unfash _ agA _ (prop P --> Q) = prop P --> @unfash _ agA _ Q)%pred.
Proof.
intros.
apply pred_ext; repeat intro.
simpl in H; eapply H in H2; eauto.
eapply pred_upclosed, pred_nec_hereditary; eauto.
simpl in H.
specialize (H a _ (necR_refl _)  (ext_refl _) H2).
eapply pred_upclosed, pred_nec_hereditary; eauto.
Qed.

Import age_to.

Lemma unfash_imp:
  forall {A} {NA: ageable A} {EO: Ext_ord A} (P Q: pred nat),
  (@unfash A _ _ (P --> Q) = (@unfash A _ _ P) --> @unfash A _ _ Q)%pred.
Proof.
intros.
apply pred_ext; repeat intro.
apply ext_level in H1.
simpl in H; eapply H in H2; [| eapply necR_level', H0 | ..]; auto.
simpl in *; subst a''.
specialize (H (age_to a' a) _ (age_to_necR _ _) (ext_refl _)).
apply necR_level in H0.
rewrite level_age_to in H; auto.
Qed.

Lemma unfash_andp:  forall {A} {agA: ageable A} {EO: Ext_ord A} (P Q: pred nat),
  (@unfash A agA _ (andp P Q) = andp (@unfash A agA _ P) (@unfash A agA _ Q)).
Proof.
intros.
apply pred_ext.
intros ? ?.
destruct H.
split; auto.
intros ? [? ?].
split; auto.
Qed.

Lemma andp_imp_e':
  forall (A : Type) (agA : ageable A) (EO: Ext_ord A) (P Q : pred A),
   P && (P --> Q) |-- P && Q.
Proof.
intros.
apply andp_right.
apply andp_left1; auto.
intros ? [? ?].
eapply H0; auto.
Qed.

Lemma unfash_fash:
  forall (A : Type) (agA : ageable A) (EO : Ext_ord A) (P : pred A),
   unfash (fash P) |-- P.
Proof.
  intros.
  unfold fash, unfash.
  simpl.
  hnf; simpl; intros.
  apply (H a).
  lia.
Qed.

Lemma imp_imp:
  forall (A : Type) (agA : ageable A) (EO : Ext_ord A) (P Q R: pred A),
    P --> (Q --> R) = P && Q --> R.
Proof.
  intros.
  apply pred_ext.
  + apply imp_andp_adjoint.
    rewrite <- andp_assoc.
    apply imp_andp_adjoint.
    rewrite andp_comm.
    eapply derives_trans; [apply andp_imp_e' | apply andp_left2].
    auto.
  + rewrite <- !imp_andp_adjoint.
    rewrite andp_assoc.
    rewrite imp_andp_adjoint.
    auto.
Qed.

Lemma imp_allp:
  forall B (A : Type) (agA : ageable A) (EO : Ext_ord A) (P: pred A) (Q: B -> pred A),
    P --> allp Q  = ALL x: B, P --> Q x.
Proof.
  intros.
  apply pred_ext.
  + apply allp_right; intros x.
    rewrite <- imp_andp_adjoint, andp_comm.
    eapply derives_trans; [apply andp_imp_e' |].
    apply andp_left2.
    apply (allp_left _ x).
    auto.
  + rewrite <- imp_andp_adjoint.
    apply allp_right; intros x.
    rewrite imp_andp_adjoint.
    apply (allp_left _ x).
    auto.
Qed.

Lemma fash_prop: forall P: Prop,
  fash (!! P: pred rmap) = !! P.
Proof.
  intros.
  apply pred_ext; unfold fash; hnf; simpl; intros.
  + destruct (ex_level a) as [r ?].
    apply (H r).
    lia.
  + auto.
Qed.

Lemma fash_unfash:
  forall (P : pred nat),
   fash (unfash P: pred rmap) = P.
Proof.
  intros.
  unfold fash, unfash.
  apply pred_ext; hnf; simpl; intros.
  + destruct (ex_level a) as [r ?].
    specialize (H r).
    rewrite H0 in H.
    apply H; lia.
  + eapply pred_nec_hereditary; [| eassumption].
    rewrite nec_nat; lia.
Qed.

Lemma prop_true_imp:
  forall (P: Prop) (Q: pred rmap),
    P -> !! P --> Q = Q.
Proof.
  intros.
  apply pred_ext.
  + rewrite <- (True_andp_eq P (!! P --> Q)) by auto.
    eapply derives_trans; [apply andp_imp_e' |].
    apply andp_left2; auto.
  + apply imp_andp_adjoint.
    apply andp_left1.
    auto.
Qed.

Section believe_monotonicity.
Context {CS: compspecs} {Espec: OracleKind}.

Lemma guard_mono gx Delta Gamma f (P Q:assert) ctl
  (GD1: forall e te, typecheck_environ Gamma (construct_rho (filter_genv gx) e te) ->
                     typecheck_environ Delta (construct_rho (filter_genv gx) e te))
  (GD2: ret_type Delta = ret_type Gamma)
  (GD3: forall e te, Q (construct_rho (filter_genv gx) e te) |--
                        P (construct_rho (filter_genv gx) e te))
  (GD4: forall e te, (funassert Gamma (construct_rho (filter_genv gx) e te)) |--
                     (funassert Delta (construct_rho (filter_genv gx) e te))):
  @guard Espec gx Delta f P ctl |--
  @guard Espec gx Gamma f Q ctl.
Proof. intros n G te e r R ? a' A' ? [[[X1 X2] X3] X4].
  eapply G; eauto.
  split; [split; [split;[auto | rewrite GD2; trivial] | apply GD3; trivial] | apply GD4; trivial].
Qed.

Lemma claims_antimono gx Gamma v sig cc A P Q Gamma' 
  (SUB: forall id spec, (glob_specs Gamma') ! id = Some spec ->
                        (glob_specs Gamma) ! id = Some spec)
  (CL: claims gx Gamma' v sig cc A P Q):
  claims gx Gamma v sig cc A P Q.
Proof. destruct CL as[id [HP [HQ [Hid X]]]]; exists id, HP, HQ; split; auto. Qed.

Lemma believe_antimonoR gx Delta Gamma Gamma'
  (DG1: forall id spec, (glob_specs Gamma') ! id = Some spec ->
                        (glob_specs Gamma) ! id = Some spec):
  @believe CS Espec Delta gx Gamma |-- @believe CS Espec Delta gx Gamma'.
Proof. intros n B v sig cc A P Q ? k nec ? CL. eapply B; eauto. eapply claims_antimono; eauto. Qed.

Lemma cenv_sub_complete_legal_cosu_type cenv1 cenv2 (CSUB: cenv_sub cenv1 cenv2): forall t,
    @composite_compute.complete_legal_cosu_type cenv1 t = true ->
    @composite_compute.complete_legal_cosu_type cenv2 t = true.
Proof.
  induction t; simpl; intros; auto. 
  + specialize (CSUB i). red in CSUB.
    destruct (cenv1 ! i); [rewrite CSUB; trivial | inv H].
  + specialize (CSUB i). red in CSUB.
    destruct (cenv1 ! i); [rewrite CSUB; trivial | inv H].
Qed.

Lemma complete_type_cenv_sub {ce ce'} (C: cenv_sub ce ce') t (T:complete_type ce t = true):
  complete_type ce' t = true.
Proof. apply (complete_type_stable ce ce'); trivial. intros. specialize (C id). rewrite H in C; apply C.
Qed.
Lemma complete_type_cspecs_sub {cs cs'} (C: cspecs_sub cs cs') t (T:complete_type (@cenv_cs cs) t = true):
  complete_type (@cenv_cs cs') t = true.
Proof. destruct C. apply (complete_type_cenv_sub H _ T). Qed.

Lemma believe_internal_cenv_sub {CS'} gx Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) k
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS'))
  (BI: @believe_internal CS Espec gx Delta v sig cc A P Q k):
  @believe_internal CS' Espec gx Delta' v sig cc A P Q k.
Proof. destruct BI as [b [f [Hv X]]]. 
  exists b, f; split; [clear X | clear Hv].
  - simpl; simpl in Hv. intuition.
    + eapply Forall_impl. 2: apply H0. simpl; intros.
       apply (complete_type_cenv_sub CSUB); auto.
    + clear - CSUB H0 H4. forget (fn_vars f) as vars. induction vars.
      constructor. inv H4. inv H0.  specialize (IHvars H5 H3).
      constructor; [ rewrite (cenv_sub_sizeof CSUB); trivial | apply IHvars].
  - intros PSI CS'' ? w W ? HSUB ? u WU ? HU ts x. eapply X; eauto.
    + simpl; intros. eapply tycontext_sub_trans. 2: apply HSUB. eauto.
    + clear - CSUB HU; simpl. apply (cenv_sub_trans CSUB HU).
Qed.
Lemma believe_internal_mono {CS'} gx Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) k
  (CSUB: cspecs_sub  CS CS')
  (BI: @believe_internal CS Espec gx Delta v sig cc A P Q k):
  @believe_internal CS' Espec gx Delta' v sig cc A P Q k.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_internal_cenv_sub CS'). apply SUB. apply CSUB. apply BI.
Qed. 

Lemma believe_cenv_sub_L {CS'} gx Delta Delta' Gamma
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')):
  @believe CS Espec Delta gx Gamma |-- @believe CS' Espec Delta' gx Gamma.
Proof.
 intros n B; repeat intro.
 edestruct B; eauto.
+ left; trivial.
+ right. clear -SUB CSUB H H2.
  apply (@believe_internal_cenv_sub CS' gx Delta); eauto.
Qed.
Lemma believe_monoL {CS'} gx Delta Delta' Gamma
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cspecs_sub  CS CS'):
  @believe CS Espec Delta gx Gamma |-- @believe CS' Espec Delta' gx Gamma.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_cenv_sub_L CS'). apply SUB. apply CSUB.
Qed.

Lemma believe_internal__mono sem gx Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) k
  (BI: believe_internal_ CS sem gx Delta v sig cc A P Q k):
(believe_internal_ CS sem gx Delta' v sig cc A P Q) k.
Proof. destruct BI as [b [f [Hv X]]].
  exists b, f; split; [trivial | clear Hv].
  intros PSI CS' ? w W ? HSUB u WU HU ts x. eapply X; eauto.
  simpl; intros. eapply tycontext_sub_trans. 2: apply HSUB. eauto.
Qed.
End believe_monotonicity.

Lemma semax__mono {CS} Espec Delta Delta'
  (SUB: tycontext_sub Delta Delta') sem P c R:
  derives (@semax_ Espec sem {| sa_cs := CS; sa_Delta := Delta; sa_P := P; sa_c := c; sa_R := R |})
      (@semax_ Espec sem {| sa_cs:=CS; sa_Delta := Delta'; sa_P := P; sa_c := c; sa_R := R |}).
Proof. unfold semax_.
  repeat (apply allp_derives; intros).
  eapply imp_derives; auto.
  intros ? [HSUB HCS]; split; auto.
  eapply tycontext_sub_trans; eauto.
Qed.

Lemma semax_mono {CS} Espec Delta Delta' P Q
  (SUB: tycontext_sub Delta Delta') c:
  @semax' CS Espec Delta P c Q |--
   @semax' CS Espec Delta' P c Q.
Proof.
rewrite semax_fold_unfold in *.
  repeat (apply allp_derives; intros).
  eapply imp_derives; auto.
  intros ? [HSUB HCS]; split; auto.
  eapply tycontext_sub_trans; eauto.
Qed.

Lemma semax_mono_box {CS} Espec Delta Delta' P Q
  (SUB: tycontext_sub Delta Delta') c w
  (BI: @box nat ag_nat _ (@laterM nat ag_nat _)
          (@semax' CS Espec Delta P c Q) w):
  @box nat ag_nat _ (@laterM nat ag_nat _)
          (@semax' CS Espec Delta' P c Q) w.
Proof. eapply box_positive; [ clear BI | apply BI].
intros a Hyp.
eapply semax_mono; eassumption.
Qed.

(*In fact, the following specialization suffices in semax_prog*)
Lemma semax_mono' {CS} Espec Delta Delta' P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) c w f
  (BI: @box nat ag_nat _ (@laterM nat ag_nat _)
          (@semax' CS Espec (func_tycontext' f Delta) P c Q) w):
  @box nat ag_nat _ (@laterM nat ag_nat _)
          (@semax' CS Espec (func_tycontext' f Delta') P c Q) w.
Proof. eapply semax_mono_box. eauto. eassumption. Qed.

Lemma semax_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Espec Delta P c R:
      @semax CS Espec Delta P c R -> @semax CS' Espec Delta P c R.
Proof.
  intros. intros n. apply (semax'_cenv_sub CSUB); trivial. 
Qed.
Lemma semax_cssub {CS CS'} (CSUB: cspecs_sub  CS CS') Espec Delta P c R:
      @semax CS Espec Delta P c R -> @semax CS' Espec Delta P c R.
Proof.
  intros. intros n. apply (semax'_cssub CSUB); trivial. 
Qed.
