Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.own.

Import Ctypes Clight_new.

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
  @jsafeN_ genv _ _ genv_symb_injective (*(genv_symb := fun ge: genv => Genv.genv_symb ge)*)
               (cl_core_sem ge) Hspec ge.

Lemma ext_join_approx : forall {Z} (z : Z) n g,
  joins g (Some (ghost_PCM.ext_ref z, NoneP) :: nil) ->
  joins (ghost_fmap (approx n) (approx n) g) (Some (ghost_PCM.ext_ref z, NoneP) :: nil).
Proof.
  intros.
  destruct H.
  change (Some (ghost_PCM.ext_ref z, NoneP) :: nil) with
    (ghost_fmap (approx n) (approx n) (Some (ghost_PCM.ext_ref z, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
Qed.

Lemma ext_join_unapprox : forall {Z} (z : Z) n g,
  joins (ghost_fmap (approx n) (approx n) g) (Some (ghost_PCM.ext_ref z, NoneP) :: nil) ->
  joins g (Some (ghost_PCM.ext_ref z, NoneP) :: nil).
Proof.
  intros.
  destruct H as (g' & J).
  destruct g; [eexists; constructor|].
  inv J.
  exists (a3 :: g); repeat constructor.
  destruct o; inv H4; constructor.
  destruct p; inv H1; constructor; simpl in *; auto.
  destruct p; simpl in *.
  inv H0.
  inv H1.
  inj_pair_tac.
  constructor; auto.
  unfold NoneP; f_equal; auto.
Qed.

Program Definition ext_compat {Z} (ora : Z) : mpred :=
  fun w => joins (ghost_of w) (Some (ghost_PCM.ext_ref ora, NoneP) :: nil).
Next Obligation.
Proof.
  repeat intro.
  erewrite age1_ghost_of by eauto.
  apply ext_join_approx; auto.
Qed.

Program Definition assert_safe
     (Espec : OracleKind)
     (ge: genv) ve te (ctl: cont) : assert :=
  fun rho => bupd (fun w => forall ora (jm:juicy_mem),
       ext_compat ora w ->
       rho = construct_rho (filter_genv ge) ve te ->
       m_phi jm = w ->
             jsafeN (@OK_spec Espec) ge (level w) ora (State ve te ctl) jm).
 Next Obligation.
  intro; intros.
  subst.
   destruct (oracle_unage _ _ H) as [jm0 [? ?]].
   subst.
   specialize (H0 ora jm0); spec H0.
   { erewrite age1_ghost_of in H1 by eauto.
      eapply ext_join_unapprox; eauto. }
   specialize (H0 (eq_refl _) (eq_refl _)).
   forget (State ve te ctl) as c. clear H ve te ctl.
  change (level (m_phi jm)) with (level jm).
  change (level (m_phi jm0)) with (level jm0) in H0.
  eapply age_safe; eauto.
Qed.

Definition list2opt {T: Type} (vl: list T) : option T :=
 match vl with nil => None | x::_ => Some x end.

Definition match_venv (ve: venviron) (vars: list (ident * type)) :=
 forall id, match ve id with Some (b,t) => In (id,t) vars | _ => True end.

Definition guard_environ (Delta: tycontext) (f: option function) (rho: environ) : Prop :=
   typecheck_environ Delta rho /\
  match f with
  | Some f' => match_venv (ve_of rho) (fn_vars f')
                /\ ret_type Delta = fn_return f'
  | None => True
  end.

Lemma guard_environ_e1:
   forall Delta f rho, guard_environ Delta f rho ->
     typecheck_environ Delta rho.
Proof. intros. destruct H; auto. Qed.

Definition _guard (Espec : OracleKind)
    (gx: genv) (Delta: tycontext) (P : assert) (f: option function) (ctl: cont) : pred nat :=
     ALL tx : Clight.temp_env, ALL vx : env,
          let rho := construct_rho (filter_genv gx) vx tx in
          !! guard_environ Delta f rho
                  && P rho && funassert Delta rho
             >=> assert_safe Espec gx vx tx ctl rho.

Definition guard (Espec : OracleKind)
    (gx: genv) (Delta: tycontext) (P : assert)  (ctl: cont) : pred nat :=
  _guard Espec gx Delta P (current_function ctl) ctl.

Definition zap_fn_return (f: function) : function :=
 mkfunction Tvoid f.(fn_callconv) f.(fn_params) f.(fn_vars) f.(fn_temps) f.(fn_body).

Definition exit_cont (ek: exitkind) (vl: option val) (k: cont) : cont :=
  match ek with
  | EK_normal => k
  | EK_break => break_cont k
  | EK_continue => continue_cont k
  | EK_return =>
         match vl, call_cont k with
         | Some v, Kcall (Some x) f ve te :: k' =>
                    Kseq (Sreturn None) :: Kcall None (zap_fn_return f) ve (PTree.set x v te) :: k'
         | _,_ => Kseq (Sreturn None) :: call_cont k
         end
   end.

Definition rguard (Espec : OracleKind)
    (gx: genv) (Delta: tycontext)  (R : ret_assert) (ctl: cont) : pred nat :=
  ALL ek: exitkind, ALL vl: option val,
    _guard Espec gx Delta (proj_ret_assert R ek vl) (current_function ctl) (exit_cont ek vl ctl).

Record semaxArg :Type := SemaxArg {
 sa_cs: compspecs;
 sa_Delta: tycontext;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.

Definition ext_spec_pre' (Espec: OracleKind) (ef: external_function)
   (x': ext_spec_type OK_spec ef) (ge_s: injective_PTree block)
   (ts: list typ) (args: list val) (z: OK_ty) : pred juicy_mem :=
  exist (hereditary age)
     (ext_spec_pre OK_spec ef x' ge_s ts args z)
     (JE_pre_hered _ _ _ _ _ _ _ _).

Program Definition ext_spec_post' (Espec: OracleKind)
   (ef: external_function) (x': ext_spec_type OK_spec ef) (ge_s: injective_PTree block)
   (tret: option typ) (ret: option val) (z: OK_ty) : pred juicy_mem :=
  exist (hereditary age)
   (ext_spec_post OK_spec ef x' ge_s tret ret z)
     (JE_post_hered _ _ _ _ _ _ _ _).

Definition juicy_mem_pred (P : pred rmap) (jm: juicy_mem): pred nat :=
     # diamond fashionM (exactly (m_phi jm) && P).

Fixpoint make_ext_args (gx: genviron) (ids: list ident) (vl: list val)  :=
  match ids, vl with
  | id::ids', v::vl' => env_set (make_ext_args gx ids' vl') id v
  | _, v::vl' => env_set (make_ext_args gx ids vl') 1%positive v
  | _, _ => mkEnviron gx (Map.empty _) (Map.empty _)
 end.

Definition make_ext_rval  (gx: genviron) (v: option val):=
  match v with
  | Some v' =>  mkEnviron gx (Map.empty _)
                              (Map.set 1%positive v' (Map.empty _))
  | None => mkEnviron gx (Map.empty _) (Map.empty _)
  end.

Definition semax_external
  (Hspec: OracleKind) (ids: list ident) ef
  (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)):
        pred nat :=
 ALL gx: genv, ALL Ts: list Type,
 ALL x: (dependent_type_functor_rec Ts A (pred rmap)),
   |>  ALL F: pred rmap, ALL ts: list typ,
   ALL args: list val,
   !!Val.has_type_list args (sig_args (ef_sig ef)) &&
   juicy_mem_op (P Ts x (make_ext_args (filter_genv gx) ids args) * F) >=>
   EX x': ext_spec_type OK_spec ef,
    (ALL z:_, juicy_mem_op (ext_compat z) -->
     ext_spec_pre' Hspec ef x' (genv_symb_injective gx) ts args z) &&
     ! ALL tret: option typ, ALL ret: option val, ALL z': OK_ty,
      ext_spec_post' Hspec ef x' (genv_symb_injective gx) tret ret z' >=>
          juicy_mem_op (Q Ts x (make_ext_rval (filter_genv gx) ret) * F).

Definition tc_option_val (sig: type) (ret: option val) :=
  match sig, ret with
    | Tvoid, None => True
    | Tvoid, Some _ => False
    | ty, Some v => tc_val ty v
    | _, _ => False
  end.

Fixpoint zip_with_tl {A : Type} (l1 : list A) (l2 : typelist) : list (A*type) :=
  match l1, l2 with
    | a::l1', Tcons b l2' => (a,b)::zip_with_tl l1' l2'
    | _, _ => nil
  end.

Definition believe_external (Hspec: OracleKind) (gx: genv) (v: val) (fsig: funsig) cc
  (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)):
  pred nat :=
  match Genv.find_funct gx v with
  | Some (External ef sigargs sigret cc') =>
      let ids := fst (split (fst fsig)) in
        !! (fsig = (zip_with_tl ids sigargs, sigret) /\ cc'=cc
           /\ ef_sig ef = mksignature
                           (typlist_of_typelist (type_of_params (fst fsig)))
                           (opttyp_of_type (snd fsig)) cc
           /\ length (typelist2list sigargs)=length ids)
        && semax_external Hspec ids ef A P Q
        && ! (ALL ts: list Type,
              ALL x: dependent_type_functor_rec ts A (pred rmap),
              ALL ret:option val,
                Q ts x (make_ext_rval (filter_genv gx) ret)
                  && !!has_opttyp ret (opttyp_of_type (snd fsig))
                  >=> !! tc_option_val sigret ret)
  | _ => FF
  end.

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
  (gx: genv) (Delta: tycontext) v (fsig: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) : pred nat :=
  let ce := (@cenv_cs CS) in
  (EX b: block, EX f: function,
   prop (v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ (map snd (fst fsig) = map snd (fst (fn_funsig f))
                      /\ snd fsig = snd (fn_funsig f)
                      /\ list_norepet (map fst (fst fsig)))
                 /\ f.(fn_callconv) = cc)
  &&
   ALL Delta':tycontext, ALL CS':compspecs,
   imp (prop (forall f, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta')))
     (imp (prop (cenv_sub (@cenv_cs CS) (@cenv_cs CS'))) 
      (ALL ts: list Type,
       ALL x : dependent_type_functor_rec ts A (pred rmap),
        |> semax (SemaxArg CS' (func_tycontext' f Delta')
                         (fun rho => (bind_args (fst fsig) (f.(fn_params)) (P ts x) rho 
                                              * stackframe_of' (@cenv_cs CS') f rho)
                                        && funassert (func_tycontext' f Delta') rho)
                          (Ssequence f.(fn_body) (Sreturn None))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) 
              (stackframe_of' (@cenv_cs CS') f)))) )).

Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Definition claims (ge: genv) (Delta: tycontext) v fsig cc A P Q : Prop :=
  exists id HP HQ, (glob_specs Delta)!id = Some (mk_funspec fsig cc A P Q HP HQ) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero.

Definition believepred CS (Espec: OracleKind) (semax: semaxArg -> pred nat)
              (Delta: tycontext) (gx: genv)  (Delta': tycontext) : pred nat :=
  ALL v:val, ALL fsig: funsig, ALL cc: calling_convention,
  ALL A: TypeTree,
  ALL P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred,
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
     ALL k: cont, ALL F: assert,
       (!! (closed_wrt_modvars c F) &&
              rguard Espec gx Delta' (frame_ret_assert R F) k) -->
        guard Espec gx Delta' (fun rho => F rho * P rho) (Kseq c :: k)
  end.

Definition semax'  {CS: compspecs} (Espec: OracleKind) Delta P c R : pred nat :=
     HORec (semax_ Espec) (SemaxArg CS Delta P c R).

Definition believe_internal {CS: compspecs} (Espec:  OracleKind)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) : pred nat :=
  let ce := @cenv_cs CS in
  (EX b: block, EX f: function,
   prop (v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ (map snd (fst fsig) = map snd (fst (fn_funsig f))
                      /\ snd fsig = snd (fn_funsig f)
                      /\ list_norepet (map fst (fst fsig)))
                 /\ f.(fn_callconv) = cc)
  && 
    ALL Delta':tycontext,ALL CS':compspecs,
     imp (prop (forall f, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta')))
      (imp (prop (cenv_sub (@cenv_cs CS) (@cenv_cs CS')))
                                               
       (ALL ts: list Type,
     ALL x : dependent_type_functor_rec ts A (pred rmap),
     |> @semax' CS' Espec (func_tycontext' f Delta')
                                (fun rho => (bind_args (fst fsig) (f.(fn_params)) (P ts x) rho * stackframe_of' (@cenv_cs CS') f rho)
                                             && funassert (func_tycontext' f Delta') rho)
                               (Ssequence f.(fn_body) (Sreturn None))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of' (@cenv_cs CS') f))))).

Definition believe {CS: compspecs} (Espec:OracleKind)
              (Delta: tycontext) (gx: genv) (Delta': tycontext): pred nat :=
  ALL v:val, ALL fsig: funsig, ALL cc: calling_convention,
  ALL A: TypeTree,
  ALL P: (forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)),
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
     ALL k: cont, ALL F: assert,
        (!! (closed_wrt_modvars c F) && rguard Espec gx Delta' (frame_ret_assert R F) k) -->
        guard Espec gx Delta' (fun rho => F rho * P rho) (Kseq c :: k).
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
  intros w W m WM [TC [M1 M2]] u MU U. specialize (W m WM).
  assert (X: (!! (tycontext_sub Delta Delta' /\ cenv_sub (@cenv_cs CS) (@cenv_cs CS'') /\ cenv_sub (@cenv_cs CS'') gx)) m).
  { clear W U. split. apply TC. split; trivial. intros i. eapply sub_option_trans. apply CSUB. apply M1. }
  apply (W X); trivial.
Qed.
Lemma semax'_cssub {CS CS'} (CSUB: cspecs_sub  CS CS') Espec Delta P c R:
      @semax' CS Espec Delta P c R |-- @semax' CS' Espec Delta P c R.
Proof.
  destruct CSUB as [CSUB _].
  apply (@semax'_cenv_sub _ _ CSUB).
Qed.

Definition weakest_pre {CS: compspecs} (Espec: OracleKind) (Delta: tycontext) c Q: assert :=
  fun rho: environ =>
  ALL gx: genv, ALL Delta': tycontext,
       !! (tycontext_sub Delta Delta' /\ genv_cenv gx = cenv_cs) -->
       unfash (believe Espec Delta' gx Delta') -->
     ALL k: cont, ALL F: assert,
        unfash (!! (closed_wrt_modvars c F) && rguard Espec gx Delta' (frame_ret_assert Q F) k) -->
        ALL tx : Clight.temp_env, ALL vx : env,
          (!! (rho = construct_rho (filter_genv gx) vx tx)) -->
          ((!! guard_environ Delta' (current_function (Kseq c :: k)) rho && funassert Delta' rho) -->
             (F rho -* assert_safe Espec gx vx tx (Kseq c :: k) rho)).

Opaque semax'.

Definition semax {CS: compspecs} (Espec: OracleKind) (Delta: tycontext) P c Q :=
  forall n, semax' Espec Delta P c Q n.

Lemma any_level_pred_nat: forall P: pred nat, (forall n, P n) <-> TT |-- P.
Proof.
  intros.
  split; intros.
  + hnf; intros; auto.
  + hnf in H; auto.
Qed.

Lemma semax_weakest_pre_aux: forall {A: Type} (P: pred nat) (Q R: A -> pred rmap),
  P = fash (ALL x: A, Q x --> R x) ->
  (TT |-- P <-> forall x, Q x |-- R x).
Proof.
  intros.
  assert (TT |-- ALL x: A, Q x --> R x <-> (forall x : A, Q x |-- R x)).
  + split; intros.
    - rewrite <- (TT_and (Q x)).
      rewrite imp_andp_adjoint.
      eapply derives_trans; [exact H0 |].
      apply (allp_left _ x); intros.
      auto.
    - apply allp_right; intros.
      rewrite <- imp_andp_adjoint.
      rewrite (TT_and (Q v)).
      auto.
  + rewrite <- H0, H.
    clear; forget (ALL x : A , Q x --> R x) as P; clear.
    split; intros.
    - unfold fash in H.
      hnf in H |- *.
      intros; simpl in H.
      eapply H; auto.
    - unfold fash.
      hnf in H |- *.
      intros; simpl.
      intros.
      apply H.
      auto.
Qed.

(* Copied from semax_switch. *)

Lemma unfash_allp:  forall {A} {agA: ageable A} {B} (f: B -> pred nat),
  @unfash _ agA (allp f) = allp (fun x:B => unfash (f x)).
Proof.
intros.
apply pred_ext.
intros ? ? ?.
specialize (H b). auto.
repeat intro. apply (H b).
Qed.

Lemma fash_TT: forall {A} {agA: ageable A}, @unfash A agA TT = TT.
Proof.
intros.
apply pred_ext; intros ? ?; apply I.
Qed.

Lemma allp_andp: 
  forall {A} {NA: ageable A} {B: Type} (b0: B) (P: B -> pred A) (Q: pred A),
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
  forall {A} {agA: ageable A} (P: Prop) (Q: pred nat),
  (@unfash _ agA (prop P --> Q) = prop P --> @unfash _ agA Q)%pred.
Proof.
intros.
apply pred_ext; repeat intro.
apply H; auto. apply necR_level'; auto.
hnf in H.
specialize (H a (necR_refl _) H1).
eapply pred_nec_hereditary; try apply H0.
apply H.
Qed.

Import age_to.

Lemma unfash_imp:
  forall {A} {NA: ageable A} (P Q: pred nat),
  (@unfash A _ (P --> Q) = (@unfash A _ P) --> @unfash A _ Q)%pred.
Proof.
intros.
apply pred_ext; repeat intro.
apply H; auto. apply necR_level'; auto.
specialize (H (age_to a' a)).
spec H.
apply age_to_necR.
spec H.
do 3 red. 
rewrite level_age_to; auto.
apply necR_level in H0. apply H0.
do 3 red in H.
rewrite level_age_to in H; auto.
apply necR_level in H0.
apply H0.
Qed.

Lemma unfash_andp:  forall {A} {agA: ageable A} (P Q: pred nat),
  (@unfash A agA (andp P Q) = andp (@unfash A agA P) (@unfash A agA Q)).
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
  forall (A : Type) (agA : ageable A) (P Q : pred A),
   P && (P --> Q) |-- P && Q.
Proof.
intros.
apply andp_right.
apply andp_left1; auto.
intros ? [? ?].
eapply H0; auto.
Qed.

(* End copied from semax_switch. *)

Lemma unfash_fash:
  forall (A : Type) (agA : ageable A) (P : pred A),
   unfash (fash P) |-- P.
Proof.
  intros.
  unfold fash, unfash.
  simpl.
  hnf; simpl; intros.
  apply (H a).
  omega.
Qed.

Lemma imp_imp:
  forall (A : Type) (agA : ageable A) (P Q R: pred A),
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
  forall B (A : Type) (agA : ageable A) (P: pred A) (Q: B -> pred A),
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
    omega.
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
    apply H; omega.
  + eapply pred_nec_hereditary; [| eassumption].
    rewrite nec_nat; omega.
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

Lemma corable_unfash:
  forall (A : Type) (JA : Join A) (PA : Perm_alg A) (SA : Sep_alg A) (agA : ageable A) 
    (AgeA : Age_alg A) (P : pred nat), corable (! P).
Proof.
  intros.
  unfold unfash; simpl.
  hnf; simpl; intros.
  rewrite level_core.
  auto.
Qed.

Section believe_monotonicity.
Context {CS: compspecs} {Espec: OracleKind}.

Lemma guard_mono gx Delta Gamma (P Q:assert) ctl
  (GD1: forall e te, typecheck_environ Gamma (construct_rho (filter_genv gx) e te) ->
                     typecheck_environ Delta (construct_rho (filter_genv gx) e te))
  (GD2: ret_type Delta = ret_type Gamma)
  (GD3: forall e te, Q (construct_rho (filter_genv gx) e te) |--
                        P (construct_rho (filter_genv gx) e te))
  (GD4: forall e te, (funassert Gamma (construct_rho (filter_genv gx) e te)) |--
                     (funassert Delta (construct_rho (filter_genv gx) e te))):
  @guard Espec gx Delta P ctl |--
  @guard Espec gx Gamma Q ctl.
Proof. intros n G te e r R a' A' [[[X1 X2] X3] X4].
  apply (G te e r R a' A').
  split; [split; [split;[auto | rewrite GD2; trivial] | apply GD3; trivial] | apply GD4; trivial].
Qed.
(*
Lemma claims_antimono gx Gamma v sig cc A P Q Gamma' 
  (SUB: forall i spec, (glob_specs Gamma') ! i = Some spec ->
        exists spec', (glob_specs Gamma) ! i = Some spec' /\ funspec_sub spec spec')
  (CL: claims gx Gamma' v sig cc A P Q):
  claims gx Gamma v sig cc A P Q.
Proof. destruct CL as [i [HP [HQ [Hi X]]]].
  destruct (SUB _ _ Hi) as [spec' [Spec' FSsub]]; clear SUB.
  destruct spec'. 
  assert (f = sig /\ c=cc). { destruct FSsub as [? [? _]]; subst; auto. }
  destruct H; subst f c. red.
  exists i, P_ne, HQ. ; split; auto. Qed.
*)
Lemma claims_antimono gx Gamma v sig cc A P Q Gamma' 
  (SUB: forall id spec, (glob_specs Gamma') ! id = Some spec ->
                        (glob_specs Gamma) ! id = Some spec)
  (CL: claims gx Gamma' v sig cc A P Q):
  claims gx Gamma v sig cc A P Q.
Proof. destruct CL as[id [HP [HQ [Hid X]]]]; exists id, HP, HQ; split; auto. Qed.

Lemma believe_antimonoR' V gx Delta Gamma Gamma'
  (DG1: forall i spec', (glob_specs (nofunc_tycontext V Gamma')) ! i = Some spec' ->
        exists spec, (glob_specs (nofunc_tycontext V Gamma)) ! i = Some spec /\ funspec_sub spec spec'):
  @believe CS Espec (nofunc_tycontext V Delta) gx (nofunc_tycontext V Gamma) |--
  @believe CS Espec (nofunc_tycontext V Delta) gx (nofunc_tycontext V Gamma').
Admitted.
(*Proof. intros n B v sig cc A' P' Q' k nec CL. 
  remember (nofunc_tycontext V Gamma') as G'.
  remember (nofunc_tycontext V Gamma) as G.
  red in CL. red in CL. destruct CL as [i [HP' [HQ' [Entry' Hi]]]].
  destruct (DG1 _ _ Entry') as [spec [Entry Sub]].
  destruct spec.
  assert (f=sig) by eapply Sub. subst f.
  assert (c=cc) by eapply Sub. subst c.
  specialize (B v sig cc A P Q k nec).
  assert (CL: claims gx G v sig cc A P Q).
  { exists i, P_ne, Q_ne; split; trivial. }
  specialize (B CL). destruct B as [Bext | Bint]; [left | right].
  + admit.
  + (*clear - HeqG HeqG' DG1 Sub Bint. *)destruct Bint as [b [f [Pr B]]].
    destruct sig as [f_argtypes f_rettype].
    exists b, f. split. apply Pr. simpl in Pr.
    destruct Pr as [PrA [PrB [PrC [PrD [PrE [PrF [[PrG [PrH PrI]] PrJ]]]]]]].
    subst cc f_rettype v.

    intros Delta' cs' p KP XX q PQ CSUB ts TS u QU.
    specialize (B Delta' cs' p KP XX q PQ CSUB).
    destruct Sub as [_ [_ Sub]]. specialize (Sub ts TS). simpl in Sub.
    rewrite semax_fold_unfold. intros ge D CS' uu Huu ZZ kk UUKK BD knt FRM pp KKPP CLOSED.
    simpl in XX, ZZ.

    intros te e rm RM rm' RM' [[WW1 WW2] WW3]. 
    unfold funsig_tycontext in Sub.
    remember (construct_rho (filter_genv ge) e te) as rho.
    destruct WW2 as [m1 [m2 [JM [HFRM MM]]]].
    destruct MM as [[m2_1 [m2_2 [JM2 [BindARGS STACKframe]]]] TYC]. simpl fst in BindARGS.
    destruct BindARGS as [BArgs1 BArgs2]. 
    hnf in BArgs2. (*Locate bind_args. -- shouldn't the ve' whose existence
      BArgs2 asserts be SOMEHOME contrained?? Maybe it should be related to (fn_vars f) ? *)
    destruct BindARGS as [BArgs1 BArgs2]. as [MM21a MM21b]; simpl in MM21a. red in MM21a. simpl in MM21b. simpl in Sub.
    destruct MM21b as [ve [xxx [XXX1 XXX2]]]. 
    destruct (Sub (mkEnviron (ge_of rho) ve xxx) m2_1) as [ts' [yyy [FRM2 [HP0 PostPred]]]]; clear Sub.
    { simpl in WW1; destruct WW1 as [WW1a WW1b]. 
      split; trivial. subst rho. simpl. simpl in XXX1.
      red. red. simpl. split3; red; intros.
      + clear - ZZ PrG PrI MM21a XXX1 H WW1a. red in WW1a; simpl in WW1a.
        forget (fn_params f) as f_params. destruct ZZ as [ZZ1 ZZ2]. unfold func_tycontext' in ZZ1. 
        red in ZZ1; simpl in ZZ1.
        generalize dependent f_params.
        induction f_argtypes; simpl; intros.
        - destruct f_params; simpl in *; [ rewrite PTree.gempty in H; discriminate | inv PrG].
        - destruct f_params; simpl in *; inv PrG.
          rewrite PTree.gsspec in H. destruct (peq id (fst a)). 
          * inv H. specialize (XXX1 0 _ _ (eq_refl _) (eq_refl _)); simpl in XXX1.
            unfold tc_val'; rewrite XXX1, H1. destruct MM21a.
            clear IHf_argtypes. 
            exists ((eval_id (fst p) (construct_rho (filter_genv ge) e te))); split; intros; trivial.
            unfold eval_id. simpl. unfold eval_id in H. simpl in H.
            forget (Map.get (make_tenv te) (fst p)) as u. unfold force_val.
            clear - H. destruct u; trivial. simpl in H. eelim tc_val_Vundef. apply H. 
          * inv PrI. destruct MM21a. apply (IHf_argtypes H5 H _ H2 H3). clear IHf_argtypes. 
           intros. apply (XXX1 (S n0)). apply H6. apply H7.
      + split; intros. rewrite PTree.gempty in H; discriminate.
         unfold filter_genv, ge_of, construct_rho in XXX2.  simpl in XXX2.
         unfold stackframe_of' in MM23. red in WW3.   as specialize (XXX1 0 _ _ (eq_refl _) (eq_refl _)); simpl in XXX1.
            unfold tc_val'. destruct MM21a.
            clear IHf_argtypes. 
            exists ((eval_id (fst p) (construct_rho (filter_genv ge) e te))); split; intros; trivial.
            unfold eval_id. simpl. unfold eval_id in H. simpl in H.
            forget (Map.get (make_tenv te) (fst p)) as u. unfold force_val.
            clear - H. destruct u; trivial. simpl in H. eelim tc_val_Vundef. apply H. 
          *Search tc_val.
            unfold construct_rho. simpl. destruct WW1a as [? [? ?]].
            red in H3. destruct ZZ1. unfold make_tycontext_t in H6. simpl in H6. Print tc_val.  Search construct_rho. unfold make_tenv.  simpl. unfold construct_rho.  unfold tc_val'.  unfold make_tycontext_t in H. red in Search typecheck_temp_environ. admit. (*TC*)  }
    simpl in PostPred.
    specialize (B _ yyy u QU).
    rewrite semax_fold_unfold in B.
    specialize (B ge D CS' uu Huu ZZ kk UUKK BD knt). red in B. clear XXX2.
    destruct (join_assoc (join_comm JM2) (join_comm JM)) as [mm1 [MM1a MM1b]].
    destruct HP0 as [m21a [m21b [JM21 [M21a M21b]]]].
    destruct (join_assoc (join_comm JM21) MM1a) as [mfrm [J1 J2]].
    assert (QQ: (!! closed_wrt_modvars (Ssequence (fn_body f) (Sreturn None))
      (fun x : environ => FRM x * FRM2) &&
      rguard Espec ge D
        (frame_ret_assert
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts' yyy))
            (stackframe_of' (@cenv_cs cs') f)) (fun x : environ => FRM x * FRM2)) knt) pp).
    { clear B. clear - PostPred CLOSED. destruct CLOSED as [CL1 CL2]. simpl in CL1. split.
      + simpl. do 2 red; intros. rewrite <- CL1; trivial.
      + intros ek vl te TE y Y aa' AA' [[AA1 AA2] AA3].
        apply (CL2 ek vl te TE y Y aa' AA'); clear CL2.
        split; trivial. split; trivial.
        destruct ek; hnf; hnf in AA2.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]]. simpl in Ha1.
          destruct Ha1 as [_ [_ [_ [? _]]]]; contradiction.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]]. simpl in Ha1.
          destruct Ha1 as [_ [_ [_ [? _]]]]; contradiction.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]]. simpl in Ha1.
          destruct Ha1 as [_ [_ [_ [? _]]]]; contradiction.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]].
          destruct Ha2 as [a21 [a22 [Ja2 [A21 A22]]]].
          specialize (join_assoc Ja2 (join_comm Ja)) as [aa [Jaa Haa]].
          exists aa, a21; apply join_comm in Haa; split3; trivial.
          clear - PostPred Jaa Ha1 A22.
          destruct Ha1 as [a11 [a12 [Ja1 [A11 A12]]]].
          specialize (join_assoc (join_comm Ja1) (join_comm Jaa)) as [aaa [Jaaa Haaa]].
          exists aaa, a12; apply join_comm in Haaa; split3; trivial.
          destruct vl; simpl; simpl in A11. 
          * split. apply A11. apply PostPred. split. simpl. admit. (*tc*) 
            exists a22, a11. apply join_comm in Jaaa; split3; trivial. apply A11.
          * destruct (fn_return f); trivial.
            apply PostPred. split. simpl. admit. (*tc*) 
            exists a22, a11. apply join_comm in Jaaa; split3; trivial. }
    subst rho. apply (B (fun x => FRM x * FRM2) pp KKPP QQ te e _ RM _ RM'); clear B QQ PostPred.
    split; trivial.
    split; trivial.
    destruct (join_assoc (join_comm J2) (join_comm MM1b)) as [? [? ?]].
    exists mfrm, x; split3; trivial.
    - exists m1, m21a; apply join_comm in J1; split3; trivial.
    - split.
      * exists m21b, m2_2; split3; trivial.
        clear - MM21a XXX1 M21b. red. simpl. simpl in *. split.
        { red. trivial. }
        exists ve, xxx. split; trivial.
      * assert (M2x: necR m2 x). admit.
        clear - TYC M2x. destruct TYC as [TYC1 TYC2].
        split; simpl; intros.
        { apply (TYC1 b b0); trivial. Search join age. eapply necR_trans; eassumption. }
        { eapply (TYC2 b b0). 2: simpl; apply H0. eapply necR_trans; eassumption. }
Abort.

Lemma believe_antimonoR' gx Delta Gamma Gamma'
  (DG1: forall i spec', (glob_specs Gamma') ! i = Some spec' ->
        exists spec, (glob_specs Gamma) ! i = Some spec /\ funspec_sub spec spec'):
  @believe CS Espec Delta gx Gamma |-- @believe CS Espec Delta gx Gamma'.
Proof. intros n B v sig cc A' P' Q' k nec CL.
  red in CL. red in CL. destruct CL as [i [HP' [HQ' [Entry' Hi]]]].
  destruct (DG1 _ _ Entry') as [spec [Entry Sub]].
  destruct spec.
  assert (f=sig) by eapply Sub. subst f.
  assert (c=cc) by eapply Sub. subst c.
  specialize (B v sig cc A P Q k nec).
  assert (CL: claims gx Gamma v sig cc A P Q).
  { exists i, P_ne, Q_ne; split; trivial. }
  specialize (B CL). destruct B as [Bext | Bint]; [left | right].
  + admit.
  + clear - Sub Bint. destruct Bint as [b [f [Pr B]]].
    exists b, f. split. apply Pr. clear Pr.
    intros Delta' cs' p KP XX q PQ CSUB ts TS u QU.
    specialize (B Delta' cs' p KP XX q PQ CSUB).
    destruct Sub as [_ [_ Sub]]. specialize (Sub ts TS). simpl in Sub.
    rewrite semax_fold_unfold. intros ge D CS' uu Huu ZZ kk UUKK BD knt FRM pp KKPP CLOSED.
    simpl in XX, ZZ.

    intros te e rm RM rm' RM' [[WW1 WW2] WW3].
    remember (construct_rho (filter_genv ge) e te) as rho.
    destruct WW2 as [m1 [m2 [JM [HFRM MM]]]].
    destruct MM as [[m2_1 [m2_2 [JM2 [MM21 MM23]]]] TYC].
    destruct MM21 as [MM21a MM21b]; simpl in MM21a. red in MM21a.
    destruct MM21b as [ve [xxx [XXX1 XXX2]]]. 
    destruct (Sub (mkEnviron (ge_of rho) ve xxx) m2_1) as [ts' [yyy [FRM2 [HP0 PostPred]]]]; clear Sub.
    { split; trivial. subst rho. simpl. admit. (*TC*)  }
    simpl in PostPred.
    specialize (B _ yyy u QU).
    rewrite semax_fold_unfold in B.
    specialize (B ge D CS' uu Huu ZZ kk UUKK BD knt). red in B. clear XXX2.
    destruct (join_assoc (join_comm JM2) (join_comm JM)) as [mm1 [MM1a MM1b]].
    destruct HP0 as [m21a [m21b [JM21 [M21a M21b]]]].
    destruct (join_assoc (join_comm JM21) MM1a) as [mfrm [J1 J2]].
    assert (QQ: (!! closed_wrt_modvars (Ssequence (fn_body f) (Sreturn None))
      (fun x : environ => FRM x * FRM2) &&
      rguard Espec ge D
        (frame_ret_assert
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts' yyy))
            (stackframe_of' (@cenv_cs cs') f)) (fun x : environ => FRM x * FRM2)) knt) pp).
    { clear B. clear - PostPred CLOSED. destruct CLOSED as [CL1 CL2]. simpl in CL1. split.
      + simpl. do 2 red; intros. rewrite <- CL1; trivial.
      + intros ek vl te TE y Y aa' AA' [[AA1 AA2] AA3].
        apply (CL2 ek vl te TE y Y aa' AA'); clear CL2.
        split; trivial. split; trivial.
        destruct ek; hnf; hnf in AA2.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]]. simpl in Ha1.
          destruct Ha1 as [_ [_ [_ [? _]]]]; contradiction.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]]. simpl in Ha1.
          destruct Ha1 as [_ [_ [_ [? _]]]]; contradiction.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]]. simpl in Ha1.
          destruct Ha1 as [_ [_ [_ [? _]]]]; contradiction.
        - destruct AA2 as [a1 [a2 [Ja [Ha1 Ha2]]]].
          destruct Ha2 as [a21 [a22 [Ja2 [A21 A22]]]].
          specialize (join_assoc Ja2 (join_comm Ja)) as [aa [Jaa Haa]].
          exists aa, a21; apply join_comm in Haa; split3; trivial.
          clear - PostPred Jaa Ha1 A22.
          destruct Ha1 as [a11 [a12 [Ja1 [A11 A12]]]].
          specialize (join_assoc (join_comm Ja1) (join_comm Jaa)) as [aaa [Jaaa Haaa]].
          exists aaa, a12; apply join_comm in Haaa; split3; trivial.
          destruct vl; simpl; simpl in A11. 
          * split. apply A11. apply PostPred. split. simpl. admit. (*tc*) 
            exists a22, a11. apply join_comm in Jaaa; split3; trivial. apply A11.
          * destruct (fn_return f); trivial.
            apply PostPred. split. simpl. admit. (*tc*) 
            exists a22, a11. apply join_comm in Jaaa; split3; trivial. }
    subst rho. apply (B (fun x => FRM x * FRM2) pp KKPP QQ te e _ RM _ RM'); clear B QQ PostPred.
    split; trivial.
    split; trivial.
    destruct (join_assoc (join_comm J2) (join_comm MM1b)) as [? [? ?]].
    exists mfrm, x; split3; trivial.
    - exists m1, m21a; apply join_comm in J1; split3; trivial.
    - split.
      * exists m21b, m2_2; split3; trivial.
        clear - MM21a XXX1 M21b. red. simpl. simpl in *. split.
        { red. trivial. }
        exists ve, xxx. split; trivial.
      * assert (M2x: necR m2 x). admit.
        clear - TYC M2x. destruct TYC as [TYC1 TYC2].
        split; simpl; intros.
        { apply (TYC1 b b0); trivial. Search join age. eapply necR_trans; eassumption. }
        { eapply (TYC2 b b0). 2: simpl; apply H0. eapply necR_trans; eassumption. }
Abort.
*)

Lemma believe_antimonoR_obsolete gx Delta Gamma Gamma'
  (DG1: forall id spec, (glob_specs Gamma') ! id = Some spec ->
                        (glob_specs Gamma) ! id = Some spec):
  @believe CS Espec Delta gx Gamma |-- @believe CS Espec Delta gx Gamma'.
Proof. intros n B v sig cc A P Q k nec CL. apply B; trivial. eapply claims_antimono; eauto. Qed.

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
  - intros PSI CS'' w W HSUB u WU HU ts x. apply (X PSI CS'' w W); trivial.
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
 intros n B v sig cc A P Q k nec CL.
 destruct (B v sig cc A P Q k nec).
+ eapply claims_antimono; eauto.
+ left; trivial.
+ right. clear -SUB CSUB H.
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
  (*explicit proof:
 intros n B v sig cc A P Q k nec CL.
 destruct (B v sig cc A P Q k nec).
+ eapply claims_antimono; eauto.
+ left; trivial.
+ right. clear -SUB CSUB H.
  apply (@believe_internal_mono CS' gx Delta); eauto.*)
Qed.

Lemma believe_internal__mono sem gx Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) k
  (BI: believe_internal_ CS sem gx Delta v sig cc A P Q k):
(believe_internal_ CS sem gx Delta' v sig cc A P Q) k.
Proof. destruct BI as [b [f [Hv X]]].
  exists b, f; split; [trivial | clear Hv].
  intros PSI CS' w W HSUB u WU HU ts x. apply (X PSI CS' w W); trivial.
  simpl; intros. eapply tycontext_sub_trans. 2: apply HSUB. eauto.
Qed.
End believe_monotonicity.

Lemma semax__mono {CS} Espec Delta Delta'
  (SUB: tycontext_sub Delta Delta') sem P c R:
  derives (@semax_ Espec sem {| sa_cs := CS; sa_Delta := Delta; sa_P := P; sa_c := c; sa_R := R |})
      (@semax_ Espec sem {| sa_cs:=CS; sa_Delta := Delta'; sa_P := P; sa_c := c; sa_R := R |}).
Proof. unfold semax_; intros w W.
intros gx Gamma CS' n N [HSUB HCS] m M B k F a A CL.
assert (X: tycontext_sub Delta Gamma) by (eapply tycontext_sub_trans; eauto).
apply (W gx Gamma CS' n N (conj X HCS) m M B k F a A CL).
Qed.

Lemma semax_mono {CS} Espec Delta Delta' P Q
  (SUB: tycontext_sub Delta Delta') c w
  (Hyp: @semax' CS Espec Delta P c Q w):
   @semax' CS Espec Delta' P c Q w.
Proof.
rewrite semax_fold_unfold in *.
intros gx Gamma CS' m M [HH HCS].
assert (SUB': tycontext_sub Delta Gamma) by (eapply tycontext_sub_trans; eassumption).
apply (Hyp gx Gamma CS' m M (conj SUB' HCS)).
Qed.

Lemma semax_mono_box {CS} Espec Delta Delta' P Q
  (SUB: tycontext_sub Delta Delta') c w
  (BI: @box nat ag_nat (@laterM nat ag_nat)
          (@semax' CS Espec Delta P c Q) w):
  @box nat ag_nat (@laterM nat ag_nat)
          (@semax' CS Espec Delta' P c Q) w.
Proof. eapply box_positive; [ clear BI | apply BI].
intros a Hyp.
eapply semax_mono; eassumption.
Qed.

(*In fact, the following specialization suffices in semax_prog*)
Lemma semax_mono' {CS} Espec Delta Delta' P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) c w f
  (BI: @box nat ag_nat (@laterM nat ag_nat)
          (@semax' CS Espec (func_tycontext' f Delta) P c Q) w):
  @box nat ag_nat (@laterM nat ag_nat)
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
