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

Program Definition assert_safe
     (Espec : OracleKind)
     (ge: genv) ve te (ctl: cont) : assert :=
  fun rho => bupd (fun w => forall ora (jm:juicy_mem),
       rho = construct_rho (filter_genv ge) ve te ->
       m_phi jm = w ->
             jsafeN (@OK_spec Espec) ge (level w) ora (State ve te ctl) jm).
 Next Obligation.
  intro; intros.
  subst.
   destruct (oracle_unage _ _ H) as [jm0 [? ?]].
   subst.
   specialize (H0 ora jm0 (eq_refl _) (eq_refl _)).
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
    ALL z:_, ext_spec_pre' Hspec ef x' (genv_symb_injective gx) ts args z &&
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


Definition believe_internal_
  (semax:semaxArg -> pred nat)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) : pred nat :=
  (EX b: block, EX f: function,
   prop (v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type (genv_cenv gx) (snd it) = true) (fn_vars f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars)) /\ var_sizes_ok (genv_cenv gx) (f.(fn_vars))
                 /\ fsig = fn_funsig f /\ f.(fn_callconv) = cc)
  && ALL ts: list Type,
     ALL x : dependent_type_functor_rec ts A (pred rmap),
           |> semax (SemaxArg  (func_tycontext' f Delta)
                                (fun rho => (bind_args f.(fn_params) f.(fn_vars) (P ts x) rho * stackframe_of' (genv_cenv gx) f rho)
                                             && funassert (func_tycontext' f Delta) rho)
                              (Ssequence f.(fn_body) (Sreturn None))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of' (genv_cenv gx) f)))).

Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Definition claims (ge: genv) (Delta: tycontext) v fsig cc A P Q : Prop :=
  exists id HP HQ, (glob_specs Delta)!id = Some (mk_funspec fsig cc A P Q HP HQ) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero.

Definition believepred (Espec: OracleKind) (semax: semaxArg -> pred nat)
              (Delta: tycontext) (gx: genv)  (Delta': tycontext) : pred nat :=
  ALL v:val, ALL fsig: funsig, ALL cc: calling_convention,
  ALL A: TypeTree,
  ALL P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred,
  ALL Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred,
       !! claims gx Delta' v fsig cc A P Q  -->
      (believe_external Espec gx v fsig cc A P Q
        || believe_internal_ semax gx Delta v fsig cc A P Q).

Definition semax_  {CS: compspecs}  (Espec: OracleKind)
       (semax: semaxArg -> pred nat) (a: semaxArg) : pred nat :=
 match a with SemaxArg Delta P c R =>
  ALL gx: genv, ALL Delta': tycontext,
       !! (tycontext_sub Delta Delta' /\ genv_cenv gx = cenv_cs)-->
      (believepred Espec semax Delta' gx Delta') -->
     ALL k: cont, ALL F: assert,
       (!! (closed_wrt_modvars c F) &&
              rguard Espec gx Delta' (frame_ret_assert R F) k) -->
        guard Espec gx Delta' (fun rho => F rho * P rho) (Kseq c :: k)
  end.

Definition semax'  {CS: compspecs} (Espec: OracleKind) Delta P c R : pred nat :=
     HORec (semax_  Espec) (SemaxArg Delta P c R).

Definition believe_internal {CS: compspecs} (Espec:  OracleKind)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) : pred nat :=
  (EX b: block, EX f: function,
   prop (v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type (genv_cenv gx) (snd it) = true) (fn_vars f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars)) /\ var_sizes_ok (genv_cenv gx) (f.(fn_vars))
                 /\ fsig = fn_funsig f /\ f.(fn_callconv) = cc)
  && ALL ts: list Type,
     ALL x : dependent_type_functor_rec ts A (pred rmap),
        |> semax' Espec (func_tycontext' f Delta)
                                (fun rho => (bind_args f.(fn_params) f.(fn_vars) (P ts x) rho * stackframe_of' (genv_cenv gx)  f rho)
                                             && funassert (func_tycontext' f Delta) rho)
                               (Ssequence f.(fn_body) (Sreturn None))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of' (genv_cenv gx) f))).

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
  ALL gx: genv, ALL Delta': tycontext,
       !! (tycontext_sub Delta Delta' /\ genv_cenv gx = cenv_cs) -->
       believe Espec Delta' gx Delta' -->
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
do 2 (apply subp_allp; intros).
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

Definition weakest_pre {CS: compspecs} (Espec: OracleKind) (Delta: tycontext) c Q: assert :=
  fun rho: environ =>
  ALL gx: genv, ALL Delta': tycontext,
       !! (tycontext_sub Delta Delta' /\ genv_cenv gx = cenv_cs) -->
       unfash (believe Espec Delta' gx Delta') -->
     ALL k: cont, ALL F: assert,
        unfash (!! (closed_wrt_modvars c F) && rguard Espec gx Delta' (frame_ret_assert Q F) k) -->
        (* guard Espec gx Delta' (fun rho => F rho * P rho) (Kseq c :: k) *)
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
