Require Import veric.juicy_base.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.extend_tc.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
Require Import veric.juicy_safety.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.expr_lemmas.

Local Open Scope nat_scope.
Local Open Scope pred.

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Definition jsafeN {Z} (Hspec : juicy_ext_spec Z)  :=
  safeN (fun ge: genv => Genv.genv_symb ge) (juicy_core_sem cl_core_sem) Hspec.

Program Definition assert_safe
     (Espec : OracleKind)
     (ge: genv) ve te (ctl: cont) : assert :=
  fun rho w => forall ora (jm:juicy_mem),
       rho = construct_rho (filter_genv ge) ve te ->
       m_phi jm = w ->
             jsafeN (@OK_spec Espec) ge (level w) ora (State ve te ctl) jm.
 Next Obligation.
  intro; intros.
  subst.
   destruct (oracle_unage _ _ H) as [jm0 [? ?]].
   subst.
   specialize (H0 ora jm0 (eq_refl _) (eq_refl _)).
   forget (State ve te ctl) as c. clear H ve te ctl.
  change (level (m_phi jm)) with (level jm).
  change (level (m_phi jm0)) with (level jm0) in H0.
  unfold jsafeN in *.
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

Definition guard  {CS: compspecs} (Espec : OracleKind)
    (gx: genv) (Delta: tycontext) (P : assert)  (ctl: cont) : pred nat :=
     ALL tx : Clight.temp_env, ALL vx : env,
          let rho := construct_rho (filter_genv gx) vx tx in
          !! guard_environ Delta (current_function ctl) rho
                  && P rho && funassert Delta rho
                (*  && (!! (genv_cenv gx = cenv_cs)) *)
             >=> assert_safe Espec gx vx tx ctl rho.

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

Definition r_update_tenv (tx:Clight.temp_env) id vl :=
match vl, id with
| v::_, Some ret => PTree.set ret v tx
| _,_ => tx
end.

Definition rguard {CS: compspecs} (Espec : OracleKind)
    (gx: genv) (Delta: exitkind -> tycontext)  (R : ret_assert) (ctl: cont) : pred nat :=
     ALL ek: exitkind, ALL vl: option val, ALL tx: Clight.temp_env, ALL vx : env,
           let rho := construct_rho (filter_genv gx) vx tx in
           !! guard_environ (Delta ek) (current_function ctl) rho &&
         R ek vl rho && funassert (Delta ek) rho
           (* && (!! (genv_cenv gx = cenv_cs)) *)
          >=> assert_safe Espec gx vx tx (exit_cont ek vl ctl) rho.

Record semaxArg :Type := SemaxArg {
 sa_Delta: tycontext;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.

Definition ext_spec_pre' (Espec: OracleKind) (ef: external_function)
   (x': ext_spec_type OK_spec ef) (ge_s: PTree.t block)
   (ts: list typ) (args: list val) (z: OK_ty) : pred juicy_mem :=
  exist (hereditary age)
     (ext_spec_pre OK_spec ef x' ge_s ts args z)
     (JE_pre_hered _ _ _ _ _ _ _ _).

Program Definition ext_spec_post' (Espec: OracleKind)
   (ef: external_function) (x': ext_spec_type OK_spec ef) (ge_s: PTree.t block)
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
    ALL z:_, ext_spec_pre' Hspec ef x' (Genv.genv_symb gx) ts args z &&
     ! ALL tret: option typ, ALL ret: option val, ALL z': OK_ty,
      ext_spec_post' Hspec ef x' (Genv.genv_symb gx) tret ret z' >=>
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
   Forall (fun var : ident * type => @sizeof cenv (snd var) <= Int.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type) (rho: environ): mpred :=
  !! (sizeof (snd idt) <= Int.max_unsigned)%Z &&
  (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) : assert :=
  fold_right (fun P Q rho => P rho * Q rho) (fun rho => emp)
     (map (fun idt => var_block' Share.top cenv idt) (Clight.fn_vars f)).


Definition believe_internal_
  (semax:semaxArg -> pred nat)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) : pred nat :=
  (EX b: block, EX f: function,
   prop (v = Vptr b Int.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
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
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero.

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
              rguard Espec gx (exit_tycon c Delta') (frame_ret_assert R F) k) -->
        guard Espec gx Delta' (fun rho => F rho * P rho) (Kseq c :: k)
  end.

Definition semax'  {CS: compspecs} (Espec: OracleKind) Delta P c R : pred nat :=
     HORec (semax_  Espec) (SemaxArg Delta P c R).

Definition believe_internal {CS: compspecs} (Espec:  OracleKind)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) : pred nat :=
  (EX b: block, EX f: function,
   prop (v = Vptr b Int.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
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
        (!! (closed_wrt_modvars c F) && rguard Espec gx (exit_tycon c Delta') (frame_ret_assert R F) k) -->
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

Opaque semax'.

Definition semax {CS: compspecs} (Espec: OracleKind) (Delta: tycontext) P c Q :=
  forall n, semax' Espec Delta P c Q n.
