Load loadpath.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import compositional_compcert.extspec.
Require Import compositional_compcert.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.

Local Open Scope nat_scope.
Local Open Scope pred.

(* Admitted: move this elsewhere *)
Lemma or_pred_ext {A} `{agA : ageable A}: forall P Q P' Q',
       (P <--> P') && (Q <--> Q') |--  (P || Q) <--> (P' || Q').
Proof.
intros.
intros w [? ?].
split; intros w' ? [?|?].
left. destruct H; eauto.
right. destruct H0; eauto.
left. destruct H; eauto.
right. destruct H0; eauto.
Qed.

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Definition jsafeN {Z} (Hspec : juicy_ext_spec Z)  :=
  safeN (juicy_core_sem cl_core_sem) Hspec.

Program Definition assert_safe 
     {Z}
     (Hspec : juicy_ext_spec Z)
     (ge: genv) ve te (ctl: cont) : assert :=
  fun rho w => forall ora (jm:juicy_mem),
       rho = construct_rho (filter_genv ge) ve te ->  
       m_phi jm = w ->
             jsafeN Hspec ge (level w) ora (State ve te ctl) jm.
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

Fixpoint assoc_list_get {A}{B}{EA: EqDec A}(l: list (A*B))(a: A) : option B :=
 match l with
 | nil => None
 | (x,y)::rest => if eq_dec a x then Some y else assoc_list_get rest a
 end.   

Definition guard_environ (Delta: tycontext) (f: option function) (rho: environ) : Prop :=
   typecheck_environ rho Delta = true /\
  match f with 
  | Some f' => 
      (forall id, ve_of rho id <> None -> In id (map fst (fn_vars f'))) 
     /\ ret_type Delta = fn_return f'
  | None => True
  end.

Lemma guard_environ_e1: 
   forall Delta f rho, guard_environ Delta f rho ->
     typecheck_environ rho Delta = true.
Proof. intros. destruct H; auto. Qed.

Definition guard  {Z} (Hspec : juicy_ext_spec Z)
    (gx: genv) (Delta: tycontext) (P : assert)  (ctl: cont) : pred nat :=
     ALL tx : Clight.temp_env, ALL vx : env,
          let rho := construct_rho (filter_genv gx) vx tx in 
          !! guard_environ Delta (current_function ctl) rho
                  && P rho && funassert Delta rho 
             >=> assert_safe Hspec gx vx tx ctl rho.

Definition zap_fn_return (f: function) : function :=
 mkfunction Tvoid f.(fn_params) f.(fn_vars) f.(fn_temps) f.(fn_body).

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

Definition exit_tycon (c: statement) (Delta: tycontext) (ek: exitkind) : tycontext :=
  match ek with 
  | EK_normal => update_tycon Delta c 
  | _ => Delta 
  end.

Definition r_update_tenv (tx:Clight.temp_env) id vl := 
match vl, id with 
| v::_, Some ret => PTree.set ret v tx  
| _,_ => tx
end.

Definition rguard  {Z} (Hspec : juicy_ext_spec Z)
    (gx: genv) (Delta: exitkind -> tycontext)  (R : ret_assert) (ctl: cont) : pred nat :=
     ALL ek: exitkind, ALL vl: option val, ALL tx: Clight.temp_env, ALL vx : env,
           let rho := construct_rho (filter_genv gx) vx tx in 
           !! guard_environ (Delta ek) (current_function ctl) rho && 
         (R ek vl rho && funassert (Delta ek) rho) >=> 
               assert_safe Hspec gx vx tx (exit_cont ek vl ctl) rho.

Record semaxArg :Type := SemaxArg {
 sa_Delta: tycontext;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.


Definition ext_spec_pre' {Z} (Hspec: juicy_ext_spec Z) (ef: external_function) 
   (x': ext_spec_type Hspec ef) (ts: list typ) (args: list val) (z: Z) : pred juicy_mem :=
  exist (hereditary age) 
     (ext_spec_pre Hspec ef x' ts args z)
     (JE_pre_hered _ _ _ _ _ _ _).

Program Definition ext_spec_post' {Z} (Hspec: juicy_ext_spec Z)
   (ef: external_function) (x': ext_spec_type Hspec ef) 
   (tret: option typ) (ret: option val) (z: Z) : pred juicy_mem :=
  exist (hereditary age) 
   (ext_spec_post Hspec ef x' tret ret z)
     (JE_post_hered _ _ _ _ _ _ _).

Definition juicy_mem_pred (P : pred rmap) (jm: juicy_mem): pred nat :=
     # diamond fashionM (exactly (m_phi jm) && P).

Fixpoint make_ext_args (n: positive) (vl: list val)  :=
  match vl with 
  | nil => any_environ (* correct but misleading, really must be empty! *)
  | v::vl' => env_set (make_ext_args (n+1)%positive vl') n v
 end.

Definition make_ext_rval (n: positive) (v: option val) :=
  match v with
  | Some v' => env_set any_environ n v'
  | None => any_environ
  end.

Definition semax_ext  {Z} (Hspec: juicy_ext_spec Z) 
                  ef (A: Type) (P Q: A -> environ -> pred rmap): 
        pred nat := 
 ALL x: A, 
 |>  ALL F: pred rmap, ALL ts: list typ, ALL args: list val,
   juicy_mem_op (P x (make_ext_args 1%positive args) * F) >=> 
   EX x': ext_spec_type Hspec ef,
    ALL z:_, ext_spec_pre' Hspec ef x' ts args z &&
     ! ALL tret: option typ, ALL ret: option val, ALL z':Z, 
      ext_spec_post' Hspec ef x' tret ret z' >=>
(*      !! (length ret = length (opt2list (sig_res (ef_sig ef)))) &&*)
          juicy_mem_op (|>(Q x (make_ext_rval 1 ret) * F)).

Fixpoint arglist (n: positive) (tl: typelist) : list (ident*type) :=
 match tl with 
  | Tnil => nil
  | Tcons t tl' => (n,t):: arglist (n+1)%positive tl'
 end.

Definition believe_external {Z} (Hspec: juicy_ext_spec Z) (gx: genv) (v: val) (fsig: funsig)
   (A: Type) (P Q: A -> environ -> pred rmap) : pred nat :=
  match Genv.find_funct gx v with 
  | Some (External ef sigargs sigret) => 
        !! (fsig = (arglist 1%positive sigargs,sigret)) && semax_ext Hspec ef A P Q 
  | _ => FF 
  end.

Definition fn_funsig (f: function) : funsig := (fn_params f, fn_return f).

Definition func_tycontext' (func: function) (Delta: tycontext) : tycontext :=
(make_tycontext_t (fn_params func) (fn_temps func),
make_tycontext_v (fn_vars func) ,
fn_return func,
 glob_types Delta).

Definition believe_internal_ 
  (semax:semaxArg -> pred nat)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) A (P Q: A -> assert) : pred nat :=
  (EX b: block, EX f: function,  
   prop (v = Vptr b Int.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars))
                 /\ fsig = fn_funsig f)
  && ALL x : A, |> semax (SemaxArg  (func_tycontext' f Delta)
                                (fun rho => (bind_args f.(fn_params) (P x) rho * stackframe_of f rho)
                                             && funassert (func_tycontext' f Delta) rho)
                              f.(fn_body)  
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f)))).

Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Definition claims (ge: genv) (Delta: tycontext) v fsig A P Q : Prop :=
  exists id, (glob_types Delta)!id = Some (Global_func (mk_funspec fsig A P Q)) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero.

Definition believepred {Z} (Hspec: juicy_ext_spec Z) (semax: semaxArg -> pred nat)
              (Delta: tycontext) (gx: genv) (Delta': tycontext) : pred nat :=
  ALL v:val, ALL fsig: funsig,
         ALL A: Type, ALL P: A -> assert, ALL Q: A -> assert,
       !! claims gx Delta' v fsig A P Q  -->
      (believe_external Hspec gx v fsig A P Q
        || believe_internal_ semax gx Delta v fsig A P Q).

Definition semax_  {Z} (Hspec: juicy_ext_spec Z)
       (semax: semaxArg -> pred nat) (a: semaxArg) : pred nat :=
 match a with SemaxArg Delta P c R =>
  ALL gx: genv, (believepred Hspec semax Delta gx Delta) --> 
     ALL k: cont, ALL F: assert, 
       (!! (closed_wrt_modvars c F) && 
              rguard Hspec gx (exit_tycon c Delta) (frame_ret_assert R F) k) -->
        guard Hspec gx Delta (fun rho => F rho * P rho) (Kseq c :: k)
  end.

Definition semax'  {Z} (Hspec: juicy_ext_spec Z) Delta P c R : pred nat := 
     HORec (semax_  Hspec) (SemaxArg Delta P c R).

Definition believe_internal {Z} (Hspec:juicy_ext_spec Z)
  (gx: genv) (Delta: tycontext) v (fsig: funsig) A (P Q: A -> assert) : pred nat :=
  (EX b: block, EX f: function,  
   prop (v = Vptr b Int.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars))
                 /\ fsig = fn_funsig f)
  && ALL x : A, |> semax' Hspec (func_tycontext' f Delta)
                                (fun rho => (bind_args f.(fn_params) (P x) rho * stackframe_of f rho)
                                             && funassert (func_tycontext' f Delta) rho)
                              f.(fn_body)  
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f))).

Definition believe {Z} (Hspec:juicy_ext_spec Z)
              (Delta: tycontext) (gx: genv) (Delta': tycontext) : pred nat :=
  ALL v:val, ALL fsig: funsig,
         ALL A: Type, ALL P: A -> assert, ALL Q: A -> assert,
       !! claims gx Delta' v fsig A P Q  -->
      (believe_external Hspec gx v fsig A P Q
        || believe_internal Hspec gx Delta v fsig A P Q).

Lemma semax_fold_unfold : forall
  {Z} (Hspec : juicy_ext_spec Z),
  semax' Hspec = fun Delta P c R =>
  ALL gx: genv,
       believe Hspec Delta gx Delta --> 
     ALL k: cont, ALL F: assert, 
        (!! (closed_wrt_modvars c F) && rguard Hspec gx (exit_tycon c Delta) (frame_ret_assert R F) k) -->
        guard Hspec gx Delta (fun rho => F rho * P rho) (Kseq c :: k).
Proof.
intros ? ?.
extensionality G P. extensionality c R.
unfold semax'.
pattern (HORec (semax_ Hspec)) at 1; rewrite HORec_fold_unfold.
reflexivity.
apply prove_HOcontractive.
intros.
unfold semax_.
clear.
sub_unfold.
do 1 (apply subp_allp; intros). 
apply subp_imp; [ | auto 50 with contractive].
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

Definition semax {Z}(Hspec: juicy_ext_spec Z) (Delta: tycontext) P c Q :=
  forall n, semax' Hspec Delta P c Q n.
