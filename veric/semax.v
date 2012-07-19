Require Import veric.base.
Require Import veric.Address.
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
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr.

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
     (ge: genv) (ctl: cont) : assert :=
  fun rho w => forall ora (jm:juicy_mem),
         m_phi jm = w ->
             jsafeN Hspec ge (level w) ora (State (ve_of rho) (te_of rho) ctl) jm.
 Next Obligation.
  subst.
   destruct (oracle_unage _ _ H) as [jm0 [? ?]].
   subst.
   specialize (H0 ora jm0 (eq_refl _)).
   destruct rho; simpl in *.
   forget (State ve te ctl) as c. clear ve te ctl.
  change (level (m_phi jm)) with (level jm).
  eapply age_safe; eauto.
Qed.

Definition list2opt {T: Type} (vl: list T) : option T :=
 match vl with nil => None | x::_ => Some x end.

Fixpoint assoc_list_get {A}{B}{EA: EqDec A}(l: list (A*B))(a: A) : option B :=
 match l with
 | nil => None
 | (x,y)::rest => if eq_dec a x then Some y else assoc_list_get rest a
 end.   

Definition guard  {Z} (Hspec : juicy_ext_spec Z)
    (gx: genv) (Delta: tycontext) (G: funspecs) (P : assert)  (ctl: cont) : pred nat :=
     All rho:environ, 
          !! (typecheck_environ rho Delta = true /\ filter_genv gx = ge_of rho) && P rho && funassert G rho 
             >=> assert_safe Hspec gx ctl rho.

Definition zap_fn_return (f: function) : function :=
 mkfunction Tvoid f.(fn_params) f.(fn_vars) f.(fn_temps) f.(fn_body).

Definition exit_cont (ek: exitkind) (vl: list val) (k: cont) : cont :=
  match ek with
  | EK_normal => k
  | EK_break => break_cont k
  | EK_continue => continue_cont k
  | EK_return => 
         match vl, call_cont k with 
         | v::_, Kcall (Some x) f ve te :: k' => 
                    Kseq (Sreturn None) :: Kcall None (zap_fn_return f) ve (PTree.set x v te) :: k'
         | _,_ => Kseq (Sreturn None) :: call_cont k
         end
   end.

Definition rguard  {Z} (Hspec : juicy_ext_spec Z)
    (gx: genv)  (Delta: tycontext) (G: funspecs) (F: assert) (R : ret_assert) (ctl: cont) : pred nat :=
     All ek: exitkind, All vl: list val, All rho:environ, 
           !! (typecheck_environ rho Delta = true /\ filter_genv gx = ge_of rho) && 
         ((F rho * R ek vl rho) && funassert G rho) >=> 
               assert_safe Hspec gx (exit_cont ek vl ctl) rho.

Record semaxArg :Type := SemaxArg {
 sa_Delta: tycontext;
 sa_G: funspecs;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.


Definition ext_spec_pre' {Z} (Hspec: juicy_ext_spec Z) (ef: external_function) 
   (x': ext_spec_type Hspec ef)(args: list val) (z: Z) : pred juicy_mem :=
  exist (hereditary age) 
     (ext_spec_pre Hspec ef x' (sig_args (ef_sig ef)) args z)
     (JE_pre_hered _ _ _ _ _ _ _).

Program Definition ext_spec_post' {Z} (Hspec: juicy_ext_spec Z)
   (ef: external_function) (x': ext_spec_type Hspec ef) 
   (ret: list val) (z: Z) : pred juicy_mem :=
  exist (hereditary age) 
   (ext_spec_post Hspec ef x' (opt2list (sig_res (ef_sig ef))) ret z)
     (JE_post_hered _ _ _ _ _ _ _).

Definition juicy_mem_pred (P : pred rmap) (jm: juicy_mem): pred nat :=
     # diamond fashionM (exactly (m_phi jm) && P).

Definition semax_ext  {Z} (Hspec: juicy_ext_spec Z) 
                  ef (A: Type) (P Q: A -> list val -> pred rmap): 
        pred nat := 
 All x: A, 
 |>  All F: pred rmap, All args: list val,
   juicy_mem_op (P x args * F) >=> 
   Ex x': ext_spec_type Hspec ef,
    All z:_, ext_spec_pre' Hspec ef x' args z &&
     ! All ret: list val, All z':Z, 
      ext_spec_post' Hspec ef x' ret z' >=>
      !! (length ret = length (opt2list (sig_res (ef_sig ef)))) &&
          juicy_mem_op (|>(Q x ret * F)).

Definition believe_external {Z} (Hspec: juicy_ext_spec Z) (gx: genv) (v: val) (fsig: funsig)
   (A: Type) (P Q: A -> list val -> pred rmap) : pred nat :=
  match Genv.find_funct gx v with 
  | Some (External ef sigargs sigret) => 
        !! (fsig = (sigargs,sigret)) && semax_ext Hspec ef A P Q 
  | _ => FF 
  end.

Definition fn_funsig (f: function) : funsig := (type_of_params (fn_params f), fn_return f).

Definition believe_internal_ 
  (semax:semaxArg -> pred nat)
  (gx: genv) (G:funspecs) v (fsig: funsig) A (P Q: A -> list val -> pred rmap) : pred nat :=
  (Ex b: block, Ex f: function,  
   prop (v = Vptr b Int.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars))
                 /\ fsig = fn_funsig f)
  && All x : A, |> semax (SemaxArg  (func_tycontext f) G
                                (fun rho => (bind_args f.(fn_params) (P x) rho * stackframe_of f rho)
                                             && funassert G rho)
                              f.(fn_body)  (function_body_ret_assert f (Q x)))).

Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (PTree.empty _) (PTree.empty _).

Definition claims (ge: genv) (G: funspecs) v fsig A P Q : Prop :=
  exists id, In (id, mk_funspec fsig A P Q) G /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero.

Definition believepred {Z} (Hspec: juicy_ext_spec Z) (semax: semaxArg -> pred nat)
              (G: funspecs) (gx: genv) (G': funspecs) : pred nat :=
  All v:val, All fsig: funsig,
         All A: Type, All P: A -> list val -> pred rmap, All Q: A -> list val -> pred rmap,
       !! claims gx G' v fsig A P Q  -->
      (believe_external Hspec gx v fsig A P Q
        || believe_internal_ semax gx G v fsig A P Q).

Definition semax_  {Z} (Hspec: juicy_ext_spec Z)
       (semax: semaxArg -> pred nat) (a: semaxArg) : pred nat :=
 match a with SemaxArg Delta G P c R =>
  All gx: genv, (believepred Hspec semax G gx G) --> 
     All k: cont, All F: assert, 
       (!! (closed_wrt_modvars c F) && rguard Hspec gx Delta G F R k) -->
        guard Hspec gx Delta G (fun rho => F rho * P rho) (Kseq c :: k)
  end.

Definition semax'  {Z} (Hspec: juicy_ext_spec Z) Delta G P c R : pred nat := 
     HORec (semax_  Hspec) (SemaxArg Delta G P c R).

Definition believe_internal {Z} (Hspec:juicy_ext_spec Z)
  (gx: genv) (G:funspecs) v (fsig: funsig) A (P Q: A -> list val -> pred rmap) : pred nat :=
  (Ex b: block, Ex f: function,  
   prop (v = Vptr b Int.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ list_norepet (map (@fst _ _) f.(fn_params) ++ map (@fst _ _) f.(fn_temps))
                 /\ list_norepet (map (@fst _ _) f.(fn_vars))
                 /\ fsig = fn_funsig f)
  && All x : A, |> semax' Hspec (func_tycontext f) G
                                (fun rho => (bind_args f.(fn_params) (P x) rho * stackframe_of f rho)
                                             && funassert G rho)
                              f.(fn_body)  (function_body_ret_assert f (Q x))).

Definition believe {Z} (Hspec:juicy_ext_spec Z)
              (G: funspecs) (gx: genv) (G': funspecs) : pred nat :=
  All v:val, All fsig: funsig,
         All A: Type, All P: A -> list val -> pred rmap, All Q: A -> list val -> pred rmap,
       !! claims gx G' v fsig A P Q  -->
      (believe_external Hspec gx v fsig A P Q
        || believe_internal Hspec gx G v fsig A P Q).

Lemma semax_fold_unfold : forall
  {Z} (Hspec : juicy_ext_spec Z),
  semax' Hspec = fun Delta G P c R =>
  All gx: genv, 
       believe Hspec G gx G --> 
     All k: cont, All F: assert, 
        (!! (closed_wrt_modvars c F) && rguard Hspec gx Delta G F R k) -->
        guard Hspec gx Delta G (fun rho => F rho * P rho) (Kseq c :: k).
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
apply sub_allp; intros.
apply sub_imp; [ | auto 50 with contractive].
apply sub_allp; intros.
apply sub_allp; intros.
apply sub_allp; intros.
apply sub_allp; intros.
apply sub_allp; intros.
apply sub_imp; intros; [ auto 50 with contractive | ].
apply sub_orp; [ auto 50 with contractive | ].
apply sub_exp; intros.
apply sub_exp; intros.
auto 50 with contractive.
Qed.

Opaque semax'.

Definition semax {Z}(Hspec: juicy_ext_spec Z) (Delta: tycontext) G P c Q :=
  typecheck_stmt Delta c = true /\
  forall n, semax' Hspec Delta G P c Q n.

Lemma pred_eq_nat: forall P Q: pred nat, (P <=> Q) = (P <--> Q).
Proof.
intros.
apply pred_ext; intros w ?.
specialize (H _ (le_refl _)); auto.
intros n' ?. inv H0; auto.
eapply pred_nec_hereditary; try apply H. 
apply nec_nat.
unfold level in H1. simpl in H1. unfold natLevel in H1. omega.
Qed.
