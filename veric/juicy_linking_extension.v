Load loadpath.
Require Import msl.base. (*for spec tac*)

Require Import veric.juicy_mem.

Require Import sepcomp.core_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.extension.
Require Import sepcomp.extension_simulations. (*for genv_domain_eq*)
Require Import sepcomp.extension_safety.
Require Import sepcomp.extension_proof.
Require Import sepcomp.Address.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.Coqlib2. 
Require Import sepcomp.wf_lemmas.
Require Import sepcomp.linking_extension.

Require Import veric.juicy_extspec.

Require Import msl.msl_standard.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Maps.

Set Implicit Arguments.
Local Open Scope nat_scope.

Definition dryout_juicy_extspec {Z: Type} (Hspec: juicy_ext_spec Z): ext_spec Z :=
  Build_external_specification _ _ _ (ext_spec_type Hspec) 
    (fun e x tys args z m => exists jm, 
      m_dry jm = m /\ ext_spec_pre Hspec e x tys args z jm)
    (fun e x rty rv z m => exists jm,
      m_dry jm = m /\ ext_spec_post Hspec e x rty rv z jm)
    (fun rv z m => exists jm,
      m_dry jm = m /\ ext_spec_exit Hspec rv z jm).

Lemma linkable_id: forall {Z: Type} (Hspec: ext_spec Z) handled, 
  linkable (fun z:Z => z) handled Hspec Hspec.
Proof.
intros.
unfold linkable.
split; auto.
intros.
exists x'.
rewrite H0 in H1; inv H1.
solve[split; auto].
Qed.

Definition upd_rguard {M Z} 
        (Hspec: external_specification M external_function Z)
        (rguard: option val -> Z -> M -> Prop) :=
  Build_external_specification M external_function Z
   (ext_spec_type Hspec)
   (ext_spec_pre Hspec)   
   (ext_spec_post Hspec)   
   rguard.

Definition j_upd_rguard {Z}
        (Hspec: juicy_ext_spec Z)
        (rguard: option val -> Z -> juicy_mem -> Prop) 
        (Hhered: forall rv z, hereditary age (rguard rv z)) :=
  Build_juicy_ext_spec _ (upd_rguard Hspec rguard) 
   (JE_pre_hered _ Hspec) (JE_post_hered _ Hspec) Hhered.

Section JuicyLinkerSafe.
Variables 
 (F V Z Zext: Type) 
 (proj_zext: Z -> Zext) 
 (zmult: unit -> Zext -> Z)
 (proj_zmult: forall t z, proj_zext (zmult t z) = z)
 (num_modules: nat)
 (cT fT vT: nat -> Type)
 (procedure_linkage_table: ident -> option nat)
 (plt_ok: 
   forall (id: ident) (i: nat), 
   procedure_linkage_table id = Some i -> i < num_modules)
 (modules: forall i: nat, i < num_modules -> CompCertModule.Sig (fT i) (vT i) (cT i))
 (entry_points: list (val*val*signature)).

Implicit Arguments plt_ok [].

Definition juicy_linker_sem := 
  juicy_core_sem (linker_core_semantics F V cT fT vT 
    procedure_linkage_table
    plt_ok
    modules
    entry_points).

(** Hspec = \Cup_{0<=i<num_modules} Hspec_i *)

Variable Hspec: juicy_ext_spec Z.
Variable Hexternal_spec: ext_spec Zext.

Definition handled ef := forall s c sig args,
  linker_proj_core (@linker_active cT fT vT num_modules modules s) s = Some c ->
  at_external (csem_map cT fT vT modules (linker_active s)) c = Some (ef, sig, args) ->
  linker_at_external procedure_linkage_table s = None.

Variable specs_linkable: 
  linkable proj_zext handled (dryout_juicy_extspec Hspec) Hexternal_spec.

Variable ge: Genv.t F V.

Variable ge_agree: forall (k: nat) (pf_k: k < num_modules),
  genvs_agree ge (get_module_genv (modules pf_k)).

Variable ge_domain: forall (k: nat) (pf_k: k < num_modules),
  genvs_domain_eq ge (get_module_genv (modules pf_k)).

Variable modules_fun: forall (k: nat) (pf_k: k < num_modules),
  corestep_fun (get_module_csem (modules pf_k)).

Variable ef2id: forall (ef: external_function), ident.

Variable ef2id_ok: 
  forall ef, match ef with
  | EF_external name _ => ef2id ef=name
  | _ => True
  end.

Variable modules_verified:
  forall i (pf: i < num_modules) ef,
  let csem := get_module_csem (modules pf) in
  let ge := get_module_genv (modules pf) in
  let P := ext_spec_pre Hspec ef in
  let Q := ext_spec_post Hspec ef in
    forall b tys args x n z c jm,
    procedure_linkage_table (ef2id ef) = Some i -> 
    Genv.find_symbol ge (ef2id ef) = Some b ->         
    make_initial_core csem ge (Vptr b (Int.repr 0)) args = Some c -> 
    P x tys args z jm -> 
    safeN (juicy_core_sem csem) 
      (j_upd_rguard Hspec (Q x (sig_res (ef_sig ef))) (JE_post_hered _ _ _ _ _)) 
      ge n z c jm.

Definition juicy_linking_extension :=
  @linking_extension F V Z Zext proj_zext zmult proj_zmult 
    cT fT vT num_modules procedure_linkage_table plt_ok modules
    (dryout_juicy_extspec Hspec) Hexternal_spec entry_points specs_linkable.

Fixpoint tl_inv (n: nat) (stack: call_stack cT num_modules) 
   (rguard_in: option val -> Z -> juicy_mem -> Prop) :=
 match stack with
 | nil => True
 | mkFrame i pf_i c_i :: stack' => 
   exists rguard_out, exists Hhered,
   (let csem := get_module_csem (modules pf_i) in
    let ge := get_module_genv (modules pf_i) in
     forall ret jm z,
       rguard_in ret z jm -> 
       exists c_i', 
         after_external (juicy_core_sem csem) ret c_i = Some c_i' /\
         safeN (juicy_core_sem csem) (j_upd_rguard Hspec rguard_out Hhered) ge n z c_i' jm) /\
   tl_inv n stack' rguard_out
  end.

Definition stack_inv (n: nat) (stack: call_stack cT num_modules) z jm := 
 match stack with
 | nil => True
 | mkFrame i pf_i c_i :: stack' => 
   let csem := get_module_csem (modules pf_i) in
   let ge := get_module_genv (modules pf_i) in
     exists rguard_out, exists Hhered,
       safeN (juicy_core_sem csem) (j_upd_rguard Hspec rguard_out Hhered) ge n z c_i jm /\
       tl_inv n stack' rguard_out
 end.

Definition linker_inv n (s: linker_corestate cT fT vT modules) z jm := 
  match s with mkLinkerCoreState stack Hlength Hat_ext => stack_inv n stack z jm end.

Lemma tl_inv_downward:
  forall n stack rguard,
  tl_inv (S n) stack rguard -> tl_inv n stack rguard.
Proof.
intros until rguard; revert n rguard; induction stack; auto.
intros n rguard.
destruct a.
intros [rguard0 [Hhered [H1 H2]]].
exists rguard0; exists Hhered; split; auto.
hnf.
intros ret jm z RGUARD.
hnf in H1.
destruct (H1 ret jm z RGUARD) as [c_i' [AFTER_EXT H3]].
exists c_i'; split; auto.
solve[apply safe_downward1; auto].
Qed.

Lemma juicy_linker_safety_step_invariant:
  forall n s jm z s' jm',
  level jm = S n -> 
  linker_inv (S n) s z jm -> 
  corestep juicy_linker_sem ge s jm s' jm' -> 
  linker_inv n s' z jm'.
Proof.
intros until jm'; intros LEV INV [STEP DECAY].
destruct s; destruct s'.
inv STEP.

(*STEP CASE*)
unfold stack_inv in INV|-*.
destruct INV as [rguard0 [Hhered INV]].
generalize H5 as H5'; intro.
generalize H5 as STEP; intro.
apply corestep_not_at_external in H5.
simpl in *|-.
rewrite H5 in INV.
apply corestep_not_halted in H5'.
unfold j_safely_halted in INV.
rewrite H5' in INV.
destruct INV as [ [c1 [m1 [STEP1 SAFE]]] TLINV ].
exists rguard0; exists Hhered.
split; auto.
destruct STEP1 as [STEP1 DECAY1].
assert (Heq: (c1, m_dry m1)=(c', m_dry jm')).
 solve[eapply modules_fun; eauto].
inv Heq; subst.
assert (m1 = jm') by admit. (* must be exposed in jstep (but should be provable
                               for all dry determ. core semantics which are 
                               subsequently juicified)*)
subst m1.
solve[apply SAFE].
solve[apply tl_inv_downward; auto].

(*CALL CASE*)
simpl in callers_at_external0.
hnf in callers_at_external0; inversion callers_at_external0; subst.
destruct H4 as [ef0 [sig0 [args0 AT_EXT0]]].
assert (Hsig: sig0 = sig).
 solve[rewrite AT_EXT0 in AT_EXT; inv AT_EXT; auto].
assert (Hargs: args0 = args).
 solve[rewrite AT_EXT0 in AT_EXT; inv AT_EXT; auto].
inv Hargs.
simpl in INV.
rewrite AT_EXT0 in INV.
generalize (at_external_halted_excl (get_module_csem (modules pf_i)) c); 
 intros [H9|H9]; try solve[congruence].
unfold j_safely_halted in INV.
rewrite H9 in INV.
destruct INV as [rguard_out [Hhered [[x [PRE POST]] TL_INV]]].
hnf.
exists (ext_spec_post Hspec ef0 x (sig_res sig)).
assert (Hhered0: forall rv z0, 
 hereditary age (ext_spec_post Hspec ef0 x (sig_res sig) rv z0)).
 intros rv z0.
 solve[eapply JE_post_hered; eauto].
exists Hhered0.
split.
assert (Heq: id = ef2id ef0).
 rewrite AT_EXT0 in AT_EXT; inv AT_EXT.
 solve[generalize (ef2id_ok (EF_external id sig)); intros ->; auto].
inv Heq.
assert (Hgenv: Genv.find_symbol 
 (get_module_genv (modules (plt_ok _ j LOOKUP))) (ef2id ef0) = Some b).
 exploit ge_agree; eauto.
 unfold genvs_agree; intros [? ?].
 solve[erewrite <-H; auto].
generalize (@modules_verified 
 j (plt_ok _ j LOOKUP) ef0
 b (sig_args sig) args x (S n) z c' jm LOOKUP Hgenv); intros VERIF.
spec VERIF; auto.
spec VERIF; auto.
assert (Hage: age jm jm'). 
 admit. (*update defn. of jstep to assert that m=m' -> age jm jm'*)
assert (Hhered1: forall rv z0, 
 hereditary age (ext_spec_post Hspec ef0 x (sig_res (ef_sig ef0)) rv z0)).
 intros rv z0.
 solve[eapply JE_post_hered; eauto].
generalize (@age_safe
 _ _ _ (get_module_csem (modules (plt_ok (ef2id ef0) j LOOKUP))) _
 (j_upd_rguard Hspec
   (ext_spec_post Hspec ef0 x (sig_res (ef_sig ef0))) Hhered1) _ _ Hage
   (get_module_genv (modules (plt_ok (ef2id ef0) j LOOKUP))) z c').
intros SAFE.
rewrite LEV in SAFE.
spec SAFE; auto.
assert (n = level jm') as ->.
 destruct DECAY as [D1 D2].
 solve[rewrite LEV in D2; inv D2; auto].
assert (Hsig: ef_sig ef0 = sig).
 rewrite AT_EXT0 in AT_EXT; inversion AT_EXT.
 solve[generalize (ef2id_ok ef0); rewrite H4; hnf; intros ->; simpl; auto].
subst.
assert (Hhered0 = Hhered1) as -> by apply proof_irr.
solve[apply SAFE].
hnf.
exists rguard_out.
exists Hhered.
split; simpl.
intros ret jm0 z0 Hpost.
destruct (POST ret jm0 z0 Hpost) as [c'' [AFTER_EXT SAFE]].
exists c''.
split; auto.
solve[apply tl_inv_downward; auto].

(*RETURN STEP*)
hnf in INV|-*.
destruct INV as [rguard_out [Hhered [SAFE TL_INV]]].
hnf in SAFE.
generalize (@at_external_halted_excl _ _ _ _ 
 (get_module_csem (modules (plt_ok id j LOOKUP))) c'); intros [X|X].
simpl in SAFE.
rewrite X in SAFE.
unfold j_safely_halted in SAFE.
rewrite HALTED in SAFE.
hnf in TL_INV.
destruct TL_INV as [rguard_out0 [Hhered0 [TL1 TL2]]].
hnf in TL1.
exists rguard_out0.
exists Hhered0.
split.
2: solve[apply tl_inv_downward; auto].
specialize (TL1 (Some retv) jm z SAFE).
destruct TL1 as [c_i' [AFTER_EXT SAFE']].
simpl in AFTER_EXT.
rewrite H6 in AFTER_EXT; inv AFTER_EXT.
rewrite <-LEV in SAFE'.
assert (n = level jm') as ->.
 destruct DECAY as [D1 D2].
 solve[rewrite LEV in D2; inv D2; auto].
assert (Hage: age jm jm'). 
 admit. (*update defn. of jstep to assert that m=m' -> age jm jm'*)
solve[eapply age_safe; eauto].
elimtype False.
clear - HALTED X.
congruence.
Qed.

End JuicyLinkerSafe.  
