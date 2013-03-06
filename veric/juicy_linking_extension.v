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
Require Import veric.compcert_rmaps.

Require Import msl.msl_standard.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.

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

Definition post_well_typed (ef: external_function) 
      (Q: ext_spec_type Hspec ef -> option typ -> option val -> Z -> juicy_mem -> Prop) :=
  forall x rv z m, 
  Q x (sig_res (ef_sig ef)) rv z m -> 
  forward_simulations.val_has_type_opt rv (ef_sig ef).    

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
      ge n z c jm /\
    post_well_typed ef Q.

(** This hypothesis may disappear after we clean up the CoreSemantics record. *)

Variable mk_initial_core_succeeds: 
  forall i (pf: i < num_modules) v vs,
  exists c, make_initial_core 
    (get_module_csem (modules pf)) 
    (get_module_genv (modules pf)) v vs = Some c.

(** Modules blocked on external calls are calling functions that aren't actually 
   defined in the current module. *)

Variable at_ext_plt_ok: 
  forall i (pf: i < num_modules) c ef sig args,
  at_external (get_module_csem (modules pf)) c = Some (ef, sig, args) -> 
  (exists j, i<>j /\ 
    procedure_linkage_table (ef2id ef) = Some j /\
    exists b, Genv.find_symbol ge (ef2id ef) = Some b /\
    ef = EF_external (ef2id ef) sig) \/
  procedure_linkage_table (ef2id ef) = None.

Variable entry_pts_ok:
  forall ef i b,
  procedure_linkage_table (ef2id ef) = Some i -> 
  Genv.find_symbol ge (ef2id ef) = Some b -> 
  In (Vptr b Int.zero, Vptr b Int.zero, ef_sig ef) entry_points.

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

Lemma age_resource_decay': 
  forall jm jm',
  age jm jm' -> 
  resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
intros until jm'; intros AGE.
hnf.
split; auto.
hnf in AGE.
generalize AGE as AGE'; intro.
apply age1_levelS in AGE.
destruct AGE as [n LEV].
rewrite level_juice_level_phi in LEV; rewrite LEV.
apply age_level in AGE'.
do 2 rewrite level_juice_level_phi in AGE'.
rewrite LEV in AGE'.
inv AGE'; omega.
intros l; split.
solve[destruct jm; apply JMalloc; auto].
left.
hnf in AGE.
apply age1_juicy_mem_unpack in AGE.
destruct AGE as [X Y].
erewrite <-age1_resource_at; eauto.
solve[rewrite resource_at_approx; auto].
Qed.

Lemma inv_invariant_steps:
  forall n s jm z,
  level jm = S n -> 
  linker_inv (S n) s z jm -> 
  (exists s', exists jm', 
    corestep juicy_linker_sem ge s jm s' jm' /\
    linker_inv n s' z jm') \/
  (exists rv, safely_halted juicy_linker_sem s = Some rv) \/
  (exists ef, exists sig, exists args, exists x,
    ext_spec_pre Hspec ef x (sig_args sig) args z jm /\
    at_external juicy_linker_sem s = Some (ef, sig, args) /\
    forall rv jm' z', 
      ext_spec_post Hspec ef x (sig_res sig) rv z' jm' ->
      exists s', after_external juicy_linker_sem rv s = Some s' /\
      linker_inv n s' z' jm').
Proof.
intros until z; intros LEV INV.
destruct s.
hnf in INV.
destruct stack.
solve[simpl in stack_nonempty; elimtype False; omega].
destruct f.
hnf in INV.
destruct INV as [rguard_out [Hhered [SAFE TL_INV]]].
simpl in SAFE.
case_eq (at_external (get_module_csem (modules PF)) c).
intros [[ef sig] args] AT_EXT.
rewrite AT_EXT in SAFE.
unfold j_safely_halted in SAFE.
case_eq (safely_halted (get_module_csem (modules PF)) c).
intros rv HALT.
rewrite HALT in SAFE.
generalize (at_external_halted_excl (get_module_csem (modules PF)) c);
 intros [X|X]; try solve[congruence].
intros HALT.
rewrite HALT in SAFE.

(*CALL*)
destruct SAFE as [x [PRE POST]].
destruct (at_ext_plt_ok PF c AT_EXT) as [X|X].

Focus 2.
(*LINKER_AT_EXTERNAL*)
right; right.
exists ef; exists sig; exists args; exists x.
split; auto.
split.
simpl.
rewrite AT_EXT.
destruct ef; auto.
assert (forall sg, ef2id (EF_external name sg) = name) as ->.
 intro sg0.
 solve[generalize (ef2id_ok (EF_external name sg0)); hnf; auto].
solve[rewrite X; auto].
intros rv jm' z' Hpost.
destruct (POST rv jm' z' Hpost) as [c' [AFTER_EXT SAFE']].
exists (mkLinkerCoreState (mkFrame i PF c' :: stack) 
  stack_nonempty callers_at_external).
split; auto.
simpl.
rewrite AFTER_EXT; auto.
assert (length_cons (mkFrame i PF c') stack = stack_nonempty) as -> 
 by apply proof_irr.
solve[auto].
hnf.
exists rguard_out; exists Hhered.
split; auto.
solve[apply tl_inv_downward; auto].

destruct  X as [j [NEQ [LOOKUP [b [GENV HEQ]]]]].
generalize (plt_ok _ _ LOOKUP); intros PFJ.
destruct (mk_initial_core_succeeds PFJ (Vptr b (Int.repr 0)) args) as [c' INIT].
assert (CALLERS: all_at_external fT vT modules
  (tl (mkFrame j PFJ c' :: mkFrame i PF c :: stack))).
 unfold all_at_external; constructor; auto.
 solve[exists ef; exists sig; exists args; auto].
left.
exists (mkLinkerCoreState (mkFrame j PFJ c' :: mkFrame i PF c :: stack) 
 (length_cons _ _) CALLERS).
assert (exists jm', age jm jm') as [jm' AGE].
 apply levelS_age1 in LEV.
 solve[apply LEV].
exists jm'.
split.
unfold juicy_linker_sem; simpl; unfold jstep; simpl.
split.
assert (AT_EXT': 
   at_external (get_module_csem (modules PF)) c = 
   Some (EF_external (ef2id ef) sig, sig, args)).
 rewrite AT_EXT.
 repeat f_equal; auto.
generalize (@link_call 
 F V _ _ _ _ 
 procedure_linkage_table plt_ok 
 _ entry_points ge stack
 _ _ _ _ _ b _ (m_dry jm) _ c' 
 LOOKUP NEQ AT_EXT'); intro LINK.
assert (m_dry jm'=m_dry jm) as ->.
 solve[symmetry; apply age_jm_dry; auto].
assert (PFJ=plt_ok (ef2id ef) j LOOKUP) as -> by apply proof_irr.
apply LINK; auto.
assert (Hsig: ef_sig ef = sig).
 admit. (*will go away after cleanup of CoreSemantics to get rid of sig*)
rewrite <-Hsig.
solve[fold Int.zero; eapply entry_pts_ok; eauto].
split.
apply age_resource_decay'; auto.
apply age_level in AGE.
do 2 rewrite level_juice_level_phi in AGE.
solve[apply AGE].
(*INVARIANT*)
hnf.
exists (ext_spec_post Hspec ef x (sig_res (ef_sig ef))).
assert (Hhered0: forall rv z0, 
 hereditary age (ext_spec_post Hspec ef x (sig_res (ef_sig ef)) rv z0)).
 intros rv z0.
 solve[eapply JE_post_hered; eauto].
exists Hhered0.
split.
assert (Hgenv: Genv.find_symbol 
 (get_module_genv (modules (plt_ok _ j LOOKUP))) (ef2id ef) = Some b).
 exploit ge_agree; eauto.
 unfold genvs_agree; intros [? ?].
 solve[erewrite <-H; auto].
generalize (@modules_verified 
 j (plt_ok _ j LOOKUP) ef
 b (sig_args sig) args x (S n) z c' jm LOOKUP Hgenv); intros VERIF.
spec VERIF; auto.
solve[assert (plt_ok (ef2id ef) j LOOKUP=PFJ) as -> by apply proof_irr; auto].
spec VERIF; auto.
destruct VERIF as [VERIF WELLTYPED].
generalize (@age_safe
 _ _ _ (get_module_csem (modules (plt_ok (ef2id ef) j LOOKUP))) _
 (j_upd_rguard Hspec
   (ext_spec_post Hspec ef x (sig_res (ef_sig ef))) Hhered0) _ _ AGE
   (get_module_genv (modules (plt_ok (ef2id ef) j LOOKUP))) z c').
intros SAFE.
rewrite LEV in SAFE.
spec SAFE; auto.
assert (n = level jm') as ->.
 cut (S n = S (level jm')).
 inversion 1; auto.
 solve[rewrite <-LEV; apply age_level; auto].
assert (plt_ok (ef2id ef) j LOOKUP=PFJ) as <- by apply proof_irr.
solve[apply SAFE; auto].
hnf.
exists rguard_out.
exists Hhered.
split; simpl.
intros ret jm0 z0 Hpost.
assert (Hsig: ef_sig ef = sig).
 admit. (*will go away after cleanup of CoreSemantics to get rid of sig*)
rewrite Hsig in *.
destruct (POST ret jm0 z0 Hpost) as [c'' [AFTER_EXT SAFE]].
exists c''.
split; auto.
solve[apply tl_inv_downward; auto].

intros AT_EXT_NONE.
rewrite AT_EXT_NONE in SAFE.
unfold j_safely_halted in SAFE.
case_eq (safely_halted (get_module_csem (modules PF)) c).
intros rv HALT.
rewrite HALT in SAFE.
destruct stack.
(*HALTED*)
right.
left.
solve[exists rv; auto].

(*RETURN*)
destruct f as [j PFJ c'].
left.
hnf in TL_INV.
destruct TL_INV as [rguard_out0 [Hhered0 [T1 T2]]].
hnf in T1.
destruct (T1 (Some rv) jm z SAFE) as [c'' [AFTER_EXT SAFE'']].
hnf in callers_at_external.
inversion callers_at_external; subst.
exists (mkLinkerCoreState (mkFrame j PFJ c'' :: stack) 
  (length_cons _ _) H2).
assert (exists jm', age jm jm') as [jm' AGE].
 apply levelS_age1 in LEV.
 destruct LEV as [jm' AGE].
 solve[exists jm'; auto].
exists jm'.
split.
hnf; simpl.
split.
destruct H1 as [ef [sig [args AT_EXT']]].
generalize AT_EXT' as AT_EXT0; intro.
generalize (@link_return F V num_modules cT fT vT
 procedure_linkage_table plt_ok modules entry_points
 ge stack j i c' (m_dry jm) PFJ c c'' rv ef sig args PF AT_EXT' HALT); 
 intros RETURN.
assert (m_dry jm'=m_dry jm) as ->.
 solve[symmetry; apply age_jm_dry; auto].
apply RETURN; auto.
admit. (*return val has right type*)
split; auto.
solve[apply age_resource_decay'; auto].
generalize AGE as AGE'; intro.
apply age1_levelS in AGE.
destruct AGE as [m LEV'].
rewrite level_juice_level_phi in LEV; rewrite LEV.
apply age_level in AGE'.
do 2 rewrite level_juice_level_phi in AGE'.
rewrite LEV in AGE'.
solve[inv AGE'; omega].
(*INVARIANT*)
hnf.
exists rguard_out0.
exists Hhered0.
split; auto.
rewrite <-LEV in SAFE''.
assert (n = level jm') as ->.
generalize AGE as AGE'; intro.
apply age1_levelS in AGE.
destruct AGE as [m LEV'].
rewrite level_juice_level_phi in LEV.
apply age_level in AGE'.
do 2 rewrite level_juice_level_phi in AGE'.
rewrite LEV in AGE'.
solve[inv AGE'; auto].
eapply age_safe; eauto.
solve[apply tl_inv_downward; auto].

(*CORESTEP*)
intros HALT.
rewrite HALT in SAFE.
destruct SAFE as [c' [jm' [CORESTEP SAFE]]].
left.
exists (mkLinkerCoreState (mkFrame i PF c' :: stack) 
 stack_nonempty callers_at_external).
exists jm'.
split; auto.
hnf; simpl.
destruct CORESTEP.
split; auto.
apply link_step; auto.
(*INVARIANT*)
hnf.
exists rguard_out.
exists Hhered.
split; auto.
solve[apply tl_inv_downward; auto].
Qed.

Definition main_sig : signature := mksignature nil (Some AST.Tint).

Lemma initial_inv:
  forall x b c jm z,
  ext_spec_pre Hspec (EF_external main_id main_sig) x nil nil z jm -> 
  Genv.find_symbol ge main_id = Some b -> 
  make_initial_core juicy_linker_sem ge (Vptr b Int.zero) nil = Some c -> 
  linker_inv (level jm) c z jm.
Proof.
intros until z.
intros PRE FIND INIT.
remember (level jm) as n.
hnf.
destruct c.
hnf.
destruct stack; auto.
destruct f.
hnf.
exists (ext_spec_post Hspec (EF_external main_id main_sig) x (Some AST.Tint)).
assert (Hhered: forall rv z, hereditary age
  (ext_spec_post Hspec (EF_external main_id main_sig) x (Some Tint) rv z)).
 solve[intros; apply JE_post_hered].
exists Hhered.
simpl.
simpl in INIT.
rewrite FIND in INIT.
if_tac in INIT; try solve[elimtype False; omega].
case_eq (procedure_linkage_table main_id).
intros b0 PLT.
revert INIT.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT; intros _ ?.
intros H1.
case_eq (make_initial_core
  (get_module_csem (modules (plt_ok main_id b0 (Logic.eq_sym e))))
  (get_module_genv (modules (plt_ok main_id b0 (Logic.eq_sym e))))
  (Vptr b Int.zero) nil).
intros c' INIT.
rewrite INIT in H1.
inv H1.
simpl; split; auto.

Focus 2.
intros INIT.
rewrite INIT in H1; congruence.

Focus 2.
intros PLT.
revert INIT.
generalize (refl_equal (procedure_linkage_table main_id)).
generalize PLT.
pattern (procedure_linkage_table main_id) at 0 2 4.
rewrite PLT; intros _ ? ?; congruence.

assert (Heq: ef2id (EF_external main_id main_sig) = main_id).
 solve[apply (ef2id_ok (EF_external main_id main_sig))].
exploit modules_verified; eauto.
solve[rewrite Heq; auto].
generalize (ge_agree PF); intros [A1 A2].
rewrite A1 in FIND.
assert (plt_ok main_id i (Logic.eq_sym e) = PF) as -> by apply proof_irr.
solve[rewrite Heq; auto].
instantiate  (1 := level (m_phi jm)).
intros [SAFE TY].
simpl in SAFE.
assert (PF = plt_ok main_id i (Logic.eq_sym e)) as -> by apply proof_irr.
apply Eqdep.EqdepTheory.inj_pair2 in H3.
inv H3.
solve[apply SAFE].
Qed.

Definition main_post: option val -> Z -> juicy_mem -> Prop := 
  fun rv z jm => True.

Lemma main_post_hered: forall rv z, hereditary age (main_post rv z).
Proof. solve[intros rv z; unfold main_post, hereditary; auto]. Qed.

Lemma inv_safe: 
  forall c z jm,
  linker_inv (level jm) c z jm -> 
  safeN juicy_linker_sem (j_upd_rguard Hspec main_post main_post_hered)
    ge (level jm) z c jm.
Proof.
intros c z jm INV.
remember (level jm) as n.
revert c z jm INV Heqn.
induction n.
solve[simpl; auto].
intros c z jm INV Heqn; hnf.
apply inv_invariant_steps in INV; auto.
destruct INV as [INV|[INV|INV]].
destruct INV as [s' [jm' [STEP INV]]].
generalize STEP as STEP0; intro.
apply corestep_not_at_external in STEP0.
rewrite STEP0.
generalize STEP as STEP1; intro.
apply corestep_not_halted in STEP1.
rewrite STEP1.
exists s'; exists jm'; split; auto.
apply IHn; auto.
hnf in STEP.
destruct STEP as [? [? ?]].
rewrite <-Heqn in H1.
solve[inv H1; auto].
destruct INV as [rv HALT].
generalize (at_external_halted_excl juicy_linker_sem c); intros [X|X].
rewrite X.
rewrite HALT.
destruct c.
simpl in HALT.
destruct stack; try solve[congruence].
destruct f.
destruct stack; try solve[congruence].
solve[simpl; unfold main_post; auto].
congruence.
destruct INV as [ef [sig [args [x [PRE [AT_EXT POST]]]]]].
rewrite AT_EXT.
case_eq (safely_halted juicy_linker_sem c).
intros rv HALT.
generalize (at_external_halted_excl juicy_linker_sem c); intros [X|X];
 congruence.
intros HALT.

(*AT_EXTERNAL*)
exists x.
split; auto.
intros rv jm' z' Hpost.
destruct (POST rv jm' z' Hpost) as [s' [AFTER INV]].
exists s'.
split; auto.
assert (Heq: level jm' = n) by admit. (*not true in general; must do wf-induction on nat lt 
                                         and expose somehow that level jm' < level jm*)
rewrite <-Heq in *.
apply IHn; auto.
Qed.

Lemma linker_safety:
  forall x b c jm z,
  ext_spec_pre Hspec (EF_external main_id main_sig) x nil nil z jm -> 
  Genv.find_symbol ge main_id = Some b -> 
  make_initial_core juicy_linker_sem ge (Vptr b Int.zero) nil = Some c -> 
  safeN juicy_linker_sem (j_upd_rguard Hspec main_post main_post_hered) 
    ge (level jm) z c jm.
Proof.
intros until z; intros GENV FIND INIT.
exploit initial_inv; eauto; intro INV.
solve[apply inv_safe; auto].
Qed.

End JuicyLinkerSafe.  
