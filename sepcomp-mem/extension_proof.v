Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations. 
Require Import sepcomp.rg_forward_simulations. 
Require Import sepcomp.compile_safe.
Require Import sepcomp.step_lemmas. 
Require Import sepcomp.extspec. 
Require Import sepcomp.extension.
Require Import sepcomp.extension_simulations.
Require Import sepcomp.Coqlib2.
Require Import sepcomp.wf_lemmas.

Require Import AST.
Require Import Values.
Require Import sepcomp.Globalenvs.
Require Import sepcomp.Events.
Require Import sepcomp.Memory.
Require Import Coqlib.

Set Implicit Arguments.

(* TEMPORARY HACK:
  use this "remember" tactic instead of the standard library one *)
Tactic Notation "remember" constr(a) "as" ident(x) :=
   let x := fresh x in
  let H := fresh "Heq" x in
  (set (x:=a) in *; assert (H: x=a) by reflexivity; clearbody x).

(*TODO: move this lemma somewhere above extension_proof.v and 
   extension_proof_safety.v*)
Lemma runnable_false (G C M D: Type) (csem: CoreSemantics G C M D): 
 forall c, runnable csem c=false -> 
 (exists rv, safely_halted csem c = Some rv) \/
 (exists ef, exists sig, exists args, 
   at_external csem c = Some (ef, sig, args)).
Proof.
intros c; unfold runnable.
destruct (at_external csem c).
destruct p as [[ef sig] vals].
intros; right; do 2 eexists; eauto.
destruct (safely_halted csem c).
intros; left; eexists; eauto.
congruence.
Qed.

Lemma genvs_domain_eq_refl: forall F V (ge: Genv.t F V), genvs_domain_eq ge ge.
Proof. solve[intros F V ge; unfold genvs_domain_eq; split; intro b; split; auto]. Qed.

Section CoreCompatibleLemmas. Variables
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: EffectfulSemantics G xT D) (** extended semantics *)
 (esig: ef_ext_spec mem Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
(** a set of core semantics *)
 (csem: forall i:nat, EffectfulSemantics (gT i) (cT i) (dT i)) 
 (csig: ef_ext_spec mem Z). (** client signature *)

 Variables (ge: G) (genv_map : forall u:nat, gT u).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

Variable Hcore_compatible: core_compatible ge genv_map E.

Import Extension.

Lemma corestep_step: 
  forall u s (c: cT u) m c' m',
  proj_core E (active E s) u s = Some c -> 
  corestep (csem u) (genv_map u) c m c' m' -> 
  exists s', corestep esem ge s m s' m' /\
    active E s = active E s' /\ proj_core E (active E s) u s' = Some c'.
Proof.
intros until m'; intros H0 H1.
inv Hcore_compatible.
generalize H1 as H1'; intro.
eapply corestep_prog in H1; eauto.
destruct H1 as [s' H1].
exists s'.
split; auto.
split; auto.
exploit corestep_pres; eauto.
solve[intros [? [? ?]]; auto].
exploit corestep_pres; eauto.
solve[intros [? [? ?]]; auto].
Qed.

Lemma corestep_stepN: 
  forall n u s (c: cT u) m c' m',
  proj_core E (active E s) u s = Some c -> 
  corestepN (csem u) (genv_map u) n c m c' m' -> 
  exists s', corestepN esem ge n s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) u s' = Some c'.
Proof.
inv Hcore_compatible.
generalize corestep_step; intro H1.
intros n.
induction n; auto.
intros until m'.
intros H0 H2.
inv H2.
simpl.
exists s.
split; auto.
intros.
simpl in H0.
destruct H0 as [c2 [m2 [H5 H6]]].
eapply H1 in H5; eauto.
destruct H5 as [s2 [H5 [H7 H9]]].
forget (active E s) as i.
subst i.
destruct (IHn u s2 c2 m2 c' m') as [s' [H10 [H11 H13]]]; auto.
exists s'.
split3.
simpl.
exists s2; exists m2; split; eauto.
auto.
auto.
Qed.

Lemma corestep_step_star: 
  forall u s (c: cT u) m c' m',
  proj_core E (active E s) u s = Some c -> 
  corestep_star (csem u) (genv_map u) c m c' m' -> 
  exists s', corestep_star esem ge s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) u s' = Some c'.
Proof.
intros until m'; intros H0 H1.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 [H2 H4]]].
exists s'.
split3; auto.
solve[exists n; eauto].
Qed.

Lemma corestep_step_plus: 
  forall u s (c: cT u) m c' m',
  proj_core E (active E s) u s = Some c -> 
  corestep_plus (csem u) (genv_map u) c m c' m' -> 
  exists s', corestep_plus esem ge s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) u s' = Some c'.
Proof.
intros until m'; intros H0 H1.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 [H2 H4]]].
exists s'.
split3; auto.
solve[exists n; eauto].
Qed.

Lemma owned_valid_inv:
  forall u s s' (x x': cT u) m m' n,
  proj_core E (active E s) u s = Some x -> 
  owned_valid esem csem E s m -> 
  corestepN (csem u) (genv_map u) n x m x' m' -> 
  corestepN esem ge n s m s' m' -> 
  proj_core E (active E s) u s' = Some x' ->
  owned_valid esem csem E s' m'.
Proof.
intros until n; intros H1 H2 H3 H4 H5.
intros i u' x'' PROJ b ofs PRIV.
assert (H6: Mem.nextblock m <= Mem.nextblock m').
 apply corestepN_fwd in H3.
 solve[apply forward_nextblock in H3; auto].
destruct (eq_nat_dec i (active E s)). subst.
assert (u = u') by (eapply proj_core_types; eauto).
subst.
rewrite PROJ in H5; inv H5.
assert (H5: {effects (csem u') x AllocEffect b ofs}+
            {~effects (csem u') x AllocEffect b ofs}) 
 by apply effects_dec.
destruct H5 as [H5|H5].
specialize (H2 (active E s) u' x H1 b ofs H5).
omega.
eapply effects_newN in PRIV; eauto.
solve[destruct PRIV; auto].
cut (proj_core E i u' s = Some x''). intro H7.
unfold owned_valid in H2.
specialize (H2 i u' x'' H7 b ofs PRIV).
assert (H8: Mem.nextblock m <= Mem.nextblock m').
 apply corestepN_fwd in H3.
 solve[apply forward_nextblock in H3; auto].
omega.
inv Hcore_compatible.
eapply corestep_others_backward with (i := i) in H3; eauto.
solve[rewrite H3; auto].
Qed.

Lemma owned_dec: forall i x b ofs,
  {effects (csem i) x AllocEffect b ofs}+
  {~effects (csem i) x AllocEffect b ofs}.
Proof.
intros.
apply effects_dec; auto.
Qed.

Lemma owned_valid_after_ext: 
  forall u s s' (x x': cT u) m m' ef sig args retv, 
  proj_core E (active E s) u s = Some x -> 
  owned_valid esem csem E s m -> 
  at_external (csem u) x = Some (ef, sig, args) -> 
  after_external (csem u) retv x = Some x' -> 
  after_external esem retv s = Some s' -> 
  proj_core E (active E s) u s' = Some x' ->
  mem_forward m m' -> 
  owned_valid esem csem E s' m'.
Proof.
intros until retv; intros PROJ PRIV AT AFTER AFTER' PROJ' FWD.
intros i u' c PROJC b ofs PRIVB.
destruct (eq_nat_dec i (active E s)).
subst.
destruct (owned_dec x b ofs). 
unfold owned_valid in PRIV.
cut (b < Mem.nextblock m). intro H1.
cut (Mem.nextblock m <= Mem.nextblock m'). intro H2.
omega.
solve[apply forward_nextblock in FWD; auto].
eapply PRIV; eauto.
assert (u = u').
 solve[eapply proj_core_types; eauto].
subst.
rewrite PROJC in PROJ'; inv PROJ'.
eapply effects_external in AFTER; eauto.
destruct AFTER.
solve[elimtype False; eauto].
assert (proj_core E i u' s = Some c).
 inv Hcore_compatible.
 rewrite after_ext_others with (retv := retv) (s' := s'); auto.
unfold owned_valid in PRIV.
cut (b < Mem.nextblock m). intro H1.
cut (Mem.nextblock m <= Mem.nextblock m'). intro H2.
omega.
solve[apply forward_nextblock in FWD; auto].
solve[eapply PRIV; eauto].
Qed.

Lemma owned_disjoint_after_ext: 
  forall u s s' (x x': cT u) ef sig args retv, 
  proj_core E (active E s) u s = Some x -> 
  owned_disjoint esem csem E s -> 
  at_external (csem u) x = Some (ef, sig, args) -> 
  after_external (csem u) retv x = Some x' -> 
  after_external esem retv s = Some s' -> 
  proj_core E (active E s) u s' = Some x' ->
  owned_disjoint esem csem E s'.
Proof.
intros until retv; intros PROJ PRIV AT AFTER AFTER' PROJ'.
unfold owned_disjoint.
intros until d; intros NEQ PROJC PROJD b ofs PRIVATE CONTRA.
destruct (eq_nat_dec i (active E s)).
subst.
assert (u = i').
 solve[eapply proj_core_types; eauto].
subst.
rewrite PROJ' in PROJC.
inv PROJC.
eapply effects_external in PRIVATE; eauto.
inv Hcore_compatible.
eapply after_ext_others in AFTER'; eauto.
rewrite <-AFTER' in *; clear AFTER'.
solve[eapply PRIV; eauto].
destruct (eq_nat_dec j (active E s)).
subst.
assert (j' = u).
 solve[eapply proj_core_types; eauto].
subst.
rewrite PROJ' in PROJD.
inv PROJD.
eapply effects_external in CONTRA; eauto.
inv Hcore_compatible.
apply after_ext_others with (j := i) (j0 := i') in AFTER'; eauto.
rewrite <-AFTER' in *; clear AFTER'.
solve[eapply PRIV; eauto].
generalize AFTER' as AFTER''; intro.
inv Hcore_compatible.
apply after_ext_others with (j := i) (j0 := i') in AFTER'; eauto.
apply after_ext_others with (j := j) (j0 := j') in AFTER''; eauto.
rewrite <-AFTER' in *; clear AFTER'.
rewrite <-AFTER'' in *; clear AFTER''.
specialize (PRIV i j i' j' c d NEQ PROJC PROJD b ofs PRIVATE CONTRA).
solve[auto].
Qed.

Lemma owned_disjoint_inv:
  forall u s s' (x x': cT u) m m' n,
  proj_core E (active E s) u s = Some x -> 
  owned_valid esem csem E s m -> 
  owned_disjoint esem csem E s -> 
  corestepN (csem u) (genv_map u) n x m x' m' -> 
  corestepN esem ge n s m s' m' -> 
  proj_core E (active E s) u s' = Some x' ->
  owned_disjoint esem csem E s'.
Proof. 
intros until n; intros H1 VAL H2 H3 H4 H5.
intros i j w y c d H6 H7 H8.
destruct (eq_nat_dec i (active E s)). subst.
cut (proj_core E j y s = Some d). intro H9.
assert (u = w).
 solve[eapply proj_core_types; eauto].
subst.
rewrite H5 in H7; inv H7.
intros b ofs H7 CONTRA.
assert (H10: ~effects (csem w) x AllocEffect b ofs).
assert (Hneq: j<>active E s) by auto.
 solve[apply (H2 j (active E s) y w d x Hneq H9 H1); auto].
generalize H3 as H3'; intro.
eapply effects_newN in H3; eauto.
specialize (VAL j y d H9 b ofs CONTRA).
omega.
inv Hcore_compatible.
solve[erewrite corestep_others_backward; eauto].
destruct (eq_nat_dec j (active E s)). subst.
cut (proj_core E i w s = Some c). intro H9.
assert (u = y).
 solve[eapply proj_core_types; eauto].
subst.
rewrite H5 in H8; inv H8.
intros b ofs H8 CONTRA.
assert (H10: ~effects (csem y) x AllocEffect b ofs).
assert (Hneq: i<>active E s) by auto.
 solve[apply (H2 i (active E s) w y c x Hneq H9 H1); auto].
generalize H3 as H3'; intro.
eapply effects_newN in H3; eauto.
specialize (VAL i w c H9 b ofs H8).
omega.
inv Hcore_compatible.
solve[erewrite corestep_others_backward; eauto].
intros.
eapply H2 with (i := i) (j := j) (i' := w) (j' := y); eauto.
inv Hcore_compatible.
solve[erewrite corestep_others_backward; eauto].
inv Hcore_compatible.
solve[erewrite corestep_others_backward; eauto].
Qed.

End CoreCompatibleLemmas.

Lemma meminj_preserves_genv2blocks: 
  forall {F V: Type} (ge: Genv.t F V) j,
  meminj_preserves_globals_ind (genv2blocks ge) j <->
  Events.meminj_preserves_globals ge j.
Proof.
intros ge; split; intro H1.
unfold meminj_preserves_globals in H1.
unfold Events.meminj_preserves_globals.
destruct H1 as [H1 [H2 H3]].
split.
intros.
apply H1; auto.
unfold genv2blocks.
unfold Genv.find_symbol in H.
simpl; exists id; auto.
split.
intros b gv H4.
apply H2; auto.
unfold genv2blocks.
unfold Genv.find_var_info in H4.
simpl; exists gv; auto.
intros until gv; intros H4 H5.
symmetry.
eapply H3; eauto.
unfold genv2blocks.
unfold Genv.find_var_info in H4.
simpl; exists gv; auto.
unfold meminj_preserves_globals.
destruct H1 as [H1 [H2 H3]].
split. 
intros b H4.
unfold genv2blocks in H4.
destruct H4; eapply H1; eauto.
split.
intros b H4.
destruct H4; eapply H2; eauto.
intros b1 b2 delta H4 H5.
unfold genv2blocks in H4.
destruct H4.
eapply H3 in H; eauto.
Qed.

Lemma genvs_domain_eq_preserves:
  forall {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) j,
  genvs_domain_eq ge1 ge2 -> 
  (meminj_preserves_globals_ind (genv2blocks ge1) j <-> 
   meminj_preserves_globals_ind (genv2blocks ge2) j).
Proof.
intros until j; intros H1.
unfold meminj_preserves_globals.
destruct H1 as [DE1 DE2].
split; intros [H2 [H3 H4]].
split.
intros b H5.
cut (fst (genv2blocks ge1) b).
 intros H6.
apply (H2 b H6).
apply (DE1 b); auto.
split.
intros b H5.
apply H3; eauto.
apply DE2; auto.
intros b1 b2 delta H5 H6.
eapply H4; eauto.
apply DE2; auto.
split.
intros b H5.
eapply H2; eauto.
apply DE1; auto.
split.
intros b H5.
apply H3; auto.
apply DE2; auto.
intros until delta; intros H5 H6.
eapply H4; eauto.
apply DE2; auto.
Qed.

Lemma genvs_domain_eq_sym:
  forall {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2),
  genvs_domain_eq ge1 ge2 -> genvs_domain_eq ge2 ge1.
Proof.
intros until ge2.
unfold genvs_domain_eq; intros [H1 H2].
split; intro b; split; intro H3; 
 solve[destruct (H1 b); auto|destruct (H2 b); auto].
Qed.

Lemma exists_ty: forall v, exists ty, Val.has_type v ty.
Proof.
intros v.
destruct v.
exists Tint; simpl; auto.
exists Tint; simpl; auto.
exists Tfloat; simpl; auto.
exists Tint; simpl; auto.
Qed.

Module ExtendedSimulations. Section ExtendedSimulations.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
 (** a set of core semantics *)
  (csemS: forall i:nat, 
    EffectfulSemantics (Genv.t (fS i) (vS i)) (cS i) (dS i)) 
 (** a set of core semantics *)
  (csemT: forall i:nat, 
    EffectfulSemantics (Genv.t (fT i) (vT i)) (cT i) (dT i)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (threads_max: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall u:nat, Genv.t (fS u) (vS u))
  (genv_mapT: forall u:nat, Genv.t (fT u) (vT u)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature).

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation MAX_CORES := (Extension.proj_max_cores).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation zint_invar_after_external := (Extension.zint_invar_after_external).

 Variable core_data: forall u: nat, Type.
 Variable match_state: forall u: nat, 
   core_data u -> meminj -> cS u -> mem -> cT u -> mem -> Prop.
 Variable core_ord: forall u: nat, core_data u -> core_data u -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Import Forward_simulation_inj_exposed.

 Variable core_simulations: forall u:nat, 
   Forward_simulation_inject (dS u) (dT u) (csemS u) (csemT u) (genv_mapS u) (genv_mapT u) 
   entry_points (core_data u) (match_state u) (core_ord u).

 Variable match_inject: forall i cd j c1 m1 c2 m2,
   match_state i cd j c1 m1 c2 m2 -> 
   Mem.inject j m1 m2.

 Variable R: meminj -> xS -> mem -> xT -> mem -> Prop.

 Definition core_datas := forall u i: nat, core_data u.

 Variable num_modules: nat.

 Definition core_ords (max_cores: nat) (cd1 cd2: core_datas) :=
  prod_ord' 
    (fun u => forall i:nat, core_data u)
    (fun u cd1' cd2' => 
      prod_ord' 
        (fun i => core_data u)
        (fun i => core_ord u)
        max_cores max_cores 
        (data_prod' _ _ _ cd1') (data_prod' _ max_cores max_cores cd2'))
    num_modules num_modules
    (data_prod' _ _ _ cd1) (data_prod' _ num_modules num_modules cd2).

 Definition core_datas_upd (u i: nat) (cdi': core_data u) (cd: core_datas): core_datas :=
   data_upd _ u (data_upd _ i cdi' (cd u)) cd.
 Implicit Arguments core_datas_upd [].

 Lemma core_datas_upd_ord (max_cores: nat) cd u i (cdi': core_data u) :
   (u < num_modules)%nat -> 
   (i < max_cores)%nat -> 
   core_ord u cdi' (cd u i) -> 
   core_ords max_cores (core_datas_upd u i cdi' cd) cd.
 Proof.
 intros H1 H2 H3. 
 unfold core_ords.
 apply prod_ord_upd; auto.
 apply prod_ord_upd; auto.
 solve[split; try solve[auto|omega]].
 solve[split; try solve[auto|omega]].
 Qed.

 Lemma core_ords_wf: forall n, well_founded (core_ords n).
 Proof. 
 intro n.
 unfold core_ords.
 apply wf_funct.
 apply wf_prod_ord.
 intros u.
 apply wf_funct.
 apply wf_prod_ord.
 intros _.
 solve[destruct (core_simulations u); auto].
 Qed.

 Definition match_states (cd: core_datas) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   owned_valid esemS csemS E_S s1 m1 /\ 
   owned_disjoint esemS csemS E_S s1 /\ 
   owned_valid esemT csemT E_T s2 m2 /\ 
   owned_disjoint esemT csemT E_T s2 /\
   core_semantics.effects_valid esemS s1 m1 /\ 
   core_semantics.effects_valid esemT s2 m2 /\
   mem_wd m1 /\ mem_wd m2 /\
   effects_guarantee esemS s1 m1 /\ effects_guarantee esemT s2 m2 /\
   R j s1 m1 s2 m2 /\ 
   ACTIVE E_S s1=ACTIVE E_T s2 /\
   (forall b0 delta b ofs, 
     j b0 = Some (b, delta) -> 
     reserved m1 b0 (ofs-delta) -> reserved m2 b ofs) /\
   (*invariant on active cores*)
   (forall u c1, 
     PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
     effects_guarantee (csemS u) c1 m1 /\
     (exists z: Z, 
       compile_safe (csemS u) z c1 m1) /\
     exists c2, PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 /\ 
       effects_guarantee (csemT u) c2 m2 /\
       match_state u (cd u (ACTIVE E_S s1)) j c1 m1 c2 m2) /\
   (*invariant on inactive cores*)
   (forall i u c1, 
     i <> ACTIVE E_S s1 -> 
     PROJ_CORE E_S i u s1 = Some c1 -> 
     exists c2, PROJ_CORE E_T i u s2 = Some c2 /\ 
     exists cd0 j0 m10 m20,
       effects_guarantee (csemS u) c1 m10 /\
       (exists z: Z, compile_safe (csemS u) z c1 m10) /\
       effects_guarantee (csemT u) c2 m20 /\
       match_state u cd0 j0 c1 m10 c2 m20).

 Variable max_cores: nat. (*TODO: fixme*)

 Inductive internal_compilability_invariant: Type := 
 InternalCompilabilityInvariant: forall 
 (match_state_runnable: forall i cd j c1 m1 c2 m2,
   match_state i cd j c1 m1 c2 m2 -> runnable (csemS i) c1=runnable (csemT i) c2)

 (match_state_inj: forall i cd j c1 m1 c2 m2,
   match_state i cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)

 (match_state_preserves_globals: forall i cd j c1 m1 c2 m2,
   match_state i cd j c1 m1 c2 m2 -> 
   Events.meminj_preserves_globals (genv_mapS i) j)

 (corestep_rel: forall cd j j' u s1 c1 m1 c1' m1' s2 c2 m2 c2' m2' s1' s2' n cd', 
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   match_states cd j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   meminj_preserves_globals_ind (genv2blocks ge_S) j -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   corestep (csemS u) (genv_mapS u) c1 m1 c1' m1' -> 
   corestepN (csemT u) (genv_mapT u) n c2 m2 c2' m2' ->
   corestep esemS ge_S s1 m1 s1' m1' -> 
   corestepN esemT ge_T n s2 m2 s2' m2' -> 
   match_state u cd' j' c1' m1' c2' m2' -> 
   effects_guarantee (csemS u) c1' m1' -> 
   effects_guarantee (csemT u) c2' m2' -> 
   R j' s1' m1' s2' m2')

 (after_external_rel: 
   forall cd j j' s1 m1 s2 m2 s1' m1' s2' m2' ret1 ret2 ef sig args1,
   match_states cd j s1 m1 s2 m2 -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   Mem.inject j' m1' m2' -> 
   mem_forward m1 m1'-> 
   mem_forward m2 m2' -> 
   rely esemS s1' m1 m1' -> 
   rely esemT s2' m2 m2' -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   after_external esemS ret1 s1 = Some s1' -> 
   after_external esemT ret2 s2 = Some s2' -> 
   val_has_type_opt ret1 (ef_sig ef) -> 
   val_has_type_opt ret2 (ef_sig ef) -> 
   val_inject_opt j' ret1 ret2 -> 
   R j' s1' m1' s2' m2')   

 (extension_diagram: forall u s1 m1 s1' m1' s2 c1 c2 m2 ef sig args1 args2 cd j,
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   runnable (csemS u) c1=false -> 
   runnable (csemT u) c2=false -> 
   at_external (csemS u) c1 = Some (ef, sig, args1) -> 
   at_external (csemT u) c2 = Some (ef, sig, args2) -> 
   match_states cd j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args (ef_sig ef)) -> 
   corestep esemS ge_S s1 m1 s1' m1' -> 
   effects_guarantee esemS s1' m1' -> 
   exists s2', exists m2', exists cd', exists j',
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     effects_guarantee esemT s2' m2' /\
     match_states cd' j' s1' m1' s2' m2' /\
     ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
      corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ords max_cores cd' cd))

 (at_external_match: forall u s1 m1 s2 c1 c2 m2 ef sig args1 args2 cd j,
   ACTIVE E_S s1=ACTIVE E_T s2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   runnable (csemS u) c1=runnable (csemT u) c2 -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   at_external (csemS u) c1 = Some (ef, sig, args1) -> 
   match_state u cd j c1 m1 c2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args (ef_sig ef)) -> 
   at_external (csemT u) c2 = Some (ef, sig, args2) -> 
   at_external esemT s2 = Some (ef, sig, args2))

 (make_initial_core_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 j sig,
   In (v1, v2, sig) entry_points -> 
   make_initial_core esemS ge_S v1 vals1 = Some s1 -> 
   Mem.inject j m1 m2 -> 
   mem_wd m1 -> 
   mem_wd m2 -> 
   Forall2 (val_inject j) vals1 vals2 -> 
   Forall2 Val.has_type vals2 (sig_args sig) -> 
   exists cd, exists s2, 
     make_initial_core esemT ge_T v2 vals2 = Some s2 /\
     match_states cd j s1 m1 s2 m2)
 
 (safely_halted_step: forall cd j c1 m1 c2 m2 v1 rty,
   match_states cd j c1 m1 c2 m2 -> 
   safely_halted esemS c1 = Some v1 -> 
   Val.has_type v1 rty -> 
   exists v2, val_inject j v1 v2 /\
     safely_halted esemT c2 = Some v2 /\ 
     Val.has_type v2 rty /\ 
     Mem.inject j m1 m2)

 (safely_halted_diagram: forall u cd j m1 m1' m2 rv1 s1 s2 s1' c1 c2,
   match_states cd j s1 m1 s2 m2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   safely_halted (csemS u) c1 = Some rv1 -> 
   corestep esemS ge_S s1 m1 s1' m1' ->  
   effects_guarantee esemS s1' m1' -> 
   exists rv2, 
     safely_halted (csemT u) c2 = Some rv2 /\
     val_inject j rv1 rv2 /\ 
     exists s2', exists m2', exists cd', exists j', 
       inject_incr j j' /\
       Events.inject_separated j j' m1 m2 /\
       corestep esemT ge_T s2 m2 s2' m2' /\
       match_states cd' j' s1' m1' s2' m2' /\
       effects_guarantee esemT s2' m2'),
  internal_compilability_invariant.

 Variables 
  (esig_compilable: internal_compilability_invariant)
  (genvs_domain_eqS: forall i: nat, genvs_domain_eq ge_S (genv_mapS i))
  (genvs_domain_eqT: forall i: nat, genvs_domain_eq ge_T (genv_mapT i))
  (core_compatS: core_compatible ge_S genv_mapS E_S) 
  (core_compatT: core_compatible ge_T genv_mapT E_T)
  (owned_conservS: owned_conserving esemS csemS E_S)
  (owned_conservT: owned_conserving esemT csemT E_T)
  (active_okS: (forall x_s, ACTIVE E_S x_s < max_cores)%nat)
  (active_okT: (forall x_t, ACTIVE E_T x_t < max_cores)%nat)
  (new_effects_alignedT: new_effects_aligned esemT csemT ge_T genv_mapT E_T).

Program Definition extended_simulation: 
  Forward_simulation_inject D_S D_T esemS esemT ge_S ge_T 
           entry_points core_datas match_states (core_ords max_cores) :=
  @Build_Forward_simulation_inject _ _ _ _ _ _ _ 
  esemS esemT ge_S ge_T entry_points core_datas match_states (core_ords max_cores) 
  _ _ _ _ _ _ _ _ _ _.
Next Obligation. apply core_ords_wf. Qed.
Next Obligation. 
unfold match_states in H.
destruct H as [? [? [? [? [RMV1 [RMV2 [? [? [WD1 [WD2 ?]]]]]]]]]].
solve[split; auto].
Qed.
Next Obligation. 
unfold match_states in H.
destruct H as [? [? [? [? [RMV1 [RMV2 ?]]]]]].
solve[split; auto].
Qed.
Next Obligation.
destruct H as 
 [? [? [? [EV1 [EV2 [WD1 [WD2 [? [? [JJ [RR [? [? [MATCH1 MATCH2]]]]]]]]]]]]]].
destruct (active_proj_core E_S c1) as [_u_ [c2' H7]].
specialize (MATCH1 _ _ H7).
destruct MATCH1 as [GR [c3 [PROJ [? [GR2 MATCH]]]]].
solve[eapply match_validblocks in MATCH; eauto].
Qed.
Next Obligation. 
destruct H as 
 [? [? [? [EV1 [EV2 [WD1 [WD2 [? [? [JJ [RR [? [? [MATCH1 MATCH2]]]]]]]]]]]]]].
solve[eauto].
Qed.
Next Obligation. 
rename H0 into MATCH.
generalize MATCH as MATCH'; intro.
destruct MATCH as [VAL1 [DISJ1 [VAL2 [DISJ2 [RVAL1 [RVAL2 
 [EV1 [EV2 [WD1 [WD2 [GR1 [GR2 [JJ [RR [ACT [MATCH_CORES1 MATCH_CORES2]]]]]]]]]]]]]]]].
rename H into STEP.
destruct (active_proj_core E_S st1) as [_u1_ [c1 PROJ1]].
destruct (active_proj_core E_T st2) as [_u2_ [c2 PROJ2]].
assert (exists c2':cT _u2_,
  PROJ_CORE E_T (ACTIVE E_S st1) _u2_ st2 = Some c2').
 clear - ACT c2 PROJ2.
 forget (ACTIVE E_S st1) as xx.
 forget (ACTIVE E_T st2) as yy.
 subst.
 solve[eexists; eauto].
clear c2 PROJ2.
destruct H as [c2 PROJ2].
case_eq (runnable (csemS _u1_) c1).

(*Case 1: runnable thread, appeal to core diagram for cores*)
intros RUN1.
assert (RUN2: runnable (csemT _u2_) c2=true).
 specialize (MATCH_CORES1 _ c1).
 spec MATCH_CORES1; auto.
 destruct MATCH_CORES1 as [GRc1 [SAFE [c2' [PROJ2' [GRc2 MTCH]]]]].
 assert (_u1_ = _u2_).
  solve[eapply Extension.proj_core_types; eauto].
 subst.
 inv esig_compilable.
 rewrite match_state_runnable 
  with (cd := cd _u2_ (ACTIVE E_S st1)) (r := r) (j := j) 
       (m1 := m1) (c2 := c2) (m2 := m2) in RUN1.
 solve[auto].
 rewrite PROJ2' in PROJ2.
 inv PROJ2.
 solve[auto].
assert (exists c1', corestep (csemS _u1_) (genv_mapS _u1_) 
         c1 m1 c1' m1') as [c1' STEP1].
 inv esig_compilable.
 inv core_compatS.
 specialize (runnable_corestep _ st1 m1 st1' m1' c1).
 destruct runnable_corestep as [c1' [H3 H4]]; auto.
 solve[exists c1'; auto].
assert (PROJ1': PROJ_CORE E_S (ACTIVE E_S st1) _u1_ st1' = Some c1').
 inv core_compatS.
 specialize (corestep_pres _ st1 c1 m1 c1' st1' m1' m1').
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 solve[destruct corestep_pres as [? [? ?]]; auto].
assert (ACT1': ACTIVE E_S st1 = ACTIVE E_S st1').
 inv core_compatS.
 specialize (corestep_pres _ st1 c1 m1 c1' st1' m1' m1').
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 solve[destruct corestep_pres; auto].
generalize (core_diagram (core_simulations _u1_)) as DIAG; intro.
clear c2 PROJ2 RUN2.
destruct (MATCH_CORES1 _ c1 PROJ1) as [GRc1 [SAFE [c2 [PROJ2 [GRc2 MATCH12]]]]].
unfold core_datas in cd.
assert (G_INNER: guarantee (csemS _u1_) r c1' m1').
 destruct SAFE as [z SAFE].
 assert (AT_EXT: at_external (csemS _u1_) c1 = None).
  solve[eapply corestep_not_at_external; eauto].
 assert (HALT: safely_halted (csemS _u1_) c1 = None).
  solve[eapply corestep_not_halted; eauto].
 inv SAFE; try solve[congruence].
 solve[destruct (H0 c1' m1' GRc1 STEP1); auto].
specialize (DIAG c1 m1 c1' m1' STEP1 (cd _ _) r c2 j m2 G_INNER MATCH12).
destruct DIAG as [c2' [m2' [cd' [r' [j' [INJ_INCR [INJ_SEP [RINCR [RSEP 
 [UNCH2 [MATCH12' STEP2]]]]]]]]]]].
destruct STEP2 as [STEP2|STEP2].

(*corestep_plus case*)
destruct STEP2 as [n STEP2].
generalize (corestep_stepN _ _ core_compatT) as CSTEPN; intro.
specialize (CSTEPN (S n) _u1_ st2). 
rewrite <-ACT in *.
specialize (CSTEPN c2 m2 c2' m2').
spec CSTEPN; auto.
spec CSTEPN; auto. 
destruct CSTEPN as [st2' [ESEM2 [ACT2' PROJ2']]].
exists st2'; exists m2'.
exists (core_datas_upd _u1_ (ACTIVE E_S st1) cd' cd).
exists r'.
exists j'.
split3; auto.
split; auto.
split; auto.
split; auto.
forget (ACTIVE E_S st1) as x.
forget (ACTIVE E_T st2') as y.
subst.
eapply (guarantee_stepN core_compatT owned_conservT new_effects_alignedT); eauto.
intros b ofs ? ? delta b2 ?.
specialize (RSEP b ofs).
spec RSEP; auto.
spec RSEP; auto.
destruct RSEP as [_ H2].
solve[eapply H2; eauto].
intros b ofs ? ? ?.
solve[exploit (INJ_SEP b ofs); eauto; intros [X Y]; apply Y; auto].
split; auto.
 (*Subgoal: match_states*)
 hnf.
 split.

 (*owned_valid*)
 eapply owned_valid_inv with (n := S O); eauto.
 solve[simpl; exists c1'; exists m1'; eauto].
 solve[simpl; eexists st1'; eexists m1'; eauto].

 (*owned_disjoint*)
 split.
 eapply owned_disjoint_inv with (n := S O) (m' := m1'); eauto.
 solve[simpl; exists c1'; exists m1'; eauto].
 solve[simpl; eexists st1'; eexists m1'; eauto].

 (*owned_valid*)
 split.
 forget (ACTIVE E_S st1) as k1.
 forget (ACTIVE E_T st2') as k2.
 subst.
 solve[eapply owned_valid_inv; eauto].

 (*owned_disjoint*)
 split.
 forget (ACTIVE E_S st1) as k1.
 forget (ACTIVE E_T st2') as k2.
 subst.
 solve[eapply owned_disjoint_inv; eauto].

 (*reserve_valid*)
 split.
 destruct (core_simulations _u1_).
 eapply reserved_locs_valid0 in MATCH12'.
 solve[destruct MATCH12'; auto].
 split.
 destruct (core_simulations _u1_).
 eapply reserved_locs_valid0 in MATCH12'.
 solve[destruct MATCH12'; auto].

 (*effects_valid*)
 split.
 solve[eapply effects_valid_preserved; eauto].
 split.
 clear - EV2 ESEM2.
 revert st2 m2 EV2 ESEM2.
 induction n; intros.
 hnf in ESEM2.
 destruct ESEM2 as [c2 [m3 [H ?]]].
 hnf in H0; inv H0.
 solve[eapply effects_valid_preserved; eauto].
 hnf in ESEM2.
 destruct ESEM2 as [c2 [m3 [H ?]]].
 assert (core_semantics.effects_valid esemT c2 m3).
  solve[eapply effects_valid_preserved; eauto].
 clear EV2.
 solve[eapply IHn; eauto].

 (*mem_wd*)
 split.
 eapply match_memwd in MATCH12'; eauto.
 solve[destruct MATCH12'; auto].
 split.
 eapply match_memwd in MATCH12'; eauto.
 solve[destruct MATCH12'; auto].
 
 (*guarantee*)
 split.
 eapply guarantee_incr_alloc1; eauto.
 eapply reserved_locs_valid in MATCH12'; eauto.
 destruct MATCH12'; auto.
 solve[intros b1 ofs1 X Y; destruct (RSEP b1 ofs1); auto].
 split.
 forget (ACTIVE E_S st1) as x.
 subst.
 eapply (guarantee_stepN core_compatT owned_conservT new_effects_alignedT); eauto.
 intros b ofs ? ? delta b2 ?.
 specialize (RSEP b ofs).
 spec RSEP; auto.
 spec RSEP; auto.
 destruct RSEP as [_ H2].
 solve[eapply H2; eauto].
 intros b ofs ? ? ?.
 solve[exploit (INJ_SEP b ofs); eauto; intros [X Y]; apply Y; auto].
  
 (*allocs_shrink*)
 split.
 unfold allocs_shrink.
 intros until delta; intros EFA2 JJ'.
 admit. (*allocs_shrink*)

 (*R*)
 split.
 inv esig_compilable. 
 eapply corestep_rel with (s1 := st1) (s2 := st2); eauto.
 erewrite <-genvs_domain_eq_preserves.
 erewrite meminj_preserves_genv2blocks.
 eauto.
 solve[apply genvs_domain_eq_sym; auto].
 solve[eapply guarantee_decr2; eauto].

 split.
  solve[rewrite <-ACT1', <-ACT2'; auto].
  split. 

  (*ACTIVE E_S st1 = i*)
  intros _u_ _c _PROJ1'.
  forget (ACTIVE E_S st1) as x.
  forget (ACTIVE E_T st2) as y.
  forget (ACTIVE E_S st1') as x'.
  forget (ACTIVE E_T st2') as y'.
  do 4 subst.
  assert (_u_ = _u1_).
   solve[eapply Extension.proj_core_types; eauto].
  subst _u_.
  assert (_c = c1') as ->.
   rewrite PROJ1' in _PROJ1'.
   solve[inv _PROJ1'; auto].
  split.
  eapply guarantee_incr_alloc1; eauto.
  eapply reserved_locs_valid in MATCH12'; eauto.
  solve[destruct MATCH12'; auto].
  intros b1 ofs1 ? ?.
  solve[destruct (RSEP b1 ofs1); auto].
  assert (GR: guarantee (csemS _u1_) r' c1' m1').
   eapply guarantee_incr_alloc1; eauto.
   eapply reserved_locs_valid; eauto.
   intros b ofs X Y.
   solve[eapply RSEP; eauto].
  split.

  destruct SAFE as [z SAFE]. exists z.
  assert (AT_EXT: at_external (csemS _u1_) c1 = None).
   solve[eapply corestep_not_at_external; eauto].
  assert (HALT: safely_halted (csemS _u1_) c1 = None).
   solve[eapply corestep_not_halted; eauto].
  inv SAFE; try solve[congruence].
  destruct (H1 c1' m1' GRc1 STEP1).
  solve[apply (H2 _ GR)].
  exists c2'.
  split; auto.
  split; auto.
  unfold core_datas_upd.
  rewrite data_upd_same.
  rewrite data_upd_same.
  solve[auto].

  (*ACTIVE E_S st1 <> i*)
  intros i _u_ _c NEQ PROJ.
  assert (_PROJ1: PROJ_CORE E_S i _u_ st1 = Some _c). 
   inv core_compatS.
   specialize (corestep_others_forward _u1_ st1 st1'). 
   forget (ACTIVE E_S st1) as x.
   forget (ACTIVE E_T st2) as y.
   forget (ACTIVE E_S st1') as x'.
   forget (ACTIVE E_T st2') as y'.
   do 4 subst.
   specialize (corestep_others_forward c1 m1 c1' m1').
   spec corestep_others_forward; auto.
   spec corestep_others_forward; auto. 
   spec corestep_others_forward; auto.
   spec corestep_others_forward; auto.
   specialize (corestep_others_forward i _u_).
   spec corestep_others_forward; auto.
   solve[rewrite corestep_others_forward; auto].
  specialize (MATCH_CORES2 i _ _c).
  spec MATCH_CORES2.
  solve[rewrite ACT1'; auto].
  destruct (MATCH_CORES2 _PROJ1) as 
   [_d [_PROJ2 [cd0 [r0 [j0 [m10 [m20 [GR10 [GR20 _MATCH12]]]]]]]]].
  assert (_PROJ2': PROJ_CORE E_T i _ st2' = Some _d). 
   inv core_compatT.
   specialize (corestep_others_backward _u1_ st2). 
   forget (ACTIVE E_S st1) as x.
   forget (ACTIVE E_T st2) as y.
   forget (ACTIVE E_S st1') as x'.
   forget (ACTIVE E_T st2') as y'.
   do 4 subst.
   specialize (corestep_others_backward c2 m2 st2' c2' m2' (S n)).
   spec corestep_others_backward; auto.
   spec corestep_others_backward; auto. 
   spec corestep_others_backward; auto.
   specialize (corestep_others_backward i _u_).
   spec corestep_others_backward; auto.
   solve[rewrite <-corestep_others_backward; auto].
  exists _d; split; auto.
  solve[exists cd0, r0, j0, m10, m20; split; auto].
  solve[left; exists n; auto].

(*corestep_star case*)
destruct STEP2 as [[n STEP2] ORD].
generalize (corestep_stepN _ _ core_compatT) as CSTEPN; intro.
specialize (CSTEPN n _u1_ st2). 
rewrite <-ACT in *.
specialize (CSTEPN c2 m2 c2' m2').
spec CSTEPN; auto.
spec CSTEPN; auto. 
destruct CSTEPN as [st2' [ESEM2 [ACT2' PROJ2']]].
exists st2'; exists m2'. 
exists (core_datas_upd _u1_ (ACTIVE E_S st1) cd' cd).
exists r'.
exists j'.
split3; auto.
split; auto.
split; auto.
split; auto.
forget (ACTIVE E_S st1) as x.
subst.
eapply (guarantee_stepN core_compatT owned_conservT new_effects_alignedT); eauto.
intros b ofs ? ? delta b2 ?.
specialize (RSEP b ofs).
spec RSEP; auto.
spec RSEP; auto.
destruct RSEP as [_ H2].
solve[eapply H2; eauto].
intros b ofs ? ? ?.
solve[exploit (INJ_SEP b ofs); eauto; intros [X Y]; apply Y; auto].
split.
 (*Subgoal: match_states*)
 hnf.
 split.

 (*owned_valid*)
 eapply owned_valid_inv with (n := S O); eauto.
 solve[simpl; exists c1'; exists m1'; eauto].
 solve[simpl; eexists st1'; eexists m1'; eauto].

 (*owned_disjoint*)
 split.
 eapply owned_disjoint_inv with (n := S O) (m' := m1'); eauto.
 solve[simpl; exists c1'; exists m1'; eauto].
 solve[simpl; eexists st1'; eexists m1'; eauto].

 (*owned_valid*)
 split.
 forget (ACTIVE E_S st1) as k1.
 forget (ACTIVE E_T st2') as k2.
 subst.
 solve[eapply owned_valid_inv; eauto].

 (*owned_disjoint*)
 split.
 forget (ACTIVE E_S st1) as k1.
 forget (ACTIVE E_T st2') as k2.
 subst.
 solve[eapply owned_disjoint_inv; eauto].

 (*reserve_valid*)
 split.
 destruct (core_simulations _u1_).
 eapply reserved_locs_valid0 in MATCH12'.
 solve[destruct MATCH12'; auto].
 split.
 destruct (core_simulations _u1_).
 eapply reserved_locs_valid0 in MATCH12'.
 solve[destruct MATCH12'; auto].

 (*effects_valid*)
 split.
 solve[eapply effects_valid_preserved; eauto].
 split.
 clear - EV2 ESEM2.
 revert st2 m2 EV2 ESEM2.
 induction n; intros.
 solve[hnf in ESEM2; inv ESEM2; auto].
 hnf in ESEM2; destruct ESEM2 as [c2 [m3 [H ?]]].
 assert (core_semantics.effects_valid esemT c2 m3).
  solve[eapply effects_valid_preserved; eauto].
 clear EV2.
 solve[eapply IHn; eauto].

 (*mem_wd*)
 split.
 eapply match_memwd in MATCH12'; eauto.
 solve[destruct MATCH12'; auto].
 split.
 eapply match_memwd in MATCH12'; eauto.
 solve[destruct MATCH12'; auto].

 (*guarantee*)
 split.
 eapply guarantee_incr_alloc1; eauto.
 eapply reserved_locs_valid in MATCH12'; eauto.
 destruct MATCH12'; auto.
 solve[intros b1 ofs1 X Y; destruct (RSEP b1 ofs1); auto].
 split.
 forget (ACTIVE E_S st1) as x.
 subst.
 eapply (guarantee_stepN core_compatT owned_conservT new_effects_alignedT); eauto.
 intros b ofs ? ? delta b2 ?.
 specialize (RSEP b ofs).
 spec RSEP; auto.
 spec RSEP; auto.
 destruct RSEP as [_ H2].
 solve[eapply H2; eauto].
 intros b ofs ? ? ?.
 solve[exploit (INJ_SEP b ofs); eauto; intros [X Y]; apply Y; auto].
 
 (*allocs_shrink*)
 split.
 unfold allocs_shrink.
 intros until delta; intros EFA2 JJ'.
 admit. (*allocs_shrink*)

 (*R*)
 split.
 inv esig_compilable. 
 eapply corestep_rel with (s1 := st1) (s2 := st2); eauto.
 erewrite <-genvs_domain_eq_preserves.
 erewrite meminj_preserves_genv2blocks.
 eauto.
 solve[apply genvs_domain_eq_sym; auto].
 solve[eapply guarantee_decr2; eauto].

 split.
  solve[rewrite <-ACT1', <-ACT2'; auto].
  split. 

  (*ACTIVE E_S st1 = i*)
  intros _u_ _c _PROJ1'.
  forget (ACTIVE E_S st1) as x.
  forget (ACTIVE E_T st2) as y.
  forget (ACTIVE E_S st1') as x'.
  forget (ACTIVE E_T st2') as y'.
  do 4 subst.
  assert (_u_ = _u1_).
   solve[eapply Extension.proj_core_types; eauto].
  subst.
  assert (_c = c1') as ->.
   rewrite PROJ1' in _PROJ1'.
   solve[inv _PROJ1'; auto].
  split.
  eapply guarantee_incr_alloc1; eauto.
  eapply reserved_locs_valid in MATCH12'; eauto.
  solve[destruct MATCH12'; auto].
  intros b1 ofs1 ? ?.
  solve[destruct (RSEP b1 ofs1); auto].
  split.

  (*compile_safe*)
  destruct SAFE as [z SAFE]. exists z.
  assert (AT_EXT: at_external (csemS _u1_) c1 = None).
   solve[eapply corestep_not_at_external; eauto].
  assert (HALT: safely_halted (csemS _u1_) c1 = None).
   solve[eapply corestep_not_halted; eauto].
  inv SAFE; try solve[congruence].
  destruct (H1 c1' m1' GRc1 STEP1).
  assert (GR: guarantee (csemS _u1_) r' c1' m1').
   eapply guarantee_incr_alloc1; eauto.
   solve[eapply reserved_locs_valid; eauto].
   solve[intros b ofs ? ?; eapply RSEP; eauto].
  solve[apply (H2 _ GR)].

  exists c2'.
  split; auto.
  split; auto.
  unfold core_datas_upd. 
  rewrite data_upd_same.
  rewrite data_upd_same.
  solve[auto].

  (*ACTIVE E_S st1 <> i*)
  intros i _u_ _c NEQ _PROJ1'.
  assert (_PROJ1: PROJ_CORE E_S i _u_ st1 = Some _c). 
   inv core_compatS.
   specialize (corestep_others_forward _u1_ st1 st1'). 
   forget (ACTIVE E_S st1) as x.
   forget (ACTIVE E_T st2) as y.
   forget (ACTIVE E_S st1') as x'.
   forget (ACTIVE E_T st2') as y'.
   do 4 subst.
   specialize (corestep_others_forward c1 m1 c1' m1').
   spec corestep_others_forward; auto.
   spec corestep_others_forward; auto. 
   spec corestep_others_forward; auto.
   spec corestep_others_forward; auto.
   specialize (corestep_others_forward i _u_).
   spec corestep_others_forward; auto.
   solve[rewrite corestep_others_forward; auto].
  specialize (MATCH_CORES2 i _ _c).
  spec MATCH_CORES2.
  solve[rewrite ACT1'; auto].
  destruct (MATCH_CORES2 _PROJ1) as 
   [_d [_PROJ2 [cd0 [r0 [j0 [m10 [m20 [GR10 [GR20 _MATCH12]]]]]]]]].
  assert (_PROJ2': PROJ_CORE E_T i _ st2' = Some _d). 
   inv core_compatT.
   specialize (corestep_others_backward _u1_ st2). 
   forget (ACTIVE E_S st1) as x.
   forget (ACTIVE E_T st2) as y.
   forget (ACTIVE E_S st1') as x'.
   forget (ACTIVE E_T st2') as y'.
   do 4 subst.
   specialize (corestep_others_backward c2 m2 st2' c2' m2' n).
   spec corestep_others_backward; auto.
   spec corestep_others_backward; auto. 
   spec corestep_others_backward; auto.
   specialize (corestep_others_backward i _u_).
   spec corestep_others_backward; auto.
   solve[rewrite <-corestep_others_backward; auto].
  exists _d; split; auto.
  solve[exists cd0, r0, j0, m10, m20; split; auto].
  right. split. exists n. auto.
  apply core_datas_upd_ord; auto.
  admit. (*all modules indexes < num_modules*)

(*runnable = false*)
intros RUN1.
generalize PROJ1 as _PROJ1; intro.
generalize RUN1 as RUN1'; intro.
apply runnable_false in RUN1.
destruct RUN1 as [[rv1 HALT]|[ef [sig [args AT_EXT]]]].

(*active thread is safely halted*)
specialize (MATCH_CORES1 _ c1 _PROJ1).
clear c2 PROJ2.
destruct MATCH_CORES1 as [GRc1 [SAFE [c2 [PROJ2 [GRc2 MATCH12]]]]].
destruct (exists_ty rv1) as [ty1 HAS_TY].
destruct (core_halted (core_simulations _u1_) 
  (cd _u1_ (ACTIVE E_S st1)) r j c1 m1 c2 m2 rv1 ty1 MATCH12 HALT) 
 as [rv2 [VAL_INJ [SAFE_T INJ]]]; auto.
inv esig_compilable.
eapply safely_halted_diagram with (m1' := m1') in MATCH'; eauto.
destruct MATCH' as [rv2' [H7 [VAL_INJ' 
 [st2' [m2' [cd' [r' [j' [INJ_INCR [SEP [STEP2' 
 [RM_INCR [RM_SEP [MATCH12' UNCH2]]]]]]]]]]]]]].
exists st2'; exists m2'; exists cd'; exists r'; exists j'.
split3; auto; split; auto.
split3; auto.
split; auto.
solve[left; exists 0%nat; eexists; eexists; split; simpl; eauto].

(*active thread is at_external*)
clear c2 PROJ2.
destruct (MATCH_CORES1 _ c1 _PROJ1) as [GRc1 [SAFE [c2 [GRc2 [PROJ2 MATCH12]]]]].
destruct (core_at_external (core_simulations _u1_) (cd _u1_ (ACTIVE E_S st1)) 
            r j c1 m1 c2 m2 ef args sig MATCH12 AT_EXT)
 as [H6 [H7 [vals2 [H8 [H9 [H10 H11]]]]]].
destruct SAFE as [z SAFE].
assert (safely_halted (csemS _u1_) c1 = None).
 exploit @at_external_halted_excl; eauto.
 intros [X|X]; eauto.
 solve[rewrite X in AT_EXT; inv AT_EXT].
inv SAFE; try solve[congruence].
apply corestep_not_at_external in H0; congruence.
rewrite H0 in AT_EXT; inv AT_EXT.
solve[intros v1 IN; destruct (H1 _ IN); auto].

inv esig_compilable. 
edestruct extension_diagram as [s2' H12]; eauto.
solve[erewrite <-match_state_runnable; eauto].
rewrite <-meminj_preserves_genv2blocks.
rewrite genvs_domain_eq_preserves with (ge2 := (genv_mapS _u1_)); auto.
solve[rewrite meminj_preserves_genv2blocks; auto].
Qed.

(*we punt in the make_initial_core case of the simulation proof; to do more requires 
   assuming too much about the structure of the extension w/r/t its inner cores*)
Next Obligation. inv esig_compilable. eapply make_initial_core_diagram; eauto. Qed.
Next Obligation. inv esig_compilable. eapply safely_halted_step; eauto. Qed.

Next Obligation. 
rename H into MATCH.
hnf in MATCH.
destruct MATCH 
 as [PRIV1 [DISJ1 [PRIV2 [DISJ2 [RMV1 [RMV2 [EV1 [EV2 
    [WD1 [WD2 [GR1 [GR2 [SHRINK [RR [ACT [MATCH_CORES1 MATCH_CORES2]]]]]]]]]]]]]]]].
destruct (active_proj_core E_S) with (s := st1) as [_u1_ [c1 PROJ1]].
assert (AT_EXT1: at_external (csemS _u1_) c1 = Some (e, sig, vals1)).
 inv core_compatS.
 edestruct (at_extern_call) as [_u'_ [c [PROJ AT_EXT]]]; eauto.
 assert (_u'_ = _u1_).
  solve[eapply Extension.proj_core_types; eauto].
 subst.  
 rewrite PROJ in PROJ1; inv PROJ1.
 solve[inv PROJ; auto].
destruct (MATCH_CORES1 _ c1 PROJ1) as [GRc1 [SAFE [c2 [PROJ2 [GRc2 MATCH12]]]]].
destruct (core_at_external (core_simulations _u1_) 
            (cd _u1_ (ACTIVE E_S st1)) r j c1 m1 c2 m2 e vals1 sig MATCH12 AT_EXT1)
 as [INJ [GLOBS [vals2 [VALINJ [TYPE [AT_EXT2 VALVAL]]]]]].
solve[apply H1].
split3; auto.
rewrite <-meminj_preserves_genv2blocks.
rewrite genvs_domain_eq_preserves with (ge2 := (genv_mapS _u1_)); auto.
rewrite meminj_preserves_genv2blocks; auto.
exists vals2.
split3; auto.
split; auto.
inv esig_compilable.
eapply at_external_match; eauto.
rewrite <-meminj_preserves_genv2blocks.
rewrite genvs_domain_eq_preserves with (ge2 := (genv_mapS _u1_)); auto.
solve[rewrite meminj_preserves_genv2blocks; auto].
Qed.

Next Obligation.
rename H into MATCH.
generalize MATCH as MATCH'; intro.
hnf in MATCH.
destruct MATCH 
 as [PRIV1 [DISJ1 [PRIV2 [DISJ2 [RMV1 [RMV2 
    [EV1 [EV2 [WD1 [WD2 [GR1 [GR2 [SHRINK [RR 
    [ACT [MATCH_CORES1 MATCH_CORES2]]]]]]]]]]]]]]]].
generalize MATCH_CORES2 as MATCH_CORES'; intro.
destruct (active_proj_core E_S) with (s := st1) as [_u1_ [c1 PROJ1]].
assert (AT_EXT1: at_external (csemS _) c1 = Some (e, sig, vals1)).
 inv core_compatS.
 edestruct (at_extern_call) as [_u'_ [c [PROJ AT_EXT]]]; eauto.
 assert (_u'_ = _u1_).
  solve[eapply Extension.proj_core_types; eauto].
 subst.
 rewrite PROJ in PROJ1; inv PROJ1.
 solve[inv PROJ; auto].
destruct (MATCH_CORES1 _ c1 PROJ1) as [GRc1 [SAFE [c2 [PROJ2 [GRc2 MATCH12]]]]].
destruct (core_after_external (core_simulations _u1_) 
                (cd _u1_ (ACTIVE E_S st1)) r r' j j' c1 c2 m1 e 
                vals1 ret1 m1' m2 m2' ret2 sig)
 as [cd' [c1' [c2' [AFTER1 [AFTER2 MATCH12']]]]]; auto.
rewrite <-meminj_preserves_genv2blocks.
rewrite <-genvs_domain_eq_preserves with (ge1 := ge_S); auto.
rewrite meminj_preserves_genv2blocks; auto.

unfold rely in H13|-*.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  r b ofs /\ effects esemS st1 AllocEffect b ofs); auto.
intros b ofs [? ?].
split; auto.
solve[eapply owned_conservS; eauto].
unfold rely', rely in H14|-*.
apply mem_unchanged_on_sub with (Q := fun b ofs => 
  inject_reserve j r b ofs /\ effects esemT st2 AllocEffect b ofs); auto.
unfold inject_reserve.
intros b ofs [[? [? [? ?]]] EF].
split.
exists x, x0.
split; auto.
solve[eapply owned_conservT; eauto].

exists (core_datas_upd _u1_ (ACTIVE E_S st1) cd' cd).
assert (exists st1', after_external esemS ret1 st1 = Some st1' /\
         PROJ_CORE E_S (ACTIVE E_S st1) _u1_ st1' = Some c1') as [st1' [? PROJ1']].
 inv core_compatS.
 specialize (after_ext_prog _ st1 c1 c1' ret1).
 solve[spec after_ext_prog; auto].
assert (exists st2', after_external esemT ret2 st2 = Some st2' /\
   PROJ_CORE E_T (ACTIVE E_S st1) _ st2' = Some c2') as [st2' [? PROJ2']].
 inv core_compatT.
 specialize (after_ext_prog _u1_ st2). 
 rewrite <-ACT in after_ext_prog.
 specialize (after_ext_prog c2 c2' ret2).
 solve[spec after_ext_prog; auto].
exists st1'; exists st2'.
split3; auto.

hnf.
assert (ACTIVE E_S st1=ACTIVE E_S st1') as <-.
 inv core_compatS.
 solve[eapply after_ext_pres; eauto; auto].
assert (ACTIVE E_T st2=ACTIVE E_T st2') as <-.
 forget (ACTIVE E_S st1) as x.
 inv core_compatT.
 solve[eapply after_ext_pres; eauto].
split; auto.

(*owned_valid*)
solve[eapply owned_valid_after_ext; eauto].
split.

(*owned_disjoint*)
solve[eapply owned_disjoint_after_ext; eauto].
split.

(*owned_valid*)
remember (ACTIVE E_S st1) as x.
remember (ACTIVE E_S st1') as x'.
remember (ACTIVE E_T st2') as y'.
subst.
assert (AT_EXT2: exists vals2, 
  Forall2 (val_inject j) vals1 vals2 /\
  Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
  at_external (csemT _u1_) c2 = Some (e, sig, vals2) /\
  (forall v2, In v2 vals2 -> val_valid v2 m2)).
 destruct (core_simulations _u1_).
 eapply core_at_external0 in AT_EXT1; eauto.
 destruct AT_EXT1 as [_ [_ [vals2 [X [Y [AT_EXT2 VALVAL]]]]]].
 solve[exists vals2; eauto].
destruct AT_EXT2 as [vals2 [FV1 [FV2 [AT_EXT2 VALVAL]]]].
solve[eapply owned_valid_after_ext; eauto].

(*owned_disjoint*)
remember (ACTIVE E_S st1) as x.
remember (ACTIVE E_S st1') as x'.
remember (ACTIVE E_T st2') as y'.
subst.
assert (AT_EXT2: exists vals2, 
  Forall2 (val_inject j) vals1 vals2 /\
  Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
  at_external (csemT _u1_) c2 = Some (e, sig, vals2) /\
  (forall v2, In v2 vals2 -> val_valid v2 m2)).
 destruct (core_simulations _u1_).
 eapply core_at_external0 in AT_EXT1; eauto.
 destruct AT_EXT1 as [_ [_ [vals2 [X [Y [AT_EXT2 VALVAL]]]]]].
 solve[exists vals2; eauto].
split.
destruct AT_EXT2 as [vals2 [FV1 [FV2 [AT_EXT2 VALVAL]]]].
solve[eapply owned_disjoint_after_ext; eauto].

(*reserve_valid_after_ext*)
split.
destruct (core_simulations _u1_).
eapply reserved_locs_valid0 in MATCH12'.
solve[destruct MATCH12'; auto].
split.
destruct (core_simulations _u1_).
eapply reserved_locs_valid0 in MATCH12'.
solve[destruct MATCH12'; auto].

(*effects_valid_after_ext*)
split.
solve[eapply effects_valid_after_ext; eauto].
split.
assert (exists vals2, at_external esemT st2 = Some (e, sig, vals2))
 as [vals2 X].
 destruct AT_EXT2 as [vals2 [? [? [? ?]]]].
 exists vals2.
 assert (X: 
   exists (c0: cS _u1_) (c3: cT _u1_),
     PROJ_CORE E_S (ACTIVE E_S st1) _u1_ st1 = Some c0 /\
     PROJ_CORE E_T (ACTIVE E_S st1) _u1_ st2 = Some c3 /\
     at_external (csemS _u1_) c0 = Some (e, sig, vals1) /\
     at_external (csemT _u1_) c3 = Some (e, sig, vals2) /\
     match_state _u1_ (cd _u1_ (ACTIVE E_S st1)) r j c0 m1 c3 m2).
  forget (ACTIVE E_S st1) as x.
  forget (ACTIVE E_S st1') as x'.
  forget (ACTIVE E_T st2) as y.
  forget (ACTIVE E_T st2') as y'.
  do 3 subst.
  exists c1, c2.
  solve[split3; auto].
 destruct X as [c0 [c3 [X1 [X2 [X3 [X4 X5]]]]]].
 inv esig_compilable.
 specialize (at_external_match _ st1 m1 st2 c0 c3 m2 e sig vals1 vals2
   (cd _u1_ (ACTIVE E_S st1)) r j).
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 unfold runnable. solve[rewrite X3, X4; auto].
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 solve[eapply match_inject; eauto].
solve[eapply effects_valid_after_ext; eauto].

(*mem_wd_after_ext*)
split; auto.
split; auto.

(*guarantee_after_ext*)
split. 
eapply guarantee_after_ext; eauto.
solve[intros b ofs ? ?; eapply H6; eauto].
split.
assert (exists vals2, at_external esemT st2 = Some (e, sig, vals2))
 as [vals2 X].
 destruct AT_EXT2 as [vals2 [? [? [? ?]]]].
 exists vals2.
 assert (X: 
   exists (c0: cS _u1_) (c3: cT _u1_),
     PROJ_CORE E_S (ACTIVE E_S st1) _u1_ st1 = Some c0 /\
     PROJ_CORE E_T (ACTIVE E_S st1) _u1_ st2 = Some c3 /\
     at_external (csemS _u1_) c0 = Some (e, sig, vals1) /\
     at_external (csemT _u1_) c3 = Some (e, sig, vals2) /\
     match_state _u1_ (cd _u1_ (ACTIVE E_S st1)) r j c0 m1 c3 m2).
  forget (ACTIVE E_S st1) as x.
  forget (ACTIVE E_S st1') as x'.
  forget (ACTIVE E_T st2) as y.
  forget (ACTIVE E_T st2') as y'.
  do 3 subst.
  exists c1, c2.
  solve[split3; auto].
 destruct X as [c0 [c3 [X1 [X2 [X3 [X4 X5]]]]]].
 inv esig_compilable.
 specialize (at_external_match _ st1 m1 st2 c0 c3 m2 e sig vals1 vals2
   (cd _u1_ (ACTIVE E_S st1)) r j).
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 unfold runnable. solve[rewrite X3, X4; auto].
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 solve[eapply match_inject; eauto].
eapply guarantee'_after_ext; eauto.
solve[intros b ofs ? ?; eapply H6; eauto].
solve[intros b ofs ? ?; eapply H4; eauto].

(*allocs_shrink_after_ext*)
split.
unfold allocs_shrink.
admit. (*allocs_shrink*)

split.
inv esig_compilable.
eapply after_external_rel; eauto.
eapply rely_same_effects; eauto.
solve[intros; eapply effects_external; eauto].
unfold rely', rely in H14|-*.
apply mem_unchanged_on_sub with (Q := 
  (fun b ofs => inject_reserve j r b ofs /\ 
    effects esemT st2 AllocEffect b ofs)); auto.
intros b ofs [? ?]; split; auto.
assert (exists vals2, at_external esemT st2 = Some (e, sig, vals2))
    as [vals2 AT_EXT2'].
 destruct AT_EXT2 as [vals2 [FV1 [FV2 [AT_EXT2 VALVAL]]]].
 exists vals2.
 remember (ACTIVE E_T st2) as y.
 forget (ACTIVE E_S st1') as x'.
 forget (ACTIVE E_T st2') as y'.
 do 4 subst.
 specialize (at_external_match 
    _ st1 m1 st2 c1 c2 m2 e sig vals1 vals2 (cd _u1_ (ACTIVE E_S st1)) r j).
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 solve[eapply match_state_runnable; eauto].
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 spec at_external_match; auto.
 solve[eapply match_state_inj; eauto].
solve[intros; eapply effects_external; eauto].

split; auto.
split.
(*ACTIVE E_S st1 = i*)
forget (ACTIVE E_S st1) as x.
forget (ACTIVE E_T st2) as y.
forget (ACTIVE E_S st1') as x'.
forget (ACTIVE E_T st2') as y'.
do 4 subst.
intros _u_ _c _PROJ1'.
assert (_u_ = _u1_).
 solve[eapply Extension.proj_core_types; eauto].
subst.
rewrite _PROJ1' in PROJ1'.
inv PROJ1'; auto.
split.
eapply guarantee_after_ext; eauto.
eapply effects_valid in MATCH12; eauto.
solve[destruct MATCH12; auto].
intros b ofs; intros.
rename H6 into RSEP.
specialize (RSEP b ofs).
spec RSEP; auto.
spec RSEP; auto.
destruct RSEP as [RSEP _]; auto.
split.
(*compile_safe*)
destruct SAFE as [z SAFE].
assert (HALT: safely_halted (csemS _u1_) c1 = None).
 exploit @at_external_halted_excl; eauto.
 instantiate (1 := c1).
 instantiate (1 := (csemS _u1_)).
 intros [Y|Y].
 rewrite Y in AT_EXT1; congruence.
 solve[auto].
inv SAFE; try solve[congruence].
solve[apply corestep_not_at_external in H18; congruence].
exists z.
eapply H20; eauto.
intros b ofs ? ? ?.
solve[apply (H6 b ofs); auto].
admit. (*val_not_reserved; will have to be added to after_external*)
admit. (*val_valid; will have to be added to after_external*)
exists c2'.
split; auto.
split; auto.
destruct AT_EXT2 as [vals2' [AT1 [AT2 [AT3 AT4]]]].
eapply guarantee'_after_ext; eauto.
eapply effects_valid in MATCH12; eauto.
solve[destruct MATCH12; auto].
solve[intros b ofs ? ?; destruct (H6 b ofs); auto].
solve[intros b ofs delta ? ?; destruct (H4 b ofs delta); auto].
solve[unfold core_datas_upd; do 2 rewrite data_upd_same; auto].

(*ACTIVE E_S st1 <> i*)
intros i _u_ _c NEQ _PROJ1'.
specialize (MATCH_CORES' i _u_  _c).
spec MATCH_CORES'; auto.
rewrite Heqx in NEQ.
spec MATCH_CORES'.
 inv core_compatS.
 solve[erewrite after_ext_others; eauto].
destruct MATCH_CORES' as [_d [_PROJ2 _MATCH12]].
exists _d; split; auto.
inv core_compatT.
erewrite <-after_ext_others; eauto.
solve[rewrite Heqx; auto].
Qed.

Lemma RGsimulations_invariant: 
  (forall i:nat, RelyGuaranteeSimulation.Sig (csemS i) (csemT i) 
       (genv_mapS i) (match_state i)) ->
  @CompilabilityInvariant.Sig F_S V_S F_T V_T D_S D_T xS xT 
       fS fT vS vT cS cT dS dT Z Zint Zext 
       esemS esemT csemS csemT csig esig max_cores num_modules
       ge_S ge_T genv_mapS genv_mapT E_S E_T 
       entry_points core_data match_state core_ord R -> 
  internal_compilability_invariant.
Proof.
intros core_simulations_RGinject INV.
inv INV.
constructor; auto.
intros; destruct (core_simulations_RGinject i) as [? _ _].
eapply match_state_runnable; eauto.
intros; destruct (core_simulations_RGinject i) as [_ ? _].
intros; destruct (core_simulations_RGinject i) as [_ _ ?].
solve[eapply match_state_preserves_globals; eauto].
Qed.

End ExtendedSimulations. End ExtendedSimulations.

Module ExtensionCompilability. Section ExtensionCompilability. 
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
  (csemS: forall i:nat, 
    EffectfulSemantics (Genv.t (fS i) (vS i)) (cS i) (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, 
    EffectfulSemantics (Genv.t (fT i) (vT i)) (cT i) (dT i)) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (threads_max: nat) 
  (num_modules: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> reserve -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].
 Variable max_cores: nat. (*TODO: fixme*)

 Definition core_datas := forall i: nat, core_data i. 

 Variable R: reserve -> meminj -> xS -> mem -> xT -> mem -> Prop.
 Variable R_antimono: 
   forall (r0 r: reserve) j s1 m1 s2 m2,
   reserve_incr r0 r -> 
   R r j s1 m1 s2 m2 -> 
   R r0 j s1 m1 s2 m2.

 Import Forward_simulation_inj_exposed.

 Lemma ExtensionCompilability: 
   EXTENSION_COMPILABILITY.Sig fS fT vS vT 
       esemS esemT csemS csemT max_cores num_modules ge_S ge_T genv_mapS genv_mapT 
       E_S E_T entry_points core_data match_state core_ord R.
 Proof.
 eapply @EXTENSION_COMPILABILITY.Make.
 intros H1 H2 H3 H4 H5 H6 PRIV1 PRIV2 core_simulations H8 H9 H10 H11.
 apply CompilableExtension.Make 
  with (core_datas := ExtendedSimulations.core_datas core_data)
       (match_states := 
  ExtendedSimulations.match_states fS fT vS vT esemS esemT csemS csemT 
                                   genv_mapS E_S E_T match_state R)
       (core_ords := 
  ExtendedSimulations.core_ords core_ord num_modules max_cores).
 eapply ExtendedSimulations.extended_simulation; eauto.
 intros until m2; intros MATCH.
 solve[destruct (H1 O i); eapply match_state_inj; eauto].
 eapply ExtendedSimulations.RGsimulations_invariant; eauto.
 intros until m2; intros MATCH.
 solve[destruct (H1 O i); eapply match_state_inj; eauto].
Qed.

End ExtensionCompilability. End ExtensionCompilability.

(** A specialization of the CompilableExtension theorem to single-core systems *)

Definition const (A B: Type) (x: B) := fun _: A => x.

Module ExtensionCompilability2. Section ExtensionCompilability2. 
 Variables
  (F_S V_S F_T V_T fS fT vS vT: Type) (** global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (dS dT: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) cS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) cT D_T) (** extended target semantics *)
  (csemS: EffectfulSemantics (Genv.t fS vS) cS dS)
  (csemT: EffectfulSemantics (Genv.t fT vT) cT dT)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (geS: Genv.t fS vS) (geT: Genv.t fT vT).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S cS esemS esig 
   _ _ (const cS) (const csemS) csig). 
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T cT esemT esig 
   _ _ (const cT) (const csemT) csig). 
 Variable entry_points: list (val*val*signature).
 Variable core_data: Type.
 Variable match_state: 
   core_data -> reserve -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Variable core_ord: core_data -> core_data -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].
 Variable max_cores: nat.
 Variable num_modules: nat.

 Definition core_datas := nat -> core_data.

 Variable R: reserve -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Variable R_antimono: 
   forall (r0 r: reserve) j s1 m1 s2 m2,
   reserve_incr r0 r -> 
   R r j s1 m1 s2 m2 -> 
   R r0 j s1 m1 s2 m2.

 Import Forward_simulation_inj_exposed.

 Lemma ExtensionCompilability: 
   EXTENSION_COMPILABILITY.Sig (const fS) (const fT) (const vS) (const vT)
    esemS esemT (const csemS) (const csemT) max_cores num_modules ge_S ge_T 
    (const geS) (const geT) E_S E_T entry_points (const core_data) 
    (const match_state) (const core_ord) R.
 Proof.
 eapply @EXTENSION_COMPILABILITY.Make.
 intros H1 H2 H3 H4 H5 H6 PRIV1 PRIV2 core_simulations H8 H9 H10 INV.
 apply CompilableExtension.Make 
  with (core_datas := ExtendedSimulations.core_datas (fun _ => core_data))
       (match_states := 
  ExtendedSimulations.match_states (const fS) (const fT) (const vS) (const vT) 
              esemS esemT (const csemS) (const csemT) 
              (const geS) E_S E_T (const match_state) R)
       (core_ords := 
  ExtendedSimulations.core_ords (const core_ord) num_modules max_cores).
 eapply ExtendedSimulations.extended_simulation; eauto. 
 intros until m2; intros MATCH.
 solve[destruct (H1 O i); eapply match_state_inj; eauto].
 eapply ExtendedSimulations.RGsimulations_invariant; eauto.
 intros until m2; intros MATCH.
 solve[destruct (H1 i O); eapply match_state_inj; eauto].
Qed.

End ExtensionCompilability2. End ExtensionCompilability2.
