Load loadpath.
Require Import msl.predicates_hered.
Require Import veric.sim veric.step_lemmas veric.base veric.expr 
               veric.extspec veric.juicy_extspec veric.extension.

Set Implicit Arguments.

Lemma genvs_domain_eq_refl: forall F V (ge: Genv.t F V), genvs_domain_eq ge ge.
Proof. solve[intros F V ge; unfold genvs_domain_eq; split; intro b; split; auto]. Qed.

Section SafetyMonotonicity. 
 Variables 
  (G cT M D Zext: Type) (CS: CoreSemantics G cT M D)
  (csig: ext_spec M Z) (handled: list AST.external_function).

Lemma safety_monotonicity : forall ge n z c m,
  safeN CS (link_ext_spec handled csig) ge n z c m -> 
  safeN CS csig ge n z c m.
Proof. 
intros ge n; induction n; auto.
intros  ora c m; simpl; intros H1.
destruct (at_external CS c).
destruct p; destruct p.
destruct (safely_halted CS c).
auto.
destruct H1 as [x [H1 H2]].
if_tac in H1.
elimtype False; apply H1.
exists x; split; auto.
intros ret m' z' H3; destruct (H2 ret m' z' H3) as [c' [H4 H5]].
exists c'; split; auto.
destruct (safely_halted CS c); auto.
destruct H1 as [c' [m' [H1 H2]]].
exists c'; exists m'; split; auto.
Qed.

End SafetyMonotonicity.

Lemma runnable_false (G C M D: Type) (csem: CoreSemantics G C M D): 
 forall c, runnable csem c=false -> 
 (exists rv, safely_halted csem c = Some rv) \/
 (exists ef, exists sig, exists args, 
   at_external csem c = Some (ef, sig, args)).
Proof.
intros c; unfold runnable.
destruct (at_external csem c).
destruct p as [[ef sig] vals].
intros; right; do 3 eexists; eauto.
destruct (safely_halted csem c).
intros; left; eexists; eauto.
congruence.
Qed.

Module ExtensionSafety. Section ExtensionSafety.
 Variables
  (G: Type) (** global environments *)
  (D: Type) (** initialization data *)
  (xT: Type) (** corestates of extended semantics *)
  (gT: nat -> Type) (** global environments of the core semantics *)
  (cT: nat -> Type) (** corestates of core semantics *)
  (M: Type) (** memories *)
  (dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)

  (esem: CoreSemantics G xT M D) (** extended semantics *)
  (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (dT i)) (** a set of core semantics *)

  (csig: ext_spec M Z) (** client signature *)
  (esig: ext_spec M Zext) (** extension signature *)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (E: Extension.Sig gT cT dT Zint esem csem csig esig handled). 

 Variables (ge: G) (genv_map : forall i:nat, gT i).

Import SafetyInvariant.
Import TruePropCoercion.

Definition proj_zint := (proj_zint E). 
Coercion proj_zint : xT >-> Zint.

Definition proj_zext := (proj_zext E).
Coercion proj_zext : Z >-> Zext.

Notation ALL_SAFE := (all_safe E).
Notation PROJ_CORE := E.(Extension.proj_core).
Notation "zint \o zext" := (E.(Extension.zmult) zint zext) 
  (at level 66, left associativity). 
Notation ACTIVE := (E.(Extension.active)).
Notation active_proj_core := E.(Extension.active_proj_core).
Notation notat_external_handled := E.(Extension.notat_external_handled).
Notation at_external_not_handled := E.(Extension.at_external_not_handled).
Notation ext_upd_at_external := E.(Extension.ext_upd_at_external).

Program Definition ExtensionSafety: EXTENSION_SAFETY.Sig ge genv_map E.
Proof.
constructor.
inversion 1; subst; intros n; induction n.
intros s m z H1; simpl; auto.
intros s m z H1.
simpl; case_eq (at_external esem s).

(*CASE 1: at_external OUTER = Some _; i.e. _really_ at_external*) 
intros [[ef sig] args] AT_EXT.
destruct (at_external_halted_excl esem s) as [H2|H2].
rewrite AT_EXT in H2; congruence.
simpl; rewrite H2.
destruct (at_extern_call s ef sig args AT_EXT) as [c [H4 H5]].
assert (H3: True) by auto.
generalize H1 as H1'; intro.
specialize (H1 (ACTIVE s) c H4).
simpl in H1.
rewrite H5 in H1.
destruct (at_external_halted_excl (csem (ACTIVE s)) c) as [H6|H6].
rewrite H6 in H5; congruence.
rewrite H6 in H1; clear H6.
destruct H1 as [x H1].
destruct H1 as [H7 H8].
generalize (Extension.esem_csem_linkable E); intros Hlink.
(*assert (H16: IN ef (DIFF csig handled)).
 apply in_diff.
 eapply Extension.at_external_csig; eauto.
 solve[eapply Extension.at_external_not_handled with (esem := esem); eauto].*)
specialize (Hlink ef 
  (ext_spec_pre esig ef) (ext_spec_post esig ef) 
  (ext_spec_pre csig ef) (ext_spec_post csig ef)).
destruct Hlink with (x' := x) 
 (tys := sig_args sig) (args := args) (m := m) (z := (s \o z)) 
 as [x' [H17 H18]]; auto.
exists x'.
erewrite at_external_not_handled; eauto.
split; auto.
rewrite Extension.zmult_proj in H17; auto.
intros ret m' z' POST.
destruct (H8 ret m' (s \o z')) as [c' [H10 H11]].
specialize (H18 (sig_res sig) ret m' (s \o z')).
rewrite Extension.zmult_proj in H18.
eapply H18 in POST; eauto.
specialize (at_extern_ret z s c m z' m' (sig_args sig) args (sig_res sig) ret c' 
 ef sig x' (ext_spec_pre esig ef) (ext_spec_post esig ef)).
hnf in at_extern_ret.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
destruct at_extern_ret as [s' [H12 [H13 H14]]].
assert (H15: True) by auto.
exists s'.
split; auto.
rewrite H12.
eapply IHn.
intros j cj PROJJ.
case_eq (eq_nat_dec (ACTIVE s) j).
(*i=j*)
intros Heq _. 
subst j.
rewrite PROJJ in H14; inversion H14; rewrite H1 in *.
unfold proj_zint in H12.
unfold proj_zint.
rewrite <-H12.
eapply ext_upd_at_external in H13; eauto.
rewrite <-H13; auto.
(*i<>j*)
intros Hneq _.
specialize (at_extern_rest z s c m z' s' m' (sig_args sig) args (sig_res sig) ret c' 
  ef x' sig (ext_spec_pre esig ef) (ext_spec_post esig ef)).
hnf in at_extern_rest.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
destruct (at_extern_rest j (csem j) cj Hneq) as [H19 H20].
rewrite <-H12.
solve[eapply H20; eauto].

(*CASE 2: at_external OUTER = None; i.e., inner corestep or handled function*)
intros H2.
case_eq (safely_halted esem s); auto.
destruct (active_proj_core s) as [c PROJECT].
case_eq (runnable (csem (ACTIVE s)) c).
(*active thread i is runnable*)
intros RUN.
destruct (core_prog n (s \o z) s m c H1 PROJECT)
 as [c' [s' [m' [CORESTEP_C [CORESTEP_T ?]]]]]; auto.
generalize (core_pres n z s c m s' c' m' H1)
 as INV'; auto.
intros Hsafehalt.
exists s'; exists m'; split; [auto|].
solve[eauto].

(*active thread not runnable*)
intros RUN.
destruct (handled_prog n z s m c H1 PROJECT RUN H2)
 as [[s' [m' [CORESTEP_T CORES_PRES]]]|[rv SAFELY_HALTED]].
2: intros CONTRA; rewrite CONTRA in SAFELY_HALTED; congruence.
exists s'; exists m'.
split; auto.
eapply IHn.
destruct (runnable_false (csem (ACTIVE s)) c RUN) 
 as [SAFELY_HALTED|[ef [sig [args AT_EXT]]]].

(*subcase A of no runnable thread: safely halted*)
intros j cj PROJECTj.
set (i := ACTIVE s) in *.
case_eq (eq_nat_dec i j).
(*i=j*)
intros Heq _; subst j.
specialize (H1 i c PROJECT).
simpl in H1. 
destruct SAFELY_HALTED as [rv SAFELY_HALTED].
destruct (@at_external_halted_excl (gT i) (cT i) M (dT i) (csem i) c) as [H4|H4]; 
 [|congruence].
destruct n; simpl; auto.
generalize (safely_halted_halted s m s' m' i c rv) as H7; auto. 
intros.
assert (H6:True) by auto.
rewrite H7 in PROJECTj; inversion PROJECTj; subst; auto.
solve[rewrite H4, SAFELY_HALTED; auto].
(*i<>j*)
intros Hneq _.
destruct (CORES_PRES i c) as [c' [PROJ' H5]]; auto.
specialize (handled_rest s m s' m' c).
hnf in handled_rest.
spec handled_rest; auto.
spec handled_rest; auto.
spec handled_rest; auto.
spec handled_rest; auto.
destruct (handled_rest j cj Hneq) as [H6 H7].
solve[eapply H7 with (z:=z); eauto].

(*subcase B of no runnable thread: at external INNER*)
intros j cj PROJECTj.
set (i := ACTIVE s) in *.
case_eq (eq_nat_dec i j).
(*i=j*)
intros Heq _; subst j.
specialize (H1 i c PROJECT).
simpl in H1. 
rewrite AT_EXT in H1.
remember (safely_halted (csem i) c) as SAFELY_HALTED.
destruct SAFELY_HALTED. 
solve[destruct ef; elimtype False; auto].
destruct H1 as [x H1].
destruct H1 as [PRE POST].
specialize (handled_pres s z m c s' m' cj ef sig args
  (ext_spec_pre csig ef)
  (ext_spec_post csig ef) x).
hnf in handled_pres.
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto.
 solve[eapply notat_external_handled in AT_EXT; eauto].
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto.
destruct (CORES_PRES i c) as [c' H4]; auto.
destruct handled_pres as [[AT_EXT' [PRE' ACT']] | POST'].
(*pre-preserved case*)
destruct H4 as [H5 H6].
assert (H4:True) by auto.
rewrite H5 in PROJECTj; inversion PROJECTj; subst.
specialize (H6 (ef,sig) args (ef,sig) args AT_EXT AT_EXT'); subst.
clear - PRE' POST AT_EXT' H4 H5 HeqSAFELY_HALTED H2 AT_EXT PROJECT.
destruct n; simpl; auto.
rewrite AT_EXT.
rewrite <-HeqSAFELY_HALTED.
exists x.
split; auto.
intros ret m'' s'' H8.
destruct (POST ret m'' s'' H8) as [c'' [H9 H10]].
exists c''; split; auto.
eapply safe_downward1; eauto.
(*post case*)
destruct H4 as [H5 H6].
assert (H4:True) by auto.
rewrite H5 in PROJECTj; inversion PROJECTj; rename H3 into H1; rewrite <-H1 in *.
destruct POST' as [ret [AFTER_EXT POST']].
generalize (after_at_external_excl (csem i) ret c c' AFTER_EXT); intros AT_EXT'.
clear - PRE POST POST' AT_EXT' AFTER_EXT H4 H5 H6 HeqSAFELY_HALTED.
destruct n; simpl; auto.
rewrite AT_EXT'.
case_eq (safely_halted (csem i) c'); auto.
destruct (POST ret m' (s' \o z) POST') as [c'' [AFTER_EXT' SAFEN]].
unfold i in AFTER_EXT'.
rewrite AFTER_EXT in AFTER_EXT'; inversion AFTER_EXT'; subst.
simpl in SAFEN.
rewrite AT_EXT' in SAFEN.
intros SAFELY_HALTED; rewrite SAFELY_HALTED in SAFEN.
destruct SAFEN as [c3 [m'' [H7 H8]]].
exists c3; exists m''; split; auto.
(*i<>j: i.e., nonactive thread*)
intros Hneq _.
destruct (CORES_PRES i c) as [c' [PROJ' H5]]. 
auto.
specialize (handled_rest s m s' m' c).
hnf in handled_rest.
spec handled_rest; auto.
spec handled_rest; auto.
left; exists ef; exists sig; exists args; auto.
spec handled_rest; auto.
spec handled_rest; auto.
destruct (handled_rest j cj Hneq) as [H6 H7].
solve[eapply H7 with (z:=z); eauto].
Qed.

End ExtensionSafety. End ExtensionSafety.

Section CoreCompatibleLemmas.
Variables 
 (G xT M D Z Zint Zext: Type) (gT: nat -> Type) (cT: nat -> Type) (dT: nat -> Type)
 (esem: CoreSemantics G xT M D) 
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (dT i))
 (csig: ext_spec M Z)
 (esig: ext_spec M Zext)
 (handled: list AST.external_function)
 (E: Extension.Sig gT cT dT Zint esem csem csig esig handled).

Variables (ge: G) (genv_map : forall i:nat, gT i).

Variable Hcore_compatible: core_compatible ge genv_map E.

Import Extension.

Lemma corestep_step: 
  forall s (c: cT (active E s)) m c' m',
  proj_core E (active E s) s = Some c -> 
  corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
  exists s', corestep esem ge s m s' m' /\
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
Proof.
intros until m'; intros H0 H1.
inv Hcore_compatible.
generalize H1 as H1'; intro.
eapply corestep_prog in H1; eauto.
destruct H1 as [s' H1].
exists s'.
solve[split; eauto]. 
Qed.

Lemma corestep_stepN: 
  forall n s (c: cT (active E s)) m c' m',
  proj_core E (active E s) s = Some c -> 
  corestepN (csem (active E s)) (genv_map (active E s)) n c m c' m' -> 
  exists s', corestepN esem ge n s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
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
destruct (IHn s2 c2 m2 c' m') as [s' [H10 [H11 H13]]]; auto.
exists s'.
split3.
simpl.
exists s2; exists m2; split; eauto.
auto.
auto.
Qed.

Lemma corestep_step_star: 
  forall s (c: cT (active E s)) m c' m',
  proj_core E (active E s) s = Some c -> 
  corestep_star (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
  exists s', corestep_star esem ge s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
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
  forall s (c: cT (active E s)) m c' m',
  proj_core E (active E s) s = Some c -> 
  corestep_plus (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
  exists s', corestep_plus esem ge s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
Proof.
intros until m'; intros H0 H1.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 [H2 H4]]].
exists s'.
split3; auto.
solve[exists n; eauto].
Qed.

End CoreCompatibleLemmas.

Lemma meminj_preserves_genv2blocks: 
  forall {F V: Type} (ge: Genv.t F V) j,
  meminj_preserves_globals (genv2blocks ge) j <->
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
  (meminj_preserves_globals (genv2blocks ge1) j <-> 
   meminj_preserves_globals (genv2blocks ge2) j).
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

Module ExtendedSimulations. Section ExtendedSimulations.
 Variables
  (F_S V_S F_T V_T: Type) (** global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F_S V_S) xS mem D_S) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F_T V_T) xT mem D_T) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) (** a set of core semantics *)
  (csig: ext_spec mem Z) (** client signature *)
  (esig: ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: Extension.Sig (fun i => Genv.t (fS i) (vS i)) cS dS Zint esemS csemS
                  csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t (fT i) (vT i)) cT dT Zint esemT csemT
                  csig esig handled).

 Variable entry_points: list (val*val*signature).
 Variable threads_max: nat.

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation notat_external_handled := (Extension.notat_external_handled).
 Notation at_external_not_handled := (Extension.at_external_not_handled).
 Notation ext_upd_at_external := (Extension.ext_upd_at_external).

 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Import Sim_inj_exposed.

 Variable core_simulations: forall i:nat, 
   Forward_simulation_inject (dS i) (dT i) (csemS i) (csemT i) (genv_mapS i) (genv_mapT i) 
   entry_points (core_data i) (match_state i) (core_ord i).

 Definition core_datas := forall i:nat, core_data i.

 Variable R: meminj -> xS -> mem -> xT -> mem -> Prop.

 Definition core_datas_upd
  i (cdi': core_data i) (cd: forall i:nat, core_data i): 
  forall i:nat, core_data i := fun j: nat => 
     match eq_nat_dec i j as pf in sumbool _ _ return core_data j with
     | left pf => match pf with
                  | eq_refl => cdi'
                  end
     | right pf => cd j
     end.
 Implicit Arguments core_datas_upd [].

 Lemma core_datas_upd_same i cdi' cd: (core_datas_upd i cdi' cd) i = cdi'.
 Proof.
 unfold core_datas_upd.
 destruct (eq_nat_dec i i).
 rewrite (UIP_refl _ _ e); auto.
 elimtype False; auto.
 Qed.

 Lemma core_datas_upd_other i j cdi' cd: i<>j -> (core_datas_upd i cdi' cd) j = cd j.
 Proof.
 unfold core_datas_upd.
 destruct (eq_nat_dec i j).
 intros; elimtype False; auto.
 auto.
 Qed.

 Definition core_ords cd1 cd2 := 
  exists i, (i < threads_max)%nat /\
   (forall j, (j < i)%nat -> cd1 j=cd2 j) /\ core_ord i (cd1 i) (cd2 i)%nat.

 Lemma core_ords_wf: well_founded core_ords.
 Proof.
 unfold core_ords.
 induction threads_max.
 constructor.
 intros b [i [H _]].
 elimtype False; omega.
 constructor.
 intros b [i [H1 [H2 H3]]].
 case_eq (eq_nat_dec i n).
  intros EQ _; subst.
  clear H1.
  destruct (IHn a) as [H4].
  specialize (H4 b).
 Admitted. (*TODO*)

 Definition core_ords_aux (i: nat) (cd1 cd2: core_datas): Prop := 
   core_ord i (cd1 i) (cd2 i) /\
   (forall j, (j < i)%nat -> cd1 j=cd2 j).

 Lemma core_ords_aux0: forall cd1 cd2,
   core_ords_aux O cd1 cd2 <-> core_ord O (cd1 O) (cd2 O). 
 Proof.
 intros cd1 cd2.
 unfold core_ords_aux.
 split.
 intros [H1 H2]; auto.
 intros H1.
 split; auto.
 intros j CONTRA.
 elimtype False; omega.
 Qed.

 Definition match_states (cd: core_datas) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   R j s1 m1 s2 m2 /\ ACTIVE E_S s1=ACTIVE E_T s2 /\
   forall i c1, PROJ_CORE E_S i s1 = Some c1 -> 
     exists c2, PROJ_CORE E_T i s2 = Some c2 /\ 
       match_state i (cd i) j c1 m1 c2 m2.

 Inductive internal_compilability_invariant: Type := 
   InternalCompilabilityInvariant: forall 
  (match_others: forall i cd j j' s1 cd' c1 m1 c1' m1' s2 c2 m2 c2' m2' d1 d2 n, 
    PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
    PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
    PROJ_CORE E_S i s1 = Some d1 -> 
    PROJ_CORE E_T i s2 = Some d2 -> 
    ACTIVE E_S s1 <> i -> 
    match_states cd j s1 m1 s2 m2 -> 
    Mem.inject j m1 m2 -> 
    meminj_preserves_globals (genv2blocks ge_S) j -> 
    inject_incr j j' -> 
    Events.inject_separated j j' m1 m2 -> 
    corestep (csemS (ACTIVE E_S s1)) (genv_mapS (ACTIVE E_S s1)) c1 m1 c1' m1' -> 
    corestepN (csemT (ACTIVE E_S s1)) (genv_mapT (ACTIVE E_S s1)) n c2 m2 c2' m2' -> 
    match_state (ACTIVE E_S s1) cd' j' c1' m1' c2' m2' -> 
    match_state i (cd i) j' d1 m1' d2 m2')

  (match_state_runnable: forall i cd j c1 m1 c2 m2,
    match_state i cd j c1 m1 c2 m2 -> runnable (csemS i) c1=runnable (csemT i) c2)

  (match_state_inj: forall i cd j c1 m1 c2 m2,
    match_state i cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)

  (match_state_preserves_globals: forall i cd j c1 m1 c2 m2,
    match_state i cd j c1 m1 c2 m2 -> 
    Events.meminj_preserves_globals (genv_mapS i) j)

  (corestep_rel: forall cd j j' s1 c1 m1 c1' m1' s2 c2 m2 c2' m2' s1' s2' n, 
    PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
    PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
    match_states cd j s1 m1 s2 m2 -> 
    Mem.inject j m1 m2 -> 
    meminj_preserves_globals (genv2blocks ge_S) j -> 
    inject_incr j j' -> 
    Events.inject_separated j j' m1 m2 -> 
    corestep (csemS (ACTIVE E_S s1)) (genv_mapS (ACTIVE E_S s1)) c1 m1 c1' m1' -> 
    corestepN (csemT (ACTIVE E_S s1)) (genv_mapT (ACTIVE E_S s1)) n c2 m2 c2' m2' ->
    corestep esemS ge_S s1 m1 s1' m1' -> 
    corestepN esemT ge_T n s2 m2 s2' m2' -> 
    R j' s1' m1' s2' m2')

  (after_external_rel: forall cd j j' s1 m1 s2 m2 s1' m1' s2' m2' ret1 ret2 ef sig args1,
    match_states cd j s1 m1 s2 m2 -> 
    inject_incr j j' -> 
    Events.inject_separated j j' m1 m2 -> 
    Mem.inject j' m1' m2' -> 
    mem_forward m1 m1'-> 
    Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' -> 
    mem_forward m2 m2' -> 
    Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' -> 
    at_external esemS s1 = Some (ef, sig, args1) -> 
    after_external esemS ret1 s1 = Some s1' -> 
    after_external esemT ret2 s2 = Some s2' -> 
    R j' s1' m1' s2' m2')   

  (extension_diagram: forall s1 m1 s1' m1' s2 c1 c2 m2 ef sig args1 args2 cd j,
    PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
    PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
    runnable (csemS (ACTIVE E_S s1)) c1=false -> 
    runnable (csemT (ACTIVE E_S s1)) c2=false -> 
    at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
    at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
    match_states cd j s1 m1 s2 m2 -> 
    Mem.inject j m1 m2 -> 
    Events.meminj_preserves_globals ge_S j -> 
    Forall2 (val_inject j) args1 args2 -> 
    Forall2 Val.has_type args2 (sig_args sig) -> 
    corestep esemS ge_S s1 m1 s1' m1' -> 
    exists s2', exists m2', exists cd', exists j',
      inject_incr j j' /\
      Events.inject_separated j j' m1 m2 /\
      match_states cd' j' s1' m1' s2' m2' /\
      ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
        corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ords cd' cd))

  (at_external_match: forall s1 m1 s2 c1 c2 m2 ef sig args1 args2 cd j,
    ACTIVE E_S s1=ACTIVE E_T s2 -> 
    PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
    PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
    runnable (csemS (ACTIVE E_S s1)) c1=runnable (csemT (ACTIVE E_S s1)) c2 -> 
    at_external esemS s1 = Some (ef, sig, args1) -> 
    at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
    match_state (ACTIVE E_S s1) cd j c1 m1 c2 m2 -> 
    Mem.inject j m1 m2 -> 
    Events.meminj_preserves_globals ge_S j -> 
    Forall2 (val_inject j) args1 args2 -> 
    Forall2 Val.has_type args2 (sig_args sig) -> 
    at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
    at_external esemT s2 = Some (ef, sig, args2))

  (after_external_diagram: 
    forall i d1 s1 m1 d2 s2 m2 s1' m1' s2' m2' ef sig args1 retv1 retv2 cd j j',
    match_state i cd j d1 m1 d2 m2 -> 
    at_external esemS s1 = Some (ef, sig, args1) -> 
    Events.meminj_preserves_globals ge_S j -> 
    inject_incr j j' -> 
    Events.inject_separated j j' m1 m2 -> 
    Mem.inject j' m1' m2' -> 
    val_inject j' retv1 retv2 -> 
    mem_forward m1 m1' -> 
    Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' -> 
    mem_forward m2 m2' -> 
    Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' -> 
    Val.has_type retv2 (proj_sig_res sig) -> 
    after_external esemS (Some retv1) s1 = Some s1' -> 
    after_external esemT (Some retv2) s2 = Some s2' -> 
    PROJ_CORE E_S i s1' = Some d1 -> 
    PROJ_CORE E_T i s2' = Some d2 -> 
    ACTIVE E_S s1 <> i -> 
    match_state i cd j' d1 m1' d2 m2')

  (make_initial_core_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 j sig,
    In (v1, v2, sig) entry_points -> 
    make_initial_core esemS ge_S v1 vals1 = Some s1 -> 
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 -> 
    Forall2 Val.has_type vals2 (sig_args sig) -> 
    exists cd, exists s2, 
      make_initial_core esemT ge_T v2 vals2 = Some s2 /\
      match_states cd j s1 m1 s2 m2)

  (safely_halted_step: forall cd j c1 m1 c2 m2 v1,
    match_states cd j c1 m1 c2 m2 -> 
    safely_halted esemS c1 = Some v1 -> 
    exists v2, val_inject j v1 v2 /\
      safely_halted esemT c2 = Some v2 /\ Mem.inject j m1 m2)

  (safely_halted_diagram: forall cd j m1 m1' m2 rv1 s1 s2 s1' c1 c2,
    match_states cd j s1 m1 s2 m2 -> 
    PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
    PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
    safely_halted (csemS (ACTIVE E_S s1)) c1 = Some rv1 -> 
    corestep esemS ge_S s1 m1 s1' m1' ->  
    exists rv2, 
      safely_halted (csemT (ACTIVE E_S s1)) c2 = Some rv2 /\
      val_inject j rv1 rv2 /\
    exists s2', exists m2', exists cd', exists j', 
      inject_incr j j' /\
      Events.inject_separated j j' m1 m2 /\
      corestep esemT ge_T s2 m2 s2' m2' /\
      match_states cd' j' s1' m1' s2' m2'),
  internal_compilability_invariant.

 Variables 
  (esig_compilable: internal_compilability_invariant)
  (genvs_domain_eqS: forall i: nat, genvs_domain_eq ge_S (genv_mapS i))
  (genvs_domain_eqT: forall i: nat, genvs_domain_eq ge_T (genv_mapT i))
  (core_compatS: core_compatible ge_S genv_mapS E_S) 
  (core_compatT: core_compatible ge_T genv_mapT E_T).

Program Definition extended_simulation: 
  Forward_simulation_inject D_S D_T esemS esemT ge_S ge_T 
           entry_points core_datas match_states core_ords :=
  @Build_Forward_simulation_inject _ _ _ _ _ _ _ 
  esemS esemT ge_S ge_T entry_points core_datas match_states core_ords _ _ _ _ _ _.
Next Obligation. apply core_ords_wf. Qed.
Next Obligation. 
rename H0 into MATCH.
generalize MATCH as MATCH'; intro.
destruct MATCH as [RR [ACT MATCH_CORES]].
rename H into STEP.
destruct (active_proj_core E_S st1) as [c1 PROJ1].
destruct (active_proj_core E_T st2) as [c2 PROJ2].
assert (exists c2':cT (ACTIVE E_S st1), PROJ_CORE E_T (ACTIVE E_S st1) st2 = Some c2').
 clear - ACT c2 PROJ2.
 forget (ACTIVE E_S st1) as xx.
 forget (ACTIVE E_T st2) as yy.
 subst.
 solve[eexists; eauto].
clear c2 PROJ2.
destruct H as [c2 PROJ2].
case_eq (runnable (csemS (ACTIVE E_S st1)) c1).

(*Case 1: runnable thread, appeal to core diagram for cores*)
intros RUN1.
assert (RUN2: runnable (csemT (ACTIVE E_S st1)) c2=true).
 inv esig_compilable.
 rewrite match_state_runnable 
  with (cd := cd (ACTIVE E_S st1)) (j := j) (m1 := m1) (c2 := c2) (m2 := m2) in RUN1.
 auto.
 specialize (MATCH_CORES (ACTIVE E_S st1) c1).
 spec MATCH_CORES; auto.
 destruct MATCH_CORES as [c2' [PROJ2' MTCH]].
 rewrite PROJ2' in PROJ2.
 inv PROJ2.
 solve[auto].
assert (exists c1', corestep (csemS (ACTIVE E_S st1)) (genv_mapS (ACTIVE E_S st1)) 
         c1 m1 c1' m1') as [c1' STEP1].
 inv esig_compilable.
 inv core_compatS.
 specialize (runnable_corestep st1 m1 st1' m1' c1).
 destruct runnable_corestep as [c1' [H3 H4]]; auto.
 solve[exists c1'; auto].
assert (PROJ1': PROJ_CORE E_S (ACTIVE E_S st1) st1' = Some c1').
 inv core_compatS.
 specialize (corestep_pres st1 c1 m1 c1' st1' m1').
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 solve[destruct corestep_pres; auto].
assert (ACT1': ACTIVE E_S st1 = ACTIVE E_S st1').
 inv core_compatS.
 specialize (corestep_pres st1 c1 m1 c1' st1' m1').
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 solve[destruct corestep_pres; auto].
generalize (core_diagram (core_simulations (ACTIVE E_S st1))) as DIAG; intro.
clear c2 PROJ2 RUN2.
destruct (MATCH_CORES (ACTIVE E_S st1) c1 PROJ1) as [c2 [PROJ2 MATCH12]].
unfold core_datas in cd.
specialize (DIAG c1 m1 c1' m1' STEP1 (cd _) c2 j m2 MATCH12).
destruct DIAG as [c2' [m2' [cd' [j' [INJ_INCR [INJ_SEP [MATCH12' STEP2]]]]]]].
destruct STEP2 as [STEP2|STEP2].

(*corestep_plus case*)
destruct STEP2 as [n STEP2].
generalize (corestep_stepN core_compatT) as CSTEPN; intro.
specialize (CSTEPN (S n) st2). 
rewrite <-ACT in *.
specialize (CSTEPN c2 m2 c2' m2').
spec CSTEPN; auto.
spec CSTEPN; auto. 
destruct CSTEPN as [st2' [ESEM2 [ACT2' PROJ2']]].
exists st2'; exists m2'.
exists (core_datas_upd (ACTIVE E_S st1) cd' cd).
exists j'.
split3; auto.
split; auto.
 (*Subgoal: match_states*)
 hnf.
 split.
 inv esig_compilable. 
 eapply corestep_rel with (s1 := st1) (s2 := st2); eauto.
 erewrite <-genvs_domain_eq_preserves.
 erewrite meminj_preserves_genv2blocks.
 eauto.
 solve[apply genvs_domain_eq_sym; auto].
 split.
 solve[rewrite <-ACT1', <-ACT2'; auto].
 
  intros i _c _PROJ1'.
  case_eq (eq_nat_dec (ACTIVE E_S st1) i).
  
  (*ACTIVE E_S st1 = i*)
  forget (ACTIVE E_S st1) as x.
  forget (ACTIVE E_T st2) as y.
  forget (ACTIVE E_S st1') as x'.
  forget (ACTIVE E_T st2') as y'.
  intros EQ _. 
  do 4 subst.
  exists c2'.
  rewrite PROJ1' in _PROJ1'.
  inv _PROJ1'.
  split; auto.
  solve[rewrite core_datas_upd_same; auto].

  (*ACTIVE E_S st1 <> i*)
  intros NEQ _.
  assert (_PROJ1: PROJ_CORE E_S i st1 = Some _c). 
   inv core_compatS.
   specialize (corestep_others_forward st1 st1'). 
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
   specialize (corestep_others_forward i NEQ).
   solve[rewrite corestep_others_forward; auto].
  assert (exists _d, PROJ_CORE E_T i st2 = Some _d) as [_d _PROJ2].
   destruct (MATCH_CORES i _c _PROJ1) as [_d [_PROJ2 _MATCH12]].
   solve[exists _d; auto].
  assert (_PROJ2': PROJ_CORE E_T i st2' = Some _d). 
   inv core_compatT.
   specialize (corestep_others_backward st2). 
   forget (ACTIVE E_S st1) as x.
   forget (ACTIVE E_T st2) as y.
   forget (ACTIVE E_S st1') as x'.
   forget (ACTIVE E_T st2') as y'.
   do 4 subst.
   specialize (corestep_others_backward c2 m2 st2' c2' m2' (S n)).
   spec corestep_others_backward; auto.
   spec corestep_others_backward; auto. 
   spec corestep_others_backward; auto.
   specialize (corestep_others_backward i NEQ).
   solve[rewrite <-corestep_others_backward; auto].
  exists _d; split; auto.
  inv esig_compilable.
  specialize (match_others i cd j j' st1 cd' c1 m1 c1' m1' st2 c2 m2 c2' m2' _c _d (S n)).
  rewrite core_datas_upd_other; auto.
  apply match_others; auto.
   solve[eapply match_state_inj; eauto].
   erewrite <-genvs_domain_eq_preserves.
   erewrite meminj_preserves_genv2blocks.
   eauto.
   solve[apply genvs_domain_eq_sym; auto].
  solve[left; exists n; auto].

(*corestep_star case*)
destruct STEP2 as [[n STEP2] ORD].
generalize (corestep_stepN core_compatT) as CSTEPN; intro.
specialize (CSTEPN n st2). 
rewrite <-ACT in *.
specialize (CSTEPN c2 m2 c2' m2').
spec CSTEPN; auto.
spec CSTEPN; auto. 
destruct CSTEPN as [st2' [ESEM2 [ACT2' PROJ2']]].
exists st2'; exists m2'. 
exists (core_datas_upd (ACTIVE E_S st1) cd' cd).
exists j'.
split3; auto.
split; auto.
 (*Subgoal: match_states*)
 hnf.
 split.
 inv esig_compilable.
 eapply corestep_rel with (s1 := st1) (s2 := st2); eauto.
 erewrite <-genvs_domain_eq_preserves.
 erewrite meminj_preserves_genv2blocks.
 eauto.
 solve[apply genvs_domain_eq_sym; auto].
 split.
 solve[rewrite <-ACT2'; auto].

  intros i _c _PROJ1'.
  case_eq (eq_nat_dec (ACTIVE E_S st1) i).
  
  (*ACTIVE E_S st1 = i*)
  forget (ACTIVE E_S st1) as x.
  forget (ACTIVE E_T st2) as y.
  forget (ACTIVE E_S st1') as x'.
  forget (ACTIVE E_T st2') as y'.
  intros EQ _. 
  do 4 subst.
  exists c2'.
  rewrite PROJ1' in _PROJ1'.
  inv _PROJ1'.
  split; auto.
  solve[rewrite core_datas_upd_same; auto].

  (*ACTIVE E_S st1 <> i*)
  intros NEQ _.
  assert (_PROJ1: PROJ_CORE E_S i st1 = Some _c). 
   inv core_compatS.
   specialize (corestep_others_forward st1 st1'). 
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
   specialize (corestep_others_forward i NEQ).
   solve[rewrite corestep_others_forward; auto].
  assert (exists _d, PROJ_CORE E_T i st2 = Some _d) as [_d _PROJ2].
   destruct (MATCH_CORES i _c _PROJ1) as [_d [_PROJ2 _MATCH12]].
   solve[exists _d; auto].
  assert (_PROJ2': PROJ_CORE E_T i st2' = Some _d). 
   inv core_compatT.
   specialize (corestep_others_backward st2). 
   forget (ACTIVE E_S st1) as x.
   forget (ACTIVE E_T st2) as y.
   forget (ACTIVE E_S st1') as x'.
   forget (ACTIVE E_T st2') as y'.
   do 4 subst.
   specialize (corestep_others_backward c2 m2 st2' c2' m2' n).
   spec corestep_others_backward; auto.
   spec corestep_others_backward; auto. 
   spec corestep_others_backward; auto.
   specialize (corestep_others_backward i NEQ).
   solve[rewrite <-corestep_others_backward; auto].
  exists _d; split; auto.
  inv esig_compilable.
  specialize (match_others i cd j j' st1 cd' c1 m1 c1' m1' st2 c2 m2 c2' m2' _c _d n).
  rewrite core_datas_upd_other; auto.
  apply match_others; auto.
  solve[eapply match_state_inj; eauto].
  erewrite <-genvs_domain_eq_preserves.
  erewrite meminj_preserves_genv2blocks.
  eauto.
  solve[apply genvs_domain_eq_sym; auto].
  right. split. exists n. auto. 
  admit. (*should follow from ORD and definition of generalized lex_prod*)

(*runnable = false*)
intros RUN1.
generalize PROJ1 as _PROJ1; intro.
generalize RUN1 as RUN1'; intro.
apply runnable_false in RUN1.
destruct RUN1 as [[rv1 HALT]|[ef [sig [args AT_EXT]]]].

(*active thread is safely halted*)
specialize (MATCH_CORES (ACTIVE E_S st1) c1 _PROJ1).
clear c2 PROJ2.
destruct MATCH_CORES as [c2 [PROJ2 MATCH12]].
destruct (core_halted (core_simulations (ACTIVE E_S st1)) 
  (cd (ACTIVE E_S st1)) j c1 m1 c2 m2 rv1 MATCH12 HALT) 
 as [rv2 [VAL_INJ [SAFE_T INJ]]].
inv esig_compilable.
eapply safely_halted_diagram with (m1' := m1') in MATCH'; eauto.
destruct MATCH' as [rv2' [H7 [VAL_INJ' 
 [st2' [m2' [cd' [j' [INJ_INCR [SEP [STEP2' MATCH12']]]]]]]]]].
exists st2'; exists m2'; exists cd'; exists j'.
split3; auto; split; auto.
solve[left; exists 0%nat; eexists; eexists; split; simpl; eauto].

(*active thread is at_external*)
clear c2 PROJ2.
destruct (MATCH_CORES (ACTIVE E_S st1) c1 _PROJ1) as [c2 [PROJ2 MATCH12]].
destruct (core_at_external (core_simulations (ACTIVE E_S st1)) (cd (ACTIVE E_S st1)) 
            j c1 m1 c2 m2 ef args sig MATCH12 AT_EXT)
 as [H6 [H7 [vals2 [H8 [H9 H10]]]]].
inv esig_compilable. 
edestruct extension_diagram as [s2' H11]; eauto.
solve[erewrite <-match_state_runnable; eauto].
rewrite <-meminj_preserves_genv2blocks.
rewrite genvs_domain_eq_preserves with (ge2 := (genv_mapS (ACTIVE E_S st1))); auto.
solve[rewrite meminj_preserves_genv2blocks; auto].
Qed.

(*we punt in the make_initial_core case of the simulation proof; to do more requires 
   assuming too much about the structure of the extension w/r/t its inner cores*)
Next Obligation. inv esig_compilable. eapply make_initial_core_diagram; eauto. Qed.
Next Obligation. inv esig_compilable. eapply safely_halted_step; eauto. Qed.

Next Obligation. 
rename H into MATCH.
hnf in MATCH.
destruct MATCH as [RR [ACT MATCH_CORES]].
destruct (active_proj_core E_S) with (s := st1) as [c1 PROJ1].
assert (AT_EXT1: at_external (csemS (ACTIVE E_S st1)) c1 = Some (e, ef_sig, vals1)).
 inv core_compatS.
 edestruct (at_extern_call) as [c [PROJ AT_EXT]]; eauto.
 rewrite PROJ in PROJ1; inv PROJ1.
 solve[inv PROJ; auto].
destruct (MATCH_CORES (ACTIVE E_S st1) c1 PROJ1) as [c2 [PROJ2 MATCH12]].
destruct (core_at_external (core_simulations (ACTIVE E_S st1)) 
            (cd (ACTIVE E_S st1)) j c1 m1 c2 m2 e vals1 ef_sig MATCH12 AT_EXT1)
 as [INJ [GLOBS [vals2 [VALINJ [TYPE AT_EXT2]]]]].
split3; auto.
rewrite <-meminj_preserves_genv2blocks.
rewrite genvs_domain_eq_preserves with (ge2 := (genv_mapS (ACTIVE E_S st1))); auto.
rewrite meminj_preserves_genv2blocks; auto.
exists vals2.
split3; auto.
inv esig_compilable.
eapply at_external_match; eauto.
rewrite <-meminj_preserves_genv2blocks.
rewrite genvs_domain_eq_preserves with (ge2 := (genv_mapS (ACTIVE E_S st1))); auto.
rewrite meminj_preserves_genv2blocks; auto.
Qed.

Next Obligation. 
rename H0 into MATCH.
generalize MATCH as MATCH'; intro.
hnf in MATCH.
destruct MATCH as [RR [ACT MATCH_CORES]].
generalize MATCH_CORES as MATCH_CORES'; intro.
destruct (active_proj_core E_S) with (s := st1) as [c1 PROJ1].
assert (AT_EXT1: at_external (csemS (ACTIVE E_S st1)) c1 = Some (e, ef_sig, vals1)).
 inv core_compatS.
 edestruct (at_extern_call) as [c [PROJ AT_EXT]]; eauto.
 rewrite PROJ in PROJ1; inv PROJ1.
 solve[inv PROJ; auto].
destruct (MATCH_CORES (ACTIVE E_S st1) c1 PROJ1) as [c2 [PROJ2 MATCH12]].
destruct (core_after_external (core_simulations (ACTIVE E_S st1)) 
                (cd (ACTIVE E_S st1)) j j' c1 c2 m1 e 
                vals1 ret1 m1' m2 m2' ret2 ef_sig)
 as [cd' [c1' [c2' [AFTER1 [AFTER2 MATCH12']]]]]; auto.
rewrite <-meminj_preserves_genv2blocks.
rewrite <-genvs_domain_eq_preserves with (ge1 := ge_S); auto.
rewrite meminj_preserves_genv2blocks; auto.
exists (core_datas_upd (ACTIVE E_S st1) cd' cd).
assert (exists st1', after_external esemS (Some ret1) st1 = Some st1' /\
         PROJ_CORE E_S (ACTIVE E_S st1) st1' = Some c1') as [st1' [? PROJ1']].
 inv core_compatS.
 specialize (after_ext_prog st1 c1 c1' (Some ret1)).
 solve[spec after_ext_prog; auto].
assert (exists st2', after_external esemT (Some ret2) st2 = Some st2' /\
         PROJ_CORE E_T (ACTIVE E_S st1) st2' = Some c2') as [st2' [? PROJ2']].
 inv core_compatT.
 specialize (after_ext_prog st2). 
 rewrite <-ACT in after_ext_prog.
 specialize (after_ext_prog c2 c2' (Some ret2)).
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
inv esig_compilable.
eapply after_external_rel; eauto.
split; auto.

intros i _c _PROJ1'.
case_eq (eq_nat_dec (ACTIVE E_S st1) i).
(*ACTIVE E_S st1 = i*)
forget (ACTIVE E_S st1) as x.
forget (ACTIVE E_T st2) as y.
forget (ACTIVE E_S st1') as x'.
forget (ACTIVE E_T st2') as y'.
do 4 subst.
intros EQ _; subst.
exists c2'; split; auto.
rewrite _PROJ1' in PROJ1'.
inv PROJ1'; auto.
solve[rewrite core_datas_upd_same; auto].

(*ACTIVE E_S st1 <> i*)
intros NEQ _.
specialize (MATCH_CORES' i _c).
spec MATCH_CORES'.
 inv core_compatS.
 solve[erewrite after_ext_others; eauto].
destruct MATCH_CORES' as [_d [_PROJ2 _MATCH12]].
exists _d; split; auto.
 inv core_compatT.
 erewrite <-after_ext_others; eauto.
 solve[rewrite <-ACT; auto].
rewrite core_datas_upd_other; auto.
inv esig_compilable.
eapply after_external_diagram; eauto.
inv core_compatT.
erewrite <-after_ext_others; eauto.
solve[rewrite <-ACT; auto].
Qed.

Lemma RGsimulations_invariant: 
  (forall i:nat, RelyGuaranteeSimulation.Sig (csemS i) (csemT i) 
       (genv_mapS i) (match_state i)) ->
  @CompilabilityInvariant.Sig F_S V_S F_T V_T D_S D_T xS xT 
       fS fT vS vT cS cT dS dT Z Zint Zext 
       esemS esemT csemS csemT csig esig handled threads_max
       ge_S ge_T genv_mapS genv_mapT E_S E_T 
       entry_points core_data match_state core_ord R -> 
  internal_compilability_invariant.
Proof.
intro core_simulations_RGinject.
constructor; try solve[inv H; auto].
  
(*1*)
intros until n; intros PROJC1 PROJC2 PROJD1 PROJD2 ACT MATCH INCR SEP STEP1 STEP2 MATCHC'.
destruct MATCH as [RR [ACTEQ MATCH_INNER]].
forget (Extension.active E_S s1) as k.
destruct (MATCH_INNER k c1 PROJC1) as [_c2 [_PROJC2 MATCHC]].
rewrite _PROJC2 in PROJC2; inv PROJC2.
destruct (MATCH_INNER i d1 PROJD1) as [_d2 [_PROJD2 MATCHD]].
rewrite _PROJD2 in PROJD2; inv PROJD2.
forget (Extension.active E_T s2) as k.
destruct (core_simulations_RGinject k) as [_ ? ? _ GUARANTEE].
specialize (GUARANTEE (genv_mapS k) (genv_mapT k)
  (cd k) m1 m1' j m2 m2' c1 c2 c1' c2' n).
intros HSTEP HMATCH.
spec GUARANTEE; auto.
spec GUARANTEE; auto.
erewrite <-genvs_domain_eq_preserves; eauto.
spec GUARANTEE; auto.
spec GUARANTEE; auto.
spec GUARANTEE; auto.
destruct GUARANTEE as [H1 H2].
destruct (core_simulations_RGinject i) as [_ _ _ RELY _].
specialize (RELY (genv_mapS i) (cd i) m1 m1' j j' m2 m2' d1 d2).
apply RELY; auto.
erewrite <-genvs_domain_eq_preserves; eauto.
solve[eapply match_state_inj; eauto].

(*2*)
intros; destruct (core_simulations_RGinject i) as [? _ _ _ _].
solve[eapply match_state_runnable; eauto].

(*3*)
intros; destruct (core_simulations_RGinject i) as [_ ? _ _ _].
solve[eapply match_state_inj; eauto].

(*4*)
intros; destruct (core_simulations_RGinject i) as [_ _ ? _ _].
solve[eapply match_state_preserves_globals; eauto].

(*2*)
intros until j'; intros MATCH EXT1 PRES INCR SEP INJ INJARGS FORW1 UNCH1 FORW2 UNCH2.
intros TYS AFTER1 AFTER2 PROJ1 PROJ2 NEQ.
forget (Extension.active E_S s1) as k.
destruct (core_simulations_RGinject i) as [? ? ? RELY _].
specialize (RELY (genv_mapS i) cd m1 m1' j j' m2 m2' d1 d2).
apply RELY; auto.
solve[eapply match_state_inj; eauto].
erewrite genvs_domain_eq_preserves.
erewrite meminj_preserves_genv2blocks.
eauto.
solve[apply genvs_domain_eq_sym; auto].
admit. (*Events vs. Events2*)
admit. (*Events vs. Events2*)
Qed.

End ExtendedSimulations. End ExtendedSimulations.

Module ExtensionCompilability. Section ExtensionCompilability. 
 Variables
  (F_S V_S F_T V_T: Type) (** global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F_S V_S) xS mem D_S) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F_T V_T) xT mem D_T) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) (** a set of core semantics *)
  (csig: ext_spec mem Z) (** client signature *)
  (esig: ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: Extension.Sig (fun i => Genv.t (fS i) (vS i)) cS dS Zint esemS csemS
                  csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t (fT i) (vT i)) cT dT Zint esemT csemT
                  csig esig handled).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].
 Variable threads_max: nat.

 Definition core_datas := forall i: nat, core_data i. 

 Variable R: meminj -> xS -> mem -> xT -> mem -> Prop.

 Import Sim_inj_exposed.

 Lemma ExtensionCompilability: 
   EXTENSION_COMPILABILITY.Sig fS fT vS vT threads_max ge_S ge_T genv_mapS genv_mapT 
       E_S E_T entry_points core_data match_state core_ord R.
 Proof.
 eapply @EXTENSION_COMPILABILITY.Make.
 intros H1 H2 H3 H4 H5 H6 core_simulations H8.
 apply CompilableExtension.Make 
  with (core_datas := ExtendedSimulations.core_datas core_data)
       (match_states := 
  ExtendedSimulations.match_states fS fT vS vT E_S E_T match_state R)
       (core_ords := 
  ExtendedSimulations.core_ords threads_max core_data core_ord).
 eapply ExtendedSimulations.extended_simulation; eauto.
 solve[eapply ExtendedSimulations.RGsimulations_invariant; eauto].
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
  (esemS: CoreSemantics (Genv.t F_S V_S) cS mem D_S) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F_T V_T) cT mem D_T) (** extended target semantics *)
  (csemS: CoreSemantics (Genv.t fS vS) cS mem dS)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT)
  (csig: ext_spec mem Z) (** client signature *)
  (esig: ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) (geS: Genv.t fS vS) (geT: Genv.t fT vT).

 Variable (E_S: Extension.Sig (fun i => Genv.t ((const fS) i) ((const vS) i)) 
                  (const cS) (const dS) Zint esemS (fun i:nat => csemS) csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t ((const fT) i) ((const vT) i)) 
                  (const cT) (const dT) Zint esemT (fun i:nat => csemT) csig esig handled).

 Variable entry_points: list (val*val*signature).
 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Variable core_ord: core_data -> core_data -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].
 Variable threads_max: nat.

 Definition core_datas := nat -> core_data.

 Variable R: meminj -> cS -> mem -> cT -> mem -> Prop.

 Import Sim_inj_exposed.

 Lemma ExtensionCompilability: 
   EXTENSION_COMPILABILITY.Sig (const fS) (const fT) (const vS) (const vT)
    threads_max ge_S ge_T (const geS) (const geT) E_S E_T entry_points 
    (const core_data) (const match_state) (const core_ord) R.
 Proof.
 eapply @EXTENSION_COMPILABILITY.Make.
 intros H1 H2 H3 H4 H5 H6 core_simulations H8.
 apply CompilableExtension.Make 
  with (core_datas := ExtendedSimulations.core_datas (fun _ => core_data))
       (match_states := 
  ExtendedSimulations.match_states (const fS) (const fT) (const vS) (const vT) E_S E_T 
                                   (const match_state) R)
       (core_ords := 
  ExtendedSimulations.core_ords threads_max (const core_data) (const core_ord)).
 eapply ExtendedSimulations.extended_simulation; eauto.
 solve[eapply ExtendedSimulations.RGsimulations_invariant; eauto].
Qed.

End ExtensionCompilability2. End ExtensionCompilability2.
