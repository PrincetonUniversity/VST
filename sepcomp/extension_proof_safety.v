Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations. 
Require Import sepcomp.rg_forward_simulations. 
Require Import sepcomp.step_lemmas. 
Require Import sepcomp.extspec. 
Require Import sepcomp.extension.
Require Import sepcomp.extension_simulations. (*for genvs_domain_eq*)
Require Import sepcomp.extension_safety.
Require Import sepcomp.Coqlib2.

Require Import AST.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Memory.
Require Import Coqlib.

Set Implicit Arguments.

(* TEMPORARY HACK:
  use this "remember" tactic instead of the standard library one *)
Tactic Notation "remember" constr(a) "as" ident(x) :=
   let x := fresh x in
  let H := fresh "Heq" x in
  (set (x:=a) in *; assert (H: x=a) by reflexivity; clearbody x).

Lemma genvs_domain_eq_refl: forall F V (ge: Genv.t F V), genvs_domain_eq ge ge.
Proof. solve[intros F V ge; unfold genvs_domain_eq; split; intro b; split; auto]. Qed.

Section SafetyMonotonicity. 
 Variables 
  (G cT M D Z Zext: Type) (CS: CoreSemantics G cT M D)
  (csig: ef_ext_spec M Z) (handled: AST.external_function -> Prop).

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
destruct H1 as [H1 H1'].
exists x; split; auto.
intros ret m' z' H3. 
destruct (H2 ret m' z').
right; auto.
destruct H as [H4 H5].
exists x0; split; auto.
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
intros; right; do 2 eexists; eauto.
destruct (safely_halted csem c).
intros; left; eexists; eauto.
congruence.
Qed.

Module ExtensionSafety. Section ExtensionSafety. Variables
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M D) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (dT i)) (** a set of core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

Import SafetyInvariant.

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
Notation zint_invar_after_external := E.(Extension.zint_invar_after_external).

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
generalize (Extension.linkable); intros Hlink.
specialize (Hlink _ _ _ _ _ _ _ _ _ _ _ _ _ _ E). 
destruct Hlink as [Hlink Hlink0].
specialize (Hlink ef 
  (ext_spec_pre esig ef) (ext_spec_post esig ef) 
  (ext_spec_pre csig ef) (ext_spec_post csig ef)).
destruct Hlink with (x' := x) 
 (tys := sig_args sig) (args := args) (m := m) (z := (s \o z)) 
 as [x' [H17 H18]]; auto.
unfold Extension.handled.
intros CONTRA.
specialize (CONTRA s c sig args H4 H5).
solve[rewrite CONTRA in AT_EXT; congruence].
exists x'.
split; auto.
rewrite Extension.zmult_proj in H17; auto.
split; auto.
unfold Extension.handled.
intros CONTRA.
specialize (CONTRA s c sig args H4 H5).
solve[rewrite CONTRA in AT_EXT; congruence].
intros ret m' z' POST.
destruct (H8 ret m' (s \o z')) as [c' [H10 H11]].
specialize (H18 (sig_res sig) ret m' (s \o z')).
rewrite Extension.zmult_proj in H18.
destruct POST.
unfold Extension.handled in H0.
rename H0 into CONTRA.
specialize (CONTRA s c sig args H4 H5).
solve[rewrite CONTRA in AT_EXT; congruence].
rename H0 into POST.
eapply H18 in POST; eauto.
specialize (at_extern_ret z s c m z' m' (sig_args sig) args (sig_res sig) ret c' 
 ef sig x' (ext_spec_pre esig ef) (ext_spec_post esig ef)).
destruct POST as [H0|POST].
rename H0 into CONTRA.
specialize (CONTRA s c sig args H4 H5).
solve[rewrite CONTRA in AT_EXT; congruence].
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
eapply zint_invar_after_external in H13; eauto.
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
intros.
admit. (*NOT NEEDED FOR PAPER 1: safely_halted, need to update invariant*)
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
rewrite H4. 
rewrite SAFELY_HALTED.
rewrite H4 in H1.
rewrite SAFELY_HALTED in H1.
admit. (*NOT NEEDED FOR PAPER 1: safely_halted, need to update invariant*) 
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
 intros s'' c'' sig' args' H3 H4.
solve[eapply (Extension.handled_invar E) with (s := s) (c := c); eauto].
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
admit. (*NOT NEEDED FOR PAPER 1: safely_halted, need to update invariant*) 
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
