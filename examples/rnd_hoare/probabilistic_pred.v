Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.
Require Import RndHoare.random_oracle.
Require Import RndHoare.imperative.
Import RndHoare.imperative.Randomized.
Require Import RndHoare.full_domain.
Require Import RndHoare.measure.

Local Open Scope R.
(*
Definition is_measurable_subspace {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomVarDomain): Prop := measurable_subspace P.
*)

Definition is_measurable_set {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomHistory -> Prop | is_measurable_subspace P) (Q: RandomHistory -> Prop): Prop :=
  Included _ Q (proj1_sig P) /\ is_measurable_set _ (sub_measure P) (sig_Set Q (proj1_sig P)).

Definition measurable_set {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomHistory -> Prop | is_measurable_subspace P): Type :=
  {Q: RandomHistory -> Prop | is_measurable_set P Q}.

Definition measure_of {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomHistory -> Prop | is_measurable_subspace P) (Q: measurable_set P): R :=
  measure_function _
   (sub_measure P)
   (exist _ (sig_Set (proj1_sig Q) (proj1_sig P)) (proj2 (proj2_sig Q))).

Class RandomHistoryDistribution (ora: RandomOracle): Type := {
  RHD_PRPS :> PartialRegularProbabilitySpace RandomHistory;
  RHD_MSS_legal: forall P, is_measurable_subspace P -> LegalRandomVarDomain P;
  RHD_MSS_consi: forall P Q, same_covered_domain P Q ->
                   (is_measurable_subspace P <-> is_measurable_subspace Q);
  RHD_MD_consi: forall (P Q: RandomVarDomain) (MP: is_measurable_subspace P) (MQ: is_measurable_subspace Q) S R, same_covered_domain P Q -> same_covered_domain S R ->
                   Included _ S P ->
                   Included _ R Q ->
                   (is_measurable_set (exist is_measurable_subspace P MP) S <-> 
                    is_measurable_set (exist is_measurable_subspace Q MQ) R);
  RHD_M_consi: forall (P Q: RandomVarDomain) (MP: is_measurable_subspace P) (MQ: is_measurable_subspace Q) S R MS MR, same_covered_domain P Q -> same_covered_domain S R ->
                   measure_of (exist is_measurable_subspace P MP) (exist (is_measurable_set (exist is_measurable_subspace P MP)) S MS) =
                   measure_of (exist is_measurable_subspace Q MQ) (exist (is_measurable_set (exist is_measurable_subspace Q MQ)) R MR);
  RHD_full_measurable: forall P, is_full_domain P -> is_measurable_subspace P
}.

Class DiscreteRandomHistoryDistribution (ora: RandomOracle) {RHD: RandomHistoryDistribution ora}: Type := {
  singleton_history_measurable: forall (h: RandomHistory), is_measurable_subspace (singleton_history_domain h)
}.

Module Predicates.

Section Predicates.

Context {imp: Imperative} {sss: SmallStepSemantics} {rhd: RandomHistoryDistribution ora} {drhd: DiscreteRandomHistoryDistribution ora}.

(***************************)
(* overload global state   *)
(***************************)

Record global_state: Type := {
  raw_gstate: Randomized.global_state;
  gs_MSS: is_measurable_subspace (rv_domain _ raw_gstate);
  gs_MF: forall (P: MetaState state -> Prop), is_measurable_set (exist is_measurable_subspace _ gs_MSS) (preimage_domain P raw_gstate)
  (* Discrete/Continuous: P should be any measurable subset of MetaState when continuous. *)
}.

Definition global_state_MSS (sigma: global_state): {P: RandomHistory -> Prop | is_measurable_subspace P} :=
  exist is_measurable_subspace _ (gs_MSS sigma).

Record HereditaryRandVariable (A: Type): Type := {
  well_defined_dom: RandomVarDomain -> Prop;
  well_defined_mono: forall d1 d2, future_domain d1 d2 -> well_defined_dom d1 -> well_defined_dom d2;
  well_defined_MSS: forall d, well_defined_dom d -> is_measurable_subspace d;
  ex_value: forall d: RandomVarDomain, well_defined_dom d -> RandomVariable A;
  ex_value_consi: forall d (H: well_defined_dom d), rv_domain _ (ex_value d H) = d;
  ex_value_hered: forall d1 d2 (H1: well_defined_dom d1) (H2: well_defined_dom d2) (h1: d1) (h2: d2),
    future_domain d1 d2 ->
    prefix_history h1 h2 ->
    RandomVar_local_equiv (ex_value d1 H1) (ex_value d2 H2) h1 h2;
  ex_value_MF: forall d (H: well_defined_dom d) (P: A -> Prop),
    is_measurable_set (exist is_measurable_subspace d (well_defined_MSS d H)) (preimage_domain P (ex_value d H))
}.


(*
Definition state_pred_domain_MS (P: MetaState state -> Prop) (sigma: global_state): measurable_set (global_state_MSS sigma).
  exists (element_pred_domain P (proj1_sig sigma)).
  split.
  + exact (element_pred_domain_Dom _ _).
  + apply (state_pred_domain_measurable P (proj1_sig sigma)).
Defined.

(*
Definition ntm_pred_MS (sigma: global_state): measurable_set (global_state_MSS sigma) :=
  state_pred_domain_MS (eq (NonTerminating _)) sigma.

Definition tm_pred_MS (P: state -> Prop) (sigma: global_state): measurable_set (global_state_MSS sigma) :=
  state_pred_domain_MS (tm_meta_pred P) sigma.
*)

*)

Definition Prob (P: RandomHistory -> Prop) (sigma: global_state): R := measure_of _ (tm_pred_MS P sigma).

Definition RCPPred (P: global_state -> Prop) (filter: RandomHistory -> Prop) (sigma: global_state): Prop :=
  ~ is_measurable_subspace (filter_domain filter (rv_domain _ (proj1_sig sigma))) /\
  exists M: is_measurable_subspace (filter_domain filter (rv_domain _ (proj1_sig sigma))),
  P (exist _ (filter_global_state filter (proj1_sig sigma)) M).

Definition ExPred {A: Type} (P: A -> global_state -> Prop) (sigma: global_state): Prop := exists a: A, P a sigma.

Definition ExrPred {A: Type} (P: RandomVariable A -> global_state -> Prop) (sigma: global_state): Prop := exists a: QRandVar A, exists H: well_defined_dom _ a (rv_domain _ (proj1_sig sigma)), P (proj1_sig (ex_value _ a _ H)) sigma.

Definition PTriple (P: global_state -> Prop) (c: cmd) (Q: global_state -> Prop): Prop :=
  forall (s1: global_state),
    P s1 ->
    nPr s1 = 0 ->
    forall (s2: global_state),
      command_oaccess c (proj1_sig s1) (proj1_sig s2) ->
      same_covered_domain (rv_domain _ (proj1_sig s1)) (rv_domain _ (proj1_sig s2)) /\
      (nPr s2 = 0 -> Q s2).

Definition TTriple (P: global_state -> Prop) (c: cmd) (Q: global_state -> Prop): Prop :=
  forall (s1: global_state),
    P s1 ->
    nPr s1 = 0 ->
    forall (s2: global_state),
      command_oaccess c (proj1_sig s1) (proj1_sig s2) ->
      same_covered_domain (rv_domain _ (proj1_sig s1)) (rv_domain _ (proj1_sig s2)) /\
      nPr s2 = 0 /\
      Q s2.

Require Import Morphisms.
