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

Lemma state_pred_domain_measurable: forall (P: MetaState state -> Prop) (sigma: global_state)
  (H: is_measurable_subspace (rv_domain _ sigma)),
  is_measurable_set (exist _ _ H) (element_pred_domain P sigma).
Admitted.

(***************************)
(* overload global state   *)
(***************************)

Definition global_state: Type := {sigma: global_state | is_measurable_subspace (rv_domain _ sigma)}.

Definition global_state_MSS (sigma: global_state): {P: RandomHistory -> Prop | is_measurable_subspace P} :=
  exist is_measurable_subspace (rv_domain _ (proj1_sig sigma)) (proj2_sig sigma).

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
Definition Pr (P: state -> Prop) (sigma: global_state): R := measure_of _ (tm_pred_MS P sigma).

Definition nPr (sigma: global_state): R := measure_of _ (ntm_pred_MS sigma).

Definition RCPPred (P: global_state -> Prop) (filter: RandomHistory -> Prop) (sigma: global_state): Prop :=
  ~ is_measurable_subspace (tm_domain filter (proj1_sig sigma)) /\
  exists M: is_measurable_subspace (tm_domain filter (proj1_sig sigma)),
  P (exist _ (element_pred_filter_global_state (tm_meta_pred filter) (proj1_sig sigma)) M).

Definition ExPred {A: Type} (P: A -> global_state -> Prop) (sigma: global_state): Prop := exists a: A, P a sigma.

Definition QRandVar (A: Type): forall d: RandomVarDomain, {v: RandomVariable A | rv_domain _ v = d}.

Definition ExrPred {A: Type} (P: QRandVar A -> global_state -> Prop) (sigma: global_state): Prop := exists a: A, P a sigma.


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
