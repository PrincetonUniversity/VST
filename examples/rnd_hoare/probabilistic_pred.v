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

Definition tm_meta_pred (P: state -> Prop): MetaState state -> Prop :=
  fun s => match s with Terminating s' => P s' | _ => False end.

Definition valid_set (P: MetaState state -> Prop) (sigma: global_state): Ensemble RandomHistory :=
  fun h => match sigma h with Some s => P s | _ => False end.

Definition ntm_set (sigma: global_state): Ensemble RandomHistory :=
  valid_set (eq (NonTerminating _)) sigma.

Definition tm_set (P: state -> Prop) (sigma: global_state): Ensemble RandomHistory :=
  valid_set (tm_meta_pred P) sigma.

Lemma valid_set_measurable: forall (P: MetaState state -> Prop) (sigma: global_state),
  is_measurable_subspace (DomainOfVar sigma) ->
  is_measurable_subspace (valid_set P sigma).
sss 
(* Not correct. P should be inhabited. *)
Admitted.

Lemma valid_set_Dom: forall (P: MetaState state -> Prop) (sigma: global_state),
  Included _ (valid_set P sigma) (DomainOfVar sigma).
Proof.
  unfold Included, Ensembles.In; intros.
  unfold valid_set in H.
  change ((DomainOfVar sigma) x) with (isSome (sigma x)).
  destruct (sigma x); simpl; auto.
Qed.

(***************************)
(* overload global state   *)
(***************************)

Definition global_state: Type := {sigma: global_state | is_measurable_subspace (DomainOfVar sigma)}.

Definition global_state_MSS (sigma: global_state): {P: RandomHistory -> Prop | is_measurable_subspace P} :=
  exist is_measurable_subspace (DomainOfVar (proj1_sig sigma)) (proj2_sig sigma).

Definition valid_set_MSS (P: MetaState state -> Prop) (sigma: global_state): {P: RandomHistory -> Prop | is_measurable_subspace P}.
  exists (valid_set P (proj1_sig sigma)).
  apply valid_set_measurable, (proj2_sig sigma).
Defined.

Definition valid_set_MS (P: MetaState state -> Prop) (sigma: global_state): measurable_set (global_state_MSS sigma).
  exists (valid_set P (proj1_sig sigma)).
  split.
  + apply valid_set_Dom.
  + apply (measurable_subset_measurable (global_state_MSS sigma) (valid_set_MSS P sigma)).
    apply valid_set_Dom.
Defined.

Definition ntm_set_MS (sigma: global_state): measurable_set (global_state_MSS sigma) :=
  valid_set_MS (eq (NonTerminating _)) sigma.

Definition tm_set_MS (P: state -> Prop) (sigma: global_state): measurable_set (global_state_MSS sigma) :=
  valid_set_MS (tm_meta_pred P) sigma.

Definition Pr (P: state -> Prop) (sigma: global_state): R := GProb (ms_construct _ _ (proj2_sig sigma)).

Definition nPr {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (sigma: global_state): R := GProb (ntm_set sigma).

Definition PTriple {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: global_state -> Prop) (c: cmd) (Q: global_state -> Prop): Prop :=
  forall p (s1: global_state),
    P s1 ->
    p > 0 ->
    vPr s1 = p ->
    nPr s1 = 0 ->
    forall (s2: global_state),
      command_oaccess c (proj1_sig s1) (proj1_sig s2) ->
      vPr s2 = p /\
      (nPr s2 = 0 -> Q s2).

Definition TTriple {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: global_state -> Prop) (c: cmd) (Q: global_state -> Prop): Prop :=
  forall p (s1: global_state),
    P s1 ->
    p > 0 ->
    vPr s1 = p ->
    nPr s1 = 0 ->
    forall (s2: global_state),
      command_oaccess c (proj1_sig s1) (proj1_sig s2) ->
      vPr s2 = p /\
      nPr s2 = 0 /\
      Q s2.

Definition Pr {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: state -> Prop): global_state -> R :=
  fun sigma => GProb (tm_set P sigma) / vPr sigma.

Definition ConditionalPred {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: global_state -> Prop) (condition: state -> Prop): global_state -> Prop :=
  fun sigma => GProb (tm_set condition sigma) = 0 \/ exists sigma', is_substate (tm_meta_pred condition) sigma sigma' /\ P sigma'.


Definition ProbEquiv {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (sigma1 sigma2: global_state): Prop :=
  forall P: MetaState state -> Prop,
    GProb (valid_set P sigma1) = GProb (valid_set P sigma2).

Require Import Morphisms.
