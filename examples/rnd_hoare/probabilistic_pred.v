Require Import Coq.Sets.Ensembles.
Require Import RndHoare.random_oracle.
Require Import RndHoare.imperative.
Import RndHoare.imperative.Randomized.
Require Import RndHoare.measure.
Require Import Classical.

Local Open Scope R.

Definition is_measurable_subspace {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomVarDomain): Prop := measurable_subspace P.

Definition is_measurable_domain {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomVarDomain | is_measurable_subspace P) (Q: RandomVarDomain): Prop :=
  Included _ Q (proj1_sig P) /\ measurable _ (sub_measure (exist _ (proj1_sig P: Ensemble _) (proj2_sig P))) (sig_Set Q (proj1_sig P)).

Definition measure_of {ora: RandomOracle} {PRPS: PartialRegularProbabilitySpace RandomHistory} (P: RandomVarDomain | is_measurable_subspace P) (Q: RandomVarDomain | is_measurable_domain P Q): R :=
  measure_function _
   (sub_measure (exist _ (proj1_sig P: Ensemble _) (proj2_sig P)))
   (exist _ (sig_Set (proj1_sig Q) (proj1_sig P)) (proj2 (proj2_sig Q))).

Class RandomHistoryDistribution (ora: RandomOracle): Type := {
  RHD_PRPS :> PartialRegularProbabilitySpace RandomHistory;
  RHD_MSS_consi: forall P Q, same_covered_domain P Q ->
                   (is_measurable_subspace P <-> is_measurable_subspace Q);
  RHD_MD_consi: forall P Q MP MQ S R, same_covered_domain P Q -> same_covered_domain S R ->
                   Included _ S P ->
                   Included _ R Q ->
                   (is_measurable_domain (exist _ P MP) S <-> 
                    is_measurable_domain (exist _ Q MQ) R);
  RHD_M_consi: forall P Q MP MQ S R MS MR, same_covered_domain P Q -> same_covered_domain S R ->
                   measure_of (exist _ P MP) (exist _ S MS) =
                   measure_of (exist _ Q MQ) (exist _ R MR)
}.

Definition is_measurable {ora: RandomOracle} {psi: RandomDistribution ora} (P: Ensemble RandomHistory): Prop := measurable _ raw_ms P.

(***************************)
(* overload measurable_set *)
(***************************)

Definition measurable_set {ora: RandomOracle} (psi: RandomDistribution ora): Type := measurable_set raw_ms.
  
Definition ms_construct {ora: RandomOracle} (psi: RandomDistribution ora) (P: Ensemble RandomHistory) (Pr: is_measurable P):measurable_set psi := exist _ P Pr.

Definition GProb {ora: RandomOracle} {psi: RandomDistribution ora} (P: measurable_set psi): R :=
  measure_function _ raw_ms P.

Definition tm_meta_pred {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: state -> Prop): MetaState state -> Prop :=
  fun s => match s with Terminating s' => P s' | _ => False end.

Module PreSubsets.

Definition valid_set {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora}  (P: MetaState state -> Prop) (sigma: global_state): Ensemble RandomHistory :=
  fun h => match sigma h with Some s => P s | _ => False end.

Definition ntm_set {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (sigma: global_state): Ensemble RandomHistory :=
  valid_set (eq (NonTerminating _)) sigma.

Definition tm_set {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: state -> Prop) (sigma: global_state): Ensemble RandomHistory :=
  valid_set (tm_meta_pred P) sigma.

Lemma tm_set_measurable: forall {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: state -> Prop) (sigma: global_state),
  is_measurable (tm_set P sigma).
(* This is true given that there are only finite oracle questions and any oracle questions has finite answers. *)
Admitted.

Lemma valid_set_measurable: forall {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: MetaState state -> Prop) (sigma: global_state),
  is_measurable (valid_set (fun _ => True) sigma) ->
  is_measurable (valid_set P sigma).
Proof.
  intros.
  destruct (classic (P (NonTerminating _))).
Admitted.

End PreSubsets.

(***************************)
(* overload global state   *)
(***************************)

Definition global_state {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora}: Type := {sigma: global_state | is_measurable (PreSubsets.valid_set (fun _ => True) sigma)}.

Definition is_substate {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: MetaState state -> Prop) (sigma sigma': global_state): Prop :=
  forall h,
    match proj1_sig sigma h with
    | Some s => (P s /\ proj1_sig sigma' h = Some s) \/ (~ P s /\ proj1_sig sigma' h = None)
    | None => proj1_sig sigma' h = None
    end.

Definition valid_set {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora}  (P: MetaState state -> Prop) (sigma: global_state): measurable_set psi :=
  ms_construct psi
   (PreSubsets.valid_set P (proj1_sig sigma)) 
   (PreSubsets.valid_set_measurable _ _ (proj2_sig sigma)).

Definition ntm_set {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (sigma: global_state): measurable_set psi :=
  valid_set (eq (NonTerminating _)) sigma.

Definition tm_set {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (P: state -> Prop) (sigma: global_state): measurable_set psi :=
  valid_set (tm_meta_pred P) sigma.

Definition vPr {imp: Imperative} {sss: SmallStepSemantics} {psi: RandomDistribution ora} (sigma: global_state): R := GProb (ms_construct _ _ (proj2_sig sigma)).

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
