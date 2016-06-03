Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_variable.
Require Import RndHoare.meta_state.

Section Predicates.

Context {ora: RandomOracle} {SFo: SigmaAlgebraFamily RandomHistory} {HBSFo: HistoryBasedSigF ora}.

Fixpoint _SigmaAlgebras (As: list Type): Type :=
  match As with 
  | nil => unit
  | cons A As0 => (SigmaAlgebra A * _SigmaAlgebras As0)%type
  end.

Class SigmaAlgebras (As: list Type): Type := sigma_algebras: _SigmaAlgebras As.

Instance nil_SigmaAlgebras: SigmaAlgebras nil := tt.
  
Instance cons_SigmaAlgebras (A: Type) (As0: list Type) {sA: SigmaAlgebra A} {sAs: SigmaAlgebras As0}: SigmaAlgebras (cons A As0) := (sA, @sigma_algebras _ sAs).

Definition head_SigmaAlgebra (A: Type) (As0: list Type) {sAs: SigmaAlgebras (cons A As0)}: SigmaAlgebra A := fst sigma_algebras.

Definition tail_SigmaAlgebra (A: Type) (As0: list Type) {sAs: SigmaAlgebras (cons A As0)}: SigmaAlgebras As0 := snd sigma_algebras.

Definition _RandomPred (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, Type :=
  fix RandomPred (As: list Type): SigmaAlgebras As -> Type :=
    match As as As_PAT return SigmaAlgebras As_PAT -> Type with
    | nil => fun _ => Prop
    | cons A As0 => fun sAs => @RandomVariable _ _ Omega A (head_SigmaAlgebra A As0) -> RandomPred As0 (tail_SigmaAlgebra A As0)
    end.

Definition RandomPred (As: list Type) {sAs: SigmaAlgebras As}: Type := forall (Omega: RandomVarDomain), _RandomPred Omega As.

Definition _prop (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As} (P: Prop), _RandomPred Omega As :=
  fix prop (As: list Type): forall (sAs: SigmaAlgebras As) (P: Prop), _RandomPred Omega As :=
  match As as As_PAT return (forall (sAs: SigmaAlgebras As_PAT) (P: Prop), _RandomPred Omega As_PAT) with
  | nil => fun sAs P => P
  | cons A As0 => fun sAs P => fun _ => prop As0 (tail_SigmaAlgebra A As0) P
  end.

Definition _andp (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, _RandomPred Omega As -> _RandomPred Omega As -> _RandomPred Omega As :=
  fix andp (As: list Type): forall sAs: SigmaAlgebras As, _RandomPred Omega As -> _RandomPred Omega As -> _RandomPred Omega As :=
  match As as As_PAT return (forall sAs: SigmaAlgebras As_PAT, _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT) with
  | nil => fun sAs P Q => P /\ Q
  | cons A As0 => fun sAs P Q => fun rho => andp As0 (tail_SigmaAlgebra A As0) (P rho) (Q rho)
  end.

Definition _orp (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, _RandomPred Omega As -> _RandomPred Omega As -> _RandomPred Omega As :=
  fix orp (As: list Type): forall sAs: SigmaAlgebras As, _RandomPred Omega As -> _RandomPred Omega As -> _RandomPred Omega As :=
  match As as As_PAT return (forall sAs: SigmaAlgebras As_PAT, _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT) with
  | nil => fun sAs P Q => P \/ Q
  | cons A As0 => fun sAs P Q => fun rho => orp As0 (tail_SigmaAlgebra A As0) (P rho) (Q rho)
  end.

Definition _imp (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, _RandomPred Omega As -> _RandomPred Omega As -> _RandomPred Omega As :=
  fix imp (As: list Type): forall sAs: SigmaAlgebras As, _RandomPred Omega As -> _RandomPred Omega As -> _RandomPred Omega As :=
  match As as As_PAT return (forall sAs: SigmaAlgebras As_PAT, _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT) with
  | nil => fun sAs P Q => P \/ Q
  | cons A As0 => fun sAs P Q => fun rho => imp As0 (tail_SigmaAlgebra A As0) (P rho) (Q rho)
  end.

Definition _exp (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As} {B: Type}, (B -> _RandomPred Omega As) -> _RandomPred Omega As :=
  fix exp (As: list Type): forall (sAs: SigmaAlgebras As) (B: Type), (B -> _RandomPred Omega As) -> _RandomPred Omega As :=
  match As as As_PAT return (forall (sAs: SigmaAlgebras As_PAT) (B: Type), (B -> _RandomPred Omega As_PAT) -> _RandomPred Omega As_PAT) with
  | nil => fun sAs B (P: B -> Prop) => ex P
  | cons A As0 => fun sAs B P => fun rho => exp As0 (tail_SigmaAlgebra A As0) B (fun b => P b rho)
  end.

Definition _expR (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As} (B: Type) {sB: SigmaAlgebra B}, (RandomVariable Omega B -> _RandomPred Omega As) -> _RandomPred Omega As :=
  fix expR (As: list Type): forall (sAs: SigmaAlgebras As) (B: Type) (sB: SigmaAlgebra B), (RandomVariable Omega B -> _RandomPred Omega As) -> _RandomPred Omega As :=
  match As as As_PAT return (forall (sAs: SigmaAlgebras As_PAT) (B: Type) (sB: SigmaAlgebra B), (RandomVariable Omega B -> _RandomPred Omega As_PAT) -> _RandomPred Omega As_PAT) with
  | nil => fun sAs B sB (P: RandomVariable Omega B -> Prop) =>
              exists (b: HeredRandomVariable B) (H: well_defined_dom _ b Omega), P (ex_value _ b Omega H)
  | cons A As0 => fun sAs B sB P => fun rho => expR As0 (tail_SigmaAlgebra A As0) B sB (fun b => P b rho)
  end.

Definition prop {As: list Type} {sAs: SigmaAlgebras As} (P: Prop): RandomPred As := fun Omega: RandomVarDomain => _prop Omega As P.

Definition andp {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): RandomPred As := fun Omega: RandomVarDomain => _andp Omega As (P Omega) (Q Omega).

Definition orp {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): RandomPred As := fun Omega: RandomVarDomain => _orp Omega As (P Omega) (Q Omega).

Definition imp {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): RandomPred As := fun Omega: RandomVarDomain => _imp Omega As (P Omega) (Q Omega).

Definition exp {As: list Type} {sAs: SigmaAlgebras As} {B: Type} (P: B -> RandomPred As): RandomPred As := fun Omega: RandomVarDomain => _exp Omega As (fun b => P b Omega).

Definition expR {As: list Type} {sAs: SigmaAlgebras As} {B: Type} {sB: SigmaAlgebra B} (P: RandomPred (B :: As)): RandomPred As := fun Omega: RandomVarDomain => _expR Omega As B (fun b => P Omega b).

End Predicates.

(*

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
*)