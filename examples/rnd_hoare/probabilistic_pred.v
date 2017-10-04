Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.
Require Import RndHoare.sigma_algebra.
Require Import RndHoare.measurable_function.
Require Import RndHoare.regular_conditional_prob.
Require Import RndHoare.random_oracle.
Require Import RndHoare.random_variable.

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

Global Existing Instances nil_SigmaAlgebras cons_SigmaAlgebras.

Definition head_SigmaAlgebra (A: Type) (As0: list Type) {sAs: SigmaAlgebras (cons A As0)}: SigmaAlgebra A := fst sigma_algebras.

Definition tail_SigmaAlgebra (A: Type) (As0: list Type) {sAs: SigmaAlgebras (cons A As0)}: SigmaAlgebras As0 := snd sigma_algebras.

Definition _RandomPred (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, Type :=
  fix RandomPred (As: list Type): SigmaAlgebras As -> Type :=
    match As as As_PAT return SigmaAlgebras As_PAT -> Type with
    | nil => fun _ => Prop
    | cons A As0 => fun sAs => @RandomVariable _ _ _ Omega A (head_SigmaAlgebra A As0) -> RandomPred As0 (tail_SigmaAlgebra A As0)
    end.

Definition _RandomPred_consi (Omega1 Omega2: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, _RandomPred Omega1 As -> _RandomPred Omega2 As -> Prop :=
  fix RandomPred_consi (As: list Type): forall (sAs: SigmaAlgebras As), @_RandomPred Omega1 As sAs -> @_RandomPred Omega2 As sAs -> Prop :=
    match As as As_PAT return forall (sAs_PAT: SigmaAlgebras As_PAT), @_RandomPred Omega1 As_PAT sAs_PAT -> @_RandomPred Omega2 As_PAT sAs_PAT -> Prop
    with
    | nil => fun _ P1 P2 => P1 <-> P2
    | cons A As0 => fun sAs P1 P2 => forall a1 a2, (forall h, Omega1 h -> Omega2 h -> RandomVar_local_equiv a1 a2 h h) -> RandomPred_consi As0 (tail_SigmaAlgebra A As0) (P1 a1) (P2 a2)
    end.

Definition RandomPred (As: list Type) {sAs: SigmaAlgebras As}: Type := {P: forall (Omega: RandomVarDomain), _RandomPred Omega As | forall O1 O2, undistinguishable_sub_domain O1 O2 -> _RandomPred_consi O1 O2 As (P O1) (P O2)}.

Definition RandomPred_Func {As: list Type} {sAs: SigmaAlgebras As}: RandomPred As -> forall (Omega: RandomVarDomain), _RandomPred Omega As := @proj1_sig _ _.

Global Coercion RandomPred_Func: RandomPred >-> Funclass.

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

Definition _appp (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As} (B: Type) {sB: SigmaAlgebra B}, HeredRandomVariable B -> (RandomVariable Omega B -> _RandomPred Omega As) -> _RandomPred Omega As :=
  fix appp (As: list Type): forall (sAs: SigmaAlgebras As) (B: Type) (sB: SigmaAlgebra B), HeredRandomVariable B -> (RandomVariable Omega B -> _RandomPred Omega As) -> _RandomPred Omega As :=
  match As as As_PAT return (forall (sAs: SigmaAlgebras As_PAT) (B: Type) (sB: SigmaAlgebra B), HeredRandomVariable B -> (RandomVariable Omega B -> _RandomPred Omega As_PAT) -> _RandomPred Omega As_PAT) with
  | nil => fun sAs B sB b (P: RandomVariable Omega B -> Prop) =>
              exists (H: well_defined_dom _ b Omega), P (ex_value _ b Omega H)
  | cons A As0 => fun sAs B sB b P => fun rho => appp As0 (tail_SigmaAlgebra A As0) B sB b (fun b => P b rho)
  end.

Definition _derives (Omega: RandomVarDomain): forall (As: list Type) {sAs: SigmaAlgebras As}, _RandomPred Omega As -> _RandomPred Omega As -> Prop :=
  fix derives (As: list Type): forall sAs: SigmaAlgebras As, _RandomPred Omega As -> _RandomPred Omega As -> Prop :=
  match As as As_PAT return (forall sAs: SigmaAlgebras As_PAT, _RandomPred Omega As_PAT -> _RandomPred Omega As_PAT -> Prop) with
  | nil => fun sAs P Q => P -> Q
  | cons A As0 => fun sAs P Q => forall rho, derives As0 (tail_SigmaAlgebra A As0) (P rho) (Q rho)
  end.

Definition prop {As: list Type} {sAs: SigmaAlgebras As} (P: Prop): RandomPred As.
  exists (fun Omega: RandomVarDomain => _prop Omega As P).
  intros.
  induction As.
  + simpl.
    tauto.
  + simpl.
    intros; apply IHAs.
Defined.

Definition andp {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): RandomPred As.
  exists (fun Omega: RandomVarDomain => _andp Omega As (P Omega) (Q Omega)).
  destruct P as [P ?H], Q as [Q ?H].
  intros; simpl in *.
  specialize (H O1 O2 H1); specialize (H0 O1 O2 H1).
  set (P1 := P O1) in *; set (P2 := P O2) in *; set (Q1 := Q O1) in *; set (Q2 := Q O2) in *.
  clearbody P1 P2 Q1 Q2.
  clear P Q.
  induction As.
  + simpl in *.
    tauto.
  + simpl.
    intros.
    apply IHAs; auto.
Defined.

Definition orp {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): RandomPred As.
  exists (fun Omega: RandomVarDomain => _orp Omega As (P Omega) (Q Omega)).
  destruct P as [P ?H], Q as [Q ?H].
  intros; simpl in *.
  specialize (H O1 O2 H1); specialize (H0 O1 O2 H1).
  set (P1 := P O1) in *; set (P2 := P O2) in *; set (Q1 := Q O1) in *; set (Q2 := Q O2) in *.
  clearbody P1 P2 Q1 Q2.
  clear P Q.
  induction As.
  + simpl in *.
    tauto.
  + simpl.
    intros.
    apply IHAs; auto.
Defined.

Definition imp {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): RandomPred As.
  exists (fun Omega: RandomVarDomain => _imp Omega As (P Omega) (Q Omega)).
  destruct P as [P ?H], Q as [Q ?H].
  intros; simpl in *.
  specialize (H O1 O2 H1); specialize (H0 O1 O2 H1).
  set (P1 := P O1) in *; set (P2 := P O2) in *; set (Q1 := Q O1) in *; set (Q2 := Q O2) in *.
  clearbody P1 P2 Q1 Q2.
  clear P Q.
  induction As.
  + simpl in *.
    tauto.
  + simpl.
    intros.
    apply IHAs; auto.
Defined.

(*
Definition exp {As: list Type} {sAs: SigmaAlgebras As} {B: Type} (P: B -> RandomPred As): RandomPred As.
  exists (fun Omega: RandomVarDomain => _exp Omega As (fun b => P b Omega)).
  intros; simpl in *.
  specialize (H O1 O2 H1).
  set (P1 := P O1) in *; set (P2 := P O2) in *; set (Q1 := Q O1) in *; set (Q2 := Q O2) in *.
  clearbody P1 P2 Q1 Q2.
  clear P Q.
  induction As.
  + simpl in *.
    tauto.
  + simpl.
    intros.
    apply IHAs; auto.
Defined.

Definition expR {As: list Type} {sAs: SigmaAlgebras As} {B: Type} {sB: SigmaAlgebra B} (P: RandomPred (B :: As)): RandomPred As := fun Omega: RandomVarDomain => _expR Omega As B (fun b => P Omega b).

Definition appp {As: list Type} {sAs: SigmaAlgebras As} {B: Type} {sB: SigmaAlgebra B} (P: RandomPred (B :: As)) (b: HeredRandomVariable B): RandomPred As := fun Omega: RandomVarDomain => _appp Omega As B b (P Omega).
*)

Definition derives {As: list Type} {sAs: SigmaAlgebras As} (P Q: RandomPred As): Prop := forall Omega: RandomVarDomain, _derives Omega As (P Omega) (Q Omega).

End Predicates.

(*

(*

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
*)