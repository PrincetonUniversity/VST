Require Import VST.msl.Extensionality.

Class NatDed (A: Type) := mkNatDed {
  andp: A -> A -> A;
  orp: A -> A -> A;
  exp: forall {T:Type}, (T -> A) -> A;
  allp: forall {T:Type}, (T -> A) -> A;
  imp: A -> A -> A;
  prop: Prop -> A;
  derives: A -> A -> Prop;
  pred_ext: forall P Q, derives P Q -> derives Q P -> P=Q;
  derives_refl: forall P, derives P P;
  derives_trans: forall P Q R, derives P Q -> derives Q R -> derives P R;
  TT := prop True;
  FF := prop False;
  andp_right:  forall X P Q:A, derives X P -> derives X Q -> derives X (andp P Q);
  andp_left1:  forall P Q R:A, derives P R -> derives (andp P Q) R;
  andp_left2:  forall P Q R:A, derives Q R -> derives (andp P Q) R;
  orp_left: forall P Q R, derives P R -> derives Q R -> derives (orp P Q) R;
  orp_right1: forall P Q R, derives P Q -> derives P (orp Q R);
  orp_right2: forall P Q R, derives P R -> derives P (orp Q R);
  exp_right: forall {B: Type} (x:B) (P: A) (Q: B -> A),
                        derives P (Q x) -> derives P (exp Q);
  exp_left: forall {B: Type} (P: B -> A) (Q: A),
                      (forall x, derives (P x) Q) -> derives (exp P) Q;
  allp_left: forall {B}(P: B -> A) x Q, derives (P x) Q -> derives (allp P) Q;
  allp_right: forall {B}(P: A) (Q: B -> A),  (forall v, derives P (Q v)) -> derives P (allp Q);
  imp_andp_adjoint: forall P Q R, derives (andp P Q) R <-> derives P (imp Q R);
  prop_left: forall (P: Prop) Q, (P -> derives TT Q) -> derives (prop P) Q;
  prop_right: forall (P: Prop) Q, P -> derives Q (prop P);
  prop_imp_prop_left: forall (P Q: Prop), derives (imp (prop P) (prop Q)) (prop (P -> Q));
  allp_prop_left: forall {B: Type} (P: B -> Prop), derives (allp (fun b => prop (P b))) (prop (forall b, P b))
(* not_prop_right: forall (P: A) (Q: Prop), (Q -> derives P FF) -> derives P (prop (not Q)) *)
}.

Instance LiftNatDed (A B: Type) {ND: NatDed B} : NatDed (A -> B) :=
 mkNatDed (A -> B)
    (*andp*) (fun P Q x => andp (P x) (Q x))
    (*orp*) (fun P Q x => orp (P x) (Q x))
    (*exp*) (fun {T} (F: T -> A -> B) (a: A) => exp (fun x => F x a))
    (*allp*) (fun {T} (F: T -> A -> B) (a: A) => allp (fun x => F x a))
    (*imp*) (fun P Q x => imp (P x) (Q x))
    (*prop*) (fun P x => prop P)
    (*derives*) (fun P Q => forall x, derives (P x) (Q x))
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
 intros; extensionality x; apply pred_ext; auto.
 intros; apply derives_refl.
 intros; eapply derives_trans; eauto.
 intros; eapply andp_right; eauto.
 intros; eapply andp_left1; eauto.
 intros; eapply andp_left2; eauto.
 intros; eapply orp_left; eauto.
 intros; eapply orp_right1; eauto.
 intros; eapply orp_right2; eauto.
 intros; eapply exp_right; eauto.
 intros; eapply exp_left; eauto.
 intros; eapply allp_left; eauto.
 intros; eapply allp_right; eauto.
 intros; split; intros;  eapply imp_andp_adjoint; eauto.
 intros; eapply prop_left; eauto.
 intros; eapply prop_right; eauto.
 intros; eapply prop_imp_prop_left; eauto.
 intros; eapply allp_prop_left; eauto.
Defined.

Delimit Scope logic with logic.
Local Open Scope logic.
Notation "P '|--' Q" := (derives P Q) (at level 80, no associativity).
Notation "'EX'  x ':' T ',' P " := (exp (fun x:T => P%logic)) (at level 65, x at level 99) : logic.
Notation "'ALL'  x ':' T  ',' P " := (allp (fun x:T => P%logic)) (at level 65, x at level 99) : logic.
Infix "||" := orp (at level 50, left associativity) : logic.
Infix "&&" := andp (at level 40, left associativity) : logic.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : logic.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : logic.
Notation "'!!' e" := (prop e) (at level 25) : logic.

Class SepLog (A: Type) {ND: NatDed A} := mkSepLog {
  emp: A;
  sepcon: A -> A -> A;
  wand: A -> A -> A;
  ewand: A -> A -> A;
  sepcon_assoc: forall P Q R, sepcon (sepcon P Q) R = sepcon P (sepcon Q R);
  sepcon_comm:  forall P Q, sepcon P Q = sepcon Q P;
  wand_sepcon_adjoint: forall (P Q R: A),  (sepcon P Q |-- R) <-> (P |-- wand Q R);
  sepcon_andp_prop: forall P Q R, sepcon P (!!Q && R) = !!Q && (sepcon P R);
  sepcon_derives: forall P P' Q Q' : A, P |-- P' -> Q |-- Q' -> sepcon P Q |-- sepcon P' Q';
  ewand_sepcon: forall (P Q R : A),  ewand (sepcon P Q) R = ewand P (ewand Q R);
  ewand_TT_sepcon: forall (P Q R: A),
                         andp (sepcon P Q) (ewand R TT) |--
                               sepcon (andp P (ewand R TT)) (andp Q (ewand R TT));
  exclude_elsewhere: forall P Q: A, sepcon P Q |-- sepcon (andp P (ewand Q TT)) Q;
  ewand_conflict: forall P Q R, sepcon P Q |-- FF -> andp P (ewand Q R) |-- FF
}.

Notation "P '*' Q" := (sepcon P Q) : logic.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : logic.

Instance LiftSepLog (A B: Type) {NB: NatDed B}{SB: SepLog B} : SepLog (A -> B).
 apply (mkSepLog (A -> B) _ (fun rho => emp)
            (fun P Q rho => P rho * Q rho) (fun P Q rho => P rho -* Q rho)
            (fun P Q rho => ewand (P rho) (Q rho))).
 (* sepcon_assoc *) intros; extensionality rho; apply sepcon_assoc.
 (* sepcon_comm *) intros; extensionality rho; apply sepcon_comm.
 intros.  split. simpl. intuition.
    apply wand_sepcon_adjoint. auto.
    intro. intro rho.     apply <- wand_sepcon_adjoint; auto.
 simpl; intros. extensionality x. apply sepcon_andp_prop.
 simpl; intros; apply sepcon_derives; auto.
 simpl; intros; extensionality x; apply ewand_sepcon.
 simpl; intros; eapply ewand_TT_sepcon.
 simpl; intros; eapply exclude_elsewhere.
 simpl; intros; eapply ewand_conflict; eauto.
Defined.

Class ClassicalSep  (A: Type) {ND: NatDed A}{SL: SepLog A} := mkCS {
   sepcon_emp: forall P, P * emp = P
}.

Instance LiftClassicalSep (A B: Type)  {NB: NatDed B}{SB: SepLog B}{CB: ClassicalSep B} :
        ClassicalSep (A -> B).
 apply mkCS.
 intros. extensionality x. simpl. apply sepcon_emp.
Qed.

Definition  extensible {A}{ND: NatDed A}{SL: SepLog A}(P:A) := sepcon P TT |-- P.

Class IntuitionisticSep (A: Type) {ND: NatDed A}{SL: SepLog A} := mkIS {
   all_extensible: forall P, extensible P
}.

Instance LiftIntuitionisticSep (A B: Type)  {NB: NatDed B}{SB: SepLog B}{IB: IntuitionisticSep B} :
        IntuitionisticSep (A -> B).
 apply mkIS.
 intros. intro. simpl. apply all_extensible.
Qed.

Class Indir (A: Type) {ND: NatDed A} := mkIndir {
  later: A -> A;
  now_later: forall P: A, P |-- later P;
  later_K: forall P Q, later (P --> Q) |-- later P --> later Q;
  later_allp: forall T (F: T -> A),  later (allp F) = ALL x:T, later (F x);
  later_exp: forall T (F: T-> A), EX x:T, later (F x) |-- later (exp F);
  later_exp': forall T (any:T) F, later (exp F) = EX x:T, later (F x);
  later_exp'': forall T F, later (exp F) |-- (EX x:T, later (F x)) || later FF;
  later_imp: forall P Q,  later(P --> Q) = later P --> later Q;
  later_prop: forall PP: Prop, later (!! PP) |-- !! PP || later FF;
  loeb: forall P,   later P |-- P ->  TT |-- P
}.

Notation "'|>' e" := (later e) (at level 30, right associativity): logic.

Instance LiftIndir (A: Type) (B: Type)  {NB: NatDed B}{IXB: Indir B} :
         @Indir (A -> B) (LiftNatDed A B).
 apply (mkIndir _ _ (fun P rho => later (P rho))); intros; simpl in *; intros.
 apply now_later.
 apply later_K.
 simpl; intros. extensionality rho. apply later_allp.
 simpl; intros. apply later_exp.
 simpl; intros. extensionality rho. apply later_exp'; auto.
 simpl; intros. apply later_exp''.
 simpl; intros. extensionality rho. apply later_imp.
 simpl; intros. apply later_prop.
 simpl; intros. apply loeb; auto.
Defined.

Class SepIndir (A: Type) {NA: NatDed A}{SA: SepLog A}{IA: Indir A} := mkSepIndir {
  later_sepcon: forall P Q, |> (P * Q) = |>P * |>Q;
  later_wand: forall P Q, |> (P -* Q) = |>P -* |>Q;
  later_ewand: forall P Q, |> (ewand P Q) = ewand (|>P) (|>Q)
}.

Instance LiftSepIndir  (A: Type) (B: Type)  {NB: NatDed B} {SB: SepLog B}{IB: Indir B}{SIB: SepIndir B} :
     @SepIndir (A -> B) (LiftNatDed A B) (LiftSepLog A B) (LiftIndir A B).
 constructor.
 intros; simpl. extensionality rho.  apply later_sepcon.
 intros; simpl. extensionality rho.  apply later_wand.
 intros; simpl. extensionality rho.  apply later_ewand.
Defined.

Class CorableSepLog (A: Type) {ND: NatDed A}{SL: SepLog A}:= mkCorableSepLog {
  corable: A -> Prop;
  corable_prop: forall P, corable (!! P);
  corable_andp: forall P Q, corable P -> corable Q -> corable (P && Q);
  corable_orp: forall P Q, corable P -> corable Q -> corable (P || Q);
  corable_imp: forall P Q, corable P -> corable Q -> corable (P --> Q);
  corable_allp: forall {B: Type} (P:  B -> A), (forall b, corable (P b)) -> corable (allp P);
  corable_exp: forall {B: Type} (P:  B -> A), (forall b, corable (P b)) -> corable (exp P);
  corable_sepcon: forall P Q, corable P -> corable Q -> corable (P * Q);
  corable_wand: forall P Q, corable P -> corable Q -> corable (P -* Q);
  corable_andp_sepcon1: forall P Q R, corable P ->  (P && Q) * R = P && (Q * R)
}.

Instance LiftCorableSepLog (A: Type) (B: Type) {NB: NatDed B} {SB: SepLog B} {CSL: CorableSepLog B} : @CorableSepLog (A -> B) (LiftNatDed A B) (LiftSepLog A B).
  apply (@mkCorableSepLog _ _ _ (fun P => forall b, corable (P b))); intros; simpl in *; intros.
  + apply corable_prop.
  + apply corable_andp; auto.
  + apply corable_orp; auto.
  + apply corable_imp; auto.
  + apply corable_allp; auto.
  + apply corable_exp; auto.
  + apply corable_sepcon; auto.
  + apply corable_wand; auto.
  + extensionality b.
    apply corable_andp_sepcon1; auto.
Defined.

Class CorableIndir (A: Type) {ND: NatDed A}{SL: SepLog A}{CSL: CorableSepLog A}{ID: Indir A} :=
  corable_later: forall P, corable P -> corable (|> P).

Instance LiftCorableIndir (A: Type) (B: Type) {NB: NatDed B} {SB: SepLog B} {CSL: CorableSepLog B} {ID: Indir B} {CI: CorableIndir B}: @CorableIndir (A -> B) (LiftNatDed A B) (LiftSepLog A B) (LiftCorableSepLog A B) (LiftIndir A B).
  unfold CorableIndir; simpl; intros.
  apply corable_later; auto.
Defined.

Lemma orp_comm: forall {A: Type} `{NatDed A} (P Q: A), P || Q = Q || P.
Proof.
  intros.
  apply pred_ext.
  + apply orp_left; [apply orp_right2 | apply orp_right1]; apply derives_refl.
  + apply orp_left; [apply orp_right2 | apply orp_right1]; apply derives_refl.
Qed.

