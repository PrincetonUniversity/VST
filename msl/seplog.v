Require Import msl.Extensionality.

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
  modus_ponens: forall P Q, derives (andp P (imp P Q)) Q;
  prop_left: forall (P: Prop) Q, (P -> derives TT Q) -> derives (prop P) Q;
  prop_right: forall (P: Prop) Q, P -> derives Q (prop P);
  exp_andp1: forall B (p: B -> A) q, andp (exp p) q = (exp (fun x => andp (p x) q))
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
 intros; eapply modus_ponens; eauto.
 intros; eapply prop_left; eauto.
 intros; eapply prop_right; eauto.
 intros; extensionality rho; eapply exp_andp1; eauto.
Defined.

Delimit Scope logic with logic.
Local Open Scope logic.
Notation "P '|--' Q" := (derives P Q) (at level 80, no associativity).
Notation "'Ex'  x ':' T ',' P " := (exp (fun x:T => P%logic)) (at level 65, x at level 99) : logic.
Notation "'All'  x ':' T  ',' P " := (allp (fun x:T => P%logic)) (at level 65, x at level 99) : logic.
Infix "||" := orp (at level 50, left associativity) : logic.
Infix "&&" := andp (at level 40, left associativity) : logic.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : logic.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : logic.
Notation "'!!' e" := (prop e) (at level 25) : logic.

Class SepLog (A: Type) {ND: NatDed A} := mkSepLog {
  emp: A;
  sepcon: A -> A -> A;
  wand: A -> A -> A;
  pure := fun (P:A) =>   P |-- emp;
  sepcon_assoc: forall P Q R, sepcon (sepcon P Q) R = sepcon P (sepcon Q R);
  sepcon_comm:  forall P Q, sepcon P Q = sepcon Q P;
  wand_sepcon_adjoint: forall (P Q R: A),  (sepcon P Q |-- R) = (P |-- wand Q R);
  sepcon_FF: forall P, sepcon P FF = FF;
  exp_sepcon1:  forall T (P: T ->  A) Q,  sepcon (exp P) Q = exp (fun x => sepcon (P x) Q);
  sepcon_andp_prop: forall P Q R, sepcon P (!!Q && R) = !!Q && (sepcon P R);
  sepcon_derives: forall P P' Q Q' : A, P |-- P' -> Q |-- Q' -> sepcon P Q |-- sepcon P' Q';
  sepcon_pure_andp: forall P Q, pure P -> pure Q -> (sepcon P Q = andp P Q);
  pure_sepcon_TT_andp: forall P Q, pure P -> andp (sepcon P TT) Q = sepcon P Q
}.

Notation "P '*' Q" := (sepcon P Q) : logic.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : logic.

Instance LiftSepLog (A B: Type) {NB: NatDed B}{SB: SepLog B} : SepLog (A -> B).
 apply (mkSepLog (A -> B) _ (fun rho => emp) 
            (fun P Q rho => P rho * Q rho) (fun P Q rho => P rho -* Q rho)).
 (* sepcon_assoc *) intros; extensionality rho; apply sepcon_assoc.
 (* sepcon_comm *) intros; extensionality rho; apply sepcon_comm.
 intros. apply prop_ext. simpl. intuition.
    rewrite <- wand_sepcon_adjoint. auto.
    rewrite wand_sepcon_adjoint; auto.
 intros. simpl. extensionality x. change (!!False) with FF. apply sepcon_FF.
 simpl; intros. extensionality x. apply exp_sepcon1.
 simpl; intros. extensionality x. apply sepcon_andp_prop.
 simpl; intros; apply sepcon_derives; auto.
 simpl; intros; extensionality x; apply sepcon_pure_andp; unfold pure; auto.
 simpl; intros; extensionality x; apply pure_sepcon_TT_andp; unfold pure in *; auto.
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
