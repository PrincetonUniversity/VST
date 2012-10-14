Require Import msl.seplog.
Require Import msl.alg_seplog.
Require Import msl.Extensionality.

Local Open Scope logic.

Hint Resolve @derives_refl.


Lemma TT_right {A}{NA: NatDed A}: forall P:A, P |-- TT.
Proof. intros; apply prop_right; auto.
Qed.

Hint Resolve @TT_right: normalize.

Ltac norm := auto with normalize.

Lemma andp_dup {A}{ND: NatDed A}: forall P: A, P && P = P.
Proof. intros. apply pred_ext.
apply andp_left1; apply derives_refl.
apply andp_right; apply derives_refl.
Qed.


Lemma FF_left {A}{NA: NatDed A}: forall P, FF |-- P.
Proof.
intros; apply prop_left. intuition.
Qed.
Hint Resolve @FF_left : normalize.

Lemma andp_TT {A}{NA: NatDed A}: forall (P: A), P && TT = P.
Proof with norm.
intros.
apply pred_ext.
apply andp_left1...
apply andp_right...
Qed.

Lemma TT_prop_right {A}{ND: NatDed A}: forall P: Prop,
   P -> @derives A ND TT (prop P).
Proof.
intros. apply prop_right; auto.
Qed.

Lemma sepcon_andp_prop'  {A}{NA: NatDed A}{SA: SepLog A}: 
     forall P Q R, (!!Q && P)*R = !!Q&&(P*R).
Proof with norm.
intros.
rewrite sepcon_comm. rewrite sepcon_andp_prop.
rewrite sepcon_comm; auto.
Qed.

Lemma emp_sepcon  {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A} : forall (P:A),
   emp * P = P.
Proof with norm.
 intros; rewrite sepcon_comm. apply sepcon_emp.
Qed.

Lemma TT_andp {A}{NA: NatDed A}: forall P: A,  TT && P = P.
Proof with norm.
  intros. apply pred_ext. apply andp_left2... apply andp_right...
Qed.

Lemma exp_sepcon2 {A}{NA: NatDed A}{SA: SepLog A}: 
   forall T (P: A) (Q: T -> A),  P * exp Q = exp (fun x => P * Q x).
Proof. intros.
 rewrite sepcon_comm. rewrite exp_sepcon1.
 f_equal. extensionality x. apply sepcon_comm.
Qed.

Lemma andp_comm  {A}{NA: NatDed A}:
  forall P Q,  P && Q = Q && P.
Proof with norm.
 intros.
   apply pred_ext.
   apply andp_right. apply andp_left2... apply andp_left1...
    apply andp_right. apply andp_left2... apply andp_left1...
Qed.

Lemma andp_assoc {A} {NA: NatDed A} : forall P Q R,
  (P && Q) && R = P && (Q && R).
Proof.
  intros; apply pred_ext;   repeat apply andp_right.
  do 2 apply andp_left1; auto.
  apply andp_left1; apply andp_left2; auto.
  apply andp_left2; auto.
  apply andp_left1; auto.
  apply andp_left2; apply andp_left1; auto.
  do 2 apply andp_left2; auto.
Qed.

Lemma exp_andp2  {A}{NA: NatDed A}:
 forall B (p: A) (q: B -> A) , (p && exp q) = exp (fun x => p && q x).
Proof.
 intros. rewrite andp_comm; rewrite exp_andp1.
 f_equal. extensionality x. apply andp_comm.
Qed.

Hint Rewrite @sepcon_emp @emp_sepcon @TT_andp @andp_TT 
             @exp_sepcon1 @exp_sepcon2
               @exp_andp1 @exp_andp2
         @sepcon_andp_prop @sepcon_andp_prop'
        : normalize.


Lemma andp_derives {A} {NA: NatDed A}:
  forall P Q P' Q': A, P |-- P' -> Q |-- Q' -> P && Q |-- P' && Q'.
Proof.
intros.
apply andp_right.
apply andp_left1; apply H.
apply andp_left2; apply H0.
Qed.

Lemma imp_derives {A} {NA: NatDed A}:
  forall P P' Q Q',
    P' |-- P ->
    Q |-- Q' -> 
    P --> Q |-- P' --> Q'.
Proof.
intros.
apply imp_andp_adjoint. 
eapply derives_trans; try apply H0; clear H0.
eapply derives_trans; [ apply andp_derives; try apply H | ]; clear H.
apply derives_refl.
rewrite andp_comm. apply modus_ponens.
Qed.

Lemma pure_sepcon {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
    forall (P : A), pure P -> P*P=P.
Proof with norm.
 intros. pose proof (sepcon_pure_andp _ _ H H).
 rewrite H0. apply pred_ext. apply andp_left1... apply andp_right...
Qed.

Lemma pure_e  {A}{NA: NatDed A}{SA: SepLog A}: forall (P: A), pure P -> (P |-- emp).
Proof.
intros.
apply H.
Qed.

Hint Resolve @pure_e : normalize.

Lemma pure_emp {A}{NA: NatDed A}{SA: SepLog A}: pure emp.
Proof with norm.
intros. unfold pure...
Qed.
Hint Resolve @pure_emp.

Lemma pure_sepcon1''  {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}: 
   forall P Q R, pure P -> Q |-- R -> P * Q |-- R.
Proof with norm.
intros.
apply @derives_trans with (emp*Q).
apply sepcon_derives...
rewrite emp_sepcon...
Qed.


Lemma pure_existential {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
   forall B (P: B -> A),    (forall x: B , pure (P x)) -> pure (exp P).
Proof.
intros.
unfold pure in *.
apply exp_left; auto.
Qed.

Hint Resolve @pure_existential.

Lemma FF_sepcon {A} {NA: NatDed A}{SA: SepLog A}: forall P, FF * P = FF.
Proof.
intros.
rewrite sepcon_comm. apply sepcon_FF.
Qed.

Hint Rewrite @FF_sepcon @sepcon_FF : normalize.

Lemma prop_true_andp {A} {NA: NatDed A}:
  forall (P: Prop) Q,  P -> (!! P && Q = Q).
Proof with norm.
intros.
apply pred_ext. apply andp_left2...
apply andp_right... apply prop_right...
Qed.

Hint Rewrite @prop_true_andp using (solve [auto]) : normalize.

Lemma true_eq {A} {NA: NatDed A}:  forall P: Prop, P -> (!! P) = (TT: A).
Proof with norm.
intros. apply pred_ext...
apply prop_right...
Qed. 
Hint Rewrite @true_eq using (solve [auto]) : normalize.

Lemma pure_con' {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}: 
      forall P Q, pure P -> pure Q -> pure (P*Q).
Proof.
intros.
unfold pure in *.
rewrite <- sepcon_emp.
apply sepcon_derives; auto.
Qed.
Hint Resolve @pure_con'.

Lemma pure_intersection1: forall {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}
       (P Q: A), pure P -> pure (P && Q).
Proof.
unfold pure; intros; auto.
apply andp_left1; auto.
Qed.

Lemma pure_intersection2: forall {A}{NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}
     (P Q: A), pure Q -> pure (P && Q).
Proof.
unfold pure; intros; auto.
apply andp_left2; auto.
Qed.
Hint Resolve @pure_intersection1 @pure_intersection2.

Lemma FF_andp {A}{NA: NatDed A}:  forall P: A, FF && P = FF.
Proof with norm.
intros. apply pred_ext...
apply andp_left1...
Qed.

Lemma andp_FF {A}{NA: NatDed A}:  forall P: A, P && FF = FF.
Proof.
intros. rewrite andp_comm. apply FF_andp.
Qed.
Hint Rewrite @FF_andp @andp_FF : normalize.

Hint Rewrite @andp_dup : normalize.

Lemma sepcon_TT {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
   forall (P: A), P |-- (P * TT).
Proof with norm.
intros.
apply @derives_trans with (P * emp).
rewrite sepcon_emp...
apply sepcon_derives...
Qed.
Hint Resolve @sepcon_TT.

Lemma imp_extract_exp_left {B A: Type} {NA: NatDed A}:
    forall    (p : B -> A) (q: A),
  (forall x, p x |-- q) ->
   exp p |-- q.
Proof.
intros.
apply exp_left. auto.
Qed.

Lemma allp_derives: 
       forall {A: Type}  {NA: NatDed A} (B: Type) (P Q: B -> A), 
               (forall x:B, P x |-- Q x) -> (allp P |-- allp Q).
Proof.
intros.
apply allp_right; intro x; apply allp_left with x; auto.
Qed.

Lemma forall_pred_ext  {A}  {NA: NatDed A}: forall B (P Q: B -> A), 
 (ALL x : B, (P x <--> Q x)) |-- (ALL x : B, P x) <--> (ALL x: B, Q x) .
Proof.
intros.
apply andp_right.
 apply @derives_trans with (ALL x:B, P x --> Q x).
 apply allp_derives; intro x; apply andp_left1; auto.
 apply imp_andp_adjoint; apply allp_right; intro x.
 apply @derives_trans with ((P x --> Q x) && P x).
 apply andp_derives; apply allp_left with x; auto.
 rewrite andp_comm. apply modus_ponens.
 apply @derives_trans with (ALL x:B, Q x --> P x).
 apply allp_derives; intro x; apply andp_left2; auto.
 apply imp_andp_adjoint; apply allp_right; intro x.
 apply @derives_trans with ((Q x --> P x) && Q x).
 apply andp_derives; apply allp_left with x; auto.
 rewrite andp_comm. apply modus_ponens.
Qed.

Lemma exists_pred_ext  {A} {NA: NatDed A}: forall B (P Q: B -> A), 
 (ALL x : B, (P x <--> Q x)) |-- (EX x : B, P x) <--> (EX x: B, Q x) .
Proof.
intros.
apply andp_right.
 apply imp_andp_adjoint.
autorewrite with normalize.
apply exp_left; intro x. apply exp_right with x.
 apply imp_andp_adjoint.
apply allp_left with x. apply andp_left1; auto.
 apply imp_andp_adjoint.
autorewrite with normalize.
apply exp_left; intro x. apply exp_right with x.
 apply imp_andp_adjoint.
apply allp_left with x. apply andp_left2; auto.
Qed.

Lemma imp_pred_ext  {A}  {NA: NatDed A}: forall B B' P Q, 
       (B <--> B') && (B --> (P <--> Q)) 
 |-- (B --> P) <-->  (B' --> Q).
Proof.
intros.
apply andp_right.
apply -> imp_andp_adjoint.
apply -> imp_andp_adjoint.
rewrite andp_comm.
rewrite (andp_comm (B --> B')).
repeat rewrite <- andp_assoc.
do 2 rewrite andp_assoc.
eapply derives_trans; [eapply andp_derives; [apply modus_ponens | apply derives_refl] | ].
apply @derives_trans with ((B && (B --> (P --> Q))) && (B && (B --> P))).
repeat apply andp_right.
apply andp_left1; auto.
apply andp_left2. apply andp_left2. apply andp_left1. apply imp_derives; auto.
apply andp_left1; auto.
apply andp_left1; auto.
apply andp_left2. apply andp_left2. apply andp_left2. auto.
apply @derives_trans with ((P --> Q) && P).
apply andp_derives; apply modus_ponens.
rewrite andp_comm; apply modus_ponens.
apply -> imp_andp_adjoint.
apply -> imp_andp_adjoint.
rewrite andp_comm.
repeat rewrite <- andp_assoc.
do 2 rewrite andp_assoc.
eapply derives_trans; [eapply andp_derives; [apply modus_ponens | apply derives_refl] | ].
apply @derives_trans with ((B' && (B' --> (Q --> P))) && (B' && (B' --> Q))).
repeat apply andp_right.
apply andp_left1; auto.
repeat rewrite <- andp_assoc.
apply andp_left1.
apply -> imp_andp_adjoint.
apply andp_left1.
eapply derives_trans; [eapply andp_derives; [apply modus_ponens | apply derives_refl] | ].
eapply derives_trans; [apply modus_ponens | ].
apply andp_left2; auto.
apply andp_left1; auto.
repeat apply andp_left2. auto.
eapply derives_trans; [eapply andp_derives; apply modus_ponens | ].
rewrite andp_comm; apply modus_ponens.
Qed.

Lemma pure_sepcon_TT_andp'  {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
  forall P Q, pure P -> Q && (P * TT) = (Q*P).
Proof.
intros. rewrite andp_comm.
rewrite pure_sepcon_TT_andp; auto.
apply sepcon_comm.
Qed.

Hint Rewrite @pure_sepcon_TT_andp @pure_sepcon_TT_andp' using (solve [auto]): normalize.

Lemma pure_sepcon1'  {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
  forall P Q R, pure P -> P * Q |-- P * R -> P * Q |-- R.
Proof with norm.
intros.
eapply derives_trans; try apply H0.
apply pure_sepcon1''; auto.
Qed.

Lemma pull_right {A} {NA: NatDed A}{SA: SepLog A}:
 forall P Q R,
   (Q * P * R) = (Q * R * P).
Proof.
intros. repeat rewrite sepcon_assoc. rewrite (sepcon_comm P); auto.
Qed.

Lemma pull_right0 {A} {NA: NatDed A}{SA: SepLog A}:
  forall P Q,   (P * Q) = (Q * P).
Proof.
intros. rewrite (sepcon_comm P); auto.
Qed.

Ltac pull_left A := repeat (rewrite <- (pull_right A) || rewrite <- (pull_right0 A)).

Ltac pull_right A := repeat (rewrite (pull_right A) || rewrite (pull_right0 A)).

Lemma pure_modus {A} {NA: NatDed A}{SA: SepLog A}{CA: ClassicalSep A}:
  forall P Q,  P |-- Q -> pure Q -> P |-- Q && P.
Proof.
intros.
apply andp_right; auto.
Qed.

Lemma derives_extract_prop {A} {NA: NatDed A}:
  forall (P: Prop) (Q R: A), (P -> Q |-- R) ->  !!P && Q |-- R.
Proof.
 intros.
 apply imp_andp_adjoint.
 apply prop_left.
 intros. apply imp_andp_adjoint. rewrite TT_andp. apply H; auto.
Qed.

Lemma derives_extract_prop0 {A}{NA: NatDed A}:
    forall (P: Prop) (R: A), (P -> TT |-- R)  -> !!P |-- R.
Proof.
intros.
apply derives_trans with (!!P && TT).
rewrite andp_TT; auto.
apply derives_extract_prop; auto.
Qed.

Lemma derives_extract_prop' {A} {NA: NatDed A}:
  forall (P: Prop) (Q R: A), (P -> Q |-- R) ->  Q && !!P|-- R.
Proof.
intros. rewrite andp_comm. apply derives_extract_prop; auto.
Qed.

Lemma andp_assoc' {A}{NA: NatDed A}:
  forall P Q R, Q && (P && R) = P && (Q && R).
Proof. intros. rewrite andp_comm. rewrite andp_assoc. f_equal. apply andp_comm. 
Qed.

Definition corable {A} {NA: NatDed A}{SA: SepLog A} (P: A) : Prop :=
 forall Q R, (P && Q) * R = P && (Q * R).

Lemma corable_andp_sepcon1{A}  {NA: NatDed A}{SA: SepLog A} :
   forall P Q R, corable P ->  (P && Q) * R = P && (Q * R).
Proof. auto. Qed.

Lemma corable_andp_sepcon2{A}  {NA: NatDed A}{SA: SepLog A} :
   forall P Q R, corable P ->  (Q && P) * R = P && (Q * R).
Proof.
intros. rewrite andp_comm. apply corable_andp_sepcon1. auto.
Qed.

Lemma corable_sepcon_andp1 {A}  {NA: NatDed A}{SA: SepLog A} :
   forall P Q R, corable P ->  Q  * (P && R) = P && (Q * R).
Proof.
intros. rewrite sepcon_comm. rewrite corable_andp_sepcon1; auto. rewrite sepcon_comm; auto.
Qed.

Lemma corable_sepcon_andp2 {A}  {NA: NatDed A}{SA: SepLog A} :
   forall P Q R, corable P ->  Q  * (R && P) = P && (Q * R).
Proof.
intros. rewrite sepcon_comm. rewrite andp_comm. rewrite corable_andp_sepcon1; auto. rewrite sepcon_comm; auto.
Qed.

Lemma prop_corable{A}  {NA: NatDed A}{SA: SepLog A}: forall P, corable (!!P).
Proof. unfold corable; intros.
rewrite sepcon_andp_prop'.  auto.
Qed.

Hint Resolve @prop_corable : normalize.

(* This hint doesn't work well, hence the extra clauses in normalize1 and normalize1_in *)
Hint Rewrite @corable_andp_sepcon1 @corable_andp_sepcon2
                    @corable_sepcon_andp1 @corable_sepcon_andp2 using solve [auto with normalize typeclass_instances].

Ltac normalize1 := 
         match goal with
            | |- _ => contradiction
            | |- context [@andp ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                      change (@andp A (@LiftNatDed T B C) D E F) with (D F && E F)
            | |- context [@later ?A  (@LiftNatDed ?T ?B ?C) (@indir_ops _ _ (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5)) ?D ?F] =>
                   change (@later A  (@LiftNatDed T B C) (@indir_ops A (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5)) D F) 
                     with (@later B C (@indir_ops B C X5) (D F))   
            | |- context [@sepcon ?A (@LiftNatDed ?B ?C ?D) 
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))
            | |- context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) by (auto with normalize)
            | |- context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) by (auto with normalize)
            | |- context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) by (auto with normalize)
            | |- context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) by (auto with normalize)
            (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                preserves the name of the "y" variable *)
            | |- context [andp (exp (fun y => _)) _] => 
                autorewrite with normalize; apply imp_extract_exp_left; intro y
            | |- context [andp _ (exp (fun y => _))] => 
                autorewrite with normalize; apply imp_extract_exp_left; intro y
            | |- context [sepcon (exp (fun y => _)) _] => 
               autorewrite with normalize; apply imp_extract_exp_left; intro y
            | |- context [sepcon _ (exp (fun y => _))] => 
                autorewrite with normalize; apply imp_extract_exp_left; intro y
 
           | |-  derives ?A   _ => match A with 
                          | context [ ((!! ?P) && ?Q) && ?R ] => rewrite (andp_assoc (!!P) Q R)
                          | context [ ?Q && (!! ?P && ?R)] =>
                                         match Q with !! _ => fail 2 | _ => rewrite (andp_assoc' (!!P) Q R) end
                         end
            | |- _ => progress  (autorewrite with normalize); auto with typeclass_instances
            | |- _ = ?x -> _ => intro; subst x
            | |- ?x = _ -> _ => intro; subst x
            |  |- ?ZZ -> _ => match type of ZZ with 
                                               | Prop => 
                                                    let H := fresh in
                                                       ((assert (H:ZZ) by auto; clear H; intros _) || intro H)
                                               | _ => intros _
                                              end             
            | |- forall _, _ => let x := fresh "x" in (intro x; normalize1; try generalize dependent x)
            | |- exp _ |-- _ => apply imp_extract_exp_left 
            | |- !! _ |-- _ => apply derives_extract_prop0
            | |- !! _ && _ |-- _ => apply derives_extract_prop
            | |- _ && !! _ |-- _ => apply derives_extract_prop'
            | |- _ |-- !! (?x = ?y) && _ => 
                            (rewrite prop_true_andp with (P:= (x=y))
                                            by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (rewrite prop_true_andp with (P:=(x=y))
                                            by (unfold x; reflexivity); unfold x in *; clear x)
            | |- TT |-- !! _ => apply TT_prop_right
            | |- _ => solve [auto with typeclass_instances]
            end.

Ltac normalize1_in Hx := 
             match type of Hx with
                 | context [@andp ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                         change (@andp A (@LiftNatDed T B C) D E F) with (D F && E F)
                 | context [@later ?A  (@LiftNatDed ?T ?B ?C) (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5) ?D ?F] =>
                    change (@later A  (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5) D F) 
                     with (@later B C X5 (D F))   
                 | context [@sepcon ?A (@LiftNatDed ?B ?C ?D) 
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))
                | context [ !! ?P ] =>      
                                    rewrite (true_eq P) in Hx by auto with typeclass_instances
                | context [ !! ?P && ?Q ] =>  
                                    rewrite (prop_true_andp P Q) in Hx by auto with typeclass_instances  
                | context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) in Hx by (auto with normalize)
                | context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) in Hx by (auto with normalize)
                | context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) in Hx by (auto with normalize)
                | context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) in Hx by (auto with normalize)
                | _ => progress  (autorewrite with normalize in Hx); auto with typeclass_instances
                end.

Ltac normalize := repeat (auto with normalize; normalize1).

Tactic Notation "normalize" "in" hyp(H) := repeat (normalize1_in H).

Definition mark {A: Type} (i: nat) (j: A) := j.

Lemma swap_mark1 {A} {NA: NatDed A}{SA: SepLog A}:
  forall i j Pi Pj B, (i<j)%nat -> B * mark i Pi * mark j Pj = B * mark j Pj * mark i Pi.
Proof.
intros.
repeat rewrite sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

Lemma swap_mark0 {A} {NA: NatDed A}{SA: SepLog A}:
  forall i j Pi Pj,  (i<j)%nat -> mark i Pi * mark j Pj = mark j Pj * mark i Pi.
Proof.
intros.
apply sepcon_comm.
Qed.

Ltac select_left n :=
  repeat match goal with 
 | |- context [(_ * mark ?i _ * mark n _)] => 
      rewrite (swap_mark1 i n); [ | solve [simpl; auto]]
 | |- context [(mark ?i _ * mark n _)] => 
      rewrite (swap_mark0 i n); [ | solve [simpl; auto]]
end.
Ltac select_all n := match n with 
                                | O => idtac 
                                | S ?n' => select_left n; select_all n' 
                              end.
Ltac markem n P := 
   match P with 
   | (?Y * ?Z) => 
        (match goal with H: mark _ Z = Z |- _ => idtac end 
        || assert (mark n Z = Z) by auto); markem (S n) Y
   | ?Z =>  match goal with H: mark _ Z = Z |- _ => idtac end 
                || assert (mark n Z = Z) by auto
  end.

Ltac prove_assoc_commut := 
 clear;
 try (match goal with |- ?F _ -> ?G _ => replace G with F; auto end);
  (repeat rewrite <- sepcon_assoc; 
   match goal with |- ?P = _ => markem O P end; 
   let LEFT := fresh "LEFT" in match goal with |- ?P = _ => set (LEFT := P) end;
  match goal with H: mark ?n _ = _ |- _ =>
     repeat  match goal with H: mark ?n _ = ?P |- _ => rewrite <- H; clear H end;
     select_all n;
     reflexivity
   end).

Lemma test_prove_assoc_commut {T}{NA: NatDed T}{SA: SepLog T} : forall A B C D E : T,
   D * E * A * C * B = A * B * C * D * E.
Proof.
intros.
prove_assoc_commut.
Qed.

(***** contractiveness ******)

Lemma later_fash1 {A} {NA: NatDed A}{IA: Indir A}:
   forall P, |> # P |-- # |> P.
Proof. intros. rewrite later_fash; auto.
Qed.

Lemma subp_later1 {A}  {NA: NatDed A}{IA: Indir A} : forall P Q,
   |>(P >=> Q)  |--   |>P >=> |>Q.
Proof.
intros.
rewrite later_fash. rewrite later_imp. auto.
Qed.

Lemma subp_later {A}  {NA: NatDed A}{IA: Indir A} : forall P Q,
   |>(P >=> Q) = |>P >=> |>Q.
Proof.
intros.
rewrite later_fash. rewrite later_imp. auto.
Qed.

Lemma eqp_later1 {A} {NA: NatDed A}{IA: Indir A} : forall P Q,
   |>(P <=> Q)  |--   |>P <=> |>Q.
Proof.
intros.
rewrite later_fash.
rewrite later_andp; repeat rewrite later_imp; repeat  rewrite fash_andp. auto.
Qed.

Lemma eqp_later {A}  {NA: NatDed A}{IA: Indir A}  : forall P Q,
    (|>(P <=> Q) = |>P <=> |>Q).
Proof.
intros.
rewrite later_fash.
rewrite later_andp; repeat rewrite later_imp; repeat  rewrite fash_andp. auto.
Qed.

Lemma subp_refl {A} {NA: NatDed A}{IA: Indir A}  : forall G P,
  G |-- P >=> P.
Proof.
intros.
rewrite <- (fash_triv G).
apply @derives_trans with (#TT).
apply fash_TT.
apply fash_derives.
apply imp_andp_adjoint.
apply andp_left2; auto.
Qed.

Lemma subp_trans {A} {NA: NatDed A}{IA: Indir A}  : forall G P Q R,
  G |-- P >=> Q ->
  G |-- Q >=> R ->
  G |-- P >=> R.
Proof.
intros.
  apply @derives_trans with ((P >=> Q) && (Q >=> R)).
 apply andp_right; auto.
  clear.
 rewrite <- fash_andp. apply fash_derives.
 apply -> imp_andp_adjoint.
 rewrite andp_comm. rewrite <- andp_assoc.
 eapply derives_trans; [ apply andp_derives | ].
 apply modus_ponens. apply derives_refl. apply modus_ponens.
Qed.

Lemma subp_top {A} {NA: NatDed A}{IA: Indir A}  : forall G P,
  G |-- P >=> TT.
Proof.
 intros. apply @derives_trans with (#TT).
 apply fash_TT.
 apply fash_derives. apply imp_andp_adjoint.
 apply andp_left1; auto.
Qed.

Lemma subp_bot {A} {NA: NatDed A}{IA: Indir A}  : forall G P,
  G |-- FF >=> P.
Proof.
 intros. apply @derives_trans with (#TT).
 apply fash_TT.
 apply fash_derives. apply imp_andp_adjoint.
 apply andp_left2; apply FF_left.
Qed.

Lemma subp_andp {A} {NA: NatDed A}{IA: Indir A}  : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- P && Q >=> (P' && Q').
Proof.
 intros.
 apply @derives_trans with ((P >=> P') && (Q >=> Q')).
 apply andp_right; auto.
 clear.
 rewrite <- fash_andp. apply fash_derives.
 apply -> imp_andp_adjoint.
 apply @derives_trans with ((P && (P --> P')) && (Q && (Q --> Q'))).
 repeat apply andp_right.
 apply andp_left2. apply andp_left1; auto.
 do 2 apply andp_left1; auto.
 repeat apply andp_left2; auto.
 apply andp_left1; apply andp_left2; auto.
 apply andp_derives; apply modus_ponens.
Qed.

Lemma subp_imp {A} {NA: NatDed A}{IA: Indir A}  : forall G P P' Q Q',
  G |-- P' >=> P ->
  G |-- Q >=> Q' ->
  G |-- (P --> Q) >=> (P' --> Q').
Proof.
 intros.
 apply @derives_trans with ((P' >=> P) && (Q >=> Q')).
 apply andp_right; auto.
 clear.
 rewrite <- fash_andp. apply fash_derives.
 apply -> imp_andp_adjoint.
 apply -> imp_andp_adjoint.
 apply @derives_trans with (((P' && (P' --> P)) && (P --> Q)) && (Q --> Q')).
 repeat apply andp_right.
 apply andp_left2.  auto.
 do 3 apply andp_left1; auto.
 apply andp_left1. repeat apply andp_left2; auto.
 apply andp_left1; apply andp_left1. apply andp_left2;  auto.
 eapply derives_trans ; [eapply andp_derives | ].
 eapply derives_trans ; [eapply andp_derives | ].
 apply modus_ponens. apply derives_refl.
 apply modus_ponens. apply derives_refl.
 apply modus_ponens.
Qed.

Lemma subp_orp {A} {NA: NatDed A}{IA: Indir A}  : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- (P || Q) >=> (P' || Q').
Proof.
 intros.
 eapply derives_trans; [ apply andp_right; [apply H | apply H0] | ].
 clear.
 rewrite <- fash_andp. apply fash_derives.
 apply -> imp_andp_adjoint.
rewrite andp_comm. apply imp_andp_adjoint.
apply orp_left; apply -> imp_andp_adjoint; [apply orp_right1 | apply orp_right2].
 rewrite <- andp_assoc. apply andp_left1. apply modus_ponens.
 rewrite (andp_comm (_ --> _)).
 rewrite <- andp_assoc. apply andp_left1. apply modus_ponens.
Qed.

Lemma subp_subp {A} {NA: NatDed A}{IA: Indir A}:
  forall G (P Q R S: A), 
   G |-- (R >=> P) ->
   G |-- (Q >=> S) ->
   G |-- (P >=> Q) >=> (R >=> S).
Proof.
 intros.
 intros.
 eapply derives_trans; [ apply andp_right; [apply H | apply H0] | ].
 clear.
 rewrite fash_triv.
 apply -> (@imp_andp_adjoint Triv).
 rewrite andp_assoc.
 apply @derives_trans with ((R >=> P) && (P >=> S)).
 apply andp_derives; auto.
 apply subp_trans with Q. apply andp_left2; auto. apply andp_left1; auto.
  apply subp_trans with P. apply andp_left1; auto. apply andp_left2; auto.
Qed.

Lemma allp_imp2_later_e2 {B}{A}{NA: NatDed A}{IA: Indir A}:
   forall (P Q: B -> A) (y: B) ,
      (ALL x:B, |> P x <=> |> Q x) |-- |> Q y >=> |> P y.
Proof. 
  intros. apply allp_left with y. repeat rewrite fash_andp. apply andp_left2; auto.
Qed.

Lemma allp_imp2_later_e1 {B}{A}{NA: NatDed A}{IA: Indir A}:
   forall (P Q: B -> A) (y: B) ,
      (ALL x:B, |> P x <=> |> Q x) |-- |> P y >=> |> Q y.
Proof. 
  intros. apply allp_left with y. repeat rewrite fash_andp. apply andp_left1; auto.
Qed.

Lemma prove_HOcontractive1 {A} {NA: NatDed A}{IA: Indir A}{RA: RecIndir A} : forall X F,
  (forall P Q: X -> A,
    (ALL x:X, |>(P x >=> Q x) |--
        ALL x:X, F P x >=> F Q x)) ->
   HOcontractive F.
Proof.
  unfold HOcontractive.
  intros.
  apply allp_right; intro v.
  rewrite fash_andp.
  apply andp_right.
  specialize (H P Q).
  eapply derives_trans; [ | eapply derives_trans ; [ apply H |] ].
  apply allp_derives; intro x.
  apply @later_derives. apply fash_derives. apply andp_left1. auto.
  apply allp_left with v; auto.
  specialize (H Q P).
  eapply derives_trans; [ | eapply derives_trans ; [ apply H |] ].
  apply allp_derives; intro x.
  apply later_derives. apply fash_derives. apply andp_left2. auto.
  apply allp_left with v; auto.
Qed.

Lemma prove_HOcontractive {A} {NA: NatDed A}{IA: Indir A}{RA: RecIndir A} : forall X F,
  (forall (P Q: X -> A) (x: X),
    (ALL x:X, (|> P x <=> |> Q x) |-- F P x >=> F Q x)) ->
   HOcontractive F.
Proof.
  intros.
  unfold HOcontractive.
  intros.
  apply allp_right; intro v.
  rewrite fash_andp.
  apply andp_right.
  eapply derives_trans; [ | apply H].
  apply allp_derives; intro x.
  rewrite eqp_later. auto.
  eapply derives_trans; [ | apply H].
  apply allp_derives; intro x.
  rewrite eqp_later. rewrite andp_comm. auto.
Qed.

Lemma sub_sepcon {A} {NA: NatDed A}{IA: Indir A}{SA: SepLog A}{SI: SepIndir A} : forall G P P' Q Q',
  G |-- P >=> P' ->
  G |-- Q >=> Q' ->
  G |-- P * Q >=> P' * Q'.
Proof.
 intros.
 eapply derives_trans; [ | apply sub_sepcon'].
 apply andp_right; auto.
Qed.

Ltac sub_unfold := 
   match goal with 
    | |- _ |-- ?A _ >=> ?A _ => unfold A 
    | |- _ |-- ?A _ _ >=> ?A _ _ => unfold A 
    | |- _ |-- ?A _ _ _ >=> ?A _ _ _ => unfold A 
    | |- _ |-- ?A _ _ _ _ >=> ?A _ _ _ _ => unfold A 
    | |- _ |-- ?A _ _ _ _ _ >=> ?A _ _ _ _ _ => unfold A 
    | v: _ |- _ => destruct v
   end.

Hint Extern 2 (_ |-- _ >=> _) => sub_unfold : contractive.

Hint Resolve @prove_HOcontractive 
  @subp_allp @subp_imp @subp_refl @subp_exp @subp_andp @subp_orp @subp_subp 
  @sub_sepcon (* NOTE: This hint fails to work unless fully instantiated, for some reason;
                             so the client must re-do the sub_sepcon hint *)
  @allp_imp2_later_e1 @allp_imp2_later_e2 : contractive.

(*Lemma Rec_sub {A} {NA: NatDed A}{IA: Indir A}{RA: RecIndir A} : forall G
  (F   : A -> A -> A)
  (HF1 : forall X, contractive (F X))
  (HF2 : forall R P Q, P >=> Q |-- F P R >=> F Q R)
  (HF3 : forall P Q X, |>(P >=> Q) |-- F X P >=> F X Q),
  forall P Q,
    G |-- P >=> Q ->
    G |-- Rec (F P) >=> Rec (F Q).
*)

Lemma HORec_sub {A}  {NA: NatDed A}{IA: Indir A}{RA: RecIndir A} : forall G B
  (F : A -> (B -> A) -> B -> A)
  (HF1 : forall X, HOcontractive (F X))
  (HF2 : forall R a P Q, P >=> Q |-- F P R a >=> F Q R a)
  (HF3 : forall P Q X, ALL b:B, |>(P b >=> Q b) |-- ALL b:B, F X P b >=> F X Q b),
  forall P Q,
    G |-- P >=> Q ->
    G |-- ALL b:B, HORec (F P) b >=> HORec (F Q) b.
Proof.
  intros.
  apply @derives_trans with (P>=>Q); auto.
  clear G H.
  apply goedel_loeb.
  apply allp_right; intro b.
  rewrite HORec_fold_unfold by auto.
  pose proof (HORec_fold_unfold _ _ (HF1 P)). 
  pose proof (HORec_fold_unfold _ _ (HF1 Q)). 
  set (P' := HORec (F P)) in *.
  set (Q' := HORec (F Q)) in *.
  rewrite <- H.
  specialize (HF3 P' Q' P).
  rewrite later_allp.
 eapply derives_trans; [apply andp_derives ; [apply derives_refl | apply HF3] | ].
  specialize (HF2 Q' b P Q). rewrite <- H0 in HF2.
 rewrite <- H in *.
  apply subp_trans with  (F P Q' b).
  apply andp_left2.  apply allp_left with b; auto.
  apply andp_left1; auto.
Qed.

(*
Lemma Rec_contractive {A}  {NA: NatDed A}{IA: Indir A}{RA: RecIndir A}  : forall
  (F   : A -> A -> A)
  (HF1 : forall X, contractive (F X))
  (HF2 : forall R, contractive (fun X => F X R)),
  contractive (fun X => Rec (F X)).

Lemma Rec_nonexpansive {A} `{ageable A} : forall
  (F   : pred A -> pred A -> pred A)
  (HF1 : forall X, contractive (F X))
  (HF2 : forall R, nonexpansive (fun X => F X R)),
  nonexpansive (fun X => Rec (F X)).


Lemma HORec_contractive {A} `{ageable A} : forall B
  (F : pred A -> (B -> pred A) -> B -> pred A)
  (HF1 : forall X, HOcontractive (F X))
  (HF2 : forall R a, contractive (fun X => F X R a)),
  forall a, contractive (fun X => HORec (F X) a).

Lemma HORec_nonexpansive {A} `{ageable A} : forall B
  (F : pred A -> (B -> pred A) -> B -> pred A)
  (HF1 : forall X, HOcontractive (F X))
  (HF2 : forall R a, nonexpansive (fun X => F X R a)),
  forall a, nonexpansive (fun X => HORec (F X) a).
*)

(****** End contractiveness *****)

