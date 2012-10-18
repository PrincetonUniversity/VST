Require Import msl.base.
Require Import msl.sepalg.

Require Import Recdef.
Require Wellfounded.  (* Can't Import this, because that brings the identifier B into
           scope, which breaks things like `{ageable B}  in this file. 
          Stupid feature of Coq, that the B in `{ageable B} is not unambiguously a 
        binding occurrence of B.  *)
Delimit Scope pred with pred.
Local Open Scope pred.

Definition pred (A:Type) := A -> Prop.
Bind Scope pred with pred.

Definition derives (A:Type) (P Q:pred A) := forall a:A, P a -> Q a.
Implicit Arguments derives.

Lemma pred_ext : forall A (P Q:pred A),
  derives P Q -> derives Q P -> P = Q.
Proof.
  intros.
  extensionality a.
  apply prop_ext; intuition.
Qed.


Lemma derives_cut {A}  : forall Q P R : pred A,
  derives P Q ->
  derives Q R ->
  derives P R.
Proof.
  repeat intro; intuition.
Qed.

Definition prop {A: Type}  (P: Prop) : pred A := (fun _  => P).
Hint Unfold prop.

Definition TT {A}: pred A := prop True.
Definition FF  {A}: pred A := prop False.

Set Implicit Arguments.

Definition imp {A}  (P Q:pred A) :=
   fun a:A => P a -> Q a.
Definition orp {A} (P Q:pred A) :=
   fun a:A => P a \/ Q a.
Definition andp {A} (P Q:pred A) :=
   fun a:A => P a /\ Q a.

Definition allp {A B: Type} (f: B -> pred A) : pred A
  := fun a => forall b, f b a.
Definition exp {A B: Type} (f: B -> pred A) : pred A
  := fun a => exists b, f b a.

Notation "'emp'" := identity.

Definition sepcon {A} {JA: Join A}(p q:pred A) := fun z:A =>
  exists x:A, exists y:A, join x y z /\ p x /\ q y.
Definition wand {A}  {JA: Join A}  (p q:pred A) := fun y =>
  forall x z, join x y z -> p x -> q z.

Notation "P '|--' Q" := (derives P Q) (at level 80, no associativity).
Notation "'EX'  x ':' T ',' P " := (exp (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
Notation "'ALL'  x ':' T  ',' P " := (allp (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
Infix "||" := orp (at level 50, left associativity) : pred.
Infix "&&" := andp (at level 40, left associativity) : pred.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : pred.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : pred.
Notation "P '*' Q" := (sepcon P Q) : pred.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : pred.
Notation "'!!' e" := (prop e) (at level 25) : pred.

Definition precise {A}  {JA: Join A}{PA: Perm_alg A}  (P: pred A) : Prop :=
     forall w w1 w2, P w1 -> P w2 -> join_sub w1 w -> join_sub w2 w -> w1=w2.

Definition precise2  {A} {JA: Join A}{PA: Perm_alg A}  (P: pred A) : Prop :=
     forall Q R, P * (Q && R) = (P * Q) && (P * R).

Lemma precise_eq {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
     precise = 
                 fun P : pred A => forall Q R, P * (Q && R) = (P * Q) && (P * R).
Proof.
extensionality P.
unfold precise.
apply prop_ext; split; intros.
extensionality w.
apply prop_ext; split; intros.
destruct H0 as [phi1 [phi2 [? [? [? ?]]]]].
split; exists phi1; exists phi2; auto.
destruct H0 as [[phi1a [phi2a [? [? ?]]]] [phi1b [phi2b [? [? ?]]]]].
specialize (H w _ _ H1 H4).
spec H.
econstructor; eauto.
spec H.
econstructor; eauto.
subst phi1b.
generalize (join_canc (join_comm H0) (join_comm H3)).
intro; subst phi2b.
exists phi1a; exists phi2a; split; auto.
split; auto.
split; auto.
rename w1 into w1a.
rename w2 into w1b.
destruct H2 as [w2a ?].
destruct H3 as [w2b ?].
pose (fa x := x=w2a).
pose (fb x := x=w2b).
assert (((P * fa) && (P * fb)) w).
split; do 2 econstructor; repeat split; eauto.
rewrite <- H in H4.
destruct H4 as [w1 [w2 [? [? [? ?]]]]].
unfold fa,fb in *.
subst.
generalize (join_canc H2 H4); intro.
subst w1a w2b.
eapply join_canc; eauto.
Qed.

Lemma derives_precise {A} {JA: Join A}{PA: Perm_alg A}:
  forall P Q, (P |-- Q) -> precise Q -> precise P.
Proof.
intros; intro; intros; eauto.
Qed.

Lemma prop_true_and:
  forall (P: Prop) A (Q: pred A), P -> (!! P && Q = Q).
Proof.
intros. unfold prop, andp; 
extensionality w; apply prop_ext; split; intuition.
Qed.

Lemma prop_andp_e {A}:  forall P Q (w:A), (!! P && Q) w -> P /\ Q w.
Proof.
intuition; destruct H; auto.
Qed.

Lemma prop_andp_i {A}:  forall P Q (w:A), P /\ Q w -> (!! P && Q) w.
Proof.
intuition.
split; auto.
Qed.

Lemma derives_trans {A}:  forall (P Q R: pred A), P |-- Q -> Q |-- R -> P |-- R.
Proof.
firstorder.
Qed.

Lemma and_i {A}: forall (P Q R: pred A),
    P |-- Q -> P |-- R -> P |-- Q && R.
Proof. intuition.
intros w ?.
split; eauto.
Qed.

Lemma andp_derives {A}  :
  forall P Q P' Q': pred A, P |-- P' -> Q |-- Q' -> P && Q |-- P' && Q'.
Proof.
intros.
intros w [? ?]; split; auto.
Qed.

Lemma sepcon_assoc {A} {JA: Join A}{PA: Perm_alg A}: 
  forall p q r, (((p * q) * r) = (p * (q * r))).
Proof.
pose proof I.
intros.
extensionality w; apply prop_ext; split; intros.
destruct H0 as [w12 [w3 [? [[w1 [w2 [? [? ?]]]] ?]]]].
destruct (join_assoc H1 H0) as [w23 [? ?]].
exists w1; exists w23; repeat split; auto.
exists w2; exists w3; split; auto.
destruct H0 as [w1 [w23 [? [? [w2 [w3 [? [? ?]]]]]]]].
 destruct (join_assoc (join_comm H2) (join_comm H0)) as [w12 [? ?]].
exists w12; exists w3; repeat split; auto.
exists w1; exists w2; repeat split; auto.
Qed.

Lemma sepcon_comm {A} {JA: Join A}{PA: Perm_alg A}:  forall (P Q: pred A) , P * Q = Q * P.
Proof.
intros.
extensionality w; apply prop_ext; split; intros;
(destruct H as [w1 [w2 [? [? ?]]]]; exists w2; exists w1; split ; [apply join_comm; auto | split; auto]).
Qed.

Lemma sepcon_emp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall P, (P * emp) = P.
Proof.
intros.
extensionality w; apply prop_ext; split; intros.
destruct H as [w1 [w2 [? [? ?]]]].
generalize (identity_unit (a:=w1) H1); intro.
spec H2.
econstructor; eauto.
unfold unit_for in H2.
generalize (join_eq H (join_comm H2)).
intros; subst; auto.
destruct (join_ex_identities w) as [e [? ?]].
exists w; exists e; repeat split; auto.
apply join_comm.
apply identity_unit; auto.
Qed.

Lemma emp_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
    forall P, (emp*P) = P.
Proof. intros. rewrite sepcon_comm; rewrite sepcon_emp; auto. Qed.

Lemma precise_emp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
     precise emp.
Proof.
intros.
rewrite precise_eq.
intros.
repeat rewrite emp_sepcon.
auto.
Qed.

Definition exactly {A} (x: A) : pred A := fun w => w=x.

Lemma join_exactly {A} {JA: Join A}{PA: Perm_alg A}:
  forall w1 w2 w3, join w1 w2 w3 -> exactly w1 * exactly w2 = exactly w3.
Proof.
intros.
unfold exactly.
extensionality w.
apply prop_ext; split; intros.
destruct H0 as [? [? [? [? ?]]]].
subst. eapply join_eq; eauto.
subst w3.
exists w1; exists w2; split; auto.
Qed.     


Lemma exists_and1 {A: Type} : forall {T: Type} (P: T -> pred A) (Q: pred A),
                   exp P && Q = EX x:T, P x && Q.
Proof.
intros.
extensionality w.
apply prop_ext; split; intros.
destruct H as [[x ?] ?].
exists x; split; auto.
destruct H as [x [? ?]].
split; auto.
exists x; auto.
Qed.

Lemma andp_comm {A: Type}: forall (P Q: pred A), P && Q = Q && P.
Proof.
intros.
extensionality w.
unfold andp; 
apply prop_ext; split; intuition.
Qed.

Lemma andp_assoc {A}: forall (P Q R: pred A), 
                 ((P && Q) && R = P && (Q && R)).
Proof.
intros.
extensionality w.
unfold andp.
apply prop_ext; intuition.
Qed.

Lemma True_andp_eq {A}:
  forall (P: Prop) (Q: pred A), P -> (!!P && Q)%pred = Q.
intros.
extensionality w; apply prop_ext; split; unfold prop, andp; simpl; intros; intuition.
Qed.

Lemma TT_i  {A} : forall w: A,  TT w.
Proof.
unfold TT, prop; simpl; auto.
Qed.

Hint Resolve @TT_i.

Lemma TT_and {A}: forall (Q: pred A), TT && Q = Q.
intros; unfold andp,  TT, prop; extensionality w.
apply prop_ext; intuition.
Qed.


Lemma andp_TT {A}: forall (P: pred A), P && TT = P.
Proof.
intros.
extensionality w; apply prop_ext; split; intros.
destruct H; auto.
split; auto.
Qed.

Lemma emp_wand {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
    forall P, emp -* P = P.
Proof.
intros.
extensionality w; apply prop_ext; split; intros.
destruct (join_ex_units w) as [e ?].
eapply H; eauto.
eapply unit_identity; eauto.
intro; intros.
replace z with w; auto.
Qed.

Lemma wand_derives {A} {JA: Join A}{PA: Perm_alg A}:
  forall P P' Q Q',  P' |-- P -> Q |-- Q' -> P -* Q |-- P' -* Q'.
Proof.
intros.
intros w ?.
intro; intros.
eauto.
Qed.

Lemma TT_sepcon_TT {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: TT * TT = TT.
Proof.
intros.
extensionality w; apply prop_ext; split; intros; auto.
destruct (join_ex_units w).
exists x; exists w; split; auto.
Qed.

Definition ewand {A} {JA: Join A} (P Q: pred A) : pred A :=
  fun w => exists w1, exists w2, join w1 w w2 /\ P w1 /\ Q w2.

(* Notation "P '-o' Q" := (ewand P Q) (at level 60, right associativity). *)

Lemma emp_ewand {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:  forall P, ewand emp P = P.
Proof.
intros.
extensionality w; apply prop_ext; split; intros.
destruct H as [w1 [w2 [? [? ?]]]].
replace w with w2; auto.
eapply join_eq; eauto.
eapply identity_unit; eauto.
destruct (join_ex_units w) as [e ?].
exists e; exists w.
split; auto. split; auto.
eapply unit_identity; eauto.
Qed.


Lemma exists_sepcon1 {A} {JA: Join A}{PA: Perm_alg A}:
  forall T (P: T ->  pred A) Q,  exp P * Q = exp (fun x => P x * Q).
Proof.
intros.
extensionality w.
apply prop_ext; split; intros.
destruct H as [w1 [w2 [? [[x ?] ?]]]].
exists x; exists w1; exists w2; split; auto.
destruct H as [x [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; split; auto.
split; auto.
exists x; auto.
Qed.

Lemma derives_refl {A: Type}:
  forall (P: pred A), (P |-- P).
Proof. firstorder.
Qed.

Hint Resolve @derives_refl.

Lemma derives_TT {A}: forall (P: pred A), P |-- TT.
Proof.
intros.
intros ? ?; auto.
Qed.
Hint Resolve @derives_TT.

Lemma sepcon_derives {A} {JA: Join A}{PA: Perm_alg A}:
  forall p q p' q', (p |-- p') -> (q |-- q') -> (p * q |-- p' * q').
Proof.
intros.
do 2 intro.
destruct H1 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; repeat split ;auto.
Qed.

Lemma derives_e {A: Type}: forall p q (st: A),
      (p |-- q) -> p st -> q st.
Proof.
auto.
Qed.

Lemma exp_derives {A} : 
       forall B (P: B -> pred A) Q , (forall x:B, P x |-- Q x) -> (exp P |-- exp Q).
Proof.
intros.
intros w [b ?].
exists b; eapply H; eauto.
Qed.


Lemma unmodus_wand {A}  {JA: Join A}{PA: Perm_alg A}:
 forall P Q R, Q = P * R ->  Q |-- P * (P -* Q).
Proof.
intros.
subst.
apply sepcon_derives; auto.
intros ?w ?; intro; intros.
exists x; exists w; split; auto.
Qed.

Definition superprecise {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} (P: pred A) :=
   forall w1 w2, P w1 -> P w2 -> comparable w1 w2 -> w1=w2.

Lemma modus_ewand {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} :  forall P Q, superprecise P -> P * (ewand P Q) |-- Q.
Proof.
pose proof I.
intros.
intros w ?.
destruct H1 as [w1 [w2 [? [? ?]]]].
unfold ewand in H3.
destruct H3 as [w1' [w3 [? [? ?]]]].
assert (w1'=w1).
  apply H0; auto. 
  apply comparable_trans with w2. eapply join_comparable2; eauto.
  apply comparable_sym.  eapply join_comparable2; eauto.
  subst.
replace w with w3; auto.
eapply join_eq; eauto.
Qed.

Lemma exists_expand_sepcon {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
 forall B (p: B -> pred A) q, (exp p * q)%pred = (exp (fun x => p x * q))%pred.
Proof.
intros; extensionality w; apply prop_ext; split; intros.
destruct H as [? [? [? [? ?]]]].
destruct H0.
exists x1; exists x; exists x0; split; auto.
destruct H as [? [? [? [? [? ?]]]]].
exists x0; exists x1; split; auto.
split; auto.
exists x; auto.
Qed.

Lemma exists_expand_sepcon' {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
 forall B p (q: B -> pred A), (p * exp q)%pred = (exp (fun x => p * q x))%pred.
Proof.
intros; extensionality w; apply prop_ext; split; intros.
destruct H as [? [? [? [? ?]]]].
destruct H1.
exists x1; exists x; exists x0; split; auto.
destruct H as [? [? [? [? [? ?]]]]].
exists x0; exists x1; split; auto.
split; auto.
exists x; auto.
Qed.

Lemma exists_expand_and {A}  {JA: Join A}:
 forall B (p: B -> pred A) q, (exp p && q)%pred = (exp (fun x => p x && q))%pred.
Proof.
intros; extensionality w; apply prop_ext; split; intros.
destruct H.
destruct H.
exists x; split; auto.
destruct H. destruct H.
split; auto.
exists x; auto.
Qed.

Lemma exists_expand_and' {A} {JA: Join A}:
 forall B p (q: B -> pred A), (p && exp q)%pred = (exp (fun x => p && q x))%pred.
Proof.
intros; extensionality w; apply prop_ext; split; intros.
destruct H.
destruct H0.
exists x; split; auto.
destruct H. destruct H.
split; auto.
exists x; auto.
Qed.

Lemma allp_derives_right {A} : forall B p (q: B -> pred A),
  ((p |-- allp q) <-> (forall x, p |-- q x)).
Proof.
intros.
split; intros.
eapply derives_trans; eauto.
intros ? ?. apply H0.
intros ? ? ?.
eapply (H b).
auto.
Qed.

Lemma wand_exists {A} {JA: Join A}{PA: Perm_alg A}:
   forall B P Q,  (EX x: B, P -* Q x) |-- (P -* EX x : B, Q x).
Proof.
pose proof I.
intros.
intros w ?.
destruct H0 as [x ?].
intros ?w ?w ? ?.
spec H0 w0 w1 H1 H2.
exists x; auto.
Qed.

Lemma modus_wand {A} {JA: Join A}{PA: Perm_alg A}:
  forall P Q,  P * (P -* Q) |-- Q.
Proof.
intros.
intros w  [?w [?w [? [? ?]]]].
eapply H1; eauto.
Qed.

Lemma distrib_sepcon_andp {A} {JA: Join A}{PA: Perm_alg A}:
  forall P Q R, P * (Q && R) |-- (P * Q) && (P * R).
Proof.
intros. intros w [w1 [w2 [? [? ?]]]].
destruct H1.
split; exists w1; exists w2; split; auto.
Qed.

Lemma andp_r {A: Type} : forall (P Q R: pred A), P |-- Q -> P |-- R -> P |-- Q && R.
Proof.
intros.
intros w ?; split; auto.
Qed.

Definition list_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} : list (pred A) -> pred A := fold_right sepcon emp.

Lemma sepcon_andp_prop {A} {JA: Join A}{PA: Perm_alg A}: forall P Q R, P * (!!Q && R) = !!Q && (P * R).
Proof.
intros.
extensionality w; apply prop_ext; split; intros.
destruct H as [w1 [w2 [? [? [? ?]]]]].
split. apply H1.
exists w1; exists w2; split; [|split]; auto.
destruct H.
destruct H0 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; repeat split; auto.
Qed.

Require Import msl.cross_split.

Lemma exactly_i {A} : forall x: A, exactly x x.
Proof. intros. reflexivity.
Qed.
Hint Resolve @exactly_i.

Lemma superprecise_exactly {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall x, superprecise (exactly x).
Proof.
unfold exactly, superprecise; intros.
subst; auto.
Qed.
Hint Resolve @superprecise_exactly.

Lemma find_overlap {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
     Cross_alg A ->
     forall S P Q R, (S * P) && (Q * R) |-- 
                          EX SQ:_, EX SR:_, EX PQ:_, EX PR:_, 
                            (((SQ* SR) && S)*((PQ* PR) && P)) &&
                            (((SQ* PQ) && Q)*((SR* PR) && R)) &&
                            !! (superprecise SQ /\ superprecise SR /\ superprecise PQ /\ superprecise PR).
Proof.
pose proof I.
intros.
intros w [[w1 [w2 [? [? ?]]]] [w3 [w4 [? [? ?]]]]].
destruct (X _ _ _ _ _ H0 H3) as [[[[wa wb] wc] wd] [? [? [? ?]]]].
exists (exactly wa); exists (exactly wb); exists (exactly wc); exists (exactly wd).
repeat split; auto.
exists w1; exists w2; split; [|split]; auto; split; auto.
exists wa; exists wb; split; [|split]; auto.
exists wc; exists wd; split; [|split]; auto.
exists w3; exists w4; split; [|split]; auto; split; auto.
exists wa; exists wc; split; [|split]; auto.
exists wb; exists wd; split; [|split]; auto.
Qed.

Lemma modus_ponens {A} : forall (X P Q:pred A),
  X |-- P ->
  X |-- (P --> Q) ->
  X |-- Q.
Proof.
  unfold derives, imp; simpl; intuition eauto.
Qed.

Lemma and_intro {A}  : forall (X P Q:pred A),
  X |-- P ->
  X |-- Q ->
  X |-- P && Q.
Proof.
  unfold derives, imp, andp; simpl; intuition.
Qed.

Lemma and1 {A}  : forall (X P Q:pred A),
  X |-- P && Q --> P.
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma and2 {A}  : forall (X P Q:pred A),
  X |-- P && Q --> Q.
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma and3 {A}  : forall (X P Q R:pred A),
  X |-- (P --> Q) --> (P --> R) --> (P --> Q && R).
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma or1 {A}  : forall (X P Q:pred A),
  X |-- P --> P || Q.
Proof.
  unfold derives, imp, orp; simpl; intuition.
Qed.

Lemma or2 {A}  : forall (X P Q:pred A),
  X |-- Q --> P || Q.
Proof.
  unfold derives, imp, orp; simpl; intuition.
Qed.

Lemma or3 {A}  : forall (X P Q R:pred A),
  X |-- (P --> R) --> (Q --> R) --> (P || Q --> R).
Proof.
  unfold derives, imp, orp; simpl; intuition eauto.
Qed.

Lemma TTrule {A}  : forall X (P: pred A),
  X |-- P --> TT.
Proof.
  unfold derives, imp, TT; simpl; intuition.
Qed.

Lemma FFrule {A}  : forall X (P: pred A),
  X |-- FF --> P.
Proof.
  unfold derives, imp, FF; simpl; intuition.
hnf in H0; contradiction.
Qed.

Lemma distribution {A}  : forall (X P Q R:pred A),
  X |-- P && (Q || R) --> (P && Q) || (P && R).
Proof.
  unfold derives, imp, orp, andp; simpl; intuition.
Qed.

Lemma wand_sepcon_adjoint {A} {JA: Join A}{PA: Perm_alg A} : forall (P Q R:pred A),
  ((P * Q) |-- R) = (P |-- (Q -* R)).
Proof.
  intros. apply prop_ext.
  split; intros.
  hnf; intros; simpl; intros.
  hnf; intros.
  apply H.
  exists a; exists x; split; auto.
  hnf; intros.
  destruct H0 as [w [v [? [? ?]]]].
  eapply H; eauto.
Qed.

Lemma ewand_sepcon {A} {JA: Join A}{PA: Perm_alg A}: forall P Q R, 
      (ewand (P * Q) R = ewand P (ewand Q R))%pred.
Proof.
intros; apply pred_ext; intros w ?.
destruct H as [w1 [w2 [? [? ?]]]].
destruct H0 as [w3 [w4 [? [? ?]]]].
exists w3.
destruct (join_assoc (join_comm H0) H) as [wf [? ?]].
exists wf.
split; [|split]; auto.
exists w4. exists w2. split; auto. 
destruct H as [w1 [w2 [? [? ?]]]].
destruct H1 as [w3 [w4 [? [? ?]]]].
destruct (join_assoc (join_comm H) (join_comm H1)) as [wf [? ?]].
exists wf. exists w4. split; [|split]; auto.
exists w1; exists w3; split; auto.
Qed.


Lemma andp_right {A}  : forall (X P Q:pred A),
  X |-- P ->
  X |-- Q ->
  X |-- P && Q.
Proof.
  unfold derives, imp, andp; simpl; intuition.
Qed.


Lemma andp_left1{A}: forall P Q R: pred A,  P |-- R -> P && Q |-- R.
Proof. repeat intro. destruct H0; auto.
Qed.

Lemma andp_left2{A}: forall P Q R: pred A,  Q |-- R -> P && Q |-- R.
Proof. repeat intro. destruct H0; auto.
Qed.


Lemma orp_left{A}: forall P Q R: pred A,  P |-- R -> Q |-- R -> P || Q |-- R.
Proof. repeat intro. destruct H1; auto.
Qed.

Lemma orp_right1{A}: forall P Q R: pred A,  P |-- Q -> P |-- Q || R. 
Proof. repeat intro. left; auto.
Qed.

Lemma orp_right2{A}: forall P Q R: pred A,  P |-- R -> P |-- Q || R. 
Proof. repeat intro. right; auto.
Qed.

Lemma exp_right: 
  forall {B A: Type}(x:B) p (q: B -> pred A),
    p |-- q x ->
    p |-- exp q.
Proof.
intros.
eapply derives_trans; try apply H.
intros w ?; exists x; auto.
Qed.

Lemma exp_left:
  forall {B A: Type}(p: B -> pred A) q,
  (forall x, p x |-- q) ->
   exp p |-- q.
Proof.
intros.
intros w [x' ?].
eapply H; eauto.
Qed.


Lemma allp_right {B A: Type}:
  forall (P: pred A) (Q: B -> pred A),
  (forall v, P |-- Q v) ->
   P |-- allp Q.
Proof.
 intros. intros w ? v; apply (H v); auto.
Qed.

Lemma allp_left {B}{A}: 
   forall (P: B -> pred A) x Q, P x |-- Q -> allp P |-- Q.
 Proof.
   intros. intros ? ?. apply H. apply H0.
Qed.

Lemma imp_andp_adjoint {A}  : forall (P Q R:pred A),
  (P && Q) |-- R <-> P |-- (Q --> R).
Proof.
  split; intros.
  hnf; intros; simpl; intros.
  intro; intros. apply H. split; auto.
  intro; intros. destruct H0. apply H; auto.
Qed.


Lemma exp_andp1 {A} :
 forall B (p: B -> pred A) q, (exp p && q)%pred = (exp (fun x => p x && q))%pred.
Proof.
intros; apply pred_ext; intros w ?.
destruct H as [[x ?] ?].
exists x; split; auto.
destruct H as [x [? ?]]; split; auto. exists x; auto.
Qed.


Lemma exp_sepcon1 {A}  {JA: Join A}{PA: Perm_alg A}:
  forall T (P: T ->  pred A) Q,  (exp P * Q = exp (fun x => P x * Q))%pred.
Proof.
intros.
apply pred_ext; intros ? ?.
destruct H as [w1 [w2 [? [[x ?] ?]]]].
exists x; exists w1; exists w2; split; auto.
destruct H as [x [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; split; auto.
split; auto.
exists x; auto.
Qed.


Definition pure {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}
     (P: pred A) : Prop :=
   P |-- emp.

Lemma sepcon_pure_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
 forall P Q, pure P -> pure Q -> ((P * Q) = (P && Q)).
Proof.
intros.
apply pred_ext; intros w ?. 
destruct H1 as [w1 [w2 [? [? ?]]]].
unfold pure in *.
assert (unit_for w1 w2). apply H in H2; simpl in H2; 
apply identity_unit; auto. exists w; auto.
unfold unit_for in H4.
assert (w2=w) by (apply (join_eq H4 H1)).
subst w2.
assert (join w w1 w1).
apply identity_unit; apply H0 in H3; simpl in H3; auto. exists w; auto.
assert (w1=w) by (apply (join_eq H5 (join_comm H1))).
subst w1.
split; auto.
destruct H1.
exists w; exists w; split; [|split]; auto.
apply H in H1.
clear dependent P. clear dependent Q.
pose proof (core_unit w); unfold unit_for in *.
pose proof (H1 _ _ (join_comm H)).
rewrite H0 in H; auto.
Qed.

Lemma pure_sepcon_TT_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall P Q, pure P -> (P * TT) && Q = (P*Q).
Proof.
 pose proof I.
intros.
apply pred_ext.
intros w [? ?].
destruct H1 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; split; [|split]; auto.
apply join_unit1_e in H1; auto.
subst; auto.
apply andp_right.
apply sepcon_derives; auto.
intros w [w1 [w2 [? [? ?]]]].
apply join_unit1_e in H1; auto.
subst; auto.
Qed.

