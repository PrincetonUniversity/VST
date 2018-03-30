Require Import VST.msl.msl_standard.
Require Import VST.msl.Coqlib2.
Set Implicit Arguments.

Inductive fold_rel (A: Type) (f: A -> A -> A -> Prop):  A -> list A -> A -> Prop :=
| fold_rel_nil: forall w, fold_rel f w nil w
| fold_rel_cons: forall a l w w1 w2,
            f w a w1 ->
            fold_rel f w1 l w2 ->
            fold_rel f w (a::l) w2.

Inductive list_forall2 {A B} (P: A -> B -> Prop): list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 P nil nil
  | list_forall2_cons:
      forall a1 al b1 bl,
      P a1 b1 ->
      list_forall2 P al bl ->
      list_forall2 P (a1 :: al) (b1 :: bl).

Fixpoint replace (A: Type) (l: list A) (n:nat) (new: A) {struct n} : option (list A) :=
  match (l, n) with
    | (nil, n) => None
    | (x :: xs, O) => Some (new :: xs)
    | (x :: xs, S n) =>
      match (replace xs n new) with
        |  None => None
        |  Some xs => Some (x :: xs)
      end
  end.



Definition list_join {A} {JA: Join A}: A -> list A -> A -> Prop :=
   fold_rel join.

Lemma list_join_assoc1 {A} {JA: Join A}{PA: Perm_alg A}:
 forall {a b cl d e},
   join a b d -> list_join d cl e ->
  exists f, list_join b cl f /\ join a f e.
Proof.
intros.
revert a b H.
induction H0; intros.
exists b. split; auto. constructor.
destruct (join_assoc H1 H) as [ba [? ?]].
destruct (IHfold_rel _ _ H3) as [f [? ?]]; clear IHfold_rel.
exists f; split; auto.
econstructor; eauto.
Qed.

Lemma list_join_assoc2 {A}  {JA: Join A}{PA: Perm_alg A}:
  forall {a b: A} {cl e f},
   list_join b cl f -> join a f e ->
   exists d,  join a b d /\ list_join d cl e.
Proof.
do 3 intro; revert a b; induction cl; intros; inv H.
exists e; split; auto; constructor.
destruct (IHcl _ _ _ _ H6 H0) as [d [? ?]].
destruct (join_assoc (join_comm H4) (join_comm H)) as [g [? ?]].
exists g; split; auto.
constructor 2 with d; auto.
Qed.

Lemma list_join_app {A} {JA: Join A}:
  forall {a: A} {bl c dl e},
   list_join a bl c -> list_join c dl e -> list_join a (bl++dl) e.
Proof.
intros a bl; revert a; induction bl; intros.
inv H.
simpl.
auto.
inv H.
rewrite <- app_comm_cons.
econstructor 2.
apply H4.
eapply IHbl.
apply H6.
auto.
Qed.

Lemma list_join_unapp {A}  {JA: Join A}:
  forall {a:A}  {bl dl e},
  list_join a (bl++dl) e -> exists c, list_join a bl c /\ list_join c dl e.
Proof.
intros a bl; revert a; induction bl; intros.
simpl in H. exists a; split; auto. constructor.
rewrite <- app_comm_cons in H.
inv H.
destruct (IHbl _ _ _ H5) as [c [? ?]]. clear IHbl.
exists c.
split; auto.
econstructor 2; eauto.
Qed.

Lemma list_join_1 {A} {JA: Join A}:
  forall a b c: A, join a b c = list_join a (b::nil) c.
Proof.
intros; apply prop_ext; split; intros.
econstructor 2; eauto.
constructor.
inv H.
inv H5.
auto.
Qed.

Definition age1_list {A} `{ageable A} := list_forall2 age.

Lemma age1_list_join {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall l (phi phi' phi2: A),
        age phi phi' ->
        list_join phi l phi2 ->
        exists l', exists phi2', age1_list l l' /\ age phi2 phi2' /\ list_join phi' l' phi2'.
Proof.
induction l; intros; inv H0.
exists (@nil A).
exists phi'.
repeat split; auto; constructor.
rename w1 into phi1.
destruct (age1_join _ H4 H) as [a' [phi1' [? [? ?]]]].
specialize ( IHl phi1 phi1' phi2 H2 H6).
destruct IHl as [l' [phi2' [? [? ?]]]].
exists (a' :: l').
exists phi2'.
repeat split; auto; econstructor 2; eauto.
Qed.

Lemma age1_list_join2 {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall (l: list A) phi phi2 phi2',  age1 phi2 = Some phi2' -> list_join phi l phi2 ->
        exists l', exists phi',  age1 phi = Some phi' /\ age1_list l l' /\ list_join phi' l' phi2'.
Proof.
induction l; intros; inv H0.
exists (@nil A).
exists phi2'.
repeat split; auto; constructor.
rename w1 into phi1.
destruct (IHl phi1 phi2 phi2' H H6) as [l' [phi1' [? [? ?]]]].
destruct (age1_join2 _ H4 H0) as [phi' [a' [? [? ?]]]].
exists (a'::l'). exists phi'.
repeat split; auto; econstructor 2; eauto.
Qed.

Lemma list_join_split_nth {A}{JA: Join A}{PA: Perm_alg A}:
 forall n (l: list A) phin phi phia phib phi2,
  nth_error l n = Some phin -> list_join phi l phi2 -> join phib phia phin ->
           exists phic, exists l',
                 replace l n phib = Some l' /\ join phi phia phic /\ list_join phic l' phi2.
Proof.
induction n; intros.
inv H.
destruct l.
discriminate.
inv H3.
inv H0.
simpl.
destruct (join_assoc H1 (join_comm H4))
      as [f [? ?]].
exists f; exists (phib::l).
repeat split; auto.
econstructor 2; eauto.
simpl in H.
destruct l.
inv H.
inv H0.
destruct (IHn _ _ _ _ _ _ H H7 H1) as [phic [l' [? [? ?]]]].
simpl. rewrite H0.
destruct (join_assoc (join_comm H5) H2) as [f [? ?]].
exists f; exists (a::l'); repeat split; auto.
econstructor 2; eauto.
Qed.

Lemma list_join_join_nth {A} {JA: Join A}{PA: Perm_alg A}:
 forall n (l: list A) phin phi phia phib phi2,
  nth_error l n = Some phin -> list_join phi l phi2 -> join phi2 phia phib ->
           exists phic, exists l',
                 join phin phia phic /\ replace l n phic = Some l' /\ list_join phi l' phib.
Proof.
induction n; intros.
inv H.
destruct l; try discriminate.
inv H0.
inv H3.
simpl.
destruct (list_join_assoc2 H7 (join_comm H1)) as [f [? ?]].
destruct (join_assoc H5 (join_comm H)) as [g [? ?]].
exists g; exists (g::l); repeat split; auto.
econstructor 2; eauto.
destruct l; simpl in H.
inv H.
inv H0.
simpl.
destruct (IHn _ _ _ _ _ _ H H7 H1) as [phic  [l' [? [? ?]]]].
exists phic. rewrite H2. exists (a::l').
repeat split; auto.
econstructor 2; eauto.
Qed.

(*****************************)

Lemma list_join_comparable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall (phi1: A) l phi2, list_join phi1 l phi2 -> comparable phi1 phi2.
Proof.
  intros; revert phi1 phi2 H; induction l; simpl; intros; inv H.
  apply comparable_refl.
  rename w1 into phi0.
  apply comparable_trans with phi0.
  apply join_comparable with a; auto.
  auto.
Qed.

Lemma join_comparable'  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2 phi3: A, join phi1 phi2 phi3 -> comparable phi2 phi3.
Proof. intros; apply join_comparable with phi1; apply join_comm; auto. Qed.

Lemma join_comparable2'  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2 phi3: A, join phi1 phi2 phi3 -> comparable phi2 phi1.
Proof. intros; apply comparable_sym; eapply join_comparable2; eauto. Qed.

Lemma list_join_comparable'  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall (phi1: A) l phi2, list_join phi1 l phi2 -> comparable phi2 phi1.
Proof. intros; apply comparable_sym; eapply list_join_comparable; eauto. Qed.

Lemma join_comparable''  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2 phi3: A, join phi1 phi2 phi3 -> comparable phi3 phi2.
Proof. intros; apply comparable_sym; eapply join_comparable'; eauto. Qed.

Lemma join_comparable'''  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2 phi3: A, join phi1 phi2 phi3 -> comparable phi3 phi1.
Proof. intros; apply comparable_sym; eapply join_comparable; eauto. Qed.

Lemma joins_comparable  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2: A, joins phi1 phi2 -> comparable phi1 phi2.
Proof.
  unfold joins; intros.
  destruct H as [phi3 ?].
  eapply join_comparable2; eauto.
Qed.

Lemma joins_comparable2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
     forall phi1 phi2: A, joins phi2 phi1 -> comparable phi1 phi2.
Proof.
unfold joins; intros.
destruct H as [phi3 ?].
apply comparable_sym.
eapply join_comparable2; eauto.
Qed.

Lemma join_sub_comparable  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2: A, join_sub phi1 phi2 -> comparable phi1 phi2.
Proof.
unfold joins; intros.
destruct H as [phi3 ?].
eapply join_comparable; eauto.
Qed.

Lemma join_sub_comparable2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
     forall phi1 phi2: A, join_sub phi2 phi1 -> comparable phi1 phi2.
Proof.
unfold joins; intros.
destruct H as [phi3 ?].
apply comparable_sym.
eapply join_comparable; eauto.
Qed.

Lemma eq_comparable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
   forall phi1 phi2: A, phi1=phi2 -> comparable phi1 phi2.
Proof.
intros; subst; apply comparable_refl.
Qed.

Lemma eq_comparable2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
   forall phi1 phi2: A, phi2=phi1 -> comparable phi1 phi2.
Proof.
intros; subst; apply comparable_refl.
Qed.

Lemma ageN_join {A}  {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall n (w1 w2 w3 w1': A),
   join w1 w2 w3 ->
      ageN n w1 = Some w1' ->
      exists w2', exists w3',
        ageN n w2 = Some w2' /\ ageN n w3 = Some w3' /\ join w1' w2' w3'.
Proof.
unfold ageN in *.
induction n; intros; simpl in *.
exists w2; exists w3; repeat split; auto.
inv H0; auto.
case_eq (age1 w1); intros; rewrite H1 in H0; try discriminate.
destruct (age1_join _ H H1) as [w2' [w3' [? [? ?]]]].
destruct (IHn _ _ _ _ H2 H0) as [w2'' [w3'' [? [? ?]]]].
clear IHn.
exists w2''; exists w3''. rewrite H3; rewrite H4.
repeat split; auto.
Qed.

Lemma ageN_join2 {A}  {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall n (w1 w2 w3 w3': A),
   join w1 w2 w3 ->
      ageN n w3 = Some w3' ->
      exists w1', exists w2',
        ageN n w1 = Some w1' /\ ageN n w2 = Some w2' /\ join w1' w2' w3'.
Proof.
unfold ageN in *.
induction n; intros; simpl in *.
exists w1; exists w2; repeat split; auto.
inv H0; auto.
case_eq (age1 w3); intros; rewrite H1 in H0; try discriminate.
destruct (age1_join2 _ H H1) as [w1' [w2' [? [? ?]]]].
destruct (IHn _ _ _ _ H2 H0) as [w1'' [w2'' [? [? ?]]]].
clear IHn.
exists w1''; exists w2''. rewrite H3; rewrite H4.
repeat split; auto.
Qed.

Lemma ageN_comparable {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall n (w1 w2 w1' w2': A),
        ageN n w1 = Some w1' -> ageN n w2 = Some w2' -> comparable w1 w2 -> comparable w1' w2'.
Proof.
unfold ageN in *.
induction n; intros; simpl in *.
inv H; inv H0; auto.
revert H H0; case_eq (age1 w1); case_eq (age1 w2); intros; try discriminate.
eapply IHn; eauto.
eapply age_comparable; eauto.
Qed.

Lemma join_unage  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall (phi3 phi1' phi2' phi3': A),
    age1 phi3 = Some phi3' ->
    join phi1' phi2' phi3' ->
    exists phi1, exists phi2, join phi1 phi2 phi3 /\
      age1 phi1 = Some phi1' /\ age1 phi2 = Some phi2'.
Proof.
  intros.
  apply (unage_join2 _ H0 H).
Qed.

Lemma join_unage'  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
    forall phi1 phi1' phi2' phi3' : A,
      age1 phi1 = Some phi1' ->
      join phi1' phi2' phi3' ->
      exists phi2, exists phi3, join phi1 phi2 phi3 /\
        age1 phi2 = Some phi2' /\ age1 phi3 = Some phi3'.
Proof.
   intros. apply (unage_join _ H0 H).
Qed.

Lemma unageN'  {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall n (phi1 phi1' phi2' phi3' : A),
    ageN n phi1 = Some phi1' ->
    join phi1' phi2' phi3' ->
    exists phi2, exists phi3, join phi1 phi2 phi3 /\
      ageN n phi2 = Some phi2' /\ ageN n phi3 = Some phi3'.
Proof.
induction n; intros.
inv H. exists phi2'; exists phi3'; split; auto.
 unfold ageN in H. simpl in H.
 revert H; case_eq (age1 phi1); intros.
  specialize ( IHn a phi1' phi2' phi3' H1 H0).
  destruct IHn as [phi2 [phi3 [? [? ?]]]].
  destruct (join_unage' _ _ _ H H2) as [phi4 [phi5 [? [? ?]]]].
  exists phi4; exists phi5. split; auto.
 split; unfold ageN; simpl. rewrite H6; auto. rewrite H7; auto.
 inv H1.
Qed.


Hint Resolve @join_comparable @join_comparable'  @join_comparable'' @join_comparable'''
      @join_comparable2 @join_comparable2'  @list_join_comparable @list_join_comparable'
      @joins_comparable  @joins_comparable2  @join_sub_comparable  @join_sub_comparable2
      @eq_comparable  @eq_comparable2
  : comparable.

Hint Immediate @comparable_refl  @comparable_sym  : comparable.

Ltac Comp1 phi1 phi2 :=
   solve [ eauto 3 with comparable typeclass_instances |
  match goal with
  | H: comparable phi1 ?phi |- _ => Comp2 H phi1 phi phi2
  | H: comparable ?phi phi1 |- _ => Comp2 H phi1 phi phi2
  | H: join phi1 ?phia ?phib |- _ =>  Comp3 H phi1 phia phib phi2
  | H: join ?phia phi1 ?phib |- _ =>   Comp3 H phi1 phia phib phi2
  | H: join ?phia ?phib phi1 |- _ =>   Comp3 H phi1 phia phib phi2
  | H: joins phi1 ?phi |- _ =>  Comp2 H phi1 phi phi2
  | H: joins ?phi phi1 |- _ =>  Comp2 H phi1 phi phi2
  | H: join_sub phi1 ?phi |- _ => Comp2 H phi1 phi phi2
  | H: join_sub ?phi phi1 |- _ => Comp2 H phi1 phi phi2
  | H: list_join phi1 _ ?phi |- _ =>  Comp2 H phi1 phi phi2
  | H: list_join ?phi _ phi1 |- _ =>  Comp2 H phi1 phi phi2
  | H: phi1 = ?phi  |- _ => Comp2 H phi1 phi phi2
  | H: ?phi = phi1  |- _ => Comp2 H phi1 phi phi2
 end]
  with Comp2 H phi1 phi phi2 :=
            solve [apply comparable_trans with phi;
                         [eauto 3 with comparable  typeclass_instances |clear H; Comp1 phi phi2]
                   | clear H; Comp1 phi1 phi2]
  with Comp3 H phi1 phia phib phi2 :=
           solve [apply comparable_trans with phia;
                          [eauto 3 with comparable typeclass_instances |clear H; Comp1 phia phi2]
                  |apply comparable_trans with phib;
                          [eauto 3 with comparable  typeclass_instances | clear H; Comp1 phib phi2]
                   | clear H; Comp1 phi1 phi2].

Ltac Comp := match goal with
                | |- comparable ?phi1 ?phi2 => Comp1 phi1 phi2
                | |-  level ?phi1 = level ?phi2 => apply comparable_fashionR; Comp1 phi1 phi2
(*                | |- level _ = level _ => rewrite comparable_level; Comp *)
                end.


Definition not_any_younger {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A} (phi phi': A)  : Prop :=
     exists phi1, necR phi phi1 /\ comparable phi1 phi'.

Lemma comparable_not_any_younger {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A} :
    forall phi phi' : A , comparable phi phi' -> not_any_younger phi phi'.
Proof.
  intros.
  exists phi; split; auto; apply rt_refl.
Qed.

Lemma necR_not_any_younger {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall phi phi' : A, necR phi phi' -> not_any_younger phi phi'.
Proof. intros; exists phi'; split; auto. apply comparable_refl. Qed.

Lemma not_any_younger_refl {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
 forall phi : A, not_any_younger phi phi.
Proof. intros; exists phi; split; auto. apply comparable_refl. Qed.

Lemma not_any_younger_trans {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall phi1 phi2 phi3, not_any_younger phi1 phi2 -> not_any_younger phi2 phi3 ->
            not_any_younger phi1 phi3.
Proof.
intros.
destruct H as [phi1' [? ?]].
destruct H0 as [phi2' [? ?]].
generalize (comparable_common_unit H1); intros [e1 [? ?]].
generalize (nec_join2 H4 H0); intros [a [b [? [? _]]]].
generalize (nec_join H3 H6); intros [u [v [? [? _]]]].
exists u.
split.
econstructor 3; eauto.
Comp.
Qed.

Lemma not_any_younger_None {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall phi phi', age1 phi = None -> not_any_younger phi phi' -> age1 phi' = None.
Proof.
intros.
destruct H0 as [phi1 [? ?]].
revert phi' H1.
induction H0; intros.
unfold age in H0.
inversion2 H H0.
generalize (comparable_common_unit H1); intros [e1 [? ?]].
case_eq (age1 phi'); [intros w ? | intro]; auto.
elimtype False.
generalize (age1_join2 _ H2 H3); intros [a [b [? [? ?]]]].
generalize (age1_join _ H0 H5); intros [c [d [? [? ?]]]].
unfold age in H8; inversion2 H H8.
assert (x=y).
clear - H0_ H.
induction H0_.
 unfold age in *.
inversion2 H H0.
auto.
rewrite <- IHH0_2; auto.
rewrite <- IHH0_1; auto.
subst y.
auto.
Qed.

Lemma nec_join3 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: forall {x x' y' z' : A},
       join x' y' z' ->
       necR x x' ->
       exists y,
         exists z,
           join x y z /\ necR y y' /\ necR z z'.
Proof.
intros.
revert y' z' H.
induction H0; intros.
destruct (unage_join _ H0 H) as [y0 [z0 [? [? ?]]]].
exists y0; exists z0; split; auto.
split; constructor 1; auto.
exists y'; exists z'.
split; auto.
rename z into x'.
rename y into x1.
destruct (IHclos_refl_trans2 _ _ H) as [x'' [y'' [? [? ?]]]].
destruct (IHclos_refl_trans1 _ _ H0) as [x0 [y0 [? [? ?]]]].
exists x0; exists y0.
split; auto.
split; econstructor 3; eauto.
Qed.

