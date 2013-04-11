(*
 * Copyright (c) 2009-2012, Andrew Appel, Robert Dockins and Aquinas Hobor.
 * This presentation of Permission Algebras and Separation Algebras
 * includes ideas from a discussion with Jonas Jensen and also from
 * a paper by Francois Pottier.
 *)
Require Import msl.Extensionality.

Set Implicit Arguments.

Class Join (t: Type) : Type := join: t -> t -> t -> Prop.

(* "Permission Algebra": commutative semigroup, 
   such that if units exist, they must have certain properties. *)
Class Perm_alg (t: Type) {J: Join t} : Type :=
  mkPerm   {
   join_eq: forall {x y z z'}, join x y z -> join x y z' -> z = z';   
   join_assoc: forall {a b c d e}, join a b d -> join d c e ->
                    {f : t & join b c f /\ join a f e};
   join_comm: forall {a b c}, join a b c -> join b a c;
   join_positivity: forall {a a' b b'}, join a a' b -> join b b' a -> a=b
}.
Implicit Arguments Perm_alg [[J]].

Definition unit_for {t}{J: Join t} (e a: t) := join e a a.
Definition identity {t} {J: Join t} (e: t) := forall a b, join e a b -> a=b.

Hint Extern 2 (@join _ _ _ _ _) => 
   (eapply join_comm; trivial; 
     try eassumption;
     (* This next line looks superfluous, but it is not: it catches the
      case where H is join at a function type, where the goal is
      join at an applied function. *)
     match goal with H: @join _ _ _ _ _ |- _ => apply H end).     
 (* Hint Immediate @join_comm. *)

Hint Unfold unit_for.

Lemma join_assoc_uniq:
  forall {t} {J: Join t} (PA1 PA2: @Perm_alg t J),
      forall a b c d e H H',
         (proj1_sig (@join_assoc _ _ PA1  a b c d e H H'))
        = (proj1_sig (@join_assoc _ _ PA2  a b c d e H H')).
Proof.
  intros.
  destruct (@join_assoc _ _ PA1  a b c d e H H') as [f [? ?]].
  destruct (@join_assoc _ _ PA2  a b c d e H H') as [g [? ?]].
  simpl. apply (join_eq j j1).
Qed.

  (* Sep_alg: additional properties that makes a Permission Algebra
     into a Separation Algebra.  The notion of "core" comes from
    F. Pottier, "Syntactic soundness proof of a type-and-capability
      system with hidden state" *)
  Class Sep_alg A {J: Join A} : Type :=
    mkSep {
      core: A -> A;
      core_unit: forall t, unit_for (core t) t;
      join_core: forall {a b c}, join a b c -> core a = core c
    }.
Implicit Arguments Sep_alg [[J]].

Lemma core_duplicable {A}{J: Join A}{SA: Sep_alg A}:
  forall a, join (core a) (core a) (core a).
Proof.
 intros.
 generalize (core_unit a); unfold unit_for; intro.
 generalize (core_unit (core a)); unfold unit_for; intro.
 generalize (join_core H); intro.
 rewrite H1 in H0; auto.
Qed.

Lemma core_self_join {A}{J: Join A}{SA: Sep_alg A}:
  forall a, a = core a -> join a a a.
Proof.
  intros.
  generalize (core_unit a); rewrite <- H; intro. apply H0.
Qed.

Lemma core_idem {A}{J: Join A}{SA: Sep_alg A}:
  forall a, core (core a) = core a.
Proof.
 intros. 
 generalize (core_unit a); unfold unit_for; intro.
 apply (join_core H).
Qed.

Lemma core_hom {A}{J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall {a b c}, join a b c -> join (core a) (core b) (core c).
Proof.
 intros.
 generalize (join_core H); intro.
  generalize (join_core (join_comm H)); intro.
 rewrite H0; rewrite H1.
 apply core_duplicable.
Qed.

Lemma split_core{A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
 forall a b c, join a b (core c) -> unit_for a a.
Proof.
 intros.
 unfold unit_for.
 generalize (join_core H); rewrite core_idem; intro.
 rewrite <- H0 in H.
 clear dependent c.
 generalize (core_unit a); unfold unit_for; intro.
 generalize (join_positivity H H0); intro.
 rewrite <- H1 in H0; auto.
Qed.

Lemma core_uniq {t} {J: Join t}{PA: Perm_alg t}:
   forall (SA1: @Sep_alg _ J)
          (SA2: @Sep_alg _ J),
     forall x, @core _ _ SA1 x = @core _ _ SA2 x.
Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
 intros.
 generalize  (@core_unit _ _ SA1 x); unfold unit_for; intro.
 generalize  (@core_unit _ _ SA2 x); unfold unit_for; intro.
 destruct (join_assoc (join_comm H0) (join_comm H1)) as [f [? ?]].
 generalize (@core_unit _ _ SA2 (@core _ _ SA1 x)); unfold unit_for; intro.
 generalize (@core_unit _ _ SA1 (@core _ _ SA2 x)); unfold unit_for; intro.
 destruct (join_assoc ( H4) H2) as [g [? ?]].
 destruct (join_assoc H5 (join_comm H2)) as [h [? ?]].
 generalize (join_eq H6 (join_comm H8)); intro. rewrite <- H10 in *; clear dependent h.
 generalize (@join_core _ _ SA1 _ _ _ H4); intro. 
 generalize (@join_core _ _ SA1 _ _ _ H0); intro. 
 generalize (@join_core _ _ SA2 _ _ _ H0); intro. 
 rewrite H11 in *. rewrite H12 in *. rewrite H10 in *.
 apply join_comm in H4.
 apply (join_eq H4 H5).
Qed.

(* Canc_alg: makes a Permission Algebra into a cancellative Perm.Alg. *)
Class Canc_alg (t: Type) {J: Join t} :=
    join_canc: forall {a1 a2 b c}, join a1 b c -> join a2 b c -> a1 = a2.
Implicit Arguments Canc_alg [[J]].

Lemma   unit_identity {A}{J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A} : 
        forall {e} b, unit_for e b -> identity e.
Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
 unfold unit_for, identity; intros.
 remember (core a) as c.
 generalize (core_unit a); intro.
 rewrite <- Heqc in H2. rename H2 into u.
 unfold unit_for in u.
 destruct (join_assoc (join_comm u) (join_comm H1)) as [f [? ?]].
 generalize (join_canc H1 (join_comm H3)); intro.
 rewrite <- H4 in *; clear f H4 H3.
 destruct (join_assoc H2 H1) as [f [? ?]].
 generalize (join_eq H1 H3); intro.
 rewrite H5 in *; clear b0 H5 H3.
 destruct (join_assoc H2 H0) as [g [? ?]].
 generalize (join_eq H0 H3); intro.
 rewrite <- H6 in *; clear g H6 H3.
 generalize (join_canc H0 H5); intro.
 rewrite <- H3 in *; clear dependent c.
 eapply join_canc. eapply join_comm; apply H1.
 apply join_comm; auto.
Qed.

Lemma core_identity  {A}{J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
  forall a, identity (core a).
Proof.
  intros. eapply unit_identity. apply core_unit.
Qed.

Lemma join_ex_identity  {A}{J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
     forall a, {e : A & prod (identity e) (unit_for e a) }.
Proof.
 intros.
 exists (core a).
 split.
 apply core_identity.
 apply core_unit.
Qed.

(* Disj_alg: adds the property that no nonempty element can join with itself. *)
Class Disj_alg  (t: Type) {J: Join t} :=
   join_self: forall {a b}, join a a b -> a = b.
Implicit Arguments Disj_alg [[J]].

  (* Sing_alg: adds the property that makes the Permission Algebra
     into a single-unit Separation Algebra.  (this is the "traditional"
     kind of Separation Algebra).   *)
Class Sing_alg A {J: Join A}{SA: Sep_alg A} :=
    mkSing { 
      the_unit: A;
      the_unit_core: forall a, core a = the_unit 
    }.
Implicit Arguments Sing_alg [[J][SA]].
Implicit Arguments mkSing [[A] [J][SA]].

  (* Positive Permission Algebra: there are no units, every element is nonempty *)
  Class Pos_alg  {A} {J: Join A} :=
    no_units: forall e a, ~unit_for e a.
Implicit Arguments Pos_alg [[J]].

(* Has the "cross-split" property described in Dockins et al,
    "A fresh look at separation algebras and share accounting", 2009 *)
Class Cross_alg (t: Type)  `{J: Join t} := 
   cross_split :
      forall a b c d z : t,
       join a b z ->
       join c d z ->
    { x:(t*t*t*t) &  match x with (ac,ad,bc,bd) =>
         join ac ad a /\ join bc bd b /\ join ac bc c /\ join ad bd d
       end
    }.
Implicit Arguments Cross_alg [J].

(* Has the "triple join" property  *)
Class Trip_alg {A} {J: Join A} :=
  triple_join_exists:
  forall (a b c ab bc ac : A), join a b ab -> join b c bc -> join a c ac ->
       {abc | join ab c abc}.
Implicit Arguments Trip_alg [J].

(* We do NOT yet introduce "emp" as a notation or synonym for "identity".
  This is because "emp" is a predicate of Separation Logic, but this file
  contains only Separation Algebras.  Some separation logics have 
  predicates that are not just "t -> Prop", and therefore it is premature
  in this file to define "emp".
*)

(** * Lemmas about separation algebras. *)

Lemma  join_ex_units{A}{J: Join A}{SA: Sep_alg A}:
    forall a, {e : A & unit_for e a }.
Proof.
 intros. exists (core a). apply core_unit.
Qed.

Lemma same_identity {A}{J: Join A}{PA: Perm_alg A}:
  forall e e' a, identity e -> unit_for e a -> identity e' -> unit_for e' a -> e = e'.
Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
 intros.
 unfold unit_for in *.
 destruct (join_assoc (join_comm H1) (join_comm H3)) as [f [? ?]].
 generalize (H0 _ _ H4); intro.
 generalize (H2 _ _ (join_comm H4)); intro.
 rewrite H6; apply H7.
Qed.

Lemma same_unit {A}{J: Join A}{PA: Perm_alg A}{SA:Sep_alg A}{CA: Canc_alg A}:
       forall {e1 e2 a}, unit_for e1 a -> unit_for e2 a -> e1 = e2.
Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
intros.
generalize (unit_identity _ H0); intro.
unfold unit_for in *.
destruct (join_assoc (join_comm H0) (join_comm H1)) as [f [? ?]].
generalize (H2 _ _ H3); intro.
rewrite <- H5 in *; clear f H5.
apply join_comm in H3.
apply (unit_identity _ H1 _ _ H3).
Qed.


  (** Elements [a] and [b] join. *)
  Definition joins {A} {J: Join A} (a b : A) : Prop :=
    exists c, join a b c.

  Definition overlap {A}{J: Join A} (a b: A) := ~(joins a b).

  Lemma join_joins {A} {J: Join A}: forall {a b c},
    join a b c -> joins a b.
  Proof. intros; econstructor; eauto.
  Qed.

  Lemma join_joins' {A} {J: Join A} {PA: Perm_alg A}: forall {a b c},
    join a b c -> joins b a.
  Proof.
    intros; econstructor. eauto. 
  Qed.

  Lemma joins_sym {A}  {J: Join A} {PA: Perm_alg A}: forall a b,
    joins a b <-> joins b a.
  Proof.
    intros.
    split; intro; destruct H;
      exists x; apply join_comm; trivial.
  Qed.

  Lemma joins_sym': forall {A} `{Perm_alg A} {phi1 phi2}, joins phi1 phi2 -> joins phi2 phi1.
  Proof.
   intros.
   apply joins_sym. auto.
  Qed.

  (** Elememt [a] is a subelement of [c] .  This relation forms a partial order. *)
  Definition join_sub {A} `{Join A} (a c : A) : Prop :=
    exists b, join a b c.

  Lemma join_join_sub {A} `{Perm_alg A}: forall {a b c},
    join a b c ->
    join_sub a c.
  Proof.
    intros; econstructor; eauto. 
  Qed.

  Lemma join_join_sub' {A} `{Perm_alg A}: forall {a b c},
    join a b c ->
    join_sub b c.
  Proof.
    intros; econstructor; eauto. 
  Qed.

  Lemma join_sub_refl {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall a,
    join_sub a a.
  Proof.
    intros.
    exists (core a). apply join_comm.
    apply core_unit.
  Qed.

  Hint Resolve @join_sub_refl.

  Lemma join_sub_trans {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}: forall a b c,
    join_sub a b ->
    join_sub b c ->
    join_sub a c.
  Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
    intros. destruct H0; destruct H1. 
    destruct (join_assoc H0 H1) as [f [? ?]].
    econstructor; eauto.
  Qed.

Lemma join_sub_same_identity {A} {J: Join A}{PA: Perm_alg A}:
   forall e e' a c,  identity e -> unit_for e a -> identity e' -> unit_for e' c ->
                  join_sub a c -> e = e'.
Proof.
 pose proof I. (* hack: shift up auto-named hyps *)
  intros.
  destruct H4.
  unfold unit_for in *.
  destruct (join_assoc (join_comm H1) H4) as [f [? ?]].
   generalize (H0 _ _ H5); intro.
   rewrite <- H7 in *; clear dependent f.
   destruct (join_assoc H5 (join_comm H6)) as [g [? ?]].
   generalize (join_eq H4 (join_comm H7)); intro.
   rewrite <- H9 in *; clear dependent g.
   apply same_identity with c; auto.
Qed.  

  Lemma join_sub_joins {A} `{HA: Perm_alg A}: forall {a b},
    join_sub a b -> joins a b -> joins a a.
  Proof.
    intros a b [? ?] [? ?].
    apply join_comm in H0.
    destruct (join_assoc H H0) as [? [? ?]].
    destruct (join_assoc H1 (join_comm H2)) as [? [? ?]].
    econstructor; eauto.
  Qed.
  (* Note: there are two other conceivable conclusions from the above
     premises: "joins b b" and "join_sub b a".  Neither must follow, since
     neither is true on the bools, but also neither is a contradiction
     since both are true on Z *)

  Lemma join_sub_joins_trans {A} `{HA: Perm_alg A}: forall {a b c},
    join_sub a c -> joins c b -> joins a b.
  Proof.
    intros.
    destruct H as [wx ?].
    destruct H0 as [wy ?].
    destruct (join_assoc (join_comm H) H0) as [wf [? ?]].
    econstructor; eauto.
  Qed.

  Lemma join_sub_joins'  {A} `{HA: Perm_alg A}:
    forall {a a' b b' : A},
      join_sub a a' -> join_sub b b' -> joins a' b' -> joins a b.
  Proof.
    intros.
    destruct H; destruct H0; destruct H1.
    destruct (join_assoc (join_comm H) H1) as [f [? ?]].
    destruct (join_assoc (join_comm H0) (join_comm H2)) as [g [? ?]].
    exists g; apply join_comm; auto.
  Qed.

  Definition sub_silhouette {A} `{Perm_alg A} (a b: A) : Prop :=
    forall c, joins c b -> joins c a.

  Definition same_silhouette {A} `{Perm_alg A} (a b: A) : Prop :=
    forall c, joins c a <-> joins c b.

  Lemma sub_silhouette_refl {A} `{Perm_alg A}: forall a, sub_silhouette a a.
  Proof. unfold sub_silhouette; intuition. Qed.

  Lemma sub_silhouette_trans {A} `{Perm_alg A}: forall a b c,
    sub_silhouette a b -> sub_silhouette b c -> sub_silhouette a c.
  Proof. unfold sub_silhouette; intuition. Qed.

  Lemma same_silhouette_refl {A} `{Perm_alg A}: forall a, same_silhouette a a.
  Proof. unfold same_silhouette; intuition. Qed.

  Lemma same_silhouette_sym {A} `{Perm_alg A}: forall a b,
    same_silhouette a b -> same_silhouette b a.
  Proof.  unfold same_silhouette; intros; split; apply H0; auto. 
  Qed.

  Lemma same_silhouette_trans {A} `{Perm_alg A}: forall a b c,
    same_silhouette a b -> same_silhouette b c -> same_silhouette a c.
 Proof. unfold same_silhouette; intros; split; intros; 
             destruct (H0 c0); destruct (H1 c0);   auto. Qed.

  Lemma same_silhouette_sub1{A} `{Perm_alg A}: forall a b,
    same_silhouette a b -> sub_silhouette a b.
  Proof. unfold same_silhouette, sub_silhouette; intros; intuition; destruct (H0 c); auto. Qed.

  Lemma same_silhouette_sub2 {A} `{Perm_alg A}: forall a b,
     same_silhouette a b -> sub_silhouette b a.
  Proof. unfold same_silhouette, sub_silhouette; intros; intuition; destruct (H0 c); auto. Qed.

  Lemma sub_same_silhouette {A} `{Perm_alg A}:
    forall a b, sub_silhouette a b -> sub_silhouette b a -> same_silhouette a b.
  Proof. unfold same_silhouette, sub_silhouette; intuition; destruct (H0 c); auto. Qed.

  Lemma same_silhouette_join {A} `{HA: Perm_alg A}:
    forall phi phi' phiy phiz phiz',
      same_silhouette phi phi' ->
      join phi phiy phiz ->
      join phi' phiy phiz' ->
      same_silhouette phiz phiz'.
  Proof.
    intros.
    intro phiu.
    split; intros [phix ?].
    destruct (join_assoc H0 (join_comm H2)) as [phif [? ?]].
    specialize (H phif).
    destruct H.
    assert (exists phiz, join phi phif phiz) by eauto.
    assert (joins phif phi) by (apply joins_sym;  auto).
    specialize (H H7).
    clear H5 H6 H7.
    destruct H as [phix' ?].
    destruct (join_assoc (join_comm H3) H) as [phig [? ?]]. 
    generalize (join_eq H1 (join_comm H5)); intro.
    rewrite <- H7 in *. clear phig H7 H5.
    exists phix'.
    auto.
    destruct (join_assoc H1 (join_comm H2)) as [phif [? ?]].
    specialize (H phif).
    destruct H.
    assert (exists phiz, join phi' phif phiz) by eauto.
    assert (joins phif phi') by (apply joins_sym;  auto).
    specialize (H5 H7).
    clear H H6 H7.
    destruct H5 as [phix' ?].
    destruct (join_assoc (join_comm H3) H) as [phig [? ?]].
    generalize (join_eq H0 (join_comm H5)); intro.
    rewrite <- H7 in *; clear phig H7 H5.
    exists phix'.
    auto.
  Qed.

Hint Resolve @join_joins @join_joins' @join_join_sub @join_join_sub'.

  Definition nonidentity {A} `{Perm_alg A} (a: A) := ~(identity a).

  (** If [a] is a subelement of [b], their units are equal. *)
  Lemma join_sub_units_eq {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A} :
   forall {a b} ea eb,
    join_sub a b ->
    unit_for ea a ->
    unit_for eb b ->
    ea = eb.
  Proof.
    unfold unit_for.
    intros.
    destruct H. 
    destruct (join_assoc H0 H) as [f [? ?]].
    generalize (join_eq H H2); intro.
    rewrite <- H4 in *; clear f H4 H2.
    eapply same_unit; eauto. 
  Qed.

  Lemma unit_core{A} {JA: Join A}{SA: Sep_alg A}{CA: Canc_alg A}:
      forall {a}, unit_for a a -> a = (core a).
  Proof.
   unfold unit_for; intros.
   generalize (core_unit a); intro.
   unfold unit_for in H0.
   apply (join_canc H H0).
  Qed.

  (** A unit for an element is a unit for itself (is idempotent). *)
  Lemma unit_self_unit {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A} : 
   forall a ea,   unit_for ea a ->  unit_for ea ea.
  Proof.
    intros.
    unfold unit_for in *.
    destruct (join_assoc (join_comm H) (join_comm H)) as [f [? _]].
    generalize (unit_identity _ H); intro.
    generalize (H1 _ _ H0); intro.
   rewrite <- H2 in H0; clear f H2.
   auto.
  Qed.

  (** If a joins with b, then their units are equal. *)
  Lemma joins_units_eq {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
   forall {a b} ea eb,
    joins a b ->
    unit_for ea a ->
    unit_for eb b ->
    ea  = eb.
  Proof.
    intros.
    destruct H.
    unfold unit_for in *.
    destruct (join_assoc (join_comm H0) H) as [f [? ?]].
    generalize (unit_identity _ H0 _ _ H2); intro.
    rewrite <- H4 in *; clear f H4.
    eapply same_unit; eauto.
  Qed.

  (** The existence of identity elements. *)
  Lemma join_ex_identities {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall a,
    {e : A & identity e /\ joins e a}.
  Proof.
    intro x.
    destruct (join_ex_identity x) as [e [? ?]].
   exists e; split; auto.
   exists x; auto.
  Qed.

  (** If something is an identity and it joins with an element then it is a
     unit for that element. *)
  Lemma identity_unit {A} `{HA: Perm_alg A}: forall e a,
    identity e ->
    joins e a ->
    unit_for e a.
  Proof.
    intros. destruct H0.
    generalize (H a x H0); intro.
    rewrite <- H1 in *; clear x H1.
    trivial.
  Qed.

  (** Identities are exactly units for themselves (are idempotent).*)
  Lemma identity_unit_equiv {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
    forall a,  identity a <-> unit_for a a.
  Proof.
    intros.
    split; intro.
    apply identity_unit; trivial.
    exists a.
    destruct (join_ex_units a) as [ea H0].
    generalize (join_comm H0); intro.
    generalize (H ea a H1); intro.
    rewrite <- H2 in *; clear a H2.
    trivial.
    apply (unit_identity _ H).
  Qed.

  (** Joinable identities are unique. *)
  Lemma identities_unique {A} `{HA: Perm_alg A} :
   forall e1 e2,  identity e1 ->  identity e2 ->  joins e1 e2 ->  e1 = e2.
  Proof.
    intros.
    destruct H1.
    assert (e2 = x) by auto.
    apply join_comm in H1.
    assert (e1 = x) by auto.
    rewrite H3; rewrite H2; reflexivity.
  Qed.

Lemma split_identity{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
 forall a b c, join a b c -> identity c -> identity a.
Proof.
 intros.
 apply identity_unit_equiv.
 apply (split_core a b c).
 generalize (core_hom H); intro.
 generalize (join_core H); intro.
  generalize (split_core _ _ _ H1); unfold unit_for; intro.
  apply identity_unit_equiv in H0.
  generalize (core_unit c); unfold unit_for; intro.
  generalize (join_canc H0 H4); intro.
  rewrite <- H5; auto.
Qed.

  (* The contrapositive of split_identity *)
  Lemma join_nonidentity {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall a b c,
    nonidentity a -> join a b c -> nonidentity c.
  Proof.
    intros a b c H H0 H1.
    contradiction H.
    apply split_identity with b c; auto.
  Qed.

  Lemma join_sub_antisym {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall x y,
    join_sub x y ->
    join_sub y x ->
    x = y.
  Proof.
    intros ? ? [? ?] [? ?].
    destruct (join_assoc H H0). destruct a.
    apply join_comm in H2.
    generalize(unit_identity _ H2); intro.
    generalize(split_identity _ _ H1 H3); intro.
    apply join_comm in H.
    auto.
  Qed.

  (** This lemma uses the full power of self_join and eliminates both N and Z. *)
  Lemma join_sub_joins_identity {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{DS: Disj_alg A}: forall a b,
    join_sub a b -> joins a b -> identity a.
  Proof.
    intros.
    apply identity_unit_equiv.
    generalize (join_sub_joins H H0); intro.
    destruct H1.
    generalize (join_self H1); intro.
    rewrite <- H2 in *; clear x H2.
    trivial.
  Qed.

  (** Sometimes it is useful to use a negative form of the previous lemma *)
  Lemma join_overlap {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{DS: Disj_alg A}: forall a b,
    join_sub a b -> nonidentity a -> overlap a b.
  Proof.
    repeat intro.
    apply H0.
    eapply join_sub_joins_identity; eauto.
  Qed.

(** The opposite of identity is maximal or full *)

Definition full {A} {JA: Join A}(sigma : A) : Prop :=
   forall sigma', joins sigma sigma' -> identity sigma'.

Definition maximal {A} {JA: Join A} (sigma : A) : Prop :=
  forall sigma', join_sub sigma sigma' -> sigma = sigma'.

Lemma full_maximal {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A} : 
       forall a, full a <-> maximal a.
Proof with auto.
 pose proof I. (* hack: shift up auto-named hyps *)
  split; intro.
  intros a'' ?.
  destruct H1 as [a' ?].
  specialize (H0 a').
  apply H0. eauto. apply join_comm...
  intros a' ?.
  destruct H1 as [a'' ?].
  rewrite <- (H0 a'') in *; eauto; clear a'' H0.
  eapply unit_identity; eauto.
Qed.

(** A join homomorphism is a function from one separation
    algebra to another which preserves the join relation.

    This is used when we build the sa_preimage (to add a Perm_alg to the knot).
 *)

Definition join_hom {A} {JA: Join A} {B} {JB: Join B} (f:A ->B) :=
  forall x y z,
    join x y z ->
    join (f x) (f y) (f z).

(** The elements of a multi-unit separation algebra can be partitioned
    into equivalance classes, where two elements are in the class iff
    they have the same unit.
  *)

  Definition comparable {A} `{Sep_alg A}  (a b:A)
    := core a = core b.

  Lemma comparable_refl {A} `{Sep_alg A} : forall a, comparable a a.
  Proof. intros; red; auto. Qed.

  Lemma comparable_sym {A} `{Sep_alg A}: forall a b, comparable a b -> comparable b a.
  Proof. unfold comparable; intros; symmetry; auto. Qed.

  Lemma comparable_trans {A} `{Sep_alg A}: forall a b c, comparable a b -> comparable b c -> comparable a c.
  Proof. unfold comparable; intros; etransitivity; eauto. Qed.

  Lemma comparable_common_unit {A} `{Sep_alg A}: forall a b,
    comparable a b ->
    exists e, join e a a /\ join e b b.
  Proof.
    intros.
    red in H0.
    exists (core a); split.
    apply core_unit.
    rewrite H0; apply core_unit.
  Qed.

  Lemma common_unit_comparable {A} `{Sep_alg A} : forall a b,
    (exists e, join e a a /\ join e b b) ->
    comparable a b.
  Proof.
    intros.
    destruct H0 as [e [H1 H2]].
    unfold comparable.
    rewrite <- (join_core H1).  apply (join_core H2).
Qed.

Lemma join_comparable  {A} `{Sep_alg A}:
  forall phi1 phi2 phi3, join phi1 phi2 phi3 -> comparable phi1 phi3.
Proof.
  intros.
  unfold comparable.
  eapply join_core; eauto.
Qed.

Lemma join_comparable2  {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall phi1 phi2 phi3, join phi1 phi2 phi3 -> comparable phi1 phi2.
Proof.
  intros.
  unfold comparable.
  generalize (join_core H); intro.
  generalize (join_core (join_comm H)); intro.
  rewrite H0; rewrite H1; reflexivity.
Qed.

Lemma join_sub_comparable  {A} `{Sep_alg A} : forall a c,
  join_sub a c -> comparable a c.
Proof.
  intros.
  destruct H0.
  eapply join_comparable; eauto.
Qed.

Lemma joins_comparable  {A} {J: Join A}{PA: Perm_alg A}{SA: Sep_alg A} : forall a c,
  joins a c -> comparable a c.
Proof.
  intros a c H0.
  destruct H0.
  eapply join_comparable2; eauto.
Qed.

Lemma join_unit1 {A} `{Perm_alg A}:
  forall x y z, unit_for x z -> y = z -> join x y z.
Proof.
intros. rewrite H1 in *; auto.
Qed.

Lemma join_unit2 {A} `{Perm_alg A}:
  forall x y z, unit_for y z -> x = z -> join x y z.
Proof.
intros. rewrite  H1 in *;  clear x H1. apply join_comm; auto.
Qed.

Lemma join_unit1_e {A} `{Perm_alg A}: 
  forall x y z, identity x -> join x y z -> y = z.
Proof.
intros.
eapply join_eq; eauto.
apply identity_unit; eauto.
Qed.

Lemma join_unit2_e {A} `{Perm_alg A}: 
  forall x y z, identity y -> join x y z -> x = z.
Proof.
intros.
apply join_comm in H1.
eapply join_unit1_e; eauto.
Qed.

Lemma PermAlg_ext:
  forall (T: Type) (J: @Join T) (sa1 sa2: @Perm_alg T J), sa1=sa2.
Proof. intros.
destruct sa1, sa2.
f_equal; try apply proof_irr.
extensionality a b c.
extensionality d e.
extensionality H1 H2.
destruct (join_assoc1 a b c d e H1 H2) as [f [? ?]].
destruct (join_assoc0 a b c d e H1 H2) as [f0 [? ?]].
apply existT_ext.
eapply join_eq0; eauto.
Qed.

Lemma Sep_alg_ext {T} {J} {PA: @Perm_alg _ J}: 
   forall (sa1 sa2: @Sep_alg T J), sa1=sa2.
Proof.
intros.
generalize (@core_uniq _ J _ sa1 sa2); intro.
destruct sa1; destruct sa2.
simpl in H.
assert (core0 = core1).
  extensionality; auto.
subst core1.
f_equal.
apply proof_irr.
apply proof_irr.
Qed.

Definition nonunit {A} `{Join A}  (a: A) := forall x, ~ unit_for a x.

Lemma nonidentity_nonunit {A} {JA: Join A} {PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
  forall {a}, nonidentity a -> nonunit a.
Proof.
 intros. intros ? H0; apply H. eapply unit_identity; apply H0.
Qed.

Lemma nonunit_nonidentity {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
  forall x, nonunit x -> ~identity x.
Proof. intros. intro.
  apply identity_unit_equiv in H0. apply (H _ H0).
Qed.
