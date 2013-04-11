(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.eq_dec.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.

(* Other definitions and facts about psepalgs *)

Lemma pjoin_unit {A} {JA: Join A}{PosA: Pos_alg A}: forall {a b : A},
  join a b b -> False.
Proof. exact no_units. Qed.

(* MOVE THIS ONE ELSEWHERE! *)
Definition cjoins {A} {JA: Join A} (a b : A) : Type := {c : A | join a b c}.

(* MOVE THIS ONE ELSEWHERE! *)
Definition cjoin_sub {A} {JA: Join A} (a c : A) : Type := {b : A | join a b c}.

(* RENAME THE USES OF THIS! *)
Lemma joins_comm {A} {JA: Join A}{PA: Perm_alg A} : forall a b,
  joins a b -> joins b a.
Proof. apply joins_sym.
Qed.

(* Interestingly, this does not require canc for either direction *)
Lemma pfull_pmaximal {A} {JA: Join A} {PA: Perm_alg A} {Pos_A: Pos_alg A} : full = maximal.
Proof with eauto.
  extensionality a.  apply prop_ext. split; repeat intro.
  destruct H0 as [a' ?]. unfold full in H.
  spec H a'. spec H...
  destruct H0 as [c ?].
  spec H c. spec H... subst. apply join_comm in H0. 
  apply no_units in H0. contradiction.
Qed.

Lemma psub_joins {A}  {JA: Join A} {PA: Perm_alg A} {Pos_A: Pos_alg A}{DA: Disj_alg A} : forall a b,
  join_sub a b -> joins a b -> False.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct (join_assoc (join_comm H) (join_comm H0)) as [? [? _]].
  rewrite (join_self H1) in H1.
  eapply no_units; eauto.
Qed.


Section DISCRETE.  (* Prevent these Instances from going global! *)
(** We can turn any set into a Pos_alg by making no element join
     with any other element (including itself): the discrete PSA *)

  Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

  Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
  Proof. constructor; intros; inv H.
  Qed.
  
  Instance psa_discrete (A: Type) :  @Pos_alg A  (Join_discrete A).
  Proof.
    repeat intro. inv H.
  Qed.  
End DISCRETE.

Set Implicit Arguments.

(** We provide a way to lift any sepalg into a Pos_alg by removing all
    of the units. *)
Section PSA_LIFT.
  Variable A : Type.
  Variable J_A: Join A.
  Variable PA_A : Perm_alg A.
  
  Definition lifted : Type := sig nonunit.
  
  Definition lifted_obj (la: lifted) : A := proj1_sig la.
(*  Definition lifted_nonidentity (la : lifted) : nonidentity (lifted_obj la) :=
    proj2_sig la.
*)
  Coercion lifted_obj : lifted >-> A.
  Definition mk_lifted (a : A) (pf : nonunit a) : lifted :=
    exist nonunit a pf.
  Implicit Arguments mk_lifted [].

  Instance Join_lift: Join lifted := fun a1 a2 a3 : lifted => @join A J_A a1 a2 a3.

    Instance Perm_lift: Perm_alg lifted.
   Proof.
     constructor; intros.

    icase x; icase y; icase z; icase z'.
    do 2 red in H, H0.
    generalize (join_eq H H0); intro. simpl in H1. subst; auto. 
    apply exist_ext. auto.
    
    icase a; icase b; icase c; icase d; icase e; red in H, H0; simpl in *.
    red  in H, H0. simpl in *.
    destruct (join_assoc H H0) as [f [? ?]].
    assert (nonunit f).
    unfold nonunit, unit_for; intros ? ?.
    destruct (join_assoc H1 H3) as [g [? ?]].
    generalize (join_positivity (join_comm H4) (join_comm H5)); intro.
    rewrite <- H6 in *; clear dependent g.
    apply n0 in H5.  auto.
    exists (existT _ f H3). simpl. split; auto.
    
    do 2 red in H|-*. icase a; icase b; icase c; simpl in *; apply join_comm; auto.

    do 2 red in H,H0.
    icase a; icase a'; icase b; icase b'. simpl in *.
    generalize (join_positivity H H0); intro. subst; f_equal; auto. apply proof_irr.
  Qed.

  Instance Pos_lift: Pos_alg lifted.
  Proof.
   repeat intro. destruct e; destruct a; simpl in *.
   hnf in H. simpl in H. apply n in H. auto.
  Qed.

  Instance Canc_lift {CA: Canc_alg A}: Canc_alg lifted.
  Proof.
    repeat intro. do 2 red in H,H0.
    destruct a1; destruct a2.    generalize (join_canc H H0); intro. simpl in H1.
    subst; f_equal; auto. apply proof_irr.
  Qed.

  Instance Disj_lift {DA: Disj_alg A}: Disj_alg lifted.
  Proof.
    repeat intro. do 2 red in H.  apply join_self in H.  destruct a; destruct b; simpl in *; subst;
    f_equal.  apply proof_irr.
  Qed.

  (** General facts about lifting *)
  
  Lemma lifted_eq : forall a b, 
    lifted_obj a = lifted_obj b -> 
    a = b.
  Proof.
    intros.
    destruct a. destruct b. simpl in *. subst x0.
    f_equal. apply proof_irr.
  Qed.
  
  Lemma mk_lifted_refl1: forall a pf1 pf2, 
    mk_lifted a pf1 = mk_lifted a pf2.
  Proof.
    intros; rewrite (proof_irr pf1 pf2); auto.
  Qed.
  
  Lemma lifted_pjoins : forall a b : lifted,
    joins a b = @joins A J_A a b.
  Proof.
    intros. apply prop_ext. split; intros.
    destruct H. exists x. apply H.
    destruct H.
    assert (nonunit x).
    destruct a as [a Ha]; destruct b as [b Hb]. simpl in H.
    intros ? ?. unfold unit_for in H0. destruct (join_assoc H H0) as [f [? ?]].
    destruct (join_assoc H0 (join_comm H1)) as [g [? ?]].
    generalize (join_eq H1 (join_comm H3)); intro.
    rewrite <- H5 in *; clear dependent g.
    generalize (join_positivity H3 (join_comm H2)); intro.
    rewrite <- H5 in *; clear dependent f.
    apply Hb in H1; auto.
    exists (existT _ x H0). trivial.
  Qed.
  
  Lemma lifted_psub : forall a b : lifted, 
    join_sub a b -> @join_sub A J_A a b.  (* converse not provable *)
  Proof.
    intros.
    destruct H. exists x. apply H.
  Qed.

  Lemma lifted_full {CA: Canc_alg A} : forall a : lifted,
    @full A J_A a -> full a.    (* converse not provable *)
  Proof with auto.
    intros. do 2 intro.
    destruct H0.
    destruct a as [a Ha]. destruct sigma' as [sigma' Hs]. destruct x as [x Hx].
    do 2 red in H0. simpl in H0.
    unfold full in H.
    simpl in H.
    spec H sigma'. spec H; eauto.
    intros ? ? ?. destruct a0, b. do 2 red in H1. simpl in H1. apply H in H1.
    subst; f_equal; auto.  apply proof_irr.
  Qed.

End PSA_LIFT.

Existing Instance Join_lift.  (* Must not be inside a Section *)
Existing Instance Perm_lift.
Existing Instance Pos_lift.
Existing Instance Canc_lift.
Existing Instance Disj_lift.
Implicit Arguments mk_lifted [A J_A].

(** The dual of lifting is lowering: adding a distinct unit to a Pos_alg 
    produces a sepalg.  Note that lower o lift is not an isomorphism for
    sepalgs with multiple units.  However, for sepalgs with a test for
    identity in Type, lower o lift is an isomorphism. *)

Section SA_LOWER.
  Variable A : Type.
  Variable Pj_A: Join A.
  Variable PA_A : Perm_alg A.  

  Inductive lower_join: option A -> option A -> option A -> Prop :=
  | lower_None1: forall a, lower_join None a a
  | lower_None2: forall a, lower_join a None a
  | lower_Some: forall a1 a2 a3,  join a1 a2 a3 -> 
        lower_join (Some a1) (Some a2) (Some a3).

  Instance Join_lower: Join (option A) := lower_join.

  Instance Perm_lower: @Perm_alg (option A) Join_lower.
  Proof.
   constructor; intros.

   inv H; inv H0; try constructor. f_equal.   apply (join_eq H1 H3).


    icase d; [ |  exists c; inv H; inv H0; split; constructor; auto].
    icase e; [ | exists a; inv H0; inv H; split; constructor; auto].
    icase c; [ | exists b; inv H; inv H0; split; constructor; auto].
    icase a; [ | exists (Some a1); inv H; inv H0; split; try constructor; auto].
    icase b; [ | exists (Some a2); inv H; inv H0; split; constructor; auto].
    assert (join a a3 a0) by (inv H; auto).
    assert (join a0 a2 a1) by (inv H0; auto).
    destruct (join_assoc H1 H2) as [f [? ?]]; exists (Some f); split; constructor; auto.

    inv H; constructor; auto.

    inv H; inv H0; auto. f_equal. apply (join_positivity H1 H4).
 Qed.

 Instance Sep_lower: @Sep_alg _ Join_lower.
 Proof. apply mkSep with (fun _ => None); intros.
   constructor. reflexivity.
 Defined.

  Instance Sing_lower: @Sing_alg _ Join_lower _.
  Proof.
     apply (mkSing None). intros. reflexivity. 
  Defined.

  Instance Canc_lower {psa_A: Pos_alg A}{CA: Canc_alg A}: @Canc_alg _ Join_lower.
  Proof. repeat intro.
    inv H; inv H0; auto. apply no_units in H3; contradiction.
    apply no_units in H1; contradiction.
   f_equal. apply (join_canc H1 H4). 
 Qed.

   Instance Disj_lower {DA: Disj_alg A}: @Disj_alg _ Join_lower.
  Proof. repeat intro. 
     icase a; inv H; auto. apply join_self in H2; f_equal; auto.
  Qed.

End SA_LOWER.
Implicit Arguments Perm_lower [[Pj_A][PA_A]].
Implicit Arguments Sep_lower [[Pj_A]].
Implicit Arguments Sing_lower [[Pj_A]].
Implicit Arguments Canc_lower [[Pj_A][psa_A][CA]].
Implicit Arguments Disj_lower [[Pj_A][DA]].

Existing Instance Join_lower.  (* Must not be inside a Section *)
Existing Instance Perm_lower.
Existing Instance Sep_lower.
Existing Instance Sing_lower.
Existing Instance Canc_lower.
Existing Instance Disj_lower.

  (* General facts about lowering *)

Lemma None_unit {A}{JOIN: Join A}: 
      forall x: option A, @unit_for (option A) (@Join_lower _ _) None x.
Proof.
intros. simpl. auto.
constructor.
Qed.

Hint Resolve @None_unit.

Lemma None_identity {A} {JA: Join A}{psaA: Pos_alg A}: 
     @identity (option A) (Join_lower _) None.
Proof.
intros.
intros x y ?. inv H; auto.
Qed.

Hint Resolve @None_identity.

  Lemma lower_inv: forall {A}{JA: Join A} {PA: Perm_alg A} {psa_A: Pos_alg A} (a b c : option A),
    join a b c ->
    (a = None /\ b = c) + (a = c /\ b = None) + 
    ({a' : A & {b' : A & {c' : A | a = Some a' /\ b = Some b' /\ c = Some c' /\
    join a' b' c'}}}).
  Proof.
    intros.
    icase a; icase b; icase c; 
    try solve [elimtype False; inv H];
    try solve [right; exists a; exists a0; exists a1; inv H; intuition].
    left; right; inv H; auto.
    left; left; inv H; auto.
  Qed.

(** The "smash" sepalg generator is the direct composition of lift and
      lower.  In previous versions of MSL (v0.3 and earlier) this was 
      called "lift" and was constructed directly *)

Section SA_SMASH.
  Variable T : Type.
  Variable J_T: Join T.
  Variable PA_T : Perm_alg T. 

  Definition smashed : Type := option (lifted J_T).
  Definition Perm_smash :  Perm_alg smashed  := Perm_lower (lifted J_T). 
  Definition Sep_smash : Sep_alg smashed := Sep_lower (lifted J_T).

  Lemma smash_inv: forall a b c : smashed,
    join a b c ->
    (a = None /\ b = c) + (a = c /\ b = None) + 
    ({a' : lifted J_T & {b' : lifted J_T & {c' : lifted J_T | a = Some a' /\ b = Some b' /\ c = Some c' /\
    join (lifted_obj a') (lifted_obj b') (lifted_obj c')}}}).
  Proof.
    intros.
    apply lower_inv in H.
    intuition.
  Qed.
End SA_SMASH.

Implicit Arguments smashed [[J_T]].
Existing Instance Perm_smash. (* Must not be inside a Section *)
Existing Instance Sep_smash. (* Must not be inside a Section *)

Lemma smashed_lifted_None_identity {A}`{Perm_alg A}:
  @identity (smashed A) _ None.
Proof. intros; apply None_identity. Qed.
Hint Resolve @smashed_lifted_None_identity.
(** The option separation algebra.  The bool sepalg is isomorphic
     to the option sepalg applied to units. *)

 Instance Perm_option (T : Type)  : @Perm_alg (option T) (@Join_lower T (@Join_discrete T)) :=
    @Perm_lower T  (@Join_discrete T) (Perm_discrete T).
 Instance Sep_option (T: Type) : @Sep_alg (option T) (@Join_lower T (@Join_discrete T)) :=
    @Sep_lower T  (@Join_discrete T) .

(** Often, once we have a Pos_alg, we want to product it with regular
    sepalgs to produce another Pos_alg, before lowering the product. *)

Instance Pos_prod
        (A: Type) {J_A: Join A} {Pos_A: Pos_alg A}
        (B: Type) {J_B: Join B}{PA_B: Perm_alg B}: 
        Pos_alg (A*B).
  Proof.
   auto with typeclass_instances.
   repeat intro. inv H. apply no_units in H0. auto.
  Qed.

(** This operator is a combination of the
    function space and smash operators
    which provides the SA equivalant of
    partial maps.  We also constrain the
    domain of the functions to be finite,
    giving a useful semantic characterization
    of finite partial maps.
*)
Section FinitePartialMap.
  Variable A:Type.
  Variable dec_A : EqDec A.

  Variable B:Type.
  Variable PJ_B: Join B.
  Variable Perm_B : Perm_alg B.
  Variable Pos_B : Pos_alg B.

  Let Rng := option B.
  Let Join_Rng := Join_lower PJ_B.
  Let Sep_Rng := Sep_lower B.
  Let Perm_Rng := Perm_lower B. 

  Definition finMap (f:A -> Rng) : Prop :=
    exists l, forall a:A, ~In a l -> f a = None.

  Lemma finMap_unit : forall x e,
    finMap x -> @unit_for _ (Join_fun A _ Join_Rng) e x -> finMap e.
  Proof.
    intros.
    destruct H as [l Hl].
    exists l.
    intros a Hl'.
    spec Hl a Hl'.
    red in H0.
    spec H0 a.
    rewrite Hl in H0. inv H0; auto.
  Qed.

  Lemma finMap_join : forall x y z,
    @join _ (Join_fun A _ Join_Rng) x y z -> finMap x -> finMap y -> finMap z.
  Proof.
    intros.
    destruct H0 as [l0 H0].
    destruct H1 as [l1 H1].
    exists (l0 ++ l1).
    intros.
    spec H a. spec H0 a. spec H1 a.
    rewrite H0 in H. rewrite H1 in H. inv H; auto.
    intro contr. apply H2. apply in_or_app; auto.
    intro contr. apply H2. apply in_or_app; auto.
  Qed.

  Definition fpm := sig finMap.
  Instance Join_fpm : Join fpm := 
     Join_prop (A -> option B)  (Join_fun A (option B) Join_Rng) finMap.

  Definition PAF: (@Perm_alg (A -> Rng)  (Join_fun A Rng Join_Rng))
  := Perm_fun _ _ _ Perm_Rng.

  Instance Perm_fpm : @Perm_alg fpm Join_fpm :=
    Perm_prop (A -> Rng) _ _ finMap finMap_join.

  Lemma finMap_core  x: finMap x -> 
        finMap (@core _ _ (Sep_fun A (option B) Join_Rng _ ) x).
  Proof. intros. exists nil; intros; reflexivity. Qed.

  Definition empty_fpm : fpm.
    refine (exist (fun x => finMap x) (fun _ => None) _).
    exists nil; auto.
  Defined.

  Instance Sep_fpm : @Sep_alg fpm Join_fpm.
  Proof. 
    apply mkSep with (core := fun _ => empty_fpm).
     intros. intro a. simpl. constructor. auto.
   Defined.

  Instance Sing_fpm:  @Sing_alg fpm _ _.
  Proof.
  apply mkSing with (the_unit := empty_fpm).
  intros ?. simpl. auto.
  Defined.

  Instance Canc_fpm {CA_B: Canc_alg B}: Canc_alg fpm.
  Proof. repeat intro.
    apply (join_canc H H0).
  Qed.

  Instance Disj_fpm {DA_B: Disj_alg B}: Disj_alg fpm.
  Proof. repeat intro. apply (join_self H). Qed.

  Definition lookup_fpm (f:fpm) : A -> Rng := proj1_sig f.

  Definition insert_fpm (a:A) (b: B) (f:fpm) : fpm.
    destruct f as [f Hf].
    set (f' := fun x => if eq_dec a x then Some b else f x).
    refine (exist _ f' _).
    destruct Hf as [l Hl].
    exists (a :: l); simpl; intros.
    unfold f'.
    destruct (eq_dec a a0); auto.
    subst a0.
    elim H; auto.
  Defined.

   Definition insert'_fpm (a:A)(b: option B) (f: fpm) : fpm.
    destruct f as [f Hf].
    set (f' := fun x => if eq_dec a x then b else f x).
    refine (exist _ f' _).
    destruct Hf as [l Hl].
    exists (a :: l); simpl; intros.
    unfold f'.
    destruct (eq_dec a a0); auto.
    subst a0.
    elim H; auto.
  Defined.

  Definition remove_fpm (a:A) (f:fpm) : fpm.
    destruct f as [f Hf].
    set (f' := fun x => if eq_dec a x then None else f x).
    refine (exist _ f' _).
    destruct Hf as [l Hl].
    exists l; intros.
    unfold f'.
    destruct (eq_dec a a0); auto.
  Defined.

  Lemma fpm_gss: forall  i v rho, 
        lookup_fpm (insert_fpm i v rho) i = Some v.
  Proof.
    unfold lookup_fpm, insert_fpm.
    destruct rho.
    simpl.
    destruct (eq_dec i i); auto. contradiction n; auto.
  Qed.

  Lemma fpm_gso: forall i j v rho, 
       i <> j -> lookup_fpm (insert_fpm j v rho) i =
                               lookup_fpm rho i.
  Proof.
    unfold lookup_fpm, insert_fpm; intros.
    destruct rho.
    simpl.
    destruct (eq_dec j i); auto. contradiction H; auto.
  Qed.

  Lemma empty_fpm_join : forall x,
    @join _ Join_fpm empty_fpm x x.
  Proof.
    repeat intro.
    simpl.
    constructor.
  Qed.

  Lemma insert_fpm_join : forall i v (x y z:fpm),
    lookup_fpm y i = None ->
    @join _ Join_fpm x y z ->
    @join _ Join_fpm (insert_fpm i v x) y (insert_fpm i v z).
  Proof.
    intros. 
    intro j.
    change (@join _ (Join_lower PJ_B)
      (lookup_fpm (insert_fpm i v x) j)
      (lookup_fpm y j)
      (lookup_fpm (insert_fpm i v z) j)).
    destruct (eq_dec i j). subst j.
    do 2 rewrite fpm_gss. 
    rewrite H.
    constructor.
    do 2 (rewrite fpm_gso; auto).
  Qed.
End FinitePartialMap.

Lemma fpm_bij_aux: forall A B B' (f: B -> B') (rho: A -> option B), 
       @finMap A B rho -> 
       @finMap A B' (fun i => match rho i with None => None | Some j => Some (f j) end).
Proof.
  intros. destruct H as [l ?]. exists l. intros. rewrite (H _ H0). auto.
Qed.
Definition fpm_bij (A B B': Type) (bij: bijection B B') : bijection (fpm A B) (fpm A B').
 destruct bij as [f g fg gf].
 unfold fpm.
 apply (Bijection _ _
     (fun x: sig (@finMap A B) => exist (@finMap A B') _ (fpm_bij_aux f (proj2_sig x)))
     (fun x: sig (@finMap A B') => exist (@finMap A B) _ (fpm_bij_aux g (proj2_sig x)))).
  intros [x Hx]. simpl in *. apply exist_ext. extensionality i. destruct (x i); auto.
  rewrite fg; auto.
  intros [x Hx]. simpl in *. apply exist_ext. extensionality i. destruct (x i); auto.
  rewrite gf; auto.
Defined.

Lemma lift_prod_aux1 {A}{JA: Join A}{B}:
  forall x,   @nonunit (A * B) (Join_prod A JA B (Join_equiv B)) x -> nonunit (fst x).
Proof.
intros. destruct x. simpl. intro.
intro.
specialize (H (x,b)).
apply H.
split; simpl; auto.
Qed.

Definition lift_prod1  {A}{JA: Join A}{B} : (@lifted (A * B) (Join_prod A _ B (Join_equiv B))) -> (@lifted A _ * B).
intros [x Hx].
destruct x as [a b].
split; auto.
apply (mk_lifted a (lift_prod_aux1 Hx)).
Defined.

Lemma lift_prod_aux2 {A}{JA: Join A}{B}: 
  forall x,
    nonunit (fst x) -> @nonunit (A * B) (Join_prod A JA B (Join_equiv B)) x.
Proof.
  intros.
  intro; intro. destruct x0 as [a b].
  destruct H0.
  apply (H _ H0).
Qed.

Definition lift_prod2  {A}{JA: Join A}{B} :(@lifted A _ * B) -> (@lifted (A * B) (Join_prod A _ B (Join_equiv B))).
intros [[x Hx] y].
 apply (mk_lifted _ (@lift_prod_aux2 _ _ _ (x,y) Hx)).
Defined.

Definition lift_prod_bij: forall A (JA: Join A) B,
     bijection  (@lifted (A * B) (Join_prod A _ B (Join_equiv B))) (@lifted A _ * B).
Proof.
  intros.
  apply (Bijection _ _ lift_prod1 lift_prod2).
  intros. destruct x; simpl. destruct l. simpl. unfold mk_lifted. f_equal. f_equal.
  apply proof_irr.
  intros. destruct x; simpl. destruct x. simpl. unfold mk_lifted. f_equal. apply proof_irr.
Defined.
