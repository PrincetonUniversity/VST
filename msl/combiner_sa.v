(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(* A portion of this file was developed by Le Xuan Bach *)

Require Import msl.base.
Require Import msl.sepalg.
Require Import msl.functors.
Require Import msl.sepalg_functors.

Definition midObj {A} {JA: Join A} (a : A) : Prop := ~identity a /\ ~ full a.

Definition ijoinable A {JA: Join A} : Type := {sh : A & midObj sh}.

Definition ijoin {A} {JA: Join A} (j1 j2 j3 : ijoinable A) : Prop :=
  match (j1, j2, j3) with 
  (existT t1 _, existT t2 _, existT t3 _) => join t1 t2 t3
  end.

Lemma ijoin_eq {A} {JA: Join A}{PA: Perm_alg A} : forall j1 j2 j3 j3',
  ijoin j1 j2 j3 ->
  ijoin j1 j2 j3' ->
  j3 = j3'.
Proof.
  intros.
  icase j1; icase j2; icase j3; icase j3'.
  unfold ijoin in *.
  apply existT_ext.
  eapply join_eq; eauto.
Qed.

Lemma ijoin_com {A} {JA: Join A}{PA: Perm_alg A} : forall j1 j2 j3,
  ijoin j1 j2 j3 -> ijoin j2 j1 j3.
Proof with auto.
  intros.
  icase j1; icase j2; icase j3.
  red in H; red.
  apply join_comm...
Qed.

Lemma ijoin_assoc {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A} : forall a b c d e,
  ijoin a b d -> 
  ijoin d c e -> 
  {f : ijoinable A | ijoin b c f /\ ijoin a f e}.
Proof with auto.
  intros.
  icase a; icase b; icase c; icase d; icase e.
  unfold ijoin in *.
  destruct (join_assoc H H0) as [f [? ?]].
  assert ((~identity f) /\ (~full f)).
    unfold midObj in *.
    split.
    intro.
    generalize (split_identity _ _ H1 H3); intro.
    tauto.
    intro.
    spec H3 x. spec H3. exists x3...
    spec H3 f x3 H2. subst x3.
    apply unit_identity in H2.
    tauto.
  exists (existT midObj f H3).
  split...
Qed.

Lemma ijoin_canc {A}  {JA: Join A}{SA: Sep_alg A}{CA: Canc_alg A}: forall a a' b c,
  ijoin a b c -> 
  ijoin a' b c ->
  a = a'.
Proof with auto.
  intros.
  icase a; icase a'; icase b; icase c.
  unfold ijoin in *.
  apply existT_ext.
  eapply join_canc; eauto.
Qed.

Lemma ijoin_identity1 {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}: forall a b,
  ijoin a b b ->
  False.
Proof with auto.
  intros.
  icase a; icase b.
  destruct m. apply n.
  apply (unit_identity x0).
  apply H.
Qed.

Lemma ijoin_identity2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{DA: Disj_alg A}: forall a b,
  ijoin a a b ->
  False.
Proof with auto.
  intros.
  icase a. icase b.
  destruct m; destruct m0.
  assert (x=x0). apply join_self. apply H. subst x0.
  assert (join x x x) by (apply H).
  apply unit_identity in H0.
  contradiction.
Qed.

Section CombineJoin.

Variable A : Type.
Variable JA: Join A.
Variable pa_A : Perm_alg A.
Variable sa_A : Sep_alg A.
Variable ca_A : Canc_alg A.

(* We either need an explicit top witness or some kind of axiom of choice
    (if not here, then in sa_fun or somesuch).  It is a little ugly this way but
    I don't see any other way around. Aquinas *)
Variable A_top : A.
Variable A_top_full : full A_top.

Variable T1 : Type.
Variable T2 : Type.
Variable J1: Join T1.
Variable pa_T1: Perm_alg T1.
Variable sa_T1: Sep_alg T1.

Variable combjoin : T1 -> T1 -> T2 -> Prop.

Variable combjoin_eq : forall v1 v1' v2 v2', 
  combjoin v1 v1' v2 ->
  combjoin v1 v1' v2' ->
  v2 = v2'.

Variable combjoin_assoc : forall v1 v2 v3 v4 v5,
   join v1 v2 v3 ->
   combjoin v3 v4 v5 ->
   {v' : T1 & join v2 v4 v' /\ combjoin v1 v' v5}.

Variable combjoin_com : forall v1 v2 v3,
   combjoin v1 v2 v3 ->
   combjoin v2 v1 v3.

Variable combjoin_canc : forall v1 v1' v2 v3,
    combjoin v1 v2 v3 ->
    combjoin v1' v2 v3 ->
    v1 = v1'.

(* We would really prefer this to be:
       exists top, join (projT1 j1) (projT1 j2) top /\ full top
   but, again, we run into Type/Prop problems and wind up needing
   some form of the axiom of choice somewhere or other. *)
Definition covers (j1 j2 : ijoinable A) : Prop :=
  join (projT1 j1) (projT1 j2) A_top.

Inductive combiner : Type :=
  | CEmpty
  | CPart : forall (sh : ijoinable A) (v : T1), combiner
  | CFull : forall (v : T2), combiner.

Instance Join_combiner : Join combiner := 
  fun c1 c2 c3 =>
  match (c1,c2,c3) with
  | (CEmpty, CEmpty, CEmpty) => True
  | (CEmpty, CPart a v, CPart a' v') => a = a' /\ v = v'
  | (CPart a v, CEmpty, CPart a' v')  => a = a' /\ v = v'
  | (CEmpty, CFull v, CFull v') => v = v'
  | (CFull v, CEmpty, CFull v') => v = v'
  | (CPart a v, CPart a' v', CPart a'' v'') => ijoin a a' a'' /\ join v v' v''
  | (CPart a v, CPart a' v', CFull v'') => combjoin v v' v'' /\ covers a a'
  | _ => False
 end.

Lemma combineJ_eq: forall x y z z' : combiner,
  join x y z -> join x y z' -> z = z'.
Proof with auto.
  intros.
  icase x;icase y;icase z;icase z';try inversion H;try inversion H0;try congruence.
  
  f_equal.
  eapply ijoin_eq; eauto.
  eapply join_eq; eauto.

  elimtype False; clear - pa_A sa_A H1 H4 A_top_full.
  destruct sh; destruct sh0; destruct sh1.
  red in H1; red in H4; simpl in H4.
  generalize (join_eq H1 H4); intro; subst x1.
  unfold midObj in *.
  tauto.

  elimtype False; clear - pa_A sa_A H2 H3 A_top_full.
  destruct sh;destruct sh0;destruct sh1.
  red in H3; red in H2; simpl in H2.
  generalize (join_eq H2 H3);intro;subst x1.
  unfold midObj in *.
  tauto.

  rewrite (combjoin_eq _ _ _ _ H1 H3)...
Qed.

Lemma combineJ_assoc: forall a b c d e : combiner, 
  join a b d -> join d c e ->
                    {f : combiner & join b c f /\ join a f e}.
Proof with auto.
   intros. red in H, H0. unfold join.
   icase a;icase b;icase c;icase d;icase e;inv H;inv H0.
  

   exists CEmpty;split;red...
   exists (CPart sh0 v0);split;red...
   exists (CFull v0);split;red...
   exists (CPart sh1 v1);split;red...
   exists (CPart sh2 v2);split;red...
   exists (CFull v2);split;red...
   exists (CFull v1);split;red...
   exists CEmpty;split;red...
   exists (CPart sh0 v0);split;red...
   exists (CPart sh0 v0);split;red...
   exists (CPart sh0 v0);split;red...
   exists (CPart sh0 v0);split;red...
   3: exists (CEmpty);split;red...
   
   destruct (ijoin_assoc _ _ _ _ _ H1 H) as [sh' [? ?]].
   destruct (join_assoc H2 H3) as [fv [? ?]].
   exists (CPart sh' fv); split; red...
   
   icase sh; icase sh0; icase sh1; icase sh2.
   red in H1, H3. simpl in H1, H3.
   destruct (join_assoc H1 H3) as [sh' [? ?]].
   assert ((~identity sh') /\ (~full sh')).
     split; intro.
     generalize (split_identity _ _ H0 H5); intro.
     unfold midObj in *.
     tauto.
     spec H5 x.
     spec H5. exists A_top...
     spec H5 sh' A_top H4.
     subst sh'.
     apply unit_identity in H4.
     unfold midObj in *.
     tauto.
  destruct (combjoin_assoc _ _ _ _ _ H2 H) as [v' [? ?]].
  exists (CPart (existT _ sh' H5) v').
  split; split...
Qed.

Lemma combineJ_com: forall a b c : combiner, 
    join a b c -> join b a c.
Proof with auto.
  intros. unfold join in H|-*.
  icase a; icase b.
  icase c; red in H; red; destruct H;
  split...
  apply ijoin_com...
  apply join_comm...
Qed.

Lemma combineJ_canc {C1: Canc_alg T1}: forall a1 a2 b c : combiner, 
       join a1 b c -> join a2 b c -> a1=a2.
Proof with auto.
   intros. unfold join in H,H0.
   icase c;icase b;icase a1;icase a2;inv H;inv H0;auto.
   
   destruct (ijoin_identity1 _ _ H).
   destruct (ijoin_identity1 _ _ H1).
   
   generalize (ijoin_canc _ _ _ _ H1 H).
   generalize (join_canc H2 H3); intros.
   subst sh2 v2...
   
   generalize (join_canc H2 H3).
   generalize (combjoin_canc _ _ _ _ H1 H); intros.
   f_equal...
   icase sh0; icase sh1.
   apply existT_ext...
Qed.

Lemma combineJ_ex_identities: forall a , {e : combiner &  join e a a}.
Proof with auto.
   intros.
   icase a;
   exists CEmpty;
   constructor...
Qed.

Lemma combineJ_self {DA: Disj_alg A}:
        forall a b : combiner, join a a b -> a = b.
Proof.
  intros.
  icase a;icase b; inv H.
  destruct (ijoin_identity2 _ _ H0).
  elimtype False. clear - DA H1 A_top_full.
  icase sh. red in H1. simpl in H1.
  generalize (join_self H1); intro.
  subst x.
  unfold midObj in *.
  tauto.
Qed.

Instance Perm_combiner : Perm_alg combiner.
Proof. constructor.
  apply combineJ_eq.
  apply combineJ_assoc.
  apply combineJ_com.
   (* positivity *)
  intros.
  hnf in H, H0.
  destruct a, a'; try contradiction; destruct b,b'; try contradiction; auto;
  try solve [destruct H; destruct H0; congruence].
  destruct H; destruct H0. 
  f_equal.
  destruct sh as [sh i]; destruct sh0 as [sh0 i0]; 
  destruct sh1 as [sh1 i1]; destruct sh2 as [sh2 i2].
  apply existT_ext. unfold ijoin in H,H0.
  eapply join_positivity; eauto. 
  eapply join_positivity; eauto. 
Qed.

Instance Sep_combiner: Sep_alg combiner.
Proof.
  apply mkSep with (fun _ => CEmpty).
  intros. hnf.  destruct t; auto.
  auto.
Defined.

Instance Sing_combiner: Sing_alg combiner.
Proof.
  apply (mkSing CEmpty).
  auto.
Defined.

Instance Canc_combiner {C1: Canc_alg T1}: Canc_alg combiner.
Proof. 
 repeat intro. eapply combineJ_canc; eauto.
Qed.

Instance Disj_combiner {D1: Disj_alg A}: Disj_alg combiner.
Proof. 
 repeat intro. eapply combineJ_self; eauto.
Qed.

(* Usefull facts about combiners *)

Lemma identity_combiner {C1: Canc_alg T1}: forall d : combiner,
  identity d -> 
  d = CEmpty.
Proof.
  intros.
  rewrite identity_unit_equiv in H.
  icase d.
  destruct H.
  destruct (ijoin_identity1 _ _ H).
Qed.

Lemma combiner_identity {C1: Canc_alg T1}:
  identity CEmpty.
Proof.
  intros.
  rewrite identity_unit_equiv.
  compute.
  trivial.
Qed.

Lemma combiner_full {C1: Canc_alg T1}: forall t2,
  full (CFull t2).
Proof.
  unfold full.  intros.
  destruct H as [sigma'' ?].
  icase sigma'.
  apply combiner_identity.
Qed.

(* This one is only true under various restrictions. *)
(*
Lemma full_combiner: forall (d : combiner),
  (* we require that As have complements *)
  (forall a : ijoinable, exists a' : ijoinable, join (projT1 a) (projT1 a') A_top) ->
  (* we require that T2 be nonempty *)
  forall (at2 : T2),
  full d ->
  {t2 : T2 | d = DFull t2}.
Proof.
  intros.
  icase d.
  3: exists v; trivial.
  spec H0 (DFull at2) (DFull at2).
  spec H0.
  apply identity_unit.
  apply combiner_identity.
  exists (DFull at2).
  compute. trivial.
  apply identity_combiner in H0.
  inversion H0.
  
  elimtype False.
  spec H sh.
  destruct H as [sh' ?].
  destruct (join_ex_identities v) as [v0 [? ?]].
  spec H0 ( sh' v0) (DFull .
  
  
  ad mit.
  exists v. trivial.
Qed.
*)

End CombineJoin.

Implicit Arguments combiner.
Implicit Arguments Join_combiner.
Implicit Arguments CEmpty.
Implicit Arguments CPart.
Implicit Arguments CFull.
Implicit Arguments identity_combiner.
Implicit Arguments combiner_identity.
Implicit Arguments combiner_full.

Section ParameterizedCombiner.

  Existing Instance Join_combiner.

  Variable S : Type.
  Variable JS : Join S.
  Variable pa_S : Perm_alg S.
  Variable sa_S : Sep_alg S.
  Variable ca_S : Canc_alg S.

  Variable T1 : Type -> Type.
  Variable J1: forall A, Join (T1 A).
  Variable Perm1: forall A, Perm_alg (T1 A).
  Variable Sep1: forall A, Sep_alg (T1 A).
  Variable f_T1 : functor T1.
  Variable T2 : Type -> Type.
  Variable f_T2 : functor T2.
 
  Definition fcombiner (A : Type) : Type := 
    @combiner S JS (T1 A) (T2 A).
 
  Definition fcombiner_fmap (A B : Type) (f : A -> B) 
    (fa : fcombiner A) : fcombiner B :=
      match fa with
        | CEmpty => CEmpty _ _ _ 
        | CPart sh rs => CPart _ sh (fmap f rs)
        | CFull trs => CFull _ _ (fmap f trs)
      end.
  Implicit Arguments fcombiner_fmap [A B].
  
  Lemma ff_combiner : functorFacts fcombiner fcombiner_fmap.
  Proof with auto.
    constructor; intros;
    extensionality pd; unfold fcombiner_fmap. 
    icase pd; rewrite fmap_id...
    icase pd; rewrite <- fmap_comp...
  Qed.
  
  Instance f_combiner : functor fcombiner := Functor ff_combiner.

  Variable top_S : S.
  Variable topS_full : full top_S.
  Variable combjoin : forall A, (T1 A) -> (T1 A) -> (T2 A) -> Prop.
  Variable combjoin_eq : forall A v1 v1' v2 v2', 
    combjoin A v1 v1' v2 ->
    combjoin A v1 v1' v2' ->
    v2 = v2'.
  Variable combjoin_assoc : forall A (v1 v2 v3 v4: T1 A) (v5: T2 A),
    join v1 v2 v3 ->
    combjoin A v3 v4 v5 ->
    {v' : (T1 A) & join v2 v4 v' /\ combjoin A v1 v' v5}.
  Variable combjoin_com : forall A v1 v2 v3,
    combjoin A v1 v2 v3 ->
    combjoin A v2 v1 v3.
  Variable combjoin_canc : forall A v1 v1' v2 v3,
    combjoin A v1 v2 v3 ->
    combjoin A v1' v2 v3 ->
    v1 = v1'.
  Variable saf_T1 : pafunctor f_T1.

  Instance Join_fcombiner (A: Type) : Join (fcombiner A) :=
    Join_combiner top_S (J1 A) (combjoin A).


  Instance Perm_fcombiner (A: Type): Perm_alg (fcombiner A).
  Proof. apply Perm_combiner; auto.
     apply combjoin_eq. apply combjoin_assoc.
  Defined.


  Instance Sep_fcombiner (A: Type): Sep_alg (fcombiner A).
  Proof. apply Sep_combiner; auto.
  Defined.

  Instance Canc_fcombiner (A: Type) (CA: Canc_alg (T1 A)): Canc_alg (fcombiner A).
  Proof.  apply Canc_combiner; auto. apply combjoin_canc.
  Qed.
    
  Definition combjoin_hom (A : Type) (B : Type)
    (f : T1 A -> T1 B) (g : T2 A -> T2 B) : Prop :=
      forall x y z, 
        combjoin A x y z -> 
        combjoin B (f x) (f y) (g z).
  Implicit Arguments combjoin_hom [A B].
  
  Variable fmaps_combjoin_hom: forall A B (f : A -> B),
    combjoin_hom (fmap f) (fmap f).

  Lemma fmap_fcombiner_hom: forall A B (f : A -> B),
    join_hom (JA := Join_fcombiner A) (JB := Join_fcombiner B) (fmap f).
  Proof with auto.
    repeat intro. hnf in H|-*.
    icase x; icase y; icase z.
    destruct H.
    split; congruence.
    simpl in H. subst v0. simpl...
    destruct H.
    split; congruence.
    destruct H.
    split...
    apply paf_join_hom...
    destruct H.
    split...
    apply fmaps_combjoin_hom...
    simpl in H. subst v0. simpl...
  Qed.
  
  Definition combjoin_unmap_left (A B : Type)
    (f : T1 A -> T1 B) (g : T2 A -> T2 B) : Type :=
      forall (x' : T1 B) (y :T1 A) (z : T2 A),
        combjoin B x' (f y) (g z) ->
        {x : T1 A &  {y0 : T1 A | combjoin A x y0 z /\ f x = x' /\ f y0 = f y}}.
  Implicit Arguments combjoin_unmap_left [A B].
  
  Variable combjoin_preserves_unmap_left : forall A B (f : A -> B),
    combjoin_unmap_left (fmap f) (fmap f).
  
  Definition combjoin_unmap_right (A B : Type)
    (f : T1 A -> T1 B) (g : T2 A -> T2 B) : Type :=
      forall (x y :T1 A) (z' : T2 B),
        combjoin B (f x) (f y) z' ->
        {y0 : T1 A &  {z : T2 A | combjoin A x y0 z /\ f y0 = f y /\ g z = z'}}.
  Implicit Arguments combjoin_unmap_right [A B].
  
  Variable combjoin_preserves_unmap_right : forall A B (f : A -> B),
    combjoin_unmap_right (fmap f) (fmap f).
  
  Lemma fmap_fcombiner_preserves_unmap_left: forall A B (f : A -> B),
    unmap_left (Join_fcombiner A) (Join_fcombiner B) (fmap f).
  Proof with auto.
    repeat intro. simpl in H|-*. unfold join in H|-*. simpl in H|-*.
    icase x'; icase y; icase z.
    exists (CEmpty _ _ _). exists (CEmpty _ _ _). firstorder.
    exists (CEmpty _ _ _). exists (CPart _ sh0 v0).
    destruct H. simpl.
    repeat split; congruence.
    exists (CEmpty _ _ _). exists (CFull _ _ v0).
    simpl in H. simpl.
    repeat split; congruence.
    exists (CPart _ sh v0). exists (CEmpty _ _ _).
    destruct H. simpl.
    repeat split; congruence.
    destruct H.
    generalize (paf_preserves_unmap_left f v v0 v1 H0); intro X.
    destruct X as [x [y0 [? [? ?]]]].
    exists (CPart _ sh x). exists (CPart _ sh0 y0).
    split. split...
    simpl. split; congruence.
    (* combjoin case *)
    destruct H.
    spec combjoin_preserves_unmap_left A B f v v0 v1 H.
    destruct combjoin_preserves_unmap_left as [x [y0 [? [? ?]]]].
    exists (CPart _ sh x). exists (CPart _ sh0 y0).
    split. split...
    simpl. split; congruence.
    (* end combjoin case *)
    exists (CFull _ _ v0). exists (CEmpty _ _ _).
    simpl in H. simpl.
    repeat split; congruence.
  Qed.

  Lemma fmap_fcombiner_preserves_unmap_right: forall A B (f : A -> B),
    unmap_right (Join_fcombiner A) (Join_fcombiner B) (fmap f).
  Proof with auto.
    repeat intro. simpl in H|-*. unfold join in H|-*. simpl in H|-*.
    icase x; icase y; icase z'.
    exists (CEmpty _ _ _). exists (CEmpty _ _ _). firstorder.
    exists (CPart _ sh v). exists (CPart _ sh v).
    destruct H. simpl.
    repeat split; congruence.
    exists (CFull _ _ v). exists (CFull _ _ v).
    simpl in H. simpl.
    repeat split; congruence.
    exists (CEmpty _ _ _). exists (CPart _ sh v).
    destruct H. simpl.
    repeat split; congruence.
    destruct H.
    generalize (paf_preserves_unmap_right f v v0 v1 H0); intro X.
    destruct X as [y0 [z [? [? ?]]]].
    exists (CPart _ sh0 y0). exists (CPart _ sh1 z).
    split. split...
    simpl. split; congruence.
    (* combjoin case *)
    destruct H.
    spec combjoin_preserves_unmap_right A B f v v0 v1 H.
    destruct combjoin_preserves_unmap_right as [y0 [z [? [? ?]]]].
    exists (CPart _ sh0 y0). exists (CFull _ _ z).
    split. split...
    simpl. split; congruence.
    (* end combjoin case *)
    exists (CEmpty _ _ _). exists (CFull _ _ v).
    simpl in H. simpl.
    repeat split; congruence.
  Qed.
  
 Instance paf_combiner: @pafunctor _ f_combiner Join_fcombiner.
 Proof.
    constructor.
    apply fmap_fcombiner_hom.
    apply fmap_fcombiner_preserves_unmap_left.
    apply fmap_fcombiner_preserves_unmap_right.
 Qed.

End ParameterizedCombiner.

Implicit Arguments fcombiner.
Implicit Arguments combjoin_hom [T1 T2 A B].
Implicit Arguments combjoin_unmap_left [A B T1 T2].
Implicit Arguments combjoin_unmap_right [A B T1 T2].
Implicit Arguments f_combiner [S JS T1 T2].
Implicit Arguments paf_combiner.

