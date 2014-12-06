(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.knot.
Require Import msl.ageable.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.
Require Import msl.sepalg_functors.
Require Import msl.age_sepalg.
Require Import msl.knot_sa.
Require Import msl.knot_lemmas.
Require Import msl.functors.
Require Import msl.sepalg_functors.
Require Import msl.knot_hered.
Require Import msl.knot_hered_sa.

(* This file specializes knot and sa_knot to have T = Prop *)

Open Local Scope nat_scope.

(*
  We get these from knot_hered and knot_hered_sa.

Module Type TY_FUNCTOR_PROP.
  Parameter F : Type -> Type.
  Parameter f_F : functor F.
  EXisting Instance f_F.

  Parameter other : Type.
End TY_FUNCTOR_PROP.

Module Type TY_FUNCTOR_SA_PROP.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.
  
  Parameter saf_F : safunctor f_F.
  EXisting Instance saf_F.
End TY_FUNCTOR_SA_PROP.
*)

Module Type KNOT_PROP.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.

  Parameter knot : Type.

  Parameter ag_knot : ageable knot. 
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition predicate := (knot * other) -> Prop.

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Definition approx (n:nat) (p:predicate) : predicate := 
     fun w => level w < n /\ p w.

  Axiom squash_unsquash : forall x, squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap (approx n) x').

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
End KNOT_PROP.

Module Type KNOT_SA_PROP.
  Declare Module TFSA:TY_FUNCTOR_SA_PROP.
  Declare Module K:KNOT_PROP with Module TF:=TFSA.TF.

  Import TFSA.TF.
  Import TFSA.
  Import K.

  Parameter Join_knot: Join knot.  Existing Instance Join_knot.
  Parameter Sep_knot : Sep_alg knot.  Existing Instance Sep_knot.
  Parameter Canc_knot : Canc_alg knot.  Existing Instance Canc_knot.
  Parameter Disj_knot :  Disj_alg knot.  Existing Instance Disj_knot.

  Instance Join_nat_F: Join (nat * F predicate) := 
       Join_prod nat  (Join_equiv nat) (F predicate) _.

 Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
    @Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F predicate _ (Perm_equiv _)).

 Instance Sep_nat_F (Sep_F: forall A, Sep_alg (F A)): Sep_alg (nat * F predicate) :=
    @Sep_prod nat _ _ _ (Sep_equiv _) (Sep_F predicate).
 Instance Canc_nat_F (Canc_F: forall A, Canc_alg (F A)): Canc_alg (nat * F predicate) :=
    @Canc_prod nat _ _ _ (Canc_equiv _) (Canc_F predicate).
 Instance Disj_nat_F (Disj_F: forall A, Disj_alg (F A)): Disj_alg (nat * F predicate) :=
    @Disj_prod nat _ _ _ (Disj_equiv _) (Disj_F predicate).

  Axiom join_unsquash : forall x1 x2 x3 : knot,
    join x1 x2 x3 = join (unsquash x1) (unsquash x2) (unsquash x3).

  Axiom asa_knot : Age_alg knot.
End KNOT_SA_PROP.

(* Coercion *)
Module TyFunctorProp2TyFunctor (TF : TY_FUNCTOR_PROP) <: TY_FUNCTOR.
(*  EXport TFP. Does not seem to work? *)
  Definition F := TF.F.
  Definition f_F := TF.f_F.
  
  Definition T: Type := Prop.
  Definition T_bot : T := False.

  Definition other := TF.other.
End TyFunctorProp2TyFunctor.

Module KnotProp (TF':TY_FUNCTOR_PROP) : KNOT_PROP with Module TF:=TF'.
  Module TF := TF'.
  
  Module TF_G := TyFunctorProp2TyFunctor(TF).

  Module Knot_G := Knot(TF_G).
  
  Import TF.
  Definition knot : Type := Knot_G.knot.
  Definition predicate := (knot * other) -> Prop.

  Definition squash : (nat * F predicate) -> knot :=
    Knot_G.squash.
  Definition unsquash : knot -> (nat * F predicate) :=
    Knot_G.unsquash.

  Definition ag_knot := Knot_G.ag_knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition approx (n:nat) (p:predicate) : predicate := 
     fun w => level w < n /\ p w.

  Lemma squash_unsquash : forall x, squash (unsquash x) = x.
  Proof.
    apply Knot_G.squash_unsquash.
  Qed.

  Lemma unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap (approx n) x').
  Proof.
    replace approx with Knot_G.approx.
    apply Knot_G.unsquash_squash.
    extensionality n p w.
    unfold approx, Knot_G.approx, TF_G.T_bot.
    case (le_gt_dec n (level w)); intro; apply prop_ext; firstorder.
    unfold knot, TF_G.other, ag_knot in *. omega.
  Qed.

  Definition knot_level := Knot_G.knot_level.
  Definition knot_age1 := Knot_G.knot_age1.
End KnotProp.

(* Coercion *)
Module KnotProp2Knot (TF' : TY_FUNCTOR_PROP) 
                                   (K : KNOT_PROP with Module TF := TF') <: 
                                     KNOT.
  Module TF := TyFunctorProp2TyFunctor(K.TF).
  Import TF.

  Definition knot : Type := K.knot.
  Definition predicate := (knot * other) -> T.

  Definition ag_knot : ageable knot :=
    K.ag_knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition squash : (nat * F predicate) -> knot :=
    K.squash.
  Definition unsquash : knot -> (nat * F predicate) :=
    K.unsquash.

  Definition approx (n:nat) (p:predicate) : predicate := 
     fun w => if le_gt_dec n (level w) then T_bot else p w.

  Lemma squash_unsquash : forall x, squash (unsquash x) = x.
  Proof.
    apply K.squash_unsquash.
  Qed.

  Lemma unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap (approx n) x').
  Proof.
    replace approx with K.approx.
    apply K.unsquash_squash.
    extensionality n p w.
    unfold approx, K.approx, TF.T_bot.
    case (le_gt_dec n (level w)); intro; apply prop_ext; firstorder.    
    unfold knot, ag_knot, other in *.
    omega.
  Qed.


  Definition knot_level := K.knot_level.
  Definition knot_age1 := K.knot_age1.
End KnotProp2Knot.

Module TyFunctorSaProp2TyFunctorSa (TF' : TY_FUNCTOR_SA_PROP) <: TY_FUNCTOR_SA.
  Module TF <: TY_FUNCTOR := TyFunctorProp2TyFunctor (TF'.TF).
  Import TF.

  Instance Join_T: Join T := Join_equiv T.
  Instance pa_T : Perm_alg T := Perm_equiv T.
  Instance sa_T : Sep_alg T := Sep_equiv T.
  Instance ca_T : Canc_alg T := Canc_equiv T.
  Instance da_T : Disj_alg T := Disj_equiv T.
  Lemma T_bot_identity : identity T_bot.
  Proof. firstorder. Qed.

  Instance Join_TF (A: Type) : Join (A -> T) := Join_fun A T Join_T.
  Instance pa_TF (A : Type) : Perm_alg (A -> T) := Perm_fun _ _ _ pa_T.
  Instance sa_TF (sa_T: Sep_alg T) (A : Type) : Sep_alg (A -> T) := Sep_fun _ _ _ sa_T.
  Instance ca_TF (ca_T: Canc_alg T) (A : Type) : Canc_alg (A -> T) := Canc_fun _ _ _ _. 
  Instance da_TF (da_T: Disj_alg T) (A : Type) : Disj_alg (A -> T) := Disj_fun _ _ _ _.

  Instance J_F (A: Type) : Join (F (A -> T)) := TF'.Join_F (A -> T).
  Instance Perm_F (A : Type) : Perm_alg (F (A -> T)) := TF'.Perm_F (A -> T) _ _.

  Instance Sep_F (A : Type) : Sep_alg (F (A -> T)).
  Proof. 
    apply (TF'.Sep_F _ (Join_TF A)); auto with typeclass_instances.
  Defined.
  Instance Canc_F (A : Type) : Canc_alg (F (A -> T)).
  Proof. 
    apply (TF'.Canc_F _ (Join_TF A)); auto with typeclass_instances.
  Qed.
  Instance Disj_F (A : Type) : Disj_alg (F (A -> T)).
  Proof. 
    apply (TF'.Disj_F _ (Join_TF A)); auto with typeclass_instances.
  Qed.

  Lemma fmap_hom : forall A B (f: (A -> T) -> (B -> T)),
    join_hom f -> join_hom (fmap f).
  Proof. intros. unfold F, J_F. apply paf_join_hom. Qed.
  Implicit Arguments fmap_hom.

  Lemma F_preserves_unmaps_left : forall A B (f : (A -> T) -> (B -> T)) 
    (Hhom : join_hom f),
    unmap_left _ _ f ->
    unmap_left _ _ (fmap f).
  Proof. intros. unfold F, J_F. apply paf_preserves_unmap_left. Qed.
  Implicit Arguments F_preserves_unmaps_left.

  Lemma F_preserves_unmaps_right : forall A B (f : (A -> T) -> (B -> T)) 
    (Hhom : join_hom f),
    unmap_right _ _ f ->
    unmap_right _ _ (fmap f).
  Proof. intros. unfold F, J_F. apply paf_preserves_unmap_right. Qed.
  Implicit Arguments F_preserves_unmaps_right.

  Lemma T_bot_unit : unit_for T_bot T_bot.
   Proof. unfold T_bot. split; auto. Qed.
End TyFunctorSaProp2TyFunctorSa.

Module KnotSaProp (TFSA':TY_FUNCTOR_SA_PROP) 
                               (K':KNOT_PROP with Module TF:=TFSA'.TF) : 
                                   KNOT_SA_PROP with Module TFSA:=TFSA' 
                                                              with Module K:=K'.
  Module TFSA <: TY_FUNCTOR_SA_PROP := TFSA'.
  Module K <: KNOT_PROP with Module TF:=TFSA'.TF := K'.

  Import TFSA.TF.
  Import TFSA.
  Import K.
  
  Module TFSA_G := TyFunctorSaProp2TyFunctorSa(TFSA').
  Module K_G <: KNOT with Module TF := TFSA_G.TF := KnotProp2Knot TFSA'.TF K'.
  
  Module KnotSa_G := KnotSa TFSA_G K_G.

  Instance Join_knot: Join knot := KnotSa_G.Join_knot.
  Instance Perm_knot : Perm_alg knot := KnotSa_G.Perm_knot.
  Instance Sep_knot : Sep_alg knot := KnotSa_G.Sep_knot _.
  Instance Canc_knot : Canc_alg knot := KnotSa_G.Canc_knot _.
  Instance Disj_knot : Disj_alg knot := KnotSa_G.Disj_knot _.


  Instance Join_nat_F: Join (nat * F predicate) := 
       Join_prod nat  (Join_equiv nat) (F predicate) _.

 Instance Perm_nat_F : Perm_alg (nat * F predicate) :=
    @Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F predicate _ (Perm_equiv _)).

 Instance Sep_nat_F (Sep_F: forall A, Sep_alg (F A)): Sep_alg (nat * F predicate) :=
    @Sep_prod nat _ _ _ (Sep_equiv _) (Sep_F predicate).
 Instance Canc_nat_F (Canc_F: forall A, Canc_alg (F A)): Canc_alg (nat * F predicate) :=
    @Canc_prod nat _ _ _ (Canc_equiv _) (Canc_F predicate).
 Instance Disj_nat_F (Disj_F: forall A, Disj_alg (F A)): Disj_alg (nat * F predicate) :=
    @Disj_prod nat _ _ _ (Disj_equiv _) (Disj_F predicate).

  Lemma join_unsquash : forall x1 x2 x3,
    join x1 x2 x3 =
    join (unsquash x1) (unsquash x2) (unsquash x3).
  Proof.
  apply KnotSa_G.join_unsquash.
  Qed.

  Definition asa_knot := KnotSa_G.asa_knot _.

End KnotSaProp.

Module KnotProp_Lemmas (K:KNOT_PROP).
  Import K.
  Import K.TF.

  Module K' := KnotProp2Knot(K.TF)(K).
  Module KL := Knot_Lemmas(K').

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    intros.
    rewrite <- (squash_unsquash k1).
    rewrite <- (squash_unsquash k2).
    rewrite H.
    trivial.
  Qed.
  Implicit Arguments unsquash_inj.
  
  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    intros.
    remember (unsquash k).
    destruct p.
    exists n.
    exists f.
    rewrite Heqp.
    rewrite squash_unsquash.
    trivial.
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap (approx n) Fp.
  Proof.
    intros.
    generalize H; intro.
    rewrite <- (squash_unsquash k) in H.
    rewrite H0 in H.
    rewrite unsquash_squash in H.
    inversion H.
    rewrite H2.
    symmetry.
    trivial.
  Qed.
  Implicit Arguments unsquash_approx.
  
  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    intros.
    extensionality p x; destruct x as [k o].
    unfold approx, compose; simpl.
    apply prop_ext; intuition.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros.
    extensionality p x; destruct x as [k o].
    unfold approx, compose; simpl.
    apply prop_ext; intuition.
  Qed.

  (* These are provided since sometimes it is tedious to break things out;
      they are not interesting except as engineering artifacts. *)
  Lemma unsquash_squash_unfolded : forall nf,
    unsquash (squash nf) = (fst nf, fmap (approx (fst nf)) (snd nf)).
  Proof.
    intros.
    destruct nf.
    apply unsquash_squash.
  Qed.
	
  Lemma unsquash_approx_unfolded : forall k,
    unsquash k = (fst (unsquash k), fmap (approx (fst (unsquash k))) (snd (unsquash k))).
  Proof.
    intros.
    case_eq (unsquash k); intros.
    simpl.
    apply injective_projections; simpl; trivial.
    apply (unsquash_approx H).
  Qed.

End KnotProp_Lemmas.
