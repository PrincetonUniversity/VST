(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Disjoint Sets data-structure. 

   The signature [DISJOINTSETS] describes a disjoint-sets data
   structure, to maintain work with sets of equivalence classes. 

   The functor [DISJOINTSETSUTILS] provides several useful lemmas to
   reason about these equivalences classes.

   The module [PosDisjointSets] implements [DISJOINTSETS] for
   [positive] numbers, as described in [1]. We implemented two
   heuristics: path-compression and union by rank. 
   
   [1] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and
   Clifford Stein. Introduction to Algorithms. The MIT Press, 2nd
   revised edition edition, September 2001.  

   TODO: the proofs in this file should be cleaned and made more robust.

   *)

Require Import Common.
Require Import MyFSets.
Require Import BoolView.
Require Import Numbers. 

Module Type DISJOINTSETS (N : NUM).
  Import N.

  Variable T: Type.
  Variable empty : T.
  
  Variable test_and_unify : T -> num -> num -> bool * T.
  Variable equiv : T -> num -> num -> bool * T.
  Variable union : T -> num -> num -> T.

  Variable class_of : T -> num -> NumSet.t.

  Parameter IsWF : T -> Prop.
  Class WF t: Prop := { wf: IsWF t }.

  Declare Instance empty_WF : WF empty.
  Declare Instance test_and_unify_WF `{WF} x y: WF (snd (test_and_unify t x y)).
  Declare Instance equiv_WF `{WF} x y : WF (snd (equiv t x y)).
  Declare Instance union_WF `{WF} x y : WF (union t x y).
  
  Parameter sameclass: T -> relation num.
  Hypothesis sameclass_equiv : forall `{WF} x y, (fst (equiv t x y) = true <-> sameclass t x y).
  Declare Instance sameclass_Equivalence `{WF}: Equivalence (sameclass t).

  Hypothesis sameclass_empty : forall x y, sameclass empty x y -> x = y.
  Hypothesis sameclass_union : forall `{WF} a b x y, 
    sameclass (union t a b) x y <-> 
    (sameclass t x y \/ (sameclass t x a /\ sameclass t y b) \/ (sameclass t y a /\ sameclass t x b)).
 
  Hypothesis sameclass_class_of : forall `{WF} x y , sameclass t x y <-> NumSet.In x (class_of t y).
 
  Hypothesis test_and_unify_eq: forall `{WF} x y, test_and_unify t x y = (fst (equiv t x y), union t x y).
  
End DISJOINTSETS.

Module DSUtils (Import N : NUM) (Import M: DISJOINTSETS N).
  Module Import NU :=  NumUtils N.

  Definition le (s t : T): Prop := inclusion _ (sameclass s) (sameclass t).

  Instance le_PreOrder : PreOrder le.
  Proof. constructor; repeat intro; auto. Qed.

  Definition eq s t := same_relation _ (sameclass s) (sameclass t). 
  Instance eq_Equivalence : Equivalence eq.
  Proof. 
    unfold eq, same_relation. constructor; repeat intro.
    split; apply le_PreOrder. 
    tauto. 
    split; apply (@PreOrder_Transitive _ _ le_PreOrder) with y; intuition. 
  Qed.
  Instance sameclass_compat : Proper (eq ==> same_relation num) sameclass.
  Proof. intros s t H. exact H. Qed.

  Instance sameclass_compat' : Proper (eq ==> @Logic.eq num ==> @Logic.eq num ==> iff) sameclass.
  Proof. split; intros; subst; apply H; trivial. Qed.

  Module Notations.
    Notation "{{ t }}" := (sameclass t). 
    Notation "x  [=T=]  y" := (eq x y) (at level 75).
    Notation "x  <T= y" := (le x y) (at level 75).
  End Notations.

  Import Notations.

  Lemma le_union `{WF}: forall x y, t <T= union t x y.
  Proof.
    intros x y. 
    unfold le. 
    intros a b ? .
    rewrite sameclass_union; trivial. intuition.
  Qed.

  Lemma eq_union `{WF}: forall x y, {{t}} x y -> t [=T=] union t x y.
  Proof.
    intros x y Hxy.
    split. apply le_union; trivial.
    intros a b H'. rewrite sameclass_union in H'; trivial. intuition. 
     rewrite H0, Hxy, H2. reflexivity.
     rewrite H0, Hxy, H2. reflexivity.
  Qed.

  Lemma le_incr `{WF} {t'} `{WF t'}: forall x y,  
    t <T= t' ->
    union t x y <T=  union t' x y. 
  Proof. 
    intros x y ? u v. rewrite 2 sameclass_union. intuition.   
  Qed.

  Lemma compat_union_eq `{WF} {t'} `{WF t'} : 
    t [=T=] t' -> 
    forall x y, union t x y [=T=] union t' x y.
  Proof.
    intros H' x y.
    split; intros; apply le_incr; auto; apply H'.
  Qed.


  Lemma class_of_empty: forall x, NumSet.Equal (class_of empty x) (NumSet.singleton x).
  Proof.
    intros x y.
    rewrite <- sameclass_class_of. 
    split; intros H. rewrite (sameclass_empty _ _ H). auto with set.
    replace y with x. reflexivity.
    apply -> set_eq_spec. 
    apply NumSet.singleton_1, H. 
  Qed.
    
  Lemma class_of_union: forall `{WF} x y, 
    NumSet.Equal (class_of (union t x y) x) (NumSet.union (class_of t x) (class_of t y)).
  Proof.
    intros t Hwf x y z.
    rewrite <- sameclass_class_of. 
    rewrite sameclass_union.
    NumSetProps.set_iff.
    setoid_rewrite <- sameclass_class_of. 
    intuition.
  Qed.

  Lemma class_of_union_2: forall `{WF} x y z, 
    ~ sameclass t x z ->
    ~ sameclass t y z ->
    NumSet.Equal (class_of (union t x y) z) (class_of t z).
  Proof.
    intros t Hwf x y z Hxz Hyz u.
    setoid_rewrite <- sameclass_class_of.
    rewrite sameclass_union.
    intuition.
  Qed.

  Lemma in_class_of_self: forall `{WF} x, NumSet.In x (class_of t x).
  Proof.
    intros. rewrite <- sameclass_class_of. reflexivity. 
  Qed.

  Instance class_of_compat `{WF} : Proper (sameclass t ==> NumSet.Equal) (class_of t). 
  Proof. 
    intros x y Hxy z. 
    setoid_rewrite <- sameclass_class_of.
    rewrite Hxy. reflexivity.
  Qed.
    
  Lemma class_of_compat' : forall `{WF} {t'} `{WF t'} x, 
    eq t t' -> 
    NumSet.Equal (class_of t x) (class_of t' x).
  Proof.
    intros t Ht t' Ht' x H y.
    setoid_rewrite <- sameclass_class_of.
    rewrite H. reflexivity.
  Qed.

  Lemma class_of_union_1: forall `{WF} x y z, 
    {{t}} x z \/ {{t}} y z ->
    NumSet.Equal (class_of (union t x y) z) (NumSet.union (class_of t x) (class_of t y)).
  Proof.
    intros t Hwf x y z [H|H]; symmetry in H.
     setoid_replace (class_of (union t x y) z) with (class_of (union t x y) x) by
      (apply class_of_compat; rewrite sameclass_union; auto).
     apply class_of_union; trivial. 
     setoid_replace (class_of (union t x y) z) with (class_of (union t x y) y) by
      (apply class_of_compat; rewrite sameclass_union; auto).
     rewrite <- class_of_union by trivial.
     apply class_of_compat. symmetry. rewrite sameclass_union by trivial.
     right. left. split; reflexivity. 
  Qed.

  Lemma class_of_injective: forall `{WF} x y, 
    NumSet.Equal (class_of t x) (class_of t y) -> {{t}} x y.
  Proof.
    intros.
    assert (NumSet.In y (class_of t y)).  
      rewrite <- sameclass_class_of. reflexivity.
    rewrite <- H0 in H1.
    rewrite <- sameclass_class_of in H1.
    symmetry. auto.
  Qed.

  Lemma sameclass_spec `{WF} x y: reflect ({{t}} x y) (fst (equiv t x y)).
  Proof.
    intros. case_eq (fst (equiv t x y)); intro Heq; constructor.
     rewrite <- sameclass_equiv; trivial.
     intro F. rewrite <- sameclass_equiv in F. rewrite F in Heq. discriminate.
  Qed.

End DSUtils.

Module PosDisjointSets <: DISJOINTSETS Positive.

  Import PositiveUtils.
  Module Z := FMapFacts.OrdProperties NumMap. (* TODO: réellement utile depuis les inductions de thomas ? *)
  Section protect.

  Open Scope nat_scope. Notation S := Datatypes.S.
  Definition num := num.
  Definition eq_num := @eq num.
  Notation "M '[' key ']' " := (NumMap.find key M)(at level 0, no associativity).
  Notation "M '[' key '>-' v ']' " := (NumMap.add key v M)(at level 0, no associativity).
  Notation "'[]'" :=(NumMap.empty _).
  
  Structure UF :=
    { 
      p : NumMap.t num; 
      rank : NumMap.t num;
      size : nat  
    }.
  
  Definition T := UF.
  
  Definition empty : T :=
    Build_UF 
    []
    []
    (S O).
  
  Fixpoint find_aux n x t :=
    match n with
      | (S n) => match t [x] with
                   | None => (x, t)
                   | (Some y) => 
                     let (ry, t) := find_aux n y t in 
                       (ry, t  [x>- ry]  )
                 end
      | O => (x,t)
    end.
  
  Definition find t x :=
    let (rx,t') := find_aux (size t) x (p t) in 
      (rx, Build_UF t' (rank t) (size t)).
  
  
  Definition get_rank x rank := 
    match  rank [x] with 
      | None => 1%positive 
      | Some rx => rx
    end.
  
  Definition link t x y :=
    let rank := rank t in 
    let rx := get_rank x rank in 
    let ry := get_rank y rank in 
    let p := p t in
      match (compare rx ry) with
           | Lt =>
             Build_UF 
             (p [x >- y])
             rank
             (S (size t))
           | Eq =>
             Build_UF 
             (p [x >- y])
             (rank [y >- Positive.S ry] )
             (S (size t))
           | Gt =>
             Build_UF 
             (p [y >- x])
             rank
             (S (size t))
         end
     .

  Definition union t x y :=
    let (rx,t) := find t x in 
    let (ry,t) := find t y  in 
      if Positive.eqb rx ry then t else link t rx ry.
   
  Definition equiv  t x y :=
    let (rx,t) := find  t x in 
    let (ry,t) := find  t y  in 
     (Positive.eqb rx ry,t).
      
  Definition test_and_unify t x y := 
    let (rx,t) := find  t x in 
    let (ry,t) := find  t y  in 
      if Positive.eqb rx ry then (true,t) else (false, link t rx ry).        


  Import NumMapProps. 
  
  Inductive repr (t: NumMap.t num) : num -> num -> Prop :=
  | rzero : forall i, ~ NumMap.In i t -> repr t i i
  | rsucc : forall i j r, NumMap.MapsTo i j t -> repr t j r -> repr t i r
    .
     
  Inductive D (t: NumMap.t num) : num -> nat -> Prop :=
  | DO : forall i, ~NumMap.In i t -> D t i O
  | DS : forall  i j n, NumMap.MapsTo i j t -> D t j n -> D t i (S n).
       
  Definition Equiv t x y  := exists2 z, repr t x z & repr t y z. 
  
  Definition FEquiv t t' := forall x y, repr t x y  <-> repr t' x y .
       
  Definition bounded t n:= forall x, exists2 m, D t x m & m < n.
  
  Section repr.
    Variable t : NumMap.t num.
    
    Lemma repr_zero_inv : forall i x,  i <> x -> ~NumMap.In i t -> ~ repr t i x.
    Proof. 
      intros i x Hix H. intro H'; inversion H'. subst. tauto_false.  subst. apply H. eexists. eassumption.
    Qed.
         
    Lemma repr_inj_right : forall a b, repr t a b -> forall c,  repr t a c -> b = c. 
    Proof.
      induction 1; intros. inversion H0. trivial. 
      find_tac.
      
      inversion H1. subst. find_tac. subst. find_tac. eauto.
    Qed.
    
    Lemma repr_inv_In : forall a b, repr t a b -> ~ NumMap.In b t.
    Proof.
      induction 1; auto. 
    Qed.
         
    Lemma repr_inj_idem : forall i j , repr t i j -> forall r, repr t j r  -> j = r.  Proof.
      induction 1;  inversion 1; subst; firstorder.
    Qed.
    
    Lemma DO_inv_In : forall x , D t x O -> ~ NumMap.In x t. 
    Proof. 
      inversion 1; auto. 
    Qed. 
    
    Hint Resolve repr_inv_In DO_inv_In.   
    
    Lemma D_repr : forall x, D t x O <-> repr t x x. 
    Proof.
      intros  x; split;   constructor; eauto.     
    Qed.
    
    Lemma D_inv_n : forall x y n, D t y O -> D t x (S n) -> x <> y. 
    Proof. inversion 1; subst. inversion 1.  subst.
      intro. subst. firstorder.
    Qed.
      
    Lemma repr_idem : forall x rx, repr t x rx -> repr t rx rx. 
    Proof.
      intros x rx H. apply repr_inv_In in H.   apply rzero. eauto.
    Qed.
    
    Lemma D_succ : forall x y n, NumMap.MapsTo x y t -> D t x n -> exists2 m, D t y m & n = S m.
    Proof.
      intros  x y n H. inversion_clear 1. 
      firstorder.
      find_tac. exists n0; firstorder.
    Qed.
    Lemma D_inj : forall x n , D t x n -> forall m, D t x m -> n = m. 
    Proof.
      induction 1;  inversion_clear 1; find_tac.  apply IHD in H3.  congruence.
    Qed.        
    
    Lemma repr_D : forall i j, repr t i j -> exists n, D t i n.
    Proof.
      induction 1. exists O. apply DO. auto. 
      destruct IHrepr. exists (S x). eapply DS; eauto. 
    Qed.

    Lemma update_In : forall i a b, repr t a b -> a <> b -> ~NumMap.In i t -> ~NumMap.In i (t [a >- b]).
    Proof. 
      clear. intros. map_iff. intros [H' | H']. subst. revert H. apply repr_zero_inv; auto. tauto.
    Qed.
  End repr.

  Lemma D_update : forall x y t, x <> y -> D t y 0 -> D (t [x>- y]) y 0.
  Proof.  
    intros x y t' Hxy H.  
    rewrite D_repr. 
    apply rzero.  map_iff.  
    intros [H' | H']; 
      [
        subst;  tauto_false 
        | inversion H ;  eauto
      ]. 
  Qed.
  
  Hint Resolve repr_idem DO_inv_In D_inv_n repr_D D_update update_In repr_inv_In.
  Lemma FEquiv_D : forall t t', FEquiv t t' -> (forall x, D t x O <-> D t' x O).
  Proof. 
    intros . unfold FEquiv in H.
    rewrite  2 D_repr.  apply H. 
  Qed.
  
  Instance FEquiv_eq : Equivalence FEquiv.
  Proof.
    unfold FEquiv.
    repeat constructor; try solve [firstorder].
    intro. simpl in *. rewrite <- H0 , <- H. auto.
    intro. simpl in *. rewrite  H , H0. auto.
  Qed.
  
  Instance repr_compat : Proper (FEquiv ==> (@eq num) ==> (@eq num)==> iff) repr.
  Proof.
    repeat intro. subst.  unfold FEquiv in H. rewrite H. auto. reflexivity.
  Qed.

  Section update.
    Variable t : NumMap.t num.
    Variable a b : num.
    Hypothesis a_diff_b: a <> b.
    Hypothesis a_repr_b: repr t a b.
    
    Lemma update_equiv : FEquiv t (t [a >- b ]).
    Proof.
      unfold FEquiv. intros x y. split; intro H.
      induction H. apply rzero. eauto.           
      destruct (eq_num_dec i a). subst. 
      assert (r=b). 
      eapply repr_inj_right. eapply rsucc. apply H. auto. auto. subst.
      eapply rsucc.  2 : apply rzero. map_iff. tauto. eauto.  
      
      eapply rsucc. 2 : apply IHrepr. map_iff. intuition.
      
      induction H.
      apply rzero. revert H. map_iff. intros. intro H'. apply H. auto.
      revert H. map_iff. intros [[H'  H''] | H'].  subst.
      
      assert (j = r). eapply repr_inj_idem;  eauto. subst. eauto.
      destruct H'.  eapply rsucc; eauto. 
    Qed.
    
    Lemma D_update_ex : forall x n, D t x n -> exists2 m, D (t [a>-b]) x m & m <= n.
    Proof. 
      induction 1. 
      exists O; auto using DO.  
      
      destruct (eq_num_dec i a). subst. 
      exists (S O). apply (DS _ _ b). map_iff. auto. apply DO.
      eauto.
      omega.
      
      destruct (IHD). exists (S x). eapply DS. 2 : eauto. map_iff. auto. omega.
    Qed.
    
    
    Lemma boundage : forall n, bounded t n -> 
      bounded (t [a>- b]) n.
    Proof.
      unfold bounded. intros. 
      destruct (H x). destruct (D_update_ex _ _ H0). exists x1. auto. omega.
    Qed.
  End update.
  
  Section link.
    Variable t : NumMap.t num.
    Variables a b : num.
    Hypothesis a_diff_b : a <> b.
    Hypothesis repr_a : repr t a a.
    Hypothesis repr_b : repr t b b.
    Lemma D_link_ex : forall x n, D t x n -> exists2 m, D (t [a>-b]) x m & m <= S n.
    Proof. 
      induction 1. 
      destruct (eq_num_dec i a). subst.      
      exists 1. apply (DS _ _  b).
      map_iff. auto. apply DO.
      map_iff; intros [H' | H']; subst. tauto_false. revert H'. eapply repr_inv_In. eauto.
      omega. 
      exists O. apply DO. map_iff.
      intros [H' | H']; subst; tauto_false. 
      omega.
      destruct (eq_num_dec i a). subst.
      exists 1. apply (DS _ _  b).  map_iff. auto. apply DO. map_iff. 
      intros [H' | H']. subst. tauto_false. 
      revert H'. eapply repr_inv_In. eauto. omega.   
      destruct IHD. exists (S x). eapply DS.  2 : eauto. map_iff. auto. omega. 
    Qed.  
    
    Lemma boundage_link : forall n, bounded t n ->  bounded (t [a>- b]) (S n).
    Proof.
      unfold bounded. intros. 
      destruct (H x). destruct (D_link_ex _ _ H0). exists x1. auto. omega.
    Qed.
    
    Lemma repr_update_fwd :
      forall y, repr t y b -> repr (t[ b>- a]) y a.
    Proof.
      induction 1.
      apply (rsucc _ i a). map_iff; auto. apply rzero. map_iff.
      intros [H' | H']. subst. tauto_false. 
      revert H'. eapply repr_inv_In. eauto.
      destruct (eq_num_dec i r). 
      subst. apply (rsucc _ r a). map_iff; auto. apply rzero. eauto. 
      
      eapply rsucc. 2: apply IHrepr; auto. map_iff. auto.
    Qed.

    Lemma repr_x_inv_upd :
      forall x,
        repr t x a -> repr (t[ b>- a]) x a.
      
    Proof.
      induction 1. 
      
      apply rzero. map_iff; intros [H' | H']; subst; tauto_false.  
      destruct (eq_num_dec i b). 
      subst. apply (rsucc _ b r).  map_iff; auto. 
      apply rzero. eauto. 
      eapply rsucc. 2 : apply IHrepr; auto. map_iff; auto.
    Qed.
    
    Lemma link_lemma_1 :
      forall z, 
        repr (t[ b>- a]) z a -> (repr t z a \/ repr t z b).
    Proof.
      induction 1.
      left. apply rzero. intro; apply H. map_iff; auto.
      destruct (eq_num_dec i b).
      subst. right; apply rzero. eapply repr_inv_In.   eauto.
      revert H. map_iff. intros [[H'  H''] | [H' H'']].  subst. tauto_false.
      destruct IHrepr. left; eapply rsucc; eauto. right; eapply rsucc; eauto.
    Qed.
    
    
    Lemma link_lemma_2 :
      forall z rz, repr (t[ b>- a]) z rz -> rz<>a ->
        repr t z rz.
    Proof.
      induction 1; intros. apply rzero. intro; apply H. map_iff; auto.
      revert H1; map_iff. completer subst.  
      
      eapply rsucc; eauto.
      revert H; map_iff; intuition subst.
      assert (j = r). eapply repr_inj_right. eapply repr_a. eauto. subst. tauto_false.
    Qed.
    
    Lemma repr_inv_upd : 
      forall z rz, repr t z rz -> rz<>b ->
        repr (t[ b>- a]) z rz.
    Proof.
      induction 1; intros. 
      apply rzero. map_iff. intros [H' | H']; subst;  tauto_false.
      destruct (eq_num_dec i b); subst.
      apply repr_inv_In in repr_b. firstorder.
      eapply rsucc. 2 : eapply IHrepr; auto. map_iff. auto. 
    Qed.
    Hint Resolve repr_x_inv_upd repr_inv_upd link_lemma_1 link_lemma_2 repr_update_fwd.
    
    Lemma link_main_lemma :
      forall x y,
        repr t x a -> repr t y b -> 
        forall u v, 
          (Equiv (t[ b>- a]) u v <->
            (Equiv t u v \/ ((Equiv t u x /\ Equiv t v y) \/             (Equiv t v x /\ Equiv t u y)))).
    Proof.
      split; intros. 
      unfold Equiv in H1. 
      destruct H1 as [ruv Hu Hv].
      destruct (eq_num_dec ruv a).
      subst.
      destruct (link_lemma_1 _ Hu);
        destruct (link_lemma_1 _ Hv); try solve [firstorder].
      apply link_lemma_2 in Hu; auto.              apply link_lemma_2 in Hv; auto.        firstorder.          
      
      destruct H1 as [[ruv Hu Hv] | [[[ru Hu Hx] [rv Hv Hy]] | [[ru Hu Hx] [rv Hv Hy]]]].
      destruct (eq_num_dec ruv a).
      subst. exists a; eauto.  
      destruct (eq_num_dec ruv b). subst.
      exists a; firstorder.  
      exists ruv; firstorder.
      
      assert ( Hrua := repr_inj_right _ _ _ H _ Hx).
      assert ( Hrvb := repr_inj_right _ _ _ H0 _ Hy).
      rewrite <- Hrua, <- Hrvb in *. clear Hrua Hrvb.  exists a. firstorder.  
      firstorder.
      
      assert ( Hrua := repr_inj_right _ _ _ H _ Hx).
      assert ( Hrvb := repr_inj_right _ _ _ H0 _ Hy).
      rewrite <- Hrua, <- Hrvb in *. clear Hrua Hrvb.  exists a. firstorder.  
      firstorder.
    Qed.
  End link.
  

  Section find_aux.
    Lemma find_equiv : forall n s t x y t' px, 
      find_aux n x t = (y,t') ->
      D t x px ->
      px < n ->
      bounded t s ->
      (
        D t' y O /\ 
        (x = y \/ NumMap.MapsTo x y t') /\ 
        FEquiv t t' /\
        bounded t' s
      ).
    Proof.
      induction n; intros s t0 x y t' px Hxt Hx Hpx Hwf. 
      omega_false.
      simpl in Hxt.
      find_analyse.
      case_eq (find_aux n x0 t0). intros p' t'' H'. rewrite H' in *. injection Hxt. intros. subst. clear Hxt. 
      
      destruct (D_succ _ _ _ _ H Hx).  subst . 
      destruct (IHn s _ _ _ _ _ H' H0) as [Hy [[Hxy | Hxy] [Heq Hwf']] ] . omega. auto.
      subst. 
      assert (x <> y).
      eapply D_inv_n. 2:eauto. rewrite FEquiv_D; eauto. 
      assert (repr t'' x y).
      rewrite <- Heq. eapply rsucc; eauto. rewrite <-  D_repr.  rewrite FEquiv_D; eauto.
      split; simpl.
      apply D_update;  auto.
      split.
      right; map_iff; auto.
      split.
      rewrite Heq; apply update_equiv; auto.
      
      apply boundage; auto. 
      
      assert (x <> y).
      eapply (D_inv_n  t0); eauto. rewrite FEquiv_D; eauto. 
      assert (repr t'' x y).
      rewrite <- Heq. eapply rsucc; eauto. rewrite Heq. eapply rsucc; eauto. rewrite <- D_repr. auto.
      split; simpl.
      eapply D_update; eauto.
      split.
      right; map_iff; auto.
      split.              
      rewrite Heq; apply update_equiv; auto. 
      apply boundage; auto.
      
      dependent destruction Hxt.
      intuition. rewrite D_repr.  eapply rzero. eauto.
    Qed.
  
  End find_aux.

  Section WF.
    Definition IsWF t : Prop := bounded (p t) (size t).
    Class WF t: Prop := { wf : IsWF t }.
    Hint Constructors WF.
  
    Inductive find_spec_decl t x : (num * T) -> Type :=
    | find_spec_1 : forall rx t'
      (Heq:FEquiv (p t) (p t'))
      (Hrepr: repr (p t') x rx)
      (Hwf: WF t'),
      find_spec_decl t x (rx,t').
  
    Lemma find_spec : forall `{WF} x, find_spec_decl t x (find t x).
    Proof. 
      intros t Hwf x.
      case_eq (find t x) ; intros rx t' H.
      unfold find in H.
      case_eq (find_aux (size t) x (p t)). intros rx' t'' H'; rewrite H' in *.   injection H. intros; subst. clear H.
      constructor; 
      destruct (@wf _ Hwf x) as [n Hxn Hn];
      destruct (find_equiv _ (size t) _ _ _ _ _ H' Hxn Hn) as [Hrx [[?|?] [Heq Hb]]];  subst; simpl; auto; try apply Hwf.
      rewrite <- D_repr. auto.
      eapply rsucc.  eauto. rewrite <- D_repr. auto.
    Qed.    
  
    Global Instance empty_WF : WF empty.
    Proof.
      constructor; exists O; [apply DO; map_iff; auto| auto].
    Qed.
  
    Global Instance find_WF `{WF} x: WF (snd (find t x )).
    Proof. 
      case find_spec; auto.
    Qed.
  
    Global Instance equiv_WF `{WF} x y: WF (snd (equiv t x y)).
    Proof.
      unfold equiv.
      repeat (case find_spec; auto; intros).
    Qed.
  
    Instance link_WF `{WF} x y : repr (p t) x x -> repr (p t) y y -> x<> y -> WF (link t x y).
    Proof.
      intros Hx Hy Hxy. unfold link. constructor.
      case compare_spec; intro; simpl; apply boundage_link; auto; apply H.
    Qed. 
    
    Global Instance union_WF `{WF} x y: WF (union t x y).
    Proof.
      unfold union.
      repeat (case find_spec; auto; intros).
      num_analyse; subst; auto. 
      assert (repr (p t'0) rx0 rx0).   eauto.
      assert (repr (p t'0) rx rx). rewrite Heq0 in *.  eauto. apply link_WF;  auto.
    Qed.
  
    Global Instance test_and_unify_WF `{WF} x y: WF (snd (test_and_unify t x y)).
    Proof.
      unfold test_and_unify. 
      repeat (case find_spec; auto; intros). 
      num_analyse. subst. simpl.  auto. 
      assert (repr (p t'0) rx0 rx0).   eauto.
      assert (repr (p t'0) rx rx). rewrite Heq0 in *.  eauto. apply link_WF;  auto.
    Qed.  
  End WF.
  
  Lemma repr_helper `{WF} x: exists z, repr (p t) x z. 
  Proof.
    destruct (@wf _ H x). clear H1.
    induction H0. exists i. apply rzero. auto.
    destruct IHD. exists x. eapply rsucc; eauto. 
  Qed.

  Section Equiv. 
    Definition sameclass t x y := Equiv (p t) x y.

    Lemma Equiv_empty :  forall m s t,NumMap.Empty m -> Equiv m s t -> s = t.
    Proof.
      intros m s t He [x H H']. 
      
      inversion_clear H; inversion_clear H'; subst; trivial.
      firstorder.
      firstorder.
      firstorder.
    Qed.

    Lemma sameclass_empty : forall s t, sameclass empty s t -> s = t.
    Proof. 
      intros. refine (Equiv_empty _ _ _ _ H). simpl.
      apply NumMap.empty_1.
    Qed.

    Instance Equiv_compat : Proper (FEquiv ==> @eq num ==> @eq num ==> iff ) Equiv.
    Proof.
      repeat intro.
      subst. unfold FEquiv in H. unfold Equiv. split; intros [rx Hx Hy]. 
      rewrite H in *. firstorder.
      rewrite <- H in *. firstorder.      
    Qed.
    
    Global Instance sameclass_Equivalence `{WF} : Equivalence (sameclass t).
    Proof. 
      unfold sameclass, Equiv. repeat constructor; repeat intro.
      destruct (repr_helper x) as [x0]. exists x0; auto. 
      destruct H0.  firstorder.
      destruct H0. destruct H1.  assert (x0 = x1). eapply repr_inj_right; eauto.  
      subst. firstorder.
    Qed.
    
    Lemma sameclass_union : forall {uf} `{WF uf} a b,
      forall s t, sameclass (union uf a b) s t <-> 
        (sameclass uf s t \/ (sameclass uf s a /\ sameclass uf t b) \/ (sameclass uf t a /\ sameclass uf s b)).
    Proof.
      intros uf a b Hwf.
      unfold union. 
      unfold sameclass. 
      repeat (case find_spec; intros; auto). rewrite Heq, Heq0 in *.
      num_analyse. subst.  intuition auto.  
      exists rx0. destruct H0. rewrite (repr_inj_right _ _ _ Hrepr _ H0). auto.
      destruct H1. rewrite (repr_inj_right _ _ _ Hrepr0 _ H1). auto.
      exists rx0. destruct H1. rewrite (repr_inj_right _ _ _ Hrepr0 _ H1). auto.
      destruct H0. rewrite <- (repr_inj_right _ _ _ H0 _ Hrepr). auto.
      
      unfold link. unfold sameclass.
      case compare_spec; simpl; intro; rewrite link_main_lemma; eauto; intuition.
    Qed.

    Lemma sameclass_equiv : forall `{WF} x y, (fst (equiv t x y) = true <-> sameclass t x y).
    Proof.
      intros t Hwf x y. unfold equiv.
      repeat (case find_spec; intros; auto). unfold sameclass; rewrite ?Heq, ?Heq0 in *.
      num_analyse; simpl; subst.
      intuition. 
        clear H. exists rx0; eauto.
        intuition try discriminate. 
        elim n.
        destruct H.
        eauto using repr_inj_right.  
    Qed.

    Lemma sameclass_find : forall `{WF} x, sameclass t (fst (find t x)) x.
    Proof.
      intros t Hwf x. 
      case (find_spec); intros; auto. simpl.
      unfold sameclass. rewrite Heq; clear Heq.
      exists rx;  [eapply repr_idem; eauto | eauto]. 
    Qed.

  End Equiv.

  Lemma test_and_unify_eq : forall {uf} `{WF uf} x y, test_and_unify uf x y = (fst (equiv uf x y), union uf x y).
  Proof.
    intros uf Hwf x y; unfold test_and_unify, union, equiv; 
      repeat (case find_spec; intros; auto).
    num_analyse; subst; reflexivity.
  Qed.

  Definition class_of' (t : T) x := 
    NumMap.fold (fun a b acc => 
      if fst (equiv t x a)  && fst (equiv t x b) 
        then (NumSet.add a (NumSet.add b acc)) 
        else acc
    )  
    (p t) 
    NumSet.empty.
  
  Lemma sameclass_equiv' : forall `{WF} y z, 
    sameclass t y z ->  forall x, @fst bool UF (equiv t y x) = fst (equiv t z x).
  Proof. 
    intros  t Hwf  y z H.
    intros.
    apply <- bool_prop_iff.
    rewrite 2 sameclass_equiv.
    rewrite H. reflexivity.
  Qed.

 
  Lemma NumMap_fold_compat A t f g (x: A):  
    (forall acc (k e : num) , f k e acc = g k e acc) ->
    NumMap.fold f t x = NumMap.fold g t x.
  Proof.
    intros. setoid_rewrite NumMap.fold_1.
    revert x.
    induction (NumMap.elements t); simpl; intros. reflexivity. 
    rewrite H. apply IHl.
  Qed.


  Lemma MapsTo_sameclass : forall `{WF} x z, NumMap.MapsTo x z (p t) -> sameclass t x z.
  Proof.
    intros.
    destruct (repr_helper x) as [y ?]; auto. 
    exists y. auto.  
    inversion H1; subst. firstorder. 
    assert (j = z). NumMapProps.find_tac. subst.  auto.
  Qed.
  

  Lemma equiv_reflexive_false : forall `{WF} x, ~ fst (equiv t x x) = false .
  Proof.
    intros. 
    assert (sameclass t x x). reflexivity.
    rewrite <- sameclass_equiv in H0.  rewrite H0. discriminate.
  Qed.   
  
  Definition class_of t x := NumSet.add x (class_of' t x).

  Lemma class_of_Equal_MapsTo : forall `{WF} x z, NumMap.MapsTo x z (p t) -> 
    NumSet.Equal (class_of' t z) (class_of' t x) .
  Proof.
    unfold class_of'.
      
    intros t Hwf x z H.
    
     intros y.
      apply MapsTo_sameclass in H; auto.
      rewrite (NumMap_fold_compat
        _
        _
        (fun a b acc => if fst (equiv t x a) && fst (equiv t x b) then NumSet.add a (NumSet.add b acc) else acc)
        (fun a b acc => if fst (equiv t z a) && fst (equiv t z b) then NumSet.add a (NumSet.add b acc) else acc)
      ); auto.
      reflexivity.
      intros. 
      rewrite  2 (sameclass_equiv' _ _ H). reflexivity.
  Qed.

  Lemma class_of_Equal_repr : forall `{WF} x z, repr (p t) x z  -> NumSet.Equal (class_of' t z) (class_of' t x).
  Proof.
    intros t Hwf x z H. 
    induction H. reflexivity.
    apply class_of_Equal_MapsTo in H. rewrite IHrepr. assumption.
  Qed.
    
  Lemma class_of_In_MapsTo : forall `{WF} x z, NumMap.MapsTo x z (p t) -> NumSet.In x (class_of t z).
  Proof.
    intros t Hwf x z H.
    unfold class_of. NumSetProps.set_iff. right.
    unfold class_of'. 
    assert (NumMap.Equal (p t) (NumMap.add x z (NumMap.remove x (p t)))).
    intro y. find_analyse; completer idtac; find_tac. destruct H2. find_tac.
    elim H1. rewrite NumMapProps.remove_in_iff. 
    destruct (eq_num_dec x y); firstorder.
    destruct H2. firstorder.

    rewrite Z.fold_Equal; ti_auto. 
    rewrite NumMapProps.fold_add; ti_auto.
    clear H0.
    case_eq (fst (equiv t z x)); 
    case_eq (fst (equiv t z z)); 
    intros; simpl.
    NumSetProps.set_iff. left. num_prop.  reflexivity.
    apply equiv_reflexive_false in H0; auto;tauto_false.


    apply MapsTo_sameclass in H. 
    exfalso.
    symmetry in H.  rewrite <- sameclass_equiv in H. congruence.
    
    apply equiv_reflexive_false in H0; auto;  tauto_false.
    
    repeat intro; subst. case (fst (equiv t z y) && fst (equiv t z y0)); rewrite H3; reflexivity.
    repeat intro; subst. repeat match goal with |- context [fst (equiv ?t ?x ?y)] => case (fst (equiv t x y)) end; simpl;try NumSetProps.setdec.  
    
    rewrite NumMapProps.remove_in_iff. intro. tauto_false.
    
    repeat intro; subst. case (fst (equiv t z y) && (fst (equiv t z y0))); rewrite H3; reflexivity.
  Qed.

  Lemma class_of_In_MapsTo' : forall `{WF} x z, NumMap.MapsTo x z (p t) -> NumSet.In z (class_of t x).
  Proof.
    intros t Hwf x z H.
    unfold class_of. NumSetProps.set_iff. right.
    unfold class_of'. 
    assert (NumMap.Equal (p t) (NumMap.add x z (NumMap.remove x (p t)))).
    intro y. find_analyse; completer idtac; find_tac. destruct H2. find_tac.
    elim H1. rewrite NumMapProps.remove_in_iff.  
    destruct (eq_num_dec x y); firstorder.
    destruct H2. firstorder.

    rewrite Z.fold_Equal; ti_auto. 
    rewrite NumMapProps.fold_add; ti_auto.
    clear H0.
    replace (fst (equiv t x x)) with true. simpl.
    case_eq (fst (equiv t x z)). intros. NumSetProps.set_iff. right. left. num_prop.  reflexivity.
    intros. exfalso.  apply MapsTo_sameclass in H.
    rewrite <- sameclass_equiv in H. congruence. 
    symmetry. rewrite sameclass_equiv. reflexivity.

    repeat intro; subst. case (fst (equiv t x y) && fst (equiv t x y0)); rewrite H3; reflexivity.
    repeat intro; subst. repeat match goal with |- context [fst (equiv ?t ?x ?y)] => case (fst (equiv t x y)) end; simpl;try NumSetProps.setdec.  
    
    rewrite NumMapProps.remove_in_iff. intro. tauto_false.
    
    repeat intro; subst. case (fst (equiv t x y) && fst (equiv t x y0)); rewrite H3; reflexivity.
  Qed.

  Lemma class_of_In_repr : forall `{WF} x z, repr (p t) x z  -> NumSet.In x (class_of t z).
  Proof.
    intros t Hwf x z H. unfold class_of in *.
    induction H. NumSetProps.setdec. 
    apply class_of_In_MapsTo in H.
    revert IHrepr. NumSetProps.set_iff. intros [H'   | H']. num_prop. subst.
    unfold class_of in H.
    revert H.  NumSetProps.set_iff. intros [? | ?]. num_prop. auto. auto.
    unfold class_of in H.
    rewrite <- (class_of_Equal_repr _ _ H0) in H.  
    revert H. NumSetProps.set_iff. intros [? | ?].  num_prop. subst. auto.  auto.  
  Qed.

  Lemma class_of_In_repr' : forall `{WF} x z, repr (p t) x z  -> NumSet.In z (class_of t x).
  Proof.
    intros t Hwf x z H. unfold class_of in *.
    induction H. NumSetProps.setdec. 
    
    assert (H'' := class_of_In_MapsTo' _ _ H). 
    
    revert IHrepr. NumSetProps.set_iff. intros [H'   | H']; num_prop; subst.
    clear H0. revert H''. unfold class_of.
    NumSetProps.set_iff. intros [? | ?]; num_prop; auto. 
    
    revert H''. unfold class_of.
    NumSetProps.set_iff. intros [? | ?];  num_prop. subst. auto. 
    right. apply class_of_Equal_MapsTo in H. rewrite <- H. auto.
  Qed.

  Lemma NumMap_Equal_Empty_empty : forall elt (t : NumMap.t elt) , NumMap.Empty t -> NumMap.Equal t (NumMap.empty _).
  Proof.
    intros elt t H a. 
    find_analyse; find_tac; firstorder. 
    assert (NumMap.Empty (NumMap.empty elt)). auto with map.  firstorder.
  Qed.   

  (* TODO: nettoyer cette preuve !!! *)
  Lemma sameclass_class_of : forall `{WF} x y , sameclass t x y <-> NumSet.In x (class_of t y).
  Proof.
    intros  t Hwf x y.
    
    split; intros.
    Focus 1.
    
    destruct H as [z H H'].
    
    assert (Hx := class_of_In_repr _ _ H).
    assert (Hy := class_of_In_repr _ _ H').
    
    
    
    revert Hx Hy; unfold class_of; NumSetProps.set_iff; num_prop. intros [? |?] [? |?]; subst; auto.
    clear H.
    assert (h'' := class_of_In_repr' _ _ H'). unfold class_of in h''. revert h''. NumSetProps.set_iff. num_prop. intuition.
    
    rewrite <- (class_of_Equal_repr _ _ H').  auto.

    Focus 1.
    unfold class_of in H.
    unfold class_of', class_of in H.
    
    revert H. NumSetProps.set_iff. num_prop. intros [? |?]. subst.  reflexivity.
    
    induction (p t) using Z.map_induction_max.
    assert (H1 := NumMap_Equal_Empty_empty _ t0 H0).    
    setoid_rewrite (Z.fold_Equal _ _ _ H1) in H .
    
    rewrite (NumMapProps.fold_Empty (eqA := NumSet.Equal)) in H; ti_auto. 
    clear - H Hwf.  revert H. NumSetProps.set_iff. num_prop. intuition. subst.

    auto with map.

    
    erewrite (Z.fold_Add_Above (eqA := NumSet.Equal)) in H; ti_auto.
    2 :  repeat intro; subst; destruct (fst (equiv t y y0) && fst (equiv t y y1)); try NumSetProps.setdec. 

     case_eq (fst (equiv t y x0) && (fst (equiv t y e))); intros; rewrite H2 in *.
     2 :apply IHt0_1; auto.



     revert H. NumSetProps.set_iff; num_prop. intros [? | [? | ?]]; num_prop; subst. 

     clear - H2 Hwf.  bool_connectors; rewrite sameclass_equiv in H2;try symmetry; auto.  intuition.
     clear - H2 Hwf.  bool_connectors; rewrite 2 sameclass_equiv in H2;try symmetry; auto.  intuition.
     
     apply IHt0_1. auto.
   Qed.

  End protect.
End PosDisjointSets.
