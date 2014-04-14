(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This module is an handler through wich we access the standard
   library about FSets.
   
   TODO: Coq standard library has evolved in v8.3, so that (parts of)
   this file might no longer be useful.

   We include the most used modules, [Facts] and [OrdProps], but
   unfortunately, we cannot import neither Props neither EqProps.

   In order to acces a lemma in Props, use [Module.Props.lemma]
   In order to acces a lemma in EqProps, use [Module.EqProps.lemma]

   We use the abreviation [setdec] for fsetdec.

   We provide a [mem_propview] tactic, see [BoolView.v] for more
   informations about this.

   We also provide (new) induction principles about finite sets,
   which actually coincides with the ones defined in FSetMaps. One
   slogan here is to use them for reasonning about fold instead of
   the _dependent_ ones provided by S. Lescuyer in the standard
   library, and to rewrite lemmas that describe the computational
   behavior of fold.

   Typically, if one want to go through a fold from top (ie, to
   rewrite [fold f acc ((x -> y) :: m)] into [f x y (fold f acc m)]),
   one will use [set_induction_above] and rewrite the lemma
   [fold_add_above], while if one want to go through the fold bottom-up
   (ie, to rewrite [fold f acc ((x -> y) :: m)] into [fold f (f x y
   acc) m]), one will use [set_induction_below] and rewrite the lemma
   [fold_add_below] *)

Require Import FSets.
Require Import Common.
Require Import BoolView.


Module MySetProps (X : FSetInterface.S).
  
  Module EqProps := FSetEqProperties.EqProperties X.
  Module Props := EqProps.MP.
  Module Facts  := Props.FM.
  Module OrdProps := FSetProperties.OrdProperties X.
  Module Dec := Props.Dec.
  
  Include Facts.
  Include OrdProps.
  Import  X.  
  Ltac setdec := Dec.fsetdec.

  Lemma mem_add : forall x s, mem x (add x s) = true.
  Proof.
    intros. rewrite <- mem_iff, add_iff. left. reflexivity. 
  Qed.

  Lemma mem_spec : forall x s, reflect (In x s) (mem x s).
  Proof. 
    intros. case_eq (mem x s); intro H; constructor. 
     apply mem_2. assumption.
     intro H'. apply mem_1 in H'. rewrite H in H'. discriminate.
  Qed.

  Instance mem_type_view : Type_View mem := { type_view := mem_spec }.

  Ltac mem_analyse := repeat type_view mem.

  Lemma mem_false_not_in: forall x s, mem x s = false <-> ~ In x s.
  Proof. intros. mem_analyse; intuition discriminate. Qed. 

  Hint Rewrite mem_false_not_in : mem_prop.
  Hint Rewrite <- mem_iff : mem_prop.
  Ltac mem_prop := autorewrite with mem_prop in *.

  Hint Rewrite singleton_b union_b add_b mem_add : bool_simpl.

  (** set_induction_below *)
  Section ListViewBelow.
    Inductive lvb : t -> Type :=
    | lnil :  forall s, Equal s empty ->  lvb s
    | lcons : forall x p, lvb p -> ~In x p -> Below x p -> forall s, Equal s (add x p) ->  lvb s.
    
    Program Definition lvb_iter 
      (P : t -> Type)
      (a : forall s, Equal s empty -> P s)
      (f : forall p x, P p -> ~In x p -> Below x p -> forall s, Equal s (add x p) -> P s)
      := 
        fix iter p (q : lvb p) : P p :=
        match q in lvb p return P p with 
          | lnil  s hs  => a s hs
          | lcons x p lvp _ _ _ _ => f p x (iter _ lvp) _ _ _ _
        end.

    Program Fixpoint lVB s {measure (cardinal s)}: lvb s :=
      match min_elt s with
        | None => @lnil _ _
        | Some x => @lcons x  _ (lVB (remove x s)) _ _ _ _
      end. 
    Next Obligation.
      assert (Empty s). 
      apply min_elt_3;auto.
      setdec.
    Qed.
    Next Obligation.
      assert (In x s). apply min_elt_1. auto. 
      assert (forall x y, S x <= y -> x < y) by (intros; omega). apply H0. clear H0.       
      rewrite EqProps.remove_cardinal_1. auto. 
      rewrite <-mem_iff. auto. 
    Qed.
    Next Obligation.
      assert (In x s). apply min_elt_1. auto.
      set_iff. intro.  intuition. 
    Qed.
    Next Obligation.
      unfold Below. intros. 
      revert H. set_iff. intros. 
      assert (~E.lt y x). destruct H; apply (@min_elt_2 s); auto.
      eapply ME.le_neq. apply H0. destruct H. intuition. 
    Qed.  
    Next Obligation. 
      assert (In x s). apply min_elt_1. auto.
      unfold Equal. symmetry.  revert a. apply Props.add_remove. auto.
    Qed.
  
    Definition set_induction_below 
      (P:t->Type) 
      (a:forall s, Equal s empty ->P s) 
      (f:forall p x, P p -> ~ In x p -> Below x p -> forall s, Equal s (add x p) -> P s) 
      (s: t): P s :=
      lvb_iter P a f s (lVB s).
  End ListViewBelow.
  

  (** set_induction_above *)
  Section ListViewAbove.
    Inductive lva : t -> Type :=
    | lnila :  forall s, Equal s empty ->  lva s
    | lconsa : forall x p, lva p -> ~In x p -> Above x p -> forall s, Equal s (add x p) ->  lva s.

    Section i.
      Variable P : t -> Type.
      Hypothesis a : forall s, Equal s empty -> P s.
      Hypothesis f : forall p x, P p -> ~In x p -> Above x p -> forall s, Equal s (add x p) -> P s.
      Lemma lva_iter: forall p, lva p -> P p. 
      Proof.
        induction 1.
         apply a, e.
         eapply f; eassumption.  
      Qed.
    End i.    

    Program Fixpoint lVA s {measure (cardinal s)}: lva s :=
      match max_elt s with
        | None => @lnila _ _
        | Some x => @lconsa x  _ (lVA (remove x s)) _ _ _ _
      end. 
    Next Obligation.
      assert (Empty s). apply max_elt_3; auto.
      setdec.
    Qed.
    Next Obligation.
      assert (In x s). apply max_elt_1. auto. 
      assert (H': forall x y, S x <= y -> x < y) by auto with arith. apply H'. clear H'.       
      rewrite EqProps.remove_cardinal_1. trivial. 
      rewrite <-mem_iff. assumption. 
    Qed.
    Next Obligation.
      assert (In x s). apply max_elt_1. auto.
      set_iff. intro.  intuition. 
    Qed.
    Next Obligation.
      unfold Above. intros. 
      revert H. set_iff. intros. 
      assert (~E.lt x y). destruct H; apply (@max_elt_2 s); auto.
      eapply ME.le_neq. apply H0. destruct H. intuition. 
    Qed.  
    Next Obligation. 
      assert (In x s). apply max_elt_1. auto.
      unfold Equal. symmetry.  revert a. apply Props.add_remove. auto.
    Qed.
  
    Definition set_induction_above 
      (P:t->Type) 
      (a:forall s, Equal s empty ->P s) 
      (f:forall p x, P p -> ~ In x p -> Above x p -> forall s, Equal s(add x p) -> P s) 
      (s: t): P s :=
      lva_iter P a f s (lVA s).
  End ListViewAbove.

  Section MyFold.
    Variable A : Type.
    Variable eqA : A -> A -> Prop.
    Hypothesis equivalence_eqA : Equivalence eqA.
    Variable f : E.t -> A -> A.
    Variable Hcompat : compat_op E.eq eqA f.
    Lemma fold_empty : forall  s (i: A),  Equal s empty -> eqA (fold f s i) i.
    Proof.
      intros  s i Hs.
      rewrite (fold_equal _ Hcompat _ Hs).
      rewrite Props.fold_empty.
      reflexivity.
    Qed.
    
    Lemma fold_add_below x p i :  
      ~In x p -> Below x p -> eqA (fold f (add x p) i) (fold f p (f x i)).
    Proof.
      intros Hxp Hxp' .
      apply (fold_4 equivalence_eqA _ Hcompat). 
      repeat intro. apply Hxp'. auto.
      rewrite P.Add_Equal. reflexivity.
    Qed.

    Lemma fold_add_above x p i: 
      ~In x p -> Above x p -> eqA (fold f (add x p) i) (f x (fold f p  i)).
    Proof.
      intros Hxp Hxp' .
      apply (fold_3 equivalence_eqA _ Hcompat). 
      repeat intro. apply Hxp'. auto.
      rewrite P.Add_Equal. reflexivity.
    Qed.

    (** Here, we prove the usual dependent induction principles about finite sets *)
    Section fold_rec_bis.
      Variable P : t -> A -> Type.
      Theorem fold_rec_bis' :
        forall (i:A)(s:t),
          (forall s s' a a', s[=]s' -> eqA a a' -> P s a -> P s' a') ->
          (P empty i ) ->
          (forall x a s', In x s -> ~In x s' -> P s' a -> P (add x s') (f x a)) ->
          P s (fold f s i).
      Proof.
        intros i . 
        induction s using set_induction_above.
        intros Hc HA _. eapply Hc; eauto. symmetry. auto. rewrite fold_empty. reflexivity. auto.
        intros Hs HA Hrec.
        eapply Hs. symmetry; eauto.
        symmetry. rewrite (fold_equal equivalence_eqA Hcompat _ H1).  rewrite fold_add_above.
        reflexivity. auto. auto.

        apply Hrec. rewrite H1. setdec. auto.
        apply IHs1. auto. auto. 
        intros.  apply Hrec. rewrite H1. setdec.  auto. auto.
      Qed.
    End fold_rec_bis.
  End MyFold.

  (** Lemmas about [elements]  *)
  Section elements.
    Lemma fold_left_id : forall A (s y : list A), List.fold_left (fun acc x => acc ++x::nil) s y = y ++ s. 
    Proof.
      intros A.
      induction s. simpl. intros. rewrite <- app_nil_end. reflexivity.
      simpl. intros. rewrite IHs. 
      rewrite <- ass_app. 
      reflexivity.
    Qed.
    
    Lemma elements_fold : forall s, elements s = fold (fun x acc => acc++x::nil) s nil.
    Proof.
      intros s.    
      rewrite fold_1.    
      rewrite fold_left_id.
      reflexivity. 
    Qed.
  End elements.


  (** Lemmas about [exists_], mainly compat issues, or describing its computationnal behavior *)
  Section exists_.
    Variable f : E.t -> bool.
    Hypothesis Hcompat : compat_bool (E.eq) f.
  
    Lemma exists_compat : forall x y,  Equal x y ->      exists_ f x = exists_ f y.
    Proof.
      intros  x y  H.
      apply <- bool_prop_iff.
      rewrite <- 2 exists_iff by apply Hcompat. 
      unfold Exists.
      completer idtac; firstorder.
    Qed.
      
    Lemma exists_add : forall x s, ~ In x s -> 
      exists_ f (add x s) = exists_ f s || f x.
    Proof.
      intros x s H. 
      apply <- bool_prop_iff; bool_connectors.  rewrite<- 2 exists_iff by apply Hcompat.

      unfold Exists. setoid_rewrite add_iff.
      completer idtac.
        rewrite <- (Hcompat _ _ H0) in H1. auto. 
        firstorder. 
        firstorder. 
        firstorder. 
    Qed.

    Lemma exists_empty :  exists_ f empty = false.
    Proof.
      assert (forall b, b = false <-> ~b=true). clear. intros [|]; firstorder.
      rewrite H.  clear H. intro. 
      rewrite <- exists_iff in H. destruct H. setdec.
      apply Hcompat.
    Qed.
  
    Lemma exists_fold' :
      forall x init init', 
      init = init' -> 
      exists_ f x || init  = fold (fun k acc => f k || acc) x init'.
    Proof.
      assert (Hf' : compat_op E.eq Logic.eq (fun k acc => f k || acc)).
      repeat intro.  subst. rewrite (Hcompat _ _ H). reflexivity. 
      induction x using set_induction_below; intros init init' Hinit.

      rewrite (fold_empty); auto. 
      rewrite (exists_compat _ _ H). rewrite Hinit.
      rewrite (exists_empty). reflexivity. 
      
      rewrite (fold_equal _ Hf' _ H1).
      rewrite (fold_add_below ); auto.
      rewrite (exists_compat _ _ H1). 
      rewrite (exists_add _ _ H). rewrite <- orb_assoc. rewrite (@IHx1 (f x2 || init) (f x2 || init')).
      reflexivity.
      subst; reflexivity.
    Qed.
    
    Lemma exists_fold x:
      exists_ f x = fold (fun k acc => f k || acc) x false.
    Proof.
      rewrite <- (exists_fold' _ false false); trivial. bool_simpl; trivial. 
    Qed.
  End exists_.

  Lemma fold_compat 
    (f : E.t -> bool -> bool) 
    (g : E.t -> bool -> bool) x x' init init' : 
    compat_op E.eq Logic.eq f  ->
    compat_op E.eq Logic.eq g  ->
      Equal x x' ->
      init = init' ->
      (forall e acc, In e x -> f e acc = g e acc) -> 
      fold f x init = fold g x' init'.
  Proof.
    revert x' init init'.
    induction x using set_induction_below.
    intros x' init init' Hf Hg Hx Hinit Hcompat. 
    rewrite 2 fold_empty; auto. rewrite <- Hx. auto. 

    
    intros x' init init' Hf Hg Hx Hinit Hcompat. 
    
    rewrite (fold_equal _ Hf _ H1). 
    rewrite H1 in Hx. symmetry in Hx.      rewrite (fold_equal _ Hg _ Hx).
    rewrite 2 fold_add_below; auto. apply IHx1. apply Hf.  apply Hg. reflexivity. 
    
    rewrite Hinit. apply Hcompat. rewrite H1. apply add_1. auto.
    intros e acc He. 
    apply Hcompat. rewrite H1. setdec.
  Qed.

End MySetProps.  

