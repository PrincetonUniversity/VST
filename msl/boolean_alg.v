(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(** This library defines boolean algebras defined from an order-theoretic
    perspective.  In short, a boolean algebra is a complemented distributive
    lattice.  We additionally require that the boolean algebra be non-trivial.

    From this definition we can recover the axioms of boolean algebras as
    defined in allp algebra.

    We also define module interfaces for boolean algebras with a splitting
    operator, with a relativization operator, and those which support
    token counting.

    We then say that a share model is a boolean algebra which satisfies
    all three module interfaces.  We also require that the elements
    have a decidable equality.
*)

Add LoadPath "..".
Require Import msl.base.
Require Import msl.eq_dec.
Require Import msl.sepalg.

Module Type BOOLEAN_ALGEBRA.
  Parameters (t:Type) (Ord : t -> t -> Prop)
     (top bot : t) (lub glb : t -> t -> t) (comp : t -> t).

  Delimit Scope ba with ba. Open Scope ba.
  Notation "x <= y" := (Ord x y) (at level 70, no associativity) : ba.

  Axiom ord_refl : forall x, x <= x.
  Axiom ord_trans : forall x y z, x <= y -> y <= z -> x <= z.
  Axiom ord_antisym : forall x y, x <= y -> y <= x -> x = y.

  Axiom lub_upper1 : forall x y, x <= (lub x y).
  Axiom lub_upper2 : forall x y, y <= (lub x y).
  Axiom lub_least : forall x y z, x <= z -> y <= z -> (lub x y) <= z.

  Axiom glb_lower1 : forall x y, (glb x y) <= x.
  Axiom glb_lower2 : forall x y, (glb x y) <= y.
  Axiom glb_greatest : forall x y z, z <= x -> z <= y -> z <= (glb x y).

  Axiom top_correct : forall x, x <= top.
  Axiom bot_correct : forall x, bot <= x.

  Axiom distrib1 : forall x y z, glb x (lub y z) = lub (glb x y) (glb x z).

  Axiom comp1 : forall x, lub x (comp x) = top.
  Axiom comp2 : forall x, glb x (comp x) = bot.

  Axiom nontrivial : top <> bot.

  Hint Resolve ord_refl ord_antisym lub_upper1 lub_upper2 lub_least
         glb_lower1 glb_lower2 glb_greatest top_correct bot_correct
         ord_trans : ba.
End BOOLEAN_ALGEBRA.

Module Type BA_FACTS.
  Include BOOLEAN_ALGEBRA.

  Axiom ord_spec1 : forall x y, x <= y <-> x = glb x y.
  Axiom ord_spec2 : forall x y, x <= y <-> lub x y = y.

  Axiom lub_idem : forall x, (lub x x) = x.
  Axiom lub_commute : forall x y, lub x y = lub y x.
  Axiom lub_bot : forall x, lub x bot = x.
  Axiom lub_top : forall x, lub x top = top.
  Axiom lub_absorb : forall x y, lub x (glb x y) = x.
  Axiom lub_assoc : forall x y z, lub (lub x y) z = lub x (lub y z).

  Axiom glb_idem : forall x, glb x x = x.
  Axiom glb_commute : forall x y, glb x y = glb y x.
  Axiom glb_bot : forall x, glb x bot = bot.
  Axiom glb_top : forall x, glb x top = x.
  Axiom glb_absorb : forall x y, glb x (lub x y) = x.
  Axiom glb_assoc : forall x y z, glb (glb x y) z = glb x (glb y z).

  Axiom distrib2 : forall x y z, lub x (glb y z) = glb (lub x y) (lub x z).

  Axiom distrib_spec : forall x y1 y2,
    lub x y1 = lub x y2 ->
    glb x y1 = glb x y2 ->
    y1 = y2.

  Axiom demorgan1 : forall x y, comp (lub x y) = glb (comp x) (comp y).
  Axiom demorgan2 : forall x y, comp (glb x y) = lub (comp x) (comp y).
  Axiom comp_inv : forall x, comp (comp x) = x.

  Instance Join_ba: Join t := fun x y z : t => glb x y = bot /\ lub x y = z.

  Axiom pa: Perm_alg t.   Existing Instance pa.
  Axiom sa : Sep_alg t.   Existing Instance sa.
  Axiom ca : Canc_alg t. Existing Instance ca.
  Axiom singa : Sing_alg t.   Existing Instance singa.
  Axiom da : Disj_alg t.   Existing Instance da.
End BA_FACTS.

Module Type SHARE_MODEL.
  Include BA_FACTS.

  Parameter EqDec_share: EqDec t.
  Existing Instance EqDec_share.

  (* Splittability *)
  Parameter split : t -> t * t.

  Axiom split_disjoint : forall x1 x2 x,
    split x = (x1, x2) ->
    glb x1 x2 = bot.

  Axiom split_together : forall x1 x2 x,
    split x = (x1, x2) ->
    lub x1 x2 = x.

  Axiom split_nontrivial : forall x1 x2 x,
    split x = (x1, x2) ->
    (x1 = bot \/ x2 = bot) ->
    x = bot.

  (* Token factories *)
  Parameter isTokenFactory : t -> nat -> Prop.
  Parameter isToken : t -> nat -> Prop.

  Parameter create_token : nat -> t -> (t*t).

  Axiom create_token_correct : forall fac fac' tok x n,
    create_token n fac = (fac',tok) ->
    isTokenFactory fac x ->
      isTokenFactory fac' (n+x) /\
      isToken tok n /\
      join fac' tok fac.

  Axiom absorbToken : forall fac fac' tok x n,
    isTokenFactory fac' (n+x) ->
    isToken tok n ->
    join fac' tok fac ->
    isTokenFactory fac x.

  Axiom mergeToken : forall tok1 n1 tok2 n2 tok',
    isToken tok1 n1 ->
    isToken tok2 n2 ->
    join tok1 tok2 tok' ->
    isToken tok' (n1+n2).

  Parameter split_token : nat -> t -> t*t.

  Axiom split_token_correct : forall n1 n2 tok tok1 tok2,
    isToken tok (n1+n2) ->
    split_token n1 tok = (tok1,tok2) ->
      isToken tok1 n1 /\
      isToken tok2 n2 /\
      join tok1 tok2 tok.

  Axiom factoryOverlap : forall f1 f2 n1 n2,
    isTokenFactory f1 n1 -> isTokenFactory f2 n2 -> glb f1 f2 <> bot.

  Axiom fullFactory : forall x, isTokenFactory x 0 <-> x = top.
  Axiom identityToken : forall x, isToken x 0 <-> x = bot.

  Axiom nonidentityToken : forall x n, (n > 0)%nat -> isToken x n -> x <> bot.
  Axiom nonidentityFactory : forall x n, isTokenFactory x n -> x <> bot.

  
  (* relativization *)
  Parameter rel : t -> t -> t.

  Axiom rel_inj_l : forall a x y, a <> bot -> rel a x = rel a y -> x = y.
  Axiom rel_inj_r : forall a b x, x <> bot -> rel a x = rel b x -> a = b.

  Axiom rel_assoc : forall x y z, rel x (rel y z) = rel (rel x y) z.

  Axiom rel_preserves_glb : forall a x y, rel a (glb x y) = glb (rel a x) (rel a y).
  Axiom rel_preserves_lub : forall a x y, rel a (lub x y) = lub (rel a x) (rel a y).

  Axiom rel_bot1 : forall a, rel a bot = bot.
  Axiom rel_bot2 : forall x, rel bot x = bot.
  Axiom rel_top1 : forall a, rel a top = a.
  Axiom rel_top2 : forall x, rel top x = x.

  Parameter unrel: t -> t -> t.
  Definition Lsh  : t := fst (split top).
  Definition Rsh  : t := snd (split top).
  Definition splice (a b: t) : t := lub (rel Lsh a) (rel Rsh b). 

  Axiom unrel_splice_L: forall a b, unrel Lsh (splice a b) = a.
  Axiom unrel_splice_R: forall a b, unrel Rsh (splice a b) = b.

 Axiom contains_Rsh_e: forall sh, join_sub Rsh sh -> unrel Rsh sh = top.

End SHARE_MODEL.


Module BA_Facts (BA:BOOLEAN_ALGEBRA) <: BA_FACTS.
  Include BA.

  Lemma ord_spec1 : forall x y, x <= y <-> x = glb x y.
  Proof.
    split; intros.
    auto with ba.
    rewrite H; auto with ba.
  Qed.

  Lemma ord_spec2 : forall x y, x <= y <-> lub x y = y.
  Proof.
    intros; split; intros.
    auto with ba.
    rewrite <- H; auto with ba.
  Qed.

  Lemma lub_idem : forall x, lub x x = x.
  Proof. auto with ba. Qed.

  Lemma glb_idem : forall x, glb x x = x.
  Proof. auto with ba. Qed.

  Lemma lub_commute : forall x y, lub x y = lub y x.
  Proof. auto with ba. Qed.

  Lemma glb_commute : forall x y, glb x y = glb y x.
  Proof. auto with ba. Qed.

  Lemma lub_absorb : forall x y, lub x (glb x y) = x.
  Proof. auto with ba. Qed.

  Lemma glb_absorb : forall x y, glb x (lub x y) = x.
  Proof. auto with ba. Qed.

  Lemma lub_assoc : forall x y z, lub (lub x y) z = lub x (lub y z).
  Proof.
    intros; apply ord_antisym; eauto with ba.
  Qed.

  Lemma glb_assoc : forall x y z, glb (glb x y) z = glb x  (glb y z).
  Proof.
    intros; apply ord_antisym; eauto with ba.
  Qed.

  Lemma glb_bot : forall x, glb x bot = bot.
  Proof. auto with ba. Qed.

  Lemma lub_top : forall x, lub x top = top.
  Proof. auto with ba. Qed.

  Lemma lub_bot : forall x, lub x bot = x.
  Proof. auto with ba. Qed.

  Lemma glb_top : forall x, glb x top = x.
  Proof. auto with ba. Qed.

  Lemma distrib2 : forall x y z,
    lub x (glb y z) = glb (lub x y) (lub x z).
  Proof.
    intros.
    apply ord_antisym.
    apply lub_least.
    rewrite distrib1.
    rewrite glb_commute.
    rewrite glb_absorb.
    apply lub_upper1.
    apply glb_greatest.
    apply ord_trans with y.
    apply glb_lower1.
    apply lub_upper2.
    apply ord_trans with z.
    apply glb_lower2.
    apply lub_upper2.
    rewrite distrib1.
    apply lub_least.
    rewrite glb_commute.
    rewrite glb_absorb.
    apply lub_upper1.
    rewrite glb_commute.
    rewrite distrib1.
    apply lub_least.
    apply ord_trans with x.
    apply glb_lower2.
    apply lub_upper1.
    rewrite glb_commute.
    apply lub_upper2.
  Qed.

  Lemma distrib_spec : forall x y1 y2,
    lub x y1 = lub x y2 ->
    glb x y1 = glb x y2 ->
    y1 = y2.
  Proof.
    intros.
    rewrite <- (lub_absorb y2 x).
    rewrite glb_commute.
    rewrite <- H0.
    rewrite distrib2.
    rewrite lub_commute.
    rewrite <- H.
    rewrite (lub_commute x y1).
    rewrite (lub_commute y2 y1).
    rewrite <- distrib2.
    rewrite <- H0.
    rewrite glb_commute.
    rewrite lub_absorb.
    auto.
  Qed.

  Lemma comp_inv : forall x, comp (comp x) = x.
  Proof.
    intro x.
    apply distrib_spec with (comp x).
    rewrite comp1.
    rewrite lub_commute.
    rewrite comp1.
    auto.
    rewrite comp2.
    rewrite glb_commute.
    rewrite comp2.
    auto.
  Qed.

  Lemma demorgan1 : forall x y, comp (lub x y) = glb (comp x) (comp y).
  Proof.
    intros x y.
    apply distrib_spec with (lub x y).
    rewrite comp1.
    rewrite distrib2.
    rewrite (lub_assoc x y (comp y)).
    rewrite comp1.
    rewrite lub_top.
    rewrite glb_top.
    rewrite (lub_commute x y).
    rewrite lub_assoc.
    rewrite comp1.
    rewrite lub_top.
    auto.
    rewrite comp2.
    rewrite glb_commute.
    rewrite distrib1.
    rewrite (glb_commute (comp x) (comp y)).
    rewrite glb_assoc.
    rewrite (glb_commute (comp x) x).
    rewrite comp2.
    rewrite glb_bot.
    rewrite lub_commute.
    rewrite lub_bot.
    rewrite (glb_commute (comp y) (comp x)).
    rewrite glb_assoc.
    rewrite (glb_commute (comp y) y).
    rewrite comp2.
    rewrite glb_bot.
    auto.
  Qed.

  Lemma demorgan2 : forall x y, comp (glb x y) = lub (comp x) (comp y).
  Proof.
    intros x y.
    apply distrib_spec with (glb x y).
    rewrite comp1.
    rewrite lub_commute.
    rewrite distrib2.
    rewrite (lub_commute (comp x) (comp y)).
    rewrite lub_assoc.
    rewrite (lub_commute (comp x) x).
    rewrite comp1.
    rewrite lub_top.
    rewrite glb_commute.
    rewrite glb_top.
    rewrite (lub_commute (comp y) (comp x)).
    rewrite lub_assoc.
    rewrite (lub_commute (comp y) y).
    rewrite comp1.
    rewrite lub_top.
    auto.
    rewrite comp2.
    rewrite distrib1.
    rewrite (glb_commute x y).
    rewrite glb_assoc.
    rewrite comp2.
    rewrite glb_bot.
    rewrite lub_commute.
    rewrite lub_bot.
    rewrite (glb_commute y x).
    rewrite glb_assoc.
    rewrite comp2.
    rewrite glb_bot.
    auto.
  Qed.

  Instance Join_ba: Join t := fun x y z : t => glb x y = bot /\ lub x y = z.

  Instance pa: Perm_alg t.
  Proof. constructor; simpl; intros.
    (* saf_eq *)
    hnf in *. destruct H; destruct H0; subst; auto.

   (* saf_proper *)
   repeat intro; hnf in *; subst; auto.

    (* saf_assoc *)
    hnf in *. intuition.
    exists (lub b c); intuition; hnf in *. split; auto.
    rewrite <- H2 in H.
    rewrite <- H.
    apply ord_antisym.
    eauto with ba.
    rewrite H; auto with ba.
    cut (glb a c = bot); intros.
    rewrite distrib1.
    rewrite H1.
    rewrite lub_commute; rewrite lub_bot; auto. split; auto.
    subst.
    apply ord_antisym; rewrite lub_assoc; auto with ba.
    subst.
    rewrite glb_commute in H |- *.
    rewrite distrib1 in H. 
    generalize (lub_upper1 (glb c a) (glb c b)); intro.
    rewrite H in H0.
    apply ord_antisym; auto.
    apply bot_correct.

    (* saf_com *)
    hnf in *.
    rewrite glb_commute.
    rewrite lub_commute.
    auto.

    (* saf_positivity *)
    hnf in *.
    intuition.
    subst a. 
    rewrite (lub_commute b) in H2. rewrite lub_commute in H2. 
     rewrite <- lub_assoc in H2. 
    apply ord_spec2 in H2.
    rewrite lub_commute; apply ord_spec2.
    apply ord_trans with (lub a' b'); auto.
    apply ord_spec2. rewrite (lub_commute b'). rewrite lub_assoc. rewrite lub_idem; auto.
  Qed.

  Instance sa: Sep_alg t.
  Proof.  apply mkSep with (fun _ => bot).
    intros. unfold unit_for. constructor. rewrite glb_commute; apply glb_bot.
             rewrite lub_commute; apply lub_bot.
    intros. reflexivity.
  Defined.

  Instance singa: Sing_alg t.
  Proof.  apply (mkSing bot). unfold core; intros; simpl. reflexivity.
  Defined.

  Instance ca: Canc_alg t.
  Proof. repeat intro.  hnf in *. intuition.
    apply distrib_spec with b.
    rewrite lub_commute; rewrite H2.
    rewrite lub_commute; rewrite H3.
    trivial.
    rewrite glb_commute; rewrite H1.
    rewrite glb_commute; rewrite H.
    trivial.
  Qed.

  Instance da: Disj_alg t.
  Proof. repeat intro.
    destruct H.
    rewrite lub_idem in H0.
    auto.
  Qed.

End BA_Facts.
