(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(** This module defines the standard operators on separation algebras, including
    the operators over pairs, disjoint sums, function spaces, dependent products,
    dependent sums, sub-separation algebras, the discrete separation algebra,
    the trivial unit and void separation algrbras.
*)

Require Import VST.msl.base.
Require Import VST.msl.sepalg.

(** The trivial separation algebra over the unit type.  This SA
    is the identity of the product SA operator, up to isomorphism.
*)

  #[global] Instance Join_unit : Join unit := fun x y z => True.

  #[global] Instance Perm_unit : Perm_alg unit.
  Proof.
  constructor; auto with typeclass_instances; try firstorder.
  destruct z; destruct z'; auto.
  destruct a; destruct b; auto.
  Qed.

  #[global] Instance Sep_unit: FSep_alg unit.
  Proof. apply mkSep with (fun _ => tt); intros;  hnf; auto with typeclass_instances. Defined.

  #[global] Instance Sing_unit: Sing_alg unit.
  Proof. apply (mkSing tt); intros; hnf; simpl.
        destruct (fcore a); auto.
 Qed.

  #[global] Instance Canc_unit: Canc_alg unit.
  Proof. repeat intro. auto. hnf; destruct a1; destruct a2; auto. Qed.

  #[global] Instance Disj_unit: Disj_alg unit.
  Proof. repeat intro. destruct a0, b0;  auto. Qed.

  #[global] Instance Cross_unit: Cross_alg unit.
  Proof. repeat intro. exists (tt,tt,tt,tt). repeat split; constructor. Qed.

(** The trivial separation algebra over the void type. This SA
    is the identity of the coproduct (disjoint sum) SA operator, up to isomorphism.
*)

  Inductive Void : Type :=.

  #[global] Instance Join_void : Join Void := fun x y z => False.

  #[global] Instance Perm_void : Perm_alg Void.
  Proof. constructor; intuition.  Qed.
  #[global] Instance Sep_void: FSep_alg Void.
  Proof. apply mkSep with (fun x => x); intros.
      auto with typeclass_instances. destruct t. destruct a.
  Defined.
  #[global] Instance Canc_void: Canc_alg Void.
  Proof. repeat intro. destruct b. Qed.
  #[global] Instance Disj_void: Disj_alg Void.
  Proof. repeat intro. destruct a. Qed.
  #[global] Instance Cross_void: Cross_alg Void.
  Proof. repeat intro. destruct z. Qed.

(** The separation algebra over booleans, e.g. Z/2 with bounded addition *)

  Inductive join_bool : bool -> bool -> bool -> Prop :=
  | jb_fff: join_bool false false false
  | jb_tft: join_bool true false true
  | jb_ftt: join_bool false true true.

  #[global] Instance Join_bool : Join bool := join_bool.

  #[global] Instance Perm_bool: Perm_alg bool.
  Proof.
    constructor. auto with typeclass_instances.
    intros; inv H; inv H0; hnf; auto.
    repeat intro; hnf in *; subst; auto.
    intros. icase a; icase b; icase d; try solve [exfalso; (inv H || inv H0)].
    exists c; inv H0; split; constructor.
    exists true; inv H0; split; constructor.
    exists c; inv H0; split; constructor.
    intros; inv H; constructor; auto.
    intros. inv H; inv H0; hnf; auto.
  Qed.

  #[global] Instance Sep_bool: FSep_alg bool.
  Proof. apply mkSep with (fun t => false); intros; hnf; auto with typeclass_instances.
     icase t; constructor.
  Defined.

  #[global] Instance Sing_bool: Sing_alg bool.
  Proof. apply (mkSing false). intros; simpl; reflexivity.
  Defined.

  #[global] Instance Canc_bool: Canc_alg bool.
  Proof. repeat intro. inv H; inv H0; hnf; auto. Qed.

  #[global] Instance Disj_bool: Disj_alg bool.
  Proof. repeat intro. inv H; inv H0; auto. Qed.

  #[global] Instance Cross_bool: Cross_alg bool.
  Proof. repeat intro.
     icase a; icase b; try solve [exfalso; (try inv H; inv H0)];
    icase z; icase c; icase d; try solve [exfalso; (try inv H; inv H0)].
     exists (true,false,false,false); repeat split; constructor.
     exists (false,true,false,false); repeat split; constructor.
     exists (false,false,true,false); repeat split; constructor.
     exists (false,false,false,true); repeat split; constructor.
     exists (false,false,false,false); repeat split; constructor.
  Qed.

Section JOIN_EQUIV.
(** The "equivalance" or discrete SA.  In this SA, every element of an arbitrary
    set is made an idempotent element.  We do not add this as a global
    #[global] Instance, because it is too widely applicable in cases where we do not
    desire it.
*)

  #[local] Instance Join_equiv (A: Type) : Join A := fun x y z => x=y/\y=z.

  #[local] Instance Perm_equiv (A: Type) :  @Perm_alg A (Join_equiv A).
  Proof. constructor; intros.
     destruct H; destruct H0; unfold equiv in *; subst; auto.
     destruct H; destruct H0; subst. exists e; split; split; auto.
     destruct H; split; subst; auto.
     destruct H; subst; reflexivity.
  Qed.

  #[local] Instance Sep_equiv (A: Type): FSep_alg A.
  Proof. apply mkSep with (fun a => a); intros.
            apply Perm_equiv.
            split; reflexivity.
            destruct H; subst; reflexivity.
  Defined.

  #[local] Instance Canc_equiv (A: Type): Canc_alg A.
  Proof. repeat intro. destruct H; destruct H0; subst; reflexivity. Qed.

  #[local] Instance Disj_equiv (A: Type): Disj_alg A.
  Proof. repeat intro. inv H0; auto. Qed.

  #[local] Instance Cross_equiv (A: Type): Cross_alg A.
  Proof. repeat intro. destruct H; destruct H0; subst.
   exists (z,z,z,z); repeat split; reflexivity.
  Qed.

Lemma join_equiv_refl: forall A (v: A), @join A (Join_equiv A) v v v.
Proof. split; auto. Qed.
End JOIN_EQUIV.

(* WARNING: DO NOT DO    [Existing Instance Join_equiv]   BECAUSE
   IT WILL MATCH IN UNINTENDED PLACES.  But I think it will do no harm
  to do the following Existing Instances: *)
#[global] Existing Instance Perm_equiv.
#[global] Existing Instance Sep_equiv.
#[global] Existing Instance Canc_equiv.
#[global] Existing Instance Disj_equiv.
#[global] Existing Instance Cross_equiv.

#[export] Hint Extern 1 (@join _ _ _ _ _) =>
   match goal with |- @join _ (@Join_equiv _) _ _ _ => apply join_equiv_refl end
   : core.

Section SepAlgProp.
  Variable A:Type.
  Variable JOIN: Join A.
  Variable PA: Perm_alg A.
  Variable P:A -> Prop.

  Variable HPjoin : forall x y z, join x y z -> P x -> P y -> P z.

  #[global] Instance Join_prop : Join (sig P) :=
                 fun x y z: (sig P) => join (proj1_sig x) (proj1_sig y) (proj1_sig z).

  #[global] Instance Perm_prop : Perm_alg (sig P).
  Proof.
   constructor; intros.
    destruct z; destruct z'. apply exist_ext. do 2 red in H,H0; eapply join_eq; eauto.
    do 2 red in H,H0.
    destruct (join_assoc H H0) as [f [? ?]].
     assert (P f) by (apply (HPjoin _ _ _ H1); auto; apply proj2_sig; auto).
     exists (exist P f H3).
     split; auto.
     do 2 red in H; apply join_comm in H; auto.
     do 2 red in H,H0. simpl in H,H0.
     destruct a, b; simpl; apply exist_ext; eapply join_positivity; eauto.
 Qed.

  #[global] Instance Sep_prop (SA: Sep_alg A)(HPcore : forall x, P x -> P (core x)): Sep_alg (sig P).
  Proof. repeat intro.
     exists (fun a : sig P => exist P (core (proj1_sig a)) (HPcore _ (proj2_sig a)));
      intros. apply Perm_prop.
      do 2 red. destruct t; simpl. apply join_comm; apply core_unit.
      exists (exist _ (core (proj1_sig c)) (HPcore _ (proj2_sig c))).
      hnf; simpl. eapply core_sub_join, join_core_sub, H.
      apply exist_ext. simpl. apply core_idem.
  Defined.

 #[global] Instance Sing_prop  (SA: Sep_alg A)(Sing_A: Sing_alg A)
               (HPcore : forall x, P x -> P (core x)): P the_unit ->
    @Sing_alg (sig P) Join_prop (Sep_prop _ HPcore).
 Proof. intros.
  apply (mkSing (exist P the_unit H)).
  intros. destruct a as  [a Ha]. simpl. apply exist_ext.
  rewrite <- (the_unit_core a). reflexivity.
 Defined.

  #[global] Instance Canc_prop  {CA: Canc_alg A}:  Canc_alg (sig P).
  Proof.
   intros [a Ha] [b Hb] [c1 Hc1] [c2 Hc2].
    unfold join, Join_prop; simpl; intros. apply exist_ext.
  eapply join_canc; eauto.
  Qed.

  #[global] Instance Disj_prop {DA: Disj_alg A}: Disj_alg (sig P).
  Proof. intros [a Ha][b Hb].
    unfold join, Join_prop; simpl; intros.
    intros [] [] Hj.
    eapply exist_ext, join_self; eauto.
  Qed.

(*  #[global] Instance CS_prop {CS: Cross_alg A}: Cross_alg (sig P). ... not true ...
  Proof. intros [a Ha][b Hb][c Hc][d Hd][z Hz].
    unfold join, Join_prop, equiv, Equiv_prop; simpl; intros.
   destruct (cross_split _ _ _ _ _ H H0) as [[[[ac ad] bc] bd][? [? [? ?]]]].
*)

End SepAlgProp.
#[global] Existing Instance Join_prop.
#[global] Existing Instance Perm_prop.
#[global] Existing Instance Sep_prop.
#[global] Existing Instance Sing_prop.
#[global] Existing Instance Canc_prop.
#[global] Existing Instance Disj_prop.

(** The function space operator from a key type [key] to
    a separation algebra on type [t'].
*)
Section SepAlgFun.
  Variable key: Type.
  Variable t' : Type.
  Variable JOIN: Join t'.
  Variable Pt': Perm_alg t'.

  #[global] Instance Join_fun: Join (key -> t') :=
                  fun a b c : key -> t' => forall x, join (a x) (b x) (c x).

  #[global] Instance Perm_fun : Perm_alg (key -> t').
  Proof.
   constructor; intros.
   extensionality k.
   apply (join_eq (H k) (H0 k)).
  exists (fun x => projT1 (join_assoc (H x) (H0 x))).
  split; intro k; destruct (join_assoc (H k) (H0 k)) as [f [? ?]]; auto.
  intro k; apply join_comm; apply H.
  extensionality k; specialize (H k); specialize (H0 k).
  apply (join_positivity H H0).
 Qed.

  #[global] Instance Sep_fun (SA: Sep_alg t'): Sep_alg (key -> t').
  Proof. exists (fun a k => core (a k)); intros.
   intro k; apply core_unit.
   eexists; intro. eapply core_sub_join, join_core_sub, H.
   extensionality k; apply core_idem.
 Defined.

 #[global] Instance Sing_fun (SA: Sep_alg t'): Sing_alg t' -> Sing_alg (key -> t').
 Proof.
 intros. apply (mkSing (fun _: key => the_unit)).
 intro a; extensionality k.
 rewrite <- (the_unit_core (a k)).
  unfold core. simpl. auto.
 Defined.

 #[global] Instance Canc_fun: Canc_alg t' -> Canc_alg (key -> t').
 Proof. repeat intro. extensionality x; apply (join_canc (H0 x) (H1 x)). Qed.

 #[global] Instance Disj_fun: Disj_alg t' -> Disj_alg (key -> t').
 Proof.  repeat intro. extensionality x. eapply join_self; eauto. Qed.
End SepAlgFun.

#[global] Existing Instance Join_fun.
#[global] Existing Instance Perm_fun.
#[global] Existing Instance Sep_fun.
#[global] Existing Instance Sing_fun.
#[global] Existing Instance Canc_fun.
#[global] Existing Instance Disj_fun.

(** The dependent product SA operator from an index set [I] into
    a SA indexed by [Pi_j].  The construction of this
    operator either requires constructive witnesses for the unit
    and associativity axioms or some form of the axiom of choice.
    We have chosen to have explicitly constructive witnesses
    and avoid the use of choice.
*)

Section SepAlgPi.
  Variable I:Type.
  Variable Pi: I -> Type.
  Variable pi_J: forall i, Join (Pi i).
  Variable PA:  forall i, Perm_alg (Pi i).

  Let P := forall i:I, Pi i.

  #[global] Instance Join_pi: Join P := fun x y z => forall i:I, join (x i) (y i) (z i).

  #[global] Instance Perm_pi  : Perm_alg P.
  Proof.
   constructor; intros.
   extensionality i. apply (join_eq (H i) (H0 i)).
   exists (fun i => projT1 (join_assoc (H i) (H0 i))).
   split; intro i; destruct (join_assoc (H i) (H0 i)) as [f [? ?]]; auto.
   intro i; apply join_comm; auto.
   extensionality i. specialize (H i); specialize (H0 i).
   apply (join_positivity H H0).
 Qed.

  #[global] Instance Sep_pi (SA : forall i:I, Sep_alg (Pi i)): Sep_alg P.
  Proof. exists (fun a i => core (a i)); intros.
   intro i; apply core_unit.
   exists (fun i => core (c i)); intro.
   eapply core_sub_join, join_core_sub, H.
   extensionality i; apply core_idem.
 Defined.

  #[global] Instance Canc_pi: (forall i, Canc_alg (Pi i)) -> Canc_alg P.
  Proof. repeat intro. extensionality i; apply (join_canc (H0 i) (H1 i)). Qed.

  #[global] Instance Disj_pi: (forall i, Disj_alg (Pi i)) -> Disj_alg P.
  Proof. repeat intro. extensionality i; apply (join_self (H0 i)); auto. Qed.

End SepAlgPi.
#[global] Existing Instance Join_pi.
#[global] Existing Instance Perm_pi.
#[global] Existing Instance Sep_pi.
#[global] Existing Instance Canc_pi.
#[global] Existing Instance Disj_pi.

(** The dependent sum operator on SAs.

   Here we have defined the operator under the hypothesis
   that dependent pairs are injective.  This property can
   be proved without axioms provided that
   the index type [I] enjoys decidable equality.

   The property for all types follows as a corollary of
   Streicher's K axiom (or one of its equivalants).
   The K axiom, in turn, follows from the classical axiom.
   Users who are willing to assume K can then use this
   construction at any index type.

   However, in this version, we use inj_pair2, which comes from
   msl.EXtensionality; the proof there relies on
   proof-irrelevance (but not on stronger forms of extensionality).
*)
Section SepAlgSigma.
  Variable I:Type.
  Variable Sigma: I -> Type.
  Variable JOIN: forall i, Join (Sigma i).
  Variable PA: forall i, Perm_alg (Sigma i).
  Let S := sigT Sigma.

  Inductive join_sigma : S -> S -> S -> Prop :=
    j_sig_def : forall (i:I) (a b c:Sigma i),
      join a b c ->
      join_sigma (existT Sigma i a) (existT Sigma i b) (existT Sigma i c).

  #[global] Instance Join_sigma: Join S := join_sigma.

  #[global] Instance Perm_sigma: Perm_alg S.
  Proof.  constructor; intros.

    (* join_eq *)
    destruct z as [z Hz]. destruct z' as [z' Hz'].
    destruct x as [x Hx]; destruct y as [y Hy].
    assert (z=z').
    inv H. subst.
    apply inj_pair2 in H3; subst.  apply inj_pair2 in H5; subst.
    apply inj_pair2 in H7; subst.
    inv H0; subst; auto. subst z'.
    f_equal.
    inv H; subst.
   apply inj_pair2 in H3; subst.
    apply inj_pair2 in H5; subst.  apply inj_pair2 in H7;  subst.
    inv H0; subst.
   apply inj_pair2 in H3; subst.
    apply inj_pair2 in H4; subst.  apply inj_pair2 in H5;  subst.
    eapply join_eq; eauto.

    (* join_assoc *)
    destruct a as [ai a]; destruct b as [bi b]; destruct c as [ci c];
    destruct d as [di d]; destruct e as [ei e].
    assert (ai = bi /\ bi = ci /\ ci = di /\ di = ei).
    inv H; inv H0; simpl; auto.
    decompose [and] H1; subst; clear H1.
    rename ei into i.
    assert (join a b d).
    inversion H. apply inj_pair2 in H3. apply inj_pair2 in H4. apply inj_pair2 in H5.
    subst; auto.
    assert (join d c e).
    inversion H0. apply inj_pair2 in H4. apply inj_pair2 in H5. apply inj_pair2 in H6.
    subst; auto.
    destruct (join_assoc H1 H2) as [f [? ?]].
    exists (existT Sigma i f).
    split; constructor; auto.

    (* join_comm *)
    inv H; subst.
    constructor.
    apply join_comm; auto.

    (* join_positivity *)
    inv H; inv H0.  apply inj_pair2 in H3.  apply inj_pair2 in H5.  subst.
    f_equal.
    eapply join_positivity; eauto.
 Qed.



  #[global] Instance Sep_sigma (SA : forall i:I, Sep_alg (Sigma i)) : Sep_alg S.
  Proof. exists
      (fun (a : S) => existT Sigma (projT1 a) (core (projT2 a))).
   intros [i a]. constructor. apply core_unit.
   intros. inv H. eexists; constructor. eapply core_sub_join, join_core_sub, H0.
   intros. simpl. rewrite core_idem; reflexivity.
  Defined.

  #[global] Instance Canc_sigma: (forall i, Canc_alg (Sigma i)) -> Canc_alg S.
  Proof. repeat intro.
       destruct a1; destruct a2; destruct b; destruct c;
       inv H0; inv H1; subst.
       repeat match goal with H: existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end.
     subst.
    f_equal. apply (join_canc H3 H2).
  Qed.

  #[global] Instance Disj_sigma: (forall i, Disj_alg (Sigma i)) -> Disj_alg S.
  Proof. repeat intro.
    destruct a as [ia a]; destruct b as [ib b].
  (* Some weird bug in Coq requires this two-stage inversion process *)
    red in H0. generalize H0; intro. inv H2.
     apply inj_pair2 in H8; apply inj_pair2 in H5; apply inj_pair2 in H6;
     subst. inv H0.
     apply inj_pair2 in H7; apply inj_pair2 in H5; apply inj_pair2 in H6;
     subst.
    inv H1. apply inj_pair2 in H5; subst.
    f_equal; eapply join_self; eauto.
 Qed.
End SepAlgSigma.

#[global] Existing Instance Join_sigma.
#[global] Existing Instance Perm_sigma.
#[global] Existing Instance Sep_sigma.
#[global] Existing Instance Canc_sigma.
#[global] Existing Instance Disj_sigma.

(** The SA operator on cartesian products. *)
Section SepAlgProd.

  Variables (A: Type) (Ja: Join A).
  Variables (B: Type) (Jb: Join B) .

  #[local] Instance Join_prod : Join (A*B) :=
               fun (x y z:A*B) =>  join (fst x) (fst y) (fst z) /\ join (snd x) (snd y) (snd z).

  Variables (PAa: Perm_alg A)(PAb: Perm_alg B).
  #[local] Instance Perm_prod  : Perm_alg (A*B).
  Proof.
    constructor.

    (* join_eq *)
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    f_equal; simpl; eapply join_eq; eauto.

    (* join_assoc *)
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    destruct (join_assoc H H1) as [x [? ?]].
    destruct (join_assoc H0 H2) as [y [? ?]].
    exists (x,y); simpl; repeat split; auto.

    (* join_comm *)
    intros [? ?] [? ?] [? ?] [? ?]; repeat split; simpl in *; apply join_comm; auto.

    (* join_positivity *)
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    f_equal; simpl; eapply join_positivity; eauto.
 Qed.

  #[global] Instance Sep_prod (SAa: Sep_alg A) (SAb: Sep_alg B) : Sep_alg (A*B).
  Proof.
    exists (fun a => (core (fst a), core (snd a))).
    intros [? ?]; split; apply core_unit; auto.
    intros [? ?] [? ?] [? ?] [? ?].
    eexists (_, _); split; simpl; eapply core_sub_join, join_core_sub; eassumption.
    intros. simpl. rewrite !core_idem; reflexivity.
  Defined.

  #[global] Instance Sing_prod {SAa: Sep_alg A} {SAb: Sep_alg B} {SingA: Sing_alg A}{SingB: Sing_alg B}: Sing_alg (A*B).
  Proof. apply (mkSing  (the_unit, the_unit)).
     intros [? ?].  f_equal; simpl; f_equal; apply the_unit_core.
  Defined.

  #[global] Instance Canc_prod {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A*B).
  Proof. intros  [? ?] [? ?] [? ?] [? ?] [? ?] [? ?].
   f_equal; simpl in *; eapply join_canc;eauto.
  Qed.

  #[global] Instance Disj_prod {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A*B).
  Proof. intros  [? ?]  [? ?] [? ?] [] [] Hj.
   f_equal; simpl in *; inv Hj; eapply join_self; eauto.
  Qed.

End SepAlgProd.

Arguments Perm_prod [A] [Ja] [B] [Jb] _ _.
Arguments Sep_prod [A] [Ja] [B] [Jb] [PAa] [PAb] _ _.
#[global] Existing Instance Join_prod.
#[global] Existing Instance Perm_prod.
#[global] Existing Instance Sep_prod.
#[global] Existing Instance Canc_prod.
#[global] Existing Instance Disj_prod.

(** The SA operator on disjoint sums. *)
Section SepAlgSum.

  Variables (A: Type) (Ja: Join A) .
  Variables (B: Type) (Jb: Join B) .
  Variables (PAa: Perm_alg A) (PAb: Perm_alg B).
  #[global] Instance Join_sum : Join (A+B) :=
    (fun (x y z: A+B) =>
    match x, y, z with
    | inl xa, inl ya, inl za => join xa ya za
    | inr xb, inr yb, inr zb => join xb yb zb
    | _, _, _ => False
    end).

  #[global] Instance Perm_sum: Perm_alg (A+B).
  Proof.
    constructor.

    intros. icase x; icase y; icase z; icase z'; simpl in *; hnf; simpl;
    f_equal; eapply join_eq; eauto.

    (* join_assoc *)
    intros; destruct e,a,b,c,d; try contradiction; hnf in H,H0;
    destruct (join_assoc H H0) as [f [? ?]].
    exists (inl B f); simpl; auto.
    exists (inr A f); simpl; auto.

    (* join_comm *)
    intros; destruct a; destruct b; destruct c; hnf in H|-*; try contradiction;
    apply join_comm; auto.

    (* join_positivity *)
    intros; hnf in H,H0|-*; destruct a; destruct a'; destruct b; destruct b'; try contradiction;
    f_equal; eapply join_positivity; eauto.
 Qed.

  #[global] Instance Sep_sum (SAa: Sep_alg A) (SAb: Sep_alg B): Sep_alg (A+B).
  Proof.
    exists (fun ab : A+B =>
              match ab with
              | inl a => inl _ (core a)
              | inr b => inr _ (core b)
              end).
    intro a; icase a; hnf; apply core_unit; auto.
    intros; icase a; icase b; icase c; hnf in *; try contradiction; [eexists (inl _) | eexists (inr _)]; simpl; eapply core_sub_join, join_core_sub, H.
    intros [|]; rewrite core_idem; reflexivity.
  Defined.

  #[global] Instance Canc_sum {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A+B).
  Proof. repeat intro. icase a1; icase a2; icase b; icase c; hnf;
    f_equal; eapply join_canc; hnf in *; eauto.
  Qed.

  #[global] Instance Disj_sum {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A+B).
  Proof. repeat intro. icase a; icase b; icase a0; icase b0; eapply f_equal, join_self; eauto.
  Qed.

End SepAlgSum.
#[global] Existing Instance Join_sum.
#[global] Existing Instance Perm_sum.
#[global] Existing Instance Sep_sum.
#[global] Existing Instance Canc_sum.
#[global] Existing Instance Disj_sum.

(** The SA operator on lists.  Lists are joined componentwise.
 *)
Section sa_list.

  Variables (A: Type) (Ja: Join A)  (PAa: Perm_alg A).

  Inductive list_join : list A -> list A -> list A -> Prop :=
  | lj_nil : list_join nil nil nil
  | lj_cons : forall x y z xs ys zs,
      join x y z ->
      list_join xs ys zs ->
      list_join (x::xs) (y::ys) (z::zs).

  #[global] Instance Join_list: Join (list A) := list_join.

  #[global] Instance Perm_list: Perm_alg (list A).
  Proof.
    constructor.

    induction x; intros; inv H; inv H0; auto; try constructor.
    f_equal. eapply join_eq; eauto. eapply IHx; eauto.

    induction a; intros;
    destruct b; destruct d; try (exfalso; inv H; fail);
    destruct c; destruct e; try (exfalso; inv H0; fail).
    exists nil. split; constructor.
    assert (join a a1 a2) by (inv H; auto).
    assert (join a2 a3 a4) by (inv H0; auto).
    assert (list_join a0 b d) by (inv H; auto).
    assert (list_join d c e) by (inv H0; auto).
    destruct (join_assoc H1 H2) as [z [? ?]].
    destruct (IHa _ _ _ _ H3 H4) as [zs [? ?]].
    exists (z::zs); split; constructor; auto.
    induction a; intros; inv H; constructor; auto.
    apply IHa; auto.

    induction a; intros.
    inv H; inv H0; auto.
    inv H0; inv H.
    f_equal.  eapply join_positivity; eauto.
    eapply IHa; eauto.
 Qed.

  #[global] Instance Sep_list (SAa: Sep_alg A) : Sep_alg (list A).
  Proof.
    exists (map core).
    induction t; constructor; auto; apply core_unit.
    intros; induction H.
    { eexists; constructor. }
    destruct (join_core_sub H), IHlist_join.
    eexists; constructor; eauto.
    intros; rewrite map_map.
    apply map_ext, core_idem.
 Defined.

  #[global] Instance Canc_list {CA: Canc_alg A}: Canc_alg (list A).
  Proof.
   intro. induction a1; intros; inv H; inv H0; auto.
    f_equal.
     eapply join_canc;eauto.
   eapply IHa1; eauto.
  Qed.

  #[global] Instance Disj_list {DAa: Disj_alg A} : Disj_alg (list A).
  Proof. intro. induction a; repeat intro; inv H; inv H0; auto.
    f_equal; [eapply join_self; eauto | eapply IHa; eauto].
  Qed.

End sa_list.
#[global] Existing Instance Join_list.
#[global] Existing Instance Perm_list.
#[global] Existing Instance Sep_list.
#[global] Existing Instance Canc_list.
#[global] Existing Instance Disj_list.

(** A join homomorphism is a function from one separation
    algebra to another which preserves the join relation.

    This is used when we build the sa_preimage (to add a Perm_alg to the knot).
 *)

Definition raw_join_hom A B (j1: A -> A -> A -> Prop) (j2: B -> B -> B -> Prop) (f:A ->B) :=
  forall x y z,
    j1 x y z ->
    j2 (f x) (f y) (f z).
Arguments raw_join_hom [A B] _ _ _.

Definition join_hom {A} {JA: Join A} {B} {JB: Join B} (f:A ->B) :=
  forall x y z,
    join x y z ->
    join (f x) (f y) (f z).

(** The SA induced by the preimage of a section
    in a section-retraction pair.

    This SA construction is used to generate
    a separation algebra over "knots".
 *)
Section sa_preimage.
  Variables A B:Type.
  Variable B_J: Join B.
   Variable PA: Perm_alg B.

  Variable f:A -> B.
  Variable f':B -> A.

  Hypothesis Hf'_f : forall x, f' (f x) = x.
  Hypothesis Hf_f' : join_hom (f oo f').

  Lemma f_inj : forall x y : A,  f x = f y -> x = y.
  Proof.
    intros.
    rewrite <- (Hf'_f x).
    rewrite <- (Hf'_f y).
    rewrite H; auto.
  Qed.

  #[global] Instance Join_preimage: Join A :=
          fun a b c => join (f a) (f b) (f c).

  #[global] Instance Perm_preimage  : @Perm_alg _  Join_preimage.
  Proof.
    constructor; simpl; intros.
   do 2 red in H,H0.
   apply f_inj.
   apply (join_eq H H0).

    do 2 red in H,H0.
    destruct (join_assoc H H0) as [z [? ?]].
    exists (f' z).
    split;
     [ do 2 red; rewrite <- (Hf'_f b); rewrite <- (Hf'_f c)
     | do 2 red; rewrite <- (Hf'_f a); rewrite <- (Hf'_f e)];
    apply (Hf_f' _ _ _); auto.

    do 2 red in H|-*; auto.

    apply f_inj; eapply join_positivity; eauto.
 Qed.

  Context {SAb: Sep_alg B}.
  Hypothesis Hcore : forall x, core (f (f' x)) = f (f' (core x)).

  #[global] Instance Sep_preimage : Sep_alg A.
  Proof.
    exists (fun x : A => f' (core (f x))); intros.

    do 3 red.
    generalize (@Hf_f' (@core B B_J SAb (f t)) (f t) (f t) (core_unit _)).
    intro.
    unfold compose in H. rewrite Hf'_f in H. auto.
    do 2 red in H.
    exists (f' (core (f c))); apply Hf_f'.
    apply join_core_sub in H; apply core_sub_join; auto.
    rewrite Hcore, Hf'_f, core_idem. reflexivity.
  Defined.

 #[global] Instance Sing_preimage {Sing_b: Sing_alg B}: Sing_alg A.
 Proof.
 apply (mkSing (f' the_unit)).
 intro.
 simpl. rewrite <- (the_unit_core (f a)). reflexivity.
 Defined.

 #[global] Instance Canc_preimage {CAb: Canc_alg B} : Canc_alg A.
 Proof. intros ? ? ? ? ? ?. do 2 red in H,H0.
  generalize (join_canc H H0); intro.
  apply f_inj; auto.
 Qed.

 #[global] Instance Disj_preimage {DAb: Disj_alg B} : Disj_alg A.
  Proof. repeat intro. do 2 red in H. apply join_self in H. apply f_inj; auto.
  Qed.

End sa_preimage.

#[global] Existing Instance Join_preimage.
#[global] Existing Instance Perm_preimage.
#[global] Existing Instance Sep_preimage.
#[global] Existing Instance Sing_preimage.
#[global] Existing Instance Canc_preimage.
#[global] Existing Instance Disj_preimage.

Section SepAlgBijection.
  Variables (A: Type) (Ja: Join A)(PAa: Perm_alg A).
  Variable B:Type .

  Variable bij : bijection A B.
  #[global] Instance Join_bij: Join B := fun (x y z : B) => join (bij_g _ _ bij x) (bij_g _ _ bij y) (bij_g _ _ bij z).

  Lemma Perm_bij  : Perm_alg B.
  Proof.
    constructor; intros.

    do 2 red in H,H0.
    generalize (join_eq H H0); clear H H0; intro.
    rewrite <- (bij_fg _ _ bij z). rewrite <- (bij_fg _ _ bij z'). f_equal; auto.

    do 2 red in H,H0.
   destruct (join_assoc H H0) as [m [? ?]]; exists (bij_f _ _ bij m); split;
   do 2 red; rewrite bij_gf; auto.

    do 2 red in H|-*. apply join_comm; auto.

    do 2 red in H,H0. rewrite <- (bij_fg _ _ bij a); rewrite <- (bij_fg _ _ bij b).
    f_equal. eapply join_positivity; eauto.
   Qed.


  #[global] Instance Sep_bij {SAa: Sep_alg A} : Sep_alg B.
  Proof.
   exists (fun b => bij_f _ _ bij (core (bij_g _ _ bij b))); intros.
   do 3 red.
   repeat rewrite bij_gf. simpl. apply core_unit.
   hnf in H. apply join_core_sub in H as [x ?].
   exists (bij_f _ _ bij x); hnf. rewrite !bij_gf; auto.
   rewrite bij_gf, core_idem; reflexivity.
 Defined.

 Lemma Sing_bij {SAa: Sep_alg A}{SingA: Sing_alg A} : Sing_alg B.
  Proof.
   apply (mkSing (bij_f _ _ bij the_unit)); intros.
   simpl. f_equal. apply  (the_unit_core (bij_g _ _ bij a)).
  Defined.

 #[global] Instance Canc_bij {SAa: Canc_alg A} : Canc_alg B.
  Proof. repeat intro.
    do 2 red in H,H0.
    generalize (join_canc H H0);intro.
    rewrite <- (bij_fg _ _ bij a1). rewrite <- (bij_fg _ _ bij a2). rewrite H1; auto.
  Qed.

  #[global] Instance  Disj_bij {DAa: Disj_alg A} : Disj_alg B.
  Proof. repeat intro. do 2 red in H.
    apply join_self in H.
    specialize (H _ _ H0).
    eapply bij_g_inj; eauto.
  Qed.

End SepAlgBijection.
#[global] Existing Instance Join_bij.
#[global] Existing Instance Perm_bij.
#[global] Existing Instance Sep_bij.
#[global] Existing Instance Sing_bij.
#[global] Existing Instance Canc_bij.
#[global] Existing Instance Disj_bij.
