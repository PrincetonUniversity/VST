(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.sepalg.
Require Import msl.psepalg.
Require Import msl.sepalg_generators.
Require Import msl.cjoins.
Require Import msl.eq_dec.

(** The cross split axiom looks unwieldly,
    but here we show that it arises naturally
    as a kind of distributivity property.
    Cross split can be rendered, with some accuracy,
    as "the separation algebra is distributive."
 *)

  (** This definition mirrors the definition of
      distributivity in a join-semilattice.  This
      definition generalizes the standard notion of
      distributivity in a lattice, but only mentions
      of the lattice operators.  Here we transplant
      the semilattice definition into the setting
      of separation algebras.
    *)
  Definition sa_distributive (A: Type) {JOIN: Join A} :=
    forall a b x z,
      join a b z ->
      constructive_join_sub x z ->
      {a' : A & {b' : A & 
           (constructive_join_sub a' a * constructive_join_sub b' b * join a' b' x)%type}}.

(*
  (** We define this weaker version of cross-split
      in order to show that the sa_distributive
      axiom is equivalent. The ordinary cross_split
      is more constructive (it uses a sigma type rather
      than 'exists'), so we have to weaken it to show
      the correspondence.  We could, instead, define
      and use a constructive version of join_sub.
    *)
  Definition weak_cross_split `{sepalg A} :=
    forall a b c d z : A,
      join a b z ->
      join c d z ->
      exists x:(A*A*A*A), match x with (ac,ad,bc,bd) =>
         join ac ad a /\
         join bc bd b /\
         join ac bc c /\
         join ad bd d
       end.
*)

  (** Here we show that the cross split axiom is
      the same as the statement of distributivity
      for join semilattices transliterated into the
      setting of separation algebras.
    *)
  Theorem cross_split_distibutive {A} `{Perm_alg A}{SA: Sep_alg A}{CS: Cross_alg A} :
          sa_distributive A.
  Proof.
    intros ? ? ? ? H1 [x0 H2].
    destruct (CS _ _ _ _ _ H1 H2) as [[[[? ?] ?] ?] ?].
    intuition eauto.
    exists a0.
    exists a2.
    intuition eauto.
    econstructor; eauto.
    econstructor; eauto.
  Qed.

  Theorem distributive_cross_split {A} `{Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
     sa_distributive A -> Cross_alg A.
  Proof.
    intros H0.
    repeat intro.
    hnf in H0.
    destruct (H0 a b c z H1) as [a' [b' [[?H ?H] ?H]]].
    exists d; auto.
    destruct H3 as [q ?H].
    destruct H4 as [w ?H].
    exists (a',q,b',w). split; auto. split; auto. split; auto.
    destruct (join_assoc H3 H1) as [f [? ?]].
    apply join_comm in H6.
    destruct (join_assoc H4 H6) as [g [? ?]].
    assert (H10: g = d); [ | rewrite H10 in *; auto].
    apply join_comm in H7.
    apply join_comm in H9.
    destruct (join_assoc H9 H7) as [h [? ?]].
    generalize (join_eq H5 (join_comm H10)); intro.
    rewrite <- H12 in *; clear H12 h.
    eapply join_canc; eauto.
  Qed.

(** NOTICE ABOUT REDUNDANT LEMMAS:
 Since sa_distribute <-> cross_split, many of the proofs below are redundant.
 This was part of an experiment to see whether, in general, sa_distributive is
 simpler to prove than cross_split.  Short answer:  not really.
*)

Lemma distributive_equiv: forall A, @sa_distributive  _ (@Join_equiv A).
Proof.
  repeat intro.
 destruct H; subst.
 exists x; exists x; repeat split; auto.  
Qed.

Lemma cross_split_equiv : forall A,  @Cross_alg _ (@Join_equiv A).
Proof.
  repeat intro.
  destruct H; destruct H0. subst. exists (((z,z),z),z). repeat split; auto.
Qed.

Lemma distributive_fun: forall A (JOIN: Join A) (key: Type),
               sa_distributive A -> @sa_distributive (key -> A) (Join_fun key A JOIN).
Proof.
unfold sa_distributive; intros.
assert (forall k, constructive_join_sub (x k) (z k)).
destruct X0 as [y ?].
intro k; exists (y k); auto.
assert (J := fun (k: key) => X (a k) (b k) (x k) (z k) (H k) (X1 k)).
clear X.
exists (fun k => projT1 (J k)).
exists (fun k => projT1 (projT2 (J k))).
split; [split|].
exists (fun k => projT1 (fst (fst (projT2 (projT2 (J k))))));
intro k; destruct (J k) as [ak' [bk' [[c c0] j]]];  simpl; destruct c; auto.
exists (fun k => projT1 (snd (fst (projT2 (projT2 (J k))))));
intro k; destruct (J k) as [ak' [bk' [[c c0] j]]];  simpl; destruct c0; auto.
intro k; destruct (J k) as [ak' [bk' [[c c0] j]]]; simpl; auto.
Qed.

Instance cross_split_fun: forall A (JOIN: Join A) (key: Type),
          Cross_alg A -> Cross_alg (key -> A).
Proof.
repeat intro.
pose (f (x: key) := projT1 (X (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))).
pose (g (x: key) := projT2 (X (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))).
pose (ac (x: key) := fst (fst (fst (f x)))).
pose (ad (x: key) := snd (fst (fst (f x)))).
pose (bc (x: key) := snd (fst (f x))).
pose (bd (x: key) := snd (f x)).
exists (ac,ad,bc,bd).
unfold ac, ad, bc, bd, f; clear ac ad bc bd f.
repeat split; intro x; simpl;
generalize (g x);  destruct (projT1 (X (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))) as [[[? ?] ?] ?]; simpl; intuition.
Qed.

Lemma sa_distributive_prod : forall A B saA saB,
  @sa_distributive A saA ->
  @sa_distributive B saB ->
  @sa_distributive (A * B) (Join_prod A _ B _).
Proof.
 intros.
 intros [a1 a2] [b1 b2] [c1 c2] [z1 z2] [? ?].
 intros [[d1 d2] [? ?]].
 simpl in *.
 destruct (X a1 b1 c1 z1 H) as [a1' [b1' [[[u1 ?] [v1 ?]] ?]]]. exists d1; auto.
 destruct (X0 a2 b2 c2 z2 H0) as [a2' [b2' [[[u2 ?] [v2 ?]] ?]]]. exists d2; auto.
 exists (a1',a2'). exists (b1',b2').
 split; [split|].
 exists (u1,u2); split; auto.
 exists (v1,v2); split; auto.
 split; auto.
Qed.

Instance Cross_prod : forall A B saA saB,
  @Cross_alg A saA ->
  @Cross_alg B saB ->
  @Cross_alg (A * B) (Join_prod _ saA _ saB).
Proof.
  repeat intro.
  destruct a as [a1 a2].
  destruct b as [b1 b2].
  destruct c as [c1 c2].
  destruct d as [d1 d2].
  destruct z as [z1 z2].
  destruct H.
  destruct H0.
  simpl in *.
  destruct (X a1 b1 c1 d1 z1)
    as [p ?]; auto.
  destruct p as [[[s1 p1] q1] r1].
  destruct (X0 a2 b2 c2 d2 z2)
    as [p ?]; auto.
  destruct p as [[[s2 p2] q2] r2].
  exists ((s1,s2),(p1,p2),(q1,q2),(r1,r2)).
  simpl; intuition; (split; simpl; auto).
Qed.

Lemma sa_distributive_bij : forall A B JA bij,
  @sa_distributive A JA ->
  @sa_distributive B (Join_bij A JA B bij).
Proof.
 repeat intro.
 destruct X0 as [u ?]. unfold Join_bij; simpl.
 destruct bij. simpl.
 destruct (X (bij_g a) (bij_g b) (bij_g x) (bij_g z)) as [a' [b' [[[? ?] [? ?]] ?]]]; auto.
 exists (bij_g u); auto.
 exists (bij_f a'); exists (bij_f b'); split; [split|].
 exists (bij_f x0); hnf; repeat rewrite bij_gf; auto.
 exists (bij_f x1); hnf; repeat rewrite bij_gf; auto.
 hnf; repeat rewrite bij_gf; auto.
Qed. 

Lemma Cross_bij : forall A B JA bij,
  @Cross_alg A  JA ->
  @Cross_alg B (Join_bij A JA B bij).
Proof.
  repeat intro. unfold join, Join_bij in *.
  destruct bij. simpl in *.
  destruct (X (bij_g a) (bij_g b) (bij_g c) (bij_g d) (bij_g z)); auto.
  destruct x as [[[s p] q] r].
  exists (bij_f s,bij_f p,bij_f q,bij_f r).
  simpl.
  repeat rewrite bij_gf.
  auto.
Qed.

Lemma constructive_join_sub_smash {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
  (forall x:A, {identity x}+{~identity x}) ->
  forall a c : lifted JA,
    constructive_join_sub (projT1 a) (projT1 c) ->
    @constructive_join_sub (option (lifted JA)) _ (Some a) (Some c).
Proof.
intros.
destruct X0 as [b ?].
destruct (X b).
assert (a=c).
destruct a; destruct c. apply exist_ext.
simpl in j.
eapply join_eq; try apply j. apply join_comm; apply identity_unit; eauto.
subst c.
exists None; constructor.
exists (Some (mk_lifted _ (nonidentity_nonunit n))).
constructor.
destruct a; destruct c; simpl in *.
auto.
Qed.

Lemma sa_distributive_smash : forall A JA {PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A},
  (forall x:A, {identity x}+{~identity x}) ->
  @sa_distributive A JA ->
  sa_distributive (option (lifted JA)).
Proof.
intros. unfold Join_lower, Join_lift; simpl.
intros [[a Ha]|].
2: intros; assert (b=z) by (inv H; auto); subst z; exists None; exists x;
    split; [split|]; auto; [ econstructor  | ]; constructor.
intros [[b Hb]|].
2: intros b [[z Hz]|] ? ?; 
 [assert (a=z) by (inv H; auto); subst z; clear H;
   rewrite (proof_irr Hz Ha) in X1; clear Hz; exists b; exists None;
    split; [split|]; auto
 | elimtype False; inv H];
  [ econstructor  | ]; constructor.
intros [[c Hc]|].
2: intros ? ? ?; exists None; exists None; split; [split|]; econstructor; econstructor.
intros [[z Hz]|] H Hj.
2: elimtype False; inv H.
destruct (X0 a b c z) as [a' [b' [[? ?] ?]]].
inv H. apply H3.
inversion Hj.
destruct x.
exists (lifted_obj l). inv H0.  apply H4.
assert (c=z) by (inv H0; auto). replace c with z.
apply constructive_join_sub_refl.
destruct (X a') as [Pa'|Pa']; [exists None | exists (Some (mk_lifted _ (nonidentity_nonunit Pa'))) ].
assert (b'=c) by (eapply join_eq; try apply j; apply identity_unit; eauto).
subst b'.
exists (Some (mk_lifted c Hc)).
split; [split|]; eauto. econstructor; econstructor.
apply constructive_join_sub_smash; auto.
constructor.
destruct (X b') as [Pb'|Pb']; [exists None | exists (Some (mk_lifted _ (nonidentity_nonunit Pb')))].
split; [split|]; eauto.
apply constructive_join_sub_smash; auto.
econstructor; econstructor.
apply join_unit2. econstructor; eauto.
f_equal. apply exist_ext.
symmetry. eapply join_eq. eapply join_comm; apply j.  apply identity_unit; eauto.
split; [split|]; eauto.
apply constructive_join_sub_smash; auto.
apply constructive_join_sub_smash; auto.
constructor; auto.
Qed.

Lemma Cross_smash : forall A (JA: Join A) {PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A},
  (forall x:A, {identity x}+{~identity x}) ->
  Cross_alg A ->
  Cross_alg (option (lifted JA)).
Proof.
  intros.
  hnf; intros.
  destruct a as [[a Na] | ].
Focus 2.
  apply join_unit1_e in H; [ | apply None_identity]. subst z.
  exists (None,None,c,d); repeat split; auto; constructor; auto.
  destruct b as [[b Nb] | ].
Focus 2.
  apply join_unit2_e in H; [ | apply None_identity]. subst z.
  exists (c,d,None,None); repeat split; auto; constructor; auto.
  destruct c as [[c Nc] | ].
Focus 2.
  apply join_unit1_e in H0; [ | apply None_identity]. subst z.
  exists (None, Some (exist nonunit _ Na), None, Some (exist nonunit _ Nb)); 
     repeat split; auto; constructor.
  destruct d as [[d Nd] | ].
Focus 2.
  apply join_unit2_e in H0; [ | apply None_identity]. subst z.
  exists (Some (exist nonunit _ Na), None,Some (exist nonunit _ Nb),None); repeat split; auto; constructor; auto.

  destruct z as [[z Nz] | ]; [ | elimtype False; inv H].
  destruct (X0 a b c d z) as [[[[ac ad] bc] bd] [? [? [? ?]]]]; try (inv H; inv H0; auto). clear H H0.
  destruct (X ac) as [Nac | Nac ].
  apply Nac in H1. subst ad. apply Nac in H3. subst bc.
  destruct (X bd) as [Nbd | Nbd].
  apply join_unit2_e in H4; auto. subst d.
  apply join_unit2_e in H2; auto. subst c.
  rewrite (proof_irr Nd Na) in *. rewrite (proof_irr Nc Nb) in *.
  exists (None, Some (exist nonunit a Na), Some (exist nonunit b Nb), None);
    repeat split; auto;  constructor.
  exists (None, Some (exist nonunit a Na), Some (exist nonunit c Nc), 
      Some (exist nonunit bd (nonidentity_nonunit Nbd))).
  repeat split; auto;  try constructor. apply H2. apply H4.
  destruct (X ad) as [Nad | Nad].
  apply join_unit2_e in H1; auto. subst ac.
  apply join_unit1_e in H4; auto. subst bd.
  destruct (X bc) as [Nbc | Nbc].
  apply join_unit2_e in H3; auto. subst c.
  apply join_unit1_e in H2; auto. subst d.
  rewrite (proof_irr Nd Nb) in *. rewrite (proof_irr Nc Na) in *.
  exists (Some (exist nonunit a Na), None, None, Some (exist nonunit b Nb));
    repeat split; auto; constructor.
  apply nonidentity_nonunit in Nbc.
  exists (Some (exist nonunit a Na), None, Some (exist nonunit _ Nbc), Some (exist nonunit d Nd));
    repeat split; auto; constructor. apply H2. apply H3.
  destruct (X bc) as [Nbc | Nbc].
  apply join_unit2_e in H3; auto. subst ac.
  apply join_unit1_e in H2; auto. subst bd.
  apply nonidentity_nonunit in Nad.
  exists (Some (exist nonunit c Nc), Some (exist nonunit _ Nad), None, Some (exist nonunit b Nb));
    repeat split; auto; try constructor. apply H1. apply H4.
  destruct (X bd) as [Nbd | Nbd].
  apply join_unit2_e in H2; auto. subst bc.
  apply join_unit2_e in H4; auto. subst ad.
  apply nonidentity_nonunit in Nbc.   apply nonidentity_nonunit in Nad.
    apply nonidentity_nonunit in Nac.
  exists (Some (exist nonunit ac Nac), Some (exist nonunit d Nd), 
             Some (exist nonunit b Nb), None).
    repeat split; auto; try constructor. apply H1. apply H3.
  apply nonidentity_nonunit in Nbc.   apply nonidentity_nonunit in Nad.
    apply nonidentity_nonunit in Nac. apply nonidentity_nonunit in Nbd.
  exists (Some (exist nonunit ac Nac), Some (exist nonunit ad Nad), 
             Some (exist nonunit bc Nbc), Some (exist nonunit bd Nbd)).
  repeat split; constructor; assumption.
Qed.

Lemma cross_split_fpm : forall A B 
      (JB: Join B) (PB: Perm_alg B)(SB : Sep_alg B)(CB: Canc_alg B)
  (Bdec: forall x:B, {identity x}+{~identity x}) ,
  Cross_alg B  ->
  Cross_alg (fpm A (lifted JB)) .
Proof.
  intros.
  assert (Cross_alg (A -> option (lifted JB))).
  apply cross_split_fun. apply Cross_smash; auto.

  hnf. intros [a Ha] [b Hb] [c Hc] [d Hd] [z Hz].
  simpl; intros.
  destruct (X0 a b c d z); auto.
  destruct x as [[[s p] q] r].
  decompose [and] y; clear y.
  assert (Hs : finMap s).
  destruct Ha.
  exists x.
  intros.
  spec H1 a0.
  rewrite e in H1; auto. inv H1; auto.
  assert (Hq : finMap q).
  destruct Hb.
  exists x.
  intros.
  spec H3 a0. inv H3; auto. rewrite H9; rewrite e; auto.
  rewrite e in H8; auto. inv H8.
  assert (Hr : finMap r).
  destruct Hb.
  exists x.
  intros.
  spec H3 a0.
  rewrite e in H3; auto. inv H3; auto.
  assert (Hp : finMap p).
  destruct Hd.
  exists x. intros. spec H5 a0. rewrite e in H5; auto. inv H5; auto.
  exists (exist _ s Hs, exist _ p Hp, exist _ q Hq, exist _ r Hr).
  simpl; intuition.
Qed.

Lemma Cross_fpm (A B: Type){JB: Join B} {PB: Perm_alg B}{PosB : Pos_alg B}
  {CrB: Cross_alg B}:   Cross_alg (fpm A B) .
 (* Warning: This lemma is valid, but it's not clear that it's useful *)
Proof.
  intros.
  assert (Cross_alg (A -> option B)).
  apply cross_split_fun.
  unfold Cross_alg.
  destruct a as [a |]. destruct b as [b|]. destruct c as [c|]. destruct d as [d|].
  destruct z as [z|].
  intros.
  hnf in H. 
  assert (join a b z) by (clear - H; inv H; auto).
  assert (join c d z) by (clear - H0; inv H0; auto).
  clear H H0.
  destruct (CrB _ _ _ _ _ H1 H2) as [[[[s p] q] r] [? [? [? ?]]]].
  exists (Some s, Some p, Some q, Some r); repeat split; try constructor; auto.
  intros. elimtype False; inv H.
  intros. assert (z = Some c) by (clear - H0; inv H0; auto).
  subst. assert (join a b c) by   (clear - H; inv H; auto).
  exists (Some a, None, Some b, None); repeat split; try constructor; auto.
  intros.
  destruct d as [d|].
  assert (z=Some d) by (clear - H0; inv H0; auto). subst z.
  exists (None, Some a, None, Some b); repeat split; try constructor; auto.
  clear - H; inv H; auto.
  elimtype False; inv H0; inv H.
  destruct c as [c|]. destruct d as [d|].
  intros.
  assert (z = Some a) by (clear - H; inv H; auto). subst z.
  exists (Some c, Some d, None, None); repeat split; try constructor; eauto.
  inv H0; auto.
  intros. assert (z = Some a) by (clear - H; inv H; auto). subst.
  assert (a=c) by (clear - H0; inv H0; auto). subst c.
  exists (Some a, None, None, None); repeat split; try constructor; auto.
  intros.
  assert (z=d) by (clear - H0; inv H0; auto). subst d. 
  assert (z = Some a) by (inv H; auto).
  subst.
  exists (None, Some a, None, None); repeat split; try constructor; auto.
  destruct b as [b|]. destruct c as [c|]. destruct d as [d|].
  intros.
  assert (z=Some b) by (inv H; auto). subst.
  exists (None, None, Some c, Some d); repeat split; try constructor; auto.
  inv H0; auto.
  intros.
  assert (z = Some b) by (inv H; auto); subst.
  assert (c=b) by (inv H0; auto); subst.
  exists (None, None, Some b, None); repeat split; try constructor; auto.
  intros.
  assert (z=d) by (clear - H0; inv H0; auto). subst d.
  assert (z=Some b) by (inv H; auto). subst.
  exists (None, None, None, Some b); repeat split; try constructor; auto.
  intros. assert (z=None) by (inv H; auto).
  subst.
  exists (None, None, None, None).
  inv H0; repeat split; constructor.

  intros [a Ha] [b Hb] [c Hc] [d Hd] [z Hz].
  simpl; intros.
  unfold Cross_alg in X.
  destruct (X (fun x => a x) b c d z); auto.
  destruct x as [[[s p] q] r].
  decompose [and] y; clear y.
  assert (Hs : finMap s).
  destruct Ha.
  exists x.
  intros.
  spec H1 a0.
  rewrite e in H1; auto. inv H1; auto.
  assert (Hq : finMap q).
  destruct Hb.
  exists x.
  intros.
  spec H3 a0. inv H3; auto. rewrite H9; rewrite e; auto.
  rewrite e in H8; auto. inv H8.
  assert (Hr : finMap r).
  destruct Hb.
  exists x.
  intros.
  spec H3 a0.
  rewrite e in H3; auto. inv H3; auto.
  assert (Hp : finMap p).
  destruct Hd.
  exists x. intros. spec H5 a0. rewrite e in H5; auto. inv H5; auto.
  exists (exist _ s Hs, exist _ p Hp, exist _ q Hq, exist _ r Hr).
  simpl; intuition.
Qed.

Definition opposite_bij {A B} (b: bijection A B) : bijection B A :=
 Bijection _ _ (bij_g _ _ b) (bij_f _ _ b) (bij_gf _ _ b) (bij_fg _ _ b).

Lemma Cross_bij' : forall A B JA JB bij,
  @Cross_alg B JB ->
   JB =  (Join_bij A JA B bij) ->
  @Cross_alg A  JA.
Proof.
  repeat intro. subst. unfold join, Join_bij in *.
  destruct bij. simpl in *.
  destruct (X (bij_f a) (bij_f b) (bij_f c) (bij_f d) (bij_f z)).
  red. repeat rewrite bij_gf; auto.
  red. repeat rewrite bij_gf; auto.
  destruct x as [[[s p] q] r].
  exists (bij_g s,bij_g p,bij_g q,bij_g r).
  unfold join in y.
  repeat rewrite bij_gf in y.
  auto.
Qed.

Definition option_bij {A B} (D: bijection A B) : bijection (option A) (option B).
 apply
 (Bijection (option A) (option B)
    (fun a => match a with Some a' => Some (bij_f _ _ D a') | None => None end)
    (fun b => match b with Some b' => Some (bij_g _ _ D b') | None => None end)).
 intros. destruct x; simpl; auto. rewrite bij_fg. auto.
 intros. destruct x; simpl; auto. rewrite bij_gf. auto.
Defined.
