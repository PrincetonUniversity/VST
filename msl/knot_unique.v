(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.knot.
Require Import VST.msl.knot_lemmas.
Require Import VST.msl.functors.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

Local Open Scope nat_scope.

Definition map_pair {A B C D} (f:A -> B) (g:C -> D) (x:A * C) : B * D :=
  (f (fst x), g (snd x)).

Module Type ISOMORPHIC_KNOTS.
  Declare Module TF : TY_FUNCTOR.
  Declare Module K1 : KNOT with Module TF := TF.
  Declare Module K2 : KNOT with Module TF := TF.
  Import TF.

  Parameter f : K1.knot -> K2.knot.
  Parameter g : K2.knot -> K1.knot.

  Definition fF : F K1.predicate -> F K2.predicate :=
    fmap F (fun p : K1.knot * other -> K1.TF.T => p oo map_pair g (@id other)).

  Definition gF : F K2.predicate -> F K1.predicate :=
    fmap F (fun p : K2.knot * other -> K2.TF.T => p oo map_pair f (@id other)).

  Axiom iso1 : f oo g = id K2.knot.
  Axiom iso2 : g oo f = id K1.knot.

  Axiom f_squash : forall n F1,
    f (K1.squash (n, F1)) = K2.squash (n, fF F1).

  Axiom g_squash : forall n F2,
    g (K2.squash (n, F2)) = K1.squash (n, gF F2).

  Axiom f_unsquash : forall k1 U1,
    U1 = K1.unsquash k1 ->
    K2.unsquash (f k1) = (fst U1, fF (snd U1)).

  Axiom g_unsquash : forall k2 U2,
    U2 = K2.unsquash k2 ->
    K1.unsquash (g k2) = (fst U2, gF (snd U2)).

End ISOMORPHIC_KNOTS.

Module Unique_Knot (TF' : TY_FUNCTOR)
                                (K1' : KNOT with Module TF := TF')
                                (K2' : KNOT with Module TF := TF') :
                                  ISOMORPHIC_KNOTS
                                    with Module TF := TF'
                                    with Module K1 := K1'
                                    with Module K2 := K2'.
Module TF := TF'.
Import TF.
Module K1 := K1'.
Module K2 := K2'.
Module K1L := Knot_Lemmas K1.
Module K2L := Knot_Lemmas K2.

Section Common.
Variable f : K1.knot -> K2.knot.
Variable g : K2.knot -> K1.knot.

Definition f_pred' (p1 : K1.predicate) : K2.predicate :=
  p1 oo map_pair g (@id other).

Definition g_pred' (p2 : K2.predicate) : K1.predicate :=
  p2 oo map_pair f (@id other).

Variable f_level : forall k, level k = level (f k).
Variable g_level : forall k, level k = level (g k).

Lemma f_pred'_approx: forall n,
f_pred' oo K1.approx n = K2.approx n oo f_pred'.
Proof.
intros.
extensionality P1 k2.
destruct k2; unfold f_pred', compose; simpl.
unfold K1'.approx, K2'.approx; simpl.
rewrite g_level; simpl; auto.
Qed.

Lemma g_pred'_approx : forall n,
g_pred' oo K2.approx n = K1.approx n oo g_pred'.
Proof.
intros.
extensionality P k1.
destruct k1; unfold g_pred', compose; simpl.
unfold K1'.approx, K2'.approx; simpl.
rewrite f_level; simpl; auto.
Qed.

Definition f_F' : TF.F K1.predicate -> TF.F K2.predicate :=
  fmap F f_pred'.

Definition g_F' : TF.F K2.predicate -> TF.F K1.predicate :=
  fmap F g_pred'.

End Common.

Section Z.
(* The base case.  To keep things simple, we will put definitions first. *)

Definition fZ_pred (p2 : K2.predicate) : K1.predicate :=
fun k1 => T_bot.

Definition gZ_pred (p1 : K1.predicate) : K2.predicate :=
fun k2 => T_bot.

Definition fF_Z : TF.F K1.predicate -> TF.F K2.predicate :=
  fmap F gZ_pred.

Definition gF_Z : TF.F K2.predicate -> TF.F K1.predicate :=
  fmap F fZ_pred.

Definition f_Z (k1 : K1.knot) : K2.knot :=
  match K1.unsquash k1 with
    (n, F_p1) => K2.squash (n, fF_Z F_p1)
  end.

Definition g_Z (k2 : K2.knot) : K1.knot :=
  match K2.unsquash k2 with
    (n, F_p2) => K1.squash (n, gF_Z F_p2)
  end.

(* Now the lemmas *)
Lemma predZ_iso1: fZ_pred oo K2.approx 0 oo gZ_pred = K1.approx 0.
Proof.
intros.
extensionality p k.
unfold compose, gZ_pred, fZ_pred, K1'.approx in *.
destruct k; simpl; auto.
Qed.

Lemma predZ_iso2: gZ_pred oo K1.approx 0 oo fZ_pred = K2.approx 0.
Proof.
intros.
extensionality p k.
unfold compose, gZ_pred, fZ_pred, K2'.approx in *.
destruct k; simpl; auto.
Qed.

Lemma iso1_Z : forall k, level k <= 0 -> (g_Z oo f_Z) k = k.
Proof.
intros.
unfold compose, g_Z, f_Z.
remember (K1.unsquash k) as unsq_k.
destruct unsq_k as [n0 Fp].
rewrite K2.unsquash_squash.
rewrite K1.knot_level in H.
rewrite <- Hequnsq_k in H.
simpl in H.
replace (fmap F (K2.approx n0) (fF_Z Fp)) with
  ((fmap F (K2.approx n0) oo (fmap F gZ_pred)) Fp) by trivial.
rewrite fmap_comp.
replace (gF_Z (fmap F (K2.approx n0 oo gZ_pred) Fp)) with
  ((fmap F fZ_pred oo fmap F (K2.approx n0 oo gZ_pred)) Fp) by trivial.
rewrite fmap_comp.
assert (n0 = 0) by omega.
clear H; subst n0.
symmetry in Hequnsq_k.
rewrite predZ_iso1; trivial.
rewrite <- (K1L.unsquash_approx Hequnsq_k).
rewrite <- Hequnsq_k.
rewrite K1.squash_unsquash.
trivial.
Qed.

Lemma iso2_Z : forall k, level k <= 0 -> (f_Z oo g_Z) k = k.
Proof.
intros.
unfold compose, g_Z, f_Z.
remember (K2.unsquash k) as unsq_k.
destruct unsq_k as [n0 Fp].
rewrite K1.unsquash_squash.
rewrite K2.knot_level in H.
replace (fmap F (K1.approx n0) (gF_Z Fp)) with
  ((fmap F (K1.approx n0) oo (fmap F fZ_pred)) Fp) by trivial.
rewrite fmap_comp.
replace (fF_Z (fmap F (K1.approx n0 oo fZ_pred) Fp)) with
  ((fmap F gZ_pred oo fmap F (K1.approx n0 oo fZ_pred)) Fp) by trivial.
rewrite fmap_comp.
symmetry in Hequnsq_k.
assert (n0 = 0).
destruct (K2'.unsquash k); inv Hequnsq_k.
simpl in H.
omega.
subst n0.
rewrite predZ_iso2; trivial.
rewrite <- (K2L.unsquash_approx Hequnsq_k).
rewrite <- Hequnsq_k.
rewrite K2.squash_unsquash.
trivial.
Qed.

(* We must also prove that f_Sn and g_Sn preserve the level property. *)
Lemma f_level_Z: forall k, level k = level (f_Z k).
Proof.
intro.
unfold f_Z.
rewrite K1.knot_level, K2.knot_level.
remember (K1.unsquash k) as uk.
destruct uk.
rewrite K2.unsquash_squash.
trivial.
Qed.

Lemma g_level_Z: forall k, level k = level (g_Z k).
Proof.
intro.
unfold g_Z.
simpl.
rewrite K1.knot_level, K2.knot_level.
remember (K2.unsquash k) as uk.
destruct uk.
rewrite K1.unsquash_squash.
trivial.
Qed.

(* Finally, we must show that fZ preserves unsquashing. *)
Lemma fZ_unsquash : forall k1,
  level k1 <= 0 ->
  forall U1,
  U1 = K1.unsquash k1 ->
  K2.unsquash (f_Z k1) = (fst U1, fF_Z (snd U1)).
Proof.
intros.
unfold fF_Z, f_Z.
destruct U1 as [n F1].
simpl.
rewrite <- H0.
rewrite K2.unsquash_squash.
replace (fmap F (K2.approx n) (fF_Z F1)) with
 ((fmap F (K2.approx n) oo fmap F gZ_pred) F1) by trivial.
rewrite fmap_comp.
assert (K2'.approx n oo gZ_pred = gZ_pred).
extensionality P1 k2.
destruct k2.
unfold gZ_pred, compose, K2'.approx; simpl.
destruct (le_gt_dec n (level k)); auto.
congruence.
Qed.

End Z.

Section Sn.
(* The inductive step.  To keep things simple, we will put definitions first. *)
Variable f : K1.knot -> K2.knot.
Variable g : K2.knot -> K1.knot.


Definition f_Sn (k1 : K1.knot) : K2.knot :=
  match K1.unsquash k1 with
    (n, F_p1) => K2.squash (n, f_F' g F_p1)
  end.

Definition g_Sn (k2 : K2.knot) : K1.knot :=
  match K2.unsquash k2 with
    (n, F_p2) => K1.squash (n, g_F' f F_p2)
  end.


(* Now we include details relevant to the proof of the inductive step. *)

Variable n : nat.
Variable iso1 : forall k, level k <= n -> (g oo f) k = k.
Variable iso2 : forall k, level k <= n -> (f oo g) k = k.

(* These two properties are enough to prove a bijection up to level k *)

Lemma f_inj : forall ka kb,
  level ka <= n ->
  level kb <= n ->
  f ka = f kb ->
  ka = kb.
Proof.
intros.
assert ((g oo f) ka = (g oo f) kb) by (unfold compose; rewrite H1; trivial).
do 2 rewrite iso1 in H2; trivial.
Qed.

Lemma g_inj : forall ka kb,
  level ka <= n ->
  level kb <= n ->
  g ka = g kb ->
  ka = kb.
Proof.
intros.
assert ((f oo g) ka = (f oo g) kb) by (unfold compose; rewrite H1; trivial).
do 2 rewrite iso2 in H2; trivial.
Qed.

Lemma f_surj : forall k2,
  level k2 <= n ->
  exists k1,
  f k1 = k2.
Proof.
intros.
exists (g k2).
rewrite <- iso2; trivial.
Qed.

Lemma g_surj : forall k1,
  level k1 <= n ->
  exists k2,
  g k2 = k1.
Proof.
intros.
exists (f k1).
rewrite <- iso1; trivial.
Qed.

(* Now we show that k1_pred and k2_pred are the identity under approximation. *)
(* Not clear that we need this. *)
(*
Lemma k1_pred_iso: K1.approx (n+1) oo k1_pred = K1.approx (n+1).
Proof.
intros.
extensionality p k.
unfold k1_pred, compose, g_pred, f_pred in *.
apply prop_ext; split; do 2 intro; spec H H0; rewrite iso1 in *; trivial; omega.
Qed.

Lemma k2_pred_iso: K2.approx (n+1) oo k2_pred = K2.approx (n+1).
Proof.
intros.
extensionality p k.
unfold k2_pred, compose, g_pred, f_pred in *.
apply prop_ext; split; do 2 intro; spec H H0; rewrite iso2 in *; trivial; omega.
Qed.
*)

(*
What we would like to show next is that f and g preserve the level of the knot,
even in their (unfortunately non-unique over level n) inverses.
Unfortunately, this is not possible:

Lemma f_level: forall k, K1.level k = K2.level (f k).

This is clearly impossible since we don't know anything about the behavior of f
for knots above level n.

Actually, even this weaker version is not provable:

Lemma f_level: forall k,
(K1.level k <= n \/ K2.level (f k) <= n) ->
K1.level k = K2.level (f k).

Counterexample: K1.knot = K2.knot = nat;
                            K1.level = K2.level = id;
                            f = inc, g = dec;
*)

(* So we must assert them as axioms, which means a bigger induction *)
Variable f_level: forall k, level k = level (f k).
Variable g_level: forall k, level k = level (g k).

(* However, using them we can prove pred_iso1 and pred_iso2, which are vital. *)
Lemma predn_iso1: forall m,
  m <= (n+1) ->
  g_pred' f oo K2.approx m oo f_pred' g = K1.approx m.
Proof.
intros.
extensionality p k.
unfold g_pred', f_pred', compose in *.
destruct k.
unfold K2'.approx, map_pair, id; simpl.
unfold K1'.approx; simpl.
rewrite <- f_level.
simpl.
destruct (le_gt_dec m (level k)); auto.
rewrite iso1; auto.
simpl; omega.
Qed.

Lemma predn_iso2: forall m,
  m <= (n+1) ->
  f_pred' g oo K1.approx m oo g_pred' f = K2.approx m.
Proof.
intros.
extensionality p k.
unfold g_pred', f_pred', compose in *.
destruct k.
unfold K1'.approx, map_pair, id; simpl.
unfold K2'.approx; simpl.
rewrite <- g_level.
simpl.
destruct (le_gt_dec m (level k)); auto.
rewrite iso2; auto.
simpl; omega.
Qed.

(* Now we can prove that f_Sn and g_Sn preserve the isomorphism. *)
Lemma iso1_Sn : forall k, level k <= n + 1 -> (g_Sn oo f_Sn) k = k.
Proof.
intros.
unfold compose, g_Sn, f_Sn.
remember (K1.unsquash k) as unsq_k.
destruct unsq_k as [n0 Fp].
rewrite K2.unsquash_squash.
rewrite K1.knot_level in H.
rewrite <- Hequnsq_k in H.
simpl in H.
replace (fmap F (K2.approx n0) (f_F' g Fp)) with
  ((fmap F (K2.approx n0) oo (fmap F (f_pred' g))) Fp) by trivial.
rewrite fmap_comp.
replace (g_F' f (fmap F (K2.approx n0 oo f_pred' g) Fp)) with
  ((fmap F (g_pred' f) oo fmap F (K2.approx n0 oo f_pred' g)) Fp) by trivial.
rewrite fmap_comp.
symmetry in Hequnsq_k.
rewrite predn_iso1; trivial.
rewrite <- (K1L.unsquash_approx Hequnsq_k).
rewrite <- Hequnsq_k.
rewrite K1.squash_unsquash.
trivial.
Qed.

Lemma iso2_Sn : forall k, level k <= n + 1 -> (f_Sn oo g_Sn) k = k.
Proof.
intros.
unfold compose, g_Sn, f_Sn.
remember (K2.unsquash k) as unsq_k.
destruct unsq_k as [n0 Fp].
rewrite K1.unsquash_squash.
simpl in H.
rewrite K2.knot_level in H.
rewrite <- Hequnsq_k in H.
simpl in H.
replace (fmap F (K1.approx n0) (g_F' f Fp)) with
  ((fmap F (K1.approx n0) oo (fmap F (g_pred' f))) Fp) by trivial.
rewrite fmap_comp.
replace (f_F' g (fmap F (K1.approx n0 oo g_pred' f) Fp)) with
  ((fmap F (f_pred' g) oo fmap F (K1.approx n0 oo g_pred' f)) Fp) by trivial.
rewrite fmap_comp.
symmetry in Hequnsq_k.
rewrite predn_iso2; trivial.
rewrite <- (K2L.unsquash_approx Hequnsq_k).
rewrite <- Hequnsq_k.
rewrite K2.squash_unsquash.
trivial.
Qed.

(* We must also prove that f_Sn and g_Sn preserve the level property. *)
Lemma f_level_Sn: forall k, level k = level (f_Sn k).
Proof.
intro.
unfold f_Sn.
rewrite K1.knot_level, K2.knot_level.
remember (K1.unsquash k) as uk.
destruct uk.
rewrite K2.unsquash_squash.
trivial.
Qed.

Lemma g_level_Sn: forall k, level k = level (g_Sn k).
Proof.
intro.
unfold g_Sn.
rewrite K1.knot_level, K2.knot_level.
remember (K2.unsquash k) as uk.
destruct uk.
rewrite K1.unsquash_squash.
trivial.
Qed.

(* Finally, we must show that f_Sn preserves unsquashing. *)
Variable fn_unsquash : forall k1,
  level k1 <= n ->
  forall U1,
  U1 = K1.unsquash k1 ->
  K2.unsquash (f k1) = (fst U1, f_F' g (snd U1)).

Lemma Fn_iso2 : forall m,
  m <= n + 1 ->
  g_F' f oo f_F' g oo fmap F (K1.approx m) = fmap F (K1.approx m).
Proof.
intros.
unfold g_F', f_F'.
do 2 rewrite fmap_comp.
replace (g_pred' f oo f_pred' g oo K1.approx m) with (K1.approx m); trivial.
rewrite f_pred'_approx; trivial.
rewrite predn_iso1; trivial.
Qed.

Lemma gn_unsquash : forall k2,
  level k2 <= n ->
  forall U2,
  U2 = K2.unsquash k2 ->
  K1.unsquash (g k2) = (fst U2, g_F' f (snd U2)).
Proof.
intros.
destruct U2 as [m F2].
simpl.
generalize (fn_unsquash (g k2)); intro.
rewrite <- g_level in H1.
remember (g k2) as k1.
specialize ( H1 H (K1.unsquash k1)).
firstorder.
assert (f k1 = (f oo g) k2) by (unfold compose; congruence).
rewrite iso2 in H2; trivial.
rewrite H2 in H1.
rewrite <- H0 in H1.
inversion H1.
apply injective_projections; simpl; trivial.
remember (K1.unsquash k1) as U1.
replace (g_F' f (f_F' g (snd U1))) with ((g_F' f oo f_F' g) (snd U1)) by trivial.
destruct U1 as [m' F1].
simpl in *.
subst m'.
clear H1.
symmetry in HeqU1.
generalize (K1L.unsquash_approx HeqU1); intro.
rewrite H1.
replace ((g_F' f oo f_F' g) (fmap F (K1'.approx m) F1)) with
  ((g_F' f oo f_F' g oo fmap F (K1.approx m)) F1) by trivial.
rewrite Fn_iso2.
trivial.
simpl in H.
rewrite K2.knot_level in H.
rewrite <- H0 in H.
simpl in H.
omega.
Qed.

Lemma gn_squash : forall m F2,
  m <= n ->
  g (K2.squash (m, F2)) = K1.squash (m, g_F' f F2).
Proof.
intros.
apply (K1L.unsquash_inj).
assert (level (K2.squash (m , F2)) <= n) by
  (simpl; rewrite K2.knot_level; rewrite K2.unsquash_squash; simpl; trivial).
rewrite (gn_unsquash (K2'.squash (m, F2)) H0 (K2.unsquash (K2'.squash (m, F2)))); trivial.
rewrite K1.unsquash_squash.
rewrite K2.unsquash_squash.
simpl.
replace (g_F' f (fmap F (K2'.approx m) F2)) with
  ((fmap F (g_pred' f) oo (fmap F (K2.approx m))) F2) by trivial.
replace (m, fmap F (K1'.approx m) (g_F' f F2)) with
  (m, (fmap F (K1.approx m) oo fmap F (g_pred' f)) F2) by trivial.
do 2 rewrite fmap_comp.
apply injective_projections; simpl; trivial.
rewrite g_pred'_approx; trivial.
Qed.

Lemma fSn_unsquash : forall k1,
  level k1 <= n + 1 ->
  forall U1,
  U1 = K1.unsquash k1 ->
  K2.unsquash (f_Sn k1) = (fst U1, f_F' (g_Sn) (snd U1)).
Proof.
intros.
unfold f_Sn.
rewrite <- H0.
destruct U1 as [m F1].
simpl.
rewrite K2.unsquash_squash.
apply injective_projections; simpl; trivial.
unfold f_F'.
replace (fmap F (K2'.approx m) (fmap F (f_pred' g) F1)) with
  ((fmap F (K2.approx m) oo fmap F  (f_pred' g)) F1) by trivial.
rewrite fmap_comp.
simpl in H.
rewrite K1.knot_level in H.
rewrite <- H0 in H.
simpl in H.
symmetry in H0.
generalize (K1L.unsquash_approx H0); intro.
pattern F1 at 2.
rewrite H1.
replace (fmap F (f_pred' g_Sn) (fmap F (K1'.approx m) F1)) with
  ((fmap F (f_pred' g_Sn) oo fmap F (K1.approx m)) F1) by trivial.
rewrite fmap_comp.
assert (K2'.approx m oo f_pred' g = f_pred' g_Sn oo K1.approx m); try congruence.
extensionality p1 k2.
destruct k2.
simpl; unfold f_pred', compose, K1.approx, K2.approx, g_Sn; simpl.
rewrite K1.knot_level, K2'.knot_level; unfold g_Sn; simpl.
unfold map_pair; simpl.
remember (K2.unsquash k) as uk2.
destruct uk2 as [m' F2].
rewrite K1.unsquash_squash.
simpl.
destruct (le_gt_dec m m'); auto.
unfold id.
rewrite <- gn_squash in *; [ | omega ].
rewrite Hequk2.
rewrite K2.squash_unsquash; trivial.
Qed.

Lemma gn_gSn_eq_n : forall k,
level k <= n ->
g k = g_Sn k.
Proof.
intros.
unfold g_Sn.
remember (K2.unsquash k) as usqk.
destruct usqk.
simpl in H.
rewrite K2.knot_level in H.
rewrite <- Hequsqk in H.
simpl in H.
rewrite <- gn_squash; try omega.
rewrite Hequsqk.
rewrite K2.squash_unsquash.
trivial.
Qed.

End Sn.

Section FG.
(* We tie it together *)

Fixpoint fg (n : nat) {struct n} : ((K1.knot -> K2.knot) * (K2.knot -> K1.knot)) :=
  match n with
   | 0 => (f_Z, g_Z)
   | S n => match fg n with (fn, gn) => (f_Sn gn, g_Sn fn) end
  end.

Lemma fg_level_fst : forall n k, level k = level (fst (fg n) k).
Proof.
intros.
destruct n.
apply f_level_Z.
unfold fg.
fold fg.
destruct (fg n).
apply f_level_Sn.
Qed.

Lemma fg_level_snd : forall n k, level k = level (snd (fg n) k).
Proof.
intros.
destruct n.
apply g_level_Z.
unfold fg.
fold fg.
destruct (fg n).
apply g_level_Sn.
Qed.

Lemma fg_id : forall n k, level k <= n -> (fst (fg n) oo snd (fg n)) k  = k.
Proof.
induction n.
unfold fg.
simpl.
intros.
rewrite iso2_Z; trivial.
unfold fg.
fold fg.
remember (fg n) as fgn.
destruct fgn as [fn gn].
simpl in *.
intros.
rewrite (iso2_Sn fn gn n); trivial; try omega.
intros.
destruct n.
unfold fg in Heqfgn.
inversion Heqfgn.
apply g_level_Z.
unfold fg in Heqfgn.
fold fg in Heqfgn.
destruct (fg n).
inversion Heqfgn.
apply g_level_Sn.
Qed.

Lemma gf_id : forall n k, level k <= n -> (snd (fg n) oo fst (fg n)) k  = k.
Proof.
induction n.
unfold fg.
simpl.
intros.
rewrite iso1_Z; trivial.
unfold fg.
fold fg.
remember (fg n) as fgn.
destruct fgn as [fn gn].
simpl in *.
intros.
rewrite (iso1_Sn fn gn n); trivial; try omega.
intros.
destruct n.
unfold fg in Heqfgn.
inversion Heqfgn.
apply f_level_Z.
unfold fg in Heqfgn.
fold fg in Heqfgn.
destruct (fg n).
inversion Heqfgn.
apply f_level_Sn.
Qed.

Lemma fg_fst_unsquash: forall n k, level k <= n ->
  forall U1,
  U1 = K1.unsquash k ->
  K2.unsquash (fst (fg n) k) = (fst U1, f_F' (snd (fg n)) (snd U1)).
Proof.
induction n;
unfold fg;
fold fg;
simpl;
intros.
rewrite (fZ_unsquash k H U1 H0).
(* Move up? *)
apply injective_projections; simpl; trivial.
unfold f_F', fF_Z.
destruct U1 as [m F1].
simpl.
simpl in H; rewrite K1.knot_level in H.
rewrite <- H0 in H.
simpl in H.
assert (m = 0) by omega.
subst m.
clear H.
symmetry in H0.
generalize (K1L.unsquash_approx H0); intro.
pattern F1 at 2.
rewrite H.
replace (fmap F (f_pred' g_Z) (fmap F (K1'.approx 0) F1)) with
  ((fmap F (f_pred' g_Z) oo fmap F (K1.approx 0)) F1) by trivial.
rewrite fmap_comp.
replace (f_pred' g_Z oo K1'.approx 0) with gZ_pred; trivial.
(* End move up *)
remember (fg n) as fgn.
destruct fgn as [fn gn].
simpl in *.
replace gn with (snd (fg n)) by (rewrite <- Heqfgn; trivial).
generalize (fSn_unsquash (fst (fg n)) (snd (fg n)) n (gf_id n) (fg_id n) (fg_level_fst n) (fg_level_snd n)); intro.
rewrite <- Heqfgn in H1.
simpl in H1.
replace (n + 1) with (S n) in H1 by omega.
specialize ( H1 IHn k H U1 H0).
rewrite <- Heqfgn.
simpl.
rewrite H1.
trivial.
Qed.

Lemma fg_fg_eq: forall n k2,
level k2 < n ->
snd (fg (level k2)) k2 = snd (fg n) k2.
Proof.
intros.
assert (exists m, level k2 + m = n).
remember (level k2) as m.
clear -H.
induction n.
inversion H.
assert (m = n \/ m < n) by omega.
clear H.
destruct H0.
subst n.
exists 1.
omega.
destruct (IHn H) as [m0 ?].
rewrite <- H0.
exists (m0 + 1).
omega.
destruct H0 as [m ?].
clear H.
revert m H0.
induction n; intros.
replace (level k2) with 0 by omega; trivial.
destruct m.
replace (level k2 + 0) with (level k2) in H0 by trivial.
rewrite H0.
trivial.
specialize ( IHn m).
rewrite IHn; try omega.
unfold fg; fold fg.
remember (fg n) as fgn.
destruct fgn as [fn gn].
simpl.
generalize (gn_gSn_eq_n (fst (fg n)) (snd (fg n)) n (gf_id n) (fg_id n) (fg_level_fst n) (fg_level_snd n) (fg_fst_unsquash n)); intro.
rewrite <- Heqfgn in H.
simpl in H.
apply H.
simpl in *.
omega.
Qed.

End FG.

(* Now for the main definitions and theorems *)

Definition f (k : K1.knot) : K2.knot := fst (fg (level k)) k.

Definition g (k : K2.knot) : K1.knot := snd (fg (level k)) k.

Definition fF : TF.F K1.predicate -> TF.F K2.predicate :=
  f_F' g.

Definition gF : TF.F K2.predicate -> TF.F K1.predicate :=
  g_F' f.

Lemma iso1 : f oo g = id K2.knot.
Proof.
extensionality k.
unfold id.
unfold compose, f, g.
rewrite <- fg_level_snd.
remember (level k) as n.
replace (fst (fg n) (snd (fg n) k)) with ((fst (fg n) oo snd (fg n)) k) by trivial.
rewrite fg_id; trivial; omega.
Qed.

Lemma iso2 : g oo f = id K1.knot.
Proof.
extensionality k.
unfold id.
unfold compose, f, g.
rewrite <- fg_level_fst.
remember (level k) as n.
replace (snd (fg n) (fst (fg n) k)) with ((snd (fg n) oo fst (fg n)) k) by trivial.
rewrite gf_id; trivial; omega.
Qed.

Lemma fpred_gpred : f_pred' g oo g_pred' f = id (K2.predicate).
Proof.
extensionality P2 k2.
unfold id.
unfold g_pred', f_pred', map_pair, compose; simpl.
destruct k2; simpl.
replace (f (g k)) with ((f oo g) k) by trivial.
rewrite iso1.
trivial.
Qed.

Lemma gpred_fpred : g_pred' f oo f_pred' g = id (K1.predicate).
Proof.
extensionality P1 k1.
unfold id.
unfold g_pred', f_pred', compose.
unfold map_pair; simpl.
destruct k1; simpl.
replace (g (f k)) with ((g oo f) k) by trivial.
rewrite iso2.
trivial.
Qed.

Lemma Fiso1 : fF oo gF = id (F K2.predicate).
Proof.
extensionality F2.
unfold id.
unfold fF, gF, f_F', g_F'.
rewrite fmap_comp.
rewrite fpred_gpred.
rewrite fmap_id.
trivial.
Qed.

Lemma Fiso2 : gF oo fF = id (F K1.predicate).
Proof.
extensionality F1.
unfold id.
unfold fF, gF, f_F', g_F'.
rewrite fmap_comp.
rewrite gpred_fpred.
rewrite fmap_id.
trivial.
Qed.

Lemma f_level : forall k, level k = level (f k).
Proof.
intros.
unfold f.
rewrite <- (fg_level_fst (level k)).
trivial.
Qed.

Lemma g_level : forall k, level k = level (g k).
Proof.
intros.
unfold g.
rewrite <- (fg_level_snd (level k)).
trivial.
Qed.

Lemma f_unsquash : forall k1 U1,
  U1 = K1.unsquash k1 ->
  K2.unsquash (f k1) = (fst U1, fF (snd U1)).
Proof.
intros.
destruct U1 as [n F1].
simpl.
unfold f; simpl; rewrite K1.knot_level.
rewrite <- H.
simpl.
assert (level k1 <= n) by (rewrite K1.knot_level; rewrite <- H; trivial).
rewrite (fg_fst_unsquash n k1 H0 (n, F1)); trivial.
simpl.
apply injective_projections; simpl; trivial.
unfold fF.
symmetry in H.
generalize (K1L.unsquash_approx H); intro.
rewrite H1.
unfold f_F'.
replace (fmap F (f_pred' (snd (fg n))) (fmap F (K1'.approx n) F1)) with
  ((fmap F (f_pred' (snd (fg n))) oo fmap F (K1.approx n)) F1) by trivial.
replace (fmap F (f_pred' g) (fmap F (K1'.approx n) F1)) with
  ((fmap F (f_pred' g) oo fmap F (K1.approx n)) F1) by trivial.
do 2 rewrite fmap_comp.
replace (f_pred' (snd (fg n)) oo K1.approx n) with (f_pred' g oo K1'.approx n); trivial.
extensionality P1 k2.
unfold f_pred', compose.
unfold K1.approx.
unfold map_pair; destruct k2; simpl.
rewrite <- fg_level_snd.
rewrite <- g_level.
simpl.
destruct (le_gt_dec n (level k)); auto.
unfold g.
red in g0.
rewrite (fg_fg_eq n k g0).
auto.
Qed.

Lemma g_unsquash : forall k2 U2,
  U2 = K2.unsquash k2 ->
  K1.unsquash (g k2) = (fst U2, gF (snd U2)).
Proof.
intros.
destruct U2 as [n F2].
simpl.
generalize (f_unsquash (g k2)); intro.
remember (g k2) as k1.
specialize ( H0 (K1.unsquash k1)).
firstorder.
assert (f k1 = (f oo g) k2) by (unfold compose; congruence).
rewrite iso1 in H1.
unfold id in H1.
rewrite H1 in H0.
rewrite <- H in H0.
inversion H0.
remember (K1.unsquash k1) as U1.
replace (gF (fF (snd U1))) with ((gF oo fF) (snd U1)) by trivial.
rewrite Fiso2.
unfold id.
destruct U1.
trivial.
Qed.


Lemma fF_approx : forall n,
fF oo (fmap F (K1.approx n)) = (fmap F (K2.approx n)) oo fF.
Proof.
intros.
unfold fF, f_F'.
do 2 rewrite fmap_comp.
rewrite f_pred'_approx.
trivial.
apply g_level.
Qed.

Lemma gF_approx : forall n,
gF oo (fmap F (K2.approx n)) = (fmap F (K1.approx n)) oo gF.
Proof.
intros.
unfold gF, g_F'.
do 2 rewrite fmap_comp.
rewrite g_pred'_approx.
trivial.
apply f_level.
Qed.

Lemma f_squash : forall n F1,
  f (K1.squash (n, F1)) = K2.squash (n, fF F1).
Proof.
intros.
apply (K2L.unsquash_inj).
rewrite (f_unsquash (K1'.squash (n, F1)) (K1.unsquash (K1'.squash (n, F1)))); trivial.
rewrite K1.unsquash_squash.
rewrite K2.unsquash_squash.
simpl.
replace (fF (fmap F (K1'.approx n) F1)) with
  ((fF oo (fmap F (K1.approx n))) F1) by trivial.
rewrite fF_approx.
trivial.
Qed.

Lemma g_squash : forall n F2,
  g (K2.squash (n, F2)) = K1.squash (n, gF F2).
Proof.
intros.
apply (K1L.unsquash_inj).
rewrite (g_unsquash (K2'.squash (n, F2)) (K2.unsquash (K2'.squash (n, F2)))); trivial.
rewrite K1.unsquash_squash.
rewrite K2.unsquash_squash.
simpl.
replace (gF (fmap F (K2'.approx n) F2)) with
  ((gF oo (fmap F (K2.approx n))) F2) by trivial.
rewrite gF_approx.
trivial.
Qed.

End Unique_Knot.
