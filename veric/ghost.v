Load loadpath.

Require Export veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.res_predicates.
Require Import veric.expr.

Definition GHOSTspec (A: Type) (x: A) : spec :=
  fun rsh sh loc =>
   allp (jam (eq_dec loc) (fun loc' => 
    yesat (SomeP (A::nil) (fun y: (A*unit) => prop(fst y = x))) 
             (FUN (nil,Tvoid)) rsh sh loc') noat).

Definition ghostp {A: Type} (sh: share) (loc: address) (x: A) : mpred :=
  GHOSTspec A x (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) loc.


Lemma ghostp_unique_sepcon:
    forall {A: Type} sh1 sh2 loc (x1 x2: A), 
     ghostp sh1 loc x1 * ghostp sh2 loc x2 |-- |> !! (x1=x2).
Proof.
intros.
unfold ghostp, GHOSTspec.
intros w [w1 [w2 [? [? ?]]]].
intros w' ?.
simpl in H2.
apply laterR_level in H2.
generalize (join_level _ _ _ H); intros [? ?].
destruct (level w). inv H2.
hnf.
rename H2 into Hw'.
specialize (H0 loc). specialize (H1 loc).
rewrite jam_true in H0 by auto.
rewrite jam_true in H1 by auto.
destruct H0 as [p ?]. destruct H1 as [p' ?].
hnf in H0,H1.
apply (resource_at_join _ _ _ loc) in H.
rewrite H0 in H; rewrite H1 in H.
simpl in H.
rewrite H3 in H. rewrite H4 in H.
assert (SomeP (A :: nil)
            (approx (S n) oo (fun y : A * unit => (!!(fst y = x1))%pred)) =
           SomeP (A :: nil)
            (approx (S n) oo (fun y : A * unit => (!!(fst y = x2))%pred))).
clear - H.
match goal with |- ?B = ?C => forget B as b; forget C as c end.
inversion H; auto.
clear H.
apply SomeP_inj in H2.
assert ((approx (S n) oo (fun y : A * unit => (!!(fst y = x1))%pred)) (x1,tt) w' =
     (approx (S n) oo (fun y : A * unit => (!!(fst y = x2))%pred)) (x1,tt) w').
rewrite H2; auto.
clear H2.
unfold approx, compose in H.
inv H.
assert  ((level w' < S n)%nat /\ x1 = x1) by (split; auto).
rewrite H5 in H.
destruct H; auto.
Qed.

Lemma ghostp_unique_andp:
    forall {A: Type} sh loc (x1 x2: A), 
     ghostp sh loc x1 && ghostp sh loc x2 |-- |> !! (x1=x2).
Proof.
intros.
unfold ghostp, GHOSTspec.
intros w [? ?].
rename H0 into H1; rename H into H0.
specialize (H0 loc). specialize (H1 loc).
rewrite jam_true in H0 by auto.
rewrite jam_true in H1 by auto.
destruct H0 as [p H0]. destruct H1 as [p' H1].
hnf in H0,H1.
rewrite H0 in H1.
simpl in H1.
intros w' H2.
simpl in H2.
apply laterR_level in H2.
destruct (level w). inv H2.
hnf.
rename H2 into Hw'.
assert (SomeP (A :: nil)
            (approx (S n) oo (fun y : A * unit => (!!(fst y = x1))%pred)) =
           SomeP (A :: nil)
            (approx (S n) oo (fun y : A * unit => (!!(fst y = x2))%pred))).
clear - H1.
match goal with |- ?B = ?C => forget B as b; forget C as c end.
inversion H1; auto.
clear H1.
apply SomeP_inj in H.
assert ((approx (S n) oo (fun y : A * unit => (!!(fst y = x1))%pred)) (x1,tt) w' =
     (approx (S n) oo (fun y : A * unit => (!!(fst y = x2))%pred)) (x1,tt) w').
rewrite H; auto.
clear H.
unfold approx, compose in H1.
inv H1.
assert  ((level w' < S n)%nat /\ x1 = x1) by (split; auto).
rewrite H2 in H.
destruct H; auto.
Qed.

Definition make_GHOSTspec:
  forall A (rsh : share) (sh: pshare) loc (x: A) (lev: nat),
   exists m: rmap, GHOSTspec A x rsh (pshare_sh sh) loc m /\ level m =  lev.
Proof.
 intros.
 assert (AV.valid (res_option oo 
  (fun l => if eq_dec l loc 
   then YES rsh sh  (FUN(nil,Tvoid))
             (SomeP (A::nil) (approx lev oo (fun y: (A*unit) => prop(fst y = x))))
   else NO Share.bot))).
 intros b ofs.
 unfold res_option, compose.
 if_tac; auto.
 destruct (make_rmap _ H lev) as [phi [? ?]].
 extensionality l.
 unfold compose, resource_fmap; simpl.
 if_tac; auto.
 simpl.
 f_equal. f_equal.
 extensionality a. unfold compose.
 change ((approx lev oo approx lev) (prop (fst a = x)) = approx lev (prop (fst a = x))).
 rewrite approx_oo_approx; auto.
 exists phi.
 split; auto.
 hnf.
 intro l.
 hnf.
 if_tac.
 subst l.
 hnf.
 exists (pshare_nonunit sh).
 hnf.
 rewrite H1. rewrite if_true. f_equal.
 destruct sh; simpl. apply exist_ext. auto.
 simpl. f_equal.
 rewrite H0; auto. auto.
 do 3 red; rewrite H1.
 rewrite if_false by auto.
 apply NO_identity.
Qed.


Lemma make_ghostp:
  forall A (x: A)  loc (lev: nat),
  exists m : rmap, ghostp Share.top loc x m /\ level m = lev.
Proof.
intros.
unfold ghostp.
destruct (make_GHOSTspec A  (Share.unrel Share.Lsh Share.top) pfullshare loc x lev) as [m [? ?]].
exists m; split; auto.
rewrite Share.contains_Rsh_e.
apply H.
apply top_correct'.
Qed.

