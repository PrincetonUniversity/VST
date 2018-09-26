Require Export VST.veric.Clight_base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.
Require Import VST.veric.shares.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.

Definition GHOSTspec (A: Type) (x: A) : spec :=
  fun sh loc =>
   allp (jam (eq_dec loc) (fun loc' => 
    yesat (SomeP (ConstType (A -> Prop)) (fun _ y => y = x)) 
             (FUN (nil,Tvoid) cc_default) sh loc') noat).

Definition ghostp {A: Type} (sh: share) (loc: address) (x: A) : mpred :=
  GHOSTspec A x sh loc.


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
(*rewrite H3 in H. rewrite H4 in H. *)
assert (SomeP (ConstType (A -> Prop))
            (fun (_ : list Type) (y : A) => y = x1) =
          SomeP (ConstType (A -> Prop))
            (fun (_ : list Type) (y : A) => y = x2))%pred.
clear - H.
match goal with |- ?B = ?C => forget B as b; forget C as c end.
inversion H; auto.
clear H.
apply SomeP_inj in H2.
pose proof (@equal_f A Prop _ _ (@equal_f (list Type) (A->Prop) _ _ H2 nil) x1).
simpl in H.
rewrite <- H; auto.
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
assert (SomeP (ConstType (A -> Prop))
            (fun (_ : list Type) (y : A) => y = x1) =
          SomeP (ConstType (A -> Prop))
            (fun (_ : list Type) (y : A) => y = x2))%pred.
clear - H1.
match goal with |- ?B = ?C => forget B as b; forget C as c end.
inversion H1; auto.
clear - H.
apply SomeP_inj in H.
pose proof (@equal_f A Prop _ _ (@equal_f (list Type) (A->Prop) _ _ H nil) x1).
rewrite <- H0; auto.
Qed.


Definition make_GHOSTspec:
  forall A (sh : share) (rsh: readable_share sh) loc (x: A) (lev: nat),
   exists m: rmap, GHOSTspec A x sh loc m /\ level m =  lev.
Proof.
 intros.
unfold GHOSTspec.
 assert (AV.valid (res_option oo 
  (fun l => if eq_dec l loc 
   then YES sh rsh (FUN(nil,Tvoid) cc_default)
             (SomeP (ConstType (A -> Prop)) 
                  (fun _ y => (y = x)))
   else NO Share.bot bot_unreadable))).
 intros b ofs.
 unfold res_option, compose.
 if_tac; auto.
 destruct (make_rmap _ H lev) as [phi [? ?]].
 extensionality l.
 unfold compose, resource_fmap; simpl.
 if_tac; auto.
 exists phi.
 split; auto.
 hnf.
 intro l.
 hnf.
 if_tac.
 subst l.
 hnf. exists rsh.
 hnf.
 rewrite H1. rewrite if_true. f_equal. 
 auto.
 do 3 red. rewrite H1.
 rewrite if_false by auto.
 apply NO_identity.
Qed.


Lemma make_ghostp:
  forall A (x: A)  loc (lev: nat),
  exists m : rmap, ghostp Share.top loc x m /\ level m = lev.
Proof.
intros.
unfold ghostp.
destruct (make_GHOSTspec A Share.top readable_share_top loc x lev) as [m [? ?]].
exists m; split; auto.
Qed.

