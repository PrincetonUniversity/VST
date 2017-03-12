Add LoadPath "../..".
Require Import msl.msl_standard.
Require Import language.

Definition world := (nat * ((var -> option adr)*(adr -> option adr)))%type.

Instance Join_world: Join world :=
  Join_prod nat (Join_equiv nat)
   _
   (Join_prod
     (var -> option adr) (Join_equiv _)
     (adr -> option adr) (Join_fun adr (option adr) (Join_lower (Join_discrete adr)))).

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Perm_alg world := _.
Instance Canc_world : Perm_alg world := _.
Instance Disj_world : Perm_alg world := _.

Definition age_world (w: world) : option world :=
 match fst w with S n => Some (n, snd w) | O => None end.

Definition level_world (w: world) : nat := fst w.

Lemma af_world: ageable_facts _ level_world age_world.
Proof.
 constructor.
 intros [n x]; exists (S n, x); simpl; auto.
 intros [n x]; unfold age_world; destruct n; simpl; intuition discriminate.
 intros. destruct x as [n x]; destruct n; inv H; simpl; auto.
Qed.

Instance ag_world: ageable world := mkAgeable _ _ _ af_world.
Instance Age_world : Age_alg world.
 constructor.
 intros [nx x] [ny y] [nz z] [nx' x'] [? ?] ?; simpl in *. destruct H; subst.
 unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
 destruct nz; inv H1. unfold age; simpl. unfold age_world; simpl.
 exists (nx', y); exists (nx', z); split; auto; split; auto.
 intros [nx x] [ny y] [nz z] [nz' z'] [? ?] ?; simpl in *. destruct H; subst.
 unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
 destruct nz; inv H1. unfold age; simpl. unfold age_world; simpl.
 exists (nz', x); exists (nz', y); split; auto; split; auto.
 intros [nx x] [nx' x'] [ny' y'] [nz' z'] [? ?] ?; simpl in *. destruct H; subst.
 unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
 destruct nx; inv H1. unfold age; simpl. unfold age_world; simpl.
 exists (S nz', y'); exists (S nz', z'); split; auto; split; auto.
 intros [nz z] [nx' x'] [ny' y'] [nz' z'] [? ?] ?; simpl in *. destruct H; subst.
 unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
 destruct nz; inv H1. unfold age; simpl. unfold age_world; simpl.
 exists (S nz', x'); exists (S nz', y'); split; auto; split; auto.
Qed.

Definition den (lev: nat) (s: state) : world := (lev, (table_get (fst s), table_get (snd s))).

Obligation Tactic := (try solve [repeat intro; match goal with H: age _ _ |- _ => inv H end]).

Program Definition defined (y: var) : pred world :=
   fun w => exists v, fst (snd w) y = Some v.
Next Obligation.
 intros. intro; intros.
 unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
 auto.
Qed.

Definition fun_set (f: nat -> option nat) (x: nat) (y: option nat) :=
   fun i => if eq_dec i x then y else f i.

Program Definition subst (x y: var) (P: pred world) : pred world :=
   fun w => P (fst w, (fun_set (fst (snd w)) x (fst (snd w) y), snd (snd w))).
Next Obligation.
 intros. intro; intros.
 unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
 simpl in *. eapply pred_hereditary; eauto.
  unfold age; simpl. unfold age_world; simpl. auto.
Qed.

Program Definition mapsto (x y: var) : pred world :=
 fun w =>
    exists ax, fst (snd w) x = Some ax /\
    exists ay, fst (snd w) y = Some ay /\
    forall a, if eq_dec a ax then snd (snd w) a = Some ay else snd (snd w) a = None.
Next Obligation.
 intros. intro; intros.
 unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
 simpl in *. auto.
Qed.

Program Definition equal (x y: var) : pred world :=
            fun w => fst (snd w) x = fst (snd w) y.
Next Obligation.
 intros. intro; intros.
 unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
 simpl in *. auto.
Qed.

Inductive modvars : command -> var -> Prop :=
| mod_assign: forall x y, modvars (Assign x y) x
| mod_load: forall x y, modvars (Load x y) x
| mod_seq1: forall x c1 c2, modvars c1 x -> modvars (Seq c1 c2) x
| mod_seq2: forall x c1 c2, modvars c2 x -> modvars (Seq c1 c2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall lev stk hp v, P (lev, (stk,hp)) -> P (lev, (fun_set stk x v, hp)).

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.

Inductive safeN: nat -> (list command * state) -> Prop :=
| safe0: forall cs, safeN 0 cs
| safe_step: forall n cs1 cs2, step' cs1 cs2 -> safeN n cs2 -> safeN (S n) cs1
| safe_halt: forall n s, safeN (S n) (nil, s).

Definition guards (P: pred world) (k: list command) : Prop :=
  forall lev s, P (den lev s) -> safeN lev (k,s).


Definition semax (P: pred world) (c: command) (Q: pred world) : Prop :=
  forall F, subset (modvars c) (nonfreevars F) ->
  forall k, guards (Q*F) k -> guards (P*F) (c :: k).

Lemma semax_assign: forall P x y,
      semax (defined y && subst x y P) (Assign x y) P.
Proof.
  intros P x y F H k H0 lev [stk hp] H1.
  destruct H1 as [[lev1 [stk1 hp1]] [[lev2 [stk2 hp2]] [? [[[v ?] ?] ?]]]].
  simpl in *.
  destruct lev; [apply safe0 | ].
  destruct H1 as [[? ?] [[? ?] ?]]; simpl in *; subst; auto.
  eapply safe_step.
  econstructor; eauto.
  apply H0.
  exists (lev,  (fun_set (table_get stk) x (table_get stk y), hp1)).
  exists (lev,  (fun_set (table_get stk) x (table_get stk y), hp2)).
  split; [|split].
  split; auto. split; auto.
  simpl. split; auto. extensionality i.
  unfold var, fun_set.
  destruct (eq_dec i x); auto.
  eapply pred_hereditary; [| eassumption ]; constructor.
  apply (H x).
  constructor.
  eapply pred_hereditary; [| eassumption ]; constructor.
Qed.

Lemma semax_load: forall x y z, x <> y -> x <> z ->
       semax (mapsto y z)  (Load x y) (mapsto y z && equal x z).
Proof.
  intros x y z Hxy Hxz F H k H0 lev [stk hp] H1.
 destruct H1 as [[lev1 [stk1 hp1]] [[lev2 [stk2 hp2]] [? [[ax [? [ay [? ?]]]] ?]]]].
 simpl in *.
 destruct H1 as [[? ?] [[? ?] ?]]; simpl in *; subst.
 destruct lev; [apply safe0 | ].
 eapply safe_step with  (k, (table_set x ay stk, hp)).
 econstructor; eauto.
 generalize (H4 ax); intros.
 destruct (eq_dec ax ax); [ | contradiction n; auto].
 generalize (H9 ax).  rewrite H1; intro. inv H6; auto.  destruct H11.
 apply H0.
 exists (lev, (table_get (table_set x ay stk), hp1)).
 exists (lev, (table_get (table_set x ay stk), hp2)).
 split.
 split; split; simpl; auto.
 split; simpl.
 destruct (eq_dec x x);  [ | contradiction n; auto].
 destruct (eq_dec y x); [ contradiction Hxy; auto |].
 destruct (eq_dec z x); [ contradiction Hxz; auto |].
 split; auto.
 exists ax; split; auto.
  exists ay; split; auto.
 apply H. constructor.
  eapply pred_hereditary; [| eassumption ]; constructor.
Qed.

Lemma semax_store: forall x y z,
         semax (defined y && mapsto x z) (Store x y) (mapsto x y).
Proof.
 intros x y z F H k H0 lev [stk hp] H1.
 destruct lev; [apply safe0 | ].
 destruct H1 as [[n1 [stk1 hp1]] [[n2 [stk2 hp2]] [[[? ?] [[H2a H2b] H2]] [[[ay ?] [ax [? [az [? ?]]]]] ?]]]].
 simpl in *; subst.
 apply safe_step with (k, (stk, table_set ax ay hp)).
 econstructor; eauto.
 apply H0.
 exists (lev, (table_get stk, fun_set hp1 ax (Some ay))); exists (lev, (table_get stk, hp2)).
 split.
 split; auto. split; auto.
 unfold den.
 simpl.
 intro i. unfold fun_set.
 specialize (H7 i). specialize (H2 i).
 change adr with nat in H7|-*.
 destruct (@eq_dec nat _ i ax). rewrite H7 in H2.
 inv H2. constructor.  inv H10.  rewrite H7 in *. auto.
 split.
 exists ax. split; auto. exists ay; split; auto.
 intro a; specialize (H7 a).
 unfold fun_set; change adr with nat in *. simpl.
 destruct (eq_dec a ax); simpl; auto.
  eapply pred_hereditary; [| eassumption ]; constructor.
Qed.

Lemma semax_seq: forall P c1 Q c2 R,
  semax P c1 Q -> semax Q c2 R -> semax P (Seq c1 c2) R.
Proof.
 intros P c1 Q c2 R C1 C2 F H k H0 lev s H1.
 assert (safeN lev (c1::c2::k,s)).
2:  destruct lev; [apply safe0 | ];
       inv H2; eapply safe_step; [constructor | eauto]; auto.
 apply (C1 F); auto.
 intros ? ?; apply H; apply mod_seq1; auto.
 apply C2; auto.
 intros ? ?; apply H; apply mod_seq2; auto.
Qed.

Lemma frame: forall F P c Q,
   subset (modvars c) (nonfreevars F) ->
    semax P c Q -> semax (P * F) c (Q * F).
Proof.
 repeat intro.
 rewrite sepcon_assoc in H2,H3.
 assert (guards (P * (F * F0)) (c::k)).
 apply H0; auto.
 intros ? ?.
 specialize (H _ H4); specialize (H1 _ H4).
 clear - H H1.
 repeat intro.
 destruct H0 as [[lev1 [stk1 hp1]] [[lev2 [stk2 hp2]] [[[? ?] [[? ?] ?]] [? ?]]]].
 simpl in *; subst.
 exists (lev, (fun_set stk x v, hp1)); exists (lev, (fun_set stk x v, hp2)); split; auto.
 split; auto.
 split; auto.
 apply H4;  auto.
Qed.

Lemma semax_pre_post:
  forall P P' c Q' Q,
    P |-- P' -> Q' |-- Q -> semax P' c Q' -> semax P c Q.
Proof.
 repeat intro.
 apply (H1 F); auto.
 intros ? ? ?. apply H3.
 eapply sepcon_derives; try apply H5; auto.
 eapply sepcon_derives; try apply H4; auto.
Qed.








