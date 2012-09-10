Require Import msl.msl_standard.
Require Import msl.examples.sep.language.

Definition world := (nat * ((var -> option adr)*(adr -> option adr)))%type.

Instance Join_world: Join world :=
  Join_prod nat (Join_equiv nat)
   _
   (Join_prod
     (var -> option adr) (Join_equiv _)
     (adr -> option adr) (Join_fun adr (option adr) (Join_lower (@Join_discrete adr)))).

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

Definition semax (P: pred world) (c: command) (Q: pred world) : Prop :=
  forall lev F s, subset (modvars c) (nonfreevars F) ->
    (P*F)%pred (den (S lev) s) -> exists s', exec c s = Some s' /\ (Q*F)%pred (den lev s').

Lemma semax_assign: forall P x y,
      semax (defined y && subst x y P) (Assign x y) P.
Proof.
  intros.  intros lev F s DISJ H.
  destruct H as [[lev1 [stk1 hp1]] [[lev2 [stk2 hp2]] [? [[[v ?] ?] ?]]]].
  exists (table_set x v (fst s), snd s).
  destruct s as [stk hp].
  destruct H. destruct H3. simpl fst in *. simpl snd in *. destruct H; subst.
  destruct H3; subst. 
  split. simpl. rewrite H0. simpl. auto.
  do 3 red in H1. simpl fst in H1; simpl snd in H1.
  exists (lev, (fun_set (table_get stk) x (table_get stk y), hp1)).
  exists (lev, (fun_set (table_get stk) x (table_get stk y), hp2)).
  simpl. split; auto. split; simpl; auto.  split; simpl; auto.
  split; simpl; auto. unfold fun_set.
  extensionality i.
  simpl.
  change var with nat; destruct (eq_dec i x); auto. 
  split;  auto.
  specialize (DISJ x).
  unfold nonfreevars in DISJ.
  eapply pred_hereditary; eauto.
 reflexivity.
 

  apply DISJ; auto.
  constructor.
  eapply pred_hereditary; eauto.
 reflexivity.
Qed.

Lemma semax_load: forall x y z, x <> y -> x <> z ->
       semax (mapsto y z)  (Load x y) (mapsto y z && equal x z).
Proof.
 intros ? ? ? Hxy Hxz; hnf; intros.
destruct s as [stk hp].
destruct H0 as [[lev1 [stk1 hp1]] [[lev2 [stk2 hp2]] [[? ?] [[ax [? [ay [? ?]]]] ?]]]].
 simpl in *.
 destruct H0; subst. destruct H1; subst.
 destruct H0; simpl in*; subst.
 rewrite H2. simpl.
 exists (table_set x ay stk, hp).
 generalize (H4 ax); intros. 
 destruct (eq_dec ax ax); [ | contradiction n; auto].
  generalize (H1 ax); rewrite H0; intro. inv H6. simpl.
  split; auto.
 exists (lev, (table_get (table_set x ay stk), hp1)).
 exists (lev, (table_get (table_set x ay stk), hp2)).
  simpl.
 split; split; simpl; auto. split; simpl; auto.
 destruct (eq_dec x x);  [ | contradiction n; auto].
 destruct (eq_dec y x); [ contradiction Hxy; auto |].
 destruct (eq_dec z x); [ contradiction Hxz; auto |].
 split; auto.
 exists ax; split; auto.
  exists ay; split; auto. 
 apply H. constructor.
 eapply pred_hereditary; eauto. reflexivity.
 destruct H10.
Qed.

Lemma semax_store: forall x y z,
         semax (defined y && mapsto x z) (Store x y) (mapsto x y).
(* Not done:  adjust the rest of this file for the "level" field of states *)
Proof.
 intros; hnf; intros.
 destruct s as [stk hp].
 destruct H0 as [[stk1 hp1] [[stk2 hp2] [[[? ?] ?] [[[ay ?] [ax [? [az [? ?]]]]] ?]]]].
 simpl in *; subst.
 exists (stk, table_set ax ay hp).
 rewrite H4. simpl. rewrite H3. simpl. split; auto.
 exists (table_get stk, fun_set hp1 ax (Some ay)); exists (table_get stk, hp2).
 simpl.
 split; auto.
  split; auto. simpl.
 intro i. unfold fun_set.
 specialize (H6 i). specialize (H2 i).
 change adr with nat in H6|-*.
 destruct (@eq_dec nat _ i ax). rewrite H6 in H2.
 inv H2. constructor.  inv H9.  rewrite H6 in *. auto.
 split; auto. 
 exists ax. split; auto. exists ay; split; auto.
 intro a; specialize (H6 a).
 unfold fun_set; change adr with nat in *;
 destruct (eq_dec a ax); auto.
Qed.

Lemma semax_seq: forall P c1 Q c2 R,
  semax P c1 Q -> semax Q c2 R -> semax P (Seq c1 c2) R.
Proof.
 unfold semax; intros. 
 destruct (H F s) as [s1 [? ?]]; auto.
 intros ? ?. apply H1. constructor 3; auto.
 destruct (H0 F s1) as [s2 [? ?]]; auto.
 intros ? ?. apply H1. constructor 4; auto.
 exists s2; split; auto.
 simpl. rewrite H3; simpl. auto.
Qed.

Lemma frame: forall F P c Q,
   subset (modvars c) (nonfreevars F) ->
    semax P c Q -> semax (P * F) c (Q * F).
Proof.
 repeat intro.
 rewrite sepcon_assoc in H2|-*.
 apply H0 in H2. auto.
 intros ? ?.
 specialize (H _ H3); specialize (H1 _ H3).
 clear - H H1.
 repeat intro.
 destruct H0 as [[stk1 hp1] [[stk2 hp2] [[[? ?] ?] [? ?]]]].
 simpl in *; subst.
 exists (fun_set stk x v, hp1); exists (fun_set stk x v, hp2); split; auto.
  split; auto.
Qed.












