Require Import language.
Require Import msl.msl_direct.
Require Import msl.env.

Import EnvSA EnvSL.
Opaque env_mapsto.  (* Why is this needed, when it's already said in env.v? *)

Definition stack := env var adr.
Definition heap := env adr adr.

Instance Join_stack : Join stack := Join_equiv _.
Instance Join_heap : Join heap := Join_env.
Definition world := (stack * heap)%type.

Instance Join_world: Join world := Join_prod _ Join_stack _ Join_heap.
Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Perm_alg world := _.
Instance Canc_world : Perm_alg world := _.
Instance Disj_world : Perm_alg world := _.

Fixpoint den_env {key}{A}{KE: EqDec key} (rho: table key A)  : env key A :=
  match rho with
  | (x,v)::xs => env_set x v (den_env xs)
  | nil => empty_env
  end.

Definition den (s: state) : world := (den_env (fst s), den_env (snd s)).

Definition defined (y: var) : pred world :=
   fun w => exists v, env_get (fst w) y = Some v.

Definition subst (x y: var) (P: pred world) : pred world :=
   fun w => P (env_set_sh x (env_get (fst w) y) (fst w), snd w).

Definition mapsto (x: var) (sh: share) (y: var) : pred world :=
 fun w =>
    exists ax, env_get (fst w) x = Some (pfullshare, ax) /\
    exists ay, env_get (fst w) y = Some (pfullshare, ay) /\
    env_mapsto ax sh ay (snd w).

Definition equal (x y: var) : pred world :=
            fun w => env_get (fst w) x = env_get (fst w) y.

Inductive modvars : command -> var -> Prop :=
| mod_assign: forall x y, modvars (Assign x y) x
| mod_load: forall x y, modvars (Load x y) x
| mod_seq1: forall x c1 c2, modvars c1 x -> modvars (Seq c1 c2) x
| mod_seq2: forall x c1 c2, modvars c2 x -> modvars (Seq c1 c2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall stk hp v, P (stk,hp) -> P (env_set x v stk, hp).

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.

(* the rest of this file is w.r.t. a previous version of the operational semantics...
Definition semax (P: pred world) (c: command) (Q: pred world) : Prop :=
  forall F s, subset (modvars c) (nonfreevars F) ->
    (P*F)%pred (den s) -> exists s', exec c s = Some s' /\ (Q*F)%pred (den s').

Lemma env_get_den1 {A B}{AE: EqDec A}:
            forall {s} {y: A} {sh} {v: B}, env_get (den_env s) y = Some (sh,v) ->
               sh = pfullshare.
Proof.
 intros.
 revert H; induction s; simpl; intros.
 rewrite env_get_empty in H. inv H.
 destruct a as [z v'].
 destruct (eq_dec z y).
 subst. rewrite env_gss in H. inv H; auto.
 rewrite env_gso in H; auto.
Qed.

Lemma env_get_den2 {A B}{AE: EqDec A}:
            forall {s} {y: A} {sh} {v: B}, env_get (den_env s) y = Some (sh,v) ->
             table_get s y = Some v.
Proof.
  intros.
  revert H; induction s; simpl; intros.
 rewrite env_get_empty in H. inv H.
 destruct a as [z v'].
 destruct (eq_dec y z).
 subst. rewrite env_gss in H. inv H; auto.
 rewrite env_gso in H; auto.
Qed.

Lemma semax_assign: forall P x y,
      semax (defined y && subst x y P) (Assign x y) P.
Proof.
  intros.  intros F s DISJ H.
  destruct H as [[stk1 hp1] [[stk2 hp2] [? [[[[sh v] ?] ?] ?]]]].
  exists (table_set x v (fst s), snd s).
  destruct H.
  destruct s as [stk hp]; simpl in *.
  destruct H. subst.
  generalize (env_get_den1 H0); intro; subst sh.
  rewrite (env_get_den2 H0) in *.
  simpl; split; auto.
  hnf in H1.
  match goal with H0: P ?X |- _ => exists X; exists (fst X, hp2) end.
  simpl. split; auto. split; simpl; auto. split; simpl; auto.
  rewrite H0. reflexivity.
  split;  auto.
  specialize (DISJ x).
  unfold nonfreevars in DISJ.
  rewrite H0.
  apply DISJ; auto.
  constructor.
Qed.

Lemma semax_load: forall x y z sh, x <> y -> x <> z ->
       semax (mapsto y sh z)  (Load x y) (mapsto y sh z && equal x z).
Proof.
 intros ? ? ? sh Hxy Hxz; hnf; intros.
destruct s as [stk hp].
destruct H0 as [[stk1 hp1] [[stk2 hp2] [[? ?] [[ax [? [ay [? ?]]]] ?]]]].
 simpl in *.
 destruct H0; subst.
 exists (table_set x ay stk, hp).
 rewrite (env_get_den2 H2). simpl.
 destruct (env_mapsto_get _ _ _ _ H4) as [p ?].
 generalize (H1 ax); rewrite H0; intro.
 assert (exists sh', env_get (den_env hp) ax = Some (sh', ay)).
  clear - H4 H1.
  apply env_mapsto_get in H4. destruct H4 as [p ?].
   specialize (H1 ax).  change nat with adr in H; rewrite H in H1.
   inv H1. econstructor; eauto. destruct a2; destruct a3.
  destruct H4. simpl in *. destruct H1; subst a a0. econstructor; eauto.
 destruct H7 as [sh' ?].
 rewrite H7 in H6.
 rewrite (env_get_den2 H7).
  simpl. split; auto.
 exists (den_env (table_set x ay stk), hp1).
 exists (den_env (table_set x ay stk), hp2).
  simpl.
 destruct (eq_nat_dec x x);  [ | contradiction n; auto].
 destruct (eq_nat_dec y x); [ contradiction Hxy; auto |].
 destruct (eq_nat_dec z x); [ contradiction Hxz; auto |].
 split; auto.
 split; auto. simpl. apply join_equiv_refl.
 split.
 split. unfold mapsto.
 exists ax; split; simpl. rewrite env_gso; auto.
 exists ay; split; simpl. rewrite env_gso; auto.
 auto.
 hnf. simpl. rewrite env_gss. rewrite env_gso; auto.
 apply H. constructor. auto.
Qed.

Lemma semax_store: forall x y z,
         semax (defined y && mapsto x Share.top z) (Store x y) (mapsto x Share.top y).
Proof.
 intros; hnf; intros.
 destruct s as [stk hp].
 destruct H0 as [[stk1 hp1] [[stk2 hp2] [[[? ?] ?] [[[[sh ay] ?] [ax [? [az [? ?]]]]] ?]]]].
 simpl in *; subst.
 exists (stk, table_set ax ay hp).
 rewrite (env_get_den2 H4). simpl. rewrite (env_get_den2 H3). simpl. split; auto.
 exists (den_env stk, env_set ax ay hp1); exists (den_env stk, hp2).
 simpl.
 split; auto.
  split; auto. simpl. apply join_equiv_refl. simpl.
 intro i.
 destruct (eq_dec ax i). subst i.
 repeat rewrite env_gss.
 specialize (H2 ax). apply env_mapsto_get in H6. destruct H6 as [p ?].
 change nat with adr in H0; rewrite H0 in H2.
 rewrite (proof_irr p top_share_nonunit) in H2.
 inv H2.  constructor.
 pfullshare_join.
 repeat rewrite env_gso; auto.
 split; auto.
 exists ax. split; auto. exists ay; split; auto.
 rewrite (env_get_den1 H3) in H3; auto.
 replace (env_set ax ay hp1) with (env_set ax ay empty_env).
 apply env_mapsto_set.
 apply env_ext.
 extensionality i.
 destruct (eq_dec i ax). subst. repeat rewrite env_gss; auto.
 repeat rewrite env_gso; auto.
 rewrite env_get_empty.
 clear - n H6. change nat with adr.
 rewrite (env_mapsto_get_neq ax i Share.top az hp1); auto.
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
 exists (env_set x v stk, hp1); exists (env_set x v stk, hp2); split; auto.
  split; auto. simpl. apply join_equiv_refl.
Qed.
*)
