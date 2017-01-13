Add LoadPath "../..".
Require Import msl.msl_direct.
Require Import language.

Definition world := ((var -> option adr)*(adr -> option adr))%type.

Instance Join_world: Join world :=
   Join_prod
     (var -> option adr) (Join_equiv _)
     (adr -> option adr) (Join_fun adr (option adr) (Join_lower (Join_discrete adr))).

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Perm_alg world := _.
Instance Canc_world : Perm_alg world := _.
Instance Disj_world : Perm_alg world := _.

Definition den (s: state) : world := (table_get (fst s), table_get (snd s)).

Definition defined (y: var) : pred world :=
   fun w => exists v, fst w y = Some v.

Definition fun_set (f: nat -> option nat) (x: nat) (y: option nat) :=
   fun i => if eq_dec i x then y else f i.

Definition subst (x y: var) (P: pred world) : pred world :=
   fun w => P (fun_set (fst w) x (fst w y), snd w).

Definition mapsto (x y: var) : pred world :=
 fun w =>
    exists ax, fst w x = Some ax /\
    exists ay, fst w y = Some ay /\
    forall a, if eq_dec a ax then snd w a = Some ay else snd w a = None.

Definition equal (x y: var) : pred world :=
            fun w => fst w x = fst w y.

Inductive modvars : command -> var -> Prop :=
| mod_assign: forall x y, modvars (Assign x y) x
| mod_load: forall x y, modvars (Load x y) x
| mod_seq1: forall x c1 c2, modvars c1 x -> modvars (Seq c1 c2) x
| mod_seq2: forall x c1 c2, modvars c2 x -> modvars (Seq c1 c2) x.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall stk hp v, P (stk,hp) -> P (fun_set stk x v, hp).

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.

Inductive safe: (list command * state) -> Prop :=
| safe_step: forall cs1 cs2, step' cs1 cs2 -> safe cs2 -> safe cs1
| safe_halt: forall s, safe (nil, s).

Definition guards (P: pred world) (k: list command) : Prop :=
  forall s, P (den s) -> safe (k,s).

Definition semax (P: pred world) (c: command) (Q: pred world) : Prop :=
  forall F, subset (modvars c) (nonfreevars F) ->
  forall k, guards (Q*F) k -> guards (P*F) (c :: k).

Lemma semax_assign: forall P x y,
      semax (defined y && subst x y P) (Assign x y) P.
Proof.
  intros P x y F H k H0 [stk hp] H1.
  destruct H1 as [[stk1 hp1] [[stk2 hp2] [? [[[v ?] ?] ?]]]].
  simpl in *.
 destruct H1 as [[? ?] ?]; simpl in *; subst; auto.
  eapply safe_step.
  econstructor; eauto.
  apply H0.
  exists (fun_set (table_get stk) x (table_get stk y), hp1).
  exists (fun_set (table_get stk) x (table_get stk y), hp2).
  split; [|split].
  split; auto. split; auto.
  simpl; extensionality i.
  unfold var, fun_set.
  destruct (eq_dec i x); auto.
  apply H3.
  apply (H x).
  constructor.
  apply H4.
Qed.

Lemma semax_load: forall x y z, x <> y -> x <> z ->
       semax (mapsto y z)  (Load x y) (mapsto y z && equal x z).
Proof.
  intros x y z Hxy Hxz F H k H0 [stk hp] H1.
 destruct H1 as [[stk1 hp1] [[stk2 hp2] [? [[ax [? [ay [? ?]]]] ?]]]].
 simpl in *.
 destruct H1 as [[? ?] ?]; simpl in *; subst.
 apply safe_step with  (k, (table_set x ay stk, hp)).
 econstructor; eauto.
 generalize (H4 ax); intros.
 destruct (eq_dec ax ax); [ | contradiction n; auto].
 generalize (H7 ax).  rewrite H1; intro. inv H6; auto.  destruct H11.
 apply H0.
 exists (table_get (table_set x ay stk), hp1).
 exists (table_get (table_set x ay stk), hp2).
 repeat split; simpl; auto.
 exists ax; split; simpl; auto.
 destruct (eq_dec y x); [ contradiction Hxy; auto | auto ].
 exists ay; split; simpl; auto.
 destruct (eq_dec z x); [ contradiction Hxz; auto | auto].
 hnf; simpl.
 destruct (eq_dec x x);  [ | contradiction n; auto].
 destruct (eq_dec z x); [ contradiction Hxz; auto | auto].
 apply H; auto. constructor.
Qed.

Lemma semax_store: forall x y z,
         semax (defined y && mapsto x z) (Store x y) (mapsto x y).
Proof.
 intros x y z F H k H0 [stk hp] H1.
 destruct H1 as [[stk1 hp1] [[stk2 hp2] [[[H2a H2b] H2] [[[ay ?] [ax [? [az [? ?]]]]] ?]]]].
 simpl in *; subst.
 apply safe_step with (k, (stk, table_set ax ay hp)).
 econstructor; eauto.
 apply H0.
 exists (table_get stk, fun_set hp1 ax (Some ay)); exists (table_get stk, hp2).
 repeat split; simpl; auto.
 intro i. unfold fun_set.
 specialize (H5 i). specialize (H2 i).
 change adr with nat in H5|-*.
 destruct (@eq_dec nat _ i ax). rewrite H5 in H2.
 inv H2. constructor.  inv H10.  rewrite H5 in *. auto.
 exists ax. split; auto. exists ay; split; auto.
 intro a; specialize (H5 a).
 unfold fun_set; change adr with nat in *. simpl.
 destruct (eq_dec a ax); simpl; auto.
Qed.


Lemma semax_seq: forall P c1 Q c2 R,
  semax P c1 Q -> semax Q c2 R -> semax P (Seq c1 c2) R.
Proof.
 intros P c1 Q c2 R C1 C2 F H k H0 s H1.
 assert (safe (c1::c2::k,s)).
2:  inv H2; eapply safe_step; [constructor | eauto]; auto.
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
 destruct H0 as [[stk1 hp1] [[stk2 hp2] [[[? ?] ?] [? ?]]]].
 simpl in *; subst.
 exists (fun_set stk x v, hp1); exists (fun_set stk x v, hp2); split; auto.
 split; auto.
 apply H4;  auto.
Qed.

Lemma semax_pre_post:
  forall P P' c Q' Q,
    P |-- P' -> Q' |-- Q -> semax P' c Q' -> semax P c Q.
Proof.
 repeat intro.
 apply (H1 F); auto.
 intros ? ?. apply H3.
 eapply sepcon_derives; try apply H5; auto.
 eapply sepcon_derives; try apply H4; auto.
Qed.


