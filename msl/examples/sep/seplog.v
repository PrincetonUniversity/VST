Require Import msl.msl_standard.
Require Import msl.examples.sep.language.

Definition world := ((var -> option adr)*(adr -> option adr))%type.

Instance Join_world: Join world :=
   Join_prod
     (var -> option adr) (Join_equiv _)
     (adr -> option adr) (Join_fun adr (option adr) (Join_lower (@Join_discrete adr))).

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Perm_alg world := _.
Instance Canc_world : Perm_alg world := _.
Instance Disj_world : Perm_alg world := _.
Instance ag_world : ageable world := ag_flat _.
Instance Age_world : Age_alg world := asa_flat.

Definition den (s: state) : world := (table_get (fst s), table_get (snd s)).

Obligation Tactic := (try solve [repeat intro; match goal with H: age _ _ |- _ => inv H end]).

Program Definition defined (y: var) : pred world :=
   fun w => exists v, fst w y = Some v.

Definition fun_set (f: nat -> option nat) (x: nat) (y: option nat) :=
   fun i => if eq_dec i x then y else f i.

Program Definition subst (x y: var) (P: pred world) : pred world :=
   fun w => P (fun_set (fst w) x (fst w y), snd w).

Program Definition mapsto (x y: var) : pred world :=
 fun w => 
    exists ax, fst w x = Some ax /\
    exists ay, fst w y = Some ay /\
    forall a, if eq_dec a ax then snd w a = Some ay else snd w a = None.

Program Definition equal (x y: var) : pred world := 
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

Definition semax (P: pred world) (c: command) (Q: pred world) : Prop :=
  forall F s, subset (modvars c) (nonfreevars F) ->
    (P*F)%pred (den s) -> exists s', exec c s = Some s' /\ (Q*F)%pred (den s').

Lemma semax_assign: forall P x y,
      semax (defined y && subst x y P) (Assign x y) P.
Proof.
  intros.  intros F s DISJ H.
  destruct H as [[stk1 hp1] [[stk2 hp2] [? [[[v ?] ?] ?]]]].
  exists (table_set x v (fst s), snd s).
  destruct H.
  destruct s as [stk hp]; simpl in *.
  destruct H. subst. rewrite H0; simpl. split; auto.
  match goal with H0: app_pred P ?X |- _ => exists X; exists (fst X, hp2) end.
  simpl. split; auto. split; simpl; auto. split; simpl; auto. unfold fun_set.
  extensionality i.
  simpl.
  change var with nat; destruct (eq_dec i x); auto. 
  split;  auto.
  specialize (DISJ x).
  unfold nonfreevars in DISJ.

  apply DISJ; auto.
  constructor.
Qed.

Lemma semax_load: forall x y z, x <> y -> x <> z ->
       semax (mapsto y z)  (Load x y) (mapsto y z && equal x z).
Proof.
 intros ? ? ? Hxy Hxz; hnf; intros.
destruct s as [stk hp].
destruct H0 as [[stk1 hp1] [[stk2 hp2] [[? ?] [[ax [? [ay [? ?]]]] ?]]]].
 simpl in *.
 destruct H0; subst. rewrite H2. simpl.
 exists (table_set x ay stk, hp).
 generalize (H4 ax); intros. 
 destruct (eq_dec ax ax); [ | contradiction n; auto].
  generalize (H1 ax); rewrite H0; intro. inv H6. simpl.
  split; auto.
 exists (table_get (table_set x ay stk), hp1).
 exists (table_get (table_set x ay stk), hp2).
 split; split; simpl; auto.
 destruct (eq_dec x x);  [ | contradiction n; auto].
 destruct (eq_dec y x); [ contradiction Hxy; auto |].
 destruct (eq_dec z x); [ contradiction Hxz; auto |].
 split; auto.
 exists ax; split; auto.
  exists ay; split; auto.
 apply H. constructor. auto.
 destruct H10.
Qed.

Lemma semax_store: forall x y z,
         semax (defined y && mapsto x z) (Store x y) (mapsto x y).
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












