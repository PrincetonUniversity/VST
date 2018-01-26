Load loadpath.
Require Import VST.msl.base VST.msl.sepalg VST.msl.psepalg VST.msl.predicates_sl VST.msl.functors
               VST.msl.sepalg_functors VST.msl.sepalg_generators.
Require Import veristar.variables veristar.model_type.

Module BarebonesStates.
Definition loc := nat.
Definition val := option nat.
Definition var := Ident.t.
Definition env := var -> val.
Definition heap := loc -> val.
End BarebonesStates.

Module BarebonesLogic <: VERISTAR_LOGIC.
Import BarebonesStates.

Definition loc := loc.
Instance Join_loc : Join loc := @Join_equiv _.
Instance Perm_loc : Perm_alg loc := _.
Instance Sep_loc : Sep_alg loc := _.
Instance Canc_loc : Canc_alg loc := _.

Instance Join_nat : Join nat := @Join_discrete _.
Instance Pos_nat : @Pos_alg nat (@Join_discrete _) := @psa_discrete _.
Instance Canc_nat : @Canc_alg nat Join_nat.
unfold Canc_alg; intros ? ? ? ? H; inv H.
Qed.

Definition val := val.
Instance Join_val : Join val := Join_lower Join_nat.
Instance Perm_val : Perm_alg val := _.
Instance Sep_val : Sep_alg val := _.
Instance Canc_val : Canc_alg val := @Canc_lower _ _ _ Canc_nat.

Lemma identity_None: @identity _ Join_val None.
repeat intro. inv H; auto. Qed.
Hint Resolve identity_None.

Definition val2loc (v: val) : option loc :=
  match v with Some (S n) => Some (S n) | _ => None end.

Definition nil_val : val := Some O.

Lemma nil_not_loc: val2loc nil_val = None.
Proof. reflexivity. Qed.

Definition empty_val : val := None.

Lemma emp_empty_val v : identity v <-> v = empty_val.
destruct v; simpl; intuition; [symmetry; apply H; constructor|inv H].
Qed.

Definition full (v: val) := forall v2, joins v v2 -> identity v2.

Lemma val2loc_full v l : val2loc v = Some l -> full v.
intro H; destruct v as [[|n]|]; inv H.
unfold full; intros v2 [[x|] H]; inv H; auto; inversion H3.
Qed.

Lemma nil_full : full nil_val.
unfold full, nil_val; intros x H; inversion H as [x0 H0]; inv H0; auto; inv H2.
Qed.

Lemma empty_not_full : ~full empty_val.
unfold not, full, empty_val; intros. specialize (H (Some O)).
spec H. econstructor; constructor. specialize (H None (Some O)).
spec H. constructor. inv H.
Qed.

Lemma val2loc_inj v1 v2 l :
  val2loc v1 = Some l ->  val2loc v2 = Some l -> v1=v2.
unfold val2loc; intros. destruct v1; inv H. destruct n; inv H2.
destruct v2; inv H0. destruct n0; inv H1. auto.
Qed.

Lemma loc_eq_dec (l1 l2 : loc) : Decidable.decidable (l1=l2).
intros; case_eq (beq_nat l1 l2); intros.
left; apply beq_nat_eq; auto.
right; apply beq_nat_false; auto.
Qed.

Lemma nil_dec v : Decidable.decidable (v=nil_val).
unfold nil_val; intros. destruct v. destruct n. left; auto. right; congruence.
right; congruence.
Qed.

Definition var := Ident.t.

Definition env := var -> nat.

Definition env_get (rho: env) : var -> val := fun x => Some (rho x).

Definition env_set (x: var) (v: val) (rho: env) : env :=
  match v with
  | None (*empty_val*) => rho
  | Some v' => fun y => if Ident.eq_dec x y then v' else rho y
  end.

Lemma gss_env (x: var) (v: val) (s: env) : v<>empty_val -> env_get (env_set x v s) x = v.
unfold env_get, env_set; intros.
destruct v.
destruct (Ident.eq_dec x x); auto.
contradiction n0; auto.
elimtype False; apply H; auto.
Qed.

Lemma gso_env (x y : var) (v: val) (s: env) :
  x<>y -> env_get (env_set x v s) y = env_get s y.
unfold env_get, env_set; intros.
destruct v; auto.
destruct (Ident.eq_dec x y); auto.
contradiction.
Qed.

(* For now, we assume vars are defined locations (i.e., we don't yet model
   data fields or deal with undefined vars; that is future work).
   In general, our soundness proof doesn't require the user to exhibit an
   empty environment anyway. *)

(*Definition empty_env : env := fun x => None.*)

(*Lemma env_gempty x : env_get empty_env x = empty_val.
Proof. unfold env_get, empty_env, empty_val; intros; auto. Qed.*)

Lemma env_reset s x : env_set x (env_get s x) s = s.
unfold env_set, env_get; extensionality.
destruct (Ident.eq_dec x x0); auto. subst; auto.
Qed.

Lemma env_reset2 s x z : env_set x (env_get s x) (env_set x z s) = s.
unfold env_set, env_get; extensionality.
destruct (Ident.eq_dec x x0); auto. subst; auto.
destruct z; auto.
destruct (Ident.eq_dec x x0); auto. subst; elimtype False; auto.
Qed.

Definition heap := loc -> val.
Instance Join_heap : Join heap := Join_fun loc val _.
Instance Perm_heap : Perm_alg heap := _.
Instance Sep_heap : Sep_alg heap := _.
Instance Canc_heap : Canc_alg heap := @Canc_fun loc val  _ _.

Definition rawnext (x: loc) (y : val) (s : heap) :=
  y <> None /\ x<>O /\ s x = y /\ forall x', x'<>x -> s x' = None.

Definition emp_at (l: loc) (h: heap) := h l = None.

Lemma heap_gempty h l : identity h -> emp_at l h.
unfold emp_at; case_eq (h l); intros ? H1; auto.
intros H2; elimtype False.
specialize (H2 (fun _ => None) h); rewrite <-H2 in H1; inv H1.
intro; constructor.
Qed.

Definition nil_or_loc (v: val) := v=nil_val \/ exists l, val2loc v = Some l.

Lemma mk_heap_rawnext (h: heap) (x0: val) (x:loc) (y: val) :
  val2loc (x0) = Some x -> nil_or_loc y ->
  exists h', rawnext x y h' /\ comparable h h'.
unfold val2loc, rawnext; intros. destruct x0; inv H. destruct n; inv H2.
exists (fun z => if beq_nat z (S n) then y else None). rewrite <- beq_nat_refl.
split. split; auto. unfold nil_or_loc in H0; intro; subst.
destruct H0. inv H. destruct H. inv H.
split; auto. split; auto. intros.
rewrite <- beq_nat_false_iff in H. rewrite H. auto.
apply common_unit_comparable. exists (fun _ => None).
split; intro x; constructor.
Qed.

Lemma rawnext_out : forall {x: loc} {x0: val} {x': loc} {y: val} {h: heap},
  rawnext x y h -> val2loc x0 =  Some x' -> x'<>x -> emp_at x' h.
unfold rawnext, val2loc, emp_at; intros.
destruct x0; inv H0. destruct n; inv H3.
destruct H as [? [? ?]]. apply H2; auto.
Qed.

Definition rawnext' x y h := exists h0, join_sub h0 h /\ rawnext x y h0.

Lemma rawnext_at1 : forall {x y h1 h2 h},
  rawnext' x y h1 -> join h1 h2 h -> emp_at x h2 /\ rawnext' x y h.
unfold rawnext', emp_at, rawnext; intros.
destruct H as [h' [? [? [? [? ?]]]]].
destruct y; [ | elimtype False; apply H1; auto].
clear H1. destruct H as [h'' ?]. generalize (H x); intros.
rewrite H3 in H1. inv H1; [ | solve [inv H8]].
generalize (H0 x); rewrite <- H8; intro.
inv H1; [ | inv H10]. split; auto. exists h'. split.
apply join_sub_trans with h1; eauto. exists h''; auto. exists h2; auto.
split; auto. congruence.
Qed.

Lemma rawnext_at2 : forall {x y h1 h2 h},
  join h1 h2 h -> rawnext' x y h -> emp_at x h2 -> rawnext' x y h1.
Proof.
 unfold rawnext', emp_at; intros.
 destruct H0 as [h' [? ?]].
 exists h'. split; auto.
 exists (fun z: loc => if beq_nat z x then None else h1 z).
 intro z.
 case_eq (beq_nat z x); intros.
 apply beq_nat_true in H3. subst.
 specialize (H x). rewrite H1 in H.
 apply join_unit2_e in H; auto.
 rewrite H.
 unfold rawnext in H2. destruct H2 as [? [? [? ?]]].
 rewrite H4.
 destruct H0. specialize (H0 x). rewrite H4 in H0.
 inv H0. contradiction H2; auto. constructor.
 inv H9.
 apply beq_nat_false in H3.
 destruct H0 as [h'' ?].
 generalize (H x) as Hx; rewrite H1; intro.
 generalize (H z) as Hz; clear H; intro.
 generalize (H0 x) as H0x; intro.
 specialize (H0 z).
 clear H1.
 apply join_unit2_e in Hx; auto.
 destruct H2 as [? [? [? ?]]].
 rewrite H2 in H0x; clear H2.
 specialize (H4 _ H3). rewrite H4 in *.
 inv H0x.
 contradiction H; auto.
 constructor.
 inv H7.
Qed.

Lemma  rawnext_not_emp:
  forall {x y h}, rawnext' x y h -> ~emp_at x h.
Proof.
 unfold rawnext', emp_at, not; intros.
 destruct H as [h' [? ?]].
 destruct H as [h'' H].
 specialize (H x).
 rewrite H0 in H; clear H0.
 destruct H1 as [? [? [? ?]]].
 rewrite H2 in H.
 inv H; apply H0; auto.
Qed.

Lemma emp_at_join: forall {h1 h2 h}, join h1 h2 h ->
    forall l,  (emp_at l h1 /\ emp_at l h2) <-> emp_at l h.
Proof.
 unfold emp_at; intros.
 specialize (H l).
 intuition. rewrite H1 in *; rewrite H2 in *; inv H; auto.
 rewrite H0 in H; inv H; auto.
 rewrite H0 in H; inv H; auto.
Qed.

Lemma join_same n1 n2 v1 v2 z :
  join (Some n1) v1 z -> join (Some n2) v2 z -> n1 = n2.
Proof.
inversion 1; inversion 1; subst; try congruence.
inversion H3; subst; auto. inversion H4.
inversion H; subst; auto. inversion H5.
inversion H4; subst; auto. inversion H5.
Qed.

Lemma rawnext_unique: forall x z z' s s' t t' r,
  rawnext x z s -> rawnext x z' s' ->
  join s t r -> join s' t' r -> z' = z /\ s'=s.
Proof with simpl; auto; try congruence.
intros until r; intros [H1 [H2 [H3 H4]]] [H5 [H6 [H7 H8]]]; subst.
intros H9 H10. cut (s = s'); [intro H11; subst s; split; auto|].
extensionality x'. spec H9 x'. spec H10 x'.
remember (s x') as b; remember (s' x') as b'; destruct b as [|v]... destruct b' as [|v']...
f_equal; eapply join_same; eauto.
destruct (loc_eq_dec x' x); [subst|]. rewrite <-Heqb' in H5... rewrite (H4 x' H) in Heqb...
destruct (loc_eq_dec x' x); [subst|]. rewrite <-Heqb in H1... rewrite (H8 x' H) in Heqb'...
Qed.

Lemma vars_defined_locs : forall z (e:env),
  exists v: val, env_get e z = v /\ nil_or_loc v.
Proof.
intros.
unfold env_get.
exists (Some (e z)).
split; auto.
unfold nil_or_loc.
unfold nil_val.
destruct (eq_nat_dec (e z) 0).
subst; left; auto.
right; exists (e z); simpl.
destruct (e z); auto.
elimtype False; omega.
Qed.

End BarebonesLogic.


Require Import veristar.model.

Module BarebonesModel := VeriStarModel BarebonesLogic.

Require Import veristar.veristar_sound.

Module BarebonesSound := VeriStarSound BarebonesModel.

(*Print Assumptions BarebonesSound.check_entailment_sound.*)

(*NOTE:
We assume prop. extensionality, functionality extensionality, and the
excluded middle. (Indeed, excluded middle is natural since we are proving
soundness of a refutation-style theorem prover.)

 prop_ext : ClassicalFacts.prop_extensionality
 Classical_Prop.classic : forall P : Prop, P \/ ~ P
 functional_extensionality_dep : forall (A : Type) (B : A -> Type)
                                   (f g : forall x : A, B x),
                                 (forall x : A, f x = g x) -> f = g

The following axioms stem from the opaque module type in variables.v, which
we implement via extraction to OCaml integers.  Note that there are NO
axioms about the behavior of the functions Z2id and add_id.

 Z2id : Z -> Ident.t
 add_id : Ident.t -> Ident.t -> Ident.t
 Ident.compare : Ident.t -> Ident.t -> comparison
 Ident.compare_spec : forall s s' : Ident.t,
                     CompSpec Ident.eq Ident.lt s s' (Ident.compare s s')
 Ident.eq_dec : forall x y : Ident.t, {Ident.eq x y} + {~ Ident.eq x y}
 Ident.lt : Ident.t -> Ident.t -> Prop
 Ident.lt_strorder : RelationClasses.StrictOrder Ident.lt
 Ident.t : Type
*)
