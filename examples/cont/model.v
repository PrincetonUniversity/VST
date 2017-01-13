Require Import msl.msl_standard.
Require Import msl.Coqlib2.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import language.
Require Import seplogic.

Hint Extern 3 (list_nodups _ = true) => (compute; reflexivity).
Hint Extern 3 (typecheck _ _ = true) => (compute; reflexivity).
Hint Extern 3 (expcheck _ _ = true) => (compute; reflexivity).
Hint Resolve andb_true_intro.

Obligation Tactic := idtac.

Module Semax : SEMAX.

Local Open Scope pred.

(******  CONSTRUCTION OF rmap FOR THE CONT LANGUAGE *****)
Inductive kind := VAL: adr -> kind | FUN: list var -> kind.

Module AV0 <: ADR_VAL0.
 Definition address := adr.
 Definition some_address := 0.
 Definition kind := kind.
End AV0.

Module AV := SimpleAdrVal AV0.
Module R := Rmaps AV.
Module RML := Rmaps_Lemmas R.
Export RML. Export R.
Instance Cross_rmap : Cross_alg rmap := Cross_rmap_simple (fun _ => I).

Obligation Tactic := idtac.

(******  MAPSTO AND RELATED OPERATORS *****)

Program Definition mapsto (v1 v2: adr) : pred rmap :=
  fun w => forall i,
         if eq_dec i v1 then w @ i = YES pfullshare (VAL v2) NoneP else identity (w @ i).
Next Obligation.
 intros. intros ? ? ? ?.
  intro i; specialize (H0 i).
  destruct (eq_dec i v1).
  apply (age1_YES _ _ _ _ _ H); auto.
  destruct (identity_resource (a @ i)) as [? _]. specialize (H1 H0).
  apply identity_resource.
  generalize (age1_resource_at _ _ H i (a @ i)); intro.
  generalize (resource_at_approx a i); intro.
  destruct (a @ i); try contradiction.
  rewrite H2; simpl in *; auto.
  rewrite H2; simpl in *; auto.
Qed.

Lemma mapsto_conflict:
   forall a b c, mapsto a b  *  mapsto a c |-- FF.
  Proof.
    intros.
    intros w  [w1 [w2 [? [? ?]]]]; hnf.
    specialize (H0 a). specialize (H1 a).
    rewrite if_true in * by auto.
    apply (resource_at_join _ _ _ a) in H.
    rewrite H0 in H; rewrite H1 in H; inv H.
    pfullshare_join.
 Qed.

Lemma singleton_rmap_OK:
   forall v v' m,
       resource_fmap (approx (level m))
            oo (fun i => if eq_dec i v then YES pfullshare (VAL v') NoneP else core m @  i) =
    (fun i => if eq_dec i v then YES pfullshare (VAL v') NoneP else core m @ i).
Proof.
  intros; extensionality i; unfold compose; simpl.
  destruct (eq_dec i v).
  unfold resource_fmap. f_equal. apply preds_fmap_NoneP.
  rewrite <- level_core.
  symmetry; apply resource_at_approx.
Qed.

Definition singleton_rmap  (v v': adr) (m: rmap) : rmap :=
  proj1_sig
  (make_rmap (fun i => if eq_dec i v then YES pfullshare (VAL v') NoneP  else core m @ i )
    I (level m) (singleton_rmap_OK _ _ m)).

Lemma singleton_rmap_level: forall x y m,
      level (singleton_rmap x y m) = level m.
Proof.
  intros.  apply level_make_rmap.
Qed.

Lemma singleton_rmap_mapsto:
   forall x y n, app_pred (mapsto x y) (singleton_rmap x y n).
 Proof.
  intros. hnf. simpl snd.
  unfold singleton_rmap.
  intro; repeat rewrite resource_at_make_rmap.
  change AV.address with adr.
 destruct (eq_dec i x); auto.
 apply resource_at_core_identity.
Qed.

Local Open Scope pred.

Lemma mapsto_uniq: forall (x y: adr) w w', core w = core w' -> mapsto x y w -> mapsto x y w' -> w=w'.
Proof.
  intros.
 apply rmap_ext.
 assert (level (core w) = level (core w')) by congruence.
 do 2 rewrite level_core in H2. auto.
 intro.
 specialize (H0 l); specialize (H1 l).
 destruct (@eq_dec adr _ l x); try congruence.
 apply identity_unit_equiv in H0.
 apply unit_core in H0.
 apply identity_unit_equiv in H1.
 apply unit_core in H1.
 rewrite core_resource_at in *. congruence.
Qed.

Lemma mapsto_e1: forall v1 v2 w,
       app_pred (mapsto v1 v2 * TT) w ->
       w @ v1 = YES pfullshare (VAL v2) NoneP.
Proof.
 intros.
 destruct H as [w1 [w2 [? [? ?]]]].
 hnf in H0.
 specialize (H0 v1).
 apply (resource_at_join _ _ _ v1) in H.
 rewrite if_true in H0 by auto. rewrite H0 in H.
apply join_YES_pfullshare1 in H. inv H; auto.
Qed.

Definition assert := env -> pred rmap.
Bind Scope pred with assert.

(****** PROGRAM SAFETY AS A SEPARATION-LOGIC PREDICATE *)

Program Definition cohere (concrete: heap) : pred rmap :=
 fun w =>
 forall p v, heap_get (concrete) p = Some v  <->
                 w @ p = YES pfullshare (VAL v) NoneP.
Next Obligation.
  unfold hereditary; intros.
  rewrite H0.
  apply age1_YES; auto.
Qed.


Program Definition assert_safe
     (p: program) (vars: varset) (ctl: control) : assert :=
  fun s w => forall s' h, varcompat vars s' ->
                   locals2env s' = s -> cohere h w -> safeN p (s',h,ctl) (level w).
 Next Obligation.
  unfold hereditary; intros.
  eapply safeN_less; [ | apply H0]; auto. subst.
  apply age_level in H.   rewrite H. change R.rmap with rmap. omega.
  clear - H H3. hnf in H3|-*. intros. rewrite H3.
    generalize (age1_YES _ _ p pfullshare (VAL v) H); intros.
  intuition.
 Qed.

Lemma assert_safe0:
        forall p vars k s w,
           (forall w', age w w' -> app_pred (assert_safe p vars k s) w) ->
            app_pred (assert_safe p vars k s) w.
Proof.
  intros.
  case_eq (age1 w); intros.
  apply (H _ H0).
  hnf; repeat intro.
  rewrite age1_level0 in H0. rewrite H0. hnf. econstructor; reflexivity.
Qed.

(******* FUNASSERT, MAKE_WORLD ********************)

Definition funspec := (list var * assert)%type.
Definition funspecs := table adr funspec.

Definition unpack (P: list adr -> pred rmap) (vl: listprod (@cons Type (list adr) nil)):  pred rmap := P (fst vl).

Definition call (P: list var * assert) (vl: list adr) : pred rmap :=
     (!! (length vl = length (fst P)) && snd P (arguments (fst P) vl)).

Program Definition cont (nP: funspec)  (v: adr) : pred rmap :=
  fun w => w @ v = PURE (FUN (fst nP)) (preds_fmap (approx (level w)) (SomeP (list adr::nil)
             (unpack (call nP)))).
Next Obligation.
 intros; intro; intros.
  apply (age1_resource_at a a' H v (PURE (FUN (fst nP)) _));   simpl; auto.
Qed.

Definition funassert (G: funspecs) : pred rmap :=
   (ALL  i:_, ALL P:_,  !! (table_get G i = Some P) --> cont P i)  &&
   (ALL  i:_, ALL P:_,  cont P i --> !! exists P', table_get G i = Some P').

Definition make_world_aux (G: funspecs) (h: heap) (n: nat) (a: adr) : resource :=
   match table_get G a with
   | Some P => PURE (FUN (fst P))
                               (preds_fmap (approx n)
                                      (SomeP (@cons Type (list adr) nil) (unpack (call P))))
   | None => match heap_get h a with
                     | Some v => YES pfullshare (VAL v) NoneP
                     | None => NO
                    end
   end.

Lemma make_world_aux_OK:
  forall G h n,
         resource_fmap (approx n) oo make_world_aux G h n =  make_world_aux G h n.
Proof.
 intros.
 extensionality v;
 unfold make_world_aux, compose.
 destruct (table_get G v). destruct f as [nargs P]. simpl.
 f_equal. f_equal. rewrite <- compose_assoc. rewrite approx_oo_approx. auto.
 destruct (heap_get h v); auto.
 unfold resource_fmap.
 f_equal. apply preds_fmap_NoneP.
Qed.

Definition make_world (G: funspecs) (h: heap) (n: nat) : rmap :=
    proj1_sig (make_rmap (make_world_aux G h n) I n (make_world_aux_OK _ _ _)).

Lemma level_make_world:
  forall h G n, level (make_world G h n) = n.
Proof.
 intros; simpl.
 apply level_make_rmap.
Qed.

Inductive match_specs: forall (p: program) (G: funspecs), Prop :=
| match_specs_nil: match_specs nil nil
| match_specs_cons: forall i vars f p' P G',
         not (In i (map (@fst _ _) p')) ->
         match_specs p' G' ->
         typecheck vars f = true ->
         match_specs ((i,(vars,f))::p') ((i,P)::G').

Lemma match_specs_boundary:
   forall p G i,
   match_specs p G -> i >= boundary p -> table_get G i = None.
Proof.
  induction 1. intros. reflexivity.
  intros. simpl in *.
  destruct (@eq_dec adr _ i i0). subst.
  clear - H2. destruct (boundary p'). elimtype False; omega.
 generalize (Max.le_max_l i0 n); intro. elimtype False. omega.
 apply IHmatch_specs.
 destruct (boundary p'); try omega.
 generalize (Max.le_max_r i0 n0);  omega.
Qed.

Lemma funassert_e:  forall G i f,
      table_get G i = Some f ->
      funassert G |-- cont f i.
Proof.
  intros.
  unfold funassert.
  apply andp_left1.
  intros w ?. apply H0; auto.
Qed.

Lemma funassert_make_world: forall p G n,
         app_pred (funassert G) (make_world G (initial_heap p) n).
Proof.
 intros ? ? ?.
 forget (initial_heap p) as h.
 split.
 intros i P w ? ?.
 hnf in H0.
 eapply pred_nec_hereditary; try apply H.
 clear w H.
 hnf. unfold make_world; simpl. rewrite resource_at_make_rmap.
 unfold make_world_aux. rewrite H0.
 f_equal. simpl. f_equal. rewrite level_make_rmap.
 reflexivity.
 intros i P w ? ?.
 hnf.
 case_eq (table_get G i); intros. eauto.
 elimtype False.
 hnf in H0.
 case_eq (make_world G h n @ i); intros.
 apply (necR_NO _ _ i H) in H2. inversion2 H0 H2.
 apply (necR_YES _ _ i _ _ _ H) in H2. inversion2 H2 H0.
 clear dependent w.
 unfold make_world in H2.
 rewrite resource_at_make_rmap in H2. unfold make_world_aux in H2.
 rewrite H1 in H2. destruct (heap_get h i); inv H2.
Qed.

Lemma cohere_make_world:
  forall p G n,
      match_specs p G ->
     app_pred (cohere (initial_heap p)) (make_world G (initial_heap p) n).
Proof.
 intros.
 hnf.
 intros. unfold make_world, make_world_aux; simpl. rewrite resource_at_make_rmap.
 unfold  initial_heap. simpl. unfold heap_get.
  rename p0 into i.
 destruct (lt_dec i (boundary p)).
 split; intro. inv H0. elimtype False.
 revert H0; case_eq (table_get G i); intros. destruct f as [nargs P].
 inv H1. inv H1.
 rewrite (match_specs_boundary p G i); auto; try omega.
 split; intro Hx; inv Hx; auto.
Qed.

Lemma funassert_get:
  forall G v nP,  funassert  G && cont nP v |--
                      EX P':assert, (ALL vl:list adr, |> ! (call nP vl <=> call (fst nP,P') vl)) && !! (table_get G v = Some (fst nP,P')).
Proof.
 intros. intros w [? ?].
 destruct H.
 specialize (H v); specialize (H1 v).
 specialize (H1 _ _ (necR_refl _) H0).
 destruct H1 as [[args P'] ?].
 exists P'.
 specialize (H _ _ (necR_refl _) H1).
 split.
 Focus 2. hnf in H,H0. inversion2 H H0. apply H1.
 clear H1. rename H into H99. rename H0 into H97.
 hnf in H99,H97. rewrite H99 in H97.  apply PURE_inj in H97. destruct H97 as [H H97].
 simpl in H. destruct nP as [na P]. inv H.
 intro vl. intros w' ? w'' ?.
  assert (level w'' < level w). do 3 red in H. apply laterR_level in H.
       apply le_lt_trans with (level w'); auto.
 simpl fst.
  split; intros w''' ? ?.
 match type of H97 with ?A = _ => assert (app_pred (A (vl,tt)) w''') end.
  rewrite H97.
 split.
  change rmap with R.rmap in *.
  change ag_rmap with R.ag_rmap in *.
  apply necR_level in H2; omega.
 apply H3.
  destruct H4. apply H5.
 match type of H97 with _ = ?A => assert (app_pred (A (vl,tt)) w''') end.
  rewrite <- H97.
 split.
  change rmap with R.rmap in *.
  change ag_rmap with R.ag_rmap in *.
  apply necR_level in H2; omega.
 apply H3.
  destruct H4. apply H5.
Qed.

Lemma cont_core: forall P i w, app_pred (cont P i) w <-> app_pred (cont P i) (core w).
Proof.
 intros.
 unfold cont. simpl. rewrite <- core_resource_at.
 split; intro. rewrite H.
 clear. symmetry. rewrite level_core. apply unit_core; constructor.
 rewrite level_core in H.
 generalize (core_unit (w @ i)); intro.
 rewrite H in H0.
 inv H0; auto.
Qed.

Lemma funassert_core: forall G w, app_pred (funassert G) w <-> app_pred (funassert G) (core w).
Proof.
 intros.
 split; intros [? ?]; split; intros i P w' ? ?.
 specialize (H i P _ (necR_refl _) H2).
 apply cont_core in H. eapply pred_nec_hereditary; eauto.
 generalize (core_unit w); intro.
 unfold unit_for in H3.
 eapply nec_join in H3; eauto.
 destruct H3 as [y' [z' [? [? ?]]]].
 generalize (necR_linear' H4 H5); intro.
 spec H6. apply join_level in H3. destruct H3; congruence.
 subst z'. clear H5.
 specialize (H0 i P _ H4).
 apply join_core in H3. rewrite cont_core in H2. rewrite H3 in H2. rewrite <- cont_core in H2.
 specialize (H0 H2). apply H0.
 assert (necR (core w) (core w')).
 generalize (core_unit w); intro.
 unfold unit_for in H3.
 apply join_comm in H3.
 eapply nec_join in H3; eauto.
 destruct H3 as [y' [z' [? [? ?]]]].
 generalize (necR_linear' H1 H5); intro.
 spec H6. apply join_level in H3. destruct H3; congruence. subst z'.
 apply join_comm in H3.
 generalize (unit_identity _ H3); intro.
 apply identity_unit_equiv in H6. apply unit_core in H6.
 apply join_core in H3. rewrite H6 in H4. rewrite H3 in H4; auto.
 specialize (H i P _ H3 H2).
 apply cont_core in H; auto.
 assert (necR (core w) (core w')).
 generalize (core_unit w); intro.
 unfold unit_for in H3.
 apply join_comm in H3.
 eapply nec_join in H3; eauto.
 destruct H3 as [y' [z' [? [? ?]]]].
 generalize (necR_linear' H1 H5); intro.
 spec H6. apply join_level in H3. destruct H3; congruence. subst z'.
 apply join_comm in H3.
 generalize (unit_identity _ H3); intro.
 apply identity_unit_equiv in H6. apply unit_core in H6.
 apply join_core in H3. rewrite H6 in H4. rewrite H3 in H4; auto.
 specialize (H0 i P _ H3).
 apply H0. rewrite <- cont_core; auto.
Qed.


(**************** ALLOCPOOL ***************************)


Program Definition allocpool (b: adr) : pred rmap :=
   fun w => b>0 /\ forall i, if lt_dec i b then identity (w @ i) else w @ i = YES pfullshare (VAL 0) NoneP.
Next Obligation.
 intros. intro; intros.
  destruct H0; split; auto.
 intro i; specialize (H1 i).
 destruct (lt_dec i b).
  eapply age1_resource_at_identity; eauto.
 apply (age1_YES _ _ _ _ _ H); auto.
Qed.

Lemma allocpool_make_world: forall p G n,
          match_specs p G ->
          app_pred (allocpool (boundary p)) (make_world G (initial_heap p) n).
Proof.
  unfold make_world; intros.
  rename H into H'.
 unfold initial_locals,initial_heap  in *.
 split.
 destruct p; simpl. omega. destruct p. destruct (boundary p0); omega.
 intro loc.
 destruct (make_rmap
        (make_world_aux G
           (fun i : adr => if lt_dec i (boundary p) then None else Some 0) n)
        I n
        (make_world_aux_OK G
           (fun i : adr => if lt_dec i (boundary p) then None else Some 0) n)) as [? [? ?]];
  simpl in *. rewrite e0. unfold make_world_aux.
 unfold heap_get.
 destruct (lt_dec loc (boundary p)).
 destruct (table_get G loc);  apply identity_resource; auto.
 rewrite (match_specs_boundary p G loc); auto.
 omega.
Qed.

Lemma alloc: forall b, allocpool b = ((!! (b > 0) && mapsto b 0) * allocpool (S b)).
Proof.
 intros. apply pred_ext.
  intros w ?.
 destruct H as [H' H].
  destruct (deallocate w
                   (fun i => if lt_dec b i then NO else w @ i)
                   (fun i => if eq_dec b i then NO else w @ i)
               I I) as [w1 [w2 [? ?]]].
 intro l; specialize (H l).
 destruct (eq_dec b l). subst. rewrite if_false by omega. rewrite if_false in H by omega.
 rewrite H; constructor.
 destruct (lt_dec b l).
 rewrite if_false in H by omega.
 rewrite H; constructor.
 rewrite if_true in H.
 apply identity_unit_equiv in H. apply H.
 unfold adr in *; omega.
 exists w1; exists w2; split3; auto.
 split; auto.
 intro i. apply (resource_at_join _ _ _ i) in H0. specialize (H i). rewrite H1 in *.
 clear w1 H1.
 destruct (lt_dec b i).
 rewrite if_false by omega. apply NO_identity.
 destruct (eq_dec i b). subst. rewrite if_false in H by omega. auto.
 rewrite if_true in H. auto.
 unfold adr in *; omega.
 split. omega.
 intro i. apply (resource_at_join _ _ _ i) in H0. specialize (H i). rewrite H1 in *.
 clear w1 H1.
 destruct (lt_dec b i).
 rewrite if_false by omega. rewrite if_false in H by omega. rewrite H in H0. inv H0; auto.
 rewrite if_true by omega.
 destruct (eq_dec i b). subst. rewrite if_false in H by omega. rewrite H in H0; inv H0; auto.
 apply NO_identity. pfullshare_join.
 rewrite if_true in H by (unfold adr in *; omega).
 apply H in H0. rewrite H0; auto.

  intros w [w1 [w2 [? [? ?]]]].
  destruct H0 as [H0' H0]. destruct H1 as [_ H1].
 split; auto.
  intro i. specialize (H0 i); specialize (H1 i). apply (resource_at_join _ _ _ i) in H.
  destruct (lt_dec i b). rewrite if_true in H1 by omega.
  rewrite if_false in H0 by omega. apply H0 in H. rewrite <- H; auto.
  destruct (@eq_dec adr _ i b). subst. rewrite H0 in H. rewrite if_true in H1 by omega.
  apply join_comm in H. apply H1 in H. auto.
  rewrite if_false in H1. rewrite H1 in H. apply H0 in H. auto.
  unfold AV.address, AV0.address, adr in *. omega.
Qed.

Require msl.seplog msl.alg_seplog.
Definition mpred : Type := predicates_hered.pred rmap.
Instance Nm: seplog.NatDed mpred := alg_seplog.algNatDed rmap.
Instance Sm: seplog.SepLog mpred := alg_seplog.algSepLog rmap.
Instance Cm: seplog.ClassicalSep mpred := alg_seplog.algClassicalSep rmap.
Instance Im: seplog.Indir mpred := alg_seplog.algIndir rmap.
Instance Rm: alg_seplog.RecIndir mpred := alg_seplog.algRecIndir rmap.
Instance SIm: seplog.SepIndir mpred := alg_seplog.algSepIndir rmap.
Instance SRm: alg_seplog.SepRec mpred := alg_seplog.algSepRec rmap.

Definition guard (p: program) (G: funspecs) (vars: varset) (P : assert) (k: control) : pred nat :=
     ALL s:env, P s && funassert G >=> assert_safe p vars k s.

Record semaxArg :Type := SemaxArg {
 sa_vars: varset;
 sa_P: assert;
 sa_c: control
}.

Definition believe (semax: semaxArg -> pred nat)
      (p: program) (P: funspec) (f: adr) : pred nat :=
      EX k: list var * control,
        !!(table_get p f = Some k /\ length (fst k) = length (fst P) /\ list_norepet (fst k)) &&
      |> semax (SemaxArg (fst k) (fun s => call P (map s (fst k))) (snd k)).

Definition believe_all (semax: semaxArg -> pred nat) (G: funspecs) (p: program) (G': funspecs) : pred nat :=
  ALL v:adr, ALL args: list var, ALL P: assert,
     !! (table_get G' v = Some (args,P)) -->
     believe semax p (args, fun s => P s && funassert G) v.

Definition semax_ (semax: semaxArg -> pred nat) (a: semaxArg) : pred nat :=
 match a with SemaxArg vars P c =>
     ALL p: program, ALL G: funspecs, believe_all semax G p G --> guard p G vars P c
  end.

Lemma prop_imp {A}{agA: ageable A}:
  forall (P: Prop) (Q: pred A) w, (P -> app_pred Q w) -> app_pred (!!P --> Q) w.
Proof. repeat intro. specialize (H H1). eapply pred_nec_hereditary; eauto.
Qed.


Lemma HOcontractive_semax_ : HOcontractive semax_.
Proof.
  auto 50 with contractive.
Qed.

Definition semax'  := HORec semax_.

Lemma semax'_unfold: forall vars P c,
     semax' (SemaxArg vars P c) =
         ALL p: program, ALL G:funspecs, believe_all semax' G p G --> guard p G vars P c.
Proof.
  intros.
  unfold semax' at 1. rewrite HORec_fold_unfold; auto.
  apply HOcontractive_semax_.
Qed.

Definition semax vars (G: funspecs) (P: assert) (k: control) : Prop :=
       typecheck vars k = true /\ forall n,  semax' (SemaxArg vars (fun s => P s && funassert G) k) n.

Definition semax_func (G: funspecs) (p: program) (G': funspecs) :=
    match_specs p G' /\
    forall n, believe_all semax' G p G' n.

Lemma semax_func_nil: forall G, semax_func G nil nil.
Proof. split; repeat intro. constructor. inv H0. Qed.

Lemma semax_func_cons:
   forall  fs id f vars P (G G': funspecs),
      inlist id (map (@fst adr (list var * control)) fs) = false ->
      list_nodups vars = true ->
      length vars = length (fst P) ->
      semax vars G (fun s => call P (map s vars)) f ->
      semax_func G fs G' ->
      semax_func G ((id, (vars,f))::fs) ((id, P) :: G').
Proof.
intros until G'. intros H0 H Hlen ? ?.
apply inlist_notIn in H0.
destruct H2.
split.
constructor; auto.
destruct H1; auto.
intro.
specialize (H3 n).
intros b nargs' Q.
specialize (H3 b nargs' Q).
intros ? ? ?.
destruct (eq_dec id b).
subst.
Focus 2.
specialize (H3 _ H4).
spec H3.
clear - H5 n0.
hnf in H5|-*.
unfold table_get  in H5; fold @table_get in H5.
rewrite if_false in H5; auto.
clear H5.
destruct H3 as [k [? ?]]; exists k; split; auto.
unfold table_get; fold @table_get.
rewrite if_false; auto.
(* End Focus 2 *)
unfold table_get in H5; fold @table_get in H5.
rewrite if_true in H5; auto.
simpl in H5.
inv H5.
exists (vars,f).
split.
simpl.
rewrite if_true; auto. split; auto. split; auto. apply nodups_norepet. auto.
simpl fst; simpl snd.
hnf; intros.
destruct H1 as [_ H1].
specialize (H1 a'0).
replace (fun s : env =>
           call (nargs', fun s0 : env => Q s0 && funassert G) (map s vars))
 with (fun s : env => call (nargs', Q) (map s vars) && funassert G).
apply H1.
extensionality s. forget (map s vars) as vl.
clear.
apply pred_ext; intros ? ?.
destruct H as [[? ?] ?].
split. apply H. simpl snd in *. split; auto.
destruct H. simpl fst in *; simpl snd in *.
destruct H0; split; auto. split; auto.
Qed.

Lemma semax_G:
   forall vars G P c, semax vars G (fun s => P s && funassert G) c -> semax vars G P c.
Proof.
  intros. destruct H; split; auto.
  intro; specialize (H0 n).
  replace (fun s : env => P s && funassert G) with (fun s : env => P s && funassert G && funassert G);
       auto.
  extensionality s.
  rewrite andp_assoc. f_equal. apply andp_dup.
Qed.

Lemma semax_go:  forall vars G (P: funspec) x ys,
    typecheck vars (Go x ys) = true ->
    semax vars G (fun s => cont P (eval x s) && call P (eval_list ys s)) (Go x ys) .
Proof.
 intros. rename H into TC.
  split; auto.
   intro n; hnf.
   rewrite semax'_unfold.
  intros p G0.
  hnf. intros n' ? ?.
  clear n H.
  intros s w ? w' ?.
  rewrite andp_assoc.
  intros [[H4 H5] [_ GUARDIAN]].
  pose (H3:=True).
  clear G. rename G0 into G.
  remember (eval x s) as v'.
  destruct (funassert_get G v' P w') as [P' [H2 H2']].
  split; auto.
  generalize (H0 _ _ _ _ (necR_refl _) H2'); intro. clear H2'.
  destruct H6 as [[formals k] [[H6 [H6' H6'']] ?]].
  hnf in H6.
 rewrite semax'_unfold in H7.
  apply assert_safe0; intros w'' Hw''.
  assert (LATER: laterR n' (level w'')).
    apply later_nat; apply necR_level in H1; apply age_level in Hw''.
   unfold R.rmap in *; omega. specialize (H2 (eval_list ys s)).
  red in H2. red in H2. red in H2.
  specialize (H2 _ (t_step _ _ _ _ Hw'' )).
  specialize (H7 _ LATER).
  apply (pred_nec_hereditary _ _ _ (laterR_necR LATER)) in H0.
  specialize (H7 p G _ (necR_refl _) H0). clear H0.
  simpl fst in *. simpl snd in *.
  do 3 red in H2.
  apply (pred_hereditary _ _ _ Hw'') in H5.
  specialize (H2 _ (le_refl _)).
  specialize (H7 (locals2env (mk_locals formals (eval_list ys s))) _ (le_refl _) _ (necR_refl _)).
  clear n' H LATER.
  intros ? ? VC L H. rewrite <- L in *. clear L s. rename s' into s.
  assert (step p (s,h, Go x ys) = Some ((mk_locals formals (eval_list ys (locals2env s)), h), k)).
  simpl.
  simpl typecheck in TC.
  rewrite andb_true_iff in TC; destruct TC as [TC1 TC2].
  rewrite (eval_expr_get vars s h x); auto. rewrite <- Heqv'.
  simpl. rewrite H6.  simpl.
  rewrite (eval_expr_get_list vars s h ys); auto.
  rename Hw'' into H12.
  rewrite (age_level _ _ H12).
  rewrite (safeN_step _ _ _ _ H0).
  clear w H1.
  pose (H11:=True).
  spec H7.
  eapply pred_hereditary in GUARDIAN; eauto.
  split; auto.
  split.
  hnf. rewrite map_length. simpl fst. auto.
  split; auto.
  destruct H2 as [? _].
  specialize (H1 _ (necR_refl _) H5).
  simpl.
  unfold call in H1. simpl in H1.
  Transparent arguments.
  unfold arguments in *.
  Opaque arguments.
  replace (map (locals2env (mk_locals formals (eval_list ys (locals2env s)))) formals)
     with (eval_list ys (locals2env s)); [ apply H1 | ].
  destruct H5 as [Hlen H5]. hnf in Hlen.
  assert (length (eval_list ys (locals2env s)) = length formals).
    rewrite H6'. auto.
  forget (eval_list ys (locals2env s)) as vs.
  clear - H2 H6''.
  revert vs H2; induction H6''; intros; destruct vs; inv H2; simpl; auto.
  f_equal. unfold locals2env; simpl. rewrite if_true by auto. auto.
 pattern vs at 1; rewrite (IHH6'' vs) by auto.
 forget (mk_locals tl vs) as y.
 clear - H. induction tl; simpl; auto. f_equal; simpl.
 unfold locals2env; simpl.
 rewrite if_false by (contradict H; simpl in *; intuition). auto.
 apply IHtl. intuition.
  apply H7; auto.
  apply varcompat_mk_locals. unfold eval_list. rewrite map_length. rewrite H6'; auto.
  destruct H5 as [H5 _]; hnf in H5.
  rewrite <- H5.
  clear. induction ys; simpl; omega.
  eapply pred_hereditary; eauto.
Qed.

Lemma semax_assign: forall x y c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c ->
    semax vars G (fun s => |> subst x (eval y s) P s) (Do x := y ; c).
Proof.
 intros until P; intros TC [TC' ?].
 split.
 simpl in *. destruct y; inv TC; simpl; auto; try rewrite TC'; try rewrite H1; auto.
 intro; intros.
 unfold subst.
 rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [[H6 H6'] H4].
 pose (H5:=True).
 apply assert_safe0; intros w'' ?.
 intros s' h VC L ?. rewrite <- L in *; clear L s; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H9.
 apply (pred_hereditary _ _ _ H7) in H8.
 specialize (H6 _ (t_step _ _ _ _ H7)).
 apply (pred_hereditary _ _ _ H7) in H4.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 apply (pred_nec_hereditary _ _ _ H10) in H1.
 clear n' w H3 H2 H0 H10.
 hnf in H5.
 assert (step p ((s,h), Do (Var x) := y; c) = Some ((table_set x (eval y (locals2env s)) s, h), c)).
 simpl. rewrite (eval_expr_get vars s h y); auto.
 apply (safeN_step _ _ _ _ H0).
  specialize (H (@level _ ag_rmap w')). rewrite semax'_unfold in H.
 specialize (H p G' _ (necR_refl _) H1).
 specialize (H (locals2env (@table_set var _ EqDec_var x (eval y (locals2env s)) s))).
 specialize (H w''). spec H; [rewrite H9; omega | ].
 specialize (H _ (necR_refl _)).
 spec H. split; auto.
 replace  (locals2env (table_set x (eval y (locals2env s)) s))
   with (env_set (locals2env s) x (eval y (locals2env s))); auto.
  split; [ auto | eapply pred_hereditary; eauto].
  clear.
   extensionality i. unfold env_set. unfold locals2env at 3.
   destruct (eq_dec i x). subst. rewrite table_gss; auto. rewrite table_gso; auto.
 apply H; auto.
  clear - VC.
  intros i ?. destruct (eq_dec i x). subst. rewrite table_gss. congruence.
  rewrite table_gso by auto. apply (VC i).
  unfold vs_mem in H. apply ListSet.set_mem_correct1 in H.
  apply ListSet.set_mem_correct2. unfold vs_add in H.
  apply ListSet.set_add_elim2 in H; auto.
Qed.

Lemma semax_if: forall x c1 c2 vars G (P: assert),
    expcheck vars x = true ->
    semax vars G (fun s => !!(eval x s <> 0) && P s) c1 ->
    semax vars G (fun s => !! (eval x s = 0) && P s) c2 ->
    semax vars G P (If x Then c1 Else c2).
Proof.
 intros. rename H into TC.
 destruct H0 as [TC0 H]; destruct H1 as [TC1 H'].
 split.
 simpl; auto.
 intro.
 rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [H5 H4].
 pose (H6:=True).
 apply assert_safe0; intros w'' ?.
 intros s' h VC L ?. rewrite <- L in *; clear L s; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H9.
 destruct (eq_dec (eval x (locals2env s)) 0).
 (* zero *)
 clear H; rename H' into H.
 subst.
 assert (step p ((s,h), If x Then c1 Else c2) = Some ((s,h), c2)).
 simpl. rewrite (eval_expr_get vars s h x); auto.
 rewrite e; simpl; auto.
 apply (safeN_step _ _ _ _ H10).
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H11 (pred_nec_hereditary _ _ _ H11 H1)).
 specialize (H (locals2env s) w'').
 spec H. omega.
 specialize (H _ (necR_refl _)).
 spec H.
  rewrite andp_comm.
 split. eapply pred_hereditary; eauto.
 apply (pred_hereditary _ _ _ H7) in H5.
 rewrite andp_assoc; split; [ |  apply H5].
 hnf; auto.
 apply H; auto.
 apply (pred_nec_hereditary _ _ _ (rt_step _ _ _ _ H7)); auto.
 (* nonzero *)
 subst.
 assert (step p ((s,h), If x Then c1 Else c2) = Some ((s,h), c1)).
 simpl. rewrite (eval_expr_get vars s h x); auto. simpl.  rewrite if_false; auto.
 apply (safeN_step _ _ _ _ H10).
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H11 (pred_nec_hereditary _ _ _ H11 H1)).
 specialize (H (locals2env s) w'').
 spec H. omega.
 specialize (H _ (necR_refl _)).
 spec H.
 rewrite andp_comm.
 split. eapply pred_hereditary; eauto.
 apply (pred_hereditary _ _ _ H7) in H5.
 rewrite andp_assoc; split; [ |  apply H5].
 hnf; auto.
 apply H; auto.
 apply (pred_nec_hereditary _ _ _ (rt_step _ _ _ _ H7)); auto.
Qed.

Lemma semax_load: forall x y z c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c ->
    semax vars G (fun s => ((mapsto (eval y s) z) * TT) && |> subst x z P s)
               (Do x := Mem y ; c).
Proof.
 intros until P. intros TC [TC' ?].
 split.
 simpl; auto.
 intro n.
 rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [H5 H4].
 destruct H5 as [[? HP] HG].
 unfold subst in HP.
 apply assert_safe0; intros w'' H7.
 specialize (HP _ (t_step _ _ _ _ H7)).
 intros s' h VC L ?. rewrite <- L in *; clear s L; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H8.
 assert (step p ((s,h), Do x := Mem y; c) = Some ((table_set x z s, h), c)).
 simpl. rewrite (eval_expr_get vars s h y); auto. simpl.
 replace (heap_get h (eval y (locals2env s))) with (Some z).
 auto.
 symmetry.
 apply H6. apply mapsto_e1; auto.
 apply (safeN_step _ _ _ _ H9). clear H9.
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H9 (pred_nec_hereditary _ _ _ H9 H1)).
 specialize (H (locals2env (@table_set _ _ EqDec_var x z s)) w'').
 spec H.    unfold R.rmap in *; omega.
 specialize (H _ (necR_refl _)).
 spec H. split; [split|].
  rewrite locals2env_table_set. eauto.
  eapply pred_hereditary; eauto.
  eapply pred_hereditary; eauto.
 apply H; auto.
 apply varcompat_add; auto.
 eapply pred_hereditary; eauto.
Qed.

Lemma semax_store: forall x y v c vars G (P: assert),
    expcheck vars x = true ->
    expcheck vars y = true ->
    semax vars G (fun s => mapsto (eval x s) (eval y s) * P s) c ->
    semax vars G (fun s => mapsto (eval x s) v  * P s)  (Do Mem x  := y ; c).
Proof.
 intros until P; intros TCx TCy [TC ?].
 split.
 simpl; auto.
 intro. rewrite semax'_unfold.
 intros p G' n' ? ? s w ? w' ? [[H5 H6] H4].
 apply assert_safe0; intros w'' ?.
 intros s' h VC L ?. rewrite <- L in *; clear L s; rename s' into s.
 generalize (age_level _ _ H7); intro. rewrite H9.
 assert (step p ((s,h), Do Mem x := y; c) = Some ((s, heap_set (eval x (locals2env s)) (eval y (locals2env s)) h), c)).
 simpl. rewrite (eval_expr_get vars s h y); auto. rewrite (eval_expr_get vars s h x); auto.
 apply (safeN_step _ _ _ _ H10).
 specialize (H n'). rewrite semax'_unfold in H.
 assert (necR n' (level w')). apply necR_trans with (level w); auto.
 apply nec_nat. auto. apply necR_level'. auto.
 specialize (H p G' _ H11 (pred_nec_hereditary _ _ _ H11 H1)).
 apply (pred_hereditary _ (level w') (level w'')) in H;
   [ |  apply age_level in H7; rewrite H7; hnf; simpl; auto].
 apply (pred_hereditary _ _ _ H7) in H5.
 apply (pred_hereditary _ _ _ H7) in H6.
 apply (pred_hereditary _ _ _ H7) in H4.
 apply (pred_hereditary _ _ _ H7) in H8.
 clear H1; pose (H1:=True). clear n H0. pose (H0:=True).
 clear n' H2 H11. pose (H2:=True). pose (H11:=True).
 simpl in H8.
clear w' H7 H9 H3.
 pose (H7:=True); pose (H9:=True); pose (H3:=True).
 clear H0 H1.
 destruct H5 as [wa [wb [H0 [HP H1]]]].
 pose (m' := singleton_rmap (eval x (locals2env s)) (eval y (locals2env s)) w'').
 assert (joins m' wb).
 apply resource_at_joins2. unfold m'.
 rewrite singleton_rmap_level.
 apply join_level in H0. destruct H0. auto.
 unfold m'. intro i.
 clear - HP H0.
 apply (resource_at_join _ _ _ i) in H0.
 specialize (HP i).
 unfold singleton_rmap. rewrite resource_at_make_rmap.
 destruct (eq_dec i (eval x (locals2env s))). subst; rewrite if_true in HP; auto.
 exists (YES pfullshare (VAL (eval y (locals2env s))) NoneP).
 rewrite HP in *. inv H0; try pfullshare_join. constructor.
 rewrite if_false in HP by auto.
 exists (wb @ i).
 apply HP in H0. rewrite H0.
 rewrite <- core_resource_at. apply core_unit.
 destruct H5 as [ww H12].
 replace (level w'') with (level ww) in H.
 Focus 2.
 transitivity (level wb).
 apply join_level in H12. destruct H12 as [H12 H13]. symmetry ; apply H13.
 apply join_level in H0; destruct H0; auto.
 specialize (H (locals2env s) ww).
 spec H. simpl. apply le_refl.
 specialize (H _ (necR_refl _)).
 spec H. rewrite andp_assoc. rewrite andp_comm.
 clear - H4 H0 HP H12 H6 H1.
 assert (app_pred ((mapsto (eval x (locals2env s)) v * TT) && (funassert G && funassert G')) w'').
 split; auto. exists wa; exists wb; split3; auto. split; auto.
 destruct H as [? _].
 split.
 apply join_comm in H0. apply join_comm in H12. apply join_core in H0. apply join_core in H12.
 apply funassert_core in H6. apply funassert_core in H4. rewrite H12 in H0.
 split; apply funassert_core; rewrite H0; auto.
 destruct H as [wa' [wb' [? [? ?]]]].
 assert (wa' = wa). eapply mapsto_uniq; eauto.
 apply join_core in H0; apply join_core in H. rewrite H0; rewrite H. auto.
 subst wa'. generalize (join_canc (join_comm H0) (join_comm H)); intro; subst wb'.
  generalize (singleton_rmap_mapsto (eval x (locals2env s)) (eval y (locals2env s)) w''); intro.
 assert (app_pred (mapsto (eval x (locals2env s)) (eval y (locals2env s)) * (TT && (funassert G && funassert G'))) ww).
 exists m'; exists wb; split3; auto.
 split; auto.
 apply join_comm in H0. apply join_comm in H12. apply join_core in H0. apply join_core in H12.
  apply funassert_core in H6. apply funassert_core in H4.
 split; apply funassert_core; rewrite H0; auto.
 exists m'; exists wb; split3; auto.
 replace (level w'') with (level ww).
 Focus 2. simpl. transitivity (level wb).
 clear - H12; apply join_level in H12; destruct H12; symmetry; apply H0.
 clear - H0; apply join_level in H0; destruct H0; apply H0.
 apply H; auto.
 intros i v0. specialize (HP i).
 simpl.
 apply (resource_at_join _ _ _ i) in H12.
 unfold m' in *; clear m'.
 unfold singleton_rmap in H12.
 rewrite resource_at_make_rmap in H12.
 change AV.address with adr in H12.
  specialize (H8 i v0). simpl in H8.

  destruct (eq_dec i (eval x (locals2env s))).
  subst. rewrite heap_gss.
  apply join_unit2_e in H12. rewrite <- H12.
  split; intro Hx; inv Hx; auto.
  apply YES_join_full in H12; auto.
  rewrite H12. apply NO_identity.
  apply join_unit1_e in H12; [ | rewrite <- core_resource_at; apply core_identity].
  rewrite heap_gso; auto.
 apply (resource_at_join _ _ _ i) in H0.
 rewrite <- H12.
 apply HP in H0. rewrite H0; auto.
Qed.

Lemma semax_pre:
  forall P P' vars G c, (forall s, P s |-- P' s) -> semax vars G P' c -> semax vars G P c.
Proof.
 intros. destruct H0 as [TC H0]; split; auto.
 intro n; specialize (H0 n).
 rewrite semax'_unfold in *.
 intros p G'. specialize (H0 p G').
 intros n' ? ?. specialize (H0 _ H1 H2).
 intros s w ? ? ? ?. specialize (H0 s _ H3 _ H4).
 apply H0.
 destruct H5; split; auto. destruct H5;  split; auto. apply H; auto.
Qed.


Lemma semax_exp: forall {A} vars G (P: A -> assert) c,
    typecheck vars c = true ->
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => EX v:A, (P v s)) c.
Proof.
 intros ? ? ? ? ? TC ?.
 split; auto.
 intro.
 rewrite semax'_unfold.
 intros p G'. intros n' ? ?.
 intros s. intros ? ?. intros ? ?. intros [[[v ?] ?] ?].
 specialize (H v). destruct H as [_ H].
 rewrite semax'_unfold in H. eapply H; eauto. split; auto. split; auto.
Qed.

Lemma semax_exp': forall {A} (any: A) vars G (P: A -> assert) c,
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => EX v:A, (P v s)) c.
Proof.
 intros ? ? ? ? ? ?.
 split; auto.
 destruct (H any); auto.
 intro.
 rewrite semax'_unfold.
 intros p G'. intros n' ? ?.
 intros s. intros ? ?. intros ? ?. intros [[[v ?] ?] ?].
 specialize (H v). destruct H as [_ H].
 rewrite semax'_unfold in H. eapply H; eauto. split; auto. split; auto.
Qed.

Lemma semax_prop:
  forall (R: Prop) vars G P c,
      typecheck vars c = true ->
      (R -> semax vars G P c) ->
      semax vars G (fun s => !! R && P s) c.
Proof.
  intros R vars G P c TC ?. split; auto. intro n.  rewrite semax'_unfold. intros p G'.
  intros n' ? ? b w ? w' ? [[[? ?] ?] ?].
  destruct (H H4).
  specialize (H9 n). rewrite semax'_unfold in H9.
  eapply H9; eauto. split; auto. split; auto.
Qed.

Definition program_proved (p: program) :=
   exists G, semax_func G p G  /\ table_get G 0 = Some (0::nil, fun s => allocpool (eval (Var 0) s)).

Lemma semax_sound:
  forall p, program_proved p -> forall n, run p n <> None.
Proof.
  intros.
  destruct H as [G [[? ?] ?]].
  generalize (funassert_make_world p G n); intro.
  destruct (semax_go nil G  (0::nil, fun s => allocpool (eval (Var 0) s))
                (Const 0) (Const (boundary p) :: nil) (eq_refl _)) as [_ ?].
  specialize (H3 n).
  rewrite semax'_unfold in H3.
  specialize (H3 p G _ (necR_refl _) (H0 _) (locals2env nil)
                    (make_world G (initial_heap p) n)).
  spec H3. rewrite level_make_world. auto.
  specialize (H3 _ (necR_refl _)).
  spec H3.
  split; auto.
  split; auto.
  split.
  apply (funassert_e _ _ _ H1 _ H2).
  unfold call.
  Transparent arguments. unfold arguments. Opaque arguments.
  simpl snd.
  unfold locals2env, table_get. rewrite if_true; auto.
  split. simpl; auto.
  apply allocpool_make_world; auto.
  hnf in H3.
  specialize (H3 nil (initial_heap p)).
  spec H3. intros i ?. inv H4.
  spec H3. auto.
  spec H3. apply cohere_make_world; auto.
  unfold run; intro.
  destruct H3 as [sk' ?].
  rewrite level_make_world in H3.
 unfold locals,table, var,adr in H3,H4. rewrite H3 in H4; inv H4.
Qed.

End Semax.
