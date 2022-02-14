Require Import VST.msl.predicates_hered.
Require Import VST.veric.ghosts.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.ageable.
Require Import VST.msl.age_sepalg.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Import FashNotation.
Import LiftNotation.
Import compcert.lib.Maps.

Require Import VST.concurrency.conclib_coqlib.
Require Import VST.concurrency.conclib_sublist.

(* rewrite is really annoying to fix in a backwards compatible way so just set the option. *)
Local Set Apply With Renaming.

(* general list lemmas *)
Notation vint z := (Vint (Int.repr z)).
Notation vptrofs z := (Vptrofs (Ptrofs.repr z)).


Lemma repable_0 : repable_signed 0.
Proof.
  split; computable.
Qed.
#[export] Hint Resolve repable_0 : core.


Open Scope logic.

Lemma iter_sepcon_sepcon: forall {A} f g1 g2 l, (forall b : A, f b = g1 b * g2 b) ->
  iter_sepcon f l = iter_sepcon g1 l * iter_sepcon g2 l.
Proof.
  intros; induction l; simpl.
  autorewrite with norm; auto.
  rewrite H, IHl; apply pred_ext; cancel.
Qed.

Lemma sepcon_app : forall l1 l2, fold_right sepcon emp (l1 ++ l2) =
  fold_right sepcon emp l1 * fold_right sepcon emp l2.
Proof.
  induction l1; simpl; intros.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

Lemma sepcon_rev : forall l, fold_right sepcon emp (rev l) = fold_right sepcon emp l.
Proof.
  induction l; simpl; auto.
  rewrite sepcon_app; simpl.
  rewrite sepcon_emp, sepcon_comm, IHl; auto.
Qed.


Lemma iter_sepcon_sepcon': forall {A} g1 g2 (l : list A),
  iter_sepcon (fun x => g1 x * g2 x) l = iter_sepcon g1 l * iter_sepcon g2 l.
Proof.
  intros. apply iter_sepcon_sepcon. easy.
Qed.

Lemma iter_sepcon_derives : forall {B} f g (l : list B), (forall x, In x l -> f x |-- g x) -> iter_sepcon f l |-- iter_sepcon g l.
Proof.
  induction l; simpl; auto; intros.
  apply sepcon_derives; auto.
Qed.


Lemma list_join_eq : forall (b : list share) a c c'
  (Hc : sepalg_list.list_join a b c) (Hc' : sepalg_list.list_join a b c'), c = c'.
Proof.
  induction b; intros; inv Hc; inv Hc'; auto.
  assert (w0 = w1) by (eapply sepalg.join_eq; eauto).
  subst; eapply IHb; eauto.
Qed.

Lemma readable_share_list_join : forall sh shs sh', sepalg_list.list_join sh shs sh' ->
  readable_share sh \/ Exists readable_share shs -> readable_share sh'.
Proof.
  induction 1; intros [? | Hexists]; try inv Hexists; auto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
Qed.


Lemma make_tycontext_s_distinct : forall a l (Ha : In a l) (Hdistinct : NoDup (map fst l)),
  (make_tycontext_s l) ! (fst a) = Some (snd a).
Proof.
  intros a l. unfold make_tycontext_s.
  induction l; simpl; intros. 
  contradiction.
  inv Hdistinct. destruct a0. simpl in *.
  destruct Ha. subst.
  simpl. rewrite PTree.gss. auto.
  rewrite PTree.gso.
  apply IHl; auto.
  intro; subst.
  apply H1; apply in_map. auto.
Qed.

Lemma lookup_distinct : forall {A B} (f : A -> B) a l t (Ha : In a l) (Hdistinct : NoDup (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! (fst a) =
  Some (f (snd a)).
Proof.
  induction l; simpl; intros; [contradiction|].
  inv Hdistinct.
  rewrite PTree.gsspec.
  destruct (peq (fst a) (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - destruct Ha; [subst; auto|].
    contradiction H1; rewrite in_map_iff; eauto.
  - apply IHl; auto.
    destruct Ha; auto; subst.
    contradiction n; auto.
Qed.

Lemma lookup_out : forall {A B} (f : A -> B) a l t (Ha : ~In a (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! a = t ! a.
Proof.
  induction l; simpl; intros; auto.
  rewrite PTree.gsspec.
  destruct (peq a (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - contradiction Ha; auto.
  - apply IHl.
    intro; contradiction Ha; auto.
Qed.


(* various seplog lemmas *)
(* wand lemmas *)
Lemma wand_eq : forall P Q R, P = Q * R -> P = Q * (Q -* P).
Proof.
  intros.
  apply seplog.pred_ext, modus_ponens_wand.
  subst; cancel.
  rewrite <- wand_sepcon_adjoint; auto.
  rewrite sepcon_comm; auto.
Qed.

Lemma wand_twice : forall P Q R, P -* Q -* R = P * Q -* R.
Proof.
  intros; apply seplog.pred_ext.
  - rewrite <- wand_sepcon_adjoint.
    rewrite <- sepcon_assoc, wand_sepcon_adjoint.
    rewrite sepcon_comm; apply modus_ponens_wand.
  - rewrite <- !wand_sepcon_adjoint.
    rewrite sepcon_assoc, sepcon_comm; apply modus_ponens_wand.
Qed.

Lemma wand_frame : forall P Q R, P -* Q |-- P * R -* Q * R.
Proof.
  intros.
  rewrite <- wand_sepcon_adjoint; cancel.
  rewrite sepcon_comm; apply modus_ponens_wand.
Qed.

Lemma data_at__eq : forall {cs : compspecs} sh t p, data_at_ sh t p = data_at sh t (default_val t) p.
Proof.
  intros; unfold data_at_, data_at, field_at_; auto.
Qed.

Lemma func_tycontext_sub : forall f V G A V2 G2 (HV : incl V V2) (HG : incl G G2)
  (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  tycontext_sub (func_tycontext f V G A) (func_tycontext f V2 G2 A).
Proof.
  intros.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  apply NoDup_app in Hdistinct; destruct Hdistinct as (? & ? & Hdistinct); auto.
  repeat split; auto; intro.
  - destruct (PTree.get _ _); auto.
  - unfold make_tycontext_g.
    revert dependent G2; revert dependent V2; revert V; induction G; simpl.
    + induction V; simpl; intros. auto.
        rewrite incl_cons_iff in HV; destruct HV.
        rewrite PTree.gsspec.
        destruct (peq id (fst a)); eauto; subst; simpl.
        rewrite lookup_out.
        apply lookup_distinct with (f0:=@id type); auto.
        { apply Hdistinct.
          rewrite in_map_iff; eexists; split; eauto. }
    + intros.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      destruct (peq id (fst a)); eauto; subst; simpl.
      apply lookup_distinct; auto.
  - unfold make_tycontext_s.
    revert dependent G2; induction G; simpl; intros.
    + auto.
    + destruct a; simpl. hnf.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      fold make_tycontext_s in *.
      destruct (peq id i); eauto; subst; simpl.
      * exists f0; split; [ | apply funspec_sub_si_refl].
        apply make_tycontext_s_distinct with (a:=(i,f0)); auto.
      * apply IHG; auto.
  - apply Annotation_sub_refl.
Qed.

(* This lets us use a library as a client. *)
(* We could also consider an alpha-renaming axiom, although this may be unnecessary. *)
Lemma semax_body_mono : forall V G {cs : compspecs} f s V2 G2
  (HV : incl V V2) (HG : incl G G2) (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  semax_body V G f s -> semax_body V2 G2 f s.
Proof.
  unfold semax_body; intros.
  destruct s, f0.
  destruct H as [H' [H'' H]]; split3; auto.
  intros; eapply semax_Delta_subsumption, H.
  apply func_tycontext_sub; auto.
Qed.


Lemma comp_join_top : forall sh, sepalg.join sh (Share.comp sh) Tsh.
Proof.
  intro; pose proof (Share.comp1 sh).
  apply comp_parts_join with (L := sh)(R := Share.comp sh); auto;
    rewrite Share.glb_idem, Share.glb_top.
  - rewrite Share.comp2. apply join_bot_eq.
  - rewrite Share.glb_commute, Share.comp2; auto.
Qed.

#[export] Hint Resolve bot_unreadable : share.

Lemma readable_not_bot : forall sh, readable_share sh -> ~sh = Share.bot.
Proof.
  repeat intro; subst; auto with share.
Qed.
#[export] Hint Resolve unreadable_bot : core.

#[export] Hint Resolve readable_not_bot : share.

Definition join_Bot := join_Bot.
Definition join_Tsh := join_Tsh.

(* It's often useful to split Tsh in half. *)
Definition gsh1 := fst (slice.cleave Tsh).
Definition gsh2 := snd (slice.cleave Tsh).

Lemma readable_gsh1 : readable_share gsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_gsh2 : readable_share gsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma gsh1_gsh2_join : sepalg.join gsh1 gsh2 Tsh.
Proof.
  apply slice.cleave_join; unfold gsh1, gsh2; destruct (slice.cleave Tsh); auto.
Qed.

#[export] Hint Resolve readable_gsh1 readable_gsh2 gsh1_gsh2_join : core.

Lemma gsh1_not_bot : gsh1 <> Share.bot.
Proof.
  intro X; contradiction unreadable_bot; rewrite <- X; auto with share.
Qed.

Lemma gsh2_not_bot : gsh2 <> Share.bot.
Proof.
  intro X; contradiction unreadable_bot; rewrite <- X; auto with share.
Qed.
#[export] Hint Resolve gsh1_not_bot gsh2_not_bot : core.

(*
Lemma data_at_Tsh_conflict : forall {cs : compspecs} sh t v v' p, sepalg.nonidentity sh -> 0 < sizeof t ->
  data_at Tsh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  assert_PROP (field_compatible t [] p) by entailer!.
  pose proof (comp_join_top sh).
  erewrite <- data_at_share_join by eauto.
  rewrite sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl | rewrite FF_sepcon; auto].
  apply data_at_conflict; auto.
  split; auto.
  unfold field_compatible in *; tauto.
Qed.
*)

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Proof.
  intros.
  pose proof (slice.cleave_readable1 _ H); pose proof (slice.cleave_readable2 _ H).
  destruct (slice.cleave sh) as (sh1, sh2) eqn: Hsplit.
  exists sh1, sh2; split; [|split]; auto.
  replace sh1 with (fst (slice.cleave sh)) by (rewrite Hsplit; auto).
  replace sh2 with (snd (slice.cleave sh)) by (rewrite Hsplit; auto).
  apply slice.cleave_join; auto.
Qed.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.


Lemma iter_sepcon_Znth: forall {A} {d : Inhabitant A} f (l : list A) i, 0 <= i < Zlength l ->
  iter_sepcon f l = f (Znth i l) * iter_sepcon f (remove_Znth i l).
Proof.
  intros; unfold remove_Znth.
  rewrite <- sublist_same at 1 by auto.
  rewrite sublist_split with (mid := i) by lia.
  rewrite sublist_next with (i0 := i) by lia.
  rewrite !iter_sepcon_app; simpl; apply pred_ext; cancel.
Qed.

Lemma iter_sepcon2_Znth: forall {A B} {d1 : Inhabitant A} {d2 : Inhabitant B}
  f (l1 : list A) (l2 : list B) i, 0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
  iter_sepcon2 f l1 l2 =
  f (Znth i l1) (Znth i l2) * iter_sepcon2 f (remove_Znth i l1) (remove_Znth i l2).
Proof.
  intros; rewrite !iter_sepcon2_spec.
  apply pred_ext; Intros l; subst.
  - rewrite Zlength_map in *.
    rewrite !remove_Znth_map, !Znth_map, iter_sepcon_Znth with (i0 := i) by auto.
    unfold uncurry at 1.
    Exists (remove_Znth i l); entailer!.
  - Exists (combine l1 l2).
    rewrite combine_fst, combine_snd
      by (rewrite <- !ZtoNat_Zlength; apply Nat2Z.inj; rewrite !Z2Nat.id; lia).
    rewrite iter_sepcon_Znth with (i0 := i)(l0 := combine _ _)
      by (rewrite Zlength_combine, Z.min_l; lia).
    rewrite Znth_combine, remove_Znth_combine by auto.
    rewrite H1, H2, combine_eq; unfold uncurry; entailer!.
    apply derives_refl.
Qed.

Lemma iter_sepcon_Znth_remove : forall {A} {d : Inhabitant A} f l i j,
  0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j ->
  iter_sepcon f (remove_Znth j l) =
  f (Znth i l) * iter_sepcon f (remove_Znth (if zlt i j then i else i - 1) (remove_Znth j l)).
Proof.
  intros ?????? Hi Hj Hn.
  pose proof (Zlength_remove_Znth _ _ Hj) as Hlen.
  unfold remove_Znth at 1 2; rewrite Hlen.
  unfold remove_Znth in *.
  if_tac.
  - rewrite -> !sublist_app by (rewrite -> ?Zlength_app in *; lia).
    autorewrite with sublist.
    rewrite -> (sublist_split 0 i j) by lia.
    rewrite !iter_sepcon_app.
    rewrite -> (sublist_next i _) by lia; simpl.
    replace (Zlength l - _ - _ + _) with (Zlength l) by lia.
    apply pred_ext; cancel.
  - rewrite -> !sublist_app by (rewrite -> ?Zlength_app in *; lia).
    autorewrite with sublist.
    rewrite -> (sublist_split (j + 1) i (Zlength l)) by lia.
    rewrite !iter_sepcon_app.
    rewrite -> (sublist_next i _) by lia; simpl.
    replace (Zlength l - _ - _ + _) with (Zlength l) by lia.
    replace (i - _ - _ + _) with i by lia.
    replace (i - _ + _) with (i + 1) by lia.
    apply pred_ext; cancel.
Qed.

Lemma iter_sepcon_Znth' : forall {A} {d : Inhabitant A} (f : A -> mpred) l i,
  0 <= i < Zlength l -> iter_sepcon f l = f (Znth i l) * (f (Znth i l) -* iter_sepcon f l).
Proof.
  intros; eapply wand_eq, iter_sepcon_Znth; auto.
Qed.

Lemma iter_sepcon_remove_wand : forall {A} {d : Inhabitant A} (f : A -> mpred) l i,
  0 <= i < Zlength l -> iter_sepcon f (remove_Znth i l) |-- f (Znth i l) -* iter_sepcon f l.
Proof.
  intros; rewrite <- wand_sepcon_adjoint.
  erewrite iter_sepcon_Znth with (l0 := l) by eauto; cancel.
Qed.

Lemma iter_sepcon_In : forall {B} (x : B) f l, In x l -> iter_sepcon f l = f x * (f x -* iter_sepcon f l).
Proof.
  intros.
  apply (@In_Znth _ x) in H as (? & ? & Heq).
  rewrite <- Heq; apply iter_sepcon_Znth'; auto.
Qed.

Lemma join_shares_nth : forall shs sh1 sh i, sepalg_list.list_join sh1 shs sh -> 0 <= i < Zlength shs ->
  exists sh', sepalg_list.list_join (Znth i shs) (remove_Znth i shs) sh' /\ sepalg.join sh1 sh' sh.
Proof.
  induction shs; simpl; intros.
  { rewrite Zlength_nil in *; lia. }
  inv H.
  destruct (eq_dec i 0).
  - subst; rewrite remove_Znth0, sublist_1_cons, Zlength_cons, sublist_same, Znth_0_cons; auto; try lia.
    eapply sepalg_list.list_join_assoc1; eauto.
  - rewrite Zlength_cons in *; exploit (IHshs w1 sh (i - 1)); auto; try lia.
    intros (sh2 & ? & ?).
    rewrite Znth_pos_cons, remove_Znth_cons; try lia.
    exploit (sepalg.join_sub_joins_trans(a := a)(b := sh2)(c := w1)); eauto.
    { eexists; eapply sepalg.join_comm; eauto. } {eexists; eauto. }
    intros (sh' & ?); exists sh'; split.
    + exploit (sepalg_list.list_join_assoc2(a := a)(b := Znth (i - 1) shs)
        (cl := remove_Znth (i - 1) shs)(e := sh')(f := sh2)); auto.
      intros (d & ? & ?). apply sepalg.join_comm in H3.
      econstructor; eauto.
    + pose proof (sepalg.join_assoc(a := sh1)(b := a)(c := sh2)(d := w1)(e := sh)) as X.
      repeat match goal with X : ?a -> _, H : ?a |- _ => specialize (X H) end.
      destruct X as (f & Ha' & ?).
      assert (f = sh') by (eapply sepalg.join_eq; eauto).
      subst; auto.
Qed.

Lemma list_join_comm : forall (l1 l2 : list share) a b, sepalg_list.list_join a (l1 ++ l2) b ->
  sepalg_list.list_join a (l2 ++ l1) b.
Proof.
  induction l1; intros; [rewrite app_nil_r; auto|].
  inversion H as [|????? H1 H2]; subst.
  apply IHl1, sepalg_list.list_join_unapp in H2.
  destruct H2 as (c & Hl2 & Hl1).
  apply sepalg.join_comm in H1.
  destruct (sepalg_list.list_join_assoc1 H1 Hl2) as (? & ? & ?).
  eapply sepalg_list.list_join_app; eauto.
  apply sepalg.join_comm in H2. econstructor; eauto.
Qed.

(* Split a share into an arbitrary number of subshares. *)
Lemma split_shares : forall n sh, readable_share sh ->
  exists sh1 shs, Zlength shs = Z.of_nat n /\ readable_share sh1 /\ Forall readable_share shs /\
                  sepalg_list.list_join sh1 shs sh.
Proof.
  induction n; intros.
  - exists sh, []; repeat split; auto.
    apply sepalg_list.fold_rel_nil.
  - destruct (split_readable_share _ H) as (sh1 & sh2 & H1 & ? & ?).
    destruct (IHn _ H1) as (sh1' & shs & ? & ? & ? & ?).
    exists sh1', (shs ++ [sh2]).
    rewrite Nat2Z.inj_succ, Zlength_app, Zlength_cons, Zlength_nil; split; [lia|].
    rewrite Forall_app; repeat split; auto.
    eapply sepalg_list.list_join_app; eauto.
    rewrite <- sepalg_list.list_join_1; auto.
Qed.

Lemma data_at_shares_join : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh),
  @data_at cs sh1 t v p * iter_sepcon (fun sh => data_at sh t v p) shs =
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    erewrite <- sepcon_assoc, data_at_share_join; eauto.
Qed.

Lemma data_at_shares_join_old : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh),
  @data_at cs sh1 t v p * fold_right sepcon emp (map (fun sh => data_at sh t v p) shs) =
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    erewrite <- sepcon_assoc, data_at_share_join; eauto.
Qed.


(* These lemmas should probably be in veric. *)
Lemma exp_comm : forall {A B} P,
  (EX x : A, EX y : B, P x y) = EX y : B, EX x : A, P x y.
Proof.
  intros; apply seplog.pred_ext; Intros x y; Exists y x; auto.
Qed.

Lemma mapsto_value_eq: forall sh1 sh2 t p v1 v2, readable_share sh1 -> readable_share sh2 ->
  v1 <> Vundef -> v2 <> Vundef -> mapsto sh1 t p v1 * mapsto sh2 t p v2 |-- !!(v1 = v2).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try solve [entailer!].
  destruct (type_is_volatile t); try solve [entailer!].
  destruct p; try solve [entailer!].
  destruct (readable_share_dec sh1); [|contradiction n; auto].
  destruct (readable_share_dec sh2); [|contradiction n; auto].

  Transparent mpred.
  rewrite !prop_false_andp with (P := v1 = Vundef), !orp_FF; auto; Intros.
  rewrite !prop_false_andp with (P := v2 = Vundef), !orp_FF; auto; Intros.
  Opaque mpred.
  constructor; apply res_predicates.address_mapsto_value_cohere.
Qed.

Lemma mapsto_value_cohere: forall sh1 sh2 t p v1 v2, readable_share sh1 ->
  mapsto sh1 t p v1 * mapsto sh2 t p v2 |-- mapsto sh1 t p v1 * mapsto sh2 t p v1.
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try simple apply derives_refl.
  destruct (type_is_volatile t); try simple apply derives_refl.
  destruct p; try simple apply derives_refl.
  destruct (readable_share_dec sh1); [|contradiction n; auto].
  destruct (eq_dec v1 Vundef).
  Transparent mpred.
  - subst; rewrite !prop_false_andp with (P := tc_val t Vundef), !FF_orp, prop_true_andp; auto;
      try apply tc_val_Vundef.
    cancel.
    rewrite prop_true_andp with (P := Vundef = Vundef); auto.
    if_tac.
    + apply orp_left; Intros; auto.
      Exists v2; auto.
    + Intros. apply andp_right; auto. apply prop_right; split; auto. hnf; intros. contradiction H3; auto.
  - rewrite !prop_false_andp with (P := v1 = Vundef), !orp_FF; auto; Intros.
    apply andp_right; [apply prop_right; auto|].
    if_tac.
    eapply derives_trans with (Q := _ * EX v2' : val,
      res_predicates.address_mapsto m v2' _ _);
      [apply sepcon_derives; [apply derives_refl|]|].
    + destruct (eq_dec v2 Vundef).
      * subst; rewrite prop_false_andp with (P := tc_val t Vundef), FF_orp;
          try apply tc_val_Vundef.
        rewrite prop_true_andp with (P := Vundef = Vundef); auto.  apply derives_refl.
      * rewrite prop_false_andp with (P := v2 = Vundef), orp_FF; auto; Intros.
        Exists v2; auto.
    + Intro v2'.
      assert_PROP (v1 = v2') by (constructor; apply res_predicates.address_mapsto_value_cohere).
      subst. apply sepcon_derives; auto. apply andp_right; auto.
      apply prop_right; auto.
    + apply sepcon_derives; auto.
      Intros. apply andp_right; auto.
      apply prop_right; split; auto.
      intro; auto. 
Opaque mpred.
Qed.

Lemma struct_pred_value_cohere : forall {cs : compspecs} m sh1 sh2 p t f off v1 v2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (IH : Forall (fun it : member => forall v1 v2 (p : val),
        readable_share sh1 -> readable_share sh2 ->
        data_at_rec sh1 (t it) v1 p * data_at_rec sh2 (t it) v2 p |--
        data_at_rec sh1 (t it) v1 p * data_at_rec sh2 (t it) v1 p) m),
  struct_pred m (fun (it : member) v =>
    withspacer sh1 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh1 (t it) v) (f it))) v1 p *
  struct_pred m (fun (it : member) v =>
    withspacer sh2 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh2 (t it) v) (f it))) v2 p |--
  struct_pred m (fun (it : member) v =>
    withspacer sh1 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh1 (t it) v) (f it))) v1 p *
  struct_pred m (fun (it : member) v =>
    withspacer sh2 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh2 (t it) v) (f it))) v1 p.
Proof.
  intros.
  revert v1 v2; induction m; auto; intros.
  apply derives_refl.
  inv IH.
  destruct m.
  - unfold withspacer, at_offset; simpl.
    if_tac; auto.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [cancel|] end.
    eapply derives_trans; [apply sepcon_derives, derives_refl|].
    { apply H1; auto. }
    cancel.
  - rewrite !struct_pred_cons2.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [cancel|] end.
    match goal with |- _ |-- (?P1 * ?Q1) * (?P2 * ?Q2) => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [|cancel] end.
    apply sepcon_derives; [|auto].
    unfold withspacer, at_offset; simpl.
    if_tac; auto.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [cancel|] end.
    eapply derives_trans; [apply sepcon_derives, derives_refl|].
    { apply H1; auto. }
    cancel.
Qed.

Lemma data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_cohere; auto.
Qed.

Lemma data_at_array_value_cohere : forall {cs : compspecs} sh1 sh2 t z a v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 (Tarray t z a) v1 p * data_at sh2 (Tarray t z a) v2 p |--
  data_at sh1 (Tarray t z a) v1 p * data_at sh2 (Tarray t z a) v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !data_at_rec_eq; simpl.
  unfold array_pred, aggregate_pred.array_pred; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite Z.sub_0_r in *.
  erewrite aggregate_pred.rangespec_ext by (intros; rewrite Z.sub_0_r; apply f_equal; auto).
  setoid_rewrite aggregate_pred.rangespec_ext at 2; [|intros; rewrite Z.sub_0_r; apply f_equal; auto].
  setoid_rewrite aggregate_pred.rangespec_ext at 4; [|intros; rewrite Z.sub_0_r; apply f_equal; auto].
  clear H3 H4.
  rewrite Z2Nat_max0 in *.
  forget (offset_val 0 p) as p'; forget (Z.to_nat z) as n; forget 0 as lo; revert dependent lo; induction n; auto; simpl; intros.
 apply derives_refl.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ =>
    eapply derives_trans with (Q := (P1 * P2) * (Q1 * Q2)); [cancel|] end.
  eapply derives_trans; [apply sepcon_derives|].
  - unfold at_offset.
    rewrite 2by_value_data_at_rec_nonvolatile by auto.
    apply mapsto_value_cohere; auto.
  - apply IHn.
  - unfold at_offset; rewrite 2by_value_data_at_rec_nonvolatile by auto; cancel.
Qed.

(* This isn't true if the type contains any unions, since in fact the type of the data could be different.
Lemma data_at_rec_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  data_at_rec sh1 t v1 p * data_at_rec sh2 t v2 p |--
  data_at_rec sh1 t v1 p * data_at_rec sh2 t v1 p.
Proof.
  intros until t; type_induction.type_induction t; intros; rewrite !data_at_rec_eq; simpl; auto;
    try solve [destruct (type_is_volatile _); [cancel | apply mapsto_value_cohere; auto]].
  - unfold array_pred, aggregate_pred.array_pred.
    rewrite sepcon_andp_prop, !sepcon_andp_prop'.
    repeat (apply derives_extract_prop; intro); entailer'.
    rewrite Z.sub_0_r in *.
    set (lo := 0) at 1 3 5 7; clearbody lo.
    forget (Z.to_nat z) as n; revert lo; induction n; simpl; intro; [cancel|].
    rewrite !sepcon_assoc, <- (sepcon_assoc _ (at_offset _ _ _)), (sepcon_comm _ (at_offset _ _ _)).
    rewrite <- (sepcon_assoc _ (at_offset _ _ _)), (sepcon_comm _ (at_offset _ _ _)).
    rewrite !sepcon_assoc, <- !(sepcon_assoc (at_offset _ _ _) (at_offset _ _ _)).
    apply sepcon_derives; unfold at_offset; auto.
  - apply struct_pred_value_cohere; auto.
  - 
Qed.

Corollary field_at_value_cohere : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p, readable_share sh1 ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |--
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v1 p.
Proof.
  intros; destruct (readable_share_dec sh2).
  - unfold field_at, at_offset; Intros; entailer'.
    apply data_at_rec_value_cohere; auto.
  - assert_PROP (value_fits (nested_field_type t gfs) v1 /\ value_fits (nested_field_type t gfs) v2)
      by entailer!.
    setoid_rewrite nonreadable_field_at_eq at 2; eauto; tauto.
Qed.

Corollary data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v1 p.
Proof.
  intros; apply field_at_value_cohere; auto.
Qed.

Corollary data_at__cohere : forall {cs : compspecs} sh1 sh2 t v p, readable_share sh1 ->
  data_at sh1 t v p * data_at_ sh2 t p =
  data_at sh1 t v p * data_at sh2 t v p.
Proof.
  intros; apply mpred_ext.
  - rewrite data_at__eq; apply data_at_value_cohere; auto.
  - entailer!.
Qed.

Lemma data_at__shares_join : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh)
  (Hreadable1 : readable_share sh1) (Hreadable : Forall readable_share shs),
  @data_at cs sh1 t v p * fold_right sepcon emp (map (fun sh => data_at_ sh t p) shs) |--
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    inv Hreadable.
    rewrite <- sepcon_assoc, data_at__cohere; auto.
    erewrite data_at_share_join; eauto.
    apply IHshs; auto.
    eapply readable_share_join; eauto.
Qed.*)

Lemma extract_nth_sepcon : forall l i, 0 <= i < Zlength l ->
  fold_right sepcon emp l = Znth i l * fold_right sepcon emp (upd_Znth i l emp).
Proof.
  intros.
  erewrite <- sublist_same with (al := l) at 1; auto.
  rewrite sublist_split with (mid := i); try lia.
  rewrite sublist_next with (i0 := i); try lia.
  rewrite sepcon_app; simpl.
  rewrite <- sepcon_assoc, (sepcon_comm _ (Znth i l)).
  unfold_upd_Znth_old; rewrite sepcon_app, sepcon_assoc; simpl.
  rewrite emp_sepcon; auto.
Qed.

Lemma replace_nth_sepcon : forall P l i, 0 <= i < Zlength l ->
  P * fold_right sepcon emp (upd_Znth i l emp) =
    fold_right sepcon emp (upd_Znth i l P).
Proof.
  intros; unfold_upd_Znth_old.
  rewrite !sepcon_app; simpl.
  rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm P); auto.
Qed.

Lemma sepcon_derives_prop : forall P Q R, (P |-- !!R) -> P * Q |-- !!R.
Proof.
  intros; eapply derives_trans; [apply saturate_aux20 with (Q' := True); eauto|].
  - entailer!.
  - apply prop_left; intros (? & ?); apply prop_right; auto.
Qed.

Lemma sepcon_map : forall {A} P Q (l : list A), fold_right sepcon emp (map (fun x => P x * Q x) l) =
  fold_right sepcon emp (map P l) * fold_right sepcon emp (map Q l).
Proof.
  induction l; simpl.
  - rewrite sepcon_emp; auto.
  - rewrite !sepcon_assoc, <- (sepcon_assoc (fold_right _ _ _) (Q a)), (sepcon_comm (fold_right _ _ _) (Q _)).
    rewrite IHl; rewrite sepcon_assoc; auto.
Qed.

Lemma sepcon_list_derives : forall l1 l2 (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall i, 0 <= i < Zlength l1 -> Znth i l1 |-- Znth i l2),
  fold_right sepcon emp l1 |-- fold_right sepcon emp l2.
Proof.
  induction l1; destruct l2; auto; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; lia).
  apply sepcon_derives.
  - specialize (Heq 0); rewrite !Znth_0_cons in Heq; apply Heq.
    rewrite Zlength_correct; lia.
  - apply IHl1; [lia|].
    intros; specialize (Heq (i + 1)); rewrite !Znth_pos_cons, !Z.add_simpl_r in Heq; try lia.
    apply Heq; lia.
Qed.

Lemma sepcon_rotate : forall lP m n, 0 <= n - m < Zlength lP ->
  fold_right sepcon emp lP = fold_right sepcon emp (rotate lP m n).
Proof.
  intros.
  unfold rotate.
  rewrite sepcon_app, sepcon_comm, <- sepcon_app, sublist_rejoin, sublist_same by lia; auto.
Qed.

Lemma sepcon_In : forall l P, In P l -> exists Q, fold_right sepcon emp l = P * Q.
Proof.
  induction l; [contradiction|].
  intros ? [|]; simpl; subst; eauto.
  destruct (IHl _ H) as [? ->].
  rewrite sepcon_comm, sepcon_assoc; eauto.
Qed.

Lemma extract_wand_sepcon : forall l P, In P l ->
  fold_right sepcon emp l = P * (P -* fold_right sepcon emp l).
Proof.
  intros.
  destruct (sepcon_In _ _ H).
  eapply wand_eq; eauto.
Qed.

Lemma wand_sepcon_map : forall {A} (R : A -> mpred) l P Q
  (HR : forall i, In i l -> R i = P i * Q i),
  fold_right sepcon emp (map R l) = fold_right sepcon emp (map P l) *
    (fold_right sepcon emp (map P l) -* fold_right sepcon emp (map R l)).
Proof.
  intros; eapply wand_eq.
  erewrite map_ext_in, sepcon_map; eauto.
  apply HR.
Qed.

Lemma semax_extract_later_prop'':
  forall {CS : compspecs} {Espec: OracleKind},
    forall (Delta : tycontext) (PP : Prop) P Q R c post P1 P2,
      (P2 |-- !!PP) ->
      (PP -> semax Delta (PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))) c post) ->
      semax Delta (PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))) c post.
Proof.
  intros.
  erewrite (add_andp P2) by eauto.
  apply semax_pre0 with (P' := |>!!PP && PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))).
  { go_lowerx.
    rewrite later_andp, <- andp_assoc, andp_comm, corable_andp_sepcon1; auto.
    apply corable_later; auto. }
  apply semax_extract_later_prop; auto.
Qed.

Lemma field_at_array_inbounds : forall {cs : compspecs} sh t z a i v p,
  field_at sh (Tarray t z a) [ArraySubsc i] v p |-- !!(0 <= i < z).
Proof.
  intros; entailer!.
  destruct H as (_ & _ & _ & _ & _ & ?); auto.
Qed.

Lemma valid_pointer_isptr : forall v, valid_pointer v |-- !!(is_pointer_or_null v).
Proof.
Transparent mpred.
Transparent predicates_hered.pred.
  destruct v; simpl; auto; try apply derives_refl.
  apply prop_right; auto.
Opaque mpred. Opaque predicates_hered.pred.
Qed.

#[export] Hint Resolve valid_pointer_isptr : saturate_local.

Lemma approx_imp : forall n P Q, compcert_rmaps.RML.R.approx n (predicates_hered.imp P Q) =
  compcert_rmaps.RML.R.approx n (predicates_hered.imp (compcert_rmaps.RML.R.approx n P)
    (compcert_rmaps.RML.R.approx n Q)).
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? Ha' HP.
  - destruct HP; split; auto.
  - apply Himp; auto; split; auto.
    pose proof (ageable.necR_level _ _ Ha'); lia.
Qed.

Definition super_non_expansive' {A} P := forall n ts x, compcert_rmaps.RML.R.approx n (P ts x) =
  compcert_rmaps.RML.R.approx n (P ts (functors.MixVariantFunctor.fmap (rmaps.dependent_type_functor_rec ts A)
        (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x)).

Lemma approx_0 : forall P, compcert_rmaps.RML.R.approx 0 P = FF.
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? []; lia.
  - intros ??; contradiction.
Qed.

Lemma approx_eq : forall n (P : mpred) r, app_pred (compcert_rmaps.RML.R.approx n P) r = (if lt_dec (level r) n then app_pred P r else False).
Proof.
  intros; apply prop_ext; split.
  - intros []; if_tac; auto.
  - if_tac; split; auto; lia.
Qed.

Lemma approx_iter_sepcon' : forall {B} n f (lP : list B) P,
  compcert_rmaps.RML.R.approx n (iter_sepcon f lP)  * compcert_rmaps.RML.R.approx n P =
  iter_sepcon (compcert_rmaps.RML.R.approx n oo f) lP * compcert_rmaps.RML.R.approx n P.
Proof.
  induction lP; simpl; intros.
  - apply predicates_hered.pred_ext; intros ? (? & ? & ? & ? & ?).
    + destruct H0; do 3 eexists; eauto.
    + do 3 eexists; eauto; split; auto; split; auto.
      destruct H1; apply join_level in H as []; lia.
  - rewrite approx_sepcon, !sepcon_assoc, IHlP; auto.
Qed.

Corollary approx_iter_sepcon: forall {B} n f (lP : list B), lP <> [] ->
  compcert_rmaps.RML.R.approx n (iter_sepcon f lP) =
  iter_sepcon (compcert_rmaps.RML.R.approx n oo f) lP.
Proof.
  destruct lP; [contradiction | simpl].
  intros; rewrite approx_sepcon, !(sepcon_comm (compcert_rmaps.RML.R.approx n (f b))), approx_iter_sepcon'; auto.
Qed.

Lemma approx_FF : forall n, compcert_rmaps.RML.R.approx n FF = FF.
Proof.
  intro; apply predicates_hered.pred_ext; intros ??; try contradiction.
  destruct H; contradiction.
Qed.

Lemma later_nonexpansive' : nonexpansive (@later mpred _ _).
Proof.
  apply contractive_nonexpansive, later_contractive.
  intros ??; auto.
Qed.

Lemma later_nonexpansive : forall n P, compcert_rmaps.RML.R.approx n (|> P) =
  compcert_rmaps.RML.R.approx n (|> compcert_rmaps.RML.R.approx n P).
Proof.
  intros.
  intros; apply predicates_hered.pred_ext.
  - intros ? []; split; auto.
    intros ? Hlater; split; auto.
    apply laterR_level in Hlater; lia.
  - intros ? []; split; auto.
    intros ? Hlater.
    specialize (H0 _ Hlater) as []; auto.
Qed.

Lemma allp_nonexpansive : forall {A} n P, compcert_rmaps.RML.R.approx n (ALL y : A, P y) =
  compcert_rmaps.RML.R.approx n (ALL y, compcert_rmaps.RML.R.approx n (P y)).
Proof.
  intros.
  apply predicates_hered.pred_ext; intros ? [? Hall]; split; auto; intro; simpl in *.
  - split; auto.
  - apply Hall.
Qed.

Lemma fold_right_sepcon_nonexpansive : forall lP1 lP2, Zlength lP1 = Zlength lP2 ->
  (ALL i : Z, Znth i lP1 <=> Znth i lP2) |--
  fold_right sepcon emp lP1 <=> fold_right sepcon emp lP2.
Proof.
  induction lP1; intros.
  - symmetry in H; apply Zlength_nil_inv in H; subst.
    constructor. apply eqp_refl.
  - destruct lP2; [apply Zlength_nil_inv in H; discriminate|].
    rewrite !Zlength_cons in H. constructor.
    simpl fold_right; apply eqp_sepcon.
    + apply predicates_hered.allp_left with 0.
      rewrite !Znth_0_cons; auto.
    + eapply predicates_hered.derives_trans, IHlP1; [|lia].
      apply predicates_hered.allp_right; intro i.
      apply predicates_hered.allp_left with (i + 1).
      destruct (zlt i 0).
      { rewrite !(Znth_underflow _ _ l); apply eqp_refl. }
      rewrite !Znth_pos_cons, Z.add_simpl_r by lia; auto.
Qed.


(* tactics *)
Lemma void_ret : ifvoid tvoid (` (PROP ( )  LOCAL ()  SEP ()) (make_args [] []))
  (EX v : val, ` (PROP ( )  LOCAL ()  SEP ()) (make_args [ret_temp] [v])) = emp.
Proof.
  extensionality; simpl.
  unfold liftx, lift, PROPx, LOCALx, SEPx; simpl. autorewrite with norm. auto.
Qed.

(*
Lemma malloc_compat : forall {cs : compspecs} sh t p,
  complete_legal_cosu_type t = true ->
  natural_aligned natural_alignment t = true ->
  malloc_token sh (sizeof t) p = !!field_compatible t [] p && malloc_token sh (sizeof t) p.
Proof.
  intros; rewrite andp_comm; apply add_andp; entailer!.
  apply malloc_compatible_field_compatible; auto.
Qed.
*)


