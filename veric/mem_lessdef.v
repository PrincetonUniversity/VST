Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.Memory.
Require Import VST.veric.juicy_mem. 
Require Import VST.veric.juicy_extspec.

Require Import VST.veric.res_predicates.

(*Lenb: Should Imports from sepcomp really be here?*)
Require Import VST.sepcomp.extspec.

(*Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.extspec.*)
(*Lenb: Should stuff that requires Imports from sepcomp really be here?*)

Notation val_inject := Val.inject. (*as in sepcomp.mem_lemmas*)

Definition mem_lessdef m1 m2 :=
  (forall b ofs len v,
      Mem.loadbytes m1 b ofs len = Some v ->
      exists v',
        Mem.loadbytes m2 b ofs len = Some v' /\
        list_forall2 memval_lessdef v v'
  ) /\
  (forall b ofs k p,
      Mem.perm m1 b ofs k p ->
      Mem.perm m2 b ofs k p) /\
  (Mem.nextblock m1 <=
   Mem.nextblock m2)%positive.

Definition mem_lessalloc m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  (Mem.nextblock m1 <= Mem.nextblock m2)%positive.

Definition mem_equiv m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Lemma perm_order_pp_refl p: Mem.perm_order'' p p.
Proof. unfold Mem.perm_order''. destruct p; trivial. apply perm_refl. Qed.

Lemma same_perm_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 <->
  (forall k x, access_at m1 x k = access_at m2 x k).
Proof.
  split; intros E.
  - intros k (b, ofs).
    match type of E with ?f = ?g => assert (S : forall b z k p, f b z k p <-> g b z k p) end.
    { rewrite E; tauto. } clear E.
    specialize (S b ofs k). revert S.
    unfold access_at, Mem.perm. simpl.
    set (o1 := (Mem.mem_access _) !! b ofs k).
    set (o2 := (Mem.mem_access _) !! b ofs k). clearbody o1 o2. intros S.
    assert (S' : forall o, Mem.perm_order'' o1 o <-> Mem.perm_order'' o2 o).
    { intros [ o | ]. apply S. destruct o1 as [o1 | ], o2 as [o2 | ]; split; intro; constructor. }
    clear S.
    destruct (S' o1) as [A _]. spec A. apply perm_order_pp_refl.
    destruct (S' o2) as [_ B]. spec B. apply perm_order_pp_refl.
    destruct o1 as [[]|], o2 as [[]|]; auto; simpl in *.
    all: try solve [inv A; inv B; auto].
  - extensionality b ofs k. specialize (E k (b, ofs)).
    unfold access_at in *.
    simpl in E.
    unfold Mem.perm in *.
    rewrite E.
    auto.
Qed.

Lemma same_loadbytes_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 ->  (* TODO change this to only need same Cur *)
  Mem.loadbytes m1 = Mem.loadbytes m2 <->
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x).
Proof.
  intros P; split; intros E.
  - intros (b, ofs) R.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes in *.
    apply equal_f with (x := b) in E.
    apply equal_f with (x := ofs) in E.
    apply equal_f with (x := 1) in E.
    unfold access_at in *.
    if_tac [p1|np1] in E; if_tac in E; try discriminate.
    + simpl in E.
      unfold contents_at in *.
      simpl.
      congruence.
    + destruct np1.
      intros ofs1 r1.
      cut (ofs1 = ofs). intros <-. apply R.
      omega.
  - extensionality b ofs k.
    unfold Mem.loadbytes in *.
    if_tac [p1|np1]; if_tac [p2|np2].
    + destruct (zle 0 k).
      * clear p2.
        f_equal.
        rewrite <-(Coqlib.nat_of_Z_eq k) in p1. 2:omega.
        revert p1. generalize (nat_of_Z k); clear k l; intros n.
        revert ofs.
        induction n; auto; intros ofs p.
        simpl. f_equal.
        -- specialize (E (b, ofs)).
           unfold contents_at in *.
           simpl in E.
           apply E.
           apply p.
           simpl.
           zify; omega.
        -- apply IHn.
           intros ofs' r'.
           apply p.
           zify. omega.
      * rewrite nat_of_Z_neg. auto. omega.
    + destruct np2.
      unfold Mem.range_perm in *.
      rewrite <-P.
      auto.
    + destruct np1.
      unfold Mem.range_perm in *.
      rewrite P.
      auto.
    + auto.
Qed.

Definition mem_equiv' m1 m2 :=
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x) /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Definition mem_lessalloc' m1 m2 :=
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x) /\
  Mem.perm m1 = Mem.perm m2 /\
  (Mem.nextblock m1 <= Mem.nextblock m2)%positive.

Lemma mem_equiv'_spec m1 m2 : mem_equiv m1 m2 <-> mem_equiv' m1 m2.
Proof.
  split; intros (? & ? & ?); repeat split; auto.
  rewrite <-same_loadbytes_spec; auto.
  rewrite same_loadbytes_spec; auto.
Qed.

Lemma mem_lessalloc'_spec m1 m2 : mem_lessalloc m1 m2 <-> mem_lessalloc' m1 m2.
Proof.
  split; intros (? & ? & ?); repeat split; auto.
  rewrite <-same_loadbytes_spec; auto.
  rewrite same_loadbytes_spec; auto.
Qed.

Lemma val_inject_antisym v1 v2 :
  val_inject inject_id v1 v2 ->
  val_inject inject_id v2 v1 ->
  v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; try subst; try congruence.
  unfold inject_id in *.
  f_equal. congruence.
  replace delta with 0%Z by congruence.
  symmetry; apply Ptrofs.add_zero.
Qed.

Lemma memval_lessdef_antisym v1 v2 : memval_lessdef v1 v2 -> memval_lessdef v2 v1 -> v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; subst; try congruence.
  f_equal. apply val_inject_antisym; auto.
Qed.

Lemma mem_lessdef_equiv m1 m2 : mem_lessdef m1 m2 -> mem_lessdef m2 m1 ->  mem_equiv m1 m2.
Proof.
  intros (L1 & P1 & N1) (L2 & P2 & N2); repeat split.
  - clear -L1 L2.
    extensionality b ofs z.
    match goal with |- ?a = ?b => destruct a as [v1|] eqn:E1; destruct b as [v2|] eqn:E2 end;
      try destruct (L1 _ _ _ _ E1) as (v2' & E1' & l1);
      try destruct (L2 _ _ _ _ E2) as (v1' & E2' & l2);
      try congruence.
    assert (v1' = v1) by congruence; assert (v2' = v2) by congruence; subst; f_equal.
    clear -l1 l2.
    revert v2 l1 l2; induction v1; intros v2 l1 l2; inversion l1; subst; auto.
    inversion l2; subst.
    f_equal; auto.
    apply memval_lessdef_antisym; auto.
  - repeat extensionality.
    apply prop_ext; split; auto.
  - zify.
    cut (Z.pos (Mem.nextblock m2) = Z.pos (Mem.nextblock m1)).
    congruence. omega.
Qed.

Lemma mem_equiv_refl m : mem_equiv m m.
Proof.
  split3; hnf; auto.
Qed.

Lemma mem_lessalloc_refl m : mem_lessalloc m m.
Proof.
  split3; auto. apply Ple_refl.
Qed.

Lemma mem_equiv_refl' m m' : m = m' -> mem_equiv m m'.
Proof.
  intros <-; apply mem_equiv_refl.
Qed.

Lemma mem_lessalloc_refl' m m' : m = m' -> mem_lessalloc m m'.
Proof.
  intros <-; apply mem_lessalloc_refl.
Qed.

Lemma mem_equiv_sym m1 m2 : mem_equiv m1 m2 -> mem_equiv m2 m1.
Proof.
  intros []; split; intuition.
Qed.

Lemma mem_equiv_trans m1 m2 m3 :
  mem_equiv m1 m2 ->
  mem_equiv m2 m3 ->
  mem_equiv m1 m3.
Proof.
  unfold mem_equiv in *.
  intros (-> & -> & ->) (-> & -> & ->); auto.
Qed.

Lemma mem_lessalloc_trans m1 m2 m3 :
  mem_lessalloc m1 m2 ->
  mem_lessalloc m2 m3 ->
  mem_lessalloc m1 m3.
Proof.
  unfold mem_lessalloc in *.
  intros (-> & -> & l) (-> & -> & l'); split; auto. split; auto.
  eapply Ple_trans; eauto.
Qed.

Lemma mem_equiv_lessalloc m1 m2 : mem_equiv m1 m2 -> mem_lessalloc m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split; auto.
  rewrite N1; auto. apply Ple_refl.
Qed.

Lemma mem_lessalloc_lessdef m1 m2 : mem_lessalloc m1 m2 -> mem_lessdef m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split.
  - rewrite L1; auto.
    intros b ofs len v H.
    exists v; intuition.
    clear.
    induction v; constructor; auto.
    apply memval_lessdef_refl.
  - rewrite P1; auto.
  - auto.
Qed.

Lemma mem_equiv_lessdef m1 m2 : mem_equiv m1 m2 -> mem_lessdef m1 m2.
Proof.
  intro H.
  apply mem_lessalloc_lessdef, mem_equiv_lessalloc, H.
Qed.

Lemma mem_lessdef_valid_pointer:
  forall m1 m2 b z, 
       mem_lessdef m1 m2 ->
       Mem.valid_pointer m1 b z = true ->
       Mem.valid_pointer m2 b z = true.
Proof.
intros.
destruct H as [? [? ?]].
unfold Mem.valid_pointer in *.
destruct (Mem.perm_dec m1 b z Cur Nonempty); inv H0.
destruct (Mem.perm_dec m2 b z Cur Nonempty); try reflexivity.
contradiction n. clear n.
apply H1; auto.
Qed.

Lemma mem_lessdef_weak_valid_pointer:
  forall m1 m2 b z, 
       mem_lessdef m1 m2 ->
       Mem.weak_valid_pointer m1 b z = true ->
       Mem.weak_valid_pointer m2 b z = true.
Proof.
intros.
unfold Mem.weak_valid_pointer in *.
rewrite orb_true_iff in *.
destruct H0; [left|right]; eapply mem_lessdef_valid_pointer; eauto.
Qed.

Ltac memval_lessdef_tac :=
match goal with
 | H: memval_lessdef ?a ?b |- _ => destruct a,b; inv H
 | H: list_forall2 _ ?a ?b |- _ => destruct a,b; inv H
 | H: proj_bytes ?a = Some _ |- _ => match a with context [nil] => inv H end
end;
 try discriminate;
 try solve [unfold decode_val; simpl; auto] .

Lemma mem_lessdef_proj_bytes:
  forall vl vl',
  list_forall2 memval_lessdef vl vl' ->
  forall bl, proj_bytes vl = Some bl -> proj_bytes vl' = Some bl.
Proof.
intros.
revert bl H0; induction H; intros; auto.
destruct bl0; inv H1.
destruct a1; auto.
inv H3.
destruct (proj_bytes al) eqn:?H; inv H3. inv H3.
destruct a1; try discriminate.
destruct (proj_bytes al) eqn:?H; inv H3.
specialize (IHlist_forall2 _ (eq_refl _)).
inv H.
simpl.
rewrite IHlist_forall2.
auto.
Qed.

Lemma mem_lessdef_decode_val:
  forall ch vl vl', list_forall2 memval_lessdef vl vl' ->
    Val.lessdef (decode_val ch vl) (decode_val ch vl').
Proof.
intros.
unfold decode_val.
destruct (proj_bytes vl) eqn:?H.
2: {
     unfold proj_value.
     destruct ch; auto.
     +
       destruct Archi.ptr64; auto.
       destruct vl; auto.
       destruct m; auto.
       destruct (check_value (size_quantity_nat Q32) v Q32 (Fragment v q n :: vl)) eqn:?; auto.
       destruct vl'; inv H.
       inv H4.
       unfold proj_bytes.
       destruct (Val.eq v Vundef).
       subst.
       simpl. auto.
       assert (H9: check_value (size_quantity_nat Q32) v2 Q32 (Fragment v2 q n :: vl') = true).
       2: rewrite H9; apply Val.load_result_lessdef; apply val_inject_id; auto.
       assert (v2=v).
       apply val_inject_id in H5.
       destruct v; try solve [contradiction n0; auto]; inv H5; auto.
       subst v2.
       clear H5.
       eapply (check_value_inject inject_id); try eassumption.
       constructor; auto.
       constructor; auto.
       apply val_inject_id; apply Val.lessdef_refl.
       apply val_inject_id; apply Val.lessdef_refl.
     +
       destruct vl; auto.
       destruct m; auto.
       destruct (check_value (size_quantity_nat Q32) v Q32 (Fragment v q n :: vl)) eqn:?; auto.
       destruct vl'; inv H.
       unfold proj_bytes.
       inv H4.
       destruct (Val.eq v Vundef).
       subst.
       simpl. auto.
       assert (H9: check_value (size_quantity_nat Q32) v2 Q32 (Fragment v2 q n :: vl') = true).
       2: rewrite H9; apply Val.load_result_lessdef; apply val_inject_id; auto.
       assert (v2=v).
       apply val_inject_id in H5.
       destruct v; try solve [contradiction n0; auto]; inv H5; auto.
       subst v2.
       clear H5.
       eapply (check_value_inject inject_id); try eassumption.
       constructor; auto.
       constructor; auto.
       apply val_inject_id; apply Val.lessdef_refl.
       apply val_inject_id; apply Val.lessdef_refl.
     +
       destruct vl; auto.
       destruct m; auto.
       destruct (check_value (size_quantity_nat Q64) v Q64 (Fragment v q n :: vl)) eqn:?; auto.
       destruct vl'; inv H.
       unfold proj_bytes.
       inv H4.
       destruct (Val.eq v Vundef).
       subst.
       simpl. auto.
       assert (H9: check_value (size_quantity_nat Q64) v2 Q64 (Fragment v2 q n :: vl') = true).
       2: rewrite H9; apply Val.load_result_lessdef; apply val_inject_id; auto.
       assert (v2=v).
       apply val_inject_id in H5.
       destruct v; try solve [contradiction n0; auto]; inv H5; auto.
       subst v2.
       clear H5.
       eapply (check_value_inject inject_id); try eassumption.
       constructor; auto.
       constructor; auto.
       apply val_inject_id; apply Val.lessdef_refl.
       apply val_inject_id; apply Val.lessdef_refl.
     } 
rewrite (mem_lessdef_proj_bytes _ _ H _ H0).
auto.
Qed.

Lemma mem_lessdef_loadbytes:
  forall m1 m2, mem_lessdef m1 m2 ->
  forall b z n v1, Mem.loadbytes m1 b z n = Some v1 ->
  exists v2, list_forall2 memval_lessdef v1 v2 /\ Mem.loadbytes m2 b z n = Some v2.
Proof.
intros.
destruct H as [? [? ?]].
apply H in H0.
destruct H0 as [v2 [? ?]]; exists v2; split; auto.
Qed.

Lemma valid_pointer_lessalloc {m m2} (M:mem_lessalloc m m2):
      Mem.valid_pointer m = Mem.valid_pointer m2.
Proof. unfold Mem.valid_pointer. destruct M as [M1 [M2 M3]].
  extensionality b. extensionality i.
  destruct (Mem.perm_dec m b i Cur Nonempty);
  destruct (Mem.perm_dec m2 b i Cur Nonempty); trivial.
  exfalso. rewrite M2 in p. contradiction.
  exfalso. rewrite M2 in n. contradiction.
Qed.

Lemma weak_valid_pointer_lessalloc {m m2} (M:mem_lessalloc m m2):
      Mem.weak_valid_pointer m = Mem.weak_valid_pointer m2.
Proof.
  unfold Mem.weak_valid_pointer.
  extensionality b. extensionality i.
  rewrite (valid_pointer_lessalloc M); trivial.
Qed.


Definition juicy_mem_equiv jm1 jm2 := mem_equiv (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Definition juicy_mem_lessdef jm1 jm2 := mem_lessdef (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Definition juicy_mem_lessalloc jm1 jm2 := mem_lessdef (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Ltac sync D :=
  first
    [ split; [destruct D as [D _] | destruct D as [_ D]]
    | destruct D as [|D]; [left|right]
    | let x := fresh in destruct D as (x, D); exists x
    | let x := fresh in intro x; specialize (D x)
    ].

Definition ext_spec_stable {M E Z} (R : M -> M -> Prop)
           (spec : external_specification M E Z) :=
  (forall e x b tl vl z m1 m2,
    R m1 m2 ->
    ext_spec_pre spec e x b tl vl z m1 ->
    ext_spec_pre spec e x b tl vl z m2) /\
  (forall e v m1 m2,
    R m1 m2 ->
    ext_spec_exit spec e v m1 ->
    ext_spec_exit spec e v m2).

(* Currently fails because jsafeN__ind is too weak. 
Lemma jsafeN__mem_equiv {G C Z HH Sem Jspec ge n z c jm1 jm2} :
  juicy_mem_equiv jm1 jm2 ->
  ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec) ->
  @jsafeN_ G Z C HH Sem Jspec ge n z c jm1 ->
  @jsafeN_ G Z C HH Sem Jspec ge n z c jm2.
Proof.  intros E [Spre Sexit] S1.
  revert jm2 E. 
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 E.

  - constructor 1.

  - destruct (juicy_step_mem_equiv_sim E step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct E as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.

Lemma jsafeN__mem_equiv {G C Z HH Sem Jspec ge n z c jm1 jm2} :
  juicy_mem_equiv jm1 jm2 ->
  ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec) ->
  @jsafeN_ G Z C HH Sem Jspec ge n z c jm1 ->
  @jsafeN_ G Z C HH Sem Jspec ge n z c jm2.
Proof.
  intros E [Spre Sexit] S1.
  revert jm2 E.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 E.

  - constructor 1.

  - destruct (juicy_step_mem_equiv_sim E step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct E as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.

Lemma jsafeN_mem_lessdef {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_lessdef jm1 jm2 ->
  ext_spec_stable juicy_mem_lessdef (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof.
  intros L [Spre Sexit] S1.
  revert jm2 L.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 L.

  - constructor 1.

  - destruct (juicy_step_mem_lessdef_sim L step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct L as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.*)

Lemma mem_ext m1 m2 :
  Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl in *.
  intros <- <- <- .
  f_equal; apply proof_irr.
Qed.
