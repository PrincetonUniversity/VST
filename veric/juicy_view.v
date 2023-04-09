From iris.algebra Require Export gmap agree.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From VST.zlist Require Import sublist.
From VST.msl Require Import shares.
From iris_ora.algebra Require Export ora gmap agree.
From VST.veric Require Export base Memory share_alg dfrac view shared.
From iris.prelude Require Import options.

(* We can't import compcert.lib.Maps because their lookup notations conflict with stdpp's.
   We can define lookup instances, which require one more ! apiece than CompCert's notation. *)
Global Instance ptree_lookup A : Lookup positive A (Maps.PTree.t A) := Maps.PTree.get(A := A).
Global Instance pmap_lookup A : LookupTotal positive A (Maps.PMap.t A) := Maps.PMap.get(A := A).

Lemma perm_order''_refl : forall s, Mem.perm_order'' s s.
Proof.
  destruct s; simpl; try done.
  apply perm_refl.
Qed.

Lemma perm_order''_trans: forall a b c, Mem.perm_order'' a b ->  Mem.perm_order'' b c ->
                             Mem.perm_order'' a c.
Proof.
   intros a b c H1 H2; destruct a, b, c; inversion H1; inversion H2; subst; eauto;
           eapply perm_order_trans; eauto.
Qed.

Lemma perm_order''_None : forall a, Mem.perm_order'' a None.
Proof. destruct a; simpl; auto. Qed.

Definition perm_of_sh (sh: Share.t): option permission :=
  if writable0_share_dec sh
  then if eq_dec sh Share.top
          then Some Freeable
          else Some Writable
  else if readable_share_dec sh
       then Some Readable
       else if eq_dec sh Share.bot
                 then None
            else Some Nonempty.
Functional Scheme perm_of_sh_ind := Induction for perm_of_sh Sort Prop.

Definition perm_of_dfrac dq :=
  match dq with
  | DfracOwn sh => perm_of_sh sh
  | DfracDiscarded => Some Readable
  | DfracBoth sh => if Mem.perm_order'_dec (perm_of_sh sh) Readable then perm_of_sh sh else Some Readable
  end.

Definition perm_of_res' {V} (r: option (dfrac * V)) :=
  match r with
  | Some (dq, _) => perm_of_dfrac dq
  | None => None
  end.

Lemma perm_of_sh_mono : forall (sh1 sh2 : shareR), sh1 ⋅ sh2 ≠ Share.bot -> Mem.perm_order'' (perm_of_sh (sh1 ⋅ sh2)) (perm_of_sh sh1).
Proof.
  intros ?? H.
  pose proof (proj1 (share_op_equiv sh1 sh2 _) eq_refl) as J.
  rewrite -> if_false in J by auto; destruct J as (? & ? & J).
  unfold perm_of_sh.
  destruct (writable0_share_dec sh1).
  { eapply join_writable01 in w; eauto.
    rewrite -> if_true by auto.
    if_tac; if_tac; simpl; try constructor.
    subst; rewrite -> (@only_bot_joins_top sh2) in H1 by (eexists; eauto); contradiction. }
  if_tac; [repeat if_tac; constructor|].
  destruct (readable_share_dec sh1).
  { eapply join_readable1 in r; eauto.
    rewrite (if_true _ _ _ _ _ r); constructor. }
  repeat if_tac; try constructor; contradiction.
Qed.

Lemma perm_order_antisym : forall p1 p2, ~perm_order p1 p2 -> perm_order p2 p1.
Proof.
  destruct p1, p2; try constructor; intros X; contradiction X; constructor.
Qed.

Lemma perm_order'_antisym : forall p1 p2, ~Mem.perm_order' p1 p2 -> Mem.perm_order'' (Some p2) p1.
Proof.
  destruct p1; simpl; auto; apply perm_order_antisym.
Qed.

Lemma perm_of_dfrac_mono : forall d1 d2, ✓d2 -> d1 ≼ d2 -> Mem.perm_order'' (perm_of_dfrac d2) (perm_of_dfrac d1).
Proof.
  intros ?? Hv [d0 ->%leibniz_equiv].
  destruct d1, d0; simpl in *; repeat if_tac; auto; try (apply perm_order''_refl || (by apply perm_of_sh_mono) || (by destruct Hv; apply perm_of_sh_mono) || constructor).
  - by apply perm_order'_antisym.
  - destruct Hv; eapply perm_order''_trans, perm_of_sh_mono; [apply perm_order'_antisym|]; eauto.
  - destruct Hv; eapply perm_order''_trans, perm_of_sh_mono; [apply perm_order'_antisym|]; eauto.
  - destruct Hv; eapply perm_order''_trans, perm_of_sh_mono; [apply perm_order'_antisym|]; eauto.
Qed.

Class resource_ops (V : ofe) := {
  perm_of_res : option (dfrac * option V) -> option permission;
  memval_of : V -> option memval;
  perm_of_res_None : perm_of_res None = None;
  perm_of_res_mono : forall d1 d2 (r : option V), ✓d2 -> d1 ≼ d2 -> Mem.perm_order'' (perm_of_res (Some (d2, r))) (perm_of_res (Some (d1, r)));
  perm_of_res_discarded : forall d (r : option V), readable_dfrac d -> Mem.perm_order'' (perm_of_res (Some (d, r))) (perm_of_res (Some (DfracDiscarded, r))) ∧
    forall d2, ✓(d ⋅ d2) -> Mem.perm_order'' (perm_of_res (Some (d ⋅ d2, r))) (perm_of_res (Some (DfracDiscarded ⋅ d2, r)));
  perm_of_res_ne : forall n d (r1 r2 : option V), r1 ≡{n}≡ r2 -> perm_of_res (Some (d, r1)) = perm_of_res (Some (d, r2));
  perm_of_res_None' : forall d (r : V), Mem.perm_order'' (perm_of_res (Some (d, Some r))) (perm_of_res (Some (d, None)));
  perm_of_res_max : forall r, Mem.perm_order'' (perm_of_res' r) (perm_of_res r);
  memval_of_ne : forall n v1 v2, v1 ≡{n}≡ v2 -> memval_of v1 = memval_of v2
}.

(** * ORA for a juicy mem. An algebra where a resource map is a view of a CompCert memory if it is
      coherent with that memory. *)

Local Definition juicy_view_fragUR (V : ofe) : uora :=
  gmapUR address (sharedR V).

(** View relation. *)
Section rel.
  Context (V : ofe) {ResOps : resource_ops V}.
  Implicit Types (m : Memory.mem) (k : address) (r : option (dfrac * option V)) (v : memval) (n : nat).
  Implicit Types (f : gmap address (shared V)).

  Notation rmap := (gmap address (shared V)).

  Definition elem_of_agree {A} (x : agree A) : { a | a ∈ agree_car x}.
  Proof. destruct x as [[|a ?] ?]; [done | exists a; apply elem_of_cons; auto]. Qed.

  Lemma elem_of_agree_ne : forall {A} n (x y : agreeR A), ✓{n} x -> x ≡{n}≡ y -> proj1_sig (elem_of_agree x) ≡{n}≡ proj1_sig (elem_of_agree y).
  Proof.
    intros; destruct (elem_of_agree x), (elem_of_agree y); simpl.
    destruct (proj1 H0 _ e) as (? & Hv2 & ->).
    rewrite H0 in H; eapply agree_validN_def; done.
  Qed.

  Definition resR_to_resource (s : option (shared V)) : option (dfrac * option V) :=
    option_map (fun s : shared V => (dfrac_of s, option_map (fun v : agree V => proj1_sig (elem_of_agree v)) (val_of s))) s.

  Lemma resR_to_resource_ne n : forall x y, ✓{n} x -> x ≡{n}≡ y -> resR_to_resource x ≡{n}≡ resR_to_resource y.
  Proof.
    intros ??? Hdist; inv Hdist; last done.
    destruct x0, y0; try done; simpl; constructor.
    - destruct H0; split; try done; simpl.
      destruct H; rewrite elem_of_agree_ne //.
    - hnf in H0; subst; done.
  Qed.

  Lemma perm_of_res_ne' : forall n r1 r2, r1 ≡{n}≡ r2 -> perm_of_res r1 = perm_of_res r2.
  Proof.
    intros; inv H; try done.
    destruct x, y, H0 as [[=] ?]; simpl in *; subst.
    by eapply perm_of_res_ne.
  Qed.

  Definition resource_at f k := resR_to_resource (f !! k).
  Local Infix "@" := resource_at (at level 50, no associativity).

  Definition contents_at (m: mem) (loc: address) : memval :=
    Maps.ZMap.get (snd loc) (Maps.PMap.get (fst loc) (Mem.mem_contents m)).

  Definition contents_cohere (m: mem) k r :=
    forall v, r ≫= (fun '(_, v) => v ≫= memval_of) = Some v -> contents_at m k = v.

  Definition access_cohere (m: mem) k r :=
    Mem.perm_order'' (access_at m k Cur) (perm_of_res r).

  Definition max_access_at m loc := access_at m loc Max.

  Definition max_access_cohere (m: mem) k r :=
    Mem.perm_order'' (max_access_at m k) (perm_of_res' r).

  Definition alloc_cohere (m: mem) k r :=
    (fst k >= Mem.nextblock m)%positive -> r = None.

  Definition coherent_loc (m: mem) k r := contents_cohere m k r ∧ access_cohere m k r ∧ max_access_cohere m k r ∧ alloc_cohere m k r.

  Definition coherent n (m : leibnizO mem) phi := ✓{n} phi ∧ forall loc, coherent_loc m loc (phi @ loc).

  Local Lemma coherent_mono n1 n2 (m1 m2 : leibnizO mem) f1 f2 :
    coherent n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    coherent n2 m2 f2.
  Proof using Type*.
    intros (Hv & H) -> Hf Hn.
    assert (✓{n2} f2) as Hv2.
    { eapply cmra_validN_includedN; eauto.
      eapply cmra_validN_le; eauto. }
    split; first done.
    intros loc; specialize (Hv loc); specialize (Hv2 loc); specialize (H loc).
    rewrite lookup_includedN in Hf; specialize (Hf loc); rewrite option_includedN in Hf.
    destruct H as (Hcontents & Hcur & Hmax & Halloc); unfold resource_at in *; repeat split.
    - unfold contents_cohere in *; intros.
      apply Hcontents.
      destruct Hf as [Hf | (x2 & x1 & Hf2 & Hf1 & Hf)]; [rewrite Hf in H; inv H|].
      rewrite Hf2 in H Hv2; inv H.
      rewrite Hf1 /= in Hv |- *.
      destruct x2 as [?? v2|]; try done.
      destruct x1 as [?? v1|]; last by destruct Hf as [Hf | Hf]; try done; apply YES_incl_NO in Hf.
      destruct Hv as [_ Hv], Hv2 as [_ Hv2].
      eapply cmra_validN_le in Hv; eauto.
      assert (v2 ≡{n2}≡ v1) as Hvs by (by destruct Hf as [[_ ?] | [_ ?%agree_valid_includedN]%YES_incl_YES]).
      symmetry; eapply memval_of_ne, elem_of_agree_ne, Hvs; auto.
    - unfold access_cohere in *.
      destruct Hf as [Hf | (x2 & x1 & Hf2 & Hf1 & Hf)]; [rewrite Hf perm_of_res_None; apply perm_order''_None|].
      eapply perm_order''_trans; [apply Hcur|].
      rewrite Hf1 Hf2 in Hv Hv2 |- *.
      eapply cmra_validN_le in Hv; eauto.
      destruct Hf; first by erewrite <- perm_of_res_ne' by (by apply resR_to_resource_ne, Some_Forall2, H); apply perm_order''_refl.
      apply shared_includedN in H as [H | [Hd Hvs]]; first by rewrite H in Hv.
      apply shared_validN in Hv as [??].
      simpl; eapply perm_order''_trans; [by apply perm_of_res_mono, Hd|].
      rewrite option_includedN_total in Hvs; destruct Hvs as [-> | (? & ? & Hval2 & Hval1 & ?)].
      + destruct (val_of x1); [apply perm_of_res_None' | apply perm_order''_refl].
      + rewrite -> Hval1, Hval2 in *; simpl; erewrite perm_of_res_ne; first apply perm_order''_refl.
        constructor; apply elem_of_agree_ne; last (symmetry; apply agree_valid_includedN; eauto); done.
    - unfold max_access_cohere in *.
      destruct Hf as [Hf | (x2 & x1 & Hf2 & Hf1 & Hf)]; [rewrite Hf; apply perm_order''_None|].
      eapply perm_order''_trans; [apply Hmax|].
      rewrite Hf1 Hf2 /= in Hv Hv2 |- *.
      destruct Hf as [[-> _]%shared_dist_implies | Hf]; first apply perm_order''_refl.
      apply shared_includedN in Hf as [H | [Hd Hvs]]; first by rewrite H in Hv.
      apply shared_validN in Hv as [??].
      apply perm_of_dfrac_mono; auto.
    - unfold alloc_cohere in *; intros H; specialize (Halloc H).
      destruct Hf as [Hf | (? & ? & Hf2 & Hf1 & _)]; [by rewrite Hf|].
      rewrite Hf1 in Halloc; discriminate.
  Qed.

  Local Lemma coherent_valid n m f :
    coherent n m f → ✓{n} f.
  Proof.
    intros H; apply H.
  Qed.

  Lemma coherent_None m k : coherent_loc m k None.
  Proof.
    repeat split.
    - by intros ?.
    - rewrite /access_cohere perm_of_res_None; apply perm_order''_None.
    - apply perm_order''_None.
  Qed.

  Local Lemma coherent_unit n :
    ∃ m, coherent n m ε.
  Proof using Type*.
    exists Mem.empty; repeat split; rewrite /resource_at lookup_empty; apply coherent_None.
  Qed.

  Local Canonical Structure coherent_rel : view_rel (leibnizO mem) (juicy_view_fragUR V) :=
    ViewRel coherent coherent_mono coherent_valid coherent_unit.

  Definition access_of_rmap f b ofs (k : perm_kind) :=
    match k with
    | Max => perm_of_res' (f @ (b, ofs))
    | Cur => perm_of_res (f @ (b, ofs))
    end.

  Definition make_access (next : Values.block) (r : rmap) :=
    fold_right (fun b p => Maps.PTree.set b (access_of_rmap r b) p) (Maps.PTree.empty _)
    (map Z.to_pos (tl (upto (Pos.to_nat next)))).

  Lemma make_access_get_aux : forall l f b t,
    Maps.PTree.get b (fold_right (fun b p => Maps.PTree.set b (access_of_rmap f b) p) t l) =
    if In_dec eq_block b l then Some (access_of_rmap f b) else Maps.PTree.get b t.
  Proof.
    induction l; simpl; auto; intros.
    destruct (eq_block a b).
    - subst; apply Maps.PTree.gss.
    - rewrite Maps.PTree.gso; last auto.
      rewrite IHl.
      if_tac; auto.
  Qed.

  Lemma make_access_get : forall next f b,
    Maps.PTree.get b (make_access next f) =
    if Pos.ltb b next then Some (access_of_rmap f b) else None.
  Proof.
    intros; unfold make_access.
    rewrite make_access_get_aux.
    if_tac; destruct (Pos.ltb_spec0 b next); auto.
    - rewrite in_map_iff in H; destruct H as (? & ? & Hin); subst.
      destruct (Pos.to_nat next) eqn: Hnext.
      { pose proof (Pos2Nat.is_pos next); lia. }
      simpl in Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
      apply In_upto in Hin.
      destruct x0; simpl in *; lia.
    - contradiction H.
      rewrite in_map_iff; do 2 eexists.
      { apply Pos2Z.id. }
      destruct (Pos.to_nat next) eqn: Hnext.
      { pose proof (Pos2Nat.is_pos next); lia. }
      simpl.
      rewrite in_map_iff; do 2 eexists.
      { rewrite -> Zminus_succ_l.
        unfold Z.succ. rewrite -> Z.add_simpl_r; reflexivity. }
      rewrite In_upto; lia.
  Qed.

  Definition make_contents (r : rmap) : Maps.PMap.t (Maps.ZMap.t memval) :=
    map_fold (fun '(b, ofs) x c => Maps.PMap.set b (Maps.ZMap.set ofs
      (match val_of x ≫= (fun v : agree V => memval_of (proj1_sig (elem_of_agree v))) with Some v => v | None => Undef end) (c !!! b)) c)
      (Maps.PMap.init (Maps.ZMap.init Undef)) r.

  Lemma make_contents_get : forall f (b : Values.block) ofs,
    Maps.ZMap.get ofs ((make_contents f) !!! b) = match f @ (b, ofs) ≫= (fun '(_, v) => v ≫= memval_of) with Some v => v | _ => Undef end.
  Proof.
    intros; unfold make_contents.
    apply (map_fold_ind (fun c f => Maps.ZMap.get ofs (c !!! b) = match f @ (b, ofs) ≫= (fun '(_, v) => v ≫= memval_of) with Some v => v | _ => Undef end)).
    - rewrite /lookup_total /pmap_lookup Maps.PMap.gi Maps.ZMap.gi /resource_at lookup_empty //.
    - intros (b1, ofs1) x ?? Hi H.
      destruct (eq_dec b1 b).
      + subst; rewrite /lookup_total /pmap_lookup Maps.PMap.gss.
        destruct (eq_dec ofs1 ofs).
        * subst; rewrite Maps.ZMap.gss /resource_at lookup_insert /=.
          destruct (val_of x); done.
        * rewrite Maps.ZMap.gso; last done.
          rewrite /resource_at lookup_insert_ne //.
          congruence.
      + rewrite /lookup_total /pmap_lookup Maps.PMap.gso; last done.
        rewrite /resource_at lookup_insert_ne //.
        congruence.
  Qed.

  Lemma make_contents_default : forall f (b : Values.block), (make_contents f !!! b).1 = Undef.
  Proof.
    intros; unfold make_contents.
    apply (map_fold_ind (fun c f => (c !!! b).1 = Undef)); try done.
    intros (b1, ofs) ?????.
    destruct (eq_dec b1 b).
    - subst; rewrite /lookup_total /pmap_lookup Maps.PMap.gss //.
    - rewrite /lookup_total /pmap_lookup Maps.PMap.gso //.
  Qed.

  Definition maxblock_of_rmap f := map_fold (fun '(b, _) _ c => Pos.max b c) 1%positive f.

  Lemma maxblock_max : forall f b ofs, (b > maxblock_of_rmap f)%positive -> f !! (b, ofs) = None.
  Proof.
    intros ???; unfold maxblock_of_rmap.
    apply (map_fold_ind (fun c f => (b > c)%positive -> f !! (b, ofs) = None)).
    - by rewrite lookup_empty.
    - intros (b1, ?) ???? IH ?.
      destruct (eq_dec b1 b); first lia.
      rewrite lookup_insert_ne; last congruence.
      apply IH; lia.
  Qed.

  Program Definition mem_of_rmap f : mem :=
    {| Mem.mem_contents := make_contents f;
       Mem.mem_access := (fun _ _ => None, make_access (maxblock_of_rmap f + 1)%positive f);
       Mem.nextblock := (maxblock_of_rmap f + 1)%positive |}.
  Next Obligation.
  Proof.
    intros; rewrite /Maps.PMap.get make_access_get.
    simple_if_tac; last done.
    apply perm_of_res_max.
  Qed.
  Next Obligation.
  Proof.
    intros.
    rewrite /Maps.PMap.get make_access_get.
    destruct (Pos.ltb_spec b (maxblock_of_rmap f + 1)%positive); done.
  Qed.
  Next Obligation.
  Proof.
    apply make_contents_default.
  Qed.

  Lemma mem_of_rmap_coherent : forall n f, ✓{n} f -> coherent n (mem_of_rmap f) f.
  Proof.
    intros; split; first done.
    intros (b, ofs); simpl.
    repeat split.
    - rewrite /contents_cohere /contents_at /= => ? Hv.
      rewrite make_contents_get Hv //.
    - rewrite /access_cohere /access_at /=.
      rewrite /Maps.PMap.get make_access_get.
      destruct (Pos.ltb_spec b (maxblock_of_rmap f + 1)%positive).
      + apply perm_order''_refl.
      + simpl. rewrite /resource_at maxblock_max; last lia.
        rewrite perm_of_res_None //.
    - rewrite /max_access_cohere /max_access_at /access_at /=.
      rewrite /Maps.PMap.get make_access_get.
      destruct (Pos.ltb_spec b (maxblock_of_rmap f + 1)%positive).
      + apply perm_order''_refl.
      + simpl. rewrite /resource_at maxblock_max //; lia.
    - rewrite /alloc_cohere /= => ?.
      rewrite /resource_at maxblock_max //; lia.
  Qed.

  Local Lemma coherent_rel_exists n f :
    (∃ m, coherent_rel n m f) ↔ ✓{n} f.
  Proof.
    split.
    - intros [m Hrel]. eapply coherent_valid, Hrel.
    - intros; eexists; apply mem_of_rmap_coherent; auto.
  Qed.

  Local Lemma coherent_rel_unit n m : coherent_rel n m ε.
  Proof.
    split. { apply uora_unit_validN. }
    simpl; intros; rewrite /resource_at lookup_empty /=.
    apply coherent_None.
  Qed.

  Local Lemma coherent_rel_discrete :
    OfeDiscrete V → ViewRelDiscrete coherent_rel.
  Proof.
    intros ? n m f [Hv Hrel].
    split; last done.
    by apply ora_discrete_valid_iff_0.
  Qed.

  Lemma rmap_orderN_includedN : ∀n f1 f2, ✓{n} f2 -> f1 ≼ₒ{n} f2 -> f1 ≼{n} f2.
  Proof.
    intros ??? Hvalid; rewrite lookup_includedN; intros.
    specialize (H i); specialize (Hvalid i).
    destruct (f1 !! i) as [x1|] eqn: Hf1, (f2 !! i) as [x2|] eqn: Hf2; rewrite ?Hf1 Hf2 /= in H Hvalid |- *; try done.
    - rewrite Some_includedN.
      destruct x1, x2; try done.
      + destruct H as [Hd Hv], Hvalid.
        apply agree_order_dist in Hv; last done.
        destruct Hd; subst; first by left.
        right; eexists (YES DfracDiscarded I v).
        rewrite /op /ora_op /= /shared_op_instance.
        destruct (readable_dfrac_dec _); try done.
        split; auto; rewrite agree_idemp //.
      + hnf in H; subst; auto.
    - rewrite option_includedN; auto.
  Qed.

  Local Lemma coherent_rel_order : ∀n a x y, x ≼ₒ{n} y → coherent_rel n a y → coherent_rel n a x.
  Proof.
    intros ???? Hord [? Hy].
    eapply coherent_mono; first (by split); auto.
    apply rmap_orderN_includedN; auto.
  Qed.

End rel.

Arguments resource_at {_} _ _.
Arguments coherent_loc {_} {_} _ _ _.

Local Existing Instance coherent_rel_discrete.

(** [juicy_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation juicy_view V := (view (@coherent _ _ V)).
Definition juicy_viewO (V : ofe) `{resource_ops V} : ofe := viewO (coherent_rel V).
Definition juicy_viewC (V : ofe) `{resource_ops V} : cmra := viewC (coherent_rel V).
Definition juicy_viewUC (V : ofe) `{resource_ops V} : ucmra := viewUC (coherent_rel V).
Canonical Structure juicy_viewR (V : ofe) `{resource_ops V} : ora := view.viewR (coherent_rel V) (coherent_rel_order V).
Canonical Structure juicy_viewUR (V : ofe) `{resource_ops V} : uora := viewUR (coherent_rel V).

Section definitions.
  Context {V : ofe} {ResOps : resource_ops V}.

  Definition juicy_view_auth (dq : dfrac) (m : leibnizO mem) : juicy_viewUR V :=
    ●V{dq} m.
  Definition juicy_view_frag (k : address) (dq : dfrac) (rsh : readable_dfrac dq) (v : V) : juicy_viewUR V :=
    ◯V {[k := YES dq rsh (to_agree v)]}.
  Definition juicy_view_frag_no (k : address) (dq : share) (rsh : ~readable_share dq) : juicy_viewUR V :=
    ◯V {[k := NO dq rsh]}.
End definitions.

Section lemmas.
  Context {V : ofe} {ResOps : resource_ops V}.
  Implicit Types (m : mem) (q : shareR) (dq : dfrac) (v : V).

  Global Instance : Params (@juicy_view_auth) 3 := {}.
  Global Instance juicy_view_auth_ne dq : NonExpansive (juicy_view_auth (V:=V) dq).
  Proof. solve_proper. Qed.
  Global Instance juicy_view_auth_proper dq : Proper ((≡) ==> (≡)) (juicy_view_auth (V:=V) dq).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@juicy_view_frag) 4 := {}.
  Global Instance juicy_view_frag_ne k rsh oq : NonExpansive (juicy_view_frag (V:=V) k rsh oq).
  Proof. solve_proper. Qed.
  Global Instance juicy_view_frag_proper k rsh oq : Proper ((≡) ==> (≡)) (juicy_view_frag (V:=V) k rsh oq).
  Proof. apply ne_proper, _. Qed.

  Lemma juicy_view_frag_irrel k dq rsh1 rsh2 v : juicy_view_frag k dq rsh1 v ≡ juicy_view_frag k dq rsh2 v.
  Proof. apply view_frag_proper, (singletonM_proper(M := gmap address)), YES_irrel. Qed.

  Lemma juicy_view_frag_no_irrel k sh rsh1 rsh2 : juicy_view_frag_no k sh rsh1 ≡ juicy_view_frag_no k sh rsh2.
  Proof. by apply view_frag_proper, (singletonM_proper(M := gmap address)). Qed.

  (* Helper lemmas *)
  Lemma elem_of_to_agree : forall {A} (v : A), proj1_sig (elem_of_agree (to_agree v)) = v.
  Proof.
    intros; destruct (elem_of_agree (to_agree v)); simpl.
    rewrite -elem_of_list_singleton //.
  Qed.

  Local Lemma coherent_rel_lookup n m k x :
    coherent_rel V n m {[k := x]} ↔ ✓{n} x ∧ coherent_loc m k (resR_to_resource _ (Some x)).
  Proof.
    split.
    - intros [Hv Hloc].
      specialize (Hv k); specialize (Hloc k).
      rewrite /resource_at lookup_singleton // in Hv Hloc.
    - intros [Hv Hloc]; split.
      + intros i; destruct (decide (k = i)).
        * subst; rewrite lookup_singleton //.
        * rewrite lookup_singleton_ne //.
      + intros i; rewrite /resource_at; destruct (decide (k = i)).
        * subst; rewrite lookup_singleton //.
        * rewrite lookup_singleton_ne // /=; apply coherent_None.
  Qed.

  (** Composition and validity *)
  Lemma juicy_view_auth_dfrac_op dp dq m :
    juicy_view_auth (dp ⋅ dq) m ≡
    juicy_view_auth dp m ⋅ juicy_view_auth dq m.
  Proof. by rewrite /juicy_view_auth view_auth_dfrac_op. Qed.
  Global Instance juicy_view_auth_dfrac_is_op dq dq1 dq2 m :
    IsOp dq dq1 dq2 → IsOp' (juicy_view_auth dq m) (juicy_view_auth dq1 m) (juicy_view_auth dq2 m).
  Proof. rewrite /juicy_view_auth. apply _. Qed.

  Lemma juicy_view_auth_dfrac_op_invN n dp m1 dq m2 :
    ✓{n} (juicy_view_auth dp m1 ⋅ juicy_view_auth dq m2) → m1 = m2.
  Proof. by intros ?%view_auth_dfrac_op_invN. Qed.
  Lemma juicy_view_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ (juicy_view_auth dp m1 ⋅ juicy_view_auth dq m2) → m1 = m2.
  Proof. by intros ?%view_auth_dfrac_op_inv. Qed.

  Lemma juicy_view_auth_dfrac_validN m n dq : ✓{n} juicy_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_validN. intuition. apply coherent_rel_unit.
  Qed.
  Lemma juicy_view_auth_dfrac_valid m dq : ✓ juicy_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_valid. intuition. apply coherent_rel_unit.
  Qed.
  Lemma juicy_view_auth_valid m : ✓ juicy_view_auth (DfracOwn Tsh) m.
  Proof. rewrite juicy_view_auth_dfrac_valid. done. Qed.

  Lemma juicy_view_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} (juicy_view_auth dq1 m1 ⋅ juicy_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof.
    rewrite view_auth_dfrac_op_validN. intuition. apply coherent_rel_unit.
  Qed.
  Lemma juicy_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ (juicy_view_auth dq1 m1 ⋅ juicy_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition. apply coherent_rel_unit.
  Qed.

  Lemma juicy_view_auth_op_validN n m1 m2 :
    ✓{n} (juicy_view_auth (DfracOwn Tsh) m1 ⋅ juicy_view_auth (DfracOwn Tsh) m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma juicy_view_auth_op_valid m1 m2 :
    ✓ (juicy_view_auth (DfracOwn Tsh) m1 ⋅ juicy_view_auth (DfracOwn Tsh) m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  (* Do we need to duplicate these for frag_no? *)
  Lemma juicy_view_frag_validN n k dq rsh v : ✓{n} juicy_view_frag k dq rsh v ↔ ✓ dq.
  Proof.
    rewrite view_frag_validN coherent_rel_exists singleton_validN.
    split; [intros [??] | split]; done.
  Qed.
  Lemma juicy_view_frag_valid k dq rsh v : ✓ juicy_view_frag k dq rsh v ↔ ✓ dq.
  Proof.
    rewrite cmra_valid_validN. setoid_rewrite juicy_view_frag_validN.
    naive_solver eauto using O.
  Qed.

  (* What's the interface we want at the higher level? *)
  Lemma juicy_view_frag_op k dq1 dq2 rsh1 rsh2 rsh v :
    juicy_view_frag k (dq1 ⋅ dq2) rsh v ≡ juicy_view_frag k dq1 rsh1 v ⋅ juicy_view_frag k dq2 rsh2 v.
  Proof. rewrite -view_frag_op singleton_op YES_op agree_idemp /juicy_view_frag //. Qed.
  Lemma juicy_view_frag_add k q1 q2 rsh1 rsh2 rsh v :
    juicy_view_frag k (DfracOwn (q1 ⋅ q2)) rsh v ≡
      juicy_view_frag k (DfracOwn q1) rsh1 v ⋅ juicy_view_frag k (DfracOwn q2) rsh2 v.
  Proof. rewrite -juicy_view_frag_op //. Qed.

  Lemma juicy_view_frag_op_validN n k dq1 dq2 rsh1 rsh2 v1 v2 :
    ✓{n} (juicy_view_frag k dq1 rsh1 v1 ⋅ juicy_view_frag k dq2 rsh2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN coherent_rel_exists singleton_op singleton_validN YES_op'.
    destruct (readable_dfrac_dec _).
    - split; intros [? Hv]; split; rewrite ?to_agree_op_validN // in Hv |- *.
    - apply dfrac_op_readable in n0; auto.
      split; first done. apply dfrac_error_invalid in n0; by intros [??].
  Qed.
  Lemma juicy_view_frag_op_valid k dq1 dq2 rsh1 rsh2 v1 v2 :
    ✓ (juicy_view_frag k dq1 rsh1 v1 ⋅ juicy_view_frag k dq2 rsh2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid. setoid_rewrite coherent_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid YES_op'.
    destruct (readable_dfrac_dec _).
    - split; intros [? Hv]; split; rewrite ?to_agree_op_valid // in Hv |- *.
    - apply dfrac_op_readable in n; auto.
      split; first done. apply dfrac_error_invalid in n; by intros [??].
  Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma juicy_view_frag_op_valid_L `{!LeibnizEquiv V} k dq1 dq2 rsh1 rsh2 v1 v2 :
    ✓ (juicy_view_frag k dq1 rsh1 v1 ⋅ juicy_view_frag k dq2 rsh2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 = v2.
  Proof. unfold_leibniz. apply juicy_view_frag_op_valid. Qed.

  Lemma juicy_view_both_dfrac_validN n dp m k dq rsh v :
    ✓{n} (juicy_view_auth dp m ⋅ juicy_view_frag k dq rsh v) ↔
      ✓ dp ∧ ✓ dq ∧ coherent_loc m k (Some (dq, Some v)).
  Proof.
    rewrite /juicy_view_auth /juicy_view_frag.
    rewrite view_both_dfrac_validN coherent_rel_lookup /=.
    rewrite elem_of_to_agree.
    intuition; try done.
    by destruct H.
  Qed.
  Lemma juicy_view_both_validN n m k dq rsh v :
    ✓{n} (juicy_view_auth (DfracOwn Tsh) m ⋅ juicy_view_frag k dq rsh v) ↔
      ✓ dq ∧ coherent_loc m k (Some (dq, Some v)).
  Proof. rewrite juicy_view_both_dfrac_validN. naive_solver done. Qed.
  Lemma juicy_view_both_dfrac_valid dp m k dq rsh v :
    ✓ (juicy_view_auth dp m ⋅ juicy_view_frag k dq rsh v) ↔
    ✓ dp ∧ ✓ dq ∧ coherent_loc m k (Some (dq, Some v)).
  Proof.
    rewrite /juicy_view_auth /juicy_view_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite coherent_rel_lookup; simpl.
    rewrite elem_of_to_agree.
    split; last by intuition.
    intros [? H]; split; auto; split; apply (H 0).
  Qed.
  Lemma juicy_view_both_valid m k dq rsh v :
    ✓ (juicy_view_auth (DfracOwn Tsh) m ⋅ juicy_view_frag k dq rsh v) ↔
    ✓ dq ∧ coherent_loc m k (Some (dq, Some v)).
  Proof. rewrite juicy_view_both_dfrac_valid. naive_solver done. Qed.

  Lemma juicy_view_frag_no_op k sh1 sh2 rsh1 rsh2 rsh :
    juicy_view_frag_no k (sh1 ⋅ sh2) rsh ≡ juicy_view_frag_no k sh1 rsh1 ⋅ juicy_view_frag_no k sh2 rsh2.
  Proof. rewrite -view_frag_op singleton_op /juicy_view_frag //. apply juicy_view_frag_no_irrel. Qed.

  Lemma juicy_view_frag_no_op_valid k sh1 sh2 rsh1 rsh2 :
    ✓ (juicy_view_frag_no k sh1 rsh1 ⋅ juicy_view_frag_no k sh2 rsh2) ↔
    ✓ (sh1 ⋅ sh2).
  Proof.
    rewrite view_frag_valid. setoid_rewrite coherent_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid //.
  Qed.

  (** Frame-preserving updates *)
(*  Lemma juicy_view_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    juicy_view_auth (DfracOwn Tsh) m ~~> juicy_view_auth (DfracOwn Tsh) (<[k := v]> m) ⋅ juicy_view_frag k dq v.
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & _ & _ & Hm).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf.
      intros [= <- <-]. eexists. do 2 (split; first done).
      rewrite lookup_insert. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & ? & Hm).
      eexists. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma juicy_view_alloc_big m m' dq :
    m' ##ₘ m →
    ✓ dq →
    juicy_view_auth (DfracOwn Tsh) m ~~>
      juicy_view_auth (DfracOwn Tsh) (m' ∪ m) ⋅ ([^op map] k↦v ∈ m', juicy_view_frag k dq v).
  Proof.
    intros. induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    rewrite IH //.
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (juicy_view_alloc _ k dq); last done.
    by apply lookup_union_None.
  Qed.

  Lemma juicy_view_delete m k v :
    juicy_view_auth (DfracOwn Tsh) m ⋅ juicy_view_frag k (DfracOwn Tsh) v ~~>
    juicy_view_auth (DfracOwn Tsh) (delete k m).
  Proof.
    apply view_update_dealloc=>n bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & _ & Hdf & _).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      exfalso. apply: dfrac_full_exclusive. apply Hdf.
    - edestruct (Hrel j) as (v' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists v'. do 2 (split; first done).
      rewrite lookup_delete_ne //.
  Qed.

  Lemma juicy_view_delete_big m m' :
    juicy_view_auth (DfracOwn Tsh) m ⋅ ([^op map] k↦v ∈ m', juicy_view_frag k (DfracOwn Tsh) v) ~~>
    juicy_view_auth (DfracOwn Tsh) (m ∖ m').
  Proof.
    induction m' as [|k v m' ? IH] using map_ind.
    { rewrite right_id_L big_opM_empty right_id //. }
    rewrite big_opM_insert //.
    rewrite [juicy_view_frag _ _ _ ⋅ _]comm assoc IH juicy_view_delete.
    rewrite -delete_difference. done.
  Qed.*)

  Global Instance exclusive_own_Tsh (v : agreeR V) : Exclusive(A := prodR dfracR (agreeR V)) (DfracOwn Tsh, v).
  Proof. apply _. Qed.

  Lemma coherent_store_outside : forall m b o bl m' loc r, Mem.storebytes m b o bl = Some m' ->
    ~adr_range (b, o) (length bl) loc ->
    coherent_loc m loc r ->
    coherent_loc m' loc r.
  Proof.
    intros ???????? Hrange (Hcontents & Hcur & Hmax & Halloc).
    split3; last split.
    - unfold contents_cohere, contents_at in *; intros.
      erewrite Mem.storebytes_mem_contents by eauto.
      destruct (eq_dec loc.1 b); [subst; rewrite Maps.PMap.gss | rewrite Maps.PMap.gso //; eauto].
      rewrite Mem.setN_other; eauto.
      { intros; unfold adr_range in *; destruct loc; simpl in *; lia. }
    - unfold access_cohere in *.
      erewrite <- storebytes_access; eauto.
    - unfold max_access_cohere, max_access_at in *.
      erewrite <- storebytes_access; eauto.
    - unfold alloc_cohere in *.
      erewrite Mem.nextblock_storebytes; eauto.
  Qed.

  Lemma get_setN : forall l z c i, (z <= i < z + length l)%Z -> Maps.ZMap.get i (Mem.setN l z c) = nth (Z.to_nat (i - z)) l Undef.
  Proof.
    induction l; simpl; intros; first lia.
    destruct (Z.to_nat (i - z)) eqn: Hi.
    - assert (i = z) as -> by lia.
      rewrite -> Mem.setN_other, Maps.ZMap.gss by lia; done.
    - rewrite IHl; last lia.
      replace (Z.to_nat (i - (z + 1))) with n by lia; done.
  Qed.

  Lemma coherent_store_in : forall m b o bl m' i dq v v', Mem.storebytes m b o bl = Some m' ->
    0 <= i < length bl -> memval_of v' = Some (nth i bl Undef) -> Mem.perm_order'' (perm_of_res (Some (dq, Some v))) (perm_of_res (Some (dq, Some v'))) ->
    coherent_loc m (b, o + Z.of_nat i)%Z (Some (dq, Some v)) ->
    coherent_loc m' (b, o + Z.of_nat i)%Z (Some (dq, Some v')).
  Proof.
    intros ??????????? Hv' Hperm (Hcontents & Hcur & Hmax & Halloc).
    split3; last split.
    - unfold contents_cohere, contents_at in *; simpl; intros ? Hv.
      rewrite Hv in Hv'; inv Hv'.
      erewrite Mem.storebytes_mem_contents by eauto.
      rewrite /= Maps.PMap.gss get_setN; last lia.
      replace (Z.to_nat _) with i by lia; done.
    - unfold access_cohere in *.
      erewrite <- storebytes_access by eauto.
      eapply perm_order''_trans; eauto.
    - unfold max_access_cohere, max_access_at in *.
      erewrite <- storebytes_access; eauto.
    - unfold alloc_cohere in *.
      erewrite Mem.nextblock_storebytes by eauto; intros.
      lapply Halloc; done.
  Qed.

  Existing Instance share_op_instance.

  Lemma writable_op_unreadable : forall n sh (Hr : readable_share sh) (v : agree V) (Hsh : writable0_share sh) x,
    ✓{n} (YES (DfracOwn sh) Hr v ⋅ x) ->
    exists sh' (nsh : ~readable_share sh'), x = NO sh' nsh ∧ exists rsh, forall (v : agree V), YES (DfracOwn sh) Hr v ⋅ x = YES (DfracOwn (sh ⋅ sh')) rsh v.
  Proof.
    intros.
    rewrite /op /ora_op /= in H |- *.
    destruct x.
    - destruct (readable_dfrac_dec _); try done.
      destruct H as [H _].
      rewrite comm in H; apply dfrac_valid_own_readable in H; tauto.
    - if_tac in H; try done.
      destruct (readable_share_dec _); try done; eauto.
  Qed.

  Lemma juicy_view_storebyte m m' k v v' b sh (Hr : readable_share sh) (Hsh : writable0_share sh)
    (Hstore : Mem.storebytes m k.1 k.2 [b] = Some m')
    (Hb : memval_of v' = Some b)
    (Hperm : forall sh', sepalg.join_sub sh sh' -> Mem.perm_order'' (perm_of_res (Some (DfracOwn sh', Some v))) (perm_of_res (Some (DfracOwn sh', Some v')))) :
      juicy_view_auth (DfracOwn Tsh) m ⋅ juicy_view_frag k (DfracOwn sh) Hr v ~~>
      juicy_view_auth (DfracOwn Tsh) m' ⋅ juicy_view_frag k (DfracOwn sh) Hr v'.
  Proof.
    apply view_update; intros ?? [Hv Hcoh].
    split.
    { intros i; specialize (Hv i).
      rewrite !lookup_op in Hv |- *.
      destruct (decide (i = k)); last by rewrite !lookup_singleton_ne in Hv |- *.
      subst; rewrite !lookup_singleton in Hv |- *.
      rewrite !Some_op_opM in Hv |- *; eapply writable_update, Hv; done. }
    intros loc; specialize (Hcoh loc); specialize (Hv loc).
    rewrite /resource_at !lookup_op in Hcoh Hv |- *.
    destruct (decide (loc = k)).
    - subst; rewrite !lookup_singleton in Hcoh Hv |- *.
      destruct (bf !! k) eqn: Hbf; rewrite Hbf /= in Hcoh Hv |- *.
      + destruct (writable_op_unreadable _ _ _ _ Hsh _ Hv) as (? & ? & -> & ? & Hop).
        rewrite /= -?Some_op !Hop /= in Hcoh Hv |- *.
        destruct k as (?, o); rewrite !elem_of_to_agree -(Z.add_0_r o) in Hcoh |- *.
        eapply (coherent_store_in _ _ _ _ _ O); eauto.
        apply Hperm; destruct Hv as [Hv _].
        edestruct share_op_join as [(? & ? & J) _]; first apply Hv; first done.
        by eexists.
      + destruct k as (?, o); rewrite !elem_of_to_agree -(Z.add_0_r o) in Hcoh |- *.
        eapply (coherent_store_in _ _ _ _ _ O); eauto.
        apply Hperm, sepalg.join_sub_refl.
    - rewrite !lookup_singleton_ne in Hcoh |- *; [| done..].
      eapply coherent_store_outside; eauto.
      destruct loc as (?, o1), k as (?, o); intros [??]; subst; simpl in *.
      assert (o1 = o) by lia; congruence.
  Qed.

  Lemma lookup_singleton_list : forall {A} {B : ora} (l : list A) (f : A -> B) k i, ([^op list] i↦v ∈ l, ({[adr_add k (Z.of_nat i) := f v]})) !! i ≡
    if adr_range_dec k (Z.of_nat (length l)) i then f <$> (l !! (Z.to_nat (i.2 - k.2))) else None.
  Proof.
    intros.
    remember (rev l) as l'; revert dependent l; induction l'; simpl; intros.
    { destruct l; simpl; last by apply app_cons_not_nil in Heql'.
      rewrite lookup_empty; if_tac; auto. }
    apply (f_equal (@rev _)) in Heql'; rewrite rev_involutive in Heql'; subst; simpl.
    rewrite lookup_proper; last apply big_opL_snoc.
    rewrite lookup_op IHl'; last by rewrite rev_involutive.
    destruct k as (?, o), i as (?, o').
    if_tac; [|if_tac].
    - destruct H; subst; simpl.
      rewrite lookup_singleton_ne; last by rewrite /adr_add; intros [=]; lia.
      rewrite if_true; last by rewrite app_length; lia.
      rewrite lookup_app.
      by destruct (lookup_lt_is_Some_2 (rev l') (Z.to_nat (o' - o))) as (? & ->); first lia.
    - destruct H0 as [-> Hrange].
      rewrite app_length /= in Hrange.
      assert (o' = o + Z.of_nat (length (rev l')))%Z as -> by (rewrite /adr_range in H; lia).
      rewrite /adr_add lookup_singleton /= list_lookup_middle //; lia.
    - rewrite lookup_singleton_ne //.
      rewrite /adr_add /=; intros [=]; subst; contradiction H0.
      split; auto; rewrite app_length /=; lia.
  Qed.

  Lemma coherent_loc_ne n m k r1 r2 : ✓{n} r1 -> r1 ≡{n}≡ r2 -> coherent_loc m k (resR_to_resource _ r1) -> coherent_loc m k (resR_to_resource _ r2).
  Proof.
    intros Hvalid H; apply resR_to_resource_ne in H; last done.
    destruct (resR_to_resource V r1) as [(d1, v1)|]; inv H; intros; last apply coherent_None.
    destruct y as (d2, v2); destruct H2 as [Hd Hv]; simpl in *; inv Hd.
    destruct H as (Hcontents & Hcur & Hmax & Halloc); split3; last split.
    - intros ?; simpl.
      intros H; apply Hcontents; simpl.
      inv Hv; try done.
      rewrite -H; eapply memval_of_ne; done.
    - unfold access_cohere in *.
      eapply perm_of_res_ne in Hv as <-; done.
    - done.
    - intros Hnext; specialize (Halloc Hnext); done.
  Qed.

  Lemma juicy_view_storebytes m m' k (vl vl' : list V) bl sh (Hr : readable_share sh) (Hsh : writable0_share sh)
    (Hstore : Mem.storebytes m k.1 k.2 bl = Some m')
    (Hv' : Forall2 (fun v' b => memval_of v' = Some b) vl' bl)
    (Hperm : Forall2 (fun v v' => forall sh', sepalg.join_sub sh sh' -> Mem.perm_order'' (perm_of_res (Some (DfracOwn sh', Some v))) (perm_of_res (Some (DfracOwn sh', Some v')))) vl vl') :
      juicy_view_auth (DfracOwn Tsh) m ⋅ ([^op list] i↦v ∈ vl, juicy_view_frag (adr_add k (Z.of_nat i)) (DfracOwn sh) Hr v) ~~>
      juicy_view_auth (DfracOwn Tsh) m' ⋅ ([^op list] i↦v ∈ vl', juicy_view_frag (adr_add k (Z.of_nat i)) (DfracOwn sh) Hr v).
  Proof.
    rewrite -!big_opL_view_frag; apply view_update; intros ?? [Hv Hcoh].
    assert (forall i, if adr_range_dec k (Z.of_nat (length vl)) i then
      exists v v', vl !! (Z.to_nat (i.2 - k.2)) = Some v /\ vl' !! (Z.to_nat (i.2 - k.2)) = Some v' /\ exists sh' rsh', sepalg.join_sub sh sh' /\
      (([^op list] k0↦x ∈ vl, {[adr_add k (Z.of_nat k0) := YES (DfracOwn sh) Hr (to_agree x)]}) ⋅ bf) !! i ≡ Some (YES (DfracOwn sh') rsh' (to_agree v)) /\
      (([^op list] k0↦x ∈ vl', {[adr_add k (Z.of_nat k0) := YES (DfracOwn sh) Hr (to_agree x)]}) ⋅ bf) !! i ≡ Some (YES (DfracOwn sh') rsh' (to_agree v'))
      else
      ((([^op list] k0↦x ∈ vl, {[adr_add k (Z.of_nat k0) := YES (DfracOwn sh) Hr (to_agree x)]}) ⋅ bf) !! i ≡
       (([^op list] k0↦x ∈ vl', {[adr_add k (Z.of_nat k0) := YES (DfracOwn sh) Hr (to_agree x)]}) ⋅ bf) !! i)) as Hlookup.
    { intros i; specialize (Hv i).
      pose proof (Forall2_length _ _ _ Hperm) as Hlen.
      rewrite !lookup_op !(lookup_singleton_list) in Hv; if_tac.
      * destruct k as (?, o), i as (?, o'); destruct H; subst; simpl.
        destruct (lookup_lt_is_Some_2 vl (Z.to_nat (o' - o))) as (? & Hv1); first lia.
        destruct (lookup_lt_is_Some_2 vl' (Z.to_nat (o' - o))) as (? & Hv2); first lia.
        eexists _, _; split; first done; split; first done.
        rewrite !lookup_op; setoid_rewrite lookup_singleton_list.
        rewrite -Hlen !if_true; [|split; auto..].
        rewrite Hv1 Hv2 /= in Hv |- *.
        destruct (bf !! (b0, o')) eqn: Hbf; rewrite Hbf in Hv |- *; last by rewrite op_None_right_id; eexists _, _; split; last done; apply sepalg.join_sub_refl.
        destruct (writable_op_unreadable _ _ _ _ Hsh _ Hv) as (? & ? & -> & ? & Heq).
        rewrite -!Some_op !Heq in Hv |- *; eexists _, _; split; last done.
        destruct Hv as [Hv _].
        edestruct share_op_join as [(? & ? & J) _]; first apply Hv; first done.
        by eexists.
      * rewrite !lookup_op !lookup_singleton_list -Hlen !if_false //. }
    split; intros i; specialize (Hlookup i).
    - specialize (Hv i).
      if_tac in Hlookup; last by rewrite -Hlookup.
      destruct Hlookup as (? & ? & ? & ? & ? & ? & ? & Heq & ->).
      rewrite Heq in Hv; destruct Hv; done.
    - specialize (Hcoh i); specialize (Hv i); unfold resource_at in *.
      if_tac in Hlookup.
      + destruct Hlookup as (? & ? & Hl1 & Hl2 & ? & ? & ? & Hv1 & Hv2).
        rewrite Hv1 in Hv; destruct Hv as [??].
        eapply (coherent_loc_ne 0); [| symmetry; apply equiv_dist; done |]; try done.
        eapply (coherent_loc_ne 0) in Hcoh; last apply equiv_dist, Hv1; last by rewrite Hv1.
        destruct k as (?, o), i as (?, o'), H; subst; simpl in *.
        replace o' with (o + Z.of_nat (Z.to_nat (o' - o)))%Z in Hcoh |- * by lia.
        eapply coherent_store_in; eauto.
        * erewrite <- Forall2_length, <- Forall2_length; eauto; lia.
        * rewrite Forall2_lookup in Hv'; specialize (Hv' (Z.to_nat (o' - o))).
          rewrite Hl2 in Hv'; inv Hv'.
          erewrite nth_lookup_Some by eauto.
          rewrite elem_of_to_agree //.
        * rewrite Forall2_lookup in Hperm; specialize (Hperm (Z.to_nat (o' - o))).
          rewrite Hl1 Hl2 in Hperm; inv Hperm.
          rewrite !elem_of_to_agree; eauto.
      + eapply coherent_loc_ne; [| apply equiv_dist, Hlookup |]; first done.
        eapply coherent_store_outside; eauto.
        destruct k; erewrite <- Forall2_length, <- Forall2_length; eauto.
  Qed.

  Lemma juicy_view_auth_persist dq m : readable_dfrac dq ->
    juicy_view_auth dq m ~~> juicy_view_auth DfracDiscarded m.
  Proof. apply view_update_auth_persist. Qed.

  Lemma perm_of_readable_share : forall sh, readable_share sh -> Mem.perm_order' (perm_of_sh sh) Readable.
  Proof.
    intros; rewrite /perm_of_sh.
    if_tac; if_tac; try constructor; done.
  Qed.

  Lemma readable_dfrac_readable : forall dq, readable_dfrac dq -> Mem.perm_order' (perm_of_dfrac dq) Readable.
  Proof.
    destruct dq; simpl; try if_tac; try constructor; try done.
    apply perm_of_readable_share.
  Qed.

  Lemma readable_dfrac_discarded : forall dq dq', readable_dfrac dq -> ✓(dq ⋅ dq') -> Mem.perm_order'' (perm_of_dfrac (dq ⋅ dq')) (perm_of_dfrac (DfracDiscarded ⋅ dq')).
  Proof.
    intros ??? Hvalid; destruct dq; [| apply perm_order''_refl |].
    - destruct dq'; simpl.
      + if_tac.
        * rewrite (@cmra_comm shareR); apply perm_of_sh_mono; rewrite (@cmra_comm shareR) //.
        * destruct (readable_dfrac_dec (DfracOwn s ⋅ DfracOwn s0)); first by apply readable_dfrac_readable in r.
          apply dfrac_op_readable in n; auto.
          rewrite /dfrac_error /= in n; if_tac in n; done.
      + if_tac; try done; constructor.
      + repeat if_tac; try done; try constructor.
        * destruct Hvalid; rewrite (@cmra_comm shareR); apply perm_of_sh_mono; rewrite (@cmra_comm shareR) //.
        * contradiction H0; eapply (perm_order''_trans _ _ (Some _)); last done.
          destruct Hvalid; rewrite (@cmra_comm shareR); apply perm_of_sh_mono; rewrite (@cmra_comm shareR) //.
    - apply perm_of_dfrac_mono; try done.
      exists (DfracOwn s).
      rewrite -assoc (comm _ dq') assoc //.
  Qed.

  (* DfracDiscarded acts as a minimum readable share *)
  Lemma juicy_view_frag_persist k dq rsh v :
    juicy_view_frag k dq rsh v ~~> juicy_view_frag k DfracDiscarded I v.
  Proof.
    apply view_update_frag=>m n bf [Hv Hrel].
    assert (forall o, bf !! k = Some o -> ∃ (v' : agree V) rsh' rsh'', Some (to_agree v) ⋅ val_of o = Some v' ∧
      YES dq rsh (to_agree v) ⋅ o = YES (dq ⋅ dfrac_of o) rsh' v' ∧
      YES DfracDiscarded I (to_agree v) ⋅ o = YES (DfracDiscarded ⋅ dfrac_of o) rsh'' v') as Hk.
    { specialize (Hv k); rewrite lookup_op lookup_singleton in Hv.
      intros ? Hbf; rewrite Hbf -Some_op in Hv.
      pose proof (shared_op_alt _ (YES dq rsh (to_agree v)) o) as Hop; destruct (readable_dfrac_dec _);
        last by destruct (dfrac_error _); [rewrite Hop in Hv | destruct Hop as (? & ? & ? & ? & ? & ?)].
      destruct Hop as (? & Hval & ?).
      pose proof (shared_op_alt _ (YES DfracDiscarded I (to_agree v)) o) as Hop'.
      destruct (readable_dfrac_dec _).
      * destruct Hop' as (? & Hval' & ?).
        rewrite Hval' in Hval; inv Hval; eauto 6.
      * destruct (dfrac_error _) eqn: Herr; last by destruct Hop' as (? & ? & ? & ? & ? & ?).
        rewrite dfrac_error_discarded in Herr.
        exfalso; eapply dfrac_error_unreadable, r; apply op_dfrac_error; done. }
    split.
    - intros i; specialize (Hv i); rewrite !lookup_op in Hv |- *.
      destruct (decide (i = k)); last by rewrite !lookup_singleton_ne in Hv |- *.
      subst; rewrite !lookup_singleton in Hv |- *.
      destruct (bf !! k) as [o|] eqn: Hbf; rewrite Hbf in Hv |- *; try done.
      rewrite -!Some_op in Hv |- *.
      destruct (Hk _ eq_refl) as (? & ? & ? & ? & Hop & Hop'); rewrite Hop in Hv; rewrite Hop'.
      destruct Hv as [Hd ?]; split; try done.
      destruct (dfrac_of o); simpl in *; try done.
      { apply dfrac_valid_own_readable in Hd; auto. }
      { destruct dq; try done; destruct Hd as [Hn (? & ? & J%sepalg.join_comm)%share_valid2_joins]; split; try done; intros X;
          contradiction Hn; eapply join_writable01; eauto. }
    - intros i; specialize (Hrel i); specialize (Hv i); rewrite /resource_at !lookup_op in Hrel Hv |- *.
      destruct (decide (i = k)); last by rewrite !lookup_singleton_ne in Hrel Hv |- *.
      subst; rewrite !lookup_singleton !Some_op_opM in Hrel Hv |- *.
      destruct Hrel as (Hcontents & Hcur & Hmax & Halloc); split3; last split.
      + intros ? H; apply Hcontents; simpl in *.
        destruct (bf !! k) eqn: Hbf; rewrite Hbf /= in H |- *; try done.
        destruct (Hk _ eq_refl) as (? & ? & ? & ? & Hop & Hop'); rewrite Hop; rewrite Hop' // in H.
      + unfold access_cohere in *.
        eapply perm_order''_trans; first done; simpl.
        destruct (bf !! k) eqn: Hbf; rewrite Hbf /= in Hv |- *; last by apply perm_of_res_discarded.
        destruct (Hk _ eq_refl) as (? & ? & ? & ? & Hop & Hop'); rewrite Hop Hop' /=.
        apply perm_of_res_discarded; try done.
        by rewrite Hop in Hv; destruct Hv.
      + unfold max_access_cohere in *.
        eapply perm_order''_trans; first done.
        destruct (bf !! k) eqn: Hbf; rewrite Hbf /= in Hv |- *; last by apply readable_dfrac_readable.
        destruct (Hk _ eq_refl) as (? & ? & ? & ? & Hop & Hop'); rewrite Hop Hop' /=.
        apply readable_dfrac_discarded; try done.
        by rewrite Hop in Hv; destruct Hv.
      + intros H; specialize (Halloc H); done.
  Qed.

  (** Typeclass instances *)
(*  Global Instance juicy_view_frag_core_id k dq rsh v : OraCoreId dq → OraCoreId (juicy_view_frag k dq rsh v).
  Proof. apply _. Qed. *)

  Global Instance juicy_view_ora_discrete : OfeDiscrete V → OraDiscrete (juicy_viewR V).
  Proof. apply _. Qed.

(*  Global Instance juicy_view_frag_mut_is_op dq dq1 dq2 k v :
    IsOp dq dq1 dq2 →
    IsOp' (juicy_view_frag k dq v) (juicy_view_frag k dq1 v) (juicy_view_frag k dq2 v).
  Proof. rewrite /IsOp' /IsOp => ->. apply juicy_view_frag_op. Qed.*)
End lemmas.

(*
(** Functor *)
Program Definition juicy_viewURF (F : oFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := juicy_viewUR (oFunctor_car F A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=coherent_rel (oFunctor_car F A1 B1))
              (rel':=coherent_rel (oFunctor_car F A2 B2))
              (gmapO_map (oFunctor_map F fg))
              (gmapO_map (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -{2}(agree_map_id va).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_ora_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hdval & Hm).
  exists (oFunctor_map F fg v).
  rewrite Hm. split; last by auto.
  rewrite Hagree. rewrite agree_map_to_agree. done.
Qed.

Global Instance juicy_viewURF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → uorarFunctorContractive (juicy_viewURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply oFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition juicy_viewRF (K : Type) `{Countable K} (F : oFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := juicy_viewR K (oFunctor_car F A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=coherent_rel K (oFunctor_car F A1 B1))
              (rel':=coherent_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Solve Obligations with apply juicy_viewURF.

Global Instance juicy_viewRF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → OrarFunctorContractive (juicy_viewRF K F).
Proof. apply juicy_viewURF_contractive. Qed.*)

Global Typeclasses Opaque juicy_view_auth juicy_view_frag.
