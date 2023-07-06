From iris.algebra Require Import agree.
Require Import VST.sepcomp.mem_lemmas.
From VST.veric Require Import base Memory juicy_base shares shared resource_map gen_heap dshare.
Require Import VST.zlist.sublist.
Export Values.

Open Scope Z.

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

Definition perm_of_sh' (s : share_car) :=
  match s with Share sh => perm_of_sh sh | ShareBot => None end.

Definition perm_of_dfrac dq :=
  match dq with
  | DfracOwn sh => perm_of_sh' sh
  | DfracBoth sh => if Mem.perm_order'_dec (perm_of_sh' sh) Readable then perm_of_sh' sh else Some Readable
  end.

(* Why do we force locks to nonempty? *)
Definition perm_of_res (r: dfrac * option resource) :=
  match r with
  | (dq, Some (VAL _)) => perm_of_dfrac dq
  | (DfracOwn (Share sh), _) => if eq_dec sh Share.bot then None else Some Nonempty
  | (DfracBoth _, _) => Some Nonempty
  | _ => None
  end.

Lemma perm_of_res_cases : forall dq r, (exists v, r = Some (VAL v) /\ perm_of_res (dq, r) = perm_of_dfrac dq) \/
  (forall v, r ≠ Some (VAL v)) /\ perm_of_res (dq, r) = if decide (dq = ε) then None else if decide (dq = DfracOwn ShareBot) then None else Some Nonempty.
Proof.
  intros; simpl.
  destruct dq as [[|]|], r as [[| |]|]; eauto; right; if_tac; subst; simpl; destruct (decide _); try done;
    by inv e.
Qed.

Lemma perm_of_sh_None: forall sh, perm_of_sh sh = None -> sh = Share.bot.
Proof.
  intros ?.
  unfold perm_of_sh.
  if_tac; if_tac; try discriminate.
  if_tac; done.
Qed.

Lemma perm_of_sh_bot : perm_of_sh Share.bot = None.
Proof.
  rewrite /perm_of_sh.
  pose proof bot_unreadable.
  rewrite eq_dec_refl !if_false; auto.
Qed.

Lemma perm_of_sh_mono : forall (sh1 sh2 : shareR), (✓ (sh1 ⋅ sh2))%stdpp -> Mem.perm_order'' (perm_of_sh' (sh1 ⋅ sh2)) (perm_of_sh' sh1).
Proof.
  intros ?? H.
  apply share_valid2_joins in H as (s1 & s2 & ? & -> & -> & H & J).
  rewrite H /= /perm_of_sh.
  destruct (writable0_share_dec s1).
  { eapply join_writable01 in w; eauto.
    rewrite -> if_true by auto.
    if_tac; if_tac; simpl; try constructor.
    subst; apply join_Tsh in J as (-> & ->); done. }
  if_tac; [repeat if_tac; constructor|].
  destruct (readable_share_dec s1).
  { eapply join_readable1 in r; eauto.
    rewrite (if_true _ _ _ _ _ r); constructor. }
  repeat if_tac; try constructor.
  subst; apply join_Bot in J as (-> & ->); done.
Qed.

Lemma perm_order_antisym : forall p1 p2, ~perm_order p1 p2 -> perm_order p2 p1.
Proof.
  destruct p1, p2; try constructor; intros X; contradiction X; constructor.
Qed.

Lemma perm_order'_antisym : forall p1 p2, ~Mem.perm_order' p1 p2 -> Mem.perm_order'' (Some p2) p1.
Proof.
  destruct p1; simpl; auto; apply perm_order_antisym.
Qed.

Lemma perm_of_dfrac_mono : forall d1 d2, (✓d2)%stdpp -> d1 ≼ d2 -> Mem.perm_order'' (perm_of_dfrac d2) (perm_of_dfrac d1).
Proof.
  intros ?? Hv [d0 ->%leibniz_equiv].
  destruct d1, d0; simpl in *; repeat if_tac; auto; try (apply perm_order''_refl || (by apply perm_of_sh_mono) || (by destruct Hv as (? & Hop & ?); apply perm_of_sh_mono; rewrite Hop) || constructor).
  - destruct Hv as (? & Hv & ?); eapply perm_order''_trans, perm_of_sh_mono; [apply perm_order'_antisym|]; eauto; rewrite Hv //.
  - destruct Hv as (? & Hv & ?); eapply perm_order''_trans, perm_of_sh_mono; [apply perm_order'_antisym|]; eauto; rewrite Hv //.
  - destruct Hv as (? & Hv & ?); eapply perm_order''_trans, perm_of_sh_mono; [apply perm_order'_antisym|]; eauto; rewrite Hv //.
Qed.

Lemma perm_of_res_ne n d (r1 r2 : optionO (leibnizO resource)) : r1 ≡{n}≡ r2 -> perm_of_res (d, r1) = perm_of_res (d, r2).
Proof.
  intros H; inv H; try inv H0; auto.
Qed.

Lemma perm_of_res_mono d1 d2 (r : option resource) : ✓d2 -> d1 ≼ d2 -> Mem.perm_order'' (perm_of_res (d2, r)) (perm_of_res (d1, r)).
Proof.
  intros ? Hd.
  destruct (perm_of_res_cases d2 r) as [(v2 & ? & Hperm2) | (Hno2 & Hperm2)],
    (perm_of_res_cases d1 r) as [(v1 & Hr & Hperm1) | (Hno1 & Hperm1)]; subst.
  - inv Hr; rewrite Hperm1 Hperm2; apply perm_of_dfrac_mono; auto.
  - by contradiction (Hno1 v2).
  - by contradiction (Hno2 v1).
  - rewrite Hperm1 Hperm2; clear - H Hd.
    rewrite dfrac_included_eq in Hd.
    destruct (decide (d1 = ε)); first apply perm_order''_None.
    destruct (decide (d1 = _)); first apply perm_order''_None.
    rewrite !if_false; first constructor.
    + intros ->; done.
    + intros ->; destruct d1; try done; simpl in Hd.
      destruct Hd as (? & Hd).
      symmetry in Hd; apply share_op_join in Hd as (? & ? & -> & -> & (-> & ->)%join_Bot); done.
Qed.

(*Global Program Instance resource_ops : resource_ops (leibnizO resource) := { perm_of_res := perm_of_res; memval_of r := match r with VAL v => Some v | _ => None end }.
Next Obligation.
Proof.
  discriminate.
Qed.
Next Obligation.
Proof.
  discriminate.
Qed.
Next Obligation.
Proof.
  intros ???.
  pose proof (readable_dfrac_readable _ H).
  split.
  - destruct (perm_of_res_cases d r) as [(v & -> & Hperm) | (Hno & Hperm)]; rewrite Hperm /= perm_of_sh_bot // /=.
    rewrite !if_false; first by destruct r as [[| |]|]; try constructor; contradiction (Hno v).
    + intros ->; done.
    + intros ->; simpl in H.
      contradiction bot_unreadable.
  - intros ? Hvalid.
    pose proof (dfrac_op_readable' _ _ (or_introl H) Hvalid) as Hreadable%readable_dfrac_readable.
    destruct (perm_of_res_cases (d ⋅ d2) r) as [(v & -> & Hperm) | (Hno & Hperm)]; rewrite Hperm; clear Hperm.
    + destruct d2; rewrite /= left_id; if_tac; try done; apply (perm_of_dfrac_mono (DfracOwn _)); try done; eexists; rewrite (@cmra_comm dfracR) //.
      instantiate (1 := DfracDiscarded ⋅ d); rewrite assoc dfrac_op_own_discarded //.
    + destruct (perm_of_res_cases (DfracDiscarded ⋅ d2) r) as [(v & -> & Hperm) | (_ & Hperm)]; first (by contradiction (Hno v)); rewrite Hperm /=; clear Hperm.
      destruct (decide (DfracDiscarded ⋅_ = _)); first apply perm_order''_None.
      destruct (decide (DfracDiscarded ⋅_ = _)); first apply perm_order''_None.
      rewrite !if_false; first constructor.
      * intros X; rewrite X // in Hvalid.
      * intros X; rewrite X /= perm_of_sh_bot // in Hreadable.
Qed.
Next Obligation.
Proof.
  simpl.
  destruct r; try apply perm_order''_refl.
  destruct d as [[|]|]; simpl; try if_tac; try constructor; try apply perm_order''_None.
  - destruct (perm_of_sh sh) eqn: Hs; simpl; try constructor.
    by apply perm_of_sh_None in Hs.
  - destruct (perm_of_sh' _) eqn: Hs; simpl; try constructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros.
  destruct r as (d, r).
  destruct (perm_of_res_cases d r) as [(v & -> & Hperm) | (Hno & Hperm)]; rewrite Hperm /=; clear Hperm.
  - apply perm_order''_refl.
  - if_tac; first apply perm_order''_None.
    if_tac; first apply perm_order''_None.
    rewrite /perm_of_res' /=.
    destruct (perm_of_dfrac d) eqn: Hd; first constructor.
    destruct d as [[|]|]; simpl in Hd; try done.
    + apply perm_of_sh_None in Hd as ->; done.
    + if_tac in Hd; try done.
      rewrite -> Hd in *; done.
Qed.
Next Obligation.
Proof.
  simpl; intros.
  inv H; done.
Qed.*)

Definition perm_of_res_lock (r: dfrac * option resource) :=
  match r with
  | (q, Some (LK _ _ _)) => match q with
                   | DfracOwn (Share sh) => perm_of_sh (Share.glb Share.Rsh sh)
                   | DfracBoth _ => Some Readable
                   | _ => None
                   end
  | _ => None
  end.

Lemma Rsh_not_top: Share.Rsh <> Share.top.
Proof.
unfold Share.Rsh.
case_eq (Share.split Share.top); intros.
simpl; intro. subst.
apply nonemp_split_neq2 in H.
apply H; auto.
apply top_share_nonidentity.
Qed.

Lemma perm_of_sh_fullshare: perm_of_sh fullshare = Some Freeable.
Proof. unfold perm_of_sh.
  rewrite if_true. rewrite -> if_true by auto. auto.
   unfold fullshare.
   apply writable_writable0.
   apply writable_share_top.
Qed.

Lemma nonreadable_extern_retainer: ~readable_share extern_retainer.
unfold extern_retainer, readable_share.
intro H; apply H; clear H.
assert (Share.glb Share.Rsh
     (fst (Share.split Share.Lsh)) = Share.bot); [ | rewrite H; auto].
apply sub_glb_bot with Share.Lsh.
destruct (Share.split Share.Lsh) eqn:H.
apply Share.split_together in H.
simpl.
rewrite <- H.
apply leq_join_sub.
apply Share.lub_upper1.
apply glb_Rsh_Lsh.
Qed.

Lemma Lsh_nonreadable: ~readable_share Share.Lsh.
Proof.
unfold readable_share; intros.
rewrite glb_Rsh_Lsh.
auto.
Qed.

Lemma perm_order''_min : forall s, perm_order'' (perm_of_sh s) (if eq_dec s Share.bot then None else Some Nonempty).
Proof.
  intros; unfold perm_of_sh; repeat if_tac; constructor.
Qed.

Lemma perm_order''_Freeable : forall s, perm_order'' (Some Freeable) s.
Proof.
  destruct s; constructor.
Qed.

Lemma perm_of_sh_glb : forall sh1 sh2, perm_order'' (perm_of_sh sh1) (perm_of_sh (Share.glb sh2 sh1)).
Proof.
  intros; unfold perm_of_sh.
  pose proof (Share.glb_lower2 sh2 sh1) as Hglb.
  if_tac.
  - if_tac; first apply perm_order''_Freeable.
    repeat if_tac; try constructor.
    rewrite H2 in Hglb.
    eapply Share.ord_antisym in Hglb; last apply Share.top_correct; contradiction.
  - rewrite (if_false _ (writable0_share_dec _)).
    if_tac; first by repeat if_tac; constructor.
    rewrite (if_false _ (readable_share_dec _)).
    repeat if_tac; try constructor.
    + subst.
      contradiction H2; apply Share.glb_bot.
    + intros X; contradiction H0; unfold readable_share, nonempty_share in *.
      intros X1%identity_share_bot; contradiction X.
      rewrite (Share.glb_commute sh2) -Share.glb_assoc X1 Share.glb_commute Share.glb_bot.
      apply bot_identity.
    + intros X; contradiction H; unfold writable0_share in *.
      rewrite -!leq_join_sub in X |- *.
      eapply Share.ord_trans; done.
Qed.

Lemma perm_of_empty_inv {s} : perm_of_sh s = None -> s = Share.bot.
Proof.
  apply perm_of_sh_None.
Qed.

(*Lemma writable_join_sub: forall loc phi1 phi2,
  join_sub phi1 phi2 -> writable loc phi1 -> writable loc phi2.
Proof.
intros.
hnf in H0|-*.
destruct H; generalize (resource_at_join _ _ _ loc H); clear H.
revert H0; destruct (phi1 @ loc); intros; try contradiction.
destruct H0; subst.
inv H.
split. eapply join_writable01; eauto. auto.
contradiction (join_writable0_readable RJ H0 rsh2).
Qed.

Lemma writable_inv: forall phi loc, writable loc phi ->
  exists sh, exists rsh, exists k, exists pp,
       phi @ loc = YES sh rsh k pp /\
       writable0_share sh /\
       isVAL k.
Proof.
simpl.
intros phi loc H.
destruct (phi @ loc); try solve [inversion H].
destruct H.
do 4 eexists. split. reflexivity. split; auto.
Qed.

Lemma nreadable_inv: forall phi loc, ~readable loc phi
  -> (exists sh, exists nsh, phi @ loc = NO sh nsh)
   \/ (exists sh, exists rsh, exists k, exists pp, phi @ loc = YES sh rsh k pp /\ ~isVAL k)
   \/ (exists k, exists pp, phi @ loc = PURE k pp).
Proof.
intros.
simpl in H.
destruct (phi@loc); eauto 50.
Qed.*)

(*Definition ord_jm jm {n r} (Hord : m_phi jm ≼ₒ{n} r) :
  {jm' | m_phi jm' = r ∧ m_dry jm' = m_dry jm}.
Proof.
  apply juicy_mem_resource.

Definition access_of_rmap r b ofs k :=
  match k with
  | Max => perm_of_res' (r @ (b, ofs))
  | Cur => perm_of_res (r @ (b, ofs))
  end.

Definition make_access (next : block) (r : rmap) :=
  fold_right (fun b m => Maps.PTree.set b (access_of_rmap r b) m) (Maps.PTree.empty _)
  (map Z.to_pos (tl (upto (Pos.to_nat next)))).

Lemma make_access_get_aux : forall l r b t,
  (fold_right (fun b m => Maps.PTree.set b (access_of_rmap r b) m) t l) !! b =
  if In_dec eq_block b l then Some (access_of_rmap r b) else t !! b.
Proof.
  induction l; simpl; auto; intros.
  destruct (eq_block a b).
  - subst; apply Maps.PTree.gss.
  - rewrite /lookup /ptree_lookup in IHl |- *; rewrite Maps.PTree.gso; last auto.
    rewrite IHl.
    if_tac; auto.
Qed.

Lemma make_access_get : forall next r b,
  (make_access next r) !! b =
  if Pos.ltb b next then Some (access_of_rmap r b) else None.
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
Qed.*)

Ltac fold_ptree_lookup := repeat match goal with |-context[Maps.PTree.get ?k ?m] =>
  change (Maps.PTree.get k m) with (m !! k) end.

(*Program Definition deflate_mem (m : Memory.mem) (r : rmap) (Halloc : alloc_cohere m r) :=
  {| mem_contents := mem_contents m;
    (* original could have non-None default, so we need to 
       reconstruct it from the blocks [1, nextblock) *)
     mem_access := (fun _ _ => None, make_access (nextblock m) r);
     nextblock := nextblock m |}.
Next Obligation.
Proof.
  intros; unfold Maps.PMap.get; simpl.
  fold_ptree_lookup; rewrite make_access_get.
  destruct (b <? nextblock m)%positive; simpl; auto.
  apply perm_of_res_op1.
Qed.
Next Obligation.
Proof.
  intros; unfold Maps.PMap.get; simpl.
  fold_ptree_lookup; rewrite make_access_get.
  destruct (Pos.ltb_spec0 b (nextblock m)); auto; contradiction.
Qed.
Next Obligation.
Proof.
  intros; apply contents_default.
Qed.*)

(*Lemma join_sub_alloc_cohere : forall m jm, m ≼ (m_phi jm) ->
  alloc_cohere (m_dry jm) m.
Proof.
  intros ?? [? J] ??.
  destruct jm; simpl in *.
  apply JMalloc in H.
  apply (resource_at_join _ _ _ loc) in J; rewrite H in J; inv J.
  apply split_identity in RJ; [|apply bot_identity].
  apply identity_share_bot in RJ; subst; f_equal; apply proof_irr.
Qed.*)

Local Hint Resolve perm_refl : core.

(*Lemma perm_of_sh_join_sub'': forall (sh1 sh2: Share.t),
  join_sub sh1 sh2 ->
  perm_order'' (perm_of_sh sh2) (perm_of_sh sh1).
Proof.
intros ?? [? J].
unfold perm_of_sh.
destruct (writable0_share_dec sh1).
{ eapply join_writable01 in w; eauto.
  rewrite (if_true _ _ _ _ _ w).
  if_tac; if_tac; simpl; try constructor.
  subst; rewrite (@only_bot_joins_top x) in J by (eexists; eauto).
  apply join_comm, bot_identity in J; subst; contradiction. }
if_tac; [repeat if_tac; constructor|].
destruct (readable_share_dec sh1).
{ eapply join_readable1 in r; eauto.
  rewrite (if_true _ _ _ _ _ r); constructor. }
repeat if_tac; try constructor.
subst; apply split_identity, identity_share_bot in J; auto; contradiction.
Qed.
*)

Lemma adr_inv0: forall (b b': block) (ofs ofs': Z) (sz: Z),
  ~ adr_range (b, ofs) sz (b', ofs') ->
  b <> b' \/ ~ ofs <= ofs' < ofs + sz.
Proof.
intros until sz.
intro H.
destruct (peq b b').
right; intro Contra.
apply H.
unfold adr_range.
auto.
left; intro Contra.
apply n; auto.
Qed.

Lemma adr_inv: forall (b b': block) (ofs ofs': Z) ch,
  ~ adr_range (b, ofs) (size_chunk ch) (b', ofs') ->
  b <> b' \/ ~ ofs <= ofs' < ofs + size_chunk ch.
Proof. intros until ch; intros H1; eapply adr_inv0; eauto. Qed.

Lemma range_inv0: forall ofs ofs' sz,
  ~ ofs <= ofs' < ofs + sz ->
  ofs' < ofs \/ ofs' >= ofs + sz.
Proof.
intros until sz; intro H.
destruct (zle ofs ofs'); destruct (zlt ofs' (ofs + sz)); lia.
Qed.

Lemma range_inv: forall ofs ofs' ch,
  ~ ofs <= ofs' < ofs + size_chunk ch ->
  ofs' < ofs \/ ofs' >= ofs + size_chunk ch.
Proof. intros; eapply range_inv0; eauto. Qed.

Lemma perm_of_sh_Freeable_top: forall sh, perm_of_sh sh = Some Freeable ->
     sh = Share.top.
Proof.
intros sh H.
unfold perm_of_sh in H.
repeat if_tac in H; solve [inversion H | auto].
Qed.

Lemma nextblock_access_empty: forall m b ofs k, (b >= nextblock m)%positive
  -> access_at m (b, ofs) k = None.
Proof.
intros.
unfold access_at. simpl.
apply (nextblock_noaccess m b ofs k).
auto.
Qed.

(*Section initial_mem.
resourceariables (m: mem) (w: rmap).

Definition initial_rmap_ok :=
   forall loc, ((fst loc >= nextblock m)%positive -> core w @ loc = None) /\
                   (match w @ loc with
(*                    | PURE _ _ => (fst loc < nextblock m)%positive /\
                                           access_at m loc Cur = Some Nonempty /\
                                            max_access_at m loc = Some Nonempty*)
                    | _ => True end).
Hypothesis IOK: initial_rmap_ok.
End initial_mem.*)

Definition empty_retainer (loc: address) := Share.bot.

Lemma perm_of_freeable: perm_of_sh Share.top = Some Freeable.
Proof.
unfold perm_of_sh.
rewrite if_true. rewrite if_true; auto.
auto.
Qed.

Lemma perm_of_writable:
   forall sh, writable_share sh -> sh <> Share.top -> perm_of_sh sh = Some Writable.
Proof.
intros.
unfold perm_of_sh.
rewrite -> if_true by auto. rewrite if_false; auto.
Qed.

Lemma perm_of_readable:
  forall sh (rsh: readable_share sh), ~writable0_share sh -> perm_of_sh sh = Some Readable.
Proof.
intros. unfold perm_of_sh. rewrite -> if_false by auto. rewrite if_true; auto.
Qed.

Lemma perm_of_nonempty:
  forall sh, sh <> Share.bot -> ~readable_share sh -> perm_of_sh sh = Some Nonempty.
Proof.
intros. unfold perm_of_sh.
rewrite -> if_false by auto.
rewrite -> if_false by auto.
rewrite -> if_false by auto; auto.
Qed.

Lemma perm_of_empty:
    perm_of_sh Share.bot = None.
Proof.
  apply perm_of_sh_bot.
Qed.

Lemma perm_of_dfrac_None: forall dq, perm_of_dfrac dq = None -> dq = ε ∨ dq = DfracOwn ShareBot.
Proof.
  destruct dq as [[|]|[|]]; simpl; try if_tac; try done; auto; intros ->%perm_of_sh_None; auto.
  rewrite perm_of_sh_bot // in H.
Qed.

Lemma perm_of_readable_share : forall sh, readable_share sh -> Mem.perm_order' (perm_of_sh sh) Readable.
Proof.
  intros; rewrite /perm_of_sh.
  if_tac; if_tac; try constructor; done.
Qed.

Lemma perm_of_Ews: perm_of_sh Ews = Some Writable.
Proof.
unfold perm_of_sh, Ews, extern_retainer.
rewrite if_true.
*
rewrite if_false; auto.
intro.
rewrite Share.lub_commute in H.
pose proof lub_Lsh_Rsh. rewrite Share.lub_commute in H0.
rewrite <- H in H0.
apply Share.distrib_spec in H0.
destruct (Share.split Share.Lsh) eqn:?H; simpl in *.
pose proof (nonemp_split_neq1 Share.Lsh t t0).
spec H2. intro.
apply identity_share_bot in H3. contradiction Lsh_bot_neq.
subst t.
apply H2; auto.
clear.
rewrite glb_Rsh_Lsh.
rewrite Share.glb_commute.
symmetry.
apply Share.ord_antisym.
rewrite <- glb_Lsh_Rsh.
apply glb_less_both.
destruct (Share.split Share.Lsh) eqn:H.
simpl.
apply Share.split_together in H.
rewrite <- H.
apply Share.lub_upper1.
apply Share.ord_refl.
apply Share.bot_correct.
*
unfold writable_share.
apply leq_join_sub.
apply Share.lub_upper2.
Qed.

Lemma perm_of_Ers: perm_of_sh Ers = Some Readable.
Proof.
unfold perm_of_sh, Ers, extern_retainer.
rewrite if_false.
*
rewrite if_true; auto.
apply readable_share_lub.
unfold readable_share.
rewrite glb_split_x.
intro.
apply identity_share_bot in H.
destruct (Share.split Share.Rsh) eqn:H0.
apply Share.split_nontrivial in H0.
unfold Share.Rsh in H0.
destruct (Share.split Share.top) eqn:H1.
simpl in *. subst.
apply Share.split_nontrivial in H1.
apply Share.nontrivial; auto.
auto.
simpl in H; auto.
*
unfold writable_share.
intro.
apply leq_join_sub in H.
apply Share.ord_spec2 in H.
apply (f_equal (Share.glb Share.Rsh)) in H.
rewrite Share.distrib1 in H.
rewrite Share.glb_idem in H.
rewrite Share.lub_absorb in H.
rewrite Share.distrib1 in H.
rewrite (@sub_glb_bot Share.Rsh (fst (Share.split Share.Lsh)) Share.Lsh)
 in H.
rewrite -> Share.lub_commute, Share.lub_bot in H.
rewrite glb_split_x in H.
destruct (Share.split Share.Rsh) eqn:H0.
apply nonemp_split_neq1 in H0.
simpl in *; subst. congruence.
apply Rsh_nonidentity.
clear.
exists (snd (Share.split Share.Lsh)).
destruct (Share.split Share.Lsh) eqn:H.
simpl.
split.
eapply Share.split_disjoint; eauto.
eapply Share.split_together; eauto.
apply glb_Rsh_Lsh.
Qed.

Lemma extern_retainer_neq_bot: extern_retainer <> Share.bot.
Proof.
unfold extern_retainer.
intro.
destruct (Share.split Share.Lsh) eqn:H0.
simpl in *. subst.
pose proof (Share.split_together _ _ _ H0).
rewrite -> Share.lub_commute, Share.lub_bot in H.
subst.
apply nonemp_split_neq2 in H0.
contradiction H0; auto.
clear.
unfold Share.Lsh.
intro.
apply identity_share_bot in H.
destruct (Share.split Share.top) eqn:H0.
simpl in *; subst.
apply split_nontrivial' in H0.
apply identity_share_bot in H0.
apply Share.nontrivial; auto.
left.
apply bot_identity.
Qed.

Lemma perm_mem_access: forall m b ofs p,
  perm m b ofs Cur p ->
  exists p', (perm_order p' p /\ access_at m (b, ofs) Cur = Some p').
Proof.
intros.
rewrite perm_access in H. red in H.
destruct (access_at m (b, ofs) Cur); try contradiction; eauto.
Qed.

Lemma free_smaller_None : forall m b b' ofs lo hi m',
  access_at m (b, ofs) Cur = None
  -> free m b' lo hi = Some m'
  -> access_at m' (b, ofs) Cur = None.
Proof.
intros.
destruct (adr_range_dec (b',lo) (hi-lo) (b,ofs)).
destruct a; simpl in *.
subst b'; apply free_access with (ofs:=ofs) in H0; [ | lia].
destruct H0.
pose proof (Memory.access_cur_max m' (b,ofs)).
rewrite H1 in H3; simpl in H3.
destruct (access_at m' (b, ofs) Cur); auto; contradiction.
rewrite <- H. symmetry.
eapply free_access_other; eauto.
destruct (eq_block b b'); auto; right.
simpl in n.
assert (~(lo <= ofs < lo + (hi - lo))) by intuition.
lia.
Qed.

Definition contents_at (m: mem) (loc: address) : memval :=
  Maps.ZMap.get (snd loc) (Maps.PMap.get (fst loc) (Mem.mem_contents m)).

Lemma free_nadr_range_eq : forall m b b' ofs' lo hi m',
  ~ adr_range (b, lo) (hi - lo) (b', ofs')
  -> free m b lo hi = Some m'
  -> access_at m (b', ofs') = access_at m' (b', ofs')
  /\  contents_at m (b', ofs') = contents_at m' (b', ofs').
Proof.
intros.
split.
extensionality k.
apply (free_access_other _ _ _ _ _ H0 b' ofs' k).
destruct (eq_block b b'); auto; right.
simpl in H.
assert (~(lo <= ofs' < lo + (hi - lo))) by intuition.
lia.
unfold contents_at.
simpl.
Transparent free.
unfold free in H0.
Opaque free.
if_tac in H0; inv H0.
unfold unchecked_free.
simpl.
reflexivity.
Qed.

Lemma free_not_freeable_eq : forall m b lo hi m' b' ofs',
  free m b lo hi = Some m'
  -> access_at m (b', ofs') Cur <> Some Freeable
  -> access_at m (b', ofs') Cur = access_at m' (b', ofs') Cur.
Proof.
intros.
destruct (adr_range_dec (b,lo) (hi-lo) (b',ofs')).
destruct a.
subst b'.
destruct (free_access _ _ _ _ _ H ofs'); [lia |].
contradiction.
apply (free_access_other _ _ _ _ _ H).
destruct (eq_block b' b); auto; right.
subst b'.
simpl in n. assert (~( lo <= ofs' < lo + (hi - lo))) by intuition; lia.
Qed.

Lemma adr_range_inv: forall loc loc' n,
  ~ adr_range loc n loc' ->
  fst loc <> fst loc' \/ (fst loc=fst loc' /\ ~snd loc <= snd loc' < snd loc + n).
Proof.
intros until n.
intro H.
destruct (peq (fst loc) (fst loc')).
right; split; auto; intro Contra.
apply H.
unfold adr_range.
destruct loc,loc'.
auto.
left; intro Contra.
apply n0; auto.
Qed.

(*Lemma dry_noperm_juicy_nonreadable : forall m loc,
  access_at (m_dry m) loc Cur = None ->   ~readable loc (m_phi m).
Proof.
intros.
rewrite (juicy_mem_access m loc) in H.
intro. hnf in H0.
destruct (m_phi m @loc); simpl in *; auto.
destruct k as [x | |]; try inv H.
unfold perm_of_sh in H2.
if_tac in H2. if_tac in H2; inv H2.
rewrite if_true in H2 by auto.
inv H2.
Qed.*)

Lemma fullempty_after_alloc : forall m1 m2 lo n b ofs,
  alloc m1 lo n = (m2, b) ->
  access_at m2 (b, ofs) Cur = None \/ access_at m2 (b, ofs) Cur = Some Freeable.
Proof.
intros.
pose proof (alloc_access_same _ _ _ _ _ H ofs Cur).
destruct (range_dec lo ofs n). auto.
left.
rewrite <- (alloc_access_other _ _ _ _ _ H b ofs Cur) by (right; lia).
apply alloc_result in H.
subst.
apply nextblock_access_empty.
apply Pos.le_ge, Pos.le_refl.
Qed.

Transparent alloc.

Lemma alloc_dry_unchanged_on : forall m1 m2 loc lo hi b0,
  alloc m1 lo hi = (m2, b0) ->
  ~adr_range (b0,lo) (hi-lo) loc ->
  access_at m1 loc = access_at m2 loc /\
  (access_at m1 loc Cur <> None -> contents_at m1 loc = contents_at m2 loc).
Proof.
intros.
destruct loc as [b z]; simpl.
split.
extensionality k.
eapply Memory.alloc_access_other; eauto.
simpl in H0.
destruct (eq_block b b0); auto. subst. right.
assert (~(lo <= z < lo + (hi - lo))) by intuition; lia.
intros.
unfold alloc in H.
inv H. unfold contents_at; simpl.
unfold adr_range in H0.
destruct (eq_dec b (nextblock m1)).
subst.
rewrite invalid_noaccess in H1; [ congruence |].
contradict H0.
red in H0. apply Pos.lt_irrefl in H0. contradiction.
rewrite -> Maps.PMap.gso by auto.
auto.
Qed.

Lemma adr_range_zle_fact : forall b lo hi loc,
  adr_range (b,lo) (hi-lo) loc ->
  zle lo (snd loc) && zlt (snd loc) hi = true.
Proof.
unfold adr_range.
intros.
destruct loc; simpl in *.
destruct H.
destruct H0.
apply andb_true_iff.
split.
apply zle_true; auto.
apply zlt_true; lia.
Qed.

Lemma alloc_dry_updated_on : forall m1 m2 lo hi b loc,
  alloc m1 lo hi = (m2, b) ->
  adr_range (b, lo) (hi - lo) loc ->
  access_at m2 loc Cur=Some Freeable /\
  contents_at m2 loc=Undef.
Proof.
intros.
destruct loc as [b' z'].
split.
destruct H0. subst b'.
apply (alloc_access_same _ _ _ _ _ H). lia.
unfold contents_at; unfold alloc in H; inv H. simpl.
destruct H0; subst b'.
rewrite Maps.PMap.gss. rewrite Maps.ZMap.gi; auto.
Qed.

Opaque alloc.

(*(* Not sure this is usable, but it's the most direct translation. *)
Definition resource_decay n (nextb: block) (phi1 phi2: rmap) :=
 forall l: address,
  ((fst l >= nextb)%positive -> forall dq r, ~ouPred_holds (l ↦{dq} r) n phi1) /\
 ((forall dq r, ouPred_holds (l ↦{dq} r) n phi1 <-> ouPred_holds (l ↦{dq} r) n phi2) \/
  (exists sh v v', writable0_share sh /\ ouPred_holds (l ↦{#sh} VAL v) n phi1 /\
                                         ouPred_holds (l ↦{#sh} VAL v') n phi2) \/
  ((fst l >= nextb)%positive /\ exists v, ouPred_holds (l ↦ VAL v) n phi2) \/
  (exists v, ouPred_holds (l ↦ VAL v) n phi1 /\ forall dq r, ~ouPred_holds (l ↦{dq} r) n phi2)).

Definition resource_nodecay n (nextb: block) (phi1 phi2: rmap) :=
  forall l: address,
  ((fst l >= nextb)%positive -> forall dq r, ~ouPred_holds (l ↦{dq} r) n phi1) /\
 ((forall dq r, ouPred_holds (l ↦{dq} r) n phi1 <-> ouPred_holds (l ↦{dq} r) n phi2) \/
  (exists sh v v', writable0_share sh /\ ouPred_holds (l ↦{#sh} VAL v) n phi1 /\
                                         ouPred_holds (l ↦{#sh} VAL v') n phi2)).

Lemma resource_nodecay_decay:
   forall n b phi1 phi2, resource_nodecay n b phi1 phi2 -> resource_decay n b phi1 phi2.
Proof.
  unfold resource_decay, resource_nodecay; intros.
  specialize (H l); intuition.
Qed.

Lemma resource_decay_refl: forall n b phi,
  (forall l, (fst l >= b)%positive -> forall dq r, ~ouPred_holds (l ↦{dq} r) n phi) ->
  resource_decay n b phi phi.
Proof.
intros; intros l; auto.
Qed.

(*Lemma resource_decay_trans: forall n b b' m1 m2 m3 (Hbb : (b <= b')%positive),
  resource_decay n b m1 m2 -> resource_decay n b' m2 m3 -> resource_decay n b m1 m3.
Proof.
  intros; intros l.
  specialize (H l); specialize (H0 l).
  destruct H,H0.
  split. auto.
  destruct H1.
  { setoid_rewrite H1. destruct H2 as [?|[?|[[??]|?]]]; auto.
    assert (l.1 >= b)%positive by lia; auto. }
  destruct H2.
  { setoid_rewrite <- H2. auto. }
  destruct H1 as [? | [? | ?]].
  - destruct H1 as (sh & v & v' & ? & ? & ?).
    destruct H2 as [? | [[??] | ?]].
    + destruct H2 as (sh2 & v2 & v2' & ? & ? & ?).
      right; left; exists sh, v, v2'; split; auto; split; auto.
       (* can only have one writable share *)
    + exfalso; eapply H0; eauto.
    + destruct H2 as (? & ? & ?); right; right; right.
      eexists; split; eauto.
       (* writable share again *)
  - destruct H1 as (? & ? & ?).
Abort. (* should be provable *)*)*)

Section mpred.

  Context `{!gen_heapGS address resource Σ} `{!wsatGS Σ}.
  Notation mpred := (iProp Σ).

  Definition core_load (ch: memory_chunk) (l: address) (v: val): mpred :=
    <absorb> ∃ bl: list memval,
    ⌜length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)%Z⌝ ∧
      ([∗ list] i↦b ∈ bl, ∃ sh, ⌜Mem.perm_order' (perm_of_dfrac sh) Readable⌝ ∧ mapsto (adr_add l (Z.of_nat i)) sh (VAL b)).

  Definition core_load' (ch: memory_chunk) (l: address) (v: val) (bl: list memval) : mpred :=
    <absorb> (⌜length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)%Z⌝ ∧
      ([∗ list] i↦b ∈ bl, ∃ sh, ⌜Mem.perm_order' (perm_of_dfrac sh) Readable⌝ ∧ mapsto (adr_add l (Z.of_nat i)) sh (VAL b))).

  (* coherence between logical state (rmap) and physical state (mem) *)
  Definition rmap := gmap address (shared (leibnizO resource)).

  Implicit Types (f : rmap) (s : sharedR (leibnizO resource)) (r : prodO dfracO (optionO (leibnizO resource))).

  Lemma elem_of_agree_ne : forall {A} n (x y : agreeR A), ✓{n} x -> x ≡{n}≡ y -> proj1_sig (elem_of_agree x) ≡{n}≡ proj1_sig (elem_of_agree y).
  Proof.
    intros; destruct (elem_of_agree x), (elem_of_agree y); simpl.
    destruct (proj1 H0 _ e) as (? & Hv2 & ->).
    rewrite H0 in H; eapply agree_validN_def; done.
  Qed.

  Lemma elem_of_agree_equiv : forall {A} (x y : agreeR A), ✓ x -> x ≡ y -> proj1_sig (elem_of_agree x) ≡ proj1_sig (elem_of_agree y).
  Proof.
    intros; apply equiv_dist; intros.
    apply elem_of_agree_ne; auto.
  Qed.

  Lemma elem_of_agree_ne' : forall {A} n (x y : agreeR (leibnizO A)), ✓{n} x -> x ≡{n}≡ y -> proj1_sig (elem_of_agree x) = proj1_sig (elem_of_agree y).
  Proof.
    intros ??????%elem_of_agree_ne; done.
  Qed.

  Definition resR_to_resource (s : optionR (sharedR (leibnizO resource))) : prodO dfracO (optionO (leibnizO resource)) :=
    match s with
    | Some s => (dfrac_of s, option_map (fun v : agree resource => proj1_sig (elem_of_agree v)) (val_of s))
    | None => (ε, None)
    end.

  Lemma resR_to_resource_ne n : forall x y, ✓{n} x -> x ≡{n}≡ y -> resR_to_resource x = resR_to_resource y.
  Proof.
    intros ??? Hdist; inv Hdist; last done.
    destruct x0, y0; try done; simpl.
    + destruct H0 as (-> & ?), H.
      erewrite (elem_of_agree_ne'(A := resource)); done.
    + hnf in H0; subst; done.
  Qed.

  Lemma resR_to_resource_eq : forall x y, ✓ x -> x ≡ y -> resR_to_resource x = resR_to_resource y.
  Proof.
    intros ??? Heq; apply (resR_to_resource_ne O); auto.
    eapply cmra_valid_validN; done.
  Qed.

  Lemma resR_to_resource_fst : forall x, (resR_to_resource x).1 =
    match x with Some a => dfrac_of a | None => ε end.
  Proof.
    destruct x; done.
  Qed.

  Lemma perm_of_res_ne' : forall n r1 r2, r1 ≡{n}≡ r2 -> perm_of_res r1 = perm_of_res r2.
  Proof.
    intros.
    destruct r1, r2, H as [[=] ?]; simpl in *; subst.
    by eapply perm_of_res_ne.
  Qed.

  Definition resource_at f k := resR_to_resource (f !! k).
  Infix "@" := resource_at (at level 50, no associativity).

  Definition contents_cohere (m: mem) k r :=
    forall v, r.2 = Some (VAL v) -> contents_at m k = v.

  Definition access_cohere (m: mem) k r :=
    Mem.perm_order'' (access_at m k Cur) (perm_of_res r).

  Definition max_access_at m loc := access_at m loc Max.

(*  Definition max_access_cohere (m: mem) k r :=
    Mem.perm_order'' (max_access_at m k) (perm_of_res r).*)

  Definition coherent_loc (m: mem) k r := contents_cohere m k r /\ access_cohere m k r (*/\ max_access_cohere m k r*).

  Definition coherent (m : mem) phi := forall loc, ((loc.1 >= Mem.nextblock m)%positive -> phi !! loc = None) /\
    coherent_loc m loc (phi @ loc).

  Definition mem_auth m := ∃ σ, ⌜coherent m σ⌝ ∧ resource_map_auth(H0 := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)) (gen_heap_name _) 1 σ.

  Lemma elem_of_to_agree : forall {A} (v : A), proj1_sig (elem_of_agree (to_agree v)) = v.
  Proof.
    intros; destruct (elem_of_agree (to_agree v)); simpl.
    rewrite -elem_of_list_singleton //.
  Qed.

  Definition res_le r1 r2 : Prop := r1.1 ≼ r2.1 ∧ (r1.2 = None ∨ r1.2 = r2.2).

  Lemma resR_le : forall x1 x2 (Hv : ✓x2) (Hmono : x1 ≼ x2), res_le (resR_to_resource x1) (resR_to_resource x2).
  Proof.
    intros ??? [-> | (? & ? & -> & -> & ?)]%option_included.
    { split; simpl; auto.
      apply @ucmra_unit_least. }
    destruct H as [H | H].
    { erewrite resR_to_resource_eq; last by constructor.
      split; auto.
      { rewrite H //. } }
    apply shared_included in H as [H | (? & H)]; first by rewrite H in Hv.
    split; simpl; first done.
    apply shared_valid in Hv as (_ & Hv).
    apply option_included_total in H as [-> | (? & ? & -> & Heq & H)]; auto.
    rewrite Heq /= in Hv |- *.
    assert (✓{0} x2) by (by apply cmra_valid_validN).
    right; f_equal; symmetry; apply (elem_of_agree_ne' O); first done.
    symmetry; apply agree_valid_includedN; first done.
    by apply @cmra_included_includedN.
  Qed.

  Lemma perm_of_res_mono' : forall x1 x2, ✓ x2.1 -> res_le x1 x2 -> Mem.perm_order'' (perm_of_res x2) (perm_of_res x1).
  Proof.
    intros (dq, ?) (?, v) ? (? & Hv).
    eapply perm_order''_trans.
    - by eapply perm_of_res_mono.
    - destruct Hv; simpl in * |-; subst; try apply perm_order''_refl.
      destruct dq as [[|]|], v as [[| |]|]; try done; try apply perm_order''_refl.
      + apply perm_order''_min.
      + simpl; if_tac; try constructor.
        apply perm_order''_trans with (Some Readable); [done | constructor].
  Qed.

  Lemma contents_cohere_mono : forall m k x x' (Hmono : res_le x x') (Hcoh : contents_cohere m k x'),
    contents_cohere m k x.
  Proof.
    intros; intros ? H.
    destruct x, Hmono as (_ & [? | ?]); simpl in *; subst; [done | eauto].
  Qed.

  Lemma access_cohere_mono : forall m k x x' (Hv : ✓x'.1) (Hmono : res_le x x') (Hcoh : access_cohere m k x'),
    access_cohere m k x.
  Proof.
    rewrite /access_cohere; intros.
    eapply perm_order''_trans; first done.
    by apply perm_of_res_mono'.
  Qed.

  Lemma coherent_mono : forall m k dq dq' v (Hv : ✓dq') (Hmono : dq ≼ dq') (Hcoh : coherent_loc m k (dq', v)),
    coherent_loc m k (dq, v).
  Proof.
    intros.
    destruct Hcoh as (Hcontents & Haccess).
    apply (contents_cohere_mono _ _ (dq, v)) in Hcontents; last by split; auto.
    apply (access_cohere_mono _ _ (dq, v)) in Haccess; last (by split; auto); last done.
    by split.
  Qed.

  Lemma coherent_val_mono : forall m k dq v, coherent_loc m k (dq, Some v) -> coherent_loc m k (dq, None).
  Proof.
    intros.
    destruct H as (Hcontents & Haccess); split; try done.
    unfold access_cohere in *; simpl in *.
    eapply perm_order''_trans; first done.
    destruct dq as [[|]|], v; try done; try apply perm_order''_refl.
    - apply perm_order''_min.
    - simpl; if_tac; try constructor.
      apply perm_order''_trans with (Some Readable); [done | constructor].
  Qed.

  Lemma mapsto_lookup {m k dq v} :
    mem_auth m -∗ k ↦{dq} v -∗ ⌜✓ dq ∧ readable_dfrac dq ∧ (k.1 < Mem.nextblock m)%positive ∧ coherent_loc m k (dq, Some v)⌝.
  Proof.
    iIntros "(% & % & Hm) H".
    iDestruct (resource_map_auth_valid with "Hm") as %(_ & Hvalid).
    iDestruct (mapsto_lookup with "Hm H") as %(? & ? & ? & ? & Hk).
    specialize (H k); destruct H as (Hnext & H).
    unfold resource_at in H; erewrite resR_to_resource_eq in H by done.
    rewrite /= elem_of_to_agree in H.
    eapply coherent_mono in H; [|done..].
    rewrite gen_heap.mapsto_unseal /gen_heap.mapsto_def resource_map.resource_map_elem_unseal.
    iDestruct "H" as "(% & ?)".
    iPureIntro; repeat (split; auto).
    { by eapply cmra_valid_included. }
    { destruct (plt k.1 (nextblock m)); first done.
      rewrite Hnext // in Hk; inv Hk. }
  Qed.

  (* basic memory operations on mems + rmaps *)
  Global Instance mapsto_lookup_combine_gives_1 {m k dq v} :
    CombineSepGives (mem_auth m) (k ↦{dq} v) ⌜✓ dq ∧ readable_dfrac dq ∧ (k.1 < Mem.nextblock m)%positive ∧ coherent_loc m k (dq, Some v)⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (mapsto_lookup with "H1 H2") as %?. eauto.
  Qed.

  Global Instance mapsto_lookup_combine_gives_2 {m k dq v} :
    CombineSepGives (k ↦{dq} v) (mem_auth m) ⌜✓ dq ∧ readable_dfrac dq ∧ (k.1 < Mem.nextblock m)%positive ∧ coherent_loc m k (dq, Some v)⌝.
  Proof.
    rewrite /CombineSepGives comm. apply mapsto_lookup_combine_gives_1.
  Qed.

  Lemma mapsto_no_lookup {m k sh} :
    mem_auth m -∗ mapsto_no k sh -∗ ⌜~readable_share sh ∧ (k.1 < Mem.nextblock m)%positive ∧ coherent_loc m k (DfracOwn (Share sh), None)⌝.
  Proof.
    iIntros "(% & % & Hm) H".
    iDestruct (resource_map_auth_valid with "Hm") as %(_ & Hvalid).
    iDestruct (mapsto_no_lookup with "Hm H") as %(? & Hv & Heq & ?).
    rewrite gen_heap.mapsto_no_unseal /gen_heap.mapsto_no_def resource_map.resource_map_elem_no_unseal.
    iDestruct "H" as "(% & ?)".
    iPureIntro; split; first done.
    specialize (H k).
    rewrite /resource_at Heq /= in H; destruct H as (Hnext & H).
    split; first by destruct (plt k.1 (nextblock m)); first done; unfold Plt in *; specialize (Hnext ltac:(lia)).
    apply shared_valid in Hv as [Hd _].
    eapply coherent_mono; try done.
    destruct (val_of x); last done.
    eapply coherent_val_mono; done.
  Qed.

  Lemma big_sepL_seq2 : forall {A} `{Inhabited A} l (f : nat -> A -> mpred),
    ([∗ list] k↦y ∈ l, f k y) ⊣⊢ [∗ list] k;y ∈ seq 0 (length l);l, f k y.
  Proof.
    intros; induction l using rev_ind; simpl; first done.
    rewrite big_sepL_app app_length seq_app big_sepL2_snoc /= -IHl.
    rewrite Nat.add_0_r bi.sep_emp //.
  Qed.

  Lemma elem_of_zip_gen : forall {A B} (l1 : list A) (l2 : list B) x, x ∈ zip l1 l2 ↔
    exists i, l1 !! i = Some x.1 /\ l2 !! i = Some x.2.
  Proof.
    induction l1; simpl; intros.
    - split.
      + by intros ?%not_elem_of_nil.
      + by intros (? & ? & ?).
    - split.
      + intros H; destruct l2; first by apply not_elem_of_nil in H.
        apply elem_of_cons in H as [-> | ?].
        * by exists O.
        * apply IHl1 in H as (i & ? & ?); by exists (S i).
      + intros (n & H1 & H2).
        destruct l2; first done.
        rewrite !lookup_cons in H1 H2.
        destruct n; first by destruct x; inv H1; inv H2; constructor.
        constructor; rewrite IHl1; eauto.
  Qed.

  Global Instance inhabited_resource : Inhabited resource := populate (VAL Undef).

  Lemma list_to_map_lookup : forall `{I : Inhabited A} k (vl : list A) l, list_to_map(M := gmap address A) (zip ((λ i, adr_add k (Z.of_nat i)) <$> seq 0 (length vl)) vl) !! l =
    if adr_range_dec k (length vl) l then Some (nth (Z.to_nat (l.2 - k.2)) vl inhabitant) else None.
  Proof.
    intros.
    destruct (list_to_map _ !! _) eqn: Hl; simpl.
    * apply elem_of_list_to_map, elem_of_zip_gen in Hl as (? & Hk & Hv); simpl in *.
      apply list_lookup_fmap_inv in Hk as (? & -> & (-> & ?)%lookup_seq).
      rewrite /adr_add /= if_true.
      rewrite Z.add_simpl_l Nat2Z.id; erewrite nth_lookup_Some; done.
      { destruct k; simpl; lia. }
      { rewrite fst_zip.
        apply NoDup_fmap_2, NoDup_seq.
        intros ??; inversion 1; lia.
        { rewrite fmap_length seq_length //. } }
    * if_tac; last done.
      destruct k as (?, z), l as (?, ofs), H; subst.
      apply not_elem_of_list_to_map_2 in Hl; contradiction Hl.
      rewrite fst_zip; last rewrite fmap_length seq_length //.
      rewrite elem_of_list_fmap /adr_add /=.
      exists (Z.to_nat (ofs - z)).
      split; first by f_equal; lia.
      rewrite elem_of_seq; lia.
  Qed.

  Lemma update_map_lookup : forall `{I : Inhabited A} (f : A -> _) k vl (σ : rmap) l, ((f <$> list_to_map (zip ((λ i, adr_add k (Z.of_nat i)) <$> seq 0 (length vl)) vl)) ∪ σ) !! l =
    if adr_range_dec k (length vl) l then Some (f (nth (Z.to_nat (l.2 - k.2)) vl inhabitant)) else σ !! l.
  Proof.
    intros.
    rewrite lookup_union lookup_fmap list_to_map_lookup.
    if_tac; last rewrite left_id //.
    rewrite union_Some_l //.
  Qed.

  Lemma nth_replicate: forall {A} n (a : A) m, nth n (replicate m a) a = a.
  Proof.
    induction n; destruct m; simpl in *; done.
  Qed.

  Lemma mapsto_alloc {m} lo hi m' b (Halloc : Mem.alloc m lo hi = (m', b)) :
    mem_auth m ==∗ mem_auth m' ∗ ([∗ list] i ∈ seq 0 (Z.to_nat (hi - lo)), adr_add (b, lo) (Z.of_nat i) ↦ VAL Undef).
  Proof.
    iIntros "(% & % & Hm)".
    rewrite -(big_sepL_fmap (λ i, adr_add (b, lo) (Z.of_nat i)) (λ _ i, i ↦ VAL Undef)).
    rewrite -(big_sepL2_replicate_r _ _ (λ _ i v, i ↦ v)); last by rewrite fmap_length seq_length.
    rewrite big_sepL2_alt fmap_length seq_length replicate_length bi.pure_True // bi.True_and.
    assert (NoDup (zip ((λ i : nat, adr_add (b, lo) (Z.of_nat i)) <$> seq 0 (Z.to_nat (hi - lo)))
     (replicate (Z.to_nat (hi - lo)) (VAL Undef))).*1).
    { rewrite fst_zip.
      apply NoDup_fmap_2, NoDup_seq.
      intros ??; inversion 1; lia.
      { rewrite fmap_length seq_length replicate_length //. } }
    rewrite -(big_sepM_list_to_map (λ x y, x ↦ y)) //.
    pose proof (alloc_result _ _ _ _ _ Halloc) as ->.
    iMod (mapsto_insert_big with "Hm") as "(Hm & $)".
    { rewrite dom_list_to_map_L fst_zip.
      intros l (? & -> & ?)%elem_of_list_to_set%elem_of_list_fmap_2.
      destruct (H (adr_add (nextblock m, lo) (Z.of_nat x))) as (Hnext & _).
      rewrite elem_of_dom Hnext.
      * intros (? & ?); done.
      * rewrite /adr_add /=; lia.
      * rewrite fmap_length seq_length replicate_length //. }
    iExists _; iFrame; iPureIntro.
    split; last done.
    intros l; specialize (H l); destruct H as (Hnext & Hcontents & Haccess).
    unfold resource_at in *.
    assert ((((λ v : resource, (YES (V := leibnizO resource) (DfracOwn (Share Tsh)) readable_Tsh (to_agree v))) <$>
     list_to_map (zip ((λ i : nat, adr_add (nextblock m, lo) (Z.of_nat i)) <$> seq 0 (Z.to_nat (hi - lo)))
          (replicate (Z.to_nat (hi - lo)) (VAL Undef)))) ∪ σ) !! l =
      if eq_dec l.1 (nextblock m) then if adr_range_dec (nextblock m, lo) (hi - lo) l then
      Some (YES (V := leibnizO resource) (DfracOwn (Share Tsh)) readable_Tsh (to_agree (VAL Undef))) else None else σ !! l) as Hlookup.
    { rewrite -{1}(replicate_length (Z.to_nat (hi - lo)) (VAL Undef)) update_map_lookup replicate_length nth_replicate.
      if_tac.
      * destruct l, H as [-> ?]; rewrite /= eq_dec_refl if_true //; lia.
      * if_tac; last done.
        rewrite if_false; first by apply Hnext; lia.
        destruct l; intros [??]; simpl in *; subst; lia. }
    rewrite Hlookup; clear Hlookup.
    split3.
    - erewrite nextblock_alloc by done.
      intros; rewrite Hnext; last lia.
      if_tac; last done; if_tac; last done; lia.
    - intros ?.
      if_tac; last by rewrite /contents_at; erewrite AllocContentsOther by done; auto.
      if_tac; last done.
      rewrite /= elem_of_to_agree; inversion 1; subst.
      rewrite -H in Halloc.
      rewrite /contents_at; erewrite AllocContentsUndef; done.
    - unfold access_cohere in *.
      destruct l; if_tac; last by erewrite <- alloc_access_other; eauto.
      if_tac; simpl in *; last by rewrite eq_dec_refl; apply perm_order''_None.
      subst; rewrite elem_of_to_agree perm_of_freeable; erewrite alloc_access_same; try done; last lia.
      apply perm_order''_refl.
  Qed.

  Lemma mapsto_alloc_readonly {m} lo hi m' b (Halloc : Mem.alloc m lo hi = (m', b)) :
    mem_auth m ==∗ mem_auth m' ∗ ([∗ list] i ∈ seq 0 (Z.to_nat (hi - lo)), adr_add (b, lo) (Z.of_nat i) ↦□ (VAL Undef)).
  Proof.
    iIntros "(% & % & Hm)".
    rewrite -(big_sepL_fmap (λ i, adr_add (b, lo) (Z.of_nat i)) (λ _ i, i ↦□ VAL Undef)).
    rewrite -(big_sepL2_replicate_r _ _ (λ _ i v, i ↦□ v)); last by rewrite fmap_length seq_length.
    rewrite big_sepL2_alt fmap_length seq_length replicate_length bi.pure_True // bi.True_and.
    assert (NoDup (zip ((λ i : nat, adr_add (b, lo) (Z.of_nat i)) <$> seq 0 (Z.to_nat (hi - lo)))
     (replicate (Z.to_nat (hi - lo)) (VAL Undef))).*1).
    { rewrite fst_zip.
      apply NoDup_fmap_2, NoDup_seq.
      intros ??; inversion 1; lia.
      { rewrite fmap_length seq_length replicate_length //. } }
    rewrite -(big_sepM_list_to_map (λ x y, x ↦□ y)) //.
    pose proof (alloc_result _ _ _ _ _ Halloc) as ->.
    iMod (mapsto_insert_persist_big with "Hm") as "(Hm & $)".
    { rewrite dom_list_to_map_L fst_zip.
      intros l (? & -> & ?)%elem_of_list_to_set%elem_of_list_fmap_2.
      destruct (H (adr_add (nextblock m, lo) (Z.of_nat x))) as (Hnext & _).
      rewrite elem_of_dom Hnext.
      * intros (? & ?); done.
      * rewrite /adr_add /=; lia.
      * rewrite fmap_length seq_length replicate_length //. }
    iExists _; iFrame; iPureIntro.
    split; last done.
    intros l; specialize (H l); destruct H as (Hnext & Hcontents & Haccess).
    unfold resource_at in *.
    assert ((((λ v : resource, YES (V := leibnizO resource) DfracDiscarded I (to_agree v)) <$>
     list_to_map (zip ((λ i : nat, adr_add (nextblock m, lo) (Z.of_nat i)) <$> seq 0 (Z.to_nat (hi - lo)))
          (replicate (Z.to_nat (hi - lo)) (VAL Undef)))) ∪ σ) !! l =
      if eq_dec l.1 (nextblock m) then if adr_range_dec (nextblock m, lo) (hi - lo) l then
      Some (YES (V := leibnizO resource) DfracDiscarded I (to_agree (VAL Undef))) else None else σ !! l) as Hlookup.
    { rewrite -{1}(replicate_length (Z.to_nat (hi - lo)) (VAL Undef)) update_map_lookup replicate_length nth_replicate.
      if_tac.
      * destruct l, H as [-> ?]; rewrite /= eq_dec_refl if_true //; lia.
      * if_tac; last done.
        rewrite if_false; first by apply Hnext; lia.
        destruct l; intros [??]; simpl in *; subst; lia. }
    rewrite Hlookup; clear Hlookup.
    split3.
    - erewrite nextblock_alloc by done.
      intros; rewrite Hnext; last lia.
      if_tac; last done; if_tac; last done; lia.
    - intros ?.
      if_tac; last by rewrite /contents_at; erewrite AllocContentsOther by done; auto.
      if_tac; last done.
      rewrite /= elem_of_to_agree; inversion 1; subst.
      rewrite -H in Halloc.
      rewrite /contents_at; erewrite AllocContentsUndef; done.
    - unfold access_cohere in *.
      destruct l; if_tac; last by erewrite <- alloc_access_other; eauto.
      if_tac; simpl in *; last by rewrite eq_dec_refl; apply perm_order''_None.
      subst; rewrite elem_of_to_agree perm_of_empty /=; erewrite alloc_access_same; try done; last lia.
      constructor.
  Qed.

  Lemma mapsto_free {m k vl} hi m' (Hfree : Mem.free m k.1 k.2 hi = Some m') (Hlen : length vl = Z.to_nat (hi - k.2)) :
    mem_auth m -∗ ([∗ list] i↦v ∈ vl, adr_add k (Z.of_nat i) ↦ v) ==∗ mem_auth m'.
  Proof.
    iIntros "(% & % & Hm) H".
    rewrite big_sepL_seq2 -(big_sepL2_fmap_l (λ i, adr_add k (Z.of_nat i)) (λ _ i y, i ↦ y)).
    assert (NoDup (zip ((λ i : nat, adr_add k (Z.of_nat i)) <$> seq 0 (length vl)) vl).*1).
    { rewrite fst_zip.
      apply NoDup_fmap_2, NoDup_seq.
      intros ??; inversion 1; lia.
      { rewrite fmap_length seq_length //. } }
    rewrite big_sepL2_alt -(big_sepM_list_to_map (λ x y, x ↦ y)) //.
    iDestruct "H" as "(_ & H)".
    iMod (mapsto_delete_big with "Hm H").
    iExists _; iFrame; iPureIntro; split; last done.
    unfold coherent, resource_at in *; intros l. rewrite update_map_lookup.
    destruct (H l) as (Hnext & Hcontents & Haccess); clear H.
    pose proof (free_range_perm _ _ _ _ _ Hfree) as Hperm.
    split3.
    - erewrite nextblock_free by done.
      if_tac; last done.
      destruct k, l as (?, ofs), H; simpl in *; subst.
      specialize (Hperm ofs ltac:(lia)); apply perm_valid_block in Hperm; rewrite /valid_block /Plt in Hperm; lia.
    - unfold contents_cohere in *.
      intros ?; if_tac; try done.
      destruct k, l; eapply free_nadr_range_eq in Hfree as [_ <-]; simpl in *; auto; lia.
    - unfold access_cohere in *.
      if_tac; first by rewrite /= eq_dec_refl; apply perm_order''_None.
      destruct k, l; eapply free_nadr_range_eq in Hfree as [<- _]; simpl in *; auto; lia.
  Qed.

  Lemma plus_1_lt : forall z, z < z + 1.
  Proof. lia. Qed.

  Lemma mapsto_storebyte {m k v} m' b sh (Hsh : writable0_share sh) :
    Mem.storebytes m k.1 k.2 [b] = Some m' ->
    mem_auth m -∗ k ↦{#sh} (VAL v) ==∗ mem_auth m' ∗ k ↦{#sh} (VAL b).
  Proof.
    intros Hstore; iIntros "(% & % & Hm) H".
    iDestruct (resource_map_auth_valid with "Hm") as %(_ & Hvalid).
    iMod (mapsto_update with "Hm H") as (?? (? & ? & Hk)) "(Hm & $)".
    iExists _; iFrame; iPureIntro; split; last done.
    unfold coherent, resource_at in *; intros l.
    destruct (H l) as (Hnext & Hcontents & Haccess); clear H.
    pose proof (storebytes_range_perm _ _ _ _ _ Hstore) as Hperm.
    specialize (Hvalid l).
    split3.
    - erewrite nextblock_storebytes by done.
      destruct (eq_dec k l); [subst; rewrite lookup_insert | rewrite lookup_insert_ne //].
      clear -Hperm.
      rewrite /= in Hperm.
      (* lia stopped working *)
      specialize (Hperm l.2); apply perm_valid_block in Hperm.
      rewrite /valid_block /Plt in Hperm; apply Positive_as_OT.lt_nle in Hperm.
      rewrite Pos.ge_le_iff //.
      { split; first done; apply plus_1_lt. }
    - unfold contents_cohere, contents_at in *.
      erewrite storebytes_mem_contents by done.
      intros ?; destruct (eq_dec k l); [subst; rewrite lookup_insert | rewrite lookup_insert_ne //].
      + rewrite /= elem_of_to_agree; inversion 1; subst.
        rewrite Maps.PMap.gss Maps.ZMap.gss //.
      + destruct (eq_dec l.1 k.1); [rewrite e Maps.PMap.gss | rewrite Maps.PMap.gso //; auto].
        simpl; destruct (eq_dec l.2 k.2); first by destruct k, l; simpl in *; subst.
        rewrite Maps.ZMap.gso // -e; auto.
    - unfold access_cohere in *.
      erewrite <- Memory.storebytes_access by done.
      destruct (eq_dec k l); [subst; rewrite lookup_insert | rewrite lookup_insert_ne //].
      erewrite resR_to_resource_eq in Haccess by done.
      rewrite /= !elem_of_to_agree // in Haccess |- *.
  Qed.

  Lemma coherent_bot m k : coherent_loc m k (ε, None).
  Proof.
    repeat split.
    - by intros ?.
    - rewrite /access_cohere /= eq_dec_refl; apply perm_order''_None.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma mapsto_lookup_big {m} k dq m0 :
    mem_auth m -∗
    ([∗ list] i↦v ∈ m0, adr_add k i ↦{dq} v) -∗
    ⌜forall i, (i < length m0)%nat -> coherent_loc m (adr_add k (Z.of_nat i)) (match m0 !! i with Some v => (dq, Some v) | None => (ε, None) end)⌝.
  Proof.
    iIntros "(% & % & Hm)".
    iDestruct (resource_map_auth_valid with "Hm") as %(_ & Hvalid).
    rewrite big_sepL_seq2 -(big_sepL2_fmap_l (λ i, adr_add k (Z.of_nat i)) (λ _ i y, i ↦{dq} y)).
    assert (NoDup (zip ((λ i : nat, adr_add k (Z.of_nat i)) <$> seq 0 (length m0)) m0).*1).
    { rewrite fst_zip.
      apply NoDup_fmap_2, NoDup_seq.
      intros ??; inversion 1; lia.
      { rewrite fmap_length seq_length //. } }
    rewrite big_sepL2_alt -(big_sepM_list_to_map (λ x y, x ↦{dq} y)) //.
    iIntros "(_ & H)".
    iDestruct (mapsto_lookup_big with "Hm H") as %Hall; iPureIntro.
    intros.
    destruct (m0 !! i) as [r|] eqn: Hi; last apply coherent_bot.
    specialize (Hall (adr_add k (Z.of_nat i)) r); spec Hall.
    { apply elem_of_list_to_map_1, elem_of_zip_gen; first done.
      exists i; rewrite list_lookup_fmap lookup_seq_lt //. }
    destruct Hall as (? & ? & ? & ? & Heq).
    specialize (Hvalid (adr_add k (Z.of_nat i))).
    specialize (H (adr_add k (Z.of_nat i))); destruct H as (Hnext & H).
    unfold resource_at in H; erewrite resR_to_resource_eq in H by done.
    rewrite /= elem_of_to_agree in H.
    eapply coherent_mono in H; done.
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

  Theorem mapsto_storebytes {m} m' k vl bl (Hlen : length vl = length bl) sh (Hsh : writable0_share sh)
    (Hstore : Mem.storebytes m k.1 k.2 bl = Some m') :
    mem_auth m -∗
    ([∗ list] i↦v ∈ vl, adr_add k (Z.of_nat i) ↦{#sh} VAL v) ==∗
    mem_auth m' ∗
        [∗ list] i↦v ∈ bl, adr_add k (Z.of_nat i) ↦{#sh} VAL v.
  Proof.
    iIntros "Hm H".
    rewrite -(big_sepL_fmap VAL (λ i v, adr_add k (Z.of_nat i) ↦{#sh} v)).
(*    iDestruct (mapsto_lookup_big with "Hm H") as %Hold.*)
    iDestruct "Hm" as "(% & % & Hm)".
    rewrite big_sepL_seq2 -(big_sepL2_fmap_l (λ i, adr_add k (Z.of_nat i)) (λ _ i y, i ↦{#sh} y)).
    rewrite fmap_length.
    assert (NoDup (zip ((λ i : nat, adr_add k (Z.of_nat i)) <$> seq 0 (length vl)) (VAL <$> vl)).*1).
    { rewrite fst_zip.
      apply NoDup_fmap_2, NoDup_seq.
      intros ??; inversion 1; lia.
      { rewrite !fmap_length seq_length //. } }
    rewrite big_sepL2_alt -(big_sepM_list_to_map (λ x y, x ↦{#sh} y)) //.
    iDestruct "H" as "(_ & H)".
    iDestruct (gen_heap.mapsto_lookup_big with "Hm H") as %Hall.
    rewrite big_sepL_seq2 -(big_sepL2_fmap_l (λ i, adr_add k (Z.of_nat i)) (λ _ i y, i ↦{#sh} VAL y)).
    rewrite -(big_sepL2_fmap_r VAL (λ _ i y, i ↦{#sh} y)).
    assert (NoDup (zip ((λ i : nat, adr_add k (Z.of_nat i)) <$> seq 0 (length bl)) (VAL <$> bl)).*1).
    { rewrite fst_zip.
      apply NoDup_fmap_2, NoDup_seq.
      intros ??; inversion 1; lia.
      { rewrite !fmap_length seq_length //. } }
    rewrite big_sepL2_alt -(big_sepM_list_to_map (λ x y, x ↦{#sh} y)) //.
    iDestruct (resource_map_auth_valid with "Hm") as %(_ & Hvalid).
    iMod (mapsto_update_big with "Hm H") as "(Hm & $)".
    { rewrite Hlen !dom_list_to_map_L !fst_zip //; rewrite !fmap_length seq_length //; lia. }
    rewrite !fmap_length seq_length bi.pure_True // bi.True_and bi.sep_emp.
    iDestruct (resource_map_auth_valid with "Hm") as %(_ & Hvalid').
    iExists _; iFrame; iPureIntro; split; last done.
    unfold coherent, resource_at in *; intros l.
    destruct (H l) as (Hnext & Hcontents & Haccess); clear H.
    pose proof (storebytes_range_perm _ _ _ _ _ Hstore) as Hperm.
    specialize (Hvalid l); specialize (Hvalid' l).
    rewrite lookup_union map_lookup_imap -(fmap_length VAL bl) list_to_map_lookup fmap_length in Hvalid' |- *.
    split3.
    - erewrite nextblock_storebytes by done.
      if_tac; last rewrite left_id //.
      simpl in *; destruct (σ !! l) eqn: Hl; rewrite Hl // in Hvalid' |- *.
      intros X; specialize (Hnext X); done.
    - unfold contents_cohere, contents_at in *.
      erewrite storebytes_mem_contents by done.
      if_tac; simpl in *.
      + destruct (σ !! l) as [[|]|] eqn: Hl; rewrite Hl // /= in Hvalid' |- *.
        rewrite elem_of_to_agree map_nth; inversion 1; subst.
        destruct l, k, H; simpl in *; subst.
        rewrite Maps.PMap.gss get_setN //.
      + rewrite left_id; destruct (eq_dec l.1 k.1); [rewrite e Maps.PMap.gss | rewrite Maps.PMap.gso //].
        rewrite -e setN_outside //.
        destruct (zlt l.2 k.2); auto.
        rewrite Z.ge_le_iff; destruct (zle (k.2 + Z.of_nat (length bl)) l.2); auto.
        contradiction H; destruct l, k; simpl in *; subst; lia.
    - unfold access_cohere in *.
      erewrite <- Memory.storebytes_access by done.
      if_tac; simpl in *; last rewrite left_id //.
      specialize (Hall l). rewrite -(fmap_length VAL vl) list_to_map_lookup fmap_length Hlen if_true // in Hall.
      specialize (Hall _ eq_refl); destruct Hall as (? & ? & ? & ? & Heq).
      erewrite resR_to_resource_eq in Haccess by done.
      inversion Heq as [?? Hc Heq'|]; subst; rewrite -Heq'.
      destruct x1; inv Hc; simpl.
      rewrite /= !elem_of_to_agree !map_nth // in Haccess |- *.
  Qed.

  Lemma empty_coherent : forall m, coherent m ∅.
  Proof.
    rewrite /coherent /resource_at; intros; rewrite lookup_empty.
    split; first done; apply coherent_bot.
  Qed.

  Lemma coherent_empty : forall (σ : rmapUR _ _), coherent Mem.empty σ → σ = ∅.
  Proof.
    intros.
    rewrite map_empty; intros l.
    destruct (H l) as (Hnext & _).
    apply Hnext; simpl; lia.
  Qed.

  Lemma mem_auth_set (m : mem) (σ : rmapUR _ _) (Hvalid : ✓ σ) (Hnext : ∀ loc, (loc.1 >= Mem.nextblock m)%positive -> σ !! loc = None)
    (Hcoh : ∀ loc : address, coherent_loc m loc (resource_at σ loc)) :
    mem_auth Mem.empty ==∗ mem_auth m ∗
    ([∗ map] l ↦ x ∈ σ, match x with
                        | (shared.YES dq _ v) => l ↦{dq} (proj1_sig (elem_of_agree v))
                        | (shared.NO (Share sh) _) => mapsto_no l sh
                        | _ => False
                        end).
  Proof.
    iIntros "(% & % & Hm)".
    apply coherent_empty in H as ->.
    iMod (gen_heap_set with "Hm") as "(? & $)".
    iExists _; iFrame; iPureIntro; split; last done; split; auto.
  Qed.

End mpred.

Infix "@" := resource_at (at level 50, no associativity).
