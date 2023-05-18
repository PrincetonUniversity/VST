Require Import VST.veric.base.
Require Import VST.veric.Memory.
Require Import VST.veric.juicy_base.
Require Import VST.veric.shares.
Require Import VST.zlist.sublist.

Definition perm_of_res_lock (r: dfrac * resource) :=
  match r with
  | (q, LK _ _) => match q with
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

Lemma perm_order''_None : forall s, perm_order'' s None.
Proof.
  destruct s; simpl; auto.
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

Lemma perm_of_res_op2:
  forall r,
    perm_order'' (perm_of_res' r) (perm_of_res_lock r).
Proof.
  destruct r as (?, ?); simpl.
  destruct r; try apply perm_order''_None.
  rewrite /perm_of_res' /=.
  unfold perm_of_dfrac; destruct d as [[|]|]; try apply perm_order''_refl || if_tac; try apply perm_of_sh_glb; try done.
  constructor.
Qed.

(*Open Scope bi_scope.

Definition contents_cohere (m: mem) : mpred := ∀dq v l,
  l ↦{dq} VAL v → ⌜contents_at m l = v⌝.

(* To be consistent with the extension order, we have to allow for the possibility that there's a discarded
   fraction giving us an extra readable share. *)
Definition access_cohere (m: mem) : mpred := ∀ l,
  (∀dq r, l ↦{dq} r → ⌜perm_order'' (access_at m l Cur) (perm_of_res (Some (dq, r)))⌝) ∧
  (⌜perm_order'' (access_at m l Cur) (Some Writable)⌝ → ∃dq r, l ↦{dq} r ∧ ⌜access_at m l Cur = perm_of_res (Some (dq, r))⌝).

Definition max_access_cohere (m: mem) : mpred := ∀l dq r,
  l ↦{dq} r → ⌜perm_order'' (max_access_at m l) (perm_of_res' (Some (dq, r)))⌝.

Definition alloc_cohere (m: mem) := ∀l dq r, l ↦{dq} r → ⌜fst l < nextblock m⌝%positive.

(*Lemma perm_of_res_order : forall n r1 r2 (Hv : valid r2) (Hr1 : r1 ≠ None), r1 ≼ₒ{n} r2 -> perm_of_res (resR_to_resource r1) = perm_of_res (resR_to_resource r2).
Proof.
  intros.
  destruct r1 as [(d1, a1)|], r2 as [(d2, a2)|]; try done; simpl in *.
  destruct H as [Hd Ha], Hv as [Hvd Hva]; simpl in *.
  assert (hd (VAL Undef) (agree.agree_car a1) = hd (VAL Undef) (agree.agree_car a2)) as Heq.
  { hnf in Ha.
    destruct a1, a2; simpl in *.
    destruct agree_car as [| v] => // /=.
    destruct agree_car0 as [| v2] => // /=.
    destruct (Ha v) as (v2' & Hin & Heq); first apply elem_of_list_here.
    specialize (Hva n); rewrite agree.agree_validN_def in Hva.
    specialize (Hva _ _ (elem_of_list_here _ _) Hin).
    hnf in Heq, Hva; subst; done. }
  rewrite Heq.
  destruct Hd; subst; try done.
  destruct d1; done.
Qed.*)

Definition coherent_with (m: mem) : mpred := contents_cohere m ∧ access_cohere m ∧ max_access_cohere m ∧ alloc_cohere m.

Section selectors.
Variable (m: mem).
(*Definition m_dry := match j with mkJuicyMem m _ _ _ _ _ => m end.
Definition m_phi := match j with mkJuicyMem _ phi _ _ _ _ => phi end.*)
Lemma coherent_contents: coherent_with m ⊢ contents_cohere m.
Proof. by rewrite /coherent_with bi.and_elim_l. Qed.
Lemma coherent_access: coherent_with m ⊢ access_cohere m.
Proof. by rewrite /coherent_with bi.and_elim_r bi.and_elim_l. Qed.
Lemma coherent_max_access: coherent_with m ⊢ max_access_cohere m.
Proof. by rewrite /coherent_with bi.and_elim_r bi.and_elim_r bi.and_elim_l. Qed.
Lemma coherent_alloc: coherent_with m ⊢ alloc_cohere m.
Proof. by rewrite /coherent_with bi.and_elim_r bi.and_elim_r bi.and_elim_r. Qed.
End selectors.*)

(*Lemma juicy_view_coherent : forall m, mem_auth m ∗ True ⊢ coherent_with m.
Proof.
  intros; iIntros "m".
  iSplit; [|iSplit; [|iSplit]].
  - 
Abort.*)

(*Definition juicy_mem_resource: forall jm m', resource_at m' = resource_at (m_phi jm) ->
  {jm' | m_phi jm' = m' /\ m_dry jm' = m_dry jm}.
Proof.
  intros.
  assert (contents_cohere (m_dry jm) m') as Hcontents.
  { intros ???.
    rewrite H; apply juicy_mem_contents. }
  assert (access_cohere (m_dry jm) m') as Haccess.
  { intro.
    rewrite H; apply juicy_mem_access. }
  assert (max_access_cohere (m_dry jm) m') as Hmax.
  { intro.
    rewrite H; apply juicy_mem_max_access. }
  assert (alloc_cohere (m_dry jm) m') as Halloc.
  { intro.
    rewrite H; apply juicy_mem_alloc_cohere. }
  exists (mkJuicyMem _ _ Hcontents Haccess Hmax Halloc); auto.
Defined.*)

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

(* There are plenty of other orders on memories, but they're all either
   way too general (Mem.extends, mem_lessdef) or way too restrictive (mem_lessalloc). *)
Definition mem_sub m1 m2 := mem_contents m1 = mem_contents m2 /\ nextblock m1 = nextblock m2 /\
  forall b ofs k p, Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.

Lemma mem_sub_valid_pointer : forall m1 m2 b ofs, mem_sub m1 m2 -> valid_pointer m1 b ofs = true ->
  valid_pointer m2 b ofs = true.
Proof.
  unfold mem_sub, valid_pointer; intros.
  destruct H as (_ & _ & Hp).
  destruct (perm_dec m1 _ _ _ _); inv H0.
  destruct (perm_dec m2 _ _ _ _); auto.
Qed.

Lemma mem_sub_weak_valid_pointer : forall m1 m2 b ofs, mem_sub m1 m2 -> weak_valid_pointer m1 b ofs = true ->
  weak_valid_pointer m2 b ofs = true.
Proof.
  unfold weak_valid_pointer; intros.
  apply orb_true_iff in H0 as [Hp | Hp]; rewrite -> (mem_sub_valid_pointer _ _ _ _ H Hp), ?orb_true_r; auto.
Qed.

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
Variables (m: mem) (w: rmap).

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
