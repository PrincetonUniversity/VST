Require Import veric.rmaps.
Require Import progs.ghost.
Require Import mailbox.general_atomics.
Require Import mailbox.acq_rel_atomics.
Require Import progs.conclib.
Require Import mailbox.maps.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.kvnode_atomic_ra.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition load_acq_spec := DECLARE _load_acq load_acq_spec.
Definition store_rel_spec := DECLARE _store_rel store_rel_spec.

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition tnode := Tstruct _node noattr.

Definition has_size : {x : Z | x = 8}.
Proof.
  eexists; eauto.
Qed.

Definition size := proj1_sig has_size.
Lemma size_def : size = 8.
Proof.
  apply (proj2_sig has_size).
Qed.

(* Lexicographic ordering doesn't lead to a PCM (it's not associative), so we keep a full log of values. *)
Definition data_T g s (v : Z) := EX ver : Z, !!(Z.even ver = true /\ log_latest s ver v) &&
  ghost_snap (ver - 1) g.

(* If the current version is dirty, the entry may have moved past the latest full version. *)
Definition node_entry sh (b : bool) log locs g lg i := EX log' : _, !!(if b then log' = log else map_incl log log') &&
  protocol_piece sh (Znth i locs Vundef) (Znth i lg Vundef) log' map_incl (data_T g).

Definition version_T locs g lg g' (s v : Z) := !!(v = s) && EX L : _,
  !!(exists vs, log_latest L (if Z.even v then v else v - 1) vs) &&
  fold_right sepcon emp (map (fun i => node_entry Share.bot true (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))) *
  ghost_snap L g'.

Definition node_state (sh : share) (L : Z -> option (list Z)) version locs g lg g' := EX v : Z, EX vs : list Z, EX v' : Z,
  !!(Z.even v = true /\ log_latest L v vs /\ (v' = v \/ v' = v + 1) /\ forall v vs, L v = Some vs -> Zlength vs = size) &&
  protocol_piece sh version g v' Z.le (version_T locs g lg g') *
  fold_right sepcon emp (map (fun i => node_entry sh (Z.even v') (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))) *
  ghost (sh, L) g'.

Definition Ish := fst (Share.split gsh2).
Definition Wsh := snd (Share.split gsh2).

Lemma readable_Ish : readable_share Ish.
Proof.
  apply slice.split_YES_ok1; auto.
Qed.

Lemma readable_Wsh : readable_share Wsh.
Proof.
  apply slice.split_YES_ok2; auto.
Qed.

Lemma Ish_Wsh_join : sepalg.join Ish Wsh gsh2.
Proof.
  apply split_join; unfold Ish, Wsh; destruct (Share.split gsh2); auto.
Qed.

Hint Resolve readable_Ish readable_Wsh Ish_Wsh_join.

(* It's useful to have both private and shared node_states, so we can know that whatever we read is at least
   later than what we already knew. *)
Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * share * val * list val * val * val * list val *
              (Z -> option (list Z)) * Z * list Z))
  empty_map [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0, vs0) => temp _n n;
   fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0, vs0) => temp _out out]
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0, vs0) => !!(readable_share sh /\
     writable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\ log_latest L0 v0 vs0) &&
   data_at sh tnode (version, locs) n * data_at_ shi (tarray tint size) out *
   node_state Share.bot L0 version locs g lg g')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0, vs0) L => node_state Ish L version locs g lg g')
  (0, []) []
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0, vs0) L '(v, vals) =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) out *
   node_state Share.bot L version locs g lg g')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0, vs0) L '(v, vals) =>
   !!(map_incl L0 L /\ v0 <= v /\ L v = Some vals) && node_state Ish L version locs g lg g')
  _ _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.

Program Definition write_spec := DECLARE _write atomic_spec
  (ConstType (val * val * share * share * val * list val * list Z * val * val * list val *
              (Z -> option (list Z)) * Z * list Z))
  empty_map [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0, vs0) => temp _n n;
   fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0, vs0) => temp _in input]
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0, vs0) => !!(readable_share sh /\
     readable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\
     Forall repable_signed vals /\ Z.even v0 = true /\ Zlength vs0 = size /\ log_latest L v0 vs0) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state Wsh L version locs g lg g')
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0, vs0) L' =>
   node_state Ish L' version locs g lg g')
  tt []
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0, vs0) _ _ =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state Wsh (map_upd L (v0 + 2) vals) version locs g lg g')
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0, vs0) _ _ =>
   node_state Ish (map_upd L (v0 + 2) vals) version locs g lg g')
  _ _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.

Definition make_node_spec := DECLARE _make_node
  WITH u : unit
  PRE [ ]
    PROP ()
    LOCAL ()
    SEP ()
  POST [ tptr tnode ]
   EX n : val, EX version : val, EX locs : list val, EX g : val, EX lg : list val, EX g' : val,
    PROP (isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp ret_temp n)
    SEP (data_at Tsh tnode (version, locs) n; malloc_token Tsh (sizeof tnode) n;
         malloc_token Tsh (sizeof tint) version; fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) locs);
         node_state Tsh (singleton 0 (repeat 0 (Z.to_nat size))) version locs g lg g').

Definition writer_spec := DECLARE _writer
  WITH n : val, sh : share, v : Z, vs : list Z, L : Z -> option (list Z), version : val, locs : list val,
       g : val, lg : list val, g' : val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size; Z.even v = true;
          Zlength vs = size; log_latest L v vs)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state Wsh L version locs g lg g')
  POST [ tptr tvoid ]
   EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + (2 * (i + 1)), repeat (i + 1) (Z.to_nat size)))%Z (upto 3)))
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Wsh L' version locs g lg g').

(*Definition reader_spec := DECLARE _reader
  WITH n : val, sh : share, version : val, locs : list val, g : val, g' : val,
       lg : list val, lg' : list val, gh : val, gsh : share
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size; gsh <> Share.bot)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; ghost_hist gsh ([] : hist) gh;
         invariant (node_inv gh version locs g g' lg lg'))
  POST [ tptr tvoid ]
   EX h : hist,
    PROP (exists v vs, add_events [] [HRead v vs] h)
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; ghost_hist gsh h gh;
         invariant (node_inv gh version locs g g' lg lg')).*)

(* We can't keep an interleaved history of reads and writes, but we can know that each read got a value
   that was at some point in the history. *)
(*Program Definition reader_spec := DECLARE _reader atomic_spec
  (ConstType (val * share * val * list val * val * val * list val * list val * val * share))
  tt [(_n, tptr tvoid)] (tptr tvoid)
  [fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) => temp _n n]
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) => !!(readable_share sh /\ isptr version /\
   Forall isptr locs /\ Zlength locs = size /\ gsh <> Share.bot) && data_at sh tnode (version, locs) n)
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) _ => node_inv gh version locs g g' lg lg')
  (0, []) []
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) _ _ => data_at sh tnode (version, locs) n)
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) _ '(v1, vs1) =>
   EX v : Z, EX vs : list Z, node_state v vs version locs g g' lg lg' * EX hr : _,
     !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some (v, vs) /\ In (HWrite v1 vs1) hr) && ghost_ref hr gh)
  _ _ _ _ _ _. (* We could encapsulate this with another argument to node_inv, a known sublist of hr. *)*)

Definition reader_spec := DECLARE _reader
  WITH n : val, sh : share, v : Z, vs : list Z, L : Z -> option (list Z), version : val, locs : list val,
       g : val, g' : val, lg : list val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size; Z.even v = true;
          log_latest L v vs)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot L version locs g lg g')
  POST [ tptr tvoid ]
   EX v' : Z, EX vs' : list Z,
    PROP (v <= v'; v' = v -> vs' = vs)
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot (map_upd L v' vs') version locs g lg g').

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; load_acq_spec; store_rel_spec;
  read_spec; write_spec; make_node_spec; writer_spec; reader_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
  - if_tac; entailer!.
  - forward_call tt.
    contradiction.
  - if_tac.
    + forward. subst p. discriminate.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Lemma land_1 : forall i, Z.land i 1 = i mod 2.
Proof.
  intros; apply Z.land_ones with (n := 1); omega.
Qed.

Existing Instance max_PCM.
Existing Instance max_order.
Existing Instance fmap_PCM.
Existing Instance fmap_order.

Lemma node_entry_duplicable : forall b L locs g lg i, duplicable (node_entry Share.bot b L locs g lg i).
Proof.
  intros; unfold node_entry.
  apply exp_duplicable; intro.
  apply prop_duplicable, protocol_R_duplicable.
Qed.

Lemma version_T_duplicable : forall locs g lg g' s v, duplicable (version_T locs g lg g' s v).
Proof.
  intros; unfold version_T.
  apply prop_duplicable, exp_duplicable; intro.
  apply sepcon_duplicable, ghost_snap_duplicable.
  apply prop_duplicable, sepcon_list_duplicable.
  rewrite Forall_map, Forall_forall; intros; apply node_entry_duplicable.
Qed.

(*Lemma node_entry_join_R : forall b1 b2 L1 L2 locs g lg i,
  node_entry Share.bot b1 L1 locs g lg i * node_entry Share.bot b2 L2 locs g lg i |--
  node_entry Share.bot (b1 && b2) (map_add L1 L2) locs g lg i.
Proof.
  intros; unfold node_entry.
  eapply derives_trans; [apply protocol_R_join'|].
  Intros L; apply map_join_spec in H; subst; auto.
Qed.*)

Definition list_max v l := fold_right Z.max v l.

Lemma list_max_app : forall v l1 l2, list_max v (l1 ++ l2) = list_max (list_max v l2) l1.
Proof.
  intros; apply fold_right_app.
Qed.

Lemma list_max_max : forall l v1 v2, Z.max v1 (list_max v2 l) = list_max (Z.max v1 v2) l.
Proof.
  induction l; auto; simpl; intros.
  rewrite Z.max_assoc, !IHl.
  rewrite Z.max_assoc, (Z.max_comm a); auto.
Qed.

Lemma list_max_spec : forall l v, v <= list_max v l /\ Forall (fun v' => v' <= list_max v l) l.
Proof.
  induction l; simpl; intros.
  - split; auto; omega.
  - rewrite list_max_max.
    destruct (IHl (Z.max a v)) as [H]; split; [|repeat constructor; auto].
    + etransitivity; eauto; apply Zle_max_r.
    + etransitivity; eauto; apply Zle_max_l.
Qed.

Lemma node_state_duplicable : forall L version locs g lg g',
  duplicable (node_state Share.bot L version locs g lg g').
Proof.
  intros; unfold node_state.
  apply exp_duplicable; intro v.
  apply exp_duplicable; intro vs.
  apply exp_duplicable; intro v'.
  apply sepcon_duplicable; [|apply ghost_snap_duplicable].
  apply sepcon_duplicable.
  - apply prop_duplicable, protocol_R_duplicable.
  - apply sepcon_list_duplicable; rewrite Forall_map, Forall_forall; intros; simpl.
    apply node_entry_duplicable.
Qed.

Lemma node_entry_single : forall b log locs g lg i v v', log v = Some v' ->
  view_shift (node_entry Share.bot b log locs g lg i) (node_entry Share.bot b (singleton v v') locs g lg i).
Proof.
  intros; unfold node_entry.
  view_shift_intro log'.
  etransitivity; [apply protocol_R_forget with (s1 := singleton v v')|].
  - intros ?? Hincl Hjoin; apply join_comm in Hjoin; pose proof (map_join_spec _ _ _ Hjoin); subst.
    do 2 eexists; [|apply map_add_incl_compat; eauto].
    specialize (Hincl v); unfold singleton in *.
    rewrite eq_dec_refl in Hincl; specialize (Hincl _ eq_refl).
    repeat intro; simpl in *.
    specialize (Hjoin v1).
    unfold singleton, map_add, map_Znth in *.
    if_tac; subst; simpl.
    + destruct (s' v); split; auto; intros [X | X]; auto; try discriminate.
      inv X; apply Hjoin; auto.
    + destruct (s' v1); split; auto; intros [|]; auto; discriminate.
  - unfold singleton, map_Znth; intros ??; if_tac; [|discriminate].
    intro X; inv X.
    destruct b; subst; auto.
  - apply derives_view_shift; Exists (singleton v v'); apply andp_right; auto.
    apply prop_right; if_tac; reflexivity.
Qed.

Lemma node_entry_snap : forall sh b log locs g lg i,
  view_shift (node_entry sh b log locs g lg i)
    (node_entry sh b log locs g lg i * node_entry Share.bot b log locs g lg i).
Proof.
  intros; unfold node_entry.
  view_shift_intro log'; view_shift_intros.
  etransitivity; [apply make_protocol_R|].
  apply derives_view_shift; Exists log' log'; entailer!.
Qed.

Lemma node_state_snap : forall sh L version locs g lg g',
  view_shift (node_state sh L version locs g lg g')
    (node_state sh L version locs g lg g' * node_state Share.bot L version locs g lg g').
Proof.
  intros; unfold node_state.
  view_shift_intro v; view_shift_intro vs; view_shift_intro v'; view_shift_intros.
  rewrite !sepcon_assoc.
  etransitivity; [apply view_shift_sepcon1, make_protocol_R|].
  etransitivity; [apply view_shift_sepcon2|].
  - apply view_shift_sepcon, make_snap.
    apply view_shift_sepcon_list.
    { rewrite 2Zlength_map; reflexivity. }
    rewrite Zlength_map; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    apply node_entry_snap.
  - rewrite sepcon_map.
    apply derives_view_shift; Exists v vs v' v vs v'; entailer!.
Qed.

(*Lemma entries_absorb : forall v vs locs g lg L b1 b2 (Hlen : Zlength vs = size) (Hlens : forall vs', L v = Some vs' -> Zlength vs' = size),
  view_shift (fold_right sepcon emp (map (fun i => node_entry Share.bot b1 (singleton v (Znth i vs 0)) locs g lg i) (upto (Z.to_nat size))) *
              fold_right sepcon emp (map (fun i => node_entry Ish b2 (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))))
             (!!(L v = Some vs) && fold_right sepcon emp (map (fun i => node_entry Ish b2 (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size)))).
Proof.
  intros.
  rewrite <- sepcon_map; etransitivity.
  - apply view_shift_sepcon_list.
    { rewrite 2Zlength_map; reflexivity. }
    rewrite Zlength_map; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    rewrite sepcon_comm.
    instantiate (1 := fun i => !!(map_Znth i L 0 v = Some (Znth i vs 0)) &&
      node_entry Ish b2 (map_Znth i L 0) locs g lg i); simpl.
    unfold node_entry.
    view_shift_intro log2; view_shift_intro log1; view_shift_intros.
    etransitivity; [apply protocol_R_absorb|].
    { intro X; contradiction unreadable_bot; rewrite <- X; auto. }
    view_shift_intros; apply derives_view_shift; Exists log2.
    apply andp_right, andp_right; try apply prop_right; auto.
    assert (log2 v = Some (Znth i vs 0)); [|destruct b2; auto].
    destruct b2; subst.
    + admit.
    + auto.
  - apply derives_view_shift.
    assert_PROP (forall i, 0 <= i < size -> map_Znth i L 0 v = Some (Znth i vs 0)).
    { rewrite prop_forall; apply allp_right; intro i.
      rewrite prop_forall; apply allp_right; intro.
      rewrite extract_nth_sepcon with (i := i) by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; auto; omega).
      erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
      Intros; apply prop_right.
      apply H; unfold singleton; rewrite eq_dec_refl; auto. }
    apply andp_right.
    + eapply prop_right, map_Znth_eq.
      * intros; rewrite Hlens; auto.
      * intro; subst; rewrite size_def in Hlen; discriminate.
      * intros; apply H; omega.
    + apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      entailer!.
Qed.*)

Lemma node_entry_choose : forall b1 b2 log1 log2 locs g lg i,
  view_shift (node_entry Share.bot b1 log1 locs g lg i * node_entry Share.bot b2 log2 locs g lg i)
    (node_entry Share.bot b1 log1 locs g lg i).
Proof.
  intros; unfold node_entry.
  view_shift_intro log1'; view_shift_intro log2'; view_shift_intros.
  etransitivity; [apply protocol_R_choose, map_join_incl_compat|].
  apply derives_view_shift; Exists log1'; entailer!.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((((n, out), sh), shi), version), locs), g), g'), lg), L0), v0), vs0); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  assert (0 <= size) by (rewrite size_def; computable).
  apply semax_pre with (P' := PROP () LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ shi (tarray tint size) out;
         EX v : Z, !!(v0 <= v) && protocol_R version g v Z.le (version_T locs g lg g');
         EX ll : _, EX lb : _, fold_right sepcon emp (map (fun i => node_entry Share.bot (Znth i lb false) (Znth i ll empty_map) locs g lg i)
           (upto (Z.to_nat size))); EX L' : _, ghost_snap (map_add L0 L') g';
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { unfold node_state; Intros v vs v'.
    Exists v' (map (fun i => map_Znth i L0 0) (upto (Z.to_nat size))) (repeat (Z.even v') (Z.to_nat size)) (@empty_map Z (list Z));
      rewrite map_add_empty; entailer!.
    { assert (v0 = v); [|omega].
      eapply log_latest_inj with (v2 := vs0)(v2' := vs); eauto. }
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_repeat', Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  Intros v ll lb L'.
  repeat forward.
  forward_call_dep [Z : Type] (version, g, v, Z.le, version_T locs g lg g', emp, version_T locs g lg g').
  { split; intros; [|apply version_T_duplicable].
    etransitivity; [apply view_shift_sepcon2, version_T_duplicable|].
    rewrite <- sepcon_assoc; reflexivity. }
  unfold version_T at 2; Intros x L1; destruct x as (v1', v1); simpl in *; subst.
  gather_SEP 7 3; replace_SEP 0 (ghost_snap (map_add L0 (map_add L' L1)) g').
  { go_lower; eapply derives_trans; [apply ghost_join'|].
    Intros LA; destruct LA as (sh', ?).
    match goal with H : join _ _ _ |- _ => destruct H as (Hsh & Hjoin); simpl in * end.
    assert (sh' = Share.bot) by (eapply sepalg.join_eq; eauto).
    rewrite !eq_dec_refl in Hjoin; apply map_join_spec in Hjoin; subst.
    rewrite map_add_assoc; auto. }
  gather_SEP 3 6; rewrite <- sepcon_map; eapply view_shift_sepcon_list with (l2 := map _ (upto (Z.to_nat size)));
    rewrite ?Zlength_map; auto; intros.
  { erewrite !Znth_map, !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
    apply node_entry_choose. }
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP (Z.even v1 = true) (LOCALx Q (SEPx R))) end.
  { eapply semax_pre; [|apply semax_continue].
    unfold POSTCONDITION, abbreviate, overridePost.
    destruct (eq_dec EK_continue EK_normal); [discriminate|].
    unfold loop1_ret_assert.
    go_lower.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1) eqn: Hodd; try contradiction.
    Exists v1 (map (fun i => map_Znth i L1 0) (upto (Z.to_nat size))) (repeat true (Z.to_nat size)) (map_add L' L1); entailer!.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_repeat', Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
  { forward.
    entailer!.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1); auto; discriminate. }
  Intros.
  destruct (Z.even v1) eqn: Hv1; try discriminate.
  forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i)
    LOCAL (temp _snap (vint v1); temp _ver version; temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n;
         data_at shi (tarray tint size) (map (fun x => vint x) vals ++ repeat Vundef (Z.to_nat (size - i))) out;
         EX vers' : list Z, !!(Zlength vers' = i /\ Forall (fun v => Z.even v = true /\ v1 <= v) vers') &&
           protocol_R version g (list_max v1 (map (fun x => x - 1) vers')) Z.le (version_T locs g lg g') *
           fold_right sepcon emp (map (fun i => node_entry Share.bot true (singleton (Znth i vers' 0) (Znth i vals 0)) locs g lg i)
             (sublist 0 i (upto (Z.to_nat size))));
         fold_right sepcon emp (map (fun i => node_entry Share.bot true (map_Znth i L1 0)
           locs g lg i) (sublist i size (upto (Z.to_nat size)))); ghost_snap (map_add L0 (map_add L' L1)) g';
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { Exists (@nil Z) (@nil Z).
    rewrite data_at__eq; unfold default_val; simpl data_at.
    rewrite repeat_list_repeat, Z.sub_0_r; entailer!.
    rewrite sublist_same by (auto; rewrite Zlength_upto, Z2Nat.id; auto); auto. }
  - Intros vers'.
    match goal with H : 0 <= i < _ |- _ => rewrite <- size_def in H end.
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    { rewrite <- size_def; apply prop_right; auto. }
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    unfold node_entry at 2.
    Intros log'; subst log'.
    forward_call_dep [Z -> option Z : Type] (Znth i locs Vundef, Znth i lg Vundef,
      map_Znth i L1 0, @map_incl Z Z, data_T g,
      protocol_R version g (list_max v1 (map (fun x => x - 1) vers')) Z.le (version_T locs g lg g'),
      fun s (v : Z) => EX v' : Z, !!(Z.even v' = true /\ log_latest s v' v) &&
        protocol_R version g (list_max v1 (map (fun x => x - 1) (vers' ++ [v']))) Z.le (version_T locs g lg g')).
    { fast_cancel. }
    { split; [|intros; apply exp_duplicable; intro; apply prop_duplicable, protocol_R_duplicable].
      intros; unfold data_T.
      view_shift_intro ver; view_shift_intros.
      etransitivity; [apply view_shift_sepcon1, protocol_R_duplicable|].
      etransitivity; [apply view_shift_sepcon2, ghost_snap_duplicable|].
      unfold protocol_R, protocol_piece at 2.
      rewrite !sepcon_assoc, <- (sepcon_assoc (ghost _ _)); setoid_rewrite ghost_snap_join'.
      rewrite <- !sepcon_assoc, (sepcon_assoc _ (invariant _)).
      apply derives_view_shift; Exists ver ver; entailer!.
      rewrite map_app, list_max_app; simpl.
      rewrite Z.max_comm, list_max_max; auto. }
    Intros y v'; destruct y as (d, log'); simpl in *.
    eapply view_shift_trans; [|apply node_entry_single with (b := true);
      match goal with H : log_latest _ _ _ |- _ => destruct H; eauto end|].
    { unfold node_entry; apply derives_view_shift.
      Exists log'; entailer!. }
    gather_SEP 1 2; rewrite protocol_R_R.
    forward.
    go_lower; Exists (x ++ [d]) (vers' ++ [v']); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    match goal with H : exists vs, log_latest _ _ _ |- _ => destruct H as (vs1 & HL1) end.
    rewrite <- size_def, upd_init, !map_app, <- app_assoc by (rewrite ?Zlength_map; omega).
    entailer!.
    { rewrite Forall_app; repeat constructor; auto.
      eapply log_incl_latest; eauto.
      unfold map_Znth, map_add.
      destruct HL1 as [->]; simpl; eauto. }
    rewrite sublist_split with (mid := Zlength x)(hi := Zlength x + 1)
      by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    erewrite sublist_len_1, Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    rewrite map_app, sepcon_app; simpl.
    rewrite !app_Znth2 by omega.
    replace (Zlength vers') with (Zlength x); rewrite Zminus_diag, !Znth_0_cons; simpl; cancel.
    apply sepcon_list_derives; rewrite !Zlength_map; auto.
    intros ? Hi; erewrite !Znth_map by auto.
    rewrite Zlength_sublist in Hi by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    rewrite !Znth_sublist, !Znth_upto by (rewrite ?Z2Nat.id; simpl; omega).
    rewrite !app_Znth1 by omega; auto.
    { rewrite map_app, list_max_app; simpl.
      rewrite <- list_max_max; apply Z.le_max_r. }
  - Intros vals' vers'; rewrite <- size_def in *.
    rewrite Zminus_diag, app_nil_r, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    forward_call_dep [Z : Type] (version, g, list_max v1 (map (fun x => x - 1) vers'), Z.le,
      version_T locs g lg g', emp, fun s v : Z => !!(v = s) && emp).
    { split; [|auto with dup].
      intros; unfold version_T.
      apply derives_view_shift; entailer!. }
    Intros x; destruct x as (v2', v2); simpl in *; subst.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v2 <> v1) (LOCALx Q (SEPx R))) end.
    + subst.
      rewrite <- (map_map II).
      gather_SEP 0 5 7 9 8; rewrite <- !sepcon_assoc; apply invariants_view_shift with
        (Q0 := EX L : _, node_state Share.bot L version locs g lg g' * Q L (v1, vals')).
      { rewrite !map_map, !sepcon_assoc, (sepcon_comm P), <- 2sepcon_assoc.
        etransitivity; [apply view_shift_sepcon2, HP|].
        view_shift_intro L2.
        etransitivity; [|apply derives_view_shift; Exists L2; apply derives_refl].
        rewrite !sepcon_assoc, (sepcon_comm (Q _ _)).
        etransitivity; [|apply view_shift_sepcon2, HQ]; simpl.
        unfold node_state at 1.
        view_shift_intro v2; view_shift_intro vs2; view_shift_intro v2'; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp _)).
        rewrite <- sepcon_assoc, 4sepcon_assoc.
        etransitivity; [apply view_shift_sepcon1; erewrite map_ext_in; [apply entries_absorb with (v := v1)(vs := vals'); eauto|]|].
        { intros; simpl.
          rewrite In_upto, Z2Nat.id in * by auto.
          match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i := a)(d := 0) in H;
            [destruct H as [Heven] | omega] end.
          destruct (list_max_spec (map (fun x => x - 1) vers') v1) as [_ Hmax].
          rewrite Forall_map in Hmax.
          apply Forall_Znth with (i := a)(d := 0) in Hmax; [simpl in Hmax | omega].
          destruct (eq_dec (Znth a vers' 0) v1); subst; auto.
          assert (Znth a vers' 0 = v1 + 1) as Heq by omega.
          rewrite Heq, Z.even_add in Heven; replace (Z.even v1) with true in Heven; discriminate. }
        view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_R _ _ _ _ _)).
        rewrite (sepcon_comm _ (protocol_piece _ _ _ _ _ _)).
        rewrite <- !sepcon_assoc, 3sepcon_assoc.
        assert (Ish <> Share.bot).
        { intro X; contradiction unreadable_bot; rewrite <- X; auto. }
        etransitivity; [apply view_shift_sepcon1, protocol_R_absorb; auto|].
        rewrite <- (sepcon_assoc (ghost_snap _ _)), snap_master_join by auto.
        view_shift_intros.
        rewrite <- !sepcon_assoc; etransitivity; [apply view_shift_sepcon1; etransitivity; [|apply node_state_snap]|].
        { apply derives_view_shift; unfold node_state.
          Exists v2 vs2; entailer!.
          auto. }
        apply derives_view_shift; entailer!. }
      Intros L2.
      forward.
      rewrite map_map; Exists (v1, vals') L2; entailer!.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; go_lower; Exists v2 (map (fun i => singleton (Znth i vers' 0) (Znth i vals' 0))
        (upto (Z.to_nat size))); entailer!.
      { destruct (list_max_spec (map (fun x => x - 1) vers') v1); omega. }
      erewrite map_ext_in; eauto; intros; simpl.
      rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega.
Qed.

(*Lemma update_entries : forall L ll locs g lg lg', view_shift
  (fold_right sepcon emp (map (node_entry_W L locs g lg lg') (upto (Z.to_nat size))) *
   fold_right sepcon emp (map (fun i => node_entry (map_Znth i ll 0) locs g lg lg' i) (upto (Z.to_nat size))))
  (fold_right sepcon emp (map (node_entry_W L locs g lg lg') (upto (Z.to_nat size))) *
   fold_right sepcon emp (map (fun i => node_entry (map_Znth i L 0) locs g lg lg' i) (upto (Z.to_nat size)))).
Proof.
  intros.
  rewrite <- !sepcon_map.
  apply view_shift_sepcon_list; rewrite !Zlength_map; auto; intros.
  erewrite !Znth_map, !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
  unfold node_entry, node_entry_W.
  etransitivity; [apply protocol_R_W|].
  view_shift_intros; apply protocol_W_R.
Qed.*)

Lemma map_Znth_log_latest : forall {B} m k (v : list B) i d, log_latest m k v ->
  log_latest (map_Znth i m d) k (Znth i v d).
Proof.
  unfold log_latest, map_Znth; intros.
  destruct H as [-> H]; split; auto.
  intros; rewrite H; auto.
Qed.

(* up *)
Lemma map_Znth_upd : forall {A B} {A_eq : EqDec A} (m : A -> option (list B)) k v i d,
  map_Znth i (map_upd m k v) d = map_upd (map_Znth i m d) k (Znth i v d).
Proof.
  intros; unfold map_Znth, map_upd; extensionality.
  if_tac; auto.
Qed.

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((((((n, input), sh), shi), version), locs), vals), g), g'), lg), L), v0), vs0); Intros.
  destruct H as (HP0 & HP & HQ).
  forward.
  rewrite map_map in HP, HQ.
  unfold node_state; Intros v0' vs0'.
  assert (v0' = v0 /\ vs0' = vs0) as [] by (eapply log_latest_inj; eauto); subst.
  focus_SEP 2; apply make_protocol_R.
  forward_call_dep [Z : Type] (version, g, v0, Z.le, version_T locs g lg,
    protocol_piece Wsh version g v0 Z.le (version_T locs g lg), fun s v : Z => !!(v = s) && emp).
  { split; [|auto with dup].
    intros.
    apply derives_view_shift; unfold version_T; entailer!. }
  Intros x; destruct x as (?, v); simpl in *; subst.
  assert (Wsh <> Share.bot).
  { intro X; contradiction unreadable_bot; rewrite <- X; auto. }
  gather_SEP 1 0; apply protocol_R_absorb; auto; Intros.
  assert (v = v0) by omega; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call_dep [Z : Type] (version, v0 + 1, g, v0, v0 + 1, Z.le, version_T locs g lg,
    P * protocol_piece Wsh version g v0 Z.le (version_T locs g lg), II, lI,
    EX L : _, EX v : Z, EX vs : list Z, !!(Z.even v = true /\ log_latest L v vs /\ forall v vs, L v = Some vs -> Zlength vs = size) &&
      fold_right sepcon emp (map (fun i => node_entry Ish (map_Znth i L 0) locs g lg i)
        (upto (Z.to_nat size))) * ghost (Ish, L) g' * R L,
    P * protocol_piece Wsh version g (v0 + 1) Z.le (version_T locs g lg)).
  { split; [auto | split; [|split; [|omega]]].
    - rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
      unfold node_state.
      view_shift_intro L1; view_shift_intro v; view_shift_intro vs.
      apply derives_view_shift; Exists L1 v vs; entailer!.
      erewrite sepcon_assoc, (sepcon_comm (ghost _ _)), <- sepcon_assoc, protocol_piece_share_join by eauto; entailer!.
    - intros.
      Print node_state.
      Search Wsh Ish.
      Intro x; destruct x as (v, vs).
      unfold node_state; Intros v'.
      Exists Tsh v' v vs; entailer!.

    - admit. }
  assert (0 <= size) by (rewrite size_def; computable).
  assert_PROP (Zlength (map (fun x => vint x) vals) = size) by entailer!.
  assert (Z.even (v0 + 2) = true) by (rewrite Z.even_add; replace (Z.even v0) with true; auto).
  rewrite <- seq_assoc.
  focus_SEP 4.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
  forward_for_simple_bound 8 (EX i : Z, PROP () (LOCALx Q
    (SEPx (fold_right sepcon emp (map (node_entry_W (map_upd L (v0 + 2) vals) locs g lg lg') (sublist 0 i (upto (Z.to_nat size)))) ::
           fold_right sepcon emp (map (node_entry_W L locs g lg lg') (sublist i size (upto (Z.to_nat size)))) :: R)))) end.
  { rewrite sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    entailer!. }
  - (* loop body *)
    forward; rewrite <- size_def in *.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward.
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    rewrite Zlength_map in *.
    destruct (log_latest_upd (map_Znth i L 0) v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
    { apply map_Znth_log_latest; auto. }
    unfold node_entry_W at 2.
    forward_call_dep [Z -> option Z : Type] (Znth i locs Vundef, Znth i vals 0, Znth i lg Vundef,
      Znth i lg' Vundef, map_Znth i L 0, map_upd (map_Znth i L 0) (v0 + 2) (Znth i vals 0), @map_incl Z Z,
      data_T g,
      protocol_W version g g' (v0 + 1) Z.le (version_T locs g lg lg'),
      protocol_W version g g' (v0 + 1) Z.le (version_T locs g lg lg')).
    { split; [apply Forall_Znth; auto; omega|].
      split; auto; intros.
      unfold data_T.
      view_shift_intro ver; view_shift_intros.
      etransitivity; [apply view_shift_sepcon1, protocol_W_R|].
      rewrite sepcon_assoc; etransitivity.
      { apply view_shift_sepcon2; unfold protocol_R.
        rewrite sepcon_assoc.
        apply view_shift_sepcon2, ghost_snap_choose'. }
      apply derives_view_shift; Exists (v0 + 2); rewrite <- Z.add_sub_assoc.
      unfold protocol_W; rewrite general_atomics.invariant_duplicable at 3; entailer!. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl fold_right.
    rewrite <- size_def, <- map_Znth_upd; unfold node_entry_W; entailer!.
  - rewrite <- size_def, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    assert (repable_signed (v0 + 2)) by admit.
    destruct (log_latest_upd L v0 vs0 (v0 + 2) vals); auto; try omega.
    forward_call_dep [Z : Type] (version, v0 + 2, g, g', v0 + 1, v0 + 2, Z.le, version_T locs g lg lg',
      fold_right sepcon emp (map (node_entry_W (map_upd L (v0 + 2) vals) locs g lg lg') (upto (Z.to_nat size))),
      fold_right sepcon emp (map (node_entry_W (map_upd L (v0 + 2) vals) locs g lg lg') (upto (Z.to_nat size)))).
    { fast_cancel. }
    { split; [auto | split; [|omega]].
      intros; unfold version_T.
      view_shift_intro L1; view_shift_intros.
      etransitivity; [apply update_entries|].
      rewrite Z.even_add; replace (Z.even v0) with true; simpl.
      apply derives_view_shift; Exists (map_upd L (v0 + 2) vals); entailer!.
      eauto. }
    rewrite <- (map_map II).
    gather_SEP 0 1 6 5; rewrite <- !sepcon_assoc; apply invariants_view_shift with
      (Q0 := node_state_W (map_upd L (v0 + 2) vals) version locs g g' lg lg' * EX L : _, Q L tt).
    { rewrite !map_map, !sepcon_assoc, (sepcon_comm P), <- sepcon_assoc.
      etransitivity; [apply view_shift_sepcon2, HP|].
      view_shift_intro L1.
      rewrite <- !exp_sepcon2, <- exp_sepcon1, <- !sepcon_assoc.
      rewrite !sepcon_assoc, (sepcon_comm (exp _)), <- sepcon_assoc.
      etransitivity; [|apply view_shift_sepcon2; etransitivity; [apply (HQ L1 tt) |
        apply derives_view_shift; Exists L1; auto]].
      unfold node_state; view_shift_intro v; view_shift_intro vs; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_R _ _ _ _ _ _)), <- sepcon_assoc, 2sepcon_assoc.
      rewrite (sepcon_comm (protocol_R _ _ _ _ _ _)).
      etransitivity; [apply view_shift_sepcon1, protocol_R_W|].
      view_shift_intros; etransitivity; [apply view_shift_sepcon1, protocol_W_R|].
      rewrite sepcon_comm, <- !sepcon_assoc, 2sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, update_entries|].
      apply derives_view_shift; unfold node_state_W.
      Exists (v0 + 2) (v0 + 2) vals vals; entailer!. }
    Intro L1; forward.
    rewrite map_map; Exists tt L1; entailer!.
Admitted.

Lemma body_make_node : semax_body Vprog Gprog f_make_node make_node_spec.
Proof.
  start_function.
  forward_malloc tnode n.
  forward_malloc tint p.
  repeat forward.
  apply ghost_alloc with (g := (@None Z, Some 0)); [apply master_init' | Intros g].
  apply master_snap; Intros.
  apply ghost_snap_le with (v1 := -1); [omega|].
  forward_for_simple_bound 8 (EX i : Z, EX ld : list val, PROP (Zlength ld = i; Forall isptr ld)
    LOCAL (temp _n n)
    SEP (ghost_snap (-1) g; ghost_master 0 g; malloc_token Tsh (sizeof tint) p; data_at Tsh tint (vint 0) p;
         malloc_token Tsh (sizeof tnode) n;
         @data_at CompSpecs Tsh tnode (p, ld ++ repeat Vundef (Z.to_nat (8 - i))) n;
         EX lg : list val, EX lg' : list val, !!(Zlength lg = i /\ Zlength lg' = i) &&
           fold_right sepcon emp (map (fun i => node_entry_W (singleton 0 (repeat 0 (Z.to_nat size))) ld g lg lg' i *
             node_entry (singleton 0 0) ld g lg lg' i) (upto (Z.to_nat i)));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) ld))).
  { Exists (@nil val) (@nil val) (@nil val); entailer!; auto. }
  - apply ghost_snap_duplicable.
    Intros lg lg'.
    forward_malloc tint d.
    rewrite data_at__isptr; Intros.
    forward.
    gather_SEP 1 2; eapply view_shift_trans; [|apply (make_protocol d 0 (singleton 0 0) (data_T g)); auto|].
    { unfold data_T.
      apply derives_view_shift; Exists 0; entailer!.
      apply log_latest_singleton. }
    Intros gi gi'.
    apply protocol_W_R.
    forward.
    Exists (x ++ [d]) (lg ++ [gi]) (lg' ++ [gi']); rewrite upd_init, <- app_assoc, !Zlength_app, !Zlength_cons,
      !Zlength_nil by (auto; tauto).
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app, Z2Nat.id by omega.
    unfold node_entry_W at 3; unfold node_entry at 3; simpl fold_right.
    rewrite !app_Znth2 by omega.
    replace (Zlength lg) with i; replace (Zlength lg') with i; replace (Zlength x) with i;
      rewrite Z.add_0_r, Zminus_diag, !Znth_0_cons.
    rewrite map_Znth_single, Znth_repeat.
    entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    cancel; erewrite map_ext_in; eauto; simpl; intros.
    unfold node_entry_W, node_entry.
    rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1 by omega; auto.
  - Intros ld lg lg'.
    rewrite <- size_def in *.
    rewrite Zminus_diag, app_nil_r.
    gather_SEP 0 1; apply master_snap_absorb_gen.
    rewrite sepcon_map; Intros.
    gather_SEP 2 0 6; eapply view_shift_trans;
      [|apply (make_protocol'(ord := Z.le) p g 0 0 (version_T ld g lg lg')); auto|].
    { unfold version_T.
      apply derives_view_shift; Exists (singleton 0 (repeat 0 (Z.to_nat size))); simpl; entailer!.
      { eexists; apply log_latest_singleton. }
      erewrite map_ext; eauto; intros; simpl.
      rewrite map_Znth_single, Znth_repeat; auto. }
    forward.
    unfold node_state_W.
    Exists n p ld g g' lg lg' 0 (repeat 0 (Z.to_nat size)); entailer!.
    apply log_latest_singleton.
Qed.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  name data _data.
  start_function.
  rewrite data_at__eq; unfold default_val; simpl.
  repeat forward.
  change (field_at Tsh (tarray tint 8) [] _ data) with (data_at Tsh (tarray tint 8) (repeat (vint 0) 8) data).
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (lvar _data (tarray tint 8) data; temp _n n)
    SEP (data_at Tsh (tarray tint 8) (repeat (vint i) 8) data; @data_at CompSpecs sh tnode (version, locs) n;
         node_state_W (map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)) (upto (Z.to_nat i))))
           version locs g g' lg lg')).
  { entailer!. }
  - Intros.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    forward_for_simple_bound 8 (EX j : Z, PROP () (LOCALx Q
      (SEPx (data_at Tsh (tarray tint 8) (repeat (vint (i + 1)) (Z.to_nat j) ++
             repeat (vint i) (Z.to_nat (8 - j))) data :: R)))) end.
    { entailer!. }
    + forward.
      { entailer!.
        rewrite app_Znth2; rewrite Zlength_repeat, Z2Nat.id; try omega.
        rewrite Zminus_diag, Znth_repeat' by (rewrite Z2Nat.id; omega); auto. }
      rewrite app_Znth2; rewrite Zlength_repeat, Z2Nat.id; try omega.
      rewrite Zminus_diag, Znth_repeat' by (rewrite Z2Nat.id; omega).
      forward.
      rewrite add_repr, upd_init_const by auto; entailer!.
    + 
    (* change_compspecs runs forever here *)
Ltac lookup_spec_and_change_compspecs CS id ::=
 tryif apply f_equal_Some
 then
   (match goal with |- ?A = ?B =>
      let x := fresh "x" in set (x := A);
      let y := fresh "y" in set (y := B);
      hnf in x; subst x; subst y
   end;
   match goal with
   | |- ?fs = _ => check_canonical_funspec (id,fs);
      first [reflexivity |
      match goal with
       | |- mk_funspec _ _ ?t1 _ _ = mk_funspec _ _ ?t2 _ _ =>
         first [unify t1 t2
           | elimtype False; elimtype (Witness_type_of_forward_call_does_not_match_witness_type_of_funspec
      t2 t1)]
      end]
   end)
 else elimtype  (Cannot_find_function_spec_in_Delta id).

Lemma node_state_W_R : forall L version locs g g' lg lg',
  view_shift (node_state_W L version locs g g' lg lg')
             (node_state_W L version locs g g' lg lg' * node_state L version locs g g' lg lg').
Proof.
  intros; unfold node_state_W.
  view_shift_intro v; view_shift_intro vs; view_shift_intros.
  etransitivity; [apply view_shift_sepcon1, protocol_W_R|].
  etransitivity.
  - apply view_shift_sepcon2, view_shift_sepcon_list; [rewrite 2Zlength_map; eauto | rewrite Zlength_map; intros].
    erewrite 2Znth_map, 2Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    unfold node_entry_W; apply protocol_W_R.
  - apply derives_view_shift; unfold node_state.
    Exists v vs v vs; rewrite sepcon_map; entailer!.
Qed.

      (* This is a bit annoying: because write is specified as atomic with node_state, we need to have a
         node_state to call it, even though it's subsumed by node_state_W. *)
      focus_SEP 2; apply node_state_W_R.
      forward_call (n, data, sh, Tsh, version, locs, repeat (i + 1) 8, g, g', lg, lg', map_upd_list L
        (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)) (upto (Z.to_nat i))), v + 2 * i,
        if eq_dec i 0 then vs else repeat i 8,
        node_state (map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)) (upto (Z.to_nat i))))
          version locs g g' lg lg',
        fun (_ : Z -> option (list Z)) (_ : unit) => EX L : _, node_state L version locs g g' lg lg',
        fun _ : Z -> option (list Z) => emp, fun _ : Z => FF, @nil Z).
      { entailer!.
        { split; [|split].
          * apply Forall_repeat.
            split; [pose proof Int.min_signed_neg; omega|].
            transitivity 3; [omega | computable].
          * rewrite Z.even_add_mul_2; auto.
          * split; [if_tac; auto; rewrite size_def; apply Zlength_repeat|].
            eapply log_latest_upd_list; eauto; try omega.
            -- if_tac.
               { subst; rewrite Z.add_0_r; auto. }
               rewrite <- (Z.sub_simpl_r i 1), Z2Nat.inj_add, upto_app, map_app by omega.
               setoid_rewrite last_snoc.
               rewrite Z2Nat.id, Z.add_0_r; auto; omega.
            -- rewrite Forall_map, Forall_forall; intros; simpl.
               rewrite In_upto, Z2Nat.id in *; omega. }
        rewrite size_def, Zminus_diag, app_nil_r, map_repeat; simpl; cancel. }
      { split; [|split].
        * admit.
        * admit.
        * intros _ _.
          apply derives_view_shift; Exists (map_upd (map_upd_list L (map (fun i0 =>
            (v + 2 * (i0 + 1), repeat (i0 + 1) 8)) (upto (Z.to_nat i)))) (v + 2 * i + 2) (repeat (i + 1) 8));
            cancel. }
      Intros L0.
      rewrite Z2Nat.inj_add, upto_app, map_app, map_upd_list_app by omega.
      change (upto 1) with [0]; simpl map_upd_list.
      rewrite Z2Nat.id, Z.add_0_r, Z.mul_add_distr_l, Z.add_assoc by omega.
      rewrite <- size_def; entailer!.
      admit.
  - forward.
    Exists data; rewrite size_def; entailer!.
Admitted.

(*Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, lg', ghost_hist gsh ([] : hist) gh,
    fun (_ : Z * list Z) '(v, vs) => EX h' : _, !!(add_events [] [HRead v vs] h') &&
      ghost_hist gsh h' gh,
    fun s => ghost_hist gsh ([] : hist) gh * EX hr : _, !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some s) &&
      ghost_ref hr gh,
    fun p => if eq_dec p 0 then node_inv gh version locs g g' lg lg' else FF, [0]).
  { entailer!.
    rewrite size_def, eq_dec_refl; simpl; cancel. }
  { split; [|split].
    * apply ghost_timeless.
    * simpl.
      admit. (* laters are messy *)
    * intros (v0, vs0) (v1, vs1); simpl.
      unfold node_inv.
      view_shift_intro hr; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_hist _ _ _)).
      rewrite <- sepcon_assoc.
      rewrite <- sepcon_assoc, sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, hist_add' with (e := HRead v1 vs1); auto|].
      apply derives_view_shift; Exists [(length hr, HRead v1 vs1)]; simpl; entailer!.
      { apply add_events_1 with (h := []), hist_incl_lt; auto. }
      eapply derives_trans, now_later.
      Exists v1 vs1 (hr ++ [HRead v1 vs1]); entailer!.
      rewrite apply_hist_app; replace (apply_hist _ _) with (Some (v0, vs0)); auto.
      (* At this point, the proof fails: the state recorded in the invariant may not match the state we read
         from. *)
Abort.*)

(*Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_atomic_function.
  destruct x as (((((((((n, sh), version), locs), g), g'), lg), lg'), gh), gsh); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, lg', P,
    fun (_ : Z * list Z) '(v1, vs1) => Q tt (v1, vs1),
    fun s => EX hr : _, !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some s) && ghost_ref hr gh, II, lI).
  { simpl; rewrite <- size_def; entailer!. }
  { split; [|split].
    * auto.
    * simpl.
      admit. (* laters are messy *)
    * intros (v0, vs0) (v1, vs1); simpl.
      rewrite map_map; etransitivity; [|apply HQ]; simpl.
      (* This also fails: the history in the invariant may not have caught up with the value we read. *)
Abort.*)

(*??*)
Lemma node_state_join : forall L1 L2 version locs g g' lg lg',
  node_state L1 version locs g g' lg lg' * node_state L2 version locs g g' lg lg' |--
  node_state (map_add L1 L2) version locs g g' lg lg'.
Proof.
  intros; unfold node_state.
  Intros v1 vs1 v2 vs2.
  rewrite <- sepcon_assoc, (sepcon_comm _ (protocol_R _ _ _ _ _ _)), <- sepcon_assoc.
  erewrite protocol_R_join; [|simpl; eauto].
  rewrite Z.max_comm; Exists (Z.max v1 v2) (if zlt v1 v2 then vs2 else vs1); entailer!.
  { split; [|apply log_latest_add; auto].
    destruct (Z.max_spec v1 v2) as [[? ->] | [? ->]]; auto. }
  rewrite <- sepcon_map; apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
  erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
  rewrite map_Znth_add; apply node_entry_join.
Qed.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, lg', node_state L version locs g g' lg lg',
    fun (_ : Z -> option (list Z)) '(v, vs) => EX L' : _, !!(L' v = Some vs) && node_state L' version locs g g' lg lg',
    fun _ : Z -> option (list Z) => emp, fun _ : Z => FF, @nil Z).
  { rewrite <- size_def; entailer!; cancel. }
  { split; [|split].
    * admit.
    * admit.
    * intros L' (v1, vs1).
      rewrite sepcon_emp, sepcon_comm; apply derives_view_shift; eapply derives_trans; [apply node_state_join|].
      Exists (map_add (singleton v1 vs1) L'); simpl; entailer!.
      unfold map_add, singleton; rewrite eq_dec_refl; auto. }
  Intro x; destruct x as ((v', vs'), ?); simpl; Intros L'.
  forward.
  Exists data v' vs'; entailer!.
  { 
Qed.