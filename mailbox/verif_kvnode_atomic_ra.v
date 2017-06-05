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
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  fold_right sepcon emp (map (fun i => node_entry Share.bot true (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))) *
  ghost_snap L g'.

Definition node_state (sh : share) (L : Z -> option (list Z)) v version locs g lg g' :=
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  protocol_piece sh version g v Z.le (version_T locs g lg g') *
  fold_right sepcon emp (map (fun i => node_entry sh (Z.even v) (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))) *
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

Lemma Ish_nonempty : Ish <> Share.bot.
Proof.
  repeat intro; contradiction unreadable_bot; rewrite <- H; auto.
Qed.

Lemma Wsh_nonempty : Wsh <> Share.bot.
Proof.
  repeat intro; contradiction unreadable_bot; rewrite <- H; auto.
Qed.

Hint Resolve Ish_nonempty Wsh_nonempty.

(* It's useful to have both private and shared node_states, so we can know that whatever we read is at least
   later than what we already knew. *)
Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * share * val * list val * val * val * list val * (Z -> option (list Z)) * Z))
  empty_map [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) => temp _n n;
   fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) => temp _out out]
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) => !!(readable_share sh /\
     writable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size) &&
   data_at sh tnode (version, locs) n * data_at_ shi (tarray tint size) out *
   node_state Share.bot L0 v0 version locs g lg g')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) L =>
   EX v1 : Z, node_state Ish L v1 version locs g lg g')
  (0, []) []
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) L '(v, vals) =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) out *
   EX v1 : Z, node_state Share.bot L v1 version locs g lg g')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) L '(v, vals) =>
   !!(map_incl L0 L /\ v0 <= v /\ Z.even v = true /\ Zlength vals = size /\ L v = Some vals) &&
   EX v1 : Z, node_state Ish L v1 version locs g lg g')
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
              (Z -> option (list Z)) * Z))
  empty_map [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) => temp _n n;
   fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) => temp _in input]
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) => !!(readable_share sh /\
     readable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\
     Forall repable_signed vals /\ Z.even v0 = true) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state Wsh L v0 version locs g lg g' * ghost (gsh1, L) g')
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) L' =>
   EX v : Z, node_state Ish L' v version locs g lg g')
  tt []
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) _ _ =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state Wsh (map_upd L (v0 + 2) vals) (v0 + 2) version locs g lg g' *
   ghost (gsh1, map_upd L (v0 + 2) vals) g')
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) _ _ =>
   node_state Ish (map_upd L (v0 + 2) vals) (v0 + 2) version locs g lg g')
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
         node_state gsh2 (singleton 0 (repeat 0 (Z.to_nat size))) 0 version locs g lg g';
         ghost (gsh1, singleton 0 (repeat 0 (Z.to_nat size))) g').

Definition writer_spec := DECLARE _writer
  WITH n : val, sh : share, v : Z, L : Z -> option (list Z), version : val, locs : list val,
       g : val, lg : list val, g' : val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size; Z.even v = true)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state Wsh L v version locs g lg g'; ghost (gsh1, L) g';
         invariant (EX L : _, EX v1 : Z, node_state Ish L v1 version locs g lg g'))
  POST [ tptr tvoid ]
   EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + (2 * (i + 1)), repeat (i + 1) (Z.to_nat size)))%Z (upto 3)))
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Wsh L' (v + 6) version locs g lg g';
         ghost (gsh1, L') g'; invariant (EX L : _, EX v1 : Z, node_state Ish L v1 version locs g lg g')).

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
  WITH n : val, sh : share, v : Z, L : Z -> option (list Z), version : val, locs : list val,
       g : val, g' : val, lg : list val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot L v version locs g lg g';
         invariant (EX L : _, EX v1 : Z, node_state Ish L v1 version locs g lg g'))
  POST [ tptr tvoid ]
   EX v' : Z, EX vs' : list Z,
    PROP (v <= v'; v' = v -> Z.even v = true /\ L v = Some vs')
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot (map_upd L v' vs') v' version locs g lg g';
         invariant (EX L : _, EX v1 : Z, node_state Ish L v1 version locs g lg g')).

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

Lemma node_state_duplicable : forall L v version locs g lg g',
  duplicable (node_state Share.bot L v version locs g lg g').
Proof.
  intros; unfold node_state.
  apply sepcon_duplicable, ghost_snap_duplicable.
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
  etransitivity; [apply protocol_R_forget with (s1 := singleton v v'); try apply map_join_incl_compat|].
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

Lemma node_state_snap : forall sh L v version locs g lg g',
  view_shift (node_state sh L v version locs g lg g')
    (node_state sh L v version locs g lg g' * node_state Share.bot L v version locs g lg g').
Proof.
  intros; unfold node_state; view_shift_intros.
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
    apply derives_view_shift; entailer!.
Qed.

Lemma node_entry_choose : forall b1 b2 log1 log2 locs g lg i,
  view_shift (node_entry Share.bot b1 log1 locs g lg i * node_entry Share.bot b2 log2 locs g lg i)
    (node_entry Share.bot b1 log1 locs g lg i).
Proof.
  intros; unfold node_entry.
  view_shift_intro log1'; view_shift_intro log2'; view_shift_intros.
  etransitivity; [apply protocol_R_choose, map_join_incl_compat|].
  apply derives_view_shift; Exists log1'; entailer!.
Qed.

Lemma node_entry_absorb : forall sh b1 b2 L1 L2 locs g lg i,
  view_shift (node_entry sh b1 L1 locs g lg i * node_entry Share.bot b2 L2 locs g lg i)
    (node_entry sh b1 L1 locs g lg i).
Proof.
  intros.
  destruct (eq_dec sh Share.bot).
  - subst; apply node_entry_choose.
  - unfold node_entry.
    view_shift_intro log1; view_shift_intro log2; view_shift_intros.
    etransitivity; [apply protocol_R_absorb; auto|].
    apply derives_view_shift; Exists log1; entailer!.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((((n, out), sh), shi), version), locs), g), g'), lg), L0), v0); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  assert (0 <= size) by (rewrite size_def; computable).
  apply semax_pre with (P' := PROP () LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ shi (tarray tint size) out;
         EX v : Z, !!(v0 <= v) && protocol_R version g v Z.le (version_T locs g lg g');
         EX ll : _, EX lb : _, fold_right sepcon emp (map (fun i => node_entry Share.bot (Znth i lb false) (Znth i ll empty_map) locs g lg i)
           (upto (Z.to_nat size))); EX L' : _, ghost_snap (map_add L0 L') g';
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { unfold node_state; Intros.
    Exists v0 (map (fun i => map_Znth i L0 0) (upto (Z.to_nat size))) (repeat (Z.even v0) (Z.to_nat size)) (@empty_map Z (list Z));
      rewrite map_add_empty; entailer!.
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
  gather_SEP 7 3; rewrite map_snap_join; Intros.
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
    Exists v1 (map (fun i => map_Znth i L1 0) (upto (Z.to_nat size))) (repeat true (Z.to_nat size)) (map_add L' L1);
      rewrite map_add_assoc; entailer!.
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
         EX vers' : list Z, !!(Zlength vers' = i /\ Forall (fun v => Z.even v = true /\ v1 <= v) vers' /\
             forall j, 0 <= j < i -> Znth j vers' 0 = v1 -> map_Znth j L1 0 v1 = Some (Znth j vals 0)) &&
           protocol_R version g (list_max v1 (map (fun x => x - 1) vers')) Z.le (version_T locs g lg g') *
           fold_right sepcon emp (map (fun i => node_entry Share.bot true (singleton (Znth i vers' 0) (Znth i vals 0)) locs g lg i)
             (sublist 0 i (upto (Z.to_nat size))));
         fold_right sepcon emp (map (fun i => node_entry Share.bot true (map_Znth i L1 0)
           locs g lg i) (sublist i size (upto (Z.to_nat size)))); ghost_snap (map_add (map_add L0 L') L1) g';
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { Exists (@nil Z) (@nil Z).
    rewrite data_at__eq; unfold default_val; simpl data_at.
    rewrite repeat_list_repeat, Z.sub_0_r; entailer!.
    { intros; omega. }
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
      rewrite !sepcon_assoc, <- (sepcon_assoc (ghost _ _)); setoid_rewrite ghost_snap_join_Z.
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
    match goal with H : exists vs, _ /\ log_latest _ _ _ |- _ => destruct H as (vs1 & ? & HL1) end.
    rewrite <- size_def, upd_init, !map_app, <- app_assoc by (rewrite ?Zlength_map; omega).
    entailer!.
    { split.
      + rewrite Forall_app; repeat constructor; auto.
        eapply log_incl_latest; eauto.
        unfold map_Znth, map_add.
        destruct HL1 as [->]; simpl; eauto.
      + intros ?? Hj.
        destruct (zlt j (Zlength x)); [assert (0 <= j < Zlength x) by tauto; rewrite app_Znth1 in * by omega; eauto|].
        rewrite app_Znth2 in * by omega.
        assert (j = Zlength x) by omega; subst j.
        replace (Zlength vers') with (Zlength x) in Hj by omega;
          rewrite Zminus_diag, Znth_0_cons in Hj |- *; subst.
        assert (exists v, map_Znth (Zlength x) L1 0 v1 = Some v) as [d' Hd'].
        { unfold map_Znth.
          match goal with H : log_latest L1 _ _ |- _ => destruct H as [->]; simpl; eauto end. }
        match goal with H : map_incl _ _ |- _ => pose proof (H _ _ Hd') as Hd'' end.
        match goal with H : log_latest log' _ _ |- _ => destruct H as [Hd]; rewrite Hd in Hd''; inv Hd''; auto end. }
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
        (Q0 := EX L : _, EX v : Z, node_state Share.bot L v version locs g lg g' * Q L (v1, vals')).
      { rewrite !map_map, !sepcon_assoc, (sepcon_comm P), <- 2sepcon_assoc.
        etransitivity; [apply view_shift_sepcon2, HP|].
        view_shift_intro L2; view_shift_intro v'.
        etransitivity; [|apply derives_view_shift; Exists L2 v'; apply derives_refl].
        rewrite !sepcon_assoc, (sepcon_comm (Q _ _)).
        etransitivity; [|apply view_shift_sepcon2, HQ]; simpl.
        unfold node_state at 1; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _ _)).
        rewrite <- !sepcon_assoc, 4sepcon_assoc; etransitivity;
          [apply view_shift_sepcon1, protocol_R_absorb; auto|].
        view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ g')).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ g')).
        rewrite <- !sepcon_assoc, snap_master_join by auto; view_shift_intros.
        rewrite !sepcon_assoc, <- (sepcon_assoc (fold_right _ _ _)), <- sepcon_map.
        rewrite (sepcon_comm (fold_right _ _ _)), <- !sepcon_assoc.
        etransitivity; [apply view_shift_sepcon2, view_shift_sepcon_list with
          (l2 := map (fun i => node_entry Ish (Z.even v') (map_Znth i L2 0) locs g lg i) (upto (Z.to_nat size)));
          rewrite !Zlength_map; auto|].
        { intros.
          erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
          unfold node_entry.
          view_shift_intro log1; view_shift_intro log2; view_shift_intros.
          rewrite sepcon_comm; etransitivity; [apply protocol_R_absorb; auto|].
          apply derives_view_shift; Exists log2; entailer!. }
        transitivity (node_state Ish L2 v' version locs g lg g' * R L2).
        { unfold node_state; apply derives_view_shift; entailer!. }
        etransitivity; [apply view_shift_sepcon1, node_state_snap|].
        apply derives_view_shift, andp_right; [apply prop_right | Exists v'; cancel].
        repeat split; auto; try omega.
        * etransitivity; eauto.
          rewrite map_add_assoc; apply map_incl_add.
        * match goal with H : map_incl (map_add _ _) _ |- _ => rewrite map_add_comm in H by auto; apply H end.
          unfold map_add.
          rewrite map_Znth_eq with (vs := vals')(d := 0); auto.
          { intros ? HL1.
            match goal with H : exists vs, _ |- _ => destruct H as [? [? [Heq]]]; rewrite Heq in HL1; inv HL1; omega end. }
          { intro; subst; rewrite size_def in *; discriminate. }
          intros j Hj; replace (Zlength vals') with size in Hj; assert (Znth j vers' 0 = v1); auto.
          match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i := j)(d := 0) in H;
            [destruct H as [Heven] | omega] end.
          destruct (list_max_spec (map (fun x => x - 1) vers') v1) as [_ Hmax].
          rewrite Forall_map in Hmax.
          apply Forall_Znth with (i := j)(d := 0) in Hmax; [simpl in Hmax | omega].
          destruct (eq_dec (Znth j vers' 0) v1); subst; auto.
          assert (Znth j vers' 0 = v1 + 1) as Heq by omega.
          rewrite Heq, Z.even_add in Heven; replace (Z.even v1) with true in Heven; discriminate. }
      Intros L2 v2.
      forward.
      rewrite map_map; Exists (v1, vals') L2 v2; entailer!.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; go_lower; Exists v2 (map (fun i => singleton (Znth i vers' 0) (Znth i vals' 0))
        (upto (Z.to_nat size))) (repeat true (Z.to_nat size)) (map_add L' L1); rewrite map_add_assoc; entailer!.
      { destruct (list_max_spec (map (fun x => x - 1) vers') v1); omega. }
      erewrite map_ext_in; eauto; intros; simpl.
      rewrite In_upto in *; erewrite Znth_repeat', Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega.
Qed.

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((((n, input), sh), shi), version), locs), vals), g), g'), lg), L), v0); Intros.
  destruct H as (HP0 & HP & HQ).
  forward.
  rewrite map_map in HP, HQ.
  unfold node_state; Intros.
  replace (Z.even v0) with true.
  focus_SEP 2; apply make_protocol_R.
  forward_call_dep [Z : Type] (version, g, v0, Z.le, version_T locs g lg g',
    protocol_piece Wsh version g v0 Z.le (version_T locs g lg g'), fun s v : Z => !!(v = s) && emp).
  { split; [|auto with dup].
    intros.
    apply derives_view_shift; unfold version_T; entailer!. }
  Intros x; destruct x as (?, v); simpl in *; subst.
  gather_SEP 1 0; apply protocol_R_absorb; auto; Intros.
  assert (v = v0) by omega; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call_dep [Z : Type] (version, v0 + 1, g, v0, v0 + 1, Z.le, version_T locs g lg g',
    P * protocol_piece Wsh version g v0 Z.le (version_T locs g lg g'), II, lI,
    EX L : _, !!(exists vs, Zlength vs = size /\ log_latest L v0 vs) &&
      fold_right sepcon emp (map (fun i => node_entry Ish (Z.even v0) (map_Znth i L 0) locs g lg i)
        (upto (Z.to_nat size))) * ghost (Ish, L) g' * R L,
    P * protocol_piece Wsh version g (v0 + 1) Z.le (version_T locs g lg g')).
  { split; [auto | split; [|split; [|omega]]].
    - rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
      unfold node_state.
      view_shift_intro L1; view_shift_intro v; view_shift_intros.
      erewrite sepcon_comm, <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _ _)),
        protocol_piece_share_join by eauto.
      view_shift_intros; subst; replace (Z.even v0) with true in *.
      apply derives_view_shift; Exists L1; entailer!.
    - intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _ _)), <- !sepcon_assoc, (sepcon_assoc _ _ P).
      etransitivity; [|apply view_shift_sepcon2, HP].
      unfold version_T at 1 4.
      view_shift_intro L0; view_shift_intro L1; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
      rewrite <- !sepcon_assoc, snap_master_join by auto; view_shift_intros.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, make_snap|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
      rewrite <- !sepcon_assoc, <- sepcon_map.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, view_shift_sepcon_list|].
      { rewrite 2Zlength_map; reflexivity. }
      { rewrite Zlength_map; intros.
        erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
        etransitivity; [rewrite sepcon_comm; apply node_entry_absorb|].
        etransitivity; [apply node_entry_snap|].
        eapply view_shift_sepcon1 with (P' := node_entry Ish (Z.even (v0 + 1)) _ _ _ _ _).
        unfold node_entry.
        rewrite Z.even_add; replace (Z.even v0) with true; simpl.
        apply derives_view_shift; Intro log'; Exists log'; entailer!. }
      rewrite (add_andp (protocol_W _ _ _ _ _) (!!(v0 + 1 = v0 + 1))), andp_comm by entailer!.
      setoid_rewrite <- protocol_piece_share_join; eauto.
      apply derives_view_shift; Exists L0 L0 (v0 + 1); unfold node_state; rewrite sepcon_map, !Z.even_add;
        replace (Z.even v0) with true; simpl; rewrite Z.add_simpl_r; entailer!. }
  assert (0 <= size) by (rewrite size_def; computable).
  assert_PROP (Zlength (map (fun x => vint x) vals) = size) by entailer!.
  assert (Z.even (v0 + 2) = true) by (rewrite Z.even_add; replace (Z.even v0) with true; auto).
  rewrite <- seq_assoc.
  focus_SEP 4.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
  forward_for_simple_bound 8 (EX i : Z, PROP () (LOCALx Q
    (SEPx (fold_right sepcon emp (map (fun i => node_entry Wsh true (map_Znth i (map_upd L (v0 + 2) vals) 0)
             locs g lg i) (sublist 0 i (upto (Z.to_nat size)))) ::
           fold_right sepcon emp (map (fun i => node_entry Wsh true (map_Znth i L 0)
             locs g lg i) (sublist i size (upto (Z.to_nat size)))) :: R)))) end.
  { rewrite sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    replace (Z.even v0) with true; entailer!. }
  - (* loop body *)
    Intros; forward; rewrite <- size_def in *.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward.
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    rewrite Zlength_map in *.
    destruct H as [vs0 [? HL]]; replace (Z.even v0) with true in HL.
    destruct (log_latest_upd (map_Znth i L 0) v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
    { apply map_Znth_log_latest; auto. }
    unfold node_entry at 2.
    Intros log'; subst log'.
    forward_call_dep [Z -> option Z : Type] (Znth i locs Vundef, Znth i vals 0, Znth i lg Vundef,
      map_Znth i L 0, map_upd (map_Znth i L 0) (v0 + 2) (Znth i vals 0), @map_incl Z Z, data_T g,
      P * protocol_piece Wsh version g (v0 + 1) Z.le (version_T locs g lg g') *
        protocol_piece Wsh (Znth i locs Vundef) (Znth i lg Vundef) (map_Znth i L 0) map_incl (data_T g) *
        ghost (Wsh, L) g', II, lI,
      !!(exists vs, Zlength vs = size /\ log_latest L v0 vs) &&
        protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g') *
        fold_right sepcon emp (upd_Znth i (map (fun i => node_entry Ish false (map_Znth i L 0) locs g lg i)
          (upto (Z.to_nat size))) emp) * ghost (Ish, L) g' * ghost (Wsh, L) g' * R L,
      P * protocol_piece Wsh version g (v0 + 1) Z.le (version_T locs g lg g') *
        protocol_piece Wsh (Znth i locs Vundef) (Znth i lg Vundef) (map_Znth i (map_upd L (v0 + 2) vals) 0)
          map_incl (data_T g) * ghost (Wsh, L) g').
    { fast_cancel. }
    { split; [apply Forall_Znth; auto; omega|].
      assert (0 <= i < Zlength (upto (Z.to_nat size))) by (rewrite Zlength_upto, Z2Nat.id; auto; omega).
      split; [|split; auto].
      + rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        unfold node_state.
        view_shift_intro L1; view_shift_intro v; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ version _ _ _ _)), <- !sepcon_assoc.
        erewrite (sepcon_comm (protocol_piece _ _ _ _ _ _)), protocol_piece_share_join by eauto.
        view_shift_intros; subst.
        apply view_shift_assert with (PP := L1 = L); [|intro; subst].
        { rewrite (sepcon_comm _ (ghost _ _)), <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
          rewrite <- !sepcon_assoc; do 4 apply sepcon_derives_prop.
          eapply derives_trans; [apply ghost_conflict|].
          apply prop_left; intros ((?, ?) & Hsh & Hj); simpl in *.
          unfold share in *.
          destruct (eq_dec Ish Share.bot); [contradiction Ish_nonempty|].
          destruct (eq_dec Wsh Share.bot); [contradiction Wsh_nonempty|].
          destruct Hj; subst; apply prop_right; auto. }
        rewrite Z.even_add in *; replace (Z.even v0) with true in *; simpl in *.
        rewrite extract_nth_sepcon with (i := i) by (rewrite Zlength_map; auto).
        erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
        unfold node_entry.
        view_shift_intro log'; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece Wsh _ _ _ _ _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece Ish _ _ _ _ _)).
        erewrite <- !sepcon_assoc, protocol_piece_share_join by eauto.
        view_shift_intros; subst.
        rewrite Z.add_simpl_r in *.
        apply derives_view_shift; entailer!.
      + intros.
        rewrite !sepcon_assoc, (sepcon_comm (data_T _ _ (Znth i vals 0))).
        rewrite <- 6sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, view_shift_sepcon1, HP].
        unfold data_T at 1 4.
        view_shift_intro ver; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ version _ _ _ _)).
        rewrite <- sepcon_assoc.
        rewrite 4sepcon_assoc; etransitivity; [apply view_shift_sepcon1 with (P' :=
          !!(ver - 1 <= v0 + 1) && protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g') *
          ghost_snap (v0 + 1) g)|].
        { unfold protocol_piece.
          rewrite sepcon_assoc, (sepcon_comm (ghost _ _)), snap_master_join.
          view_shift_intros; etransitivity; [apply view_shift_sepcon2, make_snap|].
          apply derives_view_shift; entailer!.
          { intro X; contradiction unreadable_bot; rewrite <- X; auto. } }
        view_shift_intros.
        rewrite (add_andp (protocol_piece _ version _ _ _ _) (!!(v0 + 1 = v0 + 1))) by entailer!.
        erewrite andp_comm, <- protocol_piece_share_join by eauto.
        match goal with |-context[protocol_W _ _ ?v _ _] =>
          rewrite (add_andp (protocol_W _ _ _ _ _) (!!(v = v))), andp_comm by entailer!;
          setoid_rewrite <- protocol_piece_share_join; eauto end.
        apply derives_view_shift; unfold node_state.
        Exists L (v0 + 1) (v0 + 2); rewrite Z.even_add, Z.add_simpl_r; replace (Z.even v0) with true; simpl.
        rewrite map_Znth_upd, <- Z.add_sub_assoc; simpl.
        entailer!.
        rewrite replace_nth_sepcon; apply sepcon_derives; auto.
        apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
        intros j ?; destruct (eq_dec j i); [|rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto].
        subst; rewrite upd_Znth_same by (rewrite ?Zlength_map; auto).
        erewrite Znth_map, Znth_upto by (auto; rewrite Z2Nat.id; omega).
        unfold node_entry.
        Exists (map_upd (map_Znth i L 0) (v0 + 2) (Znth i vals 0)); apply andp_right; [apply prop_right|]; auto. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl fold_right.
    rewrite <- size_def; unfold node_entry; Exists (map_Znth i (map_upd L (v0 + 2) vals) 0); entailer!.
  - rewrite <- size_def, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    assert (repable_signed (v0 + 2)) by admit.
    destruct H as [vs0 [? HL]]; replace (Z.even v0) with true in HL.
    destruct (log_latest_upd L v0 vs0 (v0 + 2) vals); auto; try omega.
    forward_call_dep [Z : Type] (version, v0 + 2, g, v0 + 1, v0 + 2, Z.le, version_T locs g lg g',
      P * protocol_piece Wsh version g (v0 + 1) Z.le (version_T locs g lg g') *
        fold_right sepcon emp (map (fun i => node_entry Wsh true (map_Znth i (map_upd L (v0 + 2) vals) 0)
          locs g lg i) (upto (Z.to_nat size))) * ghost (Wsh, L) g' * ghost (gsh1, L) g', II, lI,
      !!(exists vs, Zlength vs = size /\ log_latest L v0 vs) &&
        fold_right sepcon emp (map (fun i => node_entry Ish true (map_Znth i (map_upd L (v0 + 2) vals) 0)
          locs g lg i * node_entry Wsh true (map_Znth i (map_upd L (v0 + 2) vals) 0) locs g lg i)
          (upto (Z.to_nat size))) * ghost (Tsh, L) g' * R L,
      Q L tt * protocol_piece Wsh version g (v0 + 2) Z.le (version_T locs g lg g') *
        fold_right sepcon emp (map (fun i => node_entry Wsh true (map_Znth i (map_upd L (v0 + 2) vals) 0)
          locs g lg i) (upto (Z.to_nat size))) * ghost (Wsh, map_upd L (v0 + 2) vals) g' *
          ghost (gsh1, map_upd L (v0 + 2) vals) g').
    { fast_cancel. }
    { split; [auto | split; [| split; [|omega]]].
      + rewrite <- !sepcon_assoc, 3sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        view_shift_intro L1; view_shift_intro v; unfold node_state.
        view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _ _)).
        erewrite <- !sepcon_assoc, (sepcon_comm (protocol_piece _ _ _ _ _ _)), protocol_piece_share_join by eauto.
        view_shift_intros; subst.
        rewrite sepcon_comm, <- !sepcon_assoc, sepcon_comm.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)), <- !sepcon_assoc.
        setoid_rewrite ghost_var_share_join'; eauto.
        view_shift_intros; subst.
        rewrite (sepcon_comm (ghost_var _ _ _)); setoid_rewrite ghost_var_share_join; eauto.
        rewrite (sepcon_comm _ (fold_right _ _ _)), <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
        rewrite <- !sepcon_assoc, <- sepcon_map.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, view_shift_sepcon_list with
          (l2 := map (fun i => node_entry Ish true (map_Znth i (map_upd L (v0 + 2) vals) 0) locs g lg i *
                               node_entry Wsh true (map_Znth i (map_upd L (v0 + 2) vals) 0) locs g lg i)
                     (upto (Z.to_nat size))); rewrite !Zlength_map; auto|].
        { intros.
          erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
          unfold node_entry.
          view_shift_intro log1; view_shift_intro log2; view_shift_intros.
          erewrite protocol_piece_share_join by eauto; view_shift_intros; subst log1.
          erewrite (add_andp (protocol_piece _ _ _ _ _ _) (!!(log2 = log2))), andp_comm,
            <- protocol_piece_share_join by (eauto; entailer!).
          apply derives_view_shift; Exists log2 log2; entailer!. }
        apply derives_view_shift; unfold ghost_var, protocol_W; entailer!.
        rewrite Z.even_add, Z.add_simpl_r in *; replace (Z.even v0) with true in *; simpl in *; auto.
      + intros.
        rewrite !sepcon_assoc, (sepcon_comm (version_T _ _ _ _ (v0 + 2) _)).
        rewrite <- !sepcon_assoc, 7sepcon_assoc.
        etransitivity; [|apply view_shift_sepcon1, HQ].
        unfold version_T at 1 4.
        view_shift_intro L'; view_shift_intros.
        rewrite sepcon_map, <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
        rewrite <- !sepcon_assoc, <- sepcon_map.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, view_shift_sepcon_list|].
        { rewrite 2Zlength_map; reflexivity. }
        { rewrite Zlength_map; intros.
          erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
          etransitivity; [apply node_entry_absorb | apply node_entry_snap]. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
        rewrite <- !sepcon_assoc, snap_master_join by apply Share.nontrivial; view_shift_intros.
        rewrite !sepcon_assoc; etransitivity.
        { apply view_shift_sepcon1; etransitivity.
          * apply master_update with (v' := map_upd L (v0 + 2) vals); auto.
          * apply make_snap. }
        fold (ghost_var Tsh (map_upd L (v0 + 2) vals) g').
        erewrite <- ghost_var_share_join by eauto.
        erewrite <- (ghost_var_share_join _ _ gsh2) by eauto.
        rewrite (add_andp (protocol_W _ _ _ _ _) (!!(v0 + 2 = v0 + 2))) by entailer!.
        unfold protocol_W; erewrite andp_comm, <- protocol_piece_share_join by eauto.
        apply derives_view_shift; unfold node_state; Exists (map_upd L (v0 + 2) vals).
        rewrite Z.even_add in *; replace (Z.even v0) with true in *; simpl in *.
        rewrite Zlength_map in *; rewrite sepcon_map.
        unfold ghost_var; entailer!.
        { split; eauto. }
        rewrite sepcon_comm; auto. }
    forward.
    Exists tt L; unfold node_state; entailer!.
Admitted.

Lemma body_make_node : semax_body Vprog Gprog f_make_node make_node_spec.
Proof.
  start_function.
  forward_malloc tnode n.
  forward_malloc tint p.
  repeat forward.
  apply ghost_alloc with (g := (Tsh, 0)); [apply master_init | Intros g].
  apply make_snap; Intros.
  apply ghost_snap_le with (v1 := -1); [omega|].
  forward_for_simple_bound 8 (EX i : Z, EX ld : list val, PROP (Zlength ld = i; Forall isptr ld)
    LOCAL (temp _n n)
    SEP (ghost_snap (-1) g; ghost (Tsh, 0) g; malloc_token Tsh (sizeof tint) p; data_at Tsh tint (vint 0) p;
         malloc_token Tsh (sizeof tnode) n;
         @data_at CompSpecs Tsh tnode (p, ld ++ repeat Vundef (Z.to_nat (8 - i))) n;
         EX lg : list val, !!(Zlength lg = i) && fold_right sepcon emp (map (fun i =>
           node_entry gsh2 true (singleton 0 0) ld g lg i *
           node_entry Share.bot true (singleton 0 0) ld g lg i) (upto (Z.to_nat i)));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) ld))).
  { Exists (@nil val) (@nil val); entailer!; auto. }
  - apply ghost_snap_duplicable.
    Intros lg.
    rewrite sepcon_map.
    forward_malloc tint d.
    rewrite data_at__isptr; Intros.
    forward.
    gather_SEP 1 2; eapply view_shift_trans; [|apply (make_protocol d 0 (singleton 0 0) (data_T g)); auto|].
    { unfold data_T.
      apply derives_view_shift; Exists 0; entailer!.
      apply log_latest_singleton. }
    Intros gi.
    replace_SEP 0 (node_entry gsh2 true (singleton 0 0) (x ++ [d]) g (lg ++ [gi]) i).
    { go_lower; unfold node_entry.
      Exists (singleton 0 0); rewrite !app_Znth2 by omega.
      replace (Zlength x) with i; replace (Zlength lg) with i; rewrite Zminus_diag, !Znth_0_cons; entailer!. }
    apply node_entry_snap.
    Intros; forward.
    Exists (x ++ [d]) (lg ++ [gi]); rewrite upd_init, <- app_assoc, !Zlength_app, !Zlength_cons,
      !Zlength_nil by (auto; tauto).
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app, Z2Nat.id by omega.
    simpl fold_right.
    rewrite Z.add_0_r; entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    cancel; erewrite <- sepcon_map, map_ext_in; eauto; simpl; intros.
    unfold node_entry.
    rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1 by omega; auto.
  - Intros ld lg.
    rewrite <- size_def in *.
    rewrite Zminus_diag, app_nil_r.
    gather_SEP 0 1; rewrite snap_master_join by apply Share.nontrivial.
    rewrite sepcon_map; Intros.
    apply ghost_alloc with (g0 := (Tsh, singleton 0 (repeat 0 (Z.to_nat size))));
      [apply master_init | Intros g'].
    apply make_snap; Intros.
    gather_SEP 4 2 8 0; eapply view_shift_trans;
      [|apply (make_protocol'(ord := Z.le) p g 0 0 (version_T ld g lg g')); auto|].
    { unfold version_T.
      apply derives_view_shift; Exists (singleton 0 (repeat 0 (Z.to_nat size))); simpl.
      unfold ghost_master; entailer!.
      { do 2 eexists; [|apply log_latest_singleton].
        rewrite Zlength_repeat, Z2Nat.id; auto; rewrite size_def; computable. }
      erewrite map_ext; eauto; intros; simpl.
      rewrite map_Znth_single, Znth_repeat; auto. }
    forward.
    fold (ghost_var Tsh (singleton 0 (repeat 0 (Z.to_nat size))) g');
      erewrite <- ghost_var_share_join by eauto.
    unfold node_state.
    Exists n p ld g lg g'; unfold protocol_W, ghost_var; simpl; entailer!.
    { do 2 eexists; [|apply log_latest_singleton].
      rewrite Zlength_repeat, Z2Nat.id; auto; rewrite size_def; computable. }
    rewrite sepcon_comm; apply sepcon_derives; auto.
    erewrite map_ext; eauto; simpl; intros.
    rewrite map_Znth_single, Znth_repeat; auto.
Qed.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  name data _data.
  start_function.
  rewrite data_at__eq; unfold default_val; simpl.
  repeat forward.
  forward_for_simple_bound 3 (EX i : Z, EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)%Z) (upto (Z.to_nat i))))
    LOCAL (lvar _data (tarray tint 8) data; temp _n n)
    SEP (data_at Tsh (tarray tint 8) (repeat (vint i) 8) data; @data_at CompSpecs sh tnode (version, locs) n;
         node_state Wsh L' (v + 2 * i) version locs g lg g'; ghost (gsh1, L') g';
         invariant (EX L : _, EX v1 : Z, node_state Ish L v1 version locs g lg g'))).
  { Exists L; entailer!; auto. }
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

      forward_call (n, data, sh, Tsh, version, locs, repeat (i + 1) 8, g, g', lg, x, v + 2 * i, emp,
        fun (_ : Z -> option (list Z)) (_ : unit) => emp, fun _ : Z -> option (list Z) => emp,
        fun _ : Z => EX L : _, EX v1 : Z, node_state Ish L v1 version locs g lg g', [0]).
      { entailer!.
        { split.
          * apply Forall_repeat.
            split; [pose proof Int.min_signed_neg; omega|].
            transitivity 3; [omega | computable].
          * rewrite Z.even_add_mul_2; auto. }
        rewrite size_def, Zminus_diag, app_nil_r, map_repeat; simpl; cancel. }
      { split; [|split].
        * admit.
        * simpl.
          admit.
        * intros _ _; simpl; rewrite !sepcon_emp.
          apply derives_view_shift; eapply derives_trans, now_later.
          Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)) (v + 2 * i + 2); cancel. }
      Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)).
      rewrite Z2Nat.inj_add, upto_app, map_app, map_upd_list_app by omega.
      change (upto 1) with [0]; simpl map_upd_list.
      rewrite Z2Nat.id, Z.add_0_r, Z.mul_add_distr_l, Z.add_assoc by omega.
      rewrite <- size_def, exp_uncurry; entailer!.
  - Intros L'; forward.
    Exists data (map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)) (upto (Z.to_nat 3))));
      rewrite size_def; simpl; entailer!.
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

Lemma node_state_forget : forall L v version locs g lg g' L' v' (HL' : map_incl L' L) (Hv : v' <= v)
  (Hv' : exists vs, Zlength vs = size /\ log_latest L' (if Z.even v' then v' else v' - 1) vs),
  view_shift (node_state Share.bot L v version locs g lg g')
             (node_state Share.bot L' v' version locs g lg g').
Proof.
  intros.
  unfold node_state.
  apply view_shift_sepcon, ghost_snap_forget; try (intros; eapply map_join_incl_compat); eauto.
  apply view_shift_sepcon.
  - view_shift_intros.
    etransitivity; [apply protocol_R_forget with (s1 := v'); auto|].
    { simpl; intros; subst.
      do 2 eexists; eauto; apply Z.max_le_compat_r; auto. }
    apply derives_view_shift; entailer!.
  - apply view_shift_sepcon_list; rewrite !Zlength_map; auto.
    intros; erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    unfold node_entry.
    view_shift_intro log; view_shift_intros.
    etransitivity; [apply protocol_R_forget with (s1 := map_Znth i L' 0)|].
    { intros; eapply map_join_incl_compat; eauto. }
    { transitivity (map_Znth i L 0); [|destruct (Z.even v); auto; subst; reflexivity].
      apply map_incl_Znth; auto. }
    apply derives_view_shift; Exists (map_Znth i L' 0); apply andp_right; auto.
    apply prop_right; if_tac; auto; reflexivity.
Qed.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  assert_PROP (exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs).
  { unfold node_state; entailer!. }
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, L, v, emp,
    fun L' '(v1, vs1) => !!(map_incl L L' /\ v <= v1 /\ Z.even v1 = true /\ Zlength vs1 = size /\
      L' v1 = Some vs1) && emp,
    fun _ : Z -> option (list Z) => emp,
    fun _ : Z => EX L :_, EX v1 : Z, node_state Ish L v1 version locs g lg g', [0]).
  { rewrite <- size_def; simpl; entailer!. }
  { split; [|split].
    * admit.
    * admit.
    * intros L' (v1, vs1); simpl.
      view_shift_intro v'.
      apply derives_view_shift; rewrite !sepcon_emp; apply andp_right; [apply prop_right; auto|].
      eapply derives_trans, now_later; Exists L' v'; entailer!. }
  Intro x; destruct x as ((v', vs'), L'); simpl; Intros v1.
  focus_SEP 2.
  assert_PROP (exists vs1, Zlength vs1 = size /\ log_latest L' (if Z.even v1 then v1 else v1 - 1) vs1) as HL'.
  { unfold node_state; entailer!. }
  match goal with H : exists vs, _ /\ log_latest L _ _ |- _ => destruct H as [? [? HL]] end.
  eapply node_state_forget with (L' := map_upd L v' vs')(v' := v').
  { apply map_upd_incl; auto. }
  { destruct HL' as [? [? [? Hv1]]].
    destruct (zlt (if Z.even v1 then v1 else v1 - 1) v').
    { rewrite (Hv1 _ l) in *; discriminate. }
    destruct (Z.even v1); auto; omega. }
  { exists vs'; split; auto.
    replace (Z.even v') with true; split; unfold map_upd.
    - rewrite eq_dec_refl; auto.
    - intros; if_tac; [omega|].
      eapply HL; if_tac; omega. }
  forward.
  Exists data v' vs'; rewrite exp_uncurry, size_def; entailer!.
  split; auto.
  replace (Z.even v) with true in HL; destruct HL as [HL].
  match goal with H : map_incl L L' |- _ => rewrite (H _ _ HL) in *; congruence end.
Admitted.
