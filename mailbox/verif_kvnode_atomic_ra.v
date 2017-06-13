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

Definition node_entry sh log locs g lg i :=
  protocol_piece sh (Znth i locs Vundef) (Znth i lg Vundef) log map_incl (data_T g).

Definition version_T locs g lg g' (s v : Z) := !!(v = s) && EX L : _,
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  fold_right sepcon emp (map (fun i => node_entry Share.bot (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))) *
  ghost_snap L g'.

(* The collection of protocol assertions that describes a stable state of the node. *)
Definition node_state (sh : share) (L : Z -> option (list Z)) v version locs g lg g' :=
  !!(Z.even v = true /\ exists vs, Zlength vs = size /\ log_latest L v vs) &&
  protocol_piece sh version g v Z.le (version_T locs g lg g') *
  fold_right sepcon emp (map (fun i => node_entry sh (map_Znth i L 0) locs g lg i) (upto (Z.to_nat size))) *
  ghost (sh, L) g'.

(* Posit a version in which protocol assertions cannot be stored in invariants under any circumstances. *)

Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * share * val * list val * val * val * list val * (Z -> option (list Z)) * Z))
  empty_map [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) => temp _n n;
   fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) => temp _out out]
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) => !!(readable_share sh /\
     writable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size) &&
   data_at sh tnode (version, locs) n * data_at_ shi (tarray tint size) out *
   node_state Share.bot L0 v0 version locs g lg g')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) L => ghost (gsh1, L) g')
  (0, []) []
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) L '(v, vals) =>
   !!(v0 <= v /\ Zlength vals = size /\ (v = v0 -> L0 v = Some vals)) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) out *
   node_state Share.bot (singleton v vals) v version locs g lg g')
  (fun _ '(n, out, sh, shi, version, locs, g, g', lg, L0, v0) L '(v, vals) => !!(L v = Some vals) &&
   ghost (gsh1, L) g')
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
  (@empty_map Z (list Z)) [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) => temp _n n;
   fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) => temp _in input]
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) => !!(readable_share sh /\
     readable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\
     Forall repable_signed vals) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state gsh2 L v0 version locs g lg g')
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) L' => ghost (gsh1, L') g')
  tt []
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) _ _ =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state gsh2 (map_upd L (v0 + 2) vals) (v0 + 2) version locs g lg g')
  (fun _ '(n, input, sh, shi, version, locs, vals, g, g', lg, L, v0) _ _ =>
   ghost (gsh1, map_upd L (v0 + 2) vals) g')
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
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state gsh2 L v version locs g lg g';
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g'))
  POST [ tptr tvoid ]
   EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + (2 * (i + 1)), repeat (i + 1) (Z.to_nat size)))%Z (upto 3)))
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state gsh2 L' (v + 6) version locs g lg g';
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g')).

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
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g'))
  POST [ tptr tvoid ]
   EX v' : Z, EX vs' : list Z,
    PROP (v <= v'; v' = v -> Z.even v = true /\ L v = Some vs')
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot (map_upd L v' vs') v' version locs g lg g';
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g')).

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

Lemma version_T_duplicable : forall locs g lg g' s v, duplicable (version_T locs g lg g' s v).
Proof.
  intros; unfold version_T.
  apply prop_duplicable, exp_duplicable; intro.
  apply sepcon_duplicable, ghost_snap_duplicable.
  apply prop_duplicable, sepcon_list_duplicable.
  rewrite Forall_map, Forall_forall; intros; simpl.
  unfold node_entry; apply protocol_R_duplicable.
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

Lemma node_entry_single : forall log locs g lg i v v', log v = Some v' ->
  view_shift (node_entry Share.bot log locs g lg i) (node_entry Share.bot (singleton v v') locs g lg i).
Proof.
  intros; unfold node_entry.
  apply protocol_R_forget with (s1 := singleton v v'); try apply map_join_incl_compat.
  unfold singleton, map_Znth; intros ??; if_tac; [|discriminate].
  intro X; inv X; auto.
Qed.

Lemma node_entry_snap : forall sh log locs g lg i,
  view_shift (node_entry sh log locs g lg i)
    (node_entry sh log locs g lg i * node_entry Share.bot log locs g lg i).
Proof.
  intros; unfold node_entry.
  apply make_protocol_R.
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

Lemma node_entry_absorb : forall sh L1 L2 locs g lg i,
  view_shift (node_entry sh L1 locs g lg i * node_entry Share.bot L2 locs g lg i)
    (node_entry sh L1 locs g lg i).
Proof.
  intros.
  destruct (eq_dec sh Share.bot).
  - subst; apply protocol_R_choose, map_join_incl_compat.
  - unfold node_entry.
    etransitivity; [apply protocol_R_absorb; auto|].
    view_shift_intros; reflexivity.
Qed.

Corollary node_entry_choose : forall log1 log2 locs g lg i,
  view_shift (node_entry Share.bot log1 locs g lg i * node_entry Share.bot log2 locs g lg i)
    (node_entry Share.bot log1 locs g lg i).
Proof.
  intros; apply node_entry_absorb.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((((n, out), sh), shi), version), locs), g), g'), lg), L0), v0); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  assert (0 <= size) by (rewrite size_def; computable).
  unfold node_state; Intros.
  match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? [HL0 ?]]] end.
  apply semax_pre with (P' := PROP () LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ shi (tarray tint size) out;
         EX v : Z, !!(v0 <= v) && protocol_R version g v Z.le (version_T locs g lg g');
         EX ll : _, fold_right sepcon emp (map (fun i => node_entry Share.bot (Znth i ll empty_map) locs g lg i)
           (upto (Z.to_nat size))); EX L' : _, ghost_snap (map_add L0 L') g';
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { unfold node_state; Intros.
    Exists v0 (map (fun i => map_Znth i L0 0) (upto (Z.to_nat size))) (@empty_map Z (list Z));
      rewrite map_add_empty; entailer!.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  Intros v ll L'.
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
    Exists v1 (map (fun i => map_Znth i L1 0) (upto (Z.to_nat size))) (map_add L' L1);
      rewrite map_add_assoc; entailer!.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
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
           fold_right sepcon emp (map (fun i => node_entry Share.bot (singleton (Znth i vers' 0) (Znth i vals 0)) locs g lg i)
             (sublist 0 i (upto (Z.to_nat size))));
         fold_right sepcon emp (map (fun i => node_entry Share.bot (map_Znth i L1 0)
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
    eapply node_entry_single.
    { match goal with H : log_latest _ _ _ |- _ => destruct H; eauto end. }
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
      assert (forall j, 0 <= j < size -> Znth j vers' 0 = v1) as Hvers.
      { intros; match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i := j)(d := 0) in H;
          [destruct H as [Heven] | omega] end.
        destruct (list_max_spec (map (fun x => x - 1) vers') v1) as [_ Hmax].
        rewrite Forall_map in Hmax.
        apply Forall_Znth with (i := j)(d := 0) in Hmax; [simpl in Hmax | omega].
        destruct (eq_dec (Znth j vers' 0) v1); subst; auto.
        assert (Znth j vers' 0 = v1 + 1) as Heq by omega.
        rewrite Heq, Z.even_add in Heven; replace (Z.even v1) with true in Heven; discriminate. }
      assert (L1 v1 = Some vals') as HL1.
      { eapply map_Znth_eq.
        * intros ? HL1.
          match goal with H : exists vs, _ |- _ => destruct H as [? [? [Heq]]]; rewrite Heq in HL1; inv HL1; omega end.
        * intro; subst; rewrite size_def in *; discriminate.
        * intros j Hj; replace (Zlength vals') with size in Hj; auto. }
      gather_SEP 0 5 7 9 8; rewrite <- !sepcon_assoc; apply invariants_view_shift with
        (Q0 := node_state Share.bot (singleton v1 vals') v1 version locs g lg g' * EX L : _, Q L (v1, vals')).
      { rewrite !map_map, !sepcon_assoc, (sepcon_comm P), <- 2sepcon_assoc.
        etransitivity; [apply view_shift_sepcon2, HP|].
        view_shift_intro L2.
        etransitivity; [|apply derives_view_shift; Exists L2; apply derives_refl].
        rewrite !sepcon_assoc, (sepcon_comm (Q _ _)).
        etransitivity; [|apply view_shift_sepcon2, HQ]; simpl.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ g')).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ g')).
        rewrite <- !sepcon_assoc, snap_master_join by auto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, make_snap|].
        assert (L2 v1 = Some vals').
        { match goal with H : map_incl _ _ |- _ => apply H end.
          rewrite map_add_comm by auto.
          unfold map_add; rewrite HL1; auto. }
        assert (map_incl (singleton v1 vals') L2).
        { unfold singleton; intros ??.
          if_tac; [intro X; inv X; auto | discriminate]. }
        rewrite !sepcon_assoc; etransitivity;
          [apply view_shift_sepcon1, ghost_snap_forget with (v2 := singleton v1 vals'); auto|].
        { intros; eapply map_join_incl_compat; eauto. }
        apply derives_view_shift; unfold node_state, protocol_R, ghost_snap, share; entailer!.
        { exists vals'; split; auto.
          apply log_latest_singleton. }
        erewrite map_ext_in; eauto; intros; simpl.
        rewrite map_Znth_single, Hvers; auto.
        rewrite In_upto, Z2Nat.id in *; auto. }
      Intros L2.
      forward.
      rewrite map_map; Exists (v1, vals') L2; entailer!.
      rewrite HL0; match goal with H : compatible _ _ |- _ => eapply f_equal, H; eauto end.
      unfold map_add; rewrite HL0; auto.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; go_lower; Exists v2 (map (fun i => singleton (Znth i vers' 0) (Znth i vals' 0))
        (upto (Z.to_nat size))) (map_add L' L1); rewrite map_add_assoc; entailer!.
      { destruct (list_max_spec (map (fun x => x - 1) vers') v1); omega. }
      erewrite map_ext_in; eauto; intros; simpl.
      rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega.
Qed.

(* Is there any use to allowing RA atomics to interact with invariants if they can't take or leave protocol
   assertions? Possibly. *)
Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((((n, input), sh), shi), version), locs), vals), g), g'), lg), L), v0); Intros.
  destruct H as (HP0 & HP & HQ).
  forward.
  rewrite map_map in HP, HQ.
  unfold node_state; Intros.
  focus_SEP 2; apply make_protocol_R.
  forward_call_dep [Z : Type] (version, g, v0, Z.le, version_T locs g lg g',
    protocol_piece gsh2 version g v0 Z.le (version_T locs g lg g'), fun s v : Z => !!(v = s) && emp).
  { split; [|auto with dup].
    intros.
    apply derives_view_shift; unfold version_T; entailer!. }
  Intros x; destruct x as (?, v); simpl in *; subst.
  gather_SEP 1 0; apply protocol_R_absorb; auto; Intros.
  assert (v = v0) by omega; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call_dep [Z : Type] (version, v0 + 1, g, v0, v0 + 1, Z.le, version_T locs g lg g',
    P * protocol_piece gsh2 version g v0 Z.le (version_T locs g lg g'), II, lI,
    EX L : _, ghost (gsh1, L) g' * R L,
    P * protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g')).
  { split; [auto | split; [|split; [|omega]]].
    - rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
      rewrite sepcon_comm; reflexivity.
    - intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _ _)), <- !sepcon_assoc, (sepcon_assoc _ _ P).
      etransitivity; [|apply view_shift_sepcon2, HP].
      unfold version_T at 1 4.
      view_shift_intro L0; view_shift_intro L1; view_shift_intros.
      apply derives_view_shift.
      Exists L0 L1; entailer!.
      rewrite Z.even_add, Z.add_simpl_r; replace (Z.even v0) with true in *; auto. }
  assert (0 <= size) by (rewrite size_def; computable).
  assert_PROP (Zlength (map (fun x => vint x) vals) = size) by entailer!.
  assert (Z.even (v0 + 2) = true) by (rewrite Z.even_add; replace (Z.even v0) with true; auto).
  rewrite <- seq_assoc.
  focus_SEP 4.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
  forward_for_simple_bound 8 (EX i : Z, PROP () (LOCALx Q
    (SEPx (fold_right sepcon emp (map (fun i => node_entry gsh2 (map_Znth i (map_upd L (v0 + 2) vals) 0)
             locs g lg i) (sublist 0 i (upto (Z.to_nat size)))) ::
           fold_right sepcon emp (map (fun i => node_entry gsh2 (map_Znth i L 0)
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
    match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? ?]] end.
    destruct (log_latest_upd (map_Znth i L 0) v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
    { apply map_Znth_log_latest; auto. }
    unfold node_entry at 2.
    forward_call_dep [Z -> option Z : Type] (Znth i locs Vundef, Znth i vals 0, Znth i lg Vundef,
      map_Znth i L 0, map_upd (map_Znth i L 0) (v0 + 2) (Znth i vals 0), @map_incl Z Z, data_T g,
      P * protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g') *
        protocol_piece gsh2 (Znth i locs Vundef) (Znth i lg Vundef) (map_Znth i L 0) map_incl (data_T g) *
        ghost (gsh2, L) g', II, lI,
      !!(exists vs, Zlength vs = size /\ log_latest L v0 vs) &&
        protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g') *
        ghost (gsh1, L) g' * ghost (gsh2, L) g' * R L,
      P * protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g') *
        protocol_piece gsh2 (Znth i locs Vundef) (Znth i lg Vundef) (map_Znth i (map_upd L (v0 + 2) vals) 0)
          map_incl (data_T g) * ghost (gsh2, L) g').
    { fast_cancel. }
    { split; [apply Forall_Znth; auto; omega|].
      assert (0 <= i < Zlength (upto (Z.to_nat size))) by (rewrite Zlength_upto, Z2Nat.id; auto; omega).
      split; [|split; auto].
      + rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        unfold node_state.
        view_shift_intro L1; view_shift_intro v; view_shift_intros.
        apply view_shift_assert with (PP := L1 = L); [|intro; subst].
        { rewrite (sepcon_comm _ (ghost _ _)), <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
          rewrite <- !sepcon_assoc; do 3 apply sepcon_derives_prop.
          rewrite sepcon_comm; setoid_rewrite ghost_var_share_join'; eauto; entailer!. }
        apply derives_view_shift; entailer!.
        eauto.
      + intros.
        rewrite !sepcon_assoc, (sepcon_comm (data_T _ _ (Znth i vals 0))).
        rewrite <- 5sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, view_shift_sepcon1, HP].
        unfold data_T at 1 4.
        view_shift_intro ver; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ version _ _ _ _)).
        rewrite <- sepcon_assoc.
        rewrite 3sepcon_assoc; etransitivity; [apply view_shift_sepcon1 with (P' :=
          !!(ver - 1 <= v0 + 1) && protocol_piece gsh2 version g (v0 + 1) Z.le (version_T locs g lg g') *
          ghost_snap (v0 + 1) g)|].
        { unfold protocol_piece.
          rewrite sepcon_assoc, (sepcon_comm (ghost _ _)), snap_master_join by auto.
          view_shift_intros; etransitivity; [apply view_shift_sepcon2, make_snap|].
          apply derives_view_shift; entailer!. }
        view_shift_intros.
        apply derives_view_shift.
        Exists L (v0 + 2).
        rewrite map_Znth_upd, <- Z.add_sub_assoc; simpl.
        entailer!. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl fold_right.
    rewrite <- size_def; unfold node_entry; entailer!.
  - rewrite <- size_def, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    assert (repable_signed (v0 + 2)) by admit.
    match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? ?]] end.
    destruct (log_latest_upd L v0 vs0 (v0 + 2) vals); auto; try omega.
    forward_call_dep [Z : Type] (version, v0 + 2, g, v0 + 1, v0 + 2, Z.le, version_T locs g lg g',
      P * protocol_W version g (v0 + 1) Z.le (version_T locs g lg g') *
        fold_right sepcon emp (map (fun i => node_entry gsh2 (map_Znth i (map_upd L (v0 + 2) vals) 0)
          locs g lg i) (upto (Z.to_nat size))) * ghost (gsh2, L) g', II, lI,
      !!(exists vs, Zlength vs = size /\ log_latest L v0 vs) &&
        fold_right sepcon emp (map (fun i => node_entry gsh2 (map_Znth i (map_upd L (v0 + 2) vals) 0)
          locs g lg i) (upto (Z.to_nat size))) * ghost (Tsh, L) g' * R L,
      Q L tt * protocol_W version g (v0 + 2) Z.le (version_T locs g lg g') *
        fold_right sepcon emp (map (fun i => node_entry gsh2 (map_Znth i (map_upd L (v0 + 2) vals) 0)
          locs g lg i) (upto (Z.to_nat size))) * ghost (gsh2, map_upd L (v0 + 2) vals) g').
    { fast_cancel. }
    { split; [auto | split; [| split; [|omega]]].
      + rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        view_shift_intro L1; view_shift_intro v; unfold node_state.
        view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)), <- !sepcon_assoc.
        rewrite (sepcon_comm (ghost _ _)); setoid_rewrite ghost_var_share_join'; eauto.
        apply derives_view_shift; entailer!.
        eauto.
      + intros.
        rewrite !sepcon_assoc, (sepcon_comm (version_T _ _ _ _ (v0 + 2) _)).
        rewrite <- !sepcon_assoc, 6sepcon_assoc.
        etransitivity; [|apply view_shift_sepcon1, HQ].
        unfold version_T at 1 4.
        view_shift_intro L'; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
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
        apply derives_view_shift; Exists (map_upd L (v0 + 2) vals).
        rewrite Zlength_map in *; rewrite sepcon_map.
        rewrite Z.even_add; replace (Z.even v0) with true; simpl.
        unfold ghost_var; entailer!; eauto. }
    forward.
    Exists tt L; unfold node_state.
    rewrite Zlength_map in *; unfold protocol_W; entailer!; eauto.
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
           node_entry gsh2 (singleton 0 0) ld g lg i *
           node_entry Share.bot (singleton 0 0) ld g lg i) (upto (Z.to_nat i)));
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
    replace_SEP 0 (node_entry gsh2 (singleton 0 0) (x ++ [d]) g (lg ++ [gi]) i).
    { go_lower; unfold node_entry.
      rewrite !app_Znth2 by omega.
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
         node_state gsh2 L' (v + 2 * i) version locs g lg g';
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g'))).
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
        fun _ : Z => EX L : Z -> option (list Z), ghost (gsh1, L) g', [0]).
      { entailer!.
        { apply Forall_repeat.
          split; [pose proof Int.min_signed_neg; omega|].
          transitivity 3; [omega | computable]. }
        rewrite size_def, Zminus_diag, app_nil_r, map_repeat; simpl; cancel. }
      { split; [|split].
        * admit.
        * simpl.
          admit.
        * intros _ _; simpl; rewrite !sepcon_emp.
          apply derives_view_shift; eapply derives_trans, now_later.
          Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)); cancel. }
      Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)).
      rewrite Z2Nat.inj_add, upto_app, map_app, map_upd_list_app by omega.
      change (upto 1) with [0]; simpl map_upd_list.
      rewrite Z2Nat.id, Z.add_0_r, Z.mul_add_distr_l, Z.add_assoc by omega.
      rewrite <- size_def; entailer!.
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
  (Hv' : exists vs, Zlength vs = size /\ log_latest L' v' vs) (Heven : Z.even v' = true),
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
    apply protocol_R_forget.
    { intros; eapply map_join_incl_compat; eauto. }
    { transitivity (map_Znth i L 0); [|destruct (Z.even v); auto; subst; reflexivity].
      apply map_incl_Znth; auto. }
Qed.

(* up *)
Lemma map_add_single : forall {A B} {A_eq : EqDec A} (m : A -> option B) k v, map_add (singleton k v) m = map_upd m k v.
Proof.
  intros; extensionality; unfold map_add, singleton, map_upd; if_tac; auto.
Qed.

Lemma node_entry_join : forall log1 log2 locs g lg i,
  node_entry Share.bot log1 locs g lg i * node_entry Share.bot log2 locs g lg i |--
  node_entry Share.bot (map_add log1 log2) locs g lg i.
Proof.
  intros; unfold node_entry.
  eapply derives_trans; [apply protocol_R_join'|].
  Intros log'.
  match goal with H : join _ _ _ |- _ => rewrite map_join_spec in H; destruct H as [Hcompat]; subst; auto end.
Qed.

Lemma node_state_upd : forall L v v' vs' version locs g lg g' (Hv' : v <= v') (Hvs' : Zlength vs' = size)
  (Hcompat : v' = v -> L v' = Some vs'),
  node_state Share.bot (singleton v' vs') v' version locs g lg g' *
  node_state Share.bot L v version locs g lg g' |--
  node_state Share.bot (map_upd L v' vs') v' version locs g lg g'.
Proof.
  intros; unfold node_state; Intros.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _ _)).
  rewrite <- !sepcon_assoc, 3sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply protocol_R_join'|].
  Intros v''.
  simpl in *; subst.
  rewrite Z.max_r by auto.
  do 2 (rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _))).
  rewrite <- !sepcon_assoc; setoid_rewrite ghost_snap_join'.
  Intros L'.
  match goal with H : join _ _ _ |- _ => rewrite map_join_spec in H; destruct H as [Hcompat']; subst end.
  rewrite map_add_single.
  rewrite sepcon_assoc, <- sepcon_map.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_list_derives]|].
  { rewrite 2Zlength_map; reflexivity. }
  { rewrite Zlength_map; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    eapply derives_trans; [apply node_entry_join|].
    rewrite <- map_Znth_add, map_add_single; apply derives_refl. }
  unfold ghost_snap, protocol_R; entailer!.
  destruct (eq_dec v' v).
  - subst; rewrite map_upd_triv; auto.
  - match goal with H : exists vs, _ |- _ => destruct H as [? [? HL]] end.
    eapply log_latest_upd with (v1' := v') in HL; [|omega].
    destruct HL; eauto.
Qed.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  assert_PROP (Z.even v = true /\ exists vs, Zlength vs = size /\ log_latest L v vs) as Hv.
  { unfold node_state; entailer!. }
  destruct Hv as [Heven [? [? [HL ?]]]].
  focus_SEP 2; apply node_state_snap.
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, L, v, emp,
    fun (L' : Z -> option (list Z)) (_ : Z * list Z) => emp,
    fun _ : Z -> option (list Z) => emp,
    fun _ : Z => EX L : Z -> option (list Z), ghost (gsh1, L) g', [0]).
  { rewrite <- size_def; simpl; entailer!. }
  { split; [|split].
    * admit.
    * admit.
    * intros L' (v1, vs1); simpl.
      view_shift_intro v'.
      rewrite !sepcon_emp; apply derives_view_shift.
      eapply derives_trans, now_later; Exists L'; entailer!. }
  Intro X; destruct X as ((v', vs'), L'); simpl; Intros.
  forward.
  Exists data v' vs'; rewrite size_def; entailer!.
  apply node_state_upd; auto.
Qed.
