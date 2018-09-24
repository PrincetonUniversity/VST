Require Import VST.veric.rmaps.
Require Import VST.progs.ghosts.
From atomics Require Import general_atomics acq_rel_atomics acq_rel_SW.
Require Import VST.progs.conclib.
Require Import atomics.maps.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.kvnode_atomic_ra.

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

(* In this example, all the resources held in the protocols are snapshots, so the full and read interpretations
   are equal. *)

(* This is a bit messy to allow the mutually recursive protocol interpretations. *)
Definition data_T' version version_T s (v : Z) := EX ver : Z, !!(Z.even ver = true /\ log_latest s ver v) &&
  protocol_R version (ver - 1) Z.le (version_T, version_T).

Definition version_T_fun version locs g : (Z * Z -> mpred) -> (Z * Z -> mpred) :=
  fun R '(s, v) => !!(v = s) && EX L : _,
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  (if eq_dec v 0 then emp
   else fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
     (data_T' version (fun s v => |>R (s, v)), data_T' version (fun s v => |>R (s, v)))) (upto (Z.to_nat size)))) *
  ghost_snap L g.

Definition version_T' version locs g := HORec (version_T_fun version locs g).
Definition version_T version locs g s v := version_T' version locs g (s, v).

Definition data_T version locs g := data_T' version (|>version_T version locs g).

Lemma version_T'_eq version locs g : version_T' version locs g =
  version_T_fun version locs g (version_T' version locs g).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 (s, v).
  unfold version_T_fun.
  apply subp_andp; [apply subp_refl|].
  apply subp_exp; intro L.
  apply subp_sepcon; [|apply subp_refl].
  apply subp_andp; [apply subp_refl|].
  if_tac; [apply subp_refl|].
  pose proof (fold_right_sepcon_nonexpansive
    (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
      (data_T' version (fun s v => |>P1 (s, v)), data_T' version (fun s v => |>P1 (s, v)))) (upto (Z.to_nat size)))
    (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
      (data_T' version (fun s v => |>P2 (s, v)), data_T' version (fun s v => |>P2 (s, v)))) (upto (Z.to_nat size)))) as Hnon.
  rewrite fash_andp in Hnon.
  eapply derives_trans; [eapply derives_trans, Hnon; [|rewrite !Zlength_map; auto] | apply andp_left1; auto].
  apply allp_right; intro i.
  destruct (zlt i 0); [rewrite !Znth_underflow by auto; apply eqp_refl|].
  destruct (zlt i (Zlength (upto (Z.to_nat size))));
    [|rewrite !Znth_overflow by (rewrite Zlength_map; auto); apply eqp_refl].
  erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
  eapply derives_trans, protocol_piece_nonexpansive.
  apply allp_right; intro s1.
  apply allp_right; intro v1.
  unfold data_T'.
  eapply derives_trans, andp_right, derives_refl; auto.
  apply eqp_exp; intro ver.
  apply eqp_andp; [apply eqp_refl|].
  eapply derives_trans, protocol_piece_nonexpansive.
  apply allp_right; intro s2.
  apply allp_right; intro v2.
  apply allp_left with (s2, v2), andp_right; apply derives_refl.
Qed.

Lemma version_T_eq version locs g s v : version_T version locs g s v = !!(v = s) && EX L : _,
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  (if eq_dec v 0 then emp
   else fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
     (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size)))) * ghost_snap L g.
Proof.
  intros; unfold version_T.
  etransitivity; [rewrite version_T'_eq; reflexivity | auto].
Qed.

Lemma data_T_eq version locs g s v : data_T version locs g s v =
  EX ver : Z, !!(Z.even ver = true /\ log_latest s ver v) &&
    protocol_R version (ver - 1) Z.le (|>version_T version locs g, |>version_T version locs g).
Proof. auto. Qed.

Lemma data_T_duplicable : forall version locs g s v, duplicable (data_T version locs g s v).
Proof.
  intros; rewrite data_T_eq.
  apply exp_duplicable; intro.
  apply prop_duplicable, protocol_R_duplicable.
Qed.

Instance data_prot version locs g : protocol (data_T version locs g) (data_T version locs g).
Proof.
  apply dup_protocol, data_T_duplicable.
Qed.

Lemma version_T_duplicable : forall version locs g s v, duplicable (version_T version locs g s v).
Proof.
  intros; rewrite version_T_eq.
  apply prop_duplicable, exp_duplicable; intro.
  apply sepcon_duplicable, ghost_snap_duplicable.
  apply prop_duplicable.
  if_tac; auto with dup.
  apply sepcon_list_duplicable.
  rewrite Forall_map, Forall_forall; intros.
  apply protocol_R_duplicable.
Qed.

Instance version_prot version locs g : protocol (version_T version locs g) (version_T version locs g).
Proof.
  apply dup_protocol, version_T_duplicable.
Qed.

(* The collection of protocol assertions that describes a stable state of the node. *)
Definition node_state (sh : share) (L : Z -> option (list Z)) v version locs g :=
  !!(Z.even v = true /\ 0 <= v /\ exists vs, Zlength vs = size /\ log_latest L v vs) &&
  protocol_piece sh version v Z.le (version_T version locs g, version_T version locs g) *
  fold_right sepcon emp (map (fun i => protocol_piece sh (Znth i locs Vundef) (map_Znth i L 0) map_incl
    (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (sh, L) g.

Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * share * val * list val * val * (Z -> option (list Z)) * Z))
  empty_map [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, shi, version, locs, g, L0, v0) => temp _n n;
   fun _ '(n, out, sh, shi, version, locs, g, L0, v0) => temp _out out]
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) => !!(readable_share sh /\
     writable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size) &&
   data_at sh tnode (version, locs) n * data_at_ shi (tarray tint size) out *
   node_state Share.bot L0 v0 version locs g)
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) L => ghost (gsh1, L) g)
  (0, []) []
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) L '(v, vals) =>
   !!(v0 <= v /\ Zlength vals = size) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) out *
   node_state Share.bot (map_upd L0 v vals) v version locs g)
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) L '(v, vals) => !!(map_incl L0 L /\ L v = Some vals) &&
   ghost (gsh1, L) g)
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

(* Because the "actual state" of the structure is divided between the writer and the invariant, a writer can
   make arbitrary updates to the ghost state and the data (without calling write). However, the protocols and the
   PCM constrain the nature of those updates to the sort of changes we'd expect anyway. *)
Program Definition write_spec := DECLARE _write atomic_spec
  (ConstType (val * val * share * share * val * list val * list Z * val * (Z -> option (list Z)) * Z))
  (@empty_map Z (list Z)) [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) => temp _n n;
   fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) => temp _in input]
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) => !!(readable_share sh /\
     readable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\
     Forall repable_signed vals /\ repable_signed (v0 + 2)) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state gsh2 L v0 version locs g)
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) L' => ghost (gsh1, L') g)
  tt []
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) _ _ =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state gsh2 (map_upd L (v0 + 2) vals) (v0 + 2) version locs g)
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) _ _ => ghost (gsh1, map_upd L (v0 + 2) vals) g)
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
   EX n : val, EX version : val, EX locs : list val, EX g : val,
    PROP (isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp ret_temp n)
    SEP (data_at Tsh tnode (version, locs) n; malloc_token Tsh (sizeof tnode) n;
         malloc_token Tsh (sizeof tint) version; fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) locs);
         node_state gsh2 (singleton 0 (repeat 0 (Z.to_nat size))) 0 version locs g;
         ghost (gsh1, singleton 0 (repeat 0 (Z.to_nat size))) g).

Definition writer_spec := DECLARE _writer
  WITH n : val, sh : share, v : Z, L : Z -> option (list Z), version : val, locs : list val, g : val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size; repable_signed (v + 6))
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state gsh2 L v version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g))
  POST [ tptr tvoid ]
   EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + (2 * (i + 1)), repeat (i + 1) (Z.to_nat size)))%Z (upto 3)))
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state gsh2 L' (v + 6) version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g)).

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
  WITH n : val, sh : share, v : Z, L : Z -> option (list Z), version : val, locs : list val, g : val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot L v version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g))
  POST [ tptr tvoid ]
   EX v' : Z, EX vs' : list Z,
    PROP (v <= v'; v' = v -> Z.even v = true /\ L v = Some vs')
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot (map_upd L v' vs') v' version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g)).

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

Lemma node_state_snap : forall sh L v version locs g,
  view_shift (node_state sh L v version locs g)
             (node_state sh L v version locs g * node_state Share.bot L v version locs g).
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
    apply make_protocol_R.
  - rewrite sepcon_map.
    apply derives_view_shift; entailer!.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((n, out), sh), shi), version), locs), g), L0), v0); Intros.
  destruct H as (HP & HQ).
  assert (0 <= size) by (rewrite size_def; computable).
  unfold node_state; Intros.
  match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? [HL0 ?]]] end.
  apply semax_pre with (P' := PROP () LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ shi (tarray tint size) out;
         EX v : Z, !!(v0 <= v) && protocol_R version v Z.le (version_T version locs g, version_T version locs g);
         EX ll : _, !!(forall i, 0 <= i < size -> map_incl (map_Znth i L0 0) (Znth i ll empty_map)) && fold_right sepcon emp (map (fun i =>
           protocol_R (Znth i locs Vundef) (Znth i ll empty_map) map_incl (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size)));
         EX L' : _, ghost_snap (map_add L0 L') g;
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { unfold node_state; Intros.
    Exists v0 (map (fun i => map_Znth i L0 0) (upto (Z.to_nat size))) (@empty_map Z (list Z));
      rewrite map_add_empty; entailer!.
    { intros.
      erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega); reflexivity. }
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply ENTAIL_refl].
  Intros v ll L'.
  repeat forward.
  forward_call_dep [Z : Type] (load_acq_witness version v Z.le
    (version_T version locs g, version_T version locs g) emp (version_T version locs g)).
  { simpl; cancel. }
  { simpl; split; intros; rewrite ?emp_sepcon, ?sepcon_emp; try reflexivity.
    rewrite sepcon_comm; reflexivity. }
  Intro x; rewrite version_T_eq; Intros L1; destruct x as (v1', v1); simpl fst in *; simpl snd in *; subst.
  gather_SEP 7 3; rewrite map_snap_join; Intros.
  match goal with H : exists vs, _ |- _ => destruct H as (vs1 & ? & HL1) end.
  assert (forall i, compatible (map_Znth i L0 0) (singleton (if Z.even v1 then v1 else v1 - 1) (Znth i vs1 0)))
    as Hcompat.
  { intros ????; unfold map_Znth.
    destruct (L0 k) eqn: Hk0; [|discriminate].
    unfold singleton; if_tac; [|discriminate].
    destruct HL1 as [Hk1].
    match goal with H : compatible _ _ |- _ => specialize (H k); unfold map_add in H; subst; rewrite Hk0, Hk1 in H;
      specialize (H _ _ eq_refl eq_refl); inv H end.
    intros X Y; inv X; inv Y; auto. }
  gather_SEP 3 6; eapply view_shift_trans; [|reflexivity|].
  { instantiate (1 := fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
      (map_upd (map_Znth i L0 0) (if Z.even v1 then v1 else v1 - 1) (Znth i vs1 0)) map_incl _)
      (upto (Z.to_nat size)))).
    if_tac.
    - assert (v0 = 0) by omega.
      rewrite emp_sepcon; subst; simpl in *.
      apply view_shift_sepcon_list; rewrite ?Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
      rewrite map_upd_triv.
      apply protocol_R_forget.
      rewrite Zlength_upto, Z2Nat.id in *; auto.
      { specialize (Hcompat i 0); unfold map_Znth, singleton in Hcompat.
        rewrite HL0, eq_dec_refl in Hcompat; specialize (Hcompat _ _ eq_refl eq_refl).
        unfold map_Znth; rewrite HL0; simpl; auto. }
    - rewrite <- sepcon_map; apply view_shift_sepcon_list; rewrite ?Zlength_map; auto; intros ? Hi.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
      assert (map_incl (singleton (if Z.even v1 then v1 else v1 - 1) vs1) L1) as Hv1.
      { intros ??; unfold singleton; if_tac; [subst | discriminate].
        destruct HL1; intro X; inv X; auto. }
      eapply map_incl_Znth in Hv1.
      rewrite sepcon_comm.
      erewrite <- protocol_R_join with (s := map_upd _ _ _)(s1 := map_Znth i L0 0).
      apply view_shift_sepcon; apply protocol_R_forget; eauto.
      rewrite Zlength_upto, Z2Nat.id in *; auto.
      { rewrite map_join_spec.
        rewrite map_Znth_single; split; auto.
        rewrite map_add_comm, map_add_single; auto. } }
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP (Z.even v1 = true) (LOCALx Q (SEPx R))) end.
  { eapply semax_pre; [|apply semax_continue].
    unfold POSTCONDITION, abbreviate, overridePost.
    destruct (eq_dec EK_continue EK_normal); [discriminate|].
    unfold loop1_ret_assert.
    go_lower.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1) eqn: Hodd; try contradiction.
    Exists v1 (map (fun i => map_upd (map_Znth i L0 0) (v1 - 1) (Znth i vs1 0)) (upto (Z.to_nat size)))
      (map_add L' L1); rewrite map_add_assoc; entailer!.
    { intros.
      erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
      rewrite <- map_add_single, <- map_add_comm by auto; apply map_incl_add. }
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
           forall j, 0 <= j < i -> Znth j vers' 0 = v1 -> Znth j vals 0 = Znth j vs1 0) &&
           protocol_R version (list_max v1 (map (fun x => x - 1) vers')) Z.le (version_T version locs g, version_T version locs g) *
           fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
             (map_upd (map_Znth i L0 0) (Znth i vers' 0) (Znth i vals 0)) map_incl
             (data_T version locs g, data_T version locs g)) (sublist 0 i (upto (Z.to_nat size))));
         fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
           (map_upd (map_Znth i L0 0) v1 (Znth i vs1 0)) map_incl
           (data_T version locs g, data_T version locs g)) (sublist i size (upto (Z.to_nat size))));
         ghost_snap (map_add (map_add L0 L') L1) g;
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
      rewrite size_def in *; auto. }
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    forward_call_dep [Z -> option Z : Type] (load_acq_witness (Znth i locs Vundef)
      (map_upd (map_Znth i L0 0) v1 (Znth i vs1 0)) map_incl (data_T version locs g, data_T version locs g)
      (protocol_R version (list_max v1 (map (fun x0 : Z => x0 - 1) vers')) Z.le
        (version_T version locs g, version_T version locs g))
      (fun s (v : Z) => EX v' : Z, !!(Z.even v' = true /\ log_latest s v' v) &&
        |>protocol_R version (list_max v1 (map (fun x => x - 1) (vers' ++ [v']))) Z.le (version_T version locs g, version_T version locs g))).
    { simpl; cancel. }
    { split; simpl; intros; rewrite !emp_sepcon; [reflexivity|].
      rewrite data_T_eq.
      view_shift_intro ver; view_shift_intros.
      rewrite sepcon_comm, <- sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, view_shift_sepcon;
        apply derives_view_shift; [apply now_later | apply protocol_later]|].
      rewrite <- later_sepcon; setoid_rewrite protocol_R_join; [|rewrite join_max; eauto].
      apply derives_view_shift; Exists ver; entailer!.
      rewrite map_app, list_max_app; simpl.
      rewrite Z.max_comm, list_max_max; auto. }
    Intros y v'; destruct y as (d, log'); simpl fst in *; simpl snd in *.
    focus_SEP 1; apply protocol_R_forget with (s1 := map_upd (map_Znth i L0 0) v' d).
    { match goal with H : log_latest _ _ _ |- _ => destruct H end.
      apply map_upd_incl; auto.
      etransitivity; [|eauto].
      rewrite <- map_add_single, <- map_add_comm by auto; apply map_incl_add. }
    forward.
    go_lower; Exists (x ++ [d]) (vers' ++ [v']); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    rewrite <- size_def, upd_init, !map_app, <- app_assoc by (rewrite ?Zlength_map; omega).
    entailer!.
    { split.
      + rewrite Forall_app; repeat constructor; auto.
        eapply log_incl_latest; eauto.
        unfold map_upd; rewrite eq_dec_refl; eauto.
      + intros ?? Hv.
        destruct (eq_dec j (Zlength x)).
        * subst j; rewrite app_Znth2 in Hv |- * by omega.
          replace (Zlength vers') with (Zlength x) in Hv; rewrite Zminus_diag, Znth_0_cons in Hv |- *; subst.
          match goal with H : map_incl _ log' |- _ => specialize (H v1); unfold map_upd in H; rewrite eq_dec_refl in H;
            specialize (H _ eq_refl) end.
          match goal with H : log_latest log' _ _ |- _ => destruct H as [Hv']; rewrite Hv' in *; congruence end.
        * rewrite app_Znth1 in Hv |- * by omega; match goal with H : forall j, _ |- _ => apply H; auto; omega end. }
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
  - Intros vals' vers'; rewrite <- size_def in *.
    rewrite Zminus_diag, app_nil_r, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    forward_call_dep [Z : Type] (version, list_max v1 (map (fun x => x - 1) vers'), Z.le,
      (version_T version locs g, version_T version locs g), P *
        protocol_R version (list_max v1 (map (fun x : Z => x - 1) vers')) Z.le (version_T version locs g, version_T version locs g) *
        fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
          (map_upd (map_Znth i L0 0) (Znth i vers' 0) (Znth i vals' 0)) map_incl (data_T version locs g, data_T version locs g))
          (upto (Z.to_nat size))) * ghost_snap (map_add (map_add L0 L') L1) g, II, lI,
      fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
          (map_upd (map_Znth i L0 0) (Znth i vers' 0) (Znth i vals' 0)) map_incl (data_T version locs g, data_T version locs g))
          (upto (Z.to_nat size))) * ghost_snap (map_add (map_add L0 L') L1) g * EX L : _, ghost (gsh1, L) g * R L,
      fun s v => !!(v = s) && protocol_R version v Z.le (version_T version locs g, version_T version locs g) *
        fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
          (map_upd (map_Znth i L0 0) (Znth i vers' 0) (Znth i vals' 0)) map_incl (data_T version locs g, data_T version locs g))
          (upto (Z.to_nat size))) * (if eq_dec v v1 then EX L : _, Q L (v1, vals') * (!!(L v = Some vals' /\
           forall j, 0 <= j < size -> Znth j vers' 0 = v1) && ghost_snap (map_upd L0 v vals') g)
         else P * ghost_snap (map_add (map_add L0 L') L1) g)).
    { split; intros.
      + rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        apply derives_view_shift; cancel.
      + simpl; rewrite version_T_eq.
        view_shift_intro L; view_shift_intro L2; view_shift_intros; subst.
        rewrite prop_true_andp by auto.
        rewrite (sepcon_comm _ (protocol_R _ _ _ _)), (sepcon_comm (fold_right _ _ (map II lI))), !sepcon_assoc.
        apply view_shift_sepcon2.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
        rewrite <- !sepcon_assoc, 3sepcon_assoc; etransitivity; [apply view_shift_sepcon1|].
        { if_tac; [rewrite sepcon_emp; reflexivity|].
          rewrite <- sepcon_map; apply view_shift_sepcon_list.
          { rewrite 2Zlength_map; auto. }
          rewrite Zlength_map; intros.
          erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
          apply protocol_R_choose. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap L2 _)).
        rewrite <- sepcon_assoc, snap_master_join by auto; view_shift_intros.
        if_tac.
        * subst.
          rewrite (sepcon_comm _ (exp _)), (sepcon_comm _ (fold_right _ _ (map II lI))).
          etransitivity; [|etransitivity; [apply view_shift_sepcon1, HQ |
            apply derives_view_shift; Exists L; rewrite 2sepcon_assoc; eauto]]; simpl.
          assert (forall j, 0 <= j < size -> Znth j vers' 0 = v1) as Hvers.
          { intros; match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i := j)(d := 0) in H;
              [destruct H as [Heven] | omega] end.
            destruct (list_max_spec (map (fun x => x - 1) vers') v1) as [_ Hmax].
            rewrite Forall_map in Hmax.
            apply Forall_Znth with (i := j)(d := 0) in Hmax; [simpl in Hmax | omega].
            destruct (eq_dec (Znth j vers' 0) v1); subst; auto.
            assert (Znth j vers' 0 = v1 + 1) as Heq by omega.
            rewrite Heq, Z.even_add in Heven; replace (Z.even v1) with true in Heven; discriminate. }
          destruct HL1 as [HL1].
          assert (L1 v1 = Some vals') as Hvals'.
          { eapply map_Znth_eq.
            * intro; rewrite HL1; intro X; inv X; omega.
            * intro; subst; rewrite size_def in *; discriminate.
            * intros; unfold map_Znth in *; rewrite HL1; simpl.
              assert (0 <= i < size) by omega.
              match goal with H : forall j, _ |- _ => symmetry; apply f_equal, H; auto end. }
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
          rewrite <- sepcon_assoc, snap_master_join by auto; view_shift_intros.
          match goal with H : map_incl _ L |- _ => exploit (H v1 vals') end.
          { rewrite map_add_comm by auto.
            unfold map_add; rewrite Hvals'; auto. }
          assert (map_incl L0 L) by (etransitivity; eauto; etransitivity; apply map_incl_add).
          intro; rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, make_snap|].
          rewrite sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
            ghost_snap_forget with (v2 := map_upd L0 v1 vals'), map_upd_incl; auto|].
          apply derives_view_shift; unfold share; entailer!.
          (* Iris assumes that anything duplicable has empty footprint, and anyway doesn't care about throwing away
             resources. Should we make that assumption? We could just pass the protocol assertions instead and merge them. *)
          admit.
        * rewrite (sepcon_comm (P * _)), <- !sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, HP].
          apply derives_view_shift; Exists L; entailer!.
          admit. }
    Intros x; destruct x as (v2', v2); simpl fst in *; simpl snd in *; subst.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v2 <> v1) (LOCALx Q (SEPx R))) end.
    + subst; rewrite eq_dec_refl.
      Intros L2.
      forward.
      Exists (v1, vals') L2; unfold node_state, protocol_R, ghost_snap, share; entailer!.
      { exists vals'; split; auto.
        split.
        * unfold map_upd; rewrite eq_dec_refl; auto.
        * intros; unfold map_upd; if_tac; [omega|].
          assert (v0 < v') by omega; auto. }
      erewrite sepcon_comm, map_ext_in; eauto; intros; simpl.
      rewrite map_Znth_upd; replace v1 with (Znth a vers' 0); auto.
      rewrite In_upto, Z2Nat.id in *; auto.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; go_lower.
      if_tac; [contradiction|].
      Exists v2 (map (fun i => map_upd (map_Znth i L0 0) (Znth i vers' 0) (Znth i vals' 0))
        (upto (Z.to_nat size))) (map_add L' L1); rewrite map_add_assoc; entailer!.
      { destruct (list_max_spec (map (fun x => x - 1) vers') v1); split; [omega|].
        intros.
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
        intros ?? Hk; unfold map_upd; if_tac; auto; subst.
        match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i0 := i)(d := 0) in H;
          [simpl in H; destruct H | omega] end.
        destruct (eq_dec (Znth i vers' 0) v1).
        * match goal with H : forall i, _ |- _ => exploit H; eauto; intro Heq end.
          destruct HL1 as [HL1].
          match goal with H : forall i, compatible _ _ |- _ => exploit H end.
          { eauto. }
          { unfold singleton; rewrite <- Heq, e, eq_dec_refl; eauto. }
          intros ->; auto.
        * unfold map_Znth in Hk.
          match goal with H : forall v', _ -> L0 v' = None |- _ => rewrite H in Hk; [discriminate | omega] end. }
      erewrite map_ext_in; eauto; intros; simpl.
      rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega.
Qed.

(* Since the public view of the data structure has no data content (it's just the ghost state), there's no need
   for the backing-out linearization point reasoning (and in fact the linearization point can be anywhere,
   since all new write really guarantees is that no other data will be written at that version, plus maybe a
   certain eventual consistency). *)
Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((n, input), sh), shi), version), locs), vals), g), L), v0); Intros.
  destruct H as (HP & HQ).
  forward.
  unfold node_state; Intros.
  forward_call_dep [Z : Type] (load_acq_W_witness version v0 Z.le (version_T version locs g, version_T version locs g)
    (fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef) (map_Znth i L 0) map_incl
       (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (gsh2, L) g)
    (fun s v : Z => !!(v = s) && fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef) (map_Znth i L 0) map_incl
       (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (gsh2, L) g)).
  { simpl; unfold protocol_W, share; cancel. }
  { simpl; split; intros; rewrite !emp_sepcon.
    { etransitivity; [apply view_shift_sepcon1, make_protocol_R|].
      apply derives_view_shift; cancel. }
    rewrite !sepcon_assoc, sepcon_comm, <- !sepcon_assoc, 2sepcon_assoc.
    etransitivity; [apply view_shift_sepcon1; rewrite sepcon_comm; apply protocol_R_absorb; auto|].
    view_shift_intros; assert (s' = v0) by omega.
    apply derives_view_shift; rewrite version_T_eq; unfold protocol_W; entailer!.
    admit. (* as above *) }
  Intros x; destruct x as (?, v); simpl fst in *; simpl snd in *; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call_dep [Z : Type] (store_rel_witness version (v0 + 1) v0 (v0 + 1) Z.le
    (version_T version locs g, version_T version locs g) emp emp).
  { split; auto; split; [|split; [|omega]]; intros; simpl; rewrite !sepcon_emp, ?emp_sepcon; [reflexivity|].
    rewrite !version_T_eq.
    view_shift_intro L1; view_shift_intros; subst.
    rewrite Z.even_add, Z.add_simpl_r, H in *; simpl.
    destruct (eq_dec (v0 + 1) 0); [omega|].
    if_tac; [|apply derives_view_shift; Exists L1; entailer!].
    etransitivity; [apply view_shift_sepcon2, view_shift_sepcon1, view_shift_sepcon_list;
      [rewrite 2Zlength_map; auto|]|].
    { rewrite Zlength_map; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      apply make_protocol_R. }
    rewrite <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
    rewrite <- !sepcon_assoc, snap_master_join by auto; view_shift_intros.
    rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, make_snap|].
    rewrite sepcon_map; apply derives_view_shift; Exists L; unfold protocol_W; entailer!. }
  assert (0 <= size) by (rewrite size_def; computable).
  assert_PROP (Zlength (map (fun x => vint x) vals) = size) by entailer!.
  assert (Z.even (v0 + 2) = true) by (rewrite Z.even_add; replace (Z.even v0) with true; auto).
  rewrite <- seq_assoc; Intros.
  focus_SEP 2.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
  forward_for_simple_bound 8 (EX i : Z, PROP () (LOCALx Q
    (SEPx (fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef)
             (map_Znth i (map_upd L (v0 + 2) vals) 0) map_incl (data_T version locs g, data_T version locs g))
             (sublist 0 i (upto (Z.to_nat size)))) ::
           fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef)
             (map_Znth i L 0) map_incl (data_T version locs g, data_T version locs g))
             (sublist i size (upto (Z.to_nat size)))) :: R)))) end.
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
    forward_call_dep [Z -> option Z : Type] (store_rel_witness (Znth i locs Vundef) (Znth i vals 0)
      (map_Znth i L 0) (map_upd (map_Znth i L 0) (v0 + 2) (Znth i vals 0)) map_incl (data_T version locs g, data_T version locs g)
      (protocol_W version (v0 + 1) Z.le (version_T version locs g, version_T version locs g))
      (protocol_W version (v0 + 1) Z.le (version_T version locs g, version_T version locs g))).
    { simpl; cancel. }
    { split; [apply Forall_Znth; auto; omega|].
      assert (0 <= i < Zlength (upto (Z.to_nat size))) by (rewrite Zlength_upto, Z2Nat.id; auto; omega).
      split; [|split; auto]; intros; simpl; rewrite ?emp_sepcon, ?sepcon_emp; [reflexivity|].
      rewrite !data_T_eq; view_shift_intro ver; view_shift_intros.
      rewrite sepcon_comm; etransitivity; [apply view_shift_sepcon1, make_protocol_R|].
      apply derives_view_shift; Exists (v0 + 2).
      rewrite <- Z.add_sub_assoc; simpl; unfold protocol_W; entailer!.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply protocol_delay|].
      setoid_rewrite protocol_R_join; [|rewrite join_max; eauto].
      rewrite Z.max_l; auto.
      match goal with H : log_latest L _ _ |- _ => eapply map_Znth_log_latest, (log_latest_inj _ _ _ ver) in H;
        eauto; destruct H; subst; omega end. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl fold_right.
    rewrite <- size_def, map_Znth_upd; entailer!.
  - rewrite <- size_def, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? ?]] end.
    destruct (log_latest_upd L v0 vs0 (v0 + 2) vals); auto; try omega.
    forward_call_dep [Z : Type] (version, v0 + 2, v0 + 1, v0 + 2, Z.le, (version_T version locs g, version_T version locs g),
      P * protocol_W version (v0 + 1) Z.le (version_T version locs g, version_T version locs g) *
        fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef) (map_Znth i (map_upd L (v0 + 2) vals) 0)
          map_incl (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (gsh2, L) g, II, lI,
      fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef) (map_Znth i (map_upd L (v0 + 2) vals) 0)
          map_incl (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (Tsh, L) g * R L,
      Q L tt * node_state gsh2 (map_upd L (v0 + 2) vals) (v0 + 2) version locs g).
    { split; [auto | split; [| split; [|omega]]].
      + rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        view_shift_intro L1.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)), <- !sepcon_assoc.
        erewrite (sepcon_comm (ghost _ _)), master_share_join' by eauto.
        apply derives_view_shift; entailer!.
      + intros; simpl.
        rewrite !sepcon_assoc, (sepcon_comm (version_T _ _ _ (v0 + 2) _)).
        rewrite <- !sepcon_assoc, 4sepcon_assoc.
        etransitivity; [|apply view_shift_sepcon1, HQ].
        rewrite !version_T_eq; view_shift_intro L'; view_shift_intros.
        if_tac; [omega|].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
        rewrite <- !sepcon_assoc, <- sepcon_map.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, view_shift_sepcon_list|].
        { rewrite 2Zlength_map; reflexivity. }
        { rewrite Zlength_map; intros.
          erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
          etransitivity; [apply protocol_R_absorb; auto|].
          apply view_shift_prop; intro; apply make_protocol_R. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
        rewrite <- !sepcon_assoc, snap_master_join by apply Share.nontrivial; view_shift_intros.
        rewrite !sepcon_assoc; etransitivity.
        { apply view_shift_sepcon1; etransitivity.
          * apply master_update with (v' := map_upd L (v0 + 2) vals); auto.
          * apply make_snap. }
        erewrite <- master_share_join by eauto.
        apply derives_view_shift; Exists (map_upd L (v0 + 2) vals).
        rewrite Zlength_map in *; rewrite sepcon_map.
        rewrite Z.even_add; replace (Z.even v0) with true; simpl.
        if_tac; [omega|].
        unfold node_state, protocol_W; entailer!.
        split; eauto. }
    forward.
    Exists tt L.
    rewrite Zlength_map in *; entailer!.
Qed.

Lemma body_make_node : semax_body Vprog Gprog f_make_node make_node_spec.
Proof.
  start_function.
  forward_malloc tnode n.
  forward_malloc tint p.
  repeat forward.
  forward_for_simple_bound 8 (EX i : Z, EX ld : list val, PROP (Zlength ld = i; Forall isptr ld)
    LOCAL (temp _n n)
    SEP (malloc_token Tsh (sizeof tint) p; data_at Tsh tint (vint 0) p; malloc_token Tsh (sizeof tnode) n;
         @data_at CompSpecs Tsh tnode (p, ld ++ repeat Vundef (Z.to_nat (8 - i))) n;
         fold_right sepcon emp (map (data_at Tsh tint (vint 0)) ld);
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) ld))).
  { Exists (@nil val); entailer!; auto. }
  - forward_malloc tint d.
    rewrite data_at__isptr; Intros.
    repeat forward.
    Exists (x ++ [d]); rewrite upd_init, <- app_assoc, !Zlength_app, !Zlength_cons, !Zlength_nil by (auto; tauto).
    rewrite !map_app, !sepcon_app; simpl fold_right; entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    auto.
  - Intros ld.
    (* The special case of version_T at version 0 allows us to initialize the mutually recursive protocols. *)
    apply ghost_alloc with (g := (Tsh, singleton 0 (repeat 0 (Z.to_nat size))));
      [apply master_init | Intros g].
    apply make_snap; Intros.
    assert (exists vs, Zlength vs = size /\ log_latest (singleton 0 (repeat 0 (Z.to_nat size))) 0 vs).
    { do 2 eexists; [|apply log_latest_singleton].
      rewrite Zlength_repeat, Z2Nat.id; auto; rewrite size_def; computable. }
    gather_SEP 3 0; eapply view_shift_trans;
      [|apply (@make_protocol _ _ Z.le _ _ (version_prot p ld g) p 0 0); auto|].
    { rewrite version_T_eq; apply derives_view_shift.
      Exists (singleton 0 (repeat 0 (Z.to_nat size))); simpl; entailer!. }
    apply make_protocol_R; Intros.
    focus_SEP 1; apply protocol_R_forget with (s1 := -1); [omega|].
    rewrite app_nil_r; gather_SEP 6 0; apply list_duplicate.
    { apply protocol_R_duplicable. }
    Intros; apply view_shift_sepcon_list with (l2 := map (fun l =>
      protocol_W l (singleton 0 0) map_incl (data_T p ld g, data_T p ld g)) ld); rewrite ?Zlength_map; auto.
    { intros.
      erewrite Znth_map, Znth_map', Znth_map with (d' := Vundef) by (rewrite ?Zlength_map; auto).
      rewrite sepcon_comm; etransitivity; [|apply make_protocol with (v := 0); auto; apply data_prot].
      rewrite data_T_eq.
      apply derives_view_shift; Exists 0; entailer!.
      { apply log_latest_singleton. }
      simpl; apply protocol_delay. }
    gather_SEP 2 1; apply protocol_R_absorb; auto; Intros.
    forward.
    erewrite <- master_share_join by eauto.
    unfold node_state.
    rewrite <- size_def in *.
    Exists n p ld g; unfold protocol_W, share; simpl; entailer!.
    setoid_rewrite (list_Znth_eq Vundef ld) at 3.
    rewrite map_map, <- ZtoNat_Zlength; replace (Zlength ld) with size.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite map_Znth_single, Znth_repeat; auto.
Qed.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  name data _data.
  start_function.
  rewrite data_at__eq; unfold default_val; simpl.
  repeat forward.
  assert_PROP (0 <= v) by (unfold node_state; entailer!).
  forward_for_simple_bound 3 (EX i : Z, EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)%Z) (upto (Z.to_nat i))))
    LOCAL (lvar _data (tarray tint 8) data; temp _n n)
    SEP (data_at Tsh (tarray tint 8) (repeat (vint i) 8) data; @data_at CompSpecs sh tnode (version, locs) n;
         node_state gsh2 L' (v + 2 * i) version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g))).
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

      forward_call (n, data, sh, Tsh, version, locs, repeat (i + 1) 8, g, x, v + 2 * i, emp,
        fun (_ : Z -> option (list Z)) (_ : unit) => emp, fun _ : Z -> option (list Z) => emp,
        fun _ : Z => EX L : Z -> option (list Z), ghost (gsh1, L) g, [0]).
      { entailer!.
        { split; [|unfold repable_signed in *; pose proof Int.min_signed_neg; omega].
          apply Forall_repeat.
          split; [pose proof Int.min_signed_neg; omega|].
          transitivity 3; [omega | computable]. }
        rewrite size_def, Zminus_diag, app_nil_r, map_repeat; simpl; cancel. }
      { split; simpl; rewrite <- ?exp_sepcon1, !sepcon_emp.
        * split; reflexivity.
        * intros _ _.
          apply derives_view_shift; Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)); cancel. }
      Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)).
      rewrite Z2Nat.inj_add, upto_app, map_app, map_upd_list_app by omega.
      change (upto 1) with [0]; simpl map_upd_list.
      rewrite Z2Nat.id, Z.add_0_r, Z.mul_add_distr_l, Z.add_assoc by omega.
      rewrite <- size_def; entailer!.
  - Intros L'; forward.
    Exists (map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)) (upto (Z.to_nat 3))));
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
  destruct H as (HP & HQ).
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, lg', P,
    fun (_ : Z * list Z) '(v1, vs1) => Q tt (v1, vs1),
    fun s => EX hr : _, !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some s) && ghost_ref hr gh, II, lI).
  { simpl; rewrite <- size_def; entailer!. }
  { split; [|split].
    * auto.
    * simpl.
      admit. (* laters are messy *)
    * intros (v0, vs0) (v1, vs1); simpl.
      etransitivity; [|apply HQ]; simpl.
      (* This also fails: the history in the invariant may not have caught up with the value we read. *)
Abort.*)
>>>>>>> refs/remotes/origin/master

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  assert_PROP (Z.even v = true /\ exists vs, Zlength vs = size /\ log_latest L v vs) as Hv.
  { unfold node_state; entailer!. }
  destruct Hv as [Heven [? [? [HL ?]]]].
  forward_call (n, data, sh, Tsh, version, locs, g, L, v, emp,
    fun (L' : Z -> option (list Z)) '(v', vs') => !!(v' = v -> x = vs') && emp,
    fun _ : Z -> option (list Z) => emp,
    fun _ : Z => EX L : Z -> option (list Z), ghost (gsh1, L) g, [0]).
  { rewrite <- size_def; simpl; entailer!. }
  { split; simpl; rewrite <- ?exp_sepcon1, !sepcon_emp.
    * split; reflexivity.
    * intros L' (v1, vs1); simpl.
      apply derives_view_shift; Exists L'; entailer!.
      apply andp_right; auto; apply prop_right.
      intro; subst.
      assert (L' v = Some x) as Hv by auto; rewrite Hv in *; congruence. }
  Intro X; destruct X as ((v', vs'), L'); simpl; Intros.
  forward.
  Exists v' vs'; rewrite size_def; entailer!.
  split; auto.
  match goal with H : _ -> _ |- _ => specialize (H eq_refl); subst; auto end.
Qed.
