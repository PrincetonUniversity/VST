Require Import VST.veric.rmaps.
Require Import VST.progs.ghosts.
Require Import atomics.general_atomics.
Require Import VST.progs.conclib.
Require Import atomics.maps.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.kvnode_atomic.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition load_SC_spec := DECLARE _load_SC load_SC_spec.
Definition store_SC_spec := DECLARE _store_SC store_SC_spec.

Definition tnode := Tstruct _node noattr.

Opaque upto.

Existing Instances fmap_PCM fmap_order.

Definition node_entry sh v vs locs lg i := EX v' : Z, EX log : Z -> option Z, EX d : Z,
  !!(repable_signed d /\ (if Z.even v then v' = v /\ d = Znth i vs 0 else v' >= v - 1) /\ log_latest log v' d) &&
  ghost (sh, log) (Znth i lg Vundef) * data_at sh tint (vint d) (Znth i locs Vundef).

Existing Instances max_PCM max_order.

Definition node_state sh v vs version locs g lg := !!(repable_signed v /\
    Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs) &&
  ghost (sh, v) g * data_at sh tint (vint v) version *
  fold_right sepcon emp (map (node_entry sh v vs locs lg) (upto (length locs))).

Definition node_inv v vs version locs g lg := EX v' : Z, !!(Z.even v = true /\ (v' = v \/ v' = v + 1)) &&
  node_state gsh2 v' vs version locs g lg.

Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * val * list val * val * list val * Z * list Z)) (0, [])
  [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) => temp _n n;
   fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) => temp _out out]
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) => !!(readable_share sh /\ isptr version /\
     Forall isptr locs /\ Zlength locs = 8) &&
   data_at sh tnode (version, locs) n * data_at_ Tsh (tarray tint 8) out)
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) '(v, vs) => node_inv v vs version locs g lg)
  tt []
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vs) out)
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) '(v, vs) _ => node_inv v vs version locs g lg)
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

(* The gsh1 share of the node state acts as the write permission. *)
Program Definition write_spec := DECLARE _write atomic_spec
  (ConstType (val * val * share * val * list val * list Z * val * list val * Z * list Z)) (0, [])
  [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) => temp _n n;
   fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) => temp _in input]
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) => !!(readable_share sh /\ isptr version /\
     Forall isptr locs /\ Zlength locs = 8 /\ Forall repable_signed vals /\ Z.even v0 = true) &&
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input *
   node_state gsh1 v0 vs0 version locs g lg)
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) '(v, vs) => node_inv v vs version locs g lg)
  tt []
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input *
   node_state gsh1 (v0 + 2) vals version locs g lg)
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) '(v, vs) _ =>
   node_inv (v0 + 2) vals version locs g lg)
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

Definition Gprog : funspecs := ltac:(with_library prog [load_SC_spec; store_SC_spec; read_spec; write_spec]).

Lemma land_1 : forall i, Z.land i 1 = i mod 2.
Proof.
  intros; apply Z.land_ones with (n := 1); omega.
Qed.

Lemma singleton_snap : forall (x : Z -> option Z) p v1 v2, x v1 = Some v2 ->
  view_shift (ghost_snap x p) (ghost_snap (singleton v1 v2) p).
Proof.
  intros.
  apply ghost_snap_forget.
  unfold singleton; intros ??; if_tac; intro X; inv X; auto.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((n, out), sh), version), locs), g), lg), v0), vs0); Intros.
  destruct H as (HP & HQ).
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply ENTAIL_refl].
  repeat forward.
  forward_call (version, P, II, lI,
    fun sh v' => !!(sh = gsh2) && EX v : Z, EX vs : _, !!(Z.even v = true /\ Forall repable_signed vs /\
      Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = v \/ v' = v + 1)) && ghost (gsh2, v') g *
      fold_right sepcon emp (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) * R (v, vs),
      fun v : Z => P * ghost_snap v g).
  { split.
    + intros.
      etransitivity; [apply HP|].
      apply derives_view_shift.
      Intro x; destruct x as (v, vs).
      unfold node_inv, node_state; Intro v'.
      Exists gsh2 v' v vs; entailer!.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, HP].
      view_shift_intro v2; view_shift_intro vs; view_shift_intros.
      rewrite sepcon_comm, !sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, make_snap|].
      apply derives_view_shift.
      Exists (v2, vs); unfold node_inv, node_state; Exists v; entailer!. }
  Intros v1.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP (Z.testbit v1 0 = false) (LOCALx Q (SEPx R))) end.
  { eapply semax_pre; [|apply semax_continue].
    unfold POSTCONDITION, abbreviate, overridePost.
    destruct (eq_dec EK_continue EK_normal); [discriminate|].
    unfold loop1_ret_assert.
    entailer!.
    admit. (* drop snap *) }
  { forward.
    entailer!.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_odd in *.
    destruct (Z.odd v1); auto; discriminate. }
  Intros.
  forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i)
    LOCAL (temp _snap (vint v1); temp _ver version; temp _n n; temp _out out)
    SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI);
         P; ghost_snap v1 g; @data_at CompSpecs sh tnode (version, locs) n;
         data_at Tsh (tarray tint 8) (map (fun x => vint x) vals ++ repeat Vundef (Z.to_nat (8 - i))) out;
         EX vers : list (Z * Z), !!(Zlength vers = i /\
           Forall (fun '(v, v') => v1 <= v /\ if Z.even v then v' = v else True) vers) &&
           fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers (0, 0))) g *
             ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef))
             (sublist 0 i (upto 8))))).
  { Exists (@nil Z) (@nil (Z * Z)); rewrite !sepcon_map; entailer!. }
  - Intros vers; rewrite !sepcon_map; Intros.
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward_call (Znth i locs Vundef, P * ghost_snap v1 g,
      II, lI,
      fun sh v => !!(sh = gsh2) && EX ver : Z, EX vs : _, EX ver' : Z, EX v'' : _, EX log : _,
        !!(repable_signed ver' /\ Z.even ver = true /\ Forall repable_signed vs /\ Zlength vs = Zlength locs /\
           Zlength lg = Zlength locs /\ (ver' = ver \/ ver' = ver + 1) /\
           (if Z.even ver' then v'' = ver' /\ v = Znth i vs 0 else v'' >= ver' - 1) /\ log_latest log v'' v) &&
           ghost (gsh2, ver') g * data_at gsh2 tint (vint ver') version * ghost (gsh2, log) (Znth i lg Vundef) *
           fold_right sepcon emp (upd_Znth i (map (node_entry gsh2 ver' vs locs lg) (upto (length locs))) emp) *
        R (ver, vs) * ghost_snap v1 g,
      fun v : Z => P * EX vi : Z, EX v'' : Z, !!(v1 <= vi /\ if Z.even vi then v'' = vi else True) &&
        ghost_snap v1 g * ghost_snap vi g * ghost_snap (singleton v'' v) (Znth i lg Vundef)).
(* A common case is to do no view shifts in the first part. In this case, maybe we can provide a magic-wand
   mpred for P', and prove the magic-wand equivalence separately using wand_sepcon_adjoint. *)
     { split.
      + intros.
        rewrite <- !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        apply derives_view_shift.
        Intro s; destruct s as (v, vs).
        unfold node_inv, node_state; Intros ver'.
        rewrite extract_nth_sepcon with (i := i)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry; Intros v'' log d.
        Exists gsh2 d v vs ver' v'' log; entailer!.
      + intros.
        rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, HP].
        view_shift_intro ver; view_shift_intro vs; view_shift_intro ver'; view_shift_intro v'';
          view_shift_intro log; view_shift_intros.
        rewrite sepcon_comm, !sepcon_assoc.
        etransitivity; [apply view_shift_sepcon1, make_snap|].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ (Znth i lg Vundef))), !sepcon_assoc.
        etransitivity; [apply view_shift_sepcon1, make_snap|].
        rewrite sepcon_assoc; etransitivity; [apply view_shift_sepcon1|].
        { match goal with H : log_latest _ _ _ |- _ => destruct H end.
          apply singleton_snap; eauto. }
        apply derives_view_shift.
        assert_PROP (v1 <= ver').
        { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ g)), (sepcon_comm _ (ghost_snap v1 g)).
          rewrite <- !sepcon_assoc, snap_master_join by auto; entailer!. }
        Exists (ver, vs) ver' v''; unfold node_inv, node_state; Exists ver'; entailer!.
        { if_tac; tauto. }
        rewrite extract_nth_sepcon with (i := Zlength x)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; omega).
        unfold node_entry; Exists v'' log v; unfold share; entailer!. }
      Intros vali vi v''.
      forward.
      Exists (x ++ [vali]) (vers ++ [(vi, v'')]); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
      rewrite upd_init, map_app, <- app_assoc, !sepcon_map by (rewrite ?Zlength_map; omega); entailer!.
      { rewrite Forall_app; repeat constructor; auto. }
      rewrite sublist_split with (mid := Zlength x)(hi := Zlength x + 1) by (rewrite ?Zlength_upto; simpl; omega).
      erewrite sublist_len_1, Znth_upto by (rewrite ?Zlength_upto; simpl; omega).
      rewrite !map_app, !sepcon_app; simpl.
      rewrite !app_Znth2 by omega.
      replace (Zlength vers) with (Zlength x); rewrite Zminus_diag, !Znth_0_cons; simpl; cancel.
      rewrite <- !sepcon_map; apply sepcon_list_derives; rewrite !Zlength_map; auto.
      intros ? Hi; erewrite !Znth_map by auto.
      rewrite Zlength_sublist in Hi by (rewrite ?Zlength_upto; simpl; omega).
      rewrite !Znth_sublist, !Znth_upto by (simpl; omega).
      rewrite !app_Znth1 by omega; auto.
  - Intros vals vers.
    rewrite app_nil_r, sublist_same by auto; simpl.
    rewrite Z.bit0_odd, Zodd_even_bool in *; destruct (Z.even v1) eqn: Heven; try discriminate.
    forward_call (version, P * ghost_snap v1 g * fold_right sepcon emp (map (fun i =>
      ghost_snap (fst (Znth i vers (0, 0))) g *
      ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef)) (upto 8)), II, lI,
      fun sh v' => !!(sh = gsh2) && EX v : Z, EX vs : _, !!(Z.even v = true /\ Forall repable_signed vs /\
        Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = v \/ v' = v + 1)) &&
        ghost (gsh2, v') g * fold_right sepcon emp (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) *
        R (v, vs) * ghost_snap v1 g * fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers (0, 0))) g *
          ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef)) (upto 8)),
      fun v : Z => (if eq_dec v v1 then Q (v, vals) tt else P) *
        (!!(if eq_dec v v1 then Forall (fun '(vi, v') => vi = v1 /\ v' = v1) vers else True) &&
        ghost_snap v g * fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers (0, 0))) g *
          ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef)) (upto 8)))).
    { split.
      + intros.
        rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
        apply derives_view_shift.
        Intro x; destruct x as (v, vs).
        unfold node_inv, node_state; Intro v'.
        Exists gsh2 v' v vs; entailer!.
      + intros.
        destruct (eq_dec v v1).
        * view_shift_intro ver; view_shift_intro vs; view_shift_intros; subst.
          match goal with H : _ \/ _ |- _ => destruct H; subst;
            [|match goal with H : Z.even (ver + 1) = true |- _ => rewrite Z.even_add in H;
              replace (Z.even ver) with true in H; discriminate end] end.
          apply view_shift_assert with (PP := Forall (fun '(vi, v') => vi = ver /\ v' = ver) vers).
          { rewrite Forall_forall_Znth with (d := (0, 0)), prop_forall; apply allp_right; intro i.
            rewrite prop_forall; apply allp_right; intro.
            match goal with H : Forall _ vers |- _ => apply Forall_Znth with (i0 := i)(d := (0, 0)) in H; auto end.
            rewrite extract_nth_sepcon with (i := i)(l := map _ (upto 8))
              by (rewrite Zlength_map, Zlength_upto; simpl; omega).
            erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto; simpl; omega).
            rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ g)), (sepcon_comm _ (ghost_snap (fst _) g)).
            rewrite <- !sepcon_assoc, snap_master_join by auto.
            Intros; apply prop_right; destruct (Znth i vers (0, 0)); simpl in *.
            assert (z = ver) by omega; subst.
            destruct (Z.even ver); try discriminate; tauto. }
          intro Hvers.
          etransitivity; [|etransitivity; [apply view_shift_sepcon with (Q' :=
            ghost_snap ver g * fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers (0, 0))) g *
              ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef)) (upto 8)));
            [apply (HQ (ver, vals) tt) | reflexivity] | apply derives_view_shift; entailer!]].
          apply derives_view_shift.
          assert_PROP (vs = vals).
          { assert_PROP (forall i, 0 <= i < Zlength vs -> Znth i vs 0 = Znth i vals 0);
              [|eapply prop_right, list_Znth_eq'; auto; omega].
            rewrite prop_forall; apply allp_right; intro i.
            rewrite prop_forall; apply allp_right; intro.
            apply Forall_Znth with (i0 := i)(d := (0, 0)) in Hvers; [|omega].
            rewrite extract_nth_sepcon with (i := i)
              by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
            rewrite extract_nth_sepcon with (i := i)(l := map _ _)
              by (rewrite Zlength_map, Zlength_upto; simpl; omega).
            erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, <- ?Zlength_correct; simpl; omega).
            unfold node_entry; Intros v' log d.
            destruct (Z.even ver); try discriminate.
            destruct (Znth i vers (0, 0)); repeat match goal with H : _ = _ /\ _ = _ |- _ => destruct H end.
            subst; rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ (Znth i lg Vundef))),
              (sepcon_comm _ (ghost_snap _ (Znth i lg Vundef))).
            rewrite <- !sepcon_assoc, snap_master_join by auto; simpl; Intros; apply prop_right.
            unfold singleton in *.
            match goal with H : log_latest _ _ _ |- _ => destruct H end.
            match goal with H : map_incl _ _ |- _ => specialize (H ver); simpl in H; rewrite eq_dec_refl in H;
              specialize (H _ eq_refl); rewrite H in *; congruence end. }
          subst; unfold node_inv, node_state; Exists ver; entailer!.
        * rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
          view_shift_intro ver; view_shift_intro vs; view_shift_intros.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)), (sepcon_comm _ (ghost_snap _ _)).
          rewrite <- !sepcon_assoc, snap_master_join by auto.
          view_shift_intros; rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, make_snap|].
          apply derives_view_shift; Exists (ver, vs); unfold node_inv, node_state; Exists v; entailer!. }
    Intros v2.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v2 <> v1) (LOCALx Q (SEPx R))) end.
    + subst; rewrite eq_dec_refl in *.
      forward.
      Exists tt (v1, vals); entailer!.
      admit. (* drop snaps *)
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; if_tac; [contradiction | entailer!].
      admit. (* drop snaps *)
Admitted.

Lemma dirty_entry : forall sh v vs locs lg i, Z.even v = true ->
  node_entry sh v vs locs lg i |-- node_entry sh (v + 1) vs locs lg i.
Proof.
  intros; unfold node_entry.
  Intros v' log d.
  rewrite H in *; match goal with H : _ /\ _ |- _ => destruct H end.
  Exists v log d; entailer!.
  rewrite Z.even_add, H; simpl; omega.
Qed.

Lemma clean_entry : forall v vs locs lg i vs', Z.even v = false ->
  node_entry gsh1 (v + 1) vs' locs lg i * node_entry gsh2 v vs locs lg i |--
  node_entry gsh1 (v + 1) vs' locs lg i * node_entry gsh2 (v + 1) vs' locs lg i.
Proof.
  intros; unfold node_entry.
  Intros v1 log1 d1 v2 log2 d2.
  Exists (v + 1) log1 d1 (v + 1) log1 d1.
  rewrite sepcon_assoc, (sepcon_comm (data_at _ _ _ _)), <- !sepcon_assoc.
  erewrite master_share_join' by eauto.
  assert_PROP (d1 = d2).
  { rewrite sepcon_assoc, sepcon_comm; apply sepcon_derives_prop.
    unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; Intros.
    eapply derives_trans; [apply mapsto_value_eq; auto; discriminate|].
    apply prop_left; unfold unfold_reptype; simpl; intro; apply prop_right.
    apply repr_inj_signed; auto; congruence. }
  erewrite <- master_share_join by eauto; entailer!.
  exploit (log_latest_inj log2 v1 d2 v2); eauto; intros (? & ?); subst.
  rewrite Z.even_add, H in *; simpl in *.
  match goal with H : _ /\ _ |- _ => destruct H; subst; repeat (split; auto) end.
Qed.

Corollary clean_entries : forall v vs locs lg vs', Z.even v = false ->
  fold_right sepcon emp (map (node_entry gsh1 (v + 1) vs' locs lg) (upto 8)) *
  fold_right sepcon emp (map (node_entry gsh2 v vs locs lg) (upto 8)) |--
  fold_right sepcon emp (map (node_entry gsh1 (v + 1) vs' locs lg) (upto 8)) *
  fold_right sepcon emp (map (node_entry gsh2 (v + 1) vs' locs lg) (upto 8)).
Proof.
  intros.
  rewrite <- !sepcon_map; apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
  erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
  apply clean_entry; auto.
Qed.

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((n, input), sh), version), locs), vals), g), lg), v0), vs0); Intros.
  destruct H as (HP & HQ).
  forward.
  unfold node_state; Intros.
  forward_call (version, P * ghost (gsh1, v0) g, II, lI,
    fun sh v' => !!(sh = gsh2) && EX v : Z, EX vs : _, !!(repable_signed v' /\ Z.even v = true /\
      Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
      (v' = v \/ v' = v + 1)) && ghost (gsh2, v') g * fold_right sepcon emp
        (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) * R (v, vs) * ghost (gsh1, v0) g,
    fun v : Z => P * (!!(v = v0) && ghost (gsh1, v0) g)).
  { split.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
      apply derives_view_shift.
      Intro x; destruct x as (v, vs).
      unfold node_inv, node_state; Intros v'.
      Exists gsh2 v' v vs; entailer!.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, HP].
      apply derives_view_shift; Intros v1 vs.
      assert_PROP (v0 = v).
      { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost (gsh2, _) _)), (sepcon_comm _ (ghost (gsh1, _) _)).
        erewrite <- !sepcon_assoc, master_share_join' by eauto; entailer!. }
      Exists (v1, vs); unfold node_inv, node_state; Exists v; entailer!. }
  Intros x; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call (version, v0 + 1, P * ghost (gsh1, v0) g * data_at gsh1 tint (vint v0) version, II, lI,
    fun sh => !!(sh = Tsh) && EX v : Z, EX vs : _, EX v' : Z, !!(repable_signed v' /\ Z.even v = true /\
      Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
      (v' = v \/ v' = v + 1)) && ghost (gsh2, v') g *
      fold_right sepcon emp (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) * R (v, vs) *
      ghost (gsh1, v0) g, P * ghost (gsh1, v0 + 1) g * data_at gsh1 tint (vint (v0 + 1)) version).
  { split; [auto | split].
    + intros.
      rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
      apply derives_view_shift.
      Intros x; destruct x as (v, vs).
      unfold node_inv, node_state; Intro v'.
      Exists Tsh v vs v'; entailer!.
      eapply derives_trans; [apply data_at_value_cohere; auto|].
      erewrite sepcon_comm, data_at_share_join; eauto; cancel.
    + intros.
      rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, HP].
      view_shift_intro v; view_shift_intro vs; view_shift_intro v'; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost (gsh2, _) _)), (sepcon_comm _ (ghost (gsh1, _) _)).
      erewrite <- !sepcon_assoc, master_share_join' by eauto; view_shift_intros; subst v'.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1|].
      { apply master_update with (v' := v0 + 1); omega. }
      apply derives_view_shift.
      erewrite <- master_share_join by eauto.
      subst; erewrite <- data_at_share_join by eauto.
      Exists (v, vs); unfold node_inv, node_state.
      Exists (v0 + 1); entailer!.
      { match goal with H : _ \/ _ |- _ => destruct H; subst; auto end.
        rewrite Z.even_add in *; simpl in *.
        match goal with H : Z.even v = true |- _ => rewrite H in *; discriminate end. }
      apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      apply dirty_entry; auto. }
  assert_PROP (Zlength (map (fun x => vint x) vals) = 8) by entailer!.
  rewrite <- seq_assoc.
  forward_for_simple_bound 8 (EX i : Z, PROP ( )
    LOCAL (temp _v (vint v0); temp _ver version; temp _n n; temp _in input)
    SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P;
    ghost (gsh1, v0 + 1) g; data_at gsh1 tint (vint (v0 + 1)) version;
    @data_at CompSpecs sh tnode (version, locs) n;
    data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) input;
    fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (sublist 0 i (upto 8)));
    fold_right sepcon emp (map (node_entry gsh1 v0 vs0 locs lg) (sublist i 8 (upto 8))))).
  { rewrite <- ZtoNat_Zlength; replace (Zlength locs) with 8; entailer!. }
  - (* loop body *)
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward.
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto; simpl; omega); simpl.
    rewrite Zlength_map in *.
    forward_call (Znth i locs Vundef, Znth i vals 0, P * ghost (gsh1, v0 + 1) g *
      node_entry gsh1 v0 vs0 locs lg i, II, lI,
      fun sh => !!(sh = Tsh) && EX ver : Z, EX vs : _, EX ver' : Z, EX v'' : _, EX log : _, EX d : Z,
        !!(repable_signed ver' /\ Z.even ver = true /\ Forall repable_signed vs /\ Zlength vs = Zlength locs /\
           Zlength lg = Zlength locs /\ (ver' = ver \/ ver' = ver + 1) /\
           (if Z.even ver' then v'' = ver' /\ d = Znth i vs 0 else v'' >= ver' - 1) /\ log_latest log v'' d) &&
        ghost (gsh2, ver') g * data_at gsh2 tint (vint ver') version * ghost (gsh2, log) (Znth i lg Vundef) *
        fold_right sepcon emp (upd_Znth i (map (node_entry gsh2 ver' vs locs lg) (upto (length locs))) emp) *
        R (ver, vs) * ghost (gsh1, v0 + 1) g *
        EX log' : _, !!(log_latest log' v0 (Znth i vs0 0)) && ghost (gsh1, log') (Znth i lg Vundef),
      P * ghost (gsh1, v0 + 1) g * node_entry gsh1 (v0 + 2) vals locs lg i).
    { split; [apply Forall_Znth; auto; omega | split].
      + rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        apply derives_view_shift.
        Intro x; destruct x as (v, vs).
        unfold node_inv, node_state; Intro v'.
        rewrite extract_nth_sepcon with (i := i)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry; Intros v'' log d v2 log2 d2.
        Exists Tsh v vs v' v'' log d log2; entailer!.
        { replace (Z.even v0) with true in *; match goal with H : _ /\ _ |- _ => destruct H; subst; auto end. }
        eapply derives_trans; [apply data_at_value_cohere; auto|].
        erewrite sepcon_comm, data_at_share_join by eauto; cancel.
      + intros.
        rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [|apply view_shift_sepcon1, HP].
        view_shift_intro ver; view_shift_intro vs; view_shift_intro ver'; view_shift_intro v'';
          view_shift_intro log; view_shift_intro d; view_shift_intro log'; view_shift_intros.
        apply view_shift_assert with (PP := v0 + 1 = ver').
        { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost (gsh2, _) g)), (sepcon_comm _ (ghost (gsh1, _) g)).
          erewrite <- !sepcon_assoc, master_share_join' by eauto; entailer!. }
        intro; subst.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost (gsh2, _) (Znth _ _ _))).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost (gsh1, _) (Znth _ _ _))).
        erewrite <- !sepcon_assoc, master_share_join' by eauto; view_shift_intros; subst.
        exploit (log_latest_inj log v'' d v0); eauto; intros (? & ?); subst.
        destruct (log_latest_upd log v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1|].
        { apply master_update with (v' := map_upd log (v0 + 2) (Znth i vals 0)); auto. }
        erewrite <- master_share_join by eauto; apply derives_view_shift.
        Exists (ver, vs); unfold node_inv, node_state.
        Exists (v0 + 1); rewrite extract_nth_sepcon with (i := i)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        erewrite <- data_at_share_join by eauto.
        unfold node_entry; Exists (v0 + 2) (map_upd log (v0 + 2) (Znth i vals 0)) (Znth i vals 0) (v0 + 2)
          (map_upd log (v0 + 2) (Znth i vals 0)) (Znth i vals 0); entailer!.
        rewrite !Z.even_add; simpl.
        replace (Z.even v0) with true; simpl.
        split; split; auto; try omega; apply Forall_Znth; auto; omega. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (auto; rewrite ?Zlength_upto; simpl; omega); entailer!.
  - rewrite !sublist_nil, !sublist_same by auto; simpl.
    assert (repable_signed (v0 + 2)) by admit. (* version stays in range *)
    forward_call (version, v0 + 2, P * ghost (gsh1, v0 + 1) g * data_at gsh1 tint (vint (v0 + 1)) version *
      fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (upto 8)), II, lI,
      fun sh => !!(sh = Tsh) && EX v : Z, EX vs : _, EX v' : Z, !!(repable_signed v' /\ Z.even v = true /\
        Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
        (v' = v \/ v' = v + 1)) && ghost (gsh2, v') g *
        fold_right sepcon emp (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) * R (v, vs) *
        ghost (gsh1, v0 + 1) g * fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (upto 8)),
      EX v : Z, EX vs : list Z, Q (v, vs) tt * ghost (gsh1, v0 + 2) g * data_at gsh1 tint (vint (v0 + 2)) version *
        fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (upto 8))).
    { split; [auto | split].
      + intros.
        rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        apply derives_view_shift.
        Intros x; destruct x as (v, vs).
        unfold node_inv, node_state; Intro v'.
        Exists Tsh v vs v'; entailer!.
        eapply derives_trans; [apply data_at_value_cohere; auto|].
        erewrite sepcon_comm, data_at_share_join by eauto; cancel.
      + intros.
        view_shift_intro v; view_shift_intro vs; view_shift_intro v'; view_shift_intros.
        etransitivity; [|etransitivity; [apply view_shift_sepcon with (Q' :=
          ghost (gsh1, v0 + 2) g * data_at gsh1 tint (vint (v0 + 2)) version *
            fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (upto 8)));
          [apply (HQ (v, vs) tt) | reflexivity] | apply derives_view_shift; Exists v vs; entailer!]].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost (gsh2, _) _)), (sepcon_comm _ (ghost (gsh1, _) _)).
        erewrite <- !sepcon_assoc, master_share_join' by eauto; view_shift_intros; subst.
        match goal with H : _ \/ _ |- _ => destruct H; [subst; rewrite Z.even_add in *;
          replace (Z.even v0) with true in *; discriminate|] end.
        assert (v = v0) by omega; subst.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1|].
        { apply master_update with (v' := v0 + 2); omega. }
        erewrite <- master_share_join by eauto; apply derives_view_shift; unfold node_inv, node_state.
        Exists (v0 + 2); rewrite Zlength_map in *.
        replace (length locs) with (Z.to_nat 8) by (symmetry; rewrite <- Zlength_length; auto; computable).
        pose proof (clean_entries (v0 + 1) vs locs lg vals) as Hclean.
        rewrite <- Z.add_assoc in Hclean; simpl in *.
        sep_apply Hclean.
        { rewrite Z.even_add; replace (Z.even v0) with true; auto. }
        erewrite <- data_at_share_join by eauto; entailer!.
        rewrite Z.even_add; replace (Z.even v0) with true; auto. }
    Intros s; destruct s as (v, vs).
    forward.
    Exists tt (v, vs); entailer!.
Admitted.
