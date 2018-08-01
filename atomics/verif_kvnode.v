Require Import VST.progs.ghost.
Require Import atomics.verif_atomics.
Require Import VST.progs.conclib.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.kvnode.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(*Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.*)

Definition tnode := Tstruct _node noattr.

Opaque upto.

Definition make_loads lv := map (fun v => Load (vint v)) lv.

(* Invariant for version number: Every write increases it, and the version of each data location is at least the
   most recently read version. *)
(* Invariant for each location: The "rounded up" version number is at least the location's version. *)

Definition round_up i := i + i mod 2.
Definition round_down i := i - i mod 2.

(* Do we really need the hists? *)
(* Ghost vars act as write permissions. *)
Definition ver_R g gsh gv lg (h : list hist_el) v := ghost_master v g * ghost_var gsh v gv *
  fold_right sepcon emp (map (ghost_snap (round_down v)) lg).
Definition loc_R g gsh gl gv (h : list hist_el) (v : Z) := EX ver : Z, EX ver' : Z,
  !!(repable_signed ver' /\ ver <= round_up ver') &&
  ghost_master ver g * ghost_var gsh ver gl * ghost_snap ver' gv.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0,
             P at level 100, Q at level 100).

Definition read_spec :=
 DECLARE _read
 WITH n : val, out : val, sh : share, version : val, locs : list val, gv : val, gsh : share, gv' : val,
   gv2 : val, lg : list val, lgl : list val, hv : hist, ghosts : list val, hists : list hist, v0 : Z
 PRE [ _n OF tptr tnode, _out OF tptr tint ]
  PROP (readable_share sh; Zlength lg = 8; Zlength ghosts = 8; Zlength hists = 8; v0 mod 2 = 0)
  LOCAL (temp _n n; temp _out out)
  SEP (data_at sh tnode (version, locs) n; data_at_ Tsh (tarray tint 8) out;
       atomic_loc_hist sh version gv 0 (ver_R gv2 gsh gv' lg) hv; ghost_snap v0 gv2;
       fold_right sepcon emp (map (fun i => atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
         (loc_R (Znth i lg Vundef) gsh (Znth i lgl Vundef) gv2) (Znth i hists [])) (upto 8));
       fold_right sepcon emp (map (ghost_snap v0) lg))
 POST [ tvoid ]
  EX failvs : list Z, EX loops : Z, EX v : Z, EX hv' : hist, EX vals : list Z, EX hists' : list hist,
  PROP (v mod 2 = 0; add_events hv (make_loads (failvs ++ [v; v])) hv'; Forall repable_signed failvs;
        Forall repable_signed vals; Zlength hists' = 8; loops <= Zlength failvs)
  LOCAL ()
  SEP (data_at sh tnode (version, locs) n; data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) out;
       atomic_loc_hist sh version gv 0 (ver_R gv2 gsh gv' lg) hv'; ghost_snap v gv2;
       fold_right sepcon emp (map (fun i => EX fails : list Z,
         !!(add_events (Znth i hists []) (make_loads (fails ++ [Znth i vals 0])) (Znth i hists' []) /\
            Zlength fails = loops) &&
         atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
           (loc_R (Znth i lg Vundef) gsh (Znth i lgl Vundef) gv2) (Znth i hists' [])) (upto 8));
       fold_right sepcon emp (map (ghost_snap v) lg)).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100).

(* For now, we guarantee only one writer by using a ghost variable as a write permission. *)
Definition write_spec :=
 DECLARE _write
 WITH n : val, input : val, sh : share, version : val, locs : list val, vals : list Z, gv : val, gv2 : val,
   gsh1 : share, gsh2 : share, gv' : val, lg : list val, lgl : list val, hv : hist, ghosts : list val,
   hists : list hist, v : Z
 PRE [ _n OF tptr tnode, _in OF tptr tint ]
  PROP (readable_share sh; Forall repable_signed vals; Zlength lg = 8; Zlength lgl = 8; Zlength ghosts = 8;
        Zlength hists = 8; v mod 2 = 0; readable_share gsh1; readable_share gsh2; sepalg.join gsh1 gsh2 Tsh)
  LOCAL (temp _n n; temp _in input)
  SEP (data_at sh tnode (version, locs) n; data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input;
       atomic_loc_hist sh version gv 0 (ver_R gv2 gsh2 gv' lg) hv; ghost_snap v gv2; ghost_var gsh1 v gv';
       fold_right sepcon emp (map (fun i => atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
         (loc_R (Znth i lg Vundef) gsh2 (Znth i lgl Vundef) gv2) (Znth i hists [])) (upto 8));
       fold_right sepcon emp (map (ghost_snap v) lg); fold_right sepcon emp (map (ghost_var gsh1 v) lgl))
 POST [ tvoid ]
  EX hv' : hist, EX hists' : list hist,
  PROP (add_events hv [Load (vint v); Store (vint (v + 1)); Store (vint (v + 2))] hv'; Zlength hists' = 8;
        (v + 2) mod 2 = 0)
  LOCAL ()
  SEP (data_at sh tnode (version, locs) n; data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input;
       atomic_loc_hist sh version gv 0 (ver_R gv2 gsh2 gv' lg) hv'; ghost_snap (v + 2) gv2;
       ghost_var gsh1 (v + 2) gv';
       fold_right sepcon emp (map (fun i =>
       !!(add_events (Znth i hists []) [Store (vint (Znth i vals 0))] (Znth i hists' [])) &&
       atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
         (loc_R (Znth i lg Vundef) gsh2 (Znth i lgl Vundef) gv2) (Znth i hists' [])) (upto 8));
       fold_right sepcon emp (map (ghost_snap (v + 2)) lg);
       fold_right sepcon emp (map (ghost_var gsh1 (v + 2)) lgl)).

Definition Gprog : funspecs := ltac:(with_library prog [load_SC_spec; store_SC_spec; read_spec; write_spec]).

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Lemma snap_snap_max : forall v1 v2 p,
  ghost_snap v1 p * ghost_snap v2 p = ghost_snap v1 p * ghost_snap (Z.max v1 v2) p.
Proof.
  intros; rewrite ghost_snap_join'.
  replace (Z.max v1 v2) with (Z.max v1 (Z.max v1 v2)) at 1.
  rewrite <- ghost_snap_join'; auto.
  { rewrite Z.max_r, Z.max_comm; auto.
    apply Z.le_max_l. }
Qed.

Lemma snaps_snaps_max : forall {cs : compspecs} (v1 v2 : Z) lg,
  @view_shift cs
    (fold_right sepcon emp (map (ghost_snap v1) lg) * fold_right sepcon emp (map (ghost_snap v2) lg))
    (fold_right sepcon emp (map (ghost_snap v1) lg) * fold_right sepcon emp (map (ghost_snap (Z.max v1 v2)) lg)).
Proof.
  induction lg; simpl; repeat intro; auto.
  rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
  rewrite (sepcon_comm (ghost_snap _ _)), snap_snap_max.
  rewrite sepcon_assoc, sepcon_comm, flatten_sepcon_in_SEP.
  eapply IHlg, semax_pre; [|eauto].
  go_lowerx; entailer!.
Qed.

Lemma snaps_snaps_le : forall {cs : compspecs} v lg (lv : list Z) (Hlen : Zlength lv = Zlength lg),
 @view_shift cs
    (fold_right sepcon emp (map (ghost_snap v) lg) *
     fold_right sepcon emp (map (fun '(v, g) => ghost_snap v g) (combine lv lg)))
    (fold_right sepcon emp (map (ghost_snap v) lg) * EX lv : list Z, !!(Zlength lv = Zlength lg /\
       Forall (fun v' => v <= v') lv) &&
     fold_right sepcon emp (map (fun '(v, g) => ghost_snap v g) (combine lv lg))).
Proof.
  induction lg; simpl; repeat intro.
  - apply Zlength_nil_inv in Hlen; subst; simpl.
    eapply semax_pre; [|eauto].
    go_lowerx.
    Exists (@nil Z); entailer!.
  - destruct lv; [symmetry in Hlen; apply Zlength_nil_inv in Hlen; discriminate | simpl].
    rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost_snap _ _)), snap_snap_max.
    rewrite sepcon_assoc, sepcon_comm, flatten_sepcon_in_SEP.
    apply IHlg; auto.
    { rewrite !Zlength_cons in *; omega. }
    eapply semax_pre; [|eauto]; go_lowerx.
    Intros lv'; Exists (Z.max v z :: lv'); simpl; entailer!.
    split; [rewrite !Zlength_cons; omega|].
    constructor; auto.
    apply Zmax_bound_l; omega.
Qed.

Lemma land_1 : forall i, Z.land i 1 = i mod 2.
Proof.
  intros; apply Z.land_ones with (n := 1); omega.
Qed.

Lemma round_down_mono : forall v1 v2, v1 <= v2 -> round_down v1 <= round_down v2.
Proof.
  intros; unfold round_down.
  destruct (eq_dec v1 v2); [subst; omega|].
  exploit (Z_mod_lt v1 2); [computable|].
  exploit (Z_mod_lt v2 2); [computable|].
  omega.
Qed.

Lemma round_up_max_distr : forall v1 v2, round_up (Z.max v1 v2) = Z.max (round_up v1) (round_up v2).
Proof.
  intros; unfold round_up.
  exploit (Z_mod_lt v1 2); [computable|].
  exploit (Z_mod_lt v2 2); [computable|].
  intros; destruct (Z.max_spec v1 v2) as [(? & ->) | (? & ->)]; [rewrite Z.max_r | rewrite Z.max_l]; auto;
    try omega.
  destruct (eq_dec v1 v2); subst; omega.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  apply semax_pre with (P' := EX failvs : list Z, EX loops : Z, EX hv' : hist, EX hists' : list hist, EX v0 : Z,
    PROP (add_events hv (make_loads failvs) hv'; Forall repable_signed failvs; Zlength hists' = 8;
          loops <= Zlength failvs)
    LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ Tsh (tarray tint 8) out;
         atomic_loc_hist sh version gv 0 (ver_R gv2 gsh gv' lg) hv'; ghost_snap v0 gv2;
         fold_right sepcon emp (map (fun i => EX fails : list Z,
           !!(add_events (Znth i hists []) (make_loads fails) (Znth i hists' []) /\ Zlength fails = loops) &&
           atomic_loc_hist sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
             (loc_R (Znth i lg Vundef) gsh (Znth i lgl Vundef) gv2) (Znth i hists' [])) (upto 8));
         EX lv : list Z, !!(Zlength lv = 8) &&
             fold_right sepcon emp (map (fun '(v, g) => ghost_snap v g) (combine lv lg)))).
  { Exists (@nil Z) 0 hv hists v0 (repeat v0 8).
    rewrite combine_const2, map_map by (simpl; omega); entailer!.
    apply sepcon_derives; auto.
    apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    Exists (@nil Z); entailer!. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply ENTAIL_refl].
  - Intros failvs loops hv' hists' v1 lv.
    forward.
    unfold atomic_loc_hist at 1; rewrite atomic_loc_isptr; Intros.
    forward.
    assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
    forward_call (AL_witness sh version gv 0 (ver_R gv2 gsh gv' lg) hv'
      (ghost_snap v1 gv2 * fold_right sepcon emp (map (fun '(v, g) => ghost_snap v g) (combine lv lg)))
      (fun v => !!(v1 <= v) && ghost_snap v gv2 *
        EX lv : list Z, !!(Zlength lv = 8 /\ Forall (fun v' => round_down v <= v') lv) &&
         fold_right sepcon emp (map (fun '(v, g) => ghost_snap v g) (combine lv lg)))).
    { split; auto.
      apply AL_hist_spec; auto; repeat intro.
      unfold ver_R in *.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)), <- 2sepcon_assoc.
      rewrite sepcon_assoc, 2flatten_sepcon_in_SEP.
      assert_PROP (v1 <= v).
      { rewrite snap_master_join'; go_lowerx; entailer!. }
      eapply snap_master_update' with (v' := v); [omega|].
      focus_SEP 2; apply snaps_snaps_le; [omega|].
      eapply semax_pre; [|eauto].
      go_lowerx.
      Intros lv'; Exists lv'; entailer!. }
    Intros v; simpl; Intros hv1 lv1.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (Z.testbit v 0 = false) (LOCALx Q (SEPx R))) end.
    { eapply semax_pre; [|apply semax_continue].
      unfold POSTCONDITION, abbreviate, overridePost.
      destruct (eq_dec EK_continue EK_normal); [discriminate|].
      unfold loop1_ret_assert.
      Exists (failvs ++ [v]) loops hv1 hists' v; entailer!.
      - split; [unfold make_loads; rewrite map_app; eapply add_events_trans; eauto|].
        split; [rewrite Forall_app; auto|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
      - Exists lv1; entailer!. }
    { forward.
      entailer!.
      unfold Int.one in *; rewrite and_repr, land_1, Zmod_odd in *.
      destruct (Z.odd v); auto; discriminate. }
    Intros.
    forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i; Forall repable_signed vals)
      LOCAL (temp _snap (vint v); temp _ver version; temp _n n; temp _out out)
      SEP (atomic_loc_hist sh version gv 0 (ver_R gv2 gsh gv' lg) hv1;
           @data_at CompSpecs sh tnode (version, locs) n;
           data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals ++ repeat Vundef (Z.to_nat (8 - i))) out;
           EX hists'' : list hist, !!(Zlength hists'' = 8 /\ sublist i 8 hists'' = sublist i 8 hists') &&
           fold_right sepcon emp (map (fun j => EX fails : list Z, !!(add_events (Znth j hists [])
             (if zlt j i then make_loads (fails ++ [Znth j vals 0]) else make_loads fails) (Znth j hists'' []) /\
             Zlength fails = loops) &&
             atomic_loc_hist sh (Znth j locs Vundef) (Znth j ghosts Vundef) 0
               (loc_R (Znth j lg Vundef) gsh (Znth j lgl Vundef) gv2) (Znth j hists'' [])) (upto 8));
           EX v' : Z, EX lv' : list Z, !!(repable_signed v' /\ Zlength lv' = 8 /\
             Forall (fun vl => round_down v <= vl) lv' /\
             Forall (fun vl => vl <= round_up v') (sublist 0 i lv')) && ghost_snap v' gv2 *
             fold_right sepcon emp (map (fun '(v, g) => ghost_snap v g) (combine lv' lg)))).
    { Exists (@nil Z) hists' v lv1; unfold atomic_loc_hist at 2; rewrite data_at__eq, sublist_nil; entailer!. }
    + (* loop body *)
      Intros hists'' v' lv'.
      rewrite extract_nth_sepcon with (i := i) by (rewrite Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; simpl; omega); Intros.
      destruct (zlt i i); [omega|].
      Intros fails.
      rewrite extract_nth_sepcon with (i := i)(l := map _ _) by (rewrite Zlength_map, Zlength_combine, Z.min_l;
        auto; omega).
      rewrite Znth_map with (d' := (0, Vundef)), Znth_combine by (rewrite ?Zlength_combine, ?Z.min_l; omega).
      unfold atomic_loc_hist at 2; rewrite (atomic_loc_isptr _ (Znth i locs Vundef)); Intros.
      forward.
      assert (round_down v <= Znth i lv' 0) by (apply Forall_Znth; auto; omega).
      forward_call (AL_witness sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
        (loc_R (Znth i lg Vundef) gsh (Znth i lgl Vundef) gv2) (Znth i hists'' [])
        (ghost_snap v' gv2 * ghost_snap (Znth i lv' 0) (Znth i lg Vundef))
        (fun _ => EX ver : Z, EX ver' : Z, !!(repable_signed ver' /\ round_down v <= ver <= round_up ver') &&
           ghost_snap (Z.max ver' v') gv2 * ghost_snap ver (Znth i lg Vundef))).
      { split; auto.
        apply AL_hist_spec; auto; repeat intro.
        unfold loc_R in *.
        erewrite exp_sepcon1, extract_nth_exists_in_SEP with (n := O); [|simpl; eauto].
        Intro ver; simpl.
        erewrite exp_sepcon1, extract_nth_exists_in_SEP with (n := O); [|simpl; eauto].
        Intro ver'; simpl.
        erewrite !sepcon_andp_prop', extract_prop_in_SEP with (n := O); [|simpl; eauto].
        Intros; simpl.
        rewrite <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc.
        rewrite sepcon_assoc, 2flatten_sepcon_in_SEP.
        assert_PROP (Znth i lv' 0 <= ver).
        { rewrite snap_master_join'; go_lowerx; entailer!. }
        eapply snap_master_update' with (v'0 := ver); [omega|].
        rewrite snap_snap_max.
        eapply semax_pre; [|eauto].
        go_lowerx.
        Exists ver ver' ver ver'; entailer!. }
      Intros vi; simpl; Intros hi vers; destruct vers as (ver, ver').
      gather_SEP 3 8; rewrite replace_nth_sepcon.
      forward.
      Exists (x ++ [vi]) (upd_Znth i hists'' hi) (Z.max ver' v') (upd_Znth i lv' ver).
      rewrite map_app.
      replace (8 - (i + 1)) with (8 - (Zlength (map (fun x => vint x) x ++ [vint vi])))
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_map; subst; auto).
      simpl map; rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      match goal with H : sublist _ _ hists'' = sublist _ _ hists' |- _ =>
        rewrite sublist_next with (i0 := i)(l := hists'')(d := []),
          sublist_next with (i0 := i)(l := hists')(d := []) in H by (auto; omega); inv H end.
      rewrite combine_upd_Znth1 with (d := Vundef), <- upd_Znth_map by omega.
      subst; rewrite Zlength_map, !Zlength_app, !Zlength_cons, !Zlength_nil; entailer!.
      { split; [rewrite Forall_app; auto|].
        rewrite !upd_Znth_Zlength by omega.
        split; [|split].
        * split; auto.
          rewrite sublist_upd_Znth_r by omega; auto.
        * destruct (Z.max_spec ver' v') as [(? & ->) | (? & ->)]; auto.
        * split; auto.
          rewrite sublist_upd_Znth_lr, Z.sub_0_r by omega.
          split; [apply Forall_upd_Znth; auto; tauto|].
          rewrite sublist_split with (mid := Zlength x) by omega.
          rewrite upd_Znth_app2; rewrite !Zlength_sublist; try omega.
          rewrite Z.sub_0_r, Zminus_diag, sublist_len_1 with (d := 0), upd_Znth0, sublist_1_cons by omega.
          rewrite Zlength_cons, sublist_nil, Forall_app; repeat constructor.
          -- eapply Forall_impl; [|eauto]; simpl; intros.
             rewrite round_up_max_distr; apply Zmax_bound_r; tauto.
          -- rewrite round_up_max_distr; apply Zmax_bound_l; tauto. }
      rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map;
        auto; intros.
      erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      destruct (eq_dec i (Zlength x)).
      * subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto; omega).
        Exists fails.
        destruct (zlt (Zlength x) (Zlength x + 1)); [|omega].
        rewrite app_Znth2, Zminus_diag, Znth_0_cons by omega.
        entailer!.
        unfold make_loads; rewrite map_app; eapply add_events_trans; eauto.
      * rewrite !upd_Znth_diff' by (rewrite ?Zlength_map; auto; omega).
        erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
        Intros fails'; Exists fails'; entailer!.
        destruct (zlt i (Zlength x)), (zlt i (Zlength x + 1)); try omega; auto.
        rewrite app_Znth1; auto.
    + Intros vals hists'' v' lv'.
      unfold atomic_loc_hist at 1; Intros.
      forward_call (AL_witness sh version gv 0 (ver_R gv2 gsh gv' lg) hv1 (ghost_snap v' gv2)
        (fun v => !!(v' <= v) && ghost_snap v gv2)).
      { split; auto.
        apply AL_hist_spec; auto; repeat intro.
        unfold ver_R in *.
        rewrite sepcon_comm, <- !sepcon_assoc.
        assert_PROP (v' <= v2).
        { rewrite snap_master_join'; go_lowerx; entailer!. }
        rewrite 2flatten_sepcon_in_SEP.
        eapply snap_master_update' with (v'0 := v2); [omega|].
        eapply semax_pre; [|eauto].
        go_lowerx; entailer!. }
      Intros v2; simpl; Intros hv2.
      rewrite app_nil_r.
      rewrite Z.testbit_false, Zdiv_1_r in * by omega.
      match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (v2 <> v) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists failvs loops v hv2 vals hists''; unfold atomic_loc_hist at 2; entailer!.
        { unfold make_loads; rewrite map_app; eapply add_events_trans; eauto.
          eapply add_events_trans with (le := [_]); eauto. }
        apply sepcon_derives; [auto|].
        apply sepcon_list_derives; rewrite !Zlength_map, Zlength_combine, Z.min_l; try omega.
        intros; erewrite Znth_map with (d' := (0, Vundef)), Znth_map, Znth_combine
          by (rewrite ?Zlength_combine, ?Z.min_l; omega).
        replace (Znth i lv' 0) with v; auto.
        match goal with H : Forall _ lv' |- _ => apply Forall_Znth with (i0 := i)(d := 0) in H end; auto.
        match goal with H : Forall _ (sublist _ _ lv') |- _ =>
          rewrite sublist_same in H by (auto; omega); apply Forall_Znth with (i0 := i)(d := 0) in H end; auto.
        unfold round_down, round_up in *.
        exploit (Z_mod_lt v' 2); [computable|].
        destruct (eq_dec v' v); subst; omega.
      * forward.
        entailer!.
      * intros; unfold overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
        unfold POSTCONDITION, abbreviate, loop1_ret_assert.
        Intros; Exists (failvs ++ [v; v2]) (loops + 1) hv2 hists'' v2; unfold atomic_loc_hist at 2; entailer!.
        { rewrite Forall_app, Zlength_app, !Zlength_cons, Zlength_nil; repeat (constructor; auto); [|omega].
          unfold make_loads; rewrite map_app; eapply add_events_trans; eauto.
          eapply add_events_trans with (le := [_]); eauto. }
        Exists lv'; entailer!.
        apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
        erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
        Intros fails; Exists (fails ++ [Znth i vals 0]); entailer!.
        destruct (zlt i 8); [|rewrite Zlength_upto in *; simpl in *; omega].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; split; auto.
Qed.

Lemma ver_R_precise : forall g gsh gv lg v, precise (EX h : _, ver_R g gsh gv lg h v).
Proof.
  intros; unfold ver_R.
  rewrite exp_trivial by (exact []).
  unfold ghost_snap, ghost_master; repeat apply precise_sepcon; auto.
  { apply ghost_precise. }
  apply precise_fold_right.
  rewrite Forall_map, Forall_forall; simpl; intros.
  apply ghost_precise.
Qed.
Hint Resolve ver_R_precise.

Lemma loc_R_precise : forall g gsh gl gv v, precise (EX h : _, loc_R g gsh gl gv h v).
Proof.
  intros; unfold loc_R.
  rewrite exp_trivial by (exact []).
  unfold ghost_master, ghost_snap.
  apply derives_precise' with (Q := (EX sm : (option Z * option Z), ghost sm g) *
    (EX v : Z, ghost_var gsh v gl) * (EX sm : (option Z * option Z), ghost sm gv));
    [|repeat apply precise_sepcon; try apply ex_ghost_precise; apply ghost_var_precise].
  Intros ver ver'; Exists (@None Z, Some ver) (Some ver', @None Z) ver; auto.
Qed.
Hint Resolve loc_R_precise.

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_function.
  unfold atomic_loc_hist at 1; Intros.
  rewrite atomic_loc_isptr; Intros.
  forward.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  (* The ghost_var guarantees that no one else has changed the version. *)
  forward_call (AL_witness sh version gv 0 (ver_R gv2 gsh2 gv' lg) hv
    (ghost_var gsh1 v gv') (fun v' => !!(v' = v) && ghost_var gsh1 v gv')).
  { split; auto.
    apply AL_hist_spec; auto; repeat intro.
    unfold ver_R in *.
    rewrite !flatten_sepcon_in_SEP.
    gather_SEP 3 1.
    assert_PROP (v = v0).
    { go_lowerx; apply sepcon_derives_prop, ghost_var_inj; auto. }
    eapply semax_pre; [|eauto].
    go_lowerx; entailer!. }
  Intros v'; simpl; Intros hv1; subst.
  assert (repable_signed (v + 1)) by admit. (* version stays in range *)
  assert ((v + 1) mod 2 = 1) as Hdirty.
  { rewrite Zplus_mod; replace (v mod 2) with 0.
    rewrite !Zmod_small by (try apply Z_mod_lt; computable); auto. }
  forward_call (AS_witness sh version gv 0 (ver_R gv2 gsh2 gv' lg) hv1 (v + 1)
    (ghost_snap v gv2 * ghost_var gsh1 v gv') (ghost_snap (v + 1) gv2 * ghost_var gsh1 (v + 1) gv')).
  { split; [|split; auto].
    apply AS_hist_spec; auto.
    repeat intro.
    unfold ver_R in *.
    rewrite <- !sepcon_assoc, !flatten_sepcon_in_SEP.
    gather_SEP 4 1.
    assert_PROP (v = v').
    { go_lowerx; apply sepcon_derives_prop, ghost_var_inj; auto. }
    subst v'; erewrite ghost_var_share_join by eauto.
    apply ghost_var_update with (v' := v + 1).
    erewrite <- (ghost_var_share_join _ _ _ _ _ SH2).
    gather_SEP 3 1.
    apply snap_master_update' with (v' := v + 1); [omega|].
    eapply semax_pre; [|eauto].
    unfold round_down.
    replace (v mod 2) with 0; rewrite Hdirty, Z.sub_0_r, Z.add_simpl_r.
    go_lowerx; entailer!. }
  Intros hv2.
  exploit (add_events_trans hv); eauto; intro.
  assert_PROP (Zlength vals = 8).
  { entailer!.
    rewrite Zlength_map in *; auto. }
  rewrite <- seq_assoc.
  forward_for_simple_bound 8 (EX i : Z, EX hists' : list hist, PROP (Zlength hists' = i)
    LOCAL (temp _v (vint v); temp _ver version; temp _n n; temp _in input)
    SEP (atomic_loc_hist sh version gv 0 (ver_R gv2 gsh2 gv' lg) hv2;
         ghost_snap (v + 1) gv2; ghost_var gsh1 (v + 1) gv'; @data_at CompSpecs sh tnode (version, locs) n;
         data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) input;
         fold_right sepcon emp (map (fun j =>
           !!(j < i -> add_events (Znth j hists []) [Store (vint (Znth j vals 0))] (Znth j hists' [])) &&
           atomic_loc_hist sh (Znth j locs Vundef) (Znth j ghosts Vundef) 0
             (loc_R (Znth j lg Vundef) gsh2 (Znth j lgl Vundef) gv2)
             (if zlt j i then Znth j hists' [] else Znth j hists [])) (upto 8));
         fold_right sepcon emp (map (ghost_snap (v + 2)) (sublist 0 i lg));
         fold_right sepcon emp (map (ghost_var gsh1 (v + 2)) (sublist 0 i lgl));
         fold_right sepcon emp (map (ghost_snap v) (sublist i 8 lg));
         fold_right sepcon emp (map (ghost_var gsh1 v) (sublist i 8 lgl)))).
  { Exists (@nil hist); rewrite !sublist_nil, !sublist_same by auto; unfold atomic_loc_hist at 2; entailer!.
    apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    apply andp_right; [apply prop_right; omega|].
    destruct (zlt i 0); [omega | auto]. }
  - (* loop body *)
    rewrite extract_nth_sepcon with (i := i) by (rewrite Zlength_map; auto).
    erewrite Znth_map, Znth_upto by (auto; simpl; omega); Intros.
    destruct (zlt i i); [omega|].
    rewrite sublist_next with (i0 := i)(d := Vundef) by (auto; omega); simpl.
    rewrite sublist_next with (i0 := i)(d := Vundef) by (auto; omega); simpl.
    unfold atomic_loc_hist at 2; rewrite (atomic_loc_isptr _ (Znth i locs Vundef)); Intros.
    forward.
    forward.
    forward_call (AS_witness sh (Znth i locs Vundef) (Znth i ghosts Vundef) 0
      (loc_R (Znth i lg Vundef) gsh2 (Znth i lgl Vundef) gv2) (Znth i hists []) (Znth i vals 0)
      (ghost_snap (v + 1) gv2 * ghost_snap v (Znth i lg Vundef) * ghost_var gsh1 v (Znth i lgl Vundef))
      (ghost_snap (v + 1) gv2 * ghost_snap (v + 2) (Znth i lg Vundef) * ghost_var gsh1 (v + 2) (Znth i lgl Vundef))).
    { split; [|split; auto; apply Forall_Znth; auto; omega].
      apply AS_hist_spec; auto.
      repeat intro.
      unfold loc_R in *.
      erewrite exp_sepcon1, extract_nth_exists_in_SEP with (n := O); [|simpl; eauto].
      Intro ver; simpl.
      erewrite exp_sepcon1, extract_nth_exists_in_SEP with (n := O); [|simpl; eauto].
      Intro ver'; simpl.
      erewrite !sepcon_andp_prop', extract_prop_in_SEP with (n := O); [|simpl; eauto].
      Intros; simpl.
      rewrite <- !sepcon_assoc, !flatten_sepcon_in_SEP.
      gather_SEP 1 5.
      assert_PROP (ver = v).
      { go_lowerx; apply sepcon_derives_prop, ghost_var_inj; auto. }
      subst; erewrite ghost_var_share_join by eauto.
      apply ghost_var_update with (v'0 := v + 2).
      erewrite <- (ghost_var_share_join _ _ _ _ _ SH2).
      gather_SEP 4 1.
      apply snap_master_update' with (v'0 := v + 2); [omega|].
      gather_SEP 3 2; rewrite snap_snap_max.
      eapply semax_pre; [|eauto].
      go_lowerx.
      Exists (v + 2) (Z.max (v + 1) ver'); entailer!.
      split; [destruct (Z.max_spec (v + 1) ver') as [(? & ->) | (? & ->)]; auto|].
      rewrite round_up_max_distr; apply Zmax_bound_l.
      unfold round_up; replace (v mod 2) with 0; rewrite Hdirty; omega. }
    rewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := Vundef), map_app, sepcon_app
      by omega.
    rewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := Vundef), map_app, sepcon_app
      by omega.
    Intros h'; Exists (x ++ [h']); rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
    intros.
    erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    destruct (eq_dec i (Zlength x)).
    + subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
      destruct (zlt (Zlength x) (Zlength x + 1)); [|omega].
      rewrite app_Znth2, Zminus_diag, Znth_0_cons by omega.
      apply andp_right; auto.
      apply prop_right; auto.
    + rewrite upd_Znth_diff' by (rewrite ?Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      Intros.
      destruct (zlt i (Zlength x)), (zlt i (Zlength x + 1)); try omega.
      * rewrite app_Znth1 by auto.
        apply andp_right; auto.
        apply prop_right; auto.
      * apply andp_right; auto.
        apply prop_right; omega.
  - Intros hists'.
    unfold atomic_loc_hist at 1; Intros.
    rewrite !sublist_nil, !sublist_same by auto.
    assert ((v + 2) mod 2 = 0) as Hclean.
    { rewrite Zplus_mod.
      replace (v mod 2) with 0; rewrite Z_mod_same_full, Zmod_0_l; auto. }
    forward_call (AS_witness sh version gv 0 (ver_R gv2 gsh2 gv' lg) hv2 (v + 2)
      (ghost_snap (v + 1) gv2 * ghost_var gsh1 (v + 1) gv' * fold_right sepcon emp (map (ghost_snap (v + 2)) lg))
      (ghost_snap (v + 2) gv2 * ghost_var gsh1 (v + 2) gv' * fold_right sepcon emp (map (ghost_snap (v + 2)) lg))).
    { split; [|split; auto].
      apply AS_hist_spec; auto.
      repeat intro.
      unfold ver_R in *.
      rewrite <- !sepcon_assoc, !flatten_sepcon_in_SEP.
      gather_SEP 4 1.
      assert_PROP (v + 1 = v').
      { go_lowerx; apply sepcon_derives_prop, ghost_var_inj; auto. }
      subst v'; erewrite ghost_var_share_join by eauto.
      apply ghost_var_update with (v' := v + 2).
      erewrite <- (ghost_var_share_join _ _ _ _ _ SH2).
      gather_SEP 3 1.
      apply snap_master_update' with (v' := v + 2); [omega|].
      gather_SEP 3 2.
      apply snaps_snaps_max; rewrite Z.max_l by (unfold round_down; omega).
      eapply semax_pre; [|eauto].
      unfold round_down; rewrite Hclean, Z.sub_0_r.
      go_lowerx; entailer!.
      { admit. (* version stays in range *) } }
    Intros hv3.
    forward.
    Exists hv3 hists'; unfold atomic_loc_hist at 2; entailer!.
    + eapply add_events_trans with (le := [_; _]); eauto.
    + apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      Intros; destruct (zlt i 8); [|rewrite Zlength_upto in *; simpl in *; omega].
      apply andp_right; auto.
      apply prop_right; auto.
Admitted.

(*(* Steps to linearizability:
   A single thread sees a sequence of reads and writes.
   The join of a collection of sequences of reads and writes, if consistent, is equivalent to a sequence of reads
   and writes. *)
Inductive lin_op := Read (v : Z) (vals : list Z) | Write (v : Z) (vals : list Z).

Fixpoint do_op h1 op h2 :=
  match op with
  | Read v vals => Z.testbit v 0 = false /\ exists failvs, Forall repable_signed failvs /\
      add_events (fst h1) (make_loads (failvs ++ [v; v])) (fst h2) /\ exists loops,
      forall i, 0 <= i < 8 -> exists fails, Zlength fails = loops /\
        add_events (Znth i (snd h1) []) (make_loads (fails ++ [Znth i vals 0])) (Znth i (snd h2) [])
  | Write v vals =>
      add_events (fst h1) [Load (vint v); Store (vint (Z.lor v 1)); Store (vint (v + 2))] (fst h2) /\
      forall i, 0 <= i < 8 -> add_events (Znth i (snd h1) []) [Store (vint (Znth i vals 0))] (Znth i (snd h2) [])
  end.

Inductive do_ops h : list lin_op -> hist * list hist -> Prop :=
| do_ops_nil : do_ops h [] h
| do_ops_cons : forall a la h' h'' (Hh' : do_op h a h') (Hh'' : do_ops h' la h''), do_ops h (a :: la) h''.

(* For now, we're relying on there being only one writer. *)
Lemma full_hist_writes : forall w lr v (Hv : full_hist' (concat (w :: lr)) v) (Hw : NoDup (map fst w))
  (Hr : Forall (fun h => exists lv, map snd h = make_loads lv) lr), full_hist' w v.
Proof.
  intros; eapply full_hist'_drop; eauto.
  { simpl; apply incl_appl, incl_refl. }
  simpl; intros ?? Hin Hout ??.
  rewrite in_app in Hin; destruct Hin as [? | Hin]; [contradiction|].
  rewrite in_concat in Hin; destruct Hin as (h & ? & ?).
  rewrite Forall_forall in Hr; exploit Hr; eauto; intros (? & Hsnd).
  assert (In e (map snd h)) as He by (rewrite in_map_iff; do 2 eexists; eauto; auto).
  unfold make_loads in Hsnd; rewrite Hsnd, in_map_iff in He; destruct He as (? & ? & ?); subst; contradiction.
Qed.

Definition empty_state := ([] : hist, repeat ([] : hist) 8).

Definition make_reads le := map (fun '(v, lv) => Read v lv) le.
Definition make_writes le := map (fun '(v, lv) => Write v lv) le.

Lemma read_written : forall w lr writes reads v vals (Hw : do_ops empty_state (make_writes writes) w)
  (Hlr : Forall2 (fun rs r => do_ops empty_state (make_reads rs) r) reads lr)
  (Hfullv : full_hist' (concat (map fst (w :: lr))) v)
  (Hvals : Zlength vals = 8) (Hfullvs : forall i, 0 <= i < 8 ->
    full_hist' (concat (map (fun l => Znth i (snd l) []) (w :: lr))) (vint (Znth i vals 0))),
  incl (concat reads) writes.
Proof.
  repeat intro.
  rewrite in_concat in H; destruct H as (r & Hr & Hin).
  (* We actually need the memory model here. Since there's no connection between histories on different
     locations, we don't know that the write of the version number happens before the writes to the bodies.
     How can we recover this information? With a ghost variable marking the version number on each location? *)
  *)