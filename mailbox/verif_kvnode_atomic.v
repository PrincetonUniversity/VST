Require Import veric.rmaps.
Require Import progs.ghost.
Require Import mailbox.general_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.kvnode_atomic.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition load_SC_spec := DECLARE _load_SC load_SC_spec.
Definition store_SC_spec := DECLARE _store_SC store_SC_spec.

Definition tnode := Tstruct _node noattr.

Opaque upto.

(* Store a map from known version numbers to values. *)
Instance version_PCM : PCM (Z -> option Z) := { join a b c :=
  forall v1 v2, c v1 = Some v2 <-> a v1 = Some v2 \/ b v1 = Some v2 }.
Proof.
  - intros.
    rewrite Hjoin; tauto.
  - intros.
    exists (fun v => match b v with Some v' => Some v' | None => d v end).
    assert (forall v v1 v2, b v = Some v1 -> d v = Some v2 -> v1 = v2) as Hbd.
    { intros ??? Hb Hd.
      specialize (Hjoin1 v v1).
      destruct Hjoin1 as (_ & Hc); lapply Hc; auto; intro Hc'.
      generalize (Hjoin2 v v1); intros (_ & He); lapply He; auto; intro He1.
      specialize (Hjoin2 v v2); destruct Hjoin2 as (_ & Hjoin2); lapply Hjoin2; auto; intro He2.
      rewrite He1 in He2; inv He2; auto. }
    split; intros; specialize (Hjoin1 v1 v2); specialize (Hjoin2 v1 v2).
    + destruct (b v1) eqn: Hb; split; auto; intros [|]; auto; try discriminate.
      exploit Hbd; eauto.
    + rewrite Hjoin2, Hjoin1.
      destruct (b v1) eqn: Hb; split; auto; intros [|]; auto.
      * specialize (Hbd _ _ _ Hb H); subst; auto.
      * destruct H; auto; discriminate.
Defined.

Instance version_order : PCM_order (fun a b => forall v1 v2, a v1 = Some v2 -> b v1 = Some v2).
Proof.
  constructor; simpl; intros; eauto.
  - split; intros; specialize (H v1 v2); rewrite H; auto.
  - split; auto; intros [|]; auto.
Defined.

Definition gsh1 := fst (Share.split Tsh).
Definition gsh2 := snd (Share.split Tsh).

Lemma readable_gsh1 : readable_share gsh1.
Proof.
  apply slice.split_YES_ok1; auto.
Qed.

Lemma readable_gsh2 : readable_share gsh2.
Proof.
  apply slice.split_YES_ok2; auto.
Qed.

Lemma gsh1_gsh2_join : sepalg.join gsh1 gsh2 Tsh.
Proof.
  apply split_join; unfold gsh1, gsh2; destruct (Share.split Tsh); auto.
Qed.

Definition node_entry v vs locs lg lg' i := EX v' : Z, EX log : Z -> option Z, EX d : Z,
  !!(repable_signed d /\ (if Z.even v then v' = v /\ d = Znth i vs 0 else v' >= v - 1) /\ log v' = Some d /\
     forall v2, v' < v2 -> log v2 = None) && ghost_master log (Znth i lg Vundef) *
     ghost_var gsh2 (v', d) (Znth i lg' Vundef) * data_at Tsh tint (vint d) (Znth i locs Vundef).

Definition node_state v vs version locs g g' lg lg' := EX v' : Z, !!(repable_signed v' /\ Z.even v = true /\
  Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = v \/ v' = v + 1)) &&
  ghost_master v' g * ghost_var gsh2 v' g' * data_at Tsh tint (vint v') version *
  fold_right sepcon emp (map (node_entry v' vs locs lg lg') (upto (length locs))).

Definition singleton (v1 v2 v : Z) := if eq_dec v v1 then Some v2 else None.

Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * val * list val * val * val * list val * list val * Z * list Z)) (0, [])
  [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, version, locs, g, g', lg, lg', v0, vs0) => temp _n n;
   fun _ '(n, out, sh, version, locs, g, g', lg, lg', v0, vs0) => temp _out out]
  (fun _ '(n, out, sh, version, locs, g, g', lg, lg', v0, vs0) => !!(readable_share sh /\ isptr version /\
     Forall isptr locs /\ Zlength locs = 8) &&
   data_at sh tnode (version, locs) n * data_at_ Tsh (tarray tint 8) out *
   ghost_snap v0 g * fold_right sepcon emp (map (fun i => ghost_snap v0 g *
     ghost_snap (singleton v0 (Znth i vs0 0)) (Znth i lg Vundef)) (upto (Z.to_nat 8))))
  (fun _ '(n, out, sh, version, locs, g, g', lg, lg', v0, vs0) '(v, vs) =>
   node_state v vs version locs g g' lg lg')
  tt []
  (fun _ '(n, out, sh, version, locs, g, g', lg, lg', v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vs) out *
   ghost_snap v g * fold_right sepcon emp (map (fun i => ghost_snap v g *
     ghost_snap (singleton v (Znth i vs 0)) (Znth i lg Vundef)) (upto (Z.to_nat 8))))
  (fun _ '(n, out, sh, version, locs, g, g', lg, lg', v0, vs0) '(v, vs) _ => !!(Z.even v = true) &&
   node_state v vs version locs g g' lg lg')
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

(* For now, we guarantee only one writer by using a ghost variable as a write permission. *)
Program Definition write_spec := DECLARE _write atomic_spec
  (ConstType (val * val * share * val * list val * list Z * val * val * list val * list val * Z * list Z)) (0, [])
  [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, version, locs, vals, g, g', lg, lg', v0, vs0) => temp _n n;
   fun _ '(n, input, sh, version, locs, vals, g, g', lg, lg', v0, vs0) => temp _in input]
  (fun _ '(n, input, sh, version, locs, vals, g, g', lg, lg', v0, vs0) => !!(readable_share sh /\ isptr version /\
     Forall isptr locs /\ Zlength locs = 8 /\ Forall repable_signed vals /\ Z.even v0 = true) &&
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input *
   ghost_var gsh1 v0 g' * fold_right sepcon emp (map (fun i =>
     ghost_var gsh1 (v0, Znth i vs0 0) (Znth i lg' Vundef)) (upto (Z.to_nat 8))))
  (fun _ '(n, input, sh, version, locs, vals, g, g', lg, lg', v0, vs0) '(v, vs) =>
   node_state v vs version locs g g' lg lg')
  tt []
  (fun _ '(n, input, sh, version, locs, vals, g, g', lg, lg', v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input *
   ghost_var gsh1 (v0 + 2) g' * fold_right sepcon emp (map (fun i =>
     ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef)) (upto (Z.to_nat 8))))
  (fun _ '(n, input, sh, version, locs, vals, g, g', lg, lg', v0, vs0) '(v, vs) _ =>
   (* !!(v = v0 /\ vs = vs0) && *) node_state (v0 + 2) vals version locs g g' lg lg')
  _ _ _ _ _ _.
(* We can prove the stronger postcondition, but the writer doesn't really care what it overwrites. *)
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

Lemma singleton_snap : forall (x y : Z -> option Z) p v1 v2, y v1 = Some v2 ->
  view_shift (ghost_snap x p * ghost_master y p) (ghost_snap (singleton v1 v2) p * ghost_master y p).
Proof.
  intros.
  rewrite !snap_master_join; view_shift_intros.
  etransitivity.
  - apply ghost_update with (g' := (Some (singleton v1 v2), Some y)).
    intros (cs, cm) ((d, dm) & Hjoin & [[]|[]] & Hy); [simpl in *; subst | discriminate].
    unfold lift_ord in *.
    destruct cs, d; try contradiction.
    + exists (Some (fun v => if eq_dec v v1 then Some v2 else o v), Some y); simpl.
      split; [|split; auto].
      * unfold singleton; split; [if_tac; auto|].
        if_tac; intros [|]; auto; try discriminate.
        subst; transitivity (y v1); auto.
        apply Hy; rewrite Hjoin; auto.
      * intros ?? Heq.
        destruct (eq_dec _ _); [inv Heq; auto|].
        apply Hy; rewrite Hjoin; auto.
    + exists (Some (singleton v1 v2), Some y); simpl; split; auto; split; auto.
      unfold singleton; intros ?? Heq.
      destruct (eq_dec _ _); inv Heq; auto.
  - apply derives_view_shift; entailer!.
    unfold singleton; intros ?? Heq.
    destruct (eq_dec _ _); inv Heq; auto.
Qed.

(* up *)
Lemma wand_eq : forall P Q R, P = Q * R -> P = Q * (Q -* P).
Proof.
  intros.
  apply mpred_ext, modus_ponens_wand.
  subst; cancel.
  rewrite <- wand_sepcon_adjoint; auto.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((((n, out), sh), version), locs), g), g'), lg), lg'), v0), vs0); Intros.
  destruct H as (HP0 & HP & HQ).
  apply semax_pre with (P' := PROP ( )
    LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ Tsh (tarray tint 8) out;
         EX v0 : Z, ghost_snap v0 g;
         fold_right sepcon emp (map (fun i => EX v0 : Z, ghost_snap v0 g *
           EX l : Z -> option Z, ghost_snap l (Znth i lg Vundef)) (upto 8));
         fold_right sepcon emp (map (fun p : val => invariant (II p) p) lI); P)).
  { Exists v0; entailer!.
    apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
    rewrite Zlength_upto in *.
    erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto; auto; omega).
    Exists v0 (singleton v0 (Znth i vs0 0)); auto. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  Intro v1.
  repeat forward.
  rewrite map_map in HP, HQ.
  forward_call (version, P * ghost_snap v1 g, lI, II,
    fun sh v' => !!(sh = Tsh) && EX v : Z, EX vs : _, !!(Z.even v = true /\ Forall repable_signed vs /\
      Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = v \/ v' = v + 1)) && ghost_master v' g *
      ghost_var gsh2 v' g' * fold_right sepcon emp (map (node_entry v' vs locs lg lg') (upto (length locs))) *
      R (v, vs) * ghost_snap v1 g,
    fun v : Z => P * ghost_snap v g).
  { split.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
      apply derives_view_shift.
      Intro x; destruct x as (v, vs).
      unfold node_state; Intro v'.
      Exists Tsh v' v vs; entailer!.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
      view_shift_intro v2; view_shift_intro vs; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ _)), (sepcon_comm _ (ghost_snap _ _)).
      rewrite <- !sepcon_assoc, 3sepcon_assoc.
      etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
      { apply snap_master_update' with (v' := v); omega. }
      apply derives_view_shift.
      Exists (v2, vs); unfold node_state; Exists v; entailer!. }
  clear v1; Intros v1.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP (Z.testbit v1 0 = false) (LOCALx Q (SEPx R))) end.
  { eapply semax_pre; [|apply semax_continue].
    unfold POSTCONDITION, abbreviate, overridePost.
    destruct (eq_dec EK_continue EK_normal); [discriminate|].
    unfold loop1_ret_assert.
    Exists v1; entailer!. }
  { forward.
    entailer!.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_odd in *.
    destruct (Z.odd v1); auto; discriminate. }
  Intros.
  forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i)
    LOCAL (temp _snap (vint v1); temp _ver version; temp _n n; temp _out out)
    SEP (fold_right sepcon emp (map (fun p : val => invariant (II p) p) lI);
         P; ghost_snap v1 g; @data_at CompSpecs sh tnode (version, locs) n;
         data_at Tsh (tarray tint 8) (map (fun x => vint x) vals ++ repeat Vundef (Z.to_nat (8 - i))) out;
         EX vers : list (Z * Z), !!(Zlength vers = i /\
           Forall (fun '(v, v') => v1 <= v /\ if Z.even v then v' = v else True) vers) &&
           fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers (0, 0))) g *
             ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef))
             (sublist 0 i (upto 8)));
         fold_right sepcon emp (map (fun i => EX v2 : Z, ghost_snap v2 g *
           (EX l : Z -> option Z, ghost_snap l (Znth i lg Vundef))) (sublist i 8 (upto 8))))).
  { Exists (@nil Z) (@nil (Z * Z)); entailer!. }
  - Intros vers.
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto; auto; simpl; omega); simpl.
    Intros v' l'.
    forward_call (Znth i locs Vundef, P * ghost_snap v1 g * ghost_snap v' g * ghost_snap l' (Znth i lg Vundef),
      lI, II,
      fun sh v => !!(sh = Tsh) && EX ver : Z, EX vs : _, EX ver' : Z, EX v'' : _, EX log : _,
        !!(repable_signed ver' /\ Z.even ver = true /\ Forall repable_signed vs /\ Zlength vs = Zlength locs /\
           Zlength lg = Zlength locs /\ (ver' = ver \/ ver' = ver + 1) /\
           (if Z.even ver' then v'' = ver' /\ v = Znth i vs 0 else v'' >= ver' - 1) /\
           log v'' = Some v /\ forall v2, v'' < v2 -> log v2 = None) && ghost_master ver' g *
           ghost_var gsh2 ver' g' * data_at Tsh tint (vint ver') version *
           ghost_master log (Znth i lg Vundef) * ghost_var gsh2 (v'', v) (Znth i lg' Vundef) *
           fold_right sepcon emp (upd_Znth i (map (node_entry ver' vs locs lg lg') (upto (length locs))) emp) *
        R (ver, vs) * ghost_snap v1 g * ghost_snap v' g * ghost_snap l' (Znth i lg Vundef),
      fun v : Z => P * EX vi : Z, EX v'' : Z, !!(v1 <= vi /\ if Z.even vi then v'' = vi else True) &&
        ghost_snap v1 g * ghost_snap vi g * ghost_snap (singleton v'' v) (Znth i lg Vundef)).
(* A common case is to do no view shifts in the first part. In this case, maybe we can provide a magic-wand
   mpred for P', and prove the magic-wand equivalence separately using wand_sepcon_adjoint. *)
     { split.
      + intros.
        rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
        apply derives_view_shift.
        Intro s; destruct s as (v, vs).
        unfold node_state; Intros ver'.
        rewrite extract_nth_sepcon with (i := i)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry; Intros v'' log d.
        Exists Tsh d v vs ver' v'' log; entailer!.
      + intros.
        rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
        view_shift_intro ver; view_shift_intro vs; view_shift_intro ver'; view_shift_intro v'';
          view_shift_intro log; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ g)), (sepcon_comm _ (ghost_snap v' g)).
        rewrite <- !sepcon_assoc, 8sepcon_assoc.
        etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
        { apply snap_master_update' with (v'0 := ver'); omega. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ (Znth i lg Vundef))),
          (sepcon_comm _ (ghost_snap _ (Znth i lg Vundef))).
        rewrite <- !sepcon_assoc, 8sepcon_assoc.
        etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
        { apply singleton_snap; eauto. }
        apply derives_view_shift.
        assert_PROP (v1 <= ver').
        { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ g)), (sepcon_comm _ (ghost_snap v1 g)).
          rewrite <- !sepcon_assoc, snap_master_join'; entailer!. }
        Exists (ver, vs) ver' v''; unfold node_state; Exists ver'; entailer!.
        { if_tac; tauto. }
        rewrite extract_nth_sepcon with (i := Zlength x)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; omega).
        unfold node_entry; Exists v'' log v; entailer!. }
      Intros vali vi v''.
      forward.
      Exists (x ++ [vali]) (vers ++ [(vi, v'')]); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
      rewrite upd_init, map_app, <- app_assoc by (rewrite ?Zlength_map; omega); entailer!.
      { rewrite Forall_app; repeat constructor; auto. }
      rewrite sublist_split with (mid := Zlength x)(hi := Zlength x + 1) by (rewrite ?Zlength_upto; simpl; omega).
      erewrite sublist_len_1, Znth_upto by (rewrite ?Zlength_upto; simpl; omega).
      rewrite map_app, sepcon_app; simpl.
      rewrite !app_Znth2 by omega.
      replace (Zlength vers) with (Zlength x); rewrite Zminus_diag, !Znth_0_cons; simpl; cancel.
      apply sepcon_list_derives; rewrite !Zlength_map; auto.
      intros ? Hi; erewrite !Znth_map by auto.
      rewrite Zlength_sublist in Hi by (rewrite ?Zlength_upto; simpl; omega).
      rewrite !Znth_sublist, !Znth_upto by (simpl; omega).
      rewrite !app_Znth1 by omega; auto.
  - Intros vals vers.
    rewrite app_nil_r, sublist_nil, sublist_same by auto; simpl.
    rewrite Z.bit0_odd, Zodd_even_bool in *; destruct (Z.even v1) eqn: Heven; try discriminate.
    forward_call (version, P * ghost_snap v1 g * fold_right sepcon emp (map (fun i =>
      ghost_snap (fst (Znth i vers (0, 0))) g *
      ghost_snap (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)) (Znth i lg Vundef)) (upto 8)), lI, II,
      fun sh v' => !!(sh = Tsh) && EX v : Z, EX vs : _, !!(Z.even v = true /\ Forall repable_signed vs /\
        Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = v \/ v' = v + 1)) &&
        ghost_master v' g * ghost_var gsh2 v' g' *
        fold_right sepcon emp (map (node_entry v' vs locs lg lg') (upto (length locs))) * R (v, vs) *
        ghost_snap v1 g * fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers (0, 0))) g *
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
        unfold node_state; Intro v'.
        Exists Tsh v' v vs; entailer!.
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
            rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ _)), (sepcon_comm _ (ghost_snap (fst _) g)).
            rewrite <- !sepcon_assoc, snap_master_join'.
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
            subst; rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ (Znth i lg Vundef))),
              (sepcon_comm _ (ghost_snap _ (Znth i lg Vundef))).
            rewrite <- !sepcon_assoc, snap_master_join; simpl; Intros; apply prop_right.
            unfold singleton in *.
            match goal with H : forall v2 _, _ -> _ |- _ => specialize (H ver); rewrite eq_dec_refl in H;
              specialize (H _ eq_refl); rewrite H in *; congruence end. }
          subst; unfold node_state; Exists ver; entailer!.
        * rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
          view_shift_intro ver; view_shift_intro vs; view_shift_intros.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ _)), (sepcon_comm _ (ghost_snap _ _)).
          rewrite <- !sepcon_assoc, 4sepcon_assoc.
          etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
          { apply snap_master_update' with (v' := v); omega. }
          apply derives_view_shift.
          Exists (ver, vs); unfold node_state; Exists v; entailer!. }
    Intros v2.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v2 <> v1) (LOCALx Q (SEPx R))) end.
    + subst; rewrite eq_dec_refl in *.
      forward.
      Exists tt (v1, vals); entailer!.
      erewrite map_ext_in; eauto.
      intros a ?; rewrite In_upto in *; simpl in *.
      match goal with H : if eq_dec v1 v1 then _ else _ |- _ => rewrite eq_dec_refl in H;
        apply Forall_Znth with (i := a)(d := (0, 0)) in H; [|omega] end.
      destruct (Znth a vers (0, 0)); match goal with H : _ = _ /\ _ = _ |- _ => destruct H; subst; auto end.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; Exists v2; if_tac; [contradiction | entailer!].
      apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      Exists (fst (Znth i vers (0, 0))) (singleton (snd (Znth i vers (0, 0))) (Znth i vals 0)); auto.
Qed.

Hint Resolve readable_gsh1 readable_gsh2 gsh1_gsh2_join.

Lemma dirty_entry : forall v vs locs lg lg' i, Z.even v = true ->
  node_entry v vs locs lg lg' i |-- node_entry (v + 1) vs locs lg lg' i.
Proof.
  intros; unfold node_entry.
  Intros v' log d.
  rewrite H in *; match goal with H : _ /\ _ |- _ => destruct H end.
  Exists v log d; entailer!.
  rewrite Z.even_add, H; simpl; omega.
Qed.

Lemma clean_entry : forall v vs locs lg lg' i vs', Z.even v = false ->
  ghost_var gsh1 (v + 1, Znth i vs' 0) (Znth i lg' Vundef) * node_entry v vs locs lg lg' i |--
  ghost_var gsh1 (v + 1, Znth i vs' 0) (Znth i lg' Vundef) * node_entry (v + 1) vs' locs lg lg' i.
Proof.
  intros; unfold node_entry.
  Intros v' log d; Exists (v + 1) log d.
  erewrite (sepcon_comm _ (ghost_var gsh2 _ _)), <- !sepcon_assoc, ghost_var_share_join' by eauto.
  Intros; match goal with H : (_, _) = (_, _) |- _ => inv H end.
  erewrite <- ghost_var_share_join by eauto; entailer!.
  rewrite Z.even_add, H; simpl; auto.
Qed.

Corollary clean_entries : forall v vs locs lg lg' vs', Z.even v = false ->
  fold_right sepcon emp (map (fun i => ghost_var gsh1 (v + 1, Znth i vs' 0) (Znth i lg' Vundef)) (upto 8)) *
  fold_right sepcon emp (map (node_entry v vs locs lg lg') (upto 8)) |--
  fold_right sepcon emp (map (fun i => ghost_var gsh1 (v + 1, Znth i vs' 0) (Znth i lg' Vundef)) (upto 8)) *
  fold_right sepcon emp (map (node_entry (v + 1) vs' locs lg lg') (upto 8)).
Proof.
  intros.
  rewrite <- !sepcon_map; apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
  erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
  apply clean_entry; auto.
Qed.

Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((((n, input), sh), version), locs), vals), g), g'), lg), lg'), v0), vs0); Intros.
  destruct H as (HP0 & HP & HQ).
  forward.
  rewrite map_map in HP, HQ.
  (* The ghost_var guarantees that no one else has changed the version. *)
  forward_call (version, P * ghost_var gsh1 v0 g', lI, II,
    fun sh v' => !!(sh = Tsh) && EX v : Z, EX vs : _, !!(repable_signed v' /\ Z.even v = true /\
      Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
      (v' = v \/ v' = v + 1)) && ghost_master v' g * ghost_var gsh2 v' g' * fold_right sepcon emp
        (map (node_entry v' vs locs lg lg') (upto (length locs))) * R (v, vs) * ghost_var gsh1 v0 g',
    fun v : Z => P * (!!(v = v0) && ghost_var gsh1 v0 g')).
  { split.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
      apply derives_view_shift.
      Intro x; destruct x as (v, vs).
      unfold node_state; Intros v'.
      Exists Tsh v' v vs; entailer!.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
      apply derives_view_shift; Intros v1 vs.
      assert_PROP (v0 = v).
      { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ _)), (sepcon_comm _ (ghost_var gsh1 _ _)).
        rewrite <- !sepcon_assoc, 3sepcon_assoc.
        apply sepcon_derives_prop, ghost_var_inj; auto. }
      Exists (v1, vs); unfold node_state; Exists v; entailer!. }
  Intros x; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call (version, v0 + 1, P * ghost_var gsh1 v0 g', lI, II,
    fun sh => !!(sh = Tsh) && EX v : Z, EX vs : _, EX v' : Z, !!(repable_signed v' /\ Z.even v = true /\
      Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
      (v' = v \/ v' = v + 1)) && ghost_master v' g * ghost_var gsh2 v' g' *
      fold_right sepcon emp (map (node_entry v' vs locs lg lg') (upto (length locs))) * R (v, vs) *
      ghost_var gsh1 v0 g',
    P * ghost_var gsh1 (v0 + 1) g').
  { split; [auto | split].
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
      apply derives_view_shift.
      Intros x; destruct x as (v, vs).
      unfold node_state; Intro v'.
      Exists Tsh v vs v'; entailer!.
    + intros.
      rewrite <- sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
      view_shift_intro v; view_shift_intro vs; view_shift_intro v'; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ _)), (sepcon_comm _ (ghost_var gsh1 _ _)).
      erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto; view_shift_intros.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
      { apply ghost_var_update with (v'0 := v0 + 1). }
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ _)), !sepcon_assoc.
      etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
      { apply (@master_update _ _ _ _ max_order _ (v0 + 1)); omega. }
      apply derives_view_shift.
      erewrite <- ghost_var_share_join by eauto.
      Exists (v, vs); unfold node_state.
      Exists (v' + 1); entailer!.
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
    SEP (fold_right sepcon emp (map (fun p : val => invariant (II p) p) lI); P;
    ghost_var gsh1 (v0 + 1) g'; @data_at CompSpecs sh tnode (version, locs) n;
    data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) input;
    fold_right sepcon emp (map (fun i => ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef))
      (sublist 0 i (upto 8)));
    fold_right sepcon emp (map (fun i => ghost_var gsh1 (v0, Znth i vs0 0) (Znth i lg' Vundef))
      (sublist i 8 (upto 8))))).
  { entailer!. }
  - (* loop body *)
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward.
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto; simpl; omega); simpl.
    rewrite Zlength_map in *.
    forward_call (Znth i locs Vundef, Znth i vals 0, P * ghost_var gsh1 (v0 + 1) g' *
      ghost_var gsh1 (v0, Znth i vs0 0) (Znth i lg' Vundef), lI, II,
      fun sh => !!(sh = Tsh) && EX ver : Z, EX vs : _, EX ver' : Z, EX v'' : _, EX log : _, EX d : Z,
        !!(repable_signed ver' /\ Z.even ver = true /\ Forall repable_signed vs /\ Zlength vs = Zlength locs /\
           Zlength lg = Zlength locs /\ (ver' = ver \/ ver' = ver + 1) /\
           (if Z.even ver' then v'' = ver' /\ d = Znth i vs 0 else v'' >= ver' - 1) /\ log v'' = Some d /\
           forall v2, v'' < v2 -> log v2 = None) && ghost_master ver' g * ghost_var gsh2 ver' g' *
        data_at Tsh tint (vint ver') version * ghost_master log (Znth i lg Vundef) *
        ghost_var gsh2 (v'', d) (Znth i lg' Vundef) * fold_right sepcon emp
          (upd_Znth i (map (node_entry ver' vs locs lg lg') (upto (length locs))) emp) *
        R (ver, vs) * ghost_var gsh1 (v0 + 1) g' * ghost_var gsh1 (v0, Znth i vs0 0) (Znth i lg' Vundef),
      P * ghost_var gsh1 (v0 + 1) g' * ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef)).
    { split; [apply Forall_Znth; auto; omega | split].
      + rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
        apply derives_view_shift.
        Intro x; destruct x as (v, vs).
        unfold node_state; Intro v'.
        rewrite extract_nth_sepcon with (i := i)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry; Intros v'' log d.
        Exists Tsh v vs v' v'' log d; entailer!.
      + intros.
        rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [|apply view_shift_sepcon; [apply HP | reflexivity]].
        view_shift_intro ver; view_shift_intro vs; view_shift_intro ver'; view_shift_intro v'';
          view_shift_intro log; view_shift_intro d; view_shift_intros.
        apply view_shift_assert with (PP := v0 + 1 = ver').
        { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g')), (sepcon_comm _ (ghost_var gsh1 _ g')).
          erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto; entailer!. }
        intro; subst.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ _)), (sepcon_comm _ (ghost_var gsh1 _ _)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto; view_shift_intros.
        match goal with H : _ = _ |- _ => inv H end.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
        { apply ghost_var_update with (v' := (v'' + 2, Znth i vals 0)). }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ _)), !sepcon_assoc.
        etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
        { apply (master_update _ (fun v => if eq_dec v (v'' + 2) then Some (Znth i vals 0) else log v)).
          intros; if_tac; auto; subst.
          match goal with H : forall v2, _ |- _ => rewrite (H (v'' + 2)) in *; [discriminate | omega] end. }
        apply derives_view_shift.
        erewrite <- ghost_var_share_join by eauto.
        Exists (ver, vs); unfold node_state.
        Exists (v'' + 1); rewrite extract_nth_sepcon with (i := i)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry; Exists (v'' + 2)
          (fun v => if eq_dec v (v'' + 2) then Some (Znth i vals 0) else log v) (Znth i vals 0); entailer!.
        rewrite eq_dec_refl; split; [|split; [|split; auto]].
        * apply Forall_Znth; auto; omega.
        * rewrite Z.even_add; simpl.
          replace (Z.even v'') with true; simpl; omega.
        * intros; if_tac; [omega|].
          match goal with H : forall v2, _ |- _ => apply H; omega end. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (auto; rewrite ?Zlength_upto; simpl; omega); entailer!.
  - rewrite !sublist_nil, !sublist_same by auto; simpl.
    assert (repable_signed (v0 + 2)) by admit. (* version stays in range *)
    forward_call (version, v0 + 2, P * ghost_var gsh1 (v0 + 1) g' * fold_right sepcon emp (map (fun i =>
      ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef)) (upto 8)), lI, II,
      fun sh => !!(sh = Tsh) && EX v : Z, EX vs : _, EX v' : Z, !!(repable_signed v' /\ Z.even v = true /\
        Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
        (v' = v \/ v' = v + 1)) && ghost_master v' g * ghost_var gsh2 v' g' *
        fold_right sepcon emp (map (node_entry v' vs locs lg lg') (upto (length locs))) * R (v, vs) *
        ghost_var gsh1 (v0 + 1) g' * fold_right sepcon emp (map (fun i =>
          ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef)) (upto 8)),
      EX v : Z, EX vs : list Z, Q (v, vs) tt * ghost_var gsh1 (v0 + 2) g' * fold_right sepcon emp (map (fun i =>
        ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef)) (upto 8))).
    { split; [auto | split].
      + intros.
        rewrite <- !sepcon_assoc, sepcon_assoc; etransitivity; [apply view_shift_sepcon; [apply HP | reflexivity]|].
        apply derives_view_shift.
        Intros x; destruct x as (v, vs).
        unfold node_state; Intro v'.
        Exists Tsh v vs v'; entailer!.
      + intros.
        view_shift_intro v; view_shift_intro vs; view_shift_intro v'; view_shift_intros.
        etransitivity; [|etransitivity; [apply view_shift_sepcon with (Q' :=
          ghost_var gsh1 (v0 + 2) g' * fold_right sepcon emp (map (fun i =>
            ghost_var gsh1 (v0 + 2, Znth i vals 0) (Znth i lg' Vundef)) (upto 8)));
          [apply (HQ (v, vs) tt) | reflexivity] | apply derives_view_shift; Exists v vs; entailer!]].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ _)), (sepcon_comm _ (ghost_var gsh1 _ _)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto; view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
        { apply ghost_var_update with (v'0 := v0 + 2). }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master _ _)), !sepcon_assoc.
        etransitivity; [apply view_shift_sepcon; [|reflexivity]|].
        { apply (@master_update _ _ _ _ max_order _ (v0 + 2)); omega. }
        apply derives_view_shift.
        erewrite <- ghost_var_share_join by eauto.
        unfold node_state; subst.
        Exists (v0 + 2); rewrite Zlength_map in *.
        Search Zlength length.
        replace (length locs) with (Z.to_nat 8) by (symmetry; rewrite <- Zlength_length; auto; computable).
        pose proof (clean_entries (v0 + 1) vs locs lg lg' vals) as Hclean.
        rewrite <- Z.add_assoc in Hclean; simpl in *.
        sep_apply Hclean.
        { rewrite Z.even_add; replace (Z.even v0) with true; auto. }
        entailer!.
        rewrite Z.even_add; replace (Z.even v0) with true; auto. }
    Intros s; destruct s as (v, vs).
    forward.
    Exists tt (v, vs); entailer!.
Admitted.
