Require Import VST.veric.rmaps.
Require Import VST.progs.ghosts.
Require Import atomics.SC_atomics.
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

Existing Instances map_PCM fmap_order.

Definition ghost_log := ghost_master (ORD := @fmap_order nat Z).
Definition ghost_lsnap := ghost_snap (ORD := @fmap_order nat Z).
Definition ghost_version := ghost_master (ORD := max_order).
Definition ghost_vsnap := ghost_snap (ORD := max_order).

Definition node_entry sh v vs locs lg i := EX v' : nat, EX log : nat -> option Z, EX d : Z,
  !!(repable_signed d /\ (if Nat.even v then v' = v /\ d = Znth i vs else (v' >= v - 1)%nat) /\ log_latest log v' d) &&
  ghost_log sh log (Znth i lg) * data_at sh tint (vint d) (Znth i locs).

Existing Instances nat_PCM max_order.

Definition node_state sh v vs version locs g lg := !!(repable_signed (Z.of_nat v) /\
    Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs) &&
  ghost_version sh v g * data_at sh tint (vint (Z.of_nat v)) version *
  fold_right sepcon emp (map (node_entry sh v vs locs lg) (upto (length locs))).

Definition node_inv v vs version locs g lg := EX v' : nat, !!(Nat.even v = true /\ (v' = v \/ v' = v + 1)%nat) &&
  node_state gsh2 v' vs version locs g lg.

Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * val * list val * gname * list gname * nat * list Z))
  [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) => temp _n n;
   fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) => temp _out out]
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) => !!(readable_share sh /\ isptr version /\
     Forall isptr locs /\ Zlength locs = 8) &&
   data_at sh tnode (version, locs) n * data_at_ Tsh (tarray tint 8) out)
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) '(v, vs) => node_inv v vs version locs g lg)
  tt []
  (fun _ '(n, out, sh, version, locs, g, lg, v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vs) out *
   node_inv v vs version locs g lg)
  (Empty_set _) (Full_set _) _ _ _ _ _.
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
  (ConstType (val * val * share * val * list val * list Z * gname * list gname * nat * list Z))
  [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) => temp _n n;
   fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) => temp _in input]
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) => !!(readable_share sh /\ isptr version /\
     Forall isptr locs /\ Zlength locs = 8 /\ Forall repable_signed vals /\ Nat.even v0 = true) &&
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input *
   node_state gsh1 v0 vs0 version locs g lg)
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) '(v, vs) => node_inv v vs version locs g lg)
  tt []
  (fun _ '(n, input, sh, version, locs, vals, g, lg, v0, vs0) '(v, vs) _ =>
   data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x => vint x) vals) input *
   node_state gsh1 (v0 + 2) vals version locs g lg * node_inv (v0 + 2) vals version locs g lg)
  (Empty_set _) (Full_set _) _ _ _ _ _.
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

Lemma singleton_snap : forall x p v1 v2, x v1 = Some v2 ->
  ghost_lsnap x p |-- |==> ghost_lsnap (singleton v1 v2) p.
Proof.
  intros.
  apply ghost_snap_forget.
  unfold singleton; intros ??; if_tac; intro X; inv X; auto.
Qed.

Lemma even_inj : forall n, Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n; auto.
  rewrite Nat2Z.inj_succ, Z.even_succ, Nat.even_succ.
  rewrite <- Z.negb_even, <- Nat.negb_even, IHn; reflexivity.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((n, out), sh), version), locs), g), lg), v0), vs0); Intros.
  unfold atomic_shift; Intros P.
  set (AS := _ -* _).
  forward_loop (PROP () LOCAL (temp _n n; temp _out out)
    SEP (|> P; AS && cored; data_at sh tnode (version, locs) n;
    data_at_ Tsh (tarray tint 8) out)).
  { entailer!. }
  repeat forward.
  replace_SEP 1 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
  forward_call (version, AS && cored * |> P, Full_set iname, Empty_set iname,
    fun sh v' => !!(sh = gsh2) && EX v : nat, EX vs : _, !!(Nat.even v = true /\ Forall repable_signed vs /\
      Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = Z.of_nat v \/ v' = Z.of_nat v + 1)) && ghost_version gsh2 (Z.to_nat v') g *
      fold_right sepcon emp (map (node_entry gsh2 (Z.to_nat v') vs locs lg) (upto (length locs))) *
      (node_inv v vs version locs g lg -* |={Empty_set iname,Full_set iname}=> |> P),
      fun v : Z => |> P * ghost_vsnap (Z.to_nat v) g, inv_names).
  { cancel.
    rewrite <- emp_sepcon at 1.
    apply sepcon_derives; [|cancel].
    rewrite <- emp_sepcon at 1; apply sepcon_derives.
    + rewrite <- wand_sepcon_adjoint, emp_sepcon.
      unfold AS.
      rewrite sepcon_comm.
      eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
      eapply derives_trans; [apply modus_ponens_wand | apply fupd_mono].
      Intros x; destruct x as (v, vs).
      eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
      unfold node_inv, node_state; Intro v'.
      Exists gsh2 (Z.of_nat v') v vs; entailer!.
      rewrite Nat2Z.id; entailer!.
    + apply allp_right; intro sh1.
      apply allp_right; intro v1.
      rewrite <- wand_sepcon_adjoint, emp_sepcon.
      Intros v2 vs.
      rewrite sepcon_comm, !sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply make_snap|].
      eapply derives_trans; [apply bupd_frame_r|].
      apply fupd_bupd, bupd_mono.
      eapply derives_trans, fupd_frame_r.
      rewrite !sepcon_assoc, sepcon_comm; apply sepcon_derives; [|apply derives_refl].
      rewrite <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc.
      apply modus_ponens_wand'.
      unfold node_inv, node_state.
      Exists (Z.to_nat v1); entailer!.
      { destruct H9; subst; try rep_omega.
        rewrite Z2Nat.inj_add; try omega.
        rewrite Nat2Z.id; simpl; omega. }
      rewrite Z2Nat.id by omega.
      rewrite sepcon_comm; apply derives_refl. }
  Intros v1.
  forward_if (Z.testbit v1 0 = false).
  { viewshift_SEP 1 emp.
    { go_lower.
      apply own_dealloc. }
    forward.
    entailer!. }
  { forward.
    entailer!.
    rewrite Z.bit0_odd.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_odd in *.
    destruct (Z.odd v1); auto; discriminate. }
  Intros.
  forward_for_simple_bound 8 (@exp (environ -> mpred) _ Z (fun i => @exp (environ -> mpred) _ (list Z) (fun vals => PROP (Zlength vals = i)
    LOCAL (temp _snap (vint v1); temp _ver version; temp _n n; temp _out out)
    SEP (|> P; ghost_vsnap (Z.to_nat v1) g; AS && cored; @data_at CompSpecs sh tnode (version, locs) n;
         data_at Tsh (tarray tint 8) (map (fun x => vint x) vals ++ repeat Vundef (Z.to_nat (8 - i))) out;
         EX vers : list (nat * nat), !!(Zlength vers = i /\
           Forall (fun '(v, v') => Z.to_nat v1 <= v /\ if Nat.even v then v' = v else True)%nat vers) &&
           fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers)) g *
             ghost_lsnap (singleton (snd (Znth i vers)) (Znth i vals)) (Znth i lg))
             (sublist 0 i (upto 8))))))).
  { Exists (@nil Z) (@nil (nat * nat)); rewrite !sepcon_map; entailer!.
    apply data_at__data_at; auto. }
  - Intros vers; rewrite !sepcon_map; Intros.
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    replace_SEP 2 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
    forward_call (Znth i locs, AS && cored * |> P * ghost_vsnap (Z.to_nat v1) g,
      Full_set iname, Empty_set iname,
      fun sh v => !!(sh = gsh2) && EX ver : nat, EX vs : _, EX ver' : nat, EX v'' : nat, EX log : _,
        !!(repable_signed (Z.of_nat ver') /\ Nat.even ver = true /\ Forall repable_signed vs /\ Zlength vs = Zlength locs /\
           Zlength lg = Zlength locs /\ (ver' = ver \/ ver' = ver + 1)%nat /\
           (if Nat.even ver' then v'' = ver' /\ v = Znth i vs else v'' >= ver' - 1)%nat /\ log_latest log v'' v) &&
           ghost_version gsh2 ver' g * data_at gsh2 tint (vint (Z.of_nat ver')) version * ghost_log gsh2 log (Znth i lg) *
           fold_right sepcon emp (upd_Znth i (map (node_entry gsh2 ver' vs locs lg) (upto (length locs))) emp) *
        (node_inv ver vs version locs g lg -* |={Empty_set iname,Full_set iname}=> |> P) * ghost_vsnap (Z.to_nat v1) g,
      fun v : Z => |> P * EX vi : nat, EX v'' : nat, !!(Z.to_nat v1 <= vi /\ if Nat.even vi then v'' = vi else True)%nat &&
        ghost_vsnap (Z.to_nat v1) g * ghost_vsnap vi g * ghost_lsnap (singleton v'' v) (Znth i lg), inv_names).
     { cancel.
      rewrite <- emp_sepcon at 1.
      apply sepcon_derives; [|cancel].
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      + rewrite <- wand_sepcon_adjoint, emp_sepcon.
        rewrite (sepcon_comm _ (|> P)).
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
        eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
        Intros x; destruct x as (v, vs).
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
        unfold node_inv, node_state; Intros ver'.
        rewrite extract_nth_sepcon with (i := i)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry; Intros v'' log d.
        Exists gsh2 d v vs ver' v'' log; entailer!.
      + apply allp_right; intro sh1.
        apply allp_right; intro d1.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        Intros ver vs ver' v'' log.
        unfold ghost_version; sep_apply make_snap.
        eapply derives_trans; [apply bupd_frame_r|].
        apply fupd_bupd, bupd_mono.
        unfold ghost_log; sep_apply (make_snap(ORD := @fmap_order nat Z)).
        eapply derives_trans; [apply bupd_frame_r|].
        apply fupd_bupd, bupd_mono.
        fold (ghost_lsnap log (Znth i lg)).
        rewrite sepcon_assoc; eapply derives_trans; [apply sepcon_derives, derives_refl|].
        { match goal with H : log_latest _ _ _ |- _ => destruct H end.
          apply singleton_snap; eauto. }
        eapply derives_trans; [apply bupd_frame_r|].
        apply fupd_bupd, bupd_mono.
        eapply derives_trans, fupd_frame_r.
        assert_PROP (Z.to_nat v1 <= ver')%nat.
        { unfold ghost_vsnap; sep_apply (snap_master_join (Z.to_nat v1)); auto; entailer!. }
        Exists ver' v''; entailer!.
        { simple_if_tac; tauto. }
        rewrite (sepcon_comm _ (ghost_snap _ g)), !sepcon_assoc, sepcon_comm; apply sepcon_derives, derives_refl.
        rewrite <- !sepcon_assoc; apply modus_ponens_wand'.
         unfold node_inv, node_state; Exists ver'; entailer!.
        rewrite extract_nth_sepcon with (i := Zlength vals)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; omega).
        unfold node_entry; Exists v'' log d1; unfold share; entailer!.
        rewrite sepcon_comm; apply derives_refl. }
      Intros vali vi v''.
      forward.
      Exists (vals ++ [vali]) (vers ++ [(vi, v'')]); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
      rewrite upd_init, map_app, <- app_assoc, !sepcon_map by (rewrite ?Zlength_map; omega); entailer!.
      { rewrite Forall_app; repeat constructor; auto. }
      rewrite sublist_split with (mid := Zlength vals)(hi := Zlength vals + 1) by (rewrite ?Zlength_upto; simpl; omega).
      erewrite sublist_len_1, Znth_upto by (rewrite ?Zlength_upto; simpl; omega).
      rewrite !map_app, !sepcon_app; simpl.
      rewrite !app_Znth2 by omega.
      replace (Zlength vers) with (Zlength vals); rewrite Zminus_diag, !Znth_0_cons; simpl; cancel.
      rewrite (sepcon_comm _ (ghost_snap _ _)), !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
      rewrite <- !sepcon_map; apply sepcon_list_derives; rewrite !Zlength_map; auto.
      intros ? Hi; erewrite !Znth_map by auto.
      rewrite Zlength_sublist in Hi by (rewrite ?Zlength_upto; simpl; omega).
      rewrite !Znth_sublist, !Znth_upto by (simpl; omega).
      rewrite !app_Znth1 by omega; auto.
  - Intros vals vers.
    rewrite app_nil_r, sublist_same by auto; simpl.
    rewrite Z.bit0_odd, Zodd_even_bool in *; destruct (Z.even v1) eqn: Heven; try discriminate.
    replace_SEP 2 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
    forward_call (version, AS && cored * |> P * ghost_vsnap (Z.to_nat v1) g * fold_right sepcon emp (map (fun i =>
      ghost_vsnap (fst (Znth i vers)) g * ghost_lsnap (singleton (snd (Znth i vers)) (Znth i vals)) (Znth i lg)) (upto 8)) *
      data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) out,
      Full_set iname, Empty_set iname,
      fun sh' v' => !!(sh' = gsh2) && EX v : nat, EX vs : _, !!(Nat.even v = true /\ Forall repable_signed vs /\
        Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\ (v' = Z.of_nat v \/ v' = Z.of_nat v + 1)) &&
        ghost_version gsh2 (Z.to_nat v') g * fold_right sepcon emp (map (node_entry gsh2 (Z.to_nat v') vs locs lg) (upto (length locs))) *
        data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) out *
        ((node_inv v vs version locs g lg -* |={Empty_set iname,Full_set iname}=> |> P) &&
         (ALL y : unit, (data_at sh tnode (version, locs) n *
                data_at Tsh (tarray tint 8) (map (fun x0 : Z => vint x0) vs) out *
                node_inv v vs version locs g lg) -* |={ Empty_set iname, Full_set iname }=> Q y)) * ghost_vsnap (Z.to_nat v1) g * fold_right sepcon emp (map (fun i => ghost_vsnap (fst (Znth i vers)) g *
          ghost_lsnap (singleton (snd (Znth i vers)) (Znth i vals)) (Znth i lg)) (upto 8)),
      fun v : Z => (if eq_dec v v1 then Q tt else |> P *
          data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) out) *
        (!!(if eq_dec v v1 then Forall (fun '(vi, v') => vi = Z.to_nat v1 /\ v' = Z.to_nat v1) vers else True) &&
        ghost_vsnap (Z.to_nat v) g * fold_right sepcon emp (map (fun i => ghost_snap (fst (Znth i vers)) g *
          ghost_lsnap (singleton (snd (Znth i vers)) (Znth i vals)) (Znth i lg)) (upto 8))), inv_names).
    { unfold ghost_vsnap; cancel.
      rewrite <- emp_sepcon at 1.
      apply sepcon_derives; [|cancel].
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      + rewrite <- wand_sepcon_adjoint, emp_sepcon.
        rewrite (sepcon_comm _ (|> P)), 3sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
        eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
        Intros x; destruct x as (v, vs).
        unfold node_inv, node_state; Intro v'.
        Exists gsh2 (Z.of_nat v') v vs; entailer!.
        rewrite Nat2Z.id; auto.
      + apply allp_right; intro sh0.
        apply allp_right; intro v.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        destruct (eq_dec v v1).
        * Intros ver vs; subst.
          match goal with H : _ \/ _ |- _ => destruct H; subst; [|match goal with H : Z.even (Z.of_nat ver + 1) = true |- _ => rewrite Z.even_add, even_inj in H;
              replace (Nat.even ver) with true in H; discriminate end] end.
          rewrite Nat2Z.id in *.
          assert_PROP (Forall (fun '(vi, v') => vi = ver /\ v' = ver) vers) as Hvers.
          { rewrite Forall_forall_Znth, prop_forall; apply allp_right; intro i.
            rewrite prop_forall; apply allp_right; intro.
            match goal with H : Forall _ vers |- _ => apply Forall_Znth with (i0 := i) in H; auto end.
            rewrite extract_nth_sepcon with (i := i)(l := map _ (upto 8))
              by (rewrite Zlength_map, Zlength_upto; simpl; omega).
            erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto; simpl; omega).
            rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_version _ _ g)), (sepcon_comm _ (ghost_vsnap (fst (Znth i vers)) g)).
            unfold ghost_vsnap, ghost_version; rewrite <- !sepcon_assoc, snap_master_join by auto.
            Intros; apply prop_right; destruct (Znth i vers) as (z, ?); simpl in *.
            assert (z = ver) by rep_omega; subst.
            destruct (Nat.even ver); try discriminate; tauto. }
          rewrite prop_true_andp by auto.
          assert_PROP (vs = vals).
          { assert_PROP (forall i, 0 <= i < Zlength vs -> Znth i vs = Znth i vals);
              [|eapply prop_right, list_Znth_eq'; auto; omega].
            rewrite prop_forall; apply allp_right; intro i.
            rewrite prop_forall; apply allp_right; intro.
            apply Forall_Znth with (i0 := i) in Hvers; [|omega].
            rewrite extract_nth_sepcon with (i := i)
              by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
            rewrite extract_nth_sepcon with (i := i)(l := map _ _)
              by (rewrite Zlength_map, Zlength_upto; simpl; omega).
            erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, <- ?Zlength_correct; simpl; omega).
            unfold node_entry; Intros v' log d.
            destruct (Nat.even ver); try discriminate.
            destruct (Znth i vers); repeat match goal with H : _ = _ /\ _ = _ |- _ => destruct H end.
            subst; rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_log _ _ (Znth i lg))),
              (sepcon_comm _ (ghost_lsnap _ (Znth i lg))).
            unfold ghost_log, ghost_lsnap; rewrite <- !sepcon_assoc, snap_master_join by auto; simpl; Intros; apply prop_right.
            unfold singleton in *.
            match goal with H : log_latest _ _ _ |- _ => destruct H end.
            match goal with H : map_incl _ _ |- _ => specialize (H ver); simpl in H; rewrite eq_dec_refl in H;
              specialize (H _ eq_refl); rewrite H in *; congruence end. }
          rewrite sepcon_assoc; eapply derives_trans, fupd_frame_r; cancel.
          eapply derives_trans; [apply sepcon_derives, andp_left2, allp_left with tt; apply derives_refl|].
          apply modus_ponens_wand'.
          subst; unfold node_inv, node_state; Exists ver; entailer!.
        * Intros ver vs.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_version _ _ _)), (sepcon_comm _ (ghost_vsnap _ _)).
          unfold ghost_version, ghost_vsnap; rewrite <- !sepcon_assoc, snap_master_join by auto.
          Intros; sep_apply make_snap.
          eapply derives_trans; [apply bupd_frame_r|].
          apply fupd_bupd, bupd_mono.
          rewrite !sepcon_assoc; eapply derives_trans, fupd_frame_r; cancel.
          rewrite <- !sepcon_assoc; eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
          apply modus_ponens_wand'.
          unfold node_inv, node_state; Exists (Z.to_nat v); entailer!.
          { destruct H14; subst; try rep_omega.
            rewrite Z2Nat.inj_add, Nat2Z.id; simpl; omega. }
          unfold ghost_version; rewrite Z2Nat.id by omega; auto. }
    Intros v2.
    forward_if (v2 <> v1).
    + subst; rewrite eq_dec_refl in *.
      viewshift_SEP 1 emp.
      { go_lower; apply own_dealloc. }
      viewshift_SEP 2 emp.
      { go_lower.
        rewrite sepcon_map.
        eapply derives_trans; [apply sepcon_derives|].
        * (* apply own_list_dealloc'. *) admit.
        * (* apply own_list_dealloc'. *) admit.
        * rewrite sepcon_emp; apply derives_refl. }
      forward.
      Exists tt; entailer!.
      admit.
    + forward.
      entailer!.
    + Intros; if_tac; [contradiction | entailer!].
      admit. (* drop snaps *)
Admitted.

Lemma dirty_entry : forall sh v vs locs lg i, Nat.even v = true ->
  node_entry sh v vs locs lg i |-- node_entry sh (v + 1) vs locs lg i.
Proof.
  intros; unfold node_entry.
  Intros v' log d.
  rewrite H in *; match goal with H : _ /\ _ |- _ => destruct H end.
  Exists v log d; entailer!.
  rewrite Nat.even_add, H; simpl; omega.
Qed.

Lemma clean_entry : forall v vs locs lg i vs', Nat.even v = false ->
  node_entry gsh1 (v + 1) vs' locs lg i * node_entry gsh2 v vs locs lg i |--
  node_entry gsh1 (v + 1) vs' locs lg i * node_entry gsh2 (v + 1) vs' locs lg i.
Proof.
  intros; unfold node_entry.
  Intros v1 log1 d1 v2 log2 d2.
  Exists (v + 1)%nat log1 d1 (v + 1)%nat log1 d1.
  rewrite sepcon_assoc, (sepcon_comm (data_at _ _ _ _)), <- !sepcon_assoc.
  unfold ghost_log; erewrite master_share_join' by eauto.
  assert_PROP (d1 = d2).
  { rewrite sepcon_assoc, sepcon_comm; apply sepcon_derives_prop.
    unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; Intros.
    eapply derives_trans; [apply mapsto_value_eq; auto; discriminate|].
    apply prop_left; unfold unfold_reptype; simpl; intro; apply prop_right.
    apply repr_inj_signed; auto; congruence. }
  erewrite <- master_share_join by eauto; entailer!.
  exploit (log_latest_inj log2 v1 d2 v2); eauto; intros (? & ?); subst.
  rewrite Nat.even_add, H in *; simpl in *.
  match goal with H : _ /\ _ |- _ => destruct H; subst; repeat (split; auto) end.
Qed.

Corollary clean_entries : forall v vs locs lg vs', Nat.even v = false ->
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
  unfold atomic_shift; Intros P.
  set (AS := _ -* _).
  forward.
  unfold node_state; Intros.
  replace_SEP 1 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
  forward_call (version, AS && cored * |> P * ghost_version gsh1 v0 g, Full_set iname, Empty_set iname,
    fun sh v' => !!(sh = gsh2) && EX v : nat, EX vs : _, !!(repable_signed v' /\ Nat.even v = true /\
      Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
      (v' = Z.of_nat v \/ v' = Z.of_nat (v + 1))%nat) && ghost_version gsh2 (Z.to_nat v') g * fold_right sepcon emp
        (map (node_entry gsh2 (Z.to_nat v') vs locs lg) (upto (length locs))) *
      (node_inv v vs version locs g lg -* |={Empty_set iname,Full_set iname}=> |> P) * ghost_version gsh1 v0 g,
    fun v : Z => |> P * (!!(v = Z.of_nat v0) && ghost_version gsh1 v0 g), inv_names).
  { cancel.
    rewrite <- emp_sepcon at 1.
    apply sepcon_derives; [|cancel].
    rewrite <- emp_sepcon at 1; apply sepcon_derives.
    + rewrite <- wand_sepcon_adjoint, emp_sepcon.
      rewrite (sepcon_comm _ (|> P)).
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
      eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
      Intros x; destruct x as (v, vs).
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
      unfold node_inv, node_state; Intros v'.
      Exists gsh2 (Z.of_nat v') v vs; entailer!.
      { destruct H9; auto. }
      rewrite Nat2Z.id; auto.
    + apply allp_right; intro sh0.
      apply allp_right; intro v.
      rewrite <- wand_sepcon_adjoint, emp_sepcon.
      Intros v1 vs.
      assert_PROP (Z.of_nat v0 = v).
      { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_version gsh2 _ _)), (sepcon_comm _ (ghost_version gsh1 _ _)).
        unfold ghost_version; erewrite <- !sepcon_assoc, master_share_join' by eauto; entailer!. }
      rewrite <- sepcon_andp_prop.
      eapply derives_trans, fupd_frame_r; entailer!.
      apply modus_ponens_wand'.
      unfold node_inv, node_state; Exists v0; entailer!.
      { destruct H15; try rep_omega.
        rewrite Nat2Z.inj_add in *; simpl in *; omega. }
      rewrite Nat2Z.id; auto. }
  Intros x; subst.
  assert (repable_signed (Z.of_nat (v0 + 1))) by admit. (* version stays in range *)
  replace_SEP 2 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
  forward_call (version, Z.of_nat (v0 + 1), AS && cored * |> P * ghost_version gsh1 v0 g * data_at gsh1 tint (vint (Z.of_nat v0)) version,
    Full_set iname, Empty_set iname,
    fun sh => !!(sh = Tsh) && EX v : nat, EX vs : _, EX v' : nat, !!(repable_signed (Z.of_nat v') /\ Nat.even v = true /\
      Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
      (v' = v \/ v' = v + 1)%nat) && ghost_version gsh2 v' g *
      fold_right sepcon emp (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) *
      (node_inv v vs version locs g lg -* |={Empty_set iname,Full_set iname}=> |> P) *
      ghost_version gsh1 v0 g, |> P * ghost_version gsh1 (v0 + 1)%nat g * data_at gsh1 tint (vint (Z.of_nat (v0 + 1))) version, inv_names).
  { rewrite Nat2Z.inj_add in *; simpl in *; auto. }
  { entailer!.
    rewrite Nat2Z.inj_add in *; simpl in *; auto. }
  { cancel.
    rewrite <- emp_sepcon at 1.
    apply sepcon_derives; [|cancel].
    rewrite <- emp_sepcon at 1; apply sepcon_derives.
   + rewrite <- wand_sepcon_adjoint, emp_sepcon.
      rewrite (sepcon_comm _ (|> P)), sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
      eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
      Intros x; destruct x as (v, vs).
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
      unfold node_inv at 1, node_state; Intro v'.
      Exists Tsh v vs v'; entailer!.
      eapply derives_trans; [apply data_at_value_cohere; auto|].
      erewrite sepcon_comm, data_at_share_join; eauto; cancel.
    + apply allp_right; intro sh0.
      rewrite <- wand_sepcon_adjoint, emp_sepcon.
      Intros v vs v'.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_version gsh2 _ _)), (sepcon_comm _ (ghost_version gsh1 _ _)).
      unfold ghost_version; erewrite <- !sepcon_assoc, master_share_join' by eauto; Intros; subst v'.
      sep_apply (master_update v0 (v0 + 1)%nat); [omega|].
      eapply derives_trans; [apply bupd_frame_r|].
      apply fupd_bupd, bupd_mono.
      rewrite !sepcon_assoc; eapply derives_trans, fupd_frame_r.
      erewrite <- master_share_join by eauto.
      subst; erewrite <- data_at_share_join by eauto.
      cancel; apply modus_ponens_wand'.
      unfold node_inv, node_state.
      Exists (v0 + 1)%nat; unfold ghost_version; entailer!.
      { match goal with H : _ \/ _ |- _ => destruct H; subst; auto end.
        rewrite Nat.even_add in *; simpl in *.
        match goal with H : Nat.even v = true |- _ => rewrite H in *; discriminate end. }
      apply sepcon_list_derives; rewrite !Zlength_map; auto; intros.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      apply dirty_entry; auto. }
  assert_PROP (Zlength (map (fun x => vint x) vals) = 8) by entailer!.
  rewrite <- seq_assoc.
  forward_for_simple_bound 8 (EX i : Z, PROP ( )
    LOCAL (temp _v (vint (Z.of_nat v0)); temp _ver version; temp _n n; temp _in input)
    SEP (|>P; AS && cored;
    ghost_version gsh1 (v0 + 1)%nat g; data_at gsh1 tint (vint (Z.of_nat (v0 + 1))) version;
    @data_at CompSpecs sh tnode (version, locs) n;
    data_at Tsh (tarray tint 8) (map (fun x : Z => vint x) vals) input;
    fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (sublist 0 i (upto 8)));
    fold_right sepcon emp (map (node_entry gsh1 v0 vs0 locs lg) (sublist i 8 (upto 8))))).
  { rewrite <- ZtoNat_Zlength; replace (Zlength locs) with 8; simpl Z.to_nat; entailer!.
    rewrite sublist_same; auto. }
  - (* loop body *)
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto; simpl; omega); simpl.
    rewrite Zlength_map in *.
    Intros; forward.
    replace_SEP 1 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
    forward_call (Znth i locs, Znth i vals, AS && cored * |> P * ghost_version gsh1 (v0 + 1)%nat g *
      node_entry gsh1 v0 vs0 locs lg i, Full_set iname, Empty_set iname,
      fun sh => !!(sh = Tsh) && EX ver : nat, EX vs : _, EX ver' : nat, EX v'' : _, EX log : _, EX d : Z,
        !!(repable_signed (Z.of_nat ver') /\ Nat.even ver = true /\ Forall repable_signed vs /\ Zlength vs = Zlength locs /\
           Zlength lg = Zlength locs /\ (ver' = ver \/ ver' = ver + 1)%nat /\
           (if Nat.even ver' then v'' = ver' /\ d = Znth i vs else v'' >= ver' - 1)%nat /\ log_latest log v'' d) &&
        ghost_version gsh2 ver' g * data_at gsh2 tint (vint (Z.of_nat ver')) version * ghost_log gsh2 log (Znth i lg) *
        fold_right sepcon emp (upd_Znth i (map (node_entry gsh2 ver' vs locs lg) (upto (length locs))) emp) *
        (node_inv ver vs version locs g lg -* |={Empty_set iname,Full_set iname}=> |> P) * ghost_version gsh1 (v0 + 1)%nat g *
        EX log' : _, !!(log_latest log' v0 (Znth i vs0)) && ghost_log gsh1 log' (Znth i lg),
      |> P * ghost_version gsh1 (v0 + 1)%nat g * node_entry gsh1 (v0 + 2) vals locs lg i, inv_names).
    { cancel.
      rewrite <- emp_sepcon at 1.
      apply sepcon_derives; [|cancel].
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
     + rewrite <- wand_sepcon_adjoint, emp_sepcon.
      rewrite (sepcon_comm _ (|> P)), sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
      eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
      Intros x; destruct x as (v, vs).
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
      unfold node_inv, node_state; Intro v'.
      rewrite extract_nth_sepcon with (i := i)
        by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
      erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
      unfold node_entry; Intros v'' log d v2 log2 d2.
      Exists Tsh v vs v' v'' log d log2; entailer!.
      { replace (Nat.even v0) with true in *; match goal with H : _ /\ _ |- _ => destruct H; subst; auto end. }
      eapply derives_trans; [apply data_at_value_cohere; auto|].
      erewrite sepcon_comm, data_at_share_join by eauto; cancel.
      + apply allp_right; intro sh0.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        Intros ver vs ver' v'' log d log'.
        assert_PROP (v0 + 1 = ver')%nat as PP.
        { rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_version gsh2 _ g)), (sepcon_comm _ (ghost_version gsh1 _ g)).
          unfold ghost_version; erewrite <- !sepcon_assoc, master_share_join' by eauto; entailer!. }
        Intros; subst.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_log gsh2 _ _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_log gsh1 _ _)).
        unfold ghost_log; erewrite <- !sepcon_assoc, master_share_join' by eauto; Intros; subst.
        exploit (log_latest_inj log v'' d v0); eauto; intros (? & ?); subst.
        destruct (log_latest_upd log v0 (Znth i vs0) (v0 + 2) (Znth i vals)); auto; try omega.
        sep_apply (master_update(ORD := fmap_order) log (map_upd log (v0 + 2)%nat (Znth i vals))); auto.
        eapply derives_trans; [apply bupd_frame_r|].
        apply fupd_bupd, bupd_mono.
        erewrite <- master_share_join by eauto.
        erewrite <- data_at_share_join by eauto.
        rewrite !sepcon_assoc; eapply derives_trans, fupd_frame_r; cancel.
        unfold node_entry, ghost_log. Exists (v0 + 2)%nat (map_upd log (v0 + 2)%nat (Znth i vals)) (Znth i vals); entailer!.
        { rewrite !Nat.even_add; simpl.
          replace (Nat.even v0) with true; simpl.
          split; [|split]; auto; try omega; apply Forall_Znth; auto; omega. }
        apply modus_ponens_wand'.
        unfold node_inv, node_state.
        Exists (v0 + 1)%nat; rewrite extract_nth_sepcon with (i := i)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, <- Zlength_correct; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
        unfold node_entry, ghost_log. Exists (v0 + 2)%nat (map_upd log (v0 + 2)%nat (Znth i vals)) (Znth i vals); entailer!.
        { rewrite !Nat.even_add; simpl.
          replace (Nat.even v0) with true; simpl.
          split; auto; try omega; apply Forall_Znth; auto; omega. } }
    { apply Forall_Znth; auto; omega. }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (auto; rewrite ?Zlength_upto; simpl; omega); entailer!.
    simpl; cancel.
  - rewrite !sublist_nil, !sublist_same by auto; simpl.
    assert (repable_signed (Z.of_nat (v0 + 2))) by admit. (* version stays in range *)
    forward_call (version, Z.of_nat (v0 + 2), AS && cored * |> P * ghost_version gsh1 (v0 + 1)%nat g * data_at gsh1 tint (vint (Z.of_nat (v0 + 1))) version *
      fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (upto 8)) * data_at sh tnode (version, locs) n *
      data_at Tsh (tarray tint 8) (map (fun x0 : Z => vint x0) vals) input, Full_set iname, Empty_set iname,
      fun sh' => !!(sh' = Tsh) && EX v : nat, EX vs : _, EX v' : nat, !!(repable_signed (Z.of_nat v') /\ Nat.even v = true /\
        Forall repable_signed vs /\ Zlength vs = Zlength locs /\ Zlength lg = Zlength locs /\
        (v' = v \/ v' = v + 1)%nat) && ghost_version gsh2 v' g *
        fold_right sepcon emp (map (node_entry gsh2 v' vs locs lg) (upto (length locs))) *
        data_at sh tnode (version, locs) n * data_at Tsh (tarray tint 8) (map (fun x0 : Z => vint x0) vals) input *
        (ALL y : unit, data_at sh tnode (version, locs) n *
                data_at Tsh (tarray tint 8) (map (fun x0 : Z => vint x0) vals) input *
                node_state gsh1 (v0 + 2) vals version locs g lg *
                node_inv (v0 + 2) vals version locs g lg -*
              (|={ Empty_set iname, Full_set iname }=> Q y)) *
        ghost_version gsh1 (v0 + 1)%nat g * fold_right sepcon emp (map (node_entry gsh1 (v0 + 2) vals locs lg) (upto 8)),
      Q tt, inv_names).
    { rewrite Nat2Z.inj_add in *; auto. }
    { entailer!.
      rewrite Nat2Z.inj_add in *; auto. }
    { cancel.
      rewrite <- emp_sepcon at 1.
      apply sepcon_derives; [|cancel].
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
     + rewrite <- wand_sepcon_adjoint, emp_sepcon.
        rewrite (sepcon_comm _ (|> P)), 4sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
        eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
        Intros x; destruct x as (v, vs).
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left2; apply derives_refl|].
        unfold node_inv, node_state; Intro v'.
        Exists Tsh v vs v'; entailer!.
        eapply derives_trans; [apply data_at_value_cohere; auto|].
        erewrite sepcon_comm, data_at_share_join by eauto; cancel.
      + apply allp_right; intro sh0.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        Intros v vs v'; subst.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_version gsh2 _ _)), (sepcon_comm _ (ghost_version gsh1 _ _)).
        unfold ghost_version; erewrite <- !sepcon_assoc, master_share_join' by eauto; Intros; subst.
        match goal with H : _ \/ _ |- _ => destruct H; [subst; rewrite Nat.even_add in *;
          replace (Nat.even v0) with true in *; discriminate|] end.
        assert (v = v0) by omega; subst.
        sep_apply (master_update (v0 + 1)%nat (v0 + 2)%nat); [omega|].
        eapply derives_trans; [apply bupd_frame_r|].
        apply fupd_bupd, bupd_mono.
        rewrite <- !sepcon_assoc, sepcon_comm, <- sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives, allp_left with tt; apply derives_refl|].
        apply modus_ponens_wand'.
        erewrite <- master_share_join by eauto.
        erewrite <- data_at_share_join by eauto.
        unfold node_inv, node_state.
        rewrite Zlength_map in *.
        replace (length locs) with (Z.to_nat 8) by (symmetry; rewrite <- Zlength_length; auto; computable).
        pose proof (clean_entries (v0 + 1) vs locs lg vals) as Hclean.
        rewrite <- Nat.add_assoc in Hclean; simpl in *.
        sep_apply Hclean.
        { rewrite Nat.even_add; replace (Nat.even v0) with true; auto. }
        unfold ghost_version; Exists (v0 + 2)%nat; entailer!.
        { rewrite Nat.even_add; replace (Nat.even v0) with true; auto. } }
    forward.
    Exists tt; auto.
Admitted.
