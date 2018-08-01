Require Import VST.veric.rmaps.
Require Import VST.progs.ghosts.
Require Import atomics.general_atomics.
Require Import atomics.SC_atomics.
Require Import VST.progs.conclib.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.hashtable_atomic.
Require Import atomics.hashtable.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section Proofs.

Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition load_SC_spec := DECLARE _load_SC load_SC_spec.
Definition store_SC_spec := DECLARE _store_SC store_SC_spec.
Definition CAS_SC_spec := DECLARE _CAS_SC CAS_SC_spec.

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH t : type
   PRE [ _n OF tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned; complete_legal_cosu_type t = true;
             natural_aligned natural_alignment t = true)
       LOCAL (temp _n (Vint (Int.repr (sizeof t))))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh t p * data_at_ Tsh t p).

Definition integer_hash_spec :=
 DECLARE _integer_hash
  WITH i : Z
  PRE [ _i OF tint ]
   PROP () LOCAL (temp _i (vint i)) SEP ()
  POST [ tint ]
   PROP () LOCAL (temp ret_temp (vint (i * 654435761))) SEP ().
(* One might think it should just return an unknown number, but in fact it needs to follow a known hash
   function at the logic level to be useful. *)

Definition tentry := Tstruct _entry noattr.

(* Having size as a large known constant tends to make everything slow, so here's a hack. *)
Definition has_size : {x : Z | x = 16384}.
Proof.
  eexists; eauto.
Qed.

Instance hf1 : hash_fun := { size := proj1_sig has_size; hash i := (i * 654435761) mod (proj1_sig has_size) }.
Proof.
  - rewrite (proj2_sig has_size); computable.
  - intro; apply Z_mod_lt; rewrite (proj2_sig has_size); computable.
Defined.

(* We don't need histories, but we do need to know that a non-zero key is persistent. *)
Instance zero_PCM : Ghost := { valid a := True;
  Join_G a b c := if eq_dec a 0 then c = b else c = a /\ (b = 0 \/ a = b) }.
Proof.
  - exists (fun _ => 0); auto.
    intro; hnf; auto.
  - constructor.
    + intros; hnf in *.
      if_tac in H; subst; auto.
      destruct H, H0; subst; auto.
    + intros; hnf in *.
      exists (if eq_dec b 0 then c else b); split; hnf.
      * if_tac; auto; split; auto.
        if_tac in H; subst.
        { rewrite if_false in H0 by auto; tauto. }
        destruct H as [? [|]]; try contradiction; subst.
        rewrite if_false in H0 by auto; tauto.
      * if_tac; subst.
        { if_tac in H0; tauto. }
        destruct H; subst.
        if_tac; subst.
        { if_tac in H0; subst; auto; contradiction. }
        destruct H2; try contradiction; subst.
        rewrite if_false in H0 by auto; tauto.
    + intros; hnf in *.
      if_tac; if_tac in H; subst; auto; try tauto.
      destruct H as [? [|]]; subst; auto; contradiction.
    + intros; hnf in *.
      if_tac in H; if_tac in H0; subst; auto; try tauto.
      destruct H; subst; contradiction.
  - auto.
Defined.

Instance zero_order : PCM_order (fun a b => a = 0 \/ a = b).
Proof.
  constructor; simpl; intros.
  - intro; auto.
  - intros ???[|][|]; subst; auto.
  - exists (if eq_dec a 0 then b else a).
    unfold sepalg.join; simpl.
    if_tac; auto.
    destruct H; [contradiction|].
    subst; repeat split; auto.
    destruct H0; auto.
  - hnf in H.
    if_tac in H; auto.
    destruct H; subst; split; auto.
    destruct H1; auto.
  - hnf.
    if_tac; subst.
    + destruct H; auto.
    + split; auto; destruct H; auto.
Defined.

Definition hashtable_entry T lg entries i :=
  let '(pk, pv) := Znth i entries in let '(ki, vi) := Znth i T in
  !!(repable_signed ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) &&
  ghost_master1(ORD := zero_order) ki (Znth i lg) *
  data_at Tsh tint (vint ki) pk * data_at Tsh tint (vint vi) pv.

Definition wf_table T := forall k i, k <> 0 -> fst (Znth i T) = k -> lookup T k = Some i.

Definition hashtable H g lg entries := EX T : list (Z * Z),
  !!(Zlength T = size /\ wf_table T /\ forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) &&
  excl g H * fold_right sepcon emp (map (hashtable_entry T lg entries) (upto (Z.to_nat size))).

Program Definition set_item_spec := DECLARE _set_item atomic_spec
  (ConstType (Z * Z * globals * share * list (val * val) * gname * list gname))
  [(_key, tint); (_value, tint)] tvoid
  [fun _ '(k, v, gv, sh, entries, g, lg) => temp _key (vint k);
   fun _ '(k, v, gv, sh, entries, g, lg) => temp _value (vint v);
   fun _ '(k, v, gv, sh, entries, g, lg) => gvars gv]
  (fun _ '(k, v, gv, sh, entries, g, lg) => !!(readable_share sh /\ repable_signed k /\ repable_signed v /\
   k <> 0 /\ v <> 0 /\ Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries /\ Zlength lg = size) &&
   data_at sh (tarray tentry size) entries (gv _m_entries))
  (fun _ '(k, v, gv, sh, entries, g, lg) H => hashtable H g lg entries)
  tt []
  (fun _ '(k, v, gv, sh, entries, g, lg) H _ =>
   data_at sh (tarray tentry size) entries (gv _m_entries) * hashtable (map_upd H k v) g lg entries)
  (Empty_set _) (Full_set _) _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.

(* Read the most recently written value. *)
Program Definition get_item_spec := DECLARE _get_item atomic_spec
  (ConstType (Z * globals * share * list (val * val) * gname * list gname))
  [(_key, tint)] tint
  [fun _ '(k, p, sh, entries, g, lg) => temp _key (vint k);
   fun _ '(k, gv, sh, entries, g, lg) => gvars gv]
  (fun _ '(k, gv, sh, entries, g, lg) => !!(readable_share sh /\ repable_signed k /\ k <> 0 /\
   Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries /\ Zlength lg = size) &&
   data_at sh (tarray tentry size) entries (gv _m_entries))
  (fun _ '(k, p, sh, entries, g, lg) H => hashtable H g lg entries)
  0 [fun _ _ v => temp ret_temp (vint v)]
  (fun _ '(k, gv, sh, entries, g, lg) H v => data_at sh (tarray tentry size) entries (gv _m_entries) *
   (!!(if eq_dec v 0 then H k = None else H k = Some v) && hashtable H g lg entries))
  (Empty_set _) (Full_set _) _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? (((((k, p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? (((((k, p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? (((((k, p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? (((((k, p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? (((((k, p), sh), entries), g), lg); auto.
Qed.

Program Definition add_item_spec := DECLARE _add_item atomic_spec
  (ConstType (Z * Z * globals * share * list (val * val) * gname * list gname))
  [(_key, tint); (_value, tint)] tint
  [fun _ '(k, v, p, sh, entries, g, lg) => temp _key (vint k);
   fun _ '(k, v, p, sh, entries, g, lg) => temp _value (vint v);
   fun _ '(k, v, gv, sh, entries, g, lg) => gvars gv]
  (fun _ '(k, v, gv, sh, entries, g, lg) => !!(readable_share sh /\ repable_signed k /\ repable_signed v /\
   k <> 0 /\ v <> 0 /\ Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries /\ Zlength lg = size) &&
   data_at sh (tarray tentry size) entries (gv _m_entries))
  (fun _ '(k, v, p, sh, entries, g, lg) H => hashtable H g lg entries)
  true [fun _ _ b => temp ret_temp (Val.of_bool b)]
  (fun _ '(k, v, gv, sh, entries, g, lg) H b => data_at sh (tarray tentry size) entries (gv _m_entries) *
   (!!(H k = None <-> b = true) && hashtable (if b then map_upd H k v else H) g lg entries))
  (Empty_set _) (Full_set _) _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.
Next Obligation.
Proof.
  intros ?? ((((((k, v), p), sh), entries), g), lg); auto.
Qed.

Definition init_table_spec :=
 DECLARE _init_table
  WITH gv : globals
  PRE [ ]
   PROP ()
   LOCAL (gvars gv)
   SEP (data_at_ Ews (tarray tentry size) (gv _m_entries))
  POST [ tvoid ]
   EX entries : list (val * val), EX g : gname, EX lg : list gname,
   PROP (Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
   LOCAL ()
   SEP (data_at Ews (tarray tentry size) entries (gv _m_entries); fold_right sepcon emp (map (fun '(pk, pv) =>
          malloc_token Tsh tint pk * malloc_token Tsh tint pv) entries);
        hashtable empty_map g lg entries).

Inductive hashtable_hist_el :=
  | HSet (k : Z) (v : Z) | HGet (k : Z) (v : Z) | HAdd (k : Z) (v : Z) (r : bool).

Notation hist := (nat -> option hashtable_hist_el).

Fixpoint apply_hist H h :=
  match h with
  | [] => Some H
  | HSet k v :: h' => apply_hist (map_upd H k v) h'
  | HGet k v :: h' => match H k with Some v' => if eq_dec v' v then apply_hist H h' else None
                      | None => if eq_dec v 0 then apply_hist H h' else None end
  | HAdd k v r :: h' => match H k with None => if r then apply_hist (map_upd H k v) h' else None
                        | Some _ => if r then None else apply_hist H h' end
  end.

Definition hashtable_inv gh g lg entries := EX H : _, hashtable H g lg entries *
  EX hr : _, !!(apply_hist empty_map hr = Some H) && ghost_ref hr gh.

Definition f_lock_inv sh gsh entries gh p t locksp lockt resultsp res :=
  EX b1 : bool, EX b2 : bool, EX b3 : bool, EX h : _,
    !!(add_events empty_map [HAdd 1 1 b1; HAdd 2 1 b2; HAdd 3 1 b3] h) && ghost_hist gsh h gh *
    data_at sh (tarray tentry size) entries p *
    data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
    data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp *
    data_at Tsh tint (vint (Zlength (filter id [b1; b2; b3]))) res.

Definition f_lock_pred tsh sh gsh entries gh p t locksp lockt resultsp res :=
  selflock (f_lock_inv sh gsh entries gh p t locksp lockt resultsp res) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH tid : val, x : share * share * share * list (val * val) * iname * gname * gname * list gname * globals * Z * val *
                      val * val * val * invG
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, gsh, tsh, entries, i, gh, g, lg, gv, t, locksp, lockt, resultsp, res, inv_names) := x in
   PROP (0 <= t < 3; isptr lockt; readable_share sh; readable_share tsh; gsh <> Share.bot;
         Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
   LOCAL (temp _arg tid; gvars gv)
   SEP (data_at sh (tarray tentry size) entries (gv _m_entries);
        invariant i (hashtable_inv gh g lg entries);
        ghost_hist(hist_el := hashtable_hist_el) gsh empty_map gh;
        data_at Tsh tint (vint t) tid; malloc_token Tsh tint tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) (gv _thread_locks);
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) (gv _results);
        data_at_ Tsh tint res;
        lock_inv tsh lockt (f_lock_pred tsh sh gsh entries gh (gv _m_entries) t
                                        (gv _thread_locks) lockt (gv _results) res))
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog [] gv
  POST [ tint ] main_post prog [] gv.

Definition Gprog : funspecs := ltac:(with_library prog [makelock_spec; freelock2_spec; acquire_spec;
  release2_spec; spawn_spec; surely_malloc_spec; load_SC_spec; store_SC_spec; CAS_SC_spec;
  integer_hash_spec; set_item_spec; get_item_spec; add_item_spec; init_table_spec; f_spec; main_spec]).

Lemma body_integer_hash: semax_body Vprog Gprog f_integer_hash integer_hash_spec.
Proof.
  start_function.
  forward.
Qed.

Opaque upto.

Lemma hash_size : forall k, (k * 654435761) mod size = hash k mod size.
Proof.
  intro; simpl.
  rewrite Zmod_mod; split; auto; omega.
Qed.

Arguments size : simpl never.
Arguments hash : simpl never.

Lemma failed_entries : forall k i i1 keys lg T entries (Hk : k <> 0) (Hi : 0 <= i < size)
  (Hi1 : (i + hash k) mod size = i1 mod size) (HT : Zlength T = size) (Hlg : Zlength lg = size)
  (Hkeys: Zlength keys = size)
  (Hfail : Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k)))),
  fold_right sepcon emp (upd_Znth (i1 mod size) (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
  fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
    (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))
  |-- !! Forall (fun x => fst x <> 0 /\ fst x <> k) (sublist 0 i (rebase T (hash k))).
Proof.
  intros.
  rewrite Forall_forall, prop_forall; apply allp_right; intros (k', v').
  rewrite prop_forall; apply allp_right; intro Hin.
  apply In_Znth in Hin; destruct Hin as (j & Hj & Hjth).
  pose proof (hash_range k).
  rewrite Zlength_sublist in Hj by (rewrite ?Zlength_rebase; omega).
  rewrite Znth_sublist, Znth_rebase in Hjth by omega.
  assert (0 <= (j + hash k) mod size < size) by (apply Z_mod_lt, size_pos).
  pose proof (Z_mod_lt i1 _ size_pos).
  rewrite extract_nth_sepcon with (i := (j + hash k) mod size), extract_nth_sepcon with (i := j)(l := map _ _)
    by (rewrite ?upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
  assert ((j + hash k) mod size <> i1 mod size).
  { rewrite <- Hi1; intro Heq.
    apply Zmod_plus_inv in Heq; [|apply size_pos].
    rewrite !Zmod_small in Heq; omega. }
  erewrite !upd_Znth_diff', !Znth_map, !Znth_upto by
    (rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega).
  unfold hashtable_entry.
  rewrite Z.add_0_r in Hjth; replace (Zlength T) with size in Hjth; rewrite Hjth.
  destruct (Znth _ entries).
  Intros; rewrite <- !sepcon_assoc.
  rewrite (sepcon_comm _ (ghost_snap(P := zero_PCM) _ _)).
  rewrite <- !sepcon_assoc, snap_master_join1 by auto.
  Intros; apply prop_right; simpl.
  eapply Forall_Znth in Hfail.
  rewrite Znth_sublist, Z.add_0_r, Znth_rebase with (i0 := j) in Hfail; auto; try omega.
  replace (Zlength keys) with size in Hfail; intuition.
  { rewrite Zlength_sublist; auto; try omega.
    rewrite Zlength_rebase; omega. }
Qed.

Corollary entries_lookup : forall k i i1 keys lg T entries (Hk : k <> 0) (Hi : 0 <= i < size)
  (Hi1 : (i + hash k) mod size = i1 mod size) (HT : Zlength T = size) (Hlg : Zlength lg = size)
  (Hkeys: Zlength keys = size)
  (Hfail : Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
  (Hhit : fst (Znth (i1 mod size) T) = k \/ fst (Znth (i1 mod size) T) = 0),
  fold_right sepcon emp (upd_Znth (i1 mod size) (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
  fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
    (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))
  |-- !! (lookup T k = Some (i1 mod size)).
Proof.
  intros.
  eapply derives_trans; [apply failed_entries; eauto | apply prop_left; intro; apply prop_right].
  pose proof (hash_range k).
  unfold lookup; erewrite index_of'_succeeds.
  simpl; eauto.
  - rewrite Zlength_rebase; omega.
  - auto.
  - rewrite Znth_rebase by omega.
    rewrite HT, Hi1; auto.
Qed.

Lemma wf_table_upd : forall T k v i (Hwf : wf_table T) (HT : Zlength T = size) (Hi : lookup T k = Some i)
  (Hk : k <> 0), wf_table (upd_Znth i T (k, v)).
Proof.
  intros; intros ?? Hj ?.
  exploit lookup_range; eauto; intro.
  destruct (eq_dec i0 i); subst.
  - rewrite upd_Znth_same, lookup_upd_same; auto.
  - rewrite upd_Znth_diff' in Hj |- * by auto.
    assert (lookup T (fst (Znth i0 T)) <> Some i).
    { erewrite Hwf by eauto; congruence. }
    rewrite lookup_upd_diff; auto.
    split; auto.
    intro; erewrite Hwf in Hi by eauto; congruence.
Qed.

Corollary wf_table_upd_same : forall T k v i (Hwf : wf_table T) (HT : Zlength T = size)
  (Hi : fst (Znth i T) = k) (Hk : k <> 0), wf_table (upd_Znth i T (k, v)).
Proof.
  intros; apply wf_table_upd; auto.
Qed.

Lemma snaps_dealloc : forall {A} (l : list A) f g, fold_right sepcon emp (map (fun i => ghost_snap (f i) (g i)) l) |-- |==> emp.
Proof.
  induction l; simpl; intros.
  - apply bupd_intro.
  - eapply derives_trans; [apply sepcon_derives; [apply own_dealloc | apply IHl]|].
    setoid_rewrite <- emp_sepcon at 7; apply bupd_sepcon.
Qed.

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((k, v), gv), sh), entries), g), lg); Intros.
  forward_call k.
  pose proof size_pos.
  unfold atomic_shift; Intros P.
  set (AS := _ -* _).
  forward_loop (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (|> P; AS && cored;
         @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))))%assert
    continue: (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (Int.min_signed <= Int.signed (Int.repr i1) < Int.max_signed; i1 mod size = (i + hash k) mod size;
          0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 (i + 1) (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (|> P; AS && cored; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat (i + 1))))))%assert.
  { Exists 0 (k * 654435761)%Z (repeat 0 (Z.to_nat size)); rewrite sublist_nil; entailer!.
    split; [apply hash_size|].
    rewrite Zlength_repeat, Z2Nat.id; auto; omega.
    { simpl; auto. } }
  - Intros i i1 keys; forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    replace (2 ^ 14) with size by (setoid_rewrite (proj2_sig has_size); auto).
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) as Hi1' by omega.
    match goal with H : Forall _ _ |- _ => pose proof (Forall_Znth _ _ _ Hi1' H) as Hptr end.
    destruct (Znth (i1 mod size) entries) as (pki, pvi) eqn: Hpi; destruct Hptr.
    forward; setoid_rewrite Hpi.
    { entailer!. }
    assert (Zlength (rebase keys (hash k)) = size) as Hrebase.
    { rewrite Zlength_rebase; replace (Zlength keys) with size; auto; apply hash_range. }
    replace_SEP 1 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
    forward_call (pki, AS && cored * |> P, Full_set iname, Empty_set iname,
      fun sh v => !!(sh = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
      forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
      !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) && ghost_master1 ki (Znth (i1 mod size) lg) *
      data_at Tsh tint (vint vi) pvi * excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
          (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
      (hashtable H g lg entries -* |={Empty_set iname,Full_set iname}=> |> P),
      fun v : Z => |> P * ghost_snap v (Znth (i1 mod size) lg)).
    { cancel.
      rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      + rewrite <- wand_sepcon_adjoint, emp_sepcon.
        unfold AS.
        rewrite sepcon_comm.
        eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
        eapply derives_trans; [apply modus_ponens_wand | apply fupd_mono].
        Intros HT.
        eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
        unfold hashtable at 1; Intros T.
        rewrite extract_nth_sepcon with (i := i1 mod size)
          by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
        unfold hashtable_entry.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        Intros; Exists Tsh ki HT T; rewrite HHi; entailer!.
        apply derives_refl.
      + apply allp_right; intro sh0.
        apply allp_right; intro v0.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        Intros HT T.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
        rewrite !sepcon_assoc; eapply derives_trans.
        { apply sepcon_derives, derives_refl.
          apply (make_snap(ORD := zero_order)). }
        eapply derives_trans; [apply bupd_frame_r|].
        apply fupd_bupd, bupd_mono.
        eapply derives_trans, fupd_frame_r.
        subst v0; cancel.
        apply modus_ponens_wand'.
        unfold hashtable; Exists T.
        rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
        unfold hashtable_entry.
        rewrite Hpi, HHi; entailer!.
        apply derives_refl. }
    Intros k1.
    focus_SEP 1.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: R)))) end.
    + assert (forall k1, (k1 <> k /\ k1 <> 0) ->
        Zlength (upd_Znth (i1 mod size) keys k1) = size /\
        Forall (fun z => z <> 0 /\ z <> k)
          (sublist 0 (i + 1) (rebase (upd_Znth (i1 mod size) keys k1) (hash k)))).
      { split; [rewrite upd_Znth_Zlength; auto; omega|].
        replace (i1 mod size) with ((i + hash k) mod size); replace size with (Zlength keys);
          rewrite !rebase_upd' by (try omega; replace (Zlength keys) with size; apply Z_mod_lt; omega).
        rewrite sublist_upd_Znth_lr by (try omega; setoid_rewrite Hrebase; omega).
        rewrite sublist_split with (mid := i), sublist_len_1 by (try omega; setoid_rewrite Hrebase; omega).
        rewrite Z.sub_0_r, upd_Znth_app2, Forall_app; rewrite Zlength_sublist;
          rewrite ?Zlength_cons, ?Zlength_nil; try omega; try (setoid_rewrite Hrebase; omega).
        split; auto.
        rewrite Z.sub_0_r, Zminus_diag, upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same
          by (auto; omega).
        repeat constructor; auto; tauto. }
      forward_if (k1 = 0).
      { eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost, loop1_ret_assert, frame_ret_assert,
          function_body_ret_assert, RA_continue.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
        rewrite Z2Nat.inj_add, upto_app, map_app, sepcon_app by omega.
        change (upto (Z.to_nat 1)) with [0]; simpl fold_right; rewrite Z2Nat.id, Z.add_0_r by omega.
        replace ((i + hash k) mod size) with (i1 mod size); rewrite Zmod_mod, upd_Znth_same by omega; entailer!.
        { assert (Int.min_signed <= i1 mod size < Int.max_signed).
          { split; etransitivity; try apply Z_mod_lt; auto; try computable.
            setoid_rewrite (proj2_sig has_size); computable. }
          rewrite Int.signed_repr by omega; auto. }
        erewrite map_ext_in; [apply derives_refl|]; simpl; intros.
        rewrite upd_Znth_diff'; auto; try omega.
        replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
        rewrite In_upto, Z2Nat.id in * by omega.
        rewrite !Zmod_small in X; omega. }
      { forward.
        entailer!. }
      Intros; subst.
      replace_SEP 2 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
      forward_call (pki, 0, k, |> P * (AS && cored) * ghost_snap 0 (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
             (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))),
        Full_set iname, Empty_set iname, fun sh v => !!(sh = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
          forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
          !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) &&
          ghost_master1 ki (Znth (i1 mod size) lg) * data_at Tsh tint (vint vi) pvi *
          excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
            (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
          ghost_snap 0 (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
             (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))) *
          (hashtable H g lg entries -* |={Empty_set iname,Full_set iname}=> |> P),
        fun v : Z => |> P * ghost_snap (if eq_dec v 0 then k else v) (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
             (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))).
      { cancel.
        rewrite sepcon_comm, <- emp_sepcon at 1.
        rewrite <- sepcon_assoc.
        apply sepcon_derives; [|cancel]; apply sepcon_derives, derives_refl.
        rewrite <- emp_sepcon at 1; apply sepcon_derives.
        * rewrite <- wand_sepcon_adjoint, emp_sepcon.
          rewrite sepcon_assoc, (sepcon_comm _ (AS && cored)); unfold AS.
          eapply derives_trans.
          { apply sepcon_derives, derives_refl.
            eapply derives_trans; [apply sepcon_derives; [apply andp_left1|]; apply derives_refl|].
            rewrite sepcon_comm; apply modus_ponens_wand. }
          eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
          Intros HT.
          rewrite (sepcon_comm _ (_ && _)), !sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives; [apply andp_left1|]; apply derives_refl|].
          unfold hashtable at 2; Intros T.
          rewrite extract_nth_sepcon with (i := i1 mod size) by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
          Exists Tsh ki HT T; rewrite HHi; entailer!.
          apply derives_refl.
        * apply allp_right; intro sh0.
          apply allp_right; intro v0.
          rewrite <- wand_sepcon_adjoint, emp_sepcon.
          Intros HT T.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
          assert (0 <= i1 mod size < Zlength T) by omega.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
          rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
          rewrite 5sepcon_assoc; eapply derives_trans; [apply sepcon_derives, derives_refl|].
          { apply snap_master_update1 with (v' := if eq_dec ki 0 then k else ki).
            if_tac; auto. }
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd, bupd_mono].
          assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size; apply hash_range).
          assert (0 <= i < Zlength (rebase T (hash k))) by (rewrite Zlength_rebase; auto; omega).
          assert (fst (Znth i (rebase T (hash k))) = ki).
          { rewrite Znth_rebase by (auto; omega).
            replace (Zlength T) with size; replace ((i + hash k) mod size) with (i1 mod size); rewrite HHi; auto. }
          assert_PROP ((ki = k \/ ki = 0) -> lookup T k = Some (i1 mod size)) as Hindex.
          { rewrite prop_forall; apply allp_right; intro Hki.
            rewrite <- 3sepcon_assoc, sepcon_comm.
            rewrite <- !sepcon_assoc, 5sepcon_assoc.
            apply sepcon_derives_prop, entries_lookup; auto.
            rewrite HHi; destruct Hki; subst; auto. }
          rewrite !sepcon_assoc; eapply derives_trans, fupd_frame_r; subst v0; cancel.
          rewrite !sepcon_assoc, sepcon_comm; apply sepcon_derives, derives_refl.
          rewrite <- !sepcon_assoc, sepcon_comm.
          rewrite sepcon_comm; apply modus_ponens_wand'.
          unfold hashtable; Exists (upd_Znth (i1 mod size) T (if eq_dec ki 0 then k else ki, vi)).
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi, upd_Znth_same by omega; entailer!.
          { split; [rewrite upd_Znth_Zlength; auto|].
            split; [|if_tac; auto].
            if_tac; [subst | erewrite upd_Znth_triv; eauto].
            split; [apply wf_table_upd; auto|].
            intros.
            etransitivity; eauto; split; intros (Hin & ?); split; auto.
            - eapply In_upd_Znth_old; auto; try omega.
              rewrite HHi; intro X; inv X; tauto.
            - apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
          apply sepcon_derives; [apply derives_refl|].
          apply sepcon_list_derives; rewrite !upd_Znth_Zlength;
            rewrite !Zlength_map, !Zlength_upto, !Z2Nat.id; auto; try omega.
          intros; destruct (eq_dec i0 (i1 mod size)).
          { subst; rewrite !upd_Znth_same by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; auto; omega); auto. }
          rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; auto; omega).
          erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
          rewrite upd_Znth_diff'; auto. }
      Intros k1.
      focus_SEP 1.
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
        forward_if (PROP () ((LOCALx Q) (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: R)))) end.
      * if_tac; [discriminate|].
        replace_SEP 3 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
        forward_call (pki, |> P * (AS && cored) * ghost_snap k1 (Znth (i1 mod size) lg), Full_set iname, Empty_set iname,
          fun sh v => !!(sh = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
            forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
            !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) &&
            ghost_master1 ki (Znth (i1 mod size) lg) * data_at Tsh tint (vint vi) pvi *
            excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
              (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
            ghost_snap k1 (Znth (i1 mod size) lg) *
            (hashtable H g lg entries -* |={Empty_set iname,Full_set iname}=> |> P),
          fun v : Z => |> P * (!!(v = k1) && ghost_snap k1 (Znth (i1 mod size) lg))).
        { cancel.
          rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
          rewrite <- emp_sepcon at 1; apply sepcon_derives.
          + rewrite <- wand_sepcon_adjoint, emp_sepcon.
            eapply derives_trans; [apply sepcon_derives; [apply sepcon_derives, andp_left1|]; apply derives_refl|].
            unfold AS.
            eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
            eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
            Intros HT.
            eapply derives_trans; [apply sepcon_derives; [apply sepcon_derives, andp_left1|]; apply derives_refl|].
            unfold hashtable at 1; Intros T.
            rewrite extract_nth_sepcon with (i := i1 mod size)
              by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
            erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
            unfold hashtable_entry.
            rewrite Hpi.
            destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
            Exists Tsh ki HT T; rewrite HHi; entailer!.
            apply derives_refl.
          + apply allp_right; intro sh0.
            apply allp_right; intro v0.
            rewrite <- wand_sepcon_adjoint, emp_sepcon.
            Intros HT T.
            destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
            rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
            rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
            rewrite snap_master_join1; Intros.
            rewrite <- (prop_true_andp _ (ghost_master1 _ _) H28).
            rewrite <- (@snap_master_join1 _ _ zero_order).
            destruct H28; [contradiction | subst].
            rewrite prop_true_andp by auto.
            eapply derives_trans, fupd_frame_r; cancel.
            apply modus_ponens_wand'.
            unfold hashtable; Exists T.
            rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ _)
              by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
            erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
            unfold hashtable_entry.
            rewrite Hpi, HHi; entailer!.
            apply derives_refl. }
        Intros k2; subst.
        forward_if (k1 = k).
        { eapply semax_pre; [|apply semax_continue].
          unfold POSTCONDITION, abbreviate, overridePost, loop1_ret_assert, frame_ret_assert,
            function_body_ret_assert, RA_continue.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
          rewrite Zmod_mod, Z2Nat.inj_add, upto_app, map_app, sepcon_app by omega.
          change (upto (Z.to_nat 1)) with [0]; simpl fold_right; rewrite Z2Nat.id, Z.add_0_r by omega.
          replace ((i + hash k) mod size) with (i1 mod size); rewrite upd_Znth_same by omega; entailer!.
          { assert (Int.min_signed <= i1 mod size < Int.max_signed).
            { split; etransitivity; try apply Z_mod_lt; auto; try computable.
              setoid_rewrite (proj2_sig has_size); computable. }
            rewrite Int.signed_repr by omega; auto. }
          erewrite map_ext_in; [apply derives_refl|]; simpl; intros.
          rewrite upd_Znth_diff'; auto; try omega.
          replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
          rewrite In_upto, Z2Nat.id in * by omega.
          rewrite !Zmod_small in X; omega. }
        { forward.
          entailer!. }
        entailer!.
      * forward.
        if_tac; [|contradiction].
        subst; entailer!.
      * entailer!.
    + forward.
      subst; entailer!.
    + forward; setoid_rewrite Hpi.
      { entailer!. }
      forward_call (pvi, v, |> P * (AS && cored) * ghost_snap k (Znth (i1 mod size) lg) *
          data_at sh (tarray tentry size) entries (gv _m_entries) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
             (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))),
        Full_set iname, Empty_set iname,
        fun sh1 => !!(sh1 = Tsh) && data_at sh (tarray tentry size) entries (gv _m_entries) *
        EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
            forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
        !!(ki = k /\ repable_signed vi) && ghost_master1 k (Znth (i1 mod size) lg) *
        data_at Tsh tint (vint k) pki * excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
            (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
          ghost_snap k (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
             (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))) *
          (ALL y : unit, (data_at sh (tarray tentry size) entries (gv _m_entries) *
              hashtable (map_upd H k v) g lg entries) -* |={Empty_set iname,Full_set iname}=> Q y),
        Q tt).
      { cancel.
        rewrite <- emp_sepcon, <- sepcon_emp at 1.
        apply sepcon_derives; [|cancel].
        apply sepcon_derives, derives_refl.
        rewrite <- emp_sepcon at 1; apply sepcon_derives.
        + rewrite <- wand_sepcon_adjoint, emp_sepcon.
          rewrite !sepcon_assoc; eapply derives_trans.
          { apply sepcon_derives, sepcon_derives; [|apply andp_left1|]; apply derives_refl. }
          rewrite <- sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
          eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
          Intros HT.
          eapply derives_trans; [apply sepcon_derives; [apply sepcon_derives, andp_left2|]; apply derives_refl|].
          unfold hashtable at 1; Intros T.
          rewrite extract_nth_sepcon with (i := i1 mod size)
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
          rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
          rewrite snap_master_join1, !sepcon_andp_prop'; Intros.
          rewrite <- (prop_true_andp _ (ghost_master1 _ _) H20).
          rewrite <- (@snap_master_join1 _ _ zero_order).
          destruct H20; [contradiction | subst].
          Exists Tsh HT T; rewrite HHi; entailer!.
          rewrite sepcon_comm; apply derives_refl.
        + apply allp_right; intro sh0.
          rewrite <- wand_sepcon_adjoint, emp_sepcon.
          Intros HT T.
          destruct (Znth (i1 mod size) T) eqn: HHi; Intros.
          rewrite <- !sepcon_assoc.
          rewrite (sepcon_comm _(excl g HT)), !sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives, derives_refl|].
          { apply exclusive_update with (v' := map_upd HT k v). }
          eapply derives_trans; [apply bupd_frame_r|].
          apply fupd_bupd_elim.
          rewrite <- !sepcon_assoc, sepcon_comm.
          rewrite <- !sepcon_assoc, sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives; [apply derives_refl|]|].
          { eapply derives_trans, bupd_sepcon.
            apply sepcon_derives; [apply own_dealloc|].
            apply snaps_dealloc. }
          eapply derives_trans; [apply bupd_frame_l | apply fupd_bupd_elim].
          rewrite !sepcon_assoc, sepcon_comm.
          eapply derives_trans; [eapply sepcon_derives, allp_left; apply derives_refl|].
          apply modus_ponens_wand'.
          unfold hashtable.
          Exists (upd_Znth (i1 mod size) T (k, v)).
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite upd_Znth_same by omega.
          assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size; apply hash_range).
          rewrite Hpi; entailer!.
          { split; [rewrite upd_Znth_Zlength; omega|].
            split; [apply wf_table_upd_same; rewrite ?HHi; auto|].
            intros; unfold map_upd; if_tac.
            * split; [intro X; inv X; split; auto; apply upd_Znth_In|].
              subst; intros (Hin & ?).
              apply In_Znth in Hin; destruct Hin as (j & Hj & Hjth).
              destruct (eq_dec j (i1 mod size)).
              { subst; rewrite upd_Znth_same in Hjth by omega; inv Hjth; auto. }
              rewrite upd_Znth_diff' in Hjth by (auto; omega).
              match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto;
                exploit (H k (i1 mod size)); rewrite ?HHi; auto end.
              congruence.
            * etransitivity; eauto; split; intros (Hin & ?); split; auto.
              -- eapply In_upd_Znth_old; auto; try omega.
                 rewrite HHi; intro X; inv X; contradiction.
              -- apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
          apply sepcon_derives; [apply derives_refl|].
          apply sepcon_list_derives; rewrite !upd_Znth_Zlength;
            rewrite !Zlength_map, !Zlength_upto, !Z2Nat.id; auto; try omega.
          intros; destruct (eq_dec i0 (i1 mod size)).
          { subst; rewrite !upd_Znth_same by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; auto; omega); auto. }
          rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; auto; omega).
          erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
          rewrite upd_Znth_diff'; auto; omega. }
      forward.
      Exists tt; entailer!.
  - Intros i i1 keys.
    forward.
    { entailer!.
      rewrite (Int.signed_repr 1) by computable; omega. }
    Exists (i + 1) (i1 + 1) keys; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash k) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_atomic_function.
  destruct x as (((((k, gv), sh), entries), g), lg); Intros.
  forward_call k.
  pose proof size_pos.
  unfold atomic_shift; Intros P.
  set (AS := _ -* _).
  forward_loop (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); gvars gv)
    SEP (|> P; AS && cored; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))))%assert
    continue: (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (Int.min_signed <= Int.signed (Int.repr i1) < Int.max_signed;
          i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 (i + 1) (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); gvars gv)
    SEP (|> P; AS && cored; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat (i + 1))))))%assert.
  { Exists 0 (k * 654435761)%Z (repeat 0 (Z.to_nat size)); rewrite sublist_nil; entailer!.
    split; [apply hash_size|].
    rewrite Zlength_repeat, Z2Nat.id; auto; omega.
    { simpl; auto. } }
  - Intros i i1 keys; forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    replace (2 ^ 14) with size by (setoid_rewrite (proj2_sig has_size); auto).
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) as Hi1' by omega.
    match goal with H : Forall _ _ |- _ => pose proof (Forall_Znth _ _ _ Hi1' H) as Hptr end.
    destruct (Znth (i1 mod size) entries) as (pki, pvi) eqn: Hpi; destruct Hptr.
    forward; setoid_rewrite Hpi.
    { entailer!. }
    assert (Zlength (rebase keys (hash k)) = size) as Hrebase.
    { rewrite Zlength_rebase; replace (Zlength keys) with size; auto; apply hash_range. }
    replace_SEP 1 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
    forward_call (pki, |> P * (AS && cored) * fold_right sepcon emp (map (fun i0 : Z =>
        ghost_snap (Znth ((i0 + hash k) mod size) keys) (Znth ((i0 + hash k) mod size) lg))
        (upto (Z.to_nat i))) * data_at sh (tarray tentry size) entries (gv _m_entries), Full_set iname, Empty_set iname,
      fun sh1 v => !!(sh1 = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
      forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
      !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) && ghost_master1 ki (Znth (i1 mod size) lg) *
      data_at Tsh tint (vint vi) pvi * excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
          (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
        fold_right sepcon emp (map (fun i0 : Z => ghost_snap (Znth ((i0 + hash k) mod size) keys)
          (Znth ((i0 + hash k) mod size) lg)) (upto (Z.to_nat i))) *
        data_at sh (tarray tentry size) entries (gv _m_entries) *
      ((hashtable H g lg entries -*
              (|={ Empty_set iname, Full_set iname }=> |> P)) &&
             (ALL y : Z ,
              data_at sh (tarray tentry size) entries (gv _m_entries) *
              (!! (if eq_dec y 0 then H k = None else H k = Some y) &&
               hashtable H g lg entries) -*
              (|={ Empty_set iname, Full_set iname }=> Q y))),
      fun v => if eq_dec v 0 then Q v else |> P * ghost_snap v (Znth (i1 mod size) lg) *
        fold_right sepcon emp (map (fun i0 : Z => ghost_snap (Znth ((i0 + hash k) mod size) keys)
          (Znth ((i0 + hash k) mod size) lg)) (upto (Z.to_nat i))) *
        data_at sh (tarray tentry size) entries (gv _m_entries)).
    { cancel.
      rewrite sepcon_comm, <- emp_sepcon at 1.
      rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel].
      apply sepcon_derives, derives_refl.
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      + rewrite <- wand_sepcon_adjoint, emp_sepcon.
        unfold AS.
        rewrite sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives; [apply sepcon_derives, andp_left1|]; apply derives_refl|].
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand |].
        eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
        Intros HT.
        unfold hashtable at 1; Intros T.
        rewrite extract_nth_sepcon with (i := i1 mod size)
          by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
        unfold hashtable_entry.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        Intros; Exists Tsh ki HT T; rewrite HHi; entailer!.
        apply derives_refl.
      + apply allp_right; intro sh0.
        apply allp_right; intro v0.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        Intros HT T.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
        if_tac.
        * subst v0 ki.
          rewrite <- !sepcon_assoc, 3sepcon_assoc, sepcon_comm.
          assert_PROP (lookup T k = Some (i1 mod size)) as Hindex.
          { rewrite <- !sepcon_assoc, 5sepcon_assoc.
            apply sepcon_derives_prop, (entries_lookup k); auto.
            rewrite HHi; auto. }
          eapply derives_trans.
          { rewrite !sepcon_assoc, sepcon_comm, !sepcon_assoc.
          apply sepcon_derives, derives_refl; apply snaps_dealloc. }
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
          rewrite emp_sepcon, sepcon_comm, sepcon_assoc.
          eapply derives_trans.
          { eapply sepcon_derives; [eapply andp_left2, allp_left|]; apply derives_refl. }
          rewrite sepcon_comm; apply modus_ponens_wand'.
          unfold hashtable; Exists T.
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi, HHi, if_true by auto; entailer!.
          destruct (HT k) eqn: Hk; auto.
          match goal with H : forall k v, _ <-> _ |- _ => rewrite H in Hk end.
          destruct Hk as (Hk & ?); apply In_Znth in Hk.
          destruct Hk as (j & ? & Hjth).
          match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto end.
          rewrite Hindex; congruence.
          { apply derives_refl. }
        * rewrite sepcon_comm, !sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply (make_snap(ORD := zero_order))|].
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
          rewrite !sepcon_assoc; eapply derives_trans, fupd_frame_r.
          subst v0; cancel.
          rewrite (sepcon_comm _ (_ && _)), !sepcon_assoc.
          eapply derives_trans, modus_ponens_wand'.
          { rewrite sepcon_comm; apply sepcon_derives, andp_left1; apply derives_refl. }
          unfold hashtable; Exists T.
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi, HHi; entailer!.
          apply derives_refl. }
    Intros k1.
    forward_if (k1 <> k).
    + subst; if_tac; [contradiction | Intros].
      forward; setoid_rewrite Hpi.
      { entailer!. }
      forward_call (pvi, |> P * (AS && cored) * ghost_snap k (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i0 : Z => ghost_snap (Znth ((i0 + hash k) mod size) keys) (Znth ((i0 + hash k) mod size) lg))
          (upto (Z.to_nat i))) * data_at sh (tarray tentry size) entries (gv _m_entries),
        Full_set iname, Empty_set iname,
        fun sh1 v => !!(sh1 = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
            forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
        !!(ki = k /\ vi = v /\ repable_signed vi) && ghost_master1 k (Znth (i1 mod size) lg) *
        data_at Tsh tint (vint k) pki * excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
            (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
          ghost_snap k (Znth (i1 mod size) lg) * fold_right sepcon emp (map (fun i0 : Z =>
            ghost_snap (Znth ((i0 + hash k) mod size) keys) (Znth ((i0 + hash k) mod size) lg))
            (upto (Z.to_nat i))) * data_at sh (tarray tentry size) entries (gv _m_entries) *
        (ALL y : Z ,
              data_at sh (tarray tentry size) entries (gv _m_entries) *
              (!! (if eq_dec y 0 then H k = None else H k = Some y) &&
               hashtable H g lg entries) -*
              (|={ Empty_set iname, Full_set iname }=> Q y)),
        Q).
      { cancel.
        rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
        rewrite <- emp_sepcon at 1; apply sepcon_derives.
        + rewrite <- wand_sepcon_adjoint, emp_sepcon.
          unfold AS.
          rewrite 2sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives; [apply sepcon_derives, andp_left1|]; apply derives_refl|].
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
          eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
          Intros HT.
          eapply derives_trans; [apply sepcon_derives; [apply sepcon_derives, andp_left2|]; apply derives_refl|].
          unfold hashtable at 1; Intros T.
          rewrite extract_nth_sepcon with (i := i1 mod size)
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
          rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
          rewrite snap_master_join1, !sepcon_andp_prop'; Intros.
          rewrite <- (prop_true_andp _ (ghost_master1 _ _) H19).
          rewrite <- (@snap_master_join1 _ _ zero_order).
          destruct H19; [contradiction | subst].
          Exists Tsh vi HT T; rewrite HHi; entailer!.
          rewrite sepcon_comm; apply derives_refl.
        + apply allp_right; intro sh0.
          apply allp_right; intro v0.
          rewrite <- wand_sepcon_adjoint, emp_sepcon.
          Intros HT T.
          destruct (Znth (i1 mod size) T) eqn: HHi; Intros.
          subst; assert_PROP (lookup T k = Some (i1 mod size)) as Hindex.
          { rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)), <- !sepcon_assoc,
              (sepcon_comm _ (fold_right _ _ _)), <- !sepcon_assoc, 6sepcon_assoc.
            apply sepcon_derives_prop, entries_lookup; auto.
            rewrite HHi; auto. }
          rewrite <- !sepcon_assoc, 3sepcon_assoc, sepcon_comm.
          rewrite <- !sepcon_assoc, 6sepcon_assoc.
          eapply derives_trans.
          { apply sepcon_derives, derives_refl.
            eapply derives_trans, bupd_sepcon.
            apply sepcon_derives; [apply own_dealloc | apply snaps_dealloc]. }
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
          rewrite !emp_sepcon, sepcon_comm, sepcon_assoc.
          eapply derives_trans, modus_ponens_wand'.
          { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl|].
            eapply allp_left, derives_refl. }
          unfold hashtable; Exists T.
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi, HHi; entailer!.
          if_tac.
          * destruct (HT k) eqn: Hk; auto.
            match goal with H : forall k v, _ <-> _ |- _ => rewrite H in Hk end.
            destruct Hk as (Hk & ?); apply In_Znth in Hk.
            destruct Hk as (j & ? & Hjth).
            match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto end.
            rewrite Hindex; congruence.
          * match goal with H : forall k v, ?P <-> _ |- _ => rewrite H end.
            split; auto.
            exploit (Znth_In (i1 mod size) T); [omega|].
            rewrite HHi; auto.
          * apply derives_refl. }
      unfold POSTCONDITION, abbreviate; simpl map.
      Intros v'; forward.
      Exists v'; entailer!.
    + forward.
      entailer!.
    + Intros; forward_if (k1 <> 0).
      * subst; rewrite eq_dec_refl.
        viewshift_SEP 1 emp.
        { go_lower.
          apply andp_left2, cored_emp. }
        unfold POSTCONDITION, abbreviate; simpl map.
        forward.
        Exists 0; entailer!.
      * if_tac; [contradiction|].
        forward.
        entailer!.
      * intros.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
        rewrite Z2Nat.inj_add, upto_app, map_app, sepcon_app by omega.
        change (upto (Z.to_nat 1)) with [0]; simpl fold_right.
        rewrite Z2Nat.id, Z.add_0_r by omega.
        Intros; rewrite if_false by auto.
        replace ((i + hash k) mod size) with (i1 mod size); rewrite upd_Znth_same by omega; entailer!.
        { split.
          { assert (Int.min_signed <= i1 mod size < Int.max_signed).
            { split; etransitivity; try apply Z_mod_lt; auto; try computable.
              setoid_rewrite (proj2_sig has_size); computable. }
            rewrite Int.signed_repr by omega; auto. }
          split; [rewrite Zmod_mod; auto|].
          split; [rewrite upd_Znth_Zlength; auto; omega|].
          replace (i1 mod size) with ((i + hash k) mod size); replace size with (Zlength keys);
            rewrite !rebase_upd' by (try omega; replace (Zlength keys) with size; apply Z_mod_lt; omega).
          rewrite sublist_upd_Znth_lr by (try omega; setoid_rewrite Hrebase; omega).
          rewrite sublist_split with (mid := i), sublist_len_1 by (try omega; setoid_rewrite Hrebase; omega).
          rewrite Z.sub_0_r, upd_Znth_app2, Forall_app; rewrite Zlength_sublist;
            rewrite ?Zlength_cons, ?Zlength_nil; try omega; try (setoid_rewrite Hrebase; omega).
          split; auto.
          rewrite Z.sub_0_r, Zminus_diag, upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same
            by (auto; omega).
          repeat constructor; auto; tauto. }
        erewrite map_ext_in; [apply derives_refl|]; intros; simpl.
        rewrite upd_Znth_diff'; auto; try omega.
        replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
        rewrite In_upto, Z2Nat.id in * by omega.
        rewrite !Zmod_small in X; omega.
  - Intros i i1 keys.
    forward.
    { entailer!.
      rewrite (Int.signed_repr 1) by computable; omega. }
    Exists (i + 1) (i1 + 1) keys; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash k) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma body_add_item : semax_body Vprog Gprog f_add_item add_item_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((k, v), gv), sh), entries), g), lg); Intros.
  unfold atomic_shift; Intros P.
  set (AS := _ -* _).
  forward_call k.
  pose proof size_pos.
  forward_loop (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (|> P; AS && cored; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))))%assert
    continue: (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (Int.min_signed <= Int.signed (Int.repr i1) < Int.max_signed;
          i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 (i + 1) (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (|> P; AS && cored; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat (i + 1))))))%assert.
  { Exists 0 (k * 654435761)%Z (repeat 0 (Z.to_nat size)); rewrite sublist_nil; entailer!.
    split; [apply hash_size|].
    rewrite Zlength_repeat, Z2Nat.id; auto; omega.
    { simpl; auto. } }
  - Intros i i1 keys; forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    replace (2 ^ 14) with size by (setoid_rewrite (proj2_sig has_size); auto).
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) as Hi1' by omega.
    match goal with H : Forall _ _ |- _ => pose proof (Forall_Znth _ _ _ Hi1' H) as Hptr end.
    destruct (Znth (i1 mod size) entries) as (pki, pvi) eqn: Hpi; destruct Hptr.
    forward; setoid_rewrite Hpi.
    { entailer!. }
    assert (Zlength (rebase keys (hash k)) = size) as Hrebase.
    { rewrite Zlength_rebase; replace (Zlength keys) with size; auto; apply hash_range. }
    replace_SEP 1 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
    forward_call (pki, |> P * (AS && cored), Full_set iname, Empty_set iname,
      fun sh v => !!(sh = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
      forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
      !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) && ghost_master1 ki (Znth (i1 mod size) lg) *
      data_at Tsh tint (vint vi) pvi * excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
          (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
      (hashtable H g lg entries -* |={Empty_set iname,Full_set iname}=> |> P),
      fun v : Z => |> P * ghost_snap v (Znth (i1 mod size) lg)).
    { cancel.
      rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      + rewrite <- wand_sepcon_adjoint, emp_sepcon.
        unfold AS.
        eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
        eapply derives_trans; [apply modus_ponens_wand|].
        apply fupd_mono.
        Intros HT.
        unfold hashtable at 1; Intros T.
        rewrite extract_nth_sepcon with (i := i1 mod size)
          by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
        unfold hashtable_entry.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        rewrite <- !sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives, andp_left1; apply derives_refl|].
        Intros; Exists Tsh ki HT T; rewrite HHi; entailer!.
        apply derives_refl.
      + apply allp_right; intro sh0.
        apply allp_right; intro v0.
        rewrite <- wand_sepcon_adjoint, emp_sepcon.
        Intros HT T.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
        rewrite !sepcon_assoc; eapply derives_trans.
        { apply sepcon_derives, derives_refl.
          apply (make_snap(ORD := zero_order)). }
        eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
        eapply derives_trans, fupd_frame_r.
        subst v0; cancel.
        apply modus_ponens_wand'.
        unfold hashtable; Exists T.
        rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ _)
          by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
        erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
        unfold hashtable_entry.
        rewrite Hpi, HHi; entailer!.
        apply derives_refl. }
    Intros k1.
    focus_SEP 1.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: R)))) end.
    + assert (forall k1, (k1 <> k /\ k1 <> 0) ->
        Zlength (upd_Znth (i1 mod size) keys k1) = size /\
        Forall (fun z => z <> 0 /\ z <> k)
          (sublist 0 (i + 1) (rebase (upd_Znth (i1 mod size) keys k1) (hash k)))).
      { split; [rewrite upd_Znth_Zlength; auto; omega|].
        replace (i1 mod size) with ((i + hash k) mod size); replace size with (Zlength keys);
          rewrite !rebase_upd' by (try omega; replace (Zlength keys) with size; apply Z_mod_lt; omega).
        rewrite sublist_upd_Znth_lr by (try omega; setoid_rewrite Hrebase; omega).
        rewrite sublist_split with (mid := i), sublist_len_1 by (try omega; setoid_rewrite Hrebase; omega).
        rewrite Z.sub_0_r, upd_Znth_app2, Forall_app; rewrite Zlength_sublist;
          rewrite ?Zlength_cons, ?Zlength_nil; try omega; try (setoid_rewrite Hrebase; omega).
        split; auto.
        rewrite Z.sub_0_r, Zminus_diag, upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same
          by (auto; omega).
        repeat constructor; auto; tauto. }
      forward_if (k1 = 0).
      { eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost, loop1_ret_assert, frame_ret_assert,
          function_body_ret_assert, RA_continue.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
        rewrite Zmod_mod, Z2Nat.inj_add, upto_app, map_app, sepcon_app by omega.
        change (upto (Z.to_nat 1)) with [0]; simpl fold_right.
        rewrite Z2Nat.id, Z.add_0_r by omega.
        replace ((i + hash k) mod size) with (i1 mod size); rewrite upd_Znth_same by omega; entailer!.
        { assert (Int.min_signed <= i1 mod size < Int.max_signed).
          { split; etransitivity; try apply Z_mod_lt; auto; try computable.
            setoid_rewrite (proj2_sig has_size); computable. }
          rewrite Int.signed_repr by omega; auto. }
        erewrite map_ext_in; [apply derives_refl|]; intros; simpl.
        rewrite upd_Znth_diff'; auto; try omega.
        replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
        rewrite In_upto, Z2Nat.id in * by omega.
        rewrite !Zmod_small in X; omega. }
      { forward.
        entailer!. }
      Intros; subst.
      replace_SEP 2 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
      forward_call (pki, 0, k, |> P * (AS && cored) * ghost_snap 0 (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
            (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))),
        Full_set iname, Empty_set iname, fun sh v => !!(sh = Tsh) && EX H : _, EX T : _,
          !!(Zlength T = size /\ wf_table T /\
          forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
          !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) &&
          ghost_master1 ki (Znth (i1 mod size) lg) * data_at Tsh tint (vint vi) pvi *
          excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
            (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
          ghost_snap 0 (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))) *
         (hashtable H g lg entries -* |={Empty_set iname,Full_set iname}=> |> P),
        fun v : Z => |> P * ghost_snap (if eq_dec v 0 then k else v) (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
            (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i)))).
      { cancel.
        rewrite sepcon_comm, <- emp_sepcon at 1.
        rewrite <- sepcon_assoc.
        apply sepcon_derives; [|cancel]; apply sepcon_derives, derives_refl.
        rewrite <- emp_sepcon at 1; apply sepcon_derives.
        * rewrite <- wand_sepcon_adjoint, emp_sepcon.
          rewrite sepcon_assoc; unfold AS.
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
          eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
          Intros HT.
          unfold hashtable at 1; Intros T.
          rewrite extract_nth_sepcon with (i := i1 mod size) by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
          rewrite (sepcon_comm _ (_ && _)), !sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives; [apply andp_left1|]; apply derives_refl|].
          Exists Tsh ki HT T; rewrite HHi; entailer!.
          apply derives_refl.
        * apply allp_right; intro sh0.
          apply allp_right; intro v0.
          rewrite <- wand_sepcon_adjoint, emp_sepcon.
          Intros HT T.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
          assert (0 <= i1 mod size < Zlength T) by omega.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
          rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
          rewrite 5sepcon_assoc; eapply derives_trans; [apply sepcon_derives, derives_refl|].
          { apply snap_master_update1 with (v' := if eq_dec ki 0 then k else ki).
            if_tac; auto. }
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
          assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size; apply hash_range).
          assert (0 <= i < Zlength (rebase T (hash k))) by (rewrite Zlength_rebase; auto; omega).
          assert (fst (Znth i (rebase T (hash k))) = ki).
          { rewrite Znth_rebase by (auto; omega).
            replace (Zlength T) with size; replace ((i + hash k) mod size) with (i1 mod size); rewrite HHi; auto. }
          assert_PROP ((ki = k \/ ki = 0) -> lookup T k = Some (i1 mod size)) as Hindex.
          { rewrite prop_forall; apply allp_right; intro Hki.
            rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp _)),
              <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp _)).
            rewrite <- !sepcon_assoc, 5sepcon_assoc.
            apply sepcon_derives_prop, entries_lookup; auto.
            rewrite HHi; auto. }
          rewrite !sepcon_assoc; eapply derives_trans, fupd_frame_r.
          subst v0; cancel.
          rewrite (sepcon_comm _ (ghost_snap _ _)), !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
          rewrite <- !sepcon_assoc; apply modus_ponens_wand'.
          unfold hashtable; Exists (upd_Znth (i1 mod size) T (if eq_dec ki 0 then k else ki, vi)).
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi, upd_Znth_same by omega; entailer!.
          { split; [rewrite upd_Znth_Zlength; auto|].
            split; [|if_tac; auto].
            if_tac; [subst | erewrite upd_Znth_triv; eauto].
            split; [apply wf_table_upd; auto|].
            intros.
            etransitivity; eauto; split; intros (Hin & ?); split; auto.
            - eapply In_upd_Znth_old; auto; try omega.
              rewrite HHi; intro X; inv X; tauto.
            - apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
          apply sepcon_derives; [apply derives_refl|].
          apply sepcon_list_derives; rewrite !upd_Znth_Zlength;
            rewrite !Zlength_map, !Zlength_upto, !Z2Nat.id; auto; try omega.
          intros; destruct (eq_dec i0 (i1 mod size)).
          { subst; rewrite !upd_Znth_same by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; auto; omega); auto. }
          rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; auto; omega).
          erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
          rewrite upd_Znth_diff'; auto. }
      Intros k1.
      focus_SEP 1.
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
        forward_if (PROP () ((LOCALx Q) (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: R)))) end.
      * if_tac; [discriminate|].
        replace_SEP 3 ((AS && cored) * (AS && cored)) by (go_lower; apply cored_dup).
        forward_call (pki, |> P * (AS && cored) * ghost_snap k1 (Znth (i1 mod size) lg), Full_set iname, Empty_set iname,
          fun sh v => !!(sh = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
            forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
            !!(v = ki /\ repable_signed vi /\ (ki = 0 -> vi = 0)) &&
            ghost_master1 ki (Znth (i1 mod size) lg) * data_at Tsh tint (vint vi) pvi *
            excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
              (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
            ghost_snap k1 (Znth (i1 mod size) lg) *
            (hashtable H g lg entries -* |={Empty_set iname,Full_set iname}=> |> P),
          fun v : Z => |> P * (!!(v = k1) && ghost_snap k1 (Znth (i1 mod size) lg))).
        { cancel.
          rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
          rewrite <- emp_sepcon at 1; apply sepcon_derives.
          * rewrite <- wand_sepcon_adjoint, emp_sepcon.
            unfold AS.
            eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
            eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
            eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
            Intros HT.
            unfold hashtable at 1; Intros T.
            rewrite extract_nth_sepcon with (i := i1 mod size)
              by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
            erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
            unfold hashtable_entry.
            rewrite Hpi.
            destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
            rewrite (sepcon_comm _ (_ && _)), !sepcon_assoc.
            eapply derives_trans; [apply sepcon_derives; [apply andp_left1|]; apply derives_refl|].
            Exists Tsh ki HT T; rewrite HHi; entailer!.
            apply derives_refl.
          * apply allp_right; intro sh0.
            apply allp_right; intro v0.
            rewrite <- wand_sepcon_adjoint, emp_sepcon.
            Intros HT T.
            destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
            rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
            rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
            rewrite snap_master_join1, !sepcon_andp_prop'; Intros.
            rewrite <- (prop_true_andp _ (ghost_master1 _ _) H28).
            rewrite <- (@snap_master_join1 _ _ zero_order).
            destruct H28; [contradiction | subst].
            rewrite prop_true_andp by auto.
            eapply derives_trans, fupd_frame_r; cancel.
            apply modus_ponens_wand'.
            unfold hashtable; Exists T.
            rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ _)
              by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
            erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
            unfold hashtable_entry.
            rewrite Hpi, HHi; entailer!.
            apply derives_refl. }
        Intros k2; subst.
        forward_if (k1 = k).
        { eapply semax_pre; [|apply semax_continue].
          unfold POSTCONDITION, abbreviate, overridePost, loop1_ret_assert, frame_ret_assert,
            function_body_ret_assert, RA_continue.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
          rewrite Zmod_mod, Z2Nat.inj_add, upto_app, map_app, sepcon_app by omega.
          change (upto (Z.to_nat 1)) with [0]; simpl fold_right.
          rewrite Z2Nat.id, Z.add_0_r by omega.
          replace ((i + hash k) mod size) with (i1 mod size); rewrite upd_Znth_same by omega; entailer!.
          { assert (Int.min_signed <= i1 mod size < Int.max_signed).
          { split; etransitivity; try apply Z_mod_lt; auto; try computable.
            setoid_rewrite (proj2_sig has_size); computable. }
          rewrite Int.signed_repr by omega; auto. }
          erewrite map_ext_in; [apply derives_refl|]; intros; simpl.
          rewrite upd_Znth_diff'; auto; try omega.
          replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
          rewrite In_upto, Z2Nat.id in * by omega.
          rewrite !Zmod_small in X; omega. }
        { forward.
          entailer!. }
        entailer!.
      * forward.
        if_tac; [|contradiction].
        subst; entailer!.
      * entailer!.
    + forward.
      subst; entailer!.
    + forward; setoid_rewrite Hpi.
      { entailer!. }
      forward_call (pvi, 0, v, |> P * (AS && cored) * ghost_snap k (Znth (i1 mod size) lg) *
          fold_right sepcon emp (map (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
            (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))) *
          data_at sh (tarray tentry size) entries (gv _m_entries),
        Full_set iname, Empty_set iname, fun sh1 (v1 : Z) => !!(sh1 = Tsh) && EX H : _, EX T : _, !!(Zlength T = size /\ wf_table T /\
          forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) && let '(ki, vi) := Znth (i1 mod size) T in
          !!(ki = k /\ vi = v1 /\ repable_signed vi) && ghost_master1 k (Znth (i1 mod size) lg) *
          data_at Tsh tint (vint k) pki * excl g H * fold_right sepcon emp (upd_Znth (i1 mod size)
            (map (hashtable_entry T lg entries) (upto (Z.to_nat size))) emp) *
          ghost_snap k (Znth (i1 mod size) lg) * fold_right sepcon emp (map (fun i =>
            ghost_snap (Znth ((i + hash k) mod size) keys) (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))) *
          data_at sh (tarray tentry size) entries (gv _m_entries) *
          (ALL y : bool, (data_at sh (tarray tentry size) entries (gv _m_entries) *
              (!! (H k = None <-> y = true) &&
               hashtable (if y then map_upd H k v else H) g lg entries)) -* |={Empty_set iname,Full_set iname}=> Q y),
        fun v => Q (if eq_dec v 0 then true else false)).
      { cancel.
        rewrite <- emp_sepcon, <- sepcon_emp at 1.
        apply sepcon_derives; [|cancel].
        apply sepcon_derives, derives_refl.
        rewrite <- emp_sepcon at 1; apply sepcon_derives.
        + rewrite <- wand_sepcon_adjoint, emp_sepcon.
          rewrite 2sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply sepcon_derives, andp_left1; apply derives_refl|].
          eapply derives_trans; [apply sepcon_derives, derives_refl; apply modus_ponens_wand|].
          eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
          Intros HT.
          unfold hashtable at 1; Intros T.
          rewrite extract_nth_sepcon with (i := i1 mod size)
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          rewrite Hpi.
          destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi; Intros.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_master1 _ _)).
          rewrite (sepcon_comm _ (ghost_snap _ _)), <- !sepcon_assoc.
          rewrite snap_master_join1, !sepcon_andp_prop'; Intros.
          rewrite <- (prop_true_andp _ (ghost_master1 _ _) H20).
          rewrite <- (@snap_master_join1 _ _ zero_order).
          destruct H20; [contradiction | subst].
          rewrite (sepcon_comm _ (_ && _)), !sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives; [apply andp_left2|]; apply derives_refl|].
          Exists Tsh vi HT T; rewrite HHi; entailer!.
          rewrite sepcon_comm; apply derives_refl.
        + apply allp_right; intro sh0.
          apply allp_right; intro v0.
          rewrite <- wand_sepcon_adjoint, emp_sepcon.
          Intros HT T.
          destruct (Znth (i1 mod size) T) eqn: HHi; Intros.
          rewrite <- !sepcon_assoc, (sepcon_comm _ (excl g HT)), !sepcon_assoc.
          eapply derives_trans; [apply sepcon_derives, derives_refl|].
          { apply exclusive_update with (v' := if eq_dec v0 0 then map_upd HT k v else HT). }
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
          assert_PROP (lookup T k = Some (i1 mod size)) as Hindex.
          { rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)), <- !sepcon_assoc,
              (sepcon_comm _ (fold_right _ _ _)), <- !sepcon_assoc, 6sepcon_assoc.
            apply sepcon_derives_prop, entries_lookup; auto.
            rewrite HHi; auto. }
          rewrite <- 4sepcon_assoc, sepcon_comm, <- !sepcon_assoc, 6sepcon_assoc.
          eapply derives_trans.
          { apply sepcon_derives, derives_refl.
            eapply derives_trans, bupd_sepcon.
            apply sepcon_derives; [apply own_dealloc | apply snaps_dealloc]. }
          eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
          rewrite !emp_sepcon, sepcon_comm, sepcon_assoc, sepcon_comm.
          eapply derives_trans; [eapply sepcon_derives, allp_left; apply derives_refl|].
          rewrite <- sepcon_assoc; apply modus_ponens_wand'.
          unfold hashtable.
          Exists (if eq_dec v0 0 then upd_Znth (i1 mod size) T (k, v) else T).
          rewrite extract_nth_sepcon with (i := i1 mod size)(l := map _ (upto (Z.to_nat size)))
            by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega).
          erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; omega).
          unfold hashtable_entry.
          if_tac; subst.
          * rewrite upd_Znth_same by omega.
            assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size; apply hash_range).
            rewrite Hpi; entailer!.
            { assert (forall v', In (k, v') T -> v' = 0) as Hv'.
              { intros ? Hin.
                eapply In_Znth in Hin; destruct Hin as (j & ? & Hjth).
                match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto end.
                rewrite Hindex; intro X; inv X.
                rewrite HHi in Hjth; inv Hjth; auto. }
              split.
              { split; auto.
                destruct (HT k) eqn: Hk; auto.
                match goal with H : forall k v, _ <-> _ |- _ => rewrite H in Hk end.
                destruct Hk as (Hin & ?); specialize (Hv' _ Hin); contradiction. }
              split; [rewrite upd_Znth_Zlength; omega|].
              split; [apply wf_table_upd_same; rewrite ?HHi; auto|].
              intros; unfold map_upd; if_tac.
              * split; [intro X; inv X; split; auto; apply upd_Znth_In|].
                subst; intros (Hin & ?).
                apply In_upd_Znth in Hin; destruct Hin as [Hin | Hin]; [inv Hin; auto|].
                specialize (Hv' _ Hin); contradiction.
              * etransitivity; eauto; split; intros (Hin & ?); split; auto.
                -- eapply In_upd_Znth_old; auto; try omega.
                   rewrite HHi; intro X; inv X; contradiction.
                -- apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
            apply sepcon_derives; [apply derives_refl|].
            apply sepcon_list_derives; rewrite !upd_Znth_Zlength;
              rewrite !Zlength_map, !Zlength_upto, !Z2Nat.id; auto; try omega.
            intros; destruct (eq_dec i0 (i1 mod size)).
            { subst; rewrite !upd_Znth_same by (rewrite Zlength_map, Zlength_upto, Z2Nat.id; auto; omega); auto. }
            rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; auto; omega).
            erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
            rewrite upd_Znth_diff'; auto; omega.
          * rewrite Hpi, HHi; entailer!.
            split; [|discriminate].
            assert (HT k = Some v0) as X; [|rewrite X; discriminate].
            match goal with H : forall k v, _ <-> _ |- _ => rewrite H end.
            split; auto; rewrite <- HHi; apply Znth_In; omega.
            apply derives_refl. }
      unfold POSTCONDITION, abbreviate; simpl map.
      Intros v'; forward.
      Exists (if eq_dec v' 0 then true else false); entailer!.
      if_tac; auto.
  - Intros i i1 keys.
    forward.
    { entailer!.
      rewrite (Int.signed_repr 1) by computable; omega. }
    Exists (i + 1) (i1 + 1) keys; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash k) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Opaque Znth.

Lemma body_init_table : semax_body Vprog Gprog f_init_table init_table_spec.
Proof.
  start_function.
  forward_for_simple_bound size (EX i : Z, EX entries : list (val * val),
    PROP (Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength entries = i)
    LOCAL (gvars gv)
    SEP (@data_at CompSpecs Ews (tarray tentry size) (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i))) (gv _m_entries);
         fold_right sepcon emp (map (fun x =>
           malloc_token Tsh tint (fst x) * malloc_token Tsh tint (snd x)) entries);
         EX lg : list gname, !!(Zlength lg = i) && fold_right sepcon emp (map (fun j =>
           hashtable_entry (repeat (0, 0) (Z.to_nat size)) lg entries j) (upto (Z.to_nat i))))).
  { setoid_rewrite (proj2_sig has_size); reflexivity. }
  { pose proof size_pos; omega. }
  { setoid_rewrite (proj2_sig has_size); computable. }
  - Exists (@nil (val * val)) (@nil gname); entailer!.
    rewrite data_at__eq; unfold default_val; simpl.
    rewrite repeat_list_repeat, Z.sub_0_r; apply derives_refl.
  - Intros lg.
    ghost_alloc (ghost_master1 0).
    Intros gk.
    forward_call tint.
    { split; auto; simpl; computable. }
    Intros pk.
    rewrite sepcon_map; Intros.
    repeat forward.
    forward_call tint.
    { split; auto; simpl; computable. }
    Intros pv.
    repeat forward.
    assert (0 <= i < Zlength (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i)))).
    { rewrite Zlength_app, Zlength_repeat, Z2Nat.id; omega. }
    rewrite upd_Znth_twice, upd_Znth_same by auto.
    go_lower; Exists (entries ++ [(pk, pv)]) (lg ++ [gk]).
    rewrite !Z2Nat.inj_add, !upto_app, !map_app, !sepcon_app, !Z2Nat.id by omega.
    change (upto (Z.to_nat 1)) with [0]; unfold hashtable_entry at 3; simpl.
    rewrite Z.add_0_r, !app_Znth2 by omega.
    replace (Zlength entries) with i; replace (Zlength lg) with i; rewrite Zminus_diag, !Znth_0_cons.
    rewrite Znth_repeat', !Zlength_app, !Zlength_cons, !Zlength_nil by (rewrite Z2Nat.id; omega).
    entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    rewrite upd_init, <- app_assoc by (auto; omega); cancel.
    rewrite <- sepcon_map; cancel.
    apply sepcon_list_derives; rewrite !Zlength_map, !Zlength_upto; auto.
    rewrite <- Zlength_correct; intros.
    erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, <- Zlength_correct; auto; omega).
    unfold hashtable_entry; rewrite !app_Znth1 by omega; apply derives_refl.
  - Intros entries lg.
    rewrite Zminus_diag, app_nil_r.
    ghost_alloc (fun g => excl g (@empty_map Z Z)).
    Intro g.
    forward.
    unfold hashtable; Exists entries g lg (repeat (0, 0) (Z.to_nat size)); entailer!.
    split; [rewrite Zlength_repeat, Z2Nat.id; auto; pose proof size_pos; omega|].
    split.
    + intros ??? Hj.
      setoid_rewrite Znth_repeat in Hj; simpl in Hj; subst; contradiction.
    + split; [discriminate|].
      intros (Hin & ?); apply repeat_spec in Hin; inv Hin; contradiction.
    + apply sepcon_derives; erewrite map_ext; try apply derives_refl; auto.
      intros (?, ?); auto.
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
  f_equal.
  apply prop_ext; split; intros (? & ? & ? & Halign & ?); repeat split; auto.
  - destruct p; try contradiction; simpl in *.
    inv Halign; try discriminate.
    constructor; auto.
    intros ? Hi; specialize (H7 _ Hi).
    inv H7; econstructor; eauto.
  - destruct p; try contradiction; simpl in *.
    inv Halign; try discriminate.
    constructor; auto.
    intros ? Hi; specialize (H7 _ Hi).
    inv H7; econstructor; eauto.
Qed.

Lemma f_pred_exclusive : forall tsh sh gsh (entries : list (val * val)) gh p t locksp lockt resultsp res,
  readable_share sh ->
  exclusive_mpred (f_lock_pred tsh sh gsh entries gh p t locksp lockt resultsp res).
Proof.
  intros; unfold f_lock_pred.
  apply selflock_exclusive.
  unfold f_lock_inv.
  eapply derives_exclusive, exclusive_sepcon1 with
    (P := @data_at CompSpecs sh (tarray tentry size) entries p)(Q := EX b1 : bool, EX b2 : bool,
    EX b3 : bool, EX h : nat -> option hashtable_hist_el, _), data_at_exclusive; auto.
  - Intros b1 b2 b3 h; Exists b1 b2 b3 h.
    rewrite (sepcon_comm (ghost_hist _ _ _)), !sepcon_assoc.
    apply sepcon_derives; auto.
  - simpl.
    pose proof size_pos.
    rewrite Z.max_r; omega.
Qed.
Hint Resolve f_pred_exclusive.

Lemma apply_hist_app : forall h1 h2 H, apply_hist H (h1 ++ h2) =
  match apply_hist H h1 with Some H' => apply_hist H' h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a; rewrite IHh1; auto.
  - destruct (H k); if_tac; auto.
  - destruct (H k); simple_if_tac; auto.
Qed.

Lemma hashtable_entry_timeless : forall T lg entries i, timeless (hashtable_entry T lg entries i).
Proof.
  intros; unfold hashtable_entry.
  destruct (Znth i entries), (Znth i T).
  apply timeless_sepcon, data_at_timeless.
  apply timeless_sepcon, data_at_timeless.
  apply timeless_andp; [apply timeless_prop | apply own_timeless].
Qed.

Lemma hashtable_timeless : forall H g lg entries, timeless (hashtable H g lg entries).
Proof.
  intros; unfold hashtable.
  apply (timeless_exp nil); intro.
  apply timeless_sepcon; [apply timeless_andp; [apply timeless_prop | apply own_timeless]|].
  forget (upto (Z.to_nat size)) as l; clear; induction l; simpl.
  * apply timeless_emp.
  * apply timeless_sepcon; auto.
    apply hashtable_entry_timeless.
Qed.

Lemma hashtable_inv_timeless : forall gh g lg entries, timeless (hashtable_inv gh g lg entries).
Proof.
  intros; unfold hashtable_inv.
  apply (timeless_exp empty_map); intro.
  apply timeless_sepcon; [apply hashtable_timeless|].
  apply (timeless_exp nil); intro.
  apply timeless_andp; [apply timeless_prop|].
  unfold ghost_ref.
  apply (timeless_exp empty_map); intro.
  apply timeless_andp; [apply timeless_prop | apply own_timeless].
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (data_at_isptr Tsh); Intros.
  forward.
  rewrite <- lock_struct_array.
  forward.
  { entailer!.
    rewrite upd_Znth_same; auto. }
  forward.
  { entailer!.
    rewrite upd_Znth_same; auto. }
  rewrite !upd_Znth_same by auto.
  forward.
  forward_call (tint, tid).
  forward_for_simple_bound 3 (EX j : Z, EX ls : list bool, EX h : _,
    PROP (Zlength ls = j; add_events empty_map (map (fun j => HAdd (j + 1) 1 (Znth j ls)) (upto (Z.to_nat j))) h)
    LOCAL (temp _total (vint (Zlength (filter id ls))); temp _res res; temp _l lockt; temp _t (vint t);
           temp _arg tid; gvars gv)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         invariant i (hashtable_inv gh g lg entries);
         ghost_hist gsh h gh;
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) (upd_Znth t (repeat Vundef 3) lockt) (gv _thread_locks);
         data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) (gv _results);
         data_at_ Tsh tint res;
         lock_inv tsh lockt (f_lock_pred tsh sh gsh entries gh (gv _m_entries) t
                                         (gv _thread_locks) lockt (gv _results) res))).
  - Exists (@nil bool) (@empty_map nat hashtable_hist_el); entailer!.
  - forward_call (i0 + 1, 1, gv, sh, entries, g, lg,
      fun b => EX h' : _, !!(add_events h [HAdd (i0 + 1) 1 b] h') && ghost_hist gsh h' gh *
        data_at sh (tarray tentry size) entries (gv _m_entries), inv_names).
    { simpl; entailer!.
      { match goal with H : Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries |- _ =>
          eapply Forall_impl, H end; intros (?, ?); auto. }
      unfold atomic_shift.
      Exists (ghost_hist gsh h gh).
      rewrite invariant_dup.
      rewrite !sepcon_assoc; eapply derives_trans, sepcon_derives, derives_refl; [|apply now_later].
      cancel.
      rewrite !sepcon_assoc; apply sepcon_derives; [|cancel].
      apply andp_right, invariant_cored.
      eapply derives_trans; [apply fupd_intro|].
      rewrite <- wand_sepcon_adjoint.
      eapply derives_trans.
      { apply sepcon_derives; [apply derives_refl|].
        apply except0_timeless; [apply except0_intro|].
        apply own_timeless. }
      eapply derives_trans; [apply except0_frame_l | apply fupd_except0_elim].
      eapply derives_trans; [apply fupd_frame_r|].
      eapply derives_trans, fupd_trans; apply fupd_mono.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply inv_open with (E := Full_set _); constructor|].
      eapply derives_trans; [apply fupd_frame_r|].
      eapply derives_trans, fupd_trans; apply fupd_mono.
      rewrite !sepcon_assoc; eapply derives_trans.
      { apply sepcon_derives, derives_refl.
        apply except0_timeless; [apply except0_intro|].
        apply hashtable_inv_timeless. }
      eapply derives_trans; [apply except0_frame_r | apply fupd_except0_elim].
      unfold hashtable_inv; Intros HT hr.
      rewrite <- emp_sepcon at 1.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply fupd_intro_mask with (E2 := Empty_set _)|].
      { intro; right; intro X; inv X. }
      { intros ? X; inv X. }
      eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
      Exists HT; cancel.
      apply andp_right.
      + rewrite <- wand_sepcon_adjoint.
        rewrite !sepcon_assoc; eapply derives_trans; [apply fupd_frame_r|].
        eapply derives_trans, fupd_trans; apply fupd_mono.
        rewrite emp_sepcon, <- !sepcon_assoc, sepcon_comm.
        rewrite <- !sepcon_assoc.
        eapply derives_trans.
        { apply sepcon_derives, derives_refl.
          apply modus_ponens_wand'.
          eapply derives_trans, now_later.
          Exists HT hr; entailer!. }
        eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
        eapply derives_trans, now_later; cancel.
      + apply allp_right; intro b.
        rewrite <- wand_sepcon_adjoint; Intros.
        rewrite !sepcon_assoc; eapply derives_trans; [apply fupd_frame_r|].
        eapply derives_trans, fupd_trans; apply fupd_mono.
        rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm _ (ghost_hist _ _ _)).
        rewrite !sepcon_assoc, <- sepcon_assoc.
        assert_PROP (hist_incl h hr).
        { apply sepcon_derives_prop, hist_ref_incl; auto. }
        eapply derives_trans.
        { apply sepcon_derives, derives_refl.
          apply hist_add' with (e := HAdd (i0 + 1) 1 b); auto. }
        eapply derives_trans; [apply bupd_frame_r | apply fupd_bupd_elim].
        rewrite !sepcon_assoc, sepcon_comm.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (hashtable _ _ _ _)).
        rewrite <- !sepcon_assoc, sepcon_assoc.
        eapply derives_trans.
        { apply sepcon_derives, derives_refl.
          apply modus_ponens_wand'.
          eapply derives_trans, now_later.
          Exists (if b then map_upd HT (i0 + 1) 1 else HT) (hr ++ [HAdd (i0 + 1) 1 b]); entailer!.
          rewrite apply_hist_app, H15; simpl.
          destruct (HT (i0 + 1)), b; try congruence.
          * destruct H16 as [_ X]; specialize (X eq_refl); discriminate.
          * destruct H16 as [X _]; specialize (X eq_refl); discriminate. }
        eapply derives_trans; [apply fupd_frame_r | apply fupd_mono].
        Exists (map_upd h (length hr) (HAdd (i0 + 1) 1 b)); entailer!.
        apply (add_events_snoc _ nil); [constructor|].
        apply hist_incl_lt; auto. }
    Intros b h'.
    forward_if (temp _total (vint (Zlength (filter id (ls ++ [b]))))).
    + pose proof (Zlength_filter id ls).
      forward.
      entailer!.
      rewrite filter_app; simpl.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; auto.
    + forward.
      entailer!.
      rewrite filter_app; simpl.
      rewrite Zlength_app, Zlength_nil, Z.add_0_r; auto.
    + Exists (ls ++ [b]) h'; rewrite filter_app, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; entailer!.
      rewrite Z2Nat.inj_add, upto_app, map_app, Z2Nat.id by omega; change (upto (Z.to_nat 1)) with [0]; simpl.
      rewrite Z.add_0_r, app_Znth2, Zminus_diag, Znth_0_cons by omega.
      eapply add_events_trans; eauto.
      erewrite map_ext_in; eauto.
      intros j Hj; rewrite app_Znth1; auto.
      rewrite In_upto, Z2Nat.id in Hj; omega.
  - Intros ls h.
    viewshift_SEP 1 emp.
    { go_lower; apply invariant_dealloc. }
    forward.
    forward_call (lockt, tsh, f_lock_inv sh gsh entries gh (gv _m_entries) t
      (gv _thread_locks) lockt (gv _results) res,
                  f_lock_pred tsh sh gsh entries gh (gv _m_entries) t
      (gv _thread_locks) lockt (gv _results) res).
    { assert_PROP (Zlength entries = Zlength lg) by (pose proof size_pos; entailer!).
      lock_props.
      unfold f_lock_pred at 2.
      rewrite selflock_eq.
      unfold f_lock_inv at 1.
      rewrite lock_struct_array.
      Exists (Znth 0 ls) (Znth 1 ls) (Znth 2 ls) h; entailer!.
      rewrite (list_Znth_eq ls) at 1.
      replace (length ls) with (Z.to_nat 3) by (symmetry; rewrite <- Zlength_length by computable; auto).
      cancel.
      subst Frame; instantiate (1 := []); simpl; rewrite sepcon_emp; apply now_later. }
    forward.
Qed.

Lemma lock_struct : forall p, data_at_ Tsh (Tstruct _lock_t noattr) p = data_at_ Tsh tlock p.
Proof.
  intros.
  rewrite !data_at__eq.
  unfold_data_at 1%nat.
  rewrite field_at_data_at; simpl.
  apply pred_ext.
  - assert_PROP (field_compatible (Tstruct _lock_t noattr) [StructField _a] p) by entailer!.
    rewrite field_compatible_field_address by auto; simpl.
    entailer!.
  - assert_PROP (field_compatible (Tstruct _lock_t noattr) [StructField _a] p).
    { entailer!.
      rewrite field_compatible_cons; simpl; split; hnf; auto.
      destruct H as (? & ? & ? & Halign & ?); repeat split; auto.
      destruct p; try contradiction; simpl in *.
      eapply align_compatible_rec_Tstruct; simpl; eauto; simpl.
      intros ???.
      if_tac; inversion 1; subst; simpl.
      inversion 1; subst; simpl.
      rewrite Z.add_0_r; auto. }
    rewrite field_compatible_field_address by auto; simpl.
    entailer!.
Qed.

Lemma add_fails : forall k v b l H H' (HH : apply_hist H l = Some H') (Hadd : In (HAdd k v b) l)
  (Hk : H k <> None), b = false.
Proof.
  induction l; simpl; intros; [contradiction|].
  destruct a; try (destruct Hadd as [X|]; [inv X|]).
  - eapply IHl; eauto.
    unfold map_upd; if_tac; auto; discriminate.
  - destruct (H k0); destruct (eq_dec _ _); try discriminate; eapply IHl; eauto.
  - destruct b; auto.
    destruct (H k); [discriminate | contradiction].
  - destruct (H k0), r; try discriminate; eapply IHl; eauto.
    unfold map_upd; if_tac; auto; discriminate.
Qed.

Instance Inhabitant_hist_el : Inhabitant hashtable_hist_el := HGet 0 0.

Lemma only_one_add_succeeds : forall k v1 v2 l i1 i2 H0 H (HH : apply_hist H0 l = Some H)
  (Hin1 : Znth i1 l = HAdd k v1 true) (Hin2 : Znth i2 l = HAdd k v2 true),
  i2 = i1 /\ v2 = v1.
Proof.
  induction l; simpl; intros.
  { rewrite Znth_nil in Hin1; discriminate. }
  assert (i2 = i1); [|subst; rewrite Hin2 in Hin1; inv Hin1; auto].
  exploit (Znth_inbounds i1 (a :: l)); [rewrite Hin1; discriminate|].
  exploit (Znth_inbounds i2 (a :: l)); [rewrite Hin2; discriminate|].
  rewrite !Zlength_cons; intros.
  destruct (eq_dec i1 0), (eq_dec i2 0); subst; auto.
  - rewrite Znth_0_cons in Hin1; subst.
    rewrite Znth_pos_cons in Hin2 by omega.
    destruct (H0 k); [discriminate|].
    eapply add_fails in HH; [|rewrite <- Hin2; apply Znth_In; omega|]; [discriminate|].
    unfold map_upd; rewrite eq_dec_refl; discriminate.
  - rewrite Znth_0_cons in Hin2; subst.
    rewrite Znth_pos_cons in Hin1 by omega.
    destruct (H0 k); [discriminate|].
    eapply add_fails in HH; [|rewrite <- Hin1; apply Znth_In; omega|]; [discriminate|].
    unfold map_upd; rewrite eq_dec_refl; discriminate.
  - rewrite Znth_pos_cons in Hin1, Hin2 by omega.
    assert (i2 - 1 = i1 - 1); [|omega].
    destruct a.
    + eapply IHl; eauto.
    + destruct (H0 k0); destruct (eq_dec _ _); try discriminate; eapply IHl; eauto.
    + destruct (H0 k0), r; try discriminate; eapply IHl; eauto.
Qed.

Lemma one_add_succeeds : forall k v b l H0 H (HH : apply_hist H0 l = Some H) (Hk : H0 k = None)
  (Hin : In (HAdd k v b) l) (Hout : forall v, ~In (HSet k v) l), exists v', In (HAdd k v' true) l.
Proof.
  induction l; simpl; intros; [contradiction|].
  assert (forall v, ~In (HSet k v) l).
  { intros v0 ?; contradiction (Hout v0); auto. }
  destruct a; try (destruct Hin as [X|]; [discriminate|]).
  - destruct (eq_dec k0 k); [contradiction (Hout v0); subst; auto|].
    exploit IHl; eauto.
    { unfold map_upd; if_tac; auto; subst; contradiction. }
    intros (? & ?); eauto.
  - destruct (H0 k0), (eq_dec _ _); try discriminate; exploit IHl; eauto; intros (? & ?); eauto.
  - destruct (eq_dec k0 k).
    + subst; rewrite Hk in HH.
      destruct r; [eauto | discriminate].
    + destruct Hin as [X|]; [inv X; contradiction|].
      destruct (H0 k0), r; try discriminate; exploit IHl; eauto; try (intros (? & ?); eauto).
      unfold map_upd; if_tac; auto; subst; contradiction.
Qed.

Lemma filter_find_count : forall {A} {d : Inhabitant A} (f : A -> bool) l li (Hunique : NoDup li)
  (Hli : forall i, In i li -> f (Znth i l) = true) (Hrest : forall i, ~In i li -> f (Znth i l) = false),
  Zlength (filter f l) = Zlength li.
Proof.
  induction l; simpl; intros.
  - exploit (list_pigeonhole li (Zlength li + 1)); [omega|].
    intros (i' & ? & ?).
    destruct li; auto.
    exploit (Hli z); simpl; auto.
    exploit Hrest; eauto.
    rewrite !Znth_nil; intros ->; discriminate.
  - assert (f d = false) as Hd.
    { exploit (list_pigeonhole (upto (Z.to_nat (Zlength (a :: l))) ++ li)
       (Zlength (upto (Z.to_nat (Zlength (a :: l))) ++ li) + 1)); [omega|].
      intros (j' & ? & Hout); exploit (Hrest j').
      { intro X; contradiction Hout; rewrite in_app; auto. }
      rewrite Znth_overflow; auto.
      { destruct (zlt j' (Zlength (a :: l))); auto.
        contradiction Hout; rewrite in_app; left.
        rewrite In_upto, Z2Nat.id; omega. } }
    destruct (in_dec Z.eq_dec 0 li).
    + exploit Hli; eauto.
      rewrite Znth_0_cons; intros ->.
      rewrite Zlength_cons.
      exploit in_split; eauto; intros (li1 & li2 & ?); subst.
      apply NoDup_remove in Hunique; destruct Hunique.
      rewrite Zlength_app, Zlength_cons.
      erewrite (IHl (map (fun i => i - 1) (li1 ++ li2))), Zlength_map, Zlength_app; auto; try omega.
      * apply FinFun.Injective_map_NoDup; auto.
        intros ??; omega.
      * intros ? Hj; rewrite in_map_iff in Hj; destruct Hj as (j & ? & Hj); subst.
        exploit (Hli j).
        { rewrite in_insert_iff; auto. }
        destruct (eq_dec j 0); [subst; contradiction|].
        destruct (zlt j 0).
        { rewrite Znth_underflow, Hd by auto; discriminate. }
        rewrite Znth_pos_cons by omega; auto.
      * intros j Hj.
        destruct (zlt j 0); [rewrite Znth_underflow; auto|].
        specialize (Hrest (j + 1)); specialize (Hli (j + 1));
          rewrite Znth_pos_cons, Z.add_simpl_r in Hrest, Hli by omega.
        destruct (in_dec Z.eq_dec (j + 1) (li1 ++ 0 :: li2)); auto.
        rewrite in_insert_iff in i0; destruct i0; [omega|].
        contradiction Hj; rewrite in_map_iff; do 2 eexists; eauto; omega.
    + exploit Hrest; eauto.
      rewrite Znth_0_cons; intros ->.
      erewrite (IHl (map (fun i => i - 1) li)), Zlength_map; try omega.
      * apply FinFun.Injective_map_NoDup; auto.
        intros ??; omega.
      * intros ? Hj; rewrite in_map_iff in Hj; destruct Hj as (j & ? & Hj); subst.
        specialize (Hli _ Hj).
        destruct (eq_dec j 0); [subst; contradiction|].
        destruct (zlt j 0).
        { rewrite Znth_underflow, Hd in Hli by auto; discriminate. }
        rewrite Znth_pos_cons in Hli by omega; auto.
      * intros j Hj.
        destruct (zlt j 0); [rewrite Znth_underflow; auto|].
        specialize (Hrest (j + 1)); specialize (Hli (j + 1));
          rewrite Znth_pos_cons, Z.add_simpl_r in Hrest, Hli by omega.
        destruct (in_dec Z.eq_dec (j + 1) li); auto.
        contradiction Hj; rewrite in_map_iff; do 2 eexists; eauto; omega.
Qed.

Lemma hists_eq : forall lr l (Hlr : Forall (fun '(h, ls) => add_events empty_map
  [HAdd 1 1 (Znth 0 ls); HAdd 2 1 (Znth 1 ls); HAdd 3 1 (Znth 2 ls)] h) lr)
  (Hlens : Forall (fun '(_, ls) => Zlength ls = 3) lr)
  (Hl : hist_list' (maps_add (map fst lr)) l) (Hdisj : all_disjoint (map fst lr)),
  Permutation (concat (map snd lr)) (map (fun e => match e with HAdd _ _ b => b | _ => false end) l).
Proof.
  induction lr; simpl; intros.
  - inv Hl; [constructor|].
    unfold map_upd in H0.
    apply equal_f with (x := t) in H0.
    rewrite if_true in H0 by auto; discriminate.
  - inv Hlr; inv Hlens.
    apply all_disjoint_cons in Hdisj as [].
    destruct a as (?, h); simpl in *.
    apply hist_list'_add in Hl as (l1 & l2 & ? & ? & ?); auto.
    etransitivity; [|apply Permutation_map; symmetry; eauto].
    rewrite map_app.
    apply Permutation_app; auto.
    match goal with |- Permutation ?a ?b => assert (a = b); [|subst; reflexivity] end.
    clear - H6 H1 H3.
    inv H1.
    apply (app_inj_tail _ [_; _] _ _) in H0 as []; subst.
    inv Hh'.
    apply (app_inj_tail _ [_] _ _) in H0 as []; subst.
    inv Hh'0.
    apply (app_inj_tail _ [] _ _) in H0 as []; subst.
    inv Hh'; [|destruct le; discriminate].
    inv H6.
    { apply equal_f with t in H0; unfold map_upd in H0.
      rewrite eq_dec_refl in H0; discriminate. }
    apply add_new_inj in H0 as (? & ? & ?); auto; subst.
    inv Hrest.
    { apply equal_f with t0 in H0; unfold map_upd in H0.
      rewrite eq_dec_refl in H0; discriminate. }
    apply add_new_inj in H0 as (? & ? & ?); auto; subst.
    inv Hrest0.
    { apply equal_f with t1 in H0; unfold map_upd in H0.
      rewrite eq_dec_refl in H0; discriminate. }
    apply add_new_inj in H0 as (? & ? & ?); auto; subst.
    inv Hrest; simpl.
    rewrite list_Znth_eq at 1.
    rewrite Zlength_correct in *.
    replace (length h) with 3%nat by (apply Nat2Z.inj; auto); reflexivity.
    { apply equal_f with t2 in H0; unfold map_upd in H0.
      rewrite eq_dec_refl in H0; discriminate. }
Qed.

Lemma add_three : forall lr HT l (Hlr : Zlength lr = 3)
  (Hhists : Forall (fun '(h, ls) => add_events empty_map [HAdd 1 1 (Znth 0 ls); HAdd 2 1 (Znth 1 ls);
     HAdd 3 1 (Znth 2 ls)] h) lr) (Hlens : Forall (fun '(_, ls) => Zlength ls = 3) lr)
  (Hl : hist_list (maps_add (map fst lr)) l) (HHT : apply_hist empty_map l = Some HT)
  (Hdisj : all_disjoint (map fst lr)),
  Zlength (filter id (concat (map snd lr))) = 3.
Proof.
  intros.
  assert (Permutation.Permutation (filter id (concat (map snd lr)))
    (filter id (map (fun e => match e with HAdd _ _ b => b | _ => false end) l))) as Hperm.
  { apply Permutation_filter, hists_eq; auto.
    apply hist_list_weak; auto. }
  rewrite (Permutation_Zlength _ _ Hperm).
  assert (forall k v, ~ In (HSet k v) l).
  { repeat intro.
    apply In_nth_error in H; destruct H as (? & H).
    apply Hl in H.
    apply in_maps_add in H as (m & Hin & Hm).
    apply in_map_iff in Hin as ((?, h) & ? & Hin); simpl in *; subst.
    rewrite Forall_forall in Hhists; specialize (Hhists _ Hin); simpl in Hhists.
    eapply add_events_dom in Hm; eauto; simpl in Hm.
    decompose [or] Hm; try discriminate; contradiction. }
  assert (forall i, 0 <= i < 3 -> In (HAdd (i + 1) 1 (Znth i (snd (Znth 0 lr)))) l) as Hins.
  { intros.
    assert (exists t, maps_add (map fst lr) t = Some (HAdd (i + 1) 1 (Znth i (snd (Znth 0 lr)))))
      as (t & Hin).
    { exploit (Znth_In 0 lr); [omega | intro Hin].
      rewrite Forall_forall in Hhists; specialize (Hhists _ Hin).
      destruct (Znth 0 lr) as (h, ?); simpl in *.
      apply add_events_in with (e := HAdd (i + 1) 1 (Znth i l0)) in Hhists as (t & _ & Hh).
      exists t; eapply maps_add_in; eauto.
      { apply all_disjoint_compatible; auto. }
      rewrite in_map_iff; eexists (_, _); simpl; eauto.
      { destruct (eq_dec i 0); [subst; simpl; auto|].
        destruct (eq_dec i 1); [subst; simpl; auto|].
        destruct (eq_dec i 2); [subst; simpl; auto | omega]. } }
    apply Hl in Hin; eapply nth_error_in; eauto. }
  exploit (one_add_succeeds 1 1 (Znth 0 (snd (Znth 0 lr))) l); eauto.
  { eapply (Hins 0); auto; omega. }
  exploit (one_add_succeeds 2 1 (Znth 1 (snd (Znth 0 lr))) l); eauto.
  { eapply (Hins 1); auto; omega. }
  exploit (one_add_succeeds 3 1 (Znth 2 (snd (Znth 0 lr))) l); eauto.
  { eapply (Hins 2); auto; omega. }
  intros (v3 & Hin3) (v2 & Hin2) (v1 & Hin1).
  apply In_Znth in Hin1; destruct Hin1 as (t1 & ? & Ht1).
  apply In_Znth in Hin2; destruct Hin2 as (t2 & ? & Ht2).
  apply In_Znth in Hin3; destruct Hin3 as (t3 & ? & Ht3).
  rewrite filter_find_count with (li := [t1; t2; t3]); auto; simpl.
  - repeat constructor; auto; simpl.
    + intros [|[|]]; try contradiction; subst.
      * rewrite Ht1 in Ht2; inv Ht2.
      * rewrite Ht1 in Ht3; inv Ht3.
    + intros [|]; try contradiction; subst.
      rewrite Ht2 in Ht3; inv Ht3.
  - intros ? [|[|[|]]]; try contradiction; subst; rewrite Znth_map by omega.
    + rewrite Ht1; auto.
    + rewrite Ht2; auto.
    + rewrite Ht3; auto.
  - intros i Hi.
    destruct (zlt i 0); [rewrite Znth_underflow; auto|].
    destruct (zlt i (Zlength l)); [|rewrite Znth_overflow by (rewrite Zlength_map; omega); auto].
    rewrite Znth_map by omega.
    destruct (Znth i l) eqn: Hith; auto.
    destruct r; auto.
    contradiction Hi.
    assert (k = 1 \/ k = 2 \/ k = 3) as Hk.
    { rewrite <- nth_Znth in Hith by omega.
      exploit nth_error_nth; [apply Nat2Z.inj_lt; rewrite Z2Nat.id, <- Zlength_correct; eauto; omega|].
      rewrite Hith; intro Hin.
      apply Hl in Hin.
      apply in_maps_add in Hin as (? & Hin & Hm); subst.
      rewrite in_map_iff in Hin; destruct Hin as ((h, ?) & ? & Hin); subst; simpl in *.
      rewrite Forall_forall in Hhists; specialize (Hhists _ Hin); simpl in Hhists.
      eapply add_events_dom in Hhists; eauto; simpl in Hhists.
      destruct Hhists as [X | [X | [X | [X | X]]]]; inv X; auto. }
    destruct Hk as [|[|]]; [left | right; left | right; right; left];
      match goal with |-?P => assert (P /\ Znth (k - 1) [v1; v2; v3] = v); [|tauto] end;
      subst; eapply only_one_add_succeeds; eauto.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  name m_entries _m_entries.
  name locksp _thread_locks.
  name resp _results.
  start_function.
  replace 16384 with size by (setoid_rewrite (proj2_sig has_size); auto).
  forward.
  forward_call gv.
  { unfold tentry; cancel. }
  Intros x; destruct x as ((entries, g), lg).
  ghost_alloc (ghost_hist_ref(hist_el := hashtable_hist_el) Tsh empty_map empty_map).
  { split; auto; apply self_completable. }
  Intro gh.
  rewrite <- hist_ref_join_nil by (apply Share.nontrivial); Intros.
  rewrite <- (emp_sepcon (ghost_hist _ _ _)); Intros.
  viewshift_SEP 0 (EX inv_names : invG, wsat).
  { go_lower; apply make_wsat. }
  Intro inv_names.
  gather_SEP 0 5 2; viewshift_SEP 0 (except0 (wsat * EX i : _, invariant i (hashtable_inv gh g lg entries))).
  { go_lower.
    eapply derives_trans, wsat_fupd_elim.
    apply sepcon_derives; [apply derives_refl|].
    apply (make_inv (Empty_set _) _ (hashtable_inv gh g lg entries)).
    unfold hashtable_inv.
    Exists (@empty_map Z Z) (@nil hashtable_hist_el); entailer!. }
  erewrite except0_sepcon, except0_exp by apply O; Intros i1.
  destruct (split_shares 3 Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  destruct (split_shares 3 Tsh) as (sh0' & shs' & ? & ? & ? & Hshs'); auto.
  destruct (split_readable_share Tsh) as (sh1 & sh2 & ? & ? & ?); auto.
  rewrite <- seq_assoc.
  set (f_lock j l r := f_lock_pred sh2 (Znth j shs) (Znth j shs') entries gh (gv _m_entries)
                                         j (gv _thread_locks) l (gv _results) r).
  forward_for_simple_bound 3 (EX i : Z, EX res : list val, EX locks : list val,
    PROP (Zlength res = i; Zlength locks = i)
    LOCAL (temp _total (vint 0); gvars gv)
    SEP (@data_at CompSpecs Ews (tarray tentry size) entries (gv _m_entries);
         except0 wsat; except0 (invariant i1 (hashtable_inv gh g lg entries));
         ghost_hist(hist_el := hashtable_hist_el) Tsh empty_map gh;
         fold_right sepcon emp (map (fun x => malloc_token Tsh tint (fst x) * malloc_token Tsh tint (snd x))
           entries);
         data_at Ews (tarray (tptr tint) 3) (res ++ repeat Vundef (Z.to_nat (3 - i))) (gv _results) *
         fold_right sepcon emp (map (data_at_ Tsh tint) res) *
         fold_right sepcon emp (map (malloc_token Tsh tint) res) *
         data_at Ews (tarray (tptr (Tstruct _lock_t noattr)) 3)
           (locks ++ repeat Vundef (Z.to_nat (3 - i))) (gv _thread_locks) *
         fold_right sepcon emp (map (malloc_token Tsh (Tstruct _lock_t noattr)) locks) *
         fold_right sepcon emp (map (fun j => lock_inv Tsh (Znth j locks)
           (f_lock j (Znth j locks) (Znth j res))) (upto (Z.to_nat i))))).
  { Exists (@nil val) (@nil val); rewrite !data_at__eq; entailer!.
    erewrite map_ext; [apply derives_refl|]; intros (?, ?); auto. }
  { (* first loop *)
    forward_call (Tstruct _lock_t noattr).
    { repeat split; auto; simpl; computable. }
    rewrite sepcon_map; Intros l.
    forward.
    forward_call tint.
    { repeat split; auto; simpl; computable. }
    Intros r.
    forward.
    focus_SEP 3.
    forward_call (l, Tsh, f_lock i l r).
    { rewrite lock_struct; cancel. }
    Exists (res ++ [r]) (locks ++ [l]); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; entailer!.
    rewrite lock_inv_isptr, data_at__isptr; Intros.
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app by omega.
    simpl; change (upto 1) with [0]; simpl.
    rewrite Z2Nat.id, Z.add_0_r by omega.
    replace (Zlength res + 1) with (Zlength (res ++ [r]))
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil; auto).
    rewrite <- upd_complete_gen by omega.
    replace (Zlength (res ++ [r])) with (Zlength (locks ++ [l]))
      by (rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; auto; omega).
    rewrite <- upd_complete_gen by omega.
    rewrite !app_Znth2 by omega.
    replace (Zlength locks) with (Zlength res); rewrite Zminus_diag, !Znth_0_cons.
    destruct r; try contradiction.
    destruct l; try contradiction.
    rewrite sepcon_map; cancel.
    apply sepcon_list_derives; rewrite !Zlength_map, !Zlength_upto, <- Zlength_correct.
    { rewrite Z2Nat.id; auto; omega. }
    intros.
    erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, <- ?Zlength_correct, ?Z2Nat.id; auto; omega).
    rewrite !app_Znth1 by omega; auto. }
  Intros res locks.
  rewrite !app_nil_r.
  assert_PROP (Zlength entries = size) by (pose proof size_pos; entailer!).
  rewrite <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z, EX sh : share, EX sh' : share,
    PROP (sepalg_list.list_join sh0 (sublist i 3 shs) sh; sepalg_list.list_join sh0' (sublist i 3 shs') sh')
    LOCAL (temp _total (vint 0); gvars gv)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         except0 wsat; except0 (invariant i1 (hashtable_inv gh g lg entries));
         ghost_hist(hist_el := hashtable_hist_el) sh' empty_map gh;
         fold_right sepcon emp (map (fun x => malloc_token Tsh tint (fst x) * malloc_token Tsh tint (snd x))
           entries);
         data_at sh (tarray (tptr tint) 3) res (gv _results);
         fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i 3 res));
         fold_right sepcon emp (map (malloc_token Tsh tint) res);
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks (gv _thread_locks);
         fold_right sepcon emp (map (malloc_token Tsh (Tstruct _lock_t noattr)) locks);
         fold_right sepcon emp (map (fun j => lock_inv (if zlt j i then sh1 else Tsh) (Znth j locks)
           (f_lock j (Znth j locks) (Znth j res))) (upto 3)))).
  { rewrite !sublist_same by auto; unfold f_lock; Exists Ews Tsh; entailer!.
    erewrite map_ext_in; [apply derives_refl|].
    intros ??%In_upto.
    simpl; if_tac; auto; omega. }
  { (* second loop *)
    replace_SEP 2 (|> (invariant i1 (hashtable_inv gh g lg entries) || FF)).
    { go_lower; unfold except0.
      rewrite later_orp.
      apply orp_left; [apply orp_right1, now_later | apply orp_right2; auto]. }
    forward_call tint.
    { repeat split; auto; simpl; computable. }
    Intros t.
    rewrite sepcon_map; Intros.
    forward.
    simpl in *; assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh0 _ _ |- _ => rewrite sublist_next in H by auto;
      inversion H as [|????? Hj1 Hj2]; subst end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh3 & ? & Hj3).
    assert (3 <= Zlength shs') by omega.
    match goal with H : sepalg_list.list_join sh0' _ _ |- _ => rewrite sublist_next in H by auto;
      inversion H as [|????? Hj1' Hj2']; subst end.
    apply sepalg.join_comm in Hj1'; destruct (sepalg_list.list_join_assoc1 Hj1' Hj2') as (sh3' & ? & Hj3').
    rewrite invariant_dup, orp_FF.
    assert_PROP (isptr t) by entailer!.
    forward_spawn _f t (Znth i shs, Znth i shs', sh2, entries, i1, gh, g, lg, gv, i, gv _thread_locks, Znth i locks, gv _results,
               Znth i res, inv_names).
    { assert (0 <= i < Zlength shs) by omega.
      assert (Znth i shs' <> Share.bot).
      { intro X; contradiction unreadable_bot; rewrite <- X.
        apply Forall_Znth; auto; omega. }
      rewrite (extract_nth_sepcon (map _ (upto 3)) i) by (rewrite Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; simpl; omega).
      rewrite if_false by omega.
      rewrite lock_inv_isptr; Intros.
      entailer!.
      { apply Forall_Znth; auto. }
      rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj3).
      replace empty_map with (@map_add nat hashtable_hist_el empty_map empty_map) by apply map_add_empty.
      pose proof (@empty_map_disjoint nat hashtable_hist_el empty_map) as Hdisj.
      erewrite (add_andp (ghost_hist _ _ _) (!!_)) by (apply prop_right, Hdisj).
      rewrite andp_comm, <- (ghost_hist_join _ _ _ _ _ _ Hj3'); auto.
      rewrite <- (lock_inv_share_join sh1 sh2) by auto.
      fast_cancel; cancel.
      rewrite (sepcon_comm _ (data_at (Znth i shs) _ _ (gv _thread_locks))), !sepcon_assoc; apply sepcon_derives.
      { rewrite lock_struct_array; apply stronger_array_ext.
        - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
        - intros j ???; unfold unfold_reptype; simpl.
          destruct (eq_dec j i).
          + subst; rewrite upd_Znth_same by auto; apply derives_refl.
          + rewrite upd_Znth_diff by auto.
            setoid_rewrite Znth_repeat with (n0 := 3%nat); apply stronger_default_val. }
      rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs) _ _ (gv _results))),
        !sepcon_assoc; apply sepcon_derives.
      { apply stronger_array_ext.
        - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
        - intros j ???; unfold unfold_reptype; simpl.
          destruct (eq_dec j i).
          + subst; rewrite upd_Znth_same by auto; apply derives_refl.
          + rewrite upd_Znth_diff' by auto.
            setoid_rewrite Znth_repeat with (n0 := 3%nat); apply stronger_default_val. }
      erewrite sublist_next by (auto; omega); simpl; fast_cancel.
      { intro; subst; contradiction unreadable_bot.
        eapply join_readable1, readable_share_list_join; eauto. } }
    { simpl; auto. }
    go_lower.
    Exists sh3 sh3'; rewrite sepcon_map; entailer!.
    rewrite sepcon_assoc; apply sepcon_derives; [apply except0_intro|].
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map;
      auto.
    intros j ?; destruct (eq_dec j i).
    - subst; rewrite upd_Znth_same by auto.
      erewrite Znth_map, Znth_upto by (auto; simpl; omega).
      if_tac; [auto | omega].
    - rewrite upd_Znth_diff' by auto.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      if_tac; if_tac; auto; omega. }
  Intros sh sh'.
  rewrite sublist_nil.
  repeat match goal with H : sepalg_list.list_join _ (sublist 3 3 _) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward_for_simple_bound 3 (EX i : Z, EX x : (share * (list (hist * list bool))), EX sh' : share,
    PROP (readable_share (fst x); sepalg_list.list_join (fst x) (sublist i 3 shs) Ews; Zlength (snd x) = i;
          Forall (fun p => let '(h, ls) := p in add_events empty_map
            [HAdd 1 1 (Znth 0 ls); HAdd 2 1 (Znth 1 ls); HAdd 3 1 (Znth 2 ls)] h) (snd x);
          Forall (fun '(h, ls) => Zlength ls = 3) (snd x); all_disjoint (map fst (snd x));
          readable_share sh'; sepalg_list.list_join sh' (sublist i 3 shs') Tsh)
    LOCAL (let ls := map snd (snd x) in temp _total (vint (Zlength (filter id (concat ls)))); gvars gv)
    SEP (@data_at CompSpecs (fst x) (tarray tentry size) entries (gv _m_entries);
         except0 wsat; except0 (invariant i1 (hashtable_inv gh g lg entries));
         let h := map fst (snd x) in ghost_hist sh' (fold_right map_add empty_map h) gh;
         fold_right sepcon emp (map (fun x => malloc_token Tsh tint (fst x) * malloc_token Tsh tint (snd x))
           entries);
         data_at (fst x) (tarray (tptr tint) 3) res (gv _results);
         fold_right sepcon emp (map (malloc_token Tsh tint) (sublist i 3 res));
         data_at (fst x) (tarray (tptr (Tstruct _lock_t noattr)) 3) locks (gv _thread_locks);
         fold_right sepcon emp (map (malloc_token Tsh (Tstruct _lock_t noattr)) (sublist i 3 locks));
         fold_right sepcon emp (map (fun j => lock_inv sh1 (Znth j locks)
           (f_lock j (Znth j locks) (Znth j res))) (sublist i 3 (upto 3))))).
  { rewrite !(sublist_same 0 3) by auto.
    Exists (sh, @nil (hist * list bool)) sh'; entailer!.
    erewrite map_ext_in; [apply derives_refl|].
    intros ??%In_upto; simpl in *.
    if_tac; auto; omega. }
  { (* third loop *)
    destruct x as (sh3, lr); simpl in *.
    erewrite sublist_next with (l := upto 3), Znth_upto by (auto; rewrite ?Zlength_upto; simpl; omega); simpl.
    rewrite lock_inv_isptr, sepcon_map; Intros.
    forward.
    forward_call (Znth i locks, sh1, f_lock i (Znth i locks) (Znth i res)).
    unfold f_lock at 2; unfold f_lock_pred.
    rewrite selflock_eq; Intros.
    forward_call (Znth i locks, Tsh, sh2,
      f_lock_inv (Znth i shs) (Znth i shs') entries gh (gv _m_entries) i (gv _thread_locks) (Znth i locks) (gv _results) (Znth i res),
      f_lock i (Znth i locks) (Znth i res)).
    { lock_props.
      { subst f_lock; simpl.
        apply f_pred_exclusive; auto.
        apply Forall_Znth; auto; omega. }
      rewrite (sepcon_comm _ (lock_inv _ _ _)), !sepcon_assoc, <- sepcon_assoc;
        apply sepcon_derives; [|cancel_frame].
      rewrite <- (lock_inv_share_join sh1 sh2 Tsh) by auto; unfold f_lock, f_lock_pred; cancel. }
    erewrite sublist_next with (l := locks) by (auto; omega); simpl.
    forward_call (Tstruct _lock_t noattr, Znth i locks).
    { rewrite lock_struct; cancel. }
    unfold f_lock_inv at 1; Intros b1 b2 b3 hi.
    assert (0 <= i < Zlength shs) by omega.
    assert (readable_share (Znth i shs)) by (apply Forall_Znth; auto).
    forward.
    { assert (0 <= i < 3) as Hi by auto; clear - Hi; entailer!.
      rewrite upd_Znth_same; auto. }
    rewrite upd_Znth_same by auto.
    forward.
    Opaque filter.
    erewrite sublist_next with (l := res) by (auto; omega); simpl.
    forward_call (tint, Znth i res).
    { cancel. }
    assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh3 _ _ |- _ => rewrite sublist_next in H by auto;
      inversion H as [|??? w1 ? Hj1]; subst end.
    match goal with H : sepalg_list.list_join sh'0 _ _ |- _ => rewrite sublist_next in H by (auto; omega);
      inversion H as [|??? w1' ? Hj1']; subst end.
    gather_SEP 12 2.
    replace_SEP 0 (data_at w1 (tarray (tptr (Tstruct _lock_t noattr)) 3) locks (gv _thread_locks)).
    { go_lower.
      rewrite <- lock_struct_array.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join by eauto; apply derives_refl. }
    gather_SEP 10 3.
    replace_SEP 0 (data_at w1 (tarray (tptr tint) 3) res (gv _results)).
    { go_lower.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join by eauto; apply derives_refl. }
    gather_SEP 7 2; erewrite ghost_hist_join; eauto.
    gather_SEP 4 3; erewrite data_at_share_join by eauto.
    assert (0 <= Zlength (filter id [b1; b2; b3]) <= 3).
    { split; [apply Zlength_nonneg|].
      etransitivity; [apply Zlength_filter|].
      rewrite !Zlength_cons, Zlength_nil in *; omega. }
    assert (0 <= Zlength (filter id (concat (map snd lr))) <= 3 * Zlength shs).
    { split; [apply Zlength_nonneg|].
      etransitivity; [apply Zlength_filter|].
      etransitivity; [apply Zlength_concat_le with (n := 3)|].
      * rewrite Forall_map.
        eapply Forall_impl; [|eauto].
        intros []; simpl; omega.
      * rewrite Zlength_map; omega. }
    forward.
    go_lower; Exists (w1, lr ++ [(hi, [b1; b2; b3])]) w1'; rewrite sepcon_map; entailer!.
    rewrite !map_app, concat_app, filter_app, !Zlength_app, Zlength_cons, Zlength_nil; simpl;
      repeat (split; auto).
    - eapply join_readable1; eauto.
    - rewrite Forall_app; repeat constructor; auto.
    - rewrite Forall_app; repeat constructor; auto.
    - apply all_disjoint_snoc; split; auto.
      symmetry; auto.
    - eapply join_readable1; eauto.
    - rewrite map_app, fold_right_app; simpl.
      rewrite map_add_empty, <- fold_right_maps_add; auto.
    - intro; subst; contradiction unreadable_bot.
    - intro X; contradiction unreadable_bot; rewrite <- X.
      apply Forall_Znth; auto; omega. }
  Intros x sh''; destruct x as (?, lr); simpl fst in *; simpl snd in *.
  repeat match goal with H : sepalg_list.list_join _ (sublist 3 3 _) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  gather_SEP 3 2.
  replace_SEP 0 (|={Ensembles.Singleton i1,Empty_set _}=> !!(Zlength (filter id (concat (map snd lr))) = 3)).
  { go_lower.
    eapply derives_trans; [apply except0_frame_l | apply fupd_except0_elim].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply inv_open with (E := Ensembles.Singleton i1); constructor]|].
    eapply derives_trans; [apply fupd_frame_l|].
    eapply derives_trans, fupd_trans; apply fupd_mono.
    rewrite <- sepcon_assoc.
    eapply derives_trans.
    { apply sepcon_derives, derives_refl.
      eapply derives_trans.
      { apply sepcon_derives; [apply derives_refl|].
        apply except0_timeless, hashtable_inv_timeless; apply except0_intro. }
      eapply derives_trans; [apply except0_frame_l | apply except0_mono].
      unfold hashtable_inv.
      Intros HT hr.
      instantiate (1 := !!(exists l HT, hist_list (fold_right map_add empty_map (map fst lr)) l /\
        apply_hist empty_map l = Some HT) && TT).
      apply andp_right; auto.
      rewrite <- sepcon_assoc, sepcon_comm, <- !sepcon_assoc.
      rewrite (sepcon_comm (ghost_ref _ _)), hist_ref_join by auto.
      Intros l; apply prop_right.
      match goal with H : hist_sub _ _ _ |- _ => apply hist_sub_Tsh in H; subst end.
      exists hr, HT; split; auto. }
    eapply derives_trans; [apply except0_frame_r | apply fupd_except0_elim].
    rewrite sepcon_andp_prop'; Intros.
    replace (Subtract (Ensembles.Singleton i1) i1) with (Empty_set iname).
    eapply derives_trans, fupd_intro.
    apply prop_right.
    destruct H14 as (l & HT & ? & ?).
    eapply add_three; eauto.
    { apply Extensionality_Ensembles; split; intros ? Hin; inv Hin; contradiction. } }
  (* Without including fupd in semax, it's not clear how to extract the result
     from the fupd. In a larger application, maybe there would be another view shift. *)
  forward.
Qed.

End Proofs.