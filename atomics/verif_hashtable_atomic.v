Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.atomics.SC_atomics.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.
Require Import VST.atomics.hashtable_atomic.
Require Import VST.atomics.hashtable.
Import List.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition atom_load_spec := DECLARE _atom_load atomic_load_spec.
Definition atom_store_spec := DECLARE _atom_store atomic_store_spec.
Definition atom_CAS_spec := DECLARE _atom_CAS atomic_CAS_spec.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition integer_hash_spec :=
 DECLARE _integer_hash
  WITH i : Z
  PRE [ tint ]
   PROP () PARAMS (vint i) GLOBALS () SEP ()
  POST [ tint ]
   PROP () RETURN (vint (i * 654435761)) SEP ().
(* One might think it should just return an unknown number, but in fact it needs to follow a known hash
   function at the logic level to be useful. *)

Definition tentry := Tstruct _entry noattr.

(* Having size as a large known constant tends to make everything slow, so here's a hack. *)
Definition has_size : {x : Z | x = 16384}.
Proof.
  eexists; eauto.
Qed.

Local Program Instance hf1 : hash_fun := { size := proj1_sig has_size; hash i := (i * 654435761) mod (proj1_sig has_size) }.
Next Obligation.
Proof.
  rewrite (proj2_sig has_size); computable.
Qed.
Next Obligation.
  - apply Z_mod_lt; rewrite (proj2_sig has_size); computable.
  - apply Z_mod_lt; rewrite (proj2_sig has_size); computable.
Qed.

Lemma size_signed : size <= Int.max_signed.
Proof.
  unfold size; simpl. rewrite (proj2_sig has_size). rep_lia.
Qed.

(* We don't need histories, but we do need to know that a non-zero key is persistent. *)

Local Instance zero_perm : @sepalg.Perm_alg Z (fun a b c => if eq_dec a 0 then c = b else c = a /\ (b = 0 \/ a = b)).
Proof.
  constructor.
  + intros; hnf in *.
    if_tac in H; subst; auto.
    destruct H, H0; subst; auto.
  + intros; hnf in *.
    exists (if eq_dec b 0 then c else b); split; hnf.
    * if_tac; auto; split; auto.
      if_tac in H; subst.
      { rewrite -> if_false in H0 by auto; tauto. }
      destruct H as [? [|]]; try contradiction; subst.
      rewrite -> if_false in H0 by auto; tauto.
    * if_tac; subst.
      { if_tac in H0; tauto. }
      destruct H; subst.
      if_tac; subst.
      { if_tac in H0; subst; auto; contradiction. }
      destruct H2; try contradiction; subst.
      rewrite -> if_false in H0 by auto; tauto.
  + intros; hnf in *.
      if_tac; if_tac in H; subst; auto; try tauto.
      destruct H as [? [|]]; subst; auto; contradiction.
  + intros; hnf in *.
    if_tac in H; if_tac in H0; subst; try tauto.
    destruct H; auto.
Qed.

Local Program Instance zero_PCM : Ghost := { valid a := True : Prop;
  Join_G a b c := if eq_dec a 0 then c = b else c = a /\ (b = 0 \/ a = b) }.
Next Obligation.
Proof.
  exists (fun _ => 0); auto.
  - intro; hnf; auto.
  - intros; exists O; hnf; auto.
Defined.

Local Instance zero_order : PCM_order (fun a b => a = 0 \/ a = b).
Proof.
  constructor; simpl; intros.
  - constructor.
    + intro; auto.
    + intros ???[|][|]; subst; auto.
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
  atomic_int_at Ews (vint ki) pk * atomic_int_at Ews (vint vi) pv.

Definition wf_table (T : list (Z * Z)) := forall k i, k <> 0 -> fst (Znth i T) = k -> lookup T k = Some i.

Definition hashtable H g lg entries := EX T : list (Z * Z),
  !!(Zlength T = size /\ wf_table T /\ forall k v, H k = Some v <-> In (k, v) T /\ v <> 0) &&
  excl g H * iter_sepcon (hashtable_entry T lg entries) (upto (Z.to_nat size)).

Global Instance Inhabitant_unit : Inhabitant unit := tt.

Program Definition set_item_spec := DECLARE _set_item
  ATOMIC TYPE (ConstType (Z * Z * globals * share * list (val * val) * gname * list gname)) OBJ H INVS empty
  WITH k, v, gv, sh, entries, g, lg
  PRE [ tint, tint ]
    PROP (readable_share sh; repable_signed k; repable_signed v; k <> 0; v <> 0;
      Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
    PARAMS (vint k; vint v) GLOBALS (gv)
    SEP (data_at sh (tarray tentry size) entries (gv _m_entries)) | (hashtable H g lg entries)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at sh (tarray tentry size) entries (gv _m_entries)) | (hashtable (map_upd H k v) g lg entries).

(* Read the most recently written value. *)
Program Definition get_item_spec := DECLARE _get_item
  ATOMIC TYPE (ConstType (Z * globals * share * list (val * val) * gname * list gname)) OBJ H INVS empty
  WITH k, gv, sh, entries, g, lg
  PRE [ tint ]
    PROP (readable_share sh; repable_signed k; k <> 0; Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
    PARAMS (vint k) GLOBALS (gv)
    SEP (data_at sh (tarray tentry size) entries (gv _m_entries)) | (hashtable H g lg entries)
  POST [ tint ]
   EX v : Z,
    PROP ()
    LOCAL (temp ret_temp (vint v))
    SEP (data_at sh (tarray tentry size) entries (gv _m_entries)) | (!!(if eq_dec v 0 then H k = None else H k = Some v) && hashtable H g lg entries).

Program Definition add_item_spec := DECLARE _add_item
  ATOMIC TYPE (ConstType (Z * Z * globals * share * list (val * val) * gname * list gname)) OBJ H INVS empty
  WITH k, v, gv, sh, entries, g, lg
  PRE [ tint, tint ]
    PROP (readable_share sh; repable_signed k; repable_signed v; k <> 0; v <> 0;
      Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
    PARAMS (vint k; vint v) GLOBALS (gv)
    SEP (data_at sh (tarray tentry size) entries (gv _m_entries)) | (hashtable H g lg entries)
  POST [ tint ]
   EX b : bool,
    PROP ()
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (data_at sh (tarray tentry size) entries (gv _m_entries)) |
   (!!(H k = None <-> b = true) && hashtable (if b then map_upd H k v else H) g lg entries).

Definition init_table_spec :=
 DECLARE _init_table
  WITH gv : globals
  PRE [ ]
   PROP ()
   PARAMS () GLOBALS (gv)
   SEP (mem_mgr gv; data_at_ Ews (tarray tentry size) (gv _m_entries))
  POST [ tvoid ]
   EX entries : list (val * val), EX g : gname, EX lg : list gname,
   PROP (Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
   LOCAL ()
   SEP (mem_mgr gv; data_at Ews (tarray tentry size) entries (gv _m_entries);
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

Definition f_lock_inv sh gsh entries gh p t locksp lockt resultsp res gv :=
  EX b1 : bool, EX b2 : bool, EX b3 : bool, EX h : _,
    !!(add_events empty_map [HAdd 1 1 b1; HAdd 2 1 b2; HAdd 3 1 b3] h) && ghost_hist gsh h gh *
    data_at sh (tarray tentry size) entries p *
    data_at sh (tarray (tptr t_lock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
    data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp *
    data_at Ews tint (vint (Zlength (List.filter id [b1; b2; b3]))) res * mem_mgr gv.

Definition f_lock_pred tsh sh gsh entries gh p t locksp lockt resultsp res gv :=
  selflock (f_lock_inv sh gsh entries gh p t locksp (ptr_of lockt) resultsp res gv) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH tid : val, x : share * share * share * list (val * val) * namespace * gname * gname * list gname * globals * Z *
                      lock_handle * val
  PRE [ tptr tvoid ]
   let '(sh, gsh, tsh, entries, i, gh, g, lg, gv, t, lockt, res) := x in
   PROP (0 <= t < 3; readable_share sh; readable_share tsh; gsh <> Share.bot;
         Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength lg = size)
   PARAMS (tid)  GLOBALS (gv)
   SEP (mem_mgr gv; data_at sh (tarray tentry size) entries (gv _m_entries);
        inv i (hashtable_inv gh g lg entries);
        ghost_hist(hist_el := hashtable_hist_el) gsh empty_map gh;
        data_at Ews tint (vint t) tid; malloc_token Ews tint tid;
        data_at sh (tarray (tptr t_lock) 3) (upd_Znth t (repeat Vundef 3) (ptr_of lockt)) (gv _thread_locks);
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) (gv _results);
        data_at_ Ews tint res;
        lock_inv tsh lockt (f_lock_pred tsh sh gsh entries gh (gv _m_entries) t
                                        (gv _thread_locks) lockt (gv _results) res gv))
  POST [ tint ] PROP () RETURN (Vint Int.zero) SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [makelock_spec; freelock_spec; acquire_spec;
  release_spec; spawn_spec; surely_malloc_spec; make_atomic_spec; atom_load_spec; atom_store_spec; atom_CAS_spec;
  integer_hash_spec; set_item_spec; get_item_spec; add_item_spec; init_table_spec; f_spec; main_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (t, gv).
  Intros v.
  forward_if (v <> nullval).
  { if_tac; entailer!. }
  - forward_call 1.
    entailer!.
  - forward.
    entailer!.
  - forward.
    rewrite -> if_false by auto.
    Exists v; entailer!.
Qed.

Lemma body_integer_hash: semax_body Vprog Gprog f_integer_hash integer_hash_spec.
Proof.
  start_function.
  forward.
Qed.

Opaque upto.

Lemma hash_size : forall k, (k * 654435761) mod size = hash k mod size.
Proof.
  intro; simpl.
  rewrite Zmod_mod; split; auto; lia.
Qed.

Arguments size : simpl never.
Arguments hash : simpl never.

Lemma failed_entries : forall k i i1 keys lg T entries (Hk : k <> 0) (Hi : 0 <= i < size)
  (Hi1 : (i + hash k) mod size = i1 mod size) (HT : Zlength T = size) (Hlg : Zlength lg = size)
  (Hkeys: Zlength keys = size)
  (Hfail : Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k)))),
  iter_sepcon (hashtable_entry T lg entries) (remove_Znth (i1 mod size) (upto (Z.to_nat size))) *
  iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
    (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))
  |-- !! Forall (fun x => fst x <> 0 /\ fst x <> k) (sublist 0 i (rebase T (hash k))).
Proof.
  intros.
  rewrite -> List.Forall_forall, prop_forall; apply allp_right; intros (k', v').
  rewrite prop_forall; apply allp_right; intro Hin.
  apply In_Znth in Hin as (j & Hj & Hjth).
  pose proof (hash_range k).
  erewrite Zlength_sublist in Hj by (rewrite ?Zlength_rebase; lia).
  rewrite -> Znth_sublist, Znth_rebase in Hjth by lia.
  assert (0 <= (j + hash k) mod size < size) by (apply Z_mod_lt, size_pos).
  pose proof (Z_mod_lt i1 _ size_pos).
  assert ((j + hash k) mod size <> i1 mod size).
  { rewrite <- Hi1; intro Heq.
    apply Zmod_plus_inv in Heq; [|apply size_pos].
    rewrite !Zmod_small in Heq; lia. } cbn [fst].
  rewrite -> @iter_sepcon_Znth_remove with (d := Inhabitant_Z)
                                         (i := (j + hash k) mod size),
      @iter_sepcon_Znth' with (d := Inhabitant_Z) (i := j)(l := upto _) by
    (try apply Cveric; try rewrite -> Zlength_upto; lia).
  rewrite -> !Znth_upto by (rewrite -> Z2Nat.id; lia).
  unfold hashtable_entry at 1.
  rewrite Z.add_0_r in Hjth; replace (Zlength T) with size in Hjth; rewrite Hjth.
  destruct (Znth _ entries).
  Intros; rewrite <- !sepcon_assoc.
  rewrite (sepcon_comm _ (ghost_snap(P := zero_PCM) _ _)).
  rewrite <- !sepcon_assoc, snap_master_join1 by auto.
  Intros; apply prop_right; simpl.
  eapply Forall_Znth in Hfail.
  rewrite -> Znth_sublist, Z.add_0_r, @Znth_rebase with (i := j) in Hfail; auto; try lia.
  replace (Zlength keys) with size in Hfail; intuition; subst; intuition.
  { rewrite -> Zlength_sublist; auto; try lia.
    rewrite Zlength_rebase; lia. }
Qed.

Corollary entries_lookup : forall k i i1 keys lg T entries (Hk : k <> 0) (Hi : 0 <= i < size)
  (Hi1 : (i + hash k) mod size = i1 mod size) (HT : Zlength T = size) (Hlg : Zlength lg = size)
  (Hkeys: Zlength keys = size)
  (Hfail : Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
  (Hhit : fst (Znth (i1 mod size) T) = k \/ fst (Znth (i1 mod size) T) = 0),
  iter_sepcon (hashtable_entry T lg entries) (remove_Znth (i1 mod size) (upto (Z.to_nat size))) *
  iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
    (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))
  |-- !! (lookup T k = Some (i1 mod size)).
Proof.
  intros.
  eapply derives_trans; [apply failed_entries; eauto | apply prop_left; intro; apply prop_right].
  pose proof (hash_range k).
  unfold lookup; erewrite index_of'_succeeds.
  simpl; eauto.
  - rewrite Zlength_rebase; lia.
  - auto.
  - rewrite -> Znth_rebase by lia.
    rewrite -> HT, Hi1; auto.
Qed.

Lemma wf_table_upd : forall T k v i (Hwf : wf_table T) (HT : Zlength T = size) (Hi : lookup T k = Some i)
  (Hk : k <> 0), wf_table (upd_Znth i T (k, v)).
Proof.
  intros; intros ?? Hj ?.
  exploit lookup_range; eauto; intro.
  destruct (eq_dec i0 i); subst.
  - rewrite -> upd_Znth_same, lookup_upd_same; auto.
  - rewrite -> upd_Znth_diff' in Hj |- * by auto.
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

Lemma snaps_dealloc : forall {A} (l : list A) f g, iter_sepcon (fun i => ghost_snap (f i) (g i)) l |-- (emp)%I.
Proof.
  intros; apply (own_list_dealloc(RA := snap_PCM)).
  intro; do 3 eexists; apply derives_refl.
Qed.

Lemma upto_sub : forall n m, (n <= m)%nat -> upto m = upto n ++ map (Z.add n) (upto (m - n)).
Proof.
  intros.
  replace m with (n + (m - n))%nat by lia.
  rewrite upto_app; repeat f_equal; lia.
Qed.

Notation empty := (@empty coPset _).
Notation top := (@top coPset _).

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call k.
  pose proof size_pos as Hsize; pose proof size_signed as Hsigned.
  forward_loop (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); lvar _ref tint v_ref; temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (AS; data_at_ Tsh tint v_ref; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))))%assert
    continue: (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (Int.min_signed <= Int.signed (Int.repr i1) < Int.max_signed; i1 mod size = (i + hash k) mod size;
          0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 (i + 1) (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); lvar _ref tint v_ref; temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (AS; data_at_ Tsh tint v_ref; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat (i + 1)))))%assert.
  { Exists 0 (k * 654435761)%Z (repeat 0 (Z.to_nat size)); rewrite sublist_nil; entailer!.
    split; [apply hash_size|].
    rewrite -> coqlib4.Zlength_repeat, Z2Nat.id; auto; lia. }
  - Intros i i1 keys; forward. forward.
    rewrite -> sub_repr, and_repr; simpl.
    rewrite -> Zland_two_p with (n := 14) by lia.
    replace (2 ^ 14) with size by (setoid_rewrite (proj2_sig has_size); auto).
    exploit (Z_mod_lt i1 size); [lia | intro Hi1].
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) as Hi1' by lia.
    match goal with H : Forall _ _ |- _ => pose proof (Forall_Znth _ _ _ Hi1' H) as Hptr end.
    destruct (Znth (i1 mod size) entries) as (pki, pvi) eqn: Hpi; destruct Hptr.
    forward; setoid_rewrite Hpi.
    { entailer!. }
    assert (Zlength (rebase keys (hash k)) = size) as Hrebase.
    { rewrite Zlength_rebase; replace (Zlength keys) with size; auto; apply hash_range. }
    forward_call atomic_load_int (pki, top, empty,
      fun v : Z => AS * ghost_snap v (Znth (i1 mod size) lg)).
    { rewrite !sepcon_assoc; apply sepcon_derives; [|cancel].
      iIntros ">AS".
      iDestruct ("AS") as (HT) "[hashtable Hclose]"; simpl.
      iDestruct "hashtable" as (T) "((% & excl) & entries)".
      rewrite -> @iter_sepcon_Znth' with (d := Inhabitant_Z) (i := i1 mod size) by
        (try apply Cveric; rewrite Zlength_upto Z2Nat.id; lia).
      erewrite Znth_upto by (rewrite -> ?Zlength_upto, Z2Nat.id; lia).
      unfold hashtable_entry at 1.
      rewrite Hpi.
      destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
      iDestruct "entries" as "((((% & master) & k) & v) & entries)".
      iModIntro; iExists Ews, ki; iFrame "k".
      iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
      iIntros "k".
      iMod (make_snap with "master") as "[$ master]".
      iDestruct "Hclose" as "[Hclose _]"; iApply "Hclose".
      unfold hashtable; iExists T; iFrame "excl".
      iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
      iApply "entries"; unfold hashtable_entry.
      rewrite Hpi HHi; iFrame.
      iSplit; auto; iPureIntro; split; auto; tauto. }
    Intros k1.
    focus_SEP 2.
    focus_SEP 2.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: _ :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: data_at_ Tsh tint v_ref :: R)))) end.
    + assert (forall k1, (k1 <> k /\ k1 <> 0) ->
        Zlength (upd_Znth (i1 mod size) keys k1) = size /\
        Forall (fun z => z <> 0 /\ z <> k)
          (sublist 0 (i + 1) (rebase (upd_Znth (i1 mod size) keys k1) (hash k)))).
      { split; [rewrite upd_Znth_Zlength; auto; lia|].
        replace (i1 mod size) with ((i + hash k) mod size); replace size with (Zlength keys);
          rewrite -> !rebase_upd' by (try lia; replace (Zlength keys) with size; apply Z_mod_lt; lia).
        rewrite -> sublist_upd_Znth_lr by (try lia; setoid_rewrite Hrebase; lia).
        rewrite -> sublist_split with (mid := i), sublist_len_1 by (try lia; setoid_rewrite Hrebase; lia).
        rewrite -> Z.sub_0_r, upd_Znth_app2, Forall_app; rewrite Zlength_sublist;
          rewrite -> ?Zlength_cons, ?Zlength_nil; try lia; try (setoid_rewrite Hrebase; lia).
        split; auto.
        rewrite -> Z.sub_0_r, Zminus_diag, upd_Znth0.
        constructor. tauto. constructor. }
      forward_if (k1 = 0).
      { forward.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
        rewrite -> Z2Nat.inj_add, upto_app, iter_sepcon_app by lia.
        change (upto (Z.to_nat 1)) with [0]; simpl iter_sepcon; rewrite -> Z2Nat.id, Z.add_0_r by lia.
        replace ((i + hash k) mod size) with (i1 mod size); rewrite -> Zmod_mod, upd_Znth_same by lia; entailer!.
        { split; auto.
          split; etransitivity; try apply Z_mod_lt; auto; try computable.
          setoid_rewrite (proj2_sig has_size); computable. }
        erewrite iter_sepcon_func_strong; [apply derives_refl|]; simpl; intros.
        rewrite upd_Znth_diff'; auto; try lia.
        replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
        rewrite -> In_upto, Z2Nat.id in * by lia.
        rewrite -> !Zmod_small in X; lia. }
      { forward.
        entailer!. }
      Intros; subst.
      forward_call atomic_CAS_int (pki, Tsh, v_ref, 0, k, top, empty,
        fun v : Z => AS * ghost_snap (if eq_dec v 0 then k else v) (Znth (i1 mod size) lg) *
          iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
             (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))).
      { iIntros "[[[snap AS] entries] snaps]"; iSplitR "entries"; [|iVST; cancel_frame].
        iMod ("AS") as (HT) "[hashtable Hclose]".
        iDestruct "hashtable" as (T) "((% & excl) & entries)".
        match goal with H : _ /\ _ /\ _ |- _ => destruct H as (? & ? & ?) end.
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)
                                          (f := hashtable_entry _ _ _)
            by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; try lia).
        erewrite Znth_upto by (rewrite -> ?Zlength_upto, Z2Nat.id; lia).
        unfold hashtable_entry at 1.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        iDestruct "entries" as "((((% & master) & k) & v) & entries)".
        iModIntro; iExists Ews, ki; iFrame "k".
        iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "k".
        iMod (snap_master_update1(ORD := zero_order) _ _ _ (if eq_dec ki 0 then k else ki) with "[$snap $master]") as "[snap master]".
        { if_tac; auto. }
        assert (0 <= i1 mod size < Zlength T) by lia.
        assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size by lia; apply hash_range).
        assert (0 <= i < Zlength (rebase T (hash k))) by (rewrite Zlength_rebase; auto; lia).
        assert (fst (Znth i (rebase T (hash k))) = ki).
        { rewrite -> Znth_rebase by (auto; lia).
          replace (Zlength T) with size by lia; replace ((i + hash k) mod size) with (i1 mod size); rewrite HHi; auto. }
        iAssert (!!((ki = k \/ ki = 0) -> lookup T k = Some (i1 mod size))) as %Hindex.
        { rewrite prop_impl_imp. iIntros "%".
          iApply (entries_lookup with "[$entries $snaps]"); auto.
          rewrite HHi. now simpl. }
        iFrame "snap snaps".
        iDestruct "Hclose" as "[Hclose _]"; iApply "Hclose".
        unfold hashtable; iExists (upd_Znth (i1 mod size) T (if eq_dec ki 0 then k else ki, vi)); iFrame "excl".
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z) (i := i1 mod size)
                                          (l := upto (Z.to_nat size))
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        rewrite -> Hpi, upd_Znth_same by lia; iFrame.
        iSplitL "".
        { iSplit; auto; iPureIntro.
          split; [rewrite upd_Znth_Zlength; auto|].
          if_tac; [subst | erewrite upd_Znth_triv; auto].
          split; [apply wf_table_upd; auto|].
          intros.
          etransitivity; eauto; split; intros (Hin & ?); split; auto.
            - eapply In_upd_Znth_old; auto; try lia.
              rewrite HHi; intro X; inv X; tauto.
            - apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
        iSplitL "".
        { iSplit; auto; iPureIntro.
          if_tac; tauto. }
        erewrite iter_sepcon_func_strong; first iFrame.
        intros ??%In_remove_upto; simpl.
        rewrite !upd_Znth_diff'; auto; try lia.
        apply Z_mod_lt; auto. }
      Intros k1.
      focus_SEP 2.
      Opaque eq_dec.
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
        forward_if (PROP () ((LOCALx Q) (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: R)))) end.
      * if_tac; [discriminate|].
        forward.
        forward_if (k1 = k).
        { forward.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
          rewrite -> Zmod_mod, Z2Nat.inj_add, upto_app, iter_sepcon_app by lia.
          change (upto (Z.to_nat 1)) with [0]; simpl iter_sepcon; rewrite -> Z2Nat.id, Z.add_0_r by lia.
          replace ((i + hash k) mod size) with (i1 mod size); rewrite -> upd_Znth_same by lia; entailer!.
          { split; auto.
            split; etransitivity; try apply Z_mod_lt; auto; try computable.
            setoid_rewrite (proj2_sig has_size); computable. }
          erewrite iter_sepcon_func_strong; [apply derives_refl|]; simpl; intros.
          rewrite upd_Znth_diff'; auto; try lia.
          replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
          rewrite -> In_upto, Z2Nat.id in * by lia.
          rewrite !Zmod_small in X; lia. }
        { forward.
          entailer!. }
        entailer!; apply derives_refl.
      * forward.
        if_tac; [|contradiction].
        subst; entailer!.
      * entailer!.
        apply derives_refl.
    + forward.
      subst; entailer!.
    + forward; setoid_rewrite Hpi.
      { entailer!. }
      forward_call atomic_store_int (pvi, v, top, empty, Q).
      { subst Frame; instantiate (1 := [data_at_ Tsh tint v_ref; data_at sh (tarray tentry size) entries (gv _m_entries)]); simpl; cancel.
        iIntros "((snap & >AS) & snaps)".
        iDestruct ("AS") as (HT) "[hashtable Hclose]".
        iDestruct "hashtable" as (T) "((% & excl) & entries)".
        match goal with H : _ /\ _ /\ _ |- _ => destruct H as (? & ? & ?) end.
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(f := hashtable_entry _ _ _)
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite -> Z2Nat.id; lia).
        unfold hashtable_entry at 1.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        iDestruct "entries" as "((((% & master) & k) & v) & entries)".
        iModIntro; iExists Ews.
        iPoseProof (atomic_int_at__ with "v") as "$".
        iSplitL ""; [auto|].
        iIntros "v".
        iAssert (!! (ki = k)) as %Hk.
        { iCombine "snap master" as "master"; rewrite -> snap_master_join1.
          iDestruct "master" as "[[% | %] ?]"; auto; contradiction. }
        iMod (exclusive_update _ (map_upd HT k v) with "excl") as "excl".
        iDestruct "snap" as "_".
        iPoseProof (snaps_dealloc with "snaps") as "_".
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        unfold hashtable.
        iFrame.
        iExists (upd_Znth (i1 mod size) T (k, v)).
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(l := upto (Z.to_nat size))
            by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        rewrite -> upd_Znth_same by lia.
        assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size by lia; apply hash_range).
        rewrite Hpi; iSplitL "".
          { iSplit; auto; iPureIntro.
            split; [rewrite upd_Znth_Zlength; lia|].
            split; [apply wf_table_upd_same; rewrite ?HHi; auto|].
            intros; unfold map_upd; if_tac.
            * split; [intro X; inv X; split; auto; apply upd_Znth_In; lia|].
              subst; intros (Hin & ?).
              apply In_Znth in Hin; destruct Hin as (j & Hj & Hjth).
              destruct (eq_dec j (i1 mod size)).
              { subst; rewrite -> upd_Znth_same in Hjth by lia; inv Hjth; auto. }
              rewrite -> upd_Znth_diff' in Hjth by (auto; lia).
              match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto;
                exploit (H k (i1 mod size)); rewrite ?HHi; auto end.
              congruence.
            * etransitivity; eauto; split; intros (Hin & ?); split; auto.
              -- eapply In_upd_Znth_old; auto; try lia.
                 rewrite HHi; intro X; inv X; contradiction.
              -- apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
          subst; iFrame.
          iSplitL ""; auto.
          erewrite iter_sepcon_func_strong; [auto|].
          intros ??%In_remove_upto; simpl.
          rewrite -> !upd_Znth_diff' by lia; auto.
          apply Z_mod_lt; auto. }
      forward.
      cancel.
  - Intros i i1 keys.
    forward.
    { entailer!.
      rewrite -> (Int.signed_repr 1) by computable; lia. }
    Exists ((i + 1) mod size) (i1 + 1) keys; entailer!.
    + split; [|split].
      * rewrite <- Zplus_mod_idemp_l.
        replace (i1 mod _) with ((i + hash k) mod size); simpl.
        rewrite -> !Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto.
      * apply Z.mod_bound_pos; lia.
      * erewrite <- sublist_sublist00; [apply Forall_sublist; eauto|].
        split; [apply Z.mod_bound_pos | apply Zmod_le]; lia.
    + erewrite -> upto_sub, iter_sepcon_app; first by iIntros "[$ ?]"; iApply snaps_dealloc.
      apply Z2Nat.inj_le, Zmod_le; try lia.
      apply Z.mod_bound_pos; lia.
Qed.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call k.
  pose proof size_pos as Hsize; pose proof size_signed as Hsigned.
  forward_loop (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); gvars gv)
    SEP (AS; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))))%assert
    continue: (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (Int.min_signed <= Int.signed (Int.repr i1) < Int.max_signed;
          i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 (i + 1) (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); temp _key (vint k); gvars gv)
    SEP (AS; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat (i + 1)))))%assert.
  { Exists 0 (k * 654435761)%Z (repeat 0 (Z.to_nat size)); rewrite sublist_nil; entailer!.
    split; [apply hash_size|].
    rewrite -> coqlib4.Zlength_repeat, Z2Nat.id; auto; lia. }
  - Intros i i1 keys; forward.
    rewrite -> sub_repr, and_repr; simpl.
    rewrite -> Zland_two_p with (n := 14) by lia.
    replace (2 ^ 14) with size by (setoid_rewrite (proj2_sig has_size); auto).
    exploit (Z_mod_lt i1 size); [lia | intro Hi1].
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) as Hi1' by lia.
    match goal with H : Forall _ _ |- _ => pose proof (Forall_Znth _ _ _ Hi1' H) as Hptr end.
    destruct (Znth (i1 mod size) entries) as (pki, pvi) eqn: Hpi; destruct Hptr.
    forward; setoid_rewrite Hpi.
    { entailer!. }
    assert (Zlength (rebase keys (hash k)) = size) as Hrebase.
    { rewrite Zlength_rebase; replace (Zlength keys) with size; auto; apply hash_range. }
    forward_call atomic_load_int (pki, top, empty,
      fun v => if eq_dec v 0 then Q v else AS * ghost_snap v (Znth (i1 mod size) lg) *
        iter_sepcon (fun i0 : Z => ghost_snap (Znth ((i0 + hash k) mod size) keys)
          (Znth ((i0 + hash k) mod size) lg)) (upto (Z.to_nat i))).
    { subst Frame; instantiate (1 := [data_at sh (tarray tentry size) entries (gv _m_entries)]); simpl; cancel.
      iIntros "(>AS & snaps)".
      iDestruct "AS" as (HT) "[hashtable Hclose]".
      iDestruct "hashtable" as (T) "((% & excl) & entries)".
      match goal with H : _ /\ _ /\ _ |- _ => destruct H as (? & ? & ?) end.
      rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                        (i := i1 mod size)(f := hashtable_entry _ _ _)
        by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
      rewrite -> Znth_upto by (rewrite -> Z2Nat.id; lia).
      unfold hashtable_entry at 1.
      rewrite Hpi.
      destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
      iDestruct "entries" as "((((% & master) & k) & v) & entries)".
      iModIntro; iExists Ews, ki; iFrame "k".
      iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
      iIntros "k".
      if_tac.
      * subst ki.
        iAssert (!! (lookup T k = Some (i1 mod size))) as %Hindex.
        { iApply (entries_lookup with "[$entries $snaps]"); auto.
          rewrite HHi; auto. }
        iPoseProof (snaps_dealloc with "snaps") as "_".
        iDestruct "Hclose" as "[_ Hclose]"; iApply "Hclose".
        iFrame.
        rewrite -> if_true by auto; iSplit.
        { destruct (HT k) eqn: Hk; auto.
          match goal with H : forall k v, _ <-> _ |- _ => rewrite -> H in Hk end.
          destruct Hk as (Hk & ?); apply In_Znth in Hk.
          destruct Hk as (j & ? & Hjth).
          match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto end.
          rewrite Hindex; congruence. }
        unfold hashtable; iExists T.
        iSplitL ""; [auto|].
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(l := upto (Z.to_nat size))
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        rewrite -> Hpi, HHi; iFrame; auto.
      * iMod (make_snap with "master") as "[snap master]".
        iFrame "snap snaps".
        iDestruct "Hclose" as "[Hclose _]"; iApply "Hclose".
        unfold hashtable; iExists T.
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(l := upto (Z.to_nat size))
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        rewrite -> Hpi, HHi; iFrame; auto. }
    Intros k1.
    forward_if (k1 <> k).
    + subst; if_tac; [contradiction | Intros].
      forward; setoid_rewrite Hpi.
      { entailer!. }
      forward_call atomic_load_int (pvi, top, empty, Q).
      { subst Frame; instantiate (1 := [data_at sh (tarray tentry size) entries (gv _m_entries)]); simpl; cancel.
        iIntros "((>AS & snap) & snaps)".
        iDestruct "AS" as (HT) "[hashtable Hclose]".
        iDestruct "hashtable" as (T) "((% & excl) & entries)".
        match goal with H : _ /\ _ /\ _ |- _ => destruct H as (? & ? & ?) end.
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(f := hashtable_entry _ _ _)
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite -> Z2Nat.id; lia).
        unfold hashtable_entry at 1.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        iDestruct "entries" as "((((% & master) & k) & v) & entries)".
        iModIntro; iExists Ews, vi; iFrame "v".
        iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "v".
        iAssert (!! (ki = k)) as %Hk.
        { iCombine "snap master" as "master"; rewrite -> snap_master_join1.
          iDestruct "master" as "[[% | %] ?]"; auto; contradiction. }
        subst ki.
        iAssert (!! (lookup T k = Some (i1 mod size))) as %Hindex.
        { iApply (entries_lookup with "[$entries $snaps]"); auto.
          rewrite HHi; auto. }
        iDestruct "snap" as "_".
        iPoseProof (snaps_dealloc with "snaps") as "_".
        iDestruct "Hclose" as "[_ Hclose]"; iApply "Hclose".
        simpl; iFrame; iSplit.
        { iPureIntro; if_tac.
          * destruct (HT k) eqn: Hk; auto.
            match goal with H : forall k v, _ <-> _ |- _ => rewrite -> H in Hk end.
            destruct Hk as (Hk & ?); apply In_Znth in Hk.
            destruct Hk as (j & ? & Hjth).
            match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto end.
            rewrite Hindex; congruence.
          * match goal with H : forall k v, ?P <-> _ |- _ => rewrite H end.
            split; auto.
            exploit (Znth_In (i1 mod size) T); [lia|].
            rewrite HHi; auto. }
        unfold hashtable; iExists T.
        iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(l := upto (Z.to_nat size))
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        rewrite -> Hpi, HHi; iFrame; auto. }
      unfold POSTCONDITION, abbreviate; simpl map.
      Intros v'; forward.
      Exists v'; entailer!.
    + forward.
      entailer!.
    + Intros; forward_if (k1 <> 0).
      * subst; rewrite -> eq_dec_refl.
        unfold POSTCONDITION, abbreviate; simpl map.
        forward.
        simpl; Exists 0; entailer!.
      * if_tac; [contradiction|].
        forward.
        entailer!.
      * intros.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
        rewrite -> Z2Nat.inj_add, upto_app, iter_sepcon_app by lia.
        change (upto (Z.to_nat 1)) with [0]; simpl iter_sepcon.
        rewrite -> Z2Nat.id, Z.add_0_r by lia.
        Intros; rewrite -> if_false by auto.
        replace ((i + hash k) mod size) with (i1 mod size); rewrite -> upd_Znth_same by lia; entailer!.
        { split.
          { split; etransitivity; try apply Z_mod_lt; auto; try computable.
            setoid_rewrite (proj2_sig has_size); computable. }
          split; [rewrite Zmod_mod; auto|].
          split; [rewrite upd_Znth_Zlength; auto; lia|].
          replace (i1 mod size) with ((i + hash k) mod size); replace size with (Zlength keys);
            rewrite -> !rebase_upd' by (try lia; replace (Zlength keys) with size; apply Z_mod_lt; lia).
          rewrite -> sublist_upd_Znth_lr by (try lia; setoid_rewrite Hrebase; lia).
          rewrite -> sublist_split with (mid := i), sublist_len_1 by (try lia; setoid_rewrite Hrebase; lia).
          rewrite -> Z.sub_0_r, upd_Znth_app2, Forall_app; rewrite Zlength_sublist;
            rewrite -> ?Zlength_cons, ?Zlength_nil; try lia; try (setoid_rewrite Hrebase; lia).
          split; auto.
          rewrite -> Z.sub_0_r, Zminus_diag, upd_Znth0.
          constructor; auto. }
        erewrite iter_sepcon_func_strong; [apply derives_refl|]; intros; simpl.
        rewrite upd_Znth_diff'; auto; try lia.
        replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
        rewrite -> In_upto, Z2Nat.id in * by lia.
        rewrite !Zmod_small in X; lia.
  - Intros i i1 keys.
    forward.
    { entailer!.
      rewrite -> (Int.signed_repr 1) by computable; lia. }
    Exists ((i + 1) mod size) (i1 + 1) keys; entailer!.
    + split; [|split].
      * rewrite <- Zplus_mod_idemp_l.
        replace (i1 mod _) with ((i + hash k) mod size); simpl.
        rewrite -> !Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto.
      * apply Z.mod_bound_pos; lia.
      * erewrite <- sublist_sublist00; [apply Forall_sublist; eauto|].
        split; [apply Z.mod_bound_pos | apply Zmod_le]; lia.
    + erewrite -> upto_sub, iter_sepcon_app; first by iIntros "[$ ?]"; iApply snaps_dealloc.
      apply Z2Nat.inj_le, Zmod_le; try lia.
      apply Z.mod_bound_pos; lia.
Qed.

Lemma body_add_item : semax_body Vprog Gprog f_add_item add_item_spec.
Proof.
  start_function.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call k.
  pose proof size_pos as Hsize; pose proof size_signed as Hsigned.
  forward_loop (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 i (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); lvar _ref tint v_ref; temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (AS; data_at_ Tsh tint v_ref; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))))%assert
    continue: (EX i : Z, EX i1 : Z, EX keys : list Z,
    PROP (Int.min_signed <= Int.signed (Int.repr i1) < Int.max_signed;
          i1 mod size = (i + hash k) mod size; 0 <= i < size; Zlength keys = size;
          Forall (fun z => z <> 0 /\ z <> k) (sublist 0 (i + 1) (rebase keys (hash k))))
    LOCAL (temp _idx (vint i1); lvar _ref tint v_ref; temp _key (vint k); temp _value (vint v); gvars gv)
    SEP (AS; data_at_ Tsh tint v_ref; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
           (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat (i + 1)))))%assert.
  { Exists 0 (k * 654435761)%Z (repeat 0 (Z.to_nat size)); rewrite sublist_nil; entailer!.
    split; [apply hash_size|].
    rewrite -> coqlib4.Zlength_repeat, Z2Nat.id; auto; lia. }
  - Intros i i1 keys; forward. forward.
    rewrite -> sub_repr, and_repr; simpl.
    rewrite -> Zland_two_p with (n := 14) by lia.
    replace (2 ^ 14) with size by (setoid_rewrite (proj2_sig has_size); auto).
    exploit (Z_mod_lt i1 size); [lia | intro Hi1].
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) as Hi1' by lia.
    match goal with H : Forall _ _ |- _ => pose proof (Forall_Znth _ _ _ Hi1' H) as Hptr end.
    destruct (Znth (i1 mod size) entries) as (pki, pvi) eqn: Hpi; destruct Hptr.
    forward; setoid_rewrite Hpi.
    { entailer!. }
    assert (Zlength (rebase keys (hash k)) = size) as Hrebase.
    { rewrite Zlength_rebase; replace (Zlength keys) with size; auto; apply hash_range. }
    forward_call atomic_load_int (pki, top, empty, fun v : Z => AS * ghost_snap v (Znth (i1 mod size) lg)).
    { subst Frame; instantiate (1 := [data_at Tsh tint (vint 0) v_ref; data_at _ (tarray tentry _) entries _; iter_sepcon _ _]); simpl; cancel.
      apply sepcon_derives, derives_refl.
      iIntros ">AS".
      iDestruct "AS" as (HT) "[hashtable Hclose]".
      iDestruct "hashtable" as (T) "((% & excl) & entries)".
      rewrite -> @iter_sepcon_Znth' with (d := Inhabitant_Z) (i := i1 mod size)
          by (try apply Cveric; rewrite -> ?Zlength_map, Zlength_upto, Z2Nat.id; lia).
      erewrite Znth_upto by (rewrite -> ?Zlength_upto, Z2Nat.id; lia).
      unfold hashtable_entry at 1.
      rewrite Hpi.
      destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
      iDestruct "entries" as "((((% & master) & k) & v) & entries)".
      iModIntro; iExists Ews, ki; iFrame "k".
      iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
      iIntros "k".
      iMod (make_snap with "master") as "[$ master]".
      iDestruct "Hclose" as "[Hclose _]"; iApply "Hclose".
      unfold hashtable; iExists T; iFrame "excl".
      iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
      iApply "entries"; unfold hashtable_entry.
      rewrite Hpi HHi; iFrame.
      iSplit; auto; iPureIntro; split; auto; tauto. }
    Intros k1.
    focus_SEP 2.
    focus_SEP 2.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: _ :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: data_at_ Tsh tint v_ref :: R)))) end.
    + assert (forall k1, (k1 <> k /\ k1 <> 0) ->
        Zlength (upd_Znth (i1 mod size) keys k1) = size /\
        Forall (fun z => z <> 0 /\ z <> k)
          (sublist 0 (i + 1) (rebase (upd_Znth (i1 mod size) keys k1) (hash k)))).
      { split; [rewrite upd_Znth_Zlength; auto; lia|].
        replace (i1 mod size) with ((i + hash k) mod size); replace size with (Zlength keys);
          rewrite -> !rebase_upd' by (try lia; replace (Zlength keys) with size; apply Z_mod_lt; lia).
        rewrite -> sublist_upd_Znth_lr by (try lia; setoid_rewrite Hrebase; lia).
        rewrite -> sublist_split with (mid := i), sublist_len_1 by (try lia; setoid_rewrite Hrebase; lia).
        rewrite -> Z.sub_0_r, upd_Znth_app2, Forall_app; rewrite Zlength_sublist;
          rewrite -> ?Zlength_cons, ?Zlength_nil; try lia; try (setoid_rewrite Hrebase; lia).
        split; auto.
        rewrite -> Z.sub_0_r, Zminus_diag, upd_Znth0.
        constructor; auto. easy. }
      forward_if (k1 = 0).
      { forward.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
        rewrite -> Zmod_mod, Z2Nat.inj_add, upto_app, iter_sepcon_app by lia.
        change (upto (Z.to_nat 1)) with [0]; simpl iter_sepcon.
        rewrite -> Z2Nat.id, Z.add_0_r by lia.
        replace ((i + hash k) mod size) with (i1 mod size); rewrite -> upd_Znth_same by lia; entailer!.
        { split; auto.
          split; etransitivity; try apply Z_mod_lt; auto; try computable.
          setoid_rewrite (proj2_sig has_size); computable. }
        erewrite iter_sepcon_func_strong; [apply derives_refl|]; intros; simpl.
        rewrite upd_Znth_diff'; auto; try lia.
        replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
        rewrite -> In_upto, Z2Nat.id in * by lia.
        rewrite !Zmod_small in X; lia. }
      { forward.
        entailer!. }
      Intros; subst.
        forward_call atomic_CAS_int (pki, Tsh, v_ref, 0, k, top, empty,
        fun v : Z => AS * ghost_snap (if eq_dec v 0 then k else v) (Znth (i1 mod size) lg) *
          iter_sepcon (fun i => ghost_snap (Znth ((i + hash k) mod size) keys)
            (Znth ((i + hash k) mod size) lg)) (upto (Z.to_nat i))).
      { subst Frame; instantiate (1 := [data_at _ (tarray tentry _) entries _]); simpl; cancel.
        iIntros "((snap & >AS) & snaps)".
        iDestruct "AS" as (HT) "[hashtable Hclose]".
        iDestruct "hashtable" as (T) "((% & excl) & entries)".
        match goal with H : _ /\ _ /\ _ |- _ => destruct H as (? & ? & ?) end.
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z)
                                          (i := i1 mod size)(f := hashtable_entry _ _ _)
            by (try apply Cveric; rewrite -> ?Zlength_map, Zlength_upto, Z2Nat.id; try lia).
        erewrite Znth_upto by (rewrite -> ?Zlength_upto, Z2Nat.id; lia).
        unfold hashtable_entry at 1.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        iDestruct "entries" as "((((% & master) & k) & v) & entries)".
        iModIntro; iExists Ews, ki; iFrame "k".
        iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "k".
        iMod (snap_master_update1(ORD := zero_order) _ _ _ (if eq_dec ki 0 then k else ki) with "[$snap $master]") as "[snap master]".
        { if_tac; auto. }
        assert (0 <= i1 mod size < Zlength T) by lia.
        assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size by lia; apply hash_range).
        assert (0 <= i < Zlength (rebase T (hash k))) by (rewrite Zlength_rebase; auto; lia).
        assert (fst (Znth i (rebase T (hash k))) = ki).
        { rewrite -> Znth_rebase by (auto; lia).
          replace (Zlength T) with size by lia; replace ((i + hash k) mod size) with (i1 mod size); rewrite HHi; auto. }
        iAssert (!!((ki = k \/ ki = 0) -> lookup T k = Some (i1 mod size))) as %Hindex.
        { rewrite prop_impl_imp. iIntros "%".
          iApply (entries_lookup with "[$entries $snaps]"); auto.
          rewrite HHi; now simpl. }
        iFrame "snap snaps".
        iDestruct "Hclose" as "[Hclose _]"; iApply "Hclose".
        unfold hashtable; iExists (upd_Znth (i1 mod size) T (if eq_dec ki 0 then k else ki, vi)); iFrame "excl".
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z) (i := i1 mod size)
                                          (l := upto (Z.to_nat size))
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        rewrite -> Hpi, upd_Znth_same by lia; iFrame.
        iSplitL "".
        { iSplit; auto; iPureIntro.
          split; [rewrite upd_Znth_Zlength; auto|].
          if_tac; [subst | erewrite upd_Znth_triv; auto].
          split; [apply wf_table_upd; auto|].
          intros.
          etransitivity; eauto; split; intros (Hin & ?); split; auto.
            - eapply In_upd_Znth_old; auto; try lia.
              rewrite HHi; intro X; inv X; tauto.
            - apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
        iSplitL "".
        { iSplit; auto; iPureIntro.
          if_tac; tauto. }
        erewrite iter_sepcon_func_strong; first iFrame.
        intros ??%In_remove_upto; simpl.
        rewrite !upd_Znth_diff'; auto; try lia.
        apply Z_mod_lt; auto. }
      Intros k1.
      focus_SEP 2.
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
        forward_if (PROP () ((LOCALx Q) (SEPx (ghost_snap k (Znth (i1 mod size) lg) :: R)))) end.
      * if_tac; [discriminate|].
        forward.
        forward_if (k1 = k).
        { forward.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) keys k1).
          rewrite -> Zmod_mod, Z2Nat.inj_add, upto_app, iter_sepcon_app by lia.
          change (upto (Z.to_nat 1)) with [0]; simpl iter_sepcon.
          rewrite -> Z2Nat.id, Z.add_0_r by lia.
          replace ((i + hash k) mod size) with (i1 mod size); rewrite -> upd_Znth_same by lia; entailer!.
          { assert (Int.min_signed <= i1 mod size < Int.max_signed); auto.
            split; etransitivity; try apply Z_mod_lt; auto; try computable.
            setoid_rewrite (proj2_sig has_size); computable. }
          erewrite iter_sepcon_func_strong; [apply derives_refl|]; intros; simpl.
          rewrite upd_Znth_diff'; auto; try lia.
          replace (i1 mod size) with ((i + hash k) mod size); intro X; apply Zmod_plus_inv in X; auto.
          rewrite -> In_upto, Z2Nat.id in * by lia.
          rewrite !Zmod_small in X; lia. }
        { forward.
          entailer!. }
        entailer!.
      * forward.
        if_tac; [|contradiction].
        subst; entailer!.
      * entailer!.
        apply derives_refl.
    + forward.
      subst; entailer!.
    + forward. forward; setoid_rewrite Hpi.
      { entailer!. }
      forward_call atomic_CAS_int (pvi, Tsh, v_ref, 0, v, top, empty, fun v => Q (if eq_dec v 0 then true else false)).
      { subst Frame; instantiate (1 := [data_at sh (tarray tentry size) entries (gv _m_entries)]); simpl; cancel.
        iIntros "((snap & >AS) & snaps)".
        iDestruct "AS" as (HT) "[hashtable Hclose]".
        iDestruct "hashtable" as (T) "((% & excl) & entries)".
        match goal with H : _ /\ _ /\ _ |- _ => destruct H as (? & ? & ?) end.
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z) (i := i1 mod size)
                                          (f := hashtable_entry _ _ _)
          by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite -> Z2Nat.id; lia).
        unfold hashtable_entry at 1.
        rewrite Hpi.
        destruct (Znth (i1 mod size) T) as (ki, vi) eqn: HHi.
        iDestruct "entries" as "((((% & master) & k) & v) & entries)".
        iModIntro; iExists Ews, vi; iFrame "v".
        iSplitL ""; [iSplit; auto; iPureIntro; split; auto; tauto|].
        iIntros "v".
        iMod (exclusive_update _ (if eq_dec vi 0 then map_upd HT k v else HT) with "excl") as "excl".
        iAssert (!! (ki = k)) as %Hk.
        { iCombine "snap master" as "master"; rewrite -> snap_master_join1.
          iDestruct "master" as "[[% | %] ?]"; auto; contradiction. }
        subst ki.
        iAssert (!! (lookup T k = Some (i1 mod size))) as %Hindex.
        { iApply (entries_lookup with "[$entries $snaps]"); auto.
          rewrite HHi; auto. }
        iDestruct "snap" as "_".
        iPoseProof (snaps_dealloc with "snaps") as "_".
        iDestruct "Hclose" as "[_ Hclose]"; iApply "Hclose"; simpl.
        iSplit; last done.
        unfold hashtable.
        rewrite exp_andp2.
        iExists ((if eq_dec vi 0 then upd_Znth (i1 mod size) T (k, v) else T)).
        rewrite -> @iter_sepcon_Znth with (d := Inhabitant_Z) (i := i1 mod size)
                                          (l := upto (Z.to_nat size))
            by (try apply Cveric; rewrite -> Zlength_upto, Z2Nat.id; lia).
        rewrite -> Znth_upto by (rewrite Z2Nat.id; lia).
        unfold hashtable_entry.
        if_tac; subst.
        * rewrite -> upd_Znth_same by lia.
          assert (0 <= hash k < Zlength T) by (replace (Zlength T) with size by lia; apply hash_range).
          rewrite Hpi; iFrame.
          assert (forall v', In (k, v') T -> v' = 0) as Hv'.
          { intros ? Hin.
            eapply In_Znth in Hin; destruct Hin as (j & ? & Hjth).
            match goal with H : wf_table T |- _ => exploit (H k j); rewrite ?Hjth; auto end.
            rewrite Hindex; intro X; inv X.
            rewrite HHi in Hjth; inv Hjth; auto. }
          iSplit.
          { iPureIntro; split; auto.
            destruct (HT k) eqn: Hk; auto.
            match goal with H : forall k v, _ <-> _ |- _ => rewrite -> H in Hk end.
            destruct Hk as (Hin & ?); specialize (Hv' _ Hin); contradiction. }
          iSplitL "".
          { iSplit; auto; iPureIntro.
            split; [rewrite upd_Znth_Zlength; lia|].
            split; [apply wf_table_upd_same; rewrite ?HHi; auto|].
            intros; unfold map_upd; if_tac.
            * split; [intro X; inv X; split; auto; apply upd_Znth_In; lia|].
              subst; intros (Hin & ?).
              apply In_upd_Znth in Hin; destruct Hin as [Hin | Hin]; [inv Hin; auto|].
              specialize (Hv' _ Hin); contradiction.
            * etransitivity; eauto; split; intros (Hin & ?); split; auto.
              -- eapply In_upd_Znth_old; auto; try lia.
                 rewrite HHi; intro X; inv X; contradiction.
              -- apply In_upd_Znth in Hin; destruct Hin as [X|]; [inv X; tauto | auto]. }
          iSplitL ""; [iSplit; auto; iPureIntro; auto; tauto|].
          erewrite iter_sepcon_func_strong; [auto|].
          intros ??%In_remove_upto; simpl.
          rewrite -> !upd_Znth_diff' by lia; auto.
          apply Z_mod_lt; auto.
        * rewrite Hpi HHi; iFrame.
          iSplit; auto; iPureIntro; split; [|discriminate].
          assert (HT k = Some vi) as X; [|rewrite X; discriminate].
          match goal with H : forall k v, _ <-> _ |- _ => rewrite H end.
          split; auto; rewrite <- HHi; apply Znth_In; lia. }
      unfold POSTCONDITION, abbreviate; simpl map.
      Intros v'; forward.
      Exists (if eq_dec v' 0 then true else false); entailer!.
      if_tac; auto.
  - Intros i i1 keys.
    forward.
    { entailer!.
      rewrite -> (Int.signed_repr 1) by computable; lia. }
    Exists ((i + 1) mod size) (i1 + 1) keys; entailer!.
    + split; [|split].
      * rewrite <- Zplus_mod_idemp_l.
        replace (i1 mod _) with ((i + hash k) mod size); simpl.
        rewrite -> !Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto.
      * apply Z.mod_bound_pos; lia.
      * erewrite <- sublist_sublist00; [apply Forall_sublist; eauto|].
        split; [apply Z.mod_bound_pos | apply Zmod_le]; lia.
    + erewrite -> upto_sub, iter_sepcon_app; first by iIntros "[$ ?]"; iApply snaps_dealloc.
      apply Z2Nat.inj_le, Zmod_le; try lia.
      apply Z.mod_bound_pos; lia.
Qed.

Opaque Znth.

Lemma body_init_table : semax_body Vprog Gprog f_init_table init_table_spec.
Proof.
  start_function.
  ghost_alloc (fun g => excl g (@empty_map Z Z)).
  Intro g.
  forward_for_simple_bound size (EX i : Z, EX entries : list (val * val),
    PROP (Forall (fun '(pk, pv) => isptr pk /\ isptr pv) entries; Zlength entries = i)
    LOCAL (gvars gv)
    SEP (excl g (@empty_map Z Z); mem_mgr gv; @data_at CompSpecs Ews (tarray tentry size) (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i))) (gv _m_entries);
         EX lg : list gname, !!(Zlength lg = i) && iter_sepcon (fun j =>
           hashtable_entry (repeat (0, 0) (Z.to_nat size)) lg entries j) (upto (Z.to_nat i)))).
  { setoid_rewrite (proj2_sig has_size); reflexivity. }
  { pose proof size_pos; lia. }
  { setoid_rewrite (proj2_sig has_size); computable. }
  - Exists (@nil (val * val)) (@nil gname); entailer!.
    rewrite data_at__eq; unfold default_val; simpl.
    apply derives_refl.
  - Intros lg.
    ghost_alloc (ghost_master1 0).
    Intros gk.
    forward_call (vint 0).
    Intros pk.
    rewrite iter_sepcon_map; Intros.
    pose proof size_signed as Hsigned.
    forward.
    forward_call (vint 0).
    Intros pv.
    repeat forward.
    assert (0 <= i < Zlength (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i)))).
    { rewrite -> Zlength_app, coqlib4.Zlength_repeat, Z2Nat.id; lia. }
    rewrite -> upd_Znth_twice, upd_Znth_same by auto.
    go_lower; Exists (entries ++ [(pk, pv)]) (lg ++ [gk]).
    rewrite -> !Z2Nat.inj_add, !upto_app, !iter_sepcon_app, !Z2Nat.id by lia.
    change (upto (Z.to_nat 1)) with [0]; unfold hashtable_entry at 3; simpl.
    rewrite -> Z.add_0_r, !app_Znth2 by lia.
    replace (Zlength entries) with i; replace (Zlength lg) with i; rewrite -> Zminus_diag, !Znth_0_cons.
    rewrite -> Znth_repeat', !Zlength_app, !Zlength_cons, !Zlength_nil by (rewrite Z2Nat.id; lia).
    entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    rewrite -> upd_init, <- app_assoc by (auto; lia); cancel.
    rewrite <- iter_sepcon_map.
    erewrite iter_sepcon_func_strong; [apply derives_refl|].
    intros ??%In_upto; simpl.
    rewrite <- Zlength_correct in *.
    unfold hashtable_entry; rewrite -> !app_Znth1 by lia; auto.
  - Intros entries lg.
    rewrite -> Zminus_diag, app_nil_r.
    unfold hashtable; Exists entries g lg; entailer!.
    Exists (repeat (0, 0) (Z.to_nat size)); entailer!.
    split; [rewrite -> coqlib4.Zlength_repeat, Z2Nat.id; auto; pose proof size_pos; lia|].
    split.
    + intros ??? Hj.
      setoid_rewrite Znth_repeat in Hj; simpl in Hj; subst; contradiction.
    + split; [discriminate|].
      intros (Hin & ?); apply repeat_spec in Hin; inv Hin; contradiction.
    + apply derives_refl.
Qed.

Lemma apply_hist_app : forall h1 h2 H, apply_hist H (h1 ++ h2) =
  match apply_hist H h1 with Some H' => apply_hist H' h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a; rewrite IHh1; auto.
  - destruct (H k); if_tac; auto.
  - destruct (H k); simple_if_tac; auto.
Qed.

#[local] Instance hashtable_entry_timeless : forall T lg entries i, Timeless (hashtable_entry T lg entries i).
Proof.
  intros; unfold hashtable_entry.
  destruct (Znth i entries), (Znth i T).
  apply (@bi.sep_timeless), _.
  apply (@bi.sep_timeless), atomic_int_timeless.
  apply (@bi.and_timeless); [apply (@bi.pure_timeless) | apply own_timeless].
Qed.

#[export] Instance hashtable_timeless : forall H g lg entries, Timeless (hashtable H g lg entries).
Proof.
  intros; unfold hashtable.
  apply (@bi.exist_timeless); intro.
  apply (@bi.sep_timeless); [apply (@bi.and_timeless); [apply (@bi.pure_timeless) | apply own_timeless]|].
  forget (upto (Z.to_nat size)) as l; clear; induction l; simpl.
  * apply emp_timeless.
  * apply (@bi.sep_timeless); auto.
    apply hashtable_entry_timeless.
Qed.

#[local] Instance hashtable_inv_timeless : forall gh g lg entries, Timeless (hashtable_inv gh g lg entries).
Proof.
  intros; unfold hashtable_inv.
  apply (@bi.exist_timeless); intro.
  apply (@bi.sep_timeless); [apply hashtable_timeless|].
  apply (@bi.exist_timeless); intro.
  apply (@bi.and_timeless); [apply (@bi.pure_timeless)|].
  unfold ghost_ref.
  apply (@bi.exist_timeless); intro.
  apply (@bi.and_timeless); [apply (@bi.pure_timeless) | apply own_timeless].
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (data_at_isptr Ews); Intros.
  forward.
  forward.
  { entailer!.
    rewrite upd_Znth_same; auto. }
  forward.
  { entailer!.
    rewrite upd_Znth_same; auto. }
  rewrite -> !upd_Znth_same by auto.
  forward.
  forward_call (tint, tid, gv).
  { rewrite if_false.
    cancel.
    { destruct tid; auto; discriminate. } }
  forward_for_simple_bound 3 (EX j : Z, EX ls : list bool, EX h : _,
    PROP (Zlength ls = j; add_events empty_map (map (fun j => HAdd (j + 1) 1 (Znth j ls)) (upto (Z.to_nat j))) h)
    LOCAL (temp _total (vint (Zlength (List.filter id ls))); temp _res res; temp _l (ptr_of lockt); temp _t (vint t);
           temp _arg tid; gvars gv)
    SEP (mem_mgr gv; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         inv i (hashtable_inv gh g lg entries);
         ghost_hist gsh h gh;
         data_at sh (tarray (tptr t_lock) 3) (upd_Znth t (repeat Vundef 3) (ptr_of lockt)) (gv _thread_locks);
         data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) (gv _results);
         data_at_ Ews tint res;
         lock_inv tsh lockt (f_lock_pred tsh sh gsh entries gh (gv _m_entries) t
                                         (gv _thread_locks) lockt (gv _results) res gv))).
  - Exists (@nil bool) (@empty_map nat hashtable_hist_el); entailer!.
  - rewrite invariant_dup; Intros.
    gather_SEP (inv _ _) (ghost_hist _ _ _).
    forward_call (i0 + 1, 1, gv, sh, entries, g, lg,
      fun b => EX h' : _, !!(add_events h [HAdd (i0 + 1) 1 b] h') && ghost_hist gsh h' gh).
    { rewrite -> 5sepcon_assoc; apply sepcon_derives; [|cancel].
      iIntros "[#inv hist]"; unfold atomic_shift; iAuIntro.
      rewrite /atomic_acc /=.
      iInv "inv" as ">I" "Hclose".
      unfold hashtable_inv.
      iDestruct "I" as (HT) "[hashtable I]"; iDestruct "I" as (hr) "[%Hhr ref]".
      iExists HT; iFrame "hashtable".
      iApply fupd_mask_intro; [set_solver|].
      iIntros "Hclose'"; iSplit.
      + iIntros "hashtable".
        iMod "Hclose'"; iMod ("Hclose" with "[hashtable ref]"); auto.
        iNext; iExists HT; iFrame.
        iExists hr; iFrame; auto.
      + iIntros (b) "[[%Hret hashtable] _]".
        iPoseProof (hist_ref_incl with "[$hist $ref]") as "%"; [auto|].
        iMod (hist_add' _ _ _ (HAdd (i0 + 1) 1 b) with "[$hist $ref]") as "[hist ref]"; [auto|].
        iMod "Hclose'"; iMod ("Hclose" with "[hashtable ref]").
        * iNext; iExists (if b then map_upd HT (i0 + 1) 1 else HT); iFrame.
          iExists (hr ++ [HAdd (i0 + 1) 1 b]); iSplit; auto.
          iPureIntro; rewrite apply_hist_app Hhr; simpl.
          destruct (HT (i0 + 1)), b; try congruence.
          -- destruct Hret as [_ X]; specialize (X eq_refl); discriminate.
          -- destruct Hret as [X _]; specialize (X eq_refl); discriminate.
        * iModIntro; iExists (map_upd h (length hr) (HAdd (i0 + 1) 1 b)); iFrame.
          iSplit; auto; iPureIntro.
          apply (add_events_snoc _ nil); [constructor|].
          apply hist_incl_lt; auto. }
    { repeat (split; auto); try rep_lia. eapply List.Forall_impl, H1. intros (?, ?); auto. }
    Intros b h'.
    forward_if (temp _total (vint (Zlength (List.filter id (ls ++ [b]))))).
    + pose proof (Zlength_filter id ls).
      forward.
      entailer!.
      rewrite List.filter_app; simpl.
      rewrite -> Zlength_app, Zlength_cons, Zlength_nil; auto.
    + forward.
      entailer!.
      rewrite List.filter_app; simpl.
      rewrite -> Zlength_app, Zlength_nil, Z.add_0_r; auto.
    + Exists (ls ++ [b]) h'; rewrite -> List.filter_app, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; entailer!.
      rewrite -> Z2Nat.inj_add, upto_app, map_app, Z2Nat.id by lia; change (upto (Z.to_nat 1)) with [0]; simpl.
      rewrite -> Z.add_0_r, app_Znth2, Zminus_diag, Znth_0_cons by lia.
      eapply add_events_trans; eauto.
      erewrite map_ext_in; eauto.
      intros j Hj; rewrite app_Znth1; auto.
      rewrite -> In_upto, Z2Nat.id in Hj; lia.
  - Intros ls h.
    simpl; forward.
    forward_call release_self (tsh, lockt, f_lock_inv sh gsh entries gh (gv _m_entries) t
      (gv _thread_locks) (ptr_of lockt) (gv _results) res gv).
    { assert_PROP (Zlength entries = Zlength lg).
      { pose proof size_pos; entailer!.
        rewrite H2; auto. }
      unfold f_lock_pred, f_lock_inv; cancel.
      Exists (Znth 0 ls) (Znth 1 ls) (Znth 2 ls) h; entailer!.
      rewrite -> (list_Znth_eq ls) at 1.
      replace (length ls) with (Z.to_nat 3) by (symmetry; rewrite <- Zlength_length by computable; auto).
      cancel. }
    forward.
    apply inv_affine.
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

#[global] Instance Inhabitant_hist_el : Inhabitant hashtable_hist_el := HGet 0 0.

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
    rewrite -> Znth_pos_cons in Hin2 by lia.
    destruct (H0 k); [discriminate|].
    eapply add_fails in HH; [|rewrite <- Hin2; apply Znth_In; lia|]; [discriminate|].
    unfold map_upd; rewrite eq_dec_refl; discriminate.
  - rewrite Znth_0_cons in Hin2; subst.
    rewrite -> Znth_pos_cons in Hin1 by lia.
    destruct (H0 k); [discriminate|].
    eapply add_fails in HH; [|rewrite <- Hin1; apply Znth_In; lia|]; [discriminate|].
    unfold map_upd; rewrite eq_dec_refl; discriminate.
  - rewrite -> Znth_pos_cons in Hin1, Hin2 by lia.
    assert (i2 - 1 = i1 - 1); [|lia].
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

Lemma filter_find_count : forall {A} {d : Inhabitant A} (f : A -> bool) l li (Hunique : List.NoDup li)
  (Hli : forall i, In i li -> f (Znth i l) = true) (Hrest : forall i, ~In i li -> f (Znth i l) = false),
  Zlength (List.filter f l) = Zlength li.
Proof.
  induction l; simpl; intros.
  - exploit (list_pigeonhole li (Zlength li + 1)); [lia|].
    intros (i' & ? & ?).
    destruct li; auto.
    exploit (Hli z); simpl; auto.
    exploit Hrest; eauto.
    rewrite !Znth_nil; intros ->; discriminate.
  - assert (f d = false) as Hd.
    { exploit (list_pigeonhole (upto (Z.to_nat (Zlength (a :: l))) ++ li)
       (Zlength (upto (Z.to_nat (Zlength (a :: l))) ++ li) + 1)); [lia|].
      intros (j' & ? & Hout); exploit (Hrest j').
      { intro X; contradiction Hout; rewrite in_app; auto. }
      rewrite Znth_overflow; auto.
      { destruct (zlt j' (Zlength (a :: l))); auto.
        contradiction Hout; rewrite in_app; left.
        rewrite -> In_upto, Z2Nat.id; lia. } }
    destruct (in_dec Z.eq_dec 0 li).
    + exploit Hli; eauto.
      rewrite Znth_0_cons. intros ->.
      rewrite Zlength_cons.
      exploit in_split; eauto; intros (li1 & li2 & ?); subst.
      apply NoDup_remove in Hunique; destruct Hunique.
      rewrite Zlength_app Zlength_cons.
      erewrite (IHl (map (fun i => i - 1) (li1 ++ li2))), Zlength_map, Zlength_app; auto; try lia.
      * apply FinFun.Injective_map_NoDup; auto.
        intros ??; lia.
      * intros ? Hj; rewrite -> in_map_iff in Hj; destruct Hj as (j & ? & Hj); subst.
        exploit (Hli j).
        { rewrite in_insert_iff; auto. }
        destruct (eq_dec j 0); [subst; contradiction|].
        destruct (zlt j 0).
        { rewrite -> Znth_underflow, Hd by auto; discriminate. }
        rewrite -> Znth_pos_cons by lia; auto.
      * intros j Hj.
        destruct (zlt j 0); [rewrite Znth_underflow; auto|].
        specialize (Hrest (j + 1)); specialize (Hli (j + 1));
          rewrite -> Znth_pos_cons, Z.add_simpl_r in Hrest, Hli by lia.
        destruct (in_dec Z.eq_dec (j + 1) (li1 ++ 0 :: li2)); auto.
        rewrite -> in_insert_iff in i0; destruct i0; [lia|].
        contradiction Hj; rewrite in_map_iff; do 2 eexists; eauto; lia.
    + exploit Hrest; eauto.
      rewrite Znth_0_cons; intros ->.
      erewrite (IHl (map (fun i => i - 1) li)), Zlength_map; try lia.
      * apply FinFun.Injective_map_NoDup; auto.
        intros ??; lia.
      * intros ? Hj; rewrite -> in_map_iff in Hj; destruct Hj as (j & ? & Hj); subst.
        specialize (Hli _ Hj).
        destruct (eq_dec j 0); [subst; contradiction|].
        destruct (zlt j 0).
        { rewrite -> Znth_underflow, Hd in Hli by auto; discriminate. }
        rewrite -> Znth_pos_cons in Hli by lia; auto.
      * intros j Hj.
        destruct (zlt j 0); [rewrite Znth_underflow; auto|].
        specialize (Hrest (j + 1)); specialize (Hli (j + 1));
          rewrite -> Znth_pos_cons, Z.add_simpl_r in Hrest, Hli by lia.
        destruct (in_dec Z.eq_dec (j + 1) li); auto.
        contradiction Hj; rewrite in_map_iff; do 2 eexists; eauto; lia.
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
    rewrite -> if_true in H0 by auto; discriminate.
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
    rewrite -> list_Znth_eq at 1.
    rewrite -> Zlength_correct in *.
    replace (length h) with 3%nat by (apply Nat2Z.inj; auto); reflexivity.
    { apply equal_f with t2 in H0; unfold map_upd in H0.
      rewrite eq_dec_refl in H0; discriminate. }
Qed.

Lemma add_three : forall lr HT l (Hlr : Zlength lr = 3)
  (Hhists : Forall (fun '(h, ls) => add_events empty_map [HAdd 1 1 (Znth 0 ls); HAdd 2 1 (Znth 1 ls);
     HAdd 3 1 (Znth 2 ls)] h) lr) (Hlens : Forall (fun '(_, ls) => Zlength ls = 3) lr)
  (Hl : hist_list (maps_add (map fst lr)) l) (HHT : apply_hist empty_map l = Some HT)
  (Hdisj : all_disjoint (map fst lr)),
  Zlength (List.filter id (concat (map snd lr))) = 3.
Proof.
  intros.
  assert (Permutation.Permutation (List.filter id (concat (map snd lr)))
    (List.filter id (map (fun e => match e with HAdd _ _ b => b | _ => false end) l))) as Hperm.
  { apply Permutation_filter, hists_eq; auto.
    apply hist_list_weak; auto. }
  rewrite (Permutation_Zlength _ _ Hperm).
  assert (forall k v, ~ In (HSet k v) l).
  { repeat intro.
    apply In_nth_error in H; destruct H as (? & H).
    apply Hl in H.
    apply in_maps_add in H as (m & Hin & Hm).
    apply in_map_iff in Hin as ((?, h) & ? & Hin); simpl in *; subst.
    rewrite -> List.Forall_forall in Hhists; specialize (Hhists _ Hin); simpl in Hhists.
    eapply add_events_dom in Hm; eauto; simpl in Hm.
    decompose [or] Hm; try discriminate; contradiction. }
  assert (forall i, 0 <= i < 3 -> In (HAdd (i + 1) 1 (Znth i (snd (Znth 0 lr)))) l) as Hins.
  { intros.
    assert (exists t, maps_add (map fst lr) t = Some (HAdd (i + 1) 1 (Znth i (snd (Znth 0 lr)))))
      as (t & Hin).
    { exploit (Znth_In 0 lr); [lia | intro Hin].
      rewrite -> List.Forall_forall in Hhists; specialize (Hhists _ Hin).
      destruct (Znth 0 lr) as (h, ?); simpl in *.
      apply add_events_in with (e := HAdd (i + 1) 1 (Znth i l0)) in Hhists as (t & _ & Hh).
      exists t; eapply maps_add_in; eauto.
      { apply all_disjoint_compatible; auto. }
      rewrite in_map_iff; eexists (_, _); simpl; eauto.
      { destruct (eq_dec i 0); [subst; simpl; auto|].
        destruct (eq_dec i 1); [subst; simpl; auto|].
        destruct (eq_dec i 2); [subst; simpl; auto | lia]. } }
    apply Hl in Hin; eapply nth_error_in; eauto. }
  exploit (one_add_succeeds 1 1 (Znth 0 (snd (Znth 0 lr))) l); eauto.
  { eapply (Hins 0); auto; lia. }
  exploit (one_add_succeeds 2 1 (Znth 1 (snd (Znth 0 lr))) l); eauto.
  { eapply (Hins 1); auto; lia. }
  exploit (one_add_succeeds 3 1 (Znth 2 (snd (Znth 0 lr))) l); eauto.
  { eapply (Hins 2); auto; lia. }
  intros (v3 & Hin3) (v2 & Hin2) (v1 & Hin1).
  apply In_Znth in Hin1; destruct Hin1 as (t1 & ? & Ht1).
  apply In_Znth in Hin2; destruct Hin2 as (t2 & ? & Ht2).
  apply In_Znth in Hin3; destruct Hin3 as (t3 & ? & Ht3).
  rewrite -> filter_find_count with (li := [t1; t2; t3]); auto; simpl.
  - repeat constructor; auto; simpl.
    + intros [|[|]]; try contradiction; subst.
      * rewrite Ht1 in Ht2; inv Ht2.
      * rewrite Ht1 in Ht3; inv Ht3.
    + intros [|]; try contradiction; subst.
      rewrite Ht2 in Ht3; inv Ht3.
  - intros ? [|[|[|]]]; try contradiction; subst; rewrite -> Znth_map by lia.
    + rewrite Ht1; auto.
    + rewrite Ht2; auto.
    + rewrite Ht3; auto.
  - intros i Hi.
    destruct (zlt i 0); [rewrite Znth_underflow; auto|].
    destruct (zlt i (Zlength l)); [|rewrite -> Znth_overflow by (rewrite Zlength_map; lia); auto].
    rewrite -> Znth_map by lia.
    destruct (Znth i l) eqn: Hith; auto.
    destruct r; auto.
    contradiction Hi.
    assert (k = 1 \/ k = 2 \/ k = 3) as Hk.
    { rewrite <- nth_Znth in Hith by lia.
      exploit sublist.nth_error_nth; [apply Nat2Z.inj_lt; rewrite -> Z2Nat.id, <- Zlength_correct; eauto; lia|].
      rewrite -> Hith; intro Hin.
      apply Hl in Hin.
      apply in_maps_add in Hin as (? & Hin & Hm); subst.
      rewrite -> in_map_iff in Hin; destruct Hin as ((h, ?) & ? & Hin); subst; simpl in *.
      rewrite -> List.Forall_forall in Hhists; specialize (Hhists _ Hin); simpl in Hhists.
      eapply add_events_dom in Hhists; eauto; simpl in Hhists.
      destruct Hhists as [X | [X | [X | [X | X]]]]; inv X; auto. }
    destruct Hk as [|[|]]; [left | right; left | right; right; left];
      match goal with |-?P => assert (P /\ Znth (k - 1) [v1; v2; v3] = v); [|tauto] end;
      subst; eapply only_one_add_succeeds; eauto.
Qed.

#[global] Instance lock_handle_inhabited : Inhabitant lock_handle := (Vundef, nroot, O).

Axiom mem_mgr_dup : forall gv, mem_mgr gv = mem_mgr gv * mem_mgr gv.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  replace 16384 with size by (setoid_rewrite (proj2_sig has_size); auto).
  sep_apply (create_mem_mgr gv).
  forward.
  forward_call gv.
  Intros x; destruct x as ((entries, g), lg).
  ghost_alloc (ghost_hist_ref(hist_el := hashtable_hist_el) Tsh empty_map empty_map);
    try solve [split; auto with share; apply @self_completable].
  Intro gh.
  rewrite <- hist_ref_join_nil by (apply Share.nontrivial); Intros.
  rewrite <- (emp_sepcon (ghost_hist _ _ _)); Intros.
  gather_SEP (hashtable _ _ _ _) (ghost_ref _ _); viewshift_SEP 0 (inv (nroot .@ "i") (hashtable_inv gh g lg entries)).
  { go_lower.
    apply make_inv.
    unfold hashtable_inv.
    Exists (@empty_map Z Z) (@nil hashtable_hist_el); entailer!.
    apply derives_refl. }
  destruct (split_shares 3 Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  destruct (split_shares 3 Tsh) as (sh0' & shs' & ? & ? & ? & Hshs'); auto.
  destruct (split_readable_share Ews) as (sh1 & sh2 & ? & ? & ?); auto.
  rewrite <- seq_assoc.
  set (f_lock j l r := f_lock_pred gsh2 (Znth j shs) (Znth j shs') entries gh (gv _m_entries)
                                         j (gv _thread_locks) l (gv _results) r gv).
  set (Nt := nroot .@ "t").
  forward_for_simple_bound 3 (EX i : Z, EX res : list val, EX locks : list lock_handle,
    PROP (Zlength res = i; Zlength locks = i)
    LOCAL (temp _total (vint 0); gvars gv)
    SEP (mem_mgr gv; @data_at CompSpecs Ews (tarray tentry size) entries (gv _m_entries);
         inv (nroot .@ "i") (hashtable_inv gh g lg entries);
         ghost_hist(hist_el := hashtable_hist_el) Tsh empty_map gh;
         (*iter_sepcon (fun x => malloc_token Ews tint (fst x) * malloc_token Ews tint (snd x))
           entries;*)
         data_at Ews (tarray (tptr tint) 3) (res ++ repeat Vundef (Z.to_nat (3 - i))) (gv _results) *
         iter_sepcon (data_at_ Ews tint) res * iter_sepcon (malloc_token Ews tint) res *
         data_at Ews (tarray (tptr t_lock) 3)
           (map ptr_of locks ++ repeat Vundef (Z.to_nat (3 - i))) (gv _thread_locks) *
         (*iter_sepcon (malloc_token Ews t_lock) (map ptr_of locks) **)
         iter_sepcon (fun j => lock_inv Tsh (Znth j locks)
           (f_lock j (Znth j locks) (Znth j res))) (upto (Z.to_nat i)); has_ext tt)).
  { Exists (@nil val) (@nil lock_handle); entailer!. }
  { (* first loop *)
    forward_call (tint, gv).
    Intros r.
    forward.
    forward_call makelock_inv (gv, Nt, fun l => f_lock i l r).
    Intros lp.
    match goal with |-context[|={⊤}=> ?P] => viewshift_SEP 1 P by entailer! end.
    Intros l; subst.
    forward.
    Exists (res ++ [r]) (locks ++ [l]); rewrite -> !Zlength_app, !Zlength_cons, !Zlength_nil; entailer!.
    rewrite data_at__isptr; Intros.
    rewrite -> Z2Nat.inj_add, upto_app, !iter_sepcon_app by lia.
    simpl. change (upto 1) with [0]; simpl.
    rewrite -> Z2Nat.id, Z.add_0_r by lia.
    replace (Zlength res + 1) with (Zlength (res ++ [r]))
      by (rewrite -> Zlength_app, Zlength_cons, Zlength_nil; auto).
    rewrite <- upd_complete_gen by lia.
    replace (Zlength (res ++ [r])) with (Zlength (locks ++ [l]))
      by (rewrite -> !Zlength_app, !Zlength_cons, !Zlength_nil; auto; lia).
    rewrite <- upd_complete_gen' by (rewrite H12; lia).
    rewrite -> !app_Znth2 by (rewrite ?H12; lia).
    rewrite H12 Zminus_diag !Znth_0_cons.
    destruct r; try contradiction.
    destruct l; try contradiction.
    cancel.
    rewrite Zlength_correct Nat2Z.id.
    erewrite iter_sepcon_func_strong; [apply derives_refl|].
    intros ??%In_upto; simpl.
    rewrite <- Zlength_correct in *.
    rewrite -> 2app_Znth1 by (rewrite ?H12; lia); auto. }
  Intros res locks.
  rewrite !app_nil_r.
  assert_PROP (Zlength entries = size) by (pose proof size_pos; entailer!).
  rewrite <- seq_assoc.
  assert (forall i, 0 <= i < 3 -> Znth i (map ptr_of locks) = ptr_of (Znth i locks)) as Hi.
  { intros; apply Znth_map; lia. }
  forward_for_simple_bound 3 (EX i : Z, EX sh : share, EX sh' : share,
    PROP (sepalg_list.list_join sh0 (sublist i 3 shs) sh; sepalg_list.list_join sh0' (sublist i 3 shs') sh')
    LOCAL (temp _total (vint 0); gvars gv)
    SEP (mem_mgr gv; @data_at CompSpecs sh (tarray tentry size) entries (gv _m_entries);
         inv (nroot .@ "i") (hashtable_inv gh g lg entries);
         ghost_hist(hist_el := hashtable_hist_el) sh' empty_map gh;
         (*iter_sepcon (fun x => malloc_token Ews tint (fst x) * malloc_token Ews tint (snd x)) entries;*)
         data_at sh (tarray (tptr tint) 3) res (gv _results);
         iter_sepcon (data_at_ Ews tint) (sublist i 3 res); iter_sepcon (malloc_token Ews tint) res;
         data_at sh (tarray (tptr t_lock) 3) (map ptr_of locks) (gv _thread_locks);
         (*iter_sepcon (malloc_token Ews (Tstruct _lock_t noattr)) (map ptr_of locks);*)
         iter_sepcon (fun j => lock_inv (if zlt j i then gsh1 else Tsh) (Znth j locks)
           (f_lock j (Znth j locks) (Znth j res))) (upto 3); has_ext tt)).
  { rewrite -> !sublist_same by auto; unfold f_lock; Exists Ews Tsh; entailer!.
    erewrite iter_sepcon_func_strong; [apply derives_refl|].
    intros ??%In_upto.
    simpl; if_tac; auto; lia. }
  { (* second loop *)
    forward_call (tint, gv).
    Intros t.
    forward.
    assert (3 <= Zlength shs) by lia.
    match goal with H : sepalg_list.list_join sh0 _ _ |- _ => rewrite -> sublist_next in H by auto;
      inversion H as [|????? Hj1 Hj2]; subst end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh3 & ? & Hj3).
    assert (3 <= Zlength shs') by lia.
    match goal with H : sepalg_list.list_join sh0' _ _ |- _ => rewrite -> sublist_next in H by auto;
      inversion H as [|????? Hj1' Hj2']; subst end.
    apply sepalg.join_comm in Hj1'; destruct (sepalg_list.list_join_assoc1 Hj1' Hj2') as (sh3' & ? & Hj3').
    rewrite invariant_dup.
    assert_PROP (isptr t) by entailer!.
    rewrite mem_mgr_dup.
    forward_spawn _f t (Znth i shs, Znth i shs', gsh2, entries, nroot .@ "i", gh, g, lg, gv, i,
      Znth i locks, Znth i res).
    { assert (0 <= i < Zlength shs) by lia.
      assert (Znth i shs' <> Share.bot).
      { intro X; contradiction unreadable_bot; rewrite <- X.
        apply Forall_Znth; auto; lia. }
      rewrite -> (iter_sepcon_Znth _ (upto 3) i) by auto.
      rewrite -> Znth_upto by (auto; simpl; lia).
      rewrite -> if_false by lia.
      entailer!.
      { apply Forall_Znth; auto. }
      rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj3).
      replace empty_map with (@map_add nat hashtable_hist_el empty_map empty_map) by apply map_add_empty.
      pose proof (@empty_map_disjoint nat hashtable_hist_el empty_map) as Hdisj.
      erewrite (add_andp (ghost_hist _ _ _) (!!_)) by (apply prop_right, Hdisj).
      rewrite -> andp_comm, <- (ghost_hist_join _ _ _ _ _ _ Hj3'); auto.
      rewrite <- (lock_inv_share_join gsh1 gsh2) by auto.
      cancel.
      rewrite -> (sepcon_comm _ (data_at (Znth i shs) _ _ (gv _thread_locks))), !sepcon_assoc; apply sepcon_derives.
      { apply stronger_array_ext.
        - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
        - intros j ???; unfold unfold_reptype; simpl.
          destruct (eq_dec j i).
          + subst; rewrite -> Hi, upd_Znth_same; simpl; auto.
          + rewrite -> upd_Znth_diff by auto.
            setoid_rewrite @Znth_repeat with (n := 3%nat); apply stronger_default_val. }
      rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs) _ _ (gv _results))),
        !sepcon_assoc; apply sepcon_derives.
      { apply stronger_array_ext.
        - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
        - intros j ???; unfold unfold_reptype; simpl.
          destruct (eq_dec j i).
          + subst; rewrite -> upd_Znth_same by auto; apply derives_refl.
          + rewrite -> upd_Znth_diff' by auto.
            setoid_rewrite @Znth_repeat with (n := 3%nat); apply stronger_default_val. }
      erewrite sublist_next by (auto; lia); simpl; fast_cancel.
      { intro; subst; contradiction unreadable_bot.
        eapply join_readable1, readable_share_list_join; eauto. } }
    { simpl; auto. }
    go_lowerx.
    Exists sh3 sh3'; entailer!.
    rewrite -> (iter_sepcon_Znth _ (upto 3) i), Znth_upto by auto.
    rewrite -> if_true by lia; iFrame.
    erewrite iter_sepcon_func_strong; [auto|].
    intros ??%In_remove_upto; [simpl | lia].
    if_tac; if_tac; auto; lia. }
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
    LOCAL (let ls := map snd (snd x) in temp _total (vint (Zlength (List.filter id (concat ls)))); gvars gv)
    SEP (mem_mgr gv; @data_at CompSpecs (fst x) (tarray tentry size) entries (gv _m_entries);
         inv (nroot .@ "i") (hashtable_inv gh g lg entries);
         let h := map fst (snd x) in ghost_hist sh' (fold_right map_add empty_map h) gh;
         (*iter_sepcon (fun x => malloc_token Ews tint (fst x) * malloc_token Ews tint (snd x)) entries;*)
         data_at (fst x) (tarray (tptr tint) 3) res (gv _results);
         iter_sepcon (malloc_token Ews tint) (sublist i 3 res);
         data_at (fst x) (tarray (tptr t_lock) 3) (map ptr_of locks) (gv _thread_locks);
         (*iter_sepcon (malloc_token Ews t_lock) (sublist i 3 (map ptr_of locks));*)
         iter_sepcon (fun j => lock_inv gsh1 (Znth j locks)
           (f_lock j (Znth j locks) (Znth j res))) (sublist i 3 (upto 3)); has_ext tt)).
  { rewrite -> !(sublist_same 0 3) by auto.
    Exists (sh, @nil (hist * list bool)) sh'; entailer!.
    erewrite iter_sepcon_func_strong; [apply derives_refl|].
    intros ??%In_upto; simpl in *.
    if_tac; auto; lia. }
  { (* third loop *)
    destruct x as (sh3, lr).
    erewrite sublist_next with (l := upto 3), Znth_upto by (auto; rewrite ?Zlength_upto; simpl; lia); simpl; Intros.
    forward.
    { rewrite -> Hi by auto; entailer!. }
    forward_call acquire_inv_simple (gsh1, Znth i locks, f_lock i (Znth i locks) (Znth i res)).
    unfold f_lock at 2; unfold f_lock_pred.
    rewrite later_sepcon; Intros.
    unfold f_lock, f_lock_pred.
    forward_call freelock_self (gsh1, gsh2, Znth i locks,
      f_lock_inv (Znth i shs) (Znth i shs') entries gh (gv _m_entries) i (gv _thread_locks) (ptr_of (Znth i locks)) (gv _results) (Znth i res) gv).
    unfold f_lock_inv at 1; Intros b1 b2 b3 hi.
    assert (0 <= i < Zlength shs) by lia.
    assert (readable_share (Znth i shs)) by (apply Forall_Znth; auto).
    forward.
    { rewrite -> upd_Znth_same by auto; entailer!. }
    rewrite -> upd_Znth_same by auto.
    forward.
    Local Opaque List.filter.
    erewrite sublist_next with (l := res) by (auto; lia); simpl.
    forward_call (tint, Znth i res, gv).
    { entailer!.
      rewrite if_false.
      cancel.
      { destruct (Znth _ res); auto; discriminate. } }
    assert (3 <= Zlength shs) by lia.
    match goal with H : sepalg_list.list_join sh3 _ _ |- _ => rewrite -> sublist_next in H by auto;
      inversion H as [|??? w1 ? Hj1]; subst end.
    match goal with H : sepalg_list.list_join sh'0 _ _ |- _ => rewrite -> sublist_next in H by (auto; lia);
      inversion H as [|??? w1' ? Hj1']; subst end.
    gather_SEP 0 5; rewrite <- mem_mgr_dup.
    gather_SEP (data_at sh3 _ _ (gv _thread_locks))
               (data_at (Znth (Zlength lr) shs) _ _ (gv _thread_locks)).
    replace_SEP 0 (data_at w1 (tarray (tptr t_lock) 3) (map ptr_of locks) (gv _thread_locks)).
    { go_lower.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join by eauto; apply derives_refl. }
    gather_SEP (data_at sh3 (tarray (tptr tint) 3) _ _)
               (data_at (Znth (Zlength lr) shs) (tarray (tptr tint) 3) _ _).
    replace_SEP 0 (data_at w1 (tarray (tptr tint) 3) res (gv _results)).
    { go_lower.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join by eauto; apply derives_refl. }
    gather_SEP (ghost_hist sh'0 _ _) (ghost_hist _ _ _);
      erewrite ghost_hist_join; eauto.
    gather_SEP (data_at sh3 _ _ _) (data_at (Znth (Zlength lr) shs) _ _ _);
      erewrite data_at_share_join by eauto.
    assert (0 <= Zlength (List.filter id [b1; b2; b3]) <= 3).
    { split; [apply Zlength_nonneg|].
      etransitivity; [apply Zlength_filter|].
      rewrite -> !Zlength_cons, Zlength_nil in *; lia. }
    assert (0 <= Zlength (List.filter id (concat (map snd lr))) <= 3 * Zlength shs).
    { split; [apply Zlength_nonneg|].
      etransitivity; [apply Zlength_filter|].
      etransitivity; [apply Zlength_concat_le with (n := 3)|].
      * rewrite Forall_map.
        eapply List.Forall_impl; [|eauto].
        intros []; simpl; lia.
      * rewrite Zlength_map; lia. }
    forward.
    go_lowerx; Exists (w1, lr ++ [(hi, [b1; b2; b3])]) w1'; entailer!.
    rewrite -> !map_app, concat_app, List.filter_app, !Zlength_app, Zlength_cons, Zlength_nil; simpl;
      repeat (split; auto).
    - eapply join_readable1; eauto.
    - rewrite Forall_app; repeat constructor; auto.
    - rewrite Forall_app; repeat constructor; auto.
    - apply all_disjoint_snoc; split; auto.
      symmetry; auto.
    - eapply join_readable1; eauto.
    - rewrite map_app fold_right_app; simpl.
      rewrite -> map_add_empty, <- fold_right_maps_add; unfold f_lock, f_lock_pred; auto.
    - intro; subst; contradiction unreadable_bot.
    - intro X; contradiction unreadable_bot; rewrite <- X.
      apply Forall_Znth; auto; lia. }
  Intros x sh''; destruct x as (?, lr); simpl fst in *; simpl snd in *.
  repeat match goal with H : sepalg_list.list_join _ (sublist 3 3 _) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  gather_SEP (ghost_hist _ _ _) (inv _ _).
  viewshift_SEP 0 (!!(Zlength (List.filter id (concat (map snd lr))) = 3) && TT).
  { go_lower.
    iIntros "(hist & inv)".
    iInv "inv" as ">inv" "Hclose".
    unfold hashtable_inv.
    iDestruct "inv" as (HT) "[hashtable ref]"; iDestruct "ref" as (hr) "[% ref]".
    iAssert (!!(exists l HT, hist_list (fold_right map_add empty_map (map fst lr)) l /\
        apply_hist empty_map l = Some HT)) as %Hhist.
    { iCombine "hist ref" as "hist"; rewrite -> hist_ref_join by auto with share.
      iDestruct "hist" as (l) "[[% %] hist]".
      iPureIntro.
      match goal with H : hist_sub _ _ _ |- _ => apply hist_sub_Tsh in H; subst end.
      exists hr, HT; split; auto. }
    iMod ("Hclose" with "[hashtable ref]").
    { iNext; iExists HT; iFrame; iExists hr; iSplit; auto. }
    iModIntro; iPureIntro; split; auto.
    destruct Hhist as (? & ? & ? & ?).
    eapply add_three; eauto. }
  Intros. (* We have the pure fact that 3 adds succeeded! *)
  forward.
Qed.
