Require Import VST.progs.ghosts.
Require Import atomics.verif_atomics.
Require Import VST.progs.conclib.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.hashtable1.
Require Import atomics.hashtable.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

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

Instance hf1 : hash_fun := { size := 16384; hash i := (i * 654435761) mod 16384 }.
Proof.
  - computable.
  - intro; apply Z_mod_lt; computable.
Defined.

(* Once set, a key is never reset. *)
Definition k_R (h : list hist_el) (v : Z) := !!(Forall int_op h /\
  forall e, In e h -> value_of e <> vint 0 -> vint v = value_of e) && emp.

Definition v_R (h : list hist_el) (v : Z) := emp.

(* Entries are no longer consecutive. *)
Definition wf_hists h := Forall (fun x => (ordered_hist (fst x) /\ Forall int_op (map snd (fst x))) /\
  (ordered_hist (snd x) /\ Forall int_op (map snd (snd x)))) h.

Definition make_map h :=
  map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs)))) h.

Definition atomic_entry sh pk pv gk gv hk hv :=
  atomic_loc_hist sh pk gk 0 k_R hk * atomic_loc_hist sh pv gv 0 v_R hv.

Definition atomic_entries sh entries ghosts hists := fold_right sepcon emp
  (map (fun x => let '((pk, pv), (gk, gv), (hk, hv)) := x in atomic_entry sh pk pv gk gv hk hv)
    (combine (combine entries ghosts) hists)).

Definition failed_CAS k (a b : hist * hist) := exists r, repable_signed r /\
  (add_events (fst a) [Load (vint r)] (fst b) \/
   add_events (fst a) [Load (vint 0); CAS (vint r) (vint 0) (vint k); Load (vint r)] (fst b)) /\
  r <> 0 /\ r <> k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = vint r).

Definition found_key k (a b : hist) := (add_events a [Load (vint k)] b \/
  add_events a [Load (vint 0); CAS (vint 0) (vint 0) (vint k)] b \/
  add_events a [Load (vint 0); CAS (vint k) (vint 0) (vint k); Load (vint k)] b) /\
  let v := value_of_hist a in v <> vint 0 -> v = vint k.

Definition set_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\ found_key k (fst (Znth i h ([], []))) (fst (Znth i h' ([], []))) /\
  (add_events (snd (Znth i h ([], []))) [Store (vint v)] (snd (Znth i h' ([], [])))) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list (val * val), ghosts : list (val * val),
    h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Zlength ghosts = size;
         Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist),
   PROP (set_item_trace h key value i h')
   LOCAL ()
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h').
(* set_item_trace_map describes the properties on the resulting map. *)

Definition failed_load k (a b : hist * hist) := exists r, repable_signed r /\
  add_events (fst a) [Load (vint r)] (fst b) /\ r <> 0 /\ r <> k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = vint r).

(* get_item can return 0 in two cases: if the key is not in the map, or if its value is 0.
   In correct use, the latter should only occur if the value has not been initialized.
   Conceptually, this is still linearizable because we could have just checked before the key was added,
   but at a finer-grained level we can tell the difference from the history, so we might as well keep
   this information. *)
Definition get_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\
  (let '(hk, hv) := Znth i h ([], []) in exists r, add_events hk [Load (vint r)] (fst (Znth i h' ([], []))) /\
     (v = 0 /\ r = 0 /\ snd (Znth i h' ([], [])) = hv \/
      r = k /\ add_events hv [Load (vint v)] (snd (Znth i h' ([], [])))) /\
    (let v := value_of_hist hk in v <> vint 0 -> v = vint r)) /\
  forall j, (In j (indices (hash k) i) -> failed_load k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

(* Read the most recently written value. *)
Definition get_item_spec :=
 DECLARE _get_item
  WITH key : Z, p : val, sh : share, entries : list (val * val), ghosts : list (val * val),
    h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; key <> 0; Zlength ghosts = size; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h)
  POST [ tint ]
   EX value : Z, EX i : Z, EX h' : list (hist * hist),
   PROP (repable_signed value; get_item_trace h key value i h')
   LOCAL (temp ret_temp (vint value))
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h').

Definition add_item_trace (h : list (hist * hist)) k v i (success : bool) h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\ (let '(hk, hv) := Znth i h ([], []) in if success then
    add_events hk [Load (vint 0); CAS (vint 0) (vint 0) (vint k)] (fst (Znth i h' ([], []))) /\
    add_events hv [Store (vint v)] (snd (Znth i h' ([], []))) /\ value_of_hist hk = vint 0
  else (add_events hk [Load (vint k)] (fst (Znth i h' ([], []))) \/
    add_events hk [Load (vint 0); CAS (vint k) (vint 0) (vint k); Load (vint k)] (fst (Znth i h' ([], [])))) /\
      snd (Znth i h' ([], [])) = hv /\ let v := value_of_hist hk in v <> vint 0 -> v = vint k) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

Definition add_item_spec :=
 DECLARE _add_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list (val * val), ghosts : list (val * val),
    h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Zlength ghosts = size;
         Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h)
  POST [ tint ]
   EX success : bool, EX i : Z, EX h' : list (hist * hist),
   PROP (add_item_trace h key value i success h')
   LOCAL (temp ret_temp (Val.of_bool success))
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h').

Notation empty_hists := (repeat ([] : hist, [] : hist) (Z.to_nat size)).

Definition init_table_spec :=
 DECLARE _init_table
  WITH p : val
  PRE [ ]
   PROP ()
   LOCAL (gvar _m_entries p)
   SEP (data_at_ Ews (tarray tentry size) p)
  POST [ tvoid ]
   EX entries : list (val * val), EX ghosts : list (val * val),
   PROP (Zlength ghosts = size)
   LOCAL ()
   SEP (data_at Ews (tarray tentry size) entries p; atomic_entries Tsh entries ghosts empty_hists).

Definition freeze_table_spec :=
 DECLARE _freeze_table
  WITH sh : share, p : val, entries : list (val * val), ghosts : list (val * val), h : list (hist * hist),
    keys : val, values : val
  PRE [ _keys OF tptr tint, _values OF tptr tint ]
   PROP (readable_share sh; Zlength ghosts = Zlength entries; Zlength h = Zlength entries)
   LOCAL (gvar _m_entries p; temp _keys keys; temp _values values)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries Tsh entries ghosts h;
        data_at_ Tsh (tarray tint size) keys; data_at_ Tsh (tarray tint size) values)
  POST [ tvoid ]
   EX lk : list Z, EX lv : list Z,
   PROP (Forall repable_signed lk; Forall repable_signed lv;
         Forall2 full_hist (map fst h) lk; Forall2 full_hist (map snd h) lv;
         Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e) (map fst h) lk)
   LOCAL ()
   SEP (data_at_ sh (tarray tentry size) p;
        data_at Tsh (tarray tint size) (map (fun x => vint x) lk) keys;
        data_at Tsh (tarray tint size) (map (fun x => vint x) lv) values).

Inductive add_items_trace : list (hist * hist) -> list (Z * Z * Z * bool) -> list (hist * hist) -> Prop :=
| add_nil_items : forall h, add_items_trace h [] h
| add_snoc_items : forall h la h' k v i s h'' (Hn : add_items_trace h la h')
    (Hadd : add_item_trace h' k v i s h''), add_items_trace h (la ++ [(k, v, i, s)]) h''.

Definition f_lock_inv sh entries ghosts p t locksp lockt resultsp res :=
  (EX h : list (hist * hist), EX li : list Z, EX ls : list bool,
  !!(Zlength li = 3 /\ Zlength ls = 3 /\
     add_items_trace empty_hists (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls) h) &&
   data_at sh (tarray tentry size) entries p * atomic_entries sh entries ghosts h *
   data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
   data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp *
   data_at Tsh tint (vint (Zlength (filter id ls))) res).

Definition f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res :=
  selflock (f_lock_inv sh entries ghosts p t locksp lockt resultsp res) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH tid : val, x : share * share * list (val * val) * list (val * val) * val * Z * val * val * val * val
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, tsh, entries, ghosts, p, t, locksp, lockt, resultsp, res) := x in
   PROP (0 <= t < 3; isptr lockt; readable_share sh; readable_share tsh; Zlength ghosts = size)
   LOCAL (temp _arg tid; gvar _m_entries p; gvar _thread_locks locksp; gvar _results resultsp)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts empty_hists;
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
        data_at_ Tsh tint res;
        lock_inv tsh lockt (f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res))
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs := ltac:(with_library prog [verif_atomics.makelock_spec; freelock2_spec;
  verif_atomics.acquire_spec; release2_spec; spawn_spec; surely_malloc_spec;
  make_atomic_spec; free_atomic_spec; load_SC_spec; store_SC_spec; CAS_SC_spec;
  integer_hash_spec; set_item_spec; get_item_spec; add_item_spec; init_table_spec; freeze_table_spec;
  f_spec; main_spec]).

Lemma body_integer_hash: semax_body Vprog Gprog f_integer_hash integer_hash_spec.
Proof.
  start_function.
  forward.
Qed.

Opaque upto.

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Ltac entailer_for_return ::= go_lower; entailer'.

Lemma indices_next : forall i j, ((j - i) mod size) < size - 1 -> indices i (j + 1) = indices i j ++ [j mod size].
Proof.
  intros; unfold indices.
  exploit (Z_mod_lt (j - i) size); [apply size_pos | intro].
  rewrite Z.add_sub_swap, <- Zplus_mod_idemp_l, Zmod_small by omega.
  rewrite Z2Nat.inj_add by omega.
  rewrite upto_app, map_app; simpl.
  change (upto 1) with [0]; simpl.
  rewrite Z2Nat.id, Z.add_0_r by (apply Z_mod_lt; computable).
  rewrite Zplus_mod_idemp_r, Zplus_minus; auto.
Qed.

Lemma update_entries_hist : forall sh entries ghosts h i hk hv pki pvi gki gvi
  (Hlen : Zlength entries = Zlength h) (Hleng : Zlength ghosts = Zlength entries)
  (Hpi : Znth i entries (Vundef, Vundef) = (pki, pvi)) (Hgi : Znth i ghosts (Vundef, Vundef) = (gki, gvi))
  (Hi : 0 <= i < Zlength entries),
  atomic_entries sh entries ghosts (upd_Znth i h (hk, hv)) =
  fold_right sepcon emp (upd_Znth i (map (fun x => let '((pk, pv), (gk, gv), (hk, hv)) := x in
    atomic_loc_hist sh pk gk 0 k_R hk * atomic_loc_hist sh pv gv 0 v_R hv) (combine (combine entries ghosts) h))
    (atomic_loc_hist sh pki gki 0 k_R hk * atomic_loc_hist sh pvi gvi 0 v_R hv)).
Proof.
  intros; unfold atomic_entries.
  f_equal.
  erewrite upd_Znth_map with (v := ((pki, pvi), (gki, gvi), (hk, hv))), combine_upd_Znth2
    by (rewrite Zlength_combine, Z.min_l; auto; omega).
  rewrite Znth_combine, Hpi, Hgi; eauto.
Qed.

Lemma incr_invariant : forall (P : _ -> _ -> Prop) i1 i key (h h' : list (hist * hist)) h1
  (Hi1 : i1 = (i + hash key) mod size) (Hh' : Zlength h' = size) (Hinv : forall j,
  (In j (indices (hash key) (i + hash key)) -> P (Znth j h ([], [])) (Znth j h' ([], []))) /\
  (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
  (HP : P (Znth i1 h ([], [])) h1) (Hi : i mod size < size - 1) j,
  (In j (indices (hash key) ((i + 1) + hash key)) -> P (Znth j h ([], [])) (Znth j (upd_Znth i1 h' h1) ([], []))) /\
  (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j (upd_Znth i1 h' h1) ([], []) = Znth j h ([], [])).
Proof.
  intros; specialize (Hinv j); destruct Hinv.
  rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
  assert (0 <= i1 < Zlength h') by (subst; rewrite Hh'; apply Z_mod_lt, size_pos).
  assert (~ In i1 (indices (hash key) (i + hash key))) as Hnew.
  { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
    rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
    subst; rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
    rewrite Zmod_small in Heq; [omega|].
    destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
  split.
  * intros [Hin | Hin].
    { rewrite upd_Znth_diff'; auto.
      intro; contradiction Hnew; subst; auto. }
    simpl in Hin; destruct Hin; [subst | contradiction].
    simpl in *; rewrite upd_Znth_same; auto.
  * intro Hout; rewrite upd_Znth_diff'; auto.
    intro; contradiction Hout; subst; simpl; auto.
  * rewrite Z.add_simpl_r; auto.
Qed.

Lemma k_R_precise : forall v, precise (EX h : _, k_R h v).
Proof.
  intros; apply derives_precise' with (Q := emp); auto.
  unfold k_R; entailer!.
Qed.

Lemma v_R_precise : forall v, precise (EX h : _, v_R h v).
Proof.
  intros; apply derives_precise' with (Q := emp); auto.
  unfold v_R; entailer!.
Qed.
Hint Resolve k_R_precise v_R_precise.

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) ->
            failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    change (2 ^ 14) with size.
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert (0 <= i1 mod size < Zlength h') by omega.
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) by omega.
    assert (i <= Zlength h') by omega.
    unfold atomic_entries; rewrite extract_nth_sepcon with (i := i1 mod size),
      Znth_map with (d' := (Vundef, Vundef, (Vundef, Vundef), ([], []))), !Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine; rewrite ?Zlength_combine, ?Z.min_l; rewrite ?Z.min_l; auto;
          omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) ghosts (Vundef, Vundef)) as (gki, gvi) eqn: Hgi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; Intros.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      setoid_rewrite Hpi; auto. }
    assert (~ In (i1 mod size) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
      replace (i1 mod size) with ((i + hash key) mod size) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
    assert (Znth (i1 mod size) h ([], []) = Znth (i1 mod size) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod size) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (AL_witness sh pki gki 0 k_R hki emp
      (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AL_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto. }
    Intros v.
    simpl; Intros hki1.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: _ :: ?R)))) _ _ =>
      forward_if (EX hki' : hist, PROP (found_key key hki hki') (LOCALx Q
        (SEPx (atomic_loc_hist sh pki gki 0 k_R hki' :: R)))) end.
    + match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (v = 0) (LOCALx Q (SEPx R))) end.
      { eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) ->
            failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
          SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h')).
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki1, hvi)); entailer!.
        { split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; repeat (eexists; eauto); auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
        rewrite sepcon_assoc; auto. }
      { forward.
        entailer!. }
      Intros; subst.
      forward_call (ACAS_witness sh pki gki 0 k_R hki1 0 key emp
        (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
      { entailer!.
        setoid_rewrite Hpi; auto. }
      { repeat (split; auto).
        apply ACAS_hist_spec; auto.
        intros ???????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; [| |contradiction].
          * intros.
            if_tac; auto; absurd (value_of e = vint 0); auto.
            subst; symmetry; auto.
          * subst; simpl; intros.
            if_tac; if_tac; auto; [subst; absurd (vint 0 = vint 0); auto|].
            absurd (v' = 0); auto; apply repr_inj_signed; auto; congruence.
        + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
          exploit Hhist.
          { eapply add_events_incl; eauto. }
          intro X; apply nth_error_In in X; subst; auto. }
      Intros v hki2.
      exploit (add_events_trans hki); eauto; intro.
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: _ :: ?R)))) _ _ =>
        forward_if (EX hki' : hist, PROP (found_key key hki hki') ((LOCALx Q)
        (SEPx (atomic_loc_hist sh pki gki 0 k_R hki' :: R)))) end.
      * destruct (eq_dec 0 v); [discriminate|].
        forward_call (AL_witness sh pki gki 0 k_R hki2 emp (fun v' => !!(v' = v) && emp)).
        { entailer!.
          simpl in *; rewrite Hpi; auto. }
        { split; auto.
          apply AL_hist_spec; auto.
          intros ???????????? Ha.
          unfold k_R in *; simpl in *.
          eapply semax_pre, Ha.
          go_lowerx; entailer!.
          repeat split.
          + rewrite Forall_app; repeat constructor; auto.
          + intros ? Hin; rewrite in_app in Hin.
            destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
          + exploit add_events_in; eauto; simpl; eauto; intros (? & ? & ?).
            match goal with H : forall e, In e h'0 -> _ |- _ =>
              exploit (H (CAS (vint v) (vint 0) (vint key))) end.
            { eapply nth_error_In, Hhist; eauto. }
            { simpl.
              if_tac; [absurd (v = 0)|]; auto.
              apply repr_inj_signed; auto; congruence. }
            simpl.
            if_tac; [absurd (v = 0)|]; auto; intros; apply repr_inj_signed; auto; congruence. }
        Intros v'; simpl; Intros hki3; subst.
        exploit (add_events_trans hki); eauto; intro.
        match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROP (v = key) (LOCALx Q (SEPx R))) end.
        { eapply semax_pre; [|apply semax_continue].
          unfold POSTCONDITION, abbreviate, overridePost.
          destruct (eq_dec EK_continue EK_normal); [discriminate|].
          unfold loop1_ret_assert.
          go_lower.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki3, hvi)); entailer!.
          { split.
            { rewrite upd_Znth_Zlength; auto; omega. }
            rewrite Zmod_mod.
            split; auto.
            apply incr_invariant; auto; simpl in *; try omega.
            * rewrite Heq, Hhi; do 2 eexists; eauto.
              repeat split; auto.
              match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
                symmetry; apply H; auto end.
              rewrite ordered_last_value; auto.
            * admit. (* list is long enough *) }
          fast_cancel.
          erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
          rewrite sepcon_assoc; auto. }
        { forward.
          entailer!. }
        intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
        rewrite eq_dec_refl.
        go_lower.
        apply andp_right; [apply prop_right; auto|].
        Exists hki3; entailer!.
        split; auto.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
          symmetry; apply H; auto end.
        apply ordered_last_value; auto.
      * forward.
        destruct (eq_dec 0 v); [|discriminate].
        subst; Exists hki2; entailer!.
        split; auto.
        intros ? X; contradiction X.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
          symmetry; apply H; auto end.
        apply ordered_last_value; auto.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
        rewrite eq_dec_refl.
        Intros hki'.
        go_lower.
        apply andp_right; [apply prop_right; auto|].
        Exists hki'; entailer!.
    + forward.
      subst; Exists hki1; entailer!.
      split; auto.
      match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
        symmetry; apply H; auto end.
      apply ordered_last_value; auto.
    + rewrite (atomic_loc_isptr _ pvi).
      Intros hki'.
      forward.
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      forward_call (AS_witness sh pvi gvi 0 v_R hvi value emp emp).
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      { repeat (split; auto).
        apply AS_hist_spec; auto.
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!. }
      Intros hvi1.
      forward.
      Exists (i1 mod size) (upd_Znth (i1 mod size) h' (hki', hvi1)); entailer!.
      { split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split; auto.
        split; eauto.
        assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
        { unfold indices.
          replace (i1 mod size) with ((i + hash key) mod size).
          rewrite Zminus_mod_idemp_l; auto. }
        simpl in Hindex; split.
        + intro Hin; simpl in *.
          rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          rewrite Hindex; auto.
          { intro; contradiction Hnew; subst.
            rewrite Hindex; auto. }
        + intros Hout ?; rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          { intro; contradiction Hout; subst; simpl.
            rewrite <- Hindex; auto. } }
      fast_cancel.
      erewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_loc_hist _ _ _ _ _ _)), replace_nth_sepcon,
        update_entries_hist; eauto; auto; omega.
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash key) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) ->
            failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    change (2 ^ 14) with size.
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert (0 <= i1 mod size < Zlength h') by omega.
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) by omega.
    assert (i <= Zlength h') by omega.
    unfold atomic_entries; rewrite extract_nth_sepcon with (i := i1 mod size),
      Znth_map with (d' := (Vundef, Vundef, (Vundef, Vundef), ([], []))), !Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine; rewrite ?Zlength_combine, ?Z.min_l; rewrite ?Z.min_l; auto;
          omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) ghosts (Vundef, Vundef)) as (gki, gvi) eqn: Hgi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; Intros.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      setoid_rewrite Hpi; auto. }
    assert (~ In (i1 mod size) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
      replace (i1 mod size) with ((i + hash key) mod size) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
    assert (Znth (i1 mod size) h ([], []) = Znth (i1 mod size) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod size) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (AL_witness sh pki gki 0 k_R hki emp
      (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AL_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto. }
    Intros v; simpl; Intros hki1.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v <> key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ pvi).
      forward.
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      forward_call (AL_witness sh pvi gvi 0 v_R hvi emp (fun (v : Z) => emp)).
      { entailer!.
        simpl in Hpi; rewrite Hpi; auto. }
      { repeat (split; auto).
        apply AL_hist_spec; auto.
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!. }
      subst; Intros v; simpl; Intros hvi1.
      forward.
      Exists v (i1 mod size) (upd_Znth (i1 mod size) h' (hki1, hvi1)); entailer!.
      { split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 2 eexists; eauto; split; eauto.
          match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto.
        - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
          { unfold indices.
            replace (i1 mod size) with ((i + hash key) mod size).
            rewrite Zminus_mod_idemp_l; auto. }
          simpl in Hindex; split.
          + intro Hin; simpl in *.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          + intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. } }
      fast_cancel.
      erewrite <- !sepcon_assoc, (sepcon_assoc _ (atomic_loc _ _ _)), replace_nth_sepcon,
        update_entries_hist; eauto; try omega.
      rewrite (sepcon_comm (atomic_loc_hist _ _ _ _ _ _)); auto.
    + forward.
      entailer!.
    + Intros; match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (v <> 0) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists 0 (i1 mod size) (upd_Znth (i1 mod size) h' (hki1, hvi)); entailer!.
        { split.
          { rewrite upd_Znth_Zlength; auto. }
          split; [replace (Zlength h) with (Zlength h'); auto|].
          setoid_rewrite Heq.
          rewrite Hhi; simpl.
          rewrite upd_Znth_same by auto; simpl; split.
          - do 2 eexists; eauto; split; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
            { unfold indices.
              replace (i1 mod size) with ((i + hash key) mod size).
              rewrite Zminus_mod_idemp_l; auto. }
            simpl in Hindex; split.
            + intro Hin; simpl in *.
              rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              rewrite Hindex; auto.
              { intro; contradiction Hnew; subst.
                rewrite Hindex; auto. }
            + intros Hout ?; rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hout; subst; simpl.
                rewrite <- Hindex; auto. } }
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
      * forward.
        entailer!.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) ->
            failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
          SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h')).
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki1, hvi)); entailer!.
        { split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; repeat (eexists; eauto); auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash key) mod size).
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma body_add_item : semax_body Vprog Gprog f_add_item add_item_spec.
Proof.
  start_function.
  assert (sh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 14) by omega.
    change (2 ^ 14) with size.
    exploit (Z_mod_lt i1 size); [omega | intro Hi1].
    assert (0 <= i1 mod size < Zlength h') by omega.
    assert (0 <= i1 mod size < Zlength h) by omega.
    assert_PROP (Zlength entries = size) as Hentries by entailer!.
    assert (0 <= i1 mod size < Zlength entries) by omega.
    assert (i <= Zlength h') by omega.
    unfold atomic_entries; rewrite extract_nth_sepcon with (i := i1 mod size),
      Znth_map with (d' := (Vundef, Vundef, (Vundef, Vundef), ([], []))), !Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine; rewrite ?Zlength_combine, ?Z.min_l; rewrite ?Z.min_l; auto;
          omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) ghosts (Vundef, Vundef)) as (gki, gvi) eqn: Hgi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; Intros.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      setoid_rewrite Hpi; auto. }
    assert (~ In (i1 mod size) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt, size_pos).
      replace (i1 mod size) with ((i + hash key) mod size) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|apply size_pos].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos. }
    assert (Znth (i1 mod size) h ([], []) = Znth (i1 mod size) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod size) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (AL_witness sh pki gki 0 k_R hki emp
      (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AL_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto. }
    Intros v; simpl; Intros hki1.
    assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
    { unfold indices.
      replace (i1 mod size) with ((i + hash key) mod size).
      rewrite Zminus_mod_idemp_l; auto. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v <> key) (LOCALx Q (SEPx R))) end.
    { forward.
      Exists false (i1 mod size) (upd_Znth (i1 mod size) h' (hki1, hvi)); entailer!.
      + split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [auto|].
        setoid_rewrite Heq; rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl.
        split; [repeat split; eauto|].
        { match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto. }
        simpl in Hindex; split.
        * intro Hin; simpl in *.
          rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          simpl in *; rewrite Hindex; auto.
          { intro; contradiction Hnew; subst.
            simpl in *; rewrite Hindex; auto. }
        * intros Hout ?; rewrite upd_Znth_diff'; auto.
          match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
          { intro; contradiction Hout; subst; simpl.
            rewrite <- Hindex; auto. }
      + erewrite replace_nth_sepcon, update_entries_hist; eauto; try omega.
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto. }
    { forward.
      entailer!. }
    Intros.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v = 0) (LOCALx Q (SEPx R))) end.
    { eapply semax_pre; [|apply semax_continue].
      unfold POSTCONDITION, abbreviate, overridePost.
      destruct (eq_dec EK_continue EK_normal); [discriminate|].
      unfold loop1_ret_assert.
      instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
        PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
        forall j, (In j (indices (hash key) ((i + 1) + hash key)) ->
          failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
          (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
        LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
        SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries ghosts h')).
      Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki1, hvi)); entailer!.
      { split.
        { rewrite upd_Znth_Zlength; auto; omega. }
        rewrite Zmod_mod.
        split; auto.
        apply incr_invariant; auto; simpl in *; try omega.
        * rewrite Heq, Hhi; repeat (eexists; eauto); auto.
          match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto.
        * admit. (* list is long enough *) }
      fast_cancel.
      erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
      rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto. }
    { forward.
      entailer!. }
    Intros; subst.
    forward_call (ACAS_witness sh pki gki 0 k_R hki1 0 key emp
      (fun v => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0) && emp)).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      apply ACAS_hist_spec; auto.
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; [| |contradiction].
        * intros.
          assert (vint v' = value_of e) by auto.
          if_tac; auto.
          subst; absurd (value_of e = vint 0); auto.
        * subst; simpl; intros.
          if_tac; if_tac; auto; [absurd (vint v' = vint 0); subst; auto|].
          absurd (v' = 0); auto; apply repr_inj_signed; auto; congruence.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        exploit Hhist.
        { eapply add_events_incl; eauto. }
        intro X; apply nth_error_In in X; subst; auto. }
    Intros v; simpl; Intros hki2.
    exploit (add_events_trans hki); eauto; intro.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v = 0) ((LOCALx Q) (SEPx R))) end.
    { destruct (eq_dec 0 v); [discriminate|].
      forward_call (AL_witness sh pki gki 0 k_R hki2 emp (fun v' => !!(v' = v) && emp)).
      { entailer!.
        simpl in Hpi; rewrite Hpi; auto. }
      { split; auto.
        apply AL_hist_spec; auto.
        intros ???????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
        + exploit add_events_in; eauto; simpl; eauto; intros (? & ? & ?).
          match goal with H : forall e, In e _ -> _ |- _ =>
            exploit (H (CAS (vint v) (vint 0) (vint key))) end.
          { eapply nth_error_In, Hhist; eauto. }
          { simpl.
            if_tac; [absurd (v = 0)|]; auto; apply repr_inj_signed; auto; congruence. }
          simpl.
          if_tac; [absurd (v = 0)|]; auto; intros; apply repr_inj_signed; auto; congruence. }
      Intros v'; simpl; Intros hki3; subst.
      exploit (add_events_trans hki); eauto; intro.
      match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (fun _ : environ => FF) end.
      - forward.
        Exists false (i1 mod size) (upd_Znth (i1 mod size) h' (hki3, hvi)); entailer!.
        + split.
          { rewrite upd_Znth_Zlength; auto. }
          split; [auto|].
          setoid_rewrite Heq; rewrite Hhi; simpl.
          rewrite upd_Znth_same by auto; simpl.
          split; [split; auto; split; auto|].
          { match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto. }
          simpl in Hindex; split.
          * intro Hin; simpl in *.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          * intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. }
        + erewrite replace_nth_sepcon, update_entries_hist; eauto; try omega.
          rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
      - eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        go_lower.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki3, hvi)); entailer!.
        { split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; do 2 eexists; eauto; repeat split; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint v = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        fast_cancel.
        erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
        rewrite (sepcon_assoc _ (atomic_loc _ _ _)); auto.
      - intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
        Intros; go_lowerx; contradiction. }
    { forward.
      destruct (eq_dec 0 v); [|discriminate].
      entailer!. }
    rewrite (atomic_loc_isptr _ pvi).
    Intros; subst; simpl in Hpi.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    forward_call (AS_witness sh pvi gvi 0 v_R hvi value emp emp).
    { entailer!.
      rewrite Hpi; auto. }
    { repeat (split; auto).
      apply AS_hist_spec; auto.
      intros ???????????? Ha.
      unfold v_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!. }
    Intros hvi1.
    forward.
    Exists true (i1 mod size) (upd_Znth (i1 mod size) h' (hki2, hvi1)); entailer!.
    { split.
      { rewrite upd_Znth_Zlength; auto. }
      split; [auto|].
      setoid_rewrite Heq.
      rewrite Hhi; simpl.
      rewrite upd_Znth_same by auto; simpl; split; [repeat eexists; auto|].
      { destruct (eq_dec (value_of_hist hki) (vint 0)); auto.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
          symmetry; apply H; auto end.
        rewrite ordered_last_value; auto. }
      split.
      + intro Hin.
        rewrite upd_Znth_diff'; auto.
        match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
        rewrite Hindex; auto.
        { intro; contradiction Hnew; subst.
          rewrite Hindex; auto. }
      + intros Hout ?; simpl in *; rewrite upd_Znth_diff'; auto.
        match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
        { intro; contradiction Hout; subst; simpl.
          rewrite <- Hindex; auto. } }
    fast_cancel.
    erewrite <- !sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; try omega.
    rewrite (sepcon_assoc _ (atomic_loc _ _ _)), sepcon_comm; auto.
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod _) with ((i + hash key) mod size); simpl.
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Opaque size.
Opaque Znth.

Lemma Zlength_empty : Zlength empty_hists = size.
Proof.
  rewrite Zlength_repeat, Z2Nat.id; auto.
  pose proof size_pos; omega.
Qed.

Lemma body_init_table : semax_body Vprog Gprog f_init_table init_table_spec.
Proof.
  start_function.
  forward_for_simple_bound size (EX i : Z, PROP () LOCAL (gvar _m_entries p)
    SEP (EX entries : list (val * val), EX ghosts : list (val * val),
      !!(Zlength entries = i /\ Zlength ghosts = i) && @data_at CompSpecs Ews (tarray tentry size)
          (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i))) p *
        atomic_entries Tsh entries ghosts (repeat ([], []) (Z.to_nat i)))).
  { change size with 16384; computable. }
  { change size with 16384; computable. }
  - Exists (@nil (val * val)) (@nil (val * val)); entailer!.
    rewrite data_at__eq; unfold default_val; simpl.
    rewrite repeat_list_repeat, Z.sub_0_r; auto.
  - Intros entries ghosts.
    eapply ghost_alloc with (g := init_hist); auto with init.
    Intro gk.
    forward_call (MA_witness gk 0 k_R).
    { unfold k_R; entailer!. }
    { split; [|split; computable].
      apply MA_hist_spec; auto. }
    Intro k.
    forward.
    eapply ghost_alloc with (g := init_hist); auto with init.
    Intro gv.
    forward_call (MA_witness gv 0 v_R).
    { unfold v_R; entailer!. }
    { split; [|split; computable].
      apply MA_hist_spec; auto. }
    Intro v.
    forward.
    assert (0 <= Zlength entries < Zlength (entries ++
      repeat (Vundef, Vundef) (Z.to_nat (size - Zlength entries)))).
    { rewrite Zlength_app, Zlength_repeat, Z2Nat.id; omega. }
    subst; rewrite upd_Znth_twice, upd_complete_gen by (auto; omega).
    Exists (entries ++ [(k, v)]) (ghosts ++ [(gk, gv)]); entailer!.
    + rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; omega.
    + rewrite upd_Znth_same by auto.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
      unfold atomic_entries.
      rewrite Z2Nat.inj_add, repeat_plus by omega; simpl.
      rewrite !combine_app, map_app, sepcon_app; simpl.
      unfold atomic_entry, atomic_loc_hist; entailer!.
      { rewrite combine_length, repeat_length, Zlength_correct, Nat2Z.id, Nat.min_l; auto.
        apply Nat2Z.inj_le; rewrite <- !Zlength_correct; omega. }
      { apply Nat2Z.inj; rewrite <- !Zlength_correct; omega. }
  - Intros entries ghosts.
    rewrite Zminus_diag, app_nil_r.
    forward.
    Exists entries ghosts; entailer!.
Qed.

Lemma body_freeze_table : semax_body Vprog Gprog f_freeze_table freeze_table_spec.
Proof.
  start_function.
  assert_PROP (Zlength entries = size) as Hlen by entailer!.
  forward_for_simple_bound size (EX i : Z, PROP () LOCAL (gvar _m_entries p; temp _keys keys; temp _values values)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p;
         atomic_entries Tsh (sublist i (Zlength entries) entries) (sublist i (Zlength entries) ghosts)
           (sublist i (Zlength entries) h);
         EX lk : list Z, EX lv : list Z, !!(Zlength lk = i /\ Zlength lv = i /\
           Forall repable_signed lk /\ Forall repable_signed lv /\
           Forall2 full_hist (map fst (sublist 0 i h)) lk /\ Forall2 full_hist (map snd (sublist 0 i h)) lv /\
           Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
             (map fst (sublist 0 i h)) lk) &&
           data_at Tsh (tarray tint size) (map (fun x => vint x) lk ++ repeat Vundef (Z.to_nat (Zlength entries - i))) keys *
           data_at Tsh (tarray tint size) (map (fun x => vint x) lv ++ repeat Vundef (Z.to_nat (Zlength entries - i))) values)).
  { change size with 16384; computable. }
  { change size with 16384; computable. }
  - Exists (@nil Z) (@nil Z); rewrite sublist_nil.
    go_lower; repeat (apply andp_right; [apply prop_right; auto|]).
    rewrite !sublist_same by (auto; omega).
    repeat (apply sepcon_derives; [auto|]).
    + apply andp_right; [apply prop_right; repeat (split; auto)|].
      rewrite data_at__eq; unfold default_val; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r, Hlen; auto.
    + rewrite data_at__eq; unfold default_val; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r, Hlen; auto.
  - Intros lk lv.
    unfold atomic_entries.
    rewrite !sublist_next with (d := (Vundef, Vundef)) by omega.
    rewrite sublist_next with (i0 := i)(d := (Vundef, Vundef)) by omega.
    rewrite sublist_next with (d := ([], [])) by omega; simpl.
    destruct (Znth i entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth i ghosts (Vundef, Vundef)) as (gki, gvi) eqn: Hgi.
    destruct (Znth i h ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry, atomic_loc_hist; rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    rewrite Hpi.
    forward_call (pki, hist_R gki 0 k_R).
    unfold hist_R; Intros ki lki.
    gather_SEP 3 0; rewrite hist_ref_join by (apply Share.nontrivial).
    Intro hk'; unfold hist_sub; rewrite eq_dec_refl; Intros; subst hk'.
    forward.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    rewrite Hpi.
    forward_call (pvi, hist_R gvi 0 v_R).
    unfold hist_R; Intros vi lvi.
    gather_SEP 5 0; rewrite hist_ref_join by (apply Share.nontrivial).
    Intro hv'; unfold hist_sub; rewrite eq_dec_refl; Intros; subst hv'.
    apply ghost_dealloc.
    focus_SEP 2; apply ghost_dealloc.
    forward.
    Exists (lk ++ [ki]) (lv ++ [vi]).
    go_lower.
    unfold v_R, k_R; Intros.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    apply andp_right.
    + apply prop_right.
      repeat (split; [repeat split; auto; omega|]).
      rewrite sublist_split with (mid := i), sublist_len_1 with (d := ([], [])), !map_app, Hhi by omega.
      do 2 (split; [rewrite Forall_app; auto|]).
      split; [|split]; apply Forall2_app; auto; repeat constructor; unfold full_hist; eauto.
      intros t e Hin; match goal with H : hist_list hki _ |- _ => apply H, nth_error_in in Hin; auto end.
    + fast_cancel.
      rewrite !map_app; simpl.
      replace (i + 1) with (Zlength (map (fun x => vint x) lk ++ [vint ki]))
        by (rewrite Zlength_app, Zlength_map, Zlength_cons, Zlength_nil; omega).
      rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      replace (Zlength (map _ _ ++ _)) with (Zlength (map (fun x => vint x) lv ++ [vint vi]))
        by (rewrite !Zlength_app, !Zlength_map, !Zlength_cons, !Zlength_nil; omega).
      rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      rewrite !Zlength_map.
      apply sepcon_derives; [auto|].
      apply sepcon_derives; [replace i with (Zlength lk) | replace i with (Zlength lv)]; auto.
  - Intros lk lv; forward.
    rewrite Hlen, Zminus_diag, !app_nil_r, !sublist_nil.
    unfold atomic_entries; simpl.
    repeat match goal with H : Forall2 _ (map _ (sublist _ _ _)) _ |- _ =>
      rewrite sublist_same in H by (auto; omega) end.
    Exists lk lv; apply andp_right; auto.
    (* entailer! is slow here *)
    apply andp_right; [entailer!|].
    apply andp_right; auto.
    apply sepcon_derives; [apply data_at_data_at_ | fast_cancel].
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Lemma add_item_trace_wf : forall h k v i s h' (Hwf : wf_hists h) (Htrace : add_item_trace h k v i s h'),
  wf_hists h'.
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
  apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
  destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
  - subst; rewrite Hhi in *.
    destruct s.
    + destruct Hi as (Hi1 & Hi2 & ?).
      rewrite (add_events_snd _ _ _ Hi1), (add_events_snd _ _ _ Hi2), !Forall_app.
      repeat constructor; auto; eapply add_events_ordered; eauto.
    + destruct Hi as (Hi1 & -> & ?).
      split; auto.
      destruct Hi1 as [Hi1 | Hi1]; rewrite (add_events_snd _ _ _ Hi1), Forall_app; repeat constructor; auto;
        eapply add_events_ordered; eauto.
  - destruct Hrest as ((? & ? & Hcase & ? & ? & -> & ?) & _); auto.
    split; auto.
    destruct Hcase as [Hi1 | Hi1]; rewrite (add_events_snd _ _ _ Hi1), Forall_app; repeat constructor; auto;
      eapply add_events_ordered; eauto.
  - destruct Hrest as (_ & ->); auto.
Qed.

Corollary add_items_trace_wf : forall h la h', add_items_trace h la h' ->
  wf_hists h -> wf_hists h'.
Proof.
  induction 1; auto.
  intro; apply add_item_trace_wf in Hadd; auto.
Qed.

Lemma wf_empty : wf_hists empty_hists.
Proof.
  apply Forall_repeat; repeat split; simpl; auto; apply ordered_nil.
Qed.
Hint Resolve wf_empty.

Lemma add_items_length : forall h la h', add_items_trace h la h' -> Zlength h' = Zlength h.
Proof.
  induction 1; auto.
  destruct Hadd; omega.
Qed.

Corollary add_items_empty_length : forall h la, add_items_trace empty_hists la h -> Zlength h = size.
Proof.
  intros; erewrite add_items_length, Zlength_empty; eauto.
Qed.

Lemma f_pred_precise : forall tsh sh (entries ghosts : list (val * val)) p t locksp lockt resultsp res,
  readable_share sh -> Zlength ghosts = Zlength entries ->
  precise (f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res).
Proof.
  intros; unfold f_lock_pred.
  apply selflock_precise.
  unfold f_lock_inv.
  eapply derives_precise' with (Q := data_at_ _ _ _ *
    fold_right sepcon emp (map (fun '((pk, pv), (gk, gv)) =>
      (EX h : hist, atomic_loc_hist sh pk gk 0 k_R h) * (EX h : hist, atomic_loc_hist sh pv gv 0 v_R h))
      (combine entries ghosts)) * data_at_ sh _ _ * data_at_ _ _ _ * data_at_ _ _ _).
  - Intros hists li ls; assert_PROP (Zlength entries = size) as Hlene by entailer!.
    repeat (apply sepcon_derives; try apply data_at_data_at_).
    exploit add_items_length; eauto.
    rewrite Zlength_empty; intro Hlenh.
    assert (Zlength entries <= Zlength hists) by omega.
    apply sepcon_list_derives; rewrite !Zlength_map, !Zlength_combine, !Z.min_l; rewrite ?Z.min_l; auto;
      try omega.
    intros; rewrite Znth_map with (d' := ((Vundef, Vundef), (Vundef, Vundef), ([], [])))
      by (rewrite !Zlength_combine, !Z.min_l; rewrite ?Z.min_l; auto; omega).
    rewrite Znth_map with (d' := ((Vundef, Vundef), (Vundef, Vundef)))
      by (rewrite Zlength_combine, Z.min_l; omega).
    rewrite !Znth_combine by (rewrite ?Zlength_combine, ?Z.min_l; omega).
    unfold atomic_entry.
    destruct (Znth i entries (Vundef, Vundef)), (Znth i ghosts (Vundef, Vundef)).
    destruct (Znth i hists ([], [])) as (hk, hv).
    Exists hk hv; auto.
  - repeat (apply precise_sepcon; auto).
    apply precise_fold_right.
    rewrite Forall_map, Forall_forall; intros ((?, ?), (?, ?)) ?; simpl.
    apply precise_sepcon; apply atomic_loc_hist_precise; auto.
Qed.

Lemma f_pred_positive : forall tsh sh entries ghosts p t locksp lockt resultsp res,
  positive_mpred (f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res).
Proof.
  intros; apply selflock_positive.
Qed.
Hint Resolve f_pred_precise f_pred_positive.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (data_at_isptr Tsh); Intros.
  assert (force_val (sem_cast_neutral tid) = tid) as Htid.
  { destruct tid; try contradiction; auto. }
  replace_SEP 2 (data_at Tsh tint (vint t) (force_val (sem_cast_neutral tid))).
  { rewrite Htid; entailer!. }
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
  focus_SEP 2.
  forward_call (tid, sizeof tint).
  { rewrite Htid; apply sepcon_derives; [apply data_at_memory_block | cancel_frame]. }
  forward_for_simple_bound 3 (EX i : Z, EX ls : list bool,
    PROP (Zlength ls = i)
    LOCAL (temp _total (vint (Zlength (filter id ls))); temp _res res; temp _l lockt; temp _t (vint t);
           temp _arg tid; gvar _m_entries p; gvar _thread_locks locksp; gvar _results resultsp)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p;
         EX h : list (hist * hist), EX li : list Z,
           !!(Zlength li = i /\ add_items_trace empty_hists (combine (combine (combine (sublist 0 i [1; 2; 3])
              (sublist 0 i [1; 1; 1])) li) ls) h) && atomic_entries sh entries ghosts h;
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
         data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
         data_at_ Tsh tint res;
         lock_inv tsh lockt (f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res))).
  - Exists (@nil bool) (empty_hists : list (hist * hist)) (@nil Z); entailer!.
    constructor.
  - Intros h li.
    forward_call (i + 1, 1, p, sh, entries, ghosts, h).
    { repeat (split; auto; try computable; try omega).
      + pose proof (Int.min_signed_neg); omega.
      + transitivity 4; [omega | computable].
      + eapply add_items_empty_length; eauto.
      + eapply add_items_trace_wf; eauto. }
    apply extract_exists_pre; intros ((s, j), h'); simpl; Intros.
    match goal with |- semax _ (PROP () (LOCALx (?a :: ?b :: temp _total _ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROP () (LOCALx (a :: b :: temp _total (vint (Zlength (filter id (x ++ [s])))) :: Q)
                 (SEPx R))) end.
    + forward.
      subst; rewrite filter_app, Zlength_app; entailer!.
    + forward.
      subst; rewrite filter_app, Zlength_app; entailer!.
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
      repeat (apply andp_right; [apply prop_right; auto|]).
      Exists (x ++ [s]) h' (li ++ [j]); entailer!.
      erewrite !sublist_split with (lo := 0)(mid := Zlength x)(hi := Zlength x + 1), !sublist_len_1;
        rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; auto; try omega.
      split; auto; split; [omega|].
      rewrite !combine_app'; rewrite ?Zlength_combine, ?Zlength_sublist, ?Z.min_l; rewrite ?Z.min_l, ?Zlength_cons,
        ?Zlength_nil; try omega; simpl.
      econstructor; eauto.
      change [1; 2; 3] with (map Z.succ (upto 3)); change [1; 1; 1] with (repeat 1 3).
      rewrite Znth_map', Znth_upto, Znth_repeat; auto; simpl; omega.
  - Intros ls h li.
    forward.
    forward_call (lockt, tsh, f_lock_inv sh entries ghosts p t locksp lockt resultsp res,
                  f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res).
    { assert_PROP (Zlength entries = size) by entailer!.
      lock_props.
      { apply f_pred_precise; auto; omega. }
      { apply selflock_rec. }
      unfold f_lock_pred.
      rewrite selflock_eq at 2.
      unfold f_lock_inv at 2.
      rewrite lock_struct_array.
      Exists h li ls; entailer!.
      subst Frame; instantiate (1 := []); simpl; rewrite sepcon_emp; apply lock_inv_later. }
    forward.
Qed.

Lemma lock_struct : forall p, data_at_ Tsh (Tstruct _lock_t noattr) p |-- data_at_ Tsh tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at, at_offset; simpl.
  rewrite field_compatible_cons; simpl; entailer!.
Qed.

Fixpoint join_hists (h1 h2 : list (hist * hist)) :=
  match (h1, h2) with
  | ((k1, v1) :: rest1, (k2, v2) :: rest2) => (k1 ++ k2, v1 ++ v2) :: join_hists rest1 rest2
  | _ => []
  end.

Lemma join_hists_spec : forall h1 h2 i, Zlength h1 = Zlength h2 ->
  Znth i (join_hists h1 h2) ([], []) =
  (fst (Znth i h1 ([], [])) ++ fst (Znth i h2 ([], [])),
  (snd (Znth i h1 ([], [])) ++ snd (Znth i h2 ([], [])))).
Proof.
  induction h1; destruct h2; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *.
  - rewrite Znth_nil; auto.
  - pose proof (Zlength_nonneg h2); omega.
  - pose proof (Zlength_nonneg h1); omega.
  - destruct a, p.
    destruct (zlt i 0).
    { rewrite !Znth_underflow; auto. }
    destruct (eq_dec i 0).
    + subst; rewrite !Znth_0_cons; auto.
    + rewrite !Znth_pos_cons by omega.
      apply IHh1; omega.
Qed.

Lemma join_empty : forall h, Zlength h = size -> join_hists empty_hists h = h.
Proof.
  intros.
  rewrite Zlength_correct in H.
  assert (length h = Z.to_nat size) as Hlen by Omega0.
  forget (Z.to_nat size) as n; clear H.
  revert dependent h; induction n; destruct h; auto; intros; inv Hlen; simpl.
  destruct p; rewrite IHn; auto.
Qed.

Lemma atomic_entries_join : forall sh1 sh2 sh entries ghosts hists1 hists2 hists
  (Hjoin : sepalg.join sh1 sh2 sh) (Hhists : join_hists hists1 hists2 = hists)
  (Hghosts : Zlength ghosts = Zlength entries)
  (Hlen : Zlength entries = Zlength hists1) (Hlen1 : Zlength hists1 = Zlength hists2)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_entries sh1 entries ghosts hists1 * atomic_entries sh2 entries ghosts hists2 =
  !!(forall i, disjoint (fst (Znth i hists1 ([], []))) (fst (Znth i hists2 ([], []))) /\
               disjoint (snd (Znth i hists1 ([], []))) (snd (Znth i hists2 ([], [])))) &&
    atomic_entries sh entries ghosts hists.
Proof.
  induction entries; unfold atomic_entries; simpl; intros.
  { exploit Zlength_nil_inv; eauto; intro; subst.
    exploit (Zlength_nil_inv hists1); auto; intro; subst.
    exploit (Zlength_nil_inv hists2); auto; intro; subst.
    rewrite prop_true_andp, sepcon_emp; auto.
    intro; rewrite Znth_nil; simpl; auto. }
  destruct ghosts; [exploit (Zlength_nil_inv (a :: entries)); eauto; discriminate|].
  destruct hists1; [exploit (Zlength_nil_inv (a :: entries)); eauto; discriminate|].
  destruct hists2; [exploit Zlength_nil_inv; eauto; discriminate|].
  rewrite !Zlength_cons in *; simpl in *.
  destruct a, p as (gk, gv), p0 as (hk1, hv1), p1 as (hk2, hv2); subst; simpl.
  unfold atomic_entry.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2)); [apply mpred_ext; cancel|] end.
  setoid_rewrite (IHentries _ _ _ _ Hjoin eq_refl); auto; try omega.
  match goal with |- (?P1 * ?Q1 * (?P2 * ?Q2) * ?R) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2) * R); [apply mpred_ext; cancel|] end.
  erewrite !atomic_loc_hist_join by eauto.
  apply mpred_ext; entailer!.
  - intros.
    destruct (zlt i 0); [rewrite !Znth_underflow; simpl; auto|].
    destruct (eq_dec i 0).
    + subst; rewrite !Znth_0_cons; auto.
    + rewrite !Znth_pos_cons by omega; auto.
  - pose proof (H 0) as H0.
    rewrite !Znth_0_cons in H0; destruct H0; split; auto; split; auto.
    intro i; specialize (H (i + 1)).
    destruct (zlt i 0); [rewrite !Znth_underflow; simpl; auto|].
    rewrite !Znth_pos_cons, Z.add_simpl_r in H by omega; auto.
Qed.

Corollary atomic_entries_join_nil : forall sh1 sh2 sh entries ghosts
  (Hjoin : sepalg.join sh1 sh2 sh) (Hlen : Zlength entries = size) (Hleng : Zlength ghosts = size)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_entries sh1 entries ghosts empty_hists * atomic_entries sh2 entries ghosts empty_hists =
  atomic_entries sh entries ghosts empty_hists.
Proof.
  intros; erewrite atomic_entries_join with (sh := sh)
    by (rewrite ?join_empty; rewrite ?Zlength_empty; auto; omega).
  rewrite prop_true_andp; eauto.
  intro; rewrite Znth_repeat; simpl; auto.
Qed.

Lemma join_hists_length : forall h1 h2, Zlength h1 = Zlength h2 ->
  Zlength (join_hists h1 h2) = Zlength h1.
Proof.
  induction h1; auto; simpl; intros.
  destruct h2; [apply Zlength_nil_inv in H; discriminate|].
  destruct a, p; rewrite !Zlength_cons in *; rewrite IHh1; auto; omega.
Qed.

Corollary fold_join_hists_length : forall lh h, Forall (fun h' => Zlength h' = Zlength h) lh ->
  Zlength (fold_right join_hists h lh) = Zlength h.
Proof.
  induction lh; auto; simpl; intros.
  inv H.
  rewrite join_hists_length; auto.
  rewrite IHlh; auto.
Qed.

Corollary join_hists_empty_length : forall lh, Forall (fun h => Zlength h = size) lh ->
  Zlength (fold_right join_hists empty_hists lh) = size.
Proof.
  intros; rewrite fold_join_hists_length.
  - apply Zlength_empty.
  - eapply Forall_impl; [|eauto].
    intros; rewrite Zlength_empty; auto.
Qed.

Lemma join_empty_r : forall h, Zlength h = size -> join_hists h empty_hists = h.
Proof.
  intros.
  rewrite Zlength_correct in H.
  assert (length h = Z.to_nat size) as Hlen by Omega0.
  forget (Z.to_nat size) as n; clear H.
  revert dependent h; induction n; destruct h; auto; intros; inv Hlen; simpl.
  destruct p; rewrite IHn, !app_nil_r; auto.
Qed.

Lemma join_hists_assoc : forall a b c, join_hists a (join_hists b c) = join_hists (join_hists a b) c.
Proof.
  induction a; auto; simpl; intros.
  destruct a, b; auto; simpl.
  destruct p, c; auto; simpl.
  destruct p; rewrite IHa, !app_assoc; auto.
Qed.

Lemma join_hists_base : forall l h, Zlength h = size ->
  fold_right join_hists (join_hists h empty_hists) l = join_hists (fold_right join_hists empty_hists l) h.
Proof.
  induction l; simpl; intros.
  - rewrite join_empty, join_empty_r; auto.
  - rewrite IHl, join_hists_assoc; auto.
Qed.

Lemma add_rest_hists : forall k i h h' (Hrest : forall j,
  (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
  (~ In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], []))) j (Hj : j <> i),
  exists rest, Znth j h' ([], []) = (fst (Znth j h ([], [])) ++ rest, snd (Znth j h ([], []))) /\
    Forall (fun e => forall v, ~writes e v) (map snd rest).
Proof.
  intros.
  specialize (Hrest j).
  destruct (in_dec Z_eq_dec j (indices (hash k) i)).
  - destruct (Znth j h' ([], [])).
    destruct Hrest as ((r & ? & Hi1 & ? & ? & Hi2 & _) & _); auto.
    simpl in *; rewrite Hi2.
    destruct Hi1 as [Hi1 | Hi1]; apply add_events_add in Hi1; destruct Hi1 as (rest & ? & Hsnd); subst;
      exists rest; split; auto; rewrite Hsnd; repeat constructor; auto; simpl.
    intros ? (? & ?).
    absurd (r = 0); auto; apply repr_inj_signed; auto; congruence.
  - destruct Hrest as (_ & Hrest); rewrite Hrest by auto.
    destruct (Znth j h ([], [])); exists []; rewrite app_nil_r; simpl; auto.
Qed.

Lemma key_hists_fail : forall h k v i h' j (Hfail : add_item_trace h k v i false h')
  (Hk : k <> 0) (Hrep : repable_signed k),
  exists rest, Znth j h' ([], []) = (fst (Znth j h ([], [])) ++ rest, snd (Znth j h ([], []))) /\
    Forall (fun e => forall v, ~writes e v) (map snd rest).
Proof.
  intros.
  destruct (eq_dec j i).
  - destruct Hfail as (? & ? & Hi & _).
    subst; destruct (Znth i h ([], [])), (Znth i h' ([], [])); simpl in *.
    destruct Hi as ([Hi1 | Hi1] & ? & ?); apply add_events_add in Hi1; destruct Hi1 as (rest & ? & Hsnd); subst;
      exists rest; split; auto; rewrite Hsnd; repeat constructor; auto; simpl.
    intros ? (? & ?).
    contradiction Hk; apply repr_inj_signed; auto; congruence.
  - destruct Hfail as (? & ? & _ & Hrest).
    eapply add_rest_hists; eauto.
Qed.

Lemma add_item_trace_map : forall h k v i s h' (Hlenh : Zlength h = size)
  (Htrace : add_item_trace h k v i s h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  let m' := make_map (upd_Znth i h' (Znth i h ([], []))) in
    map_incl (make_map h) m' /\ lookup m' k = Some i /\
    if s then get (make_map h) k = None /\ make_map h' = upd_Znth i m' (k, v)
    else make_map h' = upd_Znth i m' (k, make_int (value_of_hist (snd (Znth i h' ([], []))))).
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto; congruence. }
  split.
  - intros k0 v0 j Hk0 Hj.
    exploit (Znth_inbounds j (make_map h) (0, 0)).
    { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
    intro; unfold make_map in *.
    rewrite Zlength_map in *.
    rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
    subst m'; rewrite Znth_map with (d' := ([], [])) by (rewrite upd_Znth_Zlength; omega).
    destruct (eq_dec j i); [subst; rewrite upd_Znth_same, Hhi by omega; auto|].
    rewrite upd_Znth_diff by (auto; omega).
    specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i));
      [|destruct Hrest as (_ & ->); auto].
    destruct Hrest as ((r1 & ? & Hcase & ? & ? & -> & Heq) & _); auto; simpl in *.
    assert (value_of_hist (fst (Znth j h ([], []))) <> vint 0).
    { intro X; rewrite X in Hk0; contradiction Hk0; auto. }
    destruct Hcase as [Hi1 | Hi1]; rewrite (add_events_last _ _ _ Hi1); simpl; try discriminate;
      rewrite Heq; auto.
  - assert (0 <= i < Zlength h') by (rewrite Hlen; auto).
    split.
    + subst m'; unfold lookup, make_map.
      assert (i = ((i - hash k) mod size + hash k) mod size) as Hmod.
      { rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small by omega; auto. }
      pose proof (hash_range k).
      assert (Zlength (map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs))))
              (upd_Znth i h' (hk, hv))) = size) as Hlen1.
      { rewrite Zlength_map, upd_Znth_Zlength; auto; omega. }
      erewrite index_of'_succeeds; simpl.
      f_equal; symmetry; apply Hmod.
      { rewrite Zlength_rebase; rewrite ?Zlength_map, ?upd_Znth_Zlength; auto;
          replace (Zlength h') with size; auto; try omega.
        apply Z_mod_lt, size_pos. }
      { rewrite Forall_forall; intros x Hin.
        apply In_Znth with (d := (0, 0)) in Hin; destruct Hin as (j & Hj & Hx).
        exploit (Z_mod_lt (i - hash k) size); [apply size_pos | intro].
        rewrite Zlength_sublist in Hj; rewrite ?Zlength_rebase; rewrite ?Hlen1; try (simpl in *; omega).
        rewrite Znth_sublist, Z.add_0_r in Hx by (auto; omega).
        rewrite Znth_rebase in Hx by (simpl in *; omega).
        rewrite Hlen1, Znth_map with (d' := ([], [])) in Hx.
        subst x; simpl.
        specialize (Hrest ((j + hash k) mod size)); destruct Hrest as ((r1 & ? & Hcase & ? & ? & ?) & _).
        { unfold indices; rewrite in_map_iff.
          exists j; split; [rewrite Z.add_comm; auto|].
          rewrite In_upto, Z2Nat.id; omega. }
        rewrite upd_Znth_diff'; auto.
        destruct Hcase as [Hj1 | Hj1]; setoid_rewrite (add_events_last _ _ _ Hj1); try discriminate; simpl;
          rewrite Int.signed_repr; auto.
        * intro X; rewrite <- X, Zminus_mod_idemp_l, Z.add_simpl_r, Z.sub_0_r, Zmod_small in Hj; try omega.
          destruct Hj; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos.
        * rewrite upd_Znth_Zlength by auto.
          replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos. }
      { rewrite <- Hlen1, Znth_rebase', Znth_map with (d' := ([], [])); simpl;
          rewrite ?Zlength_map, ?upd_Znth_Zlength; auto; try (simpl in *; omega).
        rewrite upd_Znth_same by auto; simpl.
        destruct s; [destruct Hi as (? & ? & ->); auto|].
        destruct Hi as (? & ? & Hr0).
        destruct (eq_dec (value_of_hist hk) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto; simpl.
        rewrite Int.signed_repr; auto. }
    + subst m'; unfold make_map; rewrite <- upd_Znth_map; destruct s; [split|].
      * unfold get, lookup.
        pose proof (index_of'_spec k (rebase (make_map h) (hash k))) as Hspec.
        unfold make_map in *; destruct (index_of' _ _); auto; simpl.
        assert (0 <= hash k < Zlength (make_map h)); unfold make_map in *.
        { rewrite Zlength_map, Hlenh; apply Z_mod_lt, size_pos. }
        rewrite Znth_map with (d' := ([], [])) by (rewrite Hlenh; apply Z_mod_lt, size_pos).
        destruct (eq_dec _ _); auto.
        destruct Hspec as (? & Hz & Hall).
        eapply Forall_sublist_le in Hall; rewrite ?Znth_rebase' with (i := i); auto; try omega.
        rewrite Zlength_rebase in * by auto.
        rewrite Znth_rebase, Znth_map with (d' := ([], [])) in Hz
          by (auto; rewrite Zlength_map; apply Z_mod_lt; omega); simpl in Hz.
        rewrite Zlength_map in *.
        rewrite Hlenh in *; destruct (eq_dec ((z + hash k) mod size) i).
        { simpl in e; rewrite e, Hhi in n; simpl in n.
          destruct Hi as (? & ? & Hzero); rewrite Hzero in n; contradiction. }
        destruct (eq_dec z ((i - hash k) mod size)).
        { subst z; contradiction n0.
          rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto. }
        destruct (Hrest ((z + hash k) mod size)) as ((r0 & ? & ? & ? & Hrk & ? & Hr0) & ?).
        { unfold indices; rewrite in_map_iff.
          do 2 eexists; [rewrite Z.add_comm; eauto|].
          rewrite In_upto, Z2Nat.id; omega. }
        destruct Hz as [Hz | Hz]; [|contradiction].
        simpl in *; destruct (value_of_hist (fst _)); try contradiction; simpl in Hz; subst.
        subst; destruct (eq_dec (Vint i0) (vint 0)).
        { inv e; contradiction Hk; rewrite Int.signed_repr; auto. }
        assert (Vint i0 = vint r0) as Heq by auto.
        inv Heq; contradiction Hrk; rewrite Int.signed_repr; auto.
        { rewrite Zlength_map, Hlenh; apply Z_mod_lt, size_pos. }
        { rewrite Znth_map', Hhi; simpl.
          destruct Hi as (? & ? & ->); tauto. }
        { rewrite Zlength_map; auto. }
      * erewrite upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map; auto.
        rewrite Znth_map'.
        destruct Hi as (Hi1 & Hi2 & ?).
        rewrite (add_events_last _ _ _ Hi1), (add_events_last _ _ _ Hi2); try discriminate; simpl.
        rewrite !Int.signed_repr; auto.
      * erewrite upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map; auto.
        rewrite Znth_map'; f_equal.
        destruct Hi as ([Hi1 | Hi1] & ? & ?); rewrite (add_events_last _ _ _ Hi1); try discriminate; simpl;
          rewrite Int.signed_repr; auto.
Qed.

Lemma join_empty_hists : forall h n, Zlength h = size -> fold_right join_hists h (repeat empty_hists n) = h.
Proof.
  induction n; auto; simpl; intro.
  rewrite join_empty; auto.
  rewrite fold_join_hists_length; auto.
  apply Forall_repeat; rewrite Zlength_repeat, Z2Nat.id; auto.
  pose proof size_pos; omega.
Qed.

Lemma Znth_join_hists : forall i lh (Hlen : Forall (fun h => Zlength h = size) lh),
  Znth i (fold_right join_hists empty_hists lh) ([], []) =
  (concat (map fst (map (fun h => Znth i h ([], [])) lh)),
   concat (map snd (map (fun h => Znth i h ([], [])) lh))).
Proof.
  induction lh; simpl; intro.
  - rewrite Znth_repeat; auto.
  - inv Hlen.
    rewrite join_hists_spec by (rewrite join_hists_empty_length; auto).
    rewrite IHlh by auto; reflexivity.
Qed.

Lemma add_items_hist_length : forall h lr, Forall (fun '(la, h') => add_items_trace h la h') lr ->
  Forall (fun h' => Zlength h' = Zlength h) (map snd lr).
Proof.
  intros.
  rewrite Forall_map; eapply Forall_impl; [|eauto].
  simpl; intros (?, ?) ?.
  eapply add_items_length; eauto.
Qed.

Corollary add_items_empty_hist_length : forall lr,
  Forall (fun '(la, h') => add_items_trace empty_hists la h') lr ->
  Forall (fun h' => Zlength h' = size) (map snd lr).
Proof.
  intros.
  eapply Forall_impl, add_items_hist_length; [|eauto].
  intros; rewrite <- Zlength_empty; auto.
Qed.

Definition hists_mono (h1 h2 : list (hist * hist)) := Forall2 (fun a b =>
  (exists l, fst b = fst a ++ l) /\ (exists l, snd b = snd a ++ l)) h1 h2.

Instance hists_mono_refl : RelationClasses.Reflexive hists_mono.
Proof.
  intro; unfold hists_mono; rewrite Forall2_eq_upto with (d1 := ([], []))(d2 := ([], [])); split; auto.
  rewrite Forall_forall; intros j Hin; rewrite In_upto, Z2Nat.id in Hin by (apply Zlength_nonneg).
  split; exists []; rewrite app_nil_r; auto.
Qed.
Hint Resolve hists_mono_refl.

Instance hists_mono_trans : RelationClasses.Transitive hists_mono.
Proof.
  intro x; induction x; intros ?? H; inv H; intro H; inv H; auto.
  constructor; [|eapply IHx; eauto].
  match goal with H : (exists l, fst y = _ ++ l) /\ _ |- _ => destruct H as ((? & ->) & (? & ->)) end.
  match goal with H : (exists l, fst y0 = _ ++ l) /\ _ |- _ => destruct H as ((? & ->) & (? & ->)) end.
  rewrite <- !app_assoc; eauto.
Qed.

Lemma add_item_trace_mono : forall h k v i s h', add_item_trace h k v i s h' -> hists_mono h h'.
Proof.
  intros; destruct H as (? & ? & Hi & Hrest).
  unfold hists_mono; rewrite Forall2_eq_upto with (d1 := ([], []))(d2 := ([], [])); split; auto.
  rewrite Forall_forall; intros j Hin; rewrite In_upto, Z2Nat.id in Hin by omega.
  destruct (eq_dec j i).
  - subst; destruct (Znth i h ([], [])), s.
    + destruct Hi as (Hi1 & Hi2 & ?); apply add_events_add in Hi1; apply add_events_add in Hi2.
      destruct Hi1 as (? & ? & ?); destruct Hi2 as (? & ? & ?); eauto.
    + destruct Hi as (Hi & -> & ?); split; [|exists []; rewrite app_nil_r; auto].
      destruct Hi as [Hi | Hi]; apply add_events_add in Hi; destruct Hi as (? & ? & ?); eauto.
  - exploit add_rest_hists; eauto; intros (? & -> & ?); simpl.
    split; eexists; eauto.
    rewrite app_nil_r; auto.
Qed.

Corollary add_items_trace_mono : forall h la h', add_items_trace h la h' ->
  hists_mono h h'.
Proof.
  induction 1; auto.
  etransitivity; eauto; eapply add_item_trace_mono; eauto.
Qed.

Lemma remove_last_full_hist : forall lh h j h' k v i k' i' (Hj : 0 <= j < Zlength lh) (Hh : Znth j lh [] = h)
  (Hi' : 0 <= i' < Zlength h) (Hadd : add_item_trace h' k v i false h) (Hk : k <> 0) (Hrep : repable_signed k)
  (Hfull : full_hist' (concat (map fst (map (fun h => Znth i' h ([], [])) lh))) k'),
  full_hist' (concat (upd_Znth j (map fst (map (fun h => Znth i' h ([], [])) lh))
    (fst (Znth i' h' ([], []))))) k'.
Proof.
  intros.
  apply key_hists_fail with (j := i') in Hadd; auto.
  destruct Hadd as (? & Heq & Hfail).
  eapply full_hist'_drop; eauto.
  - eapply concat_less_incl.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, Znth_map', Hh, Heq by (rewrite Zlength_map; auto); simpl; eauto.
  - rewrite concat_map in *.
    rewrite <- upd_Znth_map.
    eapply NoDup_concat_less.
    + destruct Hfull as (? & Hl & ?).
      rewrite <- concat_map; eapply hist_list'_NoDup; eauto.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, !Znth_map', Hh, Heq by (rewrite !Zlength_map; auto); simpl.
      rewrite map_app; auto.
  - intros t e Hin Hout.
    rewrite in_concat in Hin, Hout.
    destruct Hin as (? & ? & Hin).
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    apply In_Znth with (d := []) in Hin; destruct Hin as (j' & ? & Hj').
    destruct (eq_dec j' j); subst.
    + rewrite Heq in H; simpl in H.
      rewrite in_app in H; destruct H.
      * contradiction Hout.
        do 2 eexists; eauto.
        apply upd_Znth_In.
      * rewrite Forall_map, Forall_forall in Hfail; specialize (Hfail _ H); auto.
    + contradiction Hout.
      do 2 eexists; eauto.
      rewrite upd_Znth_map, in_map_iff; do 2 eexists; eauto.
      rewrite upd_Znth_map with (f := fun h => Znth i' h ([], [])), in_map_iff; do 2 eexists; eauto.
      erewrite <- upd_Znth_diff with (j0 := j); auto.
      apply Znth_In; rewrite upd_Znth_Zlength; auto.
Qed.

Lemma remove_last_full_hist' : forall lh h j h' k v i k' i' (Hj : 0 <= j < Zlength lh) (Hh : Znth j lh [] = h)
  (Hi' : 0 <= i' < Zlength h) (Hadd : add_item_trace h' k v i true h) (Hk : k <> 0) (Hrep : repable_signed k)
  (Hfull : full_hist' (concat (map fst (map (fun h => Znth i' h ([], [])) lh))) k') (Hneq : i' <> i),
  full_hist' (concat (upd_Znth j (map fst (map (fun h => Znth i' h ([], [])) lh))
    (fst (Znth i' h' ([], []))))) k'.
Proof.
  intros.
  destruct Hadd as (? & ? & _ & Hrest); apply add_rest_hists with (j := i') in Hrest; auto.
  destruct Hrest as (? & Heq & Hfail).
  eapply full_hist'_drop; eauto.
  - eapply concat_less_incl.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, Znth_map', Hh, Heq by (rewrite Zlength_map; auto); simpl; eauto.
  - rewrite concat_map in *.
    rewrite <- upd_Znth_map.
    eapply NoDup_concat_less.
    + destruct Hfull as (? & Hl & ?).
      rewrite <- concat_map; eapply hist_list'_NoDup; eauto.
    + rewrite !Zlength_map; auto.
    + erewrite Znth_map, !Znth_map', Hh, Heq by (rewrite !Zlength_map; auto); simpl.
      rewrite map_app; auto.
  - intros t e Hin Hout.
    rewrite in_concat in Hin, Hout.
    destruct Hin as (? & Hin0 & Hin).
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    apply In_Znth with (d := []) in Hin; destruct Hin as (j' & ? & Hj').
    destruct (eq_dec j' j); subst.
    + rewrite Heq in Hin0; simpl in Hin0.
      rewrite in_app in Hin0; destruct Hin0 as [|Hin0].
      * contradiction Hout.
        do 2 eexists; eauto.
        apply upd_Znth_In.
      * rewrite Forall_map, Forall_forall in Hfail; specialize (Hfail _ Hin0); auto.
    + contradiction Hout.
      do 2 eexists; eauto.
      rewrite upd_Znth_map, in_map_iff; do 2 eexists; eauto.
      rewrite upd_Znth_map with (f := fun h => Znth i' h ([], [])), in_map_iff; do 2 eexists; eauto.
      erewrite <- upd_Znth_diff with (j0 := j); auto.
      apply Znth_In; rewrite upd_Znth_Zlength; auto.
Qed.

Lemma add_key_success : forall la h' t e i v (Hadd : add_items_trace empty_hists la h')
  (Hin : In (t, e) (fst (Znth i h' ([], [])))) (Hval : writes e v)
  (Hnzk : Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) la),
  exists k v', In (k, v', i, true) la /\ v = vint k /\ e = CAS (vint 0) (vint 0) (vint k) /\ repable_signed k.
Proof.
  intros; remember empty_hists as h0; induction Hadd; subst.
  - rewrite Znth_repeat in Hin; contradiction.
  - rewrite Forall_app in Hnzk; destruct Hnzk as (? & Hnzk); inversion Hnzk as [|?? Hk].
    destruct Hk; subst.
    assert (0 <= i < Zlength h'').
    { apply Znth_inbounds with (d := ([], [])).
      intro X; rewrite X in Hin; contradiction. }
    assert (0 <= i < Zlength h').
    { destruct Hadd0; omega. }
    destruct (in_dec (EqDec_prod _ _ _ _) (t, e) (fst (Znth i h' ([], [])))).
    { exploit IHHadd; eauto.
      intros (? & ? & ? & ?); do 2 eexists; rewrite in_app; eauto. }
    destruct Hadd0 as (? & ? & Hi & Hrest).
    destruct (eq_dec i0 i).
    + subst; destruct (Znth i h' ([], [])).
      destruct s.
      * destruct Hi as (Hi1 & ? & _).
        apply add_events_add in Hi1; destruct Hi1 as (x & Happ & Hsnd); rewrite Happ, in_app in Hin.
        destruct Hin as [? | Hin]; [contradiction|].
        assert (In e (map snd x)) as Hin' by (rewrite in_map_iff; do 2 eexists; eauto; auto).
        rewrite Hsnd in Hin'; destruct Hin' as [Heq | [Heq | Heq]]; subst; try contradiction.
        simpl in Hval; destruct Hval.
        subst; do 2 eexists; rewrite in_app; simpl; split; eauto.
      * destruct Hi as ([Hi1 | Hi1] & ? & ?); apply add_events_add in Hi1; destruct Hi1 as (x & Happ & Hsnd);
          rewrite Happ, in_app in Hin; destruct Hin as [? | Hin]; try contradiction;
          assert (In e (map snd x)) as Hin' by (rewrite in_map_iff; do 2 eexists; eauto; auto);
          rewrite Hsnd in Hin'; simpl in Hin'; decompose [or] Hin'; subst; try contradiction.
        simpl in Hval; destruct Hval; subst.
        absurd (k = 0); auto; apply repr_inj_signed; auto; congruence.
    + exploit add_rest_hists; eauto; intros (? & Hh & Hw); rewrite Hh in Hin.
      simpl in Hin; rewrite in_app in Hin; destruct Hin as [|Hin]; [contradiction|].
      rewrite Forall_map, Forall_forall in Hw; exploit (Hw _ Hin); eauto; contradiction.
Qed.

Lemma add_val_success : forall la h' t e i v (Hadd : add_items_trace empty_hists la h')
  (Hin : In (t, e) (snd (Znth i h' ([], [])))) (Hval : value_of e = vint v) (Hv : repable_signed v)
  (Hrep : Forall (fun x => let '(_, v, _, _) := x in repable_signed v) la),
  exists k, In (k, v, i, true) la /\
    exists t', In (t', CAS (vint 0) (vint 0) (vint k)) (fst (Znth i h' ([], []))).
Proof.
  intros; remember empty_hists as h0; induction Hadd; subst.
  - rewrite Znth_repeat in Hin; contradiction.
  - rewrite Forall_app in Hrep; destruct Hrep as (? & Hrep); inv Hrep.
    assert (0 <= i < Zlength h'').
    { apply Znth_inbounds with (d := ([], [])).
      intro X; rewrite X in Hin; contradiction. }
    assert (0 <= i < Zlength h').
    { destruct Hadd0; omega. }
    destruct (in_dec (EqDec_prod _ _ _ _) (t, e) (snd (Znth i h' ([], [])))).
    { exploit IHHadd; eauto.
      intros (? & ? & ? & ?); eexists; rewrite in_app; split; eauto.
      eapply add_item_trace_mono, Forall2_Znth with (i2 := i) in Hadd0; auto.
      eexists; destruct Hadd0 as ((? & X) & _); rewrite X, in_app; eauto. }
    destruct Hadd0 as (? & ? & Hi & Hrest).
    destruct (eq_dec i0 i).
    + subst; destruct (Znth i h' ([], [])).
      destruct s.
      * destruct Hi as (Hi1 & Hi2 & _).
        apply add_events_add in Hi2; destruct Hi2 as (x & Happ & Hsnd); rewrite Happ, in_app in Hin.
        destruct Hin as [? | Hin]; [contradiction|].
        assert (In e (map snd x)) as Hin' by (rewrite in_map_iff; do 2 eexists; eauto; auto).
        rewrite Hsnd in Hin'; simpl in Hin'; decompose [or] Hin'; subst; try contradiction.
        simpl in Hval; assert (v0 = v) by (apply repr_inj_signed; auto; congruence).
        subst; eexists; rewrite in_app; simpl; split; eauto.
        eapply add_events_in in Hi1; [destruct Hi1 as (? & ? & ?); eauto | simpl; auto].
      * destruct Hi as (? & ? & ?); subst; contradiction.
    + exploit add_rest_hists; eauto; intros (? & Hi2 & ?); rewrite Hi2 in Hin; contradiction.
Qed.

Lemma writes_val : forall i e h v v', writes e v -> apply_hist i (h ++ [e]) = Some v' -> v' = v.
Proof.
  intros; rewrite apply_hist_app in *.
  destruct (apply_hist i h); [|discriminate].
  exploit apply_one_value; eauto.
  destruct e; simpl in *; try contradiction; subst; auto.
  destruct H; subst.
  rewrite eq_dec_refl; auto.
Qed.

Lemma apply_no_write : forall i h l v (Hl : hist_list' h l) (Hv : apply_hist i l = Some v)
  (Hh : Forall (fun p => ~writes (snd p) v) h), v = i /\ Forall (fun e => forall w, ~writes e w) l.
Proof.
  induction 1; simpl; intros.
  - inv Hv; auto.
  - assert (forall w, writes e w -> w = v) as Hwrite.
    { intros; symmetry; eapply writes_val; eauto. }
    rewrite apply_hist_app in Hv; destruct (apply_hist i l) eqn: Hv'; [|discriminate].
    subst; rewrite Forall_app in Hh; destruct Hh as (? & Hh); inv Hh.
    destruct (eq_dec v0 v).
    + subst; exploit IHHl; auto.
      { rewrite Forall_app; auto. }
      intros (? & ?); rewrite Forall_app; repeat constructor; auto.
      intros ? Hw; specialize (Hwrite _ Hw); subst; contradiction.
    + exploit change_implies_write; eauto; intros (? & [? | ?] & ?); subst; contradiction.
Qed.

Lemma one_CAS_succeeds : forall h v a t1 t2 b1 b2 (Hl : full_hist' h v) (Hin1 : In (t1, CAS a a b1) h)
  (Hin2 : In (t2, CAS a a b2) h) (Ha : Forall (fun p => ~writes (snd p) a) h),
  t1 = t2 /\ b1 = b2.
Proof.
  intros.
  destruct Hl as (l & Hl & Hv).
  revert dependent v; induction Hl; [contradiction|].
  subst; intros; rewrite !in_app in *; simpl in *.
  rewrite Forall_app in Ha; destruct Ha as (? & Ha); inv Ha.
  rewrite apply_hist_app in Hv.
  destruct (apply_hist (vint 0) l) eqn: Hv'; [|discriminate].
  destruct (in_dec (EqDec_prod _ _ _ _) (t1, CAS a a b1) (h1 ++ h2)),
    (in_dec (EqDec_prod _ _ _ _) (t2, CAS a a b2) (h1 ++ h2)); rewrite in_app in *.
  - eapply IHHl; eauto.
    rewrite Forall_app; auto.
  - destruct Hin2 as [? | [Heq | ?]]; try solve [contradiction n; auto]; inv Heq.
    simpl in Hv.
    destruct (eq_dec _ _); inv Hv.
    exploit apply_no_write; eauto.
    { rewrite Forall_app; auto. }
    intros (? & Hout); subst.
    assert (In (CAS (vint 0) (vint 0) b1) l) as Hin.
    { rewrite <- hist_list'_in; eauto.
      eexists; rewrite in_app; eauto. }
    rewrite Forall_forall in Hout; specialize (Hout _ Hin); simpl in Hout.
    exploit Hout; eauto; contradiction.
  - destruct Hin1 as [? | [Heq | ?]]; try solve [contradiction n; auto]; inv Heq.
    simpl in Hv.
    destruct (eq_dec _ _); inv Hv.
    exploit apply_no_write; eauto.
    { rewrite Forall_app; auto. }
    intros (? & Hout); subst.
    assert (In (CAS (vint 0) (vint 0) b2) l) as Hin.
    { rewrite <- hist_list'_in; eauto.
      eexists; rewrite in_app; eauto. }
    rewrite Forall_forall in Hout; specialize (Hout _ Hin); simpl in Hout.
    exploit Hout; eauto; contradiction.
  - destruct Hin1 as [? | [Heq | ?]]; try solve [contradiction n; auto]; inv Heq.
    destruct Hin2 as [? | [Heq | ?]]; try solve [contradiction n0; auto]; inv Heq; auto.
Qed.

Lemma timestamp_unique : forall (h : list hist) l t e1 e2 i1 i2 (Hl : hist_list' (concat h) l)
  (Ht1 : In (t, e1) (Znth i1 h [])) (Ht2 : In (t, e2) (Znth i2 h [])), i1 = i2.
Proof.
  intros.
  apply hist_list'_NoDup in Hl.
  exploit (Znth_inbounds i1 h).
  { intro X; rewrite X in Ht1; contradiction. }
  exploit (Znth_inbounds i2 h).
  { intro X; rewrite X in Ht2; contradiction. }
  intros.
  replace h with (sublist 0 i2 h ++ Znth i2 h [] :: sublist (i2 + 1) (Zlength h) h) in Ht1, Hl.
  rewrite concat_app in Hl; simpl in Hl; rewrite !map_app in Hl.
  exploit (Zlength_sublist 0 i2 h); try omega.
  rewrite Z.sub_0_r; intro Hsub.
  destruct (zlt i1 i2).
  - rewrite app_Znth1 in Ht1 by omega.
    rewrite app_assoc in Hl; apply NoDup_app in Hl; destruct Hl as (Hl & _).
    apply NoDup_app in Hl; destruct Hl as (_ & _ & Hl).
    exploit Hl; try contradiction.
    + rewrite in_map_iff; exists (t, e1); split; [reflexivity|].
      rewrite in_concat; do 2 eexists; eauto.
      apply Znth_In; omega.
    + simpl; rewrite in_map_iff; do 2 eexists; eauto; auto.
  - rewrite app_Znth2 in Ht1 by omega.
    rewrite Hsub in Ht1.
    destruct (eq_dec (i1 - i2) 0); [omega|].
    rewrite Znth_pos_cons in Ht1 by omega.
    apply NoDup_app in Hl; destruct Hl as (_ & Hl & _).
    apply NoDup_app in Hl; destruct Hl as (_ & _ & Hl).
    exploit Hl; try contradiction.
    + rewrite in_map_iff; exists (t, e2); split; [reflexivity | auto].
    + simpl; rewrite in_map_iff.
      exists (t, e1); split; auto.
      rewrite in_concat; do 2 eexists; eauto.
      apply Znth_In.
      rewrite Zlength_sublist; omega.
  - rewrite <- sublist_next, sublist_rejoin, sublist_same; auto; omega.
Qed.

Lemma add_items_Znth : forall h la h' j, add_items_trace h la h' -> 0 <= j < Zlength la ->
  exists h1 h2, let '(k, v, i, s) := Znth j la (0, 0, 0, false) in
    add_item_trace h1 k v i s h2 /\ hists_mono h h1 /\ hists_mono h2 h'.
Proof.
  induction 1; [rewrite Zlength_nil; omega | intros].
  rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
  destruct (eq_dec j (Zlength la)).
  - subst; do 2 eexists; rewrite !app_Znth2, Zminus_diag, Znth_0_cons by omega.
    split; eauto; split; auto; eapply add_items_trace_mono; eauto.
  - destruct IHadd_items_trace as (h1 & h2 & IH); [omega | exists h1, h2].
    rewrite !app_Znth1 by omega.
    destruct (Znth j la (0, 0, 0, false)) as (((?, ?), ?), ?); destruct IH as (? & ? & ?).
    split; [|split]; auto.
    etransitivity; eauto; eapply add_item_trace_mono; eauto.
Qed.

Lemma one_add_succeeds : forall lr keys
  (Hadd : Forall (fun '(la, h) => add_items_trace empty_hists la h) lr)
  (Hfullk : Forall2 full_hist' (map fst (fold_right join_hists empty_hists (map snd lr))) (map (fun x => vint x) keys))
  (Hkeys : Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
    (map fst (fold_right join_hists empty_hists (map snd lr))) keys)
  (Hrepk : Forall repable_signed keys)
  (Hnzk : Forall (fun x => Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) (fst x)) lr)
  k (Hin : In k (map fst (map fst (map fst (concat (map fst lr)))))),
  exists v i th t, In (k, v, i, true) (fst (Znth th lr ([], []))) /\
    In (t, CAS (vint 0) (vint 0) (vint k)) (fst (Znth i (snd (Znth th lr ([], []))) ([], []))).
Proof.
  intros.
  repeat (rewrite in_map_iff in Hin; destruct Hin as ((?, ?) & ? & Hin); simpl in *; subst).
  rewrite in_concat in Hin; destruct Hin as (? & Hin0 & Hin); subst.
  rewrite in_map_iff in Hin; destruct Hin as ((la, h) & ? & Hin); subst.
  assert (repable_signed k /\ vint k <> vint 0) as (? & ?).
  { rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin).
    rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin0); destruct Hnzk as (Hk & ?).
    split; auto; intro; contradiction Hk; apply repr_inj_signed; auto; congruence. }
  exploit add_items_empty_hist_length; eauto; intro.
  destruct (existsb (Z.eqb k) keys) eqn: Hk.
  - rewrite existsb_exists in Hk.
    destruct Hk as (? & Hin' & Heq); rewrite Z.eqb_eq in Heq; symmetry in Heq; subst.
    apply In_Znth with (d := 0) in Hin'; destruct Hin' as (i & ? & Hi).
    eapply Forall2_Znth with (i0 := i) in Hfullk; [|rewrite (mem_lemmas.Forall2_Zlength Hfullk), Zlength_map; auto].
    destruct Hfullk as (l & Hl & Hv); rewrite Znth_map', Hi in Hv.
    rewrite Znth_map', Znth_join_hists in Hl by auto; simpl in Hl.
    apply change_implies_write in Hv; auto.
    destruct Hv as (w & Hinw & Hw).
    rewrite <- hist_list'_in in Hinw by eauto.
    destruct Hinw as (t & Hinw).
    rewrite in_concat in Hinw; destruct Hinw as (h' & Hinw & Hin2).
    repeat (rewrite in_map_iff in Hin2; destruct Hin2 as (? & ? & Hin2); subst).
    rewrite Forall_forall in Hadd; specialize (Hadd _ Hin2).
    destruct x as (la2, h2).
    exploit add_key_success; try apply Hadd; eauto.
    { rewrite Forall_forall in Hnzk; apply (Hnzk (la2, h2)); auto. }
    intros (k & ? & ? & ? & ? & ?); subst.
    assert (Znth i keys 0 = k).
    { apply repr_inj_signed; auto; congruence. }
    eapply In_Znth in Hin2; destruct Hin2 as (? & ? & Heq).
    subst; do 5 eexists; rewrite Heq; eauto.
  - rewrite Forall_forall in Hadd; specialize (Hadd _ Hin).
    eapply In_Znth in Hin0; destruct Hin0 as (j & ? & Hj).
    apply add_items_Znth with (j := j) in Hadd; auto.
    destruct Hadd as (h1 & h2 & Hadd); rewrite Hj in Hadd.
    destruct Hadd as ((? & ? & Hi & _) & Hh1 & Hh).
    assert (exists t e, In (t, e) (fst (Znth z h2 ([], []))) /\ value_of e = vint k) as (t & e & ? & He).
    { destruct (Znth z h1 ([], [])), b.
      + destruct Hi as (Hi1 & ? & ?); eapply add_events_in in Hi1; [|simpl; eauto].
        destruct Hi1 as (? & ? & ?); eauto.
      + destruct Hi as ([Hi1 | Hi1] & ? & ?); eapply add_events_in in Hi1; simpl; eauto;
          destruct Hi1 as (? & ? & ?); eauto. }
    clear Hi.
    assert (Zlength h1 = size) by (rewrite <- (mem_lemmas.Forall2_Zlength Hh1), Zlength_empty; auto).
    eapply Forall2_Znth with (i := z)(d2 := 0) in Hkeys;
      [|rewrite Zlength_map, join_hists_empty_length by auto; omega].
    rewrite Znth_map', Znth_join_hists in Hkeys by auto; simpl in Hkeys.
    exploit (Hkeys t e).
    { eapply Forall2_Znth with (i := z) in Hh; [|omega].
      rewrite in_concat; do 2 eexists; [|repeat (rewrite in_map_iff; do 2 eexists; eauto)].
      simpl; destruct Hh as ((? & ->) & _).
      rewrite in_app; eauto. }
    { intro X; rewrite X in He.
      absurd (vint k = vint 0); auto. }
    intro X; rewrite <- X in He.
    assert (Zlength keys = size).
    { erewrite <- Zlength_map, <- (mem_lemmas.Forall2_Zlength Hfullk), Zlength_map, join_hists_empty_length
        by auto; omega. }
    exploit existsb_nth; eauto.
    { apply Nat2Z.inj_lt; rewrite Z2Nat.id, <- Zlength_correct.
      instantiate (1 := z); omega.
      { tauto. } }
    rewrite nth_Znth with (d := 0), Z2Nat.id, Z.eqb_neq by tauto; intro Hn; contradiction Hn.
    apply repr_inj_signed; auto.
    { apply Forall_Znth; auto; omega. }
    congruence.
Qed.

Lemma only_one_add_succeeds : forall lr keys th1 th2 k v1 v2 i1 i2
  (Hadd : Forall (fun '(la, h) => add_items_trace empty_hists la h) lr)
  (Hfullk : Forall2 full_hist' (map fst (fold_right join_hists empty_hists (map snd lr))) (map (fun x => vint x) keys))
  (Hkeys : Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
    (map fst (fold_right join_hists empty_hists (map snd lr))) keys)
  (Hrepk : Forall repable_signed keys)
  (Hnzk : Forall (fun x => Forall (fun x => let '(k, _, _, _) := x in k <> 0 /\ repable_signed k) (fst x)) lr)
  (Hsucc1 : In (k, v1, i1, true) (fst (Znth th1 lr ([], []))))
  (Hsucc2 : In (k, v2, i2, true) (fst (Znth th2 lr ([], [])))),
  th1 = th2 /\ i1 = i2.
Proof.
  intros.
  assert (0 <= th1 < Zlength lr) as Hth1.
  { exploit (Znth_inbounds th1 lr ([], [])); auto.
    intro X; rewrite X in Hsucc1; contradiction. }
  assert (0 <= th2 < Zlength lr) as Hth2.
  { exploit (Znth_inbounds th2 lr ([], [])); auto.
    intro X; rewrite X in Hsucc2; contradiction. }
  pose proof (Forall_Znth _ _ _ ([], []) Hth1 Hadd) as Hadd1.
  pose proof (Forall_Znth _ _ _ ([], []) Hth2 Hadd) as Hadd2.
  destruct (Znth th1 lr ([], [])) as (la1, h1) eqn: Hr1,
           (Znth th2 lr ([], [])) as (la2, h2) eqn: Hr2; simpl in *.
  eapply In_Znth in Hsucc1; destruct Hsucc1 as (j1 & ? & Hj1).
  apply add_items_Znth with (j := j1) in Hadd1; auto.
  destruct Hadd1 as (ha1 & hb1 & Hadd1); rewrite Hj1 in Hadd1.
  destruct Hadd1 as ((? & ? & Hi1 & Hrest1) & Hha1 & Hhb1).
  eapply In_Znth in Hsucc2; destruct Hsucc2 as (j2 & ? & Hj2).
  apply add_items_Znth with (j := j2) in Hadd2; auto.
  destruct Hadd2 as (ha2 & hb2 & Hadd2); rewrite Hj2 in Hadd2.
  destruct Hadd2 as ((? & ? & Hi2 & Hrest2) & Hha2 & Hhb2).
  exploit add_items_empty_hist_length; eauto; intro.
  assert (Zlength ha1 = size) by (rewrite <- (mem_lemmas.Forall2_Zlength Hha1), Zlength_empty; auto).
  assert (Zlength ha2 = size) by (rewrite <- (mem_lemmas.Forall2_Zlength Hha2), Zlength_empty; auto).
  destruct (Znth i1 ha1 ([], [])) eqn: Hh1, (Znth i2 ha2 ([], [])) eqn: Hh2.
  destruct Hi1 as (Hi1 & _ & Hzero1).
  destruct Hi2 as (Hi2 & _ & Hzero2).
  eapply add_events_in in Hi1; [|simpl; eauto].
  destruct Hi1 as (t1 & ? & ?).
  eapply add_events_in in Hi2; [|simpl; eauto].
  destruct Hi2 as (t2 & ? & ?).
  assert (In (t1, CAS (vint 0) (vint 0) (vint k)) (fst (Znth i1 h1 ([], [])))).
  { eapply Forall2_Znth with (i := i1) in Hhb1; [|omega].
    destruct Hhb1 as ((? & ->) & _); rewrite in_app; eauto. }
  assert (In (t2, CAS (vint 0) (vint 0) (vint k)) (fst (Znth i2 h2 ([], [])))).
  { eapply Forall2_Znth with (i := i2) in Hhb2; [|omega].
    destruct Hhb2 as ((? & ->) & _); rewrite in_app; eauto. }
  assert (In h1 (map snd lr)) by (rewrite in_map_iff; do 2 eexists; [|apply Znth_In]; [rewrite Hr1|]; auto).
  assert (In h2 (map snd lr)) by (rewrite in_map_iff; do 2 eexists; [|apply Znth_In]; [rewrite Hr2|]; auto).
  destruct (eq_dec i1 i2).
  - split; auto.
    eapply Forall2_Znth with (i := i1) in Hfullk;
      [|rewrite Zlength_map, join_hists_empty_length by auto; omega].
    rewrite !Znth_map', Znth_join_hists in Hfullk by auto; simpl in Hfullk.
    instantiate (1 := 0) in Hfullk.
    exploit one_CAS_succeeds; eauto.
    { rewrite in_concat; exists (fst (Znth i1 h1 ([], []))); split; eauto.
      do 2 (rewrite in_map_iff; do 2 eexists; eauto). }
    { subst; rewrite in_concat; do 2 eexists; eauto.
      do 2 (rewrite in_map_iff; do 2 eexists; eauto). }
    { rewrite Forall_forall; intros (?, ?) Hink.
      rewrite in_concat in Hink; destruct Hink as (? & ? & Hink); subst.
      do 2 (rewrite in_map_iff in Hink; destruct Hink as (? & ? & Hink); subst).
      rewrite in_map_iff in Hink; destruct Hink as ((?, ?) & ? & Hink); subst.
      rewrite Forall_forall in Hadd; specialize (Hadd _ Hink); simpl in Hadd.
      rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hink).
      intro; exploit add_key_success; try apply Hadd; eauto.
      intros (k'' & ? & Hin' & ? & ? & ?); rewrite Forall_forall in Hnzk; specialize (Hnzk _ Hin').
      destruct Hnzk; absurd (k'' = 0); auto; apply repr_inj_signed; auto; congruence. }
    intros (? & ?); subst.
    destruct Hfullk as (? & ? & ?).
    eapply timestamp_unique; eauto.
    + erewrite Znth_map, !Znth_map', Hr1 by (rewrite !Zlength_map; auto); eauto.
    + erewrite Znth_map, !Znth_map', Hr2 by (rewrite !Zlength_map; auto); eauto.
  - set (i' := if zlt ((i1 - hash k) mod size) ((i2 - hash k) mod size) then i1 else i2).
    assert (0 <= i' < size) by (destruct (zlt _ _); subst i'; omega).
    assert (Zlength keys = size).
    { erewrite <- Zlength_map, <- (mem_lemmas.Forall2_Zlength Hfullk), Zlength_map, join_hists_empty_length;
        auto. }
    assert (Znth i' keys 0 = k); [|assert (exists k', Znth i' keys 0 = k' /\ k' <> k) as (? & ? & ?); [|omega]].
    + eapply Forall2_Znth with (i := i')(d2 := 0) in Hkeys.
      assert (exists t' h', In (t', CAS (vint 0) (vint 0) (vint k)) (fst (Znth i' h' ([], []))) /\
        In h' (map snd lr)) as (t' & h' & Hin & Hh').
      { destruct (zlt _ _); do 3 eexists; eauto. }
      assert (repable_signed k /\ vint k <> vint 0) as (? & ?).
      { eapply Forall_Znth with (i := th1) in Hnzk; auto.
        rewrite Hr1 in Hnzk; simpl in Hnzk.
        eapply Forall_Znth with (i := j1) in Hnzk; auto.
        rewrite Hj1 in Hnzk; destruct Hnzk as (Hz & ?); split; auto.
        intro; contradiction Hz; apply repr_inj_signed; auto; congruence. }
      exploit Hkeys.
      { rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite in_concat; do 2 eexists; eauto.
        repeat (rewrite in_map_iff; do 2 eexists; eauto). }
      { auto. }
      simpl; intro; apply repr_inj_signed; auto.
      { apply Forall_Znth; auto; omega. }
      congruence.
      { rewrite Zlength_map, join_hists_empty_length; auto. }
    + set (j' := if zlt ((i1 - hash k) mod size) ((i2 - hash k) mod size) then i2 else i1).
      assert (exists ha hb h', Zlength hb = size /\ hists_mono hb h' /\ In h' (map snd lr) /\ forall j,
        In j (indices (hash k) j') -> failed_CAS k (Znth j ha ([], [])) (Znth j hb ([], [])))
        as (ha & hb & h' & ? & Hh' & Hin' & Hrest).
      { destruct (zlt _ _); subst i'; [exists ha2, hb2, h2 | exists ha1, hb1, h1];
          repeat split; auto; try omega; intro; [apply Hrest2 | apply Hrest1]. }
      specialize (Hrest i'); destruct Hrest as (r & ? & Hi & ? & ? & ? & ?).
      { unfold indices; rewrite in_map_iff.
        exists ((i' - hash k) mod size); split.
        { rewrite Zplus_mod_idemp_r, Zplus_minus, Zmod_small; auto. }
        rewrite In_upto, Z2Nat.id by (apply Z_mod_lt, size_pos).
        destruct (zlt _ _); subst i' j'; split; try (apply Z_mod_lt, size_pos); try tauto.
        destruct (eq_dec ((i1 - hash k) mod size) ((i2 - hash k) mod size)); try omega.
        apply Zmod_plus_inv in e; [|apply size_pos].
        rewrite !Zmod_small in e; omega. }
      assert (exists t e, In (t, e) (fst (Znth i' hb ([], []))) /\ value_of e = vint r) as (? & ? & ? & ?).
      { destruct Hi as [Hi | Hi]; eapply add_events_in in Hi; simpl; eauto; destruct Hi as (? & ? & ?); eauto. }
      eapply Forall2_Znth with (i := i')(d2 := 0) in Hkeys.
      exploit Hkeys.
      { rewrite Znth_map', Znth_join_hists by auto; simpl.
        rewrite in_concat; exists (fst (Znth i' h' ([], []))); split.
        { eapply Forall2_Znth with (i := i') in Hh'; [|omega].
          destruct Hh' as ((? & ->) & _); rewrite in_app; eauto. }
        repeat (rewrite in_map_iff; do 2 eexists; eauto). }
      { intro; absurd (r = 0); auto; apply repr_inj_signed; auto; congruence. }
      intro; assert (Znth i' keys 0 = r); [|eauto].
      apply repr_inj_signed; auto.
      { apply Forall_Znth; auto; omega. }
      congruence.
      { rewrite Zlength_map, join_hists_empty_length; auto. }
Qed.

Transparent Znth.

Lemma add_three : forall lr lk lv (Hlen : Zlength lr = 3)
  (Hadd : Forall (fun '(h, li, ls) => add_items_trace (repeat ([], []) (Z.to_nat size))
     (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls) h) lr)
  (H3 : Forall (fun '(_, li, ls) => Zlength li = 3 /\ Zlength ls = 3) lr)
  (Hrepk : Forall repable_signed lk) (Hrepv : Forall repable_signed lv)
  (Hfullk : Forall2 full_hist (map fst (fold_right join_hists empty_hists (map fst (map fst lr)))) lk)
  (Hfullv : Forall2 full_hist (map snd (fold_right join_hists empty_hists (map fst (map fst lr)))) lv)
  (Hvalk : Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
     (map fst (fold_right join_hists empty_hists (map fst (map fst lr)))) lk),
  Zlength (filter id (concat (map snd lr))) = 3.
Proof.
  intros; set (lr' := map (fun '(h, li, ls) => (combine (combine (combine [1; 2; 3] [1; 1; 1]) li) ls, h)) lr).
  assert (map snd lr' = map fst (map fst lr)) as Hlr.
  { subst lr'; rewrite !map_map; apply map_ext.
    intros ((?, ?), ?); auto. }
  assert (Forall (fun '(la, h) => add_items_trace empty_hists la h) lr') as Hadd'.
  { subst lr'; rewrite Forall_map;
      match goal with H : Forall _ lr |- _ => eapply Forall_impl; [|apply H];
        intros ((?, ?), ?); solve [auto] end. }
  assert (Forall2 full_hist' (map fst (fold_right join_hists empty_hists
    (map snd lr'))) (map (fun x => vint x) lk)) as Hfullk'.
  { rewrite Hlr; eapply Forall2_map2, Forall2_impl; [intros; apply full_hist_weak; eauto | auto]. }
  assert (Forall2 (fun h v => forall t e, In (t, e) h -> value_of e <> vint 0 -> vint v = value_of e)
    (map fst (fold_right join_hists empty_hists (map snd lr'))) lk) as Hkeys.
  { rewrite Hlr; auto. }
  assert (Forall (fun x => Forall (fun '(k, _, _, _) => k <> 0 /\ repable_signed k) (fst x)) lr') as Hnzk.
  { subst lr'.
    rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (((?, ?), ?) & ? & Hin); subst.
    rewrite Forall_forall; intros (((?, ?), ?), ?) Hin'.
    do 3 apply in_combine_l in Hin'.
    destruct Hin' as [? | [? | [? | ?]]]; try contradiction; subst; repeat split; computable. }
  pose proof (one_add_succeeds _ _ Hadd' Hfullk' Hkeys Hrepk Hnzk) as Hone.
  assert (incl [1; 2; 3] (map fst (map fst (map fst (concat (map fst lr')))))) as Hks.
  { intros a Ha.
    subst lr'; destruct lr as [|((?, li), ls)]; [rewrite Zlength_nil in *; discriminate|]; simpl.
    repeat match goal with H : Forall _ (_ :: _) |- _ => inv H end.
    match goal with H : _ /\ _ |- _ => destruct H end.
    destruct li; [rewrite Zlength_nil in *; discriminate|].
    destruct ls; [rewrite Zlength_nil in *; discriminate | simpl].
    rewrite !Zlength_cons in *.
    destruct li; [rewrite Zlength_nil in *; discriminate|].
    destruct ls; [rewrite Zlength_nil in *; discriminate | simpl].
    rewrite !Zlength_cons in *.
    destruct li; [rewrite Zlength_nil in *; discriminate|].
    destruct ls; [rewrite Zlength_nil in *; discriminate | simpl].
    destruct Ha as [? | [? | [? | ?]]]; auto; contradiction. }
  rewrite !incl_cons_iff in Hks; destruct Hks as (Hk1 & Hk2 & Hk3 & _).
  generalize (Hone _ Hk1), (Hone _ Hk2), (Hone _ Hk3).
  intros (? & ? & th1 & ? & Hin1 & ?) (? & ? & th2 & ? & Hin2 & ?) (? & ? & th3 & ? & Hin3 & ?).
  assert (forall th, 0 <= th < Zlength lr -> Znth th lr' ([], []) = (map (fun j => (j + 1, 1,
    Znth j (snd (fst (Znth th lr ([], [], [])))) 0, Znth j (snd (Znth th lr ([], [], []))) false)) (upto 3),
    fst (fst (Znth th lr ([], [], []))))) as Hnth'.
  { subst lr'; intros.
    rewrite Znth_map with (d' := ([], [], [])) by auto.
    repeat match goal with H : Forall _ lr |- _ => eapply Forall_Znth with (i := th)(d := ([], [], [])) in H;
      [|auto] end.
    destruct (Znth th lr ([], [], [])) as ((h, li), ls) eqn: Hth.
    match goal with H : Zlength li = _ /\ _ |- _ => destruct H as (Hli & Hls) end.
    destruct li; [rewrite Zlength_nil in *; discriminate|].
    destruct ls; [rewrite Zlength_nil in *; discriminate | simpl].
    rewrite !Zlength_cons in *.
    destruct li; [rewrite Zlength_nil in *; discriminate|].
    destruct ls; [rewrite Zlength_nil in *; discriminate | simpl].
    rewrite !Zlength_cons in *.
    destruct li; [rewrite Zlength_nil in *; discriminate|].
    destruct ls; [rewrite Zlength_nil in *; discriminate | simpl].
    change (upto 3) with [0; 1; 2]; auto. }
  assert (Zlength lr' = Zlength lr) as Hlenr.
  { clear; subst lr'; rewrite Zlength_map; auto. }
  assert (0 <= th1 < Zlength lr).
  { rewrite <- Hlenr; apply Znth_inbounds with (d := ([], [])); intro X; rewrite X in Hin1; contradiction. }
  assert (0 <= th2 < Zlength lr).
  { rewrite <- Hlenr; apply Znth_inbounds with (d := ([], [])); intro X; rewrite X in Hin2; contradiction. }
  assert (0 <= th3 < Zlength lr).
  { rewrite <- Hlenr; apply Znth_inbounds with (d := ([], [])); intro X; rewrite X in Hin3; contradiction. }
  assert (forall th, 0 <= th < Zlength lr -> Zlength (fst (Znth th lr' ([], []))) = 3) as Hli.
  { intros; rewrite Hnth' by auto; simpl.
    rewrite Zlength_map; auto. }
  destruct (In_Znth _ _ (0, 0, 0, false) Hin1) as (j1 & ? & Hnth1).
  rewrite Hnth' in Hnth1 by auto; simpl in Hnth1.
  destruct (In_Znth _ _ (0, 0, 0, false) Hin2) as (j2 & ? & Hnth2).
  rewrite Hnth' in Hnth2 by auto; simpl in Hnth2.
  destruct (In_Znth _ _ (0, 0, 0, false) Hin3) as (j3 & ? & Hnth3).
  rewrite Hnth' in Hnth3 by auto; simpl in Hnth3.
  rewrite Hli in * by auto.
  erewrite Znth_map, Znth_upto in Hnth1, Hnth2, Hnth3 by (auto; simpl; omega).
  inv Hnth1; inv Hnth2; inv Hnth3.
  assert (j1 = 0) by omega; subst.
  assert (j2 = 1) by omega; subst.
  assert (j3 = 2) by omega; subst.
  assert (forall th, 0 <= th < Zlength lr -> Znth 0 (snd (Znth th lr ([], [], []))) false = true -> th = th1) as Hth1.
  { intros ?? Hsucc.
    exploit (only_one_add_succeeds lr' lk th th1); eauto; [|tauto].
    rewrite Hnth' by auto; simpl.
    rewrite in_map_iff; do 2 eexists; [rewrite Hsucc; eauto|].
    rewrite In_upto; simpl; computable. }
  assert (forall th, 0 <= th < Zlength lr -> Znth 1 (snd (Znth th lr ([], [], []))) false = true -> th = th2) as Hth2.
  { intros ?? Hsucc.
    exploit (only_one_add_succeeds lr' lk th th2); eauto; [|tauto].
    rewrite Hnth' by auto; simpl.
    rewrite in_map_iff; do 2 eexists; [rewrite Hsucc; eauto|].
    rewrite In_upto; simpl; computable. }
  assert (forall th, 0 <= th < Zlength lr -> Znth 2 (snd (Znth th lr ([], [], []))) false = true -> th = th3) as Hth3.
  { intros ?? Hsucc.
    exploit (only_one_add_succeeds lr' lk th th3); eauto; [|tauto].
    rewrite Hnth' by auto; simpl.
    rewrite in_map_iff; do 2 eexists; [rewrite Hsucc; eauto|].
    rewrite In_upto; simpl; computable. }
  assert (forall th, 0 <= th < Zlength lr -> Zlength (filter id (Znth th (map snd lr) [])) =
    (if eq_dec th th1 then 1 else 0) + (if eq_dec th th2 then 1 else 0) + (if eq_dec th th3 then 1 else 0)) as Hls.
  { intros ? Hth.
    specialize (Hth1 _ Hth); specialize (Hth2 _ Hth); specialize (Hth3 _ Hth).
    rewrite Znth_map with (d' := ([], [], [])) by auto.
    repeat match goal with H : Forall _ lr |- _ => eapply Forall_Znth with (i := th)(d := ([], [], [])) in H; [|auto] end.
    destruct (Znth th lr ([], [], [])) as ((h, li), ls) eqn: Hnth.
    match goal with H : Zlength _ = _ /\ _ |- _ => destruct H as (? & Hls) end.
    simpl; replace ls with [if eq_dec th th1 then true else false; if eq_dec th th2 then true else false; if eq_dec th th3 then true else false].
    { repeat if_tac; simpl; auto. }
    destruct ls; [rewrite Zlength_nil in Hls; discriminate | simpl; rewrite Zlength_cons in Hls].
    destruct ls; [rewrite Zlength_nil in Hls; discriminate | simpl; rewrite Zlength_cons in Hls].
    destruct ls; [rewrite Zlength_nil in Hls; discriminate | simpl; rewrite Zlength_cons in Hls].
    destruct ls; [|rewrite Zlength_cons in Hls; pose proof (Zlength_nonneg ls); omega].
    simpl in *; f_equal; [|f_equal].
    - destruct (eq_dec _ _); [subst; rewrite Hnth in *; simpl in *; auto|].
      destruct b; auto; contradiction.
    - destruct (eq_dec _ _); [subst; rewrite Hnth in *; simpl in *; auto|].
      destruct b0; auto; contradiction.
    - f_equal; destruct (eq_dec _ _); [subst; rewrite Hnth in *; simpl in *; auto|].
      destruct b1; auto; contradiction. }
  destruct lr as [|((?, ?), ls1)]; [rewrite Zlength_nil in *; discriminate|]; simpl in *.
  rewrite Zlength_cons in *; destruct lr as [|((?, ?), ls2)]; [rewrite Zlength_nil in *; discriminate|]; simpl in *.
  rewrite Zlength_cons in *; destruct lr as [|((?, ?), ls3)]; [rewrite Zlength_nil in *; discriminate|]; simpl in *.
  rewrite Zlength_cons in *; destruct lr; [|rewrite Zlength_cons in *; pose proof (Zlength_nonneg lr); omega].
  rewrite app_nil_r, !filter_app, !Zlength_app.
  generalize (Hls 0), (Hls 1), (Hls 2); unfold Znth; simpl.
  intros -> -> ->; auto.
  assert (forall i, 0 <= i < 3 ->
    (if eq_dec 0 i then 1 else 0) + (if eq_dec 1 i then 1 else 0) + (if eq_dec 2 i then 1 else 0) = 1) as Hsum.
  { intros; do 3 if_tac; omega. }
  rewrite Zlength_nil in *; simpl in *.
  generalize (Hsum th1), (Hsum th2), (Hsum th3); omega.
Qed.

Opaque combine.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  name m_entries _m_entries.
  name locksp _thread_locks.
  name resp _results.
  name keys _keys.
  name values _values.
  start_function.
  forward.
  forward_call m_entries.
  Intros x; destruct x as (entries, ghosts); simpl in *.
  destruct (split_shares 3 Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  rewrite <- seq_assoc.
  destruct (split_readable_share Tsh) as (sh1 & sh2 & ? & ? & ?); auto.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
    LOCAL (temp _total (vint 0); lvar _values (tarray tint 16384) values;
           lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs Ews (tarray tentry size) entries m_entries;
         atomic_entries Tsh entries ghosts empty_hists;
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         EX res : list val, !!(Zlength res = i) &&
           data_at Ews (tarray (tptr tint) 3) (res ++ repeat Vundef (Z.to_nat (3 - i))) resp *
           fold_right sepcon emp (map (data_at_ Tsh tint) res) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) res) *
         EX locks : list val, !!(Zlength locks = i) &&
           data_at Ews (tarray (tptr (Tstruct _lock_t noattr)) 3)
             (locks ++ repeat Vundef (Z.to_nat (3 - i))) locksp *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) locks) *
           fold_right sepcon emp (map (fun j => lock_inv Tsh (Znth j locks Vundef)
             (f_lock_pred sh2 (Znth j shs Ews) entries ghosts m_entries j locksp (Znth j locks Vundef)
              resp (Znth j res Vundef))) (upto (Z.to_nat i))))).
  { Exists (@nil val) (@nil val); go_lower; entailer'. }
  { (* first loop *)
    Intros res locks.
    forward_call (sizeof (Tstruct _lock_t noattr)).
    { simpl; computable. }
    Intro l.
    rewrite malloc_compat by (auto; exists 2; auto); Intros.
    rewrite memory_block_data_at_ by auto.
    forward.
    forward_call (sizeof tint).
    { simpl; computable. }
    Intro r.
    rewrite malloc_compat by (auto; exists 2; auto); Intros.
    rewrite memory_block_data_at_ by auto.
    forward.
    focus_SEP 3.
    forward_call (l, Tsh, f_lock_pred sh2 (Znth i shs Ews) entries ghosts m_entries i locksp l resp r).
    { entailer!.
      destruct l; try contradiction; auto. }
    { apply sepcon_derives; [apply lock_struct | cancel_frame]. }
    Exists (res ++ [r]) (locks ++ [l]); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    go_lower; entailer'.
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
    rewrite <- !sepcon_assoc, (sepcon_comm _ (@data_at CompSpecs Ews (tarray tentry size) entries m_entries)),
      !sepcon_assoc; apply sepcon_derives; [auto|].
    rewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_entries Tsh entries ghosts empty_hists)), !sepcon_assoc;
      apply sepcon_derives; [auto|].
    rewrite ?sepcon_emp, ?emp_sepcon; rewrite ?sepcon_assoc.
    rewrite <- !sepcon_assoc.
    match goal with |- _ |-- ?P * ?Q => rewrite (sepcon_comm P Q) end.
    rewrite !sepcon_assoc; apply sepcon_derives; [auto|].
    rewrite <- 2sepcon_assoc, sepcon_comm, !sepcon_assoc.
    destruct r; try contradiction.
    destruct l; try contradiction.
    cancel.
    apply sepcon_list_derives; rewrite !Zlength_map, !Zlength_upto, <- Zlength_correct.
    { rewrite Z2Nat.id; auto; omega. }
    intros.
    erewrite !Znth_map, !Znth_upto by (rewrite ?Zlength_upto, <- ?Zlength_correct, ?Z2Nat.id; auto; omega).
    rewrite !app_Znth1 by omega; auto. }
  Intros res locks.
  rewrite !app_nil_r.
  assert_PROP (Zlength entries = size) by entailer!.
  rewrite <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z, EX sh : share,
    PROP (sepalg_list.list_join sh0 (sublist i 3 shs) sh)
    LOCAL (temp _total (vint 0); lvar _values (tarray tint 16384) values;
           lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries m_entries;
         EX sh' : share, !!(sepalg.join sh (Share.comp Ews) sh') && atomic_entries sh' entries ghosts empty_hists;
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         data_at sh (tarray (tptr tint) 3) res resp;
         fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i 3 res));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) res);
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) locks);
         fold_right sepcon emp (map (fun j => lock_inv (if zlt j i then sh1 else Tsh) (Znth j locks Vundef)
           (f_lock_pred sh2 (Znth j shs Ews) entries ghosts m_entries j locksp (Znth j locks Vundef)
           resp (Znth j res Vundef))) (upto 3)))).
  { rewrite !sublist_same by auto; Exists Ews Tsh; go_lower; entailer'.
    apply prop_right, comp_join_top. }
  { (* second loop *)
    forward_call (sizeof tint).
    { simpl; computable. }
    Intros t sh'.
    rewrite malloc_compat by (auto; exists 2; auto); Intros.
    rewrite memory_block_data_at_ by auto.
    forward.
    simpl in *; assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh0 _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|????? Hj1 Hj2]; subst end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh3 & ? & Hj3).
    destruct (sepalg.join_assoc(c := Share.comp Ews)(e := sh') Hj3) as (sh3' & ? & Hj3'); auto.
    get_global_function'' _f; Intros.
    apply extract_exists_pre; intros f_.
    forward_spawn (share * share * list (val * val) * list (val * val) * val * Z * val * val * val * val)%type
      (f_, t, (Znth i shs Ews, sh2, entries, ghosts, m_entries, i, locksp, Znth i locks Vundef, resp,
               Znth i res Vundef),
    fun (x : (share * share * list (val * val) * list (val * val) * val * Z * val * val * val * val)%type)
        (tid : val) =>
    let '(sh, tsh, entries, ghosts, p, t, locksp, lockt, resultsp, res) := x in
    fold_right sepcon emp
      [!!(0 <= t < 3 /\ isptr lockt /\ readable_share sh /\ readable_share tsh /\ Zlength ghosts = size) && emp;
        data_at sh (tarray tentry size) entries p; atomic_entries sh entries ghosts empty_hists;
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
        data_at_ Tsh tint res;
        lock_inv tsh lockt (f_lock_pred tsh sh entries ghosts p t locksp lockt resultsp res)]).
    { unfold spawn_pre; go_lower.
      Exists _arg (fun x : (share * share * list (val * val) * list (val * val) * val * Z * val * val * val * val) =>
        let '(sh, tsh, entries, ghosts, p, t, locksp, lockt, resultsp, res) := x in
        [(_m_entries, p); (_thread_locks, locksp); (_results, resultsp)]).
      rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
      repeat (apply andp_right; [apply prop_right; repeat split; auto|]).
      { rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
      rewrite !sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'.
        f_equal; f_equal; extensionality.
        destruct x0 as (?, x0); repeat destruct x0 as (x0, ?); simpl.
        extensionality; apply mpred_ext; entailer!. }
      rewrite (extract_nth_sepcon (map _ (upto 3)) i) by (rewrite Zlength_map; auto).
      erewrite Znth_map, Znth_upto by (auto; simpl; omega).
      destruct (zlt i i); [omega|].
      rewrite lock_inv_isptr; Intros.
      assert (0 <= i < Zlength shs) by omega.
      apply andp_right.
      - apply prop_right; split; [omega|]; split; [omega|]; split; auto; split; auto.
        apply Forall_Znth; auto.
      - rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj3).
        rewrite <- (atomic_entries_join_nil _ _ _ _ _ Hj3'); auto.
        rewrite <- (lock_inv_share_join sh1 sh2) by auto.
        rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs Ews) _ _ m_entries)),
          !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
        fast_cancel.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs Ews) _ _ locksp)),
          !sepcon_assoc; apply sepcon_derives.
        { rewrite lock_struct_array; apply stronger_array_ext.
          - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
          - intros j ???; unfold unfold_reptype; simpl.
            destruct (eq_dec j i).
            + subst; rewrite upd_Znth_same; auto.
            + rewrite upd_Znth_diff by auto.
              rewrite Znth_repeat with (x1 := Vundef)(n0 := 3%nat); apply stronger_default_val. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at (Znth i shs Ews) _ _ resp)),
          !sepcon_assoc; apply sepcon_derives.
        { apply stronger_array_ext.
          - unfold unfold_reptype; simpl; rewrite upd_Znth_Zlength; auto.
          - intros j ???; unfold unfold_reptype; simpl.
            destruct (eq_dec j i).
            + subst; rewrite upd_Znth_same; auto.
            + rewrite upd_Znth_diff' by auto.
              rewrite Znth_repeat with (x1 := Vundef)(n0 := 3%nat); apply stronger_default_val. }
        erewrite sublist_next by (auto; omega); simpl; fast_cancel.
        { apply Forall_Znth; auto. }
        { eapply join_readable1, readable_share_list_join; eauto. } }
    go_lower.
    Exists sh3 sh3'; entailer'.
    fast_cancel.
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
    intros j ?; destruct (eq_dec j i).
    - subst; rewrite upd_Znth_same by auto.
      erewrite Znth_map, Znth_upto by (auto; simpl; omega).
      if_tac; [auto | omega].
    - rewrite upd_Znth_diff' by auto.
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      if_tac; if_tac; auto; omega. }
  Intros sh sh'.
  rewrite sublist_nil, <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z, EX x : (share * (list (list (hist * hist) * list Z * list bool))),
    PROP (readable_share (fst x); sepalg_list.list_join (fst x) (sublist i 3 shs) Ews; Zlength (snd x) = i;
          Forall (fun p => let '(h, li, ls) := p in add_items_trace empty_hists (combine (combine (combine
            [1; 2; 3] [1; 1; 1]) li) ls) h) (snd x);
          Forall (fun h => Zlength h = size) (map fst (map fst (snd x)));
          Forall (fun '(h, li, ls) => Zlength li = 3 /\ Zlength ls = 3) (snd x))
    LOCAL (let ls := map snd (snd x) in temp _total (vint (Zlength (filter id (concat ls))));
           lvar _values (tarray tint 16384) values; lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs (fst x) (tarray tentry size) entries m_entries;
         EX sh' : share, !!(readable_share sh' /\ sepalg_list.list_join sh' (sublist i 3 shs) Tsh) &&
           let h := map fst (map fst (snd x)) in
           atomic_entries sh' entries ghosts (fold_right join_hists empty_hists h);
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         data_at (fst x) (tarray (tptr tint) 3) res resp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) (sublist i 3 res));
         data_at (fst x) (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) (sublist i 3 locks));
         fold_right sepcon emp (map (fun j => lock_inv sh1 (Znth j locks Vundef)
           (f_lock_pred sh2 (Znth j shs Ews) entries ghosts m_entries j locksp
              (Znth j locks Vundef) resp (Znth j res Vundef))) (sublist i 3 (upto 3))))).
  { rewrite !(sublist_same 0 3) by auto.
    Exists (sh, @nil (list (hist * hist) * list Z * list bool)) sh'; go_lower.
    match goal with H : sepalg_list.list_join _ (sublist _ _ _) _ |- _ => rewrite sublist_nil in H; inv H end.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    entailer'.
    apply prop_right; split.
    { eapply join_readable1; eauto. }
    eapply sepalg_list.list_join_assoc2 in Hshs; [|eapply sepalg.join_comm, comp_join_top].
    destruct Hshs as (shd & Hjoin' & ?).
    apply sepalg.join_comm in Hjoin'; exploit (sepalg.join_eq(x := sh)(y := Share.comp Ews)(z := shd)(z' := sh'));
      auto; intro; subst; auto. }
  { (* third loop *)
    destruct x as (sh3, lr); Intros sh3'; simpl in *.
    erewrite sublist_next with (l := upto 3), Znth_upto by (auto; rewrite ?Zlength_upto; simpl; omega); simpl.
    rewrite lock_inv_isptr; Intros.
    forward.
    forward_call (Znth i locks Vundef, sh1, f_lock_pred sh2 (Znth i shs Ews) entries ghosts m_entries i locksp
      (Znth i locks Vundef) resp (Znth i res Vundef)).
    forward_call (Znth i locks Vundef, Tsh, sh2,
      |>f_lock_inv (Znth i shs Ews) entries ghosts m_entries i locksp (Znth i locks Vundef) resp (Znth i res Vundef),
      |>f_lock_pred sh2 (Znth i shs Ews) entries ghosts m_entries i locksp (Znth i locks Vundef) resp (Znth i res Vundef)).
    { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
        [repeat apply andp_right; auto; eapply derives_trans;
         try (apply precise_weak_precise || apply positive_weak_positive || apply rec_inv_weak_rec_inv); auto |].
      { apply later_positive; auto. }
      { apply later_rec_lock, selflock_rec. }
      unfold f_lock_pred at 2.
      rewrite selflock_eq.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (lock_inv _ _ _)), !sepcon_assoc, <- sepcon_assoc;
        apply sepcon_derives; [|cancel_frame].
      rewrite <- (lock_inv_share_join sh1 sh2 Tsh) by auto; unfold f_lock_pred; cancel.
      apply lock_inv_later. }
    erewrite sublist_next with (l := locks) by (auto; omega); simpl.
    forward_call (Znth i locks Vundef, sizeof (Tstruct _lock_t noattr)).
    { entailer!. }
    { apply sepcon_derives; [|cancel_frame].
      rewrite data_at__memory_block; Intros; auto. }
    unfold f_lock_inv at 1; Intros hi lii lsi.
    assert (0 <= i < Zlength shs) by omega.
    forward.
    { apply Forall_Znth; auto. }
    { assert (0 <= i < 3) as Hi by auto; clear - Hi; entailer!.
      rewrite upd_Znth_same; auto. }
    rewrite upd_Znth_same by auto.
    forward.
    erewrite sublist_next with (l := res) by (auto; omega); simpl.
    forward_call (Znth i res Vundef, sizeof tint).
    { entailer!. }
    { rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ (Znth i res Vundef))), !sepcon_assoc;
        apply sepcon_derives; [|cancel_frame].
      apply data_at_memory_block. }
    assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh3 _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|??? w1 ? Hj1]; subst end.
    match goal with H : sepalg_list.list_join sh3' _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|??? w1' ? Hj1']; subst end.
    gather_SEP 10 2.
    replace_SEP 0 (data_at w1 (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp).
    { go_lower.
      rewrite <- lock_struct_array.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join; eauto. }
    gather_SEP 8 3.
    replace_SEP 0 (data_at w1 (tarray (tptr tint) 3) res resp).
    { go_lower.
      eapply derives_trans; [apply data_at_array_value_cohere; auto|].
      erewrite data_at_share_join; eauto. }
    forward.
    go_lower; Exists (w1, lr ++ [(hi, lii, lsi)]) w1'.
    rewrite sepcon_andp_prop', sepcon_andp_prop.
    assert (Zlength hi = size) by (erewrite add_items_empty_length; eauto).
    apply andp_right; [|apply andp_right; [|apply andp_right]]; try apply prop_right.
    - simpl; split; [omega|].
      split; [eapply join_readable1; eauto|].
      split; auto.
      split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; auto|].
      rewrite !map_app, !Forall_app; repeat constructor; auto.
    - repeat (split; auto).
      simpl; rewrite add_repr, map_app, concat_app, filter_app, Zlength_app; simpl; rewrite app_nil_r; auto.
    - split; auto.
      eapply join_readable1; eauto.
    - rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh3 _ _ m_entries)),
        (sepcon_comm _ (data_at _ _ _ m_entries)).
      erewrite <- !sepcon_assoc, data_at_share_join by eauto.
      rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_entries _ _ _ _)),
        (sepcon_comm _ (atomic_entries _ _ _ _)).
      erewrite <- !sepcon_assoc, atomic_entries_join; rewrite ?join_hists_empty_length; eauto; try omega.
      Intros.
      simpl; rewrite !map_app, fold_right_app; simpl.
      rewrite join_hists_base by auto.
      cancel.
      { apply Forall_Znth; auto. } }
  Intros x sh''; destruct x as (?, lr); simpl in *.
  repeat match goal with H : sepalg_list.list_join _ (sublist 3 3 _) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward_call (Ews, m_entries, entries, ghosts, fold_right join_hists empty_hists (map fst (map fst lr)),
    keys, values).
  { apply sepcon_derives; [apply derives_refl | cancel_frame]. }
  { split; auto; split; [omega|].
    rewrite join_hists_empty_length; auto. }
  Intro x; destruct x as (lk, lv); simpl; Intros.
  exploit (add_three lr lk lv); auto; intro.
  forward.
  Exists values keys.
  rewrite (sepcon_comm (data_at _ _ _ keys)), (sepcon_comm (data_at _ _ _ values)).
  rewrite sepcon_assoc, (sepcon_comm (data_at _ _ _ values)), <- !sepcon_assoc; apply sepcon_derives;
    [apply sepcon_derives; auto|]; apply andp_right, data_at_data_at_; apply prop_right; auto.
Qed.

(* Given the relations on histories, what can we actually conclude about the maps? *)
Lemma make_map_eq : forall h h', Forall2 (fun a b => value_of_hist (fst a) = value_of_hist (fst b) /\
  value_of_hist (snd a) = value_of_hist (snd b)) h h' -> make_map h = make_map h'.
Proof.
  induction 1; auto; simpl.
  destruct x, y; simpl in *.
  destruct H as (-> & ->); rewrite IHForall2; auto.
Qed.

Lemma make_map_no_key : forall h k (Hout : Forall (fun x => make_int (value_of_hist (fst x)) <> k) h),
  Forall (fun x => fst x <> k) (make_map h).
Proof.
  induction h; simpl; auto; intros.
  destruct a.
  inv Hout.
  constructor; auto.
Qed.

(* It would be nice if we could maintain the invariant that the map has no duplicates and is well-chained,
   and indeed, the algorithm should maintain these properties. However, the per-slot histories do not obviously
   present a way to prove this: if a new key has "mysteriously appeared" (i.e., been added by another thread),
   we don't have a good way of knowing that it's well-chained. *)
(* We can, however, allow for the possibility that there is garbage in the map, and consider the abstract map
   to be those elements that can be successfully looked up, rather than all pairs in the map. In practice, this
   *should* come down to the same thing, but how could we prove it? *)
Lemma set_item_trace_map : forall h k v i h' (Hwf : wf_hists h) (Hlenh : Zlength h = size)
  (Htrace : set_item_trace h k v i h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' /\ let m' := make_map (upd_Znth i h' (Znth i h ([], []))) in
    map_incl (make_map h) m' /\ set m' k v = Some (make_map h').
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & (Hi1 & Hr0) & Hi2 & Hrest).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto; congruence. }
  assert (value_of_hist (fst (Znth i h' ([], []))) = vint k) as Hk'.
  { destruct Hi1 as [Hi1 | [Hi1 | Hi1]]; rewrite (add_events_last _ _ _ Hi1); try discriminate; auto. }
  assert (wf_hists h') as Hwf'; [|split; auto; split].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst.
      rewrite (add_events_snd _ _ _ Hi2), Forall_app; split;
        [|repeat constructor; auto; eapply add_events_ordered; eauto].
      destruct Hi1 as [Hi1 | [Hi1 | Hi1]]; rewrite (add_events_snd _ _ _ Hi1), Forall_app; repeat constructor;
        auto; eapply add_events_ordered; eauto.
    + destruct Hrest as ((? & ? & Hcase & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      destruct Hcase as [Hj1 | Hj1]; rewrite (add_events_snd _ _ _ Hj1), Forall_app; repeat constructor; auto;
        eapply add_events_ordered; eauto.
    + destruct Hrest as (_ & ->); auto.
  - intros k0 v0 j Hk0 Hj.
    exploit (Znth_inbounds j (make_map h) (0, 0)).
    { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
    intro; unfold make_map in *; rewrite <- upd_Znth_map.
    rewrite Zlength_map in *.
    rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
    destruct (eq_dec j i); [subst; rewrite upd_Znth_same; auto | rewrite upd_Znth_diff'];
      rewrite ?Zlength_map in *; auto; try omega.
    rewrite Znth_map with (d' := ([], [])) by omega.
    specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i));
      [|destruct Hrest as (_ & ->); auto].
    destruct Hrest as ((r1 & ? & Hcase & ? & ? & -> & Heq) & _); auto; simpl in *.
    assert (value_of_hist (fst (Znth j h ([], []))) <> vint 0).
    { intro X; rewrite X in Hk0; contradiction Hk0; auto. }
    destruct Hcase as [Hj1 | Hj1]; rewrite (add_events_last _ _ _ Hj1), Heq; try discriminate; auto.
  - assert (0 <= i < Zlength h') by (rewrite Hlen; auto).
    unfold set.
    assert (lookup (make_map (upd_Znth i h' (Znth i h ([], [])))) k = Some i) as ->.
    + unfold lookup, make_map.
      assert (i = ((i - hash k) mod size + hash k) mod size) as Hmod.
      { rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small by omega; auto. }
      pose proof (hash_range k).
      assert (Zlength (map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs))))
              (upd_Znth i h' (Znth i h ([], [])))) = size) as Hlen1.
      { rewrite Zlength_map, upd_Znth_Zlength; auto; omega. }
      erewrite index_of'_succeeds; simpl.
      f_equal; symmetry; apply Hmod.
      { rewrite Zlength_rebase; rewrite ?Zlength_map, ?upd_Znth_Zlength; auto;
          replace (Zlength h') with size; auto; try omega.
        apply Z_mod_lt, size_pos. }
      { rewrite Forall_forall; intros x Hin.
        apply In_Znth with (d := (0, 0)) in Hin; destruct Hin as (j & Hj & Hx).
        exploit (Z_mod_lt (i - hash k) size); [apply size_pos | intro].
        rewrite Zlength_sublist in Hj; rewrite ?Zlength_rebase; rewrite ?Hlen1; try (simpl in *; omega).
        rewrite Znth_sublist, Z.add_0_r in Hx by (auto; omega).
        rewrite Znth_rebase in Hx by (simpl in *; omega).
        rewrite Hlen1, Znth_map with (d' := ([], [])) in Hx.
        subst x; simpl.
        specialize (Hrest ((j + hash k) mod size)); destruct Hrest as ((r1 & ? & Hcase & ? & ? & ?) & _).
        { unfold indices; rewrite in_map_iff.
          exists j; split; [rewrite Z.add_comm; auto|].
          rewrite In_upto, Z2Nat.id; omega. }
        rewrite upd_Znth_diff'; auto.
        simpl in *; destruct Hcase as [Hj1 | Hj1]; rewrite (add_events_last _ _ _ Hj1); try discriminate;
          simpl; rewrite !Int.signed_repr; auto.
        * intro X; rewrite <- X, Zminus_mod_idemp_l, Z.add_simpl_r, Z.sub_0_r, Zmod_small in Hj; try omega.
          destruct Hj; split; auto; etransitivity; eauto; apply Z_mod_lt, size_pos.
        * rewrite upd_Znth_Zlength by auto.
          replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos. }
      { rewrite <- Hlen1, Znth_rebase', Znth_map with (d' := ([], [])); simpl;
          rewrite ?Zlength_map, ?upd_Znth_Zlength; auto; try (simpl in *; omega).
        rewrite upd_Znth_same by auto; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth i h ([], [])))) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto; simpl.
        rewrite Int.signed_repr; auto. }
    + simpl; unfold make_map; erewrite <- upd_Znth_map, upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map;
        auto.
      rewrite Znth_map', Hk', (add_events_last _ _ _ Hi2); [simpl | discriminate].
      rewrite !Int.signed_repr; auto.
Qed.

Lemma get_item_trace_map : forall h k v i h' (Hwf : wf_hists h) (Hlenh : Zlength h = size)
  (Htrace : get_item_trace h k v i h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' /\ match get (make_map h') k with
  | Some v' => v' = v /\ map_incl (upd_Znth i (make_map h) (k, v)) (make_map h')
  | None => v = 0 /\ map_incl (make_map h) (make_map h') end.
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  destruct Hi as (r & Hi1 & Hi2 & Hr0).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto; congruence. }
  assert (wf_hists h') as Hwf'; [|split; auto].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst; rewrite Hhi in *.
      rewrite (add_events_snd _ _ _ Hi1), Forall_app; split;
        [repeat constructor; auto; eapply add_events_ordered; eauto|].
      destruct Hi2 as [(? & ? & ->) | (? & Hi2)]; auto.
      rewrite (add_events_snd _ _ _ Hi2), Forall_app; repeat constructor; auto; eapply add_events_ordered; eauto.
    + destruct Hrest as ((? & ? & Hj1 & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      rewrite (add_events_snd _ _ _ Hj1), Forall_app; repeat constructor; auto.
      eapply add_events_ordered; eauto.
    + destruct Hrest as (_ & ->); auto.
  - unfold get, lookup.
    pose proof (index_of'_spec k (rebase (make_map h') (hash k))) as Hspec.
    destruct (index_of' (rebase (make_map h') (hash k)) k) eqn: Hindex; simpl.
    unfold make_map at 1; rewrite Znth_map with (d' := ([], [])).
    pose proof (hash_range k).
    assert ((z + hash k) mod size = i) as Hz.
    { destruct Hspec as (Hz & Hcase & Hall).
      assert (Zlength (make_map h') = Zlength h') as Hlenm by (unfold make_map; rewrite Zlength_map; auto).
      assert (z <= (i - hash k) mod Zlength (make_map h')) as Hle.
      { eapply Forall_sublist_le; try apply Hall; simpl.
        { apply Z_mod_lt; omega. }
        { simpl in *; omega. }
        rewrite Znth_rebase' by (simpl in *; omega).
        unfold make_map; rewrite Znth_map'.
        rewrite (add_events_last _ _ _ Hi1); [simpl | discriminate].
        destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; [|rewrite Int.signed_repr by auto]; tauto. }
      rewrite Zlength_rebase in Hz by omega.
      rewrite Znth_rebase, Hlenm in Hcase by omega.
      unfold make_map in Hcase; rewrite Znth_map with (d' := ([], [])) in Hcase; simpl in Hcase.
      destruct (eq_dec ((z + hash k) mod size) i); auto.
      specialize (Hrest ((z + hash k) mod size)); destruct Hrest as ((r1 & ? & Hfst & ? & ? & ?) & _).
      { unfold indices.
        rewrite in_map_iff.
        exists z; split; [rewrite Z.add_comm; auto|].
        rewrite In_upto, Z2Nat.id.
        rewrite Hlenm in Hle; replace (Zlength h') with size in Hle by omega.
        destruct (eq_dec z ((i - hash k) mod size)); [|omega].
        contradiction n; rewrite e, Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto; omega.
        { apply Z_mod_lt, size_pos. } }
      replace (Zlength h') with size in Hcase by omega.
      simpl in *; rewrite (add_events_last _ _ _ Hfst) in Hcase; [simpl in Hcase | discriminate].
      rewrite !Int.signed_repr in Hcase; tauto.
      { apply Z_mod_lt; omega. } }
    simpl in *; rewrite Hz.
    replace (value_of_hist (fst _)) with (vint r)
      by (rewrite (add_events_last _ _ _ Hi1); [auto | discriminate]); simpl.
    destruct Hi2 as [(? & ? & Hi2) | (? & Hi2)]; clear dependent z; subst; simpl.
    + split; auto.
      intros k0 v0 j Hk0 Hj.
      exploit (Znth_inbounds j (make_map h) (0, 0)).
      { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
      unfold make_map in *; rewrite Zlength_map; intro;
        rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      rewrite Znth_map with (d' := ([], [])) by omega.
      destruct (eq_dec j i).
      { subst; rewrite Hhi in *; simpl in *; contradiction Hk0.
        destruct (eq_dec (value_of_hist hk) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto. }
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & Hj1 & ? & ? & -> & Heq) & _); auto.
        rewrite (add_events_last _ _ _ Hj1); [simpl | discriminate].
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + rewrite (add_events_last _ _ _ Hi2); [simpl | discriminate].
      rewrite !Int.signed_repr by auto.
      if_tac; [contradiction Hk; auto|].
      split; auto.
      intros k0 v0 j Hk0 Hj.
      exploit (Znth_inbounds j (upd_Znth i (make_map h) (k, v)) (0, 0)).
      { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
      unfold make_map in *; rewrite upd_Znth_Zlength; rewrite Zlength_map; auto.
      intro; rewrite Znth_map with (d' := ([], [])) by omega.
      destruct (eq_dec j i).
      { subst; rewrite upd_Znth_same in Hj by (rewrite Zlength_map; auto).
        inv Hj; rewrite (add_events_last _ _ _ Hi1), (add_events_last _ _ _ Hi2); try discriminate; simpl.
        rewrite !Int.signed_repr; auto. }
      rewrite upd_Znth_diff' in Hj; rewrite ?Zlength_map; auto.
      rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & Hj1 & ? & ? & -> & Heq) & _); auto.
        rewrite (add_events_last _ _ _ Hj1); [simpl | discriminate].
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos.
    + assert (In r (map fst (rebase (make_map h') (hash k)))).
      { rewrite in_map_iff.
        unfold rebase, make_map; eexists; rewrite rotate_In, in_map_iff.
        split; [|do 2 eexists; eauto; apply Znth_In with (i0 := i); omega].
        rewrite (add_events_last _ _ _ Hi1); [simpl | discriminate].
        apply Int.signed_repr; destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; auto.
        { pose proof (hash_range k).
          rewrite Zlength_map; omega. } }
      destruct Hspec as (Hnk & Hnz), Hi2 as [(? & ? & ?) | (? & ?)]; subst;
        [contradiction Hnz | contradiction Hnk].
Qed.
