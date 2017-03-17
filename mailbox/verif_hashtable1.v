Require Import progs.ghost.
Require Import mailbox.verif_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.hashtable1.
Require Import mailbox.hashtable.

Set Bullet Behavior "Strict Subproofs".

Set Default Timeout 40.

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
Definition k_R (h : list hist_el) (v : val) := !!(Forall int_op h /\
  forall e, In e h -> value_of e <> vint 0 -> v = value_of e) && emp.

Definition v_R (h : list hist_el) (v : val) := emp.

(* Entries are no longer consecutive. *)
Definition wf_hists h := Forall (fun x => (ordered_hist (fst x) /\ Forall int_op (map snd (fst x))) /\
  (ordered_hist (snd x) /\ Forall int_op (map snd (snd x)))) h.

Definition make_map h :=
  map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs)))) h.

Definition atomic_entry sh pk pv hk hv :=
  atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv.

Definition atomic_entries sh entries hists := fold_right sepcon emp
  (map (fun x => let '((pk, pv), (hk, hv)) := x in atomic_entry sh pk pv hk hv) (combine entries hists)).

Definition failed_CAS k (a b : hist * hist) := exists t r, newer (fst a) t /\
  (fst b = fst a ++ [(t, Load (Vint r))] \/
   exists t1 t2, (t < t1 < t2)%nat /\
     fst b = fst a ++ [(t, Load (vint 0)); (t1, CAS (Vint r) (vint 0) (vint k)); (t2, Load (Vint r))]) /\
  r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = Vint r).

Definition found_key k (a b : hist) := (exists t, newer a t /\
  (b = a ++ [(t, Load (vint k))] \/ exists t1, (t < t1)%nat /\
   (b = a ++ [(t, Load (vint 0)); (t1, CAS (vint 0) (vint 0) (vint k))] \/ exists t2, (t1 < t2)%nat /\
    b = a ++ [(t, Load (vint 0)); (t1, CAS (vint k) (vint 0) (vint k)); (t2, Load (vint k))]))) /\
  let v := value_of_hist a in v <> vint 0 -> v = vint k.

Definition set_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\ found_key k (fst (Znth i h ([], []))) (fst (Znth i h' ([], []))) /\
  (exists tv, newer (snd (Znth i h ([], []))) tv /\
   snd (Znth i h' ([], [])) = snd (Znth i h ([], [])) ++ [(tv, Store (vint v))]) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list (val * val), h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist),
   PROP (set_item_trace h key value i h')
   LOCAL ()
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h').
(* set_item_trace_map describes the properties on the resulting map. *)

Definition failed_load k (a b : hist * hist) := exists t r, newer (fst a) t /\
  fst b = fst a ++ [(t, Load (Vint r))] /\ r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = Vint r).

(* get_item can return 0 in two cases: if the key is not in the map, or if its value is 0.
   In correct use, the latter should only occur if the value has not been initialized.
   Conceptually, this is still linearizable because we could have just checked before the key was added,
   but at a finer-grained level we can tell the difference from the history, so we might as well keep
   this information. *)
Definition get_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\
  (let '(hk, hv) := Znth i h ([], []) in exists t r, newer hk t /\
     fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint r))] /\
     (v = 0 /\ r = 0 /\ snd (Znth i h' ([], [])) = hv \/
      r = k /\ exists tv, Forall (fun x => fst x < tv)%nat hv /\
        snd (Znth i h' ([], [])) = hv ++ [(tv, Load (vint v))]) /\
    (let v := value_of_hist hk in v <> vint 0 -> v = vint r)) /\
  forall j, (In j (indices (hash k) i) -> failed_load k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

(* Read the most recently written value. *)
Definition get_item_spec :=
 DECLARE _get_item
  WITH key : Z, p : val, sh : share, entries : list (val * val), h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; key <> 0; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h)
  POST [ tint ]
   EX value : Z, EX i : Z, EX h' : list (hist * hist),
   PROP (repable_signed value; get_item_trace h key value i h')
   LOCAL (temp ret_temp (vint value))
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h').

Definition add_item_trace (h : list (hist * hist)) k v i (success : bool) h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\ (let '(hk, hv) := Znth i h ([], []) in if success then
    exists t t1 tv, newer hk t /\ newer hv tv /\ (t < t1)%nat /\ fst (Znth i h' ([], [])) =
      hk ++ [(t, Load (vint 0)); (t1, CAS (vint 0) (vint 0) (vint k))] /\
      snd (Znth i h' ([], [])) = hv ++ [(tv, Store (vint v))] /\ value_of_hist hk = vint 0
    else (exists t, newer hk t /\ (fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint k))] \/
      exists t1 t2, (t < t1 < t2)%nat /\ fst (Znth i h' ([], [])) =
        hk ++ [(t, Load (vint 0)); (t1, CAS (vint k) (vint 0) (vint k)); (t2, Load (vint k))])) /\
      snd (Znth i h' ([], [])) = hv /\ let v := value_of_hist hk in v <> vint 0 -> v = vint k) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

Definition add_item_spec :=
 DECLARE _add_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list (val * val), h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Zlength h = size; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h)
  POST [ tint ]
   EX success : bool, EX i : Z, EX h' : list (hist * hist),
   PROP (add_item_trace h key value i success h')
   LOCAL (temp ret_temp (Val.of_bool success))
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries h').

Notation empty_hists := (repeat ([] : hist, [] : hist) (Z.to_nat size)).

Definition init_table_spec :=
 DECLARE _init_table
  WITH p : val
  PRE [ ]
   PROP ()
   LOCAL (gvar _m_entries p)
   SEP (data_at_ Ews (tarray tentry size) p)
  POST [ tvoid ]
   EX entries : list (val * val),
   PROP ()
   LOCAL ()
   SEP (data_at Ews (tarray tentry size) entries p; atomic_entries Tsh entries empty_hists).

Definition full_hist h v := exists l, hist_list h l /\ apply_hist (vint 0) l = Some (vint v).

Definition freeze_table_spec :=
 DECLARE _freeze_table
  WITH sh : share, p : val, entries : list (val * val), h : list (hist * hist), keys : val, values : val
  PRE [ ]
   PROP (readable_share sh; Zlength h = Zlength entries)
   LOCAL (gvar _m_entries p; temp _keys keys; temp _values values)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries Tsh entries h;
        data_at_ Tsh (tarray tint size) keys; data_at_ Tsh (tarray tint size) values)
  POST [ tvoid ]
   EX lk : list Z, EX lv : list Z,
   PROP (Forall2 full_hist (map fst h) lk; Forall2 full_hist (map snd h) lv)
   LOCAL ()
   SEP (data_at_ sh (tarray tentry size) p;
        data_at Tsh (tarray tint size) (map (fun x => vint x) lk) keys;
        data_at Tsh (tarray tint size) (map (fun x => vint x) lv) values).

Inductive add_n_items_trace : Z -> list (hist * hist) -> list Z -> list Z -> list Z -> list bool ->
  list (hist * hist) -> Prop :=
| add_0_items : forall h, add_n_items_trace 0 h [] [] [] [] h
| add_S_items : forall n h lk lv li ls h' k v i s h'' (Hn : add_n_items_trace n h lk lv li ls h')
    (Hadd : add_item_trace h' k v i s h''),
    add_n_items_trace (n + 1) h (lk ++ [k]) (lv ++ [v]) (li ++ [i]) (ls ++ [s]) h''.

Definition f_lock_inv sh entries p t locksp lockt resultsp res :=
  (EX h : list (hist * hist), EX li : list Z, EX ls : list bool,
  !!(add_n_items_trace 3 empty_hists [1; 2; 3] [1; 1; 1] li ls h) &&
     data_at sh (tarray tentry size) entries p * atomic_entries sh entries h *
     data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
     data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp *
     data_at Tsh tint (vint (Zlength (filter id ls))) res).

Definition f_lock_pred tsh sh entries p t locksp lockt resultsp res :=
  selflock (f_lock_inv sh entries p t locksp lockt resultsp res) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH tid : val, x : share * share * list (val * val) * val * Z * val * val * val * val
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, tsh, entries, p, t, locksp, lockt, resultsp, res) := x in
   PROP (0 <= t < 3; isptr lockt; readable_share sh; readable_share tsh)
   LOCAL (temp _arg tid; gvar _m_entries p; gvar _thread_locks locksp; gvar _results resultsp)
   SEP (data_at sh (tarray tentry size) entries p; atomic_entries sh entries empty_hists;
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
        data_at_ Tsh tint res; lock_inv tsh lockt (f_lock_pred tsh sh entries p t locksp lockt resultsp res))
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

Lemma update_entries_hist : forall sh entries h i hk hv pki pvi (Hlen : Zlength entries = Zlength h)
  (Hpi : Znth i entries (Vundef, Vundef) = (pki, pvi)) (Hi : 0 <= i < Zlength entries),
  atomic_entries sh entries (upd_Znth i h (hk, hv)) =
  fold_right sepcon emp (upd_Znth i (map (fun x => let '(pk, pv, (hk, hv)) := x in
    atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv) (combine entries h))
    (atomic_loc sh pki (vint 0) k_R hk * atomic_loc sh pvi (vint 0) v_R hv)).
Proof.
  intros; unfold atomic_entries.
  f_equal.
  erewrite upd_Znth_map with (v := (pki, pvi, (hk, hv))), combine_upd_Znth2, Hpi; auto.
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

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
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
      Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; auto; omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry; Intros.
    rewrite atomic_loc_isptr; Intros.

Ltac solve_efield_denote Delta P Q R efs gfs H ::=   evar (gfs : list gfield);
  assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfs) as H; 
  [
    unfold efs, gfs;
    match goal with
    | efs := nil |- _ =>
      instantiate (1 := nil);
      apply prop_right, I
    | efs := ?ef :: ?efs' |- _ =>
      let efs0 := fresh "efs" in
      let gfs0 := fresh "gfs" in
      let H0 := fresh "H" in
      pose efs' as efs0;
      solve_efield_denote Delta P Q R efs0 gfs0 H0;
      match goal with
      | gfs0 := ?gfs0' |- _ =>
        match ef with
        | eArraySubsc ?ei => 

          let HA := fresh "H" in
          let vi := fresh "vi" in evar (vi: val);
          do_compute_expr Delta P Q R ei vi HA;

          revert vi HA;
          let vvvv := fresh "vvvv" in
          let HHHH := fresh "HHHH" in
            match goal with
            | |- let vi := ?V in _ => remember V as vvvv eqn:HHHH
            end;
          autorewrite with norm in HHHH;
      
          match type of HHHH with
          | _ = Vint (Int.repr _) => idtac
          | _ = Vint (Int.sub _ _) => unfold Int.sub in HHHH
          | _ = Vint (Int.add _ _) => unfold Int.add in HHHH
          | _ = Vint (Int.mul _ _) => unfold Int.mul in HHHH
          | _ = Vint (Int.and _ _) => unfold Int.and in HHHH
          | _ = Vint (Int.or _ _) => unfold Int.or in HHHH
          | _ = Vint ?V =>
            replace V with (Int.repr (Int.unsigned V)) in HHHH
              by (rewrite (Int.repr_unsigned V); reflexivity)
          end;
          (* subst vvvv; *)
          rewrite HHHH in *; clear HHHH; (* Without this replacement, subst fails, and the next forward runs forever! *)
          intros vi HA;

          match goal with
          | vi := Vint (Int.repr ?i) |- _ => instantiate (1 := ArraySubsc i :: gfs0')
          end;
          
          let HB := fresh "H" in
          assert (match typeof ei with | Tint _ _ _ => True | _ => False end) as HB by (simpl; auto);
          
          apply (efield_denote_cons_array _ _ _ _ _ H0 HA HB)

        | eStructField ?i =>
          instantiate (1 := StructField i :: gfs0');
          apply efield_denote_cons_struct, H0
        | eUnionField ?i =>
          instantiate (1 := UnionField i :: gfs0');
          apply efield_denote_cons_union, H0
        end
      end
    end
  |].

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
    forward_call (sh, pki, vint 0, hki, fun (h : hist) => !!(h = hki) && emp, k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t, v); simpl snd in *.
    destruct v; try contradiction.
    match goal with |- semax _ (PROP () (LOCALx (_ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
      forward_if (EX hki' : hist, PROP (found_key key hki hki') (LOCALx Q
        (SEPx (atomic_loc sh pki (vint 0) k_R hki' :: R)))) end.
    + match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (i0 = Int.zero) (LOCALx Q (SEPx R))) end.
      { eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
          SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (Vint i0))], hvi)).
        go_lower.
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; repeat eexists; eauto; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega. }
      { forward.
        entailer!. }
      Intros; subst.
      forward_call (sh, pki, vint 0, vint key, vint 0, hki ++ [(t, Load (vint 0))],
        fun (h : hist) c v => !!(c = vint 0 /\ v = vint key /\ h = hki ++ [(t, Load (vint 0))]) && emp,
        k_R, fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
      { entailer!.
        setoid_rewrite Hpi; auto. }
      { repeat (split; auto).
        intros ?????????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
          apply apply_int_ops in Hvx; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; [| |contradiction].
          * intros.
            replace vx with (value_of e) by (symmetry; auto).
            if_tac; auto; absurd (value_of e = vint 0); auto.
          * subst; simpl; intros.
            if_tac; if_tac; auto; absurd (vx = vint 0); auto.
        + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
          exploit Hhist.
          { rewrite in_app; eauto. }
          intro X; apply nth_error_In in X; subst; auto.
        + apply andp_right; auto.
          eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
      Intros x; destruct x as (t', v); simpl snd in *.
      destruct v; try contradiction.
      assert (t < t')%nat.
      { match goal with H : Forall _ (hki ++ _) |- _ => rewrite Forall_app in H;
          destruct H as (_ & Ht); inv Ht; auto end. }
      match goal with |- semax _ (PROP () (LOCALx (_ :: _ :: ?Q) (SEPx (_ :: ?R)))) _ _ =>
        forward_if (EX hki' : hist, PROP (found_key key hki hki') ((LOCALx Q)
        (SEPx (atomic_loc sh pki (vint 0) k_R hki' :: R)))) end.
      * destruct (eq_dec (vint 0) (Vint i0)); [discriminate|].
        forward_call (sh, pki, vint 0, hki ++ [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key))],
          fun (h : hist) => !!(h = hki ++ [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key))]) && emp,
          k_R,
          fun (h : hist) (v : val) => !!(v = Vint i0) && emp).
        { entailer!.
          simpl in *; rewrite Hpi; auto. }
        { rewrite <- app_assoc; fast_cancel. }
        { repeat (split; auto).
          intros ???????????? Ha.
          unfold k_R in *; simpl in *.
          eapply semax_pre, Ha.
          go_lowerx; entailer!.
          repeat split.
          + rewrite Forall_app; repeat constructor; auto.
            apply apply_int_ops in Hvx; auto.
          + intros ? Hin; rewrite in_app in Hin.
            destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
          + match goal with H : forall e, In e hx -> _ |- _ =>
              exploit (H (CAS (Vint i0) (vint 0) (vint key))) end.
            { eapply nth_error_In, Hhist.
              rewrite in_app; simpl; eauto. }
            { simpl.
              if_tac; [absurd (Vint i0 = vint 0)|]; auto. }
            simpl.
            if_tac; [absurd (Vint i0 = vint 0)|]; auto.
          + apply andp_right; auto.
            eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
        Intros x; destruct x as (t'', v); simpl snd in *; subst.
        assert (t' < t'')%nat.
        { match goal with H : Forall _ (hki ++ [_; _]) |- _ => rewrite Forall_app in H;
            destruct H as (_ & Ht); inversion Ht as [|??? Ht']; inv Ht'; auto end. }
        match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
          forward_if (PROP (i0 = Int.repr key) (LOCALx Q (SEPx R))) end.
        { eapply semax_pre; [|apply semax_continue].
          unfold POSTCONDITION, abbreviate, overridePost.
          destruct (eq_dec EK_continue EK_normal); [discriminate|].
          unfold loop1_ret_assert.
          go_lower.
          Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++
            [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key)); (t'', Load (Vint i0))], hvi)).
          apply andp_right.
          { apply prop_right; split.
            { rewrite upd_Znth_Zlength; auto; omega. }
            rewrite Zmod_mod.
            split; auto; split; auto; split; auto.
            apply incr_invariant; auto; simpl in *; try omega.
            * rewrite Heq, Hhi; do 3 eexists; [|split; [right; do 3 eexists; [|reflexivity]|]]; auto.
              repeat split; auto.
              { intro; contradiction n; subst; auto. }
              match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
                symmetry; apply H; auto end.
              rewrite ordered_last_value; auto.
            * admit. (* list is long enough *) }
          apply andp_right; [apply prop_right; auto|].
          fast_cancel.
          rewrite <- app_assoc.
          erewrite <- sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega. }
        { forward.
          entailer!. }
        intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
        rewrite eq_dec_refl.
        go_lower.
        apply andp_right; [apply prop_right; auto|].
        rewrite <- app_assoc; Exists (hki ++
          [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key)); (t'', Load (Vint i0))]); entailer!.
        split; [do 2 eexists; eauto; right; do 2 eexists; eauto|].
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
          symmetry; apply H; auto end.
        apply ordered_last_value; auto.
      * forward.
        destruct (eq_dec (vint 0) (Vint i0)); [|discriminate].
        assert (i0 = Int.zero) by (inv e; auto); subst.
        rewrite <- app_assoc.
        Exists (hki ++ [(t, Load (vint 0)); (t', CAS (vint 0) (vint 0) (vint key))]); entailer!.
        split; [do 2 eexists; eauto|].
        intros ? X; contradiction X.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint Int.zero = v0 |- _ =>
          symmetry; apply H; auto end.
        apply ordered_last_value; auto.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
        rewrite eq_dec_refl.
        Intros hki'.
        go_lower.
        apply andp_right; [apply prop_right; auto|].
        Exists hki'; entailer!.
    + forward.
      subst; Exists (hki ++ [(t, Load (vint key))]); entailer!.
      split; [eauto|].
      match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
        symmetry; apply H; auto end.
      apply ordered_last_value; auto.
    + rewrite (atomic_loc_isptr _ pvi).
      Intros hki'.
      forward.
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      forward_call (sh, pvi, vint value, vint 0, hvi, fun (h : hist) v => !!(v = vint value) && emp, v_R,
        fun (h : hist) => emp).
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      { repeat (split; auto).
        intros ????????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros t'.
      forward.
      Exists (i1 mod size) (upd_Znth (i1 mod size) h' (hki', hvi ++ [(t', Store (vint value))])).
      apply andp_right; auto.
      apply andp_right.
      { apply prop_right; split; auto.
        split.
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
      apply andp_right; auto.
      fast_cancel.
      erewrite <- sepcon_assoc, (sepcon_comm (atomic_loc _ _ _ _ _)), replace_nth_sepcon,
        update_entries_hist; eauto; omega.
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
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
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
      Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; auto; omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry; Intros.
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
    forward_call (sh, pki, vint 0, hki, fun h => !!(h = hki) && emp, k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t, v); simpl snd in *.
    destruct v; try contradiction.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ pvi).
      forward.
      { entailer!.
        simpl in *; rewrite Hpi; auto. }
      forward_call (sh, pvi, vint 0, hvi, fun (h : hist) => emp, v_R, fun (h : hist) (v : val) => emp).
      { entailer!.
        simpl in Hpi; rewrite Hpi; auto. }
      { repeat (split; auto).
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros x; destruct x as (t', v); simpl snd in *.
      forward.
      Exists (Int.signed v) (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint key))],
        hvi ++ [(t', Load (Vint v))])).
      apply andp_right.
      { apply prop_right.
        split; [apply Int.signed_range|].
        split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 3 eexists; eauto; split; eauto; split; eauto; [rewrite Int.repr_signed; eauto|].
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
      apply andp_right; [apply prop_right; rewrite Int.repr_signed; auto|].
      fast_cancel.
      erewrite <- sepcon_assoc, (sepcon_comm (atomic_loc _ _ _ _ _)), replace_nth_sepcon,
        update_entries_hist; eauto; omega.
    + forward.
      entailer!.
    + Intros; match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (i0 <> Int.zero) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists 0 (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint 0))], hvi)).
        apply andp_right.
        { apply prop_right.
          split; [split; computable|].
          split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [replace (Zlength h) with (Zlength h'); auto|].
        setoid_rewrite Heq.
        rewrite Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 3 eexists; eauto; split; eauto; split; eauto.
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
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega.
      * forward.
        entailer!.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
          SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (Vint i0))], hvi)).
        go_lower.
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; repeat eexists; eauto; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega.
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
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
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
      Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine
      by (rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; auto; omega).
    destruct (Znth (i1 mod size) entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth (i1 mod size) h' ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry; Intros.
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
    forward_call (sh, pki, vint 0, hki, fun (h : hist) => !!(h = hki) && emp, k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t, v); simpl snd in *.
    destruct v; try contradiction.
    assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod size)) as Hindex.
    { unfold indices.
      replace (i1 mod size) with ((i + hash key) mod size).
      rewrite Zminus_mod_idemp_l; auto. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    { forward.
      Exists false (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint key))], hvi));
        entailer!.
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
      + erewrite replace_nth_sepcon, update_entries_hist; eauto; omega. }
    { forward.
      entailer!. }
    Intros.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 = Int.zero) (LOCALx Q (SEPx R))) end.
    { eapply semax_pre; [|apply semax_continue].
      unfold POSTCONDITION, abbreviate, overridePost.
      destruct (eq_dec EK_continue EK_normal); [discriminate|].
      unfold loop1_ret_assert.
      instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
        PROP (Zlength h' = Zlength h; i1 mod size = (i + hash key) mod size; 0 <= i < size;
        forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
          (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
        LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
        SEP (@data_at CompSpecs sh (tarray tentry size) entries p; atomic_entries sh entries h')).
      Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (Vint i0))], hvi)).
      go_lower.
      apply andp_right.
      { apply prop_right; split.
        { rewrite upd_Znth_Zlength; auto; omega. }
        rewrite Zmod_mod.
        split; auto; split; auto; split; auto.
        apply incr_invariant; auto; simpl in *; try omega.
        * rewrite Heq, Hhi; repeat eexists; eauto; auto.
          match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto.
        * admit. (* list is long enough *) }
      apply andp_right; [apply prop_right; auto|].
      fast_cancel.
      erewrite <- sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega. }
    { forward.
      entailer!. }
    Intros; subst.
    forward_call (sh, pki, vint 0, vint key, vint 0, hki ++ [(t, Load (vint 0))],
      fun (h : hist) c v => !!(c = vint 0 /\ v = vint key /\ h = hki ++ [(t, Load (vint 0))]) && emp,
      k_R, fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      setoid_rewrite Hpi; auto. }
    { repeat (split; auto).
      intros ?????????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; [| |contradiction].
        * intros.
          replace vx with (value_of e) by (symmetry; auto).
          if_tac; auto; absurd (value_of e = vint 0); auto.
        * subst; simpl; intros.
          if_tac; if_tac; auto; absurd (vx = vint 0); auto.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        exploit Hhist.
        { rewrite in_app; eauto. }
        intro X; apply nth_error_In in X; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t', v); simpl snd in *.
    destruct v; try contradiction.
    assert (t < t')%nat.
    { match goal with H : Forall _ (hki ++ _) |- _ => rewrite Forall_app in H;
        destruct H as (_ & Ht); inv Ht; auto end. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 = Int.zero) ((LOCALx Q) (SEPx R))) end.
    { destruct (eq_dec (vint 0) (Vint i0)); [discriminate|].
      forward_call (sh, pki, vint 0, hki ++ [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key))],
        fun (h : hist) => !!(h = hki ++ [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key))]) && emp,
        k_R,
        fun (h : hist) (v : val) => !!(v = Vint i0) && emp).
      { entailer!.
        simpl in Hpi; rewrite Hpi; auto. }
      { rewrite <- app_assoc; fast_cancel. }
      { repeat (split; auto).
        intros ???????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
          apply apply_int_ops in Hvx; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
        + match goal with H : forall e, In e hx -> _ |- _ =>
            exploit (H (CAS (Vint i0) (vint 0) (vint key))) end.
          { eapply nth_error_In, Hhist.
            rewrite in_app; simpl; eauto. }
          { simpl.
            if_tac; [absurd (Vint i0 = vint 0)|]; auto. }
          simpl.
          if_tac; [absurd (Vint i0 = vint 0)|]; auto.
        + apply andp_right; auto.
          eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
      Intros x; destruct x as (t'', v); simpl snd in *; subst.
      assert (t' < t'')%nat.
      { match goal with H : Forall _ (hki ++ [_; _]) |- _ => rewrite Forall_app in H;
          destruct H as (_ & Ht); inversion Ht as [|??? Ht']; inv Ht'; auto end. }
      match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (fun _ : environ => FF) end.
      - forward.
        Exists false (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint 0));
          (t', CAS (vint key) (vint 0) (vint key)); (t'', Load (vint key))], hvi));
          entailer!.
        + split.
          { rewrite upd_Znth_Zlength; auto. }
          split; [auto|].
          setoid_rewrite Heq; rewrite Hhi; simpl.
          rewrite upd_Znth_same by auto; simpl.
          split; [repeat split; [do 2 eexists; [|right; eauto]|]|]; auto.
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
        + erewrite <- app_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega.
      - eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        go_lower.
        Exists i (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++
          [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key)); (t'', Load (Vint i0))], hvi)).
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          apply incr_invariant; auto; simpl in *; try omega.
          * rewrite Heq, Hhi; do 3 eexists; [|split; [right; do 3 eexists; [|reflexivity]|]]; auto;
              repeat split; auto.
            { intro; subst; contradiction n; auto. }
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        erewrite <- app_assoc, <- sepcon_assoc, replace_nth_sepcon, update_entries_hist; eauto; omega.
      - intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; go_lowerx; contradiction. }
    { forward.
      destruct (eq_dec (vint 0) (Vint i0)); [|discriminate].
      assert (i0 = Int.zero) by (inv e; auto); entailer!. }
    rewrite (atomic_loc_isptr _ pvi).
    Intros; subst; simpl in Hpi.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    forward_call (sh, pvi, vint value, vint 0, hvi, fun (h : hist) v => !!(v = vint value) && emp, v_R,
      fun (h : hist) => emp).
    { entailer!.
      rewrite Hpi; auto. }
    { repeat (split; auto).
      intros ????????????? Ha.
      unfold v_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      apply andp_right; auto.
      eapply derives_trans, precise_weak_precise; auto. }
    Intros tv.
    forward.
    Exists true (i1 mod size) (upd_Znth (i1 mod size) h' (hki ++ [(t, Load (vint 0));
      (t', CAS (vint 0) (vint 0) (vint key))], hvi ++ [(tv, Store (vint value))])).
    apply andp_right.
    { apply prop_right; split; auto.
      split.
      { rewrite upd_Znth_Zlength; auto. }
      split; [auto|].
      setoid_rewrite Heq.
      rewrite Hhi; simpl.
      rewrite upd_Znth_same by auto; simpl; split; [repeat eexists; auto|].
      { destruct (eq_dec (value_of_hist hki) (vint 0)); auto.
        match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint Int.zero = v0 |- _ =>
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
    apply andp_right; [apply prop_right; auto|].
    fast_cancel.
    erewrite <- app_assoc, <- sepcon_assoc, (sepcon_comm (atomic_loc _ _ _ _ _)), replace_nth_sepcon,
      update_entries_hist; eauto; omega.
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

Lemma body_init_table : semax_body Vprog Gprog f_init_table init_table_spec.
Proof.
  start_function.
  forward_for_simple_bound size (EX i : Z, PROP () LOCAL (gvar _m_entries p)
    SEP (EX entries : list (val * val),
      !!(Zlength entries = i) &&
        @data_at CompSpecs Ews (tarray tentry size) (entries ++ repeat (Vundef, Vundef) (Z.to_nat (size - i))) p *
        atomic_entries Tsh entries (repeat ([], []) (Z.to_nat i)))).
  { change size with 16384; computable. }
  { change size with 16384; computable. }
  - Exists (@nil (val * val)); entailer!.
    rewrite data_at__eq; unfold default_val; simpl.
    rewrite repeat_list_repeat, Z.sub_0_r; auto.
  - Intros entries.
    forward_call (0, k_R).
    { unfold k_R; entailer!.
      rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
      apply andp_right; auto.
      eapply derives_trans, precise_weak_precise; auto.
      apply precise_andp2; auto. }
    Intro k.
    forward.
    forward_call (0, v_R).
    { unfold v_R; entailer!.
      rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
      apply andp_right; auto.
      eapply derives_trans, precise_weak_precise; auto. }
    Intro v.
    forward.
    assert (0 <= Zlength entries < Zlength (entries ++
      repeat (Vundef, Vundef) (Z.to_nat (size - Zlength entries)))).
    { rewrite Zlength_app, Zlength_repeat, Z2Nat.id; omega. }
    subst; rewrite upd_Znth_twice, upd_complete_gen by (auto; omega).
    Exists (entries ++ [(k, v)]); entailer!.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; auto.
    + rewrite upd_Znth_same by auto.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
      unfold atomic_entries.
      rewrite Z2Nat.inj_add, repeat_plus by omega; simpl.
      rewrite combine_app, map_app, sepcon_app; simpl.
      unfold atomic_entry; entailer!.
      { rewrite repeat_length, Zlength_correct, Nat2Z.id; auto. }
  - Intros entries.
    rewrite Zminus_diag, app_nil_r.
    forward.
    Exists entries; entailer!.
Qed.

Lemma body_freeze_table : semax_body Vprog Gprog f_freeze_table freeze_table_spec.
Proof.
  start_function.
  assert_PROP (Zlength entries = size) as Hlen by entailer!.
  forward_for_simple_bound size (EX i : Z, PROP () LOCAL (gvar _m_entries p; temp _keys keys; temp _values values)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p;
         atomic_entries Tsh (sublist i (Zlength entries) entries) (sublist i (Zlength entries) h);
         EX lk : list Z, EX lv : list Z, !!(Zlength lk = i /\ Zlength lv = i /\
           Forall2 full_hist (map fst (sublist 0 i h)) lk /\ Forall2 full_hist (map snd (sublist 0 i h)) lv) &&
           data_at Tsh (tarray tint size) (map (fun x => vint x) lk ++ repeat Vundef (Z.to_nat (Zlength entries - i))) keys *
           data_at Tsh (tarray tint size) (map (fun x => vint x) lv ++ repeat Vundef (Z.to_nat (Zlength entries - i))) values)).
  { change size with 16384; computable. }
  { change size with 16384; computable. }
  - Exists (@nil Z) (@nil Z); rewrite sublist_nil.
    go_lower; repeat (apply andp_right; [apply prop_right; auto|]).
    rewrite !sublist_same by (auto; omega).
    repeat (apply sepcon_derives; [auto|]).
    + apply andp_right; [apply prop_right; auto|].
      rewrite data_at__eq; unfold default_val; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r, Hlen; auto.
    + rewrite data_at__eq; unfold default_val; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r, Hlen; auto.
  - Intros lk lv.
    unfold atomic_entries.
    rewrite sublist_next with (d := (Vundef, Vundef)) by omega.
    rewrite sublist_next with (d := ([], [])) by omega; simpl.
    destruct (Znth i entries (Vundef, Vundef)) as (pki, pvi) eqn: Hpi.
    destruct (Znth i h ([], [])) as (hki, hvi) eqn: Hhi.
    unfold atomic_entry; rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    rewrite Hpi.
    forward_call (pki, vint 0, hki, k_R).
    Intros x; destruct x as (lki, ki); simpl in *.
    forward.
    rewrite atomic_loc_isptr; Intros.
    forward.
    { entailer!.
      rewrite Hpi; auto. }
    rewrite Hpi.
    forward_call (pvi, vint 0, hvi, v_R).
    Intros x; destruct x as (lvi, vi); simpl in *.
    forward.
    Exists (lk ++ [ki]) (lv ++ [vi]).
    go_lower.
    unfold v_R, k_R; Intros.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    apply andp_right.
    + apply prop_right.
      repeat (split; [repeat split; auto; omega|]).
      rewrite sublist_split with (mid := i), sublist_len_1 with (d := ([], [])), !map_app, Hhi by omega.
      split; apply Forall2_app; auto; repeat constructor; unfold full_hist; eauto.
    + rewrite !emp_sepcon, !sepcon_assoc; apply sepcon_derives; [auto|].
      apply sepcon_derives; [auto|].
      rewrite !map_app; simpl.
      replace (i + 1) with (Zlength (map (fun x => vint x) lk ++ [vint ki]))
        by (rewrite Zlength_app, Zlength_map, Zlength_cons, Zlength_nil; omega).
      rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      replace (Zlength (map _ _ ++ _)) with (Zlength (map (fun x => vint x) lv ++ [vint vi]))
        by (rewrite !Zlength_app, !Zlength_map, !Zlength_cons, !Zlength_nil; omega).
      rewrite <- upd_complete_gen by (rewrite Zlength_map; omega).
      rewrite !Zlength_map.
      apply sepcon_derives; [replace i with (Zlength lk) | replace i with (Zlength lv)]; auto.
  - Intros lk lv; forward.
    rewrite Hlen, Zminus_diag, !app_nil_r, !sublist_nil.
    repeat match goal with H : Forall2 _ (map _ (sublist _ _ _)) _ |- _ =>
      rewrite sublist_same in H by (auto; omega) end.
    Exists lk lv; entailer!.
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Lemma add_n_items_length : forall n h lk lv li ls h', add_n_items_trace n h lk lv li ls h' ->
  Zlength h' = Zlength h.
Proof.
  induction 1; auto.
  destruct Hadd; omega.
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
    + destruct Hi as (? & ? & ? & ? & ? & ? & Hi1 & Hi2 & ?); rewrite Hi1, Hi2.
      rewrite !map_app, !Forall_app; repeat constructor; auto; try (apply ordered_snoc; auto).
      rewrite app_cons_assoc; repeat apply ordered_snoc; auto.
      apply newer_snoc; auto.
    + destruct Hi as ((? & ? & Hi1) & -> & ?).
      split; auto.
      destruct Hi1 as [-> | (? & ? & ? & ->)]; rewrite !map_app, !Forall_app; repeat constructor; auto;
        try (apply ordered_snoc; auto).
      rewrite 2app_cons_assoc; repeat apply ordered_snoc; auto; repeat apply newer_snoc; auto; omega.
  - destruct Hrest as ((? & ? & ? & Hcase & ? & ? & -> & ?) & _); auto; simpl in *.
    split; auto.
    destruct Hcase as [-> | (? & ? & (? & ?) & ->)]; rewrite map_app, Forall_app; repeat constructor; auto.
    + apply ordered_snoc; auto.
    + rewrite 2app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; [apply ordered_snoc|]; auto|];
        repeat apply newer_snoc; auto.
  - destruct Hrest as (_ & ->); auto.
Qed.

Corollary add_n_items_trace_wf : forall n h lk lv li ls h', add_n_items_trace n h lk lv li ls h' ->
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

Lemma f_pred_precise : forall tsh sh entries p t locksp lockt resultsp res, readable_share sh ->
  precise (f_lock_pred tsh sh entries p t locksp lockt resultsp res).
Proof.
  intros; unfold f_lock_pred.
  apply selflock_precise.
  unfold f_lock_inv.
  eapply derives_precise' with (Q := data_at_ _ _ _ *
    fold_right sepcon emp (map (fun p => (EX h : hist, atomic_loc sh (fst p) (vint 0) k_R h) *
                                         (EX h : hist, atomic_loc sh (snd p) (vint 0) v_R h)) entries) *
    data_at_ sh _ _ * data_at_ _ _ _ * data_at_ _ _ _).
  - Intros hists li ls; assert_PROP (Zlength entries = size) as Hlene by entailer!.
    repeat (apply sepcon_derives; try apply data_at_data_at_).
    exploit add_n_items_length; eauto.
    rewrite Zlength_repeat, Z2Nat.id by (pose proof size_pos; omega); intro Hlenh.
    assert (Zlength entries <= Zlength hists) by omega.
    apply sepcon_list_derives; rewrite !Zlength_map, Zlength_combine, Z.min_l; auto.
    intros; rewrite Znth_map with (d' := ((Vundef, Vundef), ([], [])))
      by (rewrite Zlength_combine, Z.min_l; auto).
    rewrite Znth_map with (d' := (Vundef, Vundef)) by auto.
    rewrite Znth_combine by (setoid_rewrite Hlene; auto).
    unfold atomic_entry.
    destruct (Znth i entries (Vundef, Vundef)) eqn: Hpi.
    simpl in *; rewrite Hpi at 1.
    destruct (Znth i hists ([], [])) as (hk, hv).
    Exists hk hv; setoid_rewrite Hpi; auto.
  - repeat (apply precise_sepcon; auto).
    apply precise_fold_right.
    rewrite Forall_map, Forall_forall; intros; simpl.
    apply precise_sepcon; apply atomic_loc_precise'; auto.
Qed.

Lemma f_pred_positive : forall tsh sh entries p t locksp lockt resultsp res,
  positive_mpred (f_lock_pred tsh sh entries p t locksp lockt resultsp res).
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
    PROP ()
    LOCAL (temp _total (vint (Zlength (filter id ls))); temp _res res; temp _l lockt; temp _t (vint t);
           temp _arg tid; gvar _m_entries p; gvar _thread_locks locksp; gvar _results resultsp)
    SEP (@data_at CompSpecs sh (tarray tentry size) entries p;
         EX h : list (hist * hist), EX li : list Z,
           !!(add_n_items_trace i empty_hists (sublist 0 i [1; 2; 3]) (sublist 0 i [1; 1; 1]) li ls h) &&
           atomic_entries sh entries h;
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
         data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
         data_at_ Tsh tint res;
         lock_inv tsh lockt (f_lock_pred tsh sh entries p t locksp lockt resultsp res))).
  - Exists (@nil bool) (empty_hists : list (hist * hist)) (@nil Z); entailer!.
    constructor.
  - Intros h li.
    forward_call (i + 1, 1, p, sh, entries, h).
    { repeat (split; auto; try computable; try omega).
      + pose proof (Int.min_signed_neg); omega.
      + transitivity 4; [omega | computable].
      + erewrite add_n_items_length, Zlength_repeat, Z2Nat.id; eauto.
        pose proof size_pos; omega.
      + eapply add_n_items_trace_wf; eauto. }
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
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
      repeat (apply andp_right; [apply prop_right; auto|]).
      Exists (x ++ [s]) h' (li ++ [j]); entailer!.
      erewrite !sublist_split with (lo := 0)(mid := i)(hi := i + 1), !sublist_len_1
        by (rewrite ?Zlength_cons, ?Zlength_nil; auto; omega).
      econstructor; eauto.
      change [1; 2; 3] with (map Z.succ (upto 3)); change [1; 1; 1] with (repeat 1 3).
      rewrite Znth_map', Znth_upto, Znth_repeat; auto; simpl; omega.
  - Intros ls h li.
    forward.
    forward_call (lockt, tsh, f_lock_inv sh entries p t locksp lockt resultsp res,
                  f_lock_pred tsh sh entries p t locksp lockt resultsp res).
    { lock_props.
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
  unfold field_at; simpl.
  rewrite field_compatible_cons; simpl; entailer.
  (* temporarily broken *)
Admitted.

Lemma atomic_entries_join : forall sh1 sh2 sh entries hists1 hists2 hists (Hjoin : sepalg.join sh1 sh2 sh)
  (Hlen : Zlength entries = Zlength hists)
  (Hlen1 : Zlength hists1 = Zlength hists) (Hlen2 : Zlength hists2 = Zlength hists)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (Hhists : forall i, Znth i hists ([], []) = (fst (Znth i hists1 ([], [])) ++ fst (Znth i hists2 ([], [])),
     (snd (Znth i hists1 ([], [])) ++ snd (Znth i hists2 ([], []))))),
  atomic_entries sh1 entries hists1 * atomic_entries sh2 entries hists2 =
  !!(forall i, disjoint (fst (Znth i hists1 ([], []))) (fst (Znth i hists2 ([], []))) /\
               disjoint (snd (Znth i hists1 ([], []))) (snd (Znth i hists2 ([], [])))) &&
    atomic_entries sh entries hists.
Proof.
  induction entries; unfold atomic_entries; simpl; intros.
  { exploit Zlength_nil_inv; eauto; intro; subst.
    exploit (Zlength_nil_inv hists1); auto; intro; subst.
    exploit (Zlength_nil_inv hists2); auto; intro; subst.
    rewrite prop_true_andp, sepcon_emp; auto.
    intro; rewrite Znth_nil; simpl; auto. }
  destruct hists; [exploit (Zlength_nil_inv (a :: entries)); eauto; discriminate|].
  destruct hists1; [exploit Zlength_nil_inv; eauto; discriminate|].
  destruct hists2; [exploit Zlength_nil_inv; eauto; discriminate|].
  rewrite !Zlength_cons in *; simpl.
  destruct a, p, p0 as (hk1, hv1), p1 as (hk2, hv2).
  unfold atomic_entry.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2)); [apply mpred_ext; cancel|] end.
  setoid_rewrite (IHentries _ _ hists); auto; try omega.
  specialize (Hhists 0); rewrite !Znth_0_cons in Hhists; inv Hhists.
  match goal with |- (?P1 * ?Q1 * (?P2 * ?Q2) * ?R) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2) * R); [apply mpred_ext; cancel|] end.
  erewrite !atomic_loc_join by eauto.
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
  - intros.
    destruct (zlt i 0); [rewrite !Znth_underflow; simpl; auto|].
    specialize (Hhists (i + 1)).
    rewrite !Znth_pos_cons, Z.add_simpl_r in Hhists by omega; auto.
Qed.

Corollary atomic_entries_join_nil : forall sh1 sh2 sh entries
  (Hjoin : sepalg.join sh1 sh2 sh) (Hlen : Zlength entries = size)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_entries sh1 entries empty_hists * atomic_entries sh2 entries empty_hists =
  atomic_entries sh entries empty_hists.
Proof.
  intros; erewrite atomic_entries_join with (sh := sh); try assumption.
  rewrite prop_true_andp; eauto.
  - intro; rewrite Znth_repeat; simpl; auto.
  - rewrite Zlength_repeat, Z2Nat.id; auto.
    pose proof size_pos; omega.
  - reflexivity.
  - reflexivity.
  - intro; rewrite Znth_repeat; auto.
Qed.

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
  Intro entries.
  destruct (split_shares 3 Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  rewrite <- seq_assoc.
  destruct (split_readable_share Tsh) as (sh1 & sh2 & ? & ? & ?); auto.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
    LOCAL (temp _total (vint 0); lvar _values (tarray tint 16384) values;
           lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs Ews (tarray tentry size) entries m_entries;
         atomic_entries Tsh entries empty_hists;
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
             (f_lock_pred sh2 (Znth j shs Ews) entries m_entries j locksp (Znth j locks Vundef)
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
    forward_call (l, Tsh, f_lock_pred sh2 (Znth i shs Ews) entries m_entries i locksp l resp r).
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
    rewrite (sepcon_comm _ (@data_at CompSpecs Ews (tarray tentry size) entries m_entries)), !sepcon_assoc;
      apply sepcon_derives; [auto|].
    rewrite <- !sepcon_assoc, (sepcon_comm _ (atomic_entries Tsh entries empty_hists)), !sepcon_assoc;
      apply sepcon_derives; [auto|].
    rewrite ?sepcon_emp, ?emp_sepcon; rewrite ?sepcon_assoc.
    rewrite <- !sepcon_assoc.
    match goal with |- _ |-- ?P * ?Q => rewrite (sepcon_comm P Q) end.
    rewrite !sepcon_assoc; apply sepcon_derives; [auto|].
    rewrite <- 2sepcon_assoc, sepcon_comm, !sepcon_assoc.
    destruct r; try contradiction.
    destruct l; try contradiction.
    repeat (apply sepcon_derives; [apply derives_refl|]).
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
         EX sh' : share, !!(sepalg.join sh (Share.comp Ews) sh') && atomic_entries sh' entries empty_hists;
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         data_at sh (tarray (tptr tint) 3) res resp;
         fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i 3 res));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) res);
         data_at sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) locks);
         fold_right sepcon emp (map (fun j => lock_inv (if zlt j i then sh1 else Tsh) (Znth j locks Vundef)
           (f_lock_pred sh2 (Znth j shs Ews) entries m_entries j locksp (Znth j locks Vundef)
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
    forward_spawn (share * share * list (val * val) * val * Z * val * val * val * val)%type
      (f_, t, (Znth i shs Ews, sh2, entries, m_entries, i, locksp, Znth i locks Vundef, resp, Znth i res Vundef),
    fun (x : (share * share * list (val * val) * val * Z * val * val * val * val)%type) (tid : val) =>
    let '(sh, tsh, entries, p, t, locksp, lockt, resultsp, res) := x in
    fold_right sepcon emp
      [!!(0 <= t < 3 /\ isptr lockt /\ readable_share sh /\ readable_share tsh) && emp;
        data_at sh (tarray tentry size) entries p; atomic_entries sh entries empty_hists;
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at sh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        data_at sh (tarray (tptr tint) 3) (upd_Znth t (repeat Vundef 3) res) resultsp;
        data_at_ Tsh tint res;
        lock_inv tsh lockt (f_lock_pred tsh sh entries p t locksp lockt resultsp res)]).
    { unfold spawn_pre; go_lower.
      Exists _arg (fun x : (share * share * list (val * val) * val * Z * val * val * val * val) =>
        let '(sh, tsh, entries, p, t, locksp, lockt, resultsp, res) := x in
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
        rewrite <- (atomic_entries_join_nil _ _ _ _ Hj3'); auto.
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
    rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
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
    PROP (readable_share (fst x); sepalg_list.list_join (fst x) (sublist i 3 shs) Ews;
          Zlength (snd x) = i;
          Forall (fun p => let '(h, li, ls) := p in add_n_items_trace 3 empty_hists [1; 2; 3] [1; 1; 1] li ls h)
            (snd x))
    LOCAL (let ls := map snd (snd x) in temp _total (vint (Zlength (filter id (concat ls))));
           lvar _values (tarray tint 16384) values; lvar _keys (tarray tint 16384) keys; gvar _results resp;
           gvar _thread_locks locksp; gvar _m_entries m_entries)
    SEP (@data_at CompSpecs (fst x) (tarray tentry size) entries m_entries;
         EX sh' : share, !!(sepalg_list.list_join sh' (sublist i 3 shs) Tsh) &&
           let h := map fst (map fst (snd x)) in atomic_entries sh' entries (concat (empty_hists :: h));
         data_at_ Tsh (tarray tint 16384) values; data_at_ Tsh (tarray tint 16384) keys;
         data_at (fst x) (tarray (tptr tint) 3) res resp;
         let ls := map snd (snd x) in fold_right sepcon emp (map (fun j =>
           data_at Tsh tint (vint (Zlength (filter id (Znth j ls [])))) (Znth j res Vundef)) (upto (Z.to_nat i)));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) (sublist i 3 res));
         data_at (fst x) (tarray (tptr (Tstruct _lock_t noattr)) 3) locks locksp;
         fold_right sepcon emp (map (malloc_token Tsh (sizeof (Tstruct _lock_t noattr))) (sublist i 3 locks));
         fold_right sepcon emp (map (fun j => lock_inv (if zlt j i then Tsh else sh1) (Znth j locks Vundef)
           (f_lock_pred sh2 (Znth j shs Ews) entries m_entries j locksp
              (Znth j locks Vundef) resp (Znth j res Vundef))) (upto 3)))).
  { rewrite !(sublist_same 0 3) by auto.
    Exists (sh, @nil (list (hist * hist) * list Z * list bool)) sh'; go_lower; entailer'.
    apply prop_right.
    match goal with H : sepalg_list.list_join _ (sublist _ _ _) _ |- _ => rewrite sublist_nil in H; inv H end.
    split; auto; split; auto.
    eapply sepalg_list.list_join_assoc2 in Hshs; [|eapply sepalg.join_comm, comp_join_top].
    destruct Hshs as (shd & Hjoin' & ?).
    apply sepalg.join_comm in Hjoin'; exploit (sepalg.join_eq(x := sh)(y := Share.comp Ews)(z := shd)(z' := sh'));
      auto; intro; subst; auto. }
  { (* third loop *)
    destruct x as (sh3, lr); Intros sh3'; simpl in *.
    rewrite (extract_nth_sepcon (map _ (upto 3)) i) by (rewrite Zlength_map; auto).
    erewrite Znth_map, Znth_upto by (auto; simpl; omega).
    destruct (zlt i i); [omega|].
    rewrite lock_inv_isptr; Intros.
    forward.
    forward_call (Znth i locks Vundef, sh1, f_lock_pred sh2 (Znth i shs Ews) entries m_entries i locksp
      (Znth i locks Vundef) resp (Znth i res Vundef)).
    forward_call (Znth i locks Vundef, Tsh, sh2,
      |>f_lock_inv (Znth i shs Ews) entries m_entries i locksp (Znth i locks Vundef) resp (Znth i res Vundef),
      |>f_lock_pred sh2 (Znth i shs Ews) entries m_entries i locksp (Znth i locks Vundef) resp (Znth i res Vundef)).
    { lock_props.
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
      admit. (* lock size *) }
    unfold f_lock_inv at 1; Intros hi lii lsi.
    assert (0 <= i < Zlength shs) by omega.
    forward.
    { apply Forall_Znth; auto. }
    { entailer!.
      rewrite upd_Znth_same; auto. }
    rewrite upd_Znth_same by auto.
    forward.
    erewrite sublist_next with (l := res) by (auto; omega); simpl.
    forward_call (Znth i res Vundef, sizeof tint).
    { entailer!. }
    { rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ (Znth i res Vundef))), !sepcon_assoc;
        apply sepcon_derives; [|cancel_frame].
      apply data_at_memory_block. }
    forward.
    assert (3 <= Zlength shs) by omega.
    match goal with H : sepalg_list.list_join sh3 _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|??? w1 ? Hj1]; subst end.
    match goal with H : sepalg_list.list_join sh3' _ _ |- _ => rewrite sublist_next with (d := Ews) in H by auto;
      inversion H as [|??? w1' ? Hj1']; subst end.
    go_lower; Exists (w1, lr ++ [(hi, lii, lsi)]) w1'; entailer'.
    apply andp_right.
    - admit.
    - admit. }
    Print freeze_table_spec.
  Intros x sh''; destruct x as (?, lr); simpl in *.
  repeat match goal with H : sepalg_list.list_join _ (sublist 3 3 _) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward_call (Ews, m_entries, entries, map fst (map fst lr), keys, values).
Admitted.

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
  destruct Htrace as (Hlen & Hbounds & ((t & Ht & Hi1) & Hr0) & (tv & Htv & Hi2) & Hrest).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. } }
  assert (value_of_hist (fst (Znth i h' ([], []))) = vint k) as Hk'.
  { destruct Hi1 as [-> | (? & ? & [-> | (? & ? & ->)])].
    - rewrite value_of_hist_snoc; auto.
    - rewrite app_cons_assoc, value_of_hist_snoc; auto.
    - rewrite 2app_cons_assoc, value_of_hist_snoc; auto. }
  assert (wf_hists h') as Hwf'; [|split; auto; split].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst.
      split; [|rewrite Hi2, map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto].
      destruct Hi1 as [-> | (? & ? & [-> | (? & ? & ->)])]; rewrite map_app, Forall_app;
        repeat constructor; auto; try (apply ordered_snoc; auto).
      * rewrite app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; auto|].
        apply newer_snoc; auto.
      * rewrite 2app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; [apply ordered_snoc|]; auto|];
          repeat apply newer_snoc; auto.
    + destruct Hrest as ((? & ? & ? & Hcase & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      destruct Hcase as [-> | (? & ? & (? & ?) & ->)]; rewrite map_app, Forall_app; repeat constructor; auto.
      * apply ordered_snoc; auto.
      * rewrite 2app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; [apply ordered_snoc|]; auto|];
          repeat apply newer_snoc; auto.
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
    destruct Hrest as ((? & r1 & ? & Hcase & ? & ? & -> & Heq) & _); auto; simpl in *.
    assert (value_of_hist (fst (Znth j h ([], []))) <> vint 0).
    { intro X; rewrite X in Hk0; contradiction Hk0; auto. }
    destruct Hcase as [-> | (? & ? & (? & ?) & ->)].
    + rewrite value_of_hist_snoc, Heq; auto.
    + rewrite 2app_cons_assoc, value_of_hist_snoc, Heq; auto.
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
        specialize (Hrest ((j + hash k) mod size)); destruct Hrest as ((? & r1 & ? & Hcase & ? & ? & ?) & _).
        { unfold indices; rewrite in_map_iff.
          exists j; split; [rewrite Z.add_comm; auto|].
          rewrite In_upto, Z2Nat.id; omega. }
        rewrite upd_Znth_diff'; auto.
        simpl in *; destruct Hcase as [-> | (? & ? & ? & ->)]; [|rewrite 2app_cons_assoc];
          rewrite value_of_hist_snoc; simpl.
        * split; intro X; [absurd (r1 = Int.zero) | absurd (r1 = Int.repr k)]; auto; apply signed_inj; auto.
          rewrite Int.signed_repr; auto.
        * split; intro X; [absurd (r1 = Int.zero) | absurd (r1 = Int.repr k)]; auto; apply signed_inj; auto.
          rewrite Int.signed_repr; auto.
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
      rewrite Znth_map', Hk', Hi2, value_of_hist_snoc; simpl.
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
  destruct Hi as (t & r & Ht & Hi1 & Hi2 & Hr0).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. }}
  assert (wf_hists h') as Hwf'; [|split; auto].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst; rewrite Hhi in *.
      split; [rewrite Hi1, map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto|].
      destruct Hi2 as [(? & ? & ->) | (? & ? & ? & ->)]; auto.
      rewrite map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto.
    + destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      rewrite map_app, Forall_app; repeat constructor; auto.
      apply ordered_snoc; auto.
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
        rewrite Hi1, value_of_hist_snoc; simpl.
        destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; [|rewrite Int.signed_repr by auto]; tauto. }
      rewrite Zlength_rebase in Hz by omega.
      rewrite Znth_rebase, Hlenm in Hcase by omega.
      unfold make_map in Hcase; rewrite Znth_map with (d' := ([], [])) in Hcase; simpl in Hcase.
      destruct (eq_dec ((z + hash k) mod size) i); auto.
      specialize (Hrest ((z + hash k) mod size)); destruct Hrest as ((? & r1 & ? & Hfst & ? & ? & ?) & _).
      { unfold indices.
        rewrite in_map_iff.
        exists z; split; [rewrite Z.add_comm; auto|].
        rewrite In_upto, Z2Nat.id.
        rewrite Hlenm in Hle; replace (Zlength h') with size in Hle by omega.
        destruct (eq_dec z ((i - hash k) mod size)); [|omega].
        contradiction n; rewrite e, Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto; omega.
        { apply Z_mod_lt, size_pos. } }
      replace (Zlength h') with size in Hcase by omega.
      simpl in *; rewrite Hfst, value_of_hist_snoc in Hcase; simpl in Hcase.
      destruct Hcase; [absurd (r1 = Int.repr k) | absurd (r1 = Int.zero)]; auto; apply signed_inj; auto.
      rewrite Int.signed_repr; auto.
      { apply Z_mod_lt; omega. } }
    simpl in *; rewrite Hz, Hi1.
    replace (value_of_hist (hk ++ _)) with (vint r) by (rewrite value_of_hist_snoc; auto); simpl.
    destruct Hi2 as [(? & ? & Hi2) | (? & ? & ? & Hi2)]; rewrite Hi2; clear dependent z; subst; simpl.
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
      * destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & Heq) & _); auto.
        rewrite value_of_hist_snoc; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + rewrite value_of_hist_snoc; simpl.
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
        inv Hj; rewrite Hi1, Hi2.
        rewrite !value_of_hist_snoc; simpl.
        rewrite !Int.signed_repr; auto. }
      rewrite upd_Znth_diff' in Hj; rewrite ?Zlength_map; auto.
      rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & Heq) & _); auto.
        rewrite value_of_hist_snoc; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + replace (Zlength h') with size by omega; apply Z_mod_lt, size_pos.
    + assert (In r (map fst (rebase (make_map h') (hash k)))).
      { rewrite in_map_iff.
        unfold rebase, make_map; eexists; rewrite rotate_In, in_map_iff.
        split; [|do 2 eexists; eauto; apply Znth_In with (i0 := i); omega].
        rewrite Hi1, value_of_hist_snoc; simpl.
        apply Int.signed_repr; destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; auto.
        { pose proof (hash_range k).
          rewrite Zlength_map; omega. } }
      destruct Hspec as (Hnk & Hnz), Hi2 as [(? & ? & ?) | (? & ?)]; subst;
        [contradiction Hnz | contradiction Hnk].
Qed.
