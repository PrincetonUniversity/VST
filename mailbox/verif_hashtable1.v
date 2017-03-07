Require Import progs.ghost.
Require Import mailbox.verif_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.hashtable1.
Require Import mailbox.hashtable.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Definition atomic_entry sh pk pv hk hv :=
  atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv.

Definition atomic_entries sh entries hists := fold_right sepcon emp
  (map (fun x => let '((pk, pv), (hk, hv)) := x in atomic_entry sh pk pv hk hv) (combine entries hists)).

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

(*Lemma index_of_iff_out : forall m k, index_of m k = None <-> ~In k (map fst m).
Proof.
  split; intro.
  - induction m; auto; simpl in *.
    destruct a.
    destruct (eq_dec z k); [discriminate|].
    destruct (index_of m k); [discriminate|].
    intros [? | ?]; auto.
    contradiction IHm.
  - apply index_of_out.
    rewrite Forall_forall; repeat intro; contradiction H.
    rewrite in_map_iff; eauto.
Qed.

Corollary get_fail_iff : forall m k, get m k = None <-> ~In k (map fst m).
Proof.
  intros; unfold get; rewrite <- index_of_iff_out.
  destruct (index_of m k); simpl; split; auto; discriminate.
Qed.*)

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

Definition Gprog : funspecs := ltac:(with_library prog [CAS_SC_spec; load_SC_spec; store_SC_spec;
  integer_hash_spec; set_item_spec; get_item_spec]).

Lemma body_integer_hash: semax_body Vprog Gprog f_integer_hash integer_hash_spec.
Proof.
  start_function.
  forward.
Qed.

Opaque upto.

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Ltac entailer_for_return ::= go_lower; entailer'.

Lemma failed_CAS_fst : forall v h h', Forall2 (failed_CAS v) h h' -> map snd h' = map snd h.
Proof.
  induction 1; auto.
  destruct H as (? & ? & ? & ? & ? & ? & ? & ?); simpl; f_equal; auto.
Qed.

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
    Intros x; destruct x as (t, v); simpl in *.
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
          intro; rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
          split.
          * intros [Hin | Hin].
            { rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hnew; subst; auto. } }
            simpl in Hin; destruct Hin; [subst | contradiction].
            replace ((i + (key * _) mod _) mod _) with (i1 mod size).
            rewrite upd_Znth_same by auto.
            simpl; rewrite Heq, Hhi; repeat eexists; eauto; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * intro Hout; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl; auto. }
          * rewrite Z.add_simpl_r.
            admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        assert (Zlength (map (fun x => let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk *
          atomic_loc sh pv (vint 0) v_R hv) (combine entries h')) = Zlength entries) as Hlen1.
        { rewrite Zlength_map, Zlength_combine, Z.min_l; auto; omega. }
        assert (Zlength (upd_Znth (i1 mod 16384) (map (fun x =>
          let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv)
          (combine entries h')) (atomic_loc sh pki (vint 0) k_R (hki ++ [(t, Load (Vint i0))]) *
                                 atomic_loc sh pvi (vint 0) v_R hvi)) = Zlength entries) as Hupd.
        { rewrite upd_Znth_Zlength; rewrite Hlen1; auto. }
        rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite Hupd, Zlength_map, Zlength_combine, upd_Znth_Zlength, ?Z.min_l; auto; omega. }
        rewrite Hupd; intros.
        destruct (eq_dec i2 (i1 mod size)).
        * subst; rewrite upd_Znth_same by (rewrite Hlen1; auto).
          erewrite Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine.
          setoid_rewrite Hpi.
          rewrite upd_Znth_same; auto.
          { rewrite upd_Znth_Zlength; auto; omega. }
          { rewrite Zlength_combine, upd_Znth_Zlength, Z.min_l; auto; omega. }
        * rewrite upd_Znth_diff' by (rewrite ?Hlen1; auto).
          erewrite !Znth_map with (d' := (Vundef, Vundef, ([], []))), !Znth_combine;
            rewrite ?Zlength_combine, ?upd_Znth_Zlength, ?Z.min_l; auto; try omega.
          destruct (Znth i2 entries (Vundef, Vundef)).
          rewrite upd_Znth_diff'; auto. }
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
      Intros x; destruct x as (t', v); simpl in *.
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
          rewrite Hpi; auto. }
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
        Intros x; destruct x as (t'', v); simpl in *; subst.
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
            intro; rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
            split.
            * intros [Hin | Hin].
              { rewrite upd_Znth_diff'; auto.
                match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
                { intro; contradiction Hnew; subst; auto. } }
              simpl in Hin; destruct Hin; [subst | contradiction].
              replace ((i + (key * _) mod _) mod _) with (i1 mod size).
              rewrite upd_Znth_same by auto.
              simpl; rewrite Heq, Hhi; do 3 eexists; [|split; [right; do 3 eexists; [|reflexivity]|]]; auto;
                repeat split; auto.
              { intro; subst; contradiction n; auto. }
              match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
                symmetry; apply H; auto end.
              rewrite ordered_last_value; auto.
            * intro Hout; rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hout; subst; simpl; auto. }
            * rewrite Z.add_simpl_r.
              admit. (* list is long enough *) }
          apply andp_right; [apply prop_right; auto|].
          fast_cancel.
          rewrite <- app_assoc.
          assert (Zlength (map (fun x => let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk *
            atomic_loc sh pv (vint 0) v_R hv) (combine entries h')) = Zlength entries) as Hlen1.
          { rewrite Zlength_map, Zlength_combine, Z.min_l; auto; omega. }
          assert (Zlength (upd_Znth (i1 mod 16384) (map (fun x =>
            let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv)
            (combine entries h')) (atomic_loc sh pki (vint 0) k_R (hki ++ [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key)); (t'', Load (Vint i0))]) *
            atomic_loc sh pvi (vint 0) v_R hvi)) = Zlength entries) as Hupd.
          { rewrite upd_Znth_Zlength; rewrite Hlen1; auto. }
          simpl; rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives.
          { rewrite Hupd, Zlength_map, Zlength_combine, upd_Znth_Zlength, ?Z.min_l; auto; omega. }
          rewrite Hupd; intros.
          destruct (eq_dec i2 (i1 mod size)).
          * subst; rewrite upd_Znth_same by (rewrite Hlen1; auto).
            erewrite Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine.
            setoid_rewrite Hpi.
            rewrite upd_Znth_same; auto.
            { rewrite upd_Znth_Zlength; auto; omega. }
            { rewrite Zlength_combine, upd_Znth_Zlength, Z.min_l; auto; omega. }
          * rewrite upd_Znth_diff' by (rewrite ?Hlen1; auto).
            erewrite !Znth_map with (d' := (Vundef, Vundef, ([], []))), !Znth_combine;
              rewrite ?Zlength_combine, ?upd_Znth_Zlength, ?Z.min_l; auto; try omega.
            destruct (Znth i2 entries (Vundef, Vundef)).
            rewrite upd_Znth_diff'; auto. }
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
        + intro Hin.
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
      assert (Zlength (map (fun x => let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk *
        atomic_loc sh pv (vint 0) v_R hv) (combine entries h')) = Zlength entries) as Hlen1.
      { rewrite Zlength_map, Zlength_combine, Z.min_l; auto; omega. }
      assert (Zlength (upd_Znth (i1 mod 16384) (map (fun x =>
        let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv)
        (combine entries h')) (atomic_loc sh pvi (vint 0) v_R (hvi ++ [(t', Store (vint value))]) *
        atomic_loc sh pki (vint 0) k_R hki')) = Zlength entries) as Hupd.
      { rewrite upd_Znth_Zlength; rewrite Hlen1; auto. }
      rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives.
      { rewrite Hupd, Zlength_map, Zlength_combine, upd_Znth_Zlength, ?Z.min_l; auto; omega. }
      rewrite Hupd; intros.
      destruct (eq_dec i2 (i1 mod size)).
      * subst; rewrite upd_Znth_same by (rewrite Hlen1; auto).
        erewrite Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine.
        setoid_rewrite Hpi.
        rewrite upd_Znth_same, sepcon_comm; auto.
        { rewrite upd_Znth_Zlength; auto; omega. }
        { rewrite Zlength_combine, upd_Znth_Zlength, Z.min_l; auto; omega. }
      * rewrite upd_Znth_diff' by (rewrite ?Hlen1; auto).
        erewrite !Znth_map with (d' := (Vundef, Vundef, ([], []))), !Znth_combine;
          rewrite ?Zlength_combine, ?upd_Znth_Zlength, ?Z.min_l; auto; try omega.
        destruct (Znth i2 entries (Vundef, Vundef)).
        rewrite upd_Znth_diff'; auto.
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

Lemma failed_load_fst : forall v h h', Forall2 (failed_load v) h h' -> map snd h' = map snd h.
Proof.
  induction 1; auto.
  destruct H as (? & ? & ? & ? & ? & ? & ? & ?); simpl; f_equal; auto.
Qed.

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
    Intros x; destruct x as (t, v); simpl in *.
    destruct v; try contradiction.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ pvi).
      forward.
      { entailer!.
        rewrite Hpi; auto. }
      forward_call (sh, pvi, vint 0, hvi, fun (h : hist) => emp, v_R, fun (h : hist) (v : val) => emp).
      { entailer!.
        rewrite Hpi; auto. }
      { repeat (split; auto).
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros x; destruct x as (t', v); simpl in *.
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
          + intro Hin.
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
      assert (Zlength (map (fun x => let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk *
        atomic_loc sh pv (vint 0) v_R hv) (combine entries h')) = Zlength entries) as Hlen1.
      { rewrite Zlength_map, Zlength_combine, Z.min_l; auto; omega. }
      assert (Zlength (upd_Znth (i1 mod 16384) (map (fun x =>
        let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv)
        (combine entries h')) (atomic_loc sh pvi (vint 0) v_R (hvi ++ [(t', Load (Vint v))]) *
          atomic_loc sh pki (vint 0) k_R (hki ++ [(t, Load (vint key))]))) = Zlength entries) as Hupd.
      { rewrite upd_Znth_Zlength; rewrite Hlen1; auto. }
      simpl; rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives.
      { rewrite Hupd, Zlength_map, Zlength_combine, upd_Znth_Zlength, ?Z.min_l; auto; omega. }
      rewrite Hupd; intros.
      destruct (eq_dec i0 (i1 mod size)).
      * subst; rewrite upd_Znth_same by (rewrite Hlen1; auto).
        erewrite Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine.
        setoid_rewrite Hpi.
        rewrite upd_Znth_same, sepcon_comm; auto.
        { rewrite upd_Znth_Zlength; auto; omega. }
        { rewrite Zlength_combine, upd_Znth_Zlength, Z.min_l; auto; omega. }
      * rewrite upd_Znth_diff' by (rewrite ?Hlen1; auto).
        erewrite !Znth_map with (d' := (Vundef, Vundef, ([], []))), !Znth_combine;
          rewrite ?Zlength_combine, ?upd_Znth_Zlength, ?Z.min_l; auto; try omega.
        destruct (Znth i0 entries (Vundef, Vundef)).
        rewrite upd_Znth_diff'; auto.
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
          + intro Hin.
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
        assert (Zlength (map (fun x => let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk *
          atomic_loc sh pv (vint 0) v_R hv) (combine entries h')) = Zlength entries) as Hlen1.
        { rewrite Zlength_map, Zlength_combine, Z.min_l; auto; omega. }
        assert (Zlength (upd_Znth (i1 mod 16384) (map (fun x =>
          let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv)
          (combine entries h')) (atomic_loc sh pki (vint 0) k_R (hki ++ [(t, Load (vint 0))]) *
            atomic_loc sh pvi (vint 0) v_R hvi)) = Zlength entries) as Hupd.
        { rewrite upd_Znth_Zlength; rewrite Hlen1; auto. }
        simpl; rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite Hupd, Zlength_map, Zlength_combine, upd_Znth_Zlength, ?Z.min_l; auto; omega. }
        rewrite Hupd; intros.
        destruct (eq_dec i0 (i1 mod size)).
        -- subst; rewrite upd_Znth_same by (rewrite Hlen1; auto).
           erewrite Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine.
           setoid_rewrite Hpi.
           rewrite upd_Znth_same; auto.
           { rewrite upd_Znth_Zlength; auto; omega. }
           { rewrite Zlength_combine, upd_Znth_Zlength, Z.min_l; auto; omega. }
        -- rewrite upd_Znth_diff' by (rewrite ?Hlen1; auto).
           erewrite !Znth_map with (d' := (Vundef, Vundef, ([], []))), !Znth_combine;
             rewrite ?Zlength_combine, ?upd_Znth_Zlength, ?Z.min_l; auto; try omega.
           destruct (Znth i0 entries (Vundef, Vundef)).
           rewrite upd_Znth_diff'; auto.
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
          intro; rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
          split.
          * intros [Hin | Hin].
            { rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hnew; subst; auto. } }
            simpl in Hin; destruct Hin; [subst | contradiction].
            replace ((i + _) mod _) with (i1 mod size).
            rewrite upd_Znth_same by auto.
            setoid_rewrite Heq.
            rewrite Hhi; repeat eexists; eauto; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * intro Hout; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl; auto. }
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        assert (Zlength (map (fun x => let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk *
          atomic_loc sh pv (vint 0) v_R hv) (combine entries h')) = Zlength entries) as Hlen1.
        { rewrite Zlength_map, Zlength_combine, Z.min_l; auto; omega. }
        assert (Zlength (upd_Znth (i1 mod 16384) (map (fun x =>
          let '(pk, pv, (hk, hv)) := x in atomic_loc sh pk (vint 0) k_R hk * atomic_loc sh pv (vint 0) v_R hv)
          (combine entries h')) (atomic_loc sh pki (vint 0) k_R (hki ++ [(t, Load (Vint i0))]) *
            atomic_loc sh pvi (vint 0) v_R hvi)) = Zlength entries) as Hupd.
        { rewrite upd_Znth_Zlength; rewrite Hlen1; auto. }
        simpl; rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite Hupd, Zlength_map, Zlength_combine, upd_Znth_Zlength, ?Z.min_l; auto; omega. }
        rewrite Hupd; intros.
        destruct (eq_dec i2 (i1 mod size)).
        -- subst; rewrite upd_Znth_same by (rewrite Hlen1; auto).
           erewrite Znth_map with (d' := (Vundef, Vundef, ([], []))), Znth_combine.
           setoid_rewrite Hpi.
           rewrite upd_Znth_same; auto.
           { rewrite upd_Znth_Zlength; auto; omega. }
           { rewrite Zlength_combine, upd_Znth_Zlength, Z.min_l; auto; omega. }
        -- rewrite upd_Znth_diff' by (rewrite ?Hlen1; auto).
           erewrite !Znth_map with (d' := (Vundef, Vundef, ([], []))), !Znth_combine;
             rewrite ?Zlength_combine, ?upd_Znth_Zlength, ?Z.min_l; auto; try omega.
           destruct (Znth i2 entries (Vundef, Vundef)).
           rewrite upd_Znth_diff'; auto.
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
