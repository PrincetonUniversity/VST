Require Import mailbox.verif_atomics.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.lockfree_linsearch.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Definition tentry := Tstruct _entry noattr.

Definition entry_hists entries hists := fold_right_sepcon (map (fun i =>
  let '(hp, e) := (Znth i hists ([], []), Znth i entries Vundef) in
    ghost_hist (fst hp) (field_address tentry [StructField _key] e) *
    ghost_hist (snd hp) (field_address tentry [StructField _value] e)) (upto 20)).

(* In this case, let map be an association list. *)
Fixpoint index_of (m : list (Z * Z)) (k : Z) :=
  match m with
  | [] => None
  | (k1, v1) :: rest => if eq_dec k1 k then Some 0
                        else option_map Z.succ (index_of rest k)
  end.

Lemma index_of_spec : forall k m, match index_of m k with Some i => 0 <= i /\ fst (Znth i m (0, 0)) = k
  | None => ~In k (map fst m) end.
Proof.
  induction m; simpl; auto; intros.
  destruct a.
  destruct (eq_dec z k); [split; auto; computable|].
  destruct (index_of m k); simpl.
  - destruct IHm; unfold Z.succ; rewrite Znth_pos_cons, Z.add_simpl_r; [split|]; auto; omega.
  - tauto.
Qed.

Definition set m k v :=
  match index_of m k with
  | Some i => upd_Znth i m (k, v)
  | None => m ++ [(k, v)]
  end.

Definition get m k := option_map (fun i => snd (Znth i m (0, 0))) (index_of m k).

Definition value_of e :=
  match e with
  | Load v => v
  | Store v => v
  | CAS r c w => if eq_dec r c then w else r
  end.

Definition last_value (h : hist) v :=
  (* initial condition *)
  (h = [] /\ v = vint 0) \/
  exists n e, In (n, e) h /\ value_of e = v /\
  Forall (fun x => let '(m, _) := x in m <= n)%nat h.

Lemma last_value_new : forall h n e, Forall (fun x => fst x < n)%nat h ->
  last_value (h ++ [(n, e)]) (value_of e).
Proof.
  right.
  do 3 eexists; [rewrite in_app; simpl; eauto|].
  rewrite Forall_app; repeat constructor.
  eapply Forall_impl; [|eauto]; intros.
  destruct a; simpl in *; omega.
Qed.

Inductive compatible : list (hist * hist) -> list (Z * Z) -> Prop :=
| compatible_nil : compatible [] []
| compatible_cons k v m hk hv h (Hk : last_value hk (vint k)) (Hv : last_value hv (vint v)) :
    compatible ((hk, hv) :: h) ((k, v) :: m)
| compatible_zero hk hv h (Hzero : last_value hk (vint 0)) :
    compatible ((hk, hv) :: h) [].

Definition wf_map (m : list (Z * Z)) := ~In 0 (map fst m).

Definition int_op e :=
  match e with
  | Load v => exists i, v = Vint i
  | Store v => exists i, v = Vint i
  | CAS r c w => exists i1 i2 i3, r = Vint i1 /\ c = Vint i2 /\ w = Vint i3
  end.

(* Once set, a key is never reset. *)
Definition k_R (h : list hist_el) (v : val) := !!(Forall int_op h /\
  forall e, In e h -> value_of e <> vint 0 -> v = value_of e) && emp.

Definition v_R (h : list hist_el) (v : val) := emp.

Definition atomic_entry sh p := !!(field_compatible tentry [] p) && EX lkey : val, EX lval : val,
  field_at sh tentry [StructField _lkey] lkey p *
  atomic_loc sh lkey (field_address tentry [StructField _key] p) (vint 0) Tsh k_R *
  field_at sh tentry [StructField _lvalue] lval p *
  atomic_loc sh lval (field_address tentry [StructField _value] p) (vint 0) Tsh v_R.

(* Can we comprehend the per-entry histories into a broader history? *)
Definition failed_CAS k (a b : hist * hist) := exists t r,
  fst b = fst a ++ [(t, CAS (Vint r) (vint 0) (vint k))] /\
  r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a.

Definition set_item_trace (h : list (hist * hist)) k v i h' :=
  Forall2 (failed_CAS k) (sublist 0 i h) (sublist 0 i h') /\
  (let '(hk, hv) := Znth i h ([], []) in exists t r tv,
      Znth i h' ([], []) = (hk ++ [(t, CAS r (vint 0) (vint k))], hv ++ [(tv, Store (vint v))]) /\
      (r = vint 0 \/ r = vint k)) /\ sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h'.

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list val, h : list (hist * hist), m : list (Z * Z)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; Forall isptr entries; Zlength h = 20;
         wf_map m; compatible h m)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist), EX m' : list (Z * Z),
   PROP (set_item_trace h key value i h'; wf_map m'; compatible (sublist 0 i h') m';
         compatible h' (set m' key value); incl m m')
   LOCAL ()
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h').

Definition failed_load k (a b : hist * hist) := exists t r, fst b = fst a ++ [(t, Load (Vint r))] /\
  r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a.

Definition get_item_trace (h : list (hist * hist)) k v h' := exists i,
  Forall2 (failed_load k) (sublist 0 i h) (sublist 0 i h') /\
  (let '(hk, hv) := Znth i h ([], []) in exists t,
      if eq_dec v 0 then Znth i h' ([], []) = (hk ++ [(t, Load (vint 0))], hv) else
      exists tv, Znth i h' ([], []) = (hk ++ [(t, Load (vint k))], hv ++ [(tv, Load (vint v))])) /\
  sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h'.

(* Read the most recently written value. *)
Definition get_item_spec :=
 DECLARE _get_item
  WITH key : Z, p : val, sh : share, entries : list val, h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; Forall isptr entries; Zlength h = 20)
   LOCAL (temp _key (vint key); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tint ]
   EX value : Z, EX h' : list (hist * hist),
   PROP (get_item_trace h key value h')
   LOCAL ()
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h').

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; atomic_CAS_spec; atomic_load_spec;
  atomic_store_spec; set_item_spec; get_item_spec]).

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

Opaque upto.

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Ltac entailer_for_return ::= go_lower; entailer'.

Definition make_int v := match v with Vint i => Int.signed i | _ => 0 end.

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  forward.
  eapply semax_pre with (P' := EX i : Z, EX h' : list (hist * hist),
    PROP (0 <= i < 20; Forall2 (failed_CAS key) (sublist 0 i h) (sublist 0 i h');
          (* Not just that it's a failed CAS, but that it reads the corresponding value in m. *)
          sublist i (Zlength h) h = sublist i (Zlength h') h')
    LOCAL (temp _idx (vint i); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
         entry_hists entries h')).
  { Exists 0 h; rewrite sublist_nil; entailer!. }
  eapply semax_loop.
  - Intros i h'; forward.
    assert_PROP (Zlength entries = 20) by entailer!.
    assert (0 <= i < Zlength entries) by (replace (Zlength entries) with 20; auto).
    forward.
    { entailer!.
      apply isptr_is_pointer_or_null, Forall_Znth; auto. }
    rewrite extract_nth_sepcon with (i := i), Znth_map with (d' := Vundef); try rewrite Zlength_map; auto.
    unfold entry_hists; erewrite extract_nth_sepcon with (i := i)(l := map _ _), Znth_map, Znth_upto; simpl; auto;
      try omega.
    unfold atomic_entry; Intros lkey lval.
    rewrite atomic_loc_isptr.
    forward.
    forward.
    forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth i entries Vundef), lkey, vint 0,
      vint key, vint 0, fst (Znth i h' ([], [])),
      fun (h : hist) c v => !!(c = vint 0 /\ v = vint key /\ h = fst (Znth i h' ([], []))) && emp,
      k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value (fst (Znth i h' ([], []))) v0 -> v0 <> vint 0 ->
        v = v0) && emp).
(* Given that I have to do this, maybe better to remove the arguments from P. *)
    { entailer!.
      rewrite field_address_offset; simpl.
      rewrite isptr_offset_val_zero; auto.
      { rewrite field_compatible_cons; simpl.
        split; [unfold in_members; simpl|]; auto. } }
    { repeat (split; auto).
      intros ?????????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
Lemma apply_int_ops : forall v h i (Hv : verif_atomics.apply_hist (Vint i) h = Some v) (Hints : Forall int_op h),
  exists i', v = Vint i'.
Proof.
  induction h; simpl; intros.
  - inv Hv; eauto.
  - inversion Hints as [|?? Ha]; subst.
    destruct a.
    + destruct (eq_dec v0 (Vint i)); [eauto | discriminate].
    + destruct Ha; subst; eauto.
    + destruct (eq_dec r (Vint i)); [|discriminate].
      destruct Ha as (? & i' & ? & ? & ? & ?); subst.
      destruct (eq_dec (Vint i') (Vint i)); eauto.
Qed.

      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
        destruct Hvx; subst.
        simpl; repeat eexists.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; [| |contradiction].
        * intros.
          replace vx with (value_of e) by (symmetry; auto).
          if_tac; auto; absurd (value_of e = vint 0); auto.
        * subst; simpl; intros.
          if_tac; if_tac; auto; absurd (vx = vint 0); auto.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t, v); simpl in *.
    destruct v; try contradiction.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP () (LOCALx (temp _t'2 (vint (if eq_dec i0 Int.zero then 1
        else if eq_dec i0 (Int.repr key) then 1 else 0)) :: Q) (SEPx R))) end.
    { forward.
      subst; rewrite eq_dec_refl; apply drop_tc_environ. }
    { forward.
      destruct (eq_dec i0 Int.zero); [absurd (i0 = Int.repr 0); auto|].
      simpl force_val.
      destruct (eq_dec i0 (Int.repr key)).
      + subst; rewrite Int.eq_true; apply drop_tc_environ.
      + rewrite Int.eq_false; [apply drop_tc_environ | auto]. }
    assert (Zlength h' = Zlength h).
    { assert (Zlength (sublist i (Zlength h) h) = Zlength (sublist i (Zlength h') h')) as Heq
        by (replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h'); auto).
      rewrite !Zlength_sublist in Heq; try omega.
      destruct (Z_le_dec i (Zlength h')); [omega|].
      unfold sublist in Heq.
      rewrite Z2Nat_neg in Heq by omega.
      simpl in Heq; rewrite Zlength_nil in Heq; omega. }
    match goal with H : sublist _ _ h = sublist _ _ h' |- _ =>
      erewrite sublist_next with (d := ([] : hist, [] : hist)),
               sublist_next with (l := h')(d := ([] : hist, [] : hist)) in H by omega; inversion H as [Heq] end.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.zero /\ i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ lval).
      forward.
      forward.
      forward_call (Tsh, sh, field_address tentry [StructField _value] (Znth i entries Vundef), lval,
        vint value, vint 0, snd (Znth i h' ([], [])), fun (h : hist) v => !!(v = vint value) && emp,
        v_R, fun (h : hist) => emp).
      { entailer!.
        rewrite field_address_offset; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { repeat (split; auto).
        intros ????????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros t'.
      forward.
      Exists i (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, CAS (Vint i0) (vint 0) (vint key))],
        snd (Znth i h' ([], [])) ++ [(t', Store (vint value))]))
        (m ++ map (fun x => (make_int (value_of (snd (last (fst x) (O, Store (vint 0))))), 0))
                  (sublist (Zlength m) i h')).
      apply andp_right; auto.
      apply andp_right.
      { apply prop_right; repeat split.
        - rewrite sublist_upd_Znth_l; auto; omega.
        - rewrite upd_Znth_same by omega.
          replace (Znth i h ([], [])) with (Znth i h' ([], [])).
          destruct (Znth i h' ([], [])).
          repeat eexists; eauto.
          destruct (eq_dec i0 Int.zero); subst; auto.
          destruct (eq_dec i0 (Int.repr key)); subst; auto.
          absurd (Int.zero = Int.zero); auto.
        - rewrite upd_Znth_Zlength by omega.
          rewrite sublist_upd_Znth_r; auto; omega.
        - unfold wf_map in *.
          intro Hin; rewrite map_app, in_app in Hin; destruct Hin as [? | Hin]; [absurd (In 0 (map fst m)); auto|].
          rewrite in_map_iff in Hin; destruct Hin as (? & Hzero & Hin).
          rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst; simpl in *.

Lemma Forall2_In_r : forall A B (P : A -> B -> Prop) x l1 l2, Forall2 P l1 l2 -> In x l2 ->
  exists y, In y l1 /\ P y x.
Proof.
  induction 1; intro Hin; destruct Hin; simpl.
  - subst; eauto.
  - destruct IHForall2 as (? & ? & ?); eauto.
Qed.

Lemma last_snoc : forall A (d : A) x l, last (l ++ [x]) d = x.
Proof.
  induction l; auto; simpl.
  destruct (l ++ [x]) eqn: Heq; auto.
  contradiction (app_cons_not_nil l [] x); auto.
Qed.
          destruct (Z_le_dec i (Zlength m)).
          { rewrite sublist_nil_gen in Hin; auto. }
          exploit Forall2_In_r; eauto.
          { eapply sublist_In.
            rewrite sublist_sublist, 2Z.add_0_r; eauto; try omega.
            split; [apply Zlength_nonneg | omega]. }
          intros (? & ? & ? & v & Hfst & ? & ? & ?).
          setoid_rewrite Hfst in Hzero.
          rewrite last_snoc in Hzero; simpl in Hzero.
          destruct (eq_dec (Vint v) (vint 0)); [absurd (v = Int.zero); auto; inv e; auto|].
          simpl in Hzero.
          absurd (v = Int.zero); auto.
(* up *)
Lemma signed_inj : forall i1 i2, Int.signed i1 = Int.signed i2 -> i1 = i2.
Proof.
  intros.
  apply int_eq_e.
  rewrite Int.eq_signed, H.
  apply zeq_true.
Qed.
          apply signed_inj; auto.
        - rewrite sublist_upd_Znth_l by omega.
          rewrite sublist_split with (mid := Zlength m); try omega.

Lemma compatible_app : forall h1 h2 m1 m2, compatible h1 m1 -> compatible h2 m2 -> Zlength h1 = Zlength m1 ->
  compatible (h1 ++ h2) (m1 ++ m2).
Proof.
  induction 1; auto; simpl; intros.
  - constructor; auto.
  - rewrite Zlength_cons, Zlength_nil in *.
    pose proof (Zlength_nonneg h); omega.
Qed.
          apply compatible_app.
          + 


          + admit.
          + rewrite Zlength_sublist; try omega.
            admit.
            admit.
          + admit.
          + admit.
        - admit.
        - apply incl_appl, incl_refl. }
      apply andp_right; auto.
      fast_cancel.
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
      * rewrite replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i1 i).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        rewrite Znth_map with (d' := Vundef) by auto.
        unfold atomic_entry.
        Exists lkey lval; entailer!.
        { rewrite upd_Znth_diff; rewrite ?Zlength_map; auto. }
      * rewrite sepcon_comm, replace_nth_sepcon.
        assert (0 <= i < Zlength h') by omega.
        apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i1 i).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        erewrite Znth_map, Znth_upto; simpl; auto; try omega.
        rewrite upd_Znth_same; auto; simpl.
        { rewrite upd_Znth_diff; auto.
          rewrite Zlength_upto in *.
          erewrite !Znth_map, !Znth_upto; auto; try omega.
          rewrite upd_Znth_diff; auto.
          match goal with H : Zlength h' = _ |- _ => setoid_rewrite H; simpl in *; omega end. }
    + forward.
      destruct (eq_dec i0 Int.zero); [discriminate|].
      destruct (eq_dec i0 (Int.repr key)); [discriminate|].
      entailer!.
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
      instantiate (1 := EX i : Z, EX h' : list (hist * hist),
        PROP (0 <= i < 20; Forall2 (failed_CAS key) (sublist 0 (i + 1) h) (sublist 0 (i + 1) h');
              sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h')
        LOCAL (temp _idx (vint i); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
        SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
             entry_hists entries h')).
      Exists i (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, CAS (Vint i0) (vint 0) (vint key))],
        snd (Znth i h' ([], [])))).
      go_lower.
      apply andp_right.
      { apply prop_right; repeat (split; auto).
        * erewrite sublist_split, sublist_len_1 with (i1 := i); try omega.
          erewrite sublist_split with (hi := i + 1), sublist_len_1 with (i1 := i)(d := ([] : hist, [] : hist));
            rewrite ?upd_Znth_Zlength; try omega.
          rewrite sublist_upd_Znth_l by omega.
          rewrite upd_Znth_same by omega.
          apply Forall2_app; auto.
          constructor; auto.
          unfold failed_CAS; simpl.
          rewrite Heq; repeat eexists; eauto.
        * rewrite upd_Znth_Zlength by omega.
          rewrite sublist_upd_Znth_r by omega; auto. }
      apply andp_right; [apply prop_right; auto|].
      fast_cancel.
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
      * rewrite replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i1 i).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        rewrite Znth_map with (d' := Vundef) by auto.
        unfold atomic_entry.
        Exists lkey lval; entailer!.
        { rewrite upd_Znth_diff; rewrite ?Zlength_map; auto. }
      * rewrite (sepcon_comm _ (ghost_hist _ _)), <- sepcon_assoc, replace_nth_sepcon.
        assert (0 <= i < Zlength h') by omega.
        apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i1 i).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        erewrite Znth_map, Znth_upto; simpl; auto; try omega.
        rewrite upd_Znth_same; auto; simpl.
        rewrite sepcon_comm; auto.
        { rewrite upd_Znth_diff; auto.
          rewrite Zlength_upto in *.
          erewrite !Znth_map, !Znth_upto; auto; try omega.
          rewrite upd_Znth_diff; auto.
          match goal with H : Zlength h' = _ |- _ => setoid_rewrite H; simpl in *; omega end. }
  - Intros i h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) h'; entailer!.
    admit. (* list is long enough *)
Admitted.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  forward.
  eapply semax_pre with (P' := EX i : Z, EX h' : list (hist * hist),
    PROP (0 <= i < 20; Forall2 (failed_load key) (sublist 0 i h) (sublist 0 i h');
          sublist i (Zlength h) h = sublist i (Zlength h') h')
    LOCAL (temp _idx (vint i); temp _key (vint key); gvar _m_entries p)
    SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
         entry_hists entries h')).
  { Exists 0 h; rewrite sublist_nil; entailer!. }
  eapply semax_loop.
  - Intros i h'; forward.
    assert_PROP (Zlength entries = 20) by entailer!.
    assert (0 <= i < Zlength entries) by (replace (Zlength entries) with 20; auto).
    forward.
    { entailer!.
      apply isptr_is_pointer_or_null, Forall_Znth; auto. }
    rewrite extract_nth_sepcon with (i := i), Znth_map with (d' := Vundef); try rewrite Zlength_map; auto.
    unfold entry_hists; erewrite extract_nth_sepcon with (i := i)(l := map _ _), Znth_map, Znth_upto; simpl; auto;
      try omega.
    unfold atomic_entry; Intros lkey lval.
    rewrite atomic_loc_isptr.
    forward.
    forward.
    forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth i entries Vundef), lkey, vint 0,
      fst (Znth i h' ([], [])), fun (h : hist) => emp, e_R, fun (h : hist) (v : val) => emp).
    { entailer!.
      rewrite field_address_offset; simpl.
      rewrite isptr_offset_val_zero; auto.
      { rewrite field_compatible_cons; simpl.
        split; [unfold in_members; simpl|]; auto. } }
    { repeat (split; auto).
      intros ???????????? Ha.
      unfold e_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      apply andp_right; auto.
      eapply derives_trans, precise_weak_precise; auto. }
    Intros x; destruct x as (t, v); simpl in *.
    destruct v; try contradiction.
    assert (Zlength h' = Zlength h).
    { assert (Zlength (sublist i (Zlength h) h) = Zlength (sublist i (Zlength h') h')) as Heq
        by (replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h'); auto).
      rewrite !Zlength_sublist in Heq; try omega.
      destruct (Z_le_dec i (Zlength h')); [omega|].
      unfold sublist in Heq.
      rewrite Z2Nat_neg in Heq by omega.
      simpl in Heq; rewrite Zlength_nil in Heq; omega. }
    match goal with H : sublist _ _ h = sublist _ _ h' |- _ =>
      erewrite sublist_next with (d := ([] : hist, [] : hist)),
               sublist_next with (l := h')(d := ([] : hist, [] : hist)) in H by omega; inversion H as [Heq] end.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ lval).
      forward.
      forward.
      forward_call (Tsh, sh, field_address tentry [StructField _value] (Znth i entries Vundef), lval, vint 0,
        snd (Znth i h' ([], [])), fun (h : hist) => emp, e_R, fun (h : hist) (v : val) => emp).
      { entailer!.
        rewrite field_address_offset; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { repeat (split; auto).
        intros ???????????? Ha.
        unfold e_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros x; destruct x as (t', v); simpl in *.
      forward.
      Exists (Int.signed v) (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, Load (vint key))],
        snd (Znth i h' ([], [])) ++ [(t', Load (Vint v))])).
      apply andp_right.
      { apply prop_right.
        unfold get_item_trace.
        split; auto.
        exists i; split; [|split].
        * rewrite sublist_upd_Znth_l; auto; omega.
        * rewrite upd_Znth_same by omega.
          replace (Znth i h ([], [])) with (Znth i h' ([], [])).
          destruct (Znth i h' ([], [])).
          assert (v <> Int.zero) by admit. (* zero should not be stored *)
          destruct (eq_dec (Int.signed v) 0).
          { absurd (v = Int.zero); auto.
            apply signed_inj; auto. }
          rewrite Int.repr_signed; eauto.
        * rewrite upd_Znth_Zlength by omega.
          rewrite sublist_upd_Znth_r; auto; omega. }
      apply andp_right; auto.
      fast_cancel.
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
      * rewrite replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i0 i).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        rewrite Znth_map with (d' := Vundef) by auto.
        unfold atomic_entry.
        Exists lkey lval; entailer!.
        { rewrite upd_Znth_diff; rewrite ?Zlength_map; auto. }
      * rewrite sepcon_comm, replace_nth_sepcon.
        assert (0 <= i < Zlength h') by omega.
        apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i0 i).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        erewrite Znth_map, Znth_upto; simpl; auto; try omega.
        rewrite upd_Znth_same; auto; simpl.
        { rewrite upd_Znth_diff; auto.
          rewrite Zlength_upto in *.
          erewrite !Znth_map, !Znth_upto; auto; try omega.
          rewrite upd_Znth_diff; auto.
          match goal with H : Zlength h' = _ |- _ => setoid_rewrite H; simpl in *; omega end. }
    + forward.
      entailer!.
    + Intros; match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (i0 <> Int.zero) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists 0 (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, Load (vint 0))], snd (Znth i h' ([], [])))).
        apply andp_right.
        { apply prop_right.
          unfold get_item_trace.
          split; auto.
          exists i; split; [|split].
          * rewrite sublist_upd_Znth_l; auto; omega.
          * rewrite upd_Znth_same by omega.
            replace (Znth i h ([], [])) with (Znth i h' ([], [])).
            destruct (Znth i h' ([], [])).
            eexists; rewrite eq_dec_refl; eauto.
          * rewrite upd_Znth_Zlength by omega.
            rewrite sublist_upd_Znth_r; auto; omega. }
        apply andp_right; auto.
        fast_cancel.
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
        -- rewrite replace_nth_sepcon; apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i0 i).
           subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           rewrite Znth_map with (d' := Vundef) by auto.
           unfold atomic_entry.
           Exists lkey lval; entailer!.
           { rewrite upd_Znth_diff; rewrite ?Zlength_map; auto. }
        -- rewrite sepcon_comm, replace_nth_sepcon.
           assert (0 <= i < Zlength h') by omega.
           apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i0 i).
           subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           erewrite Znth_map, Znth_upto; simpl; auto; try omega.
           rewrite upd_Znth_same; auto; simpl.
           rewrite sepcon_comm; auto.
           { rewrite upd_Znth_diff; auto.
             rewrite Zlength_upto in *.
             erewrite !Znth_map, !Znth_upto; auto; try omega.
             rewrite upd_Znth_diff; auto.
             match goal with H : Zlength h' = _ |- _ => setoid_rewrite H; simpl in *; omega end. }
      * forward.
        entailer!.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
        instantiate (1 := EX i : Z, EX h' : list (hist * hist),
          PROP (0 <= i < 20; Forall2 (failed_load key) (sublist 0 (i + 1) h) (sublist 0 (i + 1) h');
                sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h')
          LOCAL (temp _idx (vint i); temp _key (vint key); gvar _m_entries p)
          SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
               entry_hists entries h')).
        Exists i (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, Load (Vint i0))], snd (Znth i h' ([], [])))).
        go_lower.
        apply andp_right.
        { apply prop_right; repeat (split; auto).
          * erewrite sublist_split, sublist_len_1 with (i1 := i); try omega.
            erewrite sublist_split with (hi := i + 1), sublist_len_1 with (i1 := i)(d := ([] : hist, [] : hist));
              rewrite ?upd_Znth_Zlength; try omega.
            rewrite sublist_upd_Znth_l by omega.
            rewrite upd_Znth_same by omega.
            apply Forall2_app; auto.
            constructor; auto.
            unfold failed_load; simpl.
            rewrite Heq; repeat eexists; eauto.
            { intro X; absurd (i0 = Int.zero); [|inv X]; auto. }
            { intro X; absurd (i0 = Int.repr key); [|inv X]; auto. }
          * rewrite upd_Znth_Zlength by omega.
            rewrite sublist_upd_Znth_r by omega; auto. }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
        -- rewrite replace_nth_sepcon; apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
          rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
          destruct (eq_dec i1 i).
          subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           rewrite Znth_map with (d' := Vundef) by auto.
          unfold atomic_entry.
          Exists lkey lval; entailer!.
          { rewrite upd_Znth_diff; rewrite ?Zlength_map; auto. }
        -- rewrite (sepcon_comm _ (ghost_hist _ _)), <- sepcon_assoc, replace_nth_sepcon.
           assert (0 <= i < Zlength h') by omega.
           apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i1 i).
          subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
          erewrite Znth_map, Znth_upto; simpl; auto; try omega.
          rewrite upd_Znth_same; auto; simpl.
          rewrite sepcon_comm; auto.
          { rewrite upd_Znth_diff; auto.
            rewrite Zlength_upto in *.
            erewrite !Znth_map, !Znth_upto; auto; try omega.
            rewrite upd_Znth_diff; auto.
            match goal with H : Zlength h' = _ |- _ => setoid_rewrite H; simpl in *; omega end. }
  - Intros i h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) h'; entailer!.
    admit. (* list is long enough *)
Admitted.
