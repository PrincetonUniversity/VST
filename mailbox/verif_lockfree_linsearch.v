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

Lemma index_of_spec : forall k m, match index_of m k with
  | Some i => 0 <= i < Zlength m /\ fst (Znth i m (0, 0)) = k
  | None => ~In k (map fst m) end.
Proof.
  induction m; simpl; auto; intros.
  destruct a.
  rewrite Zlength_cons.
  pose proof (Zlength_nonneg m).
  destruct (eq_dec z k); [split; auto; omega|].
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
  exists n e, In (n, e) h /\ value_of e = v /\ Forall (fun x => let '(m, _) := x in m <= n)%nat h.

Lemma last_value_new : forall h n e, Forall (fun x => fst x < n)%nat h ->
  last_value (h ++ [(n, e)]) (value_of e).
Proof.
  right.
  do 3 eexists; [rewrite in_app; simpl; eauto|].
  rewrite Forall_app; repeat constructor.
  eapply Forall_impl; [|eauto]; intros.
  destruct a; simpl in *; omega.
Qed.

Definition compatible h m := Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\
  last_value (snd hs) (vint (snd e))) (sublist 0 (Zlength m) h) m /\
  Forall (fun hs => last_value (fst hs) (vint 0)) (sublist (Zlength m) (Zlength h) h).

Definition ordered_hist h := forall i j (Hi : 0 <= i < j) (Hj : j < Zlength h),
  (fst (Znth i h (O, Store (vint 0))) < fst (Znth j h (O, Store (vint 0))))%nat.

Lemma ordered_cons : forall t e h, ordered_hist ((t, e) :: h) ->
  Forall (fun x => let '(m, _) := x in t < m)%nat h /\ ordered_hist h.
Proof.
  unfold ordered_hist; split.
  - rewrite Forall_forall; intros (?, ?) Hin.
    apply In_Znth with (d := (O, Store (vint 0))) in Hin.
    destruct Hin as (j & ? & Hj).
    exploit (H 0 (j + 1)); try omega.
    { rewrite Zlength_cons; omega. }
    rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r, Hj by omega; auto.
  - intros; exploit (H (i + 1) (j + 1)); try omega.
    { rewrite Zlength_cons; omega. }
    rewrite !Znth_pos_cons, !Z.add_simpl_r by omega; auto.
Qed.

Lemma ordered_last : forall t e h (Hordered : ordered_hist h) (Hin : In (t, e) h)
  (Ht : Forall (fun x => let '(m, _) := x in m <= t)%nat h), last h (O, Store (vint 0)) = (t, e).
Proof.
  induction h; [contradiction | simpl; intros].
  destruct a; apply ordered_cons in Hordered; destruct Hordered as (Ha & ?).
  inversion Ht as [|??? Hp]; subst.
  destruct Hin as [Hin | Hin]; [inv Hin|].
  - destruct h; auto.
    inv Ha; inv Hp; destruct p; omega.
  - rewrite IHh; auto.
    destruct h; auto; contradiction.
Qed.

Lemma ordered_last_value : forall h v (Hordered : ordered_hist h),
  last_value h v <-> value_of (snd (last h (O, Store (vint 0)))) = v.
Proof.
  unfold last_value; split; intro.
  - destruct H as [(? & ?) | (? & ? & ? & ? & ?)]; subst; auto.
    erewrite ordered_last; eauto; auto.
  - destruct h; [auto | right].
    destruct (last (p :: h) (O, Store (vint 0))) as (t, e) eqn: Hlast.
    exploit (@app_removelast_last _ (p :: h)); [discriminate | intro Heq].
    rewrite Hlast in Heq.
    exists t; exists e; repeat split; auto.
    + rewrite Heq, in_app; simpl; auto.
    + unfold ordered_hist in Hordered.
      rewrite Forall_forall; intros (?, ?) Hin.
      apply In_Znth with (d := (O, Store (vint 0))) in Hin.
      destruct Hin as (i & ? & Hi).
      rewrite <- Znth_last in Hlast.
      destruct (eq_dec i (Zlength (p :: h) - 1)).
      * subst; rewrite Hlast in Hi; inv Hi; auto.
      * exploit (Hordered i (Zlength (p :: h) - 1)); try omega.
        rewrite Hlast, Hi; simpl; omega.
Qed.

Definition wf_map (m : list (Z * Z)) := Forall (fun i => repable_signed i /\ i <> 0) (map fst m).

Definition int_op e :=
  match e with
  | Load v | Store v => tc_val tint v
  | CAS r c w => tc_val tint r /\ tc_val tint c /\ tc_val tint w
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

Definition int_hists (h : list (hist * hist)) := Forall (fun x => Forall int_op (map snd (fst x)) /\
                                                 Forall int_op (map snd (snd x))) h.

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list val, h : list (hist * hist), m : list (Z * Z)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; Forall isptr entries; Zlength h = 20;
         Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h; int_hists h;
         wf_map m; compatible h m)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist), EX m' : list (Z * Z),
   PROP (Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h'; int_hists h';
         set_item_trace h key value i h';
         wf_map m'; compatible (sublist 0 i h' ++ sublist i (Zlength h) h) m';
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
  WITH key : Z, p : val, sh : share, entries : list val, h : list (hist * hist), m : list (Z * Z)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; Forall isptr entries; Zlength h = 20;
         Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h; int_hists h;
         wf_map m; compatible h m)
   LOCAL (temp _key (vint key); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tint ]
   EX value : Z, EX h' : list (hist * hist), EX m' : list (Z * Z),
   PROP (Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h'; int_hists h';
         wf_map m'; compatible h' m'; get_item_trace h key value h';
         if eq_dec value 0 then ~In key (map fst m') /\ incl m m'
         else get m' key = Some value /\ incl (set m key value) m')
   LOCAL (temp ret_temp (vint value))
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

Lemma apply_int_ops : forall v h i (Hv : verif_atomics.apply_hist (Vint i) h = Some v)
  (Hints : Forall int_op h), tc_val tint v.
Proof.
  induction h; simpl; intros.
  - inv Hv; eauto.
  - inversion Hints as [|?? Ha]; subst.
    destruct a.
    + destruct (eq_dec v0 (Vint i)); [eapply IHh; eauto | discriminate].
    + destruct v0; try contradiction; eapply IHh; eauto.
    + destruct (eq_dec r (Vint i)); [|discriminate].
      destruct Ha as (? & ? & ?).
      destruct w; try contradiction.
      destruct (eq_dec c (Vint i)); eapply IHh; eauto.
Qed.

Lemma compatible_length : forall h m, compatible h m -> Zlength m <= Zlength h.
Proof.
  intros ?? (? & ?).
  apply mem_lemmas.Forall2_Zlength in H.
  pose proof (sublist_max_length 0 (Zlength m) h); omega.
Qed.

Lemma compatible_app : forall h1 h2 m1 m2 (Hcompat1 : compatible h1 m1) (Hcompat2 : compatible h2 m2),
  Zlength h1 = Zlength m1 -> compatible (h1 ++ h2) (m1 ++ m2).
Proof.
  intros; pose proof (compatible_length _ _ Hcompat2).
  destruct Hcompat1 as (Hh1 & _), Hcompat2 as (Hh2 & Hrest); unfold compatible.
  rewrite !Zlength_app.
  pose proof (Zlength_nonneg m1); pose proof (Zlength_nonneg m2).
  rewrite !sublist_app by omega.
  rewrite H, !Z.add_simpl_l.
  rewrite Z.min_l, Z.min_r, Z.max_r, Z.max_l by omega.
  rewrite Z.min_r, Z.max_l by omega.
  rewrite sublist_nil, sublist_same; auto; simpl; split; auto.
  rewrite sublist_same in Hh1; auto.
  apply Forall2_app; auto.
Qed.

Lemma ordered_snoc : forall h t e, ordered_hist h -> Forall (fun x => fst x < t)%nat h ->
  ordered_hist (h ++ [(t, e)]).
Proof.
  repeat intro.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
  rewrite app_Znth1 by omega.
  destruct (eq_dec j (Zlength h)).
  - rewrite Znth_app1; auto.
    apply Forall_Znth; auto; omega.
  - specialize (H i j).
    rewrite app_Znth1 by omega; apply H; auto; omega.
Qed.

Lemma compatible_sublist : forall h m i j, compatible h m -> 0 <= i -> j <= Zlength m ->
  compatible (sublist i j h) (sublist i j m).
Proof.
  intros; unfold compatible.
  pose proof (compatible_length _ _ H).
  destruct (Z_le_dec j i).
  { rewrite sublist_nil_gen with (l0 := m); auto.
    rewrite sublist_nil_gen with (l0 := h); auto.
    rewrite sublist_nil; split; auto; constructor. }
  rewrite Zlength_sublist, sublist_sublist by omega.
  rewrite Zlength_sublist, sublist_sublist by omega.
  rewrite sublist_nil; split; auto.
  destruct H.
  rewrite Z.add_0_l, Z.sub_simpl_r.
  replace (sublist i j h) with (sublist i j (sublist 0 (Zlength m) h)).
  apply Forall2_sublist; auto.
  { rewrite sublist_sublist by omega; f_equal; omega. }
Qed.

Lemma failed_CAS_fst : forall v h h', Forall2 (failed_CAS v) h h' -> map snd h' = map snd h.
Proof.
  induction 1; auto.
  destruct H as (? & ? & ? & ? & ? & ?); simpl; f_equal; auto.
Qed.

Lemma make_int_spec : forall v, tc_val tint v -> vint (make_int v) = v.
Proof.
  destruct v; try contradiction; simpl.
  rewrite Int.repr_signed; auto.
Qed.

Definition make_map h := (map (fun x => (make_int (value_of (snd (last (fst x) (O, Store (vint 0))))),
  make_int (value_of (snd (last (snd x) (O, Store (vint 0))))))) h).

Lemma compatible_nil : compatible [] [].
Proof.
  split; rewrite sublist_of_nil; auto.
Qed.
Hint Resolve compatible_nil.

Lemma compatible_cons : forall a b h m
  (Hkey : last_value (fst a) (vint (fst b))) (Hvalue : last_value (snd a) (vint (snd b)))
  (Hrest : compatible h m), compatible (a :: h) (b :: m).
Proof.
  unfold compatible; intros.
  pose proof (Zlength_nonneg m).
  rewrite !Zlength_cons, sublist_0_cons, sublist_S_cons by omega.
  unfold Z.succ; rewrite !Z.add_simpl_r.
  destruct Hrest; split; auto.
Qed.

Lemma int_op_value : forall e, int_op e -> tc_val tint (value_of e).
Proof.
  destruct e; auto; simpl.
  intros (? & ? & ?); destruct (eq_dec r c); auto.
Qed.

Lemma make_compatible : forall h
  (Hordered : Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h) (Hint : int_hists h),
  Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
    h (make_map h).
Proof.
  induction 1; intro; [constructor | simpl].
  inversion Hint as [|?? (Hfst & Hsnd)]; subst; destruct H.
  rewrite Forall_map in Hfst, Hsnd.
  exploit (Forall_last _ (O, Store (vint 0)) _ Hfst); simpl; auto.
  exploit (Forall_last _ (O, Store (vint 0)) _ Hsnd); simpl; auto.
  intro Hfst'; apply int_op_value in Hfst'.
  intro Hsnd'; apply int_op_value in Hsnd'.
  constructor; auto.
  rewrite !ordered_last_value; auto; simpl; rewrite !make_int_spec; auto.
Qed.

Lemma compatible_set : forall h m hk hv i k v (Hcompat : compatible h m)
  (Hcase : index_of m k = Some i \/ index_of m k = None /\ i = Zlength m) (Hi : i < Zlength h)
  (Hkey : last_value hk (vint k)) (Hvalue : last_value hv (vint v)),
  compatible (upd_Znth i h (hk, hv)) (set m k v).
Proof.
  intros.
  pose proof (index_of_spec k m) as Hk.
  pose proof (compatible_length _ _ Hcompat).
  unfold compatible.
  destruct Hcase as [Hcase | (Hcase & ?)]; subst.
  - unfold set; rewrite Hcase in *; destruct Hk.
    rewrite !upd_Znth_Zlength by (auto; omega).
    rewrite sublist_upd_Znth_r with (lo := Zlength m) by omega.
    destruct Hcompat; split; auto.
    rewrite sublist_upd_Znth_lr, Z.sub_0_r by omega.
    apply Forall2_upd_Znth; auto.
    rewrite Zlength_sublist; omega.
  - unfold set; rewrite Hcase in *.
    pose proof (Zlength_nonneg m).
    rewrite !upd_Znth_Zlength by auto.
    rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl.
    rewrite sublist_upd_Znth_r with (lo := Zlength m + 1) by omega.
    destruct Hcompat as (? & Hzero); split.
    + rewrite sublist_upd_Znth_lr, Z.sub_0_r by omega.
      rewrite sublist_split with (mid := Zlength m) by omega.
      assert (Zlength (sublist 0 (Zlength m) h) = Zlength m) as Hlen.
      { rewrite Zlength_sublist; auto; omega. }
      rewrite upd_Znth_app2, Hlen, Zminus_diag.
      apply Forall2_app; auto.
      erewrite sublist_len_1 with (d := ([] : hist, [] : hist)) by auto.
      rewrite upd_Znth0, sublist_nil; constructor; auto.
      { rewrite Hlen; split; [omega|].
        rewrite <- Z.le_sub_le_add_l, Zminus_diag; apply Zlength_nonneg. }
    + rewrite sublist_next with (d := ([] : hist, [] : hist)) in Hzero by (auto; omega).
      inv Hzero; auto.
Qed.

Lemma index_of_app : forall k m1 m2, index_of (m1 ++ m2) k =
  match index_of m1 k with Some i => Some i | None => option_map (Z.add (Zlength m1)) (index_of m2 k) end.
Proof.
  induction m1; simpl; intros.
  - destruct (index_of m2 k); auto.
  - destruct a.
    destruct (eq_dec z k); auto.
    rewrite IHm1; destruct (index_of m1 k); auto; simpl.
    destruct (index_of m2 k); auto; simpl.
    rewrite Zlength_cons; f_equal; omega.
Qed.

Lemma index_of_out : forall k m, Forall (fun x => fst x <> k) m -> index_of m k = None.
Proof.
  intros.
  pose proof (index_of_spec k m) as Hk.
  destruct (index_of m k); auto.
  destruct Hk; rewrite Forall_forall in H; exploit (H (Znth z m (0, 0))); auto; try contradiction.
  apply Znth_In; auto.
Qed.

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  forward.
  eapply semax_pre with (P' := EX i : Z, EX h' : list (hist * hist),
    PROP (0 <= i < 20; Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h'; int_hists h';
          Forall2 (failed_CAS key) (sublist 0 i h) (sublist 0 i h');
          Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
            (sublist 0 (Zlength m) h') m;
          sublist i (Zlength h) h = sublist i (Zlength h') h')
    LOCAL (temp _idx (vint i); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
         entry_hists entries h')).
  { Exists 0 h; rewrite sublist_nil; entailer!.
    match goal with H : compatible h m |- _ => destruct H; auto end. }
  eapply semax_loop.
  - Intros i h'; forward.
    assert (Zlength h' = Zlength h) as Hlen.
    { assert (Zlength (sublist i (Zlength h) h) = Zlength (sublist i (Zlength h') h')) as Heq
        by (replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h'); auto).
      rewrite !Zlength_sublist in Heq; try omega.
      destruct (Z_le_dec i (Zlength h')); [omega|].
      unfold sublist in Heq.
      rewrite Z2Nat_neg in Heq by omega.
      simpl in Heq; rewrite Zlength_nil in Heq; omega. }
    assert (i <= Zlength h') by omega.
    assert (map snd h' = map snd h) as Hsnd.
    { erewrite <- sublist_same with (al := h') by eauto.
      erewrite <- sublist_same with (al := h) by eauto.
      rewrite sublist_split with (al := h')(mid := i) by omega.
      rewrite sublist_split with (al := h)(mid := i) by omega.
      rewrite Hlen in *; rewrite !map_app; f_equal; [|congruence].
      eapply failed_CAS_fst; eauto. }
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
    destruct (Znth i h' ([], [])) as (hki, hvi) eqn: Hhi.
    forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth i entries Vundef), lkey, vint 0,
      vint key, vint 0, hki,
      fun (h : hist) c v => !!(c = vint 0 /\ v = vint key /\ h = hki) && emp,
      k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
(* Given that I have to do this, maybe better to remove the arguments from P. *)
    { entailer!.
      rewrite field_address_offset; simpl.
      rewrite isptr_offset_val_zero; auto.
      { rewrite field_compatible_cons; simpl.
        split; [unfold in_members; simpl|]; auto. } }
    { replace hki with (fst (Znth i h' ([], []))) by (rewrite Hhi; auto); fast_cancel. }
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
    assert (Znth i h ([], []) = Znth i h' ([], []) /\
      sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h') as (Heq & Hi1).
    { match goal with H : sublist _ _ h = sublist _ _ h' |- _ =>
        erewrite sublist_next with (d := ([] : hist, [] : hist)),
                 sublist_next with (l := h')(d := ([] : hist, [] : hist)) in H by omega; inv H; auto end. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.zero /\ i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ lval).
      forward.
      forward.
      forward_call (Tsh, sh, field_address tentry [StructField _value] (Znth i entries Vundef), lval,
        vint value, vint 0, hvi, fun (h : hist) v => !!(v = vint value) && emp,
        v_R, fun (h : hist) => emp).
      { entailer!.
        rewrite field_address_offset; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { replace hvi with (snd (Znth i h' ([], []))) by (rewrite Hhi; auto); fast_cancel. }
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
        snd (Znth i h' ([], [])) ++ [(t', Store (vint value))])) (m ++ make_map (sublist (Zlength m) i h')).
      apply andp_right; auto.
      apply andp_right.
      { assert (0 <= i < Zlength h') by (rewrite Hlen; omega).
        assert (Zlength m <= Zlength h').
        { rewrite Hlen; apply compatible_length; auto. }
        assert (compatible (sublist 0 i h' ++ sublist i (Zlength h) h)
                           (m ++ make_map (sublist (Zlength m) i h'))).
        { destruct (Z_lt_dec i (Zlength m)).
          + rewrite (sublist_nil_gen _ (Zlength m)), app_nil_r by omega.
            replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h').
            rewrite sublist_rejoin, sublist_same by omega.
            split; auto.
            replace (sublist (Zlength m) (Zlength h') h') with (sublist (Zlength m) (Zlength h) h).
            match goal with H : compatible h m |- _ => destruct H; auto end.
            transitivity (sublist (Zlength m - i) (Zlength h - i) (sublist i (Zlength h) h)).
            * rewrite sublist_sublist, !Z.sub_simpl_r by omega; auto.
            * replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h').
              rewrite Hlen, sublist_sublist, !Z.sub_simpl_r by omega; auto.
          + pose proof (Zlength_nonneg m).
            rewrite sublist_split with (mid := (Zlength m)) by omega.
            rewrite <- app_assoc; apply compatible_app.
            * assert (Zlength (sublist 0 (Zlength m) h') = Zlength m).
              { rewrite Zlength_sublist; omega. }
              unfold compatible; rewrite sublist_same; auto.
              split; auto.
              rewrite sublist_nil'; auto.
            * pose proof (Zlength_nonneg (sublist (Zlength m) i h')).
              pose proof (Zlength_nonneg (sublist i (Zlength h) h)).
              split.
              unfold make_map at 1; rewrite Zlength_map, sublist_app.
              rewrite Z.min_l by auto.
              rewrite Z.min_l, sublist_same by (auto; apply Z.le_refl).
              rewrite Zminus_diag.
              rewrite !Z.max_r, sublist_nil, app_nil_r by (auto; omega).
              apply make_compatible.
              { apply Forall_sublist; auto. }
              { apply Forall_sublist; auto. }
              { split; auto; apply Z.le_refl. }
              { rewrite <- Z.le_sub_le_add_l, Zminus_diag; auto. }
              { unfold make_map; rewrite Zlength_map, Zlength_app.
                rewrite sublist_app; try omega.
                rewrite Z.min_r, Z.min_r, sublist_nil; try (apply Z.le_refl); try omega.
                rewrite Zminus_diag, Z.max_l, Z.add_simpl_l, Z.max_l, sublist_same; try (apply Z.le_refl);
                  auto.
                match goal with H : compatible h m |- _ => destruct H as (_ & Hzero) end.
                apply Forall_sublist with (lo := i - Zlength m)(hi := Zlength h - Zlength m) in Hzero.
                rewrite sublist_sublist, !Z.sub_simpl_r in Hzero by omega; auto.
                { split; auto.
                  rewrite <- Z.le_sub_le_add_l, Zminus_diag; auto. } }
            * rewrite Zlength_sublist; auto; omega. }
        apply prop_right; split; [|split; [|split; [|split; [|split; [|split]]]]].
        - apply Forall_upd_Znth; auto; rewrite Hhi; simpl.
          exploit (Znth_In i h' ([], [])); [auto | rewrite Hhi; intro Hin].
          match goal with H : Forall _ h' |- _ => rewrite Forall_forall in H; specialize (H _ Hin);
            destruct H end.
          split; apply ordered_snoc; auto.
        - apply Forall_upd_Znth; auto.
          match goal with H : int_hists h' |- _ => unfold int_hists in H; rewrite Forall_forall in H;
            exploit (H (Znth i h' ([], []))) end.
          { apply Znth_In; auto. }
          intros (? & ?); simpl.
          rewrite !map_app, !Forall_app; repeat split; auto; constructor; simpl; eauto 6.
        - split; [rewrite sublist_upd_Znth_l; auto; omega|].
          split.
          + rewrite upd_Znth_same by omega.
            replace (Znth i h ([], [])) with (Znth i h' ([], [])).
            destruct (Znth i h' ([], [])).
            repeat eexists; eauto.
            destruct (eq_dec i0 Int.zero); subst; auto.
            destruct (eq_dec i0 (Int.repr key)); subst; auto.
            absurd (Int.zero = Int.zero); auto.
          + rewrite upd_Znth_Zlength by omega.
            rewrite sublist_upd_Znth_r; auto; omega.
        - unfold wf_map in *.
          rewrite map_app, Forall_app; split; auto.
          unfold make_map; rewrite !Forall_map.
          rewrite Forall_forall; intros ? Hin; simpl.
          apply In_Znth with (d := ([], [])) in Hin.
          destruct Hin as (j & Hj & Hjth).
          destruct (Z_le_dec i (Zlength m)).
          { rewrite sublist_nil_gen, Zlength_nil in Hj; omega. }
          match goal with H : Forall2 (failed_CAS key) _ _ |- _ => exploit (Forall2_In_r _ x _ _ H) end.
          { exploit (Znth_In j (sublist (Zlength m) i h') ([], [])); auto; intro.
            eapply sublist_In; rewrite sublist_sublist, 2Z.add_0_r; subst; eauto; try omega.
            pose (Zlength_nonneg m); omega. }
          intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
          setoid_rewrite Heqi; rewrite last_snoc; simpl.
          destruct (eq_dec (Vint r) (vint 0)).
          { absurd (r = Int.zero); auto; inv e; auto. }
          simpl.
          split; [apply Int.signed_range|].
          intro; absurd (r = Int.zero); auto.
          apply signed_inj; auto.
        - rewrite sublist_upd_Znth_l by omega; auto.
        - match goal with H : Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h' |- _ =>
            rewrite Forall_forall in H; exploit (H (Znth i h' ([], []))) end.
          { apply Znth_In; auto. }
          rewrite Hhi; intros (? & ?).
          apply compatible_set;
            try (rewrite ordered_last_value, last_snoc; simpl; auto; try (apply ordered_snoc; auto)).
          + match goal with H : compatible _ _ |- _ => replace (sublist i (Zlength h) h) with
              (sublist i (Zlength h') h') in H; rewrite sublist_rejoin, sublist_same in H; auto; omega end.
          + assert (Forall (fun x => fst x <> key) (sublist 0 i (m ++ make_map (sublist (Zlength m) i h'))))
              as Hmiss.
            { rewrite Forall_forall; intros ? Hin.
              rewrite sublist_app, in_app in Hin; try omega.
              assert (exists hk hv, In (hk, hv) (sublist 0 i h') /\
                value_of (snd (last hk (O, Store (vint 0)))) = vint (fst x)) as (hk & hv & Hin' & Hlast).
              { destruct Hin as [Hin | Hin].
                * pose proof (Zlength_nonneg m); rewrite Z.min_l in Hin by auto.
                  apply In_Znth with (d := (0, 0)) in Hin.
                  destruct Hin as (j & (? & Hj) & Hx).
                  rewrite Zlength_sublist in Hj.
                  rewrite Znth_sublist in Hx by (auto; omega).
                  rewrite Z.sub_0_r, Z.min_glb_lt_iff in Hj; destruct Hj.
                  match goal with H : Forall2 _ (sublist _ _ _) m |- _ =>
                    exploit (Forall2_Znth _ _ _ ([] : hist, [] : hist) (0, 0) H j) end.
                  { rewrite Zlength_sublist; auto; omega. }
                  rewrite Z.add_0_r in Hx; rewrite Hx.
                  replace (Znth j (sublist 0 (Zlength m) h') ([] : hist, [] : hist)) with
                    (Znth j (sublist 0 i h') ([], [])).
                  destruct (Znth j (sublist 0 i h') ([], [])) eqn: Hj.
                  simpl; intros (? & _).
                  do 3 eexists.
                  { rewrite <- Hj; apply Znth_In.
                    rewrite Zlength_sublist; auto; omega. }
                  rewrite <- ordered_last_value; auto.
                  match goal with H : forall x, In x h' -> ordered_hist (fst x) /\ _ |- _ =>
                    exploit (H (Znth j (sublist 0 i h') ([], []))) end.
                  { rewrite Znth_sublist by omega; apply Znth_In.
                    match goal with H : compatible h m |- _ => apply compatible_length in H end.
                    setoid_rewrite Hlen; omega. }
                  rewrite Hj; simpl; tauto.
                  { rewrite !Znth_sublist; auto; omega. }
                  { split; [apply Z.le_refl|].
                    apply Z.min_glb; auto; omega. }
                  { apply Z.le_min_r. }
                * apply sublist_In in Hin.
                  unfold make_map in Hin; rewrite in_map_iff in Hin.
                  destruct Hin as ((?, ?) & ? & Hin); subst; simpl.
                  destruct (Z_le_dec i (Zlength m)).
                  { rewrite sublist_nil_gen in Hin; auto; contradiction. }
                  do 3 eexists.
                  { pose proof (Zlength_nonneg m).
                    rewrite sublist_split with (mid := (Zlength m)) by omega.
                    rewrite in_app; eauto. }
                  symmetry; apply make_int_spec, int_op_value, Forall_last; auto.
                  match goal with H : int_hists h' |- _ => unfold int_hists in H; rewrite Forall_forall in H;
                    exploit (H (l, l0)) end.
                  { eapply sublist_In; eauto. }
                  rewrite Forall_map; tauto. }
              match goal with H : Forall2 (failed_CAS key) _ _ |- _ =>
                exploit (Forall2_In_r _ (hk, hv) _ _ H); auto end.
              intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
              simpl in Heqi; rewrite Heqi, last_snoc in Hlast; simpl in Hlast.
              destruct (eq_dec (Vint r) (vint 0)).
              { absurd (r = Int.zero); auto; inv e; auto. }
              inversion Hlast.
              intro; absurd (r = Int.repr key); subst; auto.
              { unfold make_map; rewrite Zlength_map.
                destruct (Z_le_dec i (Zlength m)).
                { rewrite sublist_nil_gen, Zlength_nil, Z.add_0_r; auto. }
                pose proof (Zlength_nonneg m).
                rewrite Zlength_sublist; auto; omega. } }
            destruct (Z_lt_dec i (Zlength m)).
            * left; rewrite sublist_nil_gen, app_nil_r by (auto; omega).
              rewrite sublist_nil_gen with (i1 := Zlength m), app_nil_r in Hmiss by omega.
              replace m with (sublist 0 i m ++ Znth i m (0, 0) :: sublist (i + 1) (Zlength m) m).
              rewrite index_of_app, index_of_out; auto; simpl.
              destruct (Znth i m (0, 0)) eqn: Hi.
              assert (z = key).
              { match goal with H : Forall2 _ (sublist _ _ _) m |- _ =>
                  exploit (Forall2_Znth _ _ _ ([] : hist, [] : hist) (0, 0) H i) end.
                { rewrite Zlength_sublist; auto; omega. }
                rewrite Znth_sublist, Z.add_0_r, Hi by omega.
                setoid_rewrite Hhi; intros (Hkey & _).
                match goal with H : wf_map m |- _ => unfold wf_map in H; rewrite Forall_forall in H;
                  exploit (H z) end.
                { rewrite in_map_iff; exists (z, z0); split; auto.
                  rewrite <- Hi; apply Znth_In; omega. }
                intros (? & ?).
                assert (repable_signed 0) by (split; computable).
                match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
                  exploit H; eauto end.
                { intro; absurd (z = 0); auto; apply repr_inj_signed; auto.
                  simpl in *; congruence. }
                intro X; inv X.
                destruct (eq_dec (Int.repr z) Int.zero); [absurd (z = 0); auto; apply repr_inj_signed; auto|].
                destruct (eq_dec (Int.repr z) (Int.repr key)); [|absurd (Int.repr 0 = Int.zero); auto].
                apply repr_inj_signed; auto. }
              subst; rewrite eq_dec_refl; simpl.
              rewrite Zlength_sublist by omega; f_equal; omega.
              { rewrite <- sublist_next, sublist_rejoin, sublist_same; auto; omega. }
            * right; pose proof (Zlength_nonneg m).
              assert (i = Zlength (m ++ make_map (sublist (Zlength m) i h'))).
              { unfold make_map; rewrite Zlength_app, Zlength_map, Zlength_sublist; auto; omega. }
              split; auto.
              rewrite sublist_same in Hmiss; auto.
              apply index_of_out; auto.
          + omega.
          + destruct (eq_dec i0 Int.zero); subst; auto.
            destruct (eq_dec i0 (Int.repr key)); [|absurd (Int.repr 0 = Int.zero); auto].
            subst; if_tac; auto.
        - split; auto; apply incl_appl, incl_refl. }
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
        rewrite upd_Znth_same, Hhi; auto; simpl.
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
        PROP (0 <= i < 20; Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h'; int_hists h';
              Forall2 (failed_CAS key) (sublist 0 (i + 1) h) (sublist 0 (i + 1) h');
              Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
                (sublist 0 (Zlength m) h') m;
              sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h')
        LOCAL (temp _idx (vint i); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
        SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
             entry_hists entries h')).
      Exists i (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, CAS (Vint i0) (vint 0) (vint key))],
        snd (Znth i h' ([], [])))).
      go_lower.
      apply andp_right.
      { assert (0 <= i < Zlength h') by (rewrite Hlen; omega).
        match goal with H : Forall _ h' |- _ => rewrite Forall_forall in H;
          exploit (H (Znth i h' ([], []))); rewrite <- Forall_forall in H end.
        { apply Znth_In; auto. }
        intros (? & ?).
        apply prop_right; repeat (split; auto).
        * apply Forall_upd_Znth; auto; simpl.
          split; auto; apply ordered_snoc; auto; rewrite Hhi; auto.
        * apply Forall_upd_Znth; auto; simpl.
          match goal with H : int_hists h' |- _ => unfold int_hists in H; rewrite Forall_forall in H;
            exploit (H (Znth i h' ([], []))) end.
          { apply Znth_In; auto. }
          intros (? & ?); split; auto.
          rewrite map_app, Forall_app; split; auto; repeat constructor.
        * erewrite sublist_split, sublist_len_1 with (i1 := i); try omega.
          erewrite sublist_split with (hi := i + 1), sublist_len_1 with (i1 := i)(d := ([] : hist, [] : hist));
            rewrite ?upd_Znth_Zlength; try omega.
          rewrite sublist_upd_Znth_l by omega.
          rewrite upd_Znth_same by omega.
          apply Forall2_app; auto.
          constructor; auto.
          unfold failed_CAS; simpl.
          rewrite Heq; repeat eexists; eauto.
        * destruct (Z_le_dec (Zlength m) i).
          { pose proof (Zlength_nonneg m); rewrite sublist_upd_Znth_l by omega; auto. }
          rewrite sublist_upd_Znth_lr; try omega.
          eapply Forall2_upd_Znth_l; auto; try omega; simpl.
          match goal with H : compatible h m |- _ => pose proof (compatible_length _ _ H);
            destruct H as (Hcompat & _) end.
          exploit (Forall2_Znth _ _ _ ([] : hist, [] : hist) (0, 0) Hcompat i).
          { rewrite Zlength_sublist; auto; omega. }
          rewrite !Znth_sublist, Z.add_0_r, Z.sub_0_r by omega.
          setoid_rewrite Heq.
          intros (? & ?); split; eauto.
          evar (R : val); replace (vint (fst (Znth i m (0, 0)))) with R; subst R;
            [apply last_value_new; rewrite Hhi; auto | simpl].
          destruct (eq_dec (Vint i0) (vint 0)).
          { absurd (i0 = Int.zero); auto; inv e; auto. }
          rewrite Hhi in *; simpl in *.
          match goal with H : forall v0, _ -> _ -> Vint i0 = v0 |- _ => apply H; auto end.
          match goal with H : wf_map m |- _ => unfold wf_map in H; rewrite Forall_map, Forall_forall in H;
            exploit (H (Znth i m (0, 0))) end.
          { apply Znth_In; omega. }
          simpl; intros (? & ?).
          intro X; absurd (fst (Znth i m (0, 0)) = 0); auto; apply repr_inj_signed; auto.
          { split; computable. }
          { congruence. }
          { rewrite Zlength_sublist; try omega.
            rewrite Hlen; apply compatible_length; auto. }
          { rewrite Hlen; split; [omega|].
            apply compatible_length; auto. }
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
        setoid_rewrite Hhi.
        rewrite sepcon_comm; auto.
        { rewrite upd_Znth_diff; auto.
          rewrite Zlength_upto in *.
          erewrite !Znth_map, !Znth_upto; auto; try omega.
          rewrite upd_Znth_diff; auto.
          setoid_rewrite Hlen; simpl in *; omega. }
  - Intros i h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) h'; entailer!.
    admit. (* list is long enough *)
Admitted.

Lemma failed_load_fst : forall v h h', Forall2 (failed_load v) h h' -> map snd h' = map snd h.
Proof.
  induction 1; auto.
  destruct H as (? & ? & ? & ? & ? & ?); simpl; f_equal; auto.
Qed.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  forward.
  eapply semax_pre with (P' := EX i : Z, EX h' : list (hist * hist),
    PROP (0 <= i < 20; Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h'; int_hists h';
          Forall2 (failed_load key) (sublist 0 i h) (sublist 0 i h');
          Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
            (sublist 0 (Zlength m) h') m;
          sublist i (Zlength h) h = sublist i (Zlength h') h')
    LOCAL (temp _idx (vint i); temp _key (vint key); gvar _m_entries p)
    SEP (data_at sh (tarray (tptr tentry) 20) entries p; fold_right_sepcon (map (atomic_entry sh) entries);
         entry_hists entries h')).
  { Exists 0 h; rewrite sublist_nil; entailer!.
    match goal with H : compatible h m |- _ => destruct H; auto end. }
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
    assert (Zlength h' = Zlength h) as Hlen.
    { assert (Zlength (sublist i (Zlength h) h) = Zlength (sublist i (Zlength h') h')) as Heq
        by (replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h'); auto).
      rewrite !Zlength_sublist in Heq; try omega.
      destruct (Z_le_dec i (Zlength h')); [omega|].
      unfold sublist in Heq.
      rewrite Z2Nat_neg in Heq by omega.
      simpl in Heq; rewrite Zlength_nil in Heq; omega. }
    assert (i < Zlength h') by omega.
    assert (map snd h' = map snd h) as Hsnd.
    { erewrite <- sublist_same with (al := h') by eauto.
      erewrite <- sublist_same with (al := h) by eauto.
      rewrite sublist_split with (al := h')(mid := i) by omega.
      rewrite sublist_split with (al := h)(mid := i) by omega.
      rewrite Hlen in *; rewrite !map_app; f_equal; [|congruence].
      eapply failed_load_fst; eauto. }
    destruct (Znth i h' ([], [])) as (hki, hvi) eqn: Hhi.
    forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth i entries Vundef), lkey, vint 0,
      hki, fun h => !!(h = hki) && emp, k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      rewrite field_address_offset; simpl.
      rewrite isptr_offset_val_zero; auto.
      { rewrite field_compatible_cons; simpl.
        split; [unfold in_members; simpl|]; auto. } }
    { replace hki with (fst (Znth i h' ([], []))) by (rewrite Hhi; auto); fast_cancel. }
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
    assert (Zlength h' = Zlength h).
    { assert (Zlength (sublist i (Zlength h) h) = Zlength (sublist i (Zlength h') h')) as Heq
        by (replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h'); auto).
      rewrite !Zlength_sublist in Heq; omega. }
    assert (Znth i h ([], []) = Znth i h' ([], []) /\
      sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h') as (Heq & Hi1).
    { match goal with H : sublist _ _ h = sublist _ _ h' |- _ =>
        erewrite sublist_next with (d := ([] : hist, [] : hist)),
                 sublist_next with (l := h')(d := ([] : hist, [] : hist)) in H by omega; inv H; auto end. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ lval).
      forward.
      forward.
      forward_call (Tsh, sh, field_address tentry [StructField _value] (Znth i entries Vundef), lval, vint 0,
        snd (Znth i h' ([], [])), fun (h : hist) => emp, v_R, fun (h : hist) (v : val) => emp).
      { entailer!.
        rewrite field_address_offset; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { repeat (split; auto).
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros x; destruct x as (t', v); simpl in *.
      forward.
      Exists (Int.signed v) (upd_Znth i h' (fst (Znth i h' ([], [])) ++ [(t, Load (vint key))],
        snd (Znth i h' ([], [])) ++ [(t', Load (Vint v))])) (m ++ make_map (sublist (Zlength m) i h')).
      apply andp_right.
      { assert (In (Znth i h' ([], [])) h').
        { apply Znth_In; split; auto; omega. }
        match goal with H : Forall _ h' |- _ => rewrite Forall_forall in H;
          exploit (H (Znth i h' ([], []))); auto; rewrite <- Forall_forall in H end.
        intros (? & ?).
        apply prop_right; split; [|split; [|split; [|split; [|split; [|split]]]]].
        - apply Forall_upd_Znth; auto.
          split; apply ordered_snoc; auto.
          rewrite Hhi; auto.
        - apply Forall_upd_Znth; auto; simpl.
          match goal with H : int_hists h' |- _ => unfold int_hists in H; rewrite Forall_forall in H;
            exploit (H (Znth i h' ([], []))); auto end.
          intros (? & ?); rewrite !map_app, !Forall_app; repeat split; auto; repeat constructor.
        - unfold wf_map; rewrite map_app, Forall_app; split; auto.
(* Clean up some of this redundancy. *)
          unfold make_map; rewrite !Forall_map.
          rewrite Forall_forall; intros ? Hin; simpl.
          apply In_Znth with (d := ([], [])) in Hin.
          destruct Hin as (j & Hj & Hjth).
          destruct (Z_le_dec i (Zlength m)).
          { rewrite sublist_nil_gen, Zlength_nil in Hj; omega. }
          match goal with H : Forall2 (failed_CAS key) _ _ |- _ => exploit (Forall2_In_r _ x _ _ H) end.
          { exploit (Znth_In j (sublist (Zlength m) i h') ([], [])); auto; intro.
            eapply sublist_In; rewrite sublist_sublist, 2Z.add_0_r; subst; eauto; try omega.
            pose (Zlength_nonneg m); omega. }
          intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
          setoid_rewrite Heqi; rewrite last_snoc; simpl.
          destruct (eq_dec (Vint r) (vint 0)).
          { absurd (r = Int.zero); auto; inv e; auto. }
          simpl.
          split; [apply Int.signed_range|].
          intro; absurd (r = Int.zero); auto.
          apply signed_inj; auto.
        - 

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
