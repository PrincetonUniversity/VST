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

Definition value_of_hist (h : hist) := value_of (snd (last h (O, Store (vint 0)))).

Lemma ordered_last_value : forall h v (Hordered : ordered_hist h), last_value h v <-> value_of_hist h = v.
Proof.
  unfold last_value, value_of_hist; split; intro.
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
Definition failed_CAS k (a b : hist * hist) := exists t r, Forall (fun x => fst x < t)%nat (fst a) /\
  fst b = fst a ++ [(t, CAS (Vint r) (vint 0) (vint k))] /\
  r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = Vint r).

Definition set_item_trace (h : list (hist * hist)) k v i h' := 0 <= i < Zlength h /\
  Forall2 (failed_CAS k) (sublist 0 i h) (sublist 0 i h') /\
  (exists t r tv, Forall (fun x => fst x < t)%nat (fst (Znth i h ([], []))) /\
     Forall (fun x => fst x < tv)%nat (snd (Znth i h ([], []))) /\
      Znth i h' ([], []) = (fst (Znth i h ([], [])) ++ [(t, CAS r (vint 0) (vint k))],
                            snd (Znth i h ([], [])) ++ [(tv, Store (vint v))]) /\
      (r = vint 0 \/ r = vint k) /\
      (let v := value_of_hist (fst (Znth i h ([], []))) in v <> vint 0 -> v = r)) /\
  sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h'.

Definition wf_hists h l := Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x) /\
  Forall int_op (map snd (fst x)) /\ Forall int_op (map snd (snd x))) h /\ 0 <= l <= Zlength h /\
    Forall (fun x => value_of_hist (fst x) <> vint 0) (sublist 0 l h) /\
    Forall (fun x => value_of_hist (fst x) = vint 0) (sublist l (Zlength h) h).

Definition make_int v := match v with Vint i => Int.signed i | _ => 0 end.

Fixpoint make_map h :=
  match h with
  | [] => []
  | (hk, hv) :: rest => let k := make_int (value_of_hist hk) in
      if eq_dec k 0 then [] else (k, make_int (value_of_hist hv)) :: make_map rest
  end.

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

(* up *)
Lemma lt_le_1 : forall i j, i < j <-> i + 1 <= j.
Proof.
  intros; omega.
Qed.

(* up *)
Lemma firstn_all : forall {A} n (l : list A), (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n; destruct l; auto; simpl; intros; try omega.
  rewrite IHn; auto; omega.
Qed.

Lemma sublist_all : forall {A} i (l : list A), Zlength l <= i -> sublist 0 i l = l.
Proof.
  intros; unfold sublist; simpl.
  apply firstn_all.
  rewrite Zlength_correct in *; Omega0.
Qed.

Lemma sublist_prefix : forall {A} i j (l : list A), sublist 0 i (sublist 0 j l) = sublist 0 (Z.min i j) l.
Proof.
  intros.
  destruct (Z_le_dec i 0).
  { rewrite !sublist_nil_gen; auto.
    rewrite Z.min_le_iff; auto. }
  destruct (Z.min_spec i j) as [(? & ->) | (? & ->)].
  - rewrite sublist_sublist, !Z.add_0_r by omega; auto.
  - apply sublist_all.
    destruct (Z_le_dec j 0); [rewrite sublist_nil_gen; auto; rewrite Zlength_nil; omega|].
    destruct (Z_le_dec j (Zlength l)).
    rewrite Zlength_sublist; try omega.
    { pose proof (sublist_max_length 0 j l); omega. }
Qed.

Lemma sublist_suffix : forall {A} i j (l : list A), 0 <= i -> 0 <= j ->
  sublist i (Zlength l - j) (sublist j (Zlength l) l) = sublist (i + j) (Zlength l) l.
Proof.
  intros.
  destruct (Z_le_dec (Zlength l - j) i).
  { rewrite !sublist_nil_gen; auto; omega. }
  rewrite sublist_sublist by omega.
  rewrite Z.sub_simpl_r; auto.
Qed.

Lemma sublist_parts1 : forall {A} i j (l : list A), 0 <= i -> sublist i j l = sublist i j (sublist 0 j l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto. }
  rewrite sublist_sublist by omega.
  rewrite !Z.add_0_r; auto.
Qed.

Lemma sublist_parts2 : forall {A} i j (l : list A), 0 <= i -> j <= Zlength l ->
  sublist i j l = sublist 0 (j - i) (sublist i (Zlength l) l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto; omega. }
  rewrite sublist_sublist; try omega.
  rewrite Z.add_0_l, Z.sub_simpl_r; auto.
Qed.

Lemma Forall_Forall2 : forall {A} (P : A -> Prop) Q l1 l2 (HP : Forall P l1) (HQ : Forall2 Q l1 l2)
  (Htransfer : forall x y, P x -> Q x y -> P y), Forall P l2.
Proof.
  induction 2; auto; intros.
  inv HP.
  constructor; eauto.
Qed.

Lemma Forall_suffix_max : forall {A} (P : A -> Prop) l1 l2 i j
  (Hi : 0 <= i <= Zlength l1) (Hj : 0 <= j <= Zlength l1)
  (Hl1 : Forall P (sublist j (Zlength l1) l1))
  (Hl2 : sublist i (Zlength l1) l1 = sublist i (Zlength l2) l2),
  Forall P (sublist (Z.max i j) (Zlength l2) l2).
Proof.
  intros.
  destruct (eq_dec i (Zlength l1)).
  { subst; rewrite sublist_nil in Hl2.
    rewrite Z.max_l by omega.
    rewrite <- Hl2; auto. }
  assert (Zlength l1 = Zlength l2) as Heq.
  { assert (Zlength (sublist i (Zlength l1) l1) = Zlength (sublist i (Zlength l2) l2)) as Heq by congruence.
    destruct (Z_le_dec (Zlength l2) i).
    { rewrite sublist_nil_gen with (l0 := l2), Zlength_nil in Heq; auto.
      rewrite !Zlength_sublist in Heq; omega. }
    rewrite !Zlength_sublist in Heq; omega. }
  intros; destruct (Z.max_spec i j) as [(? & ->) | (? & ->)].
  - replace (sublist _ _ _) with (sublist (j - i) (Zlength l2 - i) (sublist i (Zlength l2) l2)).
    rewrite <- Hl2, sublist_sublist, !Z.sub_simpl_r by omega.
    rewrite <- Heq; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r by omega; auto. }
  - rewrite <- Hl2.
    replace (sublist _ _ _) with (sublist (i - j) (Zlength l1 - j) (sublist j (Zlength l1) l1)).
    apply Forall_sublist; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r; auto; omega. }
Qed.

Lemma Forall_set : forall P m k v, Forall P m -> P (k, v) -> Forall P (set m k v).
Proof.
  intros; unfold set.
  destruct (index_of m k).
  - apply Forall_upd_Znth; auto.
  - rewrite Forall_app; split; auto.
Qed.

Lemma wf_make_map : forall h, wf_map (make_map h).
Proof.
  unfold wf_map; induction h; simpl; auto.
  destruct a.
  if_tac; simpl; auto.
  constructor; auto.
  split; auto.
  destruct (value_of_hist _); simpl; try (split; computable).
  apply Int.signed_range.
Qed.

Lemma make_map_eq : forall h h', Forall2 (fun a b => value_of_hist (fst a) = value_of_hist (fst b) /\
  value_of_hist (snd a) = value_of_hist (snd b)) h h' -> make_map h = make_map h'.
Proof.
  induction 1; auto; simpl.
  destruct x, y; simpl in *.
  destruct H as (-> & ->); rewrite IHForall2; auto.
Qed.

Lemma int_op_value : forall e, int_op e -> tc_val tint (value_of e).
Proof.
  destruct e; auto; simpl.
  intros (? & ? & ?); destruct (eq_dec r c); auto.
Qed.

Corollary int_op_value_of_hist : forall h, Forall int_op (map snd h) -> tc_val tint (value_of_hist h).
Proof.
  intros; unfold value_of_hist.
  apply Forall_last; simpl; auto.
  rewrite Forall_map in H; eapply Forall_impl; [|eauto].
  simpl; intros; apply int_op_value; auto.
Qed.

Lemma make_map_app : forall h1 h2 (Hnz : Forall (fun x => value_of_hist (fst x) <> vint 0) h1)
  (Hint : Forall (fun x => Forall int_op (map snd (fst x))) h1),
  make_map (h1 ++ h2) = make_map h1 ++ make_map h2.
Proof.
  induction 1; auto; simpl; intros.
  inv Hint.
  destruct x.
  rewrite IHHnz; auto.
  if_tac; auto.
  exploit int_op_value_of_hist; eauto; simpl.
  destruct (value_of_hist h) eqn: Hval; try contradiction; simpl in *.
  contradiction H; rewrite Hval.
  f_equal; apply signed_inj; auto.
Qed.

Lemma make_map_drop : forall h1 h2 (Hz : Forall (fun x => value_of_hist (fst x) = vint 0) h2),
  make_map (h1 ++ h2) = make_map h1.
Proof.
  induction h1; simpl; intros.
  - destruct h2; auto; simpl.
    destruct p.
    if_tac; auto.
    inv Hz.
    contradiction H; simpl in *.
    replace (value_of_hist h) with (vint 0); auto.
  - rewrite IHh1; auto.
Qed.

Lemma set_item_trace_map : forall h k v i h' l (Hwf : wf_hists h l) (Htrace : set_item_trace h k v i h')
  (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' (Z.max (i + 1) l) /\ let m' := make_map (sublist 0 i h' ++ sublist i (Zlength h) h) in
    wf_map (set m' k v) /\ incl (make_map h) m' /\ make_map h' = set m' k v.
Proof.
  intros.
  destruct Htrace as (Hbounds & Hfail & (t & r & tv & Ht & Htv & Hi & Hr & Hr0) & Hrest).
  assert (Zlength h' = Zlength h) as Hlen.
  { exploit (Znth_inbounds i h' ([], [])).
    { rewrite Hi; intro X; inversion X as [Heq].
      symmetry in Heq; apply app_cons_not_nil in Heq; auto. }
    intro.
    assert (Zlength (sublist (i + 1) (Zlength h) h) = Zlength (sublist (i + 1) (Zlength h') h')) as Heq
      by (setoid_rewrite Hrest; auto).
    rewrite !Zlength_sublist in Heq; try split; try omega.
    rewrite <- lt_le_1; destruct Hbounds; auto. }
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  destruct Hwf as (Hwf & ? & Hl1 & Hl2).
  assert (h' = sublist 0 i h' ++ Znth i h' ([], []) :: sublist (i + 1) (Zlength h') h') as Hh'.
  { rewrite <- sublist_next, sublist_rejoin, sublist_same; auto; try omega; rewrite Hlen; auto. }
  assert ((if eq_dec r (vint 0) then vint k else r) = vint k) as Hif.
  { if_tac; auto.
    destruct Hr; [absurd (r = vint 0)|]; auto. }
  assert (value_of_hist (fst (Znth i h' ([], []))) = vint k) as Hk'.
  { unfold value_of_hist; rewrite Hi; simpl; rewrite last_snoc; auto. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. }}
  assert (wf_hists h' (Z.max (i + 1) l)) as Hwf'; [|split; auto; split; [|split]].
  - split.
    + rewrite Hh'; clear Hh'; rewrite Forall_app; split; [|constructor].
      * rewrite Forall_forall; intros (?, ?) Hin.
        exploit (Forall2_In_r (failed_CAS k)); eauto.
        intros ((?, ?) & Hin' & ? & ? & ? & ? & ? & ? & ? & ?); simpl in *; subst.
        apply sublist_In in Hin'; rewrite Forall_forall in Hwf; destruct (Hwf _ Hin') as (? & ? & ? & ?).
        rewrite map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto.
      * rewrite Hi; simpl.
        rewrite Forall_forall in Hwf; exploit (Hwf (Znth i h ([], []))).
        { apply Znth_In; auto. }
        intros (? & ? & ? & ?); rewrite !map_app, !Forall_app; repeat constructor; auto;
          try (apply ordered_snoc; auto).
        destruct Hr; subst; simpl; auto.
      * rewrite <- Hrest; apply Forall_sublist; auto.
    + assert (0 <= Z.max (i + 1) l <= Zlength h'); [|split; auto].
      { destruct (Z.max_spec (i + 1) l) as [(? & ->) | (? & ->)]; auto; omega. }
      split; [|apply Forall_suffix_max with (l1 := h); auto; omega].
      rewrite Hh'; clear Hh'.
      assert (Forall (fun x => value_of_hist (fst x) <> vint 0) (sublist 0 i h')).
      { rewrite Forall_forall; intros (?, ?) Hin.
        exploit (Forall2_In_r (failed_CAS k)); eauto.
          intros ((?, ?) & ? & ? & r1 & ? & ? & ? & ? & ? & ?); simpl in *; subst.
        unfold value_of_hist; rewrite last_snoc; simpl.
        destruct (eq_dec (Vint r1) (vint 0)); auto. }
      assert (Zlength h' <= i - 0 + Z.succ (Zlength h' - (i + 1))) by omega.
      assert (0 <= Zlength h' - i) by omega.
      destruct (Z.max_spec (i + 1) l) as [(? & ->) | (? & ->)].
      * rewrite !sublist_app; rewrite ?Zlength_cons, ?Zlength_sublist; auto; try omega.
        rewrite Z.min_l, Z.min_r, Z.max_r, Z.max_l by omega.
        rewrite !Z.sub_0_r.
        rewrite sublist_sublist, !Z.add_0_r by omega.
        rewrite Forall_app; split; auto.
        rewrite sublist_0_cons by omega.
        constructor; [setoid_rewrite Hk'; auto|].
        rewrite sublist_sublist by omega.
        rewrite <- Z.sub_add_distr, Z.sub_simpl_r.
        rewrite Z.add_0_l, sublist_parts2; try omega.
        setoid_rewrite <- Hrest.
        rewrite <- sublist_parts2 by omega.
        rewrite sublist_parts1 by omega; apply Forall_sublist; auto.
        { setoid_rewrite Hlen; omega. }
      * rewrite !sublist_app; rewrite ?Zlength_cons, ?Zlength_sublist; auto; try omega.
        rewrite !Z.sub_0_r, Z.min_l, Z.min_r, Z.max_r, Z.max_l; auto; try omega.
        rewrite Z.add_simpl_l.
        rewrite sublist_same, sublist_len_1 with (d := ([], [])), Znth_0_cons;
          rewrite ?Zlength_cons, ?Zlength_sublist; auto; try omega; simpl.
        rewrite Forall_app; split; auto.
        constructor; auto; setoid_rewrite Hk'; auto.
  - unfold wf_map; rewrite Forall_map; apply Forall_set; auto.
    rewrite <- Forall_map; apply wf_make_map.
  - clear Hh'; match goal with H : 0 <= l <= _ |- _ => destruct H end.
    assert (Forall2 (fun a b => value_of_hist (fst a) = value_of_hist (fst b) /\
      value_of_hist (snd a) = value_of_hist (snd b)) (sublist 0 (Z.min i l) h) (sublist 0 (Z.min i l) h')) as Heq.
    { rewrite Forall2_eq_upto with (d1 := ([] : hist, [] : hist))(d2 := ([] : hist, [] : hist)).
      assert (0 <= Z.min i l <= Zlength h) as (? & ?).
      { split; [rewrite Z.min_glb_iff | rewrite Z.min_le_iff]; auto; omega. }
      split; [rewrite !Zlength_sublist; auto; omega|].
      rewrite Forall_forall; intros ? Hin.
      rewrite In_upto, Z2Nat.id in Hin by (apply Zlength_nonneg).
      assert (value_of_hist (fst (Znth x (sublist 0 (Z.min i l) h) ([], []))) <> vint 0) as Hnz.
      { apply Forall_Znth; auto.
        rewrite <- sublist_prefix; apply Forall_sublist; auto. }
      rewrite Zlength_sublist, Z.sub_0_r in Hin by (auto; omega).
      assert (x < i).
      { destruct Hin; eapply Z.lt_le_trans; eauto.
        apply Z.le_min_l. }
      exploit (Forall2_Znth _ _ _ ([], []) ([], []) Hfail x); auto.
      { rewrite Zlength_sublist; omega. }
      intros (? & r1 & ? & Heq1 & ? & ? & Heq2 & Hv).
      rewrite !Znth_sublist, Z.add_0_r in Heq1, Heq2, Hv, Hnz; auto; try omega.
      rewrite !Znth_sublist, Z.add_0_r in Heq2 by omega.
      rewrite !Znth_sublist, Z.add_0_r by omega.
      setoid_rewrite Heq1; setoid_rewrite Heq2; simpl; split; auto.
      unfold value_of_hist in *; rewrite last_snoc; simpl.
      destruct (eq_dec (Vint r1) (vint 0)); [absurd (r1 = Int.zero); auto; inv e; auto | auto]. }
    replace h with (sublist 0 l h ++ sublist l (Zlength h) h) at 1
      by (rewrite sublist_rejoin, sublist_same; auto; omega).
    rewrite make_map_drop; auto.
    assert (Forall (fun x => Forall int_op (map snd (fst x))) h').
    { destruct Hwf'; eapply Forall_impl; [|eauto]; tauto. }
    destruct (Z.min_spec i l) as [(? & Hmin) | (? & Hmin)]; rewrite Hmin in *; clear Hmin.
    + assert (Forall (fun x : hist * hist => value_of_hist (fst x) <> vint 0) (sublist 0 i h')).
      { eapply Forall_Forall2; try apply Heq.
        { replace i with (Z.min i l) by (apply Z.min_l; omega).
          rewrite <- sublist_prefix; apply Forall_sublist; auto. }
        intros ??? (<- & _); auto. }
      assert (Forall (fun x => Forall int_op (map snd (fst x))) (sublist 0 i h'))
        by (apply Forall_sublist; auto).
      rewrite make_map_app; auto.
      rewrite sublist_split with (lo := i)(mid := l) by omega.
      rewrite make_map_app, app_assoc.
      apply incl_appl.
      rewrite <- make_map_app; auto.
      erewrite make_map_eq; [apply incl_refl|].
      rewrite sublist_split with (mid := i) by omega.
      apply Forall2_app; auto.
      rewrite Forall2_eq_upto with (d1 := ([] : hist, [] : hist))(d2 := ([] : hist, [] : hist)).
      split; auto; rewrite Forall_forall; intros; auto.
      * rewrite sublist_parts1 by omega; apply Forall_sublist; auto.
      * apply Forall_sublist; eapply Forall_impl, Hwf; tauto.
    + rewrite sublist_split with (mid := l)(hi := i) by omega.
      rewrite <- app_assoc, make_map_app.
      apply incl_appl.
      erewrite make_map_eq; [apply incl_refl | auto].
      * eapply Forall_Forall2; try apply Heq; auto.
        intros ??? (<- & _); auto.
      * apply Forall_sublist; auto.
  - unfold set.
    assert (index_of (make_map (sublist 0 i h' ++ sublist i (Zlength h) h)) k =
      if zlt i l then Some i else None) as ->.
    { admit. }
    rewrite Hh' at 1; clear Hh'.
    destruct Hwf' as (? & ? & Hl1' & ?).
    assert (Forall (fun x => value_of_hist (fst x) <> vint 0) (sublist 0 i h') /\
      Forall (fun x => Forall int_op (map snd (fst x))) (sublist 0 i h')) as (? & ?).
    { split.
      + replace i with (Z.min i (Z.max (i + 1) l)).
        rewrite <- sublist_prefix; apply Forall_sublist; auto.
        { apply Z.min_l, Zmax_bound_l; omega. }
      + eapply Forall_sublist, Forall_impl; [|eauto]; tauto. }
    rewrite make_map_app by auto.
    assert (make_map [Znth i h' ([], [])] = [(k, v)]) as Hkv.
    { simpl.
      rewrite Hi; simpl.
      unfold value_of_hist; rewrite !last_snoc; simpl.
      rewrite Hif; simpl.
      rewrite !Int.signed_repr; auto.
      destruct (eq_dec k 0); [contradiction Hk|]; auto. }
    destruct (zlt i l).
    + rewrite make_map_app by auto.
      assert (Zlength (make_map (sublist 0 i h')) = i) as Hleni.
      { admit. }
      rewrite upd_Znth_app2, Hleni, Zminus_diag.
      change (Znth i h' ([], []) :: _) with ([Znth i h' ([], [])] ++ sublist (i + 1) (Zlength h') h').
      rewrite make_map_app, Hkv; simpl.
      rewrite sublist_next with (i0 := i)(d := ([], [])) by (auto; omega); simpl.
      destruct (Znth i h ([], [])) eqn: Hhi.
      if_tac.
      { rewrite Forall_forall in Hl1; pose proof (Hl1 (Znth i (sublist 0 l h) ([], []))) as Hnz.
        lapply Hnz.
        rewrite Znth_sublist, Z.add_0_r by omega; intro; exploit Hr0; auto.
        setoid_rewrite Hhi; simpl; intro X; rewrite X in *.
        rewrite Hhi in *; simpl in *.
        clear Hleni; destruct Hr; subst; simpl in *.
        * absurd (value_of_hist l1 = vint 0); auto.
        * rewrite Int.signed_repr in *; auto; contradiction Hk; auto.
        * apply Znth_In; rewrite Zlength_sublist; try omega.
          tauto. }
      rewrite upd_Znth0, sublist_1_cons, Zlength_cons.
      unfold Z.succ; rewrite Z.add_simpl_r, sublist_same with (lo := 0)(hi := Zlength _); auto.
      f_equal; f_equal; f_equal; auto.
      { constructor; auto; rewrite Hk'; auto. }
      { constructor; auto; rewrite Hi; simpl.
        clear Hleni.
        rewrite map_app, Forall_app; split; [|constructor; auto; destruct Hr; subst; simpl; auto].
        rewrite Forall_forall in Hwf; apply Hwf, Znth_In; auto. }
      { rewrite Hleni.
        pose proof (Zlength_nonneg (make_map (sublist i (Zlength h) h))); omega. }
    + change (Znth i h' ([], []) :: _) with ([Znth i h' ([], [])] ++ sublist (i + 1) (Zlength h') h').
      rewrite make_map_drop, make_map_drop; simpl.
      rewrite Hi; simpl.
      unfold value_of_hist; rewrite !last_snoc; simpl.
      rewrite Hif; simpl.
      rewrite !Int.signed_repr; auto.
      destruct (eq_dec k 0); [contradiction Hk|]; auto.
      { rewrite <- (Z.sub_simpl_r i l), <- sublist_suffix by omega.
        apply Forall_sublist; auto. }
      { rewrite <- Hrest.
        rewrite <- (Z.sub_simpl_r (i + 1) l), <- sublist_suffix by omega.
        apply Forall_sublist; auto. }
Qed.

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list val, h : list (hist * hist), m : list (Z * Z)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Forall isptr entries;
         Zlength h = 20; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist),
   PROP (wf_hists h'; set_item_trace h key value i h';
         wf_map (set m' key value); compatible (sublist 0 i h' ++ sublist i (Zlength h) h) m';
         compatible h' (set m' key value); incl m m')
   LOCAL ()
   SEP (data_at sh (tarray (tptr tentry) 20) entries p;
        fold_right_sepcon (map (atomic_entry sh) entries);
        entry_hists entries h').

Definition failed_load k (a b : hist * hist) := exists t r, fst b = fst a ++ [(t, Load (Vint r))] /\
  r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a.

(* get_item can return 0 in two cases: if the key is not in the map, or if its value is 0.
   In correct use, the latter should only occur if the value has not been initialized.
   Conceptually, this is still linearizable because we could have just checked before the key was added,
   but at a finer-grained level we can tell the difference from the history, so we might as well keep
   this information. *)
Definition get_item_trace (h : list (hist * hist)) k v h' := exists i,
  Forall2 (failed_load k) (sublist 0 i h) (sublist 0 i h') /\
  (let '(hk, hv) := Znth i h ([], []) in exists t,
      (v = 0 /\ Znth i h' ([], []) = (hk ++ [(t, Load (vint 0))], hv)) \/
      exists tv, Znth i h' ([], []) = (hk ++ [(t, Load (vint k))], hv ++ [(tv, Load (vint v))])) /\
  sublist (i + 1) (Zlength h) h = sublist (i + 1) (Zlength h') h'.

(* Read the most recently written value. *)
Definition get_item_spec :=
 DECLARE _get_item
  WITH key : Z, p : val, sh : share, entries : list val, h : list (hist * hist), m : list (Z * Z)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; key <> 0; Forall isptr entries; Zlength h = 20;
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
         value = 0 /\ ~In key (map fst m') /\ incl m m' \/
         get m' key = Some value /\ incl (set m key value) m')
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

Lemma value_match : forall x i m h (Hint : int_hists h) (Hi : 0 <= i <= Zlength h)
  (Hlen : Zlength m <= Zlength h)
  (Hm : Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
    (sublist 0 (Zlength m) h) m)
  (Hordered : Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h)
  (Hin : In x (sublist 0 i (m ++ make_map (sublist (Zlength m) i h)))),
  exists hs, In hs (sublist 0 i h) /\ value_of (snd (last (fst hs) (O, Store (vint 0)))) = vint (fst x).
Proof.
  intros.
  destruct Hi.
  pose proof (Zlength_nonneg m).
  rewrite sublist_app, in_app in Hin; try omega.
  destruct Hin as [Hin | Hin].
  - rewrite Z.min_l in Hin by auto.
    apply In_Znth with (d := (0, 0)) in Hin.
    destruct Hin as (j & (? & Hj) & Hx).
    rewrite Zlength_sublist in Hj.
    rewrite Znth_sublist in Hx by (auto; omega).
    rewrite Z.sub_0_r, Z.min_glb_lt_iff in Hj; destruct Hj.
    exploit (Forall2_Znth _ _ _ ([] : hist, [] : hist) (0, 0) Hm j).
    { rewrite Zlength_sublist; auto; omega. }
    rewrite Z.add_0_r in Hx; rewrite Hx.
    replace (Znth j (sublist 0 (Zlength m) h) ([] : hist, [] : hist)) with
      (Znth j (sublist 0 i h) ([], [])).
    destruct (Znth j (sublist 0 i h) ([], [])) eqn: Hj.
    simpl; intros (? & _).
    exists (Znth j (sublist 0 i h) ([], [])); split.
    { apply Znth_In.
      rewrite Zlength_sublist; auto; omega. }
    rewrite <- ordered_last_value, Hj; auto.
    rewrite Forall_forall in Hordered; apply Hordered.
    rewrite Znth_sublist by omega; apply Znth_In.
    rewrite Z.add_0_r; split; auto; eapply Z.lt_le_trans; eauto.
    { rewrite !Znth_sublist; auto; omega. }
    { split; [apply Z.le_refl|].
      apply Z.min_glb; auto; omega. }
    { apply Z.le_min_r. }
  - apply sublist_In in Hin.
    destruct (Z_le_dec i (Zlength m)).
    { rewrite sublist_nil_gen in Hin; auto; contradiction. }
    apply In_Znth with (d := (0, 0)) in Hin.
    destruct Hin as (j & Hj & Hx).
    unfold make_map in Hj; rewrite Zlength_map, Zlength_sublist in Hj by (auto; omega).
    replace (make_map (sublist (Zlength m) i h)) with (sublist (Zlength m) i (make_map h)) in Hx.
    rewrite Znth_sublist in Hx; try omega.
    exploit (make_compatible h); auto.
    intro Hall; eapply Forall2_Znth with (i0 := j + Zlength m) in Hall; try omega.
    rewrite ordered_last_value in Hall; destruct Hall.
    exists (Znth (j + Zlength m) h ([], [])).
    subst; split; eauto.
    rewrite <- (Z.add_0_r (j + Zlength m)), <- Znth_sublist with (hi := i) by omega.
    apply Znth_In; rewrite Zlength_sublist; omega.
    { rewrite Forall_forall in Hordered; apply Hordered.
      apply Znth_In; split; [omega|].
      apply Z.lt_le_trans with (m := i); auto; omega. }
    { unfold make_map; apply sublist_map. }
  - destruct (Z_le_dec i (Zlength m)); [rewrite sublist_nil_gen, Z.add_0_r; auto|].
    unfold make_map; rewrite Zlength_map, Zlength_sublist; auto; omega.
Qed.

Lemma compatible_update : forall h m i (Hi : 0 <= i < Zlength h)
  (Hordered : Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h) (Hint : int_hists h)
  (Hm : Forall2 (fun hs e =>
    last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e))) (sublist 0 (Zlength m) h) m)
  (Hzero : Forall (fun hs => last_value (fst hs) (vint 0)) (sublist (Z.max i (Zlength m)) (Zlength h) h)),
  compatible (sublist 0 i h ++ sublist i (Zlength h) h) (m ++ make_map (sublist (Zlength m) i h)).
Proof.
  intros; destruct (Z_lt_dec i (Zlength m)).
  - rewrite (sublist_nil_gen _ (Zlength m)), app_nil_r by omega.
    rewrite sublist_rejoin, sublist_same by (auto; omega).
    split; auto.
    rewrite Z.max_r in Hzero by omega; auto.
  - pose proof (Zlength_nonneg m).
    rewrite sublist_split with (mid := (Zlength m)) by omega.
    rewrite <- app_assoc; apply compatible_app.
    + assert (Zlength (sublist 0 (Zlength m) h) = Zlength m) by (rewrite Zlength_sublist; omega).
      unfold compatible; rewrite sublist_same; auto.
      split; auto.
      rewrite sublist_nil'; auto.
    + pose proof (Zlength_nonneg (sublist (Zlength m) i h)).
      pose proof (Zlength_nonneg (sublist i (Zlength h) h)).
      split.
      * unfold make_map at 1; rewrite Zlength_map, sublist_app; try (split; auto; omega).
        rewrite Z.min_l by auto.
        rewrite Z.min_l, sublist_same by (auto; apply Z.le_refl).
        rewrite Zminus_diag.
        rewrite !Z.max_r, sublist_nil, app_nil_r; try omega.
        apply make_compatible.
        { apply Forall_sublist; auto. }
        { apply Forall_sublist; auto. }
        { rewrite Z.le_sub_0; auto. }
        { rewrite <- Z.le_sub_le_add_l, Zminus_diag; auto. }
      * unfold make_map; rewrite Zlength_map, Zlength_app.
        rewrite sublist_app; try omega.
        rewrite Z.min_r, Z.min_r, sublist_nil; try (apply Z.le_refl); try omega.
        rewrite Zminus_diag, Z.max_l, Z.add_simpl_l, Z.max_l, sublist_same; try (apply Z.le_refl); auto.
        rewrite Z.max_l in Hzero; auto; omega.
        { rewrite <- Z.le_sub_le_add_l, Zminus_diag; auto. }
        { apply Z.le_refl. }
    + eapply mem_lemmas.Forall2_Zlength; eauto.
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
        pose proof (Zlength_nonneg m).
        exploit compatible_update; eauto.
        { match goal with H : compatible h m |- _ => destruct H end.
          apply Forall_suffix_max with (l1 := h); auto; omega. }
        intro.
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
        - unfold wf_map in *; rewrite Forall_map; apply Forall_set; auto.
          rewrite <- Forall_map, map_app, Forall_app; split; auto.
          unfold make_map; rewrite !Forall_map.
          rewrite Forall_forall; intros ? Hin; simpl.
          apply In_Znth with (d := ([], [])) in Hin.
          destruct Hin as (j & Hj & Hjth).
          destruct (Z_le_dec i (Zlength m)).
          { rewrite sublist_nil_gen, Zlength_nil in Hj; omega. }
          match goal with H : Forall2 (failed_CAS key) _ _ |- _ => exploit (Forall2_In_r _ x _ _ H) end.
          { exploit (Znth_In j (sublist (Zlength m) i h') ([], [])); auto; intro.
            eapply sublist_In; rewrite sublist_sublist, 2Z.add_0_r; subst; eauto; omega. }
          intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
          setoid_rewrite Heqi; rewrite last_snoc; simpl.
          destruct (eq_dec (Vint r) (vint 0)).
          { absurd (r = Int.zero); auto; inv e; auto. }
          simpl.
          split; [apply Int.signed_range|].
          intro; absurd (r = Int.zero); auto.
          apply signed_inj; auto.
        - rewrite sublist_upd_Znth_l by omega.
          replace (sublist i (Zlength h) h) with (sublist i (Zlength h') h'); auto.
        - match goal with H : Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h' |- _ =>
            rewrite Forall_forall in H; exploit (H (Znth i h' ([], []))) end.
          { apply Znth_In; auto. }
          rewrite Hhi; intros (? & ?).
          apply compatible_set;
            try (rewrite ordered_last_value, last_snoc; simpl; auto; try (apply ordered_snoc; auto)).
          + match goal with H : compatible _ _ |- _ => rewrite sublist_rejoin, sublist_same in H; auto;
              try omega end.
            match goal with H : 0 <= i < Zlength h' |- _ => destruct H end.
            split; [apply Z.lt_le_incl; auto | apply Z.le_refl].
          + assert (Forall (fun x => fst x <> key) (sublist 0 i (m ++ make_map (sublist (Zlength m) i h'))))
              as Hmiss.
            { rewrite Forall_forall; intros ? Hin.
              exploit (value_match x i m h'); auto.
              { omega. }
              { rewrite Forall_forall; auto. }
              intros ((hk, hv) & Hin' & Hlast).
              match goal with H : Forall2 (failed_CAS key) _ _ |- _ =>
                exploit (Forall2_In_r _ (hk, hv) _ _ H); auto end.
              intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
              rewrite Heqi, last_snoc in Hlast; simpl in Hlast.
              destruct (eq_dec (Vint r) (vint 0)).
              { absurd (r = Int.zero); auto; inv e; auto. }
              inversion Hlast.
              intro; absurd (r = Int.repr key); subst; auto. }
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

Lemma compatible_alt : forall h m, Forall2
  (fun (hs : hist * hist) (e : Z * Z) => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
  (sublist 0 (Zlength m) h) m <-> m = make_map (sublist 0 (Zlength m) h).
Proof.
  induction h; intro.
  - rewrite sublist_of_nil; split; intro; subst; simpl; auto.
    inv H; auto.
  - destruct (Z_le_dec (Zlength m) 0).
    { rewrite sublist_nil_gen by auto.
      split; intro; subst; simpl; auto.
      inv H; auto. }
    rewrite sublist_0_cons by omega.
    split; intro; simpl.
    + inv H.
      rewrite Zlength_cons in *.
      unfold Z.succ in *; rewrite Z.add_simpl_r in *.
      rewrite IHh in H4.
      rewrite !ordered_last_value in H2.
      destruct y, H2; f_equal; auto.
      simpl in *; setoid_rewrite H; setoid_rewrite H0.
      admit.
      admit.
      admit.
    + destruct m; [discriminate | simpl in *].
      inversion H; subst p.
      rewrite H; simpl.
      constructor; simpl.
      * admit.
      * rewrite Zlength_cons.
        unfold make_map at 1; rewrite Zlength_map.
        unfold Z.succ; rewrite Z.add_simpl_r.
        rewrite Zlength_sublist, Z.sub_0_r.
        rewrite IHh.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  forward.
  eapply semax_pre with (P' := EX i : Z, EX h' : list (hist * hist),
    PROP (0 <= i < 20; Forall (fun x => ordered_hist (fst x) /\ ordered_hist (snd x)) h'; int_hists h';
          Forall2 (failed_load key) (sublist 0 i h) (sublist 0 i h');
(*          Forall2 (fun hs e => last_value (fst hs) (vint (fst e)) /\ last_value (snd hs) (vint (snd e)))
            (sublist 0 (Zlength m) h') m;*)
          m = make_map (sublist 0 (Zlength m) h');
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
        snd (Znth i h' ([], [])) ++ [(t', Load (Vint v))]))
        (set (m ++ make_map (sublist (Zlength m) i h')) key (Int.signed v)).
      apply andp_right.
      { assert (In (Znth i h' ([], [])) h').
        { apply Znth_In; split; auto; omega. }
        match goal with H : Forall _ h' |- _ => rewrite Forall_forall in H;
          exploit (H (Znth i h' ([], []))); auto; rewrite <- Forall_forall in H end.
        intros (? & ?).
        pose proof (Zlength_nonneg m).
        apply prop_right; split; [|split; [|split; [|split; [|split]]]].
        - apply Forall_upd_Znth; auto.
          split; apply ordered_snoc; auto.
          rewrite Hhi; auto.
        - apply Forall_upd_Znth; auto; simpl.
          match goal with H : int_hists h' |- _ => unfold int_hists in H; rewrite Forall_forall in H;
            exploit (H (Znth i h' ([], []))); auto end.
          intros (? & ?); rewrite !map_app, !Forall_app; repeat split; auto; repeat constructor.
        - unfold wf_map in *; rewrite Forall_map; apply Forall_set; auto.
          rewrite <- Forall_map, map_app, Forall_app; split; auto.
          unfold make_map; rewrite !Forall_map.
          rewrite Forall_forall; intros ? Hin; simpl.
          apply In_Znth with (d := ([], [])) in Hin.
          destruct Hin as (j & Hj & Hjth).
          destruct (Z_le_dec i (Zlength m)).
          { rewrite sublist_nil_gen, Zlength_nil in Hj; omega. }
          match goal with H : Forall2 (failed_load key) _ _ |- _ => exploit (Forall2_In_r _ x _ _ H) end.
          { exploit (Znth_In j (sublist (Zlength m) i h') ([], [])); auto; intro.
            eapply sublist_In; rewrite sublist_sublist, 2Z.add_0_r; subst; eauto; omega. }
          intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
          setoid_rewrite Heqi; rewrite last_snoc; simpl.
          destruct (eq_dec (Vint r) (vint 0)).
          { absurd (r = Int.zero); auto; inv e; auto. }
          simpl.
          split; [apply Int.signed_range|].
          intro; absurd (r = Int.zero); auto.
          apply signed_inj; auto.
        - assert (Zlength m <= Zlength h) by (apply compatible_length; auto).
          apply compatible_set; auto;
            try (rewrite ordered_last_value, last_snoc; simpl; rewrite ?Int.repr_signed; auto;
            try (apply ordered_snoc; auto)).
          + erewrite <- sublist_same at 1; eauto.
            rewrite sublist_split with (mid := i) by omega.
            apply compatible_update; auto.
            { split; auto; omega. }
            { match goal with H : compatible h m |- _ => destruct H end.
              apply Forall_suffix_max with (l1 := h); auto; omega. }
          + assert (Forall (fun x => fst x <> key) (sublist 0 i (m ++ make_map (sublist (Zlength m) i h'))))
              as Hmiss.
            { rewrite Forall_forall; intros ? Hin.
              exploit (value_match x i m h'); auto; try omega.
              intros ((hk, hv) & Hin' & Hlast).
              match goal with H : Forall2 (failed_load key) _ _ |- _ =>
                exploit (Forall2_In_r _ (hk, hv) _ _ H); auto end.
              intros (? & ? & ? & r & Heqi & ? & ? & ?); subst.
              rewrite Heqi, last_snoc in Hlast; simpl in Hlast.
              inversion Hlast.
              intro; absurd (r = Int.repr key); subst; auto. }
            destruct (Z_lt_dec i (Zlength m)).
            * left; rewrite sublist_nil_gen, app_nil_r by (auto; omega).
              rewrite sublist_nil_gen with (i0 := Zlength m), app_nil_r in Hmiss by omega.
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
                match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
                  exploit H; eauto end.
                { intro; absurd (z = 0); auto; apply repr_inj_signed; auto.
                  simpl in *; congruence. }
                intro X; apply repr_inj_signed; auto; simpl in *; congruence. }
              subst; rewrite eq_dec_refl; simpl.
              rewrite Zlength_sublist by omega; f_equal; omega.
              { rewrite <- sublist_next, sublist_rejoin, sublist_same; auto; omega. }
            * right; assert (i = Zlength (m ++ make_map (sublist (Zlength m) i h'))).
              { unfold make_map; rewrite Zlength_app, Zlength_map, Zlength_sublist; auto; try omega.
                apply Z.lt_le_incl; auto. }
              split; auto.
              rewrite sublist_same in Hmiss; auto.
              apply index_of_out; auto.
          + rewrite Hhi; auto.
        - exists i; split; [|split].
          + rewrite sublist_upd_Znth_l; auto; omega.
          + rewrite upd_Znth_same by omega.
            replace (Znth i h ([], [])) with (Znth i h' ([], [])).
            destruct (Znth i h' ([], [])).
            rewrite Int.repr_signed; eauto.
          + rewrite upd_Znth_Zlength by omega.
            rewrite sublist_upd_Znth_r; auto; omega.
        - split; auto.
          right.
          admit. }
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
