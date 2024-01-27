Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Opaque upto.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Lemma body_initialize_writer : semax_body Vprog Gprog f_initialize_writer initialize_writer_spec.
Proof.
  start_function.
  rename a into gv.
  forward.
  forward.
  forward_for_simple_bound N (∃ i : Z, PROP ( )
   LOCAL (gvars gv)
   SEP (field_at Ews tint [] (eval_unop Oneg tint (vint 1)) (gv _writing); field_at Ews tint [] (vint 0) (gv _last_given);
        data_at Ews (tarray tint N) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) (gv _last_taken))).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - assert (N < Int.max_signed) by computable.
    forward.
    rewrite upd_init_const; auto.
  - forward.
Qed.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
  start_function.
  assert (N < Int.max_signed) as HN by computable.
  assert (B < Int.max_signed) as HB by computable.
  forward_for_simple_bound B (∃ i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint B) v_available; gvars gv)
   SEP (data_at Tsh (tarray tint B) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) v_available;
        data_at_ Ews tint (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
  { entailer!; 
        simpl; cancel. (* this line needed before VST 2.12 *)  }
  { forward.
    rewrite upd_init_const; auto; entailer!. }
  rewrite Zminus_diag app_nil_r.
  forward.
  forward.
  assert_PROP (Zlength lasts = N).
  { gather_SEP (data_at _ _ _ (gv _last_taken)).
    go_lowerx.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; lia|].
    apply bi.pure_mono; intros (? & ? & ?).
    unfold unfold_reptype in *; simpl in *.
    rewrite -> Zlength_map in *; auto. }
  forward_for_simple_bound N (∃ i : Z, PROP ( )
   LOCAL (temp _i (vint B); lvar _available (tarray tint B) v_available; gvars gv)
   SEP (data_at Tsh (tarray tint B) (map (fun x => vint (if eq_dec x b0 then 0
     else if in_dec eq_dec x (sublist 0 i lasts) then 0 else 1)) (upto (Z.to_nat B))) v_available;
   data_at_ Ews tint (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
   data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
  { entailer!.
    f_equiv.
    rewrite upd_Znth_eq;
       [|simpl; rewrite -> !Zlength_cons, Zlength_nil; unfold B, N in *; lia].
    simpl Datatypes.length.
    change (Z.to_nat B) with 5%nat.
    apply map_ext_in; intros ? Hin.
    rewrite In_upto in Hin. unfold eq_dec, EqDec_Z, zeq.
    destruct (Z.eq_dec a b0); auto.
    if_tac; first list_solve.
    rewrite -> Znth_repeat' by auto; done. }
  Opaque eq_dec.
  { assert (0 <= i < Zlength lasts) by lia.
    forward.
    forward_if (PROP ( )
      LOCAL (temp _last (vint (Znth i lasts)); temp _r (vint i); temp _i (vint B); lvar _available (tarray tint 5) v_available; gvars gv)
      SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) v_available;
           data_at_ Ews tint (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
    - assert (0 <= Znth i lasts < B) by (apply Forall_Znth; auto).
      forward.
      entailer!.
      rewrite upd_Znth_eq; [|auto].
      rewrite /data_at; f_equiv.
      apply map_ext_in.
      intros; rewrite -> In_upto(*, map_length, upto_length*) in *; simpl in *.
      erewrite Znth_map, Znth_upto; simpl; auto; try lia.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1; auto; try lia.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts])); rewrite -> in_app in *.
      + destruct (Z.eq_dec a (Znth i lasts)); destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
      + destruct (Z.eq_dec a (Znth i lasts)).
        { subst; contradiction n; simpl; auto. }
        destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto; contradiction n; auto.
    - forward.
      entailer!.
      rewrite /data_at; f_equiv.
      apply map_ext_in.
      intros; rewrite -> In_upto in *; simpl in *.
      destruct (eq_dec a b0); auto.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1; auto; try lia.
(*      match goal with H : Int.repr _ = Int.neg _ |- _ => apply repr_inj_signed in H end. *)
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts])); rewrite -> in_app in *.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        apply repr_inj_signed in H4; rep_lia.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        contradiction n0; auto.
    - intros. entailer!. }
  rewrite sublist_same; auto.
  set (available := map (fun x => vint (if eq_dec x b0 then 0 else if in_dec eq_dec x lasts then 0 else 1))
         (upto (Z.to_nat B))).
  unfold Sfor.
  forward.
  eapply semax_seq, semax_ff.
  eapply semax_pre with (P' := ∃ i : Z, PROP (0 <= i <= B; forall j, 0 <= j < i -> Znth j available = vint 0)
    LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) v_available; gvars gv)
    SEP (field_at Tsh (tarray tint 5) [] available v_available; data_at_ Ews tint (gv _writing);
         data_at Ews tint (vint b0) (gv _last_given); data_at Ews (tarray tint N) (map (fun x => vint x) lasts) (gv _last_taken))).
  { Exists 0; entailer!. }
  eapply semax_loop.
  + Intros i.
    assert (repable_signed i).
    { split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try lia. }
    forward_if (PROP (i < B)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) v_available; gvars gv)
      SEP (field_at Tsh (tarray tint 5) [] available v_available; data_at_ Ews tint (gv _writing);
           data_at Ews tint (vint b0) (gv _last_given);
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
    { forward.
      entailer!. }
    { forward.
      exploit (list_pigeonhole (b0 :: lasts) B).
      { rewrite Zlength_cons; unfold B; lia. }
      intros (j & ? & Hout); exploit (H3 j); [unfold B, N in *; lia|].
      subst available.
      rewrite Znth_map; [|rewrite Zlength_upto; auto].
      rewrite Znth_upto; [|rewrite Z2Nat.id; lia].
      destruct (eq_dec j b0); [contradiction Hout; simpl; auto|].
      destruct (in_dec eq_dec j lasts); [contradiction Hout; simpl; auto|].
      discriminate. }
    Intros.
    assert (0 <= i < Zlength (upto (Z.to_nat B))) by tauto.
    forward.
    forward_if (PROP (Znth i available = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) v_available; gvars gv)
      SEP (field_at Tsh (tarray tint B) [] available v_available; data_at_ Ews tint (gv _writing);
           data_at Ews tint (vint b0) (gv _last_given); data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
    { forward.
      forward.
      Exists i; entailer!.
      { subst available.
        rewrite -> Znth_upto in *.
        destruct (eq_dec i b0); [|destruct (in_dec eq_dec i lasts)]; auto; discriminate.
        all: change B with 5 in * ; lia. }
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      erewrite Znth_map, Znth_upto; rewrite -> ?Zlength_upto, ?Z2Nat.id; try assumption; try lia.
      match goal with H : Int.repr _ = Int.zero |- _ => rewrite Znth_upto in H;
        try assumption; rewrite -> ?Zlength_upto, ?Z2Nat.id; try lia end.
      destruct (eq_dec _ _); auto.
      destruct (in_dec _ _ _); auto; discriminate. }
    instantiate (1 := ∃ i : Z, PROP (0 <= i < B; Znth i available = vint 0;
      forall j : Z, 0 <= j < i -> Znth j available = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) v_available; gvars gv)
      SEP (field_at Tsh (tarray tint B) [] available v_available; data_at_ Ews tint (gv _writing);
           data_at Ews tint (vint b0) (gv _last_given); data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
    Intros. Exists i; entailer!.
    Intros i'. Exists i'. entailer!.
  + Intros i.
    forward.
      assert (B < Int.max_signed) by (compute; auto).
      entailer!.
    unfold loop2_ret_assert.
    Exists (i + 1); entailer!.
    intros; destruct (eq_dec j i); subst; auto.
    assert (0 <= j < i) by lia; auto.
Qed.

Lemma find_write_rest : forall d h, exists n, snd (find_write h d) = skipn n h.
Proof.
  induction h; simpl; intros; try discriminate.
  { exists O; auto. }
  destruct a.
  destruct (eq_dec w Empty).
  - destruct IHh as (n & ?); subst.
    exists (S n); auto.
  - exists 1%nat; auto.
Qed.

Corollary prev_taken_In : forall h, prev_taken h = vint 1 \/ In (AE (prev_taken h) Empty) h.
Proof.
  intros; unfold prev_taken.
  destruct (find_read_In (vint 1) (snd (find_write h (vint 0)))).
  - inv H; auto.
  - destruct (find_write_rest (vint 0) h) as (? & Hrest); rewrite -> Hrest in *.
    right; eapply skipn_In; eauto.
Qed.

Lemma write_val : forall h i v (Hh : apply_hist i (rev h) = Some v), v = Empty \/ v = fst (find_write h i).
Proof.
  induction h; simpl; intros.
  { inv Hh; auto. }
  destruct a.
  rewrite apply_hist_app in Hh; simpl in Hh.
  destruct (apply_hist i (rev h)) eqn: Hh'; [|discriminate].
  destruct (eq_dec r v0); inv Hh.
  destruct (eq_dec v Empty); auto.
Qed.

Lemma find_write_read : forall i d h (Hread : apply_hist i (rev h) = Some Empty) (Hi : i <> Empty),
  fst (find_read h d) = fst (find_write h i).
Proof.
  induction h; auto; simpl; intros.
  { inv Hread; contradiction Hi; auto. }
  destruct a.
  rewrite apply_hist_app in Hread; simpl in Hread.
  destruct (apply_hist i (rev h)) eqn: Hh; [|discriminate].
  destruct (eq_dec r v); [subst | discriminate].
  inv Hread.
  if_tac; last done.
  destruct (eq_dec v Empty); eauto.
  exploit write_val; eauto; intros [? | ?]; subst; eauto; contradiction n; auto.
Qed.

Lemma take_read : forall h v, apply_hist (vint 0) (rev h) = Some v ->
  prev_taken h = if eq_dec v Empty then snd (last_two_reads h)
                 else fst (last_two_reads h).
Proof.
  induction h; simpl; intros.
  - inv H.
    destruct (eq_dec (vint 0) Empty); auto.
  - destruct a; rewrite prev_taken_cons last_two_reads_cons.
    rewrite apply_hist_app in H; simpl in H.
    destruct (apply_hist (vint 0) (rev h)) eqn: Hh; [|discriminate].
    destruct (eq_dec r v0); [subst | discriminate].
    inv H.
    erewrite IHh; eauto.
    destruct (eq_dec v Empty).
    + destruct (eq_dec v0 Empty); auto.
    + unfold last_two_reads.
      destruct (find_read h (vint 1)); auto.
Qed.

Lemma find_write_In : forall d h, fst (find_write h d) = d \/ exists r, In (AE r (fst (find_write h d))) h.
Proof.
  induction h; auto; simpl; intros.
  destruct a.
  destruct (eq_dec w Empty); [destruct IHh as [|(? & ?)]|]; eauto.
Qed.

Lemma make_shares_app : forall i l1 l2 shs, Zlength l1 + Zlength l2 <= Zlength shs ->
  make_shares shs (l1 ++ l2) i =
  make_shares shs l1 i ++ make_shares (sublist (Zlength l1) (Zlength shs) shs) l2 i.
Proof.
  induction l1; simpl; intros.
  - rewrite sublist_same; auto.
  - rewrite -> Zlength_cons in *.
    destruct shs.
    { rewrite -> Zlength_nil, !Zlength_correct in *; lia. }
    rewrite -> Zlength_cons in *; simpl; rewrite IHl1; [|lia].
    rewrite (sublist_S_cons (Z.succ _)); [|rewrite Zlength_correct; lia].
    unfold Z.succ; rewrite !Z.add_simpl_r.
    destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_ext : forall i l l' shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j l = i <-> Znth j l' = i),
  make_shares shs l i = make_shares shs l' i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite -> ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite -> Zlength_correct in *; lia).
  exploit (Hi 0); [rewrite Zlength_correct; lia|].
  rewrite !Znth_0_cons; intro Hiff.
  rewrite (IHl l'); try lia.
  - destruct (eq_dec a i), (eq_dec z i); tauto.
  - intros; exploit (Hi (j + 1)); [lia|].
    rewrite -> !Znth_pos_cons, !Z.add_simpl_r; auto; lia.
Qed.

(* The complement of make_shares. *)
Fixpoint make_shares_inv shs (lasts : list Z) i {struct lasts} : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then hd Share.bot shs :: make_shares_inv (tl shs) rest i
                 else make_shares_inv (tl shs) rest i
  end.

Lemma make_shares_minus : forall i lasts sh0 shs sh' sh1 (Hsh' : sepalg_list.list_join sh0 shs sh')
  (Hsh1 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh1)
  (Hlen : Zlength shs = Zlength lasts),
  sepalg_list.list_join sh1 (make_shares_inv shs lasts i) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite -> ?Zlength_cons, ?Zlength_nil in *;
    try (rewrite -> Zlength_correct in *; lia).
  - inv Hsh1; inv Hsh'; constructor.
  - inversion Hsh' as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (x & ? & Hx).
      exploit IHlasts; eauto; [lia|].
      intro Hj'; destruct (sepalg_list.list_join_assoc2 Hj' Hx) as (? & ? & ?).
      econstructor. apply sepalg.join_comm; eassumption. auto.
    + inversion Hsh1 as [|????? Hja]; inversion Hsh' as [|????? Hjb]; subst.
      pose proof (sepalg.join_eq Hja Hjb); subst.
      eapply IHlasts; eauto; lia.
Qed.

Lemma make_shares_add : forall i i' lasts j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts = i) (Hi' : i' <> i) (Hlen : Zlength shs >= Zlength lasts),
  exists shs1 shs2, make_shares shs lasts i = shs1 ++ shs2 /\
    make_shares shs (upd_Znth j lasts i') i = shs1 ++ Znth j shs :: shs2.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite -> ?Zlength_cons, ?Zlength_nil in *; try lia.
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in Hi', IHlasts; rewrite !Znth_0_cons.
    rewrite eq_dec_refl upd_Znth0; auto; try lia; simpl.
    destruct (eq_dec i' a); [contradiction Hi'; auto|].
    eexists [], _; simpl; split; eauto.
  - rewrite Znth_pos_cons in Hi; [|lia].
    rewrite Znth_pos_cons; [|lia].
    exploit (IHlasts (j - 1) shs); try lia.
    intros (shs1 & shs2 & Heq1 & Heq2).
    rewrite upd_Znth_cons; [simpl | lia].
    exists (if eq_dec a i then shs1 else t :: shs1), shs2; rewrite Heq1 Heq2; destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts <> i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs)  (make_shares shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite -> Zlength_nil in *; lia.
  - destruct shs; rewrite -> !Zlength_cons in *; [rewrite -> Zlength_nil, Zlength_correct in *; lia|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in Hi; rewrite Znth_0_cons.
      destruct (eq_dec a i); [contradiction Hi | simpl]; auto.
    + rewrite Znth_pos_cons in Hi; [|lia].
      rewrite Znth_pos_cons; [|lia].
      exploit (IHlasts (x - 1) shs); eauto; try lia.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma make_shares_inv_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts = i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs) (make_shares_inv shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite -> Zlength_nil in *; lia.
  - destruct shs; rewrite -> !Zlength_cons in *; [rewrite -> Zlength_nil, Zlength_correct in *; lia|].
    destruct (eq_dec x 0).
    + subst; rewrite -> Znth_0_cons in *; rewrite Znth_0_cons; subst.
      rewrite eq_dec_refl; simpl; auto.
    + rewrite Znth_pos_cons in Hi; [|lia].
      rewrite Znth_pos_cons; [|lia].
      exploit (IHlasts (x - 1) shs); eauto; try lia.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma make_shares_sub : forall i lasts shs sh0 sh1 sh2 (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1) (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2),
  sepalg.join_sub sh2 sh1.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite -> ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite -> Zlength_correct in *; lia).
  - inv Hsh1; inv Hsh2; apply sepalg.join_sub_refl.
  - inversion Hsh1 as [|????? Hj1 Hj2]; inv Hsh2.
    destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?); eexists; eauto.
  - inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      exploit IHlasts; eauto; [lia|].
      intro; eapply sepalg.join_sub_trans; eauto.
       eexists; apply sepalg.join_comm; eassumption.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; lia.
Qed.

Lemma make_shares_join : forall i lasts shs sh0 j sh1 sh2
  (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1)
  (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2)
  (Hin : 0 <= j < Zlength shs)
  (Hj : Znth j lasts = i),
  exists sh', sepalg.join sh2 (Znth j shs) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite -> ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite -> Zlength_correct in *; lia); try lia.
  { rewrite Znth_overflow in Hj; [|rewrite Zlength_nil; lia].
    inv Hsh2.
    exploit (Znth_In j (t :: shs)); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply sepalg_list.list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  - subst j; rewrite Znth_0_cons in Hj; rewrite Znth_0_cons; subst.
    rewrite eq_dec_refl in Hsh2.
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    exploit make_shares_sub; eauto; [lia|].
    intro; eapply sepalg.join_sub_joins_trans; try eassumption.
    eexists; apply sepalg.join_comm; eassumption.
  - rewrite Znth_pos_cons in Hj; [|lia].
    rewrite Znth_pos_cons; [|lia].
    inversion Hsh1 as [|????? Hj1 Hj2].
    destruct (eq_dec a i); subst.
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      eapply IHlasts; eauto; lia.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; lia.
Qed.

Lemma make_shares_join' : forall i lasts shs sh0 j sh1 sh2
  (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1)
  (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2)
  (Hin : 0 <= j < Zlength shs) (Hout : Zlength lasts <= j),
  exists sh', sepalg.join sh2 (Znth j shs) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite -> ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite -> Zlength_correct in *; lia); try lia.
  { inv Hsh2.
    exploit (Znth_In j (t :: shs)); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply sepalg_list.list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  { subst; rep_lia. }
  rewrite Znth_pos_cons; [|lia].
  inversion Hsh1 as [|????? Hj1 Hj2].
  destruct (eq_dec a i); subst.
  + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    eapply IHlasts; eauto; lia.
  + inversion Hsh2 as [|????? Hj1']; subst.
    pose proof (sepalg.join_eq Hj1 Hj1'); subst.
    eapply IHlasts; eauto; lia.
Qed.

Lemma data_at_buffer_cohere : forall sh1 sh2 v1 v2 p, readable_share sh1 ->
  data_at sh1 tbuffer v1 p ∗ data_at sh2 tbuffer v2 p ⊢
  data_at sh1 tbuffer v1 p ∗ data_at sh2 tbuffer v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply bi.and_intro; first auto.
  rewrite !data_at_rec_eq; unfold withspacer, at_offset; simpl.
  rewrite !data_at_rec_eq; simpl.
  apply mapsto_value_cohere; auto.
Qed.

Lemma hd_Znth': forall {A} (d: A) al, hd d al = @Znth A d 0 al.
Proof.
intros. destruct al; reflexivity.
Qed.

(* up *)
Lemma list_insert_upd : forall {A} i (a : A) l, 0 <= i < Zlength l ->
  <[Z.to_nat i := a]>l = upd_Znth i l a.
Proof.
  intros; revert dependent i; induction l; simpl; intros.
  - rewrite Zlength_nil in H; lia.
  - rewrite Zlength_cons in H.
    destruct (Z.to_nat i) eqn: Hi; simpl.
    + assert (i = 0) as -> by lia.
      rewrite upd_Znth0 //.
    + rewrite upd_Znth_cons; last lia.
      rewrite -IHl; last lia.
      replace n with (Z.to_nat (i - 1)) by lia; done.
Qed.

Lemma upd_Znth_sep : forall {B : bi} i l (P : B), 0 <= i < Zlength l ->
  P ∗ [∗] (upd_Znth i l emp) ⊣⊢ [∗] (upd_Znth i l P).
Proof.
  intros; iSplit.
  - rewrite big_sepL_insert_acc; last by (apply Znth_lookup; rewrite Zlength_upd_Znth).
    rewrite upd_Znth_same //.
    iIntros "(P & _ & H)"; iSpecialize ("H" with "P").
    rewrite list_insert_upd; last by rewrite Zlength_upd_Znth.
    rewrite upd_Znth_twice //.
  - rewrite big_sepL_insert_acc; last by (apply Znth_lookup; rewrite Zlength_upd_Znth).
    rewrite upd_Znth_same //.
    iIntros "($ & H)"; iSpecialize ("H" $! emp with "[]"); first done.
    rewrite list_insert_upd; last by rewrite Zlength_upd_Znth.
    rewrite upd_Znth_twice //.
Qed.

(* The relationship between the last_taken array and the shares held by the writer is
   preserved by the action of the loop body. *)
Lemma upd_write_shares : forall bufs b b0 lasts shs sh0 (Hb : 0 <= b < B) (Hb0 : 0 <= b0 < B)
  (Hlasts : Forall (fun x : Z => 0 <= x < B) lasts) (Hshs : Zlength shs = N)
  (Hread : Forall readable_share shs) (Hsh0 : sepalg_list.list_join sh0 shs Ews)
  (Hdiff : b <> b0) (Hout : ~ In b lasts) (Hout0 : ~ In b0 lasts) (Hlasts : Zlength lasts = N)
  bsh' v' (Hv' : -1 <= v' < B) h' (Hh' : 0 <= Zlength h' < N)
  (Hbsh' : sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) bsh')
  bsh (Hbsh : sepalg.join bsh' (Znth (Zlength h') shs) bsh),
  (if eq_dec v' (-1) then
   ∃ v0 : Z, data_at (Znth (Zlength h') shs) tbuffer (vint v0) (Znth (Znth (Zlength h') lasts) bufs)
   else ⌜v' = b0⌝ ∧ (∃ v'0 : Z, data_at (Znth (Zlength h') shs) tbuffer (vint v'0) (Znth b0 bufs))) ∗
  ((∃ v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs)) ∗
  [∗] (upd_Znth b (map (fun a => ∃ sh : share, ⌜if eq_dec a b0 then
    sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
      (map (fun i : Z => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) a) sh
      else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
      else sepalg_list.list_join sh0 (make_shares shs
      (map (fun i : Z => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N))) a) sh⌝ ∧
      (∃ v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs))) (upto (Z.to_nat B))) emp))
  ⊢ [∗] (map (fun a => ∃ sh : share, ⌜if eq_dec a b0 then
        sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) a) sh
          else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) sh
          else sepalg_list.list_join sh0 (make_shares shs
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty then b0 else Znth i lasts) (upto (Z.to_nat N))) a) sh⌝ ∧
          (∃ v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs))) (upto (Z.to_nat B))).
Proof.
  intros; set (shi := Znth (Zlength h') shs).
  assert (readable_share shi).
  { apply Forall_Znth; auto; lia. }
  set (lasti := Znth (Zlength h') lasts).
  exploit (Znth_In (Zlength h') lasts); [lia | intro Hini].
  assert (lasti <> b) as Hneq.
  { intro; match goal with H : ~In b lasts |- _ => contradiction H end; subst b lasti; auto. }
  assert (lasti <> b0) as Hneq0.
  { intro; match goal with H : ~In b0 lasts |- _ => contradiction H end; subst b0 lasti; auto. }
  set (l0 := upd_Znth b (map (fun a => ∃ sh : share, ⌜if eq_dec a b0 then
             sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
               (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) a) sh
           else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
           else sepalg_list.list_join sh0 (make_shares shs (map (fun i => if eq_dec (Znth i h') Empty then b0
                                           else Znth i lasts) (upto (Z.to_nat N))) a) sh⌝ ∧
          (∃ v1 : Z, data_at(cs := CompSpecs) sh tbuffer (vint v1) (Znth a bufs))) (upto (Z.to_nat B)))
          (∃ v1 : Z, data_at(cs := CompSpecs) bsh' tbuffer (vint v1) (Znth b bufs))).
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map Zlength_upto; auto. }
  assert (0 <= lasti < B).
  { apply Forall_Znth; auto; lia. }
  apply derives_trans with ([∗] (
    if eq_dec v' (-1) then upd_Znth lasti l0
            (∃ sh : share, ⌜exists sh', sepalg_list.list_join sh0 (make_shares shs
             (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N))) lasti) sh' /\
             sepalg.join sh' shi sh⌝ ∧
            (∃ v1 : Z, data_at(cs := CompSpecs) sh tbuffer (vint v1) (Znth lasti bufs)))
          else upd_Znth b0 l0 (∃ sh : share, ⌜exists sh', sepalg_list.list_join sh0 (make_shares shs
            (sublist 0 (Zlength h') (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts)
            (upto (Z.to_nat N)))) b0) sh' /\ sepalg.join sh' shi sh⌝ ∧
            (∃ v1 : Z, data_at(cs := CompSpecs) sh tbuffer (vint v1) (Znth b0 bufs))))).
  { rewrite upd_Znth_sep. 2 : {
      rewrite Zlength_map.
      rewrite Zlength_upto.
      lia.
    }
    destruct (eq_dec v' (-1)).
    - rewrite (big_sepL_insert_acc _ _ (Z.to_nat lasti)).
      2: { apply Znth_lookup. subst l0; rewrite H0 //. }
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try lia.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros v1 ish v2.
      sep_apply data_at_buffer_cohere.
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join; eauto.
        + setoid_rewrite Hshs; rewrite Zlength_map Zlength_upto Z2Nat.id; lia.
        + setoid_rewrite Hshs; auto.
        + rewrite -> Znth_map by (rewrite Zlength_upto Z2Nat.id; lia).
            rewrite -> Znth_upto by (rewrite ?Z2Nat.id; lia).
            rewrite Znth_overflow; auto; lia. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      setoid_rewrite list_insert_upd; last by subst l0; rewrite H0.
      iIntros "(d & H)"; iApply "H".
      iExists sh'; iSplit; eauto.
    - Intros; subst.
      rewrite (big_sepL_insert_acc _ _ (Z.to_nat b0)).
      2: { apply Znth_lookup. subst l0; rewrite H0 //. }
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try lia.
      if_tac; last done.
      Intros v1 ish v2.
      sep_apply data_at_buffer_cohere.
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join'; try eassumption.
        + setoid_rewrite Hshs; rewrite Zlength_sublist; rewrite ?Zlength_map ?Zlength_upto ?Z2Nat.id; lia.
        + setoid_rewrite Hshs; auto.
        + rewrite Zlength_sublist; rewrite ?Zlength_map ?Zlength_upto ?Z2Nat.id; lia. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      setoid_rewrite list_insert_upd; last by subst l0; rewrite H0.
      iIntros "(d & H)"; iApply "H".
      iExists sh'; iSplit; eauto. }
  f_equiv.
  match goal with |- Forall2 _ ?l _ => assert (Zlength l = B) as Hlen end.
  { destruct (eq_dec v' (-1)); auto; rewrite upd_Znth_Zlength H0 //. }
  rewrite Forall2_forall_Znth; split; first done.
  rewrite Hlen; intros j ?.
  assert (0 <= j <= B) by lia.
  erewrite Znth_map, Znth_upto; auto.
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec v' (-1)).
    + rewrite upd_Znth_same; [|lia].
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      exploit (make_shares_add lasti b0 (map (fun i => if eq_dec (Znth i h') Empty then b0
        else Znth i lasts) (upto (Z.to_nat N))) (Zlength h') shs); auto.
      { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto ?Z2Nat.id; try lia.
        rewrite Znth_overflow; [|lia].
        destruct (eq_dec Vundef Empty); [discriminate | auto]. }
      { setoid_rewrite Hshs; rewrite Zlength_map Zlength_upto Z2Nat.id; lia. }
      simpl; intros (shsa & shsb & Hshs1 & Hshs2).
      f_equiv; intros ?; f_equiv; f_equiv.
      rewrite Hshs1.
      erewrite make_shares_ext, Hshs2.
      * intros (? & Hj1 & Hj2).
        apply sepalg_list.list_join_comm.
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        econstructor. apply sepalg.join_comm; eassumption.
        apply sepalg_list.list_join_comm; auto.
      * rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
      * rewrite Zlength_map Zlength_upto; intros.
        rewrite -> Znth_map, Znth_upto; try lia; try assumption.
        destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
        -- rewrite -> app_Znth1, upd_Znth_diff; auto; try lia.
           erewrite Znth_map, Znth_upto; auto.
        -- subst; rewrite -> Znth_app1, eq_dec_refl, upd_Znth_same; auto; reflexivity.
        -- rewrite -> Znth_overflow, upd_Znth_diff; auto; [|rewrite Zlength_app Zlength_cons Zlength_nil; lia].
           erewrite Znth_map, Znth_upto; auto; try lia.
           rewrite -> Znth_overflow with (al := h'); [reflexivity | lia].
    + subst l0; rewrite -> 2upd_Znth_diff; auto; try lia.
      erewrite Znth_map, Znth_upto; try assumption.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map Zlength_upto; intros.
      erewrite Znth_map, Znth_map, !Znth_upto; auto; try lia.
      destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
      * rewrite app_Znth1; auto; lia.
      * subst; rewrite -> Znth_overflow, Znth_app1; auto.
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint v') Empty); [contradiction n | reflexivity].
        apply Empty_inj; auto; apply repable_buf; auto.
      * rewrite -> Znth_overflow, Znth_overflow with (al := h' ++ [vint v']); auto.
        rewrite Zlength_app Zlength_cons Zlength_nil; lia.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h') Empty then b0
      else Znth i lasts) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try lia.
      rewrite Zlength_map Zlength_upto Z2Nat.id; lia. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty
      then b0 else Znth i lasts) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try lia.
      rewrite Zlength_map Zlength_upto Z2Nat.id; lia. }
    simpl in *.
    destruct (eq_dec v' (-1)).
    + assert ((∃ sh : share, ⌜sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) b0)
          sh⌝ ∧ (∃ v1 : Z, data_at sh tbuffer (vint v1) (Znth b0 bufs))) ⊢
        ∃ sh : share, ⌜sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty then b0 else Znth i lasts)
          (upto (Z.to_nat N)))) b0) sh⌝ ∧ (∃ v0 : Z, data_at sh tbuffer (vint v0) (Znth b0 bufs))).
      { erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map, Znth_upto;
          auto; rewrite -> ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; try lia.
        rewrite Znth_app1; auto.
        subst; rewrite -> eq_dec_refl, make_shares_app; simpl.
        rewrite -> eq_dec_refl, app_nil_r.
        erewrite make_shares_ext; eauto; [lia|].
        rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map, Znth_map, !Znth_upto; auto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; lia).
        rewrite app_Znth1; [reflexivity | lia].
        { setoid_rewrite Hshs; rewrite -> Hlenh', Zlength_cons, Zlength_nil; lia. } }
      destruct (eq_dec lasti (-1)); subst l0; [rewrite upd_Znth_diff | rewrite -> 2upd_Znth_diff]; auto; try lia;
        erewrite Znth_map, Znth_upto; auto; if_tac; done.
    + rewrite upd_Znth_same; [|lia].
      erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map, Znth_upto;
        auto; rewrite -> ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; simpl; try (unfold N in *; lia).
      rewrite Znth_app1; auto.
      destruct (eq_dec (vint v') Empty).
      { contradiction n0; apply Empty_inj; auto; apply repable_buf; auto. }
      rewrite make_shares_app; simpl.
      destruct (eq_dec _ b0); [contradiction n; auto|].
      rewrite -> hd_Znth', Znth_sublist; rewrite ?Hlenh'; try setoid_rewrite Hshs; try lia.
      f_equiv; intros ?; f_equiv; f_equiv.
      erewrite make_shares_ext.
      * intros (? & Hj1 & Hj2).
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        apply sepalg_list.list_join_comm; econstructor; try eassumption. apply sepalg.join_comm; eauto.
      * lia.
      * rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map, Znth_map, !Znth_upto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; lia).
        rewrite app_Znth1; [reflexivity | lia].
      * rewrite Hlenh' Zlength_cons Zlength_nil; setoid_rewrite Hshs; lia.
  - transitivity (Znth j l0).
    { destruct (eq_dec v' (-1)); rewrite upd_Znth_diff; auto; lia. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
    + rewrite upd_Znth_diff; auto.
      erewrite Znth_map, Znth_upto; auto.
      destruct (eq_dec j b0); [contradiction n0; auto|].
      destruct (eq_dec j b); [contradiction n1; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite -> Zlength_map, Zlength_upto; intros.
      erewrite Znth_map, Znth_map, !Znth_upto; auto; try lia.
      destruct (zlt j0 (Zlength h')); [|destruct (eq_dec j0 (Zlength h'))].
      * rewrite app_Znth1; auto; lia.
      * subst; rewrite -> Znth_overflow, Znth_app1; auto.
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint v') Empty); [|reflexivity].
        split; intro; subst; tauto.
      * rewrite -> Znth_overflow, Znth_overflow with (al := h' ++ [vint v']); auto.
        rewrite Zlength_app Zlength_cons Zlength_nil; lia.
Qed.

Lemma big_sep_map : forall {B : bi} {A} (P Q : A -> B) (l : list A),
  [∗] map (fun a => P a ∗ Q a) l ⊣⊢ [∗] map P l ∗ [∗] map Q l.
Proof.
  induction l; simpl.
  - symmetry; apply bi.sep_emp.
  - rewrite IHl; iSplit; iIntros "H"; iStopProof; cancel.
Qed.

Lemma map_add_empty : forall (h : hist), (h : gmap.gmapR _ (exclR (leibnizO _))) ⋅ ∅ = h.
Proof.
  intros.
  apply (gmap.gmapO_leibniz(A := exclO (leibnizO _))); first apply _.
  apply right_id.
  apply (uora_unit_right_id(A := gmap.gmapUR nat (exclR (leibnizO AE_hist_el)))).
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function. simpl map.
  rewrite big_sep_map; Intros.
  forward.
  forward.
  assert (N < Int.max_signed) by computable.
  assert_PROP (Zlength (map (fun i => vint i) lasts) = N) by entailer!.
  rewrite -> Zlength_map in *.
  forward_for_simple_bound N (∃ i : Z, PROP ( )
   LOCAL (temp _w (vint b); temp _last (vint b0); gvars gv)
   SEP (data_at Ews tint (vint b) (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        ∃ t' : list nat, ∃ h' : list val, ⌜Zlength t' = i /\ Zlength h' = i /\ Forall2 newer (sublist 0 i h) t'⌝ ∧
          [∗] (map (fun r => comm_loc lsh (Znth r comms)
            (Znth r g) (Znth r g0) (Znth r g1) (Znth r g2) bufs (Znth r shs)
            ((Znth r h : gmap.gmapR _ (exclR (leibnizO _))) ⋅ (if zlt r i then {[Znth r t' := Excl (AE (Znth r h') (vint b))]} else ∅)))
            (upto (Z.to_nat N))) ∗
          let lasts' := map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts)
                            (upto (Z.to_nat N)) in
            data_at Ews (tarray tint N) (map (fun i => vint i) lasts') (gv _last_taken) ∗
            [∗] (map (fun r =>
              ghost_frag (vint (if zlt r i then b else b0)) (Znth r g1)) (upto (Z.to_nat N))) ∗
            [∗] (map (fun r =>
              ghost_frag (vint (@Znth Z (-1) r lasts')) (Znth r g2)) (upto (Z.to_nat N))) ∗
            [∗] (map (fun a => ∃ sh : share,
              ⌜if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (sublist 0 i lasts') a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (sublist i N shs) sh
                 else sepalg_list.list_join sh0 (make_shares shs lasts' a) sh⌝ ∧
              ∃ v : Z, data_at(cs := CompSpecs) sh tbuffer (vint v) (Znth a bufs)) (upto (Z.to_nat B))))).
  { Exists (@nil nat) (@nil val).
    replace (map (fun i => if eq_dec (Znth i []) Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))
      with lasts.
    rewrite sublist_nil; entailer!.
    f_equiv; f_equiv.
    { rewrite Forall2_forall_Znth; split; first done.
      intros ?; rewrite Zlength_map Zlength_upto.
      intros ?; rewrite -> !Znth_map, !Znth_upto by (unfold N; rewrite ?Zlength_upto; lia).
      destruct (zlt i 0); [lia | rewrite map_add_empty //]. }
    { f_equiv.
      rewrite Forall2_forall_Znth; split; first done.
      intros ?; rewrite Zlength_map Zlength_upto.
      intros ?; rewrite -> !Znth_map, !Znth_upto by (unfold N; rewrite ?Zlength_upto; lia).
      destruct (zlt i 0); [lia | done]. }
    f_equiv; first done.
    f_equiv.
    rewrite Forall2_forall_Znth; split; first done.
    intros ?; rewrite Zlength_map Zlength_upto.
    intros ?; rewrite -> !Znth_map, !Znth_upto by (unfold B, N; rewrite ?Zlength_upto; lia).
    f_equiv; intros ?; f_equiv; apply bi.pure_mono.
    destruct (eq_dec i b0); [|destruct (eq_dec i b); auto]; subst.
    - intros ->; constructor.
    - rewrite -> sublist_same, make_shares_out; auto; try reflexivity.
      replace (Zlength lasts) with N; auto.
    - rewrite {1}(list_Znth_eq lasts).
      replace (length lasts) with (Z.to_nat N).
      apply map_ext.
      intro; rewrite Znth_nil; destruct (eq_dec Vundef Empty); auto; discriminate.
      { rewrite -> Zlength_correct in *; rep_lia. } }
  - assert_PROP (Zlength comms = N) as Hcomms by entailer!.
    Intros t' h'.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Hcomms; auto. }
      apply Forall_impl with (P := isptr); auto. }
    lazymatch goal with |-context[[∗] map ?f (upto (Z.to_nat N))] =>
      gather_SEP ([∗] map f (upto (Z.to_nat N))); evar (P : mpred); replace_SEP 0 P end.
    { go_lowerx; rewrite bi.sep_emp; apply (big_sepL_insert_acc _ _ (Z.to_nat i)), Znth_lookup.
      rewrite Zlength_map Zlength_upto //. }
    subst P; rewrite Znth_map //.
    rewrite Znth_upto //.
    destruct (zlt i i); [lia | rewrite map_add_empty].
(*    rewrite comm_loc_isptr; Intros. *)
    lazymatch goal with |-context[[∗] map ?f (upto 5)] =>
      gather_SEP ([∗] map f (upto 5)); evar (P : mpred); replace_SEP 0 P end.
    { go_lowerx; rewrite bi.sep_emp; apply (big_sepL_insert_acc _ _ (Z.to_nat b)), Znth_lookup.
      rewrite Zlength_map Zlength_upto //. }
    subst P; simpl; rewrite Znth_map //.
    rewrite Znth_upto //.
    Intros bsh.
    destruct (eq_dec b b0); first done.
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    match goal with H : sepalg_list.list_join _ (sublist i N shs) _ |- _ =>
      rewrite -> sublist_split with (mid := i + 1) in H; try lia;
      apply sepalg_list.list_join_comm, sepalg_list.list_join_unapp in H; destruct H as (bsh' & ? & Hsh) end.
    rewrite -> sublist_len_1, <- sepalg_list.list_join_1 in Hsh; [|lia].
    repeat match goal with |-context[[∗] map ?f ?l] =>
      gather_SEP ([∗] map f l); evar (P : mpred); replace_SEP 0 P;
      [go_lowerx; rewrite bi.sep_emp; apply (big_sepL_insert_acc _ _ (Z.to_nat i)), Znth_lookup;
       rewrite Zlength_map Zlength_upto // | subst P; simpl; rewrite !Znth_map // !Znth_upto //] end.
    rewrite -> Znth_overflow with (al := h'); [|lia].
    destruct (zlt i i); [clear - l; lia|].
    destruct (eq_dec _ _); [discriminate|].
    forward_call AE_sub (lsh, Znth i comms, Znth i g, vint 0, vint b, Znth i h,
      fun (h : hist) (v : val) => ⌜v = vint b⌝ ∧
        ghost_frag (vint b0) (Znth i g1) ∗
        ghost_frag (vint (Znth i lasts)) (Znth i g2) ∗
        ∃ v : Z, data_at (Znth i shs) tbuffer (vint v) (Znth b bufs),
      comm_R bufs (Znth i shs) (Znth i g0) (Znth i g1) (Znth i g2),
        fun (h : hist) (v : val) => ∃ b' : Z, ⌜v = vint b' /\ -1 <= b' < B⌝ ∧
          ghost_frag (vint b) (Znth i g1) ∗
          ghost_frag (vint (if eq_dec b' (-1) then b0 else Znth i lasts)) (Znth i g2) ∗
          if eq_dec b' (-1) then ∃ v : Z, data_at (Znth i shs) tbuffer (vint v) (Znth (Znth i lasts) bufs)
          else ⌜b' = b0⌝ ∧ ∃ v' : Z, data_at (Znth i shs) tbuffer (vint v') (Znth b0 bufs)).
    { unfold comm_loc; cancel.
      rewrite bi.pure_True // bi.True_and; cancel.
      assert ((∃ v, data_at bsh tbuffer (vint v) (Znth b bufs)) ⊢
        (∃ v, data_at bsh' tbuffer (vint v) (Znth b bufs)) ∗ (∃ v, data_at (Znth i shs) tbuffer (vint v) (Znth b bufs))) as ->.
      { Intro v0; Exists v0 v0; rewrite (data_at_share_join _ _ _ _ _ _ Hsh); auto. }
      cancel.
      rewrite <- bi.emp_sep; apply bi.sep_mono; last cancel.
      unfold AE_spec.
      iIntros "_" (???? (? & ? & ?)) "(>comm & % & g1 & g2 & buf)".
      unfold comm_R.
      rewrite rev_app_distr /=.
      rewrite last_two_reads_cons prev_taken_cons.
      assert (repable_signed b) by (apply repable_buf; lia).
      destruct (eq_dec vc Empty).
      { subst; assert (b = -1) by (apply Empty_inj; auto); lia. }
      iDestruct "comm" as (b' b1 b2 (-> & ? & ? & Hlast & ? & ?)) "(a0 & a1 & a2 & buf')".
      iMod (ghost_var_update with "a1 g1") as "(%Hwrite & a1 & g1)".
      iMod (ghost_var_update with "a2 g2") as "(%Hprev & a2 & g2)".
      iIntros "!>". rewrite -bi.later_intro.
      rewrite bi.sep_exist_r; iExists b.
      rewrite bi.sep_exist_r; iExists b1.
      rewrite bi.sep_exist_r; iExists b2.
      iStopProof; entailer!.
      { rewrite Forall_app; repeat constructor; auto.
        exists b', b; split; [|split]; auto; lia. }
      destruct (eq_dec b (-1)); [lia|].
      Exists b'.
      rewrite -bi.sep_exist_l -bi.sep_exist_r; ecancel.
      rewrite bi.pure_True // bi.True_and.
      erewrite take_read, Hlast in *; try (rewrite rev_involutive; eauto).
      unfold last_write in *; simpl in *.
      subst; rewrite -> (if_false (vint b = Empty)) by auto.
      assert (Znth (Zlength t') lasts = if eq_dec (vint b') Empty then b2 else b1).
      { assert (repable_signed (Znth (Zlength t') lasts)).
        { apply Forall_Znth; [lia|].
          eapply Forall_impl; [|eauto]; intros.
          apply repable_buf; simpl in *; lia. }
        if_tac; apply repr_inj_signed; auto; congruence. }
      destruct (eq_dec (vint b') Empty); subst; simpl; cancel.
      + assert (b' = -1) as -> by (apply Empty_inj; auto; apply repable_buf; auto).
        destruct (eq_dec _ _); last done.
        exploit find_write_read.
        { rewrite -> rev_involutive; eauto. }
        { discriminate. }
        intros ->; rewrite Hwrite; cancel.
      + assert (exists rest, find_write (rev hx) (vint 0) = (vint b', rest)) as (? & Hwrite').
        { assert (apply_hist (vint 0) hx = Some (vint b')) as Hvx by assumption.
          replace hx with (rev (rev hx)) in Hvx by (apply rev_involutive).
          destruct (rev hx); simpl in *.
          { assert (b' = 0); [|subst; eauto].
            apply repr_inj_signed.
            * apply repable_buf; auto.
            * split; computable.
            * congruence. }
          destruct a.
          rewrite apply_hist_app in Hvx.
          destruct (apply_hist (vint 0) (rev l)); [simpl in * | discriminate].
          destruct (eq_dec r v); [|discriminate].
          inv Hvx.
          destruct (eq_dec (vint b') Empty); [done | eauto]. }
        rewrite Hwrite' in Hwrite.
        assert (b' = b0) as ->.
        { apply repr_inj_signed; [apply repable_buf | apply repable_buf | simpl in *; congruence]; auto; lia. }
        destruct (eq_dec b0 (-1)); [subst; contradiction n3; auto|].
        unfold last_two_reads in Hlast; destruct (find_read (rev hx) (vint 1)); inv Hlast.
        simpl; entailer!. }
    Intros x b'; destruct x as (t, v); simpl in *.
    gather_SEP 0 8; replace_SEP 0 ([∗] (map (fun r =>
      comm_loc lsh (Znth r comms) (Znth r g) (Znth r g0)
        (Znth r g1) (Znth r g2) bufs (Znth r shs) ((Znth r h : gmap.gmapR _ (exclR (leibnizO _))) ⋅
        (if zlt r (i + 1) then {[Znth r (t' ++ [t]) := Excl (AE (Znth r (h' ++ [v])) (vint b))]} else ∅)))
      (upto (Z.to_nat N)))).
    { go_lower.
      iIntros "(a & H)"; iSpecialize ("H" with "a").
      rewrite list_insert_upd //.
      iApply (big_sepL_id_mono' with "H").
      rewrite Forall2_forall_Znth; rewrite Zlength_upd_Znth Zlength_map Zlength_upto; split; first done.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite -> upd_Znth_same by (rewrite -> Zlength_map, Zlength_upto; auto).
        rewrite -> (@Znth_map _ N), Znth_upto by (auto; lia).
        destruct (zlt (Zlength t') (Zlength t' + 1)); [|lia].
        rewrite -> !app_Znth2 by lia.
        rewrite Zminus_diag; replace (Zlength t') with (Zlength h'); rewrite -> Zminus_diag, !Znth_0_cons; auto.
        rewrite /comm_loc; f_equiv.
        apply (leibniz_equiv(A := gmap.gmapR _ (exclR (leibnizO _)))).
        rewrite ora_comm.
        intros i; rewrite gmap.lookup_op.
        destruct (eq_dec i t); [subst; rewrite lookup_insert lookup_singleton | rewrite lookup_insert_ne // lookup_singleton_ne // left_id //].
        rewrite newer_out //.
        replace (Zlength h') with (Zlength t'); auto.
      + rewrite -> upd_Znth_diff' by (rewrite -> ?Zlength_map, ?Zlength_upto; auto).
        rewrite -> !(@Znth_map _ N), !Znth_upto by (auto; lia).
        rewrite /comm_loc; f_equiv.
        if_tac; if_tac; rewrite ?map_add_empty; try lia; try done.
        rewrite -> !app_Znth1 by lia; done. }
    gather_SEP 1 5; replace_SEP 0 ([∗] (map (fun r =>
      ghost_frag (vint (if zlt r (i + 1) then b else b0)) (Znth r g1)) (upto (Z.to_nat N)))).
    { go_lower.
      iIntros "(a & H)"; iSpecialize ("H" with "a").
      rewrite list_insert_upd //.
      iApply (big_sepL_id_mono' with "H").
      rewrite Forall2_forall_Znth; rewrite Zlength_upd_Znth Zlength_map Zlength_upto; split; first done.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite upd_Znth_same // Znth_map // Znth_upto //.
        if_tac; [done | lia].
      + rewrite upd_Znth_diff' // !Znth_map // Znth_upto //.
        if_tac; if_tac; try done; lia. }
    gather_SEP 2 4; replace_SEP 0 ([∗] (map (fun r =>
      ghost_frag (vint (Znth r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [v])) Empty then b0
        else Znth i0 lasts) (upto (Z.to_nat N))))) (Znth r g2)) (upto (Z.to_nat N)))).
    { go_lower.
      iIntros "(a & H)"; iSpecialize ("H" with "a").
      rewrite list_insert_upd //.
      iApply (big_sepL_id_mono' with "H").
      rewrite Forall2_forall_Znth; rewrite Zlength_upd_Znth Zlength_map Zlength_upto; split; first done.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite upd_Znth_same // !Znth_map // !Znth_upto //.
        rewrite app_Znth2; last lia.
        replace (Zlength t') with (Zlength h'); rewrite Zminus_diag Znth_0_cons //.
        destruct (eq_dec (vint b') Empty), (eq_dec b' (-1)); auto; subst.
        * contradiction n1; apply Empty_inj; auto; apply repable_buf; auto.
        * contradiction n1; auto.
      + rewrite upd_Znth_diff' // !Znth_map // !Znth_upto //.
        destruct (zlt j (Zlength h')).
        * rewrite app_Znth1; auto.
        * rewrite -> Znth_overflow with (al := h'), Znth_overflow with (al := (h' ++ [vint b'])); auto.
          rewrite -> Zlength_app, Zlength_cons, Zlength_nil; lia. }
    assert (repable_signed b') by (apply repable_buf; auto); subst v.
    gather_SEP (data_at _ _ _ (gv _last_taken)).
    match goal with |- semax _ _ (PROP () (LOCALx ?Q (SEPx (data_at _ _ ?l (gv _last_taken) :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (data_at Ews (tarray tint N)
        (upd_Znth i l (vint (if eq_dec (vint b') Empty then b0 else Znth i lasts))) (gv _last_taken) :: R)))) end.
    + forward.
      subst. rewrite -> (if_true (vint b' = Empty)) by (rewrite H18; reflexivity).
      apply ENTAIL_refl.
    + forward. rewrite neg_repr in H18.
      rename H18 into n1.
      erewrite (upd_Znth_triv i).
      apply ENTAIL_refl.
      * rewrite !Zlength_map Zlength_upto; auto.
      * rewrite -> !Znth_map, Znth_upto; [|done..].
        rewrite -> Znth_overflow by lia.
        if_tac; first done; if_tac; auto.
        contradict n1; apply Vint_inj; done.
    + subst.
      Exists (t' ++ [t]) (h' ++ [vint b']).
      entailer!.
      { rewrite !Zlength_app !Zlength_cons !Zlength_nil; split3; [lia..|].
        replace (Zlength t') with (Zlength h') in *.
        rewrite -> sublist_split with (mid := Zlength h') by lia.
        rewrite -> (sublist_one (Zlength h')) by (auto; lia).
        apply Forall2_app; auto. }
      rewrite -!bi.sep_exist_l -bi.sep_exist_r.
      apply bi.sep_mono.
      * f_equiv.
        erewrite upd_Znth_eq, !map_length, upto_length, !map_map;
          [|rewrite -> !Zlength_map, Zlength_upto; unfold N in *; auto].
        apply map_ext_in; intros; rewrite -> In_upto in *.
        replace (Zlength t') with (Zlength h').
        destruct (Z.eq_dec a (Zlength h')).
        -- subst; rewrite -> app_Znth2, Zminus_diag, Znth_0_cons; auto; clear; lia.
        -- rewrite -> !Znth_map, Znth_upto; try lia; try assumption.
           destruct (zlt a (Zlength t')); [rewrite app_Znth1 | rewrite Znth_overflow]; auto; try lia.
           rewrite -> Znth_overflow with (al := _ ++ _); auto.
           rewrite -> Zlength_app, Zlength_cons, Zlength_nil; lia.
      * iIntros "($ & ? & ? & H)".
        iSpecialize ("H" $! emp with "[]"); first done.
        rewrite list_insert_upd //.
        replace (Zlength t') with (Zlength h') in *; iApply (upd_write_shares with "[$]").
  - Intros t' h'.
    forward.
    forward.
    rewrite -> sublist_nil, sublist_same; rewrite ?Zlength_map; auto.
    Exists (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))
      (map (fun '(h, (t, v)) => <[t := Excl (AE v (vint b))]>h) (combine h (combine t' h'))); entailer!.
    + repeat split.
      * rewrite Forall_map Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h') Empty); [lia|].
        rewrite -> In_upto, Z2Nat.id in *; unfold N; try lia.
        apply Forall_Znth; [lia | auto].
      * assert (Zlength h' = Zlength h) as Hlen by lia; assert (Zlength t' = Zlength h') as Hlen' by lia;
        clear - Hlen Hlen'; generalize dependent h; generalize dependent t'; induction h';
          destruct h, t'; rewrite -> ?Zlength_nil, ?Zlength_cons in *; simpl; intros; auto;
          try (rewrite -> Zlength_correct in *; lia).
        constructor; eauto.
        apply IHh'; lia.
      * rewrite in_map_iff; intros (i & ? & ?); subst.
        rewrite -> In_upto, Z2Nat.id in *; try (unfold N; lia).
        destruct (eq_dec (Znth i h') Empty); first done.
        match goal with H : ~In _ lasts |- _ => contradiction H; apply Znth_In; lia end.
    + rewrite big_sep_map; iIntros "(Hcomm & $ & $ & Hbufs)".
      iSplitL "Hcomm".
      * erewrite map_ext_in; eauto; intros; simpl.
        rewrite -> In_upto in *.
        destruct (zlt a N); [|unfold N in *; simpl in *; lia].
        f_equal.
        rewrite -> Znth_map, !Znth_combine by
          (rewrite ?Zlength_combine; rewrite ?Z.min_l; rewrite ?Z.min_l; auto; lia); auto.
        apply (leibniz_equiv(A := gmap.gmapR _ (exclR (leibnizO _)))).
        rewrite ora_comm.
        intros i; rewrite gmap.lookup_op.
        destruct (eq_dec i (Znth a t')); [subst; rewrite lookup_singleton lookup_insert | rewrite lookup_singleton_ne // lookup_insert_ne // left_id //].
        rewrite newer_out //.
        apply Forall2_Znth; auto; last lia.
        erewrite <- (sublist_same_gen _ _ h); first done; lia.
      * iApply (big_sepL_id_mono' with "Hbufs").
        rewrite Forall2_forall_Znth; rewrite Zlength_map Zlength_upto; split; first done.
        intros j ?; rewrite !Znth_map // Znth_upto //.
        do 4 f_equiv.
        destruct (eq_dec j b); if_tac; subst; try done.
        inversion 1; done.
Qed.

End mpred.
