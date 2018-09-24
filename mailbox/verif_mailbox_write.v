Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Set Bullet Behavior "Strict Subproofs".

Opaque upto.

Lemma body_initialize_writer : semax_body Vprog Gprog f_initialize_writer initialize_writer_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvars gv)
   SEP (field_at Ews tint [] (eval_unop Oneg tint (vint 1)) (gv _writing); field_at Ews tint [] (vint 0) (gv _last_given);
        data_at Ews (tarray tint N) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) (gv _last_taken))).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - forward.
    rewrite upd_init_const; auto.
  - forward.
Qed.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint B) v_available; gvars gv)
   SEP (data_at Tsh (tarray tint B) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) v_available;
        data_at_ Ews tint (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
  { unfold B, N; computable. }
  { entailer!. }
  { forward.
    rewrite upd_init_const; auto; entailer!. }
  rewrite Zminus_diag, app_nil_r.
  forward.
  forward.
  rewrite <- seq_assoc.
  assert_PROP (Zlength lasts = N).
  { gather_SEP 3.
    go_lowerx.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    apply prop_left; intros (? & ? & ?).
    unfold unfold_reptype in *; simpl in *.
    rewrite Zlength_map in *; apply prop_right; auto. }
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _i (vint B); lvar _available (tarray tint B) v_available; gvars gv)
   SEP (data_at Tsh (tarray tint B) (map (fun x => vint (if eq_dec x b0 then 0
     else if in_dec eq_dec x (sublist 0 i lasts) then 0 else 1)) (upto (Z.to_nat B))) v_available;
   data_at_ Ews tint (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
   data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
  { unfold N; computable. }
  { entailer!.
    rewrite upd_Znth_eq; simpl; [|rewrite !Zlength_cons, Zlength_nil; unfold B, N in *; omega].
    unfold Znth; simpl.
    apply derives_refl'; f_equal.
    apply map_ext_in; intros ? Hin.
    rewrite In_upto in Hin.
    destruct (eq_dec a b0); auto.
    destruct (zlt a 0); [omega|].
    destruct Hin as (? & Hin); apply Z2Nat.inj_lt in Hin; auto; try omega.
    simpl in *; destruct (Z.to_nat a); auto.
    repeat (destruct n0; [solve [auto]|]).
    omega. }
  { assert (0 <= i < Zlength lasts) by omega.
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
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      erewrite Znth_map, Znth_upto; simpl; auto; try omega.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1; auto; try omega.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts])); rewrite in_app in *.
      + destruct (eq_dec a (Znth i lasts)); destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
      + destruct (eq_dec a (Znth i lasts)).
        { subst; contradiction n; simpl; auto. }
        destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto; contradiction n; auto.
    - forward.
      entailer!.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto in *; simpl in *.
      destruct (eq_dec a b0); auto.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1; auto; try omega.
(*      match goal with H : Int.repr _ = Int.neg _ |- _ => apply repr_inj_signed in H end. *)
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts])); rewrite in_app in *.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        apply repr_inj_signed in H4; rep_omega.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        contradiction n0; auto.
    - intros. entailer!. }
  rewrite sublist_same; auto.
  set (available := map (fun x => vint (if eq_dec x b0 then 0 else if in_dec eq_dec x lasts then 0 else 1))
         (upto (Z.to_nat B))).
  rewrite <- seq_assoc.
  unfold Sfor.
  forward.
  eapply semax_seq, semax_ff.
  eapply semax_pre with (P' := EX i : Z, PROP (0 <= i <= B; forall j, 0 <= j < i -> Znth j available = vint 0)
    LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) v_available; gvars gv)
    SEP (field_at Tsh (tarray tint 5) [] available v_available; data_at_ Ews tint (gv _writing);
         data_at Ews tint (vint b0) (gv _last_given); data_at Ews (tarray tint N) (map (fun x => vint x) lasts) (gv _last_taken))).
  { Exists 0; entailer!.
    intros. omega. }
  eapply semax_loop.
  + Intros i.
    assert (repable_signed i).
    { split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try omega. }
    forward_if (PROP (i < B)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) v_available; gvars gv)
      SEP (field_at Tsh (tarray tint 5) [] available v_available; data_at_ Ews tint (gv _writing);
           data_at Ews tint (vint b0) (gv _last_given);
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
    { forward.
      entailer!. }
    { forward.
      exploit (list_pigeonhole (b0 :: lasts) B).
      { rewrite Zlength_cons; unfold B; omega. }
      intros (j & ? & Hout); exploit (H3 j); [unfold B, N in *; omega|].
      subst available.
      rewrite Znth_map; [|rewrite Zlength_upto; auto].
      rewrite Znth_upto; [|rewrite Z2Nat.id; omega].
      destruct (eq_dec j b0); [contradiction Hout; simpl; auto|].
      destruct (in_dec eq_dec j lasts); [contradiction Hout; simpl; auto|].
      discriminate. }
    Intros.
    forward.
    { unfold B, N in *; apply prop_right; omega. }
    { entailer!.
      subst available; apply Forall_Znth; [rewrite Zlength_map, Zlength_upto; unfold B, N in *; simpl; omega|].
      rewrite Forall_forall; intros ? Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); subst; simpl; auto. }
    forward_if (PROP (Znth i available = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) v_available; gvars gv)
      SEP (field_at Tsh (tarray tint B) [] available v_available; data_at_ Ews tint (gv _writing);
           data_at Ews tint (vint b0) (gv _last_given); data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) (gv _last_taken))).
    { forward.
      forward.
      Exists i; entailer!.
      { subst available.
        match goal with H : typed_true _ _ |- _ => setoid_rewrite Znth_map in H; [rewrite Znth_upto in H|];
          try assumption; rewrite ?Zlength_upto, ?Z2Nat.id; try omega; unfold typed_true in H; simpl in H; inv H end.
        destruct (eq_dec i b0); [|destruct (in_dec eq_dec i lasts)]; auto; discriminate. }
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try assumption; try omega.
      match goal with H : typed_false _ _ |- _ => setoid_rewrite Znth_map in H; [rewrite Znth_upto in H|];
        try assumption; rewrite ?Zlength_upto, ?Z2Nat.id; try omega; unfold typed_true in H; simpl in H; inv H end.
      destruct (eq_dec _ _); auto.
      destruct (in_dec _ _ _); auto; discriminate. }
    instantiate (1 := EX i : Z, PROP (0 <= i < B; Znth i available = vint 0;
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
    assert (0<= j < i) by omega; auto.
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
  - destruct (find_write_rest (vint 0) h) as (? & Hrest); rewrite Hrest in *.
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
  rewrite !eq_dec_refl.
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
  - destruct a; rewrite prev_taken_cons, last_two_reads_cons.
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
  - rewrite Zlength_cons in *.
    destruct shs.
    { rewrite Zlength_nil, !Zlength_correct in *; omega. }
    rewrite Zlength_cons in *; simpl; rewrite IHl1; [|omega].
    rewrite sublist_S_cons with (i0 := Z.succ _); [|rewrite Zlength_correct; omega].
    unfold Z.succ; rewrite !Z.add_simpl_r.
    destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_ext : forall i l l' shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j l = i <-> Znth j l' = i),
  make_shares shs l i = make_shares shs l' i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  exploit (Hi 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro Hiff.
  rewrite (IHl l'); try omega.
  - destruct (eq_dec a i), (eq_dec z i); tauto.
  - intros; exploit (Hi (j + 1)); [omega|].
    rewrite !Znth_pos_cons, !Z.add_simpl_r; auto; omega.
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
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *;
    try (rewrite Zlength_correct in *; omega).
  - inv Hsh1; inv Hsh'; constructor.
  - inversion Hsh' as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (x & ? & Hx).
      exploit IHlasts; eauto; [omega|].
      intro Hj'; destruct (sepalg_list.list_join_assoc2 Hj' Hx) as (? & ? & ?).
      econstructor; eauto.
    + inversion Hsh1 as [|????? Hja]; inversion Hsh' as [|????? Hjb]; subst.
      pose proof (sepalg.join_eq Hja Hjb); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_add : forall i i' lasts j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts = i) (Hi' : i' <> i) (Hlen : Zlength shs >= Zlength lasts),
  exists shs1 shs2, make_shares shs lasts i = shs1 ++ shs2 /\
    make_shares shs (upd_Znth j lasts i') i = shs1 ++ Znth j shs :: shs2.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in Hi', IHlasts; rewrite !Znth_0_cons.
    rewrite eq_dec_refl, upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega; simpl.
    destruct (eq_dec i' a); [contradiction Hi'; auto|].
    eexists [], _; simpl; split; eauto.
  - rewrite Znth_pos_cons in Hi; [|omega].
    rewrite Znth_pos_cons; [|omega].
    exploit (IHlasts (j - 1) shs); try omega.
    intros (shs1 & shs2 & Heq1 & Heq2).
    rewrite upd_Znth_cons; [simpl | omega].
    exists (if eq_dec a i then shs1 else t :: shs1), shs2; rewrite Heq1, Heq2; destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts <> i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs)  (make_shares shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in Hi; rewrite Znth_0_cons.
      destruct (eq_dec a i); [contradiction Hi | simpl]; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts (x - 1) shs); eauto; try omega.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma make_shares_inv_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts = i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs) (make_shares_inv shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in *; rewrite Znth_0_cons; subst.
      rewrite eq_dec_refl; simpl; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts (x - 1) shs); eauto; try omega.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma make_shares_sub : forall i lasts shs sh0 sh1 sh2 (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1) (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2),
  sepalg.join_sub sh2 sh1.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega).
  - inv Hsh1; inv Hsh2; apply sepalg.join_sub_refl.
  - inversion Hsh1 as [|????? Hj1 Hj2]; inv Hsh2.
    destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?); eexists; eauto.
  - inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      exploit IHlasts; eauto; [omega|].
      intro; eapply sepalg.join_sub_trans; eauto; eexists; eauto.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_join : forall i lasts shs sh0 j sh1 sh2
  (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1)
  (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2)
  (Hin : 0 <= j < Zlength shs)
  (Hj : Znth j lasts = i),
  exists sh', sepalg.join sh2 (Znth j shs) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega); try omega.
  { rewrite Znth_overflow in Hj; [|rewrite Zlength_nil; omega].
    inv Hsh2.
    exploit (Znth_In j (t :: shs)); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  - subst j; rewrite Znth_0_cons in Hj; rewrite Znth_0_cons; subst.
    rewrite eq_dec_refl in Hsh2.
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    exploit make_shares_sub; eauto; [omega|].
    intro; eapply sepalg.join_sub_joins_trans; eauto.
  - rewrite Znth_pos_cons in Hj; [|omega].
    rewrite Znth_pos_cons; [|omega].
    inversion Hsh1 as [|????? Hj1 Hj2].
    destruct (eq_dec a i); subst.
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      eapply IHlasts; eauto; omega.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_join' : forall i lasts shs sh0 j sh1 sh2
  (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1)
  (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2)
  (Hin : 0 <= j < Zlength shs) (Hout : Zlength lasts <= j),
  exists sh', sepalg.join sh2 (Znth j shs) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega); try omega.
  { inv Hsh2.
    exploit (Znth_In j (t :: shs)); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  { subst; rep_omega. }
  rewrite Znth_pos_cons; [|omega].
  inversion Hsh1 as [|????? Hj1 Hj2].
  destruct (eq_dec a i); subst.
  + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    eapply IHlasts; eauto; omega.
  + inversion Hsh2 as [|????? Hj1']; subst.
    pose proof (sepalg.join_eq Hj1 Hj1'); subst.
    eapply IHlasts; eauto; omega.
Qed.

Lemma data_at_buffer_cohere : forall sh1 sh2 v1 v2 p, readable_share sh1 ->
  data_at sh1 tbuffer v1 p * data_at sh2 tbuffer v2 p |--
  data_at sh1 tbuffer v1 p * data_at sh2 tbuffer v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !data_at_rec_eq; unfold withspacer, at_offset; simpl.
  rewrite !data_at_rec_eq; simpl.
  apply mapsto_value_cohere; auto.
Qed.

Lemma hd_Znth': forall {A} (d: A) al, hd d al = @Znth A d 0 al.
Proof.
intros. destruct al; reflexivity.
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
   EX v0 : Z, data_at (Znth (Zlength h') shs) tbuffer (vint v0) (Znth (Znth (Zlength h') lasts) bufs)
   else !! (v' = b0) && (EX v'0 : Z, data_at (Znth (Zlength h') shs) tbuffer (vint v'0) (Znth b0 bufs))) *
  ((EX v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs)) *
  fold_right sepcon emp (upd_Znth b (map (fun a => EX sh : share, !! (if eq_dec a b0 then
    sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
      (map (fun i : Z => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) a) sh
      else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
      else sepalg_list.list_join sh0 (make_shares shs
      (map (fun i : Z => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N))) a) sh) &&
      (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs))) (upto (Z.to_nat B))) emp))
  |-- fold_right sepcon emp (map (fun a => EX sh : share, !! (if eq_dec a b0 then
        sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) a) sh
          else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) sh
          else sepalg_list.list_join sh0 (make_shares shs
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty then b0 else Znth i lasts) (upto (Z.to_nat N))) a) sh) &&
          (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs))) (upto (Z.to_nat B))).
Proof.
  intros; set (shi := Znth (Zlength h') shs).
  assert (readable_share shi).
  { apply Forall_Znth; auto; omega. }
  set (lasti := Znth (Zlength h') lasts).
  exploit (Znth_In (Zlength h') lasts); [omega | intro Hini].
  assert (lasti <> b) as Hneq.
  { intro; match goal with H : ~In b lasts |- _ => contradiction H end; subst b lasti; auto. }
  assert (lasti <> b0) as Hneq0.
  { intro; match goal with H : ~In b0 lasts |- _ => contradiction H end; subst b0 lasti; auto. }
  set (l0 := upd_Znth b (map (fun a => EX sh : share, !!(if eq_dec a b0 then
             sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
               (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) a) sh
           else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
           else sepalg_list.list_join sh0 (make_shares shs (map (fun i => if eq_dec (Znth i h') Empty then b0
                                           else Znth i lasts) (upto (Z.to_nat N))) a) sh) &&
          (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth a bufs))) (upto (Z.to_nat B)))
          (EX v1 : Z, @data_at CompSpecs bsh' tbuffer (vint v1) (Znth b bufs))).
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto; auto. }
  assert (0 <= lasti < B).
  { apply Forall_Znth; auto; omega. }
  apply derives_trans with (fold_right sepcon emp (
    if eq_dec v' (-1) then upd_Znth lasti l0
            (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
             (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N))) lasti) sh' /\
             sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth lasti bufs)))
          else upd_Znth b0 l0 (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
            (sublist 0 (Zlength h') (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts)
            (upto (Z.to_nat N)))) b0) sh' /\ sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth b0 bufs))))).
  { rewrite replace_nth_sepcon.
    destruct (eq_dec v' (-1)).
    - rewrite extract_nth_sepcon with (i := lasti); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros v1 ish v2.
      rewrite <- sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_buffer_cohere; auto | apply derives_refl]|].
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join; eauto.
        + setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_map by (rewrite Zlength_upto, Z2Nat.id; omega).
            rewrite Znth_upto by (rewrite ?Z2Nat.id; omega).
            rewrite Znth_overflow; auto; omega. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      rewrite (extract_nth_sepcon (upd_Znth lasti l0 (EX sh : share, _)) lasti); [|rewrite upd_Znth_Zlength; omega].
      rewrite upd_Znth_twice; [|omega].
      apply sepcon_derives; [|apply derives_refl].
      rewrite upd_Znth_same; [|omega].
      Exists sh'; apply andp_right; [|Exists v1; auto].
      apply prop_right; eauto.
    - Intros; subst.
      rewrite extract_nth_sepcon with (i := b0); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec b0 b0); [|contradiction n0; auto]. clear e.
      Intros v1 ish v2.
      rewrite <- sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_buffer_cohere; auto | apply derives_refl]|].
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join'; try eassumption.
        + setoid_rewrite Hshs; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      rewrite (extract_nth_sepcon (upd_Znth b0 l0 (EX sh : share, _)) b0); [|rewrite upd_Znth_Zlength; omega].
      rewrite upd_Znth_twice; [|omega].
      apply sepcon_derives; [|apply derives_refl].
      rewrite upd_Znth_same; [|omega].
      Exists sh'; apply andp_right; [|Exists v1; auto].
      apply prop_right; eauto. }
  apply derives_refl'; f_equal.
  match goal with |- ?l = _ => assert (Zlength l = B) as Hlen end.
  { destruct (eq_dec v' (-1)); auto; rewrite upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq'.
  { rewrite Hlen, Zlength_map, Zlength_upto; auto. }
  rewrite Hlen; intros.
  assert (0 <= j <= B) by omega.
  erewrite Znth_map, Znth_upto; auto.
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec v' (-1)).
    + rewrite upd_Znth_same; [|omega].
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      exploit (make_shares_add lasti b0 (map (fun i => if eq_dec (Znth i h') Empty then b0
        else Znth i lasts) (upto (Z.to_nat N))) (Zlength h') shs); auto.
      { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec Vundef Empty); [discriminate | auto]. }
      { setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
      simpl; intros (shsa & shsb & Hshs1 & Hshs2).
      f_equal; extensionality; f_equal; f_equal.
      rewrite Hshs1.
      erewrite make_shares_ext, Hshs2.
      apply prop_ext; split.
      * intros (? & Hj1 & Hj2).
        apply list_join_comm.
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        econstructor; eauto.
        apply list_join_comm; auto.
      * intro Hj; apply list_join_comm in Hj.
        inversion Hj as [|????? Hj1 Hj2]; subst.
        apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
        do 2 eexists; eauto; apply list_join_comm; auto.
      * rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
      * rewrite Zlength_map, Zlength_upto; intros.
        rewrite Znth_map, Znth_upto; try omega; try assumption.
        destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
        -- rewrite app_Znth1, upd_Znth_diff; auto; try omega.
           erewrite Znth_map, Znth_upto; auto. reflexivity.
        -- subst; rewrite Znth_app1, eq_dec_refl, upd_Znth_same; auto; reflexivity.
        -- rewrite Znth_overflow, upd_Znth_diff; auto; [|rewrite Zlength_app, Zlength_cons, Zlength_nil; omega].
           erewrite Znth_map, Znth_upto; auto; try omega.
           rewrite Znth_overflow with (al := h'); [reflexivity | omega].
    + subst l0; rewrite 2upd_Znth_diff; auto; try omega.
      erewrite Znth_map, Znth_upto; try assumption.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map, Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
      * rewrite app_Znth1; auto; omega.
      * subst; rewrite Znth_overflow, Znth_app1; auto.
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint v') Empty); [contradiction n | reflexivity].
        apply Empty_inj; auto; apply repable_buf; auto.
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [vint v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h') Empty then b0
      else Znth i lasts) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty
      then b0 else Znth i lasts) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    simpl in *.
    destruct (eq_dec v' (-1)).
    + assert (EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))) b0)
          sh && (EX v1 : Z, data_at sh tbuffer (vint v1) (Znth b0 bufs)) =
        EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v'])) Empty then b0 else Znth i lasts)
          (upto (Z.to_nat N)))) b0) sh && (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth b0 bufs))).
      { erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map, Znth_upto;
          auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_app1; auto.
        subst; rewrite eq_dec_refl, make_shares_app; simpl.
        rewrite eq_dec_refl, app_nil_r.
        erewrite make_shares_ext; eauto; [omega|].
        rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map, Znth_map, !Znth_upto; auto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
        { setoid_rewrite Hshs; rewrite Hlenh', Zlength_cons, Zlength_nil; omega. } }
      destruct (eq_dec lasti (-1)); subst l0; [rewrite upd_Znth_diff | rewrite 2upd_Znth_diff]; auto; try omega;
        erewrite Znth_map, Znth_upto; auto; destruct (eq_dec b0 b0); auto; absurd (b0 = b0); auto.
    + rewrite upd_Znth_same; [|omega].
      erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map, Znth_upto;
        auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; simpl; try (unfold N in *; omega).
      rewrite Znth_app1; auto.
      destruct (eq_dec (vint v') Empty).
      { contradiction n0; apply Empty_inj; auto; apply repable_buf; auto. }
      rewrite make_shares_app; simpl.
      destruct (eq_dec _ b0); [contradiction n; auto|].
      rewrite hd_Znth', Znth_sublist; rewrite ?Hlenh'; try setoid_rewrite Hshs; try omega.
      f_equal; extensionality; f_equal; f_equal.
      erewrite make_shares_ext.
      apply prop_ext; split.
      * intros (? & Hj1 & Hj2).
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        apply list_join_comm; econstructor; eauto.
      * intro Hj; apply list_join_comm in Hj; inversion Hj as [|????? Hj1 Hj2]; subst.
        apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
        do 2 eexists; eauto.
      * omega.
      * rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map, Znth_map, !Znth_upto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
      * rewrite Hlenh', Zlength_cons, Zlength_nil; setoid_rewrite Hshs; omega.
  - transitivity (Znth j l0).
    { destruct (eq_dec v' (-1)); rewrite upd_Znth_diff; auto; omega. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
      apply pred_ext.
      * Exists bsh'; entailer!.
      * Intros sh.
        assert (sh = bsh') by (eapply list_join_eq; eauto; apply HshP).
        subst; auto.
    + rewrite upd_Znth_diff; auto.
      erewrite Znth_map, Znth_upto; auto.
      destruct (eq_dec j b0); [contradiction n0; auto|].
      destruct (eq_dec j b); [contradiction n1; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map, Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j0 (Zlength h')); [|destruct (eq_dec j0 (Zlength h'))].
      * rewrite app_Znth1; auto; omega.
      * subst; rewrite Znth_overflow, Znth_app1; auto.
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint v') Empty); [|reflexivity].
        split; intro; subst; tauto.
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [vint v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  rewrite sepcon_map; Intros.
  forward.
  forward.
  assert_PROP (Zlength (map (fun i => vint i) lasts) = N) by entailer!.
  rewrite Zlength_map in *.
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _w (vint b); temp _last (vint b0); gvars gv)
   SEP (data_at Ews tint (vint b) (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm); data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        EX t' : list nat, EX h' : list val, !!(Zlength t' = i /\ Zlength h' = i /\ Forall2 newer (sublist 0 i h) t') &&
          fold_right sepcon emp (map (fun r => comm_loc lsh (Znth r locks) (Znth r comms)
            (Znth r g) (Znth r g0) (Znth r g1) (Znth r g2) bufs (Znth r shs)
            gsh2 (map_add (Znth r h) (if zlt r i then singleton (Znth r t') (AE (Znth r h') (vint b)) else empty_map)))
            (upto (Z.to_nat N))) *
          let lasts' := map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts)
                            (upto (Z.to_nat N)) in
            data_at Ews (tarray tint N) (map (fun i => vint i) lasts') (gv _last_taken) *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 (vint (if zlt r i then b else b0)) (Znth r g1)) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 (vint (@Znth Z (-1) r lasts')) (Znth r g2)) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun a => EX sh : share,
              !!(if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (sublist 0 i lasts') a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (sublist i N shs) sh
                 else sepalg_list.list_join sh0 (make_shares shs lasts' a) sh) &&
              EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth a bufs)) (upto (Z.to_nat B))))).
  { unfold N; computable. }
  { Exists (@nil nat) (@nil val).
    replace (map (fun i => if eq_dec (Znth i []) Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))
      with lasts.
    rewrite sublist_nil; entailer!.
    apply derives_refl'; f_equal; f_equal.
    { f_equal.
      apply map_ext_in.
      intros; rewrite In_upto in *.
      destruct (zlt a 0); [omega | rewrite map_add_empty; auto]. }
    apply map_ext; intro.
    f_equal; extensionality; f_equal; f_equal.
    apply prop_ext.
    destruct (eq_dec a b0); [|destruct (eq_dec a b); [|reflexivity]].
    - split; intro Hx; [subst; constructor | inv Hx; auto].
    - subst; rewrite sublist_same, make_shares_out; auto; try reflexivity.
      replace (Zlength lasts) with N; auto.
    - rewrite (list_Znth_eq lasts) at 1.
      replace (length lasts) with (Z.to_nat N).
      apply map_ext.
      intro; rewrite Znth_nil; destruct (eq_dec Vundef Empty); auto; discriminate.
      { rewrite Zlength_correct in *; rep_omega. } }
  - assert_PROP (Zlength comms = N) as Hcomms by entailer!.
    Intros t' h'.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Hcomms; auto. }
      apply Forall_impl with (P := isptr); auto. }
    rewrite <- lock_struct_array.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
      [|rewrite Zlength_map; auto].
    rewrite (@Znth_map _ N); [|rewrite Zlength_upto; auto].
    rewrite Znth_upto; [|rewrite Z2Nat.id; auto; omega].
    destruct (zlt i i); [omega | rewrite map_add_empty].
    rewrite comm_loc_isptr; Intros.
    forward.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map, Zlength_upto; auto].
    rewrite (@Znth_map _ B), Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; auto; try omega.
    Intros bsh.
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    match goal with H : sepalg_list.list_join _ (sublist i N shs) _ |- _ =>
      rewrite sublist_split with (mid := i + 1) in H; try omega;
      apply list_join_comm, sepalg_list.list_join_unapp in H; destruct H as (bsh' & ? & Hsh) end.
    rewrite sublist_len_1, <- sepalg_list.list_join_1 in Hsh; [|omega].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto, ?Zlength_upto; rewrite ?Z2Nat.id; auto; try omega.
    rewrite Znth_overflow with (al := h'); [|omega].
    destruct (zlt i i); [clear - l; omega|].
    destruct (eq_dec _ _); [discriminate|].
    forward_call (lsh, Znth i comms, Znth i g, Znth i locks, vint 0, vint b, Znth i h,
      fun (h : hist) (v : val) => !!(v = vint b) &&
        ghost_var gsh1 (vint b0) (Znth i g1) *
        ghost_var gsh1 (vint (Znth i lasts)) (Znth i g2) *
        EX v : Z, data_at (Znth i shs) tbuffer (vint v) (Znth b bufs),
      comm_R bufs (Znth i shs) gsh2 (Znth i g0) (Znth i g1) (Znth i g2),
        fun (h : hist) (v : val) => EX b' : Z, !!(v = vint b' /\ -1 <= b' < B) &&
          ghost_var gsh1 (vint b) (Znth i g1) *
          ghost_var gsh1 (vint (if eq_dec b' (-1) then b0 else Znth i lasts)) (Znth i g2) *
          if eq_dec b' (-1) then EX v : Z, data_at (Znth i shs) tbuffer (vint v) (Znth (Znth i lasts) bufs)
          else !!(b' = b0) && EX v' : Z, data_at (Znth i shs) tbuffer (vint v') (Znth b0 bufs)).
    { unfold comm_loc; cancel.
      rewrite prop_true_andp by auto; cancel.
      rewrite (sepcon_comm _ (EX v : Z, _)), !sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives, derives_refl|].
      { instantiate (1 := (EX v : Z, data_at bsh' tbuffer (vint v) (Znth b bufs)) *
          (EX v : Z, data_at (Znth i shs) tbuffer (vint v) (Znth b bufs))).
         Intro v0; Exists v0 v0; rewrite (data_at_share_join _ _ _ _ _ _ Hsh); auto. }
      cancel.
      rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
      unfold AE_spec.
      apply allp_right; intro hc.
      apply allp_right; intro hx.
      apply allp_right; intro vc.
      apply allp_right; intro vx.
      rewrite <- imp_andp_adjoint; Intros.
      apply andp_right; auto; eapply derives_trans, view_shift_weak; auto.
      Intros.
      unfold comm_R at 1 2.
      rewrite rev_app_distr; simpl.
      rewrite last_two_reads_cons, prev_taken_cons.
      assert (repable_signed b) by (apply repable_buf; omega).
      destruct (eq_dec vc Empty).
      { subst; assert (b = -1) by (apply Empty_inj; auto); omega. }
      Intros b' b1 b2.
      apply (derives_trans _ (ghost_var gsh1 (vint b0) (Znth i g1) *
         ghost_var gsh2 (last_write (rev hx)) (Znth i g1) *
        ((ghost_var gsh1 (vint (Znth i lasts)) (Znth i g2) *
         ghost_var gsh2 (prev_taken (rev hx)) (Znth i g2)) *
        (ghost_var gsh2 (vint b1) (Znth i g0) *
         (if eq_dec b' (-1) then EX v1 : Z, @data_at CompSpecs (Znth i shs) tbuffer (vint v1) (Znth b2 bufs)
          else EX v1 : Z, @data_at CompSpecs (Znth i shs) tbuffer (vint v1) (Znth b' bufs)) *
         (EX v1 : Z, @data_at CompSpecs (Znth i shs) tbuffer (vint v1) (Znth b bufs)))))).
      { cancel. }
      assert_PROP (last_write (rev hx) = vint b0) as Hwrite.
      { apply sepcon_derives_prop; rewrite sepcon_comm; apply ghost_var_inj; auto. }
      assert_PROP (prev_taken (rev hx) = vint (Znth i lasts)) as Hprev.
      { rewrite <- sepcon_assoc, (sepcon_comm (_ * _) (_ * ghost_var _ _ _)).
        do 2 apply sepcon_derives_prop.
        rewrite sepcon_comm; apply ghost_var_inj; auto. }
      rewrite <- Hprev, <- Hwrite in *.
      erewrite !ghost_var_share_join by eauto.
      eapply derives_trans; [apply sepcon_derives, derives_refl;
        apply ghost_var_update with (v' := vint b)|].
      rewrite sepcon_comm, !sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply ghost_var_update with
        (v' := if eq_dec b' (-1) then last_write (rev hx) else prev_taken (rev hx))|].
      rewrite <- !sepcon_assoc, sepcon_comm, <- !sepcon_assoc, 2sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives, derives_refl; apply bupd_sepcon|].
      eapply derives_trans; [apply bupd_frame_r | apply bupd_mono].
      erewrite <- !(ghost_var_share_join _ _ Tsh) by eauto.
      Exists b b1 b2; entailer!.
      { rewrite Forall_app; repeat constructor; auto.
        exists b', b; split; [|split]; auto; omega. }
      destruct (eq_dec b (-1)); [omega|].
      Exists b'.
      rewrite <- exp_sepcon2; cancel.
      rewrite prop_true_andp by auto.
      assert (last_two_reads (rev hx) = (vint b1, vint b2)) as Hlast by assumption.
      erewrite take_read, Hlast in *; try (rewrite rev_involutive; eauto).
      unfold last_write in *; simpl in *.
      rewrite (if_false (vint b = Empty)) by auto.
      assert (Znth (Zlength t') lasts = if eq_dec (vint b') Empty then b2 else b1).
      { assert (repable_signed (Znth (Zlength t') lasts)).
        { apply Forall_Znth; [omega|].
          eapply Forall_impl; [|eauto]; intros.
          apply repable_buf; simpl in *; omega. }
        if_tac; apply repr_inj_signed; auto; congruence. }
      destruct (eq_dec (vint b') Empty); subst; simpl; cancel.
      + assert (b' = -1) by (apply Empty_inj; auto; apply repable_buf; auto).
        subst; rewrite !eq_dec_refl.
        rewrite Hwrite; simpl; cancel.
        exploit find_write_read.
        { rewrite rev_involutive; eauto. }
        { discriminate. }
        intros ->; rewrite Hwrite; auto.
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
          destruct (eq_dec (vint b') Empty); [absurd (vint b' = Empty); auto | eauto]. }
        rewrite Hwrite' in Hwrite.
        assert (b' = b0); subst.
        { apply repr_inj_signed; [apply repable_buf | apply repable_buf | simpl in *; congruence]; auto; omega. }
        destruct (eq_dec b0 (-1)); [subst; contradiction n3; auto|].
        unfold last_two_reads in Hlast; destruct (find_read (rev hx) (vint 1)); inv Hlast.
        simpl; entailer!. }
    { repeat (split; auto). }
    Intros x b'; destruct x as (t, v); simpl in *.
    gather_SEP 0 9; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      comm_loc lsh (Znth r locks) (Znth r comms) (Znth r g) (Znth r g0)
        (Znth r g1) (Znth r g2) bufs (Znth r shs) gsh2 (map_add (Znth r h)
        (if zlt r (i + 1) then singleton (Znth r (t' ++ [t])) (AE (Znth r (h' ++ [v])) (vint b)) else empty_map)))
      (upto (Z.to_nat N)))).
    { go_lower.
      rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength;
        rewrite !Zlength_map, Zlength_upto; auto.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite upd_Znth_same by (rewrite Zlength_map, Zlength_upto; auto).
        rewrite (@Znth_map _ N), Znth_upto by (auto; omega).
        destruct (zlt (Zlength t') (Zlength t' + 1)); [|omega].
        rewrite !app_Znth2 by omega.
        rewrite Zminus_diag; replace (Zlength t') with (Zlength h'); rewrite Zminus_diag, !Znth_0_cons; auto.
        rewrite map_add_comm, map_add_single; [apply derives_refl|].
        intros ??? Ht; unfold singleton.
        if_tac; intro X; inv X.
        rewrite newer_out in Ht; [discriminate|].
        replace (Zlength h') with (Zlength t'); auto.
      + rewrite upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; auto).
        rewrite !(@Znth_map _ N), !Znth_upto by (auto; omega).
        if_tac; if_tac; rewrite ?map_add_empty; try omega; try apply derives_refl.
        rewrite !app_Znth1 by omega; apply derives_refl. }
    gather_SEP 1 10; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (if zlt r (i + 1) then b else b0)) (Znth r g1)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      destruct (zlt i (i + 1)); [fast_cancel | omega].
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
      destruct (eq_dec i0 i); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map; auto).
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      destruct (zlt i0 i), (zlt i0 (i + 1)); auto; omega. }
    gather_SEP 2 10; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (@Znth Z (-1) r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [v])) Empty then b0
        else Znth i0 lasts) (upto (Z.to_nat N))))) (Znth r g2)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      erewrite Znth_map, Znth_upto by (auto; unfold N in *; simpl; omega).
      replace i with (Zlength h'); rewrite app_Znth2, Zminus_diag, Znth_0_cons; [fast_cancel | omega].
      apply sepcon_derives.
      { destruct (eq_dec v Empty), (eq_dec b' (-1)); auto; subst.
        + contradiction n1; apply Empty_inj; auto; apply repable_buf; auto.
        + contradiction n1; auto. }
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map;
        try (rewrite !Zlength_upto; simpl; unfold N in *; omega); intros.
      destruct (eq_dec i0 (Zlength h')); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; unfold N in *; simpl; auto; omega).
      erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto; auto; rewrite Zlength_upto in *; try omega.
      destruct (zlt i0 (Zlength h')).
      + rewrite app_Znth1; auto.
      + rewrite Znth_overflow with (al := h'), Znth_overflow with (al := (h' ++ [v])); auto.
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega. }
    assert (repable_signed b') by (apply repable_buf; auto); subst v.
    focus_SEP 9.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (data_at _ _ ?l (gv _last_taken) :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (data_at Ews (tarray tint N)
        (upd_Znth i l (vint (if eq_dec (vint b') Empty then b0 else Znth i lasts))) (gv _last_taken) :: R)))) end.
    + forward.
      match goal with H : Int.repr b' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto. apply ENTAIL_refl.
    + forward.
      destruct (eq_dec b' (-1)); [subst; absurd (Int.repr (-1) = Int.neg (Int.repr 1)); auto|].
      erewrite upd_Znth_triv with (i0 := i).
      apply ENTAIL_refl.
      * rewrite !Zlength_map, Zlength_upto; auto.
      * rewrite !Znth_map, Znth_upto; try (simpl; unfold N in *; omega).
        rewrite Znth_overflow by omega.
        rewrite if_false. rewrite if_false; auto.
        contradict n0. unfold Empty in n0. apply Vint_inj in n0. contradiction.
        intro Hx; inv Hx.
        change (Zlength (upto 3)) with 3. unfold N in *; omega.
        autorewrite with sublist.     change (Zlength (upto 3)) with 3. unfold N in *; omega.
    + subst.
      Exists (t' ++ [t]) (h' ++ [vint b']).
      assert (H11 := I).
      go_lower.
      repeat (apply andp_right; [apply prop_right; repeat split; auto; omega|]).
      rewrite lock_struct_array; fast_cancel.
      rewrite !sepcon_andp_prop'.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; apply andp_right.
      { replace (Zlength t') with (Zlength h') in *; apply prop_right; rewrite Zlength_app; repeat (split; auto).
        rewrite sublist_split with (mid := Zlength h') by omega.
        rewrite (sublist_one (Zlength h')) by (auto; omega).
        apply Forall2_app; auto. }
      fast_cancel.
      apply sepcon_derives.
      * apply derives_refl'; f_equal.
        erewrite upd_Znth_eq, !map_length, upto_length, !map_map;
          [|rewrite !Zlength_map, Zlength_upto; unfold N in *; auto].
        apply map_ext_in; intros; rewrite In_upto in *.
        replace (Zlength t') with (Zlength h').
        destruct (eq_dec a (Zlength h')).
        -- subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; auto; clear; omega.
        -- rewrite !Znth_map, Znth_upto; try omega; try assumption.
           destruct (zlt a (Zlength t')); [rewrite app_Znth1 | rewrite Znth_overflow]; auto; try omega.
           rewrite Znth_overflow with (al := _ ++ _); auto.
           rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
      * fast_cancel.
        replace (Zlength t') with (Zlength h') in *; eapply upd_write_shares; eauto.
  - Intros t' h'.
    forward.
    forward.
    forward.
    rewrite sublist_nil, sublist_same; rewrite ?Zlength_map; auto.
    Exists (map (fun i => if eq_dec (Znth i h') Empty then b0 else Znth i lasts) (upto (Z.to_nat N)))
      (map (fun '(h, (t, v)) => map_upd h t (AE v (vint b))) (combine h (combine t' h'))); entailer!.
    + repeat split.
      * rewrite Forall_map, Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h') Empty); [omega|].
        rewrite In_upto, Z2Nat.id in *; unfold N; try omega.
        apply Forall_Znth; [omega | auto].
      * assert (Zlength h' = Zlength h) as Hlen by omega; assert (Zlength t' = Zlength h') as Hlen' by omega;
        clear - Hlen Hlen'; revert dependent h; revert dependent t'; induction h';
          destruct h, t'; rewrite ?Zlength_nil, ?Zlength_cons in *; simpl; intros; auto;
          try (rewrite Zlength_correct in *; omega).
        constructor; eauto.
        apply IHh'; omega.
      * rewrite in_map_iff; intros (i & ? & ?); subst.
        rewrite In_upto, Z2Nat.id in *; try (unfold N; omega).
        destruct (eq_dec (Znth i h') Empty); [absurd (b0 = b0); auto|].
        match goal with H : ~In _ lasts |- _ => contradiction H; apply Znth_In; omega end.
    + rewrite sepcon_map, <- !sepcon_assoc.
      apply derives_refl'; f_equal; f_equal; [f_equal|].
      { erewrite map_ext_in; eauto; intros; simpl.
        rewrite In_upto in *.
        destruct (zlt a N); [|unfold N in *; simpl in *; omega].
        rewrite map_add_comm, map_add_single.
        rewrite Znth_map, !Znth_combine by
          (rewrite ?Zlength_combine; rewrite ?Z.min_l; rewrite ?Z.min_l; auto; omega); auto.
        intros ??? Ha; unfold singleton.
        if_tac; intro X; inv X.
        rewrite newer_out in Ha; [discriminate|].
        rewrite sublist_all in H12 by omega.
        apply Forall2_Znth; auto; omega. }
      apply map_ext; intro.
      f_equal; extensionality; f_equal; f_equal; apply prop_ext.
      destruct (eq_dec a b).
      * destruct (eq_dec a b0); [absurd (b = b0); subst; auto|].
        split; intro Hx; [inv Hx; auto | subst; constructor].
      * destruct (eq_dec a b0); reflexivity.
Qed.
