Require Import mailbox.general_atomics.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox_bad.
Require Import mailbox.verif_mailbox_bad_specs.

Set Bullet Behavior "Strict Subproofs".

Opaque upto.

Lemma body_initialize_writer : semax_body Vprog Gprog f_initialize_writer initialize_writer_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (field_at Ews tint [] (eval_unop Oneg tint (vint 1)) writing; field_at Ews tint [] (vint 0) last_given;
        data_at Ews (tarray tint N) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - forward.
    rewrite upd_init_const; auto.
    entailer!.
  - forward.
Qed.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint B) v_available; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken)
   SEP (data_at Tsh (tarray tint B) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) v_available;
        data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
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
   LOCAL (temp _i (vint B); lvar _available (tarray tint B) v_available;
   gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
     else if in_dec eq_dec x (sublist 0 i lasts) then 0 else 1)) (upto (Z.to_nat B))) v_available;
   data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!.
    rewrite upd_Znth_eq with (d := Vundef); simpl; [|rewrite !Zlength_cons, Zlength_nil; unfold B, N in *; omega].
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
      LOCAL (temp _last (vint (Znth i lasts 0)); temp _r (vint i); temp _i (vint B); lvar _available (tarray tint 5) v_available; 
             gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) v_available;
           data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    - assert (0 <= Znth i lasts 0 < B) by (apply Forall_Znth; auto).
      forward.
      entailer!.
      rewrite upd_Znth_eq with (d := Vundef); [|auto].
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      erewrite Znth_map, Znth_upto; simpl; auto; try omega.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := 0); auto; try omega.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts 0])); rewrite in_app in *.
      + destruct (eq_dec a (Znth i lasts 0)); destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
      + destruct (eq_dec a (Znth i lasts 0)).
        { subst; contradiction n; simpl; auto. }
        destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto; contradiction n; auto.
    - forward.
      entailer!.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto in *; simpl in *.
      destruct (eq_dec a b0); auto.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := 0); auto; try omega.
      match goal with H : Int.repr _ = Int.neg _ |- _ => apply repr_inj_signed in H end.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts 0])); rewrite in_app in *.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        rewrite Int.unsigned_repr in *; try computable; omega.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        contradiction n0; auto.
      + apply Forall_Znth; auto.
        eapply Forall_impl; [|eauto]; unfold repable_signed; intros.
        split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try omega.
      + unfold repable_signed; computable.
    - intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert; entailer!. }
  rewrite sublist_same; auto.
  set (available := map (fun x => vint (if eq_dec x b0 then 0 else if in_dec eq_dec x lasts then 0 else 1))
         (upto (Z.to_nat B))).
  rewrite <- seq_assoc.
  unfold Sfor.
  forward.
  eapply semax_seq, semax_ff.
  eapply semax_pre with (P' := EX i : Z, PROP (0 <= i <= B; forall j, j < i -> Znth j available (vint 0) = vint 0)
    LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) v_available; gvar _writing writing;
           gvar _last_given last_given; gvar _last_taken last_taken)
    SEP (field_at Tsh (tarray tint 5) [] available v_available; data_at_ Ews tint writing;
         data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)).
  { Exists 0; entailer!.
    intros; apply Znth_underflow; auto. }
  eapply semax_loop.
  + Intros i.
    assert (repable_signed i).
    { split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try omega. }
    forward_if (PROP (i < B)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) v_available; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint 5) [] available v_available; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      entailer!. }
    { forward.
      exploit (list_pigeonhole (b0 :: lasts) B).
      { rewrite Zlength_cons; unfold B; omega. }
      intros (j & ? & Hout); exploit (H3 j); [unfold B, N in *; omega|].
      subst available.
      rewrite Znth_map with (d' := B); [|rewrite Zlength_upto; auto].
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
    forward_if (PROP (Znth i available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) v_available; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available v_available; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
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
    intros.
    unfold exit_tycon, overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
    Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
    instantiate (1 := EX i : Z, PROP (0 <= i < B; Znth i available (vint 0) = vint 0;
      forall j : Z, j < i -> Znth j available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) v_available; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available v_available; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    Exists i; entailer!.
  + Intros i.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1); entailer!.
    intros; destruct (eq_dec j i); subst; auto.
    assert (j < i) by omega; auto.
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
    destruct a, shs.
    { rewrite Zlength_nil, !Zlength_correct in *; omega. }
    rewrite Zlength_cons in *; simpl; rewrite IHl1; [|omega].
    rewrite sublist_S_cons with (i0 := Z.succ _); [|rewrite Zlength_correct; omega].
    unfold Z.succ; rewrite !Z.add_simpl_r.
    if_tac; auto.
Qed.

Lemma make_shares_out : forall b lgood lasts shs (Hb : ~In b lasts)
  (Hlen1 : Zlength lgood = Zlength shs) (Hlen2 : Zlength lasts = Zlength shs),
  make_shares shs (combine lgood lasts) b = map snd (filter fst (combine lgood shs)).
Proof.
  induction lgood; auto; intros.
  destruct lasts; simpl.
  { symmetry in Hlen2; apply Zlength_nil_inv in Hlen2; subst.
    apply Zlength_nil_inv in Hlen1; discriminate. }
  destruct shs; simpl.
  { apply Zlength_nil_inv in Hlen1; discriminate. }
  destruct (z =? b) eqn: Heq; [rewrite Z.eqb_eq in Heq; subst; contradiction Hb; simpl; auto|].
  rewrite !Zlength_cons in *; rewrite IHlgood; try omega; simpl in *; [|tauto].
  destruct a; auto.
Qed.

Lemma make_shares_ext : forall i d l l' lgood shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j l d = i <-> Znth j l' d = i),
  make_shares shs (combine lgood l) i = make_shares shs (combine lgood l') i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  exploit (Hi 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro Hiff.
  destruct lgood; auto; simpl.
  rewrite (IHl l'); try omega.
  destruct (negb b); auto.
  destruct (a =? i) eqn: Ha, (z =? i) eqn: Hz; auto; rewrite ?Z.eqb_eq, Z.eqb_neq in *; tauto.
  { intros; exploit (Hi (j + 1)); [omega|].
    rewrite !Znth_pos_cons, !Z.add_simpl_r; auto; omega. }
Qed.

Lemma make_shares_add : forall i i' d lasts lgood j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts d = i) (Hgood : Znth j lgood false = true) (Hi' : i' <> i)
  (Hlen : Zlength shs >= Zlength lasts),
  exists shs1 shs2, make_shares shs (combine lgood lasts) i = shs1 ++ shs2 /\
    make_shares shs (combine lgood (upd_Znth j lasts i')) i = shs1 ++ Znth j shs Tsh :: shs2.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct lgood; [rewrite Znth_nil in Hgood; discriminate|].
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in Hi', IHlasts; rewrite !Znth_0_cons; simpl.
    rewrite Znth_0_cons in Hgood; subst; simpl.
    rewrite Z.eqb_refl, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega; simpl.
    rewrite <- Z.eqb_neq in Hi'; rewrite Hi'.
    eexists [], _; simpl; split; eauto.
  - rewrite Znth_pos_cons in Hi; [|omega].
    rewrite Znth_pos_cons in Hgood; [|omega].
    rewrite Znth_pos_cons; [|omega].
    exploit (IHlasts lgood (j - 1) shs); auto; try omega.
    intros (shs1 & shs2 & Heq1 & Heq2).
    rewrite upd_Znth_cons; [simpl | omega].
    exists (if (negb b || (a =? i))%bool then shs1 else t :: shs1), shs2; rewrite Heq1, Heq2;
      if_tac; auto.
Qed.

Lemma make_shares_In : forall i lasts lgood x shs (Hx : 0 <= x < Zlength lasts)
  (Hi : Znth x lasts 0 <> i) (Hgood : Znth x lgood false = true)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs Tsh) (make_shares shs (combine lgood lasts) i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct lgood; [rewrite Znth_nil in Hgood; discriminate|].
    destruct (eq_dec x 0); simpl.
    + subst; rewrite Znth_0_cons in Hi; rewrite Znth_0_cons in Hgood; rewrite Znth_0_cons.
      rewrite <- Z.eqb_neq in Hi; rewrite Hi; subst; simpl; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons in Hgood; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts lgood (x - 1) shs); eauto; try omega.
      if_tac; simpl; auto.
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
    destruct a.
    destruct (_ || _)%bool.
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      exploit IHlasts; eauto; [omega|].
      intro; eapply sepalg.join_sub_trans; eauto; eexists; eauto.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

(* up *)
Lemma combine_nil : forall {A B} (l : list A), combine l (@nil B) = [].
Proof.
  destruct l; auto.
Qed.

Lemma make_shares_join : forall i d lasts lgood shs sh0 j sh1 sh2
  (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1)
  (Hsh2 : sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts) i) sh2)
  (Hin : 0 <= j < Zlength shs) (Hj : Znth j lasts d = i),
  exists sh', sepalg.join sh2 (Znth j shs Tsh) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega); try omega.
  { rewrite Znth_nil in Hj.
    rewrite combine_nil in Hsh2; inv Hsh2.
    exploit (Znth_In j (t :: shs) Tsh); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  - subst j; rewrite Znth_0_cons in Hj; rewrite Znth_0_cons; subst.
    destruct lgood; simpl in Hsh2; [inv Hsh2; inv Hsh1; eauto|].
    rewrite Z.eqb_refl in Hsh2.
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    exploit (make_shares_sub i (combine lgood lasts)); eauto.
    { rewrite Zlength_combine, Z.ge_le_iff, Z.min_le_iff; omega. }
    { destruct b; eauto. }
    intro; eapply sepalg.join_sub_joins_trans; eauto.
  - rewrite Znth_pos_cons in Hj; [|omega].
    rewrite Znth_pos_cons; [|omega].
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    destruct lgood; simpl in Hsh2.
    { inv Hsh2.
      apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      eapply (IHlasts []); eauto; try constructor; omega. }
    destruct (_ || _)%bool.
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
  intros.
  repeat unfold_data_at 1%nat.
  rewrite !field_at_data_at'; simpl; entailer.
  apply data_at_value_cohere; auto.
Qed.

Lemma make_shares_add' : forall i i' d lasts lgood j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts d = i) (Hgood : Znth j lgood false = false)
  (Hlen : Zlength shs >= Zlength lasts),
  make_shares shs (combine lgood (upd_Znth j lasts i')) i = make_shares shs (combine lgood lasts) i.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct lgood; auto; simpl.
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in IHlasts; rewrite Znth_0_cons in Hgood; rewrite !Znth_0_cons; subst; simpl.
    rewrite Zlength_cons, sublist_1_cons, sublist_same; auto; omega.
  - rewrite Znth_pos_cons in Hi by omega.
    rewrite Znth_pos_cons in Hgood by omega.
    rewrite upd_Znth_cons by omega; simpl.
    rewrite IHlasts by (auto; omega); auto.
Qed.

Lemma make_shares_ext' : forall i d l l' lgood shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j lgood false = true -> Znth j l d = i <-> Znth j l' d = i),
  make_shares shs (combine lgood l) i = make_shares shs (combine lgood l') i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  destruct lgood; auto; simpl.
  rewrite (IHl l'); try omega.
  destruct b; auto; simpl.
  exploit (Hi 0); [rewrite Zlength_correct; omega | apply Znth_0_cons|].
  rewrite !Znth_0_cons; intro Hiff.
  destruct (a =? i) eqn: Ha, (z =? i) eqn: Hz; auto; rewrite ?Z.eqb_eq, Z.eqb_neq in *; tauto.
  { intros; exploit (Hi (j + 1)); rewrite ?Znth_pos_cons, ?Z.add_simpl_r; auto; omega. }
Qed.

(* The relationship between the last_taken array and the shares held by the writer is
   preserved by the action of the loop body. *)
Lemma upd_write_shares : forall bufs b b0 lgood lasts shs sh0 (Hb : 0 <= b < B) (Hb0 : 0 <= b0 < B)
  (Hlasts : Forall (fun x : Z => 0 <= x < B) lasts) (Hshs : Zlength shs = N)
  (Hread : Forall readable_share shs) (Hsh0 : sepalg_list.list_join sh0 shs Tsh)
  (Hdiff : b <> b0) (Hout : ~ In b lasts) (Hout0 : ~ In b0 lasts) (Hlasts : Zlength lasts = N)
  (Hlgood : Zlength lgood = N) i (Hh' : 0 <= i < N) good (Hgood : good = Znth i lgood false)
  b' (Hb' : good = true -> -1 <= b' < B) sh (Hsh : sh = Znth i shs Tsh)
  shi (Hshi : sepalg_list.list_join sh0
         (map snd (filter fst (sublist (i + 1) N (combine lgood shs)))) shi)
  bsh (Hbsh : sepalg_list.list_join shi
    (map snd (if good then [(good, sh)] else [])) bsh)
  h' (Hh' : Zlength h' = i) lasts' (Hlasts' : lasts' = map (fun i =>
    if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto 3))
  lasts'' (Hlasts'' : lasts'' = map (fun i =>
    if eq_dec (Znth i (h' ++ [vint b']) Vundef) Empty then b0 else Znth i lasts 0) (upto 3)) vb,
(if good then EX v : _, data_at sh tbuffer (Vint v)
     (Znth (if eq_dec b' (-1) then Znth i lasts 0 else b0) bufs Vundef)
 else emp) *
(data_at shi tbuffer (Vint vb) (Znth b bufs Vundef) *
 fold_right sepcon emp (upd_Znth b (map (fun a => EX sh2 : share,
   !! (if eq_dec a b0 then sepalg_list.list_join sh0
         (make_shares shs (combine lgood (sublist 0 i lasts')) a) sh2
       else if eq_dec a b then sepalg_list.list_join sh0
         (map snd (filter fst (sublist i N (combine lgood shs)))) sh2
       else sepalg_list.list_join sh0
         (make_shares shs (combine lgood lasts') a) sh2) &&
      (EX v : _, data_at sh2 tbuffer (Vint v) (Znth a bufs Vundef))) (upto 5)) emp))
|-- fold_right sepcon emp (map (fun a => EX sh2 : share,
   !! (if eq_dec a b0 then sepalg_list.list_join sh0
        (make_shares shs (combine lgood (sublist 0 (i + 1) lasts'')) a) sh2
      else if eq_dec a b then sepalg_list.list_join sh0
        (map snd (filter fst (sublist (i + 1) N (combine lgood shs)))) sh2
      else sepalg_list.list_join sh0
        (make_shares shs (combine lgood lasts'') a) sh2) &&
    (EX v : _, data_at sh2 tbuffer (Vint v) (Znth a bufs Vundef))) (upto 5)).
Proof.
  intros.
  assert (readable_share sh).
  { subst sh; apply Forall_Znth; auto; omega. }
  set (lasti := Znth i lasts 0).
  exploit (Znth_In i lasts 0); [omega | intro Hini].
  assert (lasti <> b) as Hneq.
  { intro; match goal with H : ~In b lasts |- _ => contradiction H end; subst b lasti; auto. }
  assert (lasti <> b0) as Hneq0.
  { intro; match goal with H : ~In b0 lasts |- _ => contradiction H end; subst b0 lasti; auto. }
  match goal with |- _ * (_ * fold_right sepcon emp (upd_Znth b ?l _)) |-- _ =>
    set (l0 := upd_Znth b l (EX v : _, @data_at CompSpecs shi tbuffer (Vint v) (Znth b bufs Vundef))) end.
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto; auto. }
  assert (0 <= lasti < B).
  { apply Forall_Znth; auto; omega. }
  apply derives_trans with (fold_right sepcon emp (
    if eq_dec b' (-1) then upd_Znth lasti l0
            (EX sh1 : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
             (combine lgood lasts') lasti) sh' /\ if good then sepalg.join sh' sh sh1 else sh1 = sh') &&
            (EX v1 : _, @data_at CompSpecs sh1 tbuffer (Vint v1) (Znth lasti bufs Vundef)))
          else upd_Znth b0 l0 (EX sh1 : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
            (combine lgood (sublist 0 i lasts')) b0) sh' /\ if good then sepalg.join sh' sh sh1 else sh1 = sh') &&
            (EX v1 : _, @data_at CompSpecs sh1 tbuffer (Vint v1) (Znth b0 bufs Vundef))))).
  { eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives, derives_refl]|].
    { instantiate (1 := EX v : _, data_at shi tbuffer (Vint v) (Znth b bufs Vundef)).
      Exists vb; auto. }
    rewrite replace_nth_sepcon.
    destruct (eq_dec b' (-1)).
    - rewrite extract_nth_sepcon with (i := lasti) by (subst l0; omega).
      erewrite upd_Znth_diff', Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; simpl; try (unfold B, N in *; omega).
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros ish v2.
      assert (exists sh', sepalg.join ish sh sh') as (sh' & ?).
      { subst sh; eapply make_shares_join; eauto.
        + subst lasts'; setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, ?Z2Nat.id; unfold N; simpl; omega.
        + setoid_rewrite Hshs; auto.
        + subst lasts'; rewrite Znth_map', Znth_upto by (unfold N in *; simpl; omega).
          rewrite Znth_overflow; auto; omega. }
      rewrite (extract_nth_sepcon (upd_Znth lasti l0 (EX sh : share, _)) lasti) by (rewrite upd_Znth_Zlength; omega).
      rewrite upd_Znth_twice, upd_Znth_same by omega.
      rewrite <- sepcon_assoc; apply sepcon_derives; auto.
      if_tac.
      + Intros v1.
        eapply derives_trans; [apply data_at_buffer_cohere; auto|].
        erewrite data_at_share_join by eauto.
        Exists sh' v1; entailer!; eauto.
      + Exists ish v2; entailer!; eauto.
    - Intros.
      rewrite extract_nth_sepcon with (i := b0) by (subst l0; omega).
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try (unfold B, N in *; simpl; omega).
      destruct (eq_dec b0 b0); [|contradiction].
      Intros ish v2.
      assert (exists sh', sepalg.join ish sh sh') as (sh' & ?).
      { subst sh; eapply make_shares_join; eauto.
        + subst lasts'; setoid_rewrite Hshs; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; unfold N in *; simpl; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_overflow; auto.
          subst lasts'; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; unfold N in *; simpl; omega. }
      rewrite (extract_nth_sepcon (upd_Znth b0 l0 (EX sh : share, _)) b0) by (rewrite upd_Znth_Zlength; omega).
      rewrite upd_Znth_twice, upd_Znth_same by omega.
      rewrite <- sepcon_assoc; apply sepcon_derives; auto.
      if_tac.
      + Intros v1.
        eapply derives_trans; [apply data_at_buffer_cohere; auto|].
        erewrite data_at_share_join by eauto.
        Exists sh' v1; entailer!; eauto.
      + Exists ish v2; entailer!; eauto. }
  apply derives_refl'; f_equal.
  match goal with |- ?l = _ => assert (Zlength l = B) as Hlen end.
  { destruct (eq_dec b' (-1)); auto; rewrite upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq' with (d := FF).
  { rewrite Hlen, Zlength_map, Zlength_upto; auto. }
  rewrite Hlen; intros.
  assert (0 <= j <= B) by omega.
  erewrite Znth_map, Znth_upto by auto.
  assert (forall j, j <> Zlength h' \/ vint b' <> Empty -> (if eq_dec (Znth j h' Vundef) Empty then b0 else Znth j lasts 0) =
    if eq_dec (Znth j (h' ++ [vint b']) Vundef) Empty then b0 else Znth j lasts 0) as Heq.
  { intros ? Hcase.
    destruct (zlt j0 (Zlength h')); [rewrite app_Znth1; auto|].
    rewrite Znth_overflow, app_Znth2 by auto.
    destruct (eq_dec j0 (Zlength h')).
    - if_tac; [discriminate|].
      destruct (eq_dec (Znth _ _ _) _); auto.
      subst; rewrite Zminus_diag, Znth_0_cons in e0; destruct Hcase; try contradiction.
    - rewrite (Znth_overflow _ [_]); auto.
      rewrite Zlength_cons, Zlength_nil; omega. }
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec b' (-1)).
    + rewrite upd_Znth_same by omega.
      destruct (eq_dec lasti b0); [contradiction|].
      destruct (eq_dec lasti b); [contradiction|].
      f_equal; extensionality; f_equal; f_equal.
      destruct (Znth _ lgood _) eqn: Hgood.
      * exploit (make_shares_add lasti b0 0 (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0
          else Znth i lasts 0) (upto (Z.to_nat N))) lgood (Zlength h') shs); auto.
        { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try omega.
          rewrite Znth_overflow by omega.
          destruct (eq_dec Vundef Empty); [discriminate | auto]. }
        { setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
        simpl; intros (shsa & shsb & Hshs1 & Hshs2).
        rewrite Hshs1.
        erewrite make_shares_ext, Hshs2.
        apply prop_ext; split.
        -- intros (? & Hj1 & Hj2).
           apply list_join_comm.
           apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
           econstructor; eauto.
           apply list_join_comm; auto.
        -- intro Hj; apply list_join_comm in Hj.
           inversion Hj as [|????? Hj1 Hj2]; subst.
           apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
           do 2 eexists; eauto; apply list_join_comm; auto.
        -- rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
        -- rewrite Zlength_map, Zlength_upto; intros.
           rewrite Znth_map', Znth_upto by omega.
           destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
           ++ rewrite app_Znth1, upd_Znth_diff; auto; try omega.
              erewrite Znth_map, Znth_upto; auto; [reflexivity | omega].
           ++ subst; rewrite Znth_app1, eq_dec_refl, upd_Znth_same; auto; reflexivity.
           ++ rewrite Znth_overflow, upd_Znth_diff; auto; [|rewrite Zlength_app, Zlength_cons, Zlength_nil; omega].
              erewrite Znth_map, Znth_upto; auto; [|omega].
              rewrite Znth_overflow with (al := h'); [reflexivity | omega].
      * erewrite make_shares_ext'.
        apply prop_ext; split; [intros [? []]; subst|]; eauto.
        { rewrite !Zlength_map; auto. }
        { rewrite Zlength_map; intros.
          erewrite !Znth_map with (b1 := 0), !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
          rewrite Heq; [reflexivity|].
          left; intro; subst; destruct (Znth (Zlength h') lgood false); discriminate. }
    + subst l0; rewrite 2upd_Znth_diff; auto; try omega.
      erewrite Znth_map, Znth_upto; try assumption.
      destruct (eq_dec lasti b0); [contradiction|].
      destruct (eq_dec lasti b); [contradiction|].
      erewrite make_shares_ext'; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      rewrite Heq; [reflexivity|].
      destruct (eq_dec j (Zlength h')); auto.
      subst; right; intros ?%Empty_inj; auto; apply repable_buf; auto.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint b']) Vundef) Empty
      then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    simpl in *.
    destruct (eq_dec b' (-1)).
    + assert (EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (combine lgood (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N))))) b0)
          sh && (EX v1 : _, data_at sh tbuffer (Vint v1) (Znth b0 bufs Vundef)) =
        EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (combine lgood (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint b']) Vundef) Empty then b0 else Znth i lasts 0)
          (upto (Z.to_nat N))))) b0) sh && (EX v0 : _, data_at sh tbuffer (Vint v0) (Znth b0 bufs Vundef))).
      { erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
          auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_app1; auto.
        rewrite <- (app_nil_r (sublist 0 (Zlength h') _)).
        replace lgood with (sublist 0 (Zlength h') lgood ++ sublist (Zlength h') (Zlength lgood) lgood).
        assert (Zlength (sublist 0 (Zlength h') lgood) = Zlength h').
        { rewrite Zlength_sublist; omega. }
        rewrite !combine_app', combine_nil; try omega.
        subst; rewrite eq_dec_refl, app_nil_r, make_shares_app; simpl.
        replace (make_shares (sublist _ _ _) _ _) with (@nil share).
        erewrite app_nil_r, make_shares_ext; eauto; try omega.
        rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto; auto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
        { destruct (sublist (Zlength h') (Zlength lgood) lgood); auto; simpl.
          rewrite Z.eqb_refl, orb_true_r, combine_nil; auto. }
        { rewrite !Zlength_combine, !Z.min_r; rewrite ?Zlength_cons, ?Zlength_nil; try omega.
          - setoid_rewrite Hshs; omega.
          - rewrite Zlength_sublist; omega. }
        { unfold N; simpl; omega. }
        { unfold N; simpl; omega. }
        { rewrite sublist_rejoin, sublist_same; auto; omega. } }
      destruct (eq_dec lasti (-1)); subst l0; [rewrite upd_Znth_diff | rewrite 2upd_Znth_diff]; auto; try omega.
      erewrite Znth_map, Znth_upto; auto; destruct (eq_dec b0 b0); [eauto | contradiction].
    + rewrite upd_Znth_same by omega.
      erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
        auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; simpl; try (unfold N in *; omega).
      rewrite Znth_app1; auto.
      rewrite <- (app_nil_r (sublist 0 (Zlength h') _)).
      set (good := Znth (Zlength h') lgood false).
      replace lgood with (sublist 0 (Zlength h') lgood ++ sublist (Zlength h') (Zlength lgood) lgood).
      assert (Zlength (sublist 0 (Zlength h') lgood) = Zlength h').
      { rewrite Zlength_sublist; omega. }
      rewrite !combine_app', combine_nil; try omega.
      replace (combine (sublist (Zlength h') _ _) _) with [(good,
        if eq_dec (vint b') Empty then b0 else Znth (Zlength h') lasts 0)]; simpl.
      rewrite app_nil_r, make_shares_app; simpl.
      destruct good eqn: Hgood; simpl.
      * destruct (eq_dec (vint b') Empty).
        { apply Empty_inj in e; [contradiction|].
          apply repable_buf; auto. }
        fold lasti; destruct (lasti =? b0) eqn: Heq'; [rewrite Z.eqb_eq in Heq'; contradiction|].
        rewrite hd_Znth, Znth_sublist; rewrite ?Hlenh'; try setoid_rewrite Hshs; rewrite ?Zlength_combine, ?Z.min_l; try omega.
        f_equal; extensionality; f_equal; f_equal.
        replace (Zlength (sublist _ _ lgood)) with (Zlength h').
        erewrite make_shares_ext.
        apply prop_ext; split.
        -- intros (? & Hj1 & Hj2).
           apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
           apply list_join_comm; econstructor; eauto.
           erewrite Znth_indep; eauto.
           setoid_rewrite Hshs; auto.
        -- intro Hj; apply list_join_comm in Hj; inversion Hj as [|????? Hj1 Hj2]; subst.
           apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
           do 2 eexists; eauto.
           erewrite Znth_indep; eauto.
           setoid_rewrite Hshs; auto.
        -- omega.
        -- rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto;
             rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
           rewrite app_Znth1; [reflexivity | omega].
      * f_equal; extensionality; f_equal; f_equal.
        erewrite app_nil_r, make_shares_ext'.
        apply prop_ext; split; [intros (? & ? & ?); subst|]; eauto.
        { omega. }
        { rewrite Hlenh; intros ??; erewrite !Znth_sublist, !Znth_map with (b1 := 0), !Znth_upto; rewrite ?Zlength_upto; try (unfold N in *; simpl; omega).
          rewrite Z.add_0_r; intro; rewrite Heq; [reflexivity|].
          left; intro; subst; destruct (Znth (Zlength h') lgood false); discriminate. }
      * rewrite Zlength_combine, Z.min_l, Zlength_cons, Zlength_nil by omega.
        setoid_rewrite Hshs; omega.
      * erewrite sublist_next by omega; simpl.
        rewrite combine_nil; subst good; auto.
      * rewrite sublist_rejoin, sublist_same by omega; auto.
  - transitivity (Znth j l0 FF).
    { destruct (eq_dec b' (-1)); rewrite upd_Znth_diff; auto; omega. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
      apply mpred_ext.
      * Exists shi; entailer!.
      * Intros sh1.
        assert (sh1 = shi) by (eapply list_join_eq; eauto; apply HshP).
        subst; auto.
    + rewrite upd_Znth_diff' by auto.
      erewrite Znth_map, Znth_upto by auto.
      destruct (eq_dec j b0); [contradiction|].
      destruct (eq_dec j b); [contradiction|].
      simpl; erewrite make_shares_ext'; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j0 (Zlength h')); [rewrite app_Znth1 by auto; reflexivity|].
      rewrite Znth_overflow, app_Znth2 by auto.
      destruct (eq_dec Vundef Empty); [discriminate|].
      destruct (eq_dec _ Empty); [|reflexivity].
      destruct (eq_dec j0 (Zlength h')); [|rewrite Znth_overflow in e; try discriminate].
      split; intro; subst; tauto.
      { rewrite Zlength_cons, Zlength_nil; omega. }
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  rewrite sepcon_map; Intros.
  forward.
  forward.
  assert_PROP (Zlength (map (fun i => vint i) lasts) = N) by entailer!.
  rewrite Zlength_map in *.
  assert (Zlength (combine lgood lasts) = N).
  { rewrite Zlength_combine, Z.min_l; omega. }
  assert (Zlength (combine lgood shs) = N).
  { rewrite Zlength_combine, Z.min_l; omega. }
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _w (vint b); temp _last (vint b0); gvar _writing writing; gvar _last_given last_given;
          gvar _last_taken last_taken; gvar _comm comm)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        EX t' : list nat, EX h' : list val, !!(Zlength t' = i /\ Zlength h' = i) &&
          fold_right sepcon emp (map (fun r => comm_loc (Znth r lgood false) lsh (Znth r comms Vundef)
            (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh)
            gsh2 (Znth r h [] ++ if zlt r i then [(Znth r t' O, AE (Znth r h' Vundef) (vint b))] else []))
            (upto (Z.to_nat N))) *
          let lasts' := map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0)
                            (upto (Z.to_nat N)) in
            data_at Ews (tarray tint N) (map (fun i => vint i) lasts') last_taken *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 (vint (if zlt r i then b else b0)) (Znth r g1 Vundef)) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 (vint (Znth r lasts' (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun a => EX sh : share,
              !!(if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (combine lgood (sublist 0 i lasts')) a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (map snd (filter fst (sublist i N (combine lgood shs)))) sh
                 else sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts') a) sh) &&
              EX v : _, @data_at CompSpecs sh tbuffer (Vint v) (Znth a bufs Vundef)) (upto (Z.to_nat B))))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists (@nil nat) (@nil val).
    replace (map (fun i => if eq_dec (Znth i [] Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      with lasts.
    entailer!.
    apply derives_refl'; f_equal; f_equal.
    { f_equal.
      apply map_ext_in.
      intros; rewrite In_upto in *.
      destruct (zlt a 0); [omega | rewrite app_nil_r; auto]. }
    apply map_ext; intro.
    f_equal; extensionality; f_equal; f_equal.
    rewrite sublist_nil, combine_nil; simpl.
    apply prop_ext.
    destruct (eq_dec a b0); [|destruct (eq_dec a b); [|reflexivity]].
    - split; intro Hx; [subst; constructor | inv Hx; auto].
    - subst; rewrite sublist_same, make_shares_out; unfold share in *; auto; try reflexivity; omega.
    - rewrite (list_Znth_eq 0 lasts) at 1.
      replace (length lasts) with (Z.to_nat N).
      apply map_ext.
      intro; rewrite Znth_nil; destruct (eq_dec Vundef Empty); auto; discriminate.
      { rewrite Zlength_correct in *; Omega0. } }
  - assert_PROP (Zlength comms = N) as Hcomms by entailer!.
    Intros t' h'.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Hcomms; auto. }
      apply Forall_impl with (P := isptr); auto. }
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
      [|rewrite Zlength_map; auto].
    erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
    destruct (zlt i i); [omega | rewrite app_nil_r].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b) by (rewrite Zlength_map, Zlength_upto; auto).
    erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    Intros bsh.
    destruct (eq_dec b b0); [contradiction|].
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    match goal with H : sepalg_list.list_join _ (map _ _) _ |- _ =>
      rewrite sublist_split with (mid := i + 1), sublist_len_1 with (d := (false, Tsh)), filter_app,
        map_app, Znth_combine in H by omega; simpl in H;
        apply list_join_comm, sepalg_list.list_join_unapp in H;
        destruct H as (shi & Hshi & Hbsh) end.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto, ?Zlength_upto; rewrite ?Z2Nat.id; auto; try omega.
    rewrite Znth_overflow with (al := h'); [simpl | omega].
    destruct (zlt i i); [clear - l; omega|].
    set (gi := Znth i g Vundef).
    set (g0i := Znth i g0 Vundef).
    set (g1i := Znth i g1 Vundef).
    set (g2i := Znth i g2 Vundef).
    set (c := Znth i comms Vundef).
    set (sh := Znth i shs Tsh) in *.
    set (hi := Znth i h []).
    set (good := Znth i lgood false) in *.
    Intro vb.
    forward_call (AEX_SC_witness c b
      ((if good then data_at sh tbuffer (Vint vb) (Znth b bufs Vundef) else emp) *
      ghost_var gsh1 (vint b0) g1i * ghost_var gsh1 (vint (Znth i lasts 0)) g2i * ghost_hist lsh hi gi)
      (fun _ : Z => comm_inv good c bufs sh gi g0i g1i g2i gsh2) [0]
      (fun b' => !!(good = true -> b' = -1 \/ b' = b0) &&
        (if good then EX v : _, data_at sh tbuffer (Vint v)
          (Znth (if eq_dec b' (-1) then Znth i lasts 0 else b0) bufs Vundef) else emp) *
        ghost_var gsh1 (vint b) g1i *
        ghost_var gsh1 (vint (if eq_dec b' (-1) then b0 else Znth i lasts 0)) g2i *
        EX t : _, !!(newer hi t) && ghost_hist lsh (hi ++ [(t, AE (vint b') (vint b))]) gi)).
    { unfold comm_loc at 1; simpl; cancel.
      destruct good; simpl in *.
      + rewrite <- sepalg_list.list_join_1 in Hbsh.
        rewrite <- (data_at_share_join _ _ _ _ _ _ Hbsh); cancel.
      + inv Hbsh; subst Frame; simpl; cancel. }
    { lapply (repable_buf b); [|omega].
      split; auto.
      apply wand_view_shifts2.
      assert (lsh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
      if_tac; unfold comm_inv; simpl.
      + view_shift_intro v0; view_shift_intro l.
        unfold comm_R at 1.
        view_shift_intro b1; view_shift_intro b2; view_shift_intro v'; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
        rewrite (sepcon_comm _ (ghost_hist _ _ _)).
        rewrite !sepcon_emp, <- !sepcon_assoc, 7sepcon_assoc.
        apply view_shift_assert with (PP := hist_incl hi l).
        { apply sepcon_derives_prop, hist_ref_incl; auto. }
        intros ?%hist_incl_lt.
        etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g1i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g1i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint b)|].
        erewrite <- ghost_var_share_join by eauto.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g2i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g2i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint (if eq_dec v0 (-1) then b0 else Znth i lasts 0))|].
        erewrite <- ghost_var_share_join by eauto.
        apply derives_view_shift; Exists Tsh v0.
        rewrite sepcon_andp_prop'; apply andp_right.
        { entailer!.
          apply repable_buf; auto. }
        cancel.
        rewrite <- wand_sepcon_adjoint.
        Exists (length l); cancel.
        Exists b; entailer!.
        rewrite <- exp_sepcon1, <- exp_sepcon2.
        Exists (l ++ [AE (vint v0) (vint b)]); unfold comm_R.
        rewrite !rev_app_distr; unfold last_write in *; simpl;
          rewrite last_two_reads_cons, prev_taken_cons.
        destruct (eq_dec (vint b) Empty).
        { apply Empty_inj in e; auto; subst; omega. }
        destruct (eq_dec b (-1)); [omega|].
        assert (Forall (fun a => match a with AE v1 v2 => exists r w,
          v1 = vint r /\ v2 = vint w /\ -1 <= r < B /\ -1 <= w < B end)
          (l ++ [AE (vint v0) (vint b)])).
        { rewrite Forall_app; repeat constructor; auto.
          exists v0, b; repeat (split; auto; try omega). }
        assert (apply_hist (vint 0) (l ++ [AE (vint v0) (vint b)]) = Some (vint b)).
        { rewrite apply_hist_app; replace (apply_hist _ _) with (Some (vint v0)); simpl.
          apply eq_dec_refl. }
        match goal with H : _ = prev_taken _ |- _ =>
          erewrite take_read in H by (rewrite rev_involutive; eauto) end.
        match goal with H : last_two_reads _ = _ |- _ => rewrite H in * end.
        if_tac; Intro v; Exists b1 b2 v vb.
        * subst; match goal with H : vint _ = _ |- _ => rewrite eq_dec_refl in H end.
          exploit (repr_inj_signed b2 (Znth (Zlength t') lasts 0)); auto.
          { apply Forall_Znth; [omega|].
            eapply Forall_impl; [|eauto]; simpl; intros; apply repable_buf; omega. }
          { simpl in *; congruence. }
          intro; rewrite !sepcon_andp_prop'; apply andp_right.
          { entailer!. }
          erewrite find_write_read by (rewrite ?rev_involutive; eauto; discriminate); simpl.
          replace (fst _) with (vint b0).
          rewrite (sepcon_comm _ (ghost_ref _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel.
          apply andp_right; [apply prop_right; auto | subst; cancel].
        * destruct (eq_dec (vint v0) Empty); [apply Empty_inj in e; auto; contradiction|].
          exploit (write_val (rev l)); [rewrite rev_involutive; eauto|].
          intros [|]; [contradiction|].
          exploit (repr_inj_signed v0 b0); auto.
          { apply repable_buf; omega. }
          { congruence. }
          exploit (repr_inj_signed (Znth (Zlength t') lasts 0) b1); auto.
          { apply Forall_Znth; [omega|].
            eapply Forall_impl; [|eauto]; simpl; intros; apply repable_buf; omega. }
          { simpl in *; congruence. }
          entailer!.
          rewrite sepcon_comm; apply derives_refl'; f_equal; f_equal.
          unfold last_two_reads in *.
          destruct (find_read _ _); match goal with H : (_, _) = (_, _) |- _ => inv H; auto end.
      + view_shift_intro v0; view_shift_intro l.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
        rewrite (sepcon_comm _ (ghost_hist _ _ _)).
        rewrite !sepcon_emp, <- !sepcon_assoc, 6sepcon_assoc.
        apply view_shift_assert with (PP := hist_incl hi l).
        { apply sepcon_derives_prop, hist_ref_incl; auto. }
        intros ?%hist_incl_lt.
        etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
        view_shift_intro b0'; view_shift_intro b1'; view_shift_intro b2'.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g1i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g1i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint b)|].
        erewrite <- ghost_var_share_join by eauto.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g2i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g2i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint (if eq_dec (Int.signed (Int.repr v0)) (-1) then b0
          else Znth i lasts 0))|].
        erewrite <- ghost_var_share_join by eauto.
        apply derives_view_shift.
        Exists Tsh (Int.signed (Int.repr v0)); rewrite Int.repr_signed; entailer!.
        { apply Int.signed_range. }
        rewrite <- wand_sepcon_adjoint.
        Exists (length l) b (l ++ [AE (vint v0) (vint b)])
          (vint (if eq_dec (Int.signed (Int.repr v0)) (-1) then b0 else Znth (Zlength t') lasts 0))
          (vint b) b0'; entailer!.
        { discriminate. }
        rewrite sepcon_comm; auto. }
    Intros b' t.
    gather_SEP 0 4 8; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      comm_loc (Znth r lgood false) lsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
        (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h [] ++
        (if zlt r (i + 1) then [(Znth r (t' ++ [t]) 0%nat, AE (Znth r (h' ++ [vint b']) Vundef) (vint b))] else [])))
      (upto (Z.to_nat N)))).
    { go_lower.
      rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength;
        rewrite !Zlength_map, Zlength_upto; auto.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite upd_Znth_same by (rewrite Zlength_map, Zlength_upto; auto).
        rewrite Znth_map with (d' := N), Znth_upto by (auto; omega).
        destruct (zlt (Zlength t') (Zlength t' + 1)); [|omega].
        rewrite !app_Znth2 by omega.
        subst hi c gi g0i g1i g2i good sh.
        rewrite Zminus_diag; replace (Zlength t') with (Zlength h'); rewrite Zminus_diag, !Znth_0_cons; auto.
      + rewrite upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; auto).
        rewrite !Znth_map with (d' := N), !Znth_upto by (auto; omega).
        if_tac; if_tac; auto; try omega.
        rewrite !app_Znth1; auto; omega. }
    gather_SEP 2 8; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (if zlt r (i + 1) then b else b0)) (Znth r g1 Vundef)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      destruct (zlt i (i + 1)); [subst g1i; fast_cancel | omega].
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
      destruct (eq_dec i0 i); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map; auto).
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      destruct (zlt i0 i), (zlt i0 (i + 1)); auto; omega. }
    gather_SEP 3 8; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (Znth r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [vint b']) Vundef) Empty then b0
        else Znth i0 lasts 0) (upto (Z.to_nat N))) (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      erewrite Znth_map, Znth_upto by (auto; unfold N in *; simpl; omega).
      replace i with (Zlength h'); rewrite app_Znth2, Zminus_diag, Znth_0_cons; [fast_cancel | omega].
      apply sepcon_derives.
      { replace (Zlength h') with i; subst g2i; destruct (eq_dec b' (-1)), (eq_dec (vint b') Empty);
          auto; subst; [contradiction|].
        contradiction n0; apply Empty_inj; auto; apply repable_buf; auto. }
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map;
        try (rewrite !Zlength_upto; simpl; unfold N in *; omega); intros.
      destruct (eq_dec i0 (Zlength h')); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; unfold N in *; simpl; auto; omega).
      erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto; auto; rewrite Zlength_upto in *; try omega.
      destruct (zlt i0 (Zlength h')).
      + rewrite app_Znth1; auto.
      + rewrite Znth_overflow with (al := h'), Znth_overflow with (al := (h' ++ [vint b'])); auto.
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega. }
    focus_SEP 7.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (data_at _ _ ?l last_taken :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (data_at Ews (tarray tint N)
        (upd_Znth i l (vint (if eq_dec (vint b') Empty then b0 else Znth i lasts 0))) last_taken :: R)))) end.
    + forward.
      match goal with H : Int.repr b' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto.
      destruct (eq_dec (- (1)) (-1)); [|absurd (-1 = -1); auto].
      apply ENTAIL_refl.
    + forward.
      destruct (eq_dec b' (-1)); [subst; contradiction|].
      erewrite upd_Znth_triv with (i0 := i).
      apply ENTAIL_refl.
      * rewrite !Zlength_map, Zlength_upto; auto.
      * rewrite !Znth_map', Znth_upto; [|simpl; unfold N in *; omega].
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint b') Empty); auto.
        contradiction n0; apply Empty_inj; auto.
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply ENTAIL_refl].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert.
      do 2 (apply andp_right; [apply prop_right; auto|]).
      Exists (t' ++ [t]) (h' ++ [vint b']).
      rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; entailer!.
      rewrite !sepcon_assoc; apply sepcon_derives.
      * apply derives_refl'; f_equal.
        erewrite upd_Znth_eq, !map_length, upto_length, !map_map;
          [|rewrite !Zlength_map, Zlength_upto; unfold N in *; auto].
        apply map_ext_in; intros; rewrite In_upto in *.
        replace (Zlength t') with (Zlength h').
        destruct (eq_dec a (Zlength h')).
        -- subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; auto; clear; omega.
        -- rewrite Znth_map', Znth_upto; [|omega].
           destruct (zlt a (Zlength t')); [rewrite app_Znth1 | rewrite Znth_overflow]; auto; try omega.
           rewrite Znth_overflow with (al := _ ++ _); auto.
           rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
      * fast_cancel.
        subst good sh; replace (Zlength t') with (Zlength h') in *; eapply upd_write_shares; eauto.
        intro; match goal with H : _ -> _ \/ _ |- _ => destruct H; subst; auto; omega end.
  - Intros t' h'.
    forward.
    forward.
    forward.
    Exists (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      (extendr (map (fun x : nat * val => let '(t, v) := x in (t, AE v (vint b))) (combine t' h')) h); entailer!.
    + repeat split.
      * rewrite Forall_map, Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h' Vundef) Empty); [omega|].
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
        destruct (eq_dec (Znth i h' Vundef) Empty); [absurd (b0 = b0); auto|].
        match goal with H : ~In _ lasts |- _ => contradiction H; apply Znth_In; omega end.
    + rewrite sepcon_map, <- !sepcon_assoc.
      apply derives_refl'; f_equal; f_equal; [f_equal|].
      { erewrite map_ext_in; eauto; intros; simpl.
        rewrite In_upto in *.
        destruct (zlt a N); [|unfold N in *; simpl in *; omega].
        erewrite Znth_extendr_in, Znth_map', Znth_combine; eauto;
          rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; omega. }
      apply map_ext; intro.
      f_equal; extensionality; f_equal; f_equal; apply prop_ext.
      destruct (eq_dec a b).
      * destruct (eq_dec a b0); [absurd (b = b0); subst; auto|].
        split; intro Hx; [inv Hx; auto | subst; constructor].
      * destruct (eq_dec a b0); reflexivity.
Qed.
