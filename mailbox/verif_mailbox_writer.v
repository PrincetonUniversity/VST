Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Opaque upto.
Opaque eq_dec.


Ltac entailer_for_load_tac ::= unfold tc_efield; go_lower; entailer'.
Ltac entailer_for_store_tac ::= unfold tc_efield; go_lower; entailer'.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  start_function.
  assert (B < Int.max_signed) as HB by computable.
  forward_call gv.
  forward.
  forward_loop (∃ v : Z, ∃ b0 : Z, ∃ lasts : list Z, ∃ h : list hist,
   PROP (0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; ~In b0 lasts)
   LOCAL (temp _v (vint v); temp _arg arg; gvars gv)
   SEP (data_at Ews tint Empty (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
   data_at Ews (tarray tint N) (map (fun x => vint x) lasts) (gv _last_taken);
   data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
   data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _bufs);
   [∗] (map (fun r0 => comm_loc lsh (Znth r0 comms)
     (Znth r0 g) (Znth r0 g0) (Znth r0 g1) (Znth r0 g2) bufs
     (Znth r0 shs) (Znth r0 h)) (upto (Z.to_nat N)));
   [∗] (map (fun r0 => ghost_frag (vint b0) (Znth r0 g1) ∗
     ghost_frag (vint (@Znth Z (-1) r0 lasts)) (Znth r0 g2)) (upto (Z.to_nat N)));
   [∗] (map (fun i => ∃ sh : share, ⌜if eq_dec i b0 then sh = sh0
     else sepalg_list.list_join sh0 (make_shares shs lasts i) sh⌝ ∧
     (∃ v : Z, data_at(cs := CompSpecs) sh tbuffer (vint v) (Znth i bufs))) (upto (Z.to_nat B)))))
  break: (False : assert).
  { Exists 0 0 (repeat 1 (Z.to_nat N)) (repeat (∅ : hist) (Z.to_nat N)); entailer!; simpl.
    my_auto.
    { repeat constructor; computable. }
    rewrite big_sep_map -bi.sep_assoc; f_equiv.
    { erewrite map_ext; first done.
      by intros ?; setoid_rewrite (Znth_repeat 3). }
    f_equiv; first by rewrite -> list_Znth_eq with (l := g1) at 1; rewrite map_map;
      replace (length g1) with (Z.to_nat N) by (symmetry; rewrite <- Zlength_length; auto; unfold N; computable).
    f_equiv; first by rewrite -> list_Znth_eq with (l := g2) at 1; rewrite map_map;
      replace (length g2) with (Z.to_nat N) by (symmetry; rewrite <- Zlength_length; auto; unfold N; computable).
    f_equiv.
    rewrite Forall2_map Forall2_forall_Znth; split; first done.
    intros ?; rewrite Zlength_upto.
    intros ?; rewrite -> !Znth_upto by (unfold N; rewrite ?Zlength_upto; lia).
    destruct (eq_dec i 0); try done.
    destruct (eq_dec i 1), (eq_dec 1 i); try done.
    { Intros sh; Exists sh; entailer!; constructor. }
    generalize (make_shares_out i (repeat 1 (Z.to_nat N)) shs); simpl.
    rewrite !if_false //; intros ->; [| lia | auto].
    Intros sh; Exists sh; entailer!. }
  Intros v b0 lasts h.
  rewrite big_sep_map; Intros.
  forward_call (b0, lasts, gv).
  Intros b.
  lazymatch goal with |-context[[∗] map ?f (upto (Z.to_nat B))] =>
    gather_SEP ([∗] map f (upto (Z.to_nat B))); evar (P : mpred); replace_SEP 0 P end.
  { go_lowerx; rewrite bi.sep_emp; apply (big_sepL_lookup_acc _ _ (Z.to_nat b)), Znth_lookup.
    rewrite Zlength_map Zlength_upto //. }
  subst P; simpl; rewrite Znth_map // Znth_upto //.
  Intros sh v0.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  destruct (eq_dec b b0); first done.
  assert_PROP (Zlength lasts = N).
  { entailer!.
    autorewrite with sublist in *.
    unfold N in *; simpl in *; lia. }
  rewrite -> make_shares_out in * by (auto; setoid_rewrite H; auto).
  assert (sh = Ews) by (eapply sepalg_list.list_join_eq; eauto); subst.
  forward.
  gather_SEP 0 1; replace_SEP 0 ([∗] (map (fun i => ∃ sh2 : share,
    ⌜if eq_dec i b0 then sh2 = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh2⌝ ∧
    (∃ v1 : Z, data_at sh2 tbuffer (vint v1) (Znth i bufs))) (upto (Z.to_nat B)))).
  { go_lower; iIntros "(? & H)"; iApply "H"; eauto. }
  change (upto 3) with (upto (Z.to_nat N)).
  change (upto 5) with (upto (Z.to_nat B)).
  forward_call (comms, bufs, b, b0, lasts, sh1, lsh, shs, g, g0, g1, g2, h, sh0, gv).
  { rewrite big_sep_map; cancel. }
  Intros x; destruct x as (lasts', h').
  forward.
  Exists (v + 1) b lasts' h'; entailer!.
  { replace N with (Zlength h) by auto; symmetry; eapply mem_lemmas.Forall2_Zlength; eauto. }
  cancel.
Qed.

End mpred.
