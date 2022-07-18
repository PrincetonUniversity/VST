Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import VSU_malloc_definitions.
Local Open Scope logic.
(*
Definition Gprog : funspecs := private_specs.
*)
Lemma body_free_small:  semax_body MF_Vprog MF_Gprog f_free_small free_small_spec.
Proof. 
start_function. 
destruct H as [[Hn Hn'] [Hs Hmc]].
forward_call s. (*! b = size2bin(s) !*)
{ subst; pose proof (bin2size_range(size2binZ n)); pose proof (claim2 n); rep_lia. }
set (b:=(size2binZ n)). 
assert (Hb: b = size2binZ s) by (subst; rewrite claim3; auto).
rewrite <- Hb.
assert (Hb': 0 <= b < BINS) 
  by (change b with (size2binZ n); apply claim2; split; assumption).
rewrite (mem_mgr_split_R gv b rvec Hb'). (* to expose bins[b] in mem_mgr *)
Intros bins idxs lens.
forward. (*! void *q = bin[b] !*) 
assert_PROP( (force_val (sem_cast_pointer p) = field_address (tptr tvoid) [] p) ). 
{ entailer!. unfold field_address; normalize; if_tac; auto; contradiction. }
forward. (*!  *((void ** )p) = q !*)
set (q:=(Znth b bins)).
assert_PROP (p <> nullval) by entailer!.
apply semax_pre with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
     SEP ((EX q': val, !!(malloc_compatible s p /\ p <> nullval) && 
          data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p) *
          data_at Tsh (tptr tvoid) q' p *
          memory_block Tsh (s - WORD) (offset_val WORD p) *
          mmlist (bin2sizeZ b) (Znth b lens) q' nullval) ;
     data_at Ews (tarray (tptr tvoid) BINS) bins (gv _bin);
     iter_sepcon mmlist' (sublist 0 b (zip3 lens bins idxs)) ;
     iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens bins idxs)) ;
     TT)).
{ Exists q. entailer!. }
replace (bin2sizeZ b) with s by auto. 
change (Znth b lens)
  with (Nat.pred (Nat.succ (Znth b lens))).
assert_PROP( isptr p ). 
{ entailer!. unfold nullval in *.
  match goal with | HA: p <> _ |- _ => simpl in HA end. (* not Archi.ptr64 *)
  unfold is_pointer_or_null in *. simpl in *.
  destruct p; try contradiction; simpl.  auto. 
}
assert (succ_pos: forall n:nat, Z.of_nat (Nat.succ n) > 0) 
  by (intros; rewrite Nat2Z.inj_succ; rep_lia).
rewrite <- (mmlist_unroll_nonempty s (Nat.succ (Znth b lens)) p nullval);
  try assumption; try apply succ_pos. clear succ_pos.
forward. (*! bin[b] = p !*)
set (bins':=(upd_Znth b bins p)).
set (rvec':=add_resvec rvec b 1).
set (lens':= map Z.to_nat rvec').
assert (Hlenrvec: Zlength rvec = BINS) 
  by (subst lens; rewrite Zlength_map in H0; rep_lia).
assert (Hlenrvec': Zlength rvec' = BINS)
  by (subst rvec'; rewrite Zlength_add_resvec; rep_lia).
apply ENTAIL_trans with 
    (PROP ( )
     LOCAL (temp _q q; temp _b (Vint (Int.repr b)); 
     temp _p p; temp _s (Vptrofs (Ptrofs.repr s)); gvars gv)
     SEP (EX bins1: list val, EX idxs1: list Z, EX lens1: list nat,  
          !! (Zlength bins1 = BINS /\ Zlength lens1 = BINS /\ Zlength idxs1 = BINS
             /\ lens1 = map Z.to_nat rvec'
             /\ idxs1 = map Z.of_nat (seq 0 (Z.to_nat BINS))
             /\ no_neg rvec') &&
    data_at Ews (tarray (tptr tvoid) BINS) bins1 (gv _bin) * 
    iter_sepcon mmlist' (sublist 0 b (zip3 lens1 bins1 idxs1)) *
    mmlist (bin2sizeZ b) (Znth b lens1) (Znth b bins1) nullval *
    iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens1 bins1 idxs1)) *
    TT )).
- (* first entailment *)
  Exists bins'.  Exists idxs. Exists lens'.
  assert_PROP(Zlength bins' = BINS /\ Zlength lens' = BINS).
  { unfold bins'.  unfold lens'.  
    entailer!.
    rewrite Zlength_map. subst rvec'. rewrite Zlength_add_resvec. 
    rewrite Zlength_map in H0. auto.
  } 
  replace (bin2sizeZ b) with s by auto. 
  replace (Znth b bins') with p 
    by (unfold bins'; rewrite upd_Znth_same; auto; rewrite H; assumption). 
  replace (Nat.succ (Znth b lens)) with (Znth b lens').
  2: { (* justify replacement *)
    unfold lens'. rewrite Znth_map by rep_lia. subst rvec'.  unfold add_resvec. 
    bdestruct(Zlength rvec =? BINS); simpl; try rep_lia.
    bdestruct(0<=?b); simpl; try rep_lia.
    bdestruct(b<?BINS); simpl; try rep_lia.
    rewrite upd_Znth_same by rep_lia.  subst lens. rewrite Znth_map by rep_lia.
    rewrite Z2Nat.inj_add; try rep_lia.
    change (Z.to_nat 1) with 1%nat.  change Nat.succ with S. (* ugh *)  lia. 
    unfold no_neg in *; apply Forall_Znth; try rep_lia.
    assumption.
  }
  entailer!.
  { unfold rvec'. apply add_resvec_no_neg; auto.
    unfold no_neg in *. 
    assert (0 <= Znth (size2binZ n) rvec).
    apply Forall_Znth. assumption. rep_lia. lia.
  }
  change (upd_Znth (size2binZ n) bins p) with bins'.  entailer!.
  (* remains to show bins' and lens' are same as originals aside from n *)
  set (idxs:=(map Z.of_nat (seq 0 (Z.to_nat BINS)))) in *.
  repeat rewrite sublist_zip3; try rep_lia.
  set (lens:= map Z.to_nat rvec).
  replace (sublist 0 (size2binZ n) lens') 
    with (sublist 0 (size2binZ n) lens).
  2: { unfold lens'. unfold lens.  do 2 rewrite sublist_map.
       f_equal. unfold rvec'.  unfold add_resvec.  set (b:=(size2binZ n)). 
       simple_if_tac''; auto.
       rewrite sublist_upd_Znth_l; try rep_lia; reflexivity.
  }
  replace (sublist (size2binZ n + 1) BINS lens') 
    with (sublist (size2binZ n + 1) BINS lens).
  2: { unfold lens'. unfold lens.  do 2 rewrite sublist_map.
       f_equal. unfold rvec'.  unfold add_resvec.  set (b:=(size2binZ n)). 
       simple_if_tac''; auto.
       rewrite sublist_upd_Znth_r; try rep_lia; reflexivity.
  }
  replace (sublist 0 (size2binZ n) bins') with (sublist 0 (size2binZ n) bins)
    by (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_lia).
  replace (sublist (size2binZ n + 1) BINS bins')
    with (sublist (size2binZ n + 1) BINS bins) by 
      (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_lia).
  entailer!.
- (* second entailment *)
  subst rvec'.
  rewrite <- (mem_mgr_split_R gv b (add_resvec rvec b 1) Hb').
  entailer!.
Qed.
(*
Definition module := [mk_body body_free_small].
*)