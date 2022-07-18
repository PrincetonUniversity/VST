Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import malloc.
Require Import ASI_malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import VSU_malloc_definitions.
Local Open Scope logic.
(*
Definition Gprog : funspecs := user_specs_R ++ private_specs.
*)
Lemma body_pre_fill i: semax_body MF_Vprog MF_Gprog f_pre_fill (pre_fill_spec' R_APD i).
Proof. 
start_function. 
rewrite <- seq_assoc.  
forward_call n. (*! b = size2bin(n) *)
destruct H as [[Hn_lo Hn_hi] Hp].
try rep_lia.
forward.
set (b:=size2binZ n). 
assert (Hb: 0 <= b < BINS) by (apply size2bin_range; rep_lia).
forward_call b. (*! t2 = bin2size(b) *)
simpl. rewrite (mem_mgr_split_R gv b rvec) by apply Hb.
Intros bins idxs lens.
freeze [1; 3] Otherlists.
deadvars!.
try destruct H as [[Hn_lo Hn_hi] Hp].
forward. (*! t4 = bin[b] *)
forward_call ((bin2sizeZ b), p, (Znth b bins), (Znth b lens), b). (*! t3 = list_from_block(t2,p,t4) *)
Intros q.
forward. (*! bin[b] = t3 *)
thaw Otherlists.

(* fold lists into mem_mgr_R *)
replace (size2binZ (bin2sizeZ b)) with b 
  by (subst b; rewrite claim3; try rep_lia).
simpl ASI_malloc.mem_mgr_R; unfold mem_mgr_R.
set (bins':= upd_Znth b bins q).
set (lens':= map Z.to_nat (add_resvec rvec b (chunks_from_block b))).
assert (Hrveclen: Zlength rvec = BINS) by
   ( subst lens; rewrite Zlength_map in H0; rep_lia). 
Exists bins'. Exists idxs. Exists lens'.
entailer!.
{ split. unfold lens'. rewrite Zlength_map. rewrite Zlength_add_resvec; assumption.
  apply add_resvec_no_neg; try assumption.
  pose proof (chunks_from_block_nonneg (size2binZ n)).
  assert (0 <= Znth (size2binZ n) rvec)
    by (apply Forall_Znth; try rep_lia; try unfold no_neg in *; auto).
  rep_lia.
}
set (idxs:= (map Z.of_nat (seq 0 (Z.to_nat BINS)))).
set (lens:= (map Z.to_nat rvec)).
assert (Zlength lens = BINS) by (unfold lens; rewrite Zlength_map; rep_lia).
assert (Zlength idxs = BINS) by auto.
repeat (rewrite sublist_zip3; try rep_lia).  
replace (sublist 0 b bins) with (sublist 0 b bins') 
  by (unfold bins'; rewrite sublist_upd_Znth_l; try reflexivity; try rep_lia).
replace (sublist (b+1) BINS bins) with (sublist (b+1) BINS bins') 
  by (unfold bins'; rewrite sublist_upd_Znth_r; try reflexivity; try rep_lia).
replace (sublist 0 b lens) with (sublist 0 b lens').
2: { unfold lens'. unfold lens.  do 2 rewrite sublist_map. f_equal.
     unfold add_resvec. simple_if_tac''; auto.
     rewrite sublist_upd_Znth_l; try rep_lia; reflexivity. }
replace (sublist (b + 1) BINS lens) with (sublist (b + 1) BINS lens').
2: { unfold lens'. unfold lens.  do 2 rewrite sublist_map. f_equal. 
     unfold add_resvec. simple_if_tac''; auto.
     rewrite sublist_upd_Znth_r; try rep_lia; reflexivity. }
assert (Zlength bins' = BINS) by auto.
assert (Zlength lens' = BINS) 
  by (unfold lens'; rewrite Zlength_map; rewrite Zlength_add_resvec; auto).
repeat (rewrite <- sublist_zip3; try rep_lia); try rep_lia.  
replace (Z.to_nat (chunks_from_block b) + Znth b lens)%nat with (Znth b lens').
2: {unfold lens'.  rewrite Znth_map.
    unfold add_resvec. simple_if_tac' Hcond.
    2: { assert (Zlength rvec = BINS) by auto. 
         bdestruct(Zlength rvec =? BINS); simpl in Hcond; try contradiction.
         bdestruct(0 <=? b); simpl in Hcond; try contradiction.
         bdestruct(b<?BINS); simpl in Hcond; try contradiction.
         discriminate.
         rep_lia. 
         destruct Hb; contradiction.
    }
    rewrite upd_Znth_same; try rep_lia.
    replace (Znth b lens) with (Z.to_nat (Znth b rvec)) 
      by (unfold lens; rewrite Znth_map; rep_lia).
    rewrite <- Z2Nat.inj_add. f_equal. rep_lia.
    apply chunks_from_block_nonneg.
    apply Forall_Znth; try rep_lia; try unfold no_neg in *; auto.
    rewrite Zlength_add_resvec; rep_lia.
}
replace 
 (mmlist (bin2sizeZ b) (Znth b lens') q nullval * TT *
  iter_sepcon mmlist' (sublist 0 b (zip3 lens' bins' idxs)) *
  iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens' bins' idxs)) * TT)
with 
 (iter_sepcon mmlist' (sublist 0 b (zip3 lens' bins' idxs)) *
  iter_sepcon mmlist' (sublist (b + 1) BINS (zip3 lens' bins' idxs)) * 
  mmlist (bin2sizeZ b) (Znth b lens') q nullval * TT)
by (apply pred_ext; entailer!).
replace q with (Znth b bins').
2: (unfold bins'; rewrite upd_Znth_same; auto; rep_lia).
rewrite mem_mgr_split'; try entailer!; auto.
Qed.
(*
Definition module := [mk_body body_pre_fill].
*)