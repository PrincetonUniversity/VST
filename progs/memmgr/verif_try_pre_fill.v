Require Import VST.floyd.proofauto.
Require Import malloc.
Require Import ASI_malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import VSU_malloc_definitions.
Local Open Scope logic.

(*Definition Gprog : funspecs := try_pre_fill_spec' ::  external_specs ++ user_specs_R ++ private_specs.
(* It's sort of a hack that try_pre_fill_spec' is included in Gprog here.
  If we don't, and since nobody else calls this function or includes it in their own
  Gprog, then try_pre_fill_spec' won't be in any of the Gprogs;
 that means it won't be in the combined link_main.Gprog,
  and then link_main.prog_correct will fail. 
*)*)

Lemma add_resvec_0: 
  forall rvec b, 0 <= b < BINS -> Zlength rvec = BINS -> (add_resvec rvec b 0) = rvec.
Proof.
  intros. unfold add_resvec.
  bdestruct(Zlength rvec =? BINS); [ | rep_lia].
  bdestruct(0 <=? b); [ | rep_lia].
  bdestruct(b <? BINS); [ | rep_lia].
  simpl.
  replace (Znth b rvec + 0) with (Znth b rvec) by lia.
  rewrite upd_Znth_same_val; [auto | rep_lia].
Qed.

Lemma add_resvec_plus: 
  forall rvec b n m, 0 <= b < BINS -> Zlength rvec = BINS -> 
    (add_resvec (add_resvec rvec b n) b m) = (add_resvec rvec b (n+m)).
Proof.
  intros. unfold add_resvec.
  bdestruct(Zlength rvec =? BINS); [ | rep_lia].
  bdestruct(0 <=? b); [ | rep_lia].
  bdestruct(b <? BINS); [ | rep_lia]; simpl.
  rewrite upd_Znth_Zlength.
  bdestruct(Zlength rvec =? BINS); [ | rep_lia]; simpl.
  rewrite upd_Znth_same; try rep_lia.
  rewrite upd_Znth_twice; try rep_lia.
  rewrite Z.add_assoc; reflexivity. rep_lia.
Qed.

Lemma body_try_pre_fill i: semax_body MF_Vprog MF_Gprog f_try_pre_fill (try_pre_fill_spec' R_APD i).
Proof. 
start_function.
destruct H as [[Hnlo Hnhi] [Hreqlo Hreqhi]].
unfold ASI_malloc.mem_mgr_R. simpl.
assert_PROP (Zlength rvec = BINS) as Hrvec. {
  unfold mem_mgr_R. entailer. rewrite Zlength_map in H0. entailer!. }
forward_call(BINS-1). (*! t1 = bin2size(BINS-1) *)
(*rep_lia.*)
forward_if. (*! if n > t1 *)
(* large case *)
{ forward. (*! return 0 *)
  Exists 0.
  entailer!.
  rewrite add_resvec_0; try rep_lia.
}
(* small case *)
forward_call n; try rep_lia. (*! b = size2bin(n) *)
forward. (*! ful = 0 *)
deadvars!.
set (b:=size2binZ n).
assert (Hb: 0 <= b < BINS) by (apply (size2bin_range n); rep_lia).
forward_call b. (*! t3 = bin2size(b) *)
forward. (*! chunks = (BIGBLOCK - WASTE) / t3 + WORD) *)
entailer!.
          pose proof (bin2size_range b Hb);
          apply repr_inj_unsigned in H0; rep_lia.
forward_while (*! while (req - ful > 0) *)
    (EX ful:_,
    PROP ( 0 <= ful <= Int.max_signed )
     LOCAL (temp _n (Vptrofs (Ptrofs.repr n)); temp _req (Vptrofs (Ptrofs.repr req)); 
            temp _b (Vint (Int.repr b)); temp _ful (Vint (Int.repr ful)); 
            temp _chunks (Vint (Int.repr((BIGBLOCK-WA)/(bin2sizeZ b + WORD)))); 
            gvars gv)
     SEP (mem_mgr_R (add_resvec rvec (size2binZ n) ful) gv)).
- (* init *)
Exists 0.
rewrite add_resvec_0; try rep_lia.
entailer!.
   f_equal.
   unfold Int.divu.
   f_equal.
   pose proof (bin2size_range b Hb); rewrite !Int.unsigned_repr by rep_lia.
   reflexivity.
- (* typecheck guard *)
entailer!.
- (* body preserves *)
forward_if. (*! if (UINT_MAX - ful < chunks) *)
(* case overflow *)
{ forward. (*! return ful *)
  unfold ASI_malloc.mem_mgr_R; simpl. Exists ful.
  entailer!.
}
(* continue *) 
forward_call BIGBLOCK. (*! t3 = mmap0(BIGBLOCK) *)
(*rep_lia.*)
Intros p.
forward_if. (*! if p==null *)
-- if_tac; entailer!. 
-- (* case p==null *)
if_tac. forward.
unfold ASI_malloc.mem_mgr_R; simpl. Exists ful. entailer!. contradiction.
-- (* case p<>null *)
forward_call (n,p,gv,(add_resvec rvec b ful)). (*! pre_fill(n,p) *)
unfold ASI_malloc.mem_mgr_R; simpl.
if_tac. contradiction. subst b. entailer!. 
destruct (eq_dec p nullval). contradiction.
{ (*split; [rep_lia|auto].*) auto. }
unfold b.
forward. (*! ful += chunks *)
(* restore invar *)
Exists (ful + chunks_from_block b); unfold b.
entailer!.
+ unfold chunks_from_block.
  bdestruct (0 <=? b); [ | lia].
  bdestruct (b <? BINS); [ | lia].
  rewrite andb_true_intro
    by (split; [ apply Zaux.Zle_bool_true; trivial
               | apply Zaux.Zlt_bool_true; trivial ]).
  split; [ | trivial].
  pose proof (bin2size_range b Hb).
  assert (0 <= (BIGBLOCK - WA) / (bin2sizeZ b + WORD))
        by (apply Z.div_pos; rep_lia).
  subst b.
  rewrite Int.signed_repr in H1.
  * (*WAS:solve [rep_lia]. *)
    specialize (Z_div_mod (BIGBLOCK - WA) (bin2sizeZ (size2binZ n) + WORD)); intros X.
    destruct (Z.div_eucl (BIGBLOCK - WA) (bin2sizeZ (size2binZ n) + WORD)) as [eu1 eu2].
    destruct X as [X1 X2]. rep_lia.
    rewrite X1, Z.mul_comm, Z.div_add_l, Z.div_small, Zplus_0_r by lia. split. 2: rep_lia.
    assert (0 <= eu1); rep_lia.
  * (*WAS: split; try rep_lia. 
    apply Zdiv_le_upper_bound; auto; rep_lia.*)
    specialize (Z_div_mod (BIGBLOCK - WA) (bin2sizeZ (size2binZ n) + WORD)); intros X.
    destruct (Z.div_eucl (BIGBLOCK - WA) (bin2sizeZ (size2binZ n) + WORD)) as [eu1 eu2].
    destruct X as [X1 X2]. rep_lia. split; try rep_lia.
+ unfold ASI_malloc.mem_mgr_R; simpl.
  entailer!.
  rewrite add_resvec_plus.
  subst b.
  entailer!.
  apply size2bin_range; rep_lia.
  rep_lia.
- (* after loop *) 
forward. (*! return ful *)
unfold ASI_malloc.mem_mgr_R; simpl.
Exists ful.
entailer!.
Qed.
(*
Definition module := [mk_body body_try_pre_fill].
*)