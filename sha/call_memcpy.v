Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Local Open Scope nat.
Import LiftNotation.

Lemma Zlength_repeat:
  forall {A} n (x:A), Zlength (repeat x (Z.to_nat n)) = Z.max 0 n.
Proof.
intros.
rewrite Zlength_correct, repeat_length.
destruct (zlt n 0).
rewrite Z.max_l by lia.
rewrite Z2Nat_neg by auto. reflexivity.
rewrite Z2Nat.id by lia.
rewrite Z.max_r by lia.
auto.
Qed.

Lemma splice_into_list_simplify0:
  forall {A} n (src dst: list A),
    Zlength src = n ->
    Zlength dst = n ->
    splice_into_list 0 n src dst = src.
Proof.
 intros.
 unfold splice_into_list.
rewrite !sublist_nil.
rewrite app_nil_l.
pose proof (Zlength_nonneg src).
rewrite sublist_nil' by lia.
rewrite app_nil_r.
auto.
Qed.

Lemma splice_into_list_self:
  forall {A} lo hi (l: list A),
    (0 <= lo <= hi)%Z ->
    (hi <= Zlength l)%Z ->
    splice_into_list lo hi (sublist lo hi l) l = l.
Proof.
 intros.
 unfold splice_into_list.
 autorewrite with sublist.
 auto.
Qed.
(*
Lemma splice_into_list_simplify1:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (hi-lo = Zlength src)%Z ->
    splice_into_list lo hi src tgt = tgt++src.
Proof.
intros; subst; unfold splice_into_list.
pose proof (Zlength_nonneg tgt).
pose proof (Zlength_nonneg src).
rewrite H0.
rewrite Z.sub_diag.
change (Z.to_nat 0) with 0%nat; simpl.
rewrite app_nil_r.
rewrite sublist_same by lia.
f_equal.
rewrite (sublist_nil hi), app_nil_r.
rewrite sublist_app by (rewrite ?Zlength_repeat, ?Z.max_r; lia).
rewrite ?Z.min_l by lia.
rewrite ?Z.max_r by lia.
rewrite sublist_nil, app_nil_r.
apply sublist_same; lia.
Qed.

Lemma splice_into_list_simplify2:
  forall lo hi src tgt,
    lo = Zlength tgt ->
    (lo <= hi)%Z ->
    (hi-lo <= Zlength src)%Z ->
    splice_into_list lo hi hi src tgt = tgt++ sublist 0 (hi-lo) src.
Proof.
intros; subst; unfold splice_into_list.
pose proof (Zlength_nonneg tgt).
pose proof (Zlength_nonneg src).
repeat rewrite Z.sub_diag.
change (Z.to_nat 0) with 0.
unfold repeat at 1.
rewrite app_nil_r.
rewrite sublist_same by lia.
f_equal.
rewrite sublist_nil, app_nil_r by lia.
rewrite sublist_app by (rewrite ?Zlength_repeat, ?Z.max_r; lia).
rewrite ?Z.min_l by lia.
rewrite ?Z.max_r by lia.
rewrite sublist_nil, app_nil_r by lia.
auto.
Qed.
*)
Lemma JMeq_skipn:
  forall ta tb n (la: list ta) (lb: list tb),
     ta=tb ->
     JMeq la lb ->
     JMeq (skipn n la) (skipn n lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_firstn:
  forall ta tb n (la: list ta) (lb: list tb),
    ta=tb -> JMeq la lb -> JMeq (firstn n la) (firstn n lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_length:
  forall ta tb (la: list ta) (lb: list tb),
     ta=tb -> JMeq la lb -> length la = length lb.
Proof.
intros. subst tb.  apply JMeq_eq in H0. subst lb. auto.
Qed.

Lemma JMeq_sublist:
  forall ta tb lo hi (la: list ta) (lb: list tb),
    ta=tb -> JMeq la lb -> JMeq (sublist lo hi la) (sublist lo hi lb).
Proof.
intros. subst tb. apply JMeq_eq in H0. subst lb. auto.
Qed.

 Definition fsig_of_funspec (fs: funspec)  :=
  match fs with mk_funspec fsig _ _ _ _ _=> fsig end.

Lemma part1_splice_into_list:
  forall {A} lo hi (al bl: list A),
    (0 <= lo <= Zlength bl)%Z ->
    sublist 0 lo (splice_into_list lo hi al bl) = sublist 0 lo bl.
Proof.
 intros.
 unfold splice_into_list.
 rewrite (sublist_app); rewrite ?Zlength_repeat, ?Z.max_l by lia; try lia;
 rewrite ?Zlength_sublist by lia;
 try (rewrite ?Zlength_correct; lia).
rewrite ?Z.min_l by lia.
rewrite ?Z.max_r by lia.
rewrite sublist_nil, app_nil_r by lia.
rewrite sublist_same; auto.
rewrite Zlength_sublist; lia.
Qed.

Lemma part3_splice_into_list:
  forall {A} lo hi n (al bl: list A),
    (0 <= lo <= hi)%Z -> (hi <= n)%Z ->
   (Zlength bl = n)%Z ->
   (Zlength al = hi-lo)%Z ->
    sublist hi n (splice_into_list lo hi al bl) = sublist hi n bl.
Proof.
 intros.
 unfold splice_into_list.
rewrite app_assoc.
 rewrite (sublist_app); rewrite ?Zlength_repeat, ?Z.max_r, ?Z.max_l by lia; try lia;
 rewrite ?Zlength_sublist by lia;
 try (rewrite ?Zlength_correct; lia).
rewrite !Zlength_app.
rewrite Zlength_sublist; try lia.
rewrite ?Z.min_r by lia.
rewrite ?Z.max_r by lia.
rewrite sublist_nil by lia.
simpl.
rewrite Z.max_l by lia.
rewrite sublist_sublist by lia.
f_equal. lia.
rewrite !Zlength_app.
rewrite !Zlength_sublist; lia.
Qed.

Lemma Zlength_splice_into_list:
  forall {A} lo hi (al bl: list A),
    (0 <= lo <= hi)%Z -> (hi <= Zlength bl)%Z ->
    (hi - lo = Zlength al)%Z ->
    Zlength (splice_into_list lo hi al bl) = Zlength bl.
Proof.
intros.
unfold splice_into_list.
rewrite !Zlength_app.
rewrite !Zlength_sublist; rewrite ?Zlength_app; rewrite ?Zlength_repeat; try lia.
Qed.

Local Arguments nested_field_type cs t gfs : simpl never.

Lemma semax_call_id0_alt:
 forall Espec {cs: compspecs} Delta P Q R id bl argsig tfun retty cc A x Pre Post
   (GLBL: (var_types Delta) !! id = None),
       (glob_specs Delta) !! id = Some (NDmk_funspec (argsig, retty) cc A Pre Post) ->
       (glob_types Delta) !! id = Some (type_of_funspec (NDmk_funspec (argsig, retty) cc A Pre Post)) ->
   (*tfun = type_of_params argsig ->*)tfun = argsig ->
  semax(OK_spec := Espec)(C := cs) ⊤ Delta (tc_exprlist Delta argsig bl
                  && |>(assert_of (fun rho : environ =>
               Pre x (ge_of rho, eval_exprlist argsig bl rho)) *
              PROPx P (LOCALx Q (SEPx R))))
    (Scall None (Evar id (Tfunction tfun retty cc)) bl)
    (normal_ret_assert
       ((ifvoid retty (assert_of (`(Post x : environ -> mpred) (make_args nil nil)))
           (EX v:val, (assert_of (`(Post x : environ -> mpred) (make_args (ret_temp::nil) (v::nil))))))
         ∗ PROPx P (LOCALx Q (SEPx R)))).
Proof.
intros.
subst tfun.
eapply (semax_call_id0 Delta P Q R id bl (NDmk_funspec (argsig, retty) cc A Pre Post)
           argsig retty cc (ConstType A) (λne _, ⊤)
           (λne a : leibnizO A, monPred_at (Pre a) : argsEnviron -d> mpred)
           (λne a : leibnizO A, monPred_at (Post a) : environ -d> mpred) x); eauto.
apply funspec_sub_refl.
Qed.

Lemma call_memcpy_tuchar:  (* Uses CompSpecs from sha. *)
  forall (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
           (shq: share) (tq: type) (pathq: list gfield) (loq: Z) (contents: list int) (q: val)
           (len : Z)
           (R': list mpred)
           (np nq : Z)
           (vp vp'': reptype (nested_field_type tp pathp))
           (vq : reptype (nested_field_type tq pathq))
           (e_p e_q e_n : expr)
           Espec Delta P Q R,
      typeof e_p = tptr tuchar ->
      typeof e_q = tptr tuchar ->
      typeof e_n = tuint ->
      (var_types Delta) !! _memcpy = None ->
     (glob_specs Delta) !! _memcpy = Some (snd memcpy_spec) ->
     (glob_types Delta) !! _memcpy = Some (type_of_funspec (snd memcpy_spec)) ->
     writable_share shp ->  readable_share shq ->
     nested_field_type tp pathp = tarray tuchar np ->
     nested_field_type tq pathq = tarray tuchar nq ->
     (0 <= lop)%Z ->
     (0 <= len <= Int.max_unsigned)%Z ->
     (lop + len <= np)%Z ->
     (0 <= loq)%Z ->  (loq + len <=  (*Zlength contents <=*) nq)%Z ->
     JMeq vq (map Vint contents) ->
     JMeq vp vp' ->
     JMeq vp'' (splice_into_list lop (lop+len) (sublist loq (loq + len) (map Vint contents)) vp') ->
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         tc_exprlist Delta [tptr tvoid; tptr tvoid; tuint] [e_p; e_q; e_n]  &&
         local (`(eq (field_address0 tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p)) &&
         local (`(eq (field_address0 tq (ArraySubsc loq :: pathq) q)) (eval_expr e_q)) &&
         local (`(eq (Vint (Int.repr len))) (eval_expr e_n)) &&
         PROP () (LOCALx Q (SEPx (field_at shp tp pathp vp p ::
                                                 field_at shq tq pathq vq q :: R'))) ->
   semax(OK_spec := Espec) ⊤ Delta
    (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar _memcpy
               (Tfunction
                (cons (tptr tvoid) (cons (tptr tvoid) (cons tuint nil)))
                  (tptr tvoid) cc_default))
              [e_p; e_q; e_n])
    (normal_ret_assert (PROPx P (LOCALx Q
     (SEPx (field_at shp tp pathp vp'' p ::
               field_at shq tq pathq vq q :: R'))))).
Proof.
intros until R.
intros TCp TCq TCn Hvar Hspec Hglob ? SHq ? ? Hlop Hlen Hnp Hloq Hnq; intros.
assert_PROP (fold_right and True%type P); [ go_lowerx; entailer! | ].
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx
              (field_at shp tp pathp vp'' p
               :: field_at shq tq pathq vq q :: R'))));
 [ go_lowerx; entailer! | ].
clear H6. rename H5 into Hpre.
assert_PROP (Zlength vp' = np /\ Zlength contents = nq). {
eapply derives_trans; [apply Hpre |].
apply andp_left2.
go_lowerx; entailer!.
clear - H8 H10 H0 H1 H2 H3 H Hlop Hloq Hnp Hnq Hlen.
forget (nested_field_type tp pathp) as t0.
forget (nested_field_type tq pathq) as t1.
subst t0 t1.
simplify_value_fits in H8. destruct H8 as [H8 _].
simplify_value_fits in H10. destruct H10 as [H10 _].
apply JMeq_eq in H3. subst vp; auto.
apply JMeq_eq in H2. subst vq; auto.
rewrite Zlength_map in H10.
split; auto.
} destruct H5 as [Hvp' Hvq'].

assert (reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type tp (ArraySubsc 0 :: pathp)) = val)
  by (rewrite nested_field_type_ind, H0; reflexivity).
assert (exists vpx : list (reptype (nested_field_type tp (ArraySubsc 0 :: pathp))),
                    JMeq vp vpx)
  by (rewrite H99, <- H5; exists vp; auto).
destruct H6 as [vpx Hvpx].
assert_PROP (legal_nested_field tp pathp /\ legal_nested_field tq pathq). {
  eapply derives_trans; [apply Hpre | apply andp_left2].
go_lowerx; entailer!.
} destruct H6 as [LNFp LNFq].



pose (witness := ((shq,shp),
                              field_address0 tp (ArraySubsc lop :: pathp) p,
                              field_address0 tq (ArraySubsc loq :: pathq) q,
                              len,  sublist loq (loq+len) contents)).
pose (Frame :=
        array_with_segment_hole shq tuchar loq (loq + len) nq (map Vint contents) (field_address tq pathq q)
          :: array_with_segment_hole shp tuchar lop (lop + len) np vp' (field_address tp pathp p) :: R').
eapply semax_pre_post';
  [ | | eapply semax_call_id0_alt with (x:=witness)(P:=nil)(Q:=Q);
       try eassumption;
       try (rewrite ?Hspec, ?Hglob; reflexivity)].

* unfold convertPre. simpl fst; simpl snd.
  iIntros "(#TC & H)".
  iPoseProof (Hpre with "[$]") as "H".
  iSplit; first by rewrite !bi.and_elim_l.
  iNext.
  iAssert ⌜field_address0 tp (pathp SUB lop) p <> Vundef⌝ as %DEFp.
  {
   unfold tc_exprlist.
   simpl typecheck_exprlist.
   rewrite !denote_tc_assert_andp.
   iAssert (denote_tc_assert (typecheck_expr Delta e_p) && local ((` (eq (field_address0 tp (pathp SUB lop) p))) (eval_expr e_p))) with "[H]" as "H".
   { iClear "TC"; iStopProof; solve_andp. }
   iDestruct "TC" as "-#TC".
   iCombine "TC" "H" as "?".
   rewrite <- bi.persistent_and_affinely_sep_l by apply _.
   iStopProof.
   go_lowerx; simpl.
   eapply derives_trans; [apply typecheck_expr_sound; auto |].
   apply bi.pure_mono; intros.
   rewrite <- H7 in H8.
   intro.
   rewrite H9 in H8.
   revert H8; apply tc_val_Vundef.
 }
 iAssert ⌜field_address0 tq (pathq SUB loq) q <> Vundef⌝ as %DEFq.
 {
   unfold tc_exprlist.
   simpl typecheck_exprlist.
   rewrite !denote_tc_assert_andp.
   iAssert (denote_tc_assert (typecheck_expr Delta e_q) && local ((` (eq (field_address0 tq (pathq SUB loq) q))) (eval_expr e_q))) with "[H]" as "H".
   { iClear "TC"; iStopProof; solve_andp. }
   iDestruct "TC" as "-#TC".
   iCombine "TC" "H" as "?".
   rewrite <- bi.persistent_and_affinely_sep_l by apply _.
   iStopProof.
   go_lowerx.
   eapply derives_trans; [apply typecheck_expr_sound; auto |].
   apply bi.pure_mono; intros.
   rewrite <- H7 in H8.
   intro.
   rewrite H9 in H8.
   revert H8; apply tc_val_Vundef.
 }
 subst witness. cbv beta iota. simpl @fst; simpl @snd.
 clear Hpre.
 instantiate (1:=Frame).
 iDestruct "TC" as "-#TC".
 iCombine "TC" "H" as "?".
 rewrite <- bi.persistent_and_affinely_sep_l by apply _.
 iStopProof.
 unfold env_set, PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; split => tau; monPred.unseal; unfold lift1; unfold_lift.
 rewrite TCp, TCq, TCn.  simpl.
 
 try rewrite sem_cast_i2i_correct_range by (rewrite <- H8; auto).
 entailer!!.
 rewrite bi.and_elim_r.
 cancel.
 rewrite !field_at_data_at.
 rewrite (data_at_type_changable _ _ _ _ _ H0 H3).
 rewrite (data_at_type_changable _ _ _ _ _ H1 H2).
 sep_apply (array_with_segment_hole_intro shp tuchar lop (lop + len) (*np*)(Zlength vp') vp' (field_address tp pathp p)); [lia | ].
 sep_apply (array_with_segment_hole_intro shq tuchar loq (loq + len) (*nq*)(Zlength contents)  (map Vint contents) (field_address tq pathq q)); [lia | ].
 cancel.
 apply sepcon_derives.
 - rewrite <- H1.
   rewrite <- field_address0_app by congruence.
   simpl app.
   replace (loq + len - loq)%Z with len by lia.
   rewrite sublist_map.
   auto.
 - replace (memory_block shp len) with
     (memory_block shp (sizeof (nested_field_array_type tp pathp lop (lop + len)))).
   2: {
     f_equal. unfold nested_field_array_type.
     rewrite nested_field_type_ind. rewrite H0. simpl.
     rewrite Z.max_r by lia. rewrite Z.mul_1_l. clear; lia.
   }
   eapply derives_trans; [ | apply data_at__memory_block_cancel]; cancel.
   rewrite <- H0.
   rewrite <- field_address0_app by congruence.
   simpl app.
   unfold nested_field_array_type, tarray.
   rewrite nested_field_type_ind, H0.
   apply data_at_data_at_.
 *
 intros. rewrite bi.and_elim_r.
 go_lowerx. unfold_lift.
 simpl.
 Intros x. rewrite prop_true_andp by auto.
 rewrite map_sublist.
 clear witness Frame.
 normalize in H7.
 subst x.
 simpl.
 clear Hpre H6 P Q rho.
assert (exists (vpy : list (reptype (nested_field_type tp (ArraySubsc 0 :: pathp)))),
                  JMeq vp'' vpy)
  by (rewrite H99; eauto).
destruct H6 as [vpy H7].
assert (Zlength vpy = np). {
 assert (JMeq vpy  (splice_into_list lop (lop + len)
          (sublist loq (loq + len) (map Vint contents)) vp')) by (eapply JMeq_trans; [apply @JMeq_sym |]; eassumption).
 transitivity (Zlength  (splice_into_list lop (lop + len)
          (sublist loq (loq + len) (map Vint contents)) vp')).
 clear - H6 H99 H5.
 forget (splice_into_list lop (lop + len)
          (sublist loq (loq + len) (map Vint contents)) vp') as vv.
 forget val as t. subst t. apply JMeq_eq in H6. subst; auto.
 rewrite Zlength_splice_into_list; try lia.
 autorewrite with sublist; auto.
}
cancel.
change (ArraySubsc loq :: pathq) with ([ArraySubsc loq] ++ pathq).
change (ArraySubsc lop :: pathp) with ([ArraySubsc lop] ++ pathp).
rewrite !field_address0_app by congruence.
rewrite H0, H1.
erewrite (data_at_type_changable shq _ (tarray tuchar (loq + len - loq)));
[| f_equal; lia | apply JMeq_refl].
erewrite (data_at_type_changable shp _ (tarray tuchar (lop + len - lop)));
[| f_equal; lia | apply JMeq_refl].
sep_apply (array_with_segment_hole_elim shp tuchar lop (lop + len) np (sublist loq (loq + len) (map Vint contents)) vp' (field_address tp pathp p)).
sep_apply (array_with_segment_hole_elim shq tuchar loq (loq + len) nq (sublist loq (loq + len) (map Vint contents)) (map Vint contents) (field_address tq pathq q)).
rewrite !field_at_data_at.
rewrite <- sepcon_comm.
apply sepcon_derives.
- erewrite data_at_type_changable; auto.
- erewrite data_at_type_changable; auto.
  eapply JMeq_trans; [| apply JMeq_sym, H2].
  apply eq_JMeq.
  apply splice_into_list_self.
  { lia. }
  { autorewrite with sublist. lia. }
Qed.

Lemma call_memset_tuchar:
  forall (shp : share) (tp: type) (pathp: list gfield) (lop: Z) (vp': list val) (p: val)
           (c: int) (len : Z)
           (R': list mpred)
           (np : Z)
           (vp vp'': reptype (nested_field_type tp pathp))
           (e_p e_c e_n : expr)
           Espec Delta P Q R (s: signedness)
   (TCp : typeof e_p = tptr tuchar)
   (TCc : typeof e_c = tint)
   (TCn : typeof e_n = Tint I32 s noattr)
   (Hvar : (var_types Delta) !! _memset = None)
   (Hspec : (glob_specs Delta) !! _memset = Some (snd memset_spec))
   (Hglob : (glob_types Delta) !! _memset =
        Some (type_of_funspec (snd memset_spec)))
   (H:  writable_share shp)
   (Hlop : (0 <= lop)%Z)
   (Hlen: (0 <= len <= Int.max_unsigned)%Z)
   (H0:  nested_field_type tp pathp = tarray tuchar np)
   (Hnp : (lop + len <= np)%Z)
   (H3:  JMeq vp vp')
   (H4:  JMeq vp'' (splice_into_list lop (lop+len) (repeat (Vint c) (Z.to_nat len)) vp'))
   (H5: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         tc_exprlist Delta [tptr tvoid; tint; tuint] [e_p; e_c; e_n] &&
         local (`(eq (field_address0 tp (ArraySubsc lop :: pathp) p)) (eval_expr e_p)) &&
         local (`(eq (Vint c)) (eval_expr e_c)) &&
         local (`(eq (Vint (Int.repr len))) (eval_expr e_n)) &&
         PROP () (LOCALx Q (SEPx (field_at shp tp pathp vp p :: R')))),
   semax(OK_spec := Espec) ⊤ Delta
    (PROPx P (LOCALx Q (SEPx R)))
    (Scall None
             (Evar _memset
               (Tfunction
                (cons (tptr tvoid) (cons tint (cons tuint nil)))
                  (tptr tvoid) cc_default))
              [e_p; e_c; e_n])
    (normal_ret_assert (PROPx P (LOCALx Q
     (SEPx (field_at shp tp pathp vp'' p :: R'))))).
Proof.
intros.
assert_PROP (fold_right and True%type P)
  by (go_lowerx; entailer!).
apply semax_post' with
   (PROPx nil   (LOCALx Q
           (SEPx (field_at shp tp pathp vp'' p :: R'))));
 [ go_lowerx; entailer! | ].
rename H5 into Hpre.
clear H1.
assert_PROP (Zlength vp' = np). {
eapply derives_trans; [apply Hpre | apply andp_left2].
go_lowerx; entailer!.
clear - H6 H4 H3 Hnp H0 Hlen Hlop.
forget (nested_field_type tp pathp) as t0.
subst t0.
simplify_value_fits in H6. destruct H6 as [H6 _].
apply JMeq_eq in H3. subst vp; auto.
} rename H1 into Hvp'.
assert (H5: reptype (tarray tuchar np) = list val) by reflexivity.
rewrite <- H0 in H5.
assert (H99: reptype (nested_field_type tp (ArraySubsc 0 :: pathp)) = val).
 clear - H0. unfold nested_field_type in *; simpl in *.
  destruct (nested_field_rec tp pathp); inv H0. destruct p. subst.
 reflexivity.
assert (H6: exists vpx : list (reptype (nested_field_type tp (ArraySubsc 0 :: pathp))),
                    JMeq vp' vpx).
rewrite H99. eauto.
destruct H6 as [vpx Hvpx].
assert_PROP (legal_nested_field tp pathp). {
  eapply derives_trans; [apply Hpre | apply andp_left2].
go_lowerx; entailer!.
} rename H1 into LNFp.
apply (fun H => JMeq_trans H Hvpx) in H3.
assert (LENvpx: Zlength vpx = np). {
clear - H99 Hvp' Hvpx.
forget val as t. subst t.
apply JMeq_eq in Hvpx. subst; auto.
}
erewrite field_at_Tarray in Hpre; try eassumption; auto; try lia.
rewrite (split3seg_array_at shp tp pathp 0 lop (lop+len)) in Hpre by lia.
rewrite !Z.sub_0_r in Hpre.

assert_PROP (field_compatible0 tp (pathp SUB lop) p /\
            field_compatible0 tp (pathp SUB (lop + len)) p)
  as FC. {
 eapply derives_trans; [apply Hpre | clear Hpre].
 go_lowerx. apply andp_left2. normalize.
 saturate_local.
 apply prop_right.
 split; auto.
}
pose (witness := (shp,
                              field_address0 tp (ArraySubsc lop :: pathp) p,
                              len,  c)).
pose (Frame :=
         array_at shp tp pathp (lop + len) np
              (sublist (lop+len) np vpx) p
          :: array_at shp tp pathp 0 lop (sublist 0 lop vpx) p
              :: R').
eapply semax_pre_post';
  [ | | eapply semax_call_id0_alt with (x:=witness)(P:=nil)(Q:=Q);
       try eassumption;
       try (rewrite ?Hspec, ?Hglob; reflexivity)].
* unfold convertPre. simpl fst; simpl snd.
 iIntros "(#TC & ?)".
 iPoseProof (Hpre with "[$]") as "H".
 iSplit; first by rewrite !bi.and_elim_l.
 iNext.
 iAssert ⌜field_address0 tp (pathp SUB lop) p <> Vundef⌝ as %DEFp.
 {
   unfold tc_exprlist.
   simpl typecheck_exprlist.
   rewrite !denote_tc_assert_andp.
   iDestruct "TC" as "-#TC".
   iStopProof; rewrite <- bi.persistent_and_affinely_sep_r by apply _.
   apply derives_trans with (local (tc_environ Delta) && denote_tc_assert (typecheck_expr Delta e_p) && local ((` (eq (field_address0 tp (pathp SUB lop) p))) (eval_expr e_p))); [solve_andp |].
   go_lowerx.
   eapply derives_trans; [apply typecheck_expr_sound; auto |].
   apply bi.pure_mono; intros.
   rewrite <- H1 in H6.
   intro.
   rewrite H7 in H6.
   revert H6; apply tc_val_Vundef.
 }
 iDestruct "TC" as "-#TC".
 iStopProof; rewrite <- bi.persistent_and_affinely_sep_r by apply _.
 subst witness. cbv beta iota. simpl @fst; simpl @snd.
 clear Hpre.
 autorewrite with norm1 norm2.

 instantiate (1:=Frame). simpl.
 unfold env_set, PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; split => tau; monPred.unseal; unfold lift1; unfold_lift.
 rewrite TCp, TCc, TCn.  simpl.
 
(* split3; try (repeat split; auto; congruence).*)
 try rewrite sem_cast_i2i_correct_range by (rewrite <- H2; auto).
 try rewrite sem_cast_i2i_correct_range by (rewrite <- H6; auto).
 entailer!!.
 rewrite bi.and_elim_r.
 cancel. (*
 rewrite !field_at_data_at.
 rewrite (data_at_type_changable _ _ _ _ _ H0 H3).
 rewrite (data_at_type_changable _ _ _ _ _ H1 H2).
 sep_apply (array_with_hole_intro shp tuchar lop (lop + len) (*np*)(Zlength vp') vp' (field_address tp pathp p)); [lia | ].
 sep_apply (array_with_hole_intro shq tuchar loq (loq + len) (*nq*)(Zlength contents)  (map Vint contents) (field_address tq pathq q)); [lia | ].
 cancel.

 rewrite PROP_combine.
 unfold app at 1.
 instantiate (1:=Frame).
 unfold app at 2.
 simpl argtypes. unfold eval_exprlist.
 unfold make_args'. simpl map at 2.
 rewrite TCp, TCc, TCn.
 go_lowerx. unfold env_set, eval_id. unfold_lift. simpl.
 autorewrite with gather_prop.
 apply andp_right.
 apply prop_right. split3; try (repeat split; auto; congruence).
 normalize.
 subst Frame.
 cancel.*)
 rewrite array_at_data_at' by  (try solve [clear - FC; intuition]; lia).
 eapply derives_trans; [apply data_at_data_at_ | ].
 eapply derives_trans; [apply data_at__memory_block_cancel | ].
 f_equiv.
  unfold nested_field_array_type.
   rewrite nested_field_type_ind, H0. simpl.
  rewrite Z.max_r by lia. lia.
*
 intros. apply andp_left2.
 unfold ifvoid. unfold tptr at 1.
 Intros v. subst witness. cbv beta zeta iota.
 clear Hpre.
 autorewrite with norm1 norm2.
 subst Frame.
 go_lowerx. entailer!!.
 clear H1 H2.
 assert (H2: exists (vpy : list (reptype (nested_field_type tp (ArraySubsc 0 :: pathp)))),
                  JMeq vp'' vpy).
 rewrite H99. eauto.
destruct H2 as [vpy H8].
erewrite field_at_Tarray; try eassumption; auto; try lia.
apply (JMeq_trans (JMeq_sym H4)) in H8.
clear dependent vp''. clear dependent e_c. clear dependent e_p. clear dependent e_n.
clear dependent Delta.
remember (Zlength vp') as np eqn: Hvp'.
assert (Zlength vpy = np). {
clear - H0 H8 Hvp' Hnp Hlop Hlen.
generalize dependent vpy.
rewrite nested_field_type_ind, H0. simpl. rewrite reptype_eq; simpl.
intros.
apply JMeq_eq in H8.
subst.
clear H0.
rewrite Zlength_splice_into_list; try lia.
autorewrite with sublist.
auto.
}
rewrite (split3seg_array_at shp tp pathp 0 lop (lop+len) np) by lia.
rewrite !Z.sub_0_r.
replace (sublist 0 lop vpx) with (sublist 0 lop vpy).
2:{
generalize dependent vpy.
generalize dependent vpx.
rewrite H99.
intros.
apply JMeq_eq in H8. apply JMeq_eq in Hvpx.
subst.
apply part1_splice_into_list; lia.
} 
replace (sublist (lop+len) np vpx) with (sublist (lop+len) np vpy).
2:{
generalize dependent vpy.
generalize dependent vpx.
rewrite H99.
intros.
apply JMeq_eq in H8. apply JMeq_eq in Hvpx.
subst.
apply part3_splice_into_list; try lia.
rewrite Zlength_repeat. rewrite Z.max_r by lia. lia.
} 
cancel.
 rewrite array_at_data_at' by  (try solve [clear - FC; intuition]; lia).
   erewrite data_at_type_changable; eauto.
   unfold nested_field_array_type.
   rewrite nested_field_type_ind, H0.
   unfold tarray; f_equal. clear; lia.
   apply (JMeq_sublist _ _ lop (lop + len) _ _ (eq_sym H99)) in H8.
   eapply JMeq_trans, H8.
   apply eq_JMeq.
   unfold splice_into_list.
   autorewrite with sublist. auto.
Qed.
