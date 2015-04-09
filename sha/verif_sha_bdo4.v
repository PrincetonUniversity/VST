Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.

Lemma rearrange_aux:
 forall h f c k l,
 Int.add (Int.add (Int.add (Int.add h f) c) k) l =
Int.add (Int.add (Int.add (Int.add l h) f) c) k.
Proof.
intros.
rewrite <- (Int.add_commut l).
repeat rewrite (Int.add_assoc h).
rewrite <- (Int.add_assoc l).
repeat rewrite (Int.add_assoc (Int.add l h)).
reflexivity.
Qed.

Lemma force_lengthn_same:
  forall {A} i (b: list A) v, 
     i = length b -> force_lengthn i b v = b.
Proof.
intros.
subst.
induction b; simpl; auto. f_equal; auto.
Qed.

Lemma loop1_aux_lemma1:
  forall i v b,
  (i < Zlength b) ->
  0 <= i * 4 <= Int.max_unsigned ->
  v = nthi b i ->
  upd_reptype_array tuint i (map Vint (firstn (Z.to_nat i) b))
          (Vint v)
  =  map Vint (firstn (Z.to_nat (i+1)) b).
Proof.
intros.
assert (Z.to_nat i < length b)%nat.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega. rewrite <- Zlength_correct; auto.
unfold upd_reptype_array.
repeat rewrite Z2Nat.inj_add by omega.
change (Z.to_nat 1) with 1%nat.
replace (Z.to_nat i +1)%nat with (S (Z.to_nat i)) by (clear; omega).
rewrite force_lengthn_same
  by (rewrite map_length, firstn_length, min_l; auto; omega).
subst v.
replace (nthi b i) with (nthi b (Z.of_nat (Z.to_nat i)))
 by (rewrite Z2Nat.id by omega; auto).
clear H0 H. rename H2 into H.
revert b H.
induction (Z.to_nat i); destruct b; simpl length; intros; try omega.
reflexivity.
clear i; rename n into i.
simpl map at 1.
change (map Vint (firstn (S (S i)) (i0 :: b)))
  with (Vint i0 :: map Vint (firstn (S i) b)).
rewrite <- app_comm_cons.
f_equal.
replace (nthi (i0::b) (Z.of_nat (S i))) with  (nthi b (Z.of_nat i)).
change (skipn (S (S i)) (map Vint (firstn (S i) (i0 :: b))))
 with (skipn (S i) (map Vint (firstn i b))).
apply IHn.
omega.
unfold nthi.
repeat rewrite Nat2Z.id. reflexivity.
Qed.

Lemma semax_call_id1'':
 forall Espec Delta P Q R ret id retty bl argsig A x Pre Post fs tl
   (GLBL: (var_types Delta) ! id = None),
       (glob_specs Delta) ! id = Some fs ->
       (glob_types Delta) ! id = Some (type_of_funspec fs) ->
   fs = mk_funspec (argsig, retty) A Pre Post ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
   tc_fn_return Delta (Some ret) retty ->
   tl = type_of_params argsig ->
  forall 
   (CLOSQ: Forall (closed_wrt_vars (eq ret)) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret)) R),
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q)
            (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction tl retty cc_default))
             bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q   (SEPx (`(Post x) (get_result1 ret) ::  R))))).
Proof.
intros; subst  fs tl; eapply semax_call_id1'; eauto.
Qed.

Lemma read32_reversed_in_bytearray:
 forall {Espec: OracleKind} Delta (ofs: int) base e sh (contents: list int) i P Q
 (VS:  (var_types Delta) ! ___builtin_read32_reversed = None) 
 (GS: (glob_specs Delta) ! ___builtin_read32_reversed =
    Some (snd __builtin_read32_reversed_spec))
 (GT: (glob_types Delta) ! ___builtin_read32_reversed =
    Some (type_of_funspec (snd __builtin_read32_reversed_spec)))
 (TE: typeof e = tptr tuint)
 (TCi:  tc_fn_return Delta (Some i) tuint)
 (CLOQ: Forall (closed_wrt_vars (eq i)) Q),
 PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- 
         PROP ((0 <= Int.unsigned ofs <= Zlength contents - 4 )%Z)
         LOCAL (tc_expr Delta e; `(eq (offset_val ofs base)) (eval_expr e))
         SEP  (TT) ->
 semax Delta  (PROPx P (LOCALx Q 
                        (SEP (`(data_at sh (tarray tuchar (Zlength contents)) 
                                    (map Vint contents) base)))))
        (Scall (Some i)
           (Evar ___builtin_read32_reversed
              (Tfunction (Tcons (tptr tuint) Tnil) tuint cc_default))
           [e])
        (normal_ret_assert
         (PROP () 
          (LOCALx (temp i (Vint (big_endian_integer
                               (firstn (Z.to_nat WORD) (skipn (Z.to_nat (Int.unsigned ofs)) contents))))
                        :: Q)                 
         SEP (`(data_at sh (tarray tuchar (Zlength contents)) (map Vint contents) base))))).
Proof.
intros.
apply semax_pre with
 (PROP  ((0 <= Int.unsigned ofs <= Zlength contents - 4)%Z;
             field_compatible (tarray tuchar (Zlength contents))
                 [ArraySubsc (Int.unsigned ofs)] base)
        (LOCALx (tc_expr Delta e :: `(eq (offset_val ofs base)) (eval_expr e) :: Q)
         (SEP(`(data_at sh (tarray tuchar (Zlength contents)) (map Vint contents)
             base))))).
rewrite <- (andp_dup (PROPx P _)).
eapply derives_trans; [ apply andp_derives | ].
eapply derives_trans; [ | apply H].
apply andp_derives; auto.
apply andp_derives; auto.
go_lowerx.
apply sepcon_derives; auto.
apply TT_right.
instantiate (1:= PROPx nil (LOCALx Q (SEP  (`(data_at sh (tarray tuchar (Zlength contents)) (map Vint contents)
             base))))).
go_lowerx. entailer.
go_lowerx. entailer.
apply prop_right.
eapply field_compatible_cons_Tarray; eauto.
reflexivity. omega.
normalize.
clear H. rename H1 into COMPAT.
rewrite data_at_field_at.

erewrite (array_seg_reroot_lemma sh (tarray tuchar (Zlength contents)) 
               nil tuchar (Zlength contents) noattr
                (Int.unsigned ofs) (Int.unsigned ofs + 4)
     (firstn (Z.to_nat (Int.unsigned ofs)) (map Vint contents))
     (firstn 4 (skipn (Z.to_nat (Int.unsigned ofs)) (map Vint contents)))
     (skipn (Z.to_nat (Int.unsigned ofs+ 4)) (map Vint contents))
); try reflexivity; auto; try omega.

2: rewrite Z2Nat.inj_add, <- !skipn_skipn, !firstn_skipn by omega; reflexivity.
Focus 2.
rewrite Zlength_correct, firstn_length, min_l.
rewrite Z2Nat.id by omega; omega.
rewrite map_length. apply Nat2Z.inj_le. rewrite Z2Nat.id by omega.
rewrite <- Zlength_correct; omega.
Focus 2.
rewrite Zlength_correct, firstn_length, min_l.
change (Z.of_nat 4) with 4; omega.
rewrite skipn_length. rewrite map_length.
apply Nat2Z.inj_le. 
rewrite Nat2Z.inj_sub.
rewrite <- Zlength_correct. rewrite Z2Nat.id by omega.
change (Z.of_nat 4) with 4; omega.
apply Nat2Z.inj_le. 
rewrite <- Zlength_correct. rewrite Z2Nat.id by omega.
omega.
normalize.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q  (SEP (?A; ?B; ?C)))) _ _ =>
eapply semax_pre_post;
 [ | | eapply (semax_frame1 nil [A;C]); try reflexivity ]
end.
apply andp_left2; apply derives_refl.
intros; apply andp_left2.
apply normal_ret_assert_derives'.
match goal with |- _ |-- PROP() (LOCALx ?Q (SEP ( _ ; ?B; _))) =>
   instantiate (1:=[B]);
   instantiate (1:=Q);
   instantiate (1:=nil)
end.
rewrite <- app_nil_end. entailer!.

Focus 2.
drop_LOCAL 0%nat.
match goal with |-  PROP() (LOCALx ?Q (SEP ( _ ; ?B; _))) |-- _ =>
   instantiate (1:=[B]);
   instantiate (1:=Q);
   instantiate (1:=nil)
end.
rewrite <- app_nil_end. entailer!.
2: auto 50 with closed.

replace (Int.unsigned ofs + 4 - Int.unsigned ofs) with 4 by omega.

pose (witness := 
            (offset_val ofs base, sh, 
             firstn 4 (skipn (Z.to_nat (Int.unsigned ofs)) contents))).

eapply semax_pre;
 [ | eapply semax_post'; 
     [ | eapply semax_call_id1'' with (x := witness); 
         try eassumption; try reflexivity; auto ]].
instantiate (1:=nil).
unfold witness.
rewrite skipn_map, firstn_map.
set (cts := firstn 4 (skipn (Z.to_nat (Int.unsigned ofs)) contents)).
rewrite data_at_isptr.
go_lowerx.
normalize.
rewrite prop_true_andp; auto.
rewrite field_address0_clarify; auto.
erewrite nested_field_offset2_Tarray; try reflexivity.
change (nested_field_offset2 (tarray tuchar (Zlength contents)) []) with 0%Z.
rewrite Z.add_0_l.
normalize.
rewrite Int.repr_unsigned.
apply derives_refl.
repeat split; auto.
hnf;  simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite TE; simpl. apply I.
unfold cts.
rewrite Zlength_correct.
rewrite firstn_length, min_l.
compute; clear; congruence.
rewrite skipn_length. 
clear - H0.
apply Nat2Z.inj_le.
rewrite Nat2Z.inj_sub.
rewrite <- Zlength_correct. change (Z.of_nat 4) with 4.
rewrite Z2Nat.id by omega. omega.
apply Nat2Z.inj_le.
rewrite Z2Nat.id by omega. 
rewrite <- Zlength_correct. omega.
hnf. rewrite TE. rewrite <- H3.
unfold eval_id, env_set. simpl.
clear - H5.
unfold field_address0 in H5.
if_tac in H5; try contradiction.
destruct base; try contradiction H5.
reflexivity.

unfold witness.
change (Z.to_nat WORD) with 4%nat.
rewrite skipn_map, firstn_map.
set (cts :=  firstn 4 (skipn (Z.to_nat (Int.unsigned ofs)) contents)).
fold (tarray tuchar 4).
normalize.
rewrite data_at_isptr.
go_lowerx.
normalize.
rewrite fold_right_and_app_lifted in H1.
destruct H1 as [? [? ?]].
rewrite prop_true_andp.
unfold field_address0.
rewrite if_true by (apply field_compatible_field_compatible0; auto).
erewrite nested_field_offset2_Tarray; try reflexivity.
change (nested_field_offset2 (tarray tuchar (Zlength contents)) []) with 0%Z.
rewrite Z.add_0_l.
normalize.
rewrite Int.repr_unsigned by omega.
 auto.
split; auto.
Qed.

Definition block_data_order_loop1 := 
  Sfor (Sset _i (Econst_int (Int.repr 0) tint))
         (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr 16) tint) tint)
         (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _l')
                                  (Evar ___builtin_read32_reversed (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)
                                                                    tuint
                                                                    cc_default))
                                  ((Ecast (Etempvar _data (tptr tuchar))
                                     (tptr tuint)) :: nil))
                 (Sset _l (Ecast (Etempvar _l' tuint) tuint)))
                (Sset _data
                    (Ebinop Oadd (Etempvar _data (tptr tuchar))
                        (Econst_int (Int.repr 4) tint)
                                  (tptr tuchar))))
                          (Ssequence
                              (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _X (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint)
                      (Etempvar _l tuint))
                    (Ssequence
                      (Sset _Ki
                        (Ederef
                          (Ebinop Oadd
                            (Evar _K256 (tarray tuint 64))
                            (Etempvar _i tint) (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _T1
                          (Ebinop Oadd
                            (Ebinop Oadd
                              (Ebinop Oadd
                                (Ebinop Oadd (Etempvar _l tuint)
                                  (Etempvar _h tuint) tuint)
                                (Ebinop Oxor
                                  (Ebinop Oxor
                                    (Ebinop Oor
                                      (Ebinop Oshl
                                        (Etempvar _e tuint)
                                        (Econst_int (Int.repr 26) tint)
                                        tuint)
                                      (Ebinop Oshr
                                        (Ebinop Oand
                                          (Etempvar _e tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 32) tint)
                                          (Econst_int (Int.repr 26) tint)
                                          tint) tuint) tuint)
                                    (Ebinop Oor
                                      (Ebinop Oshl
                                        (Etempvar _e tuint)
                                        (Econst_int (Int.repr 21) tint)
                                        tuint)
                                      (Ebinop Oshr
                                        (Ebinop Oand
                                          (Etempvar _e tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 32) tint)
                                          (Econst_int (Int.repr 21) tint)
                                          tint) tuint) tuint)
                                    tuint)
                                  (Ebinop Oor
                                    (Ebinop Oshl
                                      (Etempvar _e tuint)
                                      (Econst_int (Int.repr 7) tint)
                                      tuint)
                                    (Ebinop Oshr
                                      (Ebinop Oand
                                        (Etempvar _e tuint)
                                        (Econst_int (Int.repr (-1)) tuint)
                                        tuint)
                                      (Ebinop Osub
                                        (Econst_int (Int.repr 32) tint)
                                        (Econst_int (Int.repr 7) tint)
                                        tint) tuint) tuint) tuint)
                                tuint)
                              (Ebinop Oxor
                                (Ebinop Oand (Etempvar _e tuint)
                                  (Etempvar _f tuint) tuint)
                                (Ebinop Oand
                                  (Eunop Onotint
                                    (Etempvar _e tuint) tuint)
                                  (Etempvar _g tuint) tuint) tuint)
                              tuint) (Etempvar _Ki tuint) tuint))
                        (Ssequence
                          (Sset _T2
                            (Ebinop Oadd
                              (Ebinop Oxor
                                (Ebinop Oxor
                                  (Ebinop Oor
                                    (Ebinop Oshl
                                      (Etempvar _a tuint)
                                      (Econst_int (Int.repr 30) tint)
                                      tuint)
                                    (Ebinop Oshr
                                      (Ebinop Oand
                                        (Etempvar _a tuint)
                                        (Econst_int (Int.repr (-1)) tuint)
                                        tuint)
                                      (Ebinop Osub
                                        (Econst_int (Int.repr 32) tint)
                                        (Econst_int (Int.repr 30) tint)
                                        tint) tuint) tuint)
                                  (Ebinop Oor
                                    (Ebinop Oshl
                                      (Etempvar _a tuint)
                                      (Econst_int (Int.repr 19) tint)
                                      tuint)
                                    (Ebinop Oshr
                                      (Ebinop Oand
                                        (Etempvar _a tuint)
                                        (Econst_int (Int.repr (-1)) tuint)
                                        tuint)
                                      (Ebinop Osub
                                        (Econst_int (Int.repr 32) tint)
                                        (Econst_int (Int.repr 19) tint)
                                        tint) tuint) tuint) tuint)
                                (Ebinop Oor
                                  (Ebinop Oshl (Etempvar _a tuint)
                                    (Econst_int (Int.repr 10) tint)
                                    tuint)
                                  (Ebinop Oshr
                                    (Ebinop Oand
                                      (Etempvar _a tuint)
                                      (Econst_int (Int.repr (-1)) tuint)
                                      tuint)
                                    (Ebinop Osub
                                      (Econst_int (Int.repr 32) tint)
                                      (Econst_int (Int.repr 10) tint)
                                      tint) tuint) tuint) tuint)
                              (Ebinop Oxor
                                (Ebinop Oxor
                                  (Ebinop Oand (Etempvar _a tuint)
                                    (Etempvar _b tuint) tuint)
                                  (Ebinop Oand (Etempvar _a tuint)
                                    (Etempvar _c tuint) tuint)
                                  tuint)
                                (Ebinop Oand (Etempvar _b tuint)
                                  (Etempvar _c tuint) tuint) tuint)
                              tuint))
                          (Ssequence
                            (Sset _h (Etempvar _g tuint))
                            (Ssequence
                              (Sset _g (Etempvar _f tuint))
                              (Ssequence
                                (Sset _f (Etempvar _e tuint))
                                (Ssequence
                                  (Sset _e
                                    (Ebinop Oadd
                                      (Etempvar _d tuint)
                                      (Etempvar _T1 tuint) tuint))
                                  (Ssequence
                                    (Sset _d (Etempvar _c tuint))
                                    (Ssequence
                                      (Sset _c (Etempvar _b tuint))
                                      (Ssequence
                                        (Sset _b
                                          (Etempvar _a tuint))
                                        (Sset _a
                                          (Ebinop Oadd
                                            (Etempvar _T1 tuint)
                                            (Etempvar _T2 tuint)
                                            tuint))))))))))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint)).

(*Definition block_data_order_loop1 := 
   nth 0 (loops (fn_body f_sha256_block_data_order)) Sskip.
*)

Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind) (sh: share)
     (b: list int) ctx (data: val) (regs: list int) kv Xv
     (Hregs: length regs = 8%nat)
     (Hdata: isptr data),
     length b = LBLOCK ->
     semax Delta_loop1
  (PROP ()
   LOCAL (temp _ctx ctx; temp _data data;
               temp _a (Vint (nthi regs 0)); 
               temp _b (Vint (nthi regs 1)); 
               temp _c (Vint (nthi regs 2)); 
               temp _d (Vint (nthi regs 3)); 
               temp _e (Vint (nthi regs 4)); 
               temp _f (Vint (nthi regs 5)); 
               temp _g (Vint (nthi regs 6)); 
               temp _h (Vint (nthi regs 7)); 
               lvar _X (tarray tuint LBLOCKz) Xv;
               gvar _K256 kv)
   SEP ( `(K_vector kv);
           `(data_at_ Tsh (tarray tuint LBLOCKz) Xv);
           `(data_block sh (intlist_to_Zlist b) data)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(temp _ctx ctx; temp _i (Vint (Int.repr LBLOCKz));
                temp _a (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 0));
                temp _b (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 1));
                temp _c (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 2));
                temp _d (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 3));
                temp _e (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 4));
                temp _f (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 5));
                temp _g (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 6));
                temp _h (Vint (nthi (Round regs (nthi b) (LBLOCKz - 1)) 7));
                lvar _X (tarray tuint LBLOCKz) Xv;
                gvar _K256 kv)
     SEP (`(K_vector kv);
           `(data_at Tsh (tarray tuint LBLOCKz) (map Vint b) Xv);
           `(data_block sh (intlist_to_Zlist b) data))) ).
Proof. {
unfold block_data_order_loop1.
intros.
simpl nth; fold rearrange_regs.
abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name l'_ _l'.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
assert (LBE := LBLOCK_zeq).

forward_for_simple_bound 16
   (EX i:Z,
    PROP ( (i <= LBLOCKz) )
    LOCAL  (temp _ctx ctx;
                 temp _data  (offset_val (Int.repr (i*4)) data);
                 temp _a (Vint (nthi (Round regs (nthi b) (i - 1)) 0));
                 temp _b (Vint (nthi (Round regs (nthi b) (i - 1)) 1));
                 temp _c (Vint (nthi (Round regs (nthi b) (i - 1)) 2));
                 temp _d (Vint (nthi (Round regs (nthi b) (i - 1)) 3));
                 temp _e (Vint (nthi (Round regs (nthi b) (i - 1)) 4));
                 temp _f (Vint (nthi (Round regs (nthi b) (i - 1)) 5));
                 temp _g (Vint (nthi (Round regs (nthi b) (i - 1)) 6));
                 temp _h (Vint (nthi (Round regs (nthi b) (i - 1)) 7));
                 lvar _X (tarray tuint LBLOCKz) Xv;
                 gvar _K256 kv)
     SEP (`(K_vector kv);
       `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (firstn (Z.to_nat i) b)) Xv);
   `(data_block sh (intlist_to_Zlist b) data))).
{
 replace (Round regs (nthi b) (0 - 1)) with regs.
 entailer!.
 rewrite Round_equation. rewrite if_true by (compute; auto). auto.
}
{
 normalize.

(* 945,760 834,556 *)
do 2 apply -> seq_assoc.
unfold data_block.
eapply (semax_frame_seq nil)
 with (P1 := [])
         (Q1 :=  [temp _ctx ctx; temp _i (Vint (Int.repr i));
                      temp _data (offset_val (Int.repr (i * 4)) data);
                 temp _a (Vint (nthi (Round regs (nthi b) (i - 1)) 0));
                 temp _b (Vint (nthi (Round regs (nthi b) (i - 1)) 1));
                 temp _c (Vint (nthi (Round regs (nthi b) (i - 1)) 2));
                 temp _d (Vint (nthi (Round regs (nthi b) (i - 1)) 3));
                 temp _e (Vint (nthi (Round regs (nthi b) (i - 1)) 4));
                 temp _f (Vint (nthi (Round regs (nthi b) (i - 1)) 5));
                 temp _g (Vint (nthi (Round regs (nthi b) (i - 1)) 6));
                 temp _h (Vint (nthi (Round regs (nthi b) (i - 1)) 7));
                 lvar _X (tarray tuint LBLOCKz) Xv;
                 gvar _K256 kv])
         (Frame := [`(K_vector kv);
                           `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (firstn (Z.to_nat i) b)) Xv)]);
   [apply (read32_reversed_in_bytearray _ (Int.repr (i * 4)) data _ sh 
                     (map Int.repr (intlist_to_Zlist b)));
    [ reflexivity |  reflexivity | reflexivity | reflexivity | reflexivity
    | auto 50 with closed 
      (* intros; apply ZnthV_map_Vint_is_int; rewrite Zlength_correct, map_length;
          rewrite Zlength_correct in H1; apply H1 *)
      | ]
   | | auto 50 with closed | ].
(* 945,760 834,556 *)
abstract solve [entailer!;
rewrite Zlength_correct, map_length, length_intlist_to_Zlist, H;
 replace (Z.of_nat (4 * LBLOCK) - 4)%Z
  with ((Z.of_nat LBLOCK - 1) * 4)%Z; 
    [apply Zmult_le_compat_r; omega | ];
 rewrite Zmult_comm;
 rewrite Z.mul_sub_distr_l;
 reflexivity].
(* 990,216 849,172 *)
simpl app.
unfold data_block.
rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
abstract solve [rewrite Zlength_map; entailer!].
(* 1,078,128 849,172 *)
unfold app.
fold (data_block sh (intlist_to_Zlist b) data).
set (bei :=  big_endian_integer
            (firstn (Z.to_nat WORD)
               (skipn (Z.to_nat (Int.unsigned (Int.repr (i * 4))))
                  (map Int.repr (intlist_to_Zlist b))))).
forward. (* l := l'; *)
forward data_old. (* data := data + 4; *)
(* 1,194,800 849,172 *)
normalize.
(* 1,291,784 894,136 *)
change LBLOCKz with 16. (* this shouldn't be necessary *)
forward. (* X[i]=l; *)
change 16 with LBLOCKz.

 assert_PROP (bei = nthi b i). {
  entailer!.
  unfold nthi.
  rewrite Z2Nat.inj_mul by omega.
  symmetry.
  apply nth_big_endian_integer. 
  apply nth_error_nth; rewrite H; auto.
  apply Z2Nat.inj_lt; try omega. apply H0.
 }
 rewrite H3.
 clear bei H3.
 
change LBLOCKz with (Z.of_nat LBLOCK).

assert (Hi: 0 <= i * 4 <= Int.max_unsigned). {
   clear - H0;
   assert (0 <= i * 4 < 64); [split; [omega |] | repable_signed ];
   change 64 with (Z.of_nat LBLOCK *4)%Z;
   apply Zmult_lt_compat_r; [computable | ];
   (*apply Nat2Z.inj_lt;*) auto.
   apply H0.
}

set (zz := (big_endian_integer
                   (firstn (Z.to_nat WORD)
                      (skipn
                         (Z.to_nat (Int.unsigned (Int.repr (i * 4))))
                         (map Int.repr (intlist_to_Zlist b)))))).
simpl.
subst zz.
rewrite loop1_aux_lemma1; auto;
[ | rewrite Zlength_correct, H; omega].
(* 1,506,948 1,110,852 *)
(* 1,506,948 1,134,576 *)

unfold K_vector.

assert (i < Zlength K256)
  by (change (Zlength K256) with (LBLOCKz + 48); omega).
  change (Zlength K256) with 64 in *.
  change (Z.of_nat LBLOCK) with 16. change CBLOCKz with 64.
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)
entailer!.
unfold Znth. rewrite if_false by omega.
rewrite (nth_map' Vint Vundef Int.zero). apply I.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
change (Z.of_nat (length K256)) with (LBLOCKz  + 48); omega.
(* 1,811,028 1,406,332 *)
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.

match goal with 
  |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ 
       (normal_ret_assert (PROPx ?P (LOCALx ?Q _)))
 => eapply semax_post';
  [ | eapply (semax_frame1 nil R) with (P2:=P) (Q2:=Q) (R1:=nil)(R2:=nil);
    try reflexivity; auto 50 with closed;
   [ | rewrite <- app_nil_end; apply derives_refl]
   ]
end.
 entailer!.
 unfold data_block.
 rewrite prop_true_andp by (apply isbyte_intlist_to_Zlist).
 rewrite Zlength_map. auto.

(* 1,811,028 1,429,048 *)
forget (nthi b) as M.
apply semax_pre with
 (PROP  ()
   LOCAL 
   (temp _ctx ctx; temp _data (offset_val (Int.repr (Zsucc i * WORD)) data);
    temp _l (Vint (W M i)); temp _Ki (Vint (nthi K256 i));
    temp _i (Vint (Int.repr i));
                 temp _a (Vint (nthi (Round regs M (i - 1)) 0));
                 temp _b (Vint (nthi (Round regs M (i - 1)) 1));
                 temp _c (Vint (nthi (Round regs M (i - 1)) 2));
                 temp _d (Vint (nthi (Round regs M (i - 1)) 3));
                 temp _e (Vint (nthi (Round regs M (i - 1)) 4));
                 temp _f (Vint (nthi (Round regs M (i - 1)) 5));
                 temp _g (Vint (nthi (Round regs M (i - 1)) 6));
                 temp _h (Vint (nthi (Round regs M (i - 1)) 7));
                 lvar _X (tarray tuint 16) Xv; 
                 gvar _K256 kv)
   SEP()).
{ 
entailer!.
*
 f_equal. f_equal. unfold Z.succ; rewrite Z.mul_add_distr_r; reflexivity.
*
 rewrite W_equation. rewrite if_true; auto. omega.
* 
 clear - H0 H5. rename H5 into H2. unfold Znth in H2.
 rewrite if_false in H2 by omega.
 unfold nthi.
 rewrite (nth_map' _ _ Int.zero) in H2.
 congruence.
 clear H2.
 change (length K256) with 64%nat.
 apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega. 
change (Z.of_nat 64) with 64. omega.
}
{clear b H.
replace (i + 1 - 1)%Z with i by omega.
rewrite (Round_equation _ _ i).
rewrite if_false by omega.
forget (nthi K256 i) as k.
forget (W M i) as w.
assert (length (Round regs M (i - 1)) = 8)%nat.
apply length_Round; auto.
forget (Round regs M (i - 1)) as regs'.
change 16%nat with LBLOCK.
destruct regs' as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; inv H.
unfold rearrange_regs.
abbreviate_semax.
forward. (* T1 = l + h + Sigma1(e) + Ch(e,f,g) + Ki; *)
rewrite <- Sigma_1_eq, <- Ch_eq, rearrange_aux.
forward. (* T2 = Sigma0(a) + Maj(a,b,c); *)
 rewrite <- Sigma_0_eq, <- Maj_eq.
forward h_old.
forward g_old.
forward f_old.
forward e_old.
forward d_old.
forward c_old.
forward b_old.
forward a_old.
simplify_Delta.
 entailer!. 
 clear - H0. change LBLOCKz with 16. omega.
unfold rnd_function, nthi; simpl.
f_equal.
 rewrite <- rearrange_aux. symmetry. rewrite (rearrange_aux Ki).
rewrite Int.add_commut.
repeat rewrite Int.add_assoc. reflexivity.
unfold rnd_function, nthi; simpl.
f_equal.
symmetry. do 2 rewrite Int.add_assoc.
rewrite Int.add_commut. rewrite <- Int.add_assoc. f_equal.
f_equal. rewrite Int.add_assoc. reflexivity.
}
}

drop_LOCAL 1%nat.
change 16 with LBLOCKz.
entailer!.
rewrite firstn_same. auto.
rewrite H. change (Z.to_nat LBLOCKz) with LBLOCK. clear; omega.
}
Qed.
