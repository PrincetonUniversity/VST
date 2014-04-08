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

Local Open Scope nat.

Definition Delta_rearrange_aux2 : tycontext.
simplify_Delta_from
 (initialized _Ki (initialized _l (initialized _l' Delta_loop1))).
Defined.
Lemma rearrange_aux2: 
forall (Espec : OracleKind) (i : nat)(w k : int) ctx
      (a b c d e f g h : int) (eqofs : val -> Prop)
      atoh,
   i < 16 ->
  atoh = nthi (rnd_function [a, b, c, d, e, f, g, h] k w) ->
semax Delta_rearrange_aux2
  (PROP  ()
   LOCAL  (`(eq ctx) (eval_id _ctx);
   `eqofs (eval_id _data); `(eq (Vint w)) (eval_id _l);
   `(eq (Vint k)) (eval_id _Ki);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint a)) (eval_id _a);
   `(eq (Vint b)) (eval_id _b);
   `(eq (Vint c)) (eval_id _c);
   `(eq (Vint d)) (eval_id _d);
   `(eq (Vint e)) (eval_id _e);
   `(eq (Vint f)) (eval_id _f);
   `(eq (Vint g)) (eval_id _g);
   `(eq (Vint h)) (eval_id _h))
   SEP())
 rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
      `eqofs (eval_id _data);
      `(eq (Vint (atoh 0%Z))) (eval_id _a);
      `(eq (Vint (atoh 1%Z))) (eval_id _b);
      `(eq (Vint (atoh 2%Z))) (eval_id _c);
      `(eq (Vint (atoh 3%Z))) (eval_id _d);
      `(eq (Vint (atoh 4%Z))) (eval_id _e);
      `(eq (Vint (atoh 5%Z))) (eval_id _f);
      `(eq (Vint (atoh 6%Z))) (eval_id _g);
      `(eq (Vint (atoh 7%Z))) (eval_id _h))
       SEP())).
Proof.
{
intros. rename H0 into Hah.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name i_ _i.
name T1 _T1.
name T2 _T2.
name data_ _data.
name ctx_ _ctx.
simplify_Delta; abbreviate_semax.
unfold rearrange_regs.
forward. (* T1 += h + Sigma1(e) + Ch(e,f,g) + Ki; *)
assert_LOCAL 
  (`(eq (Vint (Int.add (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) k) w)))
                         (eval_id _T1)). {
 entailer!.  
 rewrite <- Sigma_1_eq, <- Ch_eq, rearrange_aux.  auto.
}
drop_LOCAL 1.
forward. (* T1 += h + Sigma1(e) + Ch(e,f,g) + Ki; *)
assert_LOCAL 
  (`(eq (Vint (Int.add (Sigma_0 a) (Maj a b c))))  (eval_id _T2)). {
 entailer!.  
 rewrite <- Sigma_0_eq, <- Maj_eq. auto.
}
drop_LOCAL 1.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
(* 1,577,248    1,732,160 *)
simplify_Delta.
 entailer!.
(* 871,496    1,685,788    1,743,816  ;   without the computational closedness: 1,913,256 *)
} Admitted. (* this proof works, but once took over 2 gigabytes  *)

Lemma rearrange_regs_proof:
 forall (Espec: OracleKind) i (data: val) M regs ctx
 (Hdata: isptr data)
 (H: length regs = 8)
 (H0: i < 16), 
 semax Delta_rearrange_aux2
  (PROP  ()
   LOCAL 
   (`(eq ctx) (eval_id _ctx);
   `(eq (offset_val (Int.repr (Zsucc (Z.of_nat i) * 4)) data)) (eval_id _data);
   `(eq (Vint (W M (Z.of_nat i))))  (eval_id _l);
   `(eq (Vint (nthi K (Z.of_nat i)))) (eval_id _Ki);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 0))) (eval_id _a);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 1))) (eval_id _b);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 2))) (eval_id _c);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 3))) (eval_id _d);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 4))) (eval_id _e);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 5))) (eval_id _f);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 6))) (eval_id _g);
   `(eq (Vint (nthi (Round regs M (Z.of_nat i - 1)) 7))) (eval_id _h))
   SEP()) rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.succ (Z.of_nat i) - 1)))) (eval_id _i);
      `(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) (eval_id _data);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 0))) (eval_id _a);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 1))) (eval_id _b);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 2))) (eval_id _c);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 3))) (eval_id _d);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 4))) (eval_id _e);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 5))) (eval_id _f);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 6))) (eval_id _g);
      `(eq (Vint (nthi (Round regs M (Z.succ (Z.of_nat i) - 1)) 7))) (eval_id _h))
        SEP())).
Proof.
intros.
replace (Z.succ (Z.of_nat i) - 1)%Z with (Z.of_nat i) by omega.
rewrite (Round_equation _ _ (Z.of_nat i)).
rewrite if_false by omega.
forget (nthi K (Z.of_nat i)) as k.
forget (W M (Z.of_nat i)) as w.
assert (length (Round regs M (Z.of_nat i - 1)) = 8).
apply length_Round; auto.
forget (Round regs M (Z.of_nat i - 1)) as regs'.
change 16 with LBLOCK.
destruct regs' as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; inv H1.
apply (rearrange_aux2 _ i w k ctx a b c d e f g h); auto.
Qed.

Lemma loop1_aux_lemma1:
forall sh b i N,
  length b = N ->
  i < N ->
 array_at tuint sh
       (upd (f_upto (tuints b) (Z.of_nat i)) (Z.of_nat i)
          (Vint
             (big_endian_integer
                (fun z : Z =>
                 force_int
                   (tuchars (map Int.repr (intlist_to_Zlist b))
                      (z + Z.of_nat i * 4))))))
        0 (Z.of_nat N) =
  array_at tuint sh
               (f_upto (tuints b) (Z.of_nat (S i))) 
              0 (Z.of_nat N).
Proof.
intros.
apply array_at_ext; intros.
unfold upd.
if_tac.
assert (exists w, nth_error b i = Some w).
subst N.
clear - H0.
revert b H0; induction i; destruct b; simpl; intros; auto.
omega.
exists i; reflexivity. 
inv H0.
apply IHi; auto. clear - H0.
apply lt_S_n; auto.
destruct H3 as [w H3].
unfold tuchars;
rewrite <- nth_big_endian_integer with (w:=w); auto.
unfold f_upto.
subst.
rewrite if_true by (rewrite inj_S; omega).
unfold tuints, ZnthV. rewrite if_false by omega. rewrite Nat2Z.id.
clear - H3; revert b H3; induction i; destruct b; intros; inv H3; simpl; auto.
unfold f_upto.
if_tac. rewrite if_true by (rewrite inj_S; omega); auto.
rewrite if_false; auto.
rewrite inj_S; 
omega.
Qed.

Lemma read32_reversed_in_bytearray:
 forall {Espec: OracleKind} Delta (ofs: int) (lo hi: Z) base e sh (contents: Z -> val) i P Q
 (VS:  (var_types Delta) ! ___builtin_read32_reversed = None) 
 (GS: (glob_types Delta) ! ___builtin_read32_reversed =
    Some (Global_func (snd __builtin_read32_reversed_spec)))
 (TE: typeof e = tptr tuint)
 (CLOQ: Forall (closed_wrt_vars (eq i)) Q)
 (Hcontents: forall i, (lo <= i < hi)%Z -> is_int (contents i)),
 PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- PROP ((lo <= Int.unsigned ofs <= hi-4 )%Z)
         LOCAL (tc_expr Delta e; `(eq (offset_val ofs base)) (eval_expr e))
         SEP  (TT) ->
 semax Delta  (PROPx P (LOCALx Q (SEP (`(array_at tuchar sh contents lo hi base)))))
        (Scall (Some i)
           (Evar ___builtin_read32_reversed
              (Tfunction (Tcons (tptr tuint) Tnil) tuint))
           [e])
        (normal_ret_assert
         (PROP () 
         (LOCALx (`(eq (Vint (big_endian_integer (fun z => force_int (contents (z+Int.unsigned ofs)%Z))))) (eval_id i)
                        :: Q)                 
         SEP (`(array_at tuchar sh contents lo hi base))))).
Proof.
intros.
apply semax_pre with
 (PROP  ((lo <= Int.unsigned ofs <= hi - 4)%Z)
        (LOCALx (tc_expr Delta e :: `(eq (offset_val ofs base)) (eval_expr e) :: Q)
         (SEP(`(array_at tuchar sh contents lo hi base))))).
rewrite <- (andp_dup (PROPx P _)).
eapply derives_trans; [ apply andp_derives | ].
eapply derives_trans; [ | apply H].
apply andp_derives; auto.
apply andp_derives; auto.
go_lowerx.
apply sepcon_derives; auto.
apply TT_right.
instantiate (1:= PROPx nil (LOCALx Q (SEP  (`(array_at tuchar sh contents lo hi base))))).
go_lowerx. entailer.
go_lowerx; entailer.
normalize.
clear H.
normalize.
rewrite (split_array_at (Int.unsigned ofs)) by omega.
rewrite (split_array_at (Int.unsigned ofs + 4)%Z) with (hi:=hi) by omega.
normalize.
match goal with |- semax _ (PROPx _ (LOCALx _ ?A)) _ _ =>
 replace A  with (SEPx( [
         `(array_at tuchar sh contents (Int.unsigned ofs)
             (Int.unsigned ofs + 4) base)] ++
               [`(array_at tuchar sh contents lo (Int.unsigned ofs) base),
         `(array_at tuchar sh contents (Int.unsigned ofs + 4) hi base)]))
 by (simpl app; apply pred_ext; go_lowerx; cancel)
end.
eapply semax_frame1; try reflexivity;
 [ |  apply derives_refl | auto 50 with closed].
eapply semax_pre_post.
Focus 3.
evar (tl: typelist).
replace (Tcons (tptr tuint) Tnil) with tl.
unfold tl.
eapply semax_call_id1'; try eassumption.
2: reflexivity.
apply GS.
2: reflexivity.
Unfocus.
instantiate (3:=nil).
apply andp_left2.
instantiate (2:=(offset_val ofs base, sh, fun z => force_int (contents (z + Int.unsigned ofs)%Z))).
cbv beta iota.
instantiate (1:=nil).
unfold split; simpl @snd.
go_lowerx.
entailer.
apply andp_right; [apply prop_right; repeat split; auto | ].
hnf. simpl.
rewrite TE.
repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite <- H3.
rewrite TE.
destruct base; inv Pbase; reflexivity.
pattern ofs at 4;
 replace ofs with (Int.repr (sizeof tuchar * Int.unsigned ofs))%Z
 by (simpl sizeof; rewrite Z.mul_1_l; apply Int.repr_unsigned).
rewrite <- offset_val_array_at.
apply derives_refl'.
apply equal_f. rewrite Z.add_0_r. apply array_at_ext.
intros. unfold cVint. rewrite Z.sub_add.
clear - H5 H0 Hcontents.
specialize (Hcontents i0);
 destruct (contents i0); 
  try solve [elimtype False; apply Hcontents; omega]. reflexivity.
2: auto with closed.
intros; apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx.
entailer.
apply derives_refl'.
pattern ofs at 2;
 replace ofs with (Int.repr (sizeof tuchar * Int.unsigned ofs))%Z
 by (simpl sizeof; rewrite Z.mul_1_l; apply Int.repr_unsigned).
rewrite <- offset_val_array_at.
apply equal_f. rewrite Z.add_0_r. 
apply array_at_ext; intros.
unfold cVint. rewrite Z.sub_add.
clear - H3 H0 Hcontents.
specialize (Hcontents i0); destruct (contents i0);
  try reflexivity;  contradiction Hcontents; omega.
Qed.
