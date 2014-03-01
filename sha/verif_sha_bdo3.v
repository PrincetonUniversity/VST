Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Local Open Scope logic.

Lemma and_mone':
 forall x, Int.and x (Int.repr (-1)) = x.
Proof.
apply Int.and_mone.
Qed.

Lemma Sigma_1_eq: forall f_,
  Sigma_1 f_ =
            (Int.xor
              (Int.xor
                 (Int.or (Int.shl f_ (Int.repr 26))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 26))))
                 (Int.or (Int.shl f_ (Int.repr 21))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 21)))))
              (Int.or (Int.shl f_ (Int.repr 7))
                 (Int.shru (Int.and f_ (Int.repr (-1)))
                    (Int.sub (Int.repr 32) (Int.repr 7))))).
Proof.
intros.
unfold Sigma_1, Sh.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 26)) with (Int.repr 6).
change (Int.sub (Int.repr 32) (Int.repr 21)) with (Int.repr 11).
change (Int.sub (Int.repr 32) (Int.repr 7)) with (Int.repr 25).
reflexivity.
Qed.

Lemma  Sigma_0_eq: forall b_,
   Sigma_0 b_ = 
      (Int.xor
        (Int.xor
           (Int.or (Int.shl b_ (Int.repr 30))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 30))))
           (Int.or (Int.shl b_ (Int.repr 19))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 19)))))
        (Int.or (Int.shl b_ (Int.repr 10))
           (Int.shru (Int.and b_ (Int.repr (-1)))
              (Int.sub (Int.repr 32) (Int.repr 10))))).
Proof.
intros.
unfold Sigma_0, Sh.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 19)) with (Int.repr 13).
change (Int.sub (Int.repr 32) (Int.repr 10)) with (Int.repr 22).
change (Int.sub (Int.repr 32) (Int.repr 30)) with (Int.repr 2).
reflexivity.
Qed.

Lemma Ch_eq: forall f_ g_ h_,
  Ch f_ g_ h_ =
        (Int.xor (Int.and f_ g_) (Int.and (Int.not f_) h_)).
Proof. reflexivity.
Qed.

Lemma Maj_eq:
  forall b c d, 
  Maj b c d =
  (Int.xor (Int.xor (Int.and b c) (Int.and b d)) (Int.and c d)).
Proof.
intros.
unfold Maj.
rewrite (Int.xor_commut) at 1.
rewrite Int.xor_assoc. auto.
Qed.

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

Lemma rearrange_aux2: 
forall (Espec : OracleKind) (i : nat)(w k : int) ctx
      (a b c d e f g h : int) (eqofs : val -> Prop),
i < 16 ->
semax (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
  (PROP  ()
   LOCAL  (`(eq ctx) (eval_id _ctx);
   `eqofs (eval_id _data); `(eq (Vint w)) (eval_id _l);
   `(eq (Vint k)) (eval_id _Ki);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (map Vint [a, b, c, d, e, f, g, h]))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP())
 rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq ctx) (eval_id _ctx);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
      `eqofs (eval_id _data);
      `(eq (map Vint (rnd_function [a, b, c, d, e, f, g, h]  k w)))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
        SEP())).
Proof.
intros.
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
admit. (* this proof works, but takes over 2 gigabytes  
unfold Delta_loop1; simplify_Delta; abbreviate_semax.
unfold rearrange_regs.
repeat forward.

simpl eval_binop;
  go_lower0;
  repeat (apply derives_extract_prop; intro);
  repeat apply andp_right; try apply prop_right; auto;
  decompose [and] H2; clear H2; subst;
  inv H18;
  repeat match goal with 
   | H: eval_id _ _ = _ |- _ => rewrite H in *; clear H
   | H: _ = eval_id _ _ |- _ => rewrite <- H in *; clear H
  end;
  repeat split; auto.

  clear;
  cbv beta iota delta [sem_and sem_notint sem_or 
    sem_shl sem_shr sem_or sem_add sem_xor
    force_val sem_shift_ii sem_notint_i
    both_int ]; simpl;
  repeat rewrite <- Sigma_1_eq;
  repeat rewrite <- Sigma_0_eq;
  repeat rewrite <- Ch_eq;
  repeat rewrite <- Maj_eq;
  repeat rewrite (rearrange_aux h);
  reflexivity.
*)
Qed.

Lemma rearrange_regs_proof:
 forall (Espec: OracleKind) i (data: val) bl regs ctx
 (Hdata: isptr data)
 (H: length bl = LBLOCK)
 (H0: i < 16), 
 semax (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
  (PROP  ()
   LOCAL 
   (`(eq ctx) (eval_id _ctx);
   `(eq (offset_val (Int.repr (Zsucc (Z.of_nat i) * 4)) data)) (eval_id _data);
   `(eq (Vint (big_endian_integer
             (fun z : Z =>
              force_int
                (tuchars (map Int.repr (intlist_to_Zlist bl))
                   (z + Z.of_nat i * 4))))))
       (eval_id _l);
   `(eq (nth_error K i)) (`Some  (`force_int (eval_id _Ki)));
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (map Vint (rnd_64 regs K (firstn i bl))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP()) rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq ctx) (eval_id _ctx);
      `(eq (Vint (Int.repr (Z.succ (Z.of_nat i) - 1)))) (eval_id _i);
      `(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) (eval_id _data);
      `(eq (map Vint (rnd_64 regs K (firstn (S i) bl))))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
        SEP())).
Proof.
intros.
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
assert (exists w, nth_error bl i = Some w).
 apply assert_lemmas.nth_error_in_bounds.
change LBLOCK with 16 in H; omega.
destruct H1 as [w H1].
assert (exists k, nth_error K i = Some k).
 apply assert_lemmas.nth_error_in_bounds.
compute; split; omega.
destruct H2 as [k H2].
set (Delta := initialized _Ki (initialized _l (initialized _l' Delta_loop1))).
set (Delta' := initialized _Ki (initialized _l (initialized _l' Delta_loop1))).
assert (Delta' = Delta) by reflexivity.
revert H3.
revert Delta.
cbv delta [Delta_loop1].
simplify_Delta.
intro HDelta'.
match goal with
         | |- semax ?D _ _ _  =>
               abbreviate D : tycontext as Delta
end.
assert (HDelta'': Delta' = Delta) by reflexivity.
rewrite (rnd_64_S _ _ _ _ _ H2 H1).
forget (rnd_64 regs K (firstn i bl)) as regs'.
apply semax_pre with
  (PROP  (exists a, exists b, exists c, exists d, 
              exists e, exists f, exists g, exists h,
                regs' = [a,b,c,d,e,f,g,h])
   LOCAL 
   (`(eq ctx) (eval_id _ctx);
   `(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data))
      (eval_id _data);
   `(eq (Vint w)) (eval_id _l);
   `(eq (Vint k)) (eval_id _Ki);
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (map Vint regs'))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP()).
abstract (entailer; split3;
  [(exists a_, b_, c_, d_, e_, f_, g_, h_;
    clear - H4; rename H4 into H0;
    do 8 (destruct regs' as [ | ? regs']; [inv H0 | ]);
    destruct regs'; inv H0; reflexivity)
  | apply nth_big_endian_integer; auto 
  | congruence]).
apply semax_extract_PROP; 
   intros [a [b [c [d [e [f [g [h Hregs]]]]]]]].
forget (eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) as eqofs.
clear Hdata data.
replace (Z.succ (Z.of_nat i) - 1)%Z with (Z.of_nat i) by (clear; omega).
rewrite <- HDelta''; unfold Delta'.
clear HDelta' Delta' HDelta'' Delta.
subst regs'.
simple apply rearrange_aux2; assumption. 
Qed.


Definition f_upto {t} (f: Z -> reptype t) (bound: Z) (i: Z) : reptype t :=
 if zlt i bound then f i else default_val t.

Lemma array_at_f_upto_lo:
  forall t sh contents lo hi, 
  array_at t sh (f_upto contents lo) lo hi = array_at_ t sh lo hi.
Proof.
intros; apply array_at_ext; intros.
unfold f_upto; if_tac; auto. omega.
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
