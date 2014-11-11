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
  (i < length b)%nat ->
  0 <= Z.of_nat i * 4 <= Int.max_unsigned ->
  v = nthi b (Z.of_nat i) ->
  upd_reptype_array tuint (Z.of_nat i) (map Vint (firstn i b))
          (Vint v)
  =  map Vint (firstn (S i) b).
Proof.
intros.
unfold upd_reptype_array.
rewrite Nat2Z.id.
rewrite Z2Nat.inj_add by omega. rewrite Nat2Z.id.
change (Z.to_nat 1) with 1%nat.
replace (i+1)%nat with (S i) by (clear; omega).
rewrite force_lengthn_same
  by (rewrite map_length, firstn_length, min_l; omega).
subst v.
clear H0.
revert b H.
induction i; destruct b; simpl length; intros; try omega.
reflexivity.
f_equal.
simpl map at 1.
change (map Vint (firstn (S (S i)) (i0 :: b)))
  with (Vint i0 :: map Vint (firstn (S i) b)).
rewrite <- app_comm_cons.
f_equal.
replace (nthi (i0::b) (Z.of_nat (S i))) with  (nthi b (Z.of_nat i)).
apply IHi.
omega.
unfold nthi.
repeat rewrite Nat2Z.id. reflexivity.
Qed.

Lemma read32_reversed_in_bytearray:
 forall {Espec: OracleKind} Delta (ofs: int) base e sh (contents: list int) i P Q
 (VS:  (var_types Delta) ! ___builtin_read32_reversed = None) 
 (GS: (glob_types Delta) ! ___builtin_read32_reversed =
    Some (Global_func (snd __builtin_read32_reversed_spec)))
 (TE: typeof e = tptr tuint)
 (TCi:  tc_fn_return Delta (Some i) tuint)
 (CLOQ: Forall (closed_wrt_vars (eq i)) Q),
 PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- 
         PROP ((0 <= Int.unsigned ofs <= Zlength contents - 4 )%Z)
         LOCAL (tc_expr Delta e; `(eq (offset_val ofs base)) (eval_expr e))
         SEP  (TT) ->
 semax Delta  (PROPx P (LOCALx Q (SEP (`(data_at sh (tarray tuchar (Zlength contents)) (map Vint contents) base)))))
        (Scall (Some i)
           (Evar ___builtin_read32_reversed
              (Tfunction (Tcons (tptr tuint) Tnil) tuint cc_default))
           [e])
        (normal_ret_assert
         (PROP () 
          (LOCALx (temp i (Vint (big_endian_integer (firstn (Z.to_nat WORD) (skipn (Z.to_nat (Int.unsigned ofs)) contents))))
                        :: Q)                 
         SEP (`(data_at sh (tarray tuchar (Zlength contents)) (map Vint contents) base))))).
Proof.
intros.
apply semax_pre with
 (PROP  ((0 <= Int.unsigned ofs <= Zlength contents - 4)%Z)
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
go_lowerx; entailer.
normalize.
clear H.
normalize.
Admitted. (*   Qinxiang: can you look at this?  ... 
rewrite (split_array_at (Int.unsigned ofs + 4)%Z) with (hi:=hi) by omega.
rewrite split_offset_array_at with (lo := Int.unsigned ofs) (hi := Int.unsigned ofs + 4);
  [| omega | simpl; omega | reflexivity].
normalize.

match goal with |- semax _ _ _ (normal_ret_assert (PROPx _ (LOCALx _ ?A))) =>
 replace A  with (SEPx( [
         `(array_at tuchar sh
             (fun i0 : Z => contents (i0 + Int.unsigned ofs)) 0
             (Int.unsigned ofs + 4 - Int.unsigned ofs)
             (offset_val (Int.repr (Int.unsigned ofs)) base))] ++
               [`(array_at tuchar sh contents lo (Int.unsigned ofs) base);
         `(array_at tuchar sh contents (Int.unsigned ofs + 4) hi base)]))
 by (simpl app; apply pred_ext; go_lowerx; normalize; cancel)
end.

match goal with |- semax _ (PROPx _ (LOCALx _ ?A)) _ _ =>
 replace A  with (SEPx( [
         `(array_at tuchar sh
             (fun i0 : Z => contents (i0 + Int.unsigned ofs)) 0
             (Int.unsigned ofs + 4 - Int.unsigned ofs)
             (offset_val (Int.repr (Int.unsigned ofs)) base))] ++
               [`(array_at tuchar sh contents lo (Int.unsigned ofs) base);
         `(array_at tuchar sh contents (Int.unsigned ofs + 4) hi base)]))
 by (simpl app; apply pred_ext; go_lowerx; normalize; cancel)
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
rewrite <- H5.
rewrite TE.
destruct base; inv Pbase; reflexivity.
pattern ofs at 4;
 replace ofs with (Int.repr (sizeof tuchar * Int.unsigned ofs))%Z
 by (simpl sizeof; rewrite Z.mul_1_l; apply Int.repr_unsigned).
apply derives_refl'.
rewrite Int.repr_unsigned.
replace (Int.unsigned ofs + 4 - Int.unsigned ofs) with 4 by omega.
simpl sizeof. rewrite Zmult_1_l. rewrite Int.repr_unsigned.
apply equal_f. apply array_at_ext.
intros. unfold cVint.

specialize (Hcontents (i0 + Int.unsigned ofs)).
destruct (contents (i0 + Int.unsigned ofs)); 
  try solve [elimtype False; apply Hcontents; omega]. reflexivity.

intros; apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx.
entailer.
apply derives_refl'.
pattern ofs at 2;
 replace ofs with (Int.repr (sizeof tuchar * Int.unsigned ofs))%Z
 by (simpl sizeof; rewrite Z.mul_1_l; apply Int.repr_unsigned).
rewrite Int.repr_unsigned.
replace (Int.unsigned ofs + 4 - Int.unsigned ofs) with 4 by omega.
simpl sizeof. rewrite Zmult_1_l. rewrite Int.repr_unsigned.
apply equal_f. 
apply array_at_ext; intros.
unfold cVint.
specialize (Hcontents (i0 + Int.unsigned ofs)).
destruct (contents (i0 + Int.unsigned ofs)); 
  try reflexivity;  contradiction Hcontents; omega.
auto.
Qed.

*)

Definition block_data_order_loop1 := 
   nth 0 (loops (fn_body f_sha256_block_data_order)) Sskip.

Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind) (sh: share)
     (b: list int) ctx (data: val) (regs: list int) kv Xv
     (Hregs: length regs = 8%nat)
     (Hdata: isptr data),
     length b = LBLOCK ->
     semax Delta_loop1
  (PROP ()
   LOCAL (temp _ctx ctx; temp _i (Vint (Int.repr 0)); temp _data data;
               temp _a (Vint (nthi regs 0)); 
               temp _b (Vint (nthi regs 1)); 
               temp _c (Vint (nthi regs 2)); 
               temp _d (Vint (nthi regs 3)); 
               temp _e (Vint (nthi regs 4)); 
               temp _f (Vint (nthi regs 5)); 
               temp _g (Vint (nthi regs 6)); 
               temp _h (Vint (nthi regs 7)); 
               var _X (tarray tuint LBLOCKz) Xv;
               var _K256 (tarray tuint CBLOCKz) kv)
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
                var _X (tarray tuint LBLOCKz) Xv;
                var _K256 (tarray tuint CBLOCKz) kv)
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

Definition loop1_inv (rg0: list int) (sh: share) (b: list int) ctx (data: val) kv Xv (delta: Z) (i: nat) :=
    PROP ( (i <= LBLOCK)%nat )
    LOCAL  (temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i - delta)));
                 temp _data  (offset_val (Int.repr ((Z.of_nat i)*4)) data);
                 temp _a (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 0));
                 temp _b (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 1));
                 temp _c (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 2));
                 temp _d (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 3));
                 temp _e (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 4));
                 temp _f (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 5));
                 temp _g (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 6));
                 temp _h (Vint (nthi (Round rg0 (nthi b) (Z.of_nat i - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                 var _K256 (tarray tuint CBLOCKz) kv)
     SEP (`(K_vector kv);
       `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (firstn i b)) Xv);
   `(data_block sh (intlist_to_Zlist b) data)).

apply semax_pre with (EX i:nat, loop1_inv regs sh b ctx data kv Xv 0 i). 
(* 345,184   326,392*) {
 apply exp_right with 0%nat.
 unfold loop1_inv.
(* rewrite array_at_f_upto_lo. *)
 replace (Round regs (nthi b) (Z.of_nat 0 - 1)) with regs.
 entailer!.
 rewrite Round_equation. rewrite if_true by (compute; auto). auto.
}
(* 419,452   431,980 *)
apply semax_post' with (loop1_inv regs sh b ctx data kv Xv 0 LBLOCK).
(* 419,452  431,980 *)
  unfold loop1_inv. entailer!.
  rewrite firstn_same by omega; auto.
(* 445,728  479,964 *)
clear POSTCONDITION.
apply (semax_loop _ _ (EX i:nat, loop1_inv regs sh b ctx data kv Xv 1 i)).
2: abstract (
apply extract_exists_pre; intro i;
forward;  (*  i += 1; *)
apply exp_right with i;
(* 452,280  481,476 *)
 unfold loop1_inv;  entailer! ; f_equal; omega).
(* 561,900  574,392 *)

apply extract_exists_pre; intro i.
unfold loop1_inv.
forward_if (
   PROP  ((i < LBLOCK)%nat)
   LOCAL  (temp _ctx ctx; temp _i  (Vint (Int.repr (Z.of_nat (0 + i))));
                temp _data (offset_val (Int.repr ((Z.of_nat i)*WORD)) data);
                 temp _a (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0));
                 temp _b (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1));
                 temp _c (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2));
                 temp _d (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3));
                 temp _e (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4));
                 temp _f (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5));
                 temp _g (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6));
                 temp _h (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                 var _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(K_vector kv);
    `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (firstn i b)) Xv);
   `(data_block sh (intlist_to_Zlist b) data))).
(* 587,640  592,608 *)
(* 613,416  655,716 *)
abstract (forward; (* skip; *)
(* 619,968  655,716 *)
   entailer; apply prop_right; rewrite Z.sub_0_r; auto).
(* 726,056  709,784 *) 
abstract (
   apply semax_extract_PROP; intro;
   forward; (* break; *)
   cbv beta;
   rewrite overridePost_EK_break,
       loop1_ret_assert_EK_break,
        normal_ret_assert_elim;
   entailer;
   assert (i=LBLOCK)%nat by omega; subst i;
   apply andp_right; [ apply prop_right | cancel];
   repeat split; auto).
(* 854,860 750,176 *)
unfold MORE_COMMANDS, POSTCONDITION, abbreviate;
 clear MORE_COMMANDS POSTCONDITION.
make_sequential.
unfold loop1_ret_assert.
apply extract_exists_post with (S i).
rewrite inj_S.
simpl plus.
normalize.

(* 945,760 834,556 *)
do 2 apply -> seq_assoc.
unfold data_block.
eapply semax_frame_seq
 with (P1 := [])
         (Q1 :=  [temp _ctx ctx; temp _i (Vint (Int.repr (Z.of_nat i)));
                      temp _data (offset_val (Int.repr (Z.of_nat i * 4)) data);
                 temp _a (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 0));
                 temp _b (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 1));
                 temp _c (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 2));
                 temp _d (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 3));
                 temp _e (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 4));
                 temp _f (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 5));
                 temp _g (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 6));
                 temp _h (Vint (nthi (Round regs (nthi b) (Z.of_nat i - 1)) 7));
                 var _X (tarray tuint LBLOCKz) Xv;
                 var _K256 (tarray tuint CBLOCKz) kv])
         (Frame := [`(K_vector kv);
                           `(data_at Tsh (tarray tuint LBLOCKz) (map Vint (firstn i b)) Xv)]);
(**{
apply (read32_reversed_in_bytearray _ (Int.repr (Z.of_nat i * 4)) data _ sh 
                     (map Int.repr (intlist_to_Zlist b))).
*)
   [apply (read32_reversed_in_bytearray _ (Int.repr (Z.of_nat i * 4)) data _ sh 
                     (map Int.repr (intlist_to_Zlist b)));
    [ reflexivity | reflexivity | reflexivity | reflexivity
    | auto 50 with closed 
      (* intros; apply ZnthV_map_Vint_is_int; rewrite Zlength_correct, map_length;
          rewrite Zlength_correct in H1; apply H1 *)
      | ]
   | | | ].
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
auto 50 with closed.
unfold app.
fold (data_block sh (intlist_to_Zlist b) data).
set (bei :=  big_endian_integer
            (firstn (Z.to_nat WORD)
               (skipn (Z.to_nat (Int.unsigned (Int.repr (Z.of_nat i * 4))))
                  (map Int.repr (intlist_to_Zlist b))))).
forward. (* l := l'; *)
forward. (* data := data + 4; *)
(* 1,194,800 849,172 *)
normalize.
(* 1,291,784 894,136 *)
change LBLOCKz with 16. (* this shouldn't be necessary *)
forward. (* X[i]=l; *)
change 16 with LBLOCKz.

 assert_LOCAL (temp _l (Vint (nthi b (Z.of_nat i)))). {
  drop_LOCAL 6%nat. drop_LOCAL 5%nat. drop_LOCAL 4%nat.
  entailer!.
  unfold nthi.
  rewrite Nat2Z.id.
  rewrite Z2Nat.inj_mul by omega. rewrite Nat2Z.id.
  apply nth_big_endian_integer. 
  apply nth_error_nth; rewrite H; auto.
 }
drop_LOCAL 2%nat; drop_LOCAL 2%nat.

change LBLOCKz with (Z.of_nat LBLOCK).

assert (Hi: 0 <= Z.of_nat i * 4 <= Int.max_unsigned). {
   clear - H0;
   assert (0 <= Z.of_nat i * 4 < 64); [split; [omega |] | repable_signed ];
   change 64 with (Z.of_nat LBLOCK *4)%Z;
   apply Zmult_lt_compat_r; [computable | ];
   apply Nat2Z.inj_lt; auto.
}

unfold bei; clear bei.
rewrite loop1_aux_lemma1; auto;
[ | omega
 | rewrite Int.unsigned_repr by auto;
   rewrite Z2Nat.inj_mul by omega; rewrite Nat2Z.id;
   symmetry;
   apply nth_big_endian_integer;
   rewrite nth_error_nth with (d:=Int.zero) by omega;
   unfold nthi; rewrite Nat2Z.id; auto].

(* 1,506,948 1,110,852 *)
(* 1,506,948 1,134,576 *)

unfold K_vector.

(*
assert (is_int I32 Unsigned (nthi K256 (Z.of_nat i)))
 by (clear - H0; apply ZnthV_map_Vint_is_int;
       split; [ omega | ];
       apply Z.lt_trans with (Z.of_nat LBLOCK);
      [omega | compute; auto]).
*)


assert (Z.of_nat i < Zlength K256) 
  by (change (Zlength K256) with (Z.of_nat (LBLOCK + 48));
       apply Nat2Z.inj_lt; omega).
STOP.  (* Qinxiang: look at the next "forward", Ki=K256[i];  *)
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)

instantiate (1:= Zlength K256).
instantiate (1:= tuints K256).
instantiate (1:= Tsh).
assert (Zlength K256 = 64%Z) by reflexivity;
  entailer!; omega.
(* 1,811,028 1,406,332 *)
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.

match goal with 
  |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ 
       (normal_ret_assert (PROPx ?P (LOCALx ?Q _)))
 => apply semax_post' with (PROPx P (LOCALx Q (SEPx R)));
  [ | change R with (nil++R); apply semax_frame_PQR with (R2:=R)]
end.
apply andp_derives; auto;
apply andp_derives; auto;
unfold Z.succ; rewrite inj_S;
go_lower0; cancel.
auto 50 with closed.
(* 1,811,028 1,429,048 *)
forget (nthi b) as M.
apply semax_pre with
 (PROP  ()
   LOCAL 
   (temp _ctx ctx; temp _data (offset_val (Int.repr (Zsucc (Z.of_nat i) * WORD)) data);
    temp _l (Vint (W M (Z.of_nat i))); temp _Ki (Vint (nthi K256 (Z.of_nat i)));
    temp _i (Vint (Int.repr (Z.of_nat i)));
                 temp _a (Vint (nthi (Round regs M (Z.of_nat i - 1)) 0));
                 temp _b (Vint (nthi (Round regs M (Z.of_nat i - 1)) 1));
                 temp _c (Vint (nthi (Round regs M (Z.of_nat i - 1)) 2));
                 temp _d (Vint (nthi (Round regs M (Z.of_nat i - 1)) 3));
                 temp _e (Vint (nthi (Round regs M (Z.of_nat i - 1)) 4));
                 temp _f (Vint (nthi (Round regs M (Z.of_nat i - 1)) 5));
                 temp _g (Vint (nthi (Round regs M (Z.of_nat i - 1)) 6));
                 temp _h (Vint (nthi (Round regs M (Z.of_nat i - 1)) 7));
                 var _K256 (tarray tuint CBLOCKz) kv)
   SEP()).
{ 
entailer!.
f_equal. f_equal. unfold Z.succ; rewrite Z.mul_add_distr_r; reflexivity.
rewrite W_equation.
rewrite if_true; auto.
omega.
(*clear - H0; change 16 with (Z.of_nat 16); apply Nat2Z.inj_lt; auto.

*)
clear - H0 H4. rename H4 into H2.
unfold tuints, ZnthV in H2.
rewrite Int.signed_repr in H2 by 
 (pose proof LBLOCK_eq; repable_signed).
rewrite if_false in H2 by omega.
unfold nthi.
rewrite Nat2Z.id in *.
rewrite (nth_map' _ _ Int.zero) in H2.
congruence.
clear H2.
change (length K256) with 64%nat.
pose proof LBLOCK_eq; omega.
}
{clear b H.
replace (Z.succ (Z.of_nat i) - 1)%Z with (Z.of_nat i) by omega.
rewrite (Round_equation _ _ (Z.of_nat i)).
rewrite if_false by omega.
forget (nthi K256 (Z.of_nat i)) as k.
forget (W M (Z.of_nat i)) as w.
assert (length (Round regs M (Z.of_nat i - 1)) = 8)%nat.
apply length_Round; auto.
forget (Round regs M (Z.of_nat i - 1)) as regs'.
change 16 with LBLOCK.
destruct regs' as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; inv H.
unfold rearrange_regs.
abbreviate_semax.
forward. (* T1 = l + h + Sigma1(e) + Ch(e,f,g) + Ki; *)
rewrite <- Sigma_1_eq, <- Ch_eq, rearrange_aux.
forward. (* T2 = Sigma0(a) + Maj(a,b,c); *)
 rewrite <- Sigma_0_eq, <- Maj_eq.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
simplify_Delta.
 entailer!. 
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
Qed.
