Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Require Import progs.verif_sha_bdo2.
Require Import progs.verif_sha_bdo3.
Local Open Scope logic.

Definition block_data_order_loop1 := 
   nth 0 (loops (fn_body f_sha256_block_data_order)) Sskip.

Definition block_data_order_loop2 := 
   nth 1 (loops (fn_body f_sha256_block_data_order)) Sskip.

Lemma read32_reversed_in_bytearray:
 forall {Espec: OracleKind} Delta (ofs: int) (lo hi: Z) base e sh contents i P Q
 (VS:  (var_types Delta) ! ___builtin_read32_reversed = None) 
 (GS: (glob_types Delta) ! ___builtin_read32_reversed =
    Some (Global_func (snd __builtin_read32_reversed_spec)))
 (TE: typeof e = tptr tuint)
 (CLOQ: Forall (closed_wrt_vars (eq i)) Q)
 (Hcontents: forall i, (lo <= i < hi)%Z -> isSome (contents i)),
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
         (LOCALx (`(eq (Vint (big_endian_integer (fun z => force_option Int.zero (contents (z+Int.unsigned ofs)%Z))))) (eval_id i)
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
instantiate (2:=(offset_val ofs base, sh, fun z => force_option Int.zero (contents (z + Int.unsigned ofs)%Z))).
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
intros. unfold cSome. rewrite Z.sub_add.
clear - H5 H0 Hcontents.
specialize (Hcontents i0);
 destruct (contents i0); [ | elimtype False; apply Hcontents; omega]. reflexivity.
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
unfold cSome. rewrite Z.sub_add.
clear - H3 H0 Hcontents.
specialize (Hcontents i0); destruct (contents i0);
  [reflexivity | contradiction Hcontents; omega].
Qed.

Definition f_upto {A} (f: Z -> option A) (bound: Z) (i: Z) : option A :=
 if zlt i bound then f i else None.

Lemma array_at_f_upto_lo:
  forall t sh contents lo hi, 
  array_at t sh (f_upto contents lo) lo hi = array_at_ t sh lo hi.
Proof.
intros; apply array_at_ext; intros.
unfold f_upto; if_tac; auto. omega.
Qed.

Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind)
     (b: list int) (data: val) (regs: list int)
     (Hdata: isptr data),
     length b = LBLOCK ->
     semax Delta_loop1
  (PROP ()
   LOCAL (`(eq (Vint (Int.repr 0))) (eval_id _i);
               `(eq data) (eval_id _data);
               `(eq (map Vint regs)) 
                  (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                   (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64));
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist (map swap b)) data)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64));
           `(array_at tuint Tsh (ZnthV tuint b) 0 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist (map swap b)) data))) ).
Proof.
unfold block_data_order_loop1, Delta_loop1.
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

Definition loop1_inv (rg0: list int) (b: list int) (data: val) (delta: Z) (i: nat) :=
    PROP ( i <= 16 )
    LOCAL  (`(eq (Vint (Int.repr (Z.of_nat i - delta)))) (eval_id _i);
               `(eq (offset_val (Int.repr ((Z.of_nat i)*4)) data)) (eval_id _data);
     `(eq (map Vint (rnd_64 rg0 K (firstn i b))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
     SEP (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
    `(array_at tuint Tsh (f_upto (ZnthV tuint b) (Z.of_nat i) ) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16));
   `(data_block (intlist_to_Zlist (map swap b)) data)).

apply semax_pre with (EX i:nat, loop1_inv regs b data 0 i).
(* 345,184   326,392*)
abstract (unfold loop1_inv;
          apply exp_right with 0;
          rewrite array_at_f_upto_lo;
          entailer!; omega).
(* 419,452   431,980 *)
apply semax_post' with (loop1_inv regs b data 0 LBLOCK).
(* 419,452  431,980 *)
abstract (unfold loop1_inv;
               entailer! ;
           rewrite <- H2; repeat f_equal; 
           symmetry; apply firstn_same; omega).
(* 445,728  479,964 *)
clear POSTCONDITION.
apply (semax_loop _ _ (EX i:nat, loop1_inv regs b data 1 i)).
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
PROP  (i < 16)
   LOCAL  (`(eq (Vint (Int.repr (Z.of_nat (0 + i))))) (eval_id _i);
               `(eq (offset_val (Int.repr ((Z.of_nat i)*4)) data)) (eval_id _data);
   `(eq (map Vint (rnd_64 regs K (firstn i b))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP 
   (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
   `(array_at tuint Tsh (f_upto (ZnthV tuint b) (Z.of_nat i)) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16));
   `(data_block (intlist_to_Zlist (map swap b)) data))).
(* 587,640  592,608 *)
abstract entailer.
(* 613,416  655,716 *)
abstract (forward; (* skip; *)
(* 619,968  655,716 *)
   entailer; apply prop_right; clear - H2; split; [omega | f_equal; omega]).
(* 726,056  709,784 *)
abstract (forward;  (* break; *)
(* 738,188  709,784 *)
  entailer; 
 assert (i=16) by omega; subst i; 
 apply andp_right; [ apply prop_right | cancel];
 replace 16 with LBLOCK in H3 by omega;
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
eapply semax_frame_seq
 with (P1 := [])
         (Q1 :=  [ 
`(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i),
`(eq (offset_val (Int.repr (Z.of_nat i * 4)) data)) (eval_id _data),
`(eq (map Vint (rnd_64 regs K (firstn i b))))
  (`cons (eval_id _a)
     (`cons (eval_id _b)
        (`cons (eval_id _c)
           (`cons (eval_id _d)
              (`cons (eval_id _e)
                 (`cons (eval_id _f)
                    (`cons (eval_id _g) (`cons (eval_id _h) `[]))))))))])
         (Frame := [`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64)),
   `(array_at tuint Tsh (f_upto (ZnthV tuint b) (Z.of_nat i)) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16))]); 
   [apply (read32_reversed_in_bytearray _ (Int.repr (Z.of_nat i * 4)) 0 (Zlength (intlist_to_Zlist (map swap b))) data _ Tsh 
                     (ZnthV tuchar (map Int.repr (intlist_to_Zlist (map swap b)))));
    [ reflexivity | reflexivity | reflexivity | auto 50 with closed | 
      intros; apply ZnthV_isSome; rewrite Zlength_correct, map_length;
          rewrite Zlength_correct in H1; apply H1
      | ]
   | | | ].
(* 945,760 834,556 *)
abstract solve [entailer!; repeat split; auto; try omega; 
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist; 
            rewrite map_length; rewrite H;
 replace (Z.of_nat (4 * LBLOCK) - 4)%Z
  with ((Z.of_nat LBLOCK - 1) * 4)%Z; 
    [apply Zmult_le_compat_r; omega | ];
 rewrite Zmult_comm;
 rewrite Z.mul_sub_distr_l;
 reflexivity].
(* 990,216 849,172 *)
abstract solve [entailer!].
(* 1,078,128 849,172 *)
auto 50 with closed.
simpl.
change (array_at tuchar Tsh (ZnthV tuchar (map Int.repr (intlist_to_Zlist (map swap b)))) 0
        (Zlength (intlist_to_Zlist (map swap b))) data)
  with (data_block  (intlist_to_Zlist (map swap b)) data).

forward. (* l := l'; *)
forward. (* data := data + 4; *)
(* 1,194,800 849,172 *)
abstract solve [entailer!].
(* 1,254,920 849,172 *)
normalize.
(* 1,291,784 894,136 *)
simpl typeof.
forward. (* X[i]=l; *)
clear POSTCONDITION MORE_COMMANDS.
instantiate (2:= Z.of_nat i).
instantiate (1:= big_endian_integer
          (fun z : Z =>
           force_option Int.zero
             (ZnthV tuchar (map Int.repr (intlist_to_Zlist (map swap b)))
                (z + Z.of_nat i * 4)))).
abstract (entailer; apply prop_right; repeat split; try omega; eapply eval_var_isptr; eauto).

rewrite <- (array_at_ext tuint Tsh 
    (f_upto (ZnthV tuint b) (Z.of_nat (S i)))
     (upd (f_upto (ZnthV tuint b) (Z.of_nat i)) (Z.of_nat i)
             (Some (big_endian_integer
          (fun z : Z =>
           force_option Int.zero
             (ZnthV tuchar (map Int.repr (intlist_to_Zlist (map swap b)))
                (z + Z.of_nat i * 4)))))))
 by abstract (
 intros; unfold upd; if_tac; unfold f_upto;
 [rewrite if_true by (rewrite inj_S; omega);
  unfold ZnthV; rewrite <- H2; rewrite Nat2Z.id;
  rewrite <- nth_big_endian_int; [ reflexivity | omega ]
 | unfold f_upto; rewrite inj_S; if_tac; if_tac; auto; omega]).
(* 1,506,948 1,110,852 *)
(* 1,506,948 1,134,576 *)
assert (isSome (ZnthV tuint K (Z.of_nat i))) 
 by abstract (clear - H0; apply ZnthV_isSome;
        split; try omega; apply Z.lt_trans with 16%Z; [omega | compute; auto]).
clear H1.
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)
abstract (
assert (Zlength K = 64%Z) by reflexivity;
entailer!; try apply_ZnthV_isSome; try omega;
 eapply eval_var_isptr; eauto).
(* 1,811,028 1,406,332 *)
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.

match goal with 
  |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ 
       (normal_ret_assert (PROPx ?P (LOCALx ?Q _)))
 => apply semax_post' with (PROPx P (LOCALx Q (SEPx R)));
  [ | change R with (nil++R); apply semax_frame_PQR with (R2:=R)]
end.
abstract (
apply andp_derives; auto;
apply andp_derives; auto;
unfold Z.succ; rewrite inj_S;
go_lower0; cancel).
auto 50 with closed.
(* 1,811,028 1,429,048 *)
change (match b with
                | [] => []
                | a :: l => a :: firstn i l
                end) with (firstn (S i) b).
eapply semax_pre; [ | apply rearrange_regs_proof; auto ].
abstract (entailer!;
 [destruct data; inv Hdata; simpl; f_equal;
  rewrite Int.add_assoc;
  f_equal; unfold Z.succ; rewrite Z.mul_add_distr_r;
  rewrite <- add_repr;
  f_equal
 | unfold ZnthV; simpl; rewrite Nat2Z.id;
   clear - H0;
   destruct (assert_lemmas.nth_error_in_bounds K i) as [j ?];
    [compute; omega | rewrite H; reflexivity]
 ]).
(* 2,xxx,xxx 1,579,524 *)
Qed.

Lemma local_and_retval: (* do we need this? *)
 forall (i: ident) (P: val -> Prop) (R: mpred),
    `(local (`P retval) && `R) (get_result1 i) = local (`P (eval_id i)) && `R.
Proof.
intros.
extensionality rho.
super_unfold_lift.
unfold get_result1. simpl.
unfold local, lift1.
f_equal; auto.
Qed.
Hint Rewrite local_and_retval: norm.

Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) (data: val) (regs: list int),
     length b = LBLOCK ->
     semax  Delta_loop1
 (PROP ()
   LOCAL (`(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at tuint Tsh (ZnthV tuint b) 0 16) (eval_var _X (tarray tuint 16))))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K (rev (generate_word (rev b) 48)))))
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16))))).
Admitted.

Lemma semax_seq_congr:  (* not provable *)
 forall (Espec: OracleKind) s1 s1' s2 s2',
  (forall Delta P R, semax Delta P s1 R <-> semax Delta P s1' R) ->
  (forall Delta P R, semax Delta P s2 R <-> semax Delta P s2' R) ->
 (forall Delta P R, 
    semax Delta P (Ssequence s1 s2) R <->
    semax Delta P (Ssequence s1' s2') R).
Abort.

Definition load8 id ofs :=
 (Sset id
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr ofs) tint) (tptr tuint)) tuint)).

Lemma sha256_block_load8:
  forall (Espec : OracleKind) 
     (data: val) (r_h: list int) (ctx: val)
   (H5 : length r_h = 8),
     semax  
      (initialized _data
         (func_tycontext f_sha256_block_data_order Vprog Gtot))
  (PROP  ()
   LOCAL  (`eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (ZnthV tuint r_h) 0 (Zlength r_h) ctx)))
   (Ssequence (load8 _a 0)
     (Ssequence (load8 _b 1)
     (Ssequence (load8 _c 2)
     (Ssequence (load8 _d 3)
     (Ssequence (load8 _e 4)
     (Ssequence (load8 _f 5)
     (Ssequence (load8 _g 6)
     (Ssequence (load8 _h 7)
         Sskip))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (`(eq (map Vint r_h))
                    (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
)));
   `eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (ZnthV tuint r_h) 0 (Zlength r_h) ctx)))).
Proof.
intros.
simplify_Delta.
unfold load8.
abbreviate_semax.
normalize.
simpl.
normalize.
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
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
abbreviate_semax.
assert (H5': Zlength r_h = 8%Z).
rewrite Zlength_correct; rewrite H5; reflexivity.
do 8 (forward; [ (entailer!; try apply_ZnthV_isSome; omega) | ]).
forward.  (* skip; *)
entailer.
do 9 (destruct r_h as [ | ?h r_h ] ; [inv H5 | ]).
reflexivity.
inv H5.
Qed.

Definition get_h (n: Z) :=
    Sset _t
        (Ederef
           (Ebinop Oadd
              (Efield
                 (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr n) tint) (tptr tuint)) tuint).

Definition add_h (n: Z) (i: ident) :=
   Sassign
       (Ederef
          (Ebinop Oadd
             (Efield
                (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                   t_struct_SHA256state_st) _h (tarray tuint 8))
             (Econst_int (Int.repr n) tint) (tptr tuint)) tuint)
       (Ebinop Oadd (Etempvar _t tuint) (Etempvar i tuint) tuint).

Definition add_them_back :=
 [get_h 0, add_h 0 _a,
  get_h 1, add_h 1 _b,
  get_h 2, add_h 2 _c,
  get_h 3, add_h 3 _d,
  get_h 4, add_h 4 _e,
  get_h 5, add_h 5 _f,
  get_h 6, add_h 6 _g,
  get_h 7, add_h 7 _h].


Lemma add_them_back_proof:
  forall (Espec : OracleKind)
     (b: list int) (r_h: list int)(ctx: val)(hashed: list int),
     length b = LBLOCK ->
     semax  Delta_loop1
   (PROP  ()
   LOCAL 
   (`(eq (map Vint (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP 
   (`(array_at tuint Tsh (ZnthV tuint (process_msg init_registers hashed)) 0
       (Zlength (process_msg init_registers hashed)) ctx)))
   (sequence add_them_back Sskip)
  (normal_ret_assert
   (PROP() LOCAL() 
    SEP (`(array_at tuint Tsh (ZnthV tuint 
                   (map2 Int.add (process_msg init_registers hashed)
                                         (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
            0 (Zlength (process_msg init_registers hashed)) ctx)))).
Admitted.

Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at_ _ _ _ _ _) =>
  (apply array_at__array_at; clear; simpl; congruence) : cancel.
(* move the Hint to malloc_lemmas.v, 
  and change the name of array_at__array_at to array_at_array_at_
*)


Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
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
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
unfold sha256state_.
simpl_stackframe_of. 
normalize. intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
repeat simpl_typed_mapsto.
unfold fst,snd.
normalize.
unfold s256_relate in H1. destruct a.
simpl in H1.
unfold s256_Nh, s256_Nl, s256_data, s256_num, fst, snd in H1.
destruct H1 as [? [? [? [H4 [H4b H4c]]]]].
destruct H4b as [n H4b].
change (length hashed = 16 * n)%nat in H4b.
assert (length r_h = 8%nat) by (subst r_h; apply length_process_msg).
forward. (* data = in; *)
abbreviate_semax.
match goal with |- semax _ (PROPx nil ?QR) _ _ =>
 apply semax_pre0 with (PROPx [isptr data] QR)
end.
apply andp_right; [ | apply andp_left2; auto].
entailer.
normalize.
match goal with |- semax _ _ ?c _ =>
 eapply seq_assocN with (cs := sequenceN 8 c)
end.
eapply semax_frame1.
eapply sha256_block_load8 with (ctx:=ctx); eassumption.
simplify_Delta; reflexivity.
entailer!.
auto 50 with closed.
abbreviate_semax.
simpl.
do 2 match goal with |- appcontext [lift1 ?A] => 
  change (lift1 A) with (`A)
end.
forward.  (* i = 0; *)

eapply semax_frame_seq.
replace Delta with Delta_loop1
 by (simplify_Delta; reflexivity).
simple apply (sha256_block_data_order_loop1_proof
  _ b data r_h); auto.
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.

eapply semax_frame_seq.
apply sha256_block_data_order_loop2_proof
              with (regs:=r_h)(b:=b); eassumption.
entailer!.
auto 50 with closed.
unfold app; abbreviate_semax.
eapply seq_assocN with (cs := add_them_back).

eapply semax_frame1.
apply (add_them_back_proof _ b r_h ctx hashed); try eassumption.
simplify_Delta; reflexivity.
entailer. cancel.
auto 50 with closed.
simpl; abbreviate_semax.

simpl.
do 2 match goal with |- appcontext [lift1 ?A] => 
  change (lift1 A) with (`A)
end.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
eapply sha256_block_data_order_return; eauto.
Qed.










