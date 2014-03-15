Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Require Import sha.verif_sha_bdo3.
Local Open Scope logic.

Definition block_data_order_loop1 := 
   nth 0 (loops (fn_body f_sha256_block_data_order)) Sskip.

Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind) (sh: share)
     (b: list int) ctx (data: val) (regs: list int)
     (Hdata: isptr data),
     length b = LBLOCK ->
     semax Delta_loop1
  (PROP ()
   LOCAL (`(eq ctx) (eval_id _ctx);
               `(eq (Vint (Int.repr 0))) (eval_id _i);
               `(eq data) (eval_id _data);
               `(eq (map Vint regs)) 
                  (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                   (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( K_vector;
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
           `(data_block sh (intlist_to_Zlist b) data)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq ctx) (eval_id _ctx);
                `(eq (Vint (Int.repr 16))) (eval_id _i);
                `(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP (K_vector;
           `(array_at tuint Tsh (tuints b) 0 16) (eval_var _X (tarray tuint 16));
           `(data_block sh (intlist_to_Zlist b) data))) ).
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

Definition loop1_inv (rg0: list int) (sh: share) (b: list int) ctx (data: val) (delta: Z) (i: nat) :=
    PROP ( (i <= 16)%nat )
    LOCAL  (`(eq ctx) (eval_id _ctx); `(eq (Vint (Int.repr (Z.of_nat i - delta)))) (eval_id _i);
               `(eq (offset_val (Int.repr ((Z.of_nat i)*4)) data)) (eval_id _data);
     `(eq (map Vint (rnd_64 rg0 K (firstn i b))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
     SEP (K_vector;
    `(array_at tuint Tsh (f_upto (tuints b) (Z.of_nat i) ) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16));
   `(data_block sh (intlist_to_Zlist b) data)).

apply semax_pre with (EX i:nat, loop1_inv regs sh b ctx data 0 i).
(* 345,184   326,392*)
abstract (unfold loop1_inv;
          apply exp_right with 0%nat;
          rewrite array_at_f_upto_lo;
          entailer!; omega).
(* 419,452   431,980 *)
apply semax_post' with (loop1_inv regs sh b ctx data 0 LBLOCK).
(* 419,452  431,980 *)
abstract (unfold loop1_inv;
               entailer! ;
           rewrite <- H2; repeat f_equal; 
           symmetry; apply firstn_same; omega).
(* 445,728  479,964 *)
clear POSTCONDITION.
apply (semax_loop _ _ (EX i:nat, loop1_inv regs sh b ctx data 1 i)).
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
PROP  ((i < 16)%nat)
   LOCAL  (`(eq ctx) (eval_id _ctx); 
                `(eq (Vint (Int.repr (Z.of_nat (0 + i))))) (eval_id _i);
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
   (K_vector;
   `(array_at tuint Tsh (f_upto (tuints b) (Z.of_nat i)) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16));
   `(data_block sh (intlist_to_Zlist b) data))).
(* 587,640  592,608 *)
abstract entailer.
(* 613,416  655,716 *)
Focus 1.
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
   assert (i=16)%nat by omega; subst i;
   apply andp_right; [ apply prop_right | cancel];
   change 16%nat with LBLOCK in H3;
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
         (Q1 :=  [ `(eq ctx) (eval_id _ctx),
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
         (Frame := [K_vector,
   `(array_at tuint Tsh (f_upto (tuints b) (Z.of_nat i)) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16))]); 
   [apply (read32_reversed_in_bytearray _ (Int.repr (Z.of_nat i * 4)) 0 (Zlength (intlist_to_Zlist b)) data _ sh 
                     (tuchars (map Int.repr (intlist_to_Zlist b))));
    [ reflexivity | reflexivity | reflexivity | auto 50 with closed | 
      intros; apply ZnthV_map_Vint_is_int; rewrite Zlength_correct, map_length;
          rewrite Zlength_correct in H1; apply H1
      | ]
   | | | ].
(* 945,760 834,556 *)
abstract solve [entailer!; repeat split; auto; try omega; 
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist; 
            (*rewrite map_length;*) rewrite H;
 replace (Z.of_nat (4 * LBLOCK) - 4)%Z
  with ((Z.of_nat LBLOCK - 1) * 4)%Z; 
    [apply Zmult_le_compat_r; omega | ];
 rewrite Zmult_comm;
 rewrite Z.mul_sub_distr_l;
 reflexivity].
(* 990,216 849,172 *)
unfold data_block.
rewrite prop_true_andp by apply isbyte_intlist_to_Zlist.
abstract solve [entailer!].
(* 1,078,128 849,172 *)
auto 50 with closed.
simpl.
replace (array_at tuchar sh (tuchars (map Int.repr (intlist_to_Zlist b))) 0
        (Zlength (intlist_to_Zlist b)) data)
  with (data_block sh (intlist_to_Zlist b) data) 
 by (unfold data_block;
       rewrite prop_true_andp by apply isbyte_intlist_to_Zlist;
       reflexivity).
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
instantiate (1:= Vint (big_endian_integer
          (fun z : Z =>
           force_int
             (tuchars (map Int.repr (intlist_to_Zlist b))
                (z + Z.of_nat i * 4))))).
abstract (entailer; apply prop_right; repeat split; try omega; eapply eval_var_isptr; eauto).

rewrite loop1_aux_lemma1; auto.
(* 1,506,948 1,110,852 *)
(* 1,506,948 1,134,576 *)
assert (is_int (tuints K (Z.of_nat i))) 
 by abstract (clear - H0; apply ZnthV_map_Vint_is_int;
        split; try omega; apply Z.lt_trans with 16%Z; [omega | compute; auto]).
unfold K_vector.
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)

abstract (
  assert (Zlength K = 64%Z) by reflexivity;
  entailer!; omega).
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
replace Delta with (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
 by (unfold Delta, Delta_loop1; simplify_Delta; reflexivity).
eapply semax_pre; [ | simple apply rearrange_regs_proof with (bl:=b)(i:=i)(data:=data); auto ].
Admitted.  (* the rest of this is correct but goes over 2 gigabytes.
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
*)

