Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Admitted.

Lemma sha256_block_data_order_return:
forall (Espec : OracleKind) (hashed : list int) (delta : nat)
  (data0 : list Z) (b : list int) (ctx data : val) (r_h : list int)
  (r_Nl r_Nh : int) (r_data : list int) (r_num : int) (n : nat),
length b = LBLOCK ->
r_h = process_msg init_registers hashed ->
length (intlist_to_Zlist hashed) =
delta + Z.to_nat (Int.unsigned r_Nh * Int.modulus + Int.unsigned r_Nl) ->
data0 = map Int.unsigned (firstn (Z.to_nat (Int.unsigned r_num)) r_data) ->
length data0 < CBLOCK ->
length hashed = (16 * n)%nat ->
length r_data = CBLOCK ->
length r_h = 8 ->
isptr data ->
semax (initialized _t Delta_loop1)
  (PROP  ()
   LOCAL ()
   SEP 
   (`(array_at tuint Tsh
        (ZnthV tuint
           (map2 Int.add (process_msg init_registers hashed)
              (rnd_64 r_h K (rev (generate_word (rev b) 48))))) 0
        (Zlength (process_msg init_registers hashed)) ctx);
   `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
     (eval_var _K256 (tarray tuint 64));
   `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
   `(data_block (intlist_to_Zlist b) data);
   `(field_mapsto Tsh t_struct_SHA256state_st _Nl ctx (Vint r_Nl));
   `(field_mapsto Tsh t_struct_SHA256state_st _Nh ctx (Vint r_Nh));
   `(array_at tuchar Tsh (ZnthV tuchar r_data) 0 (Zlength r_data)
       (offset_val (Int.repr 40) ctx));
   `(field_mapsto Tsh t_struct_SHA256state_st _num ctx (Vint r_num))))
  (Sreturn None)
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (`(sha256state_ (process_block_abs b (S256abs hashed delta data0))
             ctx) * `(data_block (intlist_to_Zlist b) data) *
         `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
           (eval_var _K256 (tarray tuint 64))))
     (stackframe_of f_sha256_block_data_order)).
Proof.
intros.
forward. (* return; *)
unfold frame_ret_assert; simpl.
unfold sha256state_.
set (regs := map2 Int.add (process_msg init_registers hashed)
        (rnd_64 (process_msg init_registers hashed) K
           (rev (generate_word (rev b) 48)))).
repeat rewrite exp_sepcon1.
apply exp_right with (regs, (r_Nl, (r_Nh, (r_data, r_num)))).
simpl_typed_mapsto.
unfold s256_relate, s256_h, s256_Nh, s256_Nl, s256_data, s256_num.
unfold fst,snd.
entailer!.
* 
apply process_msg_block; eauto.
* 
rewrite length_intlist_to_Zlist.
rewrite app_length.
rewrite H.
rewrite length_intlist_to_Zlist in *.
change CBLOCK with 64%nat.
change LBLOCK with 16%nat.
rewrite mult_plus_distr_l.
change (4*16)%nat with 64%nat.
omega.
*
exists (S n). rewrite app_length. rewrite H4, H.
change LBLOCK with 16%nat.
transitivity (16 * n + 16 * 1)%nat; [reflexivity | ].
rewrite <- mult_plus_distr_l.
rewrite plus_comm. reflexivity.
*
assert (Lregs: length regs = 8%nat)
  by (subst; apply length_map2_add_rnd_64; auto).
rewrite Zlength_correct; rewrite length_process_msg.
rewrite (Zlength_correct regs); rewrite Lregs.
simpl Z.of_nat.
unfold stackframe_of; simpl.
rewrite var_block_typed_mapsto_.
normalize. simpl_typed_mapsto.
change (Pos.to_nat 16) with 16%nat.
unfold id.
erewrite elim_globals_only
  by (split; [eassumption | reflexivity]).
apply andp_right; [ | cancel].
apply prop_right; compute; congruence.
Qed.
