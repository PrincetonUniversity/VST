Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.spec_sha.
Local Open Scope logic.

Lemma sha256_block_data_order_return:
   forall (Espec : OracleKind) (hashed b : list int) (ctx data : val)
            (sh : share) (regs : registers) kv,
  Zlength b = LBLOCKz ->
  (LBLOCKz | Zlength hashed) ->
  regs = hash_blocks init_registers hashed ->
  semax (initialized _t Delta_loop1)
  (PROP  ()
   LOCAL  (temp _ctx ctx; var _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(field_at Tsh t_struct_SHA256state_st [StructField _h]
           (map Vint (hash_block regs b)) ctx);
    `(K_vector kv);
   `(data_at_ Tsh (tarray tuint LBLOCKz)) (eval_var _X (tarray tuint LBLOCKz));
   `(data_block sh (intlist_to_Zlist b) data)))
  (Sreturn None)
  (frame_ret_assert
     (function_body_ret_assert tvoid
          (`(field_at Tsh t_struct_SHA256state_st  [StructField _h] 
                 (map Vint (hash_blocks init_registers (hashed++b))) ctx) *
          `(data_block sh (intlist_to_Zlist b) data) *
          `(K_vector kv)))
     (stackframe_of f_sha256_block_data_order)).
Proof.
intros.
unfold Delta_loop1; simplify_Delta.
forward. (* return; *)
unfold frame_ret_assert; simpl.
unfold sha256state_.
set (regs := hash_block (hash_blocks init_registers hashed) b).
unfold_lift.
simpl_stackframe_of.
unfold data_at_.
unfold tarray.
unfold regs; clear regs.
rewrite hash_blocks_last; auto.
cancel.
Qed.
