Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo2.
Require Import sha.verif_sha_bdo4.
Require Import sha.verif_sha_bdo7.
Require Import sha.verif_sha_bdo8.
Local Open Scope logic.

Lemma exp_prop: forall A P, exp (fun x: A => prop (P x)) = prop (exists x: A, P x).
Proof.
  intros.
  apply pred_ext; normalize.
  + exists x; auto.
  + destruct H as [x ?].
    apply (exp_right x).
    normalize.
Qed.
(* move somewhere else *)


Lemma fold_right_and_app:
  forall (Q1 Q2: list (environ -> Prop)) rho,
   fold_right `and `True (Q1 ++ Q2) rho = 
   (fold_right `and `True Q1 rho /\  fold_right `and `True Q2 rho).
Proof.
intros.
induction Q1; simpl; auto.
apply prop_ext; intuition.
normalize. 
simpl in IHQ1.
rewrite IHQ1.
clear; apply prop_ext; intuition.
Qed.

Lemma semax_frame_PQR':
  forall Q2 R2 Espec Delta R1 P Q P' Q' R1' c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     @semax Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c 
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     @semax Espec Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c 
                     (normal_ret_assert (PROPx P' (LOCALx (Q'++Q2) (SEPx (R1'++R2))))).
Proof.
intros.
replace (PROPx P (LOCALx (Q++Q2) (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * (LOCALx Q2 (SEPx R2))).
eapply semax_post0; [ | apply semax_frame; try eassumption].
intros ek vl rho.
unfold frame_ret_assert, normal_ret_assert.
normalize. unfold SEPx, LOCALx, local, lift1.
rewrite fold_right_sepcon_app.
normalize.
rewrite prop_true_andp; auto.
rewrite fold_right_and_app; split; auto.
clear.
extensionality rho.
simpl.
unfold PROPx, LOCALx, local, lift1, SEPx.
rewrite fold_right_sepcon_app.
simpl.
normalize.
f_equal.
f_equal.
f_equal.
rewrite fold_right_and_app. auto.
Qed.

Lemma semax_frame1':
 forall {Espec: OracleKind} QFrame Frame Delta Delta1
     P Q c R P1 Q1 R1 P2 Q2 R2,
    semax Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    Delta1 = Delta ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c (LOCALx QFrame (SEPx Frame)) ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2++Frame))))).
Proof.
intros. subst.
eapply semax_pre.
apply H1.
apply semax_frame_PQR'; auto.
Qed.

Lemma semax_frame_seq':
 forall {Espec: OracleKind} QFrame Frame Delta 
     P Q c1 c2 R P1 Q1 R1 P2 Q2 R2 R3,
    semax Delta (PROPx P1 (LOCALx Q1 (SEPx R1))) c1 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c1 (LOCALx QFrame (SEPx Frame)) ->
    semax (update_tycon Delta c1) 
         (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2 ++ Frame)))) c2 R3 ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) (Ssequence c1 c2) R3.
Proof.
intros.
eapply semax_seq'.
eapply semax_pre.
apply H0.
apply semax_frame_PQR'; auto.
apply H.
apply H2.
Qed.

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
simpl_stackframe_of.
unfold POSTCONDITION, abbreviate.
apply (remember_value (eval_var _X (tarray tuint 16))); intro Xv.
change (`(eq Xv) (eval_var _X (tarray tuint 16))) 
    with (var _X (tarray tuint 16) Xv).
replace_SEP 0 (`(data_at_ Tsh (tarray tuint 16) Xv)) .
entailer!.
remember (hash_blocks init_registers hashed) as regs eqn:Hregs.
assert (Lregs: length regs = 8%nat) 
  by (subst regs; apply length_hash_blocks; auto).
assert (Zregs: Zlength regs = 8%Z)
 by (rewrite Zlength_correct; rewrite Lregs; reflexivity).
forward. (* data = in; *)
assert_PROP (isptr data); [  entailer | ].
 match goal with |- semax _ _ ?c _ =>
  eapply seq_assocN with (cs := sequenceN 8 c)
 end.
*
 eapply (semax_frame1' 
             [ var _X (tarray tuint 16) Xv ] 
             [`(data_at_ Tsh (tarray tuint 16) Xv);
                         `(data_block sh (intlist_to_Zlist b) data);
                         `(K_vector kv)]).
 + eapply sha256_block_load8 with (ctx:=ctx); eassumption.
 + simplify_Delta; reflexivity.
 +
    instantiate (1:=kv). instantiate (1:=data). (* this line should not be necessary *)
    entailer!.
 + auto 50 with closed.
*
abbreviate_semax.
simpl.
forward.  (* i = 0; *)

eapply (semax_frame_seq' [ var _X (tarray tuint 16) Xv ]
              [`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint regs)
        ctx)]).
+ replace Delta with Delta_loop1
    by (simplify_Delta; reflexivity).
    apply (sha256_block_data_order_loop1_proof _ sh b ctx data regs kv Xv); auto.
    apply Zlength_length in H; auto.
 +
    entailer!.
 + auto 50 with closed.
 +  simpl; abbreviate_semax.
 eapply (semax_frame_seq' [ ]
        [`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx);
         `(data_block sh (intlist_to_Zlist b) data)]).
match goal with |- semax _ _ ?c _ =>
  change c with block_data_order_loop2
end.
apply sha256_block_data_order_loop2_proof
              with (regs:=regs)(b:=b); eassumption.
 instantiate (1:=Xv).  instantiate (1:=kv). instantiate (1:=ctx). (* should not be necessary *)
entailer!.
auto 50 with closed.
abbreviate_semax.
eapply seq_assocN with (cs := add_them_back).
eapply (semax_frame1'  [  var _X (tarray tuint 16) Xv ]
             [`(K_vector kv);
             `(data_at_ Tsh (tarray tuint LBLOCKz) Xv);
             `(data_block sh (intlist_to_Zlist b) data)]).
apply (add_them_back_proof _ regs (Round regs (nthi b) 63) ctx); try assumption.
apply length_Round; auto.
simplify_Delta; reflexivity.
        instantiate (1:=kv).
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with (initialized _t Delta_loop1) 
 by (simplify_Delta; reflexivity).
clear Delta.
fold (hash_block regs b).
simple apply sha256_block_data_order_return; auto.
Qed.










