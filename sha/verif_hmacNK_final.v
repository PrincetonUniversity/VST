(*Processing time: 18mins. (master: 5min)*)
Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.
Require Import sublist.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac_NK.
Require Import sha.spec_hmacNK.
Require Import sha.vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Lemma withspacer_refl: forall sh a P, withspacer sh a a P = P.
Proof. intros. unfold withspacer. 
  rewrite <- Zminus_diag_reverse. trivial.
Qed.

Lemma body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Final HMAC_Final_spec.
Proof.
start_function.
name ctx' _ctx.
name md' _md.
rename lvar0 into buf.

assert_PROP (isptr md). entailer. rename H into isptrMD.
unfold hmacstate_. normalize. intros ST. normalize.
destruct h1; simpl in *.
destruct H as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

(*VST Issue: make_Vptr c. fails*)
assert_PROP (isptr c). entailer. apply isptrD in H; destruct H as [b [i PtrC]]; rewrite PtrC in *.


(*Call sha_Final*)
assert_PROP (field_compatible (tarray tuchar 32) [] buf). entailer. 
rename H into FC_buf.
rewrite <- memory_block_data_at_ ; trivial.

unfold_data_at 1%nat.

(*assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr b i))
  as FC_c by entailer!.
rename H into FC_c.
*)
(*
assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField 13%positive] (Vptr b i)).
  apply prop_right. red in FC_c; red; intuition. split; trivial. unfold t_struct_hmac_ctx_st.
    constructor. reflexivity.
rename H into FC_c13.
*)

(*
assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr b i))
  as FC_i_ctx by entailer!.
rewrite field_at_data_at at 1.
unfold field_address; rewrite if_true by assumption.
*)

destruct ST as [MD [iCTX oCTX]]. simpl in *.
forward_call (ctx, buf, Vptr b i, Tsh, kv). 
  { unfold sha256state_. Exists MD.
    entailer!.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]).
    simpl @nested_field_type.
    unfold field_address; rewrite if_true by auto.
    simpl. rewrite Int.add_zero. cancel.
  }
 unfold map at 1.  (* should not be necessary *)

(*VST Issue: calls to forward-call with type-incorrect WITH-list instantiations simply succeed immediately, 
  without doing anything. Instead, they should fail with a meaningful error message.*)

(*Coq (8.4?) Issue: type equality between
    @reptype CompSpecs t_struct_SHA256state_st * (s256state * s256state)
and @reptype CompSpecs t_struct_hmac_ctx_st
  is not corrrectly identified here: instead of the pose l:=...; assert (exists l':..., ...);
   use l' in data_at c, we'd really like to simply write
  data_at Tsh t_struct_hmac_ctx_st (default_val t_struct_SHA256state_st, (iCTX, oCTX)) c.*)

pose  (l:=(default_val t_struct_SHA256state_st, (iCTX, oCTX))).
assert (exists l':@reptype CompSpecs t_struct_hmac_ctx_st, l'=l). 
  exists l. trivial.
destruct H as [l' Hl']. subst l.

apply semax_pre with (P':=
  (PROP  ()
   LOCAL  (lvar _buf (tarray tuchar 32) buf; temp _md md; temp _ctx (Vptr b i);
   gvar sha._K256 kv)
   SEP  (`(K_vector kv); 
   `(data_at Tsh t_struct_hmac_ctx_st l' (Vptr b i));
   `(data_block Tsh (sha_finish ctx) buf);
   `(memory_block shmd 32 md)))).
{ entailer!.
      unfold_data_at 1%nat.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      simpl @nested_field_type.
      unfold field_address; rewrite if_true.
      simpl. rewrite Int.add_zero. cancel.
      hnf in H5; hnf; intuition.
      apply compute_legal_nested_field_spec'; repeat constructor.
}
subst l'.

(*
assert (field_compatible t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i)).
  red. red in FC_c. intuition. split; trivial.
    right. right. left. reflexivity.
rename H into FCO.
*)

unfold_data_at 1%nat.
rewrite (field_at_data_at _ _ [StructField _o_ctx]).
unfold field_address.
if_tac; [ | apply semax_pre with FF; [ entailer!; destruct H5; contradiction | apply semax_ff ]].
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
unfold field_address.
if_tac; [ | apply semax_pre with FF; [ entailer!; destruct H8; contradiction | apply semax_ff ]].

simpl.
rewrite Int.add_zero.
replace_SEP 2 `(memory_block Tsh 108 (Vptr b i)).
  { entailer!. 
    eapply derives_trans. apply data_at_data_at_.
    rewrite <- (memory_block_data_at_ Tsh _ _ H4). apply derives_refl.
  }

forward_call ((Tsh, Tsh), Vptr b i, Vptr b (Int.add i (Int.repr 216)), 
              mkTrep t_struct_SHA256state_st oCTX, 108) rv. 
subst rv; simpl. 

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. trivial.
rename H into FC_o_ctx;
rename H0 into FC_md_ctx.

(*Call sha256Update*)
forward_call (oSha, sha_finish ctx, Vptr b i, buf, Tsh, Z.of_nat SHA256.DigestLength, kv) updSha.
  { unfold sha256state_. normalize. Exists oCTX. normalize. cancel. } 
  { unfold SHA256.DigestLength. 
    rewrite oShaLen. simpl. intuition. }
simpl.
rename H into UPDSHA. rewrite sublist_same in UPDSHA; try omega. 
unfold sha256state_. normalize. intros updShaST. normalize. rename H into updShaREL. 

(*Call SHA_Final*)
forward_call (updSha, md, Vptr b i, shmd, kv). (*Issue: takes 10 times longer than in master*)
  { unfold sha256state_. normalize. Exists updShaST. normalize. cancel. } 
simpl.

forward.
Exists buf. normalize.
Exists (sha_finish updSha, HMACabs updSha iSha oSha). normalize.
apply andp_right. apply prop_right. split; trivial.
  exists updSha; eauto.
cancel.
unfold data_block. rewrite SFL. normalize.
apply derives_trans with (Q:= hmacstate_PostFinal (HMACabs updSha iSha oSha)
      (Vptr b i) *
    data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr (sha_finish ctx))) buf).
2: cancel.
cancel.
unfold hmacstate_PostFinal, hmac_relate_PostFinal. normalize.
Exists (updShaST, (iCTX, oCTX)). normalize.
match goal with |- _ |-- data_at _ _ ?A _ =>
change A with (default_val t_struct_SHA256state_st, (iCTX, oCTX))
end.
Time unfold_data_at 2%nat. (* VST Issue: unfold_field_at here takes ages ... now 0.623 sec *)
cancel.
rewrite (field_at_data_at _ _ [StructField _o_ctx]). 
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
unfold data_at_. unfold field_at_.
rewrite field_at_data_at.
simpl.
unfold field_address. rewrite if_true by trivial. rewrite if_true by trivial. rewrite if_true by trivial.
trivial.
Qed.
