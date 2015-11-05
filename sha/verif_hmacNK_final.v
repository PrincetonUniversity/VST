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

Time assert_PROP (isptr md) as isptrMD by entailer!. (*0.6*)
unfold hmacstate_. Time normalize. (*8.1*)
intros ST. Time normalize. (*2*)
destruct h1; simpl in *.
destruct H as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

(*VST Issue: make_Vptr c. fails*)
Time assert_PROP (isptr c) as Pc by entailer!. (*1.4*) 
apply isptrD in Pc; destruct Pc as [b [i PtrC]]; rewrite PtrC in *.

(*Call sha_Final*)
Time assert_PROP (field_compatible (tarray tuchar 32) [] buf)
  as FC_buf by entailer!. (*1.3*) 
Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr b i))
  as FC_ctx by entailer!. (*1.6*) 
assert (FC_mdctx: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr b i)).
{ clear - FC_ctx. red; red in FC_ctx. intuition.
  split; trivial. left; trivial. }
assert (FC_octx: field_compatible t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i)).
{ clear - FC_ctx. red; red in FC_ctx. intuition.
  split; trivial. right; right; left; trivial. }
rewrite <- memory_block_data_at_ ; trivial.

unfold_data_at 1%nat.

destruct ST as [MD [iCTX oCTX]]. simpl in *.
Time forward_call (ctx, buf, Vptr b i, Tsh, kv). (*9.5*)
  { unfold sha256state_. Exists MD.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]).
    simpl @nested_field_type.
    unfold field_address; rewrite if_true by trivial.
    simpl. rewrite Int.add_zero. Time (normalize; cancel). (*5.7*)
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
   LOCAL  (lvar _buf (tarray tuchar 32) buf; temp _md md; 
           temp _ctx (Vptr b i); gvar sha._K256 kv)
   SEP  (`(K_vector kv); 
   `(data_at Tsh t_struct_hmac_ctx_st l' (Vptr b i));
   `(data_block Tsh (sha_finish ctx) buf);
   `(memory_block shmd 32 md)))).
{ Time entailer!. (*8*)
      unfold_data_at 1%nat.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      simpl @nested_field_type.
      unfold field_address; rewrite if_true by trivial.
      simpl. rewrite Int.add_zero. Time cancel. (*3.4*)
      (*Unnecessary, presumably due to introduction of FC_octx above:
      hnf in H5; hnf; intuition.*)
      (*Unnecessary, presumably due to introduction of FC_mdctx above:
        apply compute_legal_nested_field_spec'; repeat constructor.*)
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
unfold field_address. rewrite if_true by trivial. 
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
unfold field_address. rewrite if_true by trivial.

simpl.
rewrite Int.add_zero.
replace_SEP 2 `(memory_block Tsh 108 (Vptr b i)).
  { Time entailer!. (*1*) 
    eapply derives_trans. apply data_at_data_at_.
    rewrite <- (memory_block_data_at_ Tsh _ _ H2). apply derives_refl.
  }

Time forward_call ((Tsh, Tsh), Vptr b i, Vptr b (Int.add i (Int.repr 216)), 
              mkTrep t_struct_SHA256state_st oCTX, 108) rv. (*7.7*) 
simpl. cancel. 
subst rv; simpl. 

assert (SFL: Zlength (sha_finish ctx) = 32). 
  unfold sha_finish. destruct ctx. 
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'; trivial.

(*Call sha256Update*)
Time forward_call (oSha, sha_finish ctx, Vptr b i, buf, Tsh, Z.of_nat SHA256.DigestLength, kv) updSha.
  (*8.1*)
  { unfold sha256state_. Time normalize. (*1.3*)
    Exists oCTX. Time (normalize; cancel). (*6.8*) } 
  { unfold SHA256.DigestLength. 
    rewrite oShaLen. simpl; intuition. }
simpl.
rename H into UPDSHA. rewrite sublist_same in UPDSHA; try omega. 
unfold sha256state_. Time normalize. (*5.3*)
intros updShaST. Time normalize. (*1.3*)
rename H into updShaREL. 

(*Call SHA_Final*)
Time forward_call (updSha, md, Vptr b i, shmd, kv). (*27 SLOW. takes 3.2 in version with freezer*) (*Issue: was faster in old_compcert, so probably related to new memory/type treatment*)
  { unfold sha256state_. Time normalize. (*1.4*)
    Exists updShaST. Time (normalize; cancel). (*3.4*)} 
simpl.

Time forward. (*9.7*)
Exists buf. Time normalize. (*3.2*)
Exists (sha_finish updSha, HMACabs updSha iSha oSha). Time normalize. (*3.1*)
apply andp_right. apply prop_right. split; trivial.
  exists updSha; eauto.
Time cancel. (*3.6*)
unfold data_block. rewrite SFL. Time normalize. (*2.1*)
apply derives_trans with (Q:= hmacstate_PostFinal (HMACabs updSha iSha oSha)
      (Vptr b i) *
    data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr (sha_finish ctx))) buf).
2: cancel.
 change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar 32))
     with (@data_at CompSpecs Tsh (tarray tuchar 32)).
 change (@data_at_ spec_sha.CompSpecs Tsh t_struct_SHA256state_st)
     with (@data_at_ CompSpecs Tsh t_struct_SHA256state_st).
 cancel.

unfold hmacstate_PostFinal, hmac_relate_PostFinal. normalize.
Exists (updShaST, (iCTX, oCTX)). normalize.
match goal with |- _ |-- data_at _ _ ?A _ =>
change A with (default_val t_struct_SHA256state_st, (iCTX, oCTX))
end.
Time unfold_data_at 2%nat. (* 0.5, was slow*)
Time cancel. (*6.3*)
rewrite (field_at_data_at _ _ [StructField _o_ctx]). 
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
unfold data_at_. unfold field_at_.
rewrite field_at_data_at.
simpl.
unfold field_address. rewrite if_true by trivial. rewrite if_true by trivial. rewrite if_true by trivial.
Time trivial. (*3*)
Time Qed. (*43*)
