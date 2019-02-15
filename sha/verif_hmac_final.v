(*Processing time: 18mins. (master: 5min)*)
Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac.
Require Import sha.spec_hmac.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Lemma withspacer_refl: forall sh a P, withspacer sh a a P = P.
Proof. intros. unfold withspacer.
  rewrite <- Zminus_diag_reverse. trivial.
Qed.

Lemma finalbodyproof Espec c md wsh shmd gv buf (h1 : hmacabs)
      (Hwsh: writable_share wsh)
      (SH : writable_share shmd):
@semax CompSpecs Espec (func_tycontext f_HMAC_Final HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _buf (tarray tuchar 32) buf; temp _md md;
           temp _ctx c; gvars gv)
   SEP  (data_at_ Tsh (tarray tuchar 32) buf; hmacstate_ wsh h1 c;
         K_vector gv; memory_block shmd 32 md))
  (Ssequence (fn_body f_HMAC_Final) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP  (K_vector gv; hmacstate_PostFinal wsh (fst (hmacFinal h1)) c;
               data_block shmd (snd (hmacFinal h1)) md)))
     (stackframe_of f_HMAC_Final)%assert).
Proof. intros. abbreviate_semax.
Time assert_PROP (isptr md) as isptrMD by entailer!. (*0.6*)
unfold hmacstate_.
Intros ST.
destruct h1; simpl in H|-*.
destruct H as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

(*VST Issue: make_Vptr c. fails*)
Time assert_PROP (isptr c) as Pc by entailer!. (*1.4*)
apply isptrD in Pc; destruct Pc as [b [i PtrC]]; rewrite PtrC in *.

(*Call sha_Final*)
Time assert_PROP (field_compatible (tarray tuchar 32) [] buf)
  as FC_buf by entailer!. (*1.3*)
Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr b i))
  as FC_ctx by entailer!. (*1.4*)
assert (FC_mdctx: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr b i)).
{ clear - FC_ctx. red; red in FC_ctx. intuition.
  split; trivial. left; trivial. }
assert (FC_octx: field_compatible t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr b i)).
{ clear - FC_ctx. red; red in FC_ctx. intuition.
  split; trivial. right; right; left; trivial. }
rewrite <- memory_block_data_at_ ; trivial.
unfold_data_at (data_at _ _ _ _).

destruct ST as [MD [iCTX oCTX]]. simpl in reprMD,reprI,reprO |- *.
freeze FR1 := - (memory_block _ _ buf) (field_at _ _ [StructField _md_ctx] _ _) (K_vector _).
Time forward_call (ctx, buf, Vptr b i, wsh, Tsh, gv). (*3.6 versus 9.5*)
  { unfold sha256state_. Exists MD.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    normalize. simpl.
   change (Tstruct _SHA256state_st noattr) with  t_struct_SHA256state_st.
   change_compspecs CompSpecs.
   cancel.
  }

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
   gvars gv)
   SEP  (K_vector gv;
     data_at wsh t_struct_hmac_ctx_st l' (Vptr b i);
     data_block Tsh (SHA256.SHA_256 ctx) buf;
     memory_block shmd 32 md))).
{ Time entailer!. (*5.2versus 11.7*)
      unfold_data_at (@data_at CompSpecs _ t_struct_hmac_ctx_st _ _). thaw FR1.
      rewrite (field_at_data_at wsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      rewrite field_address_offset by auto with field_compatible.
      simpl. rewrite Ptrofs.add_zero.
      fold t_struct_SHA256state_st.
      change (Tstruct _SHA256state_st noattr) with t_struct_SHA256state_st.
      Time cancel. (*0.9*)
}
subst l'. clear FR1.
freeze FR2 := - (@data_at CompSpecs _ _ _ (Vptr b i)).
unfold_data_at (@data_at CompSpecs _ _ _ (Vptr b i)).
rewrite (field_at_data_at _ _ [StructField _o_ctx]).
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
rewrite field_address_offset by auto with field_compatible.
rewrite field_address_offset by auto with field_compatible.
unfold offset_val; simpl.
rewrite Ptrofs.add_zero.
replace_SEP 1 (memory_block wsh 108 (Vptr b i)).
  { Time entailer!. (*1.3 versus 1.6*)
    eapply derives_trans. apply data_at_data_at_.
    rewrite <- (memory_block_data_at_ wsh _ _ H). apply derives_refl.
  }
freeze FR3 := - (memory_block _ _ (Vptr b i)) (@data_at CompSpecs _ _ _ (Vptr b (Ptrofs.add i (Ptrofs.repr 216)))).
Time forward_call (wsh, wsh, Vptr b i, Vptr b (Ptrofs.add i (Ptrofs.repr 216)),
              mkTrep t_struct_SHA256state_st oCTX, 108). (*5 versus 8.7*)
(* Time solve [simpl; cancel]. (*0.1 versus 1*) *)

assert (SFL: Zlength (SHA256.SHA_256 ctx) = 32).
  rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'; trivial.

(*Call sha256Update*)
thaw FR3. thaw FR2.
Time forward_call (oSha, SHA256.SHA_256 ctx, Vptr b i, wsh, buf, Tsh, Z.of_nat SHA256.DigestLength, gv).
  (*5.1 versus 10.2*)
  { unfold sha256state_.
    Exists oCTX. Time normalize. (*2.9 versus 3.2*)
    simpl. change_compspecs CompSpecs.
(*    rewrite prop_true_andp by auto.*)
(*    change (@data_block spec_sha.CompSpecs Tsh (SHA256.SHA_256 ctx))
     with (@data_block CompSpecs Tsh (SHA256.SHA_256 ctx)).
*)
     Time cancel. (*0.2 versus 1.6*) }
  { unfold SHA256.DigestLength.
    rewrite oShaLen. simpl; intuition. }
simpl.
rewrite sublist_same; try omega.
unfold sha256state_. Intros updShaST.
rename H into updShaREL.

(*Call SHA_Final*)
remember (oSha ++ SHA256.SHA_256 ctx) as updSha.

Time forward_call (updSha, md, Vptr b i, wsh, shmd, gv). (*4.2 versus 21 SLOW*)
  { unfold sha256state_.
    Exists updShaST.
    change_compspecs CompSpecs. entailer!. }

Time forward. (*Sreturn None; 2.7 versus 10.2*)
(*    change (@data_block spec_sha.CompSpecs shmd (SHA256.SHA_256 updShaST) md)
     with (@data_block CompSpecs shmd (SHA256.SHA_256 updShaST) md).
     Time cancel. (*0.5*)*)
(*change_compspecs CompSpecs.*)
unfold data_block. simpl. rewrite SFL.
Time (normalize; cancel). (*5.5*)

unfold hmacstate_PostFinal, hmac_relate_PostFinal.
Exists (updShaST, (iCTX, oCTX)). rewrite prop_true_andp by (split3; auto).
match goal with |- _ |-- data_at _ _ ?A _ =>
change A with (default_val t_struct_SHA256state_st, (iCTX, oCTX))
end.
Time unfold_data_at (@data_at CompSpecs _ _ _ (Vptr b i)).
Time assert_PROP (field_compatible t_struct_SHA256state_st [] (Vptr b i)) as FC by entailer!. (*1.2*)
Time cancel. (*0.7*)
unfold data_at_, field_at_.
rewrite (field_at_data_at _ _ [StructField _o_ctx]).
rewrite field_address_offset by auto with field_compatible. Time cancel. (*0.2*)
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
rewrite field_address_offset by auto with field_compatible. simpl.
rewrite field_at_data_at.
rewrite field_address_offset by auto with field_compatible. simpl.  apply derives_refl.
Time Qed. (*VST 2.0: 6s*) 

Lemma body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs
       f_HMAC_Final HMAC_Final_spec.
Proof.
start_function.
apply finalbodyproof; trivial.
Time Qed.
