Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.
Require Import sublist.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac_NK.
Require Import sha.spec_hmacNK.

Lemma body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Update HMAC_Update_spec.
Proof.
start_function.
name ctx' _ctx.
name data' _data.
name len' _len.
unfold hmacstate_.
Intros ST.
destruct H as [DL1 [DL2 DL3]].
destruct h1; simpl in *.
destruct H0 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

Time assert_PROP (isptr c /\ field_compatible t_struct_hmac_ctx_st [] c)
   as H by entailer!. (*1.95*)
destruct H as [isptr_c FC_c].
assert (FC_md_ctx: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
 {red in FC_c. red. intuition.  constructor. trivial. constructor. reflexivity. }
assert (FC_i_ctx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] c).
 {red in FC_c. red. intuition.  constructor. trivial. right; left. reflexivity. }
unfold_data_at 1%nat.
rewrite (field_at_data_at  _ _ [StructField _i_ctx]).
rewrite (field_at_data_at _ _ [StructField _md_ctx]).   
unfold field_address. rewrite if_true by trivial. rewrite if_true by trivial.
simpl @nested_field_type.
make_Vptr c.
simpl. rewrite Int.add_zero.
Time forward_call (ctx, data, Vptr b i, d, Tsh, len, kv) s. (*12.7 secs*) 
 (*Issue: the forward_call takes ca 50secs in newComCert, instead of 6secs in Master, 
   no matter wther the field_at_data_at stuff s done outside of the call or inside.
   Resolved (11/4/15): with the faster canceler, now 12.5 sec.
 *)
  { (* rewrite field_at_data_at at 1.*)
    unfold sha256state_. Exists (fst ST).
    rewrite prop_true_andp by auto. 
    change_compspecs CompSpecs.
    change (Tstruct _SHA256state_st noattr) with  t_struct_SHA256state_st.
    cancel.
  }
  intuition.

rename H into HmacUpdate. simpl.
rewrite sublist_same in HmacUpdate; trivial.
Time forward. (*10.4*) (*Issue: leaves RHS in less normalized shape than previously*)
Exists (HMACabs s iSha oSha). Time entailer!. (*5.6*)
exists s; eauto.
unfold hmacstate_, sha256state_, hmac_relate.
Intros r. Exists (r,(iCtx ST, oCtx ST)).
simpl.
Time normalize. (*2.6*) 
unfold_data_at 3%nat. 
destruct ST as [ST1 [ST2 ST3]]. simpl in *.
rewrite (field_at_data_at _ _ [StructField _i_ctx]).
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
unfold field_address. rewrite !if_true by eauto.
simpl. rewrite Int.add_zero.
Time cancel. (*3.1*)
Time Qed. (*22*)