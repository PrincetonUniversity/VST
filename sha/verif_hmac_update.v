Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac.
Require Import sha.spec_hmac.

Lemma updatebodyproof Espec wsh sh c d len data gv (h1 : hmacabs)
      (H : has_lengthD (s256a_len (absCtxt h1)) len data)
   (Hwsh: writable_share wsh)
   (Hsh: readable_share sh):
@semax CompSpecs Espec (func_tycontext f_HMAC_Update HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _ctx c; temp _data d;
           temp _len (Vint (Int.repr len)); gvars gv)
   SEP  (K_vector gv; hmacstate_ wsh h1 c; data_block sh data d))
  (Ssequence (fn_body f_HMAC_Update) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP  (K_vector gv; hmacstate_ wsh (hmacUpdate data h1) c;
         data_block sh data d))) emp).
Proof. abbreviate_semax.
unfold hmacstate_.
Intros ST.
destruct H as [DL1 [DL2 DL3]].
destruct h1; simpl in DL3,H0|-*.
destruct H0 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

Time assert_PROP (isptr c /\ field_compatible t_struct_hmac_ctx_st [] c)
   as H by entailer!. (*1.95*)
destruct H as [isptr_c FC_c].
assert (FC_md_ctx: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
 {red in FC_c. repeat split; try solve [apply FC_c]. constructor; trivial. }
assert (FC_i_ctx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] c).
 {red in FC_c. repeat split; try solve [apply FC_c]. simpl. right; left; reflexivity. }
unfold_data_at (@data_at CompSpecs _ _ _ c). 
freeze FR := - (K_vector _) (field_at _ _ [StructField _md_ctx] _ _) (data_block _ _ d).
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
rewrite field_address_offset by auto with field_compatible.
simpl @nested_field_type.
make_Vptr c.
simpl. rewrite Ptrofs.add_zero.
Time forward_call (ctx, data, Vptr b i, wsh, d, sh, len, gv). (*6 versus 21 *)
  { unfold sha256state_. Exists (fst ST).
    rewrite prop_true_andp by auto.
    change_compspecs CompSpecs.
   change (@data_block spec_sha.CompSpecs Tsh data d)
     with (@data_block CompSpecs Tsh data d).
    change (Tstruct _SHA256state_st noattr) with  t_struct_SHA256state_st.
    cancel.
  }
split; [ | split3]; auto. rep_omega. simpl; rep_omega.
rewrite sublist_same; trivial.
freeze FR1 := - (FRZL FR).
Time forward. (*12 versus 12.4*)
simpl.
thaw FR1.
unfold hmacstate_, sha256state_, hmac_relate.
Intros r.  Exists (r,(iCtx ST, oCtx ST)).
Time entailer!. (*2.1*)
thaw FR.
unfold_data_at (@data_at CompSpecs _ _ _ (Vptr b i)).
destruct ST as [ST1 [ST2 ST3]]. simpl in *.
Time cancel. (*0.5*)
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
rewrite field_address_offset by auto with field_compatible.
simpl. 
change (Tstruct _SHA256state_st noattr) with  t_struct_SHA256state_st.
change_compspecs CompSpecs.
rewrite Ptrofs.add_zero. apply derives_refl. 
Time Qed. (*1.8*)

Lemma body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs
       f_HMAC_Update HMAC_Update_spec.
Proof.
start_function.
apply updatebodyproof; trivial.
Qed.
