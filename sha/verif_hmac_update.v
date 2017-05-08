Require Import floyd.proofauto.
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

Lemma updatebodyproof Espec c d len data kv (h1 : hmacabs)
      (H : has_lengthD (s256a_len (absCtxt h1)) len data):
@semax CompSpecs Espec (func_tycontext f_HMAC_Update HmacVarSpecs HmacFunSpecs)
  (PROP  ()
   LOCAL  (temp _ctx c; temp _data d;
           temp _len (Vint (Int.repr len)); gvar sha._K256 kv)
   SEP  (K_vector kv; hmacstate_ h1 c; data_block Tsh data d))
  (Ssequence (fn_body f_HMAC_Update) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP  (K_vector kv; hmacstate_ (hmacUpdate data h1) c;
         data_block Tsh data d))) emp).
Proof. abbreviate_semax.
unfold hmacstate_.
Intros ST.
destruct H as [DL1 [DL2 DL3]].
destruct h1; simpl in *.
destruct H0 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].

Time assert_PROP (isptr c /\ field_compatible t_struct_hmac_ctx_st [] c)
   as H by entailer!. (*1.95*)
destruct H as [isptr_c FC_c].
assert (FC_md_ctx: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] c).
 {red in FC_c. repeat split; try solve [apply FC_c]. constructor; trivial. }
assert (FC_i_ctx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] c).
 {red in FC_c. repeat split; try solve [apply FC_c]. simpl. right; left; reflexivity. }
unfold_data_at 1%nat.
freeze [2;3] FR.
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
rewrite field_address_offset by auto with field_compatible.
simpl @nested_field_type.
make_Vptr c.
simpl. rewrite Int.add_zero.
Time forward_call (ctx, data, Vptr b i, d, Tsh, len, kv). (*6 versus 21 *)
  { unfold sha256state_. Exists (fst ST).
    rewrite prop_true_andp by auto.
    change_compspecs CompSpecs.
   change (@data_block spec_sha.CompSpecs Tsh data d)
     with (@data_block CompSpecs Tsh data d).
    change (Tstruct _SHA256state_st noattr) with  t_struct_SHA256state_st.
    cancel.
  }
split; [ intuition | omega ].
rewrite sublist_same; trivial.
freeze [0;1;2] FR1.
Time forward. (*12 versus 12.4*)
thaw FR1.
change (@data_block spec_sha.CompSpecs Tsh data d)
     with (@data_block CompSpecs Tsh data d). Time cancel. (*0.2*)
unfold hmacstate_, sha256state_, hmac_relate.
Intros r.  Exists (r,(iCtx ST, oCtx ST)).
Time entailer!. (*2.1*)
thaw FR.
unfold_data_at 2%nat.
destruct ST as [ST1 [ST2 ST3]]. simpl in *.
Time cancel. (*0.5*)
rewrite (field_at_data_at _ _ [StructField _md_ctx]).
rewrite field_address_offset by auto with field_compatible.
simpl. rewrite Int.add_zero. apply derives_refl.
Time Qed. (*9.5 versus 20.3*)

Lemma body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs
       f_HMAC_Update HMAC_Update_spec.
Proof.
start_function.
apply updatebodyproof; trivial.
Qed.