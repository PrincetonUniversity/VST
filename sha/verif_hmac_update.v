Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac091c.
Require Import sha.spec_hmac.

Lemma body_hmac_update: semax_body Vprog Gtot 
       f_HMAC_Update HMAC_Update_spec.
Proof.
start_function.
(*rewrite <- SHACTX in *.*)
name ctx' _ctx.
name data' _data.
name len' _len.
unfold hmacstate_. normalize. intros ST. normalize.
destruct H as [DL1 [DL2 DL3]].
destruct h1; simpl in *.
destruct H0 as [reprMD [reprI [reprO [iShaLen [oShaLen [KeyST [l [KeylenST [KL ZLen]]]]]]]]].
rewrite KL in *.
erewrite (field_except_at_lemma _ _ _md_ctx nil); try reflexivity.
simpl. 

(*By rewriting with field_at_data_at here instead of inside the forward_call,
  we remember facts SCc and ACc which are necessary for performing the
  "inverse" conversion at the end of this proof*)  
rewrite field_at_data_at; try reflexivity. simpl. normalize. 
rename H into SCc. rename H0 into ACc.

eapply semax_seq'. 
frame_SEP 0 2 3.
remember (ctx, data, c, d, Tsh, len, KV) as WITNESS.
forward_call WITNESS.
  { assert (FR: Frame =nil).
       subst Frame. reflexivity.
    rewrite FR. clear FR Frame. 
    subst WITNESS. entailer. 
    cancel.
    unfold sha256state_. apply exp_right with (x:= mdCtx ST). entailer.
    (*rewrite field_at_data_at; try reflexivity. simpl. entailer.*)
  }
after_call. subst WITNESS. normalize. simpl. (* normalize.*)

assert (FF: firstn (Z.to_nat len) data = data). 
    rewrite DL1 in *. 
    apply firstn_same. rewrite Zlength_correct, Nat2Z.id. omega.
rewrite FF in *. 


(**** Again, distribute EX over lift*)
apply semax_pre with (P' :=EX  x : s256abs,
  (PROP  ()
   LOCAL  (tc_environ Delta; `(eq c) (eval_id _ctx); `(eq d) (eval_id _data);
   `(eq (Vint (Int.repr len))) (eval_id _len);
   (*`(eq KV) (eval_var sha._K256 (tarray tuint 64))*)
     (fun rho => (eq KV) (eval_var sha._K256 (tarray tuint 64) (globals_only rho))))
   SEP 
   (`(fun a : environ =>
      (PROP  (update_abs data (*(firstn (Z.to_nat len) data)*) ctx x)
       LOCAL ()
       SEP  (`(K_vector KV); `(sha256state_ x c); `(data_block Tsh data d)))
        a) globals_only;
   `(field_except_at Tsh t_struct_hmac_ctx_st _md_ctx [] (snd ST) c)))
). entailer. rename x into s. apply exp_right with (x:=s). entailer.
apply extract_exists_pre. intros s. normalize. simpl. normalize.
(********************************************************)
rename H into HmacUpdate.

(*WHY IS THIS NEEDED?*) unfold MORE_COMMANDS, abbreviate.
forward.
(*rewrite Zlength_correct, Nat2Z.id in FF. rewrite FF.*)
apply exp_right with (x:= HMACabs s iSha oSha (Int.unsigned l) key). entailer.
apply andp_right. apply prop_right. exists s; eauto.
cancel. 
unfold hmacstate_, sha256state_, hmac_relate. normalize.
apply exp_right with (x:=(r, (iCtx ST, (oCtx ST, (Vint l, Key ST))))). 
simpl. entailer.
apply andp_right. apply prop_right. exists l; eauto.
erewrite (field_except_at_lemma Tsh t_struct_hmac_ctx_st _md_ctx nil); try reflexivity.
destruct ST as [ST1 [ST2 [ST3 [ST4 ST5]]]]. simpl in *. subst ST4. cancel.
rewrite field_at_data_at; try reflexivity. simpl. normalize. 
Qed.