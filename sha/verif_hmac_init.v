Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.spec_hmac.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac091c.

Require Import sha.verif_hmac_init_part1.
(*updconents = (upd contents vi (valinject _ v2)) *)
(*Lemma semax_loadstore_array':
  forall {Espec: OracleKind},
 forall vi lo hi t1 gfs contents updcontents v1 v2 (Delta: tycontext) e1 e2 sh P P', 
   writable_share sh ->
   reptype t1 = val -> 
   type_is_by_value t1 ->
   legal_alignas_type t1 = true ->
   typeof e1 = t1 ->
   tc_val t1 v2 ->
   in_range lo hi vi ->
   P |--  rel_lvalue e1  (eval_binop Oadd (tptr t1) tint v1 (Vint (Int.repr vi)) )
           && rel_expr (Ecast e2 t1) v2 
           && (`(array_at sh t1 gfs lo hi contents v1) * P') ->
   @semax Espec Delta (|> P) (Sassign e1 e2) 
          (normal_ret_assert (`(array_at sh t1 gfs lo hi updcontents v1) * P')).
Proof.
intros until 2. intros BYVAL LAT H1 TCV RANGE H2. 
  eapply semax_pre_post; [| | eapply semax_loadstore]; try eassumption.
  apply andp_left2; apply derives_refl.
 intros.
Focus 2.
 rewrite H1.
 repeat rewrite prop_true_andp by auto.
 rewrite <- (andp_dup P).
 eapply derives_trans.
 apply andp_derives. apply H2. apply derives_refl.
 instantiate (4:=v2).
(* normalize. *)
 apply andp_right.
 apply andp_right.
 apply andp_right. entailer.
 apply andp_left1. apply andp_left1. apply andp_left1. apply derives_refl.
 apply andp_left1. apply andp_left1. apply andp_left2. apply derives_refl.
 intro rho. unfold_lift. simpl.
 apply andp_left1. apply andp_left2.
 erewrite (split3_array_at sh t1 gfs lo vi). contents hi v1 (repinject _ (contents vi))); auto.
 rewrite (sepcon_comm (array_at t1 sh contents lo vi v1)).
 repeat rewrite sepcon_assoc.
 apply sepcon_derives.
 apply derives_refl.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives; [ |  apply derives_refl].
 apply sepcon_derives; apply derives_refl'; apply equal_f; apply array_at_ext; intros;
 rewrite upd_neq by omega; auto.
 clear - H0 BYVAL.
 destruct t1; try contradiction.
 destruct i,s; reflexivity.
 destruct s; reflexivity.
 destruct f; reflexivity.
 reflexivity.
*
 apply andp_left2.
 apply normal_ret_assert_derives'.
 intro rho.
 unfold_lift; simpl.
  rewrite H1.
   rewrite <- field_at_Tarray.
 match goal with |- ?A |-- _ => set (XX := A) end.
  rewrite (split3_array_at' sh t1 vi (*(upd contents vi (valinject t1 v2))*) lo hi updcontents v1 v2); auto.
 2: rewrite upd_eq; apply valinject_JMeq; auto.
 rewrite (sepcon_comm (array_at t1 sh (upd contents vi (valinject t1 v2)) lo vi v1)).
 repeat rewrite sepcon_assoc.
 unfold XX; clear XX.
 apply derives_refl.
*
 rewrite H1.
 repeat rewrite prop_true_andp by auto.
 rewrite <- (andp_dup P).
 eapply derives_trans.
 apply andp_derives. apply H2. apply derives_refl.
(* normalize. *)
 apply andp_right.
 apply andp_right.
 apply andp_left1. apply andp_left1. apply andp_left1. apply derives_refl.
 apply andp_left1. apply andp_left1. apply andp_left2. apply derives_refl.
 intro rho. unfold_lift. simpl.
 apply andp_left1. apply andp_left2.
 rewrite (split3_array_at' vi t1 sh contents lo hi v1 (repinject _ (contents vi))); auto.
 rewrite (sepcon_comm (array_at t1 sh contents lo vi v1)).
 repeat rewrite sepcon_assoc.
 apply sepcon_derives.
 apply derives_refl.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives; [ |  apply derives_refl].
 apply sepcon_derives; apply derives_refl'; apply equal_f; apply array_at_ext; intros;
 rewrite upd_neq by omega; auto.
 clear - H0 BYVAL.
 destruct t1; try contradiction.
 destruct i,s; reflexivity.
 destruct s; reflexivity.
 destruct f; reflexivity.
 reflexivity.
Qed.

(*(upd contents vi (valinject _ v2))*)
Lemma NEWsemax_loadstore_array:
  forall {Espec: OracleKind},
 forall n k gfs vi lo hi t1 (contents updcontents:list (reptype (nested_field_type2 t1 (ArraySubsc 0 :: gfs)))) 
        v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R, 
  (*H0*) reptype t1 = val -> 
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tarray t1 k->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at sh t1 gfs lo hi contents v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2) 
          (normal_ret_assert 
           (PROPx P (LOCALx Q (SEPx 
            (replace_nth n R `(array_at sh t1 gfs lo hi updcontents v1)))))).
Proof. 
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl. 
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed.*)

(*
Lemma ZnthV_map_Vint_is_int_I8: forall l (i : Z) ,
       0 <= i < Zlength l -> 
is_int I8 Unsigned
  (ZnthV (Tint I8 Unsigned noattr)
     (map Vint (map Int.repr (map Byte.unsigned l))) i).
Proof.
intros.
unfold ZnthV.
if_tac; [omega | ].
assert (Z.to_nat i < length l)%nat.
destruct H.
rewrite Zlength_correct in H1.
apply Z2Nat.inj_lt in H1; try omega.
rewrite Nat2Z.id in H1. auto.
unfold is_int. simpl.
clear - H1.
revert l H1; induction (Z.to_nat i); destruct l; intros; simpl in *.
omega. rewrite Int.unsigned_repr. apply Byte.unsigned_range_2. 
  destruct (Byte.unsigned_range_2 i0). split. omega.
  assert ( Byte.max_unsigned <= Int.max_unsigned).
    unfold Byte.max_unsigned, Int.max_unsigned. 
    unfold Byte.modulus, Int.modulus, Byte.wordsize, Int.wordsize. simpl. omega.
   omega.
  omega.
 apply IHn; omega.
Qed.

Lemma array_at_local_facts'':
  forall (t : type) (sh : Share.t) (f : Z -> reptype t) (lo hi : Z) (v : val),
  array_at t sh f lo hi v
  = array_at t sh f lo hi v && !!isptr v &&
      !!offset_in_range (sizeof t * lo) v &&
      !!offset_in_range (sizeof t * hi) v && !!align_compatible t v.
Proof. intros. apply pred_ext; normalize. apply andp_right; entailer.
  unfold array_at. entailer.
Qed. 

Lemma xor_pad_result: forall key i N z (isbyte_key : Forall isbyteZ key) (I : 0 <= i < 64)
        (HN : nth (Z.to_nat i) (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef =
              Vint N),
      ZnthV tuchar (map Vint (map Int.repr
           (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) (Byte.repr z)))) i =
      Vint (Int.zero_ext 8 (Int.xor (Int.repr z) N)).
Proof. intros. unfold cVint, ZnthV, upd. if_tac. omega. simpl.
            erewrite @nth_mapVint'.
            Focus 2. unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. 
                     repeat rewrite map_length. 
                     rewrite combine_length, length_SF, map_length, mkKey_length. simpl.
                     split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            f_equal. 
              unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg.
              eapply (@nthD_1 _ _ _ _ _ _ _ Int.zero) in HN.
              2: rewrite map_length, mkKey_length; apply (Z2Nat.inj_lt _ 64); omega.
              destruct HN as [zz [Inzz [NTH II]]]. inversion II; clear II; subst zz.
              eapply @nthD_1 in H1.
              2: rewrite mkKey_length; apply (Z2Nat.inj_lt _ 64); omega.
              destruct H1 as [yy [Inyy [NTH II]]]. 
              erewrite mapnth'. instantiate (1:=Byte.repr z). 2: reflexivity.
              erewrite mapnth'. instantiate (1:=(Byte.repr z, Byte.zero)).
              2: simpl; rewrite Byte.xor_zero; trivial.
              rewrite combine_nth.
              2: rewrite map_length, mkKey_length, length_SF; trivial.
              erewrite mapnth'. 2: reflexivity. (*instantiate (1:=0).*) rewrite NTH.
                unfold HMAC_SHA256.sixtyfour; rewrite nth_list_repeat', Byte.xor_commut; simpl.
              2:  apply (Z2Nat.inj_lt _ 64); omega.
              assert (IB: Forall isbyteZ (HMAC_SHA256.mkKey key)). 
               apply Forall_forall. unfold HMAC_SHA256.mkKey; intros.
               destruct (Zlength key >? Z.of_nat SHA256.BlockSize). 
               specialize (zeropad_isbyteZ _ (isbyte_sha key)); intros.
               eapply Forall_forall; try eapply H1. assumption.
               specialize (zeropad_isbyteZ _ isbyte_key); intros.
               eapply Forall_forall; try eapply H1. assumption.
              eapply Forall_forall in IB; try eassumption.
             apply Int.same_bits_eq. intros. unfold Int.zero_ext. 
             repeat rewrite Int.testbit_repr; trivial.
             rewrite Int.Zzero_ext_spec; try omega. 
             if_tac. unfold Ipad.
               repeat rewrite Ztest_Bytetest. 
               assert (BZ: 0 <= i0 < Byte.zwordsize). unfold Byte.zwordsize; simpl. omega.            
               rewrite Byte.bits_xor; trivial.
               repeat rewrite Byte.testbit_repr; trivial.
               subst N. rewrite Ztest_Inttest, Int.bits_xor; trivial.
               repeat rewrite Int.testbit_repr; trivial.
             repeat rewrite Ztest_Bytetest. 
               apply Byte.bits_above. apply H1.
Qed.
*)
Definition postResetHMS key (iS oS: s256state): hmacstate :=
  (emptySha, (iS, (oS, 
   (if zlt 64 (Zlength key) then Vint (Int.repr 32) else Vint (Int.repr (Zlength key)), 
   map Vint (map Int.repr (HMAC_SHA256.mkKey key)))))).

Lemma Tarray_emp_field_compatible b ofs: field_compatible (Tarray tuchar 0 noattr) [] (Vptr b ofs).
        Proof. split; simpl. trivial. split. reflexivity. split. reflexivity.
          split. apply (size_0_compatible (Tarray tuchar 0 noattr) (eq_refl _) (Vptr b ofs)).
          split. apply Z.divide_1_l.
          constructor; simpl; trivial.
        Qed. 
        
Lemma data_Tarray_array_at_emp C b ofs: data_at Tsh (Tarray tuchar 0 noattr) C (Vptr b ofs)
                  = !!field_compatible (Tarray tuchar 0 noattr) [] (Vptr b ofs) && emp.
        Proof.
          rewrite data_at_field_at.
          erewrite field_at_Tarray. 2: reflexivity. 2: apply JMeq.JMeq_refl.
          rewrite array_at_emp; trivial. omega.
        Qed.

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
simpl_stackframe_of.
destruct H as [KL1 [KL2 KL3]]. normalize.
(*Sset _reset (Econst_int (Int.repr 0) tint)*)
forward.

(*unfold data_block.*) normalize. 

(*isolate branch if (key != NULL) *)
apply seq_assoc.

remember (EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs/\ (r=0 \/ r=1))
                    LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
                    `(eq pad) (eval_var _pad (tarray tuchar 64));
                    `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
                    `(eq (Vint (Int.repr l))) (eval_id _len);
                    `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector KV)))))) as PostKeyNull. 
forward_seq. instantiate (1:= PostKeyNull). (*eapply semax_seq.*)
{ assert (DD: Delta = initialized _reset 
               (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)) by reflexivity.
  rewrite DD; clear DD.
  eapply hmac_init_part1; eassumption.
}
subst PostKeyNull. normalize.
apply extract_exists_pre; intros cb. 
apply extract_exists_pre; intros cofs. 
apply extract_exists_pre; intros pad. 
apply extract_exists_pre; intros r.
normalize. rename H into HC; rewrite HC. rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.
Definition initPostResetConditional r (c:val) (k: val) h key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else !!(Forall isbyteZ key) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS key iS oS) c) *
                        (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b ofs)))
(*was:                        (array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr b ofs)))*)
  | _ => FF
  end.

remember (EX iSA:_, EX iS:_, EX oSA:_, EX oS:_,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key)) iSA /\ s256_relate iSA iS /\
                 outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key)) oSA /\ s256_relate oSA oS)
                 LOCAL  (
                 `(eq pad) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq k) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))

                 SEP  (
                 `(data_at_ Tsh (tarray tuchar 64) pad); (*was:`(array_at_ tuchar Tsh 0 64 pad); *)
                 `(initPostResetConditional r c k h1 key iS oS); `(K_vector KV)))
  as PostResetBranch.
(*forward_seq. instantiate (1:= PostResetBranch).*)
eapply semax_seq. instantiate (1:=PostResetBranch).
{ forward_if PostResetBranch. 
  { (* THEN*)
    (*remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))))) as IPADcont.
    remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))))) as OPADcont.
    *)
    remember (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))) as IPADcont.
    remember (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))) as OPADcont.
    assert (ZLI: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    assert (ZLO: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    (*remember (ZnthV tuchar (default_val (Tarray tuchar 64 noattr))) as DEFAULTcont.*)
    unfold data_at_, (*tuchars,*) tarray.
    (*erewrite data_at_array_at; try reflexivity. 2: omega.
    rewrite array_at_isptr.*)
    rewrite data_at_isptr. normalize. apply isptrD in H. destruct H as [pb [pofs Hpad]]. subst pad.
    apply semax_pre with (P':=PROP  (r<>0 /\ Forall isbyteZ key)
         LOCAL  (tc_environ Delta;
            `(eq (Vint (Int.repr r))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
            `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
         SEP  (`(K_vector KV);
               `(data_at Tsh (Tarray tuchar 64 noattr)
                   (default_val (Tarray tuchar 64 noattr)) (Vptr pb pofs));
(*`(array_at tuchar Tsh (ZnthV tuchar (default_val (Tarray tuchar 64 noattr)))
                   0 64 (Vptr pb pofs));*)
               `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
               `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) k))).
               (*`(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k))).*)
    { clear HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional. entailer.
      destruct key'; try contradiction.
      (*integer, ie key==NULL*)
          simpl in TC0. subst i. simpl. if_tac. subst r. inversion H0.
          apply andp_right. entailer. entailer.
      (*key == Vptr*)
       if_tac. subst r.
          unfold typed_true in H0. simpl in H0. inversion H0.
          entailer. cancel.
    } 
    (*rewrite (array_at_isptr _ _ _ _ _ k). normalize.*)
    rewrite data_at_isptr with (p:=k). normalize.

    destruct R; subst r. omega. clear H. 
    rename H0 into isbyte_key.
    apply isptrD in H1; destruct H1 as [kb [kofs HK]]; rewrite HK in *.
    
    forward_seq. 
    instantiate (1:= 
      (PROP  ()
       LOCAL  (
        `(eq (Vint (Int.repr 1))) (eval_id _reset);
        `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
        `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
        `(eq (Vint (Int.repr l))) (eval_id _len);
        `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
       SEP 
        ((*`(array_at tuchar Tsh IPADcont 0 64 (Vptr pb pofs));*)
        `(K_vector KV);
   `(data_at Tsh (Tarray tuchar 64 noattr) IPADcont (Vptr pb pofs));
   `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs))))).

    { (*ipad loop*)
(*      specialize split_offset_array_at.*)
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP  (
          `(data_at Tsh (Tarray tuchar i noattr) IPADcont (Vptr pb pofs));
          `(data_at Tsh (Tarray tuchar (64 - i) noattr) (default_val (Tarray tuchar (64 - i) noattr))
             (offset_val (Int.repr i) (Vptr pb pofs)));
(*          `(array_at tuchar Tsh IPADcont 0 i (Vptr pb pofs));
          `(array_at tuchar Tsh DEFAULTcont i 64 (Vptr pb pofs));*)
          `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
          `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
             (Vptr kb kofs)); `(K_vector KV)))).
      { (*precondition implies "invariant"*) 
        clear HeqPostResetBranch.
        entailer. cancel. 
        rewrite data_Tarray_array_at_emp. 
        specialize (Tarray_emp_field_compatible pb pofs); intros. entailer.
      }
      { unfold normal_ret_assert. simpl. intros rho. entailer. cancel.
        rewrite data_Tarray_array_at_emp. entailer.
      }
      { admit.
        (*unfold_data_at 3%nat. normalize. 
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
        normalize. 
        rename H into I. (*rename H0 into SCc. rename H1 into ACc.*)
        (*rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.*)
        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.
        { subst PostResetBranch. 
          eapply semax_data_store_nth.
          eapply semax_pre'. semax_store_nth.
          eapply semax_pre.
          WITH x12: (t1 * t2)%type
          remember (ZnthV tuchar (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) i) as CONTi.
          unfold ZnthV in CONTi. destruct (nth_mapVintZ i (HMAC_SHA256.mkKey key)) as [N HN].
              rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl. 
               assumption.            
          assert (Hres: ZnthV tuchar (map Vint (map Int.repr
                   (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad))) i
              = Vint (Int.zero_ext 8 (Int.xor (Int.repr 54) N))). 
          { clear - HN I isbyte_key. apply xor_pad_result; assumption. }
          eapply NEWsemax_loadstore_array
          with (P:= nil)
          (Q:= [`(eq (Vint (Int.repr i))) (eval_id _i);
            `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
            `(eq (Vint (Int.repr 1))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
            `(eq (Vptr cb cofs)) (eval_id _ctx);
            `(eq (Vptr kb kofs)) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq KV) (eval_var sha._K256 (tarray tuint 64))])
          (R:= [`(field_at Tsh t_struct_hmac_ctx_st [_key_length]
               (if zlt 64 (Zlength key)
                then Vint (Int.repr 32)
                else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
            `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_key])
                (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
               (offset_val
                 (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_key]))
                 (Vptr cb cofs)));
            `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] emptySha (Vptr cb cofs));
            `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] emptySha (Vptr cb cofs));
            `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
            `(array_at tuchar Tsh IPADcont 0 i (Vptr pb pofs));
            `(array_at tuchar Tsh DEFAULTcont i 64 (Vptr pb pofs));
            `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr key))) 0
                (Zlength key) (Vptr kb kofs)); `(K_vector KV)])
          (n:=6%nat)
          (v2:=(ZnthV tuchar (map Vint(map Int.repr (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad))) i)).
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          Focus 2. simpl. unfold value, nested_field_type2, t_struct_hmac_ctx_st; simpl.
            reflexivity.
          2: trivial.     
          instantiate (1:=i). unfold nested_field_offset2, _struct_SHA256state_st; simpl.
          intros rho. normalize.
           apply andp_right. apply andp_right; rel_expr.
           rewrite Hres.
           erewrite (data_at_type_changable Tsh _ (tarray tuchar 64)); try reflexivity.
           unfold tarray. 
           erewrite data_at_array_at; try reflexivity.
           erewrite (split3_array_at' i); try reflexivity. 2: trivial. 2: omega.
           {  rel_expr.  instantiate (1:=cofs). instantiate (1:=cb).
              rel_expr.
                  admit. (*relexpr*)
             unfold nested_field_offset2, _struct_SHA256state_st; simpl.
              instantiate (2:=Tsh). unfold add_ptr_int. simpl.
              instantiate (1:=(ZnthV tuchar (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) i)).
              cancel.
             unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. discriminate.
             simpl; intros.
                unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. reflexivity.
             reflexivity.
           }
           { unfold HMAC_SHA256.mkArgZ. simpl. apply ZnthV_map_Vint_is_int_I8.
             unfold HMAC_SHA256.mkArgZ in ZLI. rewrite Zlength_correct, map_length in ZLI. 
             rewrite Zlength_correct, ZLI. omega.
           }
           red; omega.          
        }
        { entailer. cancel.
          rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega. cancel.
          unfold_data_at 2%nat. cancel.
          rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
          entailer.
          rewrite at_offset'_eq.
          2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val. cancel.
          apply sepcon_derives.
            rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
            cancel.
            apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros.
            assert (i0=i). omega. subst i0. simpl.
            destruct (zlt i 0). omega. simpl. rewrite upd_eq.
            destruct (nth_mapVintZ i 
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)) as [n Hn].
             rewrite ZLI; assumption.
            rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
          apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros. rewrite upd_neq; trivial. omega.
        } *)
      }
    }

    (*continuation after ipad-loop*)   
    unfold_data_at 2%nat. normalize.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity. normalize.
    (*was: rewrite at_offset'_eq.
           2: simpl; rewrite Int.add_zero; reflexivity.*)
    (*now: extract field-address info before doing anything else*) 
       rewrite data_at_isptr. normalize.
       apply isptrD in H. destruct H as [? [? PT]]; rewrite PT.
       unfold field_address in PT.
       destruct(field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
           (Vptr cb cofs)); simpl in PT; inversion PT; clear PT.
       subst x x0. 
       unfold nested_field_offset2; simpl. 

    eapply semax_seq'.
    myframe_SEP'' [3].
    forward_call (Vptr cb (Int.add cofs (Int.repr 108))).
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. 
    }
    after_call. simpl. normalize. 

    eapply semax_seq'.
    myframe_SEP'' [0; 5; 6].
    remember (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad,
            Vptr cb (Int.add cofs (Int.repr 108)),
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer.
      unfold data_block, tarray. rewrite ZLI. cancel.
      entailer.
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned.
      cancel.
    }
    after_call. simpl. intros rho. subst WITNESS. rewrite firstn_precise. normalize.
    unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. repeat rewrite map_length.
      unfold HMAC_SHA256.sixtyfour. 
      rewrite combine_length, map_length, length_list_repeat, mkKey_length.
      unfold SHA256.BlockSize; simpl. trivial.

    simpl.
    apply semax_pre with (P':=EX x : s256abs,
     (PROP  (update_abs
          (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
          init_s256abs x)
     LOCAL  (tc_environ Delta; 
       `(eq (Vint (Int.repr 1))) (eval_id _reset);
       `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
       `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
       `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
     SEP  (`(K_vector KV);
       `(sha256state_ x (Vptr cb (Int.add cofs (Int.repr 108))));
       `(data_block Tsh
           (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
           (Vptr pb pofs));
      `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
         (if zlt 64 (Zlength key)
          then Vint (Int.repr 32)
          else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
      `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
          (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
      `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] emptySha
          (Vptr cb cofs));
      `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha
          (Vptr cb cofs));
      `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
          (Vptr kb kofs))))).
    { entailer. apply (exp_right x). entailer. }
    apply extract_exists_pre. intros ipadSHAabs.
    (*rename H into SCc.
    rename H0 into ACc.*)
    normalize. (* simpl. normalize.*) rename H into ipadAbs_def.

    (*essentially the same for opad*)
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]); try reflexivity.
    (*was: normalize.
        rewrite at_offset'_eq.
      2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val; simpl.*)
    (*now:*)
       rewrite data_at_isptr. normalize.
       apply isptrD in H. destruct H as [? [? PT]]; rewrite PT.
       unfold field_address in PT.
       destruct(field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
           (Vptr cb cofs)); simpl in PT; inversion PT; clear PT.
       subst x x0. 
       unfold nested_field_offset2; simpl. rename f into g.
 
    forward_seq.
    instantiate (1:= 
  (PROP  ()
   LOCAL  (tc_environ Delta; `(eq (Vint (Int.repr 1))) (eval_id _reset);
       `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
       `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
       `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
(*   `(data_block Tsh
       (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)
       (Vptr pb pofs));*)
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
       (if zlt 64 (Zlength key)
        then Vint (Int.repr 32)
        else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
   `(data_at Tsh
       (nested_field_type2 t_struct_hmac_ctx_st [StructField _o_ctx])
       emptySha (Vptr cb (Int.add cofs (Int.repr 216))));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs));
   `(data_at Tsh (Tarray tuchar 64 noattr) OPADcont (Vptr pb pofs))))).

    { (*opad loop*)
admit. (*
      forward_for_simple_bound' 64 (EX i:Z, 
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
   `(array_at tuchar Tsh OPADcont 0 i (Vptr pb pofs));
   `(array_at tuchar Tsh IPADcont i 64 (Vptr pb pofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
       (if zlt 64 (Zlength key)
        then Vint (Int.repr 32)
        else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key]
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
   `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx]) emptySha
       (Vptr cb
          (Int.add cofs
             (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
   `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
   `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
       (Vptr kb kofs))))).
      { (*precondition implies "invariant"*)
        rewrite array_at_emp. unfold data_block. normalize. entailer. 
        apply andp_right.
          unfold array_at. normalize. rewrite ZLI in *. destruct H5.  destruct H7.
            simpl in *. apply prop_right. omega.
        cancel. rewrite ZLI. 
            apply array_lemmas.array_at_ext'. 
            unfold tuchars, cVint, ZnthV; simpl. intros. destruct (zlt i 0). omega.
            destruct (nth_mapVintZ i 
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)) as [n Hn].
            rewrite ZLI. assumption.
            rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.            
      }
      { unfold normal_ret_assert, data_block. simpl. intros rho. 
        rewrite array_at_emp. entailer.
        apply andp_right. apply prop_right. apply isbyte_map_ByteUnsigned.
        cancel. unfold tuchars. rewrite ZLO.
            apply array_lemmas.array_at_ext'. 
            unfold tuchars, cVint, ZnthV; simpl. intros. destruct (zlt i 0). omega.
            destruct (nth_mapVintZ i 
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)) as [n Hn].
            rewrite ZLO. assumption. rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
      }
      { (*unfold_data_at 1%nat. normalize.*)
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
        normalize. rename H into I. 
        rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.
        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.
        { subst PostResetBranch.
          remember (ZnthV tuchar (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) i) as CONTi.
          unfold ZnthV in CONTi. destruct (nth_mapVintZ i (HMAC_SHA256.mkKey key)) as [N HN].
              rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl. 
               assumption.
          assert (Hres: ZnthV tuchar (map Vint (map Int.repr
                   (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad))) i
              = Vint (Int.zero_ext 8 (Int.xor (Int.repr 92) N))). 
          { clear - HN I isbyte_key. apply xor_pad_result; assumption. }
          eapply NEWsemax_loadstore_array
          with (P:= nil)
          (Q:= [`(eq (Vint (Int.repr i))) (eval_id _i);
            `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
            `(eq (Vint (Int.repr 1))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
            `(eq (Vptr cb cofs)) (eval_id _ctx);
            `(eq (Vptr kb kofs)) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq KV) (eval_var sha._K256 (tarray tuint 64))])
          (R:= [`(K_vector KV);
     `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
     `(array_at tuchar Tsh OPADcont 0 i (Vptr pb pofs));
     `(array_at tuchar Tsh IPADcont i 64 (Vptr pb pofs));
     `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
         (if zlt 64 (Zlength key)
          then Vint (Int.repr 32)
          else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
     `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_key])
         (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
         (offset_val
            (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_key]))
            (Vptr cb cofs)));
     `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx])
         emptySha
         (Vptr cb
            (Int.add cofs
               (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
     `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
     `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
         (Vptr kb kofs))])
          (n:=3%nat)
          (v2:=(ZnthV tuchar (map Vint(map Int.repr (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad))) i)).
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          Focus 2. simpl. unfold value, nested_field_type2, t_struct_hmac_ctx_st; simpl.
            reflexivity.
          2: trivial.
          instantiate (1:=i). unfold nested_field_offset2, _struct_SHA256state_st; simpl.
          intros rho. normalize.
           apply andp_right. apply andp_right; rel_expr.
           rewrite Hres.
           erewrite (data_at_type_changable Tsh _ (tarray tuchar 64)); try reflexivity.
           unfold tarray. 
           erewrite data_at_array_at; try reflexivity.
           erewrite (split3_array_at' i _ _ _ 0 64); try reflexivity. 2: trivial. 2: omega.
           { rel_expr. 
              instantiate (1:=cofs). instantiate (1:=cb). admit. (* rel_expr.*)
             unfold nested_field_offset2, _struct_SHA256state_st; simpl.
              instantiate (2:=Tsh). unfold add_ptr_int. simpl.
              instantiate (1:=(ZnthV tuchar (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) i)).
              cancel.
             unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. discriminate.
             simpl; intros.
                unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. reflexivity.
             reflexivity.
           }
           { unfold HMAC_SHA256.mkArgZ. simpl. apply ZnthV_map_Vint_is_int_I8.
             unfold HMAC_SHA256.mkArgZ in ZLO. rewrite Zlength_correct, map_length in ZLO. 
             rewrite Zlength_correct, ZLO. omega.
           }
           red; omega. 
        }
        { entailer. cancel.
          rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega. cancel.
          unfold_data_at 1%nat. cancel.
          rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
          rewrite at_offset'_eq.
            2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val.
          unfold_data_at 1%nat. entailer. cancel.
          apply sepcon_derives.
            rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
            cancel.
            apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros.
            assert (i0=i). omega. subst i0. simpl.
            destruct (zlt i 0). omega. simpl. rewrite upd_eq.
            destruct (nth_mapVintZ i 
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)) as [n Hn].
              rewrite ZLO; assumption.
            rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
          apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros. rewrite upd_neq; trivial. omega.
        } 
      }*)
    }

    (*continuation after opad-loop*)   
(*    unfold_data_at 1%nat. normalize.*)
(*    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]); try reflexivity. normalize.*)
    eapply semax_seq'.
    myframe_SEP'' [4].
    forward_call (Vptr cb (Int.add cofs (Int.repr 216))).
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. 
    }
    after_call. simpl. normalize.

    unfold MORE_COMMANDS, abbreviate. (*WHY IS THIS NOT DONE AUTOMATICALLY?*)
(*    make_sequential.
    frame_SEP 0 1 3.*)
    remember (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad,
            Vptr cb (Int.add cofs (Int.repr 216)),
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [
         `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
              (if zlt 64 (Zlength key)
               then Vint (Int.repr 32)
               else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] emptySha (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))]). 
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS.  unfold data_block. rewrite ZLO. entailer. 
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned.
      cancel. 
    }
    after_call. simpl. intros rho. subst WITNESS PostResetBranch.
    rewrite firstn_precise. normalize.
        rename x into opadSHAabs. 
        unfold sha256state_; normalize. rename r into iUpd. rename x into oUpd.
        apply exp_right with (x:=ipadSHAabs). entailer.
        apply exp_right with (x:=iUpd). entailer.
        apply exp_right with (x:=opadSHAabs). entailer.
        apply exp_right with (x:=oUpd). entailer.
        unfold data_block, initPostResetConditional. simpl.
        rewrite ZLO. entailer. cancel. (*Qinxiang: this cancel used to take 5-10secs - now it takes at least 5mins!*)
        unfold_data_at 3%nat. cancel.

   (*The following  7 lines this should be done more elegantly*)
    rewrite field_at_data_at.
    rewrite field_at_data_at.
    unfold field_address. simpl.
       destruct(field_compatible_dec t_struct_hmac_ctx_st [StructField _o_ctx]
           (Vptr cb cofs)); try contradiction.
       destruct(field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
           (Vptr cb cofs)); try contradiction.
       unfold nested_field_offset2, nested_field_type2; simpl. cancel.

    unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. repeat rewrite map_length.
      unfold HMAC_SHA256.sixtyfour. 
      rewrite combine_length, map_length, length_list_repeat, mkKey_length.
      unfold SHA256.BlockSize; simpl. trivial.

  }
  { (*ELSE*) 
    forward. unfold overridePost. simpl. intros rho. apply andp_right. apply prop_right. trivial.
    subst. unfold initPostKeyNullConditional; simpl. entailer.
    rewrite <- H1 in *; simpl in *. unfold typed_false in H0. simpl in H0.
        inversion H0; clear H0. apply negb_false_iff in H6.
        apply eq_sym in H6; apply binop_lemmas.int_eq_true in H6.
    destruct R; subst. simpl.
      remember (eval_id _key rho) as k. destruct k; entailer. 
      remember (Int.eq i Int.zero) as d. destruct d. 2: entailer.
      unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
      destruct h1; entailer.
       destruct H10 as [ii [KLi [KLunsig [SF [ISHA OSHA]]]]].
       apply exp_right with (x:= iSha). 
       apply exp_right with (x:= (iCtx r)).
       apply exp_right with (x:= oSha).
       apply exp_right with (x:= (oCtx r)).
       entailer. rewrite <- Heqd. cancel.
       unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
       (*apply sepcon_derives. unfold tarray. rewrite data_at__array_at_. cancel. omega. reflexivity. *)
       apply exp_right with (x:= r). apply exp_right with (x:=v).
       entailer. apply prop_right. exists ii; eauto.
     simpl. apply Int.one_not_zero in H6. contradiction.
   } 
}
{ (*Continuation after if (reset*)
  subst PostResetBranch.
simpl update_tycon.
apply semax_extensionality_Delta with (Delta). apply expr_lemmas.tycontext_sub_refl.
  apply extract_exists_pre; intros iSA. 
  apply extract_exists_pre; intros iS. 
  apply extract_exists_pre; intros oSA. 
  apply extract_exists_pre; intros oS. unfold initPostResetConditional.
  normalize. 
  rename H into INNER. rename H0 into InnerRelate.
  rename H1 into OUTER. rename H2 into OuterRelate.
  unfold initPostResetConditional; rewrite HC.
  destruct k;
    try solve [apply semax_pre with (P':=FF); try entailer; try apply semax_ff].
  { (*k is integer, ie key==null*)
     destruct (Int.eq i Int.zero). 
     Focus 2. apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
     destruct R; subst r; simpl.
     Focus 2. apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
     unfold hmacstate_PreInitNull; simpl. normalize.
     intros s. normalize. intros v. normalize. rename H into Hs.
     unfold hmac_relate_PreInitNull in Hs. 
     clear INNER InnerRelate OUTER OuterRelate iSA iS oSA oS.
     destruct h1.
     destruct Hs as [XX [IREL [OREL [ILEN [OLEN [KK [ii [KLii [KL [HH1 [HH2 HH3]]]]]]]]]]].
     subst key0. destruct s as [mdS [iS [oS [kl K]]]]. simpl in *. subst kl K.
     unfold_data_at 1%nat.
     (* eapply semax_seq'.
     frame_SEP 3 4.*)
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
     rewrite data_at_isptr. (*NEW, order to extract the knowledge about field_address*)
     normalize.
     
     (*XXX: was: rename H into SCc. rename H0 into ACc. now:*)
     apply isptrD in H. destruct H as [cb' [cofs' PT]]; rewrite PT.
     unfold field_address in PT.
     destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
           (Vptr cb cofs)); simpl in PT; inversion PT. subst cb' cofs'; clear PT.

     (*was:rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.*)
     remember ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) as  WITNESS.
     forward_call WITNESS.
     { assert (FR: Frame = [
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] (Vint ii) (Vptr cb cofs)); 
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
               (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad); `(K_vector KV)]).
          subst Frame. reflexivity.
       rewrite FR. clear FR Frame. 
       subst WITNESS. entailer. cancel.
       apply sepcon_derives. 
         rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.

         (*XXX was: unfold field_address.
            rewrite at_offset'_eq. unfold offset_val. normalize.
            simpl; rewrite Int.add_zero; reflexivity.
          now:*)
         rewrite data_at_isptr. normalize.
         apply isptrD in H1. destruct H1 as [? [? PT]]; rewrite PT.
         unfold field_address in PT.
         destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
             (Vptr cb cofs)); simpl in PT; inversion PT. subst x x0; clear PT.
         cancel.

       eapply derives_trans.
         apply data_at_data_at_. (*was: reflexivity. *)
         (*was: rewrite <- memory_block_data_at_; try reflexivity. entailer*)
         (*now:*) rewrite data_at__memory_block; try reflexivity. entailer.
     }
     after_call. subst WITNESS. normalize. subst retval0. simpl. 

     forward. (*return*)
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     apply exp_right with (x:=HMACabs iSha iSha oSha KL key).   
     entailer.
     apply andp_right. 
       apply prop_right. exists iSha, oSha.
       rewrite Int.unsigned_repr. auto.
       rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
       destruct (zlt 64 (Zlength key)); omega.     
     simpl_stackframe_of. unfold tarray. 
     (*was:rewrite <- data_at__array_at_ with (a:=noattr).
     2: omega. 2: reflexivity.*)
     cancel.
     unfold hmacstate_, hmac_relate.
      remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) as kl.
      normalize.
      apply exp_right with
        (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HMAC_SHA256.mkKey key))))))).
      simpl.
      apply andp_right. apply prop_right. repeat split; trivial.
      destruct (zlt 64 (Zlength key)); simpl in *.
         exists (Int.repr 32); eauto.
         rewrite Heqkl, HH1. exists (Int.repr (Int.unsigned ii)).
         rewrite Int.repr_unsigned; eauto.

      unfold_data_at 3%nat. cancel.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      entailer. cancel.

      (*Qinxiang: here's again a bit of extra code that's related to field_address*)
          unfold field_address.
          destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
              (Vptr cb cofs)); try contradiction.
          destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
              (Vptr cb cofs)); try contradiction.
          unfold nested_field_type2; simpl.
          unfold nested_field_offset2; simpl.
          rewrite int_add_repr_0_r.

      destruct (zlt 64 (Zlength key)); simpl in *;
        rewrite HH1, Int.repr_unsigned; simpl in *.
        cancel.
        cancel.
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
    normalize. 
    unfold postResetHMS. simpl. unfold_data_at 1%nat.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
    normalize.
    (*was:rename H into SCc. rename H0 into ACc.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.*)
    (*now:*) rewrite data_at_isptr. normalize. 
             apply isptrD in H0; destruct H0 as [? [? PT]]. 
             rewrite PT. 
             unfold field_address in PT.
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
                  (Vptr cb cofs)); inversion PT. subst x x0; clear PT.

    rename b into kb; rename i into kofs.
    eapply semax_pre with (P':=PROP  ()
      LOCAL  (`(eq pad) (eval_var _pad (tarray tuchar 64));
       `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
       `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (`(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
            (if zlt 64 (Zlength key)
            then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs));
          `(K_vector KV);
          `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])))
             (offset_val
                (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _md_ctx]))
             (Vptr cb cofs))))).
    { entailer. cancel.
      (*was:unfold tarray. erewrite data_at__array_at_. 2: omega. 2: reflexivity. 
      cancel.*) (*now:*) unfold nested_field_type2; simpl.
      eapply derives_trans.
        apply data_at_data_at_. (*was: reflexivity. *)
        rewrite <- memory_block_data_at_; try reflexivity. cancel.
        (*new:*) apply f. 
    }
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.
    normalize. 
    (*was: rewrite at_offset'_eq.
       2: simpl; rewrite Int.add_zero; reflexivity.*)
    (*now:*) rewrite data_at_isptr. normalize. 
             apply isptrD in H0; destruct H0 as [? [? PT]]. 
             rewrite PT. 
             unfold field_address in PT.
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
                  (Vptr cb cofs)); inversion PT. subst x x0; clear PT.

    remember ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) as  WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
            (if zlt 64 (Zlength key)
             then Vint (Int.repr 32)
             else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
            (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr cb cofs));
         `(data_at_ Tsh (tarray tuchar 64) pad);
         `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
            (Vptr kb kofs)); `(K_vector KV)]).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. cancel. 
    }
    after_call. subst WITNESS. normalize.  subst retval0. simpl. 

    forward. (*return*)
    remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
    apply exp_right with (x:=HMACabs iSA iSA oSA KL key). 
    entailer.
    apply andp_right. 
      apply prop_right. unfold hmacInit. exists iSA, oSA.
      rewrite Int.unsigned_repr. auto.
      rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
      destruct (zlt 64 (Zlength key)); omega.    
    unfold data_block. simpl_stackframe_of. entailer. cancel.
    unfold hmacstate_, hmac_relate.
    remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
              else Vint (Int.repr (Zlength key))) as kl.
    normalize.
    apply exp_right with
      (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HMAC_SHA256.mkKey key))))))).
    simpl. entailer.
    apply andp_right. apply prop_right.
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      split. rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      exists (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)).
      rewrite Int.unsigned_repr. 
      split. destruct (zlt 64 (Zlength key)); trivial.
      split; trivial.
      rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
      destruct (zlt 64 (Zlength key)); omega.

    unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
    (*new:*) unfold field_address; simpl.
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
                  (Vptr cb cofs)); try contradiction.
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
                  (Vptr cb cofs)); try contradiction.
    entailer.
  }
} 
Qed.