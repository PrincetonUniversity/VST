Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.general_lemmas.
Require Import sha.spec_sha.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmac.

Require Import sha.hkdf.
Require Import sha.spec_hkdf.
Require Import sha.hkdf_functional_prog.

Definition Done (i:Z): int := Int.repr (digest_len*i).
Definition OUTpred PrkCont InfoCont sh z r cont p: mpred:=
  data_at sh (tarray tuchar z) (sublist 0 z (map Vint (map Int.repr (HKDF_expand PrkCont InfoCont cont)))) p *
  memory_block sh r (offset_val z p).

Definition PREVcont PRK INFO (i: Z): reptype (Tarray tuchar 32 noattr) :=
     if zeq i 0 then list_repeat 32 Vundef 
     else (map Vint (map Int.repr (Ti (CONT PRK) (CONT INFO) (Z.to_nat i)))).

Lemma PREV_len PRK INFO i: 0 <= i -> Zlength (PREVcont PRK INFO i) = 32.
Proof. intros. unfold PREVcont.
destruct (zeq i 0). rewrite Zlength_list_repeat'; reflexivity.
assert (exists n, Z.to_nat i = S n).
{ specialize (Z2Nat_inj_0 i). intros.
  destruct (Z.to_nat i). omega. eexists; reflexivity. }
destruct H0; rewrite H0.
unfold Ti; simpl. repeat rewrite Zlength_map. apply HMAC_Zlength.
Qed.

Lemma PREV_isbyteZ PRK INFO i: 0 < i -> exists l, PREVcont PRK INFO i = map Vint (map Int.repr l) /\
                                                  Forall general_lemmas.isbyteZ l.
Proof. intros. unfold PREVcont.
destruct (zeq i 0). omega. eexists; split. reflexivity.
assert (exists n, Z.to_nat i = S n).
{ specialize (Z2Nat_inj_0 i). intros.
  destruct (Z.to_nat i). omega. eexists; reflexivity. }
destruct H0; rewrite H0.
unfold Ti; simpl. apply isbyte_hmac. 
Qed.

Lemma PREVcont_Sn PRK INFO i p: 0 <= i -> PREVcont PRK INFO i = map Vint (map Int.repr p) -> 
      Forall general_lemmas.isbyteZ p ->
      PREVcont PRK INFO (i+1) = if zeq i 0 then map Vint (map Int.repr (HMAC256_functional_prog.HMAC256 (CONT INFO ++ [1]) (CONT PRK)))
                                else map Vint (map Int.repr (HMAC256_functional_prog.HMAC256 (p ++ CONT INFO ++ [i + 1]) (CONT PRK))).
Proof. intros. unfold PREVcont.
destruct (zeq (i+1) 0). omega.
change (i+1) with (Z.succ i). rewrite Z2Nat.inj_succ; try omega. simpl.
unfold PREVcont in H0.
destruct (zeq i 0).
+ subst i. simpl; trivial. 
+ apply map_Vint_injective in H0. apply map_IntReprOfBytes_injective in H0; trivial.
  rewrite H0, Zpos_P_of_succ_nat, Z2Nat.id; trivial.
  apply isbyteZ_Ti.
Qed.

Lemma PREV_listZ PRK INFO i: 0 < i -> exists l, PREVcont PRK INFO i = map Vint (map Int.repr l).
Proof. intros. unfold PREVcont.
destruct (zeq i 0). omega. eexists; reflexivity.
Qed. 

Lemma sublist_HKDF_expand4 PRK INFO i rest l (REST : 0 <= rest < 32)
      (g : 255 >= i + 1) (OLEN : 32 * i + rest + 32 <= Int.max_unsigned)
      (Hl : if zeq i 0 then l = [] else PREVcont PRK INFO i = map Vint (map Int.repr l) /\ Forall general_lemmas.isbyteZ l)
      (Hi: 0 <= i):
sublist 0 rest
  (HMAC256_functional_prog.HMAC256 ((l ++ CONT INFO) ++ [Int.unsigned (Int.zero_ext 8 (Int.repr (i + 1)))]) (CONT PRK)) =
sublist (32 * i) (32 * i + rest) (HKDF_expand (CONT PRK) (CONT INFO) (32 * (i + 1))).
Proof.
  unfold PREVcont in Hl. destruct (zeq i 0).
  + subst i l; simpl. rewrite Z.add_0_l. unfold HKDF_expand; simpl.
    rewrite sublist_sublist; try omega. rewrite 2 Z.add_0_r.
    rewrite zero_ext_inrange; try rewrite Int.unsigned_repr;
        try rewrite int_max_unsigned_eq; try omega; trivial.
  + destruct Hl as [Hl isBl].
    apply map_Vint_injective in Hl.
    apply map_IntReprOfBytes_injective in Hl; trivial.
    2: apply isbyteZ_Ti.
    unfold HKDF_expand; simpl.
    destruct (zle (32 * (i + 1)) 0); try omega.
    rewrite sublist_sublist; try omega. rewrite 2 Z.add_0_r.
    rewrite (Zmod_unique _ _ (i+1) 0); try omega. simpl. 
    rewrite (Zdiv_unique _ _ (i+1) 0); try omega. 
    replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    2: rewrite Z.add_comm, Z2Nat.inj_add; try reflexivity; try omega.
    simpl. rewrite sublist_app2; rewrite Zlength_T, Nat2Z.inj_mul, Z2Nat.id; simpl; try omega.
    rewrite Zminus_diag, Hl, <- app_assoc, Zpos_P_of_succ_nat, Z2Nat.id; try omega.
    replace ((32 * i + rest - 32 * i)%Z) with rest%Z by omega.
    replace (i + 1) with (Z.succ i) in * by trivial.
    rewrite zero_ext_inrange; try rewrite Int.unsigned_repr; trivial; try omega.
    change (two_p 8 - 1) with 255; omega.
Qed.

Lemma sublist_HKDF_expand5 PRK INFO l i
         (Hl : if zeq i 0 then l = []
               else PREVcont PRK INFO i = map Vint (map Int.repr l) /\ Forall general_lemmas.isbyteZ l)
         (Hi : 0 <= i):
      sublist 0 32 (HMAC256_functional_prog.HMAC256 ((l ++ CONT INFO) ++ [i + 1]) (CONT PRK)) =
      sublist (32 * i) (32 * i + 32) (HKDF_expand (CONT PRK) (CONT INFO) (32 * (i + 1))).
Proof.
  unfold HKDF_expand. destruct (zle (32*(i + 1)) 0); try omega. simpl.
  rewrite (Zmod_unique _ _ (i+1) 0) by omega. simpl. 
  rewrite (Zdiv_unique _ _(i+1) 0) by omega.
  rewrite sublist_sublist; try omega. rewrite ! Z.add_0_r.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  2: rewrite Z.add_comm, Z2Nat.inj_add; try reflexivity; try omega.
  simpl.
  rewrite Zpos_P_of_succ_nat, Z2Nat.id; try omega. 
  rewrite sublist_app2; rewrite Zlength_T, Nat2Z.inj_mul, Z2Nat.id; simpl; try omega.
  rewrite Zminus_diag. replace ((32 * i + 32 - 32 * i)%Z) with 32%Z by omega.
  unfold PREVcont in Hl.
  destruct (zeq i 0). { simpl in *; subst i l; simpl; trivial. }
  destruct Hl as [Hl isBTl]. apply map_Vint_injective in Hl.
  apply map_IntReprOfBytes_injective in Hl; trivial. 2: apply isbyteZ_Ti.
  rewrite Hl, <- app_assoc.
  change (i+1)%Z with (Z.succ i); trivial.
Qed.

Lemma body_hkdf_expand: semax_body Hkdf_VarSpecs Hkdf_FunSpecs 
       f_HKDF_expand HKDF_expand_spec.
Proof.
start_function. 
rename H into LenPRK. rename H0 into LEN_INFO1.
destruct H1 as [LEN_INFO2 LEN_INFO3]. rename H2 into OLEN.

freeze [0;1;2;3;4;5;6] FR1.
forward. forward. forward. forward.
unfold Int.divu, Int.add, Int.sub.
assert (OLEN2: 0 <= (olen + 32 - 1) / 32 <= Int.max_unsigned).
{ split. apply Z_div_pos; omega.
  apply Zdiv_le_upper_bound; omega. }
rewrite (Int.unsigned_repr 32); [| rewrite int_max_unsigned_eq; omega].
rewrite (Int.unsigned_repr olen); [| omega]. 
rewrite (Int.unsigned_repr 1); [| rewrite int_max_unsigned_eq; omega].
rewrite (Int.unsigned_repr (Int.unsigned (Int.repr (olen + 32)) - 1));
  [| rewrite Int.unsigned_repr; omega]. 
rewrite Int.unsigned_repr; [| omega].
forward_if 
  (EX v:_, 
   PROP (if zlt (olen + 32) olen then v = Vint (Int.repr 1) 
         else v = Val.of_bool (Int.ltu (Int.repr 255) (Int.repr ((olen + 32 - 1) / 32))) )
   LOCAL (temp _t'1 v;
   temp _n (Vint (Int.repr ((olen + 32 - 1) / 32)));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (Int.repr 0));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar v_ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) v_hmac;
   lvar _previous (tarray tuchar 64) v_previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).
{ forward. Exists (Vint (Int.repr 1)). erewrite zlt_true; try eapply H.
  entailer!. } 
{ forward.
  Exists (Val.of_bool (Int.ltu (Int.repr 255) (Int.repr ((olen + 32 - 1) / 32)))).
  rewrite if_false; trivial. 
  entailer!. unfold sem_cast, sem_cast_i2bool, Val.of_bool; simpl.
  destruct (Int.ltu (Int.repr 255) (Int.repr ((olen + 32 - 1) / 32))); simpl; reflexivity. }
apply extract_exists_pre. intros v. Intros. rename H into HV.
unfold Int.ltu in HV.
rewrite Int.unsigned_repr in HV; [| rewrite int_max_unsigned_eq; omega].
rewrite Int.unsigned_repr in HV; [| omega].
unfold Val.of_bool in HV. 
forward_if 
  (PROP (v=Vint (Int.repr 0))
   LOCAL (temp _t'1 v; temp _n (Vint (Int.repr ((olen + 32 - 1) / 32)));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (Int.repr 0));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar v_ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) v_hmac;
   lvar _previous (tarray tuchar 64) v_previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).
{ unfold typed_true in H.
  rewrite if_false in HV; try omega.
  subst v.
  destruct (zlt 255 ((olen + 32 - 1) / 32)); [clear H | inv H].
  forward. normalize.
  Exists (expand_out_post shmd (CONT PRK) (CONT INFO) olen out).
  entailer!.
  + unfold expand_out_post, digest_len; simpl.
    rewrite if_false; try omega.
    rewrite if_true; trivial.
  + thaw FR1.
    unfold expand_out_post, digest_len; simpl.
    rewrite if_false; try omega.
    rewrite if_true; trivial. simpl. cancel. }
{ forward. entailer!. unfold typed_false in H; simpl in H; inv H.
  destruct (zlt (olen + 32) olen). inv HV; simpl in *; try discriminate.
  destruct (zlt 255 ((olen + 32 - 1) / 32)); inv HV; simpl in *; try discriminate; trivial. }
Intros. subst v. rewrite if_false in HV; try omega. 
destruct (zlt 255 ((olen + 32 - 1) / 32)); [inv HV | clear HV]. 
drop_LOCAL 0%nat.
thaw FR1. 
Time assert_PROP (isptr prk) as isPtrPrk by entailer!. (*destruct prk; try contradiction. (Vptr b i)*)

freeze [0;2;3;6] FR1.
assert_PROP (field_compatible t_struct_hmac_ctx_st [] v_hmac) as FC_hmac by entailer!.
replace_SEP 1 (HMAC_SPEC.EMPTY v_hmac).
{ entailer!. eapply HMAC_SPEC.mkEmpty; trivial. }
idtac "Timing the call to _HMAC_Init".
Time forward_call (@inr (val * Z * list Z * val) _ (v_hmac, spec_hmac.LEN PRK, CONT PRK, kv, prk)).
(*Finished transaction in 1.717 secs (1.371u,0.017s) (successful)*)

remember ((olen + 32 - 1) / 32) as bnd.
thaw FR1.
assert_PROP (isptr v_previous /\ field_compatible (tarray tuchar 64) [] v_previous) as prevPtr by entailer!.
destruct prevPtr as [prevPtr prevFC].
(*destruct previous; try contradiction. clear prevPtr.*)

unfold data_at_ at 2. unfold field_at_.
rewrite field_at_data_at. simpl. unfold tarray. 
assert (VV: exists vv :reptype (Tarray tuchar 64 noattr), vv= list_repeat 64 Vundef).
{ eexists; reflexivity. }
destruct VV as [vv VV].
assert (JMeq_1: JMeq (default_val (Tarray tuchar 64 noattr)) (sublist 0 64 vv)).
{ subst vv. rewrite sublist_list_repeat with (k:=64); try omega. simpl. apply JMeq_refl. }
erewrite  split2_data_at_Tarray with (n1:=32). 
2: omega.
3: apply JMeq_refl.
3: apply JMeq_refl.
2: eassumption.
normalize. simpl.
rewrite field_address_offset by auto with field_compatible. simpl.
rewrite isptr_offset_val_zero; trivial. (* rewrite Int.add_zero.*)
rewrite field_address0_offset by auto with field_compatible. simpl.
rewrite memory_block_field_compatible_tarraytuchar by rep_omega.
Intros. rename H into FCout. 

freeze [1;3] FR0. 
assert_PROP (isptr out) as isPTRout by entailer!.
assert (Arith: 32 > 0) by omega.
specialize (Z_div_mod_eq olen 32 Arith); intros OLEN1.
assert (REST:= Z_mod_lt olen 32 Arith). remember (olen / 32) as rounds. remember (olen mod 32) as rest.
assert (BND: bnd = if zeq rest 0 then rounds else rounds + 1).
{ subst bnd olen. clear Heqrounds Heqrest.
  destruct (zeq rest 0).
  + subst rest. assert (X: 32 * rounds + 0 + 32 - 1 = 32 * rounds + 31) by omega. rewrite X; clear X.
    symmetry. eapply Zdiv.Zdiv_unique. 2: reflexivity. omega.
  + assert (X: 32 * rounds + rest + 32 - 1 = rounds * 32 + (rest + 31)) by omega. rewrite X; clear X.
    rewrite Z.div_add_l. f_equal. apply Zdiv_unique with (b:=rest -1); omega. omega. }
clear Heqbnd Heqrounds Heqrest. 

forward_for_simple_bound bnd
       (EX ii:Z, PROP (0 <= olen - Int.unsigned(if zlt ii bnd then Done ii else Int.repr olen))
             LOCAL (temp _n (Vint (Int.repr bnd)); 
                    temp _ret (Vint (Int.repr 0)); 
                    temp _done (Vint (if zlt ii bnd then Done ii else Int.repr olen));
                    temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar v_ctr;
                    lvar _hmac (Tstruct _hmac_ctx_st noattr) v_hmac; lvar _previous (tarray tuchar 64) v_previous;
                    temp _out_key out; temp _out_len (Vint (Int.repr olen)); temp _prk prk;
                    temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); temp _info info;
                    temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO))); gvar sha._K256 kv)
             SEP (FRZL FR0; K_vector kv; data_at_ Tsh tuchar v_ctr; 
            data_at Tsh (Tarray tuchar 32 noattr) (PREVcont PRK INFO ii) v_previous;
            data_block Tsh (CONT INFO) info;
            if zeq ii 0 then HMAC_SPEC.REP (HMAC_SPEC.hABS (CONT PRK) []) v_hmac
            else HMAC_SPEC.FULL (CONT PRK) v_hmac; 
            OUTpred (CONT PRK) (CONT INFO) shmd (Z.min (digest_len * ii) olen) 
                    (olen - Z.min (digest_len * ii) olen) (ii*32) out)).
{ destruct (zeq 0 0); try solve [omega]. clear e; entailer!.
  + unfold Done; simpl.
    destruct (zeq rest 0); simpl.
    - subst rest.
      destruct (zlt 0 rounds); simpl.
      * split; trivial. rewrite Int.unsigned_repr; omega.
      * assert(R0: rounds = 0) by omega. rewrite R0 in *; clear R0. simpl. split; trivial; omega.        
    - rewrite if_true. 2: omega. split; trivial. rewrite Int.unsigned_repr; omega.
  + unfold OUTpred. destruct (zeq rest 0).
    - subst rest; simpl.
      destruct (zlt 0 rounds); simpl.
      * rewrite Zplus_0_r, Z.min_l, Zminus_0_r, data_at_tuchar_zero_array_eq, isptr_offset_val_zero(*, data_at__memory_block*); trivial; try omega.
        cancel. 
      * assert(R0: rounds = 0) by omega. rewrite R0 in *; clear R0. simpl. unfold tarray. (*cancel.*)
        rewrite isptr_offset_val_zero, data_at_tuchar_zero_array_eq; trivial. cancel. 
    - rewrite Zmin_l by omega. rewrite Zminus_0_r, data_at_tuchar_zero_array_eq; trivial.
      rewrite isptr_offset_val_zero; trivial. cancel.
}

{ (*loop body*)
  rename H into Hi1. Intros. rename i into i1. rename H into olenBounded. unfold Done, digest_len in olenBounded.
   rewrite if_true in olenBounded; try omega.
   rewrite Int.unsigned_repr in olenBounded. 2: rewrite int_max_unsigned_eq; omega.

  forward. rewrite Zmin_l. 2: unfold digest_len; omega.

  forward_if (EX l:_, 
  PROP ( if zeq i1 0 then l=@nil Z else PREVcont PRK INFO i1 = map Vint (map Int.repr l) /\ Forall general_lemmas.isbyteZ l)
   LOCAL (temp _i (Vint (Int.repr i1)); temp _n (Vint (Int.repr bnd));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (if zlt i1 bnd then Done i1 else Int.repr olen));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar v_ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) v_hmac;
   lvar _previous (tarray tuchar 64) v_previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (LEN PRK))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (FRZL FR0; K_vector kv;
   field_at Tsh tuchar []
     (Vint (cast_int_int I8 Unsigned (Int.add (Int.repr i1) (Int.repr 1)))) v_ctr;
   data_at Tsh (Tarray tuchar 32 noattr) (PREVcont PRK INFO i1) v_previous;
   data_block Tsh (CONT INFO) info; 
   OUTpred (CONT PRK) (CONT INFO) shmd (digest_len * i1) (olen - digest_len * i1) (i1*32) out;
   HMAC_SPEC.REP (HMAC_SPEC.hABS (CONT PRK) l) v_hmac)).

   { destruct (zlt i1 bnd); try omega. rewrite if_false; trivial.
     freeze [0;2;4;6] FR1.
     idtac "Timing the call to _HMAC_Init".
     Time forward_call (@inl _ (val * Z * list Z * val * val) (v_hmac,0,CONT PRK,kv)).
     (* Finished transaction in 1.73 secs (1.472u,0.011s) (successful)*)
     destruct (PREV_isbyteZ PRK INFO i1) as [prev [Hprev BTprev]]. omega. rewrite Hprev.
     assert (Zlength_prev: Zlength prev = 32).
     { specialize (PREV_len PRK INFO i1). rewrite Hprev.
       do 2 rewrite Zlength_map. intros X; rewrite X; trivial. omega. }

     idtac "Timing the first call to _HMAC_Update".
     Time forward_call (CONT PRK, v_hmac, v_previous, @nil Z, prev, kv).
     (*Finished transaction in 2.55 secs (2.048u,0.005s) (successful)*)
     * rewrite Zlength_prev, sem_cast_neutral_ptr; trivial. 
       apply prop_right; split; trivial. 
     * assert (Frame = [FRZL FR1]). subst Frame; reflexivity. simpl; cancel.
       unfold data_block. normalize. rewrite Zlength_prev; trivial.
     * rewrite Zlength_prev, Zlength_nil.
       split. rewrite int_max_unsigned_eq; omega.
       cbv; trivial.
     * Exists prev. rewrite if_false; trivial. entailer!. thaw FR1. cancel.
       unfold data_block. normalize. rewrite Hprev, Zlength_prev. cancel. }
   { subst i1. forward. Exists (@nil Z). rewrite ! if_true; try omega.
     entailer!. }

   apply extract_exists_pre. intros l. Intros. rename H into Hl. rewrite if_true. 2: omega. 

   idtac "Timing the second call to _HMAC_Update".
   Time forward_call (CONT PRK, v_hmac, info, l, CONT INFO, kv).
   (* Finished transaction in 2.659 secs (2.094u,0.014s) (successful)*) 
   { rewrite LEN_INFO1, sem_cast_neutral_ptr; trivial. 
     apply prop_right. split; reflexivity. }
   { split. omega.
     destruct (zeq i1 0).
     + subst i1 l. rewrite Zlength_nil, Zplus_0_r. omega.
     + assert (Arith1: 0<= i1) by omega. specialize (PREV_len PRK INFO i1 Arith1); intros HZ.
       destruct Hl.
       assert (HH: Zlength (@map int val Vint (@map Z int Int.repr l)) = @Zlength val (PREVcont PRK INFO i1))
         by (f_equal; auto).
       repeat rewrite Zlength_map in HH. rewrite HH, HZ, <- Zplus_assoc; simpl. omega. }

   simpl. freeze [1;3;5;6] FR3.
   assert_PROP (field_compatible (tarray tuchar 1) [] v_ctr /\ isptr v_ctr) as HH by entailer!.
   destruct HH as [FC_cptr isptrCtr].

   replace_SEP 3 (data_at Tsh (tarray tuchar 1) [Vint (Int.zero_ext 8 (Int.add (Int.repr i1) (Int.repr 1)))] v_ctr).
   { entailer!. apply data_at_tuchar_singleton_array. }

   assert (Forall general_lemmas.isbyteZ [Int.unsigned (Int.zero_ext 8 (Int.repr (i1+1)))]) as isBT.
      { constructor. red. rewrite zero_ext_inrange; rewrite Int.unsigned_repr. omega.
         rewrite int_max_unsigned_eq; omega.
         assert (Arith1: two_p 8 - 1 = 255) by reflexivity. rewrite Arith1; omega.
         rewrite int_max_unsigned_eq; omega. constructor. }
   assert (LEN: Zlength [Int.unsigned (Int.zero_ext 8 (Int.add (Int.repr i1) (Int.repr 1)))] = 1) by reflexivity.

   idtac "Timing the third call to _HMAC_Update".
   Time forward_call (CONT PRK, v_hmac, v_ctr, l++CONT INFO, 
        [Int.unsigned (Int.zero_ext 8 (Int.add (Int.repr i1) (Int.repr 1)))], kv).
   (* Finished transaction in 2.64 secs (2.057u,0.004s) (successful)*)
   { assert (Frame = [FRZL FR3]). subst Frame; reflexivity. subst Frame. simpl. cancel.
     unfold data_block. simpl. rewrite Int.repr_unsigned, LEN. entailer!. }
   { rewrite LEN. rewrite int_max_unsigned_eq, Zlength_app. split. omega.
     destruct (zeq i1 0).
     + subst l; rewrite Zlength_nil. rewrite Z.add_0_l. omega.
     + specialize (PREV_len PRK INFO i1). destruct Hl as [Hl isbyte_l]. rewrite Hl. do 2 rewrite Zlength_map.
       intros HH; rewrite HH; omega. } 

   normalize. thaw FR3. freeze [1;3;4;6] FR4.
   replace_SEP 3 (memory_block Tsh 32 v_previous).
   { entailer!. eapply derives_trans. apply data_at_memory_block. trivial. }
   idtac "Timing the call to _HMAC_Final".
   Time forward_call (((l ++ CONT INFO) ++ [Int.unsigned (Int.zero_ext 8 (Int.repr (i1 + 1)))]),
                 CONT PRK, v_hmac, v_previous, Tsh, kv).
   (* Finished transaction in 2.64 secs (2.057u,0.004s) (successful)*)
   unfold data_block. normalize. focus_SEP 2. erewrite (extract_prop_in_SEP 0); simpl. 2: reflexivity.
   Intros. rename H into isBT_app. (*VST TODO: why does normalize/Intros need the explicit extract_prop_in_SEP???*)
   rewrite HMAC_Zlength.
   remember (HMAC256_functional_prog.HMAC256
                   ((l ++ CONT INFO) ++
                    [Int.unsigned (Int.zero_ext 8 (Int.repr (i1 + 1)))]) 
                   (CONT PRK)) as CONTRIB. 
   forward. 
   forward_if 
  (PROP ( )
   LOCAL (temp _todo (if zlt olen
                             (Int.unsigned (Int.add (Done i1) (Int.repr 32)))
                      then Vint (Int.sub (Int.repr olen) (Done i1))
                      else Vint (Int.repr 32)); 
   temp _i (Vint (Int.repr i1));
   temp _n (Vint (Int.repr bnd)); temp _ret (Vint (Int.repr 0)); 
   temp _done (Vint (Done i1)); temp _digest_len (Vint (Int.repr 32));
   lvar _ctr tuchar v_ctr; lvar _hmac (Tstruct _hmac_ctx_st noattr) v_hmac;
   lvar _previous (tarray tuchar 64) v_previous; 
   temp _out_key out; temp _out_len (Vint (Int.repr olen));
   temp _prk prk; temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK)));
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)
   SEP (data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr CONTRIB)) v_previous;
   K_vector kv; HMAC_SPEC.FULL (CONT PRK) v_hmac; FRZL FR4)).
   { forward. entailer!. rewrite if_true; trivial; omega. } 
   { forward. entailer!. rewrite if_false; trivial; omega. } 

   thaw FR4. 
   (*destruct out; try contradiction. (*out = Vptr b1 i2*) *)
   unfold OUTpred, Done, digest_len. normalize.
   freeze [0;3;4;5;6;7] FR5.
   
   idtac "Timing the call to _memcpy".
   Time forward_call (hkdf_compspecs.CompSpecs, (Tsh, shmd), 
                 offset_val (32*i1) out, v_previous, 
                 olen - (32* i1), 32,
             if zlt olen (32 * i1 + 32)
             then olen - 32 * i1
             else 32, map Int.repr CONTRIB).
   (* Finished transaction in 4.255 secs (3.485u,0.006s) (successful)*)
   { destruct (zlt olen (32 * i1 + 32)); simpl; entailer!. }
   { simpl; cancel. }
   { simpl. split. apply readable_share_top. split; trivial.
     destruct (zlt olen (32 * i1 + 32)); omega. } 
   forward.

   (* establish loop invariant*)
   destruct (zeq (i1 + 1) 0); try omega.
   destruct (zlt olen (32 * i1 + 32)).
   + entailer!.
     * clear - OLEN2 olenBounded OLEN Hi1 REST l0. unfold Done, digest_len in *. simpl. 
(*       rewrite add_repr.*)
       destruct (zeq rest 0).
       - subst rest; simpl in *.
         destruct (zlt (i1 + 1) rounds); rewrite Int.unsigned_repr; omega.
       - destruct (zlt (i1 + 1) (rounds+1)). rewrite Int.unsigned_repr; omega.
         rewrite Int.unsigned_repr; try omega. split. omega. f_equal. f_equal. omega.
     * thaw FR5. destruct out; try contradiction. simpl. rewrite Zminus_diag, memory_block_zero_Vptr. cancel.
       clear H1 H2 H (*AC SC*) H4 H5.
       unfold data_block. normalize. rewrite LEN, data_at_tuchar_singleton_array_eq. cancel.
       rewrite sepcon_assoc. apply sepcon_derives.
       - apply data_at_ext_derives; trivial.
         rewrite zero_ext_inrange; try rewrite Int.unsigned_repr; try omega. 2: change (two_p 8 - 1) with 255; omega. 
         
         destruct (zeq i1 0).
         ++ subst l. rewrite e in *; simpl. unfold PREVcont; simpl; trivial.
         ++ clear - Hl n0 Hi1. destruct Hl. erewrite PREVcont_Sn; try eassumption. 
            rewrite if_false, app_assoc; trivial. omega.
       - unfold OUTpred, digest_len. simpl.
         destruct (zeq rest 0).
         ++ subst rest; simpl. rewrite Zplus_0_r in *. omega.
         ++ destruct (zlt (i1 + 1) (rounds + 1)); try solve [omega].
            assert (i1 = rounds) by omega. subst i1.
            replace (32 * rounds + rest - 32 * rounds) with rest by omega.
            rewrite Zmin_r; [| omega].
            rewrite Zminus_diag, memory_block_zero_Vptr; try solve [omega].
            replace (((rounds + 1)*32)%Z) with ((32 * (rounds + 1) + 0)%Z) by omega.
            rewrite (split2_data_at_Tarray_tuchar shmd (32 * rounds + rest) (32 * rounds)); simpl; trivial; try omega.
            
            Focus 2. rewrite Zlength_sublist; try omega.
                     rewrite 2 Zlength_map.
                     rewrite Zlength_HKDF_expand; simpl; omega.
            unfold tarray; cancel. 
               rewrite field_address0_offset; simpl.
               2: eapply field_compatible0_cons_Tarray; [ reflexivity | trivial | omega].
            entailer!. rewrite sublist_sublist; try omega.
            rewrite sublist_sublist; try omega. rewrite ! Z.add_0_r. 
            replace (32 * rounds + rest - 32 * rounds) with rest by omega.
            rewrite ! sublist_map.

            replace (rounds * 32)%Z with (32*rounds)%Z by omega.
            rewrite sublist_HKDF_expand4, <- sublist_HKDF_expand2; trivial; try omega.
            cancel.

   + entailer!.
     * clear H H0 H1 H2 H3 H4 H5 (*AC SC*) JMeq_1 LEN. unfold Done, digest_len in *. simpl.
       (*rewrite add_repr.*)
       destruct (zeq rest 0).
       - subst rest; simpl in *.
         destruct (zlt (i1 + 1) rounds).
         ++ split. rewrite Int.unsigned_repr; try omega.
            f_equal. f_equal. omega.
         ++ split. rewrite Int.unsigned_repr; try omega.
            f_equal. f_equal. omega.
       - destruct (zlt (i1 + 1) (rounds+1)).
         ++ split. rewrite Int.unsigned_repr; try omega.
            f_equal. f_equal. omega.
         ++ split. rewrite Int.unsigned_repr; try omega.
            f_equal. f_equal. omega.
     * thaw FR5. cancel.
       unfold data_block, digest_len. normalize. rewrite LEN, data_at_tuchar_singleton_array_eq. cancel.
       rewrite Z.min_l by omega.
       repeat rewrite sepcon_assoc. apply sepcon_derives.
       - apply data_at_ext_derives; trivial.
         rewrite zero_ext_inrange; try rewrite Int.unsigned_repr; try omega. 2: change (two_p 8 - 1) with 255; omega. 
         
         destruct (zeq i1 0).
         ++ subst l. rewrite e in *; simpl. unfold PREVcont. simpl; trivial. 
         ++ clear - Hl n0 Hi1. destruct Hl. erewrite PREVcont_Sn; try eassumption. 
            rewrite if_false, app_assoc; trivial. omega.
       - unfold OUTpred, digest_len. simpl. rewrite Z.mul_add_distr_l, Z.mul_1_r.
         rewrite zero_ext_inrange; rewrite Int.unsigned_repr; try omega.
         2: change (two_p 8 - 1) with 255; omega. 
         destruct (zeq rest 0).
         ++ subst rest; simpl in *. rewrite Zplus_0_r in *.
            destruct (zlt (i1+1) rounds).
            ** replace (32 * rounds - (32 * i1 + 32)) with (32 * rounds - 32 * i1 - 32) by omega. cancel.
               rewrite (split2_data_at_Tarray_tuchar shmd (32 * i1+32) (32 * i1)); simpl; trivial; try omega.
               -- unfold tarray. 
                  replace (32 * i1 + 32 - 32 * i1) with 32 by omega. 
                  rewrite field_address0_offset; simpl. 
                  Focus 2. eapply field_compatible0_cons_Tarray. reflexivity.  
                           eapply field_compatible_array_smaller0. apply FCout. omega. omega.
                  rewrite sublist_sublist; try omega. 
                  rewrite sublist_sublist; try omega.
                  rewrite ! sublist_map, !  Z.mul_1_l, ! Z.add_0_r, ! Z.add_0_l.
                  clear - Hl Hi1.
                  replace ((i1 + 1) * 32)%Z with (32*(i1 + 1))%Z by omega.
                  replace (i1 * 32)%Z with (32*i1)%Z by omega.
                  rewrite <- sublist_HKDF_expand2; try omega. 
                  erewrite <- sublist_HKDF_expand5; try omega; try eassumption. cancel.                      
              -- rewrite Zlength_sublist; try omega. rewrite ! Zlength_map. 
                 replace ((i1 + 1) * 32)%Z with ((32 * (i1 + 1))+0) by omega.
                 rewrite Zlength_HKDF_expand; omega.
            ** assert (rounds = i1+1) by omega. subst rounds; simpl in *.
               replace (32 * (i1 + 1))%Z with ((32 * i1 + 32)%Z) by omega.
               replace (32 * i1 + 32 - 32 * i1 - 32)%Z with 0%Z by omega.
               rewrite Zminus_diag, memory_block_zero. cancel. 
               rewrite (split2_data_at_Tarray_tuchar shmd (32 * i1 + 32) (32 * i1)); simpl; trivial; try omega.
               -- replace ((32 * i1 + 32 - 32 * i1)%Z) with 32%Z by omega.
                  rewrite field_address0_offset by auto with field_compatible. simpl. 
                  repeat rewrite sublist_sublist; try omega. rewrite ! Z.add_0_r, ! Z.add_0_l, ! Z.mul_1_l.
                  unfold tarray; rewrite sepcon_comm.
                  replace ((i1 + 1) * 32)%Z with (32*(i1+1))%Z by omega.
                  replace (i1 * 32)%Z with (32*i1)%Z by omega.
                  rewrite ! sublist_map, <- (sublist_HKDF_expand5 PRK INFO l i1 Hl),
                    <- sublist_HKDF_expand2; try omega; cancel.
               -- rewrite Zlength_sublist; try omega. rewrite 2 Zlength_map.
                  replace (((i1 + 1)*32)%Z) with ((32 * (i1 + 1) + 0)%Z) by omega.
                  rewrite Zlength_HKDF_expand; omega. 
          ++ replace (32 * rounds + rest - 32 * i1 - 32)%Z with (32 * rounds + rest - (32 * i1 + 32))%Z by omega. 
             cancel.

             rewrite (split2_data_at_Tarray_tuchar shmd (32*i1 + 32) (32*i1)); simpl; trivial; try omega.
                ** rewrite field_address0_offset; simpl. rewrite Z.mul_1_l, Z.add_0_l.
                   rewrite ! sublist_map, ! sublist_sublist, ! Z.add_0_r; try omega.
                   replace (32 * i1 + 32 - 32 * i1) with 32 by omega.
                   replace ((i1 + 1)*32)%Z with (32*(i1+1))%Z by omega.
                   replace (i1*32)%Z with (32*i1)%Z by omega.
                   rewrite <- (sublist_HKDF_expand5 PRK INFO l i1 Hl), <- sublist_HKDF_expand2; try omega. cancel.
                   eapply field_compatible0_cons_Tarray; [ reflexivity | | omega].
                   eapply field_compatible_array_smaller0; [ apply FCout | omega].
                ** rewrite ! sublist_map, ! Zlength_map, Zlength_sublist; try omega.
                   replace ((i1 + 1) * 32)%Z with (32 * (i1+1) + 0)%Z by omega.
                   rewrite Zlength_HKDF_expand; omega. }
(*Continuation after loop*)
  normalize. rewrite if_false in H. 2: omega. clear H. (*eliminate this PROP in loop invariant entirely?*)

  forward. 
    freeze [0;1;2;3;4;6] FR6.
  
  idtac "Timing the call to _HMAC_cleanup".
  Time forward_call (CONT PRK, v_hmac).
  (* Finished transaction in 1.589 secs (1.371u,0.004s) (successful)*)
    { assert (Frame = [FRZL FR6]). subst Frame; reflexivity.
      subst Frame; simpl. cancel.
      destruct (zeq bnd 0); trivial. apply HMAC_SPEC.REP_FULL. }
  forward. forward. (*
    forward_if (
  (PROP ( )
   LOCAL (temp _ret (Vint (Int.repr 1)); temp _i (Vint (Int.repr bnd));
   temp _n (Vint (Int.repr bnd));
   temp _done (Vint (if zlt bnd bnd then Done bnd else Int.repr olen));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar v_ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) v_hmac;
   lvar _previous (tarray tuchar 64) v_previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (LEN PRK))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (HMAC_SPEC.EMPTY v_hmac; FRZL FR6))).
     { forward. entailer!. } 
     { forward. entailer!. }

  forward. *)
     Exists (expand_out_post shmd (CONT PRK) (CONT INFO) (32 * rounds + rest) out).
     Time entailer!.
     + unfold expand_out_post, digest_len.
       rewrite if_false. 2: omega.
       rewrite if_false. simpl; trivial.
       destruct (zeq rest 0); simpl in *.
       - subst rest. assert (X: 32 * rounds + 0 + 32 - 1 = 32 * rounds + 31) by omega.
         rewrite X; clear X. erewrite <- Zdiv.Zdiv_unique. 3: reflexivity. omega. omega.
       - assert (X: 32 * rounds + rest + 32 - 1 = rounds * 32 + (rest + 31)) by omega.
         rewrite X; clear X.
         rewrite Z.div_add_l; try omega.
         erewrite Zdiv_unique with (b:=rest -1)(a:=1); omega.
     + thaw FR6. thaw FR0. cancel. unfold expand_out_post, digest_len. 
        rewrite 2 sepcon_assoc. rewrite sepcon_comm. apply sepcon_derives; [| apply HMAC_SPEC.EmptyDissolve]. 
        rewrite <- sepcon_assoc. rewrite sepcon_comm. apply sepcon_derives.
        - destruct (zlt (32 * rounds + rest + 32) (32 * rounds + rest)); try omega.
          destruct (zlt (if zeq rest 0 then rounds else rounds + 1) (if zeq rest 0 then rounds else rounds + 1)); try omega.
          unfold OUTpred, data_block.
          rewrite Z.min_r by (destruct (zeq rest 0); omega). 
          rewrite Zminus_diag, memory_block_zero, Zlength_HKDF_expand; try omega. normalize.
          destruct (zlt 255 ((32 * rounds + rest + 32 - 1) / 32)).
          { exfalso. destruct (zeq rest 0).
            + subst rest; simpl in *. replace (32 * rounds + 0 + 32 - 1)%Z with (rounds * 32 + 31) in l by omega.
              rewrite Z_div_plus_full_l, Zdiv_small in l; omega.
            + replace (32 * rounds + rest + 32 - 1)%Z with (rounds * 32 + (rest + 31))%Z in l by omega.
              rewrite Z_div_plus_full_l in l; try omega. erewrite (Zdiv_unique _ _ 1 ((rest + 31)-32)) in l; omega. }
          simpl.
          apply andp_right. apply prop_right; apply isbyteZ_HKDF_expand.
          apply data_at_ext_derives; trivial.
          destruct (zeq rest 0).
          * subst rest; simpl. rewrite Z.add_0_r, sublist_same, Z.mul_comm; trivial.
            rewrite ! Zlength_map. replace ((rounds*32)%Z) with ((32 * rounds + 0)%Z) by omega.
            rewrite Zlength_HKDF_expand; omega.
          * replace ((rounds + 1)*32)%Z with (32 * rounds + 32)%Z by omega.
            rewrite 2 sublist_map. f_equal. f_equal.
            apply sublist_HKDF_expand3; omega.
        - rewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
          rewrite field_address0_offset. cancel.
          eapply field_compatible0_cons_Tarray; [reflexivity | trivial | omega].
Time Qed.
  (*Finished transaction in 11.161 secs (11.057u,0.056s) *)
 (*Coq8.6:37secs*)
 (*Finished transaction in 195.171 secs (171.828u,0.031s) (successful)*)
 (* Last week: Finished transaction in 54.281 secs (49.656u,0.015s) (successful)*)

