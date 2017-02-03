Require Import floyd.proofauto.
Import ListNotations.
(*Require sha.sha.
Require Import sha.SHA256.*)
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.hmac_common_lemmas.

Require Import sha.hkdf.
Require Import sha.spec_hmac.
Require Import sha.spec_hkdf.
Require Import sha.hkdf_functional_prog.

Lemma myadmit (P:Prop): P. Admitted.

(*True in the implementation but not exposed in protocol_spec-interface*)
Axiom HMAC_CEMPTY_data_at: forall hmac,
    HMAC_SPEC.EMPTY hmac |-- data_at_ Tsh (Tstruct _hmac_ctx_st noattr) hmac.


Lemma map_Vint_injective: forall l m, map Vint l = map Vint m -> l=m.
Proof. induction l; intros.
+ destruct m; simpl in *; inv H; trivial.
+ destruct m; simpl in *; inv H. f_equal; eauto.
Qed.

Lemma map_IntReprOfBytes_injective: forall l m, Forall general_lemmas.isbyteZ  l -> 
  Forall general_lemmas.isbyteZ m -> map Int.repr l = map Int.repr m -> l=m.
Proof. induction l; intros.
+ destruct m; simpl in *; inv H1; trivial.
+ destruct m; simpl in *; inv H1. inv H. inv H0.
  rewrite (IHl m); trivial. f_equal. clear IHl H4 H6 H7.
  unfold general_lemmas.isbyteZ in *. do 2 rewrite Int.Z_mod_modulus_eq in H3.
  do 2 rewrite Zmod_small in H3; trivial; rewrite int_modulus_eq; omega. 
Qed.

Lemma isbyteZ_Ti x y : forall n, Forall general_lemmas.isbyteZ (Ti x y n).
Proof. induction n; simpl. constructor.
apply isbyte_hmac. 
Qed.

Lemma isbyteZ_T: forall n x y, Forall general_lemmas.isbyteZ (T x y n).
Proof.
induction n; simpl; intros. constructor.
apply Forall_app. split; trivial.
apply isbyte_hmac.
Qed.

Lemma Zlength_Ti PRK INFO n: Zlength (Ti PRK INFO n) = match n with O => 0 | S k => 32 end.
Proof. destruct n; simpl. apply Zlength_nil. apply HMAC_Zlength. Qed.


Lemma Zlength_T PRK INFO n: Zlength (T PRK INFO n) = Z.of_nat (32 *n).
Proof. induction n.
apply Zlength_nil.
replace (T PRK INFO (S n)) with ((T PRK INFO n) ++ (Ti PRK INFO (S n))) by reflexivity.
rewrite Zlength_app, IHn, Zlength_Ti.
do 2 rewrite Nat2Z.inj_mul. rewrite (Nat2Z.inj_succ n), Zmult_succ_r_reverse; trivial.
Qed.

Lemma isptr_field_compatible_tarray_tuchar0 p: isptr p -> 
      field_compatible (tarray tuchar 0) nil p.
Proof. intros; red. destruct p; try contradiction.
  repeat split; simpl; trivial.
  destruct (Int.unsigned_range i); omega.
  apply Z.divide_1_l. 
Qed. 

Lemma data_at_tuchar_singleton_array cs sh v p:
  @data_at cs sh tuchar v p |-- @data_at cs sh (tarray tuchar 1) [v] p.  
Proof. assert_PROP (isptr p /\ field_compatible (tarray tuchar 1) [] p) by entailer!.
  destruct H.
  unfold data_at at 2.
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  erewrite array_at_len_1. 2: apply JMeq_refl.
  rewrite field_at_data_at; simpl. 
  rewrite field_address_offset; trivial.
    simpl. rewrite isptr_offset_val_zero; trivial.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. omega.
Qed. 
Lemma data_at_tuchar_singleton_array_inv cs sh v p:
  @data_at cs sh (tarray tuchar 1) [v] p |-- @data_at cs sh tuchar v p.  
Proof. assert_PROP (isptr p /\ field_compatible (tarray tuchar 1) [] p) by entailer!.
  destruct H.
  unfold data_at at 1.
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  erewrite array_at_len_1. 2: apply JMeq_refl.
  rewrite field_at_data_at; simpl. 
  rewrite field_address_offset; trivial.
    simpl. rewrite isptr_offset_val_zero; trivial.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. omega.
Qed.
 
Lemma data_at_tuchar_singleton_array_eq cs sh v p:
  @data_at cs sh (tarray tuchar 1) [v] p = @data_at cs sh tuchar v p.  
Proof. apply pred_ext.
  apply data_at_tuchar_singleton_array_inv.
  apply data_at_tuchar_singleton_array. 
Qed. 

Lemma data_at_tuchar_zero_array cs sh p: isptr p ->
  emp |-- @data_at cs sh (tarray tuchar 0) [] p.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  rewrite array_at_len_0. apply andp_right; trivial.
  apply prop_right. apply isptr_field_compatible_tarray_tuchar0 in H.
  unfold field_compatible in H.  
  unfold field_compatible0; simpl in *. intuition.
Qed.
Lemma data_at_tuchar_zero_array_inv cs sh p:
  @data_at cs sh (tarray tuchar 0) [] p |-- emp.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  rewrite array_at_len_0. entailer. 
Qed.
Lemma data_at_tuchar_zero_array_eq cs sh p:
  isptr p ->
  @data_at cs sh (tarray tuchar 0) [] p = emp.  
Proof. intros.
  apply pred_ext.
  apply data_at_tuchar_zero_array_inv.
  apply data_at_tuchar_zero_array; trivial.
Qed. 

Lemma data_at__tuchar_zero_array cs sh p (H: isptr p):
  emp |-- @data_at_ cs sh (tarray tuchar 0) p.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array; trivial. Qed.

Lemma data_at__tuchar_zero_array_inv cs sh p:
  @data_at_ cs sh (tarray tuchar 0) p |-- emp.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array_inv. Qed.

Lemma data_at__tuchar_zero_array_eq cs sh p (H: isptr p):
  @data_at_ cs sh (tarray tuchar 0) p = emp.  
Proof. intros.
  apply pred_ext.
  apply data_at__tuchar_zero_array_inv.
  apply data_at__tuchar_zero_array; trivial.
Qed. 

Lemma split2_data_at__Tarray_tuchar
     : forall {cs} (sh : Share.t)  (n n1 : Z) (p : val),
       0 <= n1 <= n -> isptr p ->field_compatible (Tarray tuchar n noattr) [] p ->
       @data_at_ cs sh (Tarray tuchar n noattr) p =
       @data_at_ cs sh (Tarray tuchar n1 noattr) p *
       @data_at_ cs sh (Tarray tuchar (n - n1) noattr)
         (field_address0 (Tarray tuchar n noattr) [ArraySubsc n1] p).
Proof. intros. unfold data_at_ at 1; unfold field_at_.
rewrite field_at_data_at.
erewrite (@split2_data_at_Tarray cs sh tuchar n n1).
instantiate (1:= list_repeat (Z.to_nat (n-n1)) Vundef).
instantiate (1:= list_repeat (Z.to_nat n1) Vundef).
unfold field_address. simpl. 
rewrite if_true; trivial. rewrite isptr_offset_val_zero; trivial.
trivial.
simpl.
instantiate (1:=list_repeat (Z.to_nat n) Vundef).
unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl. 
unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl. 
unfold default_val. simpl. autorewrite with sublist. apply JMeq_refl.
Qed. (*ToDO: generalize to types other than tuchar?*)

Lemma change_compspecs_datablock:
  @data_block spec_hmac.CompSpecs  =
  @data_block CompSpecs.
Proof. extensionality gfs. trivial. Qed.

Lemma change_compspecs_t_struct_hmacctxstate_st:
  @data_at_ spec_hmac.CompSpecs Tsh t_struct_hmac_ctx_st =
  @data_at_ CompSpecs Tsh t_struct_hmac_ctx_st.
Proof. extensionality gfs. trivial. Qed.

Hint Rewrite change_compspecs_t_struct_SHA256state_st : norm.
Hint Rewrite change_compspecs_t_struct_hmacctxstate_st: norm.
(*
Parameter INV : DATA -> DATA -> environ -> mpred.
Parameter INVi : DATA -> DATA -> Z -> environ -> mpred.
Parameter PREINC : DATA -> DATA -> environ -> mpred.
Parameter MYPOST : DATA -> DATA -> environ -> mpred.

Parameter A:Type.
Parameter a:A.
*)
Definition Done (i:Z): int := Int.repr (digest_len*i).
(*
Definition OUTpred sh l p ii: mpred:=
  data_at_ sh (tarray tuchar (digest_len*ii)) p *
  memory_block sh (l - digest_len * ii) (offset_val (digest_len*ii) p).

Definition OUTpred PrkCont InfoCont sh l z c p: mpred:=
  data_at sh (tarray tuchar z) (map Vint (map Int.repr (HKDF_expand PrkCont InfoCont c))) p *
  memory_block sh (l - z) (offset_val z p).
*)
Definition OUTpred PrkCont InfoCont sh z r cont p: mpred:=
  data_at sh (tarray tuchar z) (sublist 0 z (map Vint (map Int.repr (HKDF_expand PrkCont InfoCont cont)))) p *
  memory_block sh r (offset_val z p).

(*
Parameter OUTpred': share -> Z -> val -> Z -> mpred.
Definition OUTpred sh l p ii: mpred:=
  if zeq ii 0 then memory_block sh l p
  else OUTpred' sh l p ii.*)
(*
Function Ri (PRK info: list Z) n:=
  match n with
  O => list_repeat 32 Vundef
 |S m => let prev := Ri PRK info m in
         HMAC256 (prev ++ info ++ [Z.of_nat n]) PRK
  end.

Function R (PRK info: list Z) (n:nat):list Z :=
  match n with
  O => nil
| S m => (T PRK info m) ++ (Ti PRK info n)
  end.*)


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
change (i+1) with (Zsucc i). rewrite Z2Nat.inj_succ; try omega. simpl.
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

Lemma isbyteZ_HKDF_expand x y z: Forall general_lemmas.isbyteZ (HKDF_expand x y z).
Proof. unfold HKDF_expand; intros.
destruct (zle z 0). constructor.
apply Forall_firstn.
apply isbyteZ_T.
Qed.

Lemma sublist_HKDF_expand1 prk info i r (I: 0 <= i) (R:0<=r<32): 
    sublist 0 (32 * i) (HKDF_expand prk info (32*i)) =
    sublist 0 (32 * i) (HKDF_expand prk info (32*i+r)).
Proof. unfold HKDF_expand.
destruct (zle (32 * i) 0); simpl.
+ assert (i=0) by omega. subst i. simpl. rewrite Z.add_0_l.
  destruct (zle r 0); trivial.
+ destruct (zle (32 * i + r) 0); try omega. 
    rewrite (Zmod_unique _ _ i 0); try omega. simpl. 
    rewrite (Zdiv_unique _ _ i 0); try omega.
    rewrite (Zmod_unique _ _ i r); try omega. 
    rewrite (Zdiv_unique _ _ i r); try omega.
  rewrite 2 sublist_sublist; try omega. simpl. rewrite Z.add_0_r.
  destruct (zeq r 0); simpl; trivial.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    2: rewrite Z.add_comm, Z2Nat.inj_add; try reflexivity; try omega.
  simpl. rewrite sublist_app1; trivial. omega.
      rewrite Zlength_T, Nat2Z.inj_mul, Z2Nat.id; simpl; omega.
Qed.

Lemma sublist_HKDF_expand2 prk info i (I: 0 <= i) : 
    sublist 0 (32 * i) (HKDF_expand prk info (32*i)) =
    sublist 0 (32 * i) (HKDF_expand prk info (32*(i+1))).
Proof. unfold HKDF_expand.
destruct (zle (32 * i) 0); simpl.
+ assert (i=0) by omega. subst i; simpl. reflexivity.
+ destruct (zle (32 * (i + 1)) 0); try omega. 
    rewrite (Zmod_unique _ _ i 0); try omega. simpl. 
    rewrite (Zdiv_unique _ _ i 0); try omega.
    rewrite (Zmod_unique _ _ (i+1) 0); try omega. 
    rewrite (Zdiv_unique _ _ (i+1) 0); try omega. simpl.
  rewrite 2 sublist_sublist; try omega. simpl. rewrite Z.add_0_r.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    2: rewrite Z.add_comm, Z2Nat.inj_add; try reflexivity; try omega.
  simpl. rewrite sublist_app1; trivial. omega.
  rewrite Zlength_T, Nat2Z.inj_mul, Z2Nat.id; simpl; omega.
Qed.

Lemma sublist_HKDF_expand3 PRK INFO i rest l (REST : 0 <= rest < 32)
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

Lemma sublist_HKDF_expand4 prk info i rest (REST : 0 < rest < 32)
      (OLEN : 0 <= 32 * i + rest):
  sublist 0 (32 * i + rest) (HKDF_expand prk info (32 * i + 32)) =
  HKDF_expand prk info (32 * i + rest).
Proof.
            unfold HKDF_expand. simpl. destruct (zle (32 * i + 32) 0); try omega.
            destruct (zle (32 * i + rest) 0); try omega.
            rewrite sublist_sublist; try omega. rewrite 2 Z.add_0_r.
            erewrite (Zmod_unique _ _(i+1) 0); try omega. simpl. 
            erewrite (Zdiv_unique _ _(i+1) 0); try omega.
            erewrite (Zmod_unique _ _ i rest); try omega. rewrite if_false; try omega.
            erewrite (Zdiv_unique _ _ i rest); try omega; trivial.
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

Lemma Zlength_HKDF_expand x y z rest: 0 <= 32 * z -> 0 <= rest < 32 -> 
      (Zlength (HKDF_expand x y (32*z+rest)) = 32*z+rest)%Z.
Proof. unfold HKDF_expand; intros.
destruct (zle (32*z+rest) 0).
+ rewrite Zlength_nil; omega.
+ rewrite Zlength_sublist; try omega. simpl.
  rewrite Zlength_T.
  destruct (zeq rest 0).
  - subst rest. rewrite Z.add_0_r in *.
    assert (X: (32 * z) mod 32 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
    rewrite X, if_true; trivial. 
    assert (Y: (32 * z) / 32 = z). rewrite Z.mul_comm; apply Z_div_mult_full; omega.
    rewrite Y, Nat2Z.inj_mul, Z2Nat.id; simpl; omega. 
  - rewrite if_false. 
    * replace (32 * z + rest) with (z * 32 + rest) by omega.
      rewrite Z_div_plus_full_l, Zdiv_small, Zplus_0_r; try omega.
      rewrite Nat2Z.inj_mul, Z2Nat.id. simpl. 2: omega.
      rewrite Z.mul_add_distr_l, Z.mul_1_r. omega.
    * intros N. replace (32 * z + rest) with (rest + z * 32) in N by omega.
      rewrite Z_mod_plus, Zmod_small in N; omega.
Qed.

Lemma body_hkdf_expand: semax_body Hkdf_VarSpecs Hkdf_FunSpecs 
       f_HKDF_expand HKDF_expand_spec.
Proof.
start_function. rename lvar0 into previous.
rename lvar1 into hmac. rename lvar2 into ctr.
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
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).
{ forward. Exists (Vint (Int.repr 1)). erewrite zlt_true; try eapply H.
  entailer!. } 
{ forward.
  Exists (Val.of_bool (Int.ltu (Int.repr 255) (Int.repr ((olen + 32 - 1) / 32)))).
  rewrite if_false; trivial.
  entailer. unfold sem_cast; simpl. 
  rewrite sem_cast_i2i_correct_range; [| apply semax_straight.is_int_of_bool]; simpl.
  apply prop_right; trivial. }
apply extract_exists_pre. intros v. Intros. rename H into HV.
unfold Int.ltu in HV.
rewrite Int.unsigned_repr in HV; [| rewrite int_max_unsigned_eq; omega].
rewrite Int.unsigned_repr in HV; [| omega].
unfold Val.of_bool in HV. 
forward_if 
  (PROP ((*255 >= Int.unsigned (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32)) *)
         v=Vint (Int.repr 0))
   LOCAL (temp _t'1 v; temp _n (Vint (Int.repr ((olen + 32 - 1) / 32)));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (Int.repr 0));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).
{ unfold typed_true in H.
  rewrite if_false in HV; try omega.
  subst v.
  destruct (zlt 255 ((olen + 32 - 1) / 32)); [clear H | inv H].
  forward. Exists ctr. Exists hmac. Exists previous.
  Exists (expand_out_post shmd (CONT PRK) (CONT INFO) olen out).
  thaw FR1; entailer. unfold expand_out_post, digest_len; simpl.
  rewrite if_false; try omega.
  rewrite if_true; trivial. entailer!. }
{ forward. entailer. unfold typed_false in H; simpl in H; inv H.
  destruct (zlt (olen + 32) olen). inv HV; simpl in *; try discriminate.
  destruct (zlt 255 ((olen + 32 - 1) / 32)); inv HV; simpl in *; try discriminate. 
  entailer!. }
Intros. subst v. rewrite if_false in HV; try omega. 
destruct (zlt 255 ((olen + 32 - 1) / 32)); [inv HV | clear HV]. 
drop_LOCAL 0%nat.
thaw FR1. 
Time assert_PROP (isptr prk) as isPtrPrk by entailer!. destruct prk; try contradiction.
(*
assert (AUX1: @data_at_ CompSpecs Tsh (Tstruct _hmac_ctx_st noattr) = 
        @data_at_ spec_hmac.CompSpecs Tsh (Tstruct _hmac_ctx_st noattr)) by normalize.  
(*rewrite H.*)
assert (AUX2: @data_block CompSpecs Tsh (CONT PRK) = 
        @data_block spec_hmac.CompSpecs Tsh (CONT PRK)) by normalize.  
(*rewrite H0.*)
assert (Tstruct _hmac_ctx_st noattr = t_struct_hmac_ctx_st). 
{ unfold _hmac_ctx_st, t_struct_hmac_ctx_st. simpl. adxmit.
assert (tptr (Tstruct _hmac_ctx_st noattr) = tptr t_struct_hmac_ctx_st). rewrite H1; trivial. 
rewrite H2.*)

(*remember (inr(hmac, spec_hmac.LEN PRK, CONT PRK, kv, b, i): (val * Z * list Z * val + val * Z * list Z * val * block * int)) as w.*)
freeze [0;2;3;6] FR1.
assert_PROP (field_compatible t_struct_hmac_ctx_st [] hmac) as FC_hmac by entailer!.
(*rewrite H1.*)
replace_SEP 1 (HMAC_SPEC.EMPTY hmac).
{ rewrite data_at__memory_block. entailer. eapply HMAC_SPEC.mkEmpty; trivial. }
(*rewrite <- H1.*)
forward_call (@inr (val * Z * list Z * val) _ (hmac, spec_hmac.LEN PRK, CONT PRK, kv, b, i)).

remember ((olen + 32 - 1) / 32) as bnd.
thaw FR1.
assert_PROP (isptr previous /\ field_compatible (tarray tuchar 64) [] previous) as prevPtr by entailer!.
destruct prevPtr as [prevPtr prevFC].
destruct previous; try contradiction. clear prevPtr.

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
rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
rewrite field_address0_offset by auto with field_compatible. simpl.

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

assert_PROP (field_compatible (tarray tuchar olen) nil out) as FCout.
{ entailer. apply prop_right. red; repeat split; simpl; trivial.
  + unfold legal_alignas_type, tarray, nested_pred, local_legal_alignas_type; simpl.
     rewrite andb_true_r. apply Zle_imp_le_bool. apply OLEN.
  + rewrite Z.max_r, Z.mul_1_l, <- initialize.max_unsigned_modulus; omega.
  + red. destruct out; try contradiction. simpl. rewrite Z.max_r, Z.mul_1_l; try omega. 
    apply myadmit. (*maybe replace memory_block with data_at_ in spec?*)
  + red. destruct out; try contradiction. unfold alignof, align_attr; simpl. apply Z.divide_1_l. }

forward_for_simple_bound bnd
       (EX ii:Z, PROP (0 <= olen - Int.unsigned(if zlt ii bnd then Done ii else Int.repr olen))
             LOCAL (temp _n (Vint (Int.repr bnd)); 
                    temp _ret (Vint (Int.repr 0)); 
                    temp _done (Vint (if zlt ii bnd then Done ii else Int.repr olen));
                    temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
                    lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac; lvar _previous (tarray tuchar 64) (Vptr b0 i0);
                    temp _out_key out; temp _out_len (Vint (Int.repr olen)); temp _prk (Vptr b i);
                    temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); temp _info info;
                    temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO))); gvar sha._K256 kv)
             SEP (FRZL FR0; K_vector kv; data_at_ Tsh tuchar ctr; 
            data_at Tsh (Tarray tuchar 32 noattr) (PREVcont PRK INFO ii) (Vptr b0 i0);
            data_block Tsh (CONT INFO) info;
            (*hmacstate_ (HMACcont ii) hmac;*)
            if zeq ii 0 then HMAC_SPEC.REP (HMAC_SPEC.hABS (CONT PRK) []) hmac
            else HMAC_SPEC.FULL (CONT PRK) hmac; 
            (*OUTpred shmd olen out ii*)
            OUTpred (CONT PRK) (CONT INFO) shmd (Z.min (digest_len * ii) olen) 
                    (olen - Z.min (digest_len * ii) olen)
                    (*(if zlt ii bnd then digest_len * ii else olen)*) (ii*32) out)).
{ destruct (zeq 0 0); try solve [omega]. clear e; entailer!.
  + unfold Done; simpl. (*rewrite Int.unsigned_repr; [| omega]. split; try omega.*)
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
    - rewrite Zmin_l. (*if_true.*) 2: omega. rewrite Zminus_0_r, data_at_tuchar_zero_array_eq; trivial.
      rewrite isptr_offset_val_zero; trivial. cancel.
}

{ (*loop body*)
  rename H into Hi1. Intros. rename H into olenBounded. unfold Done, digest_len in olenBounded.
  (*rewrite Int.unsigned_repr in olenBounded. 2: rewrite int_max_unsigned_eq; omega. *)
   rewrite if_true in olenBounded; try omega.
   rewrite Int.unsigned_repr in olenBounded. 2: rewrite int_max_unsigned_eq; omega.
   
  forward. rewrite Zmin_l. 2: unfold digest_len; omega.

  forward_if (EX l:_, 
  PROP ( if zeq i1 0 then l=@nil Z else PREVcont PRK INFO i1 = map Vint (map Int.repr l) /\ Forall general_lemmas.isbyteZ l)
   LOCAL (temp _i (Vint (Int.repr i1)); temp _n (Vint (Int.repr bnd));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (if zlt i1 bnd then Done i1 else Int.repr olen));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) (Vptr b0 i0); temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk (Vptr b i);
   temp _prk_len (Vint (Int.repr (LEN PRK))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (FRZL FR0; K_vector kv;
   field_at Tsh tuchar []
     (Vint (cast_int_int I8 Unsigned (Int.add (Int.repr i1) (Int.repr 1)))) ctr;
   data_at Tsh (Tarray tuchar 32 noattr) (PREVcont PRK INFO i1) (Vptr b0 i0);
   data_block Tsh (CONT INFO) info; 
   (*OUTpred shmd olen out i1*)(*OUTpred (CONT PRK) (CONT INFO) shmd olen  (digest_len * i1)%Z 
          (if zlt i1 bnd then (digest_len * i1)%Z else olen) out;*)
   OUTpred (CONT PRK) (CONT INFO) shmd (digest_len * i1) (olen - digest_len * i1) (i1*32) out;
   HMAC_SPEC.REP (HMAC_SPEC.hABS (CONT PRK) l) hmac)).

   { destruct (zlt i1 bnd); try omega. rewrite if_false; trivial.
     freeze [0;2;4;6] FR1.
     forward_call (@inl _ (val * Z * list Z * val * block * int) (hmac,0,CONT PRK,kv)).
     destruct (PREV_isbyteZ PRK INFO i1) as [prev [Hprev BTprev]]. omega. rewrite Hprev.
     assert (Zlength_prev: Zlength prev = 32).
     { specialize (PREV_len PRK INFO i1). rewrite Hprev.
       do 2 rewrite Zlength_map. intros X; rewrite X; trivial. omega. }
     forward_call (CONT PRK, hmac, Vptr b0 i0, @nil Z, prev, kv).
     * rewrite Zlength_prev; apply prop_right; trivial. 
     * assert (Frame = [FRZL FR1]). subst Frame; reflexivity. simpl; cancel.
       unfold data_block. rewrite Zlength_prev. entailer!.
     * rewrite Zlength_prev, Zlength_nil.
       split. rewrite int_max_unsigned_eq; omega.
       cbv; trivial.
     * Exists prev. rewrite if_false; trivial. thaw FR1. (*rewrite if_true; try omega.*) entailer!. 
       unfold data_block. rewrite Hprev, Zlength_prev. clear - prevFC. unfold tarray. normalize. apply andp_left2. trivial. (*VST why does entailer fail to do this?*) 
     (* * omega.*) }
   { subst i1. forward. Exists (@nil Z). repeat rewrite if_true; try omega.
     entailer!. }

   apply extract_exists_pre. intros l. Intros. rename H into Hl. rewrite if_true. 2: omega. 

   forward_call (CONT PRK, hmac, info, l, CONT INFO, kv).
   { rewrite LEN_INFO1; apply prop_right; reflexivity. }
   { split. omega.
     destruct (zeq i1 0).
     + subst i1 l. rewrite Zlength_nil, Zplus_0_r. omega.
     + assert (Arith1: 0<= i1) by omega. specialize (PREV_len PRK INFO i1 Arith1); intros HZ.
       destruct Hl.
       assert (HH: Zlength (@map int val Vint (@map Z int Int.repr l)) = @Zlength val (PREVcont PRK INFO i1))
         by (f_equal; auto).
       repeat rewrite Zlength_map in HH. rewrite HH, HZ, <- Zplus_assoc; simpl. omega. }
   
   simpl. freeze [1;3;5;6] FR3.
   assert_PROP (field_compatible (tarray tuchar 1) [] ctr /\ isptr ctr) as HH by entailer!.
   destruct HH as [FC_cptr isptrCtr]. 
   
   replace_SEP 3 (data_at Tsh (tarray tuchar 1) [Vint (Int.zero_ext 8 (Int.add (Int.repr i1) (Int.repr 1)))] ctr).
   { entailer!. apply data_at_tuchar_singleton_array. }
 
   assert (Forall general_lemmas.isbyteZ [Int.unsigned (Int.zero_ext 8 (Int.repr (i1+1)))]) as isBT.
      { constructor. red. rewrite zero_ext_inrange; rewrite Int.unsigned_repr. omega.
         rewrite int_max_unsigned_eq; omega.
         assert (Arith1: two_p 8 - 1 = 255) by reflexivity. rewrite Arith1; omega.
         rewrite int_max_unsigned_eq; omega. constructor. }
   assert (LEN: Zlength [Int.unsigned (Int.zero_ext 8 (Int.add (Int.repr i1) (Int.repr 1)))] = 1) by reflexivity.
   forward_call (CONT PRK, hmac, ctr, l++CONT INFO, 
        [Int.unsigned (Int.zero_ext 8 (Int.add (Int.repr i1) (Int.repr 1)))], kv). 
   { assert (Frame = [FRZL FR3]). subst Frame; reflexivity. subst Frame. simpl. cancel.
     unfold data_block. simpl. rewrite Int.repr_unsigned, LEN. entailer!. }
   { rewrite LEN. rewrite int_max_unsigned_eq, Zlength_app. split. omega.
     destruct (zeq i1 0).
     + subst l; rewrite Zlength_nil. rewrite Z.add_0_l. omega.
     + specialize (PREV_len PRK INFO i1). destruct Hl as [Hl isbyte_l]. rewrite Hl. do 2 rewrite Zlength_map.
       intros HH; rewrite HH; omega. } 

   normalize. thaw FR3. freeze [1;3;4;6] FR4.
   replace_SEP 3 (memory_block Tsh 32 (Vptr b0 i0)).
   { entailer!. eapply derives_trans. apply data_at_memory_block. trivial. }
   forward_call (((l ++ CONT INFO) ++ [Int.unsigned (Int.zero_ext 8 (Int.repr (i1 + 1)))]),
                 CONT PRK, hmac, Vptr b0 i0, Tsh, kv).
   unfold data_block. normalize. focus_SEP 2. erewrite (extract_prop_in_SEP 0); simpl. 2: reflexivity.
   Intros. (*VST TODO: why does normalize/Intros need the explicit extract_prop_in_SEP???*)
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
   lvar _ctr tuchar ctr; lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) (Vptr b0 i0); 
   temp _out_key out; temp _out_len (Vint (Int.repr olen));
   temp _prk (Vptr b i); temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK)));
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)
   SEP (data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr CONTRIB)) (Vptr b0 i0);
   K_vector kv; HMAC_SPEC.FULL (CONT PRK) hmac; FRZL FR4)).
   { forward. entailer!. rewrite if_true; trivial; omega. } 
   { forward. entailer!. rewrite if_false; trivial; omega. } 

   thaw FR4. 
   destruct out; try contradiction. (*out = Vptr b1 i2*) 
   (* unfold abbreviate in FR0. simpl in FR0. *)
   unfold OUTpred, Done, digest_len. normalize.
   freeze [0;3;4;5;6;7] FR5.
   forward_call ((Tsh, shmd), offset_val (32*i1) (Vptr b1 i2), Vptr b0 i0, 
                 olen - (32* i1), 32,
             if zlt olen (32 * i1 + 32)
             then olen - 32 * i1
             else 32, map Int.repr CONTRIB).
   { destruct (zlt olen (32 * i1 + 32)); simpl; entailer!. }
   { (*rewrite if_true; [| omega].*) simpl. cancel. }
   { simpl. split. apply readable_share_top. split; trivial.
     destruct (zlt olen (32 * i1 + 32)); omega. } 
   forward.

   (* establish loop invariant*)
   destruct (zeq (i1 + 1) 0); try omega.
   destruct (zlt olen (32 * i1 + 32)).
   + entailer!.
     * clear - OLEN2 olenBounded OLEN Hi1 REST l0. unfold Done, digest_len in *. simpl. 
       rewrite add_repr.
       destruct (zeq rest 0).
       - subst rest; simpl in *.
         destruct (zlt (i1 + 1) rounds); rewrite Int.unsigned_repr; omega.
       - destruct (zlt (i1 + 1) (rounds+1)). rewrite Int.unsigned_repr; omega.
         rewrite Int.unsigned_repr; try omega. split. omega. f_equal. f_equal. omega.
     * thaw FR5. rewrite Zminus_diag, memory_block_zero_Vptr. cancel.
       clear H1 H2 H AC SC H4 H5.
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
            (*replace (32 * rounds + rest - 32 * (rounds + 1)) with (rest - 32) by omega. *)
            rewrite (*if_true,*) Zminus_diag, memory_block_zero_Vptr; try solve [omega].
            replace (((rounds + 1)*32)%Z) with ((32 * (rounds + 1) + 0)%Z) by omega.
            rewrite (split2_data_at_Tarray_tuchar shmd (32 * rounds + rest) (32 * rounds)); simpl; trivial; try omega.
            
            Focus 2. rewrite Zlength_sublist; try omega.
                     rewrite 2 Zlength_map.
                     rewrite Zlength_HKDF_expand; simpl; omega.
            unfold tarray; cancel. 
               rewrite field_address0_offset; simpl.
               2: eapply field_compatible0_cons_Tarray; try reflexivity; trivial.
               2: omega.
            entailer!. rewrite sublist_sublist; try omega.
            rewrite sublist_sublist; try omega. rewrite ! Z.add_0_r. 
            replace (32 * rounds + rest - 32 * rounds) with rest by omega.
            rewrite ! sublist_map.

            rewrite sepcon_comm. apply sepcon_derives; apply data_at_ext_derives; trivial.
            -- replace (rounds * 32)%Z with (32*rounds)%Z by omega.
               rewrite <- sublist_HKDF_expand2; trivial; omega.
            -- f_equal. f_equal. apply sublist_HKDF_expand3; trivial; try omega.
   + entailer!.
     * clear H H0 H1 H2 H3 H4 H5 AC SC JMeq_1 LEN. unfold Done, digest_len in *. simpl.
       rewrite add_repr.
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
  
    forward_call (CONT PRK, hmac).
    { assert (Frame = [FRZL FR6]). subst Frame; reflexivity.
      subst Frame; simpl. cancel.
      destruct (zeq bnd 0); trivial. apply HMAC_SPEC.REP_FULL. }
    forward_if (
  (PROP ( )
   LOCAL (temp _ret (Vint (Int.repr 1)); temp _i (Vint (Int.repr bnd));
   temp _n (Vint (Int.repr bnd));
   temp _done (Vint (if zlt bnd bnd then Done bnd else Int.repr olen));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) (Vptr b0 i0); temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk (Vptr b i);
   temp _prk_len (Vint (Int.repr (LEN PRK))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (HMAC_SPEC.EMPTY hmac; FRZL FR6))).
     { forward. entailer!. } 
     { forward. entailer!. }

  forward. Exists ctr. Exists hmac. Exists (Vptr b0 i0). 
     Exists (expand_out_post shmd (CONT PRK) (CONT INFO) (32 * rounds + rest) out).
     Time entailer.
     apply andp_right.
     + apply prop_right. unfold expand_out_post, digest_len.
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

        rewrite 2 sepcon_assoc. rewrite sepcon_comm. apply sepcon_derives; [| apply HMAC_CEMPTY_data_at].
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
            apply sublist_HKDF_expand4; omega.
        - rewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
          rewrite field_address0_offset. cancel.
          eapply field_compatible0_cons_Tarray; [reflexivity | trivial | omega].
Time Qed. (* Finished transaction in 54.281 secs (49.656u,0.015s) (successful)*)
            