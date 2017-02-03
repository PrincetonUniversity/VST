Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import floyd.library.
Require Import sha.general_lemmas.

(************************ TO BE MOVED SOMEWHERE INSODE FLOYD****************)
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

Lemma isptr_field_compatible_tarray_tuchar0 {cs} p: isptr p -> 
      @field_compatible cs (tarray tuchar 0) nil p.
Proof. intros; red. destruct p; try contradiction.
  repeat split; simpl; trivial.
  destruct (Int.unsigned_range i); omega.
  apply Z.divide_1_l. 
Qed. 

Lemma data_at_tuchar_singleton_array {cs} sh v p:
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
Lemma data_at_tuchar_singleton_array_inv {cs} sh v p:
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
 
Lemma data_at_tuchar_singleton_array_eq {cs} sh v p:
  @data_at cs sh (tarray tuchar 1) [v] p = @data_at cs sh tuchar v p.  
Proof. apply pred_ext.
  apply data_at_tuchar_singleton_array_inv.
  apply data_at_tuchar_singleton_array. 
Qed. 

Lemma data_at_tuchar_zero_array {cs} sh p: isptr p ->
  emp |-- @data_at cs sh (tarray tuchar 0) [] p.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  rewrite array_at_len_0. apply andp_right; trivial.
  apply prop_right. apply isptr_field_compatible_tarray_tuchar0 in H.
  unfold field_compatible in H.  
  unfold field_compatible0; simpl in *. intuition.
Qed.
Lemma data_at_tuchar_zero_array_inv {cs} sh p:
  @data_at cs sh (tarray tuchar 0) [] p |-- emp.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial. 
  rewrite array_at_len_0. entailer. 
Qed.

Lemma data_at_tuchar_zero_array_eq {cs} sh p:
  isptr p ->
  @data_at cs sh (tarray tuchar 0) [] p = emp.  
Proof. intros.
  apply pred_ext.
  apply data_at_tuchar_zero_array_inv.
  apply data_at_tuchar_zero_array; trivial.
Qed. 

Lemma data_at__tuchar_zero_array {cs} sh p (H: isptr p):
  emp |-- @data_at_ cs sh (tarray tuchar 0) p.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array; trivial. Qed.

Lemma data_at__tuchar_zero_array_inv {cs} sh p:
  @data_at_ cs sh (tarray tuchar 0) p |-- emp.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array_inv. Qed.

Lemma data_at__tuchar_zero_array_eq {cs} sh p (H: isptr p):
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

(****************************************************************************)



Require Import sha.spec_sha.
Require Import sha.protocol_spec_hmac.

Require Import sha.hkdf_functional_prog.
Require Import sha.hkdf.
Require Import sha.hkdf_compspecs.

Declare Module HMAC_SPEC : HMAC_ABSTRACT_SPEC.
Definition digest_len:Z := 32.
Definition expand_out_post sh PrkCont InfoCont olen out: Z * mpred :=
  let n := (olen + digest_len - 1) / digest_len in
  if zlt (olen + digest_len) olen 
  then (0, memory_block sh olen out)
  else if zlt 255 n 
       then (0, memory_block sh olen out)
       else (1, data_block sh (HKDF_expand PrkCont InfoCont olen) out).

(*todo: refine spec to capture path leading to rv=0*)
Definition HKDF_expand_spec :=
  DECLARE _HKDF_expand
   WITH out: val, olen:Z,
        prk: val, PRK:spec_hmac.DATA,
        info: val, INFO:spec_hmac.DATA,
        kv:val, shmd: share
   PRE [ _out_key OF tptr tuchar, _out_len OF tuint,
         _prk OF tptr tuchar, _prk_len OF tuint,
         _info OF tptr tuchar, _info_len OF tuint]
         PROP (writable_share shmd; 
               spec_hmac.has_lengthK (spec_hmac.LEN PRK) (spec_hmac.CONT PRK);
               spec_hmac.LEN INFO = Zlength (spec_hmac.CONT INFO);
               0 <= Zlength (spec_hmac.CONT INFO) <= Int.max_unsigned /\
                 Zlength (spec_hmac.CONT INFO) + 97 < two_power_pos 61;
               0 <= olen /\ olen + 32 <= Int.max_unsigned)
         LOCAL (temp _out_key out; temp _out_len (Vint (Int.repr olen)); 
                temp _prk prk;
                temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK)));
                temp _info info;
                temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (spec_hmac.CONT INFO) info;
             data_block Tsh (spec_hmac.CONT PRK) prk;
             K_vector kv;
             memory_block shmd olen out
             (*data_at_ shmd (tarray tuchar olen) out*))
  POST [ tint ] EX result:_,
          PROP (result = expand_out_post shmd (spec_hmac.CONT PRK) (spec_hmac.CONT INFO) olen out)
          LOCAL (temp ret_temp (Vint (Int.repr (fst result))))
          SEP(K_vector kv;
              data_block Tsh (spec_hmac.CONT INFO) info;
              data_block Tsh (spec_hmac.CONT PRK) prk;
              (snd result)).

Definition HKDF_extract_spec :=
  DECLARE _HKDF_extract
   WITH out: val, olen:val,
        secret: val, SECRET:spec_hmac.DATA,
        salt: val, SALT:spec_hmac.DATA,
        kv:val, shmd: share
   PRE [_out_key OF tptr tuchar, _out_len OF tptr tuint,
        _secret OF tptr tuchar, _secret_len OF tuint,
        _salt OF tptr tuchar, _salt_len OF tuint ]
         PROP (writable_share shmd; spec_hmac.has_lengthK (spec_hmac.LEN SALT) (spec_hmac.CONT SALT);
               spec_hmac.has_lengthD 512 (spec_hmac.LEN SECRET) (spec_hmac.CONT SECRET))
         LOCAL (temp _out_key out;  
                temp _out_len olen;
                temp _salt salt;
                temp _salt_len (Vint (Int.repr (spec_hmac.LEN SALT)));
                temp _secret secret;
                temp _secret_len (Vint (Int.repr (spec_hmac.LEN SECRET)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (spec_hmac.CONT SECRET) secret;
             data_block Tsh (spec_hmac.CONT SALT) salt;
             K_vector kv; data_at_ Tsh tuint olen;
             memory_block shmd 32 out)
  POST [ tint ]  
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr 1)))
          SEP(K_vector kv;
              data_block Tsh (spec_hmac.CONT SECRET) secret;
              data_block Tsh (spec_hmac.CONT SALT) salt; data_at Tsh tuint (Vint (Int.repr 32)) olen;
              data_block shmd (HKDF_extract (spec_hmac.CONT SALT) (spec_hmac.CONT SECRET)) out).

Definition HKDF_spec :=
  DECLARE _HKDF
   WITH out: val, olen:Z, 
        secret: val, SECRET:spec_hmac.DATA,
        salt: val, SALT:spec_hmac.DATA,
        info:val, INFO:spec_hmac.DATA,
        kv:val, shmd: share
   PRE [_out_key OF tptr tuchar, _out_len OF tuint,
        _secret OF tptr tuchar, _secret_len OF tuint,
        _salt OF tptr tuchar, _salt_len OF tuint,
        _info OF tptr tuchar, _info_len OF tuint ]
         PROP (writable_share shmd; spec_hmac.has_lengthK (spec_hmac.LEN SALT) (spec_hmac.CONT SALT); 
               spec_hmac.has_lengthD 512 (spec_hmac.LEN SECRET) (spec_hmac.CONT SECRET);
               spec_hmac.LEN INFO = Zlength (spec_hmac.CONT INFO); 0 <= Zlength (spec_hmac.CONT INFO) <= Int.max_unsigned;
               Zlength (spec_hmac.CONT INFO) + 97 < two_power_pos 61; 0 <= olen; olen + 32 <= Int.max_unsigned)
         LOCAL (temp _out_key out; temp _out_len (Vint (Int.repr olen)); 
                temp _salt salt;
                temp _salt_len (Vint (Int.repr (spec_hmac.LEN SALT)));
                temp _secret secret;
                temp _secret_len (Vint (Int.repr (spec_hmac.LEN SECRET)));
                temp _info info;
                temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (spec_hmac.CONT SECRET) secret;
             data_block Tsh (spec_hmac.CONT SALT) salt;
             data_block Tsh (spec_hmac.CONT INFO) info;
             K_vector kv;
             memory_block shmd olen out)
  POST [ tint ] EX r:Z,
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr r)))
          SEP(K_vector kv;
              data_block Tsh (spec_hmac.CONT SECRET) secret;
              data_block Tsh (spec_hmac.CONT SALT) salt;
              data_block Tsh (spec_hmac.CONT INFO) info;
              if zlt 255 ((olen + 31) / 32) 
              then (!!(r=0) && memory_block shmd olen out)
              else (!!(r=1) && data_block shmd (HKDF (spec_hmac.CONT SALT) (spec_hmac.CONT SECRET) (spec_hmac.CONT INFO) olen) out)).

(*generalizes spec_sha.memcpy_spec by allowing SRC/TGT-array to be longer than necessary*)
Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, m:Z, k:Z, contents: list int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 0 <= k <= n;
       k <= m <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr k)))
       SEP (data_at (fst sh) (tarray tuchar m) (map Vint contents) q;
              memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at (fst sh) (tarray tuchar m) (map Vint contents) q;
           data_at (snd sh) (tarray tuchar k) (map Vint (sublist 0 k contents)) p;
              memory_block (snd sh) (n-k) (offset_val k p)).
(*Definition memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec). *)

(***************** We combine all specifications to a specification context *******)

(*Definition SHA256_spec := (_SHA256, snd spec_sha.SHA256_spec). *)(*
Definition sha256init_spec := (_SHA256_Init, snd SHA256_Init_spec).
Definition sha256update_spec := (_SHA256_Update, snd SHA256_Update_spec).
Definition sha256final_spec := (_SHA256_Final, snd SHA256_Final_spec).
Definition memset_spec := (_memset, snd spec_sha.memset_spec). *)

Definition Hkdf_VarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.


Definition hmac_init_funspec:=
    (WITH x : val * Z * list Z * val + val * Z * list Z * val * block * int PRE
     [(hmac._ctx, tptr spec_hmac.t_struct_hmac_ctx_st), (hmac._key, tptr tuchar),
     (hmac._len, tint)] match x with
                        | inl (c, l, key, kv) =>
                            PROP ( )
                            LOCAL (temp hmac._ctx c; temp hmac._key nullval;
                            temp hmac._len (Vint (Int.repr l)); 
                            gvar sha._K256 kv)
                            SEP (HMAC_SPEC.FULL key c;
                            spec_sha.K_vector kv)
                        | inr (c, l, key, kv, b0, i) =>
                            PROP (spec_hmac.has_lengthK l key)
                            LOCAL (temp hmac._ctx c; temp hmac._key (Vptr b0 i);
                            temp hmac._len (Vint (Int.repr l)); 
                            gvar sha._K256 kv)
                            SEP (HMAC_SPEC.EMPTY c;
                            spec_sha.data_block Tsh key (Vptr b0 i); 
                            spec_sha.K_vector kv)
                        end
     POST [tvoid] match x with
                  | inl (c, _, key, kv) =>
                      PROP ( )
                      LOCAL ()
                      SEP (HMAC_SPEC.REP
                             (HMAC_SPEC.hABS key []) c;
                      spec_sha.K_vector kv)
                  | inr (c, _, key, kv, b0, i) =>
                      PROP ( )
                      LOCAL ()
                      SEP (HMAC_SPEC.REP
                             (HMAC_SPEC.hABS key []) c;
                      spec_sha.data_block Tsh key (Vptr b0 i); 
                      spec_sha.K_vector kv)
                  end).

Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  (HMAC_SPEC.hmac_update_spec)::
  (HMAC_SPEC.hmac_final_spec)::  
  (HMAC_SPEC.hmac_cleanup_spec)::  
  (_HMAC_Init, hmac_init_funspec)::
  (HMAC_SPEC.hmac_crypto_spec)::nil)).
(*
Inductive augmentFunspecsResult :=
  OK_aFR: funspecs -> augmentFunspecsResult 
| DeleteErr_aFR: ident -> augmentFunspecsResult 
| NoDeletaErr_aFR: ident -> augmentFunspecsResult
| MismatchErr_aFR: list ident ->  augmentFunspecsResult.

Fixpoint my_augment_funspecs' (fds: list (ident * fundef)) (G:funspecs) :augmentFunspecsResult :=
 match fds with
 | (i,fd)::fds' => match delete_id i G with
                       | Some (f, G') => 
                              match my_augment_funspecs' fds' G' with
                               | OK_aFR G2 => OK_aFR ((i,f)::G2)
                               | DeleteErr_aFR i => DeleteErr_aFR i
                               | NoDeletaErr_aFR i => NoDeletaErr_aFR i
                               | MismatchErr_aFR l => MismatchErr_aFR l
                              end
                       | None =>
                              match my_augment_funspecs' fds' G with
                               | OK_aFR G2 => OK_aFR ((i, vacuous_funspec fd)::G2)
                               | DeleteErr_aFR i => DeleteErr_aFR i
                               | NoDeletaErr_aFR i => NoDeletaErr_aFR i
                               | MismatchErr_aFR l => MismatchErr_aFR l
                              end
                        end
 | nil => match G with nil => OK_aFR nil | (* _::_ => None*) (h::t) => MismatchErr_aFR (map fst (h::t)) end
 end.
(*
Fixpoint my_augment_funspecs' (fds: list (ident * fundef)) (G:funspecs) : option funspecs :=
 match fds with
 | (i,fd)::fds' => match delete_id i G with
                       | Some (f, G') => 
                              match my_augment_funspecs' fds' G' with
                               | Some G2 => Some ((i,f)::G2)
                               | None => None
                              end
                       | None =>
                              match my_augment_funspecs' fds' G with
                               | Some G2 => Some ((i, vacuous_funspec fd)::G2)
                               | None => None
                              end
                        end
 | nil => match G with nil => Some nil | _::_ => None end
 end.*)

Definition StringofPos (p:positive): string := String (Coq.Strings.Ascii.ascii_of_pos p) EmptyString.

Delimit Scope string_scope with string.
Bind Scope string_scope with string.
Open Local Scope string_scope.
Definition printlist (l:list ident):string := List.fold_right (fun p s => String (Coq.Strings.Ascii.ascii_of_pos p) s) EmptyString l.

Ltac mywith_library' p G :=
  let x := eval hnf in (my_augment_funspecs' (prog_funct p) G) in match x with
  | OK_aFR ?l => exact l
  | DeleteErr_aFR ?i => let v := constr:("Delete " ++ (StringofPos i)) in fail 5 v
  | NoDeletaErr_aFR ?i => let v:= constr:("NoDelete " ++ (StringofPos i)) in fail 5 v
  | MismatchErr_aFR ?l => let v := constr:("Mismatch " ++ printlist (map fst l))                                  
                          in fail 5 v
  end.

Ltac mywith_library prog G := mywith_library' prog G.
Locate _HMAC.
Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
(*  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  HMAC_SPEC.hmac_update_spec::
  HMAC_SPEC.hmac_final_spec::  
  HMAC_SPEC.hmac_cleanup_spec::  
  (_HMAC_Init,hmac_init_funspec)::*)
  _HMAC, (snd HMAC_SPEC.hmac_crypto_spec)::nil)).
Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  HMAC_SPEC.hmac_update_spec::
  HMAC_SPEC.hmac_final_spec::  
  HMAC_SPEC.hmac_cleanup_spec::  
  (_HMAC_Init,hmac_init_funspec)::
  HMAC_SPEC.hmac_crypto_spec::nil)).
(*
Definition HMS : hmacstate := default_val t_struct_hmac_ctx_st.

Lemma change_compspecs_t_struct_SHA256state_st:
  @data_at spec_sha.CompSpecs Tsh t_struct_SHA256state_st =
  @data_at CompSpecs Tsh t_struct_SHA256state_st.
Proof.
extensionality gfs v.
reflexivity.
Qed.

Hint Rewrite change_compspecs_t_struct_SHA256state_st : norm.
*)
*)