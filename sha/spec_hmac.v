Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

(*when generating hmac091c.v using clightgen, manually hack the generated 
file hmac091c.v by adding

Require Import sha.sha.
Definition t_struct_SHA256state_st := sha.t_struct_SHA256state_st.
Definition _key : ident := 141%positive.

BEFORE the definition of all identifiers, and modifying

Definition _key : ident := 41%positive. into
Definition _key : ident := 141%positive.

to avoid a name clash between _key and sha._K256 *)

Require Import sha.hmac091c.

(*A lttle test to check whether _key and _K256 have indeed been disambiguated*)
Goal _key = 141%positive /\ sha._K256 = 41%positive.
Proof. split; reflexivity. Qed.

Record TREP := mkTrep { t: type; v: reptype t}.
Definition tp_of (T:TREP) : type.
  destruct T. apply t0. 
Defined.
Definition v_of (T:TREP) : reptype (tp_of T).
  destruct T. apply v0. 
Defined.

Definition memcpy_spec_data_at :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, T:TREP
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh); 0 <= sizeof  (tp_of T) <= Int.max_unsigned)
       LOCAL (`(eq p) (eval_id 1%positive); `(eq q) (eval_id 2%positive);
                    `(eq (Vint (Int.repr (sizeof (tp_of T))))) (eval_id 3%positive))
       SEP (`(data_at (fst sh)  (tp_of T) (v_of T) q);
              `(memory_block (snd sh) (Int.repr (sizeof  (tp_of T))) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(data_at (snd sh) (tp_of T) (v_of T) p) *`(data_at (fst sh) (tp_of T) (v_of T) q)).

Inductive hmacabs :=  (* HMAC abstract state *)
 HMACabs: forall (ctx iSha oSha: s256abs) (*sha structures for md_ctx, i_ctx, o_ctx*)
                 (keylen: Z) 
                 (key: list Z), 
                 hmacabs.

Definition absCtxt (h:hmacabs): s256abs :=
  match h with HMACabs ctx _ _ _ _ => ctx end.

Definition innerShaInit (k: list byte) (s:s256abs):Prop :=
  update_abs (HMAC_FUN.mkArgZ k Ipad) init_s256abs s.
Definition outerShaInit (k: list byte) (s:s256abs):Prop :=
  update_abs (HMAC_FUN.mkArgZ k Opad) init_s256abs s.

Definition hmacInit (k:list Z) (h:hmacabs):Prop :=  
  let key := HMAC_FUN.mkKey k in
  let keyB := map Byte.repr key in
  exists iS oS, innerShaInit keyB iS /\ outerShaInit keyB oS /\
  h = HMACabs iS iS oS (if zlt 64 (Zlength k) then 32 else Zlength k) k.

Definition hmacUpdate (data: list Z) (h1 h2:hmacabs):Prop :=
  match h1 with
    HMACabs ctx1 iS oS klen k
  => exists ctx2, update_abs data ctx1 ctx2
     /\ h2 = HMACabs ctx2 iS oS klen k
  end.

Definition hmacFinalSimple h (digest: list Z) :=
  match h with
    HMACabs ctx iS oS klen k
  => exists oS1, 
       update_abs (sha_finish ctx) oS oS1 /\
       sha_finish oS1 = digest
  end.
(*copying oS to ctx is not modelled here*)

Definition hmacFinal h (digest: list Z) h2 :=
  match h with
    HMACabs ctx iS oS klen k
  => let buf := sha_finish ctx in
     exists oS1, update_abs buf oS oS1 /\
       h2 = HMACabs oS1 iS oS klen k /\
       sha_finish oS1 = digest
  end.
(*copying oS to ctx is modelled here by h2, but it's slightly out of order:
  it "follows" the update buf oS oS1 in order to capture the fact that
   oCtx position is not overwritten.
  Also, the effect of the final sha_final is not captured.*)

(*hmac cleanup not modelled*)

Definition hmacSimple (k:list Z) (data:list Z) (dl:Z) (dig:list Z) :=
  exists hInit hUpd,
  hmacInit k hInit /\
  hmacUpdate data hInit hUpd /\
  hmacFinalSimple hUpd dig.

Lemma hmacSimple_sound k data dl dig: 
      hmacSimple k data dl dig ->
      dig = HMAC_FUN.HMAC data k.
Proof.
 unfold hmacSimple; intros [hInit [hUpd [HH1 [HH2 HH3]]]].
 unfold hmacInit in HH1. destruct HH1 as [iInit [oInit [HiInit [HoInit HINIT]]]]. subst.
 unfold innerShaInit in HiInit. inversion HiInit; clear HiInit.
   rewrite Zlength_correct in *; simpl in *. subst.
 unfold outerShaInit in HoInit. inversion HoInit; clear HoInit.
   rewrite Zlength_correct in *; simpl in *. subst.
 unfold HMAC_FUN.mkArgZ in *.
 destruct HH2 as [ctx2 [Hupd HU]]. subst.
 inversion Hupd; clear Hupd. subst.
 unfold hmacFinalSimple in HH3. destruct HH3 as [oS [Upd FINISH]]. subst.
 inversion Upd; clear Upd. subst.
 unfold HMAC_FUN.HMAC, HMAC_FUN.OUTER, HMAC_FUN.INNER.
 unfold sha_finish. rewrite functional_prog.SHA_256'_eq. f_equal.
 unfold HMAC_FUN.innerArg, HMAC_FUN.mkArgZ. rewrite H7. clear H7. 
 unfold HMAC_FUN.outerArg, HMAC_FUN.mkArgZ. rewrite H12. clear H12.
 unfold sha_finish in *. rewrite intlist_to_Zlist_app in *.
rewrite <- app_assoc. rewrite <- H22; clear H22. 
repeat rewrite <- app_assoc. rewrite H17. reflexivity. 
Qed.

Definition hmac (k:list Z) (data:list Z) (dl:Z) (dig:list Z) h :=
  exists hInit hUpd,
  hmacInit k hInit /\
  hmacUpdate data hInit hUpd /\
  hmacFinal hUpd dig h.

Definition hmacFinal_hmacFinalSimple h digest:
  hmacFinalSimple h digest = exists h', hmacFinal h digest h'.
Proof. destruct h. simpl. apply prop_ext.
  split; intros. 
    destruct H as [oS1 [UPD FIN]].
    eexists; exists oS1; eauto.
  destruct H as [h' [oS1 [UPD [H' FIN]]]].
    exists oS1; eauto.
Qed.

Lemma hmac_hmacSimple (k:list Z) (data:list Z) (dl:Z) (dig:list Z) :
  hmacSimple k data dl dig = exists h, hmac k data dl dig h .
Proof. intros. unfold hmacSimple, hmac.
  apply prop_ext. split; intros.
    destruct H as [hInit [hUpd [HInit [HUpd HFinalSimple]]]].
    rewrite hmacFinal_hmacFinalSimple in HFinalSimple.
    destruct HFinalSimple as [h' H'].
    exists h', hInit, hUpd; auto.
  destruct H as [h' [hInit [hUpd [HInit [HUpd HFinal]]]]].
    exists hInit, hUpd. split; trivial. split; trivial.
    rewrite hmacFinal_hmacFinalSimple. exists h'; trivial.
Qed.

Lemma hmac_sound k data dl dig h: 
      hmac k data dl dig h ->
      dig = HMAC_FUN.HMAC data k.
Proof.
 intros.
 eapply hmacSimple_sound.
 rewrite hmac_hmacSimple. exists h; eassumption. 
Qed.

Definition hmacstate: Type := 
  (s256state * (s256state * (s256state * (val * list val))))%type.

Definition mdCtx (h: hmacstate): s256state.
Proof. 
  destruct h as [MDCTX _]. apply MDCTX. 
Defined.

Definition iCtx (h: hmacstate): s256state.
destruct h as [_ [ICTX _]]. apply ICTX.
Defined.

Definition oCtx (h: hmacstate): s256state.
destruct h as [_ [_ [OCTX _]]]. apply OCTX. 
Defined.

Definition Keylen (h: hmacstate): val.
destruct h as [_ [_ [_ [KL _]]]]. apply KL.
Defined.

Definition Key (h: hmacstate): list val.
destruct h as [_ [_ [_ [_ K]]]]. apply K.
Defined.

Definition hmac_relate (h: hmacabs) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS klen k =>
    s256_relate ctx (mdCtx r) /\
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512 /\ 
    Key r = map Vint (map Int.repr (HMAC_FUN.mkKey k)) /\ 
    exists i, Keylen r = Vint i /\ klen=Int.unsigned i /\ 
              (if zlt 64 (Zlength k) then 32 else Zlength k)=klen
  end.

Definition hmacstate_ (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate, 
    !!  hmac_relate h r && data_at Tsh t_struct_hmac_ctx_st r c.

Definition has_lengthK (l:Z) (key:list Z) :=
  l = Zlength key /\ 0 <= l <= Int.max_signed /\
  l * 8 < two_p 64.

Definition HMAC_Init_spec :=
  DECLARE _HMAC_Init
   WITH c : val, k:val, l:Z, key:list Z, KV:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key) 
         LOCAL (`(eq c) (eval_id _ctx);
                `(eq k) (eval_id _key);
                `(eq (Vint (Int.repr l))) (eval_id _len);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(data_at_ Tsh t_struct_hmac_ctx_st c);
             `(data_block Tsh key k); `(K_vector KV))
  POST [ tvoid ] 
           `(EX h:hmacabs, !!hmacInit key  h &&
                             (hmacstate_ h c) * 
                             (data_block Tsh key k) * (K_vector KV)).

Definition has_lengthD (k l:Z) (data:list Z) :=
            l = Zlength data /\ 0 <= l <= Int.max_unsigned /\
            l * 8 + k < two_p 64.

Definition HMAC_Update_spec :=
  DECLARE _HMAC_Update
   WITH h1: hmacabs, c : val, d:val, len:Z, data:list Z, KV:val
   PRE [ (*WAS:_ctx OF tptr t_struct_hmac_ctx_st,
         _data OF tptr tuchar,
         _len OF tint*)
         _ctx OF tptr t_struct_hmac_ctx_st, 
         _data OF tptr tvoid, 
         _len OF tuint]
         PROP (has_lengthD (s256a_len (absCtxt h1)) len data) 
         LOCAL (`(eq c) (eval_id _ctx);
                `(eq d) (eval_id _data);
                `(eq (Vint (Int.repr len))) (eval_id _len);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(K_vector KV);
             `(hmacstate_ h1 c); `(data_block Tsh data d))
  POST [ tvoid ] 
         EX h2:hmacabs, 
          PROP (hmacUpdate data h1 h2) 
          LOCAL ()
          SEP(`(K_vector KV);
              `(hmacstate_ h2 c); `(data_block Tsh data d)).

Definition hmac_relate_simple (h:hmacabs ) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS klen k =>
    (*no clause for ctx*)
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512 /\ 
    Key r = map Vint (map Int.repr (HMAC_FUN.mkKey k)) /\ 
    exists i, Keylen r = Vint i /\ klen=Int.unsigned i /\ 
              (if zlt 64 (Zlength k) then 32 else Zlength k)=klen
  end.

Definition hmacstate_simple (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate, 
    !!  hmac_relate_simple h r && 
    data_at Tsh t_struct_hmac_ctx_st 
       (upd_reptype t_struct_hmac_ctx_st [_md_ctx] r  (default_val t_struct_SHA256state_st)) c.

Definition HMAC_FinalSimple_spec :=
  DECLARE _HMAC_Final
   WITH h1: hmacabs, c : val, md:val, shmd: share, KV:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
         PROP (writable_share shmd) 
         LOCAL (`(eq md) (eval_id _md); 
                `(eq c) (eval_id _ctx);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(hmacstate_ h1 c);
             `(K_vector KV);
             `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX digest: list Z, EX h2:hmacabs,  
          PROP (hmacFinalSimple h1 digest) 
          LOCAL ()
          SEP(`(K_vector KV);
              `(hmacstate_simple h2 c);
              `(data_block shmd digest md)).

Definition HMAC_Final_spec :=
  DECLARE _HMAC_Final
   WITH h1: hmacabs, c : val, md:val, shmd: share, KV:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share shmd) 
         LOCAL (`(eq md) (eval_id _md); 
                `(eq c) (eval_id _ctx);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(hmacstate_ h1 c);
             `(K_vector KV);
             `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX digest:list Z, EX h2:hmacabs, 
          PROP (hmacFinal h1 digest h2) 
          LOCAL ()
          SEP(`(K_vector KV);
              `(hmacstate_ h2 c);
              `(data_block shmd digest md)).

Definition HMAC_Cleanup_spec :=
  DECLARE _HMAC_cleanup
   WITH h: hmacabs, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP () 
         LOCAL (`(eq c) (eval_id _ctx))
         SEP(`(hmacstate_simple h c))
  POST [ tvoid ]  
          PROP (size_compatible t_struct_hmac_ctx_st c /\
                align_compatible t_struct_hmac_ctx_st c) 
          LOCAL ()
          SEP(`(data_block Tsh (Nlist 0 (Z.to_nat(sizeof t_struct_hmac_ctx_st))) c)).

Record DATA := { LEN:Z; CONT: list Z}.

Definition HMAC_Simple_spec :=
  DECLARE _HMAC
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        KV:val, shmd: share, md: val
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd; 
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (`(eq md) (eval_id _md); 
                `(eq keyVal) (eval_id _key);
                `(eq (Vint (Int.repr (LEN KEY)))) (eval_id _key_len);
                `(eq msgVal) (eval_id _d);
                `(eq (Vint (Int.repr (LEN MSG)))) (eval_id _n);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(data_block Tsh (CONT KEY) keyVal);
             `(data_block Tsh (CONT MSG) msgVal);
             `(K_vector KV);
             `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX digest:_, EX c:val,
          PROP (hmacSimple (CONT KEY)
                           (CONT MSG) (LEN MSG)
                           digest)
          LOCAL ()
          SEP(`(K_vector KV);
              `(data_block shmd digest md);
              `(data_block Tsh (CONT KEY) keyVal);
              `(data_block Tsh (CONT MSG) msgVal)).

Definition HMAC_spec :=
  DECLARE _HMAC
   WITH KeyStruct :(val * (Z * list Z))%type, 
        DataStruct:(val * (Z * list Z))%type, 
        KV:val, shmd: share, md: val
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd) 
         LOCAL (`(eq md) (eval_id _md); 
                `(eq (fst KeyStruct)) (eval_id _key);
                `(eq (Vint (Int.repr (fst(snd KeyStruct))))) (eval_id _key_len);
                `(eq (fst DataStruct)) (eval_id _d);
                `(eq (Vint (Int.repr (fst(snd DataStruct))))) (eval_id _n);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(data_block Tsh (snd (snd KeyStruct)) (fst KeyStruct));
             `(data_block Tsh (snd(snd DataStruct)) (fst DataStruct));
             `(K_vector KV);
             `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX digest:_, EX c:val, EX h:hmacabs,
          PROP (hmac (snd (snd KeyStruct)) 
                     (snd (snd DataStruct)) (fst(snd DataStruct))
                     digest h)
          LOCAL ()
          SEP(`(K_vector KV);
              `(data_block shmd digest md);
              `(data_block Tsh (snd (snd KeyStruct)) (fst KeyStruct));
              `(data_block Tsh (snd(snd DataStruct)) (fst DataStruct))).

(*Definition SHA256_spec := (_SHA256, snd spec_sha.SHA256_spec). *)
Definition sha256init_spec := (_SHA256_Init, snd SHA256_Init_spec).
Definition sha256update_spec := (_SHA256_Update, snd SHA256_Update_spec).
Definition sha256final_spec := (_SHA256_Final, snd SHA256_Final_spec).
Definition memset_spec := (_memset, snd spec_sha.memset_spec). 
Definition memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec). 

Definition HmacVarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.

Definition HmacFunSpecs : funspecs := 
  memcpy_spec_data_at(*memcpy_spec*):: memset_spec::
  sha256init_spec::sha256update_spec::sha256final_spec::(*SHA256_spec::*)
  HMAC_Init_spec:: HMAC_Update_spec::HMAC_Cleanup_spec::
  HMAC_FinalSimple_spec (*alternative: HMAC_FinalSimple_spec or HMAC_Final_spec*)::
  HMAC_Simple_spec (*alternative:HMAC_spec*)::nil.

