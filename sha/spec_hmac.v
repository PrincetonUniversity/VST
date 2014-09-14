Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac091c.

Lemma isbyte_sha x: Forall isbyteZ (functional_prog.SHA_256' x).
Proof. apply isbyte_intlist_to_Zlist. Qed.

Inductive hmacabs :=  (* SHA-256 abstract state *)
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

Definition hmacInit (k:list Z) (kl:Z) (h:hmacabs):Prop :=  
  let key := HMAC_FUN.mkKey k in
  let keyB := map Byte.repr key in
  exists iS oS, innerShaInit keyB iS /\ outerShaInit keyB oS /\
  h = HMACabs iS iS oS 64 key /\ kl=Zlength k.

Definition hmacUpdate (data: list Z) (len:Z) (h1 h2:hmacabs):Prop :=
  match h1 with
    HMACabs ctx1 iS oS klen k
  => exists ctx2, update_abs data ctx1 ctx2
     /\ h2 = HMACabs ctx2 iS oS klen k /\ len=Zlength data
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

(*hmac cleanup not modelled for the time being*)

Definition hmacSimple (k:list Z) (kl:Z) (data:list Z) (dl:Z) (dig:list Z) :=
  exists hInit hUpd,
  hmacInit k kl hInit /\
  hmacUpdate data dl hInit hUpd /\
  hmacFinalSimple hUpd dig.

Lemma hmacSimple_sound k kl data dl dig: 
      hmacSimple k kl data dl dig ->
      dig = HMAC_FUN.HMAC data k.
Proof.
 unfold hmacSimple; intros [hInit [hUpd [HH1 [HH2 HH3]]]].
 unfold hmacInit in HH1. destruct HH1 as [iInit [oInit [HiInit [HoInit [HINIT KL]]]]]. subst.
 unfold innerShaInit in HiInit. inversion HiInit; clear HiInit.
   rewrite Zlength_correct in *; simpl in *. subst.
 unfold outerShaInit in HoInit. inversion HoInit; clear HoInit.
   rewrite Zlength_correct in *; simpl in *. subst.
 unfold HMAC_FUN.mkArgZ in *.
 destruct HH2 as [ctx2 [Hupd [HU DF]]]. subst.
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

Definition hmac (k:list Z) (kl:Z) (data:list Z) (dl:Z) (dig:list Z) h :=
  exists hInit hUpd,
  hmacInit k kl hInit /\
  hmacUpdate data dl hInit hUpd /\
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

Lemma hmac_hmacSimple (k:list Z) (kl:Z) (data:list Z) (dl:Z) (dig:list Z) :
  hmacSimple k kl data dl dig = exists h, hmac k kl data dl dig h .
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

Lemma hmac_sound k kl data dl dig h: 
      hmac k kl data dl dig h ->
      dig = HMAC_FUN.HMAC data k.
Proof.
 intros.
 eapply hmacSimple_sound.
 rewrite hmac_hmacSimple. exists h; eassumption. 
Qed.

Definition hmacstate: Type := (reptype t_struct_hmac_ctx_st).

Definition mdCtx (h: hmacstate): s256state.
Proof. 
  destruct h as [MDCTX _]. simpl in *.   
  destruct MDCTX as [h_ [Nl_ [Nh_ [data_ [num_ _]]]]].
  apply (h_ ,(Nl_ ,(Nh_ ,(data_, num_)))).
Defined.

Definition iCtx (h: hmacstate): s256state.
destruct h as [_ [ICTX _]]. simpl in *. 
  destruct ICTX as [h_ [Nl_ [Nh_ [data_ [num_ _]]]]].
  apply (h_ ,(Nl_ ,(Nh_ ,(data_, num_)))).
Defined.

Definition oCtx (h: hmacstate): s256state.
destruct h as [_ [_ [OCTX _]]]. simpl in *. 
  destruct OCTX as [h_ [Nl_ [Nh_ [data_ [num_ _]]]]].
  apply (h_ ,(Nl_ ,(Nh_ ,(data_, num_)))).
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
    Key r = map Vint (map Int.repr k) /\ 
    exists i, Keylen r = Vint i /\ klen=Int.unsigned i /\ 
              Zlength k=klen (*maybe also require klen=64?*)
  end.

Definition hmacstate_ (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate, 
    !!  hmac_relate h r && data_at Tsh t_struct_hmac_ctx_st r c.

Definition has_lengthK (l:Z) (key:list Z) :=
  l = Zlength key /\ 0 <= l <= Int.max_signed /\
  l * 8 < two_p 64.

Definition HMAC_Init_spec :=
  DECLARE _HMAC_Init
   WITH c : val, k:val, l:Z, key:list Z
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key) 
         LOCAL (`(eq c) (eval_id _ctx);
                `(eq k) (eval_id _key);
                `(eq (Vint (Int.repr l))) (eval_id _len))
         SEP(`(data_at_ Tsh t_struct_hmac_ctx_st c);
             `(data_block Tsh key k))
  POST [ tvoid ] 
           `(EX h:hmacabs, !!hmacInit key (Zlength key) h &&
                             (hmacstate_ h c) * (data_block Tsh key k)).


Definition has_lengthD (l:Z) (data:list Z) :=
            l = Zlength data /\ 0 <= l <= Int.max_signed /\
            l * 8 + 64 < two_p 64.

Definition HMAC_Update_spec :=
  DECLARE _HMAC_Update
   WITH h1: hmacabs, c : val, d:val, len:Z, data:list Z, KV:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _data OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthD len data) 
         LOCAL (`(eq c) (eval_id _ctx);
                `(eq d) (eval_id _data);
                `(eq (Vint (Int.repr len))) (eval_id _len);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(K_vector KV);
             `(hmacstate_ h1 c); `(data_block Tsh data d))
  POST [ tvoid ] 
         EX h2:hmacabs, 
          PROP (hmacUpdate (firstn (Z.to_nat len) data) len h1 h2) 
          LOCAL ()
          SEP(`(K_vector KV);
              `(hmacstate_ h2 c); `(data_block Tsh data d)).

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
              `(hmacstate_ h2 c);
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
         SEP(`(hmacstate_ h c))
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(`(data_block Tsh (Nlist 0 (Z.to_nat(sizeof t_struct_hmac_ctx_st))) c)).

Definition HMAC_Simple_spec :=
  DECLARE _HMAC
   WITH KeyStruct :(val * (Z * list Z))%type, 
        DataStruct:(val * (Z * list Z))%type, 
        KV:val, shmd: share, md: val
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd; 
               has_lengthK (fst(snd KeyStruct)) (snd (snd KeyStruct));
               has_lengthD (fst(snd DataStruct)) (snd (snd DataStruct)))
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
         EX digest:_, EX c:val,
          PROP (hmacSimple (snd (snd KeyStruct)) (fst(snd KeyStruct))
                           (snd (snd DataStruct)) (fst(snd DataStruct))
                           digest)
          LOCAL ()
          SEP(`(K_vector KV);
              `(data_block shmd digest md);
              `(data_block Tsh (snd (snd KeyStruct)) (fst KeyStruct));
              `(data_block Tsh (snd(snd DataStruct)) (fst DataStruct))).

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
          PROP (hmac (snd (snd KeyStruct)) (fst(snd KeyStruct))
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


Definition Vprog : varspecs := (*(_K256, tarray tuint 64)::*) nil.

Definition Gprog : funspecs := 
  memcpy_spec:: memset_spec::
  sha256init_spec::sha256update_spec::sha256final_spec::(*SHA256_spec::*)
  HMAC_Init_spec:: HMAC_Update_spec::HMAC_Cleanup_spec::
  HMAC_FinalSimple_spec (*alternative: HMAC_Final_spec*)::
  HMAC_Simple_spec (*alternative:HMAC_spec*)::nil.

Fixpoint do_builtins (n: nat) (defs : list (ident * globdef fundef type)) : funspecs :=
 match n, defs with
  | S n', (id, Gfun (External (EF_builtin _ sig) argtys resty cc_default))::defs' => 
     (id, mk_funspec (iota_formals 1%positive argtys, resty) unit FF FF) 
      :: do_builtins n' defs'
  | _, _ => nil
 end.

(*Definition Gtot := do_builtins 3 (prog_defs prog) ++ Gprog.*)
Definition Gtot := Gprog.