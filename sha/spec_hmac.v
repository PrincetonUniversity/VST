Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Record TREP := mkTrep { t: type; v: reptype t}.

Definition tp_of (T:TREP) : type.
  destruct T. apply t0.
Defined.

Definition v_of (T:TREP) : reptype (tp_of T).
  destruct T. apply v0.
Defined.

Definition memcpy_spec_data_at :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, T:TREP, n:Z
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh); n= sizeof (tp_of T);
             0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q;
              temp 3%positive (Vint (Int.repr n)))
       SEP (data_at (fst sh) (tp_of T) (v_of T) q;
            memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (data_at (snd sh) (tp_of T) (v_of T) p;
            data_at (fst sh) (tp_of T) (v_of T) q).

(****** Coq-representation of hmac states, and predicates characterizing the incremental functions.

If the corresponding predicates for SHA operations were modeled as functions, the ones here could be, too *)

Inductive hmacabs :=  (* HMAC abstract state *)
 HMACabs: forall (ctx iSha oSha: s256abs) (*sha structures for md_ctx, i_ctx, o_ctx*),
                 hmacabs.

Definition absCtxt (h:hmacabs): s256abs :=
  match h with HMACabs ctx _ _ => ctx end.
(*
Definition innerShaInit (k: list byte) (s:s256abs):Prop :=
  update_abs (HMAC_SHA256.mkArgZ k Ipad) init_s256abs s.
Definition outerShaInit (k: list byte) (s:s256abs):Prop :=
  update_abs (HMAC_SHA256.mkArgZ k Opad) init_s256abs s.
*)
Definition innerShaInit (k: list byte):s256abs :=
   HMAC_SHA256.mkArgZ k Ipad.
Definition outerShaInit (k: list byte):s256abs :=
   HMAC_SHA256.mkArgZ k Opad.

Definition hmacInit (k:list Z):hmacabs :=
  let key := HMAC_SHA256.mkKey k in
  let keyB := map Byte.repr key in
  let iS := innerShaInit keyB in
  let oS := outerShaInit keyB in
  HMACabs iS iS oS.

Definition hmacUpdate (data: list Z) (h1:hmacabs): hmacabs :=
  match h1 with
    HMACabs ctx1 iS oS
  => let ctx2 := ctx1 ++ data in
     HMACabs ctx2 iS oS
  end.

Definition hmacFinalSimple h : list Z :=
  match h with
    HMACabs ctx iS oS
  => let inner := SHA256.SHA_256 ctx in
     SHA256.SHA_256 (oS ++ inner)
  end.

Definition hmacFinal h : (hmacabs * list Z) :=
  match h with
    HMACabs ctx iS oS
  => let inner := SHA256.SHA_256 ctx in
     let outerArg := oS ++ inner in
     (HMACabs outerArg iS oS, SHA256.SHA_256 outerArg)
  end.

(*hmac cleanup not modelled*)

Definition hmacSimple (k:list Z) (data:list Z):list Z:=
  hmacFinalSimple (hmacUpdate data (hmacInit k)).

Definition hmac (k:list Z) (data:list Z):(hmacabs * list Z) :=
  hmacFinal (hmacUpdate data (hmacInit k)).

Lemma hmacSimple_sound k data:
      hmacSimple k data = HMAC256 data k.
Proof.
  unfold hmacSimple, hmacFinalSimple, hmacUpdate, hmacInit.
  unfold HMAC256, HMAC_SHA256.HMAC, HMAC_SHA256.HmacCore.
  unfold HMAC_SHA256.KeyPreparation.
  forget (HMAC_SHA256.mkKey k) as q.
  unfold HMAC_SHA256.OUTER, HMAC_SHA256.INNER, SHA256.Hash.
  rewrite functional_prog.SHA_256'_eq. f_equal.
Qed.

Lemma hmac_sound k data:
      snd(hmac k data) = HMAC256 data k.
Proof.
  rewrite <- (hmacSimple_sound k data).
  unfold hmac, hmacFinal, hmacSimple, hmacFinalSimple.
  destruct (hmacUpdate data (hmacInit k)). trivial.
Qed.

(*Lemma update_abs_nil ctx x: s256_relate ctx x -> update_abs [] ctx ctx.
Proof.
  intros.
  destruct ctx. simpl in H.
  specialize (Update_abs nil hashed nil data data); simpl.
  do 2 rewrite app_nil_r. intros U; apply U; trivial; clear U; intuition.
Qed.

Lemma update_abs_app ctx0 ctx1 ctx2 data data1:
   update_abs data ctx0 ctx1 ->
   update_abs data1 ctx1 ctx2 ->
   update_abs (data ++ data1) ctx0 ctx2.
Proof. intros.
  inv H. inv H0.
  specialize (Update_abs (data ++ data1) hashed (blocks++blocks0) oldfrag newfrag0).
    rewrite  <- app_assoc. intros ZZ; apply ZZ; clear ZZ; trivial.
    rewrite Zlength_app. apply Z.divide_add_r; assumption.
    rewrite app_assoc. rewrite H5; clear H5. rewrite <- app_assoc.
    rewrite H13; clear H13. rewrite intlist_to_Zlist_app. rewrite app_assoc; trivial.
Qed.

Lemma hmacUpdate_app h0 h1 h2 data data1:
      hmacUpdate data h0 h1 ->
      hmacUpdate data1 h1 h2 ->
      hmacUpdate (data ++ data1) h0 h2.
Proof.
  intros.
  destruct h0; simpl in *. destruct H as [? [UPD ?]]. subst h1.
  destruct H0 as [? [? ?]]. subst h2. exists x0; split; trivial.
  eapply update_abs_app; eassumption.
Qed.
*)

Lemma hmacUpdate_nil h: hmacUpdate [] h = h.
Proof. destruct h. simpl. rewrite app_nil_r. trivial. Qed.

Lemma hmacUpdate_app data data' h:
      hmacUpdate data (hmacUpdate data' h) = hmacUpdate (data'++data) h.
Proof. destruct h; simpl. rewrite app_assoc; trivial. Qed.

(************Coq counterpart of HMAC_CTX, but for CompCert values (val etc)*********************)
Definition hmacstate: Type :=
  (s256state * (s256state * s256state))%type.

Definition mdCtx (h: hmacstate): s256state.
Proof.
  destruct h as [MDCTX _]. apply MDCTX.
Defined.

Definition iCtx (h: hmacstate): s256state.
destruct h as [_ [ICTX _]]. apply ICTX.
Defined.

Definition oCtx (h: hmacstate): s256state.
destruct h as [_ [_ OCTX]]. apply OCTX.
Defined.

(***************** The next two definitions link abstract states (hmacabs) with Coq
 representations of HMAC_CTX values (hmacstate), and lift
 the relationship to a separation logic predicates*)
Definition hmac_relate (h: hmacabs) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS =>
    s256_relate ctx (mdCtx r) /\
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512
  end.

Definition t_struct_hmac_ctx_st := Tstruct _hmac_ctx_st noattr.

Definition hmacstate_ (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate,
    !!  hmac_relate h r && data_at Tsh t_struct_hmac_ctx_st r c.

(************************ Specification of HMAC_init ********************************************)

Definition has_lengthK (l:Z) (key:list Z) :=
  l = Zlength key /\ 0 < l <= Int.max_signed /\ (*requirement 0<l new in new_compcert - previously, it was 0<=l*)
  l * 8 < two_p 64.

Definition hmac_relate_PreInitNull (key:list Z) (h:hmacabs ) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS =>
    (*no clause for ctx*)
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512 /\
    let keyB := map Byte.repr (HMAC_SHA256.mkKey key) in
    innerShaInit keyB = iS /\ outerShaInit keyB = oS
  end.

Definition hmacstate_PreInitNull key (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate, EX v:_,
    !!hmac_relate_PreInitNull key h r &&
    data_at Tsh t_struct_hmac_ctx_st
       (upd_reptype t_struct_hmac_ctx_st [StructField _md_ctx] r v) c.

Definition initPre (c:val) (k: val) h l key : mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then hmacstate_PreInitNull key h c
              else FF
  | Vptr b ofs => !!has_lengthK l key &&
                  (data_at_ Tsh t_struct_hmac_ctx_st c *
                        (data_block Tsh key (Vptr b ofs)))
  | _ => FF
  end.

Definition initPostKey k key:mpred :=
  match k with
    Vint z => !!(z=Int.zero) && emp
  | Vptr b ofs => data_block Tsh key k
  | _ => FF
  end.

Definition HMAC_Init_spec :=
  DECLARE _HMAC_Init
   WITH c : val, k:val, l:Z, key:list Z, kv:val, h1:hmacabs
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP ((*has_lengthK l key*))
         LOCAL (temp _ctx c; temp _key k; temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (K_vector kv; initPre c k h1 l key)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (hmacstate_ (hmacInit key) c; initPostKey k key; K_vector kv).

(************************ Specification of HMAC_update *******************************************************)

Definition has_lengthD (k l:Z) (data:list Z) :=
            l = Zlength data /\ 0 <= l <= Int.max_unsigned /\
            l * 8 + k < two_p 64.

Definition HMAC_Update_spec :=
  DECLARE _HMAC_Update
   WITH h1: hmacabs, c : val, d:val, len:Z, data:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _data OF tptr tvoid,
         _len OF tuint]
         PROP (has_lengthD (s256a_len (absCtxt h1)) len data)
         LOCAL (temp _ctx c; temp _data d; temp  _len (Vint (Int.repr len));
                gvar sha._K256 kv)
         SEP(K_vector kv; hmacstate_ h1 c; data_block Tsh data d)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(K_vector kv; hmacstate_ (hmacUpdate data h1) c; data_block Tsh data d).
(*
Lemma hmacUpdate_nil h x: hmac_relate h x -> hmacUpdate [] h h.
Proof.
 intros.
 destruct h. simpl. exists ctx; split; trivial.
 simpl in H.
 eapply update_abs_nil. apply H.
Qed.
*)
(************************ Specification of HMAC_final *******************************************************)

Definition hmac_relate_PostFinal (h:hmacabs ) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS =>
    (*no clause for ctx*)
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512
  end.

Definition hmacstate_PostFinal (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate,
    !!  hmac_relate_PostFinal h r &&
    data_at Tsh t_struct_hmac_ctx_st
       (upd_reptype t_struct_hmac_ctx_st [StructField _md_ctx] r  (default_val t_struct_SHA256state_st)) c.

Definition HMAC_Final_spec :=
  DECLARE _HMAC_Final
   WITH h1: hmacabs, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share shmd)
       LOCAL (temp _md md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(hmacstate_ h1 c; K_vector kv; memory_block shmd 32 md)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(K_vector kv; hmacstate_PostFinal (fst (hmacFinal h1)) c;
              data_block shmd (snd (hmacFinal h1)) md).

Lemma hmacstate_PostFinal_PreInitNull key data dig h2 v:
      forall (Round1Final : hmacFinal (hmacUpdate data (hmacInit key)) = (h2,dig)),
      hmacstate_PostFinal h2 v
  |-- hmacstate_PreInitNull key h2 v.
Proof. intros.
  unfold hmacstate_PostFinal, hmac_relate_PostFinal, hmacstate_PreInitNull; normalize.
  Exists r.
  Exists (default_val t_struct_SHA256state_st).
  apply andp_right. 2: apply derives_refl.
  apply prop_right.
    destruct h2. red. unfold hmacFinal in Round1Final.
    remember (hmacUpdate data (hmacInit key)) as h.
    destruct h. inv Round1Final.
    simpl in Heqh. inv Heqh. intuition.
Qed.

(************************ Specifications of HMAC_cleanup *******************************************************)

Definition HMAC_Cleanup_spec :=
  DECLARE _HMAC_cleanup
   WITH h: hmacabs, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP ()
         LOCAL (temp _ctx c)
         SEP(hmacstate_PostFinal h c)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(data_block Tsh (list_repeat (Z.to_nat(sizeof t_struct_hmac_ctx_st)) 0) c).

Definition HMAC_Cleanup_spec1 :=
  DECLARE _HMAC_cleanup
   WITH h: hmacabs, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP ()
         LOCAL (temp _ctx c)
         SEP(EX key:_, hmacstate_PreInitNull key h c)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(data_block Tsh (list_repeat (Z.to_nat(sizeof t_struct_hmac_ctx_st)) 0) c).


(************************ Specification of oneshot HMAC *******************************************************)

Record DATA := { LEN:Z; CONT: list Z}.

Definition HMAC_spec :=
  DECLARE _HMAC
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        kv:val, shmd: share, md: val
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd;
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key keyVal;
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msgVal;
                temp _n (Vint (Int.repr (LEN MSG)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (CONT KEY) keyVal;
             data_block Tsh (CONT MSG) msgVal;
             K_vector kv;
             memory_block shmd 32 md)
  POST [ tptr tuchar ] EX digest:_,
          PROP (digest= HMAC256 (CONT MSG) (CONT KEY))
          LOCAL (temp ret_temp md)
          SEP(K_vector kv;
              data_block shmd digest md;
              initPostKey keyVal (CONT KEY);
              data_block Tsh (CONT MSG) msgVal).

(*A stronger spec of oneshot hmac that includes the cryptographic assertion in the postcondition
  is given in the verif_hmac_crpyto.v. This avoids having to Import FCF, hmacfc, and the
  proof of equivalence between HMAC_functional_prog and the functional spec of the
  cryptographic program in the present file.*)

(*Furthermore, verif_hmac_double.v contains the verification of an additional function
  an additional function, hmac2, that we added to the c file in order to exercise the reuse of
  a key for several messages. We call hmac twice, (on the same message, using the same key)
  and put the resulting (identical) digests side by side in a suitably large array*)

(***************** We combine all specifications to a specification context *******)

(*Definition SHA256_spec := (_SHA256, snd spec_sha.SHA256_spec). *)
Definition sha256init_spec := (_SHA256_Init, snd SHA256_Init_spec).
Definition sha256update_spec := (_SHA256_Update, snd SHA256_Update_spec).
Definition sha256final_spec := (_SHA256_Final, snd SHA256_Final_spec).
Definition memset_spec := (_memset, snd spec_sha.memset_spec).
Definition memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec).

Definition HmacVarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.

Definition HmacFunSpecs : funspecs :=
  memcpy_spec_data_at:: memset_spec::
  sha256init_spec::sha256update_spec::sha256final_spec::(*SHA256_spec::*)
  HMAC_Init_spec:: HMAC_Update_spec::HMAC_Cleanup_spec::
  HMAC_Final_spec:: HMAC_spec ::nil.

Definition HMS : hmacstate := default_val t_struct_hmac_ctx_st.

Lemma change_compspecs_t_struct_SHA256state_st:
  @data_at spec_sha.CompSpecs Tsh t_struct_SHA256state_st =
  @data_at CompSpecs Tsh t_struct_SHA256state_st.
Proof.
extensionality gfs v.
reflexivity.
Qed.

Hint Rewrite change_compspecs_t_struct_SHA256state_st : norm.

