Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac.
Require Import VST.veric.change_compspecs.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Instance CompSpecs_Preserve: change_composite_env spec_sha.CompSpecs CompSpecs.
  make_cs_preserve spec_sha.CompSpecs CompSpecs.
Defined.
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
   WITH rsh : share, wsh: share, p: val, q: val, T:TREP, n:Z
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share rsh; writable_share wsh;
                 n= sizeof (tp_of T); 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q;
              temp 3%positive (Vint (Int.repr n)))
       SEP (data_at rsh (tp_of T) (v_of T) q;
            memory_block wsh n p)
    POST [ tptr tvoid ]
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (data_at wsh (tp_of T) (v_of T) p;
            data_at rsh (tp_of T) (v_of T) q).

(****** Coq-representation of hmac states, and predicates characterizing the incremental functions.

If the corresponding predicates for SHA operations were modeled as functions, the ones here could be, too *)

Inductive hmacabs :=  (* HMAC abstract state *)
 HMACabs: forall (ctx iSha oSha: s256abs) (*sha structures for md_ctx, i_ctx, o_ctx*),
                 hmacabs.

Definition absCtxt (h:hmacabs): s256abs :=
  match h with HMACabs ctx _ _ => ctx end.

Definition innerShaInit (k: list byte):s256abs :=
   HMAC_SHA256.mkArg k Ipad.
Definition outerShaInit (k: list byte):s256abs :=
   HMAC_SHA256.mkArg k Opad.

Definition hmacInit (k:list byte):hmacabs :=
  let key := HMAC_SHA256.mkKey k in
  let iS := innerShaInit key in
  let oS := outerShaInit key in
  HMACabs iS iS oS.

Definition hmacUpdate (data: list byte) (h1:hmacabs): hmacabs :=
  match h1 with
    HMACabs ctx1 iS oS
  => let ctx2 := ctx1 ++ data in
     HMACabs ctx2 iS oS
  end.

Definition hmacFinalSimple h : list byte :=
  match h with
    HMACabs ctx iS oS
  => let inner := SHA256.SHA_256 ctx in
     SHA256.SHA_256 (oS ++ inner)
  end.

Definition hmacFinal h : (hmacabs * list byte) :=
  match h with
    HMACabs ctx iS oS
  => let inner := SHA256.SHA_256 ctx in
     let outerArg := oS ++ inner in
     (HMACabs outerArg iS oS, SHA256.SHA_256 outerArg)
  end.

(*hmac cleanup not modelled*)

Definition hmacSimple (k:list byte) (data:list byte):list byte:=
  hmacFinalSimple (hmacUpdate data (hmacInit k)).

Definition hmac (k:list byte) (data:list byte):(hmacabs * list byte) :=
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

Definition hmacstate_ (wsh: share) (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate,
    !!  hmac_relate h r && data_at wsh t_struct_hmac_ctx_st r c.

(************************ Specification of HMAC_init ********************************************)

Definition has_lengthK (l:Z) (key:list byte) :=
  l = Zlength key /\ 0 < l <= Int.max_signed. (*requirement 0<l new in new_compcert - previously, it was 0<=l*)

Definition hmac_relate_PreInitNull (key:list byte) (h:hmacabs ) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS =>
    (*no clause for ctx*)
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512 /\
    let keyB := HMAC_SHA256.mkKey key in
    innerShaInit keyB = iS /\ outerShaInit keyB = oS
  end.

Definition hmacstate_PreInitNull (wsh: share) key (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate, EX v:_,
    !!hmac_relate_PreInitNull key h r &&
    data_at wsh t_struct_hmac_ctx_st
       (upd_reptype t_struct_hmac_ctx_st [StructField _md_ctx] r v) c.

Definition initPre (wsh sh: share) (c:val) (k: val) h l key : mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then hmacstate_PreInitNull wsh key h c
              else FF
  | Vptr b ofs => !!has_lengthK l key &&
                  (data_at_ wsh t_struct_hmac_ctx_st c *
                        (data_block sh key (Vptr b ofs)))
  | _ => FF
  end.

Definition initPostKey (sh: share) k key:mpred :=
  match k with
    Vint z => !!(z=Int.zero) && emp
  | Vptr b ofs => data_block sh key k
  | _ => FF
  end.

Definition HMAC_Init_spec :=
  DECLARE _HMAC_Init
   WITH wsh: share, sh: share, c : val, k:val, l:Z, key:list byte, h1:hmacabs, gv:globals
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (writable_share wsh; readable_share sh (*has_lengthK l key*))
         LOCAL (temp _ctx c; temp _key k; temp _len (Vint (Int.repr l));
                gvars gv)
         SEP (K_vector gv; initPre wsh sh c k h1 l key)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (hmacstate_ wsh (hmacInit key) c; initPostKey sh k key; K_vector gv).

(************************ Specification of HMAC_update *******************************************************)

Definition has_lengthD (k l:Z) (data:list byte) :=
            l = Zlength data /\ 0 <= l <= Int.max_unsigned /\
            l * 8 + k < two_p 64.

Definition HMAC_Update_spec :=
  DECLARE _HMAC_Update
   WITH wsh:share, sh:share, h1: hmacabs, c : val, d:val, len:Z, data:list byte, gv: globals
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _data OF tptr tvoid,
         _len OF tuint]
         PROP (writable_share wsh; readable_share sh;
                   has_lengthD (s256a_len (absCtxt h1)) len data)
         LOCAL (temp _ctx c; temp _data d; temp  _len (Vint (Int.repr len));
                gvars gv)
         SEP(K_vector gv; hmacstate_ wsh h1 c; data_block sh data d)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(K_vector gv; hmacstate_ wsh (hmacUpdate data h1) c; data_block sh data d).

(************************ Specification of HMAC_final *******************************************************)

Definition hmac_relate_PostFinal (h:hmacabs ) (r: hmacstate) : Prop :=
  match h with HMACabs ctx iS oS =>
    (*no clause for ctx*)
    s256_relate iS (iCtx r) /\
    s256_relate oS (oCtx r) /\
    s256a_len iS = 512 /\ s256a_len oS = 512
  end.

Definition hmacstate_PostFinal (wsh: share) (h: hmacabs) (c: val) : mpred :=
   EX r:hmacstate,
    !!  hmac_relate_PostFinal h r &&
    data_at wsh t_struct_hmac_ctx_st
       (upd_reptype t_struct_hmac_ctx_st [StructField _md_ctx] r  (default_val t_struct_SHA256state_st)) c.

Definition HMAC_Final_spec :=
  DECLARE _HMAC_Final
   WITH wsh: share, h1: hmacabs, c : val, md:val, shmd: share, gv: globals
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share wsh; writable_share shmd)
       LOCAL (temp _md md; temp _ctx c;
              gvars gv)
       SEP(hmacstate_ wsh h1 c; K_vector gv; memory_block shmd 32 md)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(K_vector gv; hmacstate_PostFinal wsh (fst (hmacFinal h1)) c;
              data_block shmd (snd (hmacFinal h1)) md).

Lemma hmacstate_PostFinal_PreInitNull wsh key data dig h2 v:
      forall (Round1Final : hmacFinal (hmacUpdate data (hmacInit key)) = (h2,dig)),
      hmacstate_PostFinal wsh h2 v
  |-- hmacstate_PreInitNull wsh key h2 v.
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
   WITH wsh: share, h: hmacabs, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP (writable_share wsh)
         LOCAL (temp _ctx c)
         SEP(hmacstate_PostFinal wsh h c)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(data_block wsh (list_repeat (Z.to_nat(sizeof t_struct_hmac_ctx_st)) Byte.zero) c).

Definition HMAC_Cleanup_spec1 :=
  DECLARE _HMAC_cleanup
   WITH wsh: share, h: hmacabs, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP (writable_share wsh)
         LOCAL (temp _ctx c)
         SEP(EX key:_, hmacstate_PreInitNull wsh key h c)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(data_block wsh (list_repeat (Z.to_nat(sizeof t_struct_hmac_ctx_st)) Byte.zero) c).


(************************ Specification of oneshot HMAC *******************************************************)

Record DATA := { LEN:Z; CONT: list byte}.

Definition HMAC_spec :=
  DECLARE _HMAC
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        shk: share, shm: share, shmd: share, md: val, gv: globals
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (readable_share shk; readable_share shm; writable_share shmd;
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key keyVal;
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msgVal;
                temp _n (Vint (Int.repr (LEN MSG)));
                gvars gv)
         SEP(data_block shk (CONT KEY) keyVal;
             data_block shm (CONT MSG) msgVal;
             K_vector gv;
             memory_block shmd 32 md)
  POST [ tptr tuchar ] EX digest:_,
          PROP (digest= HMAC256 (CONT MSG) (CONT KEY))
          LOCAL (temp ret_temp md)
          SEP(K_vector gv;
              data_block shmd digest md;
              initPostKey shk keyVal (CONT KEY);
              data_block shm (CONT MSG) msgVal).

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

Definition HmacVarSpecs : varspecs := 
  [(_m, tarray tuchar 32); (_m__1, tarray tuchar 64); (sha._K256, tarray tuint 64)].

Definition HmacFunSpecs : funspecs :=
  memcpy_spec_data_at:: memset_spec::
  sha256init_spec::sha256update_spec::sha256final_spec::(*SHA256_spec::*)
  HMAC_Init_spec:: HMAC_Update_spec::HMAC_Cleanup_spec::
  HMAC_Final_spec:: HMAC_spec ::nil.

Definition HMS : hmacstate := default_val t_struct_hmac_ctx_st.

Lemma change_compspecs_data_block: forall sh v,
  @data_block spec_sha.CompSpecs sh v =
  @data_block CompSpecs sh v.
Proof.
  intros.
  unfold data_block.
  apply data_at_change_composite; auto.
Qed.

Ltac change_compspecs' cs cs' ::=
  match goal with
  | |- context [@data_block cs'] => rewrite change_compspecs_data_block
  | |- context [@data_at cs' ?sh ?t ?v1] => erewrite (@data_at_change_composite cs' cs _ sh t); [| apply JMeq_refl | reflexivity]
  | |- context [@field_at cs' ?sh ?t ?gfs ?v1] => erewrite (@field_at_change_composite cs' cs _ sh t gfs); [| apply JMeq_refl | reflexivity]
  | |- context [@data_at_ cs' ?sh ?t] => erewrite (@data_at__change_composite cs' cs _ sh t); [| reflexivity]
  | |- context [@field_at_ cs' ?sh ?t ?gfs] => erewrite (@field_at__change_composite cs' cs _ sh t gfs); [| reflexivity]
  | |- context [?A cs'] => change (A cs') with (A cs)
  | |- context [?A cs' ?B] => change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => change (A cs' B C D E F) with (A cs B C D E F)
 end.

(* TODO: maybe this lemma is not needed any more. *)
Lemma change_compspecs_t_struct_SHA256state_st:
  @data_at spec_sha.CompSpecs Ews t_struct_SHA256state_st =
  @data_at CompSpecs Ews t_struct_SHA256state_st.
Proof.
  extensionality gfs v.
  (* TODO: simplify this proof. *)
  unfold data_at, field_at.
  f_equal.
  unfold field_compatible.
  apply ND_prop_ext.
  assert (@align_compatible spec_sha.CompSpecs t_struct_SHA256state_st v <-> @align_compatible CompSpecs t_struct_SHA256state_st v); [| tauto].
  destruct v; unfold align_compatible; try tauto.
  split; intros.
  + eapply align_compatible_rec_Tstruct; [reflexivity | simpl co_members].
    intros.
    eapply align_compatible_rec_Tstruct_inv in H; [| reflexivity | eassumption | eassumption].
    simpl in H0.
    if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | inv H0]]]]].
    - clear - H.
      apply align_compatible_rec_Tarray; intros.
      eapply align_compatible_rec_Tarray_inv in H; [| eassumption].
      eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - clear - H.
      apply align_compatible_rec_Tarray; intros.
      eapply align_compatible_rec_Tarray_inv in H; [| eassumption].
      eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
  + eapply align_compatible_rec_Tstruct; [reflexivity | simpl co_members].
    intros.
    eapply align_compatible_rec_Tstruct_inv in H; [| reflexivity | eassumption | eassumption].
    simpl in H0.
    if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | if_tac in H0; [inv H0 | inv H0]]]]].
    - clear - H.
      apply align_compatible_rec_Tarray; intros.
      eapply align_compatible_rec_Tarray_inv in H; [| eassumption].
      eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - clear - H.
      apply align_compatible_rec_Tarray; intros.
      eapply align_compatible_rec_Tarray_inv in H; [| eassumption].
      eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
    - eapply align_compatible_rec_by_value; [reflexivity |].
      eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
      auto.
Qed.

Hint Rewrite change_compspecs_t_struct_SHA256state_st : norm.

