Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.
Lemma split_offset_array_at_: forall (ty : type) (sh : Share.t) 
         (z lo hi : Z) (v : val),
       z <= lo <= hi ->
       sizeof ty > 0 ->
       legal_alignas_type ty = true ->
       array_at_ ty sh z hi v =
       !! offset_in_range (sizeof ty * z) v &&
       !! offset_in_range (sizeof ty * hi) v &&
       array_at_ ty sh z lo v * 
       array_at_ ty sh 0 (hi - lo) 
       (offset_val (Int.repr (sizeof ty * lo)) v).
Proof.
  intros. unfold array_at_.
  rewrite <- split_offset_array_at; trivial.
Qed.
Lemma offset_val_array_at0:
 forall t sh f lo hi v,
  sizeof t > 0 -> hi >= 0 ->
  legal_alignas_type t = true ->
  array_at t sh (fun i => f (i-lo)%Z) lo (lo + hi) v 
  |--
  array_at t sh f 0 hi (offset_val (Int.repr (sizeof t * lo)) v).
Proof.
  intros.
  rewrite (split_offset_array_at t _ _ lo lo); trivial.
  rewrite array_at_emp.
  entailer. rewrite Zplus_comm. rewrite Z.add_simpl_r.
  apply array_at_ext'. intros. rewrite Z.add_simpl_r. trivial.
  omega.
Qed.

Lemma offset_val_array_at1:
 forall t sh f g k lo hi ofs v,
    sizeof t > 0 -> hi >= 0 ->
    legal_alignas_type t = true ->
    k = lo + hi ->
    g = (fun i => f (i-lo)%Z) ->
    ofs = Int.repr (sizeof t * lo) ->
  array_at t sh g lo k v |--
  array_at t sh f 0 hi ((offset_val ofs) v).
Proof.
  intros. subst. apply offset_val_array_at0; trivial.
Qed.

Require Import sha.spec_sha.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_sha256.

Definition SHA256_spec := (_SHA256, snd spec_sha.SHA256_spec). 
Definition memset_spec := (_memset, snd spec_sha.memset_spec). 
Definition memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec). 

Parameter readable_share:share -> Prop. 
 (*VST provides predicate writable_share, but not this?*)

Definition isUnsignedintZ (i: Z) := (0 <= i < Int.modulus)%Z.

Definition isPosSigned (i: Z) := (0 <= i < Int.max_signed)%Z.

(*only readshare needed*)
Definition repr_text (a: HMAC_Refined.Args) sh: val -> mpred := 
  data_block sh (HMAC_Refined.text a).

Definition repr_text_len (a: HMAC_Refined.Args) (v:val): Prop :=
  let l := HMAC_Refined.text_len a in
  (isPosSigned l /\ v = Vint (Int.repr l) /\
   64 + l <= 1024 (*needed for  instruction memcpy( bufferIn + 64, text, text_len )*)).

(*writeshare needed*)
Definition repr_key (a: HMAC_Refined.Args) sh: val -> mpred := 
  data_block sh (HMAC_Refined.key a).

Definition repr_key_len (a: HMAC_Refined.Args) (v:val): Prop :=
  let l := HMAC_Refined.key_len a in
  (isPosSigned l /\ v = Vint (Int.repr l)).

(*writeshare needed*)
Definition repr_digest (b:bool) (a: HMAC_Refined.Args) sh: val -> mpred := 
if b then
  memory_block sh (Int.repr 32)
else data_block sh (HMAC_Refined.digest a).
(*the boolean flag indicates whether we want to apply the predicate in
the precondition (when digest contains arbitrary junk
"memory_block") or in the postcondition (when digest contains
 sansible data)*)

Record ARGS := 
  { TEXT : val;
    TEXTLEN : val;
    KEY : val;
    KEYLEN : val;
    DIGEST : val}.

Definition prop_args shares (A:ARGS) (a:@HMAC_Refined.Args): Prop := 
match shares with (tsh, (ksh, dsh)) =>
  let tlen := TEXTLEN A in
  let klen := KEYLEN A in
  repr_key_len a klen /\ repr_text_len a tlen /\
     writable_share ksh /\ writable_share dsh /\ readable_share tsh /\
     Zlength (HMAC_Refined.text a) = Int.unsigned (force_int tlen) /\
     Zlength (HMAC_Refined.key a) = Int.unsigned (force_int klen) 
end.

Definition repr_args shares (A:ARGS) (a:@HMAC_Refined.Args) (b:bool): mpred := 
match shares with (tsh, (ksh, dsh)) =>
   repr_key a ksh (KEY A) * repr_text a tsh (TEXT A) * 
   repr_digest b a dsh (DIGEST A)
end.

Definition hmac_spec :=
  DECLARE _hmac_sha256
   WITH tsh: share, ksh : share, dsh: share,
        A:ARGS, a: HMAC_Refined.Args, KV: val
   PRE [ _text OF tptr tuchar, _key OF tptr tuchar, 
         _digest OF tptr tvoid, 
         _text_len OF tuint, _key_len OF tuint]
       PROP (prop_args (tsh, (ksh, dsh)) A a)
       LOCAL (`(eq (TEXT A)) (eval_id _text);
              `(eq (KEY A)) (eval_id _key);
              `(eq (TEXTLEN A)) (eval_id _text_len); 
              `(eq (KEYLEN A)) (eval_id _key_len); 
              `(eq (DIGEST A)) (eval_id _digest);
              `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
       SEP (`(K_vector KV); 
            `(repr_args (tsh, (ksh, dsh)) A a true))
            (*i.e. repr_key a ksh (KEY A));
            `(repr_text a tsh (TEXT A));
            `(repr_digest true a dsh (DIGEST A))*)
    POST [ tvoid ]
     SEP (`(K_vector KV);
          `(repr_key a ksh (KEY A));
          `(repr_text a tsh (TEXT A));
          `(repr_digest false (fst (RefinedHMAC a)) dsh (DIGEST A))).

Definition Vprog : varspecs := (*(_K256, tarray tuint 64)::*) nil.

Definition Gprog : funspecs := 
  memcpy_spec:: memset_spec::
  SHA256_spec:: hmac_spec::nil.

Fixpoint do_builtins (n: nat) (defs : list (ident * globdef fundef type)) : funspecs :=
 match n, defs with
  | S n', (id, Gfun (External (EF_builtin _ sig) argtys resty cc_default))::defs' => 
     (id, mk_funspec (iota_formals 1%positive argtys, resty) unit FF FF) 
      :: do_builtins n' defs'
  | _, _ => nil
 end.

(*Definition Gtot := do_builtins 3 (prog_defs prog) ++ Gprog.*)
Definition Gtot := Gprog.

(********************************VERIFICATION**************************)
(*the type of each local*)
Definition TYPES:= @HMAC_Refined.localRecord type.
Definition types : TYPES:=
  {| k_ipad := tarray tuchar 65;
     k_opad := tarray tuchar 65;
     tk     := tarray tuchar 32;
     tk2    := tarray tuchar 32;
     bufferIn:= tarray tuchar 1024;
     bufferOut:= tarray tuchar 1024 |}.
 
Definition IDENTS: Type := @HMAC_Refined.localRecord ident.
Definition idents: IDENTS :=
  {| k_ipad := _k_ipad;
     k_opad := _k_opad;
     tk := _tk;
     tk2 := _tk2;
     bufferIn := _bufferIn;
     bufferOut := _bufferOut |}.

Definition SHARES := @HMAC_Refined.localRecord share.
Definition topshares: SHARES :=
  {| k_ipad := Tsh;
     k_opad := Tsh;
     tk     := Tsh;
     tk2    := Tsh;
     bufferIn:= Tsh;
     bufferOut:= Tsh |}.

Definition EVAL := @HMAC_Refined.localRecord (environ -> val).
Definition evalID : EVAL :=
  {| k_ipad := eval_id (k_ipad idents);
     k_opad := eval_id (k_opad idents);
     tk := eval_id (tk idents);
     tk2 := eval_id (tk2 idents);
     bufferIn := eval_id (bufferIn idents);
     bufferOut := eval_id (bufferOut idents) |}.

Definition evalVAR : EVAL :=
  {| k_ipad := eval_var (k_ipad idents) (k_ipad types);
     k_opad := eval_var (k_opad idents) (k_opad types);
     tk := eval_var (tk idents) (tk types);
     tk2 := eval_var (tk2 idents) (tk2 types);
     bufferIn := eval_var (bufferIn idents) (bufferIn types);
     bufferOut := eval_var (bufferOut idents) (bufferOut types) |}.

Definition VALUES := @HMAC_Refined.localRecord val.

Definition ApplyID rho : VALUES :=
  {| k_ipad := k_ipad evalID rho;
     k_opad := k_opad evalID rho;
     tk := tk evalID rho;
     tk2 := tk2 evalID rho;
     bufferIn := bufferIn evalID rho;
     bufferOut := bufferOut evalID rho |}.
Definition ApplyVAR rho : VALUES :=
  {| k_ipad := k_ipad evalVAR rho;
     k_opad := k_opad evalVAR rho;
     tk := tk evalVAR rho;
     tk2 := tk2 evalVAR rho;
     bufferIn := bufferIn evalVAR rho;
     bufferOut := bufferOut evalVAR rho |}.

(*boolean flags for initialization status*)
Definition FLAGS:= @HMAC_Refined.localRecord bool.
Definition initFlags : FLAGS :=
  {| k_ipad := true;
     k_opad := true;
     tk     := true;
     tk2    := true;
     bufferIn:= true;
     bufferOut:= true |}.

Definition repr_local (b:bool) sh (tp:type) (vals:list Z) (v:val):mpred :=
if b 
then data_at_ sh tp v (*memory_block sh (Int.repr (sizeof tp)) v*)
else data_block sh vals v.

Definition repr_locals (f: FLAGS) (V:VALUES) (s:HMAC_Refined.Locals) : mpred :=
repr_local (k_ipad f) (k_ipad topshares) (k_ipad types) (k_ipad s) (k_ipad V) *
repr_local (k_opad f) (k_opad topshares) (k_opad types) (k_opad s) (k_opad V) *
repr_local (tk f) (tk topshares) (tk types) (tk s) (tk V) *
repr_local (tk2 f) (tk2 topshares) (tk2 types) (tk2 s) (tk2 V) *
repr_local (bufferIn f) (bufferIn topshares) (bufferIn types) (bufferIn s) (bufferIn V) *
repr_local (bufferOut f) (bufferOut topshares) (bufferOut types) (bufferOut s) (bufferOut V).

Definition permissions' (SH: SHARES) : Prop :=
  writable_share (k_ipad SH) /\ writable_share (k_opad SH) /\
  writable_share (tk SH) /\ writable_share (tk2 SH) /\ 
  writable_share (bufferIn SH) /\ writable_share (bufferOut SH).
Definition permissions := permissions' topshares.

Definition sizes' (t:TYPES): Prop :=
  sizeof (k_ipad t) <= Int.max_unsigned /\ 
  sizeof (k_opad t) <= Int.max_unsigned /\
  sizeof (tk t) <= Int.max_unsigned /\ 
  sizeof (tk2 t) <= Int.max_unsigned /\
  sizeof (bufferIn t) <= Int.max_unsigned /\ 
  sizeof (bufferOut t) <= Int.max_unsigned.
Definition sizes := sizes' types.

Definition ASSN_SuperCanon (SH: SHARES) argshares (A1 A2:ARGS) KV
           (F: FLAGS) a1 a2 (s:HMAC_Refined.Locals) (V: VALUES)(*(P:lift_T (LiftEnviron mpred))*): 
           environ -> mpred :=
       PROP (permissions; sizes; prop_args argshares A2 a2
             (*offset_strict_in_range 64 v is needed, but unfolds too eagerly?
               Shouldn;t this be statically assured the allocation policy
               of the array?*))
       LOCAL (`(eq (TEXT A1)) (eval_id _text);
              `(eq (KEY A2)) (eval_id _key);
              `(eq KV) (eval_var sha._K256 (tarray tuint 64));
              `(eq (TEXTLEN A2)) (eval_id _text_len); 
              `(eq (KEYLEN A2)) (eval_id _key_len); 
              `(eq (DIGEST A2)) (eval_id _digest);
              `(eq (k_ipad V)) (eval_var _k_ipad (k_ipad types));
              `(eq (k_opad V)) (eval_var _k_opad (k_opad types)); 
              `(eq (tk V)) (eval_var _tk (tk types)); 
              `(eq (tk2 V)) (eval_var _tk2 (tk2 types));
              `(eq (bufferIn V)) (eval_var _bufferIn (bufferIn types)); 
              `(eq (bufferOut V)) (eval_var _bufferOut (bufferOut types)))
       SEP (`(K_vector KV); 
            `(repr_locals F V s); `(repr_args argshares A1 a1 true) (*; `(P)*)).

Definition ASSN SH argshares KV F h a A1 A2:= 
  ASSN_SuperCanon SH argshares A1 A2 KV F (args h) a (locals h).
(*
Definition ASSN_EQ SH argshares F h a A1 A2 := 
  EX V: VALUES, EX KV: val, ASSN SH argshares KV F h a A1 A2 V.
*)
Axiom AxiomK: (* ;-) *) forall rho, 
         K_vector (eval_var sha._K256 (tarray tuint 64) rho) =
         K_vector (eval_var sha._K256 (tarray tuint 64) (globals_only rho)).

Lemma sepcon_fold: forall Frame P rho, 
Frame = cons `(P) nil ->
P |-- fold_right
      (fun (P Q : environ -> mpred) (rho0 : environ) => P rho0 * Q rho0) 
      `emp Frame rho.
Proof. intros. subst. simpl. entailer. Qed.

Lemma nth_mapVint: forall i (l:list Z) (Hi: (0 <= i < length l)%nat),
  exists n, nth i (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros i. 
  induction i; simpl; intros.
    destruct l; simpl in *. omega. eexists; reflexivity.
    destruct l; simpl in *. omega.
      destruct (IHi l). omega. rewrite H. eexists; reflexivity.
Qed.

Lemma nth_mapVint' {z}: forall i (l:list Z)
  (Hi: (0 <= i < length l)%nat),
  nth i (map Vint (map Int.repr l)) Vundef = 
  Vint (Int.repr (nth i l z)).
Proof. intros i. 
  induction i; simpl; intros.
    destruct l; simpl in *. omega. trivial.
    destruct l; simpl in *. omega.
      rewrite (IHi l). trivial. omega.
Qed.

Lemma nth_mapVintZ: forall i (l:list Z) (Hi: 0 <= i < Zlength l),
  exists n, nth (Z.to_nat i) (map Vint (map Int.repr l)) Vundef = Vint n.
Proof. intros.
  eapply nth_mapVint. rewrite Zlength_correct in Hi.
  destruct Hi; split.   omega. 
unfold Z.of_nat in H0. unfold Z.to_nat.
destruct l; simpl in *. omega.
destruct i; try omega.
rewrite <- SuccNat2Pos.id_succ.
apply Pos2Nat.inj_lt.
apply H0.
Qed.

Lemma nth_Nlist {A}: forall (a d:A) k i (Hik: (i <k)%nat),
      nth i (Nlist a k) d = a.
Proof. intros a d k.
  induction k; simpl. 
    intros. omega.
  intros. destruct i; simpl. trivial. 
   apply IHk. omega.
Qed. 

Lemma map_Nlist: forall {A B} a (f:A -> B) n,
                 map f (Nlist a n) = Nlist (f a) n.
Proof. intros. induction n; simpl; trivial. rewrite IHn. trivial. Qed.

Lemma minus_lt_compat_r: forall n m p : nat,
      (n < m)%nat -> (p <= n)%nat -> (n - p < m - p)%nat.
Proof. intros. unfold lt in *. omega. Qed.

  Lemma map_nth_error_inv {A B}: forall n (l:list A) (f: A -> B) fd,
    nth_error (map f l) n = Some fd -> exists d, nth_error l n = Some d /\ fd = f d.
  Proof. intros n.
    induction n; intros l.
     destruct l; simpl; intros. inversion H.
       inversion H. exists a. split; trivial.
     destruct l; simpl; intros. inversion H.
       eapply IHn. apply H.
  Qed.
  Lemma nth_error_app {A}: forall n (l:list A) d,
    nth_error l n = Some d -> forall ll, nth_error (l ++ ll) n = Some d.
  Proof. intros n.
    induction n; intros l.
     destruct l; simpl; intros. inversion H. trivial.
     destruct l; simpl; intros. inversion H.
       eapply IHn. apply H.
  Qed.

Lemma isByte_ByteUnsigned b: isbyteZ (Byte.unsigned b).
Proof.
  unfold Byte.unsigned, Byte.intval. destruct b.
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize in intrange.
  rewrite two_power_nat_correct in intrange.
  unfold Zpower_nat in intrange. simpl in intrange. unfold isbyteZ. omega.
Qed.

Lemma nth_zeropad_left {d d'}: forall l i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HMAC_FUN.zeroPad l) d = nth (Z.to_nat i) l d'.
Proof. unfold HMAC_FUN.zeroPad. intros.
  destruct I.
  apply Z2Nat.inj_lt in H0; try omega.
  rewrite Zlength_correct, Nat2Z.id in H0.
  rewrite app_nth1; trivial.
  apply nth_indep; trivial. 
Qed.

Lemma mkKey_left {d d'}: forall l (L: false = (Zlength l >? 64)) 
        i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HMAC_FUN.mkKey l) d = nth (Z.to_nat i) l d'.
Proof.
  unfold HMAC_FUN.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_left; trivial.
Qed.
Lemma nth_zeropad_right {d}: forall l i (I: Zlength l <= i < 64),
      nth (Z.to_nat i) (HMAC_FUN.zeroPad l) d = Z0.
Proof. unfold HMAC_FUN.zeroPad. intros.
  rewrite app_nth2. rewrite nth_Nlist. trivial.
  apply minus_lt_compat_r. destruct I. apply Z2Nat.inj_lt in H0. apply H0.
  specialize (initial_world.zlength_nonneg _ l). omega.
  omega.
  destruct I. apply Z2Nat.inj_le in H. rewrite Zlength_correct, Nat2Z.id in H. apply H.
  apply(initial_world.zlength_nonneg _ l).
  specialize (initial_world.zlength_nonneg _ l). omega. 
  destruct I. apply Z2Nat.inj_le in H. rewrite Zlength_correct, Nat2Z.id in H. apply H.
  apply(initial_world.zlength_nonneg _ l). 
  specialize (initial_world.zlength_nonneg _ l). omega.  
Qed.
Lemma mkKey_right {d}: forall l (L: false = (Zlength l >? 64)) 
        i (I: Zlength l <= i < 64),
      nth (Z.to_nat i) (HMAC_FUN.mkKey l) d = Z0.
Proof.
  unfold HMAC_FUN.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_right; trivial.
Qed.

Lemma Forall_app {A} p (l1 l2: list A): Forall p (l1 ++ l2) <-> (Forall p l1 /\ Forall p l2).
Proof. intros. repeat  rewrite Forall_forall. 
  split; intros.
    split; intros; apply H; apply in_or_app. left; trivial. right; trivial.
  apply in_app_or in H0. destruct H. destruct H0; eauto.
Qed. 

Lemma isbyte_map_ByteUnsigned l: Forall isbyteZ (map Byte.unsigned l).
Proof. 
  rewrite Forall_forall. intros. 
  apply list_in_map_inv in H. destruct H as [b [B1 _]]. subst x.
  apply isByte_ByteUnsigned.
Qed.

(*PATH where key_len a <= 64 holds*)
Module Type HMAC_PART2LE.

Parameter HMAC_LE : forall Espec tsh ksh dsh
(A : ARGS)
(a : HMAC_Refined.Args)
(KV : val)
(HH1 : 0 <= key_len a < Int.max_signed)
(HH2 : KEYLEN A = Vint (Int.repr (key_len a)))
(HH3 : isPosSigned (text_len a))
(TL : TEXTLEN A = Vint (Int.repr (text_len a)))
(TL1024 : 64 + text_len a <= 1024)
(HH5 : writable_share ksh)
(HH6 : writable_share dsh)
(HH7 : readable_share tsh)
(HH8 : Zlength (text a) = text_len a)
(HH9 : Zlength (key a) = key_len a)
(text' : name _text)
(key' : name _key)
(digest' : name _digest)
(textlen' : name _text_len)
(keylen' : name _key_len)
(perms : permissions)
(h0 : HMAC_Refined.hmacState)
(l : HMAC_Refined.Locals)
(Heql : l = HMAC_Refined.initLocalVals)
(Heqh0 : h0 = {| HMAC_Refined.args := a; HMAC_Refined.locals := l |})
(VALS : VALUES)
(HeqKLENGTH : false = (key_len a >? 64))
(GT : key_len a <= 64)
(H0 : sizes)
(TLrange : 0 <= text_len a <= Int.max_unsigned)
(isByteKey : Forall isbyteZ (key a))
(Delta := func_tycontext f_hmac_sha256 Vprog Gtot)
(*(POSTCONDITION := abbreviate : ret_assert)
(MORE_COMMANDS := abbreviate : statement)*)
(KL : 0 <= key_len a <= Int.max_unsigned)
(LK : (length (key a) <= 64)%nat)
(H : align_compatible tuchar (k_opad VALS))
(H1 : isptr (k_opad VALS))
(H2 : offset_in_range 64 (k_opad VALS))
(H3 : offset_in_range 64 (k_ipad VALS))
(H4 : align_compatible tuchar (k_ipad VALS))
(H5 : isptr (k_ipad VALS))
(KIPAD : list Z)
(HeqKIPAD : KIPAD =
           map Byte.unsigned
             (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))
(IPAD : Z -> int)
(HeqIPAD : IPAD = force_int oo ZnthV tuchar (map Vint (map Int.repr KIPAD)))
(KOPAD : list Z)
(HeqKOPAD : KOPAD =
           map Byte.unsigned
             (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))
(OPAD : Z -> int)
(HeqOPAD : OPAD = force_int oo ZnthV tuchar (map Vint (map Int.repr KOPAD)))
(KKEY : Z -> int)
(HeqKKEY : KKEY = force_int oo ZnthV tuchar (map Vint (map Int.repr (key a))))
(ZERO : Z -> val)
(HeqZERO : ZERO = (fun _ : Z => Vint Int.zero)),
@semax Espec (initialized _i Delta)
  (PROP  ()
   LOCAL  (`(eq (TEXT A)) (eval_id _text); `(eq (KEY A)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (TEXTLEN A)) (eval_id _text_len);
   `(eq (KEYLEN A)) (eval_id _key_len); `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP  (`emp; `emp; `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
   `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
   `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
   `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
   `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
   `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
   `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)); `(K_vector KV);
   `(repr_text a tsh (TEXT A)); `(memory_block dsh (Int.repr 32) (DIGEST A))))
  (Ssequence
     (Scall None
        (Evar _memset
           (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Evar _bufferIn (tarray tuchar 1024), Econst_int (Int.repr 0) tint,
        Econst_int (Int.repr 1024) tint])
     (Ssequence
        (Scall None
           (Evar _memcpy
              (Tfunction
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                 (tptr tvoid) cc_default))
           [Evar _bufferIn (tarray tuchar 1024),
           Evar _k_ipad (tarray tuchar 65), Econst_int (Int.repr 64) tint])
        (Ssequence
           (Scall None
              (Evar _memcpy
                 (Tfunction
                    (Tcons (tptr tvoid)
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                    cc_default))
              [Ebinop Oadd (Evar _bufferIn (tarray tuchar 1024))
                 (Econst_int (Int.repr 64) tint) (tptr tuchar),
              Etempvar _text (tptr tuchar), Etempvar _text_len tint])
           (Ssequence
              (Scall None
                 (Evar _SHA256
                    (Tfunction
                       (Tcons (tptr tuchar)
                          (Tcons tuint (Tcons (tptr tuchar) Tnil))) tvoid
                       cc_default))
                 [Evar _bufferIn (tarray tuchar 1024),
                 Ebinop Oadd (Econst_int (Int.repr 64) tint)
                   (Etempvar _text_len tint) tint,
                 Evar _tk2 (tarray tuchar 32)])
              (Ssequence
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Evar _bufferOut (tarray tuchar 1024),
                    Econst_int (Int.repr 0) tint,
                    Econst_int (Int.repr 1024) tint])
                 (Ssequence
                    (Scall None
                       (Evar _memcpy
                          (Tfunction
                             (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             (tptr tvoid) cc_default))
                       [Evar _bufferOut (tarray tuchar 1024),
                       Evar _k_opad (tarray tuchar 65),
                       Econst_int (Int.repr 64) tint])
                    (Ssequence
                       (Scall None
                          (Evar _memcpy
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Ebinop Oadd (Evar _bufferOut (tarray tuchar 1024))
                             (Econst_int (Int.repr 64) tint) (tptr tuchar),
                          Evar _tk2 (tarray tuchar 32),
                          Econst_int (Int.repr 32) tint])
                       (Ssequence 
                         (Scall None
                          (Evar _SHA256
                             (Tfunction
                                (Tcons (tptr tuchar)
                                   (Tcons tuint (Tcons (tptr tuchar) Tnil)))
                                tvoid cc_default))
                          [Evar _bufferOut (tarray tuchar 1024),
                          Ebinop Oadd (Econst_int (Int.repr 64) tint)
                            (Econst_int (Int.repr 32) tint) tint,
                          Etempvar _digest (tptr tvoid)])
                         (Sreturn None)))))))))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        SEP  (`(K_vector KV);
        `(repr_key a ksh (KEY A)); 
        `(repr_text a tsh (TEXT A));
        `(repr_digest false (fst (RefinedHMAC a)) dsh (DIGEST A))))
     (stackframe_of f_hmac_sha256)).

End HMAC_PART2LE.

(*PATH where key_len a > 64 holds*)
Module Type HMAC_PART2GT.

Parameter HMAC_GT: forall Espec tsh ksh dsh
(A : ARGS)
(a : HMAC_Refined.Args)
(KV : val)
(HH1 : isPosSigned (key_len a))
(HH2 : KEYLEN A = Vint (Int.repr (key_len a)))
(HH3 : isPosSigned (text_len a))
(HH4 : TEXTLEN A = Vint (Int.repr (text_len a)))
(TL1024 : 64 + text_len a <= 1024)
(HH5 : writable_share ksh)
(HH6 : writable_share dsh)
(HH7 : readable_share tsh)
(HH8 : Zlength (text a) = text_len a)
(HH9 : Zlength (key a) = key_len a)
(text' : name _text)
(key' : name _key)
(digest' : name _digest)
(textlen' : name _text_len)
(keylen' : name _key_len)
(perms : permissions)
(h0 : HMAC_Refined.hmacState)
(l : HMAC_Refined.Locals)
(Heql : l = HMAC_Refined.initLocalVals)
(Heqh0 : h0 = {| HMAC_Refined.args := a; HMAC_Refined.locals := l |})
(VALS : VALUES)
(h1 : HMAC_Refined.hmacState)
(Heqh1 : h1 = HMAC_Refined.snippet1 h0)
(HeqKLENGTH : true = (key_len a >? 64))
(GT : key_len a > 64)
(H0 : sizes)
(anew : HMAC_Refined.Args)
(Heqanew : anew = args h1)
(TLN : text_len anew = text_len a)
(KLN : key_len anew = 32)
(TN : text anew = text a)
(KN : key anew = functional_prog.SHA_256' (key a))
(TLrange : 0 <= text_len a <= Int.max_unsigned)
(KLrange : 0 <= key_len a <= Int.max_unsigned)
(TKN : tk (locals h1) = functional_prog.SHA_256' (key a))
(ZLenSha : Zlength (tk (locals h1)) = 32)
(isByteKey : Forall isbyteZ (key a))
(isByteShaKey : Forall isbyteZ (functional_prog.SHA_256' (key a)))
(Delta := func_tycontext f_hmac_sha256 Vprog Gtot)
(*(POSTCONDITION := abbreviate : ret_assert)
(MORE_COMMANDS := abbreviate : statement)*)
(H : align_compatible tuchar (k_opad VALS))
(H1 : isptr (k_opad VALS))
(H2 : offset_in_range 64 (k_opad VALS))
(H3 : offset_in_range 64 (k_ipad VALS))
(H4 : align_compatible tuchar (k_ipad VALS))
(H5 : isptr (k_ipad VALS))
(KIPAD : list Z)
(HeqKIPAD : KIPAD =
           map Byte.unsigned
             (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))
(IPAD : Z -> int)
(HeqIPAD : IPAD = force_int oo ZnthV tuchar (map Vint (map Int.repr KIPAD)))
(KOPAD : list Z)
(HeqKOPAD : KOPAD =
           map Byte.unsigned
             (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))
(OPAD : Z -> int)
(HeqOPAD : OPAD = force_int oo ZnthV tuchar (map Vint (map Int.repr KOPAD)))
(KKEY : Z -> int)
(HeqKKEY : KKEY =
          force_int
          oo ZnthV tuchar
               (map Vint (map Int.repr (functional_prog.SHA_256' (key a)))))
(ZERO : Z -> val)
(HeqZERO : ZERO = (fun _ : Z => Vint Int.zero)),
@semax Espec (initialized _i Delta)
  (PROP  ()
   LOCAL  (`(eq (TEXT A)) (eval_id _text); `(eq (tk VALS)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (Vint (Int.repr (text_len a)))) (eval_id _text_len);
   `(eq (Vint (Int.repr 32))) (eval_id _key_len);
   `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP  (`emp; `emp; `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
   `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
   `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
   `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
   `(array_at tuchar Tsh (cVint KKEY) 0 32 (tk VALS));
   `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)); `(K_vector KV);
   `(array_at tuchar ksh (tuchars (map Int.repr (key a))) 0 (Zlength (key a))
       (KEY A)); `(repr_text a tsh (TEXT A));
   `(memory_block dsh (Int.repr 32) (DIGEST A))))
  (Ssequence
     (Scall None
        (Evar _memset
           (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Evar _bufferIn (tarray tuchar 1024), Econst_int (Int.repr 0) tint,
        Econst_int (Int.repr 1024) tint])
     (Ssequence
        (Scall None
           (Evar _memcpy
              (Tfunction
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                 (tptr tvoid) cc_default))
           [Evar _bufferIn (tarray tuchar 1024),
           Evar _k_ipad (tarray tuchar 65), Econst_int (Int.repr 64) tint])
        (Ssequence
           (Scall None
              (Evar _memcpy
                 (Tfunction
                    (Tcons (tptr tvoid)
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                    cc_default))
              [Ebinop Oadd (Evar _bufferIn (tarray tuchar 1024))
                 (Econst_int (Int.repr 64) tint) (tptr tuchar),
              Etempvar _text (tptr tuchar), Etempvar _text_len tint])
           (Ssequence
              (Scall None
                 (Evar _SHA256
                    (Tfunction
                       (Tcons (tptr tuchar)
                          (Tcons tuint (Tcons (tptr tuchar) Tnil))) tvoid
                       cc_default))
                 [Evar _bufferIn (tarray tuchar 1024),
                 Ebinop Oadd (Econst_int (Int.repr 64) tint)
                   (Etempvar _text_len tint) tint,
                 Evar _tk2 (tarray tuchar 32)])
              (Ssequence
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Evar _bufferOut (tarray tuchar 1024),
                    Econst_int (Int.repr 0) tint,
                    Econst_int (Int.repr 1024) tint])
                 (Ssequence
                    (Scall None
                       (Evar _memcpy
                          (Tfunction
                             (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             (tptr tvoid) cc_default))
                       [Evar _bufferOut (tarray tuchar 1024),
                       Evar _k_opad (tarray tuchar 65),
                       Econst_int (Int.repr 64) tint])
                    (Ssequence
                       (Scall None
                          (Evar _memcpy
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Ebinop Oadd (Evar _bufferOut (tarray tuchar 1024))
                             (Econst_int (Int.repr 64) tint) (tptr tuchar),
                          Evar _tk2 (tarray tuchar 32),
                          Econst_int (Int.repr 32) tint])
                       (Ssequence
                          (Scall None
                             (Evar _SHA256
                                (Tfunction
                                   (Tcons (tptr tuchar)
                                      (Tcons tuint (Tcons (tptr tuchar) Tnil)))
                                   tvoid cc_default))
                             [Evar _bufferOut (tarray tuchar 1024),
                             Ebinop Oadd (Econst_int (Int.repr 64) tint)
                               (Econst_int (Int.repr 32) tint) tint,
                             Etempvar _digest (tptr tvoid)]) (Sreturn None)))))))))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        SEP  (`(K_vector KV);
        `(repr_key a ksh (KEY A)); 
        `(repr_text a tsh (TEXT A));
        `(repr_digest false (fst (RefinedHMAC a)) dsh (DIGEST A))))
     (stackframe_of f_hmac_sha256)).

End HMAC_PART2GT.

Require Import sha_lemmas.
Lemma isbyte_sha: forall x, Forall isbyteZ (functional_prog.SHA_256' x).
Proof. intros. unfold functional_prog.SHA_256'. apply isbyte_intlist_to_Zlist. Qed.
