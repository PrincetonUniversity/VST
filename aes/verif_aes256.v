Require Import aesutils.
Require Import aes.
Require Import floyd.proofauto.
Require Import AES256.

Local Open Scope logic.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Copied from sha/sha_spec.v
   Note that we just trust that the stdlib is correctly implemented! *)
Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).

Definition t_struct_aesctx := Tstruct _mbedtls_aes_context_struct noattr.
Definition t_struct_tables := Tstruct _aes_tables_struct noattr.

Definition tables_initialized (tables : val) := data_at Ews t_struct_tables (map Vint sbox, 
  (map Vint FT0, (map Vint FT1, (map Vint FT2, (map Vint FT3, (map Vint inv_sbox,
  (map Vint RT0, (map Vint RT1, (map Vint RT2, (map Vint RT3, 
  (map Vint (words_to_ints full_rcons)))))))))))) tables.

Definition tables_uninitialized tables := data_at_ Ews t_struct_tables tables.

Definition aes_init_spec :=
  DECLARE _mbedtls_aes_init
    WITH ctx : val, sh : share
    PRE [ _ctx OF (tptr t_struct_aesctx)]
      PROP (writable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (data_at_ sh t_struct_aesctx ctx)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (data_at sh t_struct_aesctx (Vint Int.zero, (Vint Int.zero, list_repeat 68 (Vint Int.zero))) ctx)
.

Definition zeroize_spec :=
  DECLARE _mbedtls_zeroize
    WITH v : val, cont : share, size : Z
    PRE [ _v OF (tptr tvoid), _n OF tuint ]
      PROP (writable_share cont; 0 <= size <= Int.max_unsigned)
      LOCAL (temp _v v; temp _n (Vint (Int.repr size)))
      SEP (data_at_ cont (tarray tuchar size) v)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (data_at cont (tarray tuchar size) (list_repeat (Z.to_nat size) (Vint Int.zero)) v)
.

Definition aes_free_spec :=
  DECLARE _mbedtls_aes_free
    WITH ctx_cont : share, addr : int
    PRE [ _ctx OF (tptr t_struct_aesctx) ]
      PROP (writable_share ctx_cont)
      LOCAL (temp _ctx (Vint addr))
      SEP (if Int.eq addr Int.zero then emp
           else data_at_ ctx_cont t_struct_aesctx (Vint addr))
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (if Int.eq addr Int.zero then emp
           else data_at ctx_cont t_struct_aesctx (Vint Int.zero, (Vint Int.zero, list_repeat 68 (Vint Int.zero))) (Vint addr))
.

Definition gen_tables_spec :=
  DECLARE _aes_gen_tables
    WITH tables : val
    PRE [  ]
      PROP ()
      LOCAL (gvar _tables tables)
      SEP (tables_uninitialized tables)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (tables_initialized tables)
.

Definition key_expansion_spec :=
  DECLARE _mbedtls_aes_setkey_enc
    WITH ctx : val, key : val, ctx_cont : share, key_cont : share, key_words : list word,
         tables : val, init_done : int
    PRE [ _ctx OF (tptr t_struct_aesctx), _key OF (tptr tuchar), _keybits OF tuint  ]
      PROP (writable_share ctx_cont; readable_share key_cont;
            Zlength key_words = Nk; words_in_bounds key_words;
           (Int.eq init_done Int.one = true \/ Int.eq init_done Int.zero = true))
      LOCAL (temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256)); 
             gvar _aes_init_done (Vint init_done); gvar _tables tables; gvar _aes_init_done (Vint init_done))
      SEP (data_at_ ctx_cont t_struct_aesctx ctx;
           data_at key_cont (tarray tuchar (4*Nk)) (map Vint (words_to_ints key_words)) key;
           if Int.eq init_done Int.one then tables_initialized tables 
           else tables_uninitialized tables)
    POST [  tint ]
      PROP () 
      LOCAL (temp ret_temp (Vint Int.zero); gvar _aes_init_done (Vint Int.one))
      SEP (data_at key_cont (tarray tuchar (4*Nk)) (map Vint (words_to_ints key_words)) key;
           data_at ctx_cont t_struct_aesctx 
                   (Vint (Int.repr Nr), (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])), 
                                         (map Vint (blocks_to_ints (extra_key_expansion key_words)))
                                          ++ list_repeat (4%nat) Vundef)) ctx;
          tables_initialized tables)
.

Definition inv_key_expansion_spec :=
  DECLARE _mbedtls_aes_setkey_dec
    WITH ctx : val, key : val, fsb : val, ctx_cont : share, key_cont : share, 
         tables : val, key_words : list word
    PRE [ _ctx OF (tptr t_struct_aesctx), _key OF (tptr tuchar), _keybits OF tuint ]
      PROP (writable_share ctx_cont; readable_share key_cont; 
            Zlength key_words = Nk; words_in_bounds key_words)
      LOCAL (temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256)); gvar _FSb fsb; gvar _tables tables)
      SEP (tables_uninitialized tables; 
           data_at key_cont (tarray tuchar (4*Nk)) (map Vint (words_to_ints key_words)) key;
           data_at_ ctx_cont t_struct_aesctx ctx)
    POST [  tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint Int.zero))
      SEP (tables_initialized tables;
           data_at key_cont (tarray tuchar (4*Nk)) (map Vint (words_to_ints key_words)) key;
           data_at ctx_cont t_struct_aesctx 
                   (Vint (Int.repr Nr), (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])), 
                                         (map Vint (blocks_to_ints (rev (InverseKeyExpansion key_words))) 
                                                                   ++ list_repeat (8%nat) Vundef))) ctx)
.

Definition encryption_spec :=
  DECLARE _mbedtls_aes_encrypt
    WITH ctx : val, input : val, output : val, ctx_cont : share, in_cont : share, out_cont : share, 
         content : block, key : list block, tables : val
      PRE [ _ctx OF (tptr t_struct_aesctx), _input OF (tptr tuchar), _output OF (tptr tuchar) ]
        PROP (block_in_bounds content; blocks_in_bounds key; Zlength key = (Nr+1)%Z; 
              writable_share out_cont; readable_share in_cont; readable_share ctx_cont)
        LOCAL (temp _ctx ctx; temp _input input; temp _output output; gvar _tables tables)
        SEP (data_at in_cont (tarray tuchar 16) (map Vint (block_to_ints (transpose content))) input;
             data_at ctx_cont (t_struct_aesctx) (Vint (Int.repr Nr), 
               (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])),
                map Vint (blocks_to_ints key) ++ list_repeat (8%nat) Vundef)) ctx;
             data_at_ out_cont (tarray tuchar 16) output;
             tables_initialized tables)
      POST [ tvoid ]
        PROP() LOCAL()
        SEP (data_at out_cont (tarray tuchar 16) (map Vint (block_to_ints (transpose (Cipher key content)))) output;
             data_at in_cont (tarray tuchar 16) (map Vint (block_to_ints (transpose content))) input;
             data_at ctx_cont (t_struct_aesctx) (Vint (Int.repr Nr), 
               (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])),
                map Vint (blocks_to_ints key) ++ list_repeat (8%nat) Vundef)) ctx;
             tables_initialized tables)
.

Definition decryption_spec :=
  DECLARE _mbedtls_aes_decrypt
    WITH ctx : val, input : val, output : val, ctx_cont : share, in_cont : share, out_cont : share, 
         content : block, key : list block, tables : val
      PRE [ _ctx OF (tptr t_struct_aesctx), _input OF (tptr tuchar), _output OF (tptr tuchar) ]
        PROP (block_in_bounds content; blocks_in_bounds key; Zlength key = (Nr+1)%Z; 
              writable_share out_cont; readable_share in_cont; readable_share ctx_cont)
        LOCAL (temp _ctx ctx; temp _input input; temp _output output; gvar _tables tables)
        SEP (data_at in_cont (tarray tuchar 16) (map Vint (block_to_ints (transpose content))) input;
             data_at ctx_cont (t_struct_aesctx) (Vint (Int.repr Nr), 
               (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])),
                map Vint (blocks_to_ints key) ++ list_repeat (8%nat) Vundef)) ctx;
             data_at_ out_cont (tarray tuchar 16) output;
             tables_initialized tables)
      POST [ tvoid ]
        PROP() LOCAL()
        SEP (data_at in_cont (tarray tuchar 16) (map Vint (block_to_ints (transpose content))) input;
             data_at ctx_cont (t_struct_aesctx) (Vint (Int.repr Nr), 
               (Vint (Int.repr (nested_field_offset t_struct_aesctx [StructField _buf])),
                map Vint (blocks_to_ints key) ++ list_repeat (8%nat) Vundef)) ctx;
             data_at out_cont (tarray tuchar 16) (map Vint (block_to_ints (transpose (EqInvCipher key content)))) output;
             tables_initialized tables)
.

Definition Gprog : funspecs := augment_funspecs prog [
  memset_spec; 
  aes_init_spec; 
  zeroize_spec; 
  aes_free_spec; 
  gen_tables_spec; 
  key_expansion_spec; 
  inv_key_expansion_spec; 
  encryption_spec; 
  decryption_spec
].

Lemma body_aes_init: semax_body Vprog Gprog f_mbedtls_aes_init aes_init_spec.
Proof.
  start_function.
  forward_call (* memset( ctx, 0, sizeof( mbedtls_aes_context ) ); *)
    (sh, ctx, 280, Int.zero).
  + rewrite data_at__memory_block. entailer. assert ((sizeof t_struct_aesctx) = 280) by reflexivity. rewrite H0. cancel.
  + (* TODO floyd improve: this works, but it occurs often, can I do it shorter? *)
    split. auto. split; compute; intro; discriminate.
  + forward. 
    (* QQQ how to go from "data_at sh (tarray tuchar 280)" to
                           "data_at sh t_struct_aesctx" *)
    (* Instead of assuming memset for void*, assume it for ctx directly.
       Or do we actually need the postcondition that all is initialized to 0? *)
Abort.

(*
"(Sloop body incr)" corresponds to "for (;; incr) body".
In the body_zeroize lemma, we'll get "(Sloop body Sskip)", and also, Swhile is defined as
Swhile = fun (e : expr) (s : statement) => Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip
so let's prove a lemma for Sloop where incr is Sskip:
*)

Lemma semax_loop_no_incr {Espec : OracleKind} {CS: compspecs}: 
  forall Delta Q body R,
     @semax CS Espec Delta Q body (loop1_ret_assert Q R) ->
     @semax CS Espec Delta Q (Sloop body Sskip) R.
Proof.
  intros. apply semax_loop with (Q' := Q). assumption.
  apply semax_post with (R' := normal_ret_assert Q).
  * intros. destruct ek; unfold normal_ret_assert; simpl; intro.
    - normalize. apply andp_left2. apply derives_refl.
      (* TODO improve floyd: why does entailer! not solve it completely? *)
    - apply andp_left2. apply andp_left1. apply prop_left. intro. discriminate.
    - apply andp_left2. apply andp_left1. apply prop_left. intro. discriminate.
    - apply andp_left2. apply andp_left1. apply prop_left. intro. discriminate.
  * apply semax_skip.
Qed.

(* a list initialized with 0 except its last i elements *)
Definition list_zero_except (i : Z) (size : Z) : list val :=
  (list_repeat (Z.to_nat (size-i)) (Vint Int.zero)) ++ (list_repeat (Z.to_nat i) Vundef).

Lemma list_zero_except_zero: forall size,
  list_zero_except 0 size = list_repeat (Z.to_nat size) (Vint Int.zero).
Proof.
  intro. unfold list_zero_except. simpl. rewrite app_nil_r.
  replace (size - 0) with size by omega. reflexivity.
Qed.

Lemma list_zero_except_all: forall size,
  list_zero_except size size = default_val (tarray tuchar size).
Proof.
  intro. unfold list_zero_except. replace (size - size) with 0 by omega. reflexivity.
Qed.

(* should be in client_lemmas.v TODO floyd *)
Lemma typed_false_tuint:
 forall v, typed_false tuint v -> v = nullval.
Proof.
  intros.
  hnf in H. destruct v; inv H. 
  destruct (Int.eq i Int.zero) eqn:?; inv H1.
  apply int_eq_e in Heqb. subst. reflexivity.
Qed.

Lemma typed_false_tuint_Vint:
  forall v, typed_false tuint (Vint v) -> v = Int.zero.
Proof.
  intros. apply typed_false_tuint in H. apply Vint_inj in H; auto.
Qed.

(* TODO add to library *)
(* TODO generalize: special case of (replace 0 by m) *)
Lemma Z_repr_0_unsigned: forall n,
  0 <= n <= Int.max_unsigned ->
  Int.repr n = Int.zero ->
  n = 0.
Proof.
  (* TODO library: does it have to be such a hack? *)
  intros. assert (Int.unsigned (Int.repr n) = Int.unsigned Int.zero) by congruence.
  rewrite Int.unsigned_repr in H1. compute in H1. assumption. assumption.
Qed.

Lemma body_zeroize: semax_body Vprog Gprog f_mbedtls_zeroize zeroize_spec.
Proof. (* TODO: share with hmacdrbg/verif_hmac_drbg_other.v, where it's almost done *)
  start_function.
  forward.
  (* Swhile takes an expr as condition, but here we have a statement, so it's not parsed as an
     Swhile, but as a "raw" Sloop. *)
  apply semax_seq' with (P' := PROP () LOCAL ()
    SEP (data_at cont (tarray tuchar size) (list_zero_except 0 size) v)).
  * apply semax_pre with (P' := EX n: Z,
      PROP (0 <= n <= Int.max_unsigned)
      LOCAL (temp _p (offset_val (size-n) v); temp _v v; temp _n (Vint (Int.repr n)))
      SEP (data_at cont (tarray tuchar size) (list_zero_except n size) v)).
    - Exists size.
      replace (size - size) with 0 by omega.
      rewrite list_zero_except_all.
      entailer!.
    - apply semax_loop_no_incr. Intros n. forward. forward.
      forward_if (
        PROP ( )
        LOCAL (temp _n (Vint (Int.sub (Int.repr n) (Int.repr 1))); temp _t'1 (Vint (Int.repr n));
               temp _p (offset_val (size - n) v); temp _v v)
        SEP (data_at cont (tarray tuchar size) (list_zero_except n size) v)).
      + forward. entailer.
      + forward.
        apply typed_false_tuint_Vint in H1. apply Z_repr_0_unsigned in H1; [idtac | assumption]. subst.
        entailer.
      + forward. forward. 
        assert_PROP (isptr v) by entailer. destruct v; try inv H1. simpl. (* force_val goes away *)
        admit.
        (* forward. *) (* TODO: why does forward fail? *)
  * simpl. unfold_abbrev'. rewrite list_zero_except_zero. forward.
Admitted.

Lemma body_aes_free: semax_body Vprog Gprog f_mbedtls_aes_free aes_free_spec.
Proof.
  start_function.
  forward_if (
    PROP (Int.eq addr Int.zero = false)
    LOCAL (temp _ctx (Vint addr))
    SEP (if Int.eq addr Int.zero then emp else data_at_ ctx_cont t_struct_aesctx (Vint addr))).
  + simpl in H0. subst. entailer!.
  + forward.
  + forward. entailer.
  + Intros. rewrite H. forward_call ((Vint addr), Tsh, 280).
    - subst Frame. instantiate (1 := []). (* Frame: what's unchanged by function call *)
      unfold fold_right. cancel.
      (* QQQA TODO (again): how can we cast "t_struct_aesctx" into "(tarray tuchar 280)" ? *) admit.
    - split. auto. split; compute; intro; discriminate.
      (* TODO (again): Can we write it shorter? *)
    - forward. rewrite H. (* TODO same casting again *) admit.
Abort.

Lemma ff_exp_range: forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  0 <= Int.unsigned (ff_exp (Int.repr a) (Int.repr b)) < 256.
Proof.
Admitted.

(* In C:  #define XTIME(x) ( ( x << 1 ) ^ ( ( x & 0x80 ) ? 0x1B : 0x00 ) )
          y = XTIME( x ) & 0xFF; 

Watch out! The usage of XTIME is slightly different in all 3 usages!
And luckily, all three usages are in gen_tables.
*)
Lemma xtime_impl: forall {ES : OracleKind} {CS: compspecs} Delta _x _y _t x,
 @semax CS ES Delta
  (PROP () LOCAL (
    temp _x (Vint (Int.repr x))
  ) SEP ())
  (Ssequence
     (Sifthenelse (Ebinop Oand (Etempvar _x tint) (Econst_int (Int.repr 128) tint) tint)
        (Sset _t (Ecast (Econst_int (Int.repr 27) tint) tint))
        (Sset _t (Ecast (Econst_int (Int.repr 0) tint) tint)))
     (Sset _x
        (Ebinop Oand
           (Ebinop Oxor (Etempvar _x tint)
              (Ebinop Oxor (Ebinop Oshl (Etempvar _x tint) (Econst_int (Int.repr 1) tint) tint)
                 (Etempvar _t tint) tint) tint) (Econst_int (Int.repr 255) tint) tint)))
  (normal_ret_assert
     (PROP () LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (xtime (Int.repr x)))) SEP ())).
Proof.
  intros.
(* forward *)
(* check_Delta. *)
(* simplify_Delta. *)
(* Note: The tactics don't work on an abstract Delta, it has to be "fully known" *)
Abort.

(* Calls forward_if with the current precondition to which the provided conditions are added *)
(* QQQ TODO does this already exist? Add to library? *)
Ltac forward_if_diff add := match add with
| (PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2))) => match goal with
  | |- semax ?Delta (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _ _ =>
    let P3 := fresh "P3" in let Q3 := fresh "Q3" in let R3 := fresh "R3" in
    pose (P3 := P1 ++ P2); pose (Q3 := Q1 ++ Q2); pose (R3 := R1 ++ R2);
    simpl in P3, Q3, R3;
    forward_if (PROPx P3 (LOCALx Q3 (SEPx R3)));
    subst P3 Q3 R3
  end
end.

(*
Lemma xtime_step: forall (m: nat), 
  Int.xor (exp3 m) (xtime (exp3 m)) = exp3 (S m).
*)

(* note: does not yet do &0xFF, so the result might be bigger than 256 *)
Definition xtime' (b : int) : int := 
  (Int.xor (Int.shl b Int.one)
           (if Int.eq (Int.and b (Int.repr 128)) Int.zero
            then Int.zero
            else Int.repr 27)).

(* 3^(i+1) = (3^i XOR XTIME(3^i)) & 0xFF *)
Lemma exp3_step: forall (i : Z),
  0 <= i < 256 ->
  (ff_exp (Int.repr 3) (Int.repr (i + 1))) =
  (Int.and (Int.xor (ff_exp (Int.repr 3) (Int.repr i))
                    (xtime' (ff_exp (Int.repr 3) (Int.repr i))))
           (Int.repr 255)).
Proof.
Admitted.

Lemma pow_table_invariant
(i : Z)
(Hi : 0 <= i < 256)
(pow : list val)
(Hp : forall j : Z,
     0 <= j < i ->
     Znth j pow Vundef = Vint (ff_exp (Int.repr 3) (Int.repr j)))
:
(forall j : Z,
     0 <= j < i + 1 ->
     Znth j (upd_Znth i pow (Vint (ff_exp (Int.repr 3) (Int.repr i)))) Vundef
     = Vint (ff_exp (Int.repr 3) (Int.repr j))).
Proof.
  intros. assert (0 <= j < i \/ j = i) as C by omega. destruct C as [C | C].

Admitted.

Lemma log_table_invariant
(i : Z)
(Hi : 0 <= i < 256)
(log : list val)
(Hl : forall j : Z,
     0 <= j < i ->
     Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr j))) log Vundef = Vint (Int.repr j))
:
(forall j : Z,
     0 <= j < i + 1 ->
     Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr j)))
          (upd_Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr i))) log (Vint (Int.repr i))) Vundef
     = Vint (Int.repr j)).
Admitted.

(* TODO floyd put into library (note: not the same as Int.eq_true) *)
Lemma int_eq_same: forall (x y : int),
  x = y -> Int.eq x y = true.
Proof. intros. subst. apply Int.eq_true. Qed.

Lemma body_gen_tables: semax_body Vprog Gprog f_aes_gen_tables gen_tables_spec.
Proof.
  start_function.
  (* this is what seq_assoc2 does:
  match goal with
  |- semax ?D ?Pre (Ssequence (Ssequence (Ssequence ?Init ?Loop) ?Rest1) ?Rest2) ?Post
  => cut (semax D Pre (Ssequence (Ssequence Init Loop) (Ssequence Rest1 Rest2)) Post)
  end.
  *)
  (* Preparation step 1: *)
  simple apply seq_assoc2.
  (* Note: (Ssequence (Ssequence c1 c2) (Ssequence Rest1 Rest2)) is the "canonical" Ssequence form
     that all forward tactics expect, because many commands which look like one command in the C source
     are actually split up into two commands, and the tactic has to see both of them without digging
     too deep. *)

  (* Preparation step 2: *)
  assert (forall Init Cond Body Incr, Sfor Init Cond Body Incr =
    Ssequence Init (Sloop (Ssequence (Sifthenelse Cond Sskip Sbreak) Body) Incr)) as Eq by reflexivity.
  rewrite <- Eq. clear Eq.

  (* And now, we can finally apply forward_for_simple_bound.
     TODO improve floyd: This should be possible without the preparation steps!
     In start_function' of forward.v, generalize the condition for when Sloop is replaced by Sfor,
     and check all usages of Sfor to make sure it doesn't break
  *)
  forward_for_simple_bound 256 (EX i: Z,
    PROP ( 0 <= i ) (* TODO floyd: why do we only get "Int.min_signed <= i < 256", instead of lo=0 ?
                       Probably because there are 2 initialisations in the for-loop... *)
    LOCAL (temp _x (Vint (ff_exp (Int.repr 3) (Int.repr i))); 
        (* TODO documentation should say that I don't need to do this *)
        (* TODO floyd: tactic should tell me so *)
        (* temp _i (Vint (Int.repr i)); *)
           lvar _log (tarray tint 256) lvar1;
           lvar _pow (tarray tint 256) lvar0;
           gvar _tables tables)
    SEP (EX log : list val,
           !!(Zlength log = 256) &&
           !!(forall j, 0 <= j < i -> Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr j))) log Vundef = Vint (Int.repr j))
           && data_at Tsh (tarray tint 256) log lvar1;
         EX pow : list val,
           !!(Zlength pow = 256) &&
           !!(forall j, 0 <= j < i -> Znth j pow Vundef = Vint (ff_exp (Int.repr 3) (Int.repr j)))
           && data_at Tsh (tarray tint 256) pow lvar0;
         tables_uninitialized tables)).
  { (* init *)
    forward. forward. Exists 0. entailer!. do 2 Exists (repeat Vundef 256). entailer!. }
  { (* body *)
    (* forward. TODO floyd: "forward" should tell me to use Intros instead of just failing *)
    Intros log pow.
    freeze [0; 2] Fr.
    forward.
    (* forward. "Error: No applicable tactic." 
       TODO floyd: error message should say that I have to thaw *)
    thaw Fr.
    forward.
      + entailer!. apply ff_exp_range; omega.
      + (* t'1 = ( x & 0x80 ) ? 0x1B : 0x00 ) *)
        forward_if_diff (PROP () LOCAL (temp _t'1 (Vint (
          if Int.eq (Int.and (ff_exp (Int.repr 3) (Int.repr i)) (Int.repr 128)) Int.zero
          then Int.zero
          else (Int.repr 27)
        ))) SEP ()).
        * (* then-branch of "_ ? _ : _" *)
          forward. rewrite Int.eq_false by assumption. entailer!.
        * (* else-branch of "_ ? _ : _" *)
          forward. rewrite int_eq_same by assumption. entailer!. (* TODO floyd: entailer
            should pick up the hypothesis to get rid of the if *)
        * (* after  "_ ? _ : _" *)
          (* x = (x ^ ((x << 1) ^ t'1)) & 0xFF *)
          forward.
          entailer!.
          { f_equal. apply exp3_step. omega. }
          { Exists (upd_Znth i pow (Vint (ff_exp (Int.repr 3) (Int.repr i)))).
            Exists (upd_Znth (Int.unsigned (ff_exp (Int.repr 3) (Int.repr i))) log (Vint (Int.repr i))).
            entailer!. repeat split.
            - replace 256 with (Zlength log) by assumption.
              apply upd_Znth_Zlength.
              replace (Zlength log) with 256 by assumption.
              apply ff_exp_range; omega.
            - apply log_table_invariant. omega. assumption.
            - replace 256 with (Zlength pow) by assumption.
              apply upd_Znth_Zlength. omega.
            - apply pow_table_invariant. omega. assumption. }
  }
  { (* next part: round constants *)
    admit. }
Qed.

