Require Import floyd.proofauto.
Require Import aes.
Require Import tablesLL.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* definitions copied from other files, just to see what we need: *)
Definition t_struct_aesctx := Tstruct _mbedtls_aes_context_struct noattr.
Definition t_struct_tables := Tstruct _aes_tables_struct noattr.
Definition Nr := 14. (* number of cipher rounds *)

Definition tables_initialized (tables : val) := data_at Ews t_struct_tables 
  (map Vint FSb, (map Vint FT0, (map Vint FT1, (map Vint FT2, (map Vint FT3,
  (map Vint RSb, (map Vint RT0, (map Vint RT1, (map Vint RT2, (map Vint RT3, 
  (map Vint RCON))))))))))) tables.

(* arr: list of 4 bytes *)
Definition get_uint32_le (arr: list int) (i: Z) : int :=
 (Int.or (Int.or (Int.or
            (Znth  i    arr Int.zero)
   (Int.shl (Znth (i+1) arr Int.zero) (Int.repr  8)))
   (Int.shl (Znth (i+2) arr Int.zero) (Int.repr 16)))
   (Int.shl (Znth (i+3) arr Int.zero) (Int.repr 24))).

(* outputs a list of 4 bytes *)
Definition put_uint32_le (x : int) : list int :=
  [ (Int.and           x                (Int.repr 255));
    (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255)) ].

Definition byte0 (x : int) : Z :=
  (Z.land (Int.unsigned x) (Int.unsigned (Int.repr 255))).
Definition byte1 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).
Definition byte2 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 16))) (Int.unsigned (Int.repr 255))).
Definition byte3 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).

Definition mbed_tls_fround_col (col0 col1 col2 col3 : int) (rk : int) : int :=
  (Int.xor (Int.xor (Int.xor (Int.xor rk 
    (force_int (Znth (byte0 col0) (map Vint FT0) Vundef)))
    (force_int (Znth (byte1 col1) (map Vint FT1) Vundef)))
    (force_int (Znth (byte2 col2) (map Vint FT2) Vundef)))
    (force_int (Znth (byte3 col3) (map Vint FT3) Vundef))).

Definition four_ints := (int * (int * (int * int)))%type.

Definition mbed_tls_fround (cols : four_ints) (rks : list int) (i : Z) : four_ints :=
match cols with (col0, (col1, (col2, col3))) =>
  ((mbed_tls_fround_col col0 col1 col2 col3 (Znth  i    rks Int.zero)),
  ((mbed_tls_fround_col col1 col2 col3 col0 (Znth (i+1) rks Int.zero)),
  ((mbed_tls_fround_col col2 col3 col0 col1 (Znth (i+2) rks Int.zero)),
   (mbed_tls_fround_col col3 col0 col1 col2 (Znth (i+3) rks Int.zero)))))
end.

Fixpoint mbed_tls_enc_rounds (n : nat) (state : four_ints) (rks : list int) (i : Z) : four_ints :=
match n with
| O => state
| S m => mbed_tls_enc_rounds m (mbed_tls_fround state rks i) rks (i+4)
end.

Definition mbed_tls_final_enc_round (state : four_ints) (rks : list int) : four_ints := state. (* TODO *)

(* plaintext: array of bytes
   rks: expanded round keys, array of Int32 *)
Definition mbed_tls_initial_add_round_key (plaintext : list int) (rks : list int) : four_ints :=
((Int.xor (get_uint32_le plaintext  0) (Znth 0 rks Int.zero)),
((Int.xor (get_uint32_le plaintext  4) (Znth 1 rks Int.zero)),
((Int.xor (get_uint32_le plaintext  8) (Znth 2 rks Int.zero)),
 (Int.xor (get_uint32_le plaintext 12) (Znth 3 rks Int.zero))))).

Definition mbed_tls_aes_enc (plaintext : list int) (rks : list int) : list int :=
  let state0 := mbed_tls_initial_add_round_key plaintext rks in
  match (mbed_tls_final_enc_round (mbed_tls_enc_rounds 13 state0 rks 0) rks) with
  | (col0, (col1, (col2, col3))) => 
       (put_uint32_le col0) ++ (put_uint32_le col1) ++ (put_uint32_le col2) ++ (put_uint32_le col3)
  end.

Definition encryption_spec_ll :=
  DECLARE _mbedtls_aes_encrypt
  WITH ctx : val, input : val, output : val, (* arguments *)
       ctx_sh : share, in_sh : share, out_sh : share, (* shares *)
       plaintext : list Z, (* 16 chars *)
       exp_key : list Z, (* expanded key, 4*(Nr+1)=60 32-bit integers *)
       tables : val (* global var *)
  PRE [ _ctx OF (tptr t_struct_aesctx), _input OF (tptr tuchar), _output OF (tptr tuchar) ]
    PROP (Zlength plaintext = 16; Zlength exp_key = 60;
          readable_share ctx_sh; readable_share in_sh; writable_share out_sh)
    LOCAL (temp _ctx ctx; temp _input input; temp _output output; gvar _tables tables)
    SEP (data_at ctx_sh (t_struct_aesctx) (
          (Vint (Int.repr Nr)), 
          ((field_address t_struct_aesctx [StructField _buf] ctx),
          ((map Vint (map Int.repr exp_key)) ++ (list_repeat (8%nat) Vundef)))
         ) ctx;
         data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
         data_at_ out_sh (tarray tuchar 16) output;
         tables_initialized tables)
  POST [ tvoid ]
    PROP() LOCAL()
    SEP (data_at out_sh (tarray tuchar 16) 
                        (map Vint (mbed_tls_aes_enc (map Int.repr plaintext) (map Int.repr exp_key)))
                         output).

(* QQQ: How to know that if x is stored in a var of type tuchar, 0 <= x < 256 ? *)
(* QQQ: Declare vars of type Z or of type int in API spec ? *)

Definition Gprog : funspecs := ltac:(with_library prog [ encryption_spec_ll ]).

(* TODO move to library (if no one else has done it yet) *)
(* copied from verif_sumarray2.v, but removed unused argument v' *)
Lemma split_array:
 forall {cs: compspecs} mid n (sh: Share.t) (t: type) 
                            v (v1' v2': list (reptype t)) v1 v2 p,
    0 <= mid <= n ->
    JMeq v (v1'++v2') ->
    JMeq v1 v1' ->
    JMeq v2 v2' ->
    data_at sh (tarray t n) v p =
    data_at sh (tarray t mid) v1  p *
    data_at sh (tarray t (n-mid)) v2 
            (field_address0 (tarray t n) [ArraySubsc mid] p).
Admitted.

(* TODO generalize for the case where the original array does not start at index 0 *)
Lemma split_array_head:
 forall {cs: compspecs} n (sh: Share.t) (t: type) 
                            v (v1': (reptype t)) (v2': list (reptype t)) v1 v2 p,
    0 < n ->
    JMeq v (v1' :: v2') ->
    JMeq v1 v1' ->
    JMeq v2 v2' ->
    data_at sh (tarray t n) v p =
    data_at sh t v1 (field_address0 (tarray t n) [ArraySubsc 0] p) *
    data_at sh (tarray t (n-1)) v2 
            (field_address0 (tarray t n) [ArraySubsc 1] p).
Proof.
  intros. replace (v1' :: v2') with ([v1'] ++ v2') in * by reflexivity.
  erewrite (split_array 1 n sh _ v [v1'] v2').
  - f_equal.
Admitted.

(* Simplified Hoare triple corresponding proven by this lemma:
  {e is an lvalue pointing to p.gfs, and at p.gfs, the value v is stored}
  id = e
  {the local variable id stores the value v}
*)
Lemma semax_max_path_field_load_nth_ram':
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) Pre
      (t t_root: type) (gfs: list gfield)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      typeof e = nested_field_type t_root gfs ->
      readable_share sh ->
      type_is_volatile (typeof e) = false ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root (* was t before *) gfs p)) (eval_lvalue e)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H0.
  rewrite H1 in H8.
  assert_PROP (field_compatible t_root gfs p). {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2;
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H6 |].
    rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_load_nth_ram; try eassumption.
  + eapply self_ramify_trans; [exact H6 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; try rewrite <- H1; eauto.
Qed.

Lemma semax_SC_field_load':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e: expr)
      (t t_root: type) (gfs0 gfs1 gfs: list gfield)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      readable_share sh ->
      type_is_volatile (typeof e) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) ->
      typeof e = nested_field_type t_root gfs ->
      gfs = gfs1 ++ gfs0 ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros.
  eapply semax_extract_later_prop'; [exact H9 | clear H9; intro H9].
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v) as A. {
    apply valinject_JMeq. apply is_neutral_cast_by_value with t. rewrite <- H4. assumption.
  }
  eapply semax_max_path_field_load_nth_ram'.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  exact A.
  eassumption.
  2: eassumption.
  2: eassumption.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply H7 |].
    rewrite H5 in A.
    apply @JMeq_sym, A.
  + rewrite <- H5; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H5.
    apply derives_refl.
Qed.

Ltac simpl_Int := repeat match goal with
| |- context [ (Int.mul (Int.repr ?A) (Int.repr ?B)) ] =>
    let x := fresh "x" in (pose (x := (A * B)%Z)); simpl in x;
    replace (Int.mul (Int.repr A) (Int.repr B)) with (Int.repr x); subst x; [|reflexivity]
| |- context [ (Int.add (Int.repr ?A) (Int.repr ?B)) ] =>
    let x := fresh "x" in (pose (x := (A + B)%Z)); simpl in x;
    replace (Int.add (Int.repr A) (Int.repr B)) with (Int.repr x); subst x; [|reflexivity]
end.

Ltac find_SEP_clause_for p Rs i nSH nT nGfs nV nn := match Rs with
| ?R :: ?Rest => match R with
  | field_at ?SH ?T ?gfs ?V p =>
      pose (nSH := SH); pose (nT := T); pose (nGfs := gfs);
      pose (nV := V); pose (nn := i); cbv in nn
  | data_at ?SH ?T ?V p =>
      pose (nSH := SH); pose (nT := T); pose (nGfs := (@nil gfield));
      pose (nV := V); pose (nn := i); cbv in nn
  | field_at_ ?SH ?T ?gfs p =>
      pose (nSH := SH); pose (nT := T); pose (nGfs := gfs);
      pose (nV := (default_val (nested_field_type T gfs))); pose (nn := i); cbv in nn
  | data_at_ ?SH ?T p =>
      pose (nSH := SH); pose (nT := T); pose (nGfs := (@nil gfield));
      pose (nV := (default_val (nested_field_type T []))); pose (nn := i); cbv in nn
  | _ => find_SEP_clause_for p Rest (S i) nSH nT nGfs nV nn
  end
end.

Ltac solve_legal_nested_field_in_entailment' :=
(* same as solve_legal_nested_field_in_entailment but without these lines commented out:
   match goal with
   | |- _ |-- !! legal_nested_field ?t_root (?gfs1 ++ ?gfs0) =>
    unfold t_root, gfs0, gfs1
  end;
*)
  first
  [ apply prop_right; apply compute_legal_nested_field_spec';
    match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor; omega
  |
  apply compute_legal_nested_field_spec;
  match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor;
  try solve [apply prop_right; auto; omega];
  try solve [normalize; apply prop_right; auto; omega]
  ].

Ltac load_tac' :=
ensure_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e1) _ =>
  let HLE := fresh "HLE" in
  let p := fresh "p" in evar (p: val);
  do_compute_lvalue Delta P Q R e1 p HLE;
  subst p;
  match type of HLE with
  | (ENTAIL _, PROPx _ (LOCALx _ (SEPx ?R)) 
    |-- local (`( eq (field_address ?T ?gfs ?p)) (eval_lvalue _))) =>
    let nSH := fresh "SH" in let nT := fresh "T" in let nGfs := fresh "gfs0" in let nV := fresh "V"
    in let nn := fresh "n" in
    find_SEP_clause_for p R 0%nat nSH nT nGfs nV nn;
    let gfs1 := fresh "gfs1" in
    evar (gfs1 : list gfield);
    let H := fresh "Hgfs" in
    assert (gfs1 = (sublist 0 (Zlength gfs - Zlength nGfs) gfs)) as H by (cbv; reflexivity);
    (eapply semax_SC_field_load' with (n0 := nn) (sh := nSH) (gfs2 := nGfs) (gfs3 := gfs1);
    subst nn nSH nGfs gfs1);
    [ reflexivity
    | reflexivity
    | solve [auto] (* readable share *)
    | reflexivity
    | exact HLE
    | reflexivity
    | reflexivity
    | cbv [nth_error]; reflexivity
    | eapply JMeq_refl
    | entailer!
    | solve_legal_nested_field_in_entailment' ]
  end
end.

Ltac forward1' s :=  (* Note: this should match only those commands that
                                     can take a normal_ret_assert *)
  lazymatch s with 
  | Sassign _ _ => store_tac
  | Sset _ ?e => 
    first [no_loads_expr e false; forward_setx
            | load_tac']
  | Sifthenelse ?e _ _ => forward_if_complain
  | Swhile _ _ => forward_while_complain
  | Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward_for_complain
  | Scall _ (Evar _ _) _ =>  advise_forward_call
  | Sskip => forward_skip
  end.

Ltac fwd'' :=
 match goal with
 | |- semax _ _ (Ssequence (Ssequence _ _) _) _ => 
             rewrite <- seq_assoc; fwd''
 | |- semax _ _ (Ssequence ?c _) _ => 
      eapply semax_seq'; [forward1' c | fwd_result]
 | |- semax _ _ ?c _ =>
      rewrite -> semax_seq_skip; 
      eapply semax_seq'; [ forward1' c | fwd_result]
 end.

Ltac forward' :=
  check_Delta;
 repeat simple apply seq_assoc2;
 first
 [ fwd_last
 | fwd_skip
 | fwd'';
  [ .. |
   Intros;
   abbreviate_semax;
   try fwd_skip]
 ].

(**********)

Lemma field_compatible_concat: forall t_root gfsA gfsB a,
  field_compatible t_root (gfsB ++ gfsA) a <->
  field_compatible (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a).
Admitted.

Lemma nested_field_type_concat: forall t_root gfsA gfsB,
  nested_field_type t_root (gfsB ++ gfsA) =
  nested_field_type (nested_field_type t_root gfsA) gfsB.
Admitted.

Lemma field_address_concat: forall t_root gfsA gfsB a,
  field_address t_root (gfsB ++ gfsA) a =
  field_address (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a).
Admitted.

Lemma semax_max_path_field_load_nth_ram_general:
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e1: expr) Pre
      (t t_root: type) (efs: list efield) (gfsA gfsB: list gfield) (tts: list type)
      (a v : val) (v' : reptype (nested_field_type t_root (gfsB ++ gfsA))) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      readable_share sh ->
   (* LR_of_type t_root = lr -> *)
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
   (* legal_nested_efield t_root e1 gfs tts lr = true -> *)
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root (gfsB ++ gfsA) v' a * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfsA a)) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_LR Delta e1 lr) &&
        (tc_efield Delta efs) &&
        efield_denote efs gfsB &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros until 0. intros TId Cast Rsh EqLr Volatile Lnf JM GetR F Evale1 Tc.
  pose proof is_neutral_cast_by_value _ _ Cast as ByVal.
  assert_PROP (typeof (nested_efield e1 efs tts) = nested_field_type t_root (gfsB ++ gfsA)) as EqT. {
    rewrite nested_field_type_concat.
    eapply derives_trans; [exact Tc |].
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ Lnf)).
    normalize.
    apply prop_right; symmetry; auto.
  }
  rewrite EqT in ByVal.
  assert_PROP (field_compatible t_root (gfsB ++ gfsA) a) as Fc. {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2;
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply F |].
    rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_load_nth_ram with (p := (field_address t_root (gfsB ++ gfsA) a)).
  + exact EqT.
  + exact TId.
  + exact Cast.
  + rewrite field_address_concat.
    rewrite (add_andp _ _ Evale1), (add_andp _ _ Tc).
    eapply derives_trans; [| apply eval_lvalue_nested_efield; try eassumption].
    - solve_andp.
    - apply field_compatible_concat. exact Fc.
    - rewrite <- nested_field_type_concat. exact ByVal.
  + eassumption.
  + eassumption.
  + eapply self_ramify_trans; [exact F |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; [auto | rewrite <- EqT; auto | auto | eauto].
  + apply andp_right.
    - rewrite (add_andp _ _ Evale1), (add_andp _ _ Tc).
      eapply derives_trans; [| eapply tc_lvalue_nested_efield].
      * solve_andp.
      * eapply field_compatible_concat. exact Fc.
      * eassumption.
      * eassumption.
      * rewrite <- nested_field_type_concat. exact ByVal.
    - eapply derives_trans; [exact Tc |].
      rewrite EqT. solve_andp.
Qed.


(*
a is the "base pointer" of the SEP clause to be used, and the path to the value can be split in 2 ways:
- a.gfsA.gfsB :  a.gfsA corresponds to e1, and gfsB corresponds to efs
- a.gfs0.gfs1 :  a.gfs0 is what we have a field_at clause for, and gfs1 goes from there to final value
*)
Lemma semax_SC_field_load_general:
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfsA gfsB: list gfield) (tts: list type)
      (p a : val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfsB ->
(*      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) `(field_address t_root gfsA a)) ->*)
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (p = field_address t_root gfsA a) ->
      nth_error R n = Some (field_at sh t_root gfs0 v' a) ->
      readable_share sh ->
      gfsB ++ gfsA = gfs1 ++ gfs0 ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
         local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root (gfsB ++ gfsA)) ->
  (*  LR_of_type t_root = lr ->   <-- split will have to be at right place *)
      LR_of_type (nested_field_type t_root gfsA) = lr ->
(*      legal_nested_efield t_root_should_be_tA e1 gfsB tts lr = true -> *)
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros until 0. intros TypeOf Cast Volatile Ugly Edenote Nice GetR Rsh Split Dig Tc Lnf EqLr Lnef.
  eapply semax_extract_later_prop'; [exact Lnf | clear Lnf; intro Lnf].
  eapply semax_extract_later_prop'; [exact Nice | clear Nice; intro Nice]. subst p.
  eapply semax_extract_later_prop'; 
   [eapply derives_trans; [exact Edenote | eapply typeof_nested_efield; eauto] | intro EqT].
  assert (JMeq (valinject (nested_field_type t_root (gfsB ++ gfsA)) v) v) as JM. {
    apply valinject_JMeq. apply is_neutral_cast_by_value with t.
    rewrite nested_field_type_concat. rewrite EqT. assumption.
  }
  eapply semax_max_path_field_load_nth_ram_general.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ Edenote), (add_andp _ _ Tc); solve_andp.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply Dig |].
    rewrite Split in JM.
    apply @JMeq_sym, JM.
  + rewrite <- Split. exact Lnf.
  + apply sepcon_derives; [| auto].
    rewrite <- Split.
    apply derives_refl.
Qed.

Lemma field_address_nil: forall p t, field_compatible t [] p -> field_address t [] p = p.
Proof.
  intros. rewrite field_compatible_field_address by assumption. simpl.
  rewrite isptr_offset_val_zero. reflexivity. eapply field_compatible_isptr. exact H.
Qed.

(* Now prove the original lemma using the new one:
Lemma semax_SC_field_load:
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      readable_share sh ->
      LR_of_type t_root = lr ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        efield_denote efs gfs ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros.
  eapply semax_SC_field_load_general with (gfsA := []); try rewrite app_nil_r; try eassumption.
  - rewrite field_address_nil.
    + admit. (* TODO = *)
    + admit. (* field_compatible *)
Abort.
*)

(*
Ltac solve_legal_nested_field_in_entailment ::=
(* same as solve_legal_nested_field_in_entailment but with the first match behind a try: *)
   try match goal with
   | |- _ |-- !! legal_nested_field ?t_root (?gfs1 ++ ?gfs0) =>
    unfold t_root, gfs0, gfs1
  end;
  first
  [ apply prop_right; apply compute_legal_nested_field_spec';
    match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor; omega
  |
  apply compute_legal_nested_field_spec;
  match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor;
  try solve [apply prop_right; auto; omega];
  try solve [normalize; apply prop_right; auto; omega]
  ].

Require Import floyd.simpl_reptype.

Ltac entailer_for_load_tac := try solve [entailer!].
(*
Ltac entailer_for_load_tac ::= idtac.
*)

Ltac load_tac ::=
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ (Ecast ?e _)) _ =>
 (* Super canonical cast load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;
    
    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;
    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (ENTAIL _, PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;
    eapply (semax_SC_field_cast_load Delta sh n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [ reflexivity
    | reflexivity
    | now (clear; let H := fresh in intro H; inversion H)
    | solve [subst sh; auto] (* readable share *)
    | reflexivity
    | reflexivity
    | reflexivity
    | reflexivity
    | exact Heq
    | exact HLE
    | exact H_Denote
    | solve_load_rule_evaluation
    | clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n;
      repeat match goal with H := _ |- _ => clear H end;
      try quick_typecheck3; 
      unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
      entailer_for_load_tac
    | solve_legal_nested_field_in_entailment;
      try clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n
    ]

| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
  (* Super canonical load *)
  let e1 := fresh "e" in
  let efs := fresh "efs" in
  let tts := fresh "tts" in
    construct_nested_efield e e1 efs tts;

  let lr := fresh "lr" in
    pose (compute_lr e1 efs) as lr;
    vm_compute in lr;

  let HLE := fresh "H" in
  let p := fresh "p" in evar (p: val);
    match goal with
    | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
    | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
    end;

  let H_Denote := fresh "H" in
  let gfs := fresh "gfs" in
    solve_efield_denote Delta P Q R efs gfs H_Denote;

  ((
    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;
    
    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (ENTAIL _, PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;

    eapply (semax_SC_field_load Delta sh n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [ reflexivity
    | reflexivity
    | solve [subst sh; auto] (* readable share *)
    | reflexivity
    | reflexivity
    | reflexivity
    | reflexivity
    | exact Heq
    | exact HLE
    | exact H_Denote
    | solve_load_rule_evaluation
    | clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n;
      repeat match goal with H := _ |- _ => clear H end;
      try quick_typecheck3; 
      unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
      entailer_for_load_tac
    | solve_legal_nested_field_in_entailment; try clear Heq HLE H_Denote H (*H_LEGAL*);
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n]
  )
  ||
    (eapply semax_SC_field_load_general with (lr0 := lr);
    [ reflexivity
    | reflexivity
    | reflexivity
    | exact HLE
    | exact H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote
    | subst e1 efs tts lr p gfs; clear HLE H_Denote ])
  )
end.
*)

(*********)

Require Import floyd.new_load_tac.

Lemma body_aes_encrypt: semax_body Vprog Gprog f_mbedtls_aes_encrypt encryption_spec_ll.
Proof.
  start_function.
  (* TODO floyd: put (Sreturn None) in such a way that the code can be folded into MORE_COMMANDS *)

  (* RK = ctx->rk; *)
  forward.
  { entailer!. auto with field_compatible. (* TODO floyd: why is this not done automatically? *) }

  assert_PROP (field_compatible t_struct_aesctx [StructField _buf] ctx) as Fctx. entailer!.
  assert ((field_address t_struct_aesctx [StructField _buf] ctx)
        = (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx)) as Eq. {
    do 2 rewrite field_compatible_field_address by auto with field_compatible.
    reflexivity.
  }
  rewrite Eq in *. clear Eq.

  (* Bring the SEP clause about ctx into a suitable form: *)
  (*
  unfold_data_at (1%nat).
  rewrite (field_at_data_at ctx_sh t_struct_aesctx [StructField _buf]).
  *)
  remember (list_repeat 8 Vundef) as Vundefs.
  (*
  simpl.
  erewrite (split_array 60 68 ctx_sh tuint
                        (map Vint (map Int.repr exp_key) ++ Vundefs)
                        (map Vint (map Int.repr exp_key))   Vundefs);
  first [ apply JMeq_refl | omega | idtac ].
  replace (68 - 60) with 8 by omega.
  *)
  assert (exists k1 k2 k3 k4 exp_key_tail, exp_key = k1 :: k2 :: k3 :: k4 :: exp_key_tail) as Eq. {
    destruct exp_key as [|k1 [| k2 [| k3 [| k4 exp_key_tail]]]];
      try solve [compute in H0; omega]. repeat eexists.
  }
  destruct Eq as [k1 [k2 [k3 [k4 [exp_tail Eq]]]]]. subst exp_key. 
  repeat rewrite map_cons.

  (* GET_UINT32_LE( X0, input,  0 ); X0 ^= *RK++;
     GET_UINT32_LE( X1, input,  4 ); X1 ^= *RK++;
     GET_UINT32_LE( X2, input,  8 ); X2 ^= *RK++;
     GET_UINT32_LE( X3, input, 12 ); X3 ^= *RK++; *)
  Ltac GET_UINT32_LE_tac := do 4 (
    (forward; repeat rewrite zlist_hint_db.Znth_map_Vint by (rewrite Zlength_map; omega));
    [ solve [ entailer! ] | idtac ]
  ).
  GET_UINT32_LE_tac. forward. forward. forward.

simpl.

freeze [1; 2; 3] Fr.

forward.
- entailer!.
- instantiate (4 := 1%nat). simpl. unfold data_at. instantiate (2 := []). reflexivity.
- assumption.
- rewrite app_nil_l, app_nil_r. reflexivity.
- eapply JMeq_refl.
- entailer!.
- rewrite app_nil_l. solve_legal_nested_field_in_entailment.
- reflexivity.
- reflexivity.
- {

thaw Fr.
forward.
simpl; repeat rewrite eq_rect_r_eq.

assert_PROP (isptr ctx) as PNctx by entailer!.
assert_PROP (isptr (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx)). {
  destruct ctx; inversion PNctx. entailer!.
}

  GET_UINT32_LE_tac. forward. forward. forward. { entailer. 
  (* TODO floyd: entailer! clears the useful H1 and thus cannot solve the goal *) }

simpl.

forward.
- assert ((force_val
          (sem_add_pi tuint (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx)
             (Vint (Int.repr 1)))
  = (field_address t_struct_aesctx [ArraySubsc 1; StructField _buf] ctx))) as Eq by admit.
  rewrite Eq.
  entailer!.
- instantiate (4 := 3%nat). simpl. unfold data_at. instantiate (2 := []). reflexivity.
- assumption.
- rewrite app_nil_l, app_nil_r. reflexivity.
- eapply JMeq_refl.
- entailer!.
- rewrite app_nil_l. solve_legal_nested_field_in_entailment.
- reflexivity.
- reflexivity.
- {

forward.
simpl; repeat rewrite eq_rect_r_eq.

  GET_UINT32_LE_tac. forward. forward. forward. { entailer!. admit. (* isptr *) }

(* TODO put this in floyd/freezer.v *)
Ltac freeze_except' R Rs i acc name := match Rs with
| nil => let l := fresh "l" in pose (l := rev acc); simpl in l; freeze l name
| R :: ?Rt => freeze_except' R Rt (i+1) acc name
| ?Rh :: ?Rt => freeze_except' R Rt (i+1) (i :: acc) name
end.

Ltac freeze_except R name := match goal with
| |- semax _ (PROPx _ (LOCALx _ (SEPx ?Rs))) _ _ =>
       freeze_except' R Rs 0 (@nil Z) name
end.

freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (field_address t_struct_aesctx [ArraySubsc 0; StructField _buf] ctx,
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.

repeat rewrite field_compatible_field_address by assumption. simpl.
repeat rewrite Int.add_assoc.
simpl.
simpl_Int.

clear Eq.
assert (Eq: (Vptr b (Int.add octx (Int.repr 12)))
    = (field_address t_struct_aesctx [ArraySubsc 1; StructField _buf] ctx)). {
  rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
}
rewrite Eq in *. clear Eq.

forward'.

thaw Fr.
freeze_except (data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input) Fr.
  unfold MORE_COMMANDS. unfold abbreviate.
forward.
  GET_UINT32_LE_tac. forward. forward. forward.

thaw Fr.
freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (Vptr b (Int.add octx (Int.repr 8)),
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.
simpl_Int.
repeat rewrite Int.add_assoc.
simpl_Int.

assert (Eq: (Vptr b (Int.add octx (Int.repr 16)))
    = (field_address t_struct_aesctx [ArraySubsc 2; StructField _buf] ctx)). {
  rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
}
rewrite Eq in *. clear Eq.

forward'.

thaw Fr.
freeze_except (data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input) Fr.
  unfold MORE_COMMANDS. unfold abbreviate.
forward.
  GET_UINT32_LE_tac. forward. forward. forward.

thaw Fr.
freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (Vptr b (Int.add octx (Int.repr 8)),
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.
simpl_Int.
repeat rewrite Int.add_assoc.
simpl_Int.

assert (Eq: (Vptr b (Int.add octx (Int.repr 20)))
    = (field_address t_struct_aesctx [ArraySubsc 3; StructField _buf] ctx)). {
  rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
}
rewrite Eq in *. clear Eq.

forward'.

forward.

match goal with
| |- context [temp _X0 (Vint (Int.xor ?E (Int.repr k1)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 0) by reflexivity
end.
match goal with
| |- context [temp _X1 (Vint (Int.xor ?E (Int.repr k2)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 4) by reflexivity
end.
match goal with
| |- context [temp _X2 (Vint (Int.xor ?E (Int.repr k3)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 8) by reflexivity
end.
match goal with
| |- context [temp _X3 (Vint (Int.xor ?E (Int.repr k4)))] =>
       replace E with (get_uint32_le (map Int.repr plaintext) 12) by reflexivity
end.

unfold Sfor.

(* beginning of for loop *)

forward. forward.
eapply semax_seq'.
{

thaw Fr.

(* ugly hack to avoid type mismatch between
   "(val * (val * list val))%type" and "reptype t_struct_aesctx" *)
assert (exists (v: reptype t_struct_aesctx), v =
       (Vint (Int.repr Nr),
     (Vptr b (Int.add octx (Int.repr 8)),
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs)))
as EE by (eexists; reflexivity).

destruct EE as [vv EE].

apply semax_pre with (P' := 
  (EX i: Z,   PROP ( ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (Vptr b (Int.add octx (Int.repr 24)));
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx 
  ))).
{ subst vv. Exists 6. entailer!. }
{ apply semax_loop with (
  (EX i: Z,   PROP ( ) LOCAL ( 
     temp _i (Vint (Int.repr i));
     temp _RK (Vptr b (Int.add octx (Int.repr 24)));
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx 
  ))).
{ (* loop body *) 
Intro i.

forward_if (PROP ( ) LOCAL (
     temp _i (Vint (Int.repr i));
     temp _RK (Vptr b (Int.add octx (Int.repr 24)));
     temp _X3 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 12) (Int.repr k4)));
     temp _X2 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 8) (Int.repr k3)));
     temp _X1 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 4) (Int.repr k2)));
     temp _X0 (Vint (Int.xor (get_uint32_le (map Int.repr plaintext) 0) (Int.repr k1)));
     temp _ctx ctx;
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv ctx
  )).
{ (* then-branch: Sskip to body *)
  forward. entailer!.
 }
{ (* else-branch: exit loop *)
  forward. entailer!.
 }
{ (* rest: loop body *)
  forward. forward.
  (* now we need the SEP clause about ctx: *) subst vv.

freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (Vptr b (Int.add octx (Int.repr 8)),
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.

assert (Eq: (Vptr b (Int.add octx (Int.repr 24)))
    = (field_address t_struct_aesctx [ArraySubsc 4; StructField _buf] ctx)). {
  rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
}
rewrite Eq in *. clear Eq.

forward'.

{
(* TODO simplify this earlier! *)
admit. (* TODO is_int *)
}

(* next command in loop body: *)
(*     uint32_t b0 = tables.FT0[ ( Y0       ) & 0xFF ];    *)
thaw Fr.
freeze [0; 2] Fr.
unfold tables_initialized.
forward.
{ (* TODO floyd: entailer! says 
Ltac call to "entailer" failed.
Error: Tactic failure: The entailer tactic works only on entailments  _ |-- _ .
even though the goal does have the form _ |-- _ !
*)
admit. }
{
admit. (* TODO 0 <= _ < 256 bounds *)
}

forward. (* takes about half an hour! *)
{ admit. (* entailer!. too slow *) }
{ (* bounds *) admit. }

freeze [2] Fr2.

(* Time forward. aborted after 3.5 hours *)

admit.
}
}
}
{ (* loop incr *)
admit.
}
}
}
{
admit.
}

Qed.

(* TODO floyd: sc_new_instantiate: distinguish between errors caused because the tactic is trying th
   wrong thing and errors because of user type errors such as "tuint does not equal t_struct_aesctx" *)

(* TODO floyd: compute_nested_efield should not fail silently *)

(* TODO floyd: if field_address is given a gfs which doesn't match t, it should not fail silently,
   or at least, the tactics should warn.
   And same for nested_field_offset. *)

(* TODO floyd: I want "omega" for int instead of Z 
   maybe "autorewrite with entailer_rewrite in *"
*)

(* TODO floyd: when load_tac should tell that it cannot handle memory access in subexpressions *)

(* TODO floyd: for each tactic, test how it fails when variables are missing in Pre *)

(*
Note:
field_compatible/0 -> legal_nested_field/0 -> legal_field/0:
  legal_field0 allows an array index to point 1 past the last array cell, legal_field disallows this
*)
