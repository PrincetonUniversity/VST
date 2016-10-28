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
(* real:
    SEP (data_at out_sh (tarray tuchar 16) 
                        (map Vint (mbed_tls_aes_enc (map Int.repr plaintext) (map Int.repr exp_key)))
                         output).
*)
(* fake: (works with start_function) *)
    SEP (data_at out_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) output).

(* QQQ: How to know that if x is stored in a var of type tuchar, 0 <= x < 256 ? *)
(* QQQ: Declare vars of type Z or of type int in API spec ? *)

Definition Gprog : funspecs := augment_funspecs prog [ encryption_spec_ll ].

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
      typeof e = nested_field_type t_root gfs ->
      readable_share sh ->
      type_is_volatile (typeof e) = false ->
      gfs = gfs1 ++ gfs0 ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) ->
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
    apply valinject_JMeq. apply is_neutral_cast_by_value with t. rewrite <- H1. assumption.
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
    rewrite H4 in A.
    apply @JMeq_sym, A.
  + rewrite <- H4; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H4.
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


Lemma body_aes_encrypt: semax_body Vprog Gprog f_mbedtls_aes_encrypt encryption_spec_ll.
Proof.
  start_function.

(* If we give the real specification in the postcondition, start_function tries to simplify it,
   (but it shouldn't), because it consumes more than 14GB of memory! *)
(*
 match goal with |- semax_body _ _ _ ?spec =>
          try unfold spec 
 end.
 match goal with
 | |- semax_body _ _ _ (DECLARE _ WITH u : unit
               PRE  [] main_pre _ u
               POST [ tint ] main_post _ u) => idtac
 | |- semax_body _ _ _ ?spec => 
        check_canonical_funspec spec
 end.
(*
 match goal with |- semax_body _ _ _ _ => start_function' 
   | _ => idtac
 end.
*)

 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec [a b] 
   | (fun i => _) => intros Espec i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end.

 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end.
(* simplify_func_tycontext. (* <--- this one !! *) *)
 match goal with |- @semax _ _ ?DD ?Pre ?Body ?Post =>  
  match DD with context [(func_tycontext ?f ?V ?G)] =>
    let Pre' := fresh "Pre" in set (Pre':=Pre) at 1;
    let Body' := fresh "Body" in set (Body':=Body) at 1;
    let Post' := fresh "Post" in set (Post':=Post) at 1;
    let D1 := fresh "D1" in let Delta := fresh "Delta" in 
    set (Delta := func_tycontext f V G);
    set (D1 := func_tycontext f V G) in Delta (*good*);
    change D1 with (@abbreviate tycontext D1) in Delta;
    unfold func_tycontext, make_tycontext in D1;
    let S1 := fresh "S1" in let DS := fresh "Delta_specs" in
    revert Delta (*good*);
    set (DS := make_tycontext_s G) in D1;
    revert D1;
    set (S1 := make_tycontext_s G) in DS;
    change S1 with (@abbreviate (PTree.t funspec) S1) in DS;
    intros D1 Delta(*good*);
    lazy beta iota zeta delta - [DS] in D1 (*good*); subst D1;
    unfold make_tycontext_s, fold_right in S1; red in S1;
    revert S1 DS Delta(*;
    reduce_snd S1; (* carefully staged to avoid "simpl"       <-- culprit!!
                 in any of the user's funspecs! *)
    intros DS Delta; subst S1 Pre' Body' Post'*)
   end
 end.

(*
match goal with
| |- context [snd ?A] =>
   let j := fresh in set (j := snd A) at 1;
   hnf in j
end.
no match *)

intro S1. (* and BAM, we're gonna simpl in encryption_spec_ll !! *)
*)

  (* TODO floyd: put (Sreturn None) in such a way that the code can be folded into MORE_COMMANDS *)

  (* RK = ctx->rk; *)
  forward.
  { entailer!. auto with field_compatible. (* TODO floyd: why is this not done automatically? *) }

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

eapply semax_seq'. {
hoist_later_in_pre.

eapply (semax_SC_field_load' _ ctx_sh 1 _ _ _ _ _ tuint t_struct_aesctx
[] [ArraySubsc 0; StructField _buf] [ArraySubsc 0; StructField _buf]
 ctx (Vint (Int.repr k1)));
  first [ apply JMeq_refl | reflexivity | assumption | idtac ].
{ entailer!.
  (* TODO floyd why doesn't entailer do this automatically? *)
  do 2 rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity. }
{ entailer!. }
{ entailer!.
  (* TODO floyd why doesn't entailer do in_members? *)
 rewrite <- compute_in_members_true_iff. reflexivity. }
}

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

thaw Fr.
freeze_except (data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input) Fr.
  unfold MORE_COMMANDS. unfold abbreviate.
forward.
  GET_UINT32_LE_tac. forward. forward. forward.

entailer!.
{
(* TODO why is (isptr (field_address t_struct_aesctx [StructField _buf] ctx)) not solved automatically?*)
admit.
}
thaw Fr.

freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (field_address t_struct_aesctx [StructField _buf] ctx,
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.

assert_PROP (field_compatible t_struct_aesctx [StructField _buf] ctx) as Fctx. entailer!.

assert_PROP (isptr ctx) as PNctx by entailer. 
destruct ctx; inversion PNctx. rename i into octx.

repeat rewrite field_compatible_field_address by assumption. simpl.
repeat rewrite Int.add_assoc.
simpl.
simpl_Int.

eapply semax_seq'. {
hoist_later_in_pre.

assert (Eq: (Vptr b (Int.add octx (Int.repr 12)))
    = (field_address t_struct_aesctx [ArraySubsc 1; StructField _buf] (Vptr b octx))). {
  rewrite field_compatible_field_address by auto with field_compatible.
  reflexivity.
}
assert (El: [ArraySubsc 1; StructField _buf] = [ArraySubsc 1; StructField _buf] ++ [])
  by reflexivity.
rewrite Eq in *. rewrite El in *.

match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e1) _ =>
    let HLE := fresh "HLE" in
    let p := fresh "p" in evar (p: val);
    do_compute_lvalue Delta P Q R e1 p HLE;
    subst p
end.

(* how to find the gfs'es:
 gfs: gfs1 ++ gfs0      found from do_compute_lvalue
 gfs0:   go through SEP clauses (knowing p) and check for matching suffix (prefix on path)
 gfs1: rest
 *)

unfold data_at in HLE.

(*
(* Given a list l and a list l0, which is supposed to be a suffix of l,
   find the list l1 such that l = l1 ++ l0, and assign it to result *)
Ltac find_prefix l l0 result :=
  pose (result := sublist 0 ((Zlength l) - (Zlength l0)) l);
  cbv in result. (*;
  instantiate (l1 := result);
  subst result.
*)

find_prefix [4; 5; 6; 8] [6; 8] L1. 

evar (L33: list Z). 
instantiate (L33 := result).

gfs = gfs1 ++ gfs0
*)

Ltac find_SEP_clause_for p Rs i nSH nT nGfs nV nn := match Rs with
| ?R :: ?Rest => match R with
  | field_at ?SH ?T ?gfs ?V p =>
      pose (nSH := SH); pose (nT := T); pose (nGfs := gfs); pose (nV := V); pose (nn := i); cbv in nn
  | _ => find_SEP_clause_for p Rest (S i) nSH nT nGfs nV nn
  end
end.

match type of HLE with
| (ENTAIL _, PROPx _ (LOCALx _ (SEPx ?R)) 
  |-- local (`( eq (field_address ?T ?gfs ?p)) (eval_lvalue _))) =>
    let nSH := fresh "SH" in let nT := fresh "T" in let nGfs := fresh "gfs0" in let nV := fresh "V"
    in let nn := fresh "n" in
    find_SEP_clause_for p R 0%nat nSH nT nGfs nV nn;
    evar (gfs1 : list gfield);
    let H := fresh "Hgfs" in
    assert (gfs1 = (sublist 0 (Zlength gfs - Zlength gfs0) gfs)) as H by (cbv; reflexivity);
    (eapply semax_SC_field_load' with (n0 := nn) (sh := nSH) (gfs2 := nGfs) (gfs3 := gfs1);
    subst nn nSH nGfs gfs1);
 [ reflexivity
 | reflexivity
 | idtac (* should come after gfs instantiation *)
 | solve [auto] (* readable share *)
 | reflexivity
 | idtac (* gfs equality *)
 | idtac (* nth_error *)
 | exact HLE
 | idtac
 | idtac
 | idtac (* solve_legal_nested_field_in_entailment fails *) ]
end.

reflexivity.

reflexivity.

cbv [nth_error]. reflexivity.

eapply JMeq_refl.

entailer!.

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

solve_legal_nested_field_in_entailment'.
}
thaw Fr.
freeze_except (data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input) Fr.
  unfold MORE_COMMANDS. unfold abbreviate.
forward.
  GET_UINT32_LE_tac. forward. forward. forward.

entailer!.
{
(* TODO why is (isptr (field_address t_struct_aesctx [StructField _buf] ctx)) not solved automatically?*)
admit.
}
thaw Fr.

freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (field_address t_struct_aesctx [StructField _buf] ctx,
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.

eapply semax_seq'. {
hoist_later_in_pre.

eapply (semax_SC_field_load' _ ctx_sh 1 _ _ _ _ _ tuint t_struct_aesctx
[] [ArraySubsc 2; StructField _buf] [ArraySubsc 2; StructField _buf]
 ctx (Vint (Int.repr k3)));
  first [ apply JMeq_refl | reflexivity | assumption | idtac ].
{ entailer!.
  (* TODO floyd why doesn't entailer do this automatically? *)
  do 2 rewrite field_compatible_field_address by auto with field_compatible. simpl.
  destruct ctx; inversion PNctx. reflexivity. simpl. do 2 rewrite Int.add_assoc.
  reflexivity. }
{ entailer!. (* TODO isptr field_address *) admit. }
{ entailer!.
  (* TODO floyd why doesn't entailer do in_members? *)
 rewrite <- compute_in_members_true_iff. reflexivity. }
}

thaw Fr.
freeze_except (data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input) Fr.
  unfold MORE_COMMANDS. unfold abbreviate.
forward.
  GET_UINT32_LE_tac. forward. forward. forward.

entailer!.
{
(* TODO why is (isptr (field_address t_struct_aesctx [StructField _buf] ctx)) not solved automatically?*)
admit.
}
thaw Fr.

freeze_except (data_at ctx_sh t_struct_aesctx
     (Vint (Int.repr Nr),
     (field_address t_struct_aesctx [StructField _buf] ctx,
     Vint (Int.repr k1)
     :: Vint (Int.repr k2)
        :: Vint (Int.repr k3) :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ Vundefs))
     ctx) Fr.

eapply semax_seq'. {
hoist_later_in_pre.

eapply (semax_SC_field_load' _ ctx_sh 1 _ _ _ _ _ tuint t_struct_aesctx
[] [ArraySubsc 3; StructField _buf] [ArraySubsc 3; StructField _buf]
 ctx (Vint (Int.repr k4)));
  first [ apply JMeq_refl | reflexivity | assumption | idtac ].
{ entailer!.
  (* TODO floyd why doesn't entailer do this automatically? *)
  do 2 rewrite field_compatible_field_address by auto with field_compatible. simpl.
  destruct ctx; inversion PNctx. reflexivity. simpl. do 3 rewrite Int.add_assoc.
  reflexivity. }
{ entailer!. (* TODO isptr field_address *) admit. }
{ entailer!.
  (* TODO floyd why doesn't entailer do in_members? *)
 rewrite <- compute_in_members_true_iff. reflexivity. }
}

thaw Fr.
unfold MORE_COMMANDS. unfold abbreviate.
forward.

assert_PROP (field_compatible t_struct_aesctx [StructField _buf] ctx) as Fctx. entailer!.

assert_PROP (isptr ctx) as PNctx by entailer. 
destruct ctx; inversion PNctx. simpl. rename i into octx.

repeat rewrite field_compatible_field_address by assumption. simpl.
repeat rewrite Int.add_assoc.
simpl.

simpl_Int.

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
     temp _ctx (Vptr b octx);
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv (Vptr b octx) 
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
     temp _ctx (Vptr b octx);
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv (Vptr b octx) 
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
     temp _ctx (Vptr b octx);
     temp _input input;
     temp _output output;
     gvar _tables tables
  ) SEP (
     data_at_ out_sh (tarray tuchar 16) output;
     tables_initialized tables;
     data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
     data_at ctx_sh t_struct_aesctx vv (Vptr b octx)
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
     (Vptr b octx)) Fr.

eapply semax_seq'. {
hoist_later_in_pre.

match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e1) _ =>
    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
    do_compute_lvalue Delta P Q R e1 p HLE;
    subst p
end.

Lemma semax_SC_field_load'':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e: expr) Pre
      (t: type)
      (a : val) (v : val) (v' : reptype t),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
(*      typeof e = nested_field_type t_root gfs -> *)
      readable_share sh ->
      type_is_volatile (typeof e) = false ->
(*      gfs = gfs1 ++ gfs0 -> *)
      nth_error R n = Some Pre ->
      Pre |-- data_at sh t v' a ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq a) (eval_lvalue e)) ->
      JMeq v' v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
(*    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) -> *)
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Admitted.

(* Note: different from the lower-level semax_max_path_field_load_nth_ram', because it's
   not defined in terms of gfs *)

(*  Level 0: semax_load_nth_ram

eapply semax_load_nth_ram with (t1 := tuint) (t2 := tuint) (n := 1%nat) 
(*
(v :=
(Znth 5
  (Vint (Int.repr k1)
       :: Vint (Int.repr k2)
          :: Vint (Int.repr k3)
             :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ list_repeat 8 Vundef) Vundef))
*)
; first [exact H1 | eassumption | reflexivity | idtac].
{ (* QQQ: Can we solve this goal (which includes the evar ?v) automatically? *)

instantiate (1 := (Znth 5
  (Vint (Int.repr k1)
       :: Vint (Int.repr k2)
          :: Vint (Int.repr k3)
             :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ list_repeat 8 Vundef) Vundef)).
admit.
 }
{ entailer!.
admit. (* TODO is_int *)
}
}
*)


(* Level 1: semax_max_path_field_load_nth_ram' 

not what we want, because it's using gfs stuff
 *)


(* Level 2: semax_SC_field_load''
(where we removed the gfs stuff)  *)

eapply semax_SC_field_load'' with (n := 1%nat) (sh := ctx_sh);
 first [exact H1 | assumption | reflexivity | eapply JMeq_refl | idtac].
{ (* QQQ: Can we solve this goal (which includes the evar ?v') automatically? *)

instantiate (1 := (Znth 5
  (Vint (Int.repr k1)
       :: Vint (Int.repr k2)
          :: Vint (Int.repr k3)
             :: Vint (Int.repr k4) :: map Vint (map Int.repr exp_tail) ++ list_repeat 8 Vundef) Vundef)).

entailer!.
admit.
 }
{ entailer!.
admit. (* TODO is_int *)
}
}

{
unfold MORE_COMMANDS, abbreviate.
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

