Require Import floyd.proofauto.
Require Import progs.load_demo.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition pair_pair_t := (Tstruct _pair_pair noattr).

Definition array_size := 100.

Definition get22_spec :=
 DECLARE _get22
  WITH pps: val, i: Z, x11: val, x12: val, x21: val, x22: val, sh : share
  PRE [ _pps OF (tptr pair_pair_t), _i OF tint ]
    PROP  (readable_share sh; 0 <= i < array_size)
    LOCAL (temp _pps pps; temp _i (Vint (Int.repr i)))
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i] ((x11, x12), (x21, x22)) pps)
  POST [ tint ]
        PROP () LOCAL (temp ret_temp x22)
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i] ((x11, x12), (x21, x22)) pps).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [get22_spec; main_spec].

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

(* Now prove the original lemma using the new one: *)
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

Ltac solve_legal_nested_field_in_entailment' :=
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


Lemma body_go: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.
(* int res = p->snd; *)
(* forward.   fails *)

eapply semax_seq'. {
hoist_later_in_pre.
match goal with
| |- semax ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sset _ ?e) _ =>
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
      solve_efield_denote Delta P Q R efs gfs H_Denote (*;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let Hint := fresh "Hint" in
    assert (Hint: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- ` (field_at sh t_root gfs0 v p * TT));
    subst p e1*)
end.

eapply semax_SC_field_load_general with (lr0 := lr).
- reflexivity.
- reflexivity.
- reflexivity.
- exact H0. (* HLE *)
- exact H1. (* H_Denote *)
- subst e efs tts lr p gfs. clear H0 H1.
  entailer!. simpl.
  instantiate (1 := pps).
  instantiate (1 := [StructField _right; ArraySubsc i]).
  instantiate (1 := (tarray pair_pair_t array_size)).
  rewrite field_compatible_field_address.
  + simpl. reflexivity.
  + auto with field_compatible.
- subst e efs tts lr p gfs. clear H0 H1.
  instantiate (3 := sh). instantiate (3 := O). simpl.
  unfold data_at. instantiate (2 := [ArraySubsc i]). reflexivity.
- (*solve [subst sh; auto].*) assumption. (* readable share *)
- subst e efs tts lr p gfs. clear H0 H1.
  instantiate (1 := [StructField _snd; StructField _right]).
  reflexivity.
- eapply JMeq_refl.
- subst e efs tts lr p gfs. clear H0 H1. entailer!. simpl; do 2 rewrite eq_rect_r_eq.
  admit. (* is_int stuff *)
- solve_legal_nested_field_in_entailment'.
- reflexivity.
- reflexivity.
}
unfold MORE_COMMANDS, abbreviate.

(* TODO simpl_proj_reptype and fwd_result don't give nice results, why? *)
simpl; do 2 rewrite eq_rect_r_eq. (* QQQ what's this magic?? *)

forward.
Abort.


Lemma body_go: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.
(* int res = p->snd; *)
(* forward.   fails *)

Require Import floyd.simpl_reptype.

eapply semax_seq'. {
hoist_later_in_pre.
match goal with
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
      try solve [entailer!]
    | solve_legal_nested_field_in_entailment; try clear Heq HLE H_Denote H (*H_LEGAL*);
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n]
  )
  ||
    (eapply semax_SC_field_load_general with (lr0 := lr);
    [ reflexivity
    | reflexivity
    | reflexivity
    | exact HLE
    | exact H1
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

(* try reflexivity; try exact HLE; try exact H_Denote; subst e1 efs tts lr p gfs; clear HLE H_Denote *)
end.

- entailer!. simpl.
  instantiate (1 := pps).
  instantiate (1 := [StructField _right; ArraySubsc i]).
  instantiate (1 := (tarray pair_pair_t array_size)).
  rewrite field_compatible_field_address.
  + simpl. reflexivity.
  + auto with field_compatible.
- instantiate (3 := sh). instantiate (3 := O). simpl.
  unfold data_at. instantiate (2 := [ArraySubsc i]). reflexivity.
- assumption. (* readable share *)
- instantiate (1 := [StructField _snd; StructField _right]).
  reflexivity.
- eapply JMeq_refl.
- entailer!. simpl; do 2 rewrite eq_rect_r_eq.
  admit. (* is_int stuff *)
- solve_legal_nested_field_in_entailment'.
- reflexivity.
- reflexivity.
}
unfold MORE_COMMANDS, abbreviate.

(* TODO simpl_proj_reptype and fwd_result don't give nice results, why? *)
simpl; do 2 rewrite eq_rect_r_eq. (* QQQ what's this magic?? *)

forward.

Abort.

Ltac entailer_for_load_tac := try solve [entailer!].
(*
Ltac entailer_for_load_tac ::= idtac.
*)

Ltac load_tac ::=
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with
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

Lemma body_go: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.
(* int res = p->snd; *)
forward.
- entailer!. simpl.
  instantiate (1 := pps).
  instantiate (1 := [StructField _right; ArraySubsc i]).
  instantiate (1 := (tarray pair_pair_t array_size)).
  rewrite field_compatible_field_address.
  + simpl. reflexivity.
  + auto with field_compatible.
- instantiate (3 := sh). instantiate (3 := O). simpl.
  unfold data_at. instantiate (2 := [ArraySubsc i]). reflexivity.
- assumption. (* readable share *)
- instantiate (1 := [StructField _snd; StructField _right]).
  reflexivity.
- eapply JMeq_refl.
- entailer!. simpl; do 2 rewrite eq_rect_r_eq.
  admit. (* is_int stuff *)
- solve_legal_nested_field_in_entailment'.
- reflexivity.
- reflexivity.
- {
(* return res; *)
simpl; do 2 rewrite eq_rect_r_eq.
forward.
Qed.

