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
(*      legal_nested_efield t_root_should_be_tA e1 gfsB tts lr = true -> *)
(*      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) `(field_address t_root gfsA a)) ->*)
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (p = field_address t_root gfsA a) ->
      nth_error R n = Some (field_at sh t_root gfs0 v' a) ->
      readable_share sh ->
      gfsB ++ gfsA = gfs1 ++ gfs0 ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
  (*     local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&  <-- TODO split correctly *)
         (tc_efield Delta efs) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root (gfsB ++ gfsA)) ->
  (*  LR_of_type t_root = lr ->   <-- split will have to be at right place *)
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
Admitted. (*
  intros until 7; pose proof I; intros.
  eapply semax_extract_later_prop'; [exact H12 | clear H12; intro H12].
  eapply semax_extract_later_prop'; 
   [eapply derives_trans; [exact H9 | eapply typeof_nested_efield; eauto] | intro].
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v)
    by (apply valinject_JMeq; apply is_neutral_cast_by_value with t; rewrite H13; auto).
  eapply semax_max_path_field_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  2: rewrite (add_andp _ _ H9), (add_andp _ _ H11); solve_andp.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply H10 |].
    rewrite H4 in H14.
    apply @JMeq_sym, H14.
  + rewrite <- H4; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H4.
    apply derives_refl.
Qed.
*)

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
- subst e efs tts lr p gfs. clear H0 H1. entailer!.
- solve_legal_nested_field_in_entailment'.
(* - cbv. reflexivity *)
}
unfold MORE_COMMANDS, abbreviate.

(* TODO simpl_proj_reptype and fwd_result don't give nice results, why? *)
simpl; do 2 rewrite eq_rect_r_eq. (* QQQ what's this magic?? *)

forward.
Qed.
