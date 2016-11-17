Require Import floyd.base.
Require Import floyd.canon.
Require Import floyd.nested_field_lemmas.
Require Import floyd.reptype_lemmas.
Require Import floyd.simpl_reptype.
Require Import floyd.client_lemmas.
Require Import floyd.entailer.
Require Import floyd.field_at.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.mapsto_memory_block.
Require Import floyd.proj_reptype_lemmas.
Require Import floyd.nested_loadstore.
Require Import floyd.forward.
Require Import floyd.efield_lemmas.
Require Import floyd.field_compat.
Require Import floyd.sc_set_load_store.
Require Import floyd.assert_lemmas.

Local Open Scope logic.

Section SEMAX_SC.

Context {cs: compspecs}.

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
      LR_of_type (nested_field_type t_root gfsA) = lr ->
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

Lemma field_address_nil: forall p t, field_compatible t nil p -> p = field_address t nil p.
Proof.
  intros. rewrite field_compatible_field_address by assumption. simpl.
  rewrite isptr_offset_val_zero. reflexivity. eapply field_compatible_isptr. exact H.
Qed.

(* same as above except note *)
Lemma semax_SC_field_load_general':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfsA gfsB: list gfield) (tts: list type)
      (p a : val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfsB ->
      (* note: rhs of disjunction is just a special case of lhs, but does not require field_compatible,
         so it's simpler to use *)
      (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! (p = field_address t_root gfsA a)) 
         \/ (p = a /\ gfsA = nil) ->
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
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros until 0. intros TypeOf Cast Volatile Ugly Edenote Nice GetR Rsh Split Dig Tc Lnf EqLr Lnef.
  destruct Nice as [Nice | [? ?]].
  - eapply semax_SC_field_load_general; eassumption.
  - subst. eapply semax_SC_field_load_general; try eassumption; try reflexivity.
    (* We prefer to do the following lines in a lemma rather than in the load_tac: *)
    rewrite field_at_compatible' in GetR.
    eapply derives_trans with (Q0 := !! field_compatible t_root gfs0 a).
    * (* based on GetR *) admit.
    * apply prop_derives. intro. apply field_address_nil. (* TODO *) admit.
Admitted.

(* same as above except note
Lemma semax_SC_field_load_general':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfsA gfsB: list gfield) (tts: list type)
      (p a : val) (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      type_is_volatile (typeof (nested_efield e1 efs tts)) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (`(eq p) (eval_LR e1 lr)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- efield_denote efs gfsB ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      (* note: rhs of disjunction is just a special case of lhs, but does not require field_compatible,
         so it's simpler to use *)
        !! (p = field_address t_root gfsA a \/ (p = a /\ gfsA = nil)) ->
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
      LR_of_type (nested_field_type t_root gfsA) = lr ->
      legal_nested_efield (nested_field_type t_root gfsA) e1 gfsB tts lr = true ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros until 0. intros TypeOf Cast Volatile Ugly Edenote Nice GetR Rsh Split Dig Tc Lnf EqLr Lnef.
  eapply semax_extract_later_prop'; [exact Nice | clear Nice; intro Nice].
  destruct Nice as [Nice | [? ?]].
  - eapply semax_SC_field_load_general; try eassumption. apply prop_right. assumption.
  - subst. eapply semax_SC_field_load_general; try eassumption; try reflexivity.
    (* We prefer to do the following lines in a lemma rather than in the load_tac: *)
    rewrite field_at_compatible' in GetR.
    eapply derives_trans with (Q0 := !! field_compatible t_root gfs0 a).
    * (* based on GetR *) admit.
    * apply prop_derives. intro. apply field_address_nil. (* TODO *) admit.
Admitted.
*)

End SEMAX_SC.

Inductive undo_and_first__assert_PROP: Prop -> Prop := .

Ltac test_legal_nested_efield TY e gfsA gfsB tts lr ::=
  unify (legal_nested_efield (nested_field_type TY gfsA) e gfsB tts lr) true.

Ltac unify_var_or_evar name val :=
  let E := fresh "E" in assert (name = val) as E by (subst name; reflexivity); clear E.

Ltac sc_try_instantiate P Q R0 Delta e gfsA gfsB tts a sh t_root gfs0 v n N H SH GFS TY V A ::=
      assert (ENTAIL Delta, PROPx P (LOCALx Q (SEPx (R0 :: nil))) 
         |-- `(field_at sh t_root gfs0 v a)) as H;
      [unify_var_or_evar gfs0 GFS;
       unify_var_or_evar t_root TY;
       unify_var_or_evar sh SH;
       unify_var_or_evar v V;
       unify_var_or_evar a A;
       unfold sh, t_root, gfs0, v, a;
       unfold data_at_;
       unfold data_at;
       unify GFS (skipn (length (gfsB++gfsA) - length GFS) (gfsB++gfsA));
       simpl skipn; subst e gfsA gfsB tts;
       try unfold field_at_;
       generalize V;
       intro;
       solve [
             go_lowerx; rewrite sepcon_emp, <- ?field_at_offset_zero; 
             apply derives_refl
       ]
      | pose N as n ].

Ltac sc_new_instantiate P Q R Rnow Delta e gfsA gfsB tts lr a sh t_root gfs0 v n N H ::=
  match Rnow with
  | ?R0 :: ?Rnow' => 
    match R0 with
    | data_at ?SH ?TY ?V ?A => 
      test_legal_nested_efield TY e gfsA gfsB tts lr;
      sc_try_instantiate P Q R0 Delta e gfsA gfsB tts a sh t_root gfs0 v n N H SH (@nil gfield) TY V A
    | data_at_ ?SH ?TY ?A => 
      test_legal_nested_efield TY e gfsA gfsB tts lr;
      sc_try_instantiate P Q R0 Delta e gfsA gfsB tts a sh t_root gfs0 v n N H SH (@nil gfield) TY
      (default_val (nested_field_type TY nil)) A
    | field_at ?SH ?TY ?GFS ?V ?A =>
      test_legal_nested_efield TY e gfsA gfsB tts lr;
      sc_try_instantiate P Q R0 Delta e gfsA gfsB tts a sh t_root gfs0 v n N H SH GFS TY V A
    | field_at_ ?SH ?TY ?GFS ?A =>
      test_legal_nested_efield TY e gfsA gfsB tts lr;
      sc_try_instantiate P Q R0 Delta e gfsA gfsB tts a sh t_root gfs0 v n N H SH GFS TY
      (default_val (nested_field_type TY GFS)) A
    | _ => sc_new_instantiate P Q R Rnow' Delta e gfsA gfsB tts lr a sh t_root gfs0 v n (S N) H
    end
  end.

Ltac solve_legal_nested_field_in_entailment ::=
   match goal with
   | |- _ |-- !! legal_nested_field ?t_root ?gfs =>
     try unfold t_root;
     try unfold gfs;
     try match gfs with
     | (?gfs1 ++ ?gfs0) => try unfold gfs1; try unfold gfs0
     end
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
    let gfsA := fresh "gfsA" in pose (gfsA := @nil gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    (* new way of invoking sc_new_instantiate even though we're still in old code here!! *)
    sc_new_instantiate P Q R R Delta e1 gfsA gfs tts lr p sh t_root gfs0 v n (0%nat) H;
    
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
      try solve [entailer!]
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

    let HLE := fresh "HLE" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H_Denote" in
    let gfsB := fresh "gfsB" in
      solve_efield_denote Delta P Q R efs gfsB H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs0" in evar (gfs0: list gfield);
    let gfsA := fresh "gfsA" in evar (gfsA: list gfield);
    let a := fresh "a" in evar (a: val);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let Hf := fresh "Hf" in
    let eqL := constr:(p = field_address t_root gfsA a) in
    let eqR := constr:(p = a /\ gfsA = nil) in
    let g := constr:((ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! eqL) \/ eqR) in
    let HNice := fresh "HNice" in

    tryif (
      tryif (
        assert g as HNice by (
          subst p gfsA gfsB a t_root;
          left;
          (eassumption || (apply prop_right; (eassumption || reflexivity)))
        )
      ) then (
        (sc_new_instantiate P Q R R Delta e1 gfsA gfsB tts lr a sh t_root gfs0 v n (0%nat) Hf
         || fail 15 "sc_new_instantiate should really not have failed" )
      ) else (
        instantiate (gfsA := nil);
        (* will fail if setting gfsA to nil was a bad idea: *)
        sc_new_instantiate P Q R R Delta e1 gfsA gfsB tts lr a sh t_root gfs0 v n (0%nat) Hf;
        (assert g as HNice by (
          subst p gfsA gfsB a t_root;
          right;
          split; reflexivity
        ) || fail 15 "assert should really not have failed" )
      )
    ) then (
      let len := fresh "len" in
      pose ((length (gfsB ++ gfsA) - length gfs0)%nat) as len;
      simpl in len;
      let gfs1 := fresh "gfs1" in
      match goal with
      | len := ?len' |- _ => pose (gfs1 := (firstn len' (gfsB ++ gfsA)));
                             cbv [app gfsB gfsA firstn] in gfs1
      end;

      let gfsEq := fresh "gfsEq" in
      assert (gfsB ++ gfsA = gfs1 ++ gfs0) as gfsEq by reflexivity;

      let Heq := fresh "Heq" in
      match type of Hf with
      | (ENTAIL _, PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
      end;

      refine (semax_SC_field_load_general' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _  _ _ lr _ _ _ HLE H_Denote HNice Heq _ gfsEq _ _ _ _ _); try reflexivity;
      [ auto (* readable_share *)
      | solve_load_rule_evaluation
      | clear HLE H_Denote;
        subst lr e1 gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        repeat match goal with H := _ |- _ => clear H end;
        try quick_typecheck3; 
        unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
        try solve [entailer!]
      | subst lr e1 gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        solve_legal_nested_field_in_entailment; try clear HLE H_Denote ]
    ) else (
      assert (undo_and_first__assert_PROP eqL); subst t_root gfsA gfsB a p
    )
end.

Ltac store_tac ::= 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
  (* Super canonical field store *)
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

    let HRE := fresh "H" in
    let v0 := fresh "v" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof (nested_efield e1 efs tts))) v0 HRE;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let gfsA := fresh "gfsA" in pose (gfsA := @nil gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    (* new way of invoking sc_new_instantiate even though we're still in old code here!! *)
    sc_new_instantiate P Q R R Delta e1 gfsA gfs tts lr p sh t_root gfs0 v n (0%nat) H;

    try (unify v (default_val (nested_field_type t_root gfs0));
          lazy beta iota zeta delta - [list_repeat Z.to_nat] in v);

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
    subst gfs;

    eapply (semax_SC_field_store Delta sh n p)
      with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    subst p;
      [ reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity
      | try unfold data_at; try unfold data_at_; try unfold field_at_;
        subst n; cbv beta iota zeta delta [nth_error]; reflexivity
      | exact HLE
      | exact HRE
      | exact H_Denote
      | solve [subst sh; auto] (* writable share *)
      | solve_store_rule_evaluation
      | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        pre_entailer;
        try quick_typecheck3; 
        clear HLE HRE H_Denote H;
        unfold tc_efield; try solve[entailer!]; 
        simpl app; simpl typeof
      | solve_legal_nested_field_in_entailment;
        subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        clear HLE HRE H_Denote H
     ]
end.

