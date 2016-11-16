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
