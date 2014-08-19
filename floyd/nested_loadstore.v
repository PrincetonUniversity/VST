Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.closed_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

Lemma nested_field_type2_nil: forall t, nested_field_type2 t nil = t.
Proof.
  intros.
  reflexivity.
Qed.

Lemma nested_field_type2_Tstruct_cons: forall i f a t id ids0,
  nested_field_type2 t ids0 = Tstruct i f a ->
  nested_field_type2 t (id :: ids0) = nested_field_type2 (Tstruct i f a) (id :: nil).
Proof.
  intros.
  unfold nested_field_type2 in *.
  destruct (nested_field_rec t ids0) eqn:HH; inversion H; clear H.
  destruct p.
  simpl.
  rewrite HH.
  subst t0.
  solve_field_offset_type id f; reflexivity.
Qed.

Lemma nested_field_type2_len_1_hd: forall i_str i t f a_str id, Pos.eqb i id = true -> nested_field_type2 (Tstruct i_str (Fcons i t f) a_str) (id :: nil) = t.
Proof.
  intros.
  unfold nested_field_type2.
  apply Pos.eqb_eq in H; subst.
  simpl.
  unfold field_offset; simpl.
  if_tac; [reflexivity | congruence].
Qed.

Lemma nested_field_type2_len_1_tl: forall i_str i t f a_str id, Pos.eqb i id = false -> nested_field_type2 (Tstruct i_str (Fcons i t f) a_str) (id :: nil) = nested_field_type2 (Tstruct i_str f a_str) (id :: nil).
Proof.
  intros.
  unfold nested_field_type2.
  unfold nested_field_rec.
  solve_field_offset_type id (Fcons i t f).
  + simpl in H1.
    rewrite Pos.eqb_neq in H.
    if_tac in H1; try congruence.
    solve_field_offset_type id f.
    inversion H1.
    reflexivity.
    inversion H1.
  + simpl in H1.
    rewrite Pos.eqb_neq in H.
    if_tac in H1; try congruence.
    solve_field_offset_type id f.
    inversion H1.
    reflexivity.
Qed.

Fixpoint proj_reptype_structlist i f a (id: ident) (v: reptype_structlist f) : reptype (nested_field_type2 (Tstruct i f a) (id :: nil)) :=
  match f as f'
    return reptype_structlist f' -> reptype (nested_field_type2 (Tstruct i f' a) (id :: nil)) with
  | Fnil => fun _ => default_val _
  | Fcons i0 t0 flds0 => 
    let res :=
   (if is_Fnil flds0 as b
      return (is_Fnil flds0 = b -> 
              (if b then reptype t0 else reptype t0 * reptype_structlist flds0) ->
              reptype (nested_field_type2 (Tstruct i (Fcons i0 t0 flds0) a) (id :: nil)))
    then fun _ v => 
     (if (Pos.eqb i0 id) as b0
        return (Pos.eqb i0 id = b0 ->
                reptype (nested_field_type2 (Tstruct i (Fcons i0 t0 flds0) a) (id :: nil)))
      then fun H => eq_rect_r reptype v (nested_field_type2_len_1_hd i i0 t0 flds0 a id H)
      else fun _ => default_val _) eq_refl
    else fun _ v => 
     (if (Pos.eqb i0 id) as b0
        return (Pos.eqb i0 id = b0 ->
                reptype (nested_field_type2 (Tstruct i (Fcons i0 t0 flds0) a) (id :: nil)))
      then fun H => eq_rect_r reptype (fst v) (nested_field_type2_len_1_hd i i0 t0 flds0 a id H)
      else fun H => eq_rect_r reptype 
                    (proj_reptype_structlist i flds0 a id (snd v)) 
                    (nested_field_type2_len_1_tl i i0 t0 flds0 a id H)
     ) eq_refl) 
    eq_refl
    in
    (fun v0: reptype_structlist (Fcons i0 t0 flds0) => res v0)
  end v.

Fixpoint proj_reptype (t: type) (ids: list ident) (v: reptype t) : reptype (nested_field_type2 t ids) :=
  match ids as ids' return reptype (nested_field_type2 t ids') with
  | nil => eq_rect_r reptype v (eq_sym (nested_field_type2_nil t))
  | id :: ids0 => 
    match (nested_field_type2 t ids0) as T 
      return (nested_field_type2 t ids0 = T) -> reptype T -> reptype (nested_field_type2 t (id :: ids0))
    with
    | Tstruct i f a => fun H proj_v => eq_rect_r reptype 
                                       (proj_reptype_structlist i f a id proj_v)
                                       (nested_field_type2_Tstruct_cons i f a t id ids0 H)
    | _ => fun _ _ => default_val _
    end eq_refl (proj_reptype t ids0 v)
  end.

Fixpoint upd_reptype_structlist i f a (id: ident) (v: reptype_structlist f) (v0: reptype (nested_field_type2 (Tstruct i f a) (id :: nil))): reptype_structlist f :=
  match f as f'
    return reptype_structlist f' -> reptype (nested_field_type2 (Tstruct i f' a) (id :: nil)) -> reptype_structlist f' with
  | Fnil => fun _ _ => struct_default_val _
  | Fcons i0 t0 flds0 => 
    let res :=
   (if is_Fnil flds0 as b
      return (is_Fnil flds0 = b -> 
              (if b then reptype t0 else reptype t0 * reptype_structlist flds0) ->
              reptype (nested_field_type2 (Tstruct i (Fcons i0 t0 flds0) a) (id :: nil)) ->
              (if b then reptype t0 else reptype t0 * reptype_structlist flds0))
    then fun _ v v0 => 
     (if (Pos.eqb i0 id) as b0
        return (Pos.eqb i0 id = b0 -> reptype t0)
      then fun H => eq_rect_r reptype v0 (eq_sym (nested_field_type2_len_1_hd i i0 t0 flds0 a id H))
      else fun _ => v) eq_refl
    else fun _ v v0 => 
     (if (Pos.eqb i0 id) as b0
        return (Pos.eqb i0 id = b0 -> reptype t0 * reptype_structlist flds0)
      then fun H => (eq_rect_r reptype (v0) (eq_sym (nested_field_type2_len_1_hd i i0 t0 flds0 a id H)),
                     snd v)
      else fun H => (fst v, 
                     upd_reptype_structlist i flds0 a id (snd v)
                     (eq_rect_r reptype v0 (eq_sym (nested_field_type2_len_1_tl i i0 t0 flds0 a id H))))
     )eq_refl
   )eq_refl
    in
    (fun v0: reptype_structlist (Fcons i0 t0 flds0) => res v0)
  end v v0.

Fixpoint upd_reptype (t: type) (ids: list ident) (v: reptype t) (v0: reptype (nested_field_type2 t ids)): reptype t :=
  match ids as ids' return (reptype (nested_field_type2 t ids') -> reptype t) with
  | nil => fun v0 => eq_rect_r reptype v0 (nested_field_type2_nil t)
  | id :: ids0 =>
    let res :=
      match (nested_field_type2 t ids0) as T 
        return (nested_field_type2 t ids0 = T) -> reptype T -> 
               reptype (nested_field_type2 t (id :: ids0)) -> reptype T
      with
      | Tstruct i f a => fun H v v0 => 
        upd_reptype_structlist i f a id v
          (eq_rect_r reptype v0 (eq_sym (nested_field_type2_Tstruct_cons i f a t id ids0 H)))
      | _ => fun _ v _ => v
      end eq_refl
    in 
    fun v0 => upd_reptype t ids0 v (res (proj_reptype t ids0 v) v0)
  end v0.

Module Test.
  Definition T1 := Tstruct 1%positive (Fcons 101%positive tint (Fcons 102%positive tint Fnil)) noattr.
  Definition T2 := Tstruct 2%positive (Fcons 201%positive T1 (Fcons 202%positive T1 Fnil)) noattr.
  Definition T3 := Tstruct 3%positive (Fcons 301%positive T2 (Fcons 302%positive T2 Fnil)) noattr.

  Definition v : reptype T3 :=
   (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 5), Vint (Int.repr 6)), (Vint (Int.repr 7), Vint (Int.repr 8)))).

  Lemma Test1: 
    JMeq (proj_reptype T3 (201%positive :: 302%positive :: nil) v) (Vint (Int.repr 5), Vint (Int.repr 6)).
  Proof.
    simpl.
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    reflexivity.
  Qed.

  Lemma Test2:
    JMeq (upd_reptype T3 (201%positive :: 302%positive :: nil) v 
    (Vint (Int.repr 15), Vint (Int.repr 16))) 
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 15), Vint (Int.repr 16)), (Vint (Int.repr 7), Vint (Int.repr 8)))).
  Proof.
    simpl.
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    reflexivity.
  Qed.
End Test.

(*
Lemma semax_nested_efield_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
      is_neutral_cast (typeof (nested_efield e1 ids tts)) t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local `(tc_val (typeof (nested_efield e1 ids tts)) v) &&
        (`(field_at sh (typeof e1) ids v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 ids tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
*)