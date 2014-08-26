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

(**********************************************

nf_sub: substraction in type
PROJ_reptype: big reptype value
proj_reptype: small reptype value
nf_pair_reptype: reversion of proj/PROJ
upd_reptype
data_at_with_exception
data_at_with_exception * field_at = data_at

Further plan: multi substraction, which is useful for definion tree structure

mnf_sub: substraction in type
mPROJ_reptype: big reptype value
mproj_reptype: small reptype value
mnf_pair_reptype: reversion of proj/PROJ
mupd_reptype
data_at_with_mexception
data_at_with_mexception * [field_at] = data_at

**********************************************)

Fixpoint all_fields_except_one (f: fieldlist) (id: ident) : option fieldlist :=
 match f with
 | Fnil => None
 | Fcons i t f0 =>
   if Pos.eqb i id
   then Some f0
   else match (all_fields_except_one f0 id) with
        | None => None
        | Some res => Some (Fcons i t res)
        end
 end.

Fixpoint all_fields_except_one2 (f: fieldlist) (id: ident) : fieldlist :=
 match f with
 | Fnil => Fnil
 | Fcons i t f0 =>
   if Pos.eqb i id
   then f0
   else Fcons i t (all_fields_except_one2 f0 id)
 end.

Fixpoint all_fields_replace_one (f: fieldlist) (id: ident) (t0: type) : option fieldlist :=
 match f with
 | Fnil => None
 | Fcons i t f0 =>
   if Pos.eqb i id
   then Some (Fcons i t0 f0)
   else match (all_fields_replace_one f0 id t0) with
        | None => None
        | Some res => Some (Fcons i t res)
        end
 end.

Fixpoint all_fields_replace_one2 (f: fieldlist) (id: ident) (t0: type) : fieldlist :=
 match f with
 | Fnil => Fnil
 | Fcons i t f0 =>
   if Pos.eqb i id
   then Fcons i t0 f0
   else Fcons i t (all_fields_replace_one2 f0 id t0)
 end.

Fixpoint nf_replace t ids t0: option type :=
  match ids with
  | nil => Some t0
  | id :: ids0 => 
    match nested_field_type2 t ids0 with
    | Tstruct i f a =>
      match all_fields_replace_one f id t0 with
      | Some f' => nf_replace t ids0 (Tstruct i f' a)
      | None => None
      end
    | _ => None
    end
  end.

Fixpoint nf_replace2 t ids t0: type :=
  match ids with
  | nil => t0
  | id :: ids0 => 
    match nested_field_type2 t ids0 with
    | Tstruct i f a => nf_replace2 t ids0 (Tstruct i (all_fields_replace_one2 f id t0) a)
    | _ => t
    end
  end.

Definition nf_sub t id ids: option type :=
  match nested_field_type2 t ids with
  | Tstruct i f a =>
    match all_fields_except_one f id with
    | Some f' => nf_replace t ids (Tstruct i f' a)
    | None => None
    end
  | _ => None
  end.

Definition nf_sub2 t id ids: type :=
  match nested_field_type2 t ids with
  | Tstruct i f a => nf_replace2 t ids (Tstruct i (all_fields_except_one2 f id) a)
  | _ => t
  end.

Lemma all_fields_except_one_all_fields_except_one2: forall f id,
  all_fields_except_one f id = Some (all_fields_except_one2 f id) \/
  all_fields_except_one f id = None.
Proof.
  intros.
  induction f.
  + auto.
  + simpl; if_tac; [ |destruct IHf].
    - auto.
    - rewrite H. auto.
    - rewrite H. auto.
Qed.

Lemma all_fields_replace_one_all_fields_replace_one2: forall f id t,
  all_fields_replace_one f id t = Some (all_fields_replace_one2 f id t) \/
  all_fields_replace_one f id t = None.
Proof.
  intros.
  induction f.
  + auto.
  + simpl; if_tac; [ |destruct IHf].
    - auto.
    - rewrite H. auto.
    - rewrite H. auto.
Qed.

Lemma nf_replace_nf_replace2: forall t ids t0,
  nf_replace t ids t0 = Some (nf_replace2 t ids t0) \/
  nf_replace t ids t0 = None.
Proof.
  induction ids; intros.
  + auto.
  + simpl; destruct (nested_field_type2 t ids); auto.
    destruct (all_fields_replace_one_all_fields_replace_one2 f a t0) as [H | H];
    rewrite H; auto.
Qed.

Lemma nf_sub_nf_sub2: forall t id ids,
  nf_sub t id ids = Some (nf_sub2 t id ids) \/
  nf_sub t id ids = None.
Proof.
  intros.
  unfold nf_sub2, nf_sub.
  destruct (nested_field_type2 t ids); auto.
  destruct (all_fields_except_one_all_fields_except_one2 f id) as [H | H];
  rewrite H; auto.
  apply nf_replace_nf_replace2.
Qed.

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

Lemma gupd_reptype_structlist_aux: forall i f a i0 t0,
  reptype (Tstruct i (all_fields_replace_one2 f i0 t0) a) = 
  match f with
  | Fnil => reptype_structlist Fnil
  | Fcons i1 t1 flds0 =>
      if (i1 =? i0)%positive
      then
       if is_Fnil flds0
       then reptype t0
       else (reptype t0 * reptype_structlist flds0)%type
      else
       if is_Fnil (all_fields_replace_one2 flds0 i0 t0)
       then reptype t1
       else
        (reptype t1 *
         reptype_structlist (all_fields_replace_one2 flds0 i0 t0))%type
  end.
Proof.
  intros.
  destruct f; [|simpl; if_tac]; reflexivity.
Qed.

Fixpoint gupd_reptype_structlist i f a (i0: ident) (t0: type) (v: reptype (Tstruct i f a)) (v0: reptype t0) : reptype (Tstruct i (all_fields_replace_one2 f i0 t0) a) :=
  let res :=
  match f as f'
    return reptype_structlist f' -> 
           match f' with
           | Fnil => reptype_structlist Fnil
           | Fcons i1 t1 flds0 => 
             if (Pos.eqb i1 i0)
              then (if is_Fnil flds0 then reptype t0 else reptype t0 * reptype_structlist flds0)
              else (if is_Fnil (all_fields_replace_one2 flds0 i0 t0) then reptype t1 else reptype t1 * 
                    reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
           end
  with
  | Fnil => fun _ => struct_default_val _
  | Fcons i1 t1 flds0 => fun v =>
   (if Pos.eqb i1 i0 as b
      return if b
             then (if is_Fnil flds0 then reptype t0 else reptype t0 * reptype_structlist flds0)
             else (if is_Fnil (all_fields_replace_one2 flds0 i0 t0) then reptype t1 else reptype t1 * 
                   reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
    then
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t1 else reptype t1 * reptype_structlist flds0) ->
               (if b0 then reptype t0 else reptype t0 * reptype_structlist flds0)
      then fun _ => v0
      else fun v => (v0, snd v)
     ) v
    else
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t1 else reptype t1 * reptype_structlist flds0) ->
               (if is_Fnil (all_fields_replace_one2 flds0 i0 t0) then reptype t1 else reptype t1 * 
                   reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
      then
        if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b1
          return reptype t1 ->
                 (if b1 then reptype t1 else reptype t1 * 
                     reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
        then fun _ => default_val _
        else fun _ => (default_val _, struct_default_val _)
      else
        if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b1
          return reptype t1 * reptype_structlist flds0 ->
                 (if b1 then reptype t1 else reptype t1 * 
                     reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
        then fun _ => default_val _
        else fun v => (fst v, gupd_reptype_structlist i flds0 a i0 t0 (snd v) v0)
      ) v
   )
  end v
  in eq_rect_r id res (gupd_reptype_structlist_aux i f a i0 t0).

Fixpoint gupd_reptype (t: type) (ids: list ident) (t0: type) (v: reptype t) (v0: reptype t0): reptype (nf_replace2 t ids t0) := 
  match ids as ids' return reptype (nf_replace2 t ids' t0) with
  | nil => v0
  | id :: ids0 => 
    match (nested_field_type2 t ids0) as T 
      return reptype T -> reptype (match T with
                                   | Tstruct i f a => nf_replace2 t ids0 
                                     (Tstruct i (all_fields_replace_one2 f id t0) a)
                                   | _ => t
                                   end)
    with
    | Tstruct i f a => fun v' => gupd_reptype t ids0 (Tstruct i (all_fields_replace_one2 f id t0) a) v 
                                 (gupd_reptype_structlist i f a id t0 v' v0)
    | _ => fun _ => default_val _
    end (proj_reptype t ids0 v)
  end.

Print Errors.

Lemma all_fields_replace_one2_identical: forall f i t,
  (field_type i f = Errors.OK t \/ exists e, field_type i f = Errors.Error e) -> all_fields_replace_one2 f i t = f.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl in *.
    if_tac in H; [apply Pos.eqb_eq in H0 | apply Pos.eqb_neq in H0];
    rewrite Pos.eqb_sym in H0; rewrite H0.
    - destruct H as [? | [? ?]]; inversion H; reflexivity.
    - rewrite (IHf H). reflexivity.
Qed.

Lemma nf_replace2_identical: forall t ids, t = nf_replace2 t ids (nested_field_type2 t ids).
Proof.
  intros.
  induction ids.
  + reflexivity.
  + simpl.
    destruct (nested_field_type2 t ids) eqn:?; auto.
    rewrite all_fields_replace_one2_identical; auto.
    erewrite nested_field_type2_Tstruct_cons; eauto.
    unfold nested_field_type2; simpl.
    solve_field_offset_type a f; eauto.
Qed.

Fixpoint upd_reptype (t: type) (ids: list ident) (v: reptype t) (v0: reptype (nested_field_type2 t ids)): reptype t :=
  eq_rect_r reptype (gupd_reptype t ids (nested_field_type2 t ids) v v0) (nf_replace2_identical t ids).
  (* It is indeed not a fixpoint. But this definition style *)
  (* enables it to get unfolded directly by simpl tactic.   *)

Fixpoint PROJ_reptype_structlist (f: fieldlist) (id: ident) (v: reptype_structlist f): reptype_structlist (all_fields_except_one2 f id) :=
  let res :=
  match f as f'
    return reptype_structlist f' -> 
           reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i t f0 =>
                                   if (i =? id)%positive
                                   then f0
                                   else Fcons i t (all_fields_except_one2 f0 id)
                               end)
  with
  | Fnil => fun v => v
  | Fcons i t f0 => fun v => 
     if Pos.eqb i id as b
       return reptype_structlist (if b
                                  then f0
                                  else Fcons i t (all_fields_except_one2 f0 id))
     then
      (if (is_Fnil f0) as b0
         return (if b0 then reptype t else reptype t * reptype_structlist f0) -> reptype_structlist f0
       then fun _ => struct_default_val _
       else fun v => snd v) v
     else
      (if (is_Fnil f0) as b0
         return (if b0 then reptype t else reptype t * reptype_structlist f0) -> 
                (if is_Fnil (all_fields_except_one2 f0 id) then reptype t else 
                 reptype t * reptype_structlist (all_fields_except_one2 f0 id))
       then fun v => 
         if is_Fnil (all_fields_except_one2 f0 id) as b1
           return if b1 then reptype t else 
                  reptype t * reptype_structlist (all_fields_except_one2 f0 id)
         then v
         else (v, struct_default_val _)
       else fun v =>
         if is_Fnil (all_fields_except_one2 f0 id) as b1
           return if b1 then reptype t else 
                  reptype t * reptype_structlist (all_fields_except_one2 f0 id)
         then fst v
         else (fst v, PROJ_reptype_structlist f0 id (snd v))
      ) v
  end v
  in
  match f as f'
    return reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i t f0 =>
                                   if (i =? id)%positive
                                   then f0
                                   else Fcons i t (all_fields_except_one2 f0 id)
                               end) ->
           reptype_structlist (all_fields_except_one2 f' id)
  with
  | Fnil => fun v => v
  | _ => fun v => v
  end res.

Fixpoint PROJ_reptype (t: type) (id: ident) (ids: list ident) (v: reptype t) : reptype (nf_sub2 t id ids) :=
  match nested_field_type2 t ids as T 
    return reptype T ->
           reptype (match T with
                    | Tstruct i f a => nf_replace2 t ids (Tstruct i (all_fields_except_one2 f id) a)
                    | _ => t
                    end)
  with
  | Tstruct i f a => fun v0 => gupd_reptype t ids (Tstruct i (all_fields_except_one2 f id) a) v 
                     (PROJ_reptype_structlist f id v0)
  | _ => fun _ => v
  end (proj_reptype t ids v).

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

  Lemma Test3:
    JMeq (PROJ_reptype T3 201%positive (302%positive :: nil) v) 
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))), 
    ((Vint (Int.repr 7), Vint (Int.repr 8)))).
  Proof.
    simpl.
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    reflexivity.
  Qed.
End Test.

Definition precise : mpred -> Prop := msl.predicates_sl.precise.

Lemma mapsto_precise: forall sh t v p, precise (mapsto sh t p v).
Proof.
Admitted.

Lemma emp_precise: precise emp.
Proof.
Admitted.

Lemma precise_sepcon: forall P Q, precise P -> precise Q -> precise (P * Q).
Proof.
Admitted.

Lemma precise_andp: forall P Q, precise P -> precise Q -> precise (P && Q).
Proof.
Admitted.

Lemma precise_prop_andp: forall P Q, precise Q -> precise (!! P && Q).
Proof.
Admitted.

Lemma precise_wand_sepcon: forall P Q, precise P -> P -* (P * Q) = Q.
Proof.
Admitted.

Lemma precise_sepcon_cancel: forall P Q R, precise P -> P * Q = P * R -> Q = R.
Proof.
  intros.
  rewrite <- precise_wand_sepcon with (P:= P) (Q := Q) by auto.
  rewrite <- precise_wand_sepcon with (P:= P) (Q := R) by auto.
  rewrite H0.
  reflexivity.
Qed.  

(* Here, this precise can be set to be more stronger property, such as splittable precise. *)
Lemma mapsto__precise: forall sh t p, precise (mapsto_ sh t p).
Proof.
  intros.
  unfold mapsto_.
  apply mapsto_precise.
Qed.

Lemma FF_precise: precise (FF).
Proof.
  replace (@FF mpred Nveric) with (mapsto Tsh tint Vundef Vundef).
  apply mapsto_precise.
  unfold mapsto.
  reflexivity.
Qed.

Lemma memory_block_precise: forall sh n p, precise (memory_block sh n p).
Proof.
  intros.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  destruct p; try apply FF_precise.
  apply precise_prop_andp.
  forget (nat_of_Z (Int.unsigned n)) as nn; clear n.
  forget (Int.unsigned i) as ii; clear i.
  generalize ii.
  induction nn; intros.
  + apply emp_precise.
  + simpl. 
    apply precise_sepcon.
    apply mapsto_precise.
    apply IHnn.
Qed.

Lemma at_offset'_preserve_precise: forall P, (forall p, precise (P p)) -> 
  forall be p, P (offset_val (Int.repr 0) p) = P p -> precise (at_offset' P be p).
Proof.
  intros.
  rewrite at_offset'_eq by auto.
  apply H.
Qed.

Lemma spacer_precise: forall sh be ed p, precise (spacer sh be ed p).
Proof.
  intros.
  unfold spacer.
  if_tac.
  apply emp_precise.
  apply at_offset'_preserve_precise; [intros; apply memory_block_precise |].
  apply memory_block_offset_zero.
Qed.

Lemma withspacer_preserve_precise: forall sh be ed P p,
  precise (P p) -> precise (withspacer sh be ed P p).
Proof.
  intros.
  rewrite withspacer_spacer.
Opaque spacer.
  simpl.
Transparent spacer.
  apply precise_sepcon.
  apply spacer_precise.
  exact H.
Qed.

Lemma array_at'_preserve_precise: forall t sh P v lo hi p,
  (forall v p, precise (P v p)) -> precise (array_at' t sh P v lo hi p).
Proof.
  intros.
  unfold array_at'.
  apply precise_prop_andp.
  unfold rangespec.
  forget (nat_of_Z (hi - lo)) as nn; clear hi.
  generalize lo.
  induction nn; intros; simpl.
  + apply emp_precise.
  + apply precise_sepcon.
    apply H.
    apply IHnn.
Qed.

Lemma data_at'_precise: forall sh env t ofs v p, precise (data_at' sh env t ofs v p).
Proof.
  intros.
  apply (type_mut (fun t => forall ofs v p, precise (data_at' sh env t ofs v p))
                  (fun tl => True)
                  (fun fld => (forall al ofs v p, precise (sfieldlist_at' sh env fld al ofs v p)) /\
                              (forall al ofs v p, precise (ufieldlist_at' sh env fld al ofs v p))));
  intros; auto; try simpl;
  try (unfold at_offset2; apply at_offset'_preserve_precise;
       [| try (apply memory_block_offset_zero);
          try (apply mapsto_offset_zero);
          try (symmetry; apply array_at'_offset_zero)]).
  + apply memory_block_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + intros; apply array_at'_preserve_precise.
    apply H.
  + apply memory_block_precise.
  + destruct H as [H _]; apply H.
  + destruct H as [_ H]; apply H.
  + apply mapsto_precise.
  + simpl; split; intros; apply precise_prop_andp, emp_precise.
  + destruct H0.
    split; intros; destruct (is_Fnil f).
    - apply withspacer_preserve_precise, H.
    - apply precise_sepcon.
      apply withspacer_preserve_precise, H.
      apply H0.
    - apply withspacer_preserve_precise, H.
    - destruct v0.
      apply withspacer_preserve_precise, H.
      apply H1.
Qed.

Lemma data_at_precise: forall sh t v p, precise (data_at sh t v p).
Proof.
  intros; unfold data_at.
  simpl.
  apply precise_prop_andp, data_at'_precise.
Qed.

Lemma field_at_precise: forall sh t ids v p, precise (field_at sh t ids v p).
Proof.
  intros; unfold field_at.
  simpl.
  apply precise_prop_andp, data_at'_precise.
Qed.

Lemma eq_rect_r_JMeq: forall (A:Type) (x y: A) F (v: F x) (H: y = x), JMeq (eq_rect_r F v H) v.
Proof.
  intros.
  subst.
  unfold eq_rect_r; rewrite <- eq_rect_eq.
  reflexivity.
Qed.

Lemma proj_reptype_cons_hd_Fnil: forall i i0 t0 a t id ids v,
  Pos.eqb i0 id = true ->
  nested_field_type2 t ids = Tstruct i (Fcons i0 t0 Fnil) a ->
  JMeq (proj_reptype t (id :: ids) v) (proj_reptype t ids v).
Proof.
  intros.
  simpl proj_reptype at 1.
  generalize (@eq_refl type (nested_field_type2 t ids)) as EQ.
  generalize (proj_reptype t ids v) as v0.
  pattern (nested_field_type2 t ids) at 1 3 4 16; rewrite H0.
  intros.
  simpl proj_reptype_structlist.
  generalize (@eq_refl bool (Pos.eqb i0 id)) as EQ1.
  pattern ((i0 =? id)%positive) at 2 3; rewrite H; intros.
  rewrite !eq_rect_r_JMeq.
  reflexivity.
Qed.

Lemma JMeq_fst: forall A B C D (x: A*B) (y: C*D), A = C -> B = D -> JMeq x y -> JMeq (fst x) (fst y).
Proof.
  intros.
  subst.
  apply JMeq_eq in H1.
  subst.
  reflexivity.
Qed.

Lemma proj_reptype_cons_hd_Fcons: forall i i0 t0 i1 t1 f a t id ids v 
  (v0: nested_reptype_structlist t ids (Fcons i0 t0 (Fcons i1 t1 f))),
  nested_legal_fieldlist t = true ->
  Pos.eqb i0 id = true ->
  nested_field_type2 t ids = Tstruct i (Fcons i0 t0 (Fcons i1 t1 f)) a ->
  JMeq (proj_reptype t ids v) v0 ->
  JMeq (proj_reptype t (id :: ids) v) (fst v0).
Proof.
  intros.
  simpl proj_reptype at 1.
  generalize (@eq_refl type (nested_field_type2 t ids)) as EQ.
  revert H2.
  generalize (proj_reptype t ids v) as v1.
  pattern (nested_field_type2 t ids) at 1 2 4 5; rewrite H1.
  intros.
  simpl proj_reptype_structlist.
  generalize (@eq_refl bool (Pos.eqb i0 id)) as EQ1.
  pattern ((i0 =? id)%positive) at 2 3. rewrite H0; intros.
  rewrite !eq_rect_r_JMeq.
  clear EQ EQ1.

  eapply JMeq_fst.
  + f_equal.
    erewrite nested_field_type2_hd; [reflexivity | eauto].
  + change (if is_Fnil f
            then reptype t1
            else (reptype t1 * reptype_structlist f)%type) with
      (reptype_structlist (Fcons i1 t1 f)).
    match goal with 
    | |- _ = ?A => change A with (nested_reptype_structlist t ids (Fcons i1 t1 f))
    end.
    unfold nested_field_type2 in H1.
    destruct (nested_field_rec t ids) as [[? ?]|] eqn:?; try inversion H1.
    eapply nested_reptype_structlist_lemma; eauto.
    instantiate (2:= Fcons i0 t0 Fnil).
    simpl.
    rewrite H3 in Heqo.
    exact Heqo.
  + exact H2.
Qed.

(*
Definition nested_sfieldlist_at: forall sh t id ids i f a0 vs v p t0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tstruct i f a0 ->
  field_type id f = Errors.OK t0 ->
  JMeq (proj_reptype t ids v) vs ->
  exists P, nested_sfieldlist_at sh t ids f vs p = 
  field_at sh t (id :: ids) (proj_reptype t (id :: ids) v) p * P.
Proof.
  intros.
  induction f.
  + inversion H1.
  + simpl in H1.
Opaque field_at proj_reptype spacer.
    if_tac in H1. (* whether id = the ident of head field *)
    - subst.
      clear IHf. 
      simpl nested_sfieldlist_at.
      destruct f.
      * simpl; rewrite withspacer_spacer; simpl.
        simpl in vs, H2.
        erewrite <- proj_reptype_cons_hd_Fnil in H2; [| apply Pos.eqb_eq; reflexivity | eauto].
        rewrite <- H2.
        rewrite sepcon_comm.
        eauto.
      * Opaque nested_sfieldlist_at. simpl.
        rewrite withspacer_spacer; simpl. Transparent nested_sfieldlist_at.
        rewrite sepcon_comm with (Q := field_at sh t (i0 :: ids) (fst vs) p).
        rewrite sepcon_assoc.
        replace (fst vs) with (proj_reptype t (i0 :: ids) v).
        eauto.
        apply JMeq_eq.
        eapply proj_reptype_cons_hd_Fcons; eauto.
        apply Pos.eqb_eq; reflexivity.
    - destruct f; try (solve [inversion H1]).
Print nested_sfieldlist_at.



Definition nested_field_sub_aux: forall sh t ids v p, 
  nested_legal_fieldlist t = true ->
  legal_alignas_type t = true ->
  isSome (nested_field_type t ids) ->
  exists P, data_at sh t v p = field_at sh t ids (proj_reptype t ids v) p * P.
Proof.
  intros.
  induction ids.
  + exists emp.
    rewrite sepcon_emp.
    rewrite data_at_field_at.
    simpl.
    unfold eq_rect_r.
    rewrite <- eq_rect_eq.
    reflexivity.
  + unfold nested_field_type in *; simpl in H1.
    destruct (nested_field_rec t ids) as [[ofs0 t0] |] eqn:?; try inversion H1.
    destruct t0; try inversion H1.
    - solve_field_offset_type a f; inversion H1.
      destruct (IHids I) as [P ?].
      rewrite H2.
      assert (nested_field_type2 t ids = Tstruct i f a0) 
        by (unfold nested_field_type2; rewrite Heqo; reflexivity).

      erewrite field_at_Tstruct with (ids := ids); eauto.
  

      simpl proj_reptype.
      generalize (@eq_refl type (nested_field_type2 t ids)) as EQ.
Set Printing All.
      pattern (nested_field_type2 t ids) at 2 3.
      rewrite H5 at 1.
Check nested_sfieldlist_at.
SearchAbout nested_reptype_structlist.



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