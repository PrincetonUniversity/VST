Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.fieldlist.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Open Scope Z.

Module Type ACR_DEC.

  Parameter align_compatible_rec_dec:
    forall {cs: compspecs},
      forall t z, {align_compatible_rec cenv_cs t z} + {~ align_compatible_rec cenv_cs t z}.

End ACR_DEC.

Module align_compatible_rec_dec: ACR_DEC.

Section align_compatible_rec_dec.

Context {cs: compspecs}.

Definition dec_type := sigT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}).

Definition dec_by_value (ch: memory_chunk): dec_type :=
  existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => (Memdata.align_chunk ch | z)) (fun z => Zdivide_dec (Memdata.align_chunk ch) z (Memdata.align_chunk_pos _)).

Definition dec_False: dec_type :=
  existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => False) (fun z => right (fun H => H)).

Definition dec_True: dec_type :=
  existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => True) (fun z => left I).
(*
Definition dec_aux_struct_field (denv: PTree.t dec_type) (i: positive) (m: members): dec_type :=
  match field_type i m, field_offset cenv_cs i m with
  | Errors.OK t, Errors.OK ofs => existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => projT1 (dec_aux denv t) (z + ofs)) (fun z => projT2 (dec_aux denv t) (z + ofs))
  | _, _ => dec_False
  end.

Definition dec_aux_union_field (denv: PTree.t dec_type) (i: positive) (m: members): dec_type :=
  match field_type i m with
  | Errors.OK t => dec_aux denv t
  | _ => dec_False
  end.

Fixpoint dec_aux_struct_composite (denv: PTree.t dec_type) (m_rec m: members): dec_type :=
  match m_rec with
  | nil => dec_True
  | (i, _) :: m_rec' => existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => projT1 (dec_aux_struct_field denv i m) z /\ projT1 (dec_aux_struct_composite denv m_rec' m) z) (fun z => sumbool_dec_and (projT2 (dec_aux_struct_field denv i m) z) (projT2 (dec_aux_struct_composite denv m_rec' m) z))
  end.

Fixpoint dec_aux_union_composite (denv: PTree.t dec_type) (m_rec m: members): dec_type :=
  match m_rec with
  | nil => dec_True
  | (i, _) :: m_rec' => existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => projT1 (dec_aux_union_field denv i m) z /\ projT1 (dec_aux_union_composite denv m_rec' m) z) (fun z => sumbool_dec_and (projT2 (dec_aux_union_field denv i m) z) (projT2 (dec_aux_union_composite denv m_rec' m) z))
  end.


Definition dec_aux: type -> dec_type.
  refine (type_func (fun _ => dec_type) _ _ _ _).
  + intro t.
    exact (match access_mode t with
           | By_value ch => dec_by_value ch
           | _ => dec_False
           end).
  + intros t' n _ d.
    exact (existT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z}) (fun z => forall i, 0 <= i < n -> projT1 d (z + sizeof t' * i)) (fun z => Zrange_pred_dec (fun i => projT1 d (z + sizeof t' * i)) (fun i => projT2 d (z + sizeof t' * i)) 0 n)).
  + intros id _ D.
    unfold FT_aux in D.
    


Definition dec_aux_composite (denv: PTree.t dec_type) (su: struct_or_union) (m: members): dec_type :=
  match su with
  | Struct => dec_aux_struct_composite denv m m
  | Union => dec_aux_union_composite denv m m
  end.

Definition dec_aux_env : PTree.t dec_type :=
  let l := composite_reorder.rebuild_composite_elements cenv in
  fold_right (fun (ic: positive * composite) (T0: PTree.t dec_type) => let (i, co) := ic in let T := T0 in PTree.set i (dec_aux_composite T (co_su co) (co_members co)) T) (PTree.empty _) l.

 *)

Lemma align_compatible_rec_dec: forall t z, {align_compatible_rec cenv_cs t z} + {~ align_compatible_rec cenv_cs t z}.
Admitted.

End align_compatible_rec_dec.

End align_compatible_rec_dec.

Lemma align_compatible_dec: forall {cs: compspecs} t p, {align_compatible t p} + {~ align_compatible t p}.
Proof.
  intros.
  destruct p; try solve [left; unfold align_compatible; simpl; tauto].
  simpl.
  apply align_compatible_rec_dec.align_compatible_rec_dec.
Qed.

