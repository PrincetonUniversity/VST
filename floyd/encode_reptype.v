Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.type_induction.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Import VST.floyd.aggregate_pred.auxiliary_pred.
Require Import VST.floyd.reptype_lemmas.
Require Export VST.floyd.fieldlist.
Require Import VST.floyd.simple_data_at_rec_lemmas.

(* convert a reptype into bytes *)

Section mpred.
  Context `{!heapGS Σ} {cs: compspecs}.

  #[local] Opaque Ctypes.field_type.

  Definition struct_encode_aux (m m0: members) (sz: Z)
       (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> list memval) m))
       (v: compact_prod (map (fun it => reptype (field_type (name_member it) m0)) m)) : list memval.
  Proof.
    destruct m as [| a0 m]; [exact [] |].
    revert a0 v P; induction m as [| a0 m]; intros ? v P.
    + simpl in v, P.
      inversion P; subst.
      exact (X v ++ Zrepeat Undef (field_offset_next cenv_cs (name_member a0) m0 sz - (field_offset cenv_cs (name_member a0) m0 + sizeof (field_type (name_member a0) m0)))).
    + simpl in v, P.
      inversion P; subst.
      exact (X (fst v) ++ Zrepeat Undef (field_offset_next cenv_cs (name_member a1) m0 sz - (field_offset cenv_cs (name_member a1) m0 + sizeof (field_type (name_member a1) m0))) ++
        IHm a0 (snd v) X0).
  Defined.

  Definition struct_encode (m: members) {A : member → Type} (P : ∀ it, A it → list memval) (v: compact_prod (map A m)) : list memval.
  Proof.
    destruct m as [| a m]; [exact [] | ].
    revert a v; induction m as [| b m]; intros ? v.
    + simpl in v.
      exact (P _ v).
    + simpl in v.
      exact (P _ (fst v) ++ IHm _ (snd v)).
  Defined.

  Lemma struct_encode_aux_spec: forall m m0 sz v P,
    struct_encode_aux m m0 sz
      (hmap (fun it => reptype (field_type (name_member it) m0) -> list memval) P m) v =
    struct_encode m (fun it v => P it v ++
      Zrepeat Undef (field_offset_next cenv_cs (name_member it) m0 sz - (field_offset cenv_cs (name_member it) m0 + sizeof (field_type (name_member it) m0)))) v.
  Proof.
    intros.
    destruct m as [| a0 m]; [reflexivity |].
    revert a0 v; induction m as [| a0 m]; intros.
    + reflexivity.
    + change (struct_encode_aux (a1 :: a0 :: m) m0 sz
     (hmap (fun it : member => reptype (field_type (name_member it) m0) -> list memval)
        P (a1 :: a0 :: m)) v) with
     (P a1 (fst v) ++ Zrepeat Undef (field_offset_next cenv_cs (name_member a1) m0 sz - (field_offset cenv_cs (name_member a1) m0 + sizeof (field_type (name_member a1) m0))) ++
      struct_encode_aux (a0 :: m) m0 sz
        (hmap (fun it : member => reptype (field_type (name_member it) m0) -> list memval)
        P (a0 :: m)) (snd v)).
      rewrite IHm app_assoc //.
  Qed.

  Definition union_encode_aux (m m0: members) (sz: Z)
      (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> list memval) m))
      (v: compact_sum (map (fun it => reptype (field_type (name_member it) m0)) m)) : list memval.
  Proof.
    destruct m as [| a0 m]; [exact [] |].
    revert a0 v P; induction m as [| a0 m]; intros ? v P.
    + simpl in v, P.
      inversion P; subst.
      exact (X v ++ Zrepeat Undef (sz - sizeof (field_type (name_member a0) m0))).
    + simpl in v, P.
      inversion P; subst.
      destruct v as [v | v].
      - exact (X v ++ Zrepeat Undef (sz - sizeof (field_type (name_member a1) m0))).
      - exact (IHm a0 v X0).
  Defined.

  Definition union_encode (m: members) {A : member → Type} (P : ∀ it, A it → list memval) (v: compact_sum (map A m)) : list memval.
  Proof.
    destruct m as [| a m]; [exact [] | ].
    revert a v; induction m as [| b m]; intros ? v.
    + simpl in v.
      exact (P _ v).
    + simpl in v.
      destruct v as [v | v].
      - exact (P _ v).
      - exact (IHm _ v).
  Defined.

  Lemma union_encode_aux_spec: forall m m0 sz v P,
    union_encode_aux m m0 sz
      (hmap (fun it => reptype (field_type (name_member it) m0) -> list memval) P m) v =
    union_encode m (fun it v => P it v ++
      Zrepeat Undef (sz - sizeof (field_type (name_member it) m0))) v.
  Proof.
    intros.
    destruct m as [| a0 m]; [reflexivity |].
    revert a0 v; induction m as [| a0 m]; intros.
    + reflexivity.
    + destruct v as [v | v].
      - reflexivity.
      - match goal with
        | _ => apply IHm
        | _ => simpl; f_equal; apply IHm
        end.
  Qed.

  Definition encode_reptype: forall t, reptype t -> list memval :=
    type_func (fun t => reptype t -> list memval)
      (fun t v => match access_mode t with By_value ch => encode_val ch (repinject t v) | _ => Zrepeat Undef (sizeof t) end)
      (fun t n a P v => flat_map P (resize (Z.to_nat n) (default_val t) (unfold_reptype v)))
      (fun id a P v => struct_encode_aux (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v))
      (fun id a P v => union_encode_aux (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v)).

  Lemma encode_reptype_eq: forall t v,
    encode_reptype t v =
    match t return REPTYPE t -> list memval with
    | Tvoid
    | Tfunction _ _ _ => fun _ => [Undef]
    | Tint _ _ _
    | Tfloat _ _
    | Tlong _ _
    | Tpointer _ _ => fun v => match access_mode t with By_value ch => encode_val ch v | _ => Zrepeat Undef (sizeof t) end
    | Tarray t0 n a => fun v => flat_map (encode_reptype t0) (resize (Z.to_nat n) (default_val t0) v)
    | Tstruct id a => struct_encode (co_members (get_co id)) (fun it v => encode_reptype (field_type (name_member it) (co_members (get_co id))) v ++
        Zrepeat Undef (field_offset_next cenv_cs (name_member it) (co_members (get_co id)) (co_sizeof (get_co id)) -
          (field_offset cenv_cs (name_member it) (co_members (get_co id)) + sizeof (field_type (name_member it) (co_members (get_co id))))))
    | Tunion id a => union_encode (co_members (get_co id)) (fun it v => encode_reptype (field_type (name_member it) (co_members (get_co id))) v ++
        Zrepeat Undef ((co_sizeof (get_co id)) - sizeof (field_type (name_member it) (co_members (get_co id)))))
    end (unfold_reptype v).
  Proof.
    intros.
    unfold encode_reptype at 1.
    rewrite type_func_eq.
    destruct t; auto.
    + rewrite <- struct_encode_aux_spec; reflexivity.
    + rewrite <- union_encode_aux_spec; reflexivity.
  Qed.

  Lemma encode_val_Zlength: forall ch v, Zlength (encode_val ch v) = size_chunk ch.
  Proof.
    intros; rewrite Zlength_correct encode_val_length /size_chunk_nat Z2Nat.id //.
    pose proof (size_chunk_pos ch); lia.
  Qed.

  Lemma flat_map_constant_Zlength: forall [A B] [c] (f : A -> list B) l,
    (forall x, In x l -> Zlength (f x) = c) ->
    Zlength (flat_map f l) = Zlength l * c.
  Proof.
    intros.
    destruct l; first done.
    assert (0 <= c).
    { specialize (H a); spec H; simpl; list_solve. }
    rewrite !Zlength_correct (flat_map_constant_length(c := Z.to_nat c)).
    - rewrite Nat2Z.inj_mul Z2Nat.id //.
    - intros x ?; rewrite -(H x) // Zlength_correct Nat2Z.id //.
  Qed.

(*  Lemma struct_encode_Zlength: forall m {A} P (v: compact_prod (map A m))
    (HP: forall it v, Zlength (P it v) = bytes_of_bits (next_field cenv_cs 0 it)),
    Zlength (struct_encode m P v) = Ctypes.sizeof_struct cenv_cs m.
  Proof.
    destruct m as [|a0 m]; first done.
    revert a0; induction m as [|a0 m]; intros; simpl; auto.
    rewrite Zlength_app HP IHm //=.
    rewrite /Ctypes.sizeof_struct /=.
Search next_field.
  Admitted.

  Lemma encode_size: forall t v, Zlength (encode_reptype t v) = sizeof t.
  Proof.
    intros t; type_induction t; intros; rewrite encode_reptype_eq //.
    - destruct (access_mode _) eqn: Hch; rewrite ?Zlength_Zrepeat //; try by pose proof (sizeof_pos (Tint i s a)); lia.
      rewrite encode_val_Zlength.
      symmetry; by apply size_chunk_sizeof.
    - rewrite /= encode_val_Zlength //.
    - destruct (access_mode _) eqn: Hch; rewrite ?Zlength_Zrepeat //; try by pose proof (sizeof_pos (Tfloat f a)); lia.
      rewrite encode_val_Zlength.
      symmetry; by apply size_chunk_sizeof.
    - rewrite /= encode_val_Zlength //.
    - rewrite (flat_map_constant_Zlength (c := sizeof t)) //=.
      rewrite Zlength_correct length_resize Z_to_nat_max.
      rewrite /sizeof Z.max_comm; lia.
    - rewrite sizeof_Tstruct co_consistent_sizeof; last apply get_co_consistent.
      rewrite /unfold_reptype.
      Search sizeof_composite align.
      destruct (co_su (get_co id)) eqn: Hsu.
      + rewrite divide_align.
simpl sizeof_composite.
Search align Z.divide.
co_sizeof_alignof
Search co_alignof.
Search Ctypes.sizeof align.
        rewrite struct_encode_Zlength //. *)

  (* This can't be true in general, but might be true under certain conditions (no volatiles, no void or function, ... 
  Lemma encode_data_at: forall sh t v b o, data_at_rec sh t v (Vptr b o) ⊣⊢ [∗ list] i ↦ v ∈ encode_reptype t v, adr_add (b, Ptrofs.unsigned o) i ↦{#sh} VAL v.
  Proof.
    intros sh t; type_induction t; intros; rewrite data_at_rec_eq encode_reptype_eq //.
  *)

End mpred.
