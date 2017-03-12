Require Import AggregateType.demo2.expr.
Require Import AggregateType.demo2.computable_theorems.
Require Import AggregateType.demo2.type_induction.
Require Import AggregateType.demo2.prod_lemmas.

Section TypeRecFunctions.

Context {cs: compspecs}.

Definition reptype_gen: type -> (sigT (fun x => x)) :=
  type_func (fun _ => (sigT (fun x => x)))
  (fun t =>
     match t with
     | Tint => existT (fun x => x) val Vundef
     | Tstruct _ => existT (fun x => x) unit tt
     end)
  (fun id TVs => existT (fun x => x) (list_prod_sigT_type (decay TVs)) (list_prod_sigT_value (decay TVs))).

Definition reptype t: Type := match reptype_gen t with existT t _ => t end.

Definition default_val t: reptype t :=
  match reptype_gen t as tv
    return match tv with existT t _ => t end
  with existT t v => v end.

Lemma reptype_gen_eq: forall t,
  reptype_gen t =
  match t with
  | Tstruct id => existT (fun x => x)
                     (list_prod_sigT_type (map reptype_gen (map (fun it => field_type (fst it) (co_members (get_co id))) (co_members (get_co id)))))
                     (list_prod_sigT_value (map reptype_gen (map (fun it => field_type (fst it) (co_members (get_co id))) (co_members (get_co id)))))
  | Tint => existT (fun x => x) val Vundef
  end.
Proof.
  intros.
  unfold reptype_gen at 1.
  rewrite type_func_ind.
  destruct t; auto.
  + unfold FTI_aux; rewrite decay_spec.
    rewrite map_map.
    reflexivity.
Defined.

Definition reptype_members (m: members) := list_prod (map (fun it => reptype (field_type (fst it) m)) m).

Notation REPTYPE t :=
  match t return Type with
  | Tint => val
  | Tstruct id => reptype_members (co_members (get_co id))
  end.

Lemma reptype_eq: forall t,
  reptype t = REPTYPE t.
Proof.
  intros.
  unfold reptype.
  rewrite reptype_gen_eq.
  destruct t as [| id]; auto.

  unfold list_prod_sigT_type.
  rewrite map_map.
  rewrite map_map.
  unfold reptype_members.
  reflexivity.
Defined.

Definition unfold_reptype {t} (v: reptype t): REPTYPE t :=
  @eq_rect Type (reptype t) (fun x: Type => x) v (REPTYPE t) (reptype_eq t).

Definition fold_reptype {t} (v: REPTYPE t): reptype t :=
  @eq_rect_r Type (REPTYPE t) (fun x: Type => x) v (reptype t) (reptype_eq t).

Definition struct_default_val (m : members) := list_prod_gen (fun it => default_val (field_type (fst it) m)) m.

Lemma default_val_eq: forall t,
  default_val t =
  fold_reptype
  match t as t_PAT return REPTYPE t_PAT with
  | Tint => Vundef
  | Tstruct id => struct_default_val (co_members (get_co id))
  end.
Proof.
  intros.
  unfold fold_reptype.
  generalize (reptype_eq t).
  unfold default_val, reptype.
  rewrite (reptype_gen_eq t).
  destruct t.
  + intros.
    unfold eq_rect_r; rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq.
    auto.
  + unfold struct_default_val.
    rewrite map_map.
    apply list_prod_sigT_value_list_prod_gen.
Qed.

Definition repinject (t: type): reptype t -> val :=
  match t as t_PAT return reptype t_PAT -> val with
  | Tint => fun v => v
  | _ => fun _ => Vundef
  end.

Definition at_offset (P: val -> Pred) (z: Z): val -> Pred :=
 fun v => P (offset_val z v).

Fixpoint struct_pred (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> Pred): list_prod (map A m) -> val -> Pred :=
  match m as m_PAT return list_prod (map A m_PAT) -> val -> Pred with
  | nil => fun _ _ => emp
  | (i0, t0) :: m0 => fun v p => (P _ (fst v) p * struct_pred m0 P (snd v) p)%logic
  end.

Definition struct_data_at_rec_aux (m m0: members) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> Pred)) m)) (v: list_prod (map (fun it => reptype (field_type (fst it) m0)) m)) : (val -> Pred).
Proof.
  induction m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  simpl in v, P.
  inversion P; subst.
  exact (at_offset (a (fst v)) (field_offset cenv_cs i0 m0) * IHm b (snd v))%logic.
Defined.

Lemma struct_data_at_rec_aux_spec: forall m m0 v P,
  struct_data_at_rec_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> Pred)
     P m) v =
  struct_pred m
   (fun it v => at_offset (P it v) (field_offset cenv_cs (fst it) m0)) v.
Proof.
  intros.
  induction m as [| (i0, t0) m]; [reflexivity |].
  replace
   (struct_data_at_rec_aux ((i0, t0) :: m) m0
     (ListTypeGen (fun it : ident * type => reptype (field_type (fst it) m0) -> val -> Pred)
        P ((i0, t0) :: m)) v) with
   (at_offset (P (i0, t0) (fst v)) (field_offset cenv_cs i0 m0) *
      struct_data_at_rec_aux m m0
       (ListTypeGen (fun it : ident * type => reptype (field_type (fst it) m0) -> val -> Pred)
          P m) (snd v))%logic.
  - rewrite IHm.
    reflexivity.
  - simpl.
    destruct (ident_eq i0 i0); [| congruence].
    reflexivity.
Qed.

Definition data_at_rec: forall t, reptype t -> val -> Pred :=
  type_func (fun t => reptype t -> val -> Pred)
    (fun t v p => mapsto p (repinject t v))
    (fun id P v => struct_data_at_rec_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v)).

Lemma data_at_rec_eq: forall t v,
  data_at_rec t v =
  match t return REPTYPE t -> val -> Pred with
  | Tint => fun v p => mapsto p v
  | Tstruct id => struct_pred (co_members (get_co id))
                      (fun it v => at_offset (data_at_rec (field_type (fst it) (co_members (get_co id))) v) (field_offset cenv_cs (fst it) (co_members (get_co id))))
  end (unfold_reptype v).
Proof.
  intros.
  unfold data_at_rec at 1.
  rewrite type_func_ind.
  destruct t.
  + auto.
  + rewrite <- struct_data_at_rec_aux_spec; reflexivity.
Qed.

End TypeRecFunctions.

Notation REPTYPE t :=
  match t return Type with
  | Tint => val
  | Tstruct id => reptype_members (co_members (get_co id))
  end.




