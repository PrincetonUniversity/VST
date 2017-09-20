Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.composite_compute.

(* This file contains three computational align criteria.
   1: the hardware alignof is not larger than alignof.
   2: all fields are aligned as hardware requires. size as a multiple of hardware alignof.
   3: all value is well-aligned stored.
   The third one is the final specification we want. *)

Section align_compatiable_rec.

Context (cenv: composite_env).

Inductive align_compatiable_rec: type -> Z -> Prop :=
| align_compatiable_rec_by_value: forall t ch z, access_mode t = By_value ch -> (Memdata.align_chunk ch | z) -> align_compatiable_rec t z
| align_compatiable_rec_Tarray: forall t n a z, (forall i, 0 <= i < n -> align_compatiable_rec t (z + sizeof cenv t * i)) -> align_compatiable_rec (Tarray t n a) z
| align_compatiable_rec_Tstruct: forall i a co z, cenv ! i = Some co -> (forall i0 t0 z0, field_type i0 (co_members co) = Errors.OK t0 -> field_offset cenv i0 (co_members co) = Errors.OK z0 -> align_compatiable_rec t0 (z + z0)) -> align_compatiable_rec (Tstruct i a) z
| align_compatiable_rec_Tunion: forall i a co z, cenv ! i = Some co -> (forall i0 t0, field_type i0 (co_members co) = Errors.OK t0 -> align_compatiable_rec t0 z) -> align_compatiable_rec (Tunion i a) z.

End align_compatiable_rec.

Fixpoint hardware_alignof (ha_env: PTree.t Z) t: Z :=
  match t with
  | Tarray t' _ _ => hardware_alignof ha_env t'
  | Tstruct id _ =>
      match ha_env ! id with
      | Some ha => ha
      | None => 1
      end
  | Tunion id _ =>
      match ha_env ! id with
      | Some ha => ha
      | None => 1
      end
  | _ => match access_mode t with
         | By_value ch => Memdata.align_chunk ch
         | _ => 1
         end
  end.

Fixpoint hardware_alignof_composite (ha_env: PTree.t Z) (m: members): Z :=
  match m with
  | nil => 1
  | (_, t) :: m' => Z.max (hardware_alignof ha_env t) (hardware_alignof_composite ha_env m')
  end.

Definition hardware_alignof_env (cenv: composite_env): PTree.t Z :=
  let l := composite_reorder.rebuild_composite_elements cenv in
  fold_right (fun (ic: positive * composite) (T0: PTree.t Z) => let (i, co) := ic in let T := T0 in PTree.set i (hardware_alignof_composite T (co_members co)) T) (PTree.empty _) l.

Module Type HARDWARE_ALIGNOF_FACTS.

  Axiom hardware_alignof_consistent:
    forall (cenv: composite_env) (ha_env: PTree.t Z),
      composite_env_consistent cenv ->
      ha_env = hardware_alignof_env cenv ->
      forall i co ha,
        cenv ! i = Some co ->
        ha_env ! i = Some ha ->
        ha = hardware_alignof_composite ha_env (co_members co).

  Axiom hardware_alignof_complete:
    forall (cenv: composite_env) (ha_env: PTree.t Z),
      ha_env = hardware_alignof_env cenv ->
      forall i,
        (exists co, cenv ! i = Some co) <->
        (exists ha, ha_env ! i = Some ha).

End HARDWARE_ALIGNOF_FACTS.

Module hardware_alignof_facts: HARDWARE_ALIGNOF_FACTS.

Lemma aux1: forall T co,
  (fix fm (l : list (ident * Z)) : Z :=
     match l with
     | nil => 1
     | (_, ha) :: l' => Z.max ha (fm l')
     end)
    (map
       (fun it0 : positive * type =>
        let (i0, t0) := it0 in
        (i0,
        type_func.F
          (fun t : type =>
           match access_mode t with
           | By_value ch => align_chunk ch
           | By_reference => 1
           | By_copy => 1
           | By_nothing => 1
           end) (fun (ha _ : Z) (_ : attr) => ha) (fun (ha : Z) (_ : attr) => ha)
          (fun (ha : Z) (_ : attr) => ha) T t0)) (co_members co)) =
                    hardware_alignof_composite T (co_members co).
Proof.
  intros; unfold hardware_alignof_composite, hardware_alignof.
  induction (co_members co) as [| [i t] ?].
  + auto.
  + simpl.
    f_equal; auto.
    clear.
    induction t; auto.
Qed.

Lemma aux2: forall (cenv: composite_env),
  type_func.Env
          (fun t : type =>
           match access_mode t with
           | By_value ch => align_chunk ch
           | By_reference => 1
           | By_copy => 1
           | By_nothing => 1
           end) (fun (ha _ : Z) (_ : attr) => ha) (fun (ha : Z) (_ : attr) => ha)
          (fun (ha : Z) (_ : attr) => ha)
          (fun _ : struct_or_union =>
           fix fm (l : list (ident * Z)) : Z :=
             match l with
             | nil => 1
             | (_, ha) :: l' => Z.max ha (fm l')
             end) (composite_reorder.rebuild_composite_elements cenv) =
  hardware_alignof_env cenv.
Proof.
  intros.
  unfold type_func.Env, type_func.env_rec, hardware_alignof_env.
  f_equal.
  extensionality ic.
  destruct ic as [i co].
  extensionality T.
  f_equal.
  apply aux1.
Qed.

Lemma hardware_alignof_consistent (cenv: composite_env) (ha_env: PTree.t Z):
  composite_env_consistent cenv ->
  ha_env = hardware_alignof_env cenv ->
  forall i co ha,
    cenv ! i = Some co ->
    ha_env ! i = Some ha ->
    ha = hardware_alignof_composite ha_env (co_members co).
Proof.
  intros.
  pose proof @composite_reorder_consistent Z cenv
             (fun t =>
                match access_mode t with
                | By_value ch => Memdata.align_chunk ch
                | _ => 1
                end)
             (fun ha _ _ => ha)
             (fun ha _ => ha)
             (fun ha _ => ha)
             (fun _ =>
                fix fm (l: list (ident * Z)): Z :=
                match l with
                | nil => 1
                | (_, ha) :: l' => Z.max ha (fm l')
                end)
             H
    as HH.
  hnf in HH.
  subst ha_env.
  rewrite aux2 in HH.
  specialize (HH _ _ ha H1 H2).
  rewrite HH, aux1; auto.
Qed.

Lemma hardware_alignof_complete (cenv: composite_env) (ha_env: PTree.t Z):
  ha_env = hardware_alignof_env cenv ->
  forall i,
    (exists co, cenv ! i = Some co) <->
    (exists ha, ha_env ! i = Some ha).
Proof.
  intros.
  pose proof @composite_reorder_complete Z cenv
             (fun t =>
                match access_mode t with
                | By_value ch => Memdata.align_chunk ch
                | _ => 1
                end)
             (fun ha _ _ => ha)
             (fun ha _ => ha)
             (fun ha _ => ha)
             (fun _ =>
                fix fm (l: list (ident * Z)): Z :=
                match l with
                | nil => 1
                | (_, ha) :: l' => Z.max ha (fm l')
                end)
    as HH.
  hnf in HH.
  subst.
  rewrite aux2 in HH.
  auto.
Qed.

End hardware_alignof_facts.

Section legal_alignas_l1.

Context (cenv: composite_env) (ha_env: PTree.t Z).

Fixpoint legal_alignas_l1 (la1_env: PTree.t bool) t: bool :=
  (hardware_alignof ha_env t <=? alignof cenv t) &&
  match t with
  | Tarray t' _ _ => legal_alignas_l1 la1_env t'
  | Tstruct id _ =>
      match la1_env ! id with
      | Some la1 => la1
      | None => false
      end
  | Tunion id _ =>
      match la1_env ! id with
      | Some la1 => la1
      | None => false
      end
  | _ => match access_mode t with
         | By_value ch => true
         | _ => false
         end
  end.

Fixpoint legal_alignas_l1_composite (la1_env: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => (legal_alignas_l1 la1_env t) && (legal_alignas_l1_composite la1_env m')
  end.

Definition legal_alignas_l1_env: PTree.t bool :=
  let l := composite_reorder.rebuild_composite_elements cenv in
  fold_right (fun (ic: positive * composite) (T0: PTree.t bool) => let (i, co) := ic in let T := T0 in PTree.set i (legal_alignas_l1_composite T (co_members co)) T) (PTree.empty _) l.

End legal_alignas_l1.

















Lemma plain_alignof_spec: forall env t,
  alignof env t = align_attr (attr_of_type t) (plain_alignof env t).
Proof.
  intros.
  destruct t; auto.
Qed.

Lemma plain_alignof_two_p: forall env t, exists n,
  plain_alignof env t = two_power_nat n.
Proof.
  intros.
  destruct t as [| []  ? ? | | [] ? | | | | |];
  try solve [exists 0%nat; reflexivity | exists 1%nat; reflexivity | exists 2%nat; reflexivity].
  + simpl.
    apply alignof_two_p.
  + simpl.
    destruct (env ! i); [apply co_alignof_two_p | exists 0%nat; auto].
  + simpl.
    destruct (env ! i); [apply co_alignof_two_p | exists 0%nat; auto].
Qed.

Definition local_legal_alignas_type env (t: type): bool :=
  Z.leb (plain_alignof env t) (alignof env t) &&
  match t with
  | Tarray t' n a => Z.eqb ((sizeof env t') mod (alignof env t')) 0 && Z.leb 0 n
  | Tlong _ _ => Z.leb 8 (alignof env t)
  | _ => true
  end.

Lemma local_legal_alignas_type_spec: forall env t,
  local_legal_alignas_type env t = true ->
  (plain_alignof env t | alignof env t).
Proof.
  intros.
  apply andb_true_iff in H.
  destruct H as [? _].
  apply Zle_is_le_bool in H.
  apply power_nat_divide'; [apply alignof_two_p | apply plain_alignof_two_p | omega].
Qed.

Lemma align_chunk_alignof: forall env t ch, local_legal_alignas_type env t = true -> access_mode t = By_value ch -> (Memdata.align_chunk ch | alignof env t).
Proof.
  intros.
  destruct t; inversion H0.
  - eapply Z.divide_trans; [| apply local_legal_alignas_type_spec; auto].
    destruct i, s; inversion H2; simpl; unfold align_attr;
    destruct (attr_alignas a); reflexivity.
  - unfold local_legal_alignas_type in H.
    rewrite andb_true_iff in H; destruct H as [_ ?].
    apply Zge_is_le_bool in H.
    apply power_nat_divide' in H.
    * auto.
    * apply alignof_two_p.
    * exists 3%nat; auto.
  - eapply Z.divide_trans; [| apply local_legal_alignas_type_spec; auto].
    destruct f; inversion H2; simpl; unfold align_attr;
    destruct (attr_alignas a); reflexivity.
  - eapply Z.divide_trans; [| apply local_legal_alignas_type_spec; auto].
    inversion H2; simpl; unfold align_attr;
    destruct (attr_alignas a); reflexivity.
Qed.

Definition composite_legal_alignas (env : composite_env) (co : composite) : Prop :=
  (co_alignof co >= alignof_composite env (co_members co)).

Definition composite_env_legal_alignas env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_alignas env co.

