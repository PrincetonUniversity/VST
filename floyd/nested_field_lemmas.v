Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.type_id_env.

(************************************************

Definition, lemmas and useful samples of nested_pred

nested_pred only ensure the specific property to be true on nested types with
memory assigned, i.e. inside structure of pointer, function, empty array are
not included.

************************************************)

Fixpoint nested_pred (atom_pred: type -> bool) (t: type) : bool :=
  match t with
  | Tarray t0 n _ => (atom_pred t && (nested_pred atom_pred t0 || Z.leb n 0))%bool
  | Tstruct _ flds _ => (atom_pred t && nested_fields_pred atom_pred flds)%bool
  | Tunion _ flds _ => (atom_pred t && nested_fields_pred atom_pred flds)%bool
  | _ => atom_pred t
  end
with nested_fields_pred (atom_pred: type -> bool) (f: fieldlist) : bool :=
  match f with 
  | Fnil => true 
  | Fcons _ t f' => (nested_pred atom_pred t && nested_fields_pred atom_pred f')%bool
  end.

Lemma nested_pred_atom_pred: forall {atom_pred: type -> bool} (t: type),
  nested_pred atom_pred t = true -> atom_pred t = true.
Proof.
  intros.
  destruct t; simpl in *; try apply andb_true_iff in H; try tauto.
Defined.

Lemma nested_pred_Tarray: forall {atom_pred: type -> bool} t n a,
  nested_pred atom_pred (Tarray t n a) = true -> n > 0 -> nested_pred atom_pred t = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H.
  destruct H.
  apply orb_true_iff in H1.
  destruct H1.
  + exact H1.
  + apply Zle_is_le_bool in H1.
    omega.
Defined.

Lemma nested_pred_Tstruct: forall {atom_pred: type -> bool} i f a, nested_pred atom_pred (Tstruct i f a) = true -> nested_fields_pred atom_pred f = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_pred_Tunion: forall {atom_pred: type -> bool} i f a, nested_pred atom_pred (Tunion i f a) = true -> nested_fields_pred atom_pred f = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_fields_pred_hd: forall {atom_pred: type -> bool} i t f,
  nested_fields_pred atom_pred (Fcons i t f) = true ->
  nested_pred atom_pred t = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_fields_pred_tl: forall {atom_pred: type -> bool} i t f,
  nested_fields_pred atom_pred (Fcons i t f) = true ->
  nested_fields_pred atom_pred f = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_fields_pred_nested_pred: forall {atom_pred: type -> bool} i t f, field_type i f = Errors.OK t -> nested_fields_pred atom_pred f = true -> nested_pred atom_pred t = true.
Proof.
  intros.
  induction f.
  + inversion H.
  + simpl in H.
    if_tac in H; simpl in H0.
    - apply andb_true_iff in H0.
      inversion H.
      subst.
      tauto.
    - apply andb_true_iff in H0.
      destruct H0.
      apply IHf; assumption.
Defined.

(******* Samples : legal_alignas_type *************)

Definition local_legal_alignas_type (t: type): bool :=
  match t with
  | Tvoid            => true
  | Tint _ _ a       => match attr_alignas a with | None => true | _ => false end
  | Tlong _ a        => match attr_alignas a with | None => true | _ => false end
  | Tfloat _ a       => match attr_alignas a with | None => true | _ => false end
  | Tpointer _ a     => match attr_alignas a with | None => true | _ => false end
  | Tfunction _ _ _  => true
  | Tarray t _ a     => match attr_alignas a with | None => true | _ => false end
  | Tstruct _ flds a => 
      match attr_alignas a with
      | None => true 
      | Some l => Z.leb (alignof_fields flds) (two_p (Z.of_N l))
      end
  | Tunion _ flds a  =>
      match attr_alignas a with
      | None => true 
      | Some l => Z.leb (alignof_fields flds) (two_p (Z.of_N l))
      end
  | Tcomp_ptr _ a    => match attr_alignas a with | None => true | _ => false end
  end.

Definition legal_alignas_type := nested_pred local_legal_alignas_type.

Hint Extern 0 (legal_alignas_type _ = true) => reflexivity : cancel.

Lemma local_legal_alignas_type_Tarray: forall t z a,
  local_legal_alignas_type (Tarray t z a) = true ->
  alignof (Tarray t z a) = alignof t.
Proof.
  intros.
  simpl.
  simpl in H.
  destruct (attr_alignas a).
  + inversion H.
  + reflexivity.
Qed.

Lemma local_legal_alignas_type_Tstruct: forall i f a,
  local_legal_alignas_type (Tstruct i f a) = true ->
  (alignof_fields f | alignof (Tstruct i f a)).
Proof.
  intros.
  simpl.
  simpl in H.
  destruct (attr_alignas a).
  + apply Zle_is_le_bool in H.
    rewrite <- N_nat_Z in *.
    rewrite <- two_power_nat_two_p in *.
    destruct (alignof_fields_two_p f).
    rewrite H0 in *; clear H0.
    apply (power_nat_divide _ _ H).
  + apply Z.divide_refl.
Qed.

Lemma local_legal_alignas_type_Tunion: forall i f a,
  local_legal_alignas_type (Tunion i f a) = true ->
  (alignof_fields f | alignof (Tunion i f a)).
Proof.
  intros.
  simpl.
  simpl in H.
  destruct (attr_alignas a).
  + apply Zle_is_le_bool in H.
    rewrite <- N_nat_Z in *.
    rewrite <- two_power_nat_two_p in *.
    destruct (alignof_fields_two_p f).
    rewrite H0 in *; clear H0.
    apply (power_nat_divide _ _ H).
  + apply Z.divide_refl.
Qed.

Lemma legal_alignas_type_Tarray: forall t z a,
  legal_alignas_type (Tarray t z a) = true ->
  alignof (Tarray t z a) = alignof t.
Proof.
  intros.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tarray.
  exact H.
Qed.

Lemma legal_alignas_type_Tstruct: forall i f a,
  legal_alignas_type (Tstruct i f a) = true ->
  (alignof_fields f | alignof (Tstruct i f a)).
Proof.
  intros.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tstruct.
  exact H.
Qed.

Lemma legal_alignas_type_Tunion: forall i f a,
  legal_alignas_type (Tunion i f a) = true ->
  (alignof_fields f | alignof (Tunion i f a)).
Proof.
  intros.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tunion.
  exact H.
Qed.

Lemma legal_alignas_sizeof_alignof_compat: forall t : type,
  legal_alignas_type t = true -> (alignof t | sizeof t).
Proof.
  intros.
  induction t; pose proof nested_pred_atom_pred _ H; simpl in *;
  try (destruct (attr_alignas a); inversion H0).
  - apply Z.divide_refl.
  - destruct i; apply Z.divide_refl.
  - unfold Z.divide. exists 2. reflexivity.
  - destruct f. apply Z.divide_refl.
    unfold Z.divide. exists 2. reflexivity.
  - apply Z.divide_refl.
  - destruct (zle z 0).
    * rewrite Z.max_l; [|exact l].
      rewrite <- Zmult_0_r_reverse.
      apply Z.divide_0_r.
    * apply nested_pred_Tarray in H; [|exact g].
      apply IHt in H.
      apply Z.divide_mul_l.
      exact H.
  - apply Z.divide_refl.
  - apply align_divides, two_p_gt_ZERO, N2Z.is_nonneg.
  - apply align_divides, alignof_fields_pos.
  - apply align_divides, two_p_gt_ZERO, N2Z.is_nonneg.
  - apply align_divides, alignof_fields_pos.
  - apply Z.divide_refl.
Qed.

Opaque alignof.

(******* Samples : fieldlist_no_replicate *************)

Definition nested_legal_fieldlist := nested_pred (fun t => 
  match t with
  | Tstruct i f a => fieldlist_no_replicate f
  | Tunion i f a => fieldlist_no_replicate f
  | _ => true
  end).

(******* Samples : nested_non_volatile_type *************)

Definition uncompomize_non_volatile t :=
  match t with
  | Tvoid => true
  | Tint _ _ a => negb (attr_volatile a)
  | Tlong _ a => negb (attr_volatile a)
  | Tfloat _ a => negb (attr_volatile a)
  | Tpointer _ a => negb (attr_volatile a)
  | Tarray _ _ _ => true
  | Tfunction _ _ _ => true
  | Tstruct _ _ _ => true
  | Tunion _ _ _ => true
  | Tcomp_ptr _ a => negb (attr_volatile a)
  end.

Definition nested_non_volatile_type := nested_pred uncompomize_non_volatile.

Lemma nested_non_volatile_type_fact: forall t,
  nested_non_volatile_type t = true ->
  match t with
  | Tint _ _ _ => type_is_volatile t = false
  | Tlong _ _ => type_is_volatile t = false
  | Tfloat _ _ => type_is_volatile t = false
  | Tpointer _ _ => type_is_volatile t = false
  | Tcomp_ptr i a => type_is_volatile (Tpointer (look_up_ident_default i empty_ti) a) = false
  | _ => True
  end.
Proof.
  intros.
  unfold nested_non_volatile_type in H.
  destruct t; unfold type_is_volatile; simpl in *; auto;
  rewrite negb_true_iff in H; auto.
  + destruct i, s; auto.
  + destruct f; auto.
Qed.

(************************************************

Definition of nested_field_type2, nested_field_offset2

************************************************)

Inductive gfield : Type :=
  | ArraySubsc : forall i: Z, gfield
  | StructField : forall i: ident, gfield
  | UnionField : forall i: ident, gfield.

(*
Notation "Y @s X" := (cons (StructField X) Y) (at level 70).
Notation "Y @u X" := (cons (UnionField X) Y) (at level 70).
Notation "Y [ X ]" := (cons (ArraySubsc X) Y) (at level 70).
*)
(*
Notation "@@s X" := (cons (StructField X) nil) (at level 60).
Notation "@@u X" := (cons (UnionField X) nil) (at level 60).
Notation "[( X )]" := (cons (ArraySubsc X) nil) (at level 60).
*)

Fixpoint nested_field_rec (t: type) (gfs: list gfield) : option (prod Z type) :=
  match gfs with
  | nil => Some (0, t)
  | hd :: tl =>
    match nested_field_rec t tl with
    | Some (pos, t') => 
      match t', hd with
      | Tarray t'' n _, ArraySubsc i =>
        if (Z.leb 0 i && Z.ltb i n)
        then Some(pos + sizeof t'' * i, t'')
        else None
      | Tstruct _ f _, StructField i => 
        match field_offset i f, field_type i f with
        | Errors.OK ofs, Errors.OK t'' => Some (pos + ofs, t'')
        | _, _ => None
        end
      | Tunion _ f _, UnionField i =>
        match field_type i f with
        | Errors.OK t'' => Some (pos, t'')
        | _ => None
        end
      | _, _ => None
      end
    | None => None
    end
  end.

Definition nested_field_offset (t: type) (gfs: list gfield) : option Z :=
  match nested_field_rec t gfs with
  | Some (pos, _) => Some pos
  | _ => None
  end.

Definition nested_field_type (t: type) (gfs: list gfield) : option type :=
  match nested_field_rec t gfs with
  | Some (_, t0) => Some t0
  | _ => None
  end.

Definition nested_field_offset2 (t: type) (gfs: list gfield) : Z :=
  match nested_field_rec t gfs with
  | Some (pos, _) => pos
  | _ => 0
  end.

Definition nested_field_type2 (t: type) (gfs: list gfield) : type :=
  match nested_field_rec t gfs with
  | Some (_, t0) => t0
  | _ => Tvoid
  end.

Ltac valid_nested_field_rec f a T :=
  let H := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  simpl in T; destruct (nested_field_rec f a) as [[ofs t]|] eqn:H; [|inversion T].

Ltac auto_destruct_above_line :=
repeat (match goal with
        | H: _ /\ _ |- _ => destruct H 
        | H: prod _ _ |- _ => destruct H 
        | H: @ex _ _ |- _ => destruct H 
        | H: sigT _ |- _ => destruct H 
        end).

Ltac solve_array_subsc_range H :=
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  pose proof H as H0;
  destruct H0 as [H1 H2];
  apply Zle_is_le_bool in H1;
  apply Zlt_is_lt_bool in H2;
  try rewrite H1 in *;
  try rewrite H2 in *;
  clear H1 H2.

Lemma nested_field_rec_cons_isSome_lemma: forall t gf gfs, 
  isSome (nested_field_rec t (gf :: gfs)) <->
  isSome (nested_field_rec t gfs) /\ 
  match gf with
  | ArraySubsc i0 => exists t0 n a, 0 <= i0 < n /\ 
                     nested_field_type2 t gfs = Tarray t0 n a
  | StructField i0 => exists i f a, isOK (field_type i0 f) = true /\ 
                      nested_field_type2 t gfs = Tstruct i f a
  | UnionField i0 => exists i f a, isOK (field_type i0 f) = true /\
                     nested_field_type2 t gfs = Tunion i f a
  end.
Proof.
  intros.
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt; destruct gf |];
  (split; intros; [try inversion H | auto_destruct_above_line]; 
   try solve[inversion H]; try solve[inversion H1]; try solve[inversion H2]).
  + destruct ((0 <=? i) && (i <? z0)) eqn:?H; [| inversion H].
    split; [simpl; auto |]; exists tt, z0, a.
    rewrite andb_true_iff in H0.
    destruct H0.
    apply Zle_bool_imp_le in H0.
    apply Zlt_is_lt_bool in H1.
    split; [omega | reflexivity].
  + apply Zle_is_le_bool in H0. 
    apply Zlt_is_lt_bool in H2.
    inversion H1; subst.
    rewrite H0, H2.
    simpl; auto.
  + simpl; split; auto; exists i, f, a.
    destruct (field_type i0 f); simpl.
      auto.
      destruct (field_offset i0 f); inversion H.
  + subst. inversion H1.
    solve_field_offset_type i0 x0. simpl; auto. inversion H0.
  + simpl; split; auto; exists i, f, a.
    destruct (field_type i0 f); simpl.
      auto.
      destruct (field_offset i0 f); inversion H.
  + subst. inversion H1.
    solve_field_offset_type i0 x0. simpl; auto. inversion H0.
Qed.

Definition iffT A B := ((A -> B) * (B -> A))%type.

Definition nested_field_rec_cons_isSome_lemmaT: forall t gf gfs, 
  iffT (isSome (nested_field_rec t (gf :: gfs)))
  (isSome (nested_field_rec t gfs) *
  match gf with
  | ArraySubsc i0 => sigT (fun t0 => sigT (fun n => sigT (fun a => (0 <= i0 < n) *
                     (nested_field_type2 t gfs = Tarray t0 n a))))%type
  | StructField i0 => sigT (fun i => sigT (fun f => sigT (fun a => 
               (isOK (field_type i0 f) = true) * (nested_field_type2 t gfs = Tstruct i f a))))%type
  | UnionField i0 => sigT (fun i => sigT (fun f => sigT (fun a => 
               (isOK (field_type i0 f) = true) * (nested_field_type2 t gfs = Tunion i f a))))%type
  end).
Proof.
  intros.
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt; destruct gf |];
  (split; intros; [try inversion H | auto_destruct_above_line]; 
   try solve[inversion i]; try solve[inversion e0]; try solve[inversion e]).
  + destruct ((0 <=? i) && (i <? z0)) eqn:?H; [| inversion H].
    split; [simpl; auto |]; exists tt, z0, a.
    rewrite andb_true_iff in H0.
    destruct H0.
    apply Zle_bool_imp_le in H0.
    apply Zlt_is_lt_bool in H1.
    split; [omega | reflexivity].
  + apply Zle_is_le_bool in H.
    apply Zlt_is_lt_bool in H0.
    inversion e; subst.
    rewrite H0, H.
    simpl; auto.
  + simpl; split; auto; exists i, f, a.
    destruct (field_type i0 f); simpl.
      auto.
      destruct (field_offset i0 f); inversion H.
  + subst. inversion e0. subst.
    solve_field_offset_type i0 x0. simpl; auto. inversion e.
  + simpl; split; auto; exists i, f, a.
    destruct (field_type i0 f); simpl.
      auto.
      destruct (field_offset i0 f); inversion H.
  + subst. inversion e0. subst.
    solve_field_offset_type i0 x0. simpl; auto. inversion e.
Defined.

Lemma nested_field_rec_cons_eq_Some_lemma: forall t gf gfs ofs0 t0, 
  nested_field_rec t (gf :: gfs) = Some (ofs0, t0) <->
  match gf with
  | ArraySubsc i0 => exists ofs n a, nested_field_rec t gfs = Some (ofs, Tarray t0 n a) /\
                     0 <= i0 < n /\ ofs0 = ofs + sizeof t0 * i0
  | StructField i0 => exists ofs i f a, nested_field_rec t gfs = Some (ofs, Tstruct i f a) /\
                     field_type i0 f = Errors.OK t0 /\ field_offset i0 f = Errors.OK (ofs0 - ofs)
  | UnionField i0 => exists i f a, nested_field_rec t gfs = Some (ofs0, Tunion i f a) /\
                     field_type i0 f = Errors.OK t0
  end.
Proof.
  intros.
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt |]; destruct gf;
  (split; intros; [try solve [inversion H] | auto_destruct_above_line]; 
   try solve[inversion H]; try solve[inversion H0]; try solve[inversion H1]).
  + destruct ((0 <=? i) && (i <? z0)) eqn:?H; [| inversion H].
    rewrite andb_true_iff in H0.
    destruct H0.
    apply Zle_bool_imp_le in H0.
    apply Zlt_is_lt_bool in H1.
    exists z, z0, a.
    inversion H; subst.
    repeat split; auto.
  + apply Zle_is_le_bool in H0.
    apply Zlt_is_lt_bool in H2.
    inversion H; subst.
    rewrite H0, H2.
    simpl; auto.
  + solve_field_offset_type i0 f; inversion H; subst.
    exists z, i, f, a.
    repeat split; auto.
    rewrite H2.
    f_equal; omega.
  + inversion H; subst.
    solve_field_offset_type i0 x1; inversion H1; inversion H0; subst.
    f_equal; f_equal. omega.
  + solve_field_offset_type i0 f; inversion H; subst.
    exists i, f, a.
    repeat split; auto.
  + inversion H; subst.
    solve_field_offset_type i0 x0; inversion H0; subst.
    reflexivity.
Qed.

Ltac solve_nested_field_rec_cons_isSome H :=
  let HH := fresh "HH" in
  let Heq := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  let _i := fresh "i" in
  let i := fresh "i" in
  let f := fresh "f" in
  let a := fresh "a" in
  let t := fresh "t" in
  let n := fresh "n" in
  match type of H with
  | isSome (nested_field_rec ?T (?A :: ?GFS)) =>
    destruct (nested_field_rec_cons_isSome_lemmaT T A GFS) as [HH _];
    specialize (HH H);
    destruct A eqn:Heq
  end;
  [try solve [inversion Heq]; destruct HH as [H1 [t [n [a [H2 H3]]]]]
  |try solve [inversion Heq]; destruct HH as [H1 [i [f [a [H2 H3]]]]]
  |try solve [inversion Heq]; destruct HH as [H1 [i [f [a [H2 H3]]]]]].

Ltac solve_nested_field_rec_cons_eq_Some H :=
  let HH := fresh "HH" in
  let Heq := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  let _i := fresh "i" in
  let i := fresh "i" in
  let f := fresh "f" in
  let a := fresh "a" in
  let t := fresh "t" in
  let n := fresh "n" in
  let ofs := fresh "ofs" in
  match type of H with
  | (nested_field_rec ?T (?A :: ?GFS) = Some (?OFS, ?T0)) => 
    destruct (nested_field_rec_cons_eq_Some_lemma T A GFS OFS T0) as [HH _];
    specialize (HH H);
    destruct A eqn:Heq
  end;
  [try solve [inversion Heq]; destruct HH as [ofs [n [a [H1 [H2 H3]]]]]
  |try solve [inversion Heq]; destruct HH as [ofs [i [f [a [H1 [H2 H3]]]]]]
  |try solve [inversion Heq]; destruct HH as [i [f [a [H1 H2]]]]].

Lemma nested_field_rec_nest_pred: forall {atom_pred: type -> bool} (t: type) (gfs: list gfield) pos t', nested_pred atom_pred t = true -> nested_field_rec t gfs = Some (pos, t') -> nested_pred atom_pred t' = true.
Proof.
  intros.
  revert pos t' H0; induction gfs; intros.
  + inversion H0.
    subst.
    exact H.
  + solve_nested_field_rec_cons_eq_Some H0. 
    - (* Tarray case *)
      specialize (IHgfs _ _ H1).
      eapply nested_pred_Tarray; [exact IHgfs | omega].
    - (* Tstruct case *)
      specialize (IHgfs _ _ H1).
      eapply nested_fields_pred_nested_pred; [exact H2 |].
      eapply nested_pred_Tstruct; exact IHgfs.
    - (* Tunion case *)
      specialize (IHgfs _ _ H1).
      eapply nested_fields_pred_nested_pred; [exact H2 |].
      eapply nested_pred_Tunion; exact IHgfs.
Defined.

Lemma nested_field_type_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t t': type) (gfs: list gfield), nested_pred atom_pred t = true -> nested_field_type t gfs = Some t' -> nested_pred atom_pred t' = true.
Proof.
  intros.
  unfold nested_field_type in *.
  valid_nested_field_rec t gfs H1.
  inversion H1; subst t0; clear H1.
  eapply nested_field_rec_nest_pred. exact H0.
  exact H2.
Defined.

Lemma nested_field_type2_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (gfs: list gfield), nested_pred atom_pred t = true -> nested_pred atom_pred (nested_field_type2 t gfs) = true.
Proof.
  intros.
  unfold nested_field_type2.
  valid_nested_field_rec t gfs H0.
  eapply nested_field_rec_nest_pred. exact H0. exact H1.
  simpl; rewrite H, H0; reflexivity.
Defined.

Lemma nested_field_type2_field_type: forall i f a id t, nested_field_type2 (Tstruct i f a) (StructField id :: nil) = t /\ t <> Tvoid -> field_type id f = Errors.OK t.
Proof.
  unfold nested_field_type2.
  intros.
  simpl in H.
  solve_field_offset_type id f; destruct H.
  - subst; reflexivity.
  - congruence.
Defined.

Lemma nested_field_type2_Tarray_nested_field_rec_isSome: forall t gfs t0 n a,
  nested_field_type2 t gfs = Tarray t0 n a -> isSome (nested_field_rec t gfs).
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  simpl; auto.
Defined.

Lemma nested_field_type2_Tstruct_nested_field_rec_isSome: forall t gfs i f a,
  nested_field_type2 t gfs = Tstruct i f a -> isSome (nested_field_rec t gfs).
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  simpl; auto.
Defined.

Lemma nested_field_type2_Tunion_nested_field_rec_isSome: forall t gfs i f a,
  nested_field_type2 t gfs = Tunion i f a -> isSome (nested_field_rec t gfs).
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  simpl; auto.
Defined.

Lemma nested_field_type2_nil: forall t, nested_field_type2 t nil = t.
Proof.
  intros.
  reflexivity.
Defined.

Lemma nested_field_type2_cons: forall t gf gfs0,
  nested_field_type2 t (gf :: gfs0) = 
  match gf, nested_field_type2 t gfs0 with
  | ArraySubsc i, Tarray t0 n a => if (Z.leb 0 i && Z.ltb i n) then t0 else Tvoid
  | StructField i, Tstruct i0 f a => match field_offset i f, field_type i f with
                                     | Errors.OK _, Errors.OK t0 => t0
                                     | _, _ => Tvoid
                                     end
  | UnionField i, Tunion i0 f a => match field_type i f with
                                    | Errors.OK t0 => t0
                                    | _ => Tvoid
                                    end
  | _, _ => Tvoid
  end.
Proof.
  intros.
  unfold nested_field_type2 in *.
  simpl.
  destruct (nested_field_rec t gfs0) eqn:HH; try reflexivity.
  destruct p.
  destruct t0, gf; try reflexivity.
  + destruct ((0 <=? i) && (i <? z0)); reflexivity.
  + destruct (field_offset i0 f), (field_type i0 f); reflexivity.
  + destruct (field_type i0 f); reflexivity.
  + destruct gf; reflexivity.
Defined.

Lemma nested_field_rec_divide: forall t gfs pos t', nested_field_rec t gfs = Some (pos, t') -> legal_alignas_type t = true -> Z.divide (alignof t') pos.
Proof.
  intros.
  assert ((alignof t' | pos) /\ legal_alignas_type t' = true); [| tauto].
  revert pos t' H; induction gfs; intros.
  + inversion H. split; [apply Z.divide_0_r | inversion H; subst; exact H0].
  + solve_nested_field_rec_cons_eq_Some H.
    - (* Tarray Case *)
      destruct (IHgfs _ _ H1).
      assert (legal_alignas_type t' = true) by
        (eapply nested_pred_Tarray; [exact H5 | omega]).
      split; [| auto].
      rewrite legal_alignas_type_Tarray in H4 by auto.
      subst.
      apply Z.divide_add_r; try assumption.
      apply Z.divide_mul_l; try assumption.
      apply legal_alignas_sizeof_alignof_compat; auto.
    - (* Tstruct Case *)
      subst.
      destruct (IHgfs _ _ H1).
      pose proof field_offset_aligned i f _ t' H3 H2.
      assert (alignof_fields f | ofs) by
        (eapply Zdivides_trans; [apply legal_alignas_type_Tstruct; exact H5 | exact H4]).
      split.
      * replace pos with ((pos - ofs) + ofs) by omega.
        apply Z.divide_add_r; try assumption.
        eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H2. exact H7.
      * eapply nested_fields_pred_nested_pred. exact H2. eapply nested_pred_Tstruct. exact H5.
    - (* Tunion Case *)
      subst.
      destruct (IHgfs _ _ H1).
      assert (alignof_fields f | pos) by
        (eapply Zdivides_trans; [apply legal_alignas_type_Tunion; exact H4 | exact H3]).
      split.
      * eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H2. exact H5.
      * eapply nested_fields_pred_nested_pred. exact H2. eapply nested_pred_Tunion. exact H4.
Defined.

Lemma nested_field_offset2_type2_divide: forall gfs t, legal_alignas_type t = true -> Z.divide (alignof (nested_field_type2 t gfs)) (nested_field_offset2 t gfs).
Proof.
  intros.
  unfold nested_field_type2, nested_field_offset2.
  valid_nested_field_rec t gfs H.
  + exact (nested_field_rec_divide t gfs  _ _ H0 H).
  + apply Zdivide_0.
Defined.

(************************************************

nested_field_rec_Tarray
nested_field_rec_Tstruct_hd
nested_field_rec_Tstruct_mid
nested_field_rec_Tunion_hd
nested_field_rec_Tunion_mid

************************************************)

Lemma nested_field_rec_Tarray: forall t0 n a gfs t ofs i,
  nested_field_rec t gfs = Some (ofs, Tarray t0 n a) ->
  0 <= i < n ->
  nested_field_rec t (ArraySubsc i :: gfs) = Some (ofs + sizeof t0 * i, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  destruct H0.
  apply Zle_is_le_bool in H0.
  apply Zlt_is_lt_bool in H1.
  rewrite H0, H1.
  reflexivity.
Qed.

Lemma nested_field_rec_Tstruct: forall gfs t i0 t0 i f a ofs ofs0,
  nested_field_rec t gfs = Some (ofs, Tstruct i f a) ->
  field_offset i0 f = Errors.OK ofs0 ->
  field_type i0 f = Errors.OK t0 ->
  nested_field_rec t (StructField i0 :: gfs) = Some (ofs + ofs0, t0).
Proof.
  intros.
  simpl.
  rewrite H, H0, H1.
  reflexivity.
Qed.

Lemma nested_field_rec_Tunion: forall gfs t i0 t0 i f a ofs,
  nested_field_rec t gfs = Some (ofs, Tunion i f a) ->
  field_type i0 f = Errors.OK t0 ->
  nested_field_rec t (UnionField i0 :: gfs) = Some (ofs, t0).
Proof.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma nested_field_rec_Tstruct_hd: forall i0 t0 gfs t i f a ofs,
  nested_field_rec t gfs = Some (ofs, Tstruct i (Fcons i0 t0 f) a) ->
  nested_field_rec t (StructField i0 :: gfs) = Some (ofs, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite field_offset_hd, field_type_hd.
  replace (ofs + 0) with ofs; [reflexivity | omega].
Qed.

Lemma nested_field_rec_Tunion_hd: forall i0 t0 gfs t i f a ofs,
  nested_field_rec t gfs = Some (ofs, Tunion i (Fcons i0 t0 f) a) ->
  nested_field_rec t (UnionField i0 :: gfs) = Some (ofs, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite field_type_hd.
  reflexivity.
Qed.

Lemma nested_field_rec_Tstruct_mid:
  forall i1 t1 t1' i0 t0 t gfs i f' f a ofs ofs0,
  legal_alignas_type t = true -> 
  nested_legal_fieldlist t = true ->
  nested_field_rec t gfs = Some (ofs, Tstruct i 
    (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a) -> 
  nested_field_rec t (StructField i1 :: gfs) = Some (ofs0, t1') ->
  nested_field_rec t (StructField i0 :: gfs) = 
    Some (align (ofs0 + sizeof t1) (alignof t0), t0).
Proof.
  intros.
  simpl in H2; rewrite H1 in H2; simpl; rewrite H1.
  pose proof (nested_field_rec_nest_pred t gfs ofs _ H0 H1).
  apply nested_pred_atom_pred in H3.
  solve_field_offset_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))); inversion H2.
  subst; clear H2.
  rewrite (field_offset_mid _ _ _ _ _ _ ofs1 H3 H6).
  rewrite fieldlist_app_Fcons. rewrite fieldlist_app_Fcons in H3.
  pose proof (field_type_mid i0 t0 _ _ H3) as HH.
  rewrite HH.
  replace (align (ofs + ofs1 + sizeof t1) (alignof t0)) with (ofs + align (ofs1 + sizeof t1) (alignof t0)); [reflexivity | rewrite <- Z.add_assoc].
  apply divide_add_align.
  eapply Zdivide_trans; [| apply (nested_field_rec_divide t gfs _ _ H1 H)].
  pose proof (nested_field_rec_nest_pred t gfs ofs _ H H1).
  eapply Zdivides_trans; [| apply legal_alignas_type_Tstruct; exact H2].
  rewrite fieldlist_app_Fcons.
  apply (alignof_type_divide_whole_fl i0 _ _ HH).
Qed.

Lemma nested_field_rec_Tunion_mid:
  forall i0 t0 t gfs i f' f a ofs,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_rec t gfs = Some (ofs,
    Tunion i (fieldlist_app f' (Fcons i0 t0 f)) a) ->
  nested_field_rec t (UnionField i0 :: gfs) = Some (ofs, t0).
Proof.
  intros.
  pose proof (nested_field_rec_nest_pred t gfs ofs _ H0 H1).
  apply nested_pred_atom_pred in H2.
  simpl.
  rewrite H1.
  rewrite (field_type_mid i0 t0 _ _ H2).
  reflexivity.
Qed.

Lemma nested_field_offset2_Tarray: forall t0 n a gfs t i,
  nested_field_type2 t gfs = Tarray t0 n a ->
  0 <= i < n ->
  nested_field_offset2 t (ArraySubsc i :: gfs) = nested_field_offset2 t gfs + sizeof t0 * i.
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  subst.
  unfold nested_field_offset2.
  erewrite nested_field_rec_Tarray by eauto.
  rewrite H1.
  reflexivity.
Qed.

Lemma nested_field_type2_Tarray: forall t0 n a gfs t i,
  nested_field_type2 t gfs = Tarray t0 n a ->
  0 <= i < n ->
  nested_field_type2 t (ArraySubsc i :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  subst.
  unfold nested_field_type2.
  erewrite nested_field_rec_Tarray by eauto.
  reflexivity.
Qed.

Lemma nested_field_offset2_Tstruct: forall t gfs i0 i f a ofs,
  nested_field_type2 t gfs = Tstruct i f a ->
  field_offset i0 f = Errors.OK ofs ->
  nested_field_offset2 t (StructField i0 :: gfs) = nested_field_offset2 t gfs + ofs.
Proof.
  intros.
  unfold nested_field_type2 in H.
  unfold nested_field_offset2.
  valid_nested_field_rec t gfs H.
  solve_field_offset_type i0 f; [| inversion H0].
  inversion H0; subst ofs1 t0.
  erewrite nested_field_rec_Tstruct by eauto.
  reflexivity.
Qed.

Lemma nested_field_type2_Tstruct: forall t gfs i0 i f a t0,
  nested_field_type2 t gfs = Tstruct i f a ->
  field_type i0 f = Errors.OK t0 ->
  nested_field_type2 t (StructField i0 :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in H |- *.
  valid_nested_field_rec t gfs H.
  solve_field_offset_type i0 f; [| inversion H0].
  inversion H0; subst t2 t1.
  erewrite nested_field_rec_Tstruct by eauto.
  reflexivity.
Qed.

Lemma nested_field_offset2_Tunion: forall t gfs i0 i f a,
  nested_field_type2 t gfs = Tunion i f a ->
  isOK (field_offset i0 f) = true->
  nested_field_offset2 t (UnionField i0 :: gfs) = nested_field_offset2 t gfs.
Proof.
  intros.
  unfold nested_field_type2 in H.
  unfold nested_field_offset2.
  valid_nested_field_rec t gfs H.
  solve_field_offset_type i0 f; [| inversion H0].
  subst t0.
  erewrite nested_field_rec_Tunion by eauto.
  reflexivity.
Qed.

Lemma nested_field_type2_Tunion: forall t gfs i0 i f a t0,
  nested_field_type2 t gfs = Tunion i f a ->
  field_type i0 f = Errors.OK t0 ->
  nested_field_type2 t (UnionField i0 :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in H |- *.
  valid_nested_field_rec t gfs H.
  solve_field_offset_type i0 f; [| inversion H0].
  inversion H0; subst t2 t1.
  erewrite nested_field_rec_Tunion by eauto.
  reflexivity.
Qed.

Lemma nested_field_offset2_Tstruct_hd: forall i0 t0 t gfs i f a, nested_field_type2 t gfs = Tstruct i (Fcons i0 t0 f) a -> nested_field_offset2 t (StructField i0 :: gfs) = nested_field_offset2 t gfs.
Proof.
  intros.
  unfold nested_field_offset2. simpl. unfold nested_field_type2 in H.
  destruct (nested_field_rec t gfs) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  omega.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_type2_Tstruct_hd: forall i0 t0 t gfs i f a, nested_field_type2 t gfs = Tstruct i (Fcons i0 t0 f) a -> nested_field_type2 t (StructField i0 :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  destruct (nested_field_rec t gfs) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  reflexivity.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_offset2_Tstruct_mid: forall i0 t0 i1 t1 t gfs i f a f', 
  legal_alignas_type t = true -> 
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tstruct i (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a -> 
  nested_field_offset2 t (StructField i0 :: gfs) = 
  align (nested_field_offset2 t (StructField i1 :: gfs) + sizeof t1) (alignof t0).
Proof.
  intros.
  unfold nested_field_type2, nested_field_offset2 in *.
  valid_nested_field_rec t gfs H0.
  subst t2.
  cut (isSome (nested_field_rec t (StructField i1 :: gfs))); intros.
  + destruct (nested_field_rec t (StructField i1 :: gfs)) as [[? ?]|] eqn:?; inversion H1.
    erewrite nested_field_rec_Tstruct_mid; eauto.
  + apply nested_field_rec_cons_isSome_lemma.
    unfold nested_field_type2.
    rewrite H2.
    simpl.
    split; [exact I | exists i, (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))), a ].
    rewrite field_type_mid.
    simpl; eauto.
    unfold nested_legal_fieldlist in H0.
    eapply nested_field_type2_nest_pred with (gfs0 := gfs) in H0; [| reflexivity].
    apply nested_pred_atom_pred in H0.
    unfold nested_field_type2 in H0.
    rewrite H2 in H0.
    exact H0.
  + inversion H1.
Qed.

Lemma nested_field_type2_Tstruct_mid: forall i0 t0 t gfs i f' f a,
  nested_field_type2 t gfs = Tstruct i (fieldlist_app f' (Fcons i0 t0 f)) a ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t (StructField i0 :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  valid_nested_field_rec t gfs H.
  eapply nested_field_type2_nest_pred with (gfs0 := gfs) in H0; [| reflexivity].
  apply nested_pred_atom_pred in H0.
  unfold nested_field_type2 in H0.
  rewrite H1 in H0.
  subst t1.
  solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 f)).
  + rewrite field_type_mid in H2; [|exact H0].
    inversion H2.
    reflexivity.
  + rewrite field_type_mid in H2; [|exact H0].
    inversion H2.
Qed.

Lemma nested_field_offset2_Tunion_hd: forall i0 t0 t gfs i f a, nested_field_type2 t gfs = Tunion i (Fcons i0 t0 f) a -> nested_field_offset2 t (UnionField i0 :: gfs) = nested_field_offset2 t gfs.
Proof.
  intros.
  unfold nested_field_offset2. simpl. unfold nested_field_type2 in H.
  destruct (nested_field_rec t gfs) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  omega.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_type2_Tunion_hd: forall i0 t0 t gfs i f a, nested_field_type2 t gfs = Tunion i (Fcons i0 t0 f) a -> nested_field_type2 t (UnionField i0 :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  destruct (nested_field_rec t gfs) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  reflexivity.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_offset2_Tunion_mid:
  forall i0 t0 t gfs i f' f a,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tunion i (fieldlist_app f' (Fcons i0 t0 f)) a ->
  nested_field_offset2 t (UnionField i0 :: gfs) = nested_field_offset2 t gfs.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  unfold nested_field_offset2 in *. simpl.
  valid_nested_field_rec t gfs H1.
  eapply nested_field_type2_nest_pred with (gfs0 := gfs) in H0; [| reflexivity].
  apply nested_pred_atom_pred in H0.
  unfold nested_field_type2 in H0.
  rewrite H2 in H0.
  subst t1.
  solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 f)).
  + reflexivity.
  + rewrite field_type_mid in H3 by auto.
    inversion H3.
Qed.

Lemma nested_field_type2_Tunion_mid: forall i0 t0 t gfs i f' f a,
  nested_field_type2 t gfs = Tunion i (fieldlist_app f' (Fcons i0 t0 f)) a ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t (UnionField i0 :: gfs) = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  valid_nested_field_rec t gfs H.
  eapply nested_field_type2_nest_pred with (gfs0 := gfs) in H0; [| reflexivity].
  apply nested_pred_atom_pred in H0.
  unfold nested_field_type2 in H0.
  rewrite H1 in H0.
  subst t1.
  solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 f)).
  + rewrite field_type_mid in H2; [|exact H0].
    inversion H2.
    reflexivity.
  + rewrite field_type_mid in H2; [|exact H0].
    inversion H2.
Qed.

(************************************************

nested_field_offset_app

************************************************)

Lemma nested_field_rec_app: forall t gfs0 gfs1 t0 t1 ofs0 ofs1,
  nested_field_rec t gfs0 = Some (ofs0, t0) ->
  nested_field_rec t0 gfs1 = Some (ofs1, t1) ->
  nested_field_rec t (gfs1 ++ gfs0) = Some (ofs0 + ofs1, t1).
Proof.
  intros.
  revert ofs1 t1 H0.
  induction gfs1; intros.
  + simpl in *.
    inversion H0.
    subst.
    rewrite H.
    rewrite Z.add_0_r.
    reflexivity.
  + solve_nested_field_rec_cons_eq_Some H0.
    - (* Tarray *)
      subst.
      simpl.
      rewrite (IHgfs1 _ _ H1).
      destruct H2.
      apply Zle_is_le_bool in H2.
      apply Zlt_is_lt_bool in H3.
      rewrite H2, H3.
      simpl.
      f_equal.
      f_equal.
      omega.
    - (* Tstruct *)
      subst.
      simpl.
      rewrite (IHgfs1 _ _ H1).
      rewrite H2, H3.
      f_equal.
      f_equal.
      omega.
    - (* Tunion *)
      subst.
      simpl.
      rewrite (IHgfs1 _ _ H1).
      rewrite H2.
      reflexivity.
Qed.

Lemma nested_field_rec_app_isSome: forall t gfs0 gfs1,
  isSome (nested_field_rec t (gfs1 ++ gfs0)) -> isSome (nested_field_rec t gfs0).
Proof.
  intros.
  induction gfs1.
  + simpl in *; auto.
  + simpl app in H.
    solve_nested_field_rec_cons_isSome H;
    unfold nested_field_type2 in H2;
    valid_nested_field_rec t (gfs1 ++ gfs0) H2.
    - subst.
      simpl in IHgfs1.
      auto.
    - subst.
      simpl in IHgfs1.
      auto.
    - subst.
      simpl in IHgfs1.
      auto.
Qed.

Lemma nested_field_rec_app_isSome': forall t gfs0 gfs1,
  isSome (nested_field_rec t (gfs1 ++ gfs0)) -> isSome (nested_field_rec (nested_field_type2 t gfs0) gfs1).
Proof.
  intros.
  pose proof nested_field_rec_app_isSome _ _ _ H.
  unfold nested_field_type2.
  valid_nested_field_rec t gfs0 H0.
  valid_nested_field_rec t (gfs1 ++ gfs0) H.
  clear H H0.
  revert ofs ofs0 t0 t1 H1 H2.
  induction gfs1; intros.
  + simpl in *; auto.
  + simpl app in H2.
    solve_nested_field_rec_cons_eq_Some H2;
    pose proof IHgfs1 _ _ _ _ H1 H as H4;
    valid_nested_field_rec t0 gfs1 H4.
    - pose proof nested_field_rec_app _ _ _ _ _ _ _ H1 H5.
      simpl; rewrite H5.
      rewrite H in H6; inversion H6.
      subst.
      destruct H0.
      apply Zle_is_le_bool in H0.
      apply Zlt_is_lt_bool in H3.
      rewrite H0, H3.
      simpl.
      auto.
    - pose proof nested_field_rec_app _ _ _ _ _ _ _ H1 H5.
      simpl; rewrite H5.
      rewrite H in H6; inversion H6.
      rewrite H0, H3.
      simpl.
      auto.
    - pose proof nested_field_rec_app _ _ _ _ _ _ _ H1 H3.
      simpl; rewrite H3.
      rewrite H in H5; inversion H5.
      rewrite H0.
      simpl.
      auto.
Qed.

Lemma nested_field_offset2_app: forall t gfs0 gfs1,
  isSome (nested_field_rec t (gfs1 ++ gfs0)) ->
  nested_field_offset2 t (gfs1 ++ gfs0) = nested_field_offset2 t gfs0 +
    nested_field_offset2 (nested_field_type2 t gfs0) gfs1.
Proof.
  intros.
  pose proof nested_field_rec_app_isSome _ _ _ H.
  pose proof nested_field_rec_app_isSome' _ _ _ H.
  unfold nested_field_offset2, nested_field_type2 in *.
  valid_nested_field_rec t (gfs1 ++ gfs0) H.
  valid_nested_field_rec t gfs0 H0.
  valid_nested_field_rec t1 gfs1 H1.
  pose proof nested_field_rec_app t gfs0 gfs1 _ _ _ _ H3 H4.
  rewrite H2 in H5.
  inversion H5.
  reflexivity.
Qed.

Lemma nested_field_type2_nested_field_type2: forall t gfs0 gfs1,
  nested_field_type2 (nested_field_type2 t gfs0) gfs1 = nested_field_type2 t (gfs1 ++ gfs0).
Proof.
  intros.
  destruct (isSome_dec (nested_field_rec t (gfs1 ++ gfs0))).
  + pose proof nested_field_rec_app_isSome _ _ _ i.
    pose proof nested_field_rec_app_isSome' _ _ _ i.
    unfold nested_field_type2 in *.
    valid_nested_field_rec t (gfs1 ++ gfs0) i.
    valid_nested_field_rec t gfs0 H.
    valid_nested_field_rec t1 gfs1 H0.
    pose proof nested_field_rec_app _ _ _ _ _ _ _ H2 H3.
    rewrite H1 in H4.
    inversion H4.
    reflexivity.
  + unfold nested_field_type2.
    destruct (nested_field_rec t gfs0) as [[? ?]|] eqn:?H.
    - destruct (nested_field_rec t0 gfs1) as [[? ?]|] eqn:?H.
      * rewrite (nested_field_rec_app _ _ _ _ _ _ _ H H0). reflexivity.
      * destruct (nested_field_rec t (gfs1 ++ gfs0)); [simpl in n; tauto |].
        reflexivity.
    - destruct (nested_field_rec t (gfs1 ++ gfs0)); [simpl in n; tauto |].
      induction gfs1.
      * reflexivity.
      * simpl.
        destruct (nested_field_rec Tvoid gfs1) as [[? ?]|]; inversion IHgfs1; reflexivity.
Qed.

(************************************************

Other lemmas

************************************************)

Lemma nested_field_offset2_in_range: forall t gfs,
  isSome (nested_field_rec t gfs) ->
  0 <= nested_field_offset2 t gfs /\
  (nested_field_offset2 t gfs) + sizeof (nested_field_type2 t gfs) <= sizeof t.
Proof.
  intros.
  induction gfs.
  + unfold nested_field_type2, nested_field_offset2; simpl.
    omega.
  + solve_nested_field_rec_cons_isSome H;
    unfold nested_field_type2, nested_field_offset2 in *; simpl;
    valid_nested_field_rec t gfs H2; subst;
    simpl IHgfs; pose proof IHgfs I.
    - (* Tarray *)
      destruct H1.
      assert (0 <= sizeof t0) by (pose proof sizeof_pos t0; omega).
      assert (0 <= sizeof t0 * i) by (apply Z.mul_nonneg_nonneg; [exact H5 | exact H1]).        
      assert (sizeof t0 * i + sizeof t0 <= sizeof t0 * Z.max 0 n).
        rewrite Zred_factor3.
        apply Zmult_le_compat_l; [apply Zmax_bound_r; omega | exact H5].
      apply Zle_is_le_bool in H1.
      apply Zlt_is_lt_bool in H4.
      rewrite H1, H4.
      simpl in H2 |- *.
      split; omega.
    - (* Tstruct *)
      solve_field_offset_type i f; try solve [inversion H1].
      pose proof field_offset_in_range i0 f a0 _ ofs0 t0 H6 H5.
      omega.
    - (* Tunion *)
      solve_field_offset_type i f; try solve [inversion H1].
      pose proof field_offset_in_range' i0 f a0 _ t0 H5.
      omega.
Qed.
  
Lemma alignof_nested_field_type2_divide: forall t gfs,
  legal_alignas_type t = true ->
  isSome (nested_field_rec t gfs) ->
  (alignof (nested_field_type2 t gfs) | alignof t).
Proof.
  intros.
  induction gfs.
  + unfold nested_field_type2; simpl.
    apply Z.divide_refl.
  + assert (legal_alignas_type (nested_field_type2 t gfs) = true)
      by (apply nested_field_type2_nest_pred; auto).
    solve_nested_field_rec_cons_isSome H0;
    unfold nested_field_type2 in *; simpl;
    valid_nested_field_rec t gfs H4; subst;
    simpl IHgfs; pose proof IHgfs I.
    - (* Tarray *)
      destruct H3.
      apply Zle_is_le_bool in H3.
      apply Zlt_is_lt_bool in H6.
      rewrite H3, H6.
      simpl.
      rewrite legal_alignas_type_Tarray in H4; auto.
    - (* Tstruct *)
      solve_field_offset_type i f; try solve [inversion H3].
      pose proof alignof_type_divide_whole_fl _ _ _ H7.
      pose proof legal_alignas_type_Tstruct i f a0 H1.
      repeat (eapply Z.divide_trans; [eassumption|]).
      apply Z.divide_refl.
    - (* Tunion *)
      solve_field_offset_type i f; try solve [inversion H3].
      pose proof alignof_type_divide_whole_fl _ _ _ H7.
      pose proof legal_alignas_type_Tunion i f a0 H1.
      repeat (eapply Z.divide_trans; [eassumption|]).
      apply Z.divide_refl.
Qed.

