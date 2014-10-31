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
  | Tarray t0 n _ => (atom_pred t && nested_pred atom_pred t0)%bool
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
  nested_pred atom_pred (Tarray t n a) = true -> nested_pred atom_pred t = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H.
  tauto.
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

(******* Samples : array_never_empty **************)

Definition local_array_never_empty (t: type) :=
  match t with
  | Tarray _ n _ => Z.ltb 0 n
  | _ => true
  end.

Definition array_never_empty := nested_pred local_array_never_empty.

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
  - apply nested_pred_Tarray in H.
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
      | Tarray t'' n _, ArraySubsc i => Some(pos + sizeof t'' * i, t'')
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

Fixpoint nested_array_subsc_in_range (t: type) (gfs: list gfield) : Prop :=
  match gfs with
  | nil => True
  | gf :: gfs0 =>
    match nested_field_type2 t gfs0, gf with
    | Tarray _ n _, ArraySubsc i => (0 <= i < n /\ nested_array_subsc_in_range t gfs0)
    | _, _ => nested_array_subsc_in_range t gfs0
    end
  end.

Definition legal_nested_field t gfs :=
  isSome (nested_field_rec t gfs) /\ nested_array_subsc_in_range t gfs.

Ltac valid_nested_field_rec f a T :=
  let H := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  simpl in T; destruct (nested_field_rec f a) as [[ofs t]|] eqn:H; [|inversion T].

Ltac auto_destruct_above_line :=
repeat (
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let x := fresh "x" in
  match goal with
  | H: _ /\ _ |- _ => destruct H as [H1 H2]
  | H: prod _ _ |- _ => destruct H as [H1 H2]
  | H: @ex _ _ |- _ => destruct H as [x H1]
  | H: sigT _ |- _ => destruct H as [x H1]
  end).

Lemma legal_nested_field_nested_field_rec_None_conflict: forall t gfs P,
  legal_nested_field t gfs ->
  nested_field_rec t gfs = None ->
  P.
Proof.
  intros.
  unfold legal_nested_field in H.
  rewrite H0 in H.
  simpl in H.
  tauto.
Qed.

Lemma legal_nested_field_nil_lemma: forall t, legal_nested_field t nil.
Proof.
  intros.
  unfold legal_nested_field.
  simpl.
  tauto.
Qed.

Lemma legal_nested_field_cons_lemma: forall t gf gfs, 
  legal_nested_field t (gf :: gfs) <->
  legal_nested_field t gfs /\ 
  match gf, nested_field_type2 t gfs with
  | ArraySubsc i0, Tarray t0 n a => 0 <= i0 < n
  | StructField i0, Tstruct i f a => isOK (field_type i0 f) = true
  | UnionField i0, Tunion i f a => isOK (field_type i0 f) = true
  | _, _ => False
  end.
Proof.
  intros.
  unfold legal_nested_field.
  simpl (nested_array_subsc_in_range t (gf :: gfs)).
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt; destruct gf |];
  (split; intro H;
  [destruct H as [HH0 HH1]; try inversion HH0 
  |auto_destruct_above_line;
   try solve[inversion H | inversion H0 | inversion H1 | inversion H2 | inversion H3]]).
  + simpl; tauto.
  + simpl; tauto.
  + solve_field_offset_type i0 f; [| inversion HH0].
    simpl; tauto.
  + solve_field_offset_type i0 f; [| inversion H1].
    simpl; tauto.
  + solve_field_offset_type i0 f; [| inversion HH0].
    simpl; tauto.
  + solve_field_offset_type i0 f; [| inversion H1].
    simpl; tauto.
Qed.

Lemma nested_field_rec_cons_legal_eq_Some_lemma: forall t gf gfs ofs0 t0, 
  nested_field_rec t (gf :: gfs) = Some (ofs0, t0) /\ legal_nested_field t (gf :: gfs)
  <->
  match gf, nested_field_rec t gfs with
  | ArraySubsc i0, Some (ofs, Tarray t1 n a) =>
      0 <= i0 < n /\ ofs0 = ofs + sizeof t0 * i0 /\ t0 = t1
  | StructField i0, Some (ofs, Tstruct i f a) =>
      field_type i0 f = Errors.OK t0 /\ field_offset i0 f = Errors.OK (ofs0 - ofs)
  | UnionField i0, Some (ofs, Tunion i f a) =>
      field_type i0 f = Errors.OK t0 /\ ofs0 = ofs
  | _, _ => False
  end /\ legal_nested_field t gfs.
Proof.
  intros.
  unfold legal_nested_field.
  simpl (nested_array_subsc_in_range t (gf :: gfs)).
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt; destruct gf |];
  (split; intro H; auto_destruct_above_line);
  try solve[inversion H | inversion H0 | inversion H1 | inversion H2 | inversion H3].
  + inversion H0.
    simpl; auto.
  + subst.
    simpl; auto.
  + solve_field_offset_type i0 f; inversion H; subst.
    inversion H0.
    simpl; repeat split; auto.
    f_equal; omega.
  + rewrite H1, H3.
    simpl; repeat split; auto.
    f_equal; f_equal. omega.
  + solve_field_offset_type i0 f; inversion H; subst.
    inversion H0.
    simpl; auto.
  + rewrite H1, H3.
    simpl; auto.
Qed.

Lemma nested_field_rec_cons_eq_Some_lemma: forall t gf gfs ofs0 t0, 
  nested_field_rec t (gf :: gfs) = Some (ofs0, t0)
  <->
  match gf, nested_field_rec t gfs with
  | ArraySubsc i0, Some (ofs, Tarray t1 n a) =>
      ofs0 = ofs + sizeof t0 * i0 /\ t0 = t1
  | StructField i0, Some (ofs, Tstruct i f a) =>
      field_type i0 f = Errors.OK t0 /\ field_offset i0 f = Errors.OK (ofs0 - ofs)
  | UnionField i0, Some (ofs, Tunion i f a) =>
      field_type i0 f = Errors.OK t0 /\ ofs0 = ofs
  | _, _ => False
  end.
Proof.
  intros.
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt; destruct gf |];
  (split; intro H; auto_destruct_above_line);
  try solve[inversion H | inversion H0 | inversion H1 | inversion H2].
  + inversion H; subst.
    auto.
  + subst. auto.
  + solve_field_offset_type i0 f; inversion H; subst.
    repeat split; auto.
    f_equal; omega.
  + rewrite H0, H1.
    f_equal; f_equal. omega.
  + solve_field_offset_type i0 f; inversion H; subst.
    auto.
  + rewrite H0, H1.
    auto.
  + destruct gf; inversion H.
Qed.

Ltac solve_legal_nested_field_cons H :=
  let HH := fresh "HH" in
  let Heq := fresh "Heq" in
  let HeqNFT := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  match type of H with
  | (legal_nested_field ?T (?A :: ?GFS)) =>
    destruct (legal_nested_field_cons_lemma T A GFS) as [HH _];
    specialize (HH H);
    destruct A eqn:Heq;
    destruct (nested_field_type2 T GFS) eqn:HeqNFT;
    try solve [destruct HH as [_ HH]; inversion HH]
  end;
  [try solve [inversion Heq]; destruct HH as [H1 H2]
  |try solve [inversion Heq]; destruct HH as [H1 H2]
  |try solve [inversion Heq]; destruct HH as [H1 H2]].

(*
Ltac solve_nested_field_rec_cons_legal_eq_Some H :=
  let HH := fresh "HH" in
  let Heq := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  let H4 := fresh "H" in
  let _i := fresh "i" in
  let i := fresh "i" in
  let f := fresh "f" in
  let a := fresh "a" in
  let t := fresh "t" in
  let n := fresh "n" in
  let ofs := fresh "ofs" in
  match type of H with
  | (nested_field_rec ?T (?A :: ?GFS) = Some (?OFS, ?T0)) => 
    destruct (nested_field_rec_cons_legal_eq_Some_lemma T A GFS OFS T0) as [HH _];
    match goal with
    | H0 : legal_nested_field T (A :: GFS) |- _ => specialize (HH (conj H H0))
    end;
    destruct A eqn:Heq
  end;
  [try solve [inversion Heq]; destruct HH as [[ofs [n [a [H1 [H2 H3]]]]] H4]
  |try solve [inversion Heq]; destruct HH as [[ofs [i [f [a [H1 [H2 H3]]]]]] H4]
  |try solve [inversion Heq]; destruct HH as [[i [f [a [H1 H2]]]] H4]].
*)

Ltac solve_nested_field_rec_cons_eq_Some H :=
  let HH := fresh "HH" in
  let HeqA := fresh "Heq" in
  let HeqNFT := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let ofs := fresh "ofs" in
  match type of H with
  | (nested_field_rec ?T (?A :: ?GFS) = Some (?OFS, ?T0)) => 
    destruct (nested_field_rec_cons_eq_Some_lemma T A GFS OFS T0) as [HH _];
    specialize (HH H);
    destruct A eqn:HeqA;
    destruct (nested_field_rec T GFS) as [[ofs [ | | | | | | | | | ]]|] eqn:HeqNFT;
    try solve [inversion HH]
  end;
  [try solve [inversion HeqA]; destruct HH as [H1 H2]
  |try solve [inversion HeqA]; destruct HH as [H1 H2]
  |try solve [inversion HeqA]; destruct HH as [H1 H2]].

Ltac solve_legal_nested_field :=
  first [
   solve [apply legal_nested_field_nil_lemma]
  | apply legal_nested_field_cons_lemma; simpl;
    split; [solve_legal_nested_field | auto]].

Global Opaque legal_nested_field.

Lemma sumbool_dec_iff: forall A B, {A} + {~A} -> (A <-> B) -> {B} + {~B}.
Proof.
  intros.
  destruct H.
  + left. tauto.
  + right. tauto.
Qed.

Lemma sumbool_dec_and: forall A B, {A} + {~A} -> {B} + {~B} -> {A /\ B} + {~(A /\ B)}.
Proof.
  intros.
  destruct H, H0.
  + left; tauto.
  + right; tauto.
  + right; tauto.
  + right; tauto.
Qed.

Definition legal_nested_field_dec: forall t gfs,
  {legal_nested_field t gfs} + {~ legal_nested_field t gfs}.
Proof.
  intros.
  induction gfs.
  + left. apply legal_nested_field_nil_lemma.
  + eapply sumbool_dec_iff; [| apply iff_sym, legal_nested_field_cons_lemma].
    destruct a, (nested_field_type2 t gfs); try solve [right; tauto].
    - apply sumbool_dec_and; auto.
      apply sumbool_dec_and; [apply Z_le_dec | apply Z_lt_dec].
    - apply sumbool_dec_and; auto.
      destruct (isOK (field_type i f)) eqn:?H; [left; eauto | right; congruence].
    - apply sumbool_dec_and; auto.
      destruct (isOK (field_type i f)) eqn:?H; [left; eauto | right; congruence].
Qed.

Lemma nested_field_rec_nest_pred: forall {atom_pred: type -> bool} (t: type) (gfs: list gfield) pos t', nested_pred atom_pred t = true -> nested_field_rec t gfs = Some (pos, t') -> nested_pred atom_pred t' = true.
Proof.
  intros.
  revert pos t' H0; induction gfs; intros.
  + inversion H0.
    subst.
    exact H.
  + solve_nested_field_rec_cons_eq_Some H0. 
    - (* Tarray case *)
      specialize (IHgfs _ _ eq_refl).
      subst.
      eapply nested_pred_Tarray, IHgfs.
    - (* Tstruct case *)
      specialize (IHgfs _ _ eq_refl).
      eapply nested_fields_pred_nested_pred; [exact H1 |].
      eapply nested_pred_Tstruct, IHgfs.
    - (* Tunion case *)
      specialize (IHgfs _ _ eq_refl).
      eapply nested_fields_pred_nested_pred; [exact H1 |].
      eapply nested_pred_Tunion, IHgfs.
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

(*
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
*)

Lemma nested_field_type2_nil: forall t, nested_field_type2 t nil = t.
Proof.
  intros.
  reflexivity.
Defined.

Lemma nested_field_type2_cons: forall t gf gfs0,
  nested_field_type2 t (gf :: gfs0) = 
  match gf, nested_field_type2 t gfs0 with
  | ArraySubsc i, Tarray t0 n a => t0
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
      destruct (IHgfs _ _ eq_refl).
      subst t0.
      assert (legal_alignas_type t' = true) by (eapply nested_pred_Tarray, H4).
      split; [| auto].
      rewrite legal_alignas_type_Tarray in H3 by auto.
      subst.
      apply Z.divide_add_r; try assumption.
      apply Z.divide_mul_l; try assumption.
      apply legal_alignas_sizeof_alignof_compat; auto.
    - (* Tstruct Case *)
      subst.
      destruct (IHgfs _ _ eq_refl).
      pose proof field_offset_aligned i f _ t' H2 H1.
      assert (alignof_fields f | ofs) by
        (eapply Zdivides_trans; [apply legal_alignas_type_Tstruct; exact H4 | exact H3]).
      split.
      * replace pos with ((pos - ofs) + ofs) by omega.
        apply Z.divide_add_r; try assumption.
        eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H1. exact H6.
      * eapply nested_fields_pred_nested_pred. exact H1. eapply nested_pred_Tstruct. exact H4.
    - (* Tunion Case *)
      subst.
      destruct (IHgfs _ _ eq_refl).
      assert (alignof_fields f | ofs) by
        (eapply Zdivides_trans; [apply legal_alignas_type_Tunion; exact H3 | exact H2]).
      split.
      * eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H1. exact H4.
      * eapply nested_fields_pred_nested_pred. exact H1. eapply nested_pred_Tunion. exact H3.
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
  nested_field_rec t (ArraySubsc i :: gfs) = Some (ofs + sizeof t0 * i, t0).
Proof.
  intros.
  simpl.
  rewrite H.
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
  nested_field_offset2 t (ArraySubsc i :: gfs) = nested_field_offset2 t gfs + sizeof t0 * i.
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t gfs H.
  subst.
  unfold nested_field_offset2.
  erewrite nested_field_rec_Tarray by eauto.
  rewrite H0.
  reflexivity.
Qed.

Lemma nested_field_type2_Tarray: forall t0 n a gfs t i,
  nested_field_type2 t gfs = Tarray t0 n a ->
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
  valid_nested_field_rec t gfs H0; [| inversion H1].
  subst t2.
  cut (isSome (nested_field_rec t (StructField i1 :: gfs))); intros.
  + destruct (nested_field_rec t (StructField i1 :: gfs)) as [[? ?]|] eqn:?; inversion H1.
    erewrite nested_field_rec_Tstruct_mid; eauto.
  + assert (isOK (field_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) = true).
    Focus 1. {
      rewrite fieldlist_app_field_type_isOK.
      simpl.
      if_tac; [| congruence].
      destruct (isOK (field_type i1 f')); reflexivity.
    } Unfocus.
    destruct (field_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:?H;
      [| inversion H1].
    assert (isOK (field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) = true).
    Focus 1. {
      solve_field_offset_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))).
      + reflexivity.
      + inversion H3.
    } Unfocus.
    destruct (field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:?H;
      [| inversion H4].
    erewrite nested_field_rec_Tstruct; eauto.
    simpl; auto.
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
      rewrite (IHgfs1 _ _ eq_refl).
      f_equal.
      f_equal.
      omega.
    - (* Tstruct *)
      subst.
      simpl.
      rewrite (IHgfs1 _ _ eq_refl).
      rewrite H1, H2.
      f_equal.
      f_equal.
      omega.
    - (* Tunion *)
      subst.
      simpl.
      rewrite (IHgfs1 _ _ eq_refl).
      rewrite H1.
      reflexivity.
Qed.

Lemma nested_field_rec_app_rev: forall t gfs0 gfs1 t0 t1 ofs0 ofs1,
  nested_field_rec t gfs0 = Some (ofs0, t0) ->
  nested_field_rec t (gfs1 ++ gfs0) = Some (ofs0 + ofs1, t1) ->
  nested_field_rec t0 gfs1 = Some (ofs1, t1).
Proof.
  intros.
  revert ofs1 t1 H0.
  induction gfs1; intros.
  + simpl in *.
    rewrite H in H0.
    inversion H0.
    f_equal. f_equal. omega.
  + simpl app in H0.
    solve_nested_field_rec_cons_eq_Some H0;
    apply nested_field_rec_cons_eq_Some_lemma.
    - (* Tarray *)
      specialize (IHgfs1 (ofs - ofs0) (Tarray t2 z a0)).
      replace (ofs0 + (ofs - ofs0)) with ofs in IHgfs1 by omega.
      rewrite (IHgfs1 eq_refl).
      split; [f_equal; f_equal; omega | auto].
    - (* Tstruct *)
      specialize (IHgfs1 (ofs - ofs0) (Tstruct i0 f a0)).
      replace (ofs0 + (ofs - ofs0)) with ofs in IHgfs1 by omega.
      rewrite (IHgfs1 eq_refl).
      rewrite H1, H2.
      split; [auto | f_equal; omega].
    - (* Tunion *)
      specialize (IHgfs1 ofs1 (Tunion i0 f a0)).
      subst ofs.
      rewrite (IHgfs1 eq_refl).
      rewrite H1.
      auto.
Qed.

Lemma legal_nested_field_app: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) -> legal_nested_field t gfs0.
Proof.
  intros.
  induction gfs1.
  + simpl in *; auto.
  + simpl app in H.
    solve_legal_nested_field_cons H.
    - tauto.
    - tauto.
    - tauto.
Qed.

Lemma nested_field_type2_nested_field_type2: forall t gfs0 gfs1,
  nested_field_type2 (nested_field_type2 t gfs0) gfs1 = nested_field_type2 t (gfs1 ++ gfs0).
Proof.
  intros.
  destruct (nested_field_rec t gfs0) as [[? ?] |] eqn:?H;
  unfold nested_field_type2; rewrite H.
  + destruct (nested_field_rec t0 gfs1) as [[? ?] |] eqn:?H.
    - erewrite nested_field_rec_app by eauto.
      reflexivity.
    - induction gfs1.
      * inversion H0.
      * destruct (nested_field_rec t ((a :: gfs1) ++ gfs0)) as [[? ?] |] eqn:?H; [| reflexivity].
        replace z0 with (z + (z0 - z)) in H1 by omega.
        erewrite nested_field_rec_app_rev in H0 by eauto.
        inversion H0.
  + assert (match nested_field_rec Tvoid gfs1 with
            | Some (_, t0) => t0
            | None => Tvoid
            end = Tvoid).
    Focus 1. {
      induction gfs1.
      + reflexivity.
      + simpl; destruct (nested_field_rec Tvoid gfs1) as [[? ?] |] eqn:HH; 
          inversion IHgfs1; reflexivity.
    } Unfocus.
    assert (nested_field_rec t (gfs1 ++ gfs0) = None).
    Focus 1. {
      clear H0.
      induction gfs1.
      + simpl. exact H.
      + simpl; rewrite IHgfs1; reflexivity.
    } Unfocus.
    rewrite H0, H1; reflexivity.
Qed.

Lemma legal_nested_field_app': forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) -> legal_nested_field (nested_field_type2 t gfs0) gfs1.
Proof.
  intros.
  pose proof legal_nested_field_app _ _ _ H.
  induction gfs1; intros.
  + apply legal_nested_field_nil_lemma.
  + simpl app in H.
    solve_legal_nested_field_cons H;
    specialize (IHgfs1 H1);
    apply legal_nested_field_cons_lemma;
    (split; [auto |]);
    rewrite nested_field_type2_nested_field_type2;
    rewrite Heq0; eauto.
Qed.

Lemma nested_field_offset2_app: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) ->
  nested_field_offset2 t (gfs1 ++ gfs0) = nested_field_offset2 t gfs0 +
    nested_field_offset2 (nested_field_type2 t gfs0) gfs1.
Proof.
  intros.
  pose proof (legal_nested_field_app _ _ _ H).
  pose proof (legal_nested_field_app' _ _ _ H).
  destruct (nested_field_rec t gfs0) as [[? ?] |] eqn:?H;
  unfold nested_field_type2, nested_field_offset2 in *; rewrite H2.
  + destruct (nested_field_rec t0 gfs1) as [[? ?] |] eqn:?H.
    - erewrite nested_field_rec_app by eauto.
      reflexivity.
    - rewrite H2 in H1.
      eapply legal_nested_field_nested_field_rec_None_conflict; eauto.
  + clear - H0 H2.
    eapply legal_nested_field_nested_field_rec_None_conflict; eauto.
Qed.

(************************************************

Other lemmas

************************************************)

Lemma nested_field_offset2_in_range: forall t gfs,
  legal_nested_field t gfs ->
  0 <= nested_field_offset2 t gfs /\
  (nested_field_offset2 t gfs) + sizeof (nested_field_type2 t gfs) <= sizeof t.
Proof.
  intros.
  induction gfs.
  + unfold nested_field_type2, nested_field_offset2; simpl.
    omega.
  + solve_legal_nested_field_cons H.
    - (* Tarray *)
      erewrite nested_field_offset2_Tarray by eauto.
      erewrite nested_field_type2_Tarray by eauto.
      specialize (IHgfs H0).
      destruct IHgfs.
      assert (0 <= sizeof t0) by (pose proof sizeof_pos t0; omega).
      assert (0 <= sizeof t0 * i) by (apply Z.mul_nonneg_nonneg; [exact H4 | omega]).        
      assert (sizeof t0 * i + sizeof t0 <= sizeof t0 * Z.max 0 z).
        rewrite Zred_factor3.
        apply Zmult_le_compat_l; [apply Zmax_bound_r; omega | exact H4].
      simpl in H3 |- *.
      split; omega.
    - (* Tstruct *)
      solve_field_offset_type i f; try solve [inversion H1].
      erewrite nested_field_offset2_Tstruct by eauto.
      erewrite nested_field_type2_Tstruct by eauto.
      pose proof field_offset_in_range i0 f a0 _ ofs t0 H4 H3.
      specialize (IHgfs H0).
      omega.
    - (* Tunion *)
      solve_field_offset_type i f; try solve [inversion H1].
      erewrite nested_field_offset2_Tunion; eauto.
      Focus 2. rewrite H4; simpl; reflexivity.
      erewrite nested_field_type2_Tunion by eauto.
      pose proof field_offset_in_range' i0 f a0 _ t0 H3.
      specialize (IHgfs H0).
      omega.
Qed.
  
Lemma alignof_nested_field_type2_divide: forall t gfs,
  legal_alignas_type t = true ->
  legal_nested_field t gfs ->
  (alignof (nested_field_type2 t gfs) | alignof t).
Proof.
  intros.
  induction gfs.
  + unfold nested_field_type2; simpl.
    apply Z.divide_refl.
  + assert (legal_alignas_type (nested_field_type2 t gfs) = true)
      by (apply nested_field_type2_nest_pred; auto).
    solve_legal_nested_field_cons H0;
    specialize (IHgfs H2).
    - (* Tarray *)
      erewrite nested_field_type2_Tarray by eauto.
      rewrite legal_alignas_type_Tarray in IHgfs; auto.
    - (* Tstruct *)
      solve_field_offset_type i f; try solve [inversion H3].
      erewrite nested_field_type2_Tstruct by eauto.
      pose proof alignof_type_divide_whole_fl _ _ _ H5.
      pose proof legal_alignas_type_Tstruct i f a0 H1.
      repeat (eapply Z.divide_trans; [eassumption|]).
      apply Z.divide_refl.
    - (* Tunion *)
      solve_field_offset_type i f; try solve [inversion H3].
      erewrite nested_field_type2_Tunion by eauto.
      pose proof alignof_type_divide_whole_fl _ _ _ H5.
      pose proof legal_alignas_type_Tunion i f a0 H1.
      repeat (eapply Z.divide_trans; [eassumption|]).
      apply Z.divide_refl.
Qed.

