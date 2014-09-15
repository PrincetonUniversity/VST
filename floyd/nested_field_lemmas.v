Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

(************************************************

Lemmas about fieldlist_app

************************************************)

Lemma fieldlist_app_Fnil: forall f, fieldlist_app f Fnil = f.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl. rewrite IHf. reflexivity.
Defined.

Lemma fieldlist_app_Fcons: forall f1 i t f2, fieldlist_app f1 (Fcons i t f2) = fieldlist_app (fieldlist_app f1 (Fcons i t Fnil)) f2.
Proof.
  intros.
  induction f1.
  + reflexivity.
  + simpl.
    rewrite IHf1.
    reflexivity.
Defined.

Lemma fieldlist_app_field_type_isOK: forall i f1 f2, isOK (field_type i (fieldlist_app f1 f2)) = (isOK (field_type i f1) || isOK (field_type i f2)) %bool.
Proof.
  intros.
  induction f1; simpl.
  + reflexivity.
  + if_tac.
    - reflexivity.
    - exact IHf1.
Qed.

Fixpoint fieldlist_no_replicate (f: fieldlist) : bool :=
  match f with
  | Fnil => true
  | Fcons i _ f' => 
    andb (negb (isOK (field_type i f'))) (fieldlist_no_replicate f')
  end.

Lemma fieldlist_no_replicate_fact:
  forall f1 f2 i, fieldlist_no_replicate (fieldlist_app f1 f2) = true ->
  isOK (field_type i f1) = true -> isOK (field_type i f2) = true -> False.
Proof.
  intros.
  induction f1.
  + inversion H0.
  + simpl in H0, H.
    apply andb_true_iff in H.
    if_tac in H0.
    - destruct H as [? _].
      rewrite fieldlist_app_field_type_isOK in H.
      rewrite negb_true_iff, orb_false_iff in H.
      destruct H as [_ ?].
      subst.
      congruence.
    - destruct H as [_ ?].
      apply IHf1; auto.
Qed.

(************************************************

Lemmas about alignof and alignof_fields

************************************************)

Lemma alignof_fields_hd_divide: forall i t f, Zdivide (alignof t) (alignof_fields (Fcons i t f)).
Proof.
  intros.
  destruct (alignof_two_p t) as [n ?].
  destruct (alignof_fields_two_p (Fcons i t f)) as [m ?].
  assert ((alignof t) <= (alignof_fields (Fcons i t f))) by (apply Z.le_max_l).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide n m H1).
Qed.

Lemma alignof_fields_tl_divide: forall i t f, Zdivide (alignof_fields f) (alignof_fields (Fcons i t f)).
Proof.
  intros.
  destruct (alignof_fields_two_p f) as [n ?].
  destruct (alignof_fields_two_p (Fcons i t f)) as [m ?].
  assert (alignof_fields f <= alignof_fields (Fcons i t f)) by (apply Z.le_max_r).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide n m H1).
Qed.

Lemma alignof_type_divide_whole_fl: forall i t f, field_type i f = Errors.OK t -> (alignof t | alignof_fields f).
Proof.
  intros.
  induction f; simpl in H.
  + inversion H.
  + if_tac in H.
    - inversion H. apply alignof_fields_hd_divide.
    - eapply Z.divide_trans; [exact (IHf H) | apply alignof_fields_tl_divide].
Qed.

(****************************************************************

field_type_hd, field_type_mid, field_offset_hd, field_offset_mid

****************************************************************)

Lemma field_type_hd: forall i t f, field_type i (Fcons i t f) = Errors.OK t.
Proof.
  intros.
  simpl.
  if_tac; [reflexivity | congruence].
Defined.

Lemma field_type_mid: forall i t f' f, fieldlist_no_replicate (fieldlist_app f' (Fcons i t f)) = true -> field_type i (fieldlist_app f' (Fcons i t f)) = Errors.OK t.
Proof.
  intros.
  pose proof field_type_hd i t f.
  assert (isOK (field_type i (Fcons i t f)) = true) by (simpl; if_tac; [| congruence]; reflexivity).
  remember (Fcons i t f) as f''; clear Heqf'' f.
  pose proof (fun HH => fieldlist_no_replicate_fact _ _ _ H HH H1).
  clear H1.
  induction f'.
  + exact H0.
  + simpl in *.
    destruct (ident_eq i i0); [simpl in H2; congruence|].
    apply andb_true_iff in H; destruct H as [_ ?]. 
    exact (IHf' H H2).
Defined.

Lemma field_offset_hd: forall i t f, field_offset i (Fcons i t f) = Errors.OK 0.
Proof.
  intros.
  unfold field_offset.
  simpl.
  if_tac; [rewrite (align_0 _ (alignof_pos _)); reflexivity | congruence].
Defined.

Lemma field_offset_mid: forall i0 t0 i1 t1 f' f ofs, fieldlist_no_replicate (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = true -> field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK ofs -> field_offset i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK (align (ofs + sizeof t1) (alignof t0)).
Proof.
  intros.
  unfold field_offset in *.
  remember 0 as pos; clear Heqpos.
  revert pos H0; induction f'; intros.
  + simpl in *.
    if_tac.
    - if_tac in H; try congruence. inversion H.
    - if_tac in H; try congruence; clear H1.
      if_tac in H0; try congruence; clear H1.
      if_tac; try congruence.
  + simpl in *.
    apply andb_true_iff in H.
    destruct H.
    destruct (isOK (field_type i (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H';
      [rewrite fieldlist_app_field_type_isOK in H; rewrite H' in H;
       destruct (isOK (field_type i f')); inversion H|].
    simpl in H'.
    if_tac in H'; try solve [inversion H'].
    if_tac in H'; try solve [inversion H'].
    if_tac; try congruence.
    if_tac in H0; try congruence.
    apply (IHf' H1), H0.
Defined.

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

Lemma legal_alignas_type_Tarray: forall t z a,
  legal_alignas_type (Tarray t z a) = true ->
  alignof (Tarray t z a) = alignof t.
Proof.
  intros.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tarray.
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

(************************************************

Definition of nested_field_type, nested_field_offset

************************************************)

Fixpoint nested_field_rec (t: type) (ids: list ident) : option (prod Z type) :=
  match ids with
  | nil => Some (0, t)
  | hd :: tl =>
    match nested_field_rec t tl with
    | Some (pos, t') => 
      match t' with
      | Tarray _ _ _ => None (* Array case, maybe rewrite later *)
      | Tstruct _ f _ => 
        match field_offset hd f, field_type hd f with
        | Errors.OK ofs, Errors.OK t'' => Some (pos + ofs, t'')
        | _, _ => None
        end
      | Tunion _ f _ => 
        match field_type hd f with
        | Errors.OK t'' => Some (pos, t'')
        | _ => None
        end
      | _ => None
      end
    | None => None
    end
  end.

Definition nested_field_offset (t: type) (ids: list ident) : option Z :=
  match nested_field_rec t ids with
  | Some (pos, _) => Some pos
  | _ => None
  end.

Definition nested_field_type (t: type) (ids: list ident) : option type :=
  match nested_field_rec t ids with
  | Some (_, t0) => Some t0
  | _ => None
  end.

Definition nested_field_offset2 (t: type) (ids: list ident) : Z :=
  match nested_field_rec t ids with
  | Some (pos, _) => pos
  | _ => 0
  end.

Definition nested_field_type2 (t: type) (ids: list ident) : type :=
  match nested_field_rec t ids with
  | Some (_, t0) => t0
  | _ => Tvoid
  end.

Lemma field_offset_field_type_match: forall i f,
  match field_offset i f, field_type i f with
  | Errors.OK _, Errors.OK _ => True
  | Errors.Error _, Errors.Error _ => True
  | _, _ => False
  end.
Proof.
  intros.
  unfold field_offset.
  remember 0 as pos; clear Heqpos.
  revert pos; induction f; intros.
  + simpl. auto.
  + simpl. destruct (ident_eq i i0) eqn:HH.
    - auto.
    - apply IHf.
Defined.

Ltac solve_field_offset_type i f :=
  let H := fresh "H" in 
  let Hty := fresh "H" in 
  let Hofs := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  pose proof field_offset_field_type_match i f;
  destruct (field_offset i f) as [ofs|?] eqn:Hofs, (field_type i f) as [t|?] eqn:Hty;
    [clear H | inversion H | inversion H | clear H].

Ltac valid_nested_field_rec f a T :=
  let H := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  simpl in T; destruct (nested_field_rec f a) as [(ofs, t)|] eqn:H; [|inversion T].

Lemma nested_field_rec_nest_pred: forall {atom_pred: type -> bool} (t: type) (ids: list ident) pos t', nested_pred atom_pred t = true -> nested_field_rec t ids = Some (pos, t') -> nested_pred atom_pred t' = true.
Proof.
  intros.
  revert pos t' H0; induction ids; intros.
  + inversion H0.
    subst.
    exact H.
  + valid_nested_field_rec t ids H0.
    destruct t0; inversion H0; clear H3; solve_field_offset_type a f;
    inversion H0; subst; clear H0.
    - pose proof IHids ofs (Tstruct i f a0) eq_refl.
      eapply nested_fields_pred_nested_pred; [exact H3|].
      eapply nested_pred_Tstruct; exact H0.
    - pose proof IHids pos (Tunion i f a0) eq_refl.
      eapply nested_fields_pred_nested_pred; [exact H3|].
      eapply nested_pred_Tunion; exact H0.
Defined.

Lemma nested_field_type_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t t': type) (ids: list ident), nested_pred atom_pred t = true -> nested_field_type t ids = Some t' -> nested_pred atom_pred t' = true.
Proof.
  intros.
  unfold nested_field_type in *.
  valid_nested_field_rec t ids H1.
  inversion H1; subst t0; clear H1.
  eapply nested_field_rec_nest_pred. exact H0.
  exact H2.
Defined.

Lemma nested_field_type2_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (ids: list ident), nested_pred atom_pred t = true -> nested_pred atom_pred (nested_field_type2 t ids) = true.
Proof.
  intros.
  unfold nested_field_type2.
  valid_nested_field_rec t ids H0.
  eapply nested_field_rec_nest_pred. exact H0. exact H1.
  simpl; rewrite H, H0; reflexivity.
Defined.

Lemma field_offset_nested_field_offset: forall i f a id ofs, nested_field_offset (Tstruct i f a) (id :: nil) = Some ofs <-> field_offset id f = Errors.OK ofs.
Proof.
  intros.
  unfold nested_field_offset.
  simpl.
  solve_field_offset_type id f.
  + split; intro H; inversion H; reflexivity.
  + split; intro H; inversion H.
Defined.

Lemma field_offset_nested_field_offset2: forall i f a id ofs, field_offset id f = Errors.OK ofs -> nested_field_offset2 (Tstruct i f a) (id :: nil) = ofs.
Proof.
  intros.
  unfold nested_field_offset2.
  simpl.
  solve_field_offset_type id f.
  + inversion H; reflexivity.
  + inversion H.
Defined.

Lemma nested_field_offset2_field_offset: forall i f a id ofs, nested_field_offset2 (Tstruct i f a) (id :: nil) = ofs /\ ofs <> 0 -> field_offset id f = Errors.OK ofs.
Proof.
  unfold nested_field_offset2.
  intros.
  simpl in H.
  solve_field_offset_type id f; destruct H.
  + subst; reflexivity.
  + congruence.
Defined.

Lemma field_type_nested_field_type2: forall i f a id t, field_type id f = Errors.OK t -> nested_field_type2 (Tstruct i f a) (id :: nil) = t.
Proof.
  intros.
  unfold nested_field_type2.
  simpl.
  solve_field_offset_type id f.
  + inversion H; reflexivity.
  + inversion H.
Defined.

Lemma nested_field_type2_field_type: forall i f a id t, nested_field_type2 (Tstruct i f a) (id :: nil) = t /\ t <> Tvoid -> field_type id f = Errors.OK t.
Proof.
  unfold nested_field_type2.
  intros.
  simpl in H.
  solve_field_offset_type id f; destruct H.
  - subst; reflexivity.
  - congruence.
Defined.

Lemma nested_field_rec_cons_isSome_lemma: forall t id ids, 
  isSome (nested_field_rec t (id :: ids)) <->
  isSome (nested_field_rec t ids) /\ exists i f a, isOK (field_type id f) = true /\
  (nested_field_type2 t ids = Tstruct i f a \/ nested_field_type2 t ids = Tunion i f a).
Proof.
  intros.
  simpl (nested_field_rec t (id :: ids)).
  unfold nested_field_type2.
  destruct (nested_field_rec t ids) as [[? tt]|]; [destruct tt |]; 
  (split; intros; [try inversion H | destruct H as [? [? [? [? [? [? | ?]]]]]]]; try inversion H1).
  + simpl; split; auto; exists i, f, a.
    destruct (field_type id f); simpl.
      auto.
      destruct (field_offset id f); inversion H.
  + subst.
    solve_field_offset_type id x0. simpl; auto. inversion H0.
  + simpl; split; auto; exists i, f, a.
    destruct (field_type id f); simpl.
      auto.
      destruct (field_offset id f); inversion H.
  + subst.
    solve_field_offset_type id x0. simpl; auto. inversion H0.
Qed.

Definition iffT A B := ((A -> B) * (B -> A))%type.

Definition nested_field_rec_cons_isSome_lemmaT: forall t id ids, 
  iffT (isSome (nested_field_rec t (id :: ids)))
  (isSome (nested_field_rec t ids) * sigT (fun i => sigT (fun f => sigT (fun a => 
  (isOK (field_type id f) = true) * ((nested_field_type2 t ids = Tstruct i f a) + (nested_field_type2 t ids = Tunion i f a)))))%type).
Proof.
  intros.
  simpl (nested_field_rec t (id :: ids)).
  unfold nested_field_type2.
  destruct (nested_field_rec t ids) as [[? tt]|]; [destruct tt |];
  (split; intro H; [try inversion H | destruct H as [? [? [? [? [? [H1 | H1]]]]]]]; try inversion H1).
  + simpl; split; auto; exists i, f, a.
    destruct (field_type id f); simpl.
      auto.
      destruct (field_offset id f); inversion H.
  + subst.
    solve_field_offset_type id x0. simpl; auto. inversion e.
  + simpl; split; auto; exists i, f, a.
    destruct (field_type id f); simpl.
      auto.
      destruct (field_offset id f); inversion H.
  + subst.
    solve_field_offset_type id x0. simpl; auto. inversion e.
Defined.

Ltac solve_nested_field_rec_cons_isSome H :=
  let HH := fresh "HH" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  let i := fresh "i" in
  let f := fresh "f" in
  let a := fresh "a" in
  let i' := fresh "i" in
  let f' := fresh "f" in
  let a' := fresh "a" in
  match type of H with
  | isSome (nested_field_rec ?T (?A :: ?IDS)) =>
    destruct (nested_field_rec_cons_isSome_lemmaT T A IDS) as [HH _];
    destruct (HH H) as [H1 [i' [f' [a' [H2 [H3 | H3]]]]]]; clear HH;
    rename i' into i;
    rename f' into f;
    rename a' into a
  end.

Lemma nested_field_type2_Tstruct_nested_field_rec_isSome: forall t ids i f a,
  nested_field_type2 t ids = Tstruct i f a -> isSome (nested_field_rec t ids).
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t ids H.
  simpl; auto.
Defined.

Lemma nested_field_type2_Tunion_nested_field_rec_isSome: forall t ids i f a,
  nested_field_type2 t ids = Tunion i f a -> isSome (nested_field_rec t ids).
Proof.
  intros.
  unfold nested_field_type2 in H.
  valid_nested_field_rec t ids H.
  simpl; auto.
Defined.

Lemma nested_field_type2_nil: forall t, nested_field_type2 t nil = t.
Proof.
  intros.
  reflexivity.
Defined.

Lemma nested_field_type2_cons: forall t id ids0,
  nested_field_type2 t (id :: ids0) = 
  match nested_field_type2 t ids0 with
  | Tstruct i f a => match field_offset id f, field_type id f with
                     | Errors.OK _, Errors.OK t0 => t0
                     | _, _ => Tvoid
                     end
  | Tunion i f a  => match field_type id f with
                     | Errors.OK t0 => t0
                     | _ => Tvoid
                     end
  | _ => Tvoid
  end.
Proof.
  intros.
  unfold nested_field_type2 in *.
  simpl.
  destruct (nested_field_rec t ids0) eqn:HH; try reflexivity.
  destruct p.
  destruct t0; try reflexivity;
  destruct (field_offset id f), (field_type id f); reflexivity.
Defined.

Lemma nested_field_rec_divide: forall t ids pos t', nested_field_rec t ids = Some (pos, t') -> legal_alignas_type t = true -> Z.divide (alignof t') pos.
Proof.
  intros.
  assert ((alignof t' | pos) /\ legal_alignas_type t' = true); [| tauto].
  revert pos t' H; induction ids; intros.
  + inversion H. split; [apply Z.divide_0_r | inversion H; subst; exact H0].
  + valid_nested_field_rec t ids H.
    destruct t0 eqn:HH; inversion H; clear H.
    - solve_field_offset_type a f; inversion H3; clear H3. (* Tstruct Case *)
      subst.
      destruct (IHids ofs (Tstruct i f a0) eq_refl).
      pose proof field_offset_aligned a f ofs0 t' H4 H2.
      assert (alignof_fields f | ofs) by
        (eapply Zdivides_trans; [apply legal_alignas_type_Tstruct; exact H3 | exact H]).
      clear H; rename H6 into H.
      split.
      * apply Z.divide_add_r; try assumption.
        eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H2. exact H.
      * eapply nested_fields_pred_nested_pred. exact H2. apply nested_pred_Tstruct in H3. exact H3.
    - solve_field_offset_type a f; inversion H3; clear H3. (* Tunion Case *)
      subst.
      destruct (IHids pos (Tunion i f a0) eq_refl).
      pose proof field_offset_aligned a f ofs0 t' H4 H2.
      assert (alignof_fields f | pos) by
        (eapply Zdivides_trans; [apply legal_alignas_type_Tunion; exact H3 | exact H]).
      clear H; rename H6 into H.
      split.
      * eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H2. exact H.
      * eapply nested_fields_pred_nested_pred. exact H2. apply nested_pred_Tunion in H3. exact H3.
Defined.

Lemma nested_field_offset2_type2_divide: forall ids t, legal_alignas_type t = true -> Z.divide (alignof (nested_field_type2 t ids)) (nested_field_offset2 t ids).
Proof.
  intros.
  unfold nested_field_type2, nested_field_offset2.
  valid_nested_field_rec t ids H.
  + exact (nested_field_rec_divide t ids  _ _ H0 H).
  + apply Zdivide_0.
Defined.

(************************************************

nested_field_rec_Tstruct_hd
nested_field_rec_Tstruct_mid
nested_field_rec_Tunion_hd
nested_field_rec_Tunion_mid

************************************************)

Lemma nested_field_rec_Tstruct_hd: forall i0 t0 ids t i f a ofs,
  nested_field_rec t ids = Some (ofs, Tstruct i (Fcons i0 t0 f) a) ->
  nested_field_rec t (i0 :: ids) = Some (ofs, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite field_offset_hd, field_type_hd.
  replace (ofs + 0) with ofs; [reflexivity | omega].
Qed.

Lemma nested_field_rec_Tunion_hd: forall i0 t0 ids t i f a ofs,
  nested_field_rec t ids = Some (ofs, Tunion i (Fcons i0 t0 f) a) ->
  nested_field_rec t (i0 :: ids) = Some (ofs, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite field_type_hd.
  reflexivity.
Qed.

Lemma nested_field_rec_Tstruct_mid:
  forall i1 t1 t1' i0 t0 t ids i f' f a ofs ofs0,
  legal_alignas_type t = true -> 
  nested_legal_fieldlist t = true ->
  nested_field_rec t ids = Some (ofs, Tstruct i 
    (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a) -> 
  nested_field_rec t (i1 :: ids) = Some (ofs0, t1') ->
  nested_field_rec t (i0 :: ids) = 
    Some (align (ofs0 + sizeof t1) (alignof t0), t0).
Proof.
  intros.
  simpl in H2; rewrite H1 in H2; simpl; rewrite H1.
  pose proof (nested_field_rec_nest_pred t ids ofs _ H0 H1).
  apply nested_pred_atom_pred in H3.
  solve_field_offset_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))); inversion H2.
  subst; clear H2.
  rewrite (field_offset_mid _ _ _ _ _ _ ofs1 H3 H6).
  rewrite fieldlist_app_Fcons. rewrite fieldlist_app_Fcons in H3.
  pose proof (field_type_mid i0 t0 _ _ H3) as HH.
  rewrite HH.
  replace (align (ofs + ofs1 + sizeof t1) (alignof t0)) with (ofs + align (ofs1 + sizeof t1) (alignof t0)); [reflexivity | rewrite <- Z.add_assoc].
  apply divide_add_align.
  eapply Zdivide_trans; [| apply (nested_field_rec_divide t ids _ _ H1 H)].
  pose proof (nested_field_rec_nest_pred t ids ofs _ H H1).
  eapply Zdivides_trans; [| apply legal_alignas_type_Tstruct; exact H2].
  rewrite fieldlist_app_Fcons.
  apply (alignof_type_divide_whole_fl i0 _ _ HH).
Qed.

Lemma nested_field_rec_Tunion_mid:
  forall i0 t0 t ids i f' f a ofs,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_rec t ids = Some (ofs,
    Tunion i (fieldlist_app f' (Fcons i0 t0 f)) a) ->
  nested_field_rec t (i0 :: ids) = Some (ofs, t0).
Proof.
  intros.
  pose proof (nested_field_rec_nest_pred t ids ofs _ H0 H1).
  apply nested_pred_atom_pred in H2.
  simpl.
  rewrite H1.
  rewrite (field_type_mid i0 t0 _ _ H2).
  reflexivity.
Qed.

(* These four lemmas are not used for now. But it is good to put them into *)
(* a proof system and open to users. If in that case, 4 more lemmas about  *)
(* Tunion should be added.                                                 *)

Lemma nested_field_offset2_Tstruct_hd: forall i0 t0 t ids i f a, nested_field_type2 t ids = Tstruct i (Fcons i0 t0 f) a -> nested_field_offset2 t (i0 :: ids) = nested_field_offset2 t ids.
Proof.
  intros.
  unfold nested_field_offset2. simpl. unfold nested_field_type2 in H.
  destruct (nested_field_rec t ids) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  omega.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_type2_Tstruct_hd: forall i0 t0 t ids i f a, nested_field_type2 t ids = Tstruct i (Fcons i0 t0 f) a -> nested_field_type2 t (i0 :: ids) = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  destruct (nested_field_rec t ids) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  reflexivity.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_offset2_Tstruct_mid: forall i0 t0 i1 t1 t ids i f a f', 
  legal_alignas_type t = true -> 
  nested_legal_fieldlist t = true ->
  nested_field_type2 t ids = Tstruct i (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a -> 
  nested_field_offset2 t (i0 :: ids) = 
  align (nested_field_offset2 t (i1 :: ids) + sizeof t1) (alignof t0).
Proof.
  intros.
  unfold nested_field_type2, nested_field_offset2 in *.
  valid_nested_field_rec t ids H0.
  subst t2.
  cut (isSome (nested_field_rec t (i1 :: ids))); intros.
  + destruct (nested_field_rec t (i1 :: ids)) as [[? ?]|] eqn:?; inversion H1.
    erewrite nested_field_rec_Tstruct_mid; eauto.
  + apply nested_field_rec_cons_isSome_lemma.
    unfold nested_field_type2.
    rewrite H2.
    simpl.
    split; [exact I | exists i, (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))), a ].
    rewrite field_type_mid.
    simpl; eauto.
    unfold nested_legal_fieldlist in H0.
    eapply nested_field_type2_nest_pred with (ids0 := ids) in H0; [| reflexivity].
    apply nested_pred_atom_pred in H0.
    unfold nested_field_type2 in H0.
    rewrite H2 in H0.
    exact H0.
  + inversion H1.
Qed.

Lemma nested_field_type2_Tstruct_mid: forall i0 t0 t ids i f' f a,
  nested_field_type2 t ids = Tstruct i (fieldlist_app f' (Fcons i0 t0 f)) a ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t (i0 :: ids) = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  valid_nested_field_rec t ids H.
  eapply nested_field_type2_nest_pred with (ids0 := ids) in H0; [| reflexivity].
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
