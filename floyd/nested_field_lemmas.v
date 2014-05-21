Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

(************************************************

Lemmas about align and divide on alignof 

************************************************)

Lemma power_nat_divide: forall n m, two_power_nat n <= two_power_nat m -> Z.divide (two_power_nat n) (two_power_nat m).
Proof.
  intros.
  repeat rewrite two_power_nat_two_p in *.
  unfold Zdivide.
  exists (two_p (Z.of_nat m - Z.of_nat n)).
  assert ((Z.of_nat m) = (Z.of_nat m - Z.of_nat n) + Z.of_nat n) by omega.
  rewrite H0 at 1.
  assert (Z.of_nat m >= 0) by omega.
  assert (Z.of_nat n >= 0) by omega.
  assert (Z.of_nat n <= Z.of_nat m).
    destruct (Z_le_gt_dec (Z.of_nat n) (Z.of_nat m)).
    exact l.
    assert (Z.of_nat m < Z.of_nat n) by omega.
    assert (two_p (Z.of_nat m) < two_p (Z.of_nat n)) by (apply two_p_monotone_strict; omega).
    omega.  
  apply (two_p_is_exp (Z.of_nat m - Z.of_nat n) (Z.of_nat n)); omega.
Qed.

Lemma divide_add_align: forall a b c, Z.divide b a -> a + (align c b) = align (a + c) b.
Proof.
  intros.
  pose proof zeq b 0.
  destruct H0; unfold Z.divide in H; unfold align.
  + destruct H. subst. 
    repeat rewrite Zdiv_0_r.
    simpl.
    omega.
  + destruct H.
    subst.
    replace (x * b + c + b - 1) with (x * b + (c + b - 1)) by omega.
    rewrite Z_div_plus_full_l.
    rewrite Z.mul_add_distr_r.
    reflexivity.
    omega.
Qed.

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

(************************************************

Definition, lemmas and usefulsamples of nested_pred

nested_pred only ensure the specific property to be true on nested types with
memory assigned, i.e. inside structure of pointer, function are not included.

************************************************)

Fixpoint nested_pred (atom_pred: type -> bool) (t: type) : bool :=
  match t with
  | Tarray t0 _ _ => (atom_pred t && nested_pred atom_pred t0)%bool
  | Tstruct _ flds _ => (atom_pred t && nested_fields_pred atom_pred flds)%bool
  | Tunion _ flds _ => (atom_pred t && nested_fields_pred atom_pred flds)%bool
  | _ => atom_pred t
  end
with nested_fields_pred (atom_pred: type -> bool) (f: fieldlist) : bool :=
  match f with 
  | Fnil => true 
  | Fcons _ t f' => (nested_pred atom_pred t && nested_fields_pred atom_pred f')%bool
  end.

Lemma nested_pred_atom_pred: forall {atom_pred: type -> bool} (t: type), nested_pred atom_pred t = true -> atom_pred t = true.
Proof.
  intros.
  destruct t; simpl in *; try apply andb_true_iff in H; tauto.
Qed.

Lemma nested_pred_Tarray: forall {atom_pred: type -> bool} t n a, nested_pred atom_pred (Tarray t n a) = true -> nested_pred atom_pred t = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Qed.

Lemma nested_pred_Tstruct: forall {atom_pred: type -> bool} i f a, nested_pred atom_pred (Tstruct i f a) = true -> nested_fields_pred atom_pred f = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Qed.

Lemma nested_pred_Tunion: forall {atom_pred: type -> bool} i f a, nested_pred atom_pred (Tunion i f a) = true -> nested_fields_pred atom_pred f = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Qed.

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
Qed.

(******* Samples : no_alignas_type *************)

Definition no_alignas a : bool := match attr_alignas a with  None => true | _ => false end.

Definition no_alignas_type (t: type): bool :=
  match t with
  | Tvoid => true
  | Tint _ _ a => no_alignas a
  | Tlong _ a => no_alignas a
  | Tfloat _ a => no_alignas a
  | Tpointer _ a => no_alignas a
  | Tfunction _ _ _ => true
  | Tarray t _ a => no_alignas a
  | Tstruct _ flds a => no_alignas a
  | Tunion _ flds a => no_alignas a
  | Tcomp_ptr _ a => no_alignas a
 end.

Definition no_nested_alignas_type := nested_pred no_alignas_type.

Lemma no_alignas_type_Tstruct: forall i f a, no_alignas_type (Tstruct i f a) = true -> alignof (Tstruct i f a) = alignof_fields f.
Proof.
  intros.
  simpl.
  unfold no_alignas_type, no_alignas in H.
  destruct (attr_alignas a).
  + inversion H.
  + reflexivity.
Qed.

Lemma no_alignas_type_Tunion: forall i f a, no_alignas_type (Tunion i f a) = true -> alignof (Tunion i f a) = alignof_fields f.
Proof.
  intros.
  simpl.
  unfold no_alignas_type, no_alignas in H.
  destruct (attr_alignas a).
  + inversion H.
  + reflexivity.
Qed.

Lemma no_nested_alignas_type_Tstruct: forall i f a, no_nested_alignas_type (Tstruct i f a) = true -> alignof (Tstruct i f a) = alignof_fields f.
Proof.
  intros.
  apply nested_pred_atom_pred in H.
  apply no_alignas_type_Tstruct.
  exact H.
Qed.

Lemma no_nested_alignas_type_Tunion: forall i f a, no_nested_alignas_type (Tunion i f a) = true -> alignof (Tunion i f a) = alignof_fields f.
Proof.
  intros.
  apply nested_pred_atom_pred in H.
  apply no_alignas_type_Tunion.
  exact H.
Qed.

(******* Samples : no_replicate *************)

Fixpoint fieldlist_in (id: ident) (f: fieldlist) : bool :=
  match f with
  | Fnil => false
  | Fcons i _ f' => 
    if (Pos.eqb id i) then true else fieldlist_in id f'
  end.

Fixpoint fieldlist_no_replicate (f: fieldlist) : bool :=
  match f with
  | Fnil => true
  | Fcons i _ f' => 
    andb (negb (fieldlist_in i f')) (fieldlist_no_replicate f')
  end.

Definition nested_legal_fieldlist := nested_pred (fun t => 
  match t with
  | Tstruct i f a => fieldlist_no_replicate f
  | Tunion i f a => fieldlist_no_replicate f
  | _ => true
  end).

Lemma fieldlist_app_in: forall i f1 f2, fieldlist_in i (fieldlist_app f1 f2) = (fieldlist_in i f1 || fieldlist_in i f2) % bool.
Proof.
  intros.
  induction f1; simpl.
  + reflexivity.
  + if_tac.
    - reflexivity.
    - exact IHf1.
Qed.

Lemma fieldlist_no_replicate_fact: forall (f1 f2: fieldlist), fieldlist_no_replicate (fieldlist_app f1 f2) = true -> forall x: ident, fieldlist_in x f2 = true -> fieldlist_in x f1 = false.
Proof.
  intros.
  induction f1; simpl in *.
  + reflexivity.
  + destruct (Pos.eqb x i) eqn:Heq.
    - apply Peqb_true_eq in Heq.
      subst x.
      rewrite fieldlist_app_in in H.
      rewrite H0 in H.
      destruct (fieldlist_in i f1); inversion H.
    - apply eq_sym, andb_true_eq in H; destruct H as [_ ?]. apply eq_sym in H.
      exact (IHf1 H).
Qed.

(****************************************************************

field_type_hd, field_type_mid, field_offset_hd, field_offset_mid

****************************************************************)

Lemma field_type_hd: forall i t f, field_type i (Fcons i t f) = Errors.OK t.
Proof.
  intros.
  simpl.
  if_tac; [reflexivity | congruence].
Qed.

Lemma field_type_mid: forall i t f' f, fieldlist_no_replicate (fieldlist_app f' (Fcons i t f)) = true -> field_type i (fieldlist_app f' (Fcons i t f)) = Errors.OK t.
Proof.
  intros.
  pose proof field_type_hd i t f.
  assert (fieldlist_in i (Fcons i t f) = true) by (simpl; rewrite (Pos.eqb_refl i); reflexivity).
  remember (Fcons i t f) as f''; clear Heqf'' f.
  apply (fieldlist_no_replicate_fact _ _ H) in H1.
  induction f'.
  + exact H0.
  + simpl in *.
    destruct (Pos.eqb i i0) eqn:Heq; [inversion H1|].
    apply Pos.eqb_neq in Heq.
    destruct (ident_eq i i0); [congruence| clear n].
    apply eq_sym, andb_true_eq in H; destruct H as [_ ?]. apply eq_sym in H.
    exact (IHf' H H1).
Qed.

Lemma field_offset_hd: forall i t f, field_offset i (Fcons i t f) = Errors.OK 0.
Proof.
  intros.
  unfold field_offset.
  simpl.
  if_tac; [rewrite (align_0 _ (alignof_pos _)); reflexivity | congruence].
Qed.

Lemma field_offset_mid: forall i0 t0 i1 t1 f' f ofs, fieldlist_no_replicate (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = true -> field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK ofs -> field_offset i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK (align (ofs + sizeof t1) (alignof t0)).
Proof.
  intros.
  unfold field_offset in *.
  remember 0 as pos; clear Heqpos.
  revert pos H0; induction f'; intros.
  + simpl in *.
    destruct (Pos.eqb i1 i0) eqn:Hneq; inversion H.
    apply Pos.eqb_neq in Hneq.
    if_tac; try congruence; clear H1.
    if_tac; try congruence; clear H1.
    if_tac in H0; try congruence.
  + simpl in *.
    apply andb_true_iff in H.
    destruct H.
    destruct (fieldlist_in i (Fcons i1 t1 (Fcons i0 t0 f))) eqn:H';
      [rewrite fieldlist_app_in in H; rewrite H' in H; destruct (fieldlist_in i f'); inversion H|].
    simpl in H'.
    destruct (Pos.eqb i i1) eqn:Hneq1; [inversion H' | apply Pos.eqb_neq in Hneq1].
    destruct (Pos.eqb i i0) eqn:Hneq0; [inversion H'| apply Pos.eqb_neq in Hneq0].
    if_tac; try congruence; clear H2.
    if_tac in H0; try congruence; clear H2.
    apply (IHf' H1).
    exact H0.
Qed.

Opaque alignof.

(************************************************

Definition of nested_field_type, nested_field_offset

************************************************)

Fixpoint nested_field_rec (ids: list ident) (t: type) : option (prod Z type) :=
  match ids with
  | nil => Some (0, t)
  | hd :: tl =>
    match nested_field_rec tl t with
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

Definition nested_field_offset (ids: list ident) (t: type) : option Z :=
  match nested_field_rec ids t with
  | Some (pos, _) => Some pos
  | _ => None
  end.

Definition nested_field_type (ids: list ident) (t: type) : option type :=
  match nested_field_rec ids t with
  | Some (_, t0) => Some t0
  | _ => None
  end.

Definition nested_field_offset2 (ids: list ident) (t: type) : Z :=
  match nested_field_rec ids t with
  | Some (pos, _) => pos
  | _ => 0
  end.

Definition nested_field_type2 (ids: list ident) (t: type) : type :=
  match nested_field_rec ids t with
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
Qed.

Ltac solve_field_offset_type i f :=
  let H := fresh "H" in 
  let Hty := fresh "H" in 
  let Hofs := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  pose proof field_offset_field_type_match i f;
  destruct (field_offset i f) as [ofs|?] eqn:Hofs, (field_type i f) as [t|?] eqn:Hty;
    [clear H | inversion H | inversion H | clear H].

Ltac valid_nested_field_rec a f T :=
  let H := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  simpl in T; destruct (nested_field_rec a f) as [(ofs, t)|] eqn:H; [|inversion T].

Lemma nested_field_rec_nest_pred: forall {atom_pred: type -> bool} (ids: list ident) (t: type) pos t', nested_pred atom_pred t = true -> nested_field_rec ids t = Some (pos, t') -> nested_pred atom_pred t' = true.
Proof.
  intros.
  revert pos t' H0; induction ids; intros.
  + inversion H0.
    subst.
    exact H.
  + valid_nested_field_rec ids t H0.
    destruct t0; inversion H0; clear H3; solve_field_offset_type a f;
    inversion H0; subst; clear H0.
    - pose proof IHids ofs (Tstruct i f a0) eq_refl.
      eapply nested_fields_pred_nested_pred; [exact H3|].
      eapply nested_pred_Tstruct; exact H0.
    - pose proof IHids pos (Tunion i f a0) eq_refl.
      eapply nested_fields_pred_nested_pred; [exact H3|].
      eapply nested_pred_Tunion; exact H0.
Qed.

Lemma nested_field_type_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (ids: list ident) (t t': type), nested_pred atom_pred t = true -> nested_field_type ids t = Some t' -> nested_pred atom_pred t' = true.
Proof.
  intros.
  unfold nested_field_type in *.
  valid_nested_field_rec ids t H1.
  inversion H1; subst t0; clear H1.
  eapply nested_field_rec_nest_pred. exact H0.
  exact H2.
Qed.

Lemma nested_field_type2_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (ids: list ident) (t: type), nested_pred atom_pred t = true -> nested_pred atom_pred (nested_field_type2 ids t) = true.
Proof.
  intros.
  unfold nested_field_type2.
  valid_nested_field_rec ids t H0.
  eapply nested_field_rec_nest_pred. exact H0. exact H1.
  simpl; rewrite H, H0; reflexivity.
Qed.

Lemma field_offset_nested_field_offset: forall i f a id ofs, nested_field_offset (id :: nil) (Tstruct i f a) = Some ofs <-> field_offset id f = Errors.OK ofs.
Proof.
  intros.
  unfold nested_field_offset.
  simpl.
  solve_field_offset_type id f.
  + split; intro H; inversion H; reflexivity.
  + split; intro H; inversion H.
Qed.

Lemma field_offset_nested_field_offset2: forall i f a id ofs, field_offset id f = Errors.OK ofs -> nested_field_offset2 (id :: nil) (Tstruct i f a) = ofs.
Proof.
  intros.
  unfold nested_field_offset2.
  simpl.
  solve_field_offset_type id f.
  + inversion H; reflexivity.
  + inversion H.
Qed.

Lemma nested_field_offset2_field_offset: forall i f a id ofs, nested_field_offset2 (id :: nil) (Tstruct i f a) = ofs /\ ofs <> 0 -> field_offset id f = Errors.OK ofs.
Proof.
  unfold nested_field_offset2.
  intros.
  simpl in H.
  solve_field_offset_type id f; destruct H.
  + subst; reflexivity.
  + congruence.
Qed.

Lemma field_type_nested_field_type2: forall i f a id t, field_type id f = Errors.OK t -> nested_field_type2 (id :: nil) (Tstruct i f a) = t.
Proof.
  intros.
  unfold nested_field_type2.
  simpl.
  solve_field_offset_type id f.
  + inversion H; reflexivity.
  + inversion H.
Qed.

Lemma nested_field_type2_field_type: forall i f a id t, nested_field_type2 (id :: nil) (Tstruct i f a) = t /\ t <> Tvoid -> field_type id f = Errors.OK t.
Proof.
  unfold nested_field_type2.
  intros.
  simpl in H.
  solve_field_offset_type id f; destruct H.
  - subst; reflexivity.
  - congruence.
Qed.

Lemma nested_field_rec_divide: forall ids t pos t', nested_field_rec ids t = Some (pos, t') -> no_nested_alignas_type t = true -> Z.divide (alignof t') pos.
Proof.
  intros.
  assert ((alignof t' | pos) /\ no_nested_alignas_type t' = true); [| tauto].
  revert pos t' H; induction ids; intros.
  + inversion H. split; [apply Z.divide_0_r | inversion H; subst; exact H0].
  + valid_nested_field_rec ids t H.
    destruct t0 eqn:HH; inversion H; clear H.
    - solve_field_offset_type a f; inversion H3; clear H3. (* Tstruct Case *)
      subst.
      destruct (IHids ofs (Tstruct i f a0) eq_refl).
      pose proof field_offset_aligned a f ofs0 t' H4 H2.
      rewrite no_nested_alignas_type_Tstruct in H; [|exact H3].
      split.
      * apply Z.divide_add_r; try assumption.
        eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H2. exact H.
      * eapply nested_fields_pred_nested_pred. exact H2. apply nested_pred_Tstruct in H3. exact H3.
    - solve_field_offset_type a f; inversion H3; clear H3. (* Tunion Case *)
      subst.
      destruct (IHids pos (Tunion i f a0) eq_refl).
      pose proof field_offset_aligned a f ofs0 t' H4 H2.
      rewrite no_nested_alignas_type_Tunion in H; [|exact H3].
      split.
      * eapply Z.divide_trans. eapply alignof_type_divide_whole_fl. exact H2. exact H.
      * eapply nested_fields_pred_nested_pred. exact H2. apply nested_pred_Tunion in H3. exact H3.
Qed.

Lemma nested_field_offset2_type2_divide: forall ids t, no_nested_alignas_type t = true -> Z.divide (alignof (nested_field_type2 ids t)) (nested_field_offset2 ids t).
Proof.
  intros.
  unfold nested_field_type2, nested_field_offset2.
  valid_nested_field_rec ids t H.
  + exact (nested_field_rec_divide ids t _ _ H0 H).
  + apply Zdivide_0.
Qed.

(************************************************

************************************************)

Lemma fieldlist_app_Fnil: forall f, fieldlist_app f Fnil = f.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl. rewrite IHf. reflexivity.
Qed.

Lemma fieldlist_app_Fcons: forall f1 i t f2, fieldlist_app f1 (Fcons i t f2) = fieldlist_app (fieldlist_app f1 (Fcons i t Fnil)) f2.
Proof.
  intros.
  induction f1.
  + reflexivity.
  + simpl.
    rewrite IHf1.
    reflexivity.
Qed.

Lemma nested_field_rec_hd: forall i0 t0 ids t i f a ofs, nested_field_rec ids t = Some (ofs, Tstruct i (Fcons i0 t0 f) a) -> nested_field_rec (i0 :: ids) t = Some (ofs, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite field_offset_hd, field_type_hd.
  replace (ofs + 0) with ofs; [reflexivity | omega].
Qed.

Lemma nested_field_rec_mid: forall i1 t1 i0 t0 ids t i f' f a ofs ofs0, no_nested_alignas_type t = true -> nested_legal_fieldlist t = true -> nested_field_rec ids t = Some (ofs, Tstruct i (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a) -> nested_field_rec (i1 :: ids) t = Some (ofs0, t1) -> nested_field_rec (i0 :: ids) t = Some (align (ofs0 + sizeof t1) (alignof t0), t0).
Proof.
  intros.
  simpl in H2; rewrite H1 in H2; simpl; rewrite H1.
  pose proof (nested_field_rec_nest_pred ids t ofs _ H0 H1).
  apply nested_pred_atom_pred in H3.
  solve_field_offset_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))); inversion H2.
  subst; clear H2.
  rewrite (field_offset_mid _ _ _ _ _ _ ofs1 H3 H6).
  rewrite fieldlist_app_Fcons. rewrite fieldlist_app_Fcons in H3.
  pose proof (field_type_mid i0 t0 _ _ H3) as HH.
  rewrite HH.
  replace (align (ofs + ofs1 + sizeof t1) (alignof t0)) with (ofs + align (ofs1 + sizeof t1) (alignof t0)); [reflexivity | rewrite <- Z.add_assoc].
  apply divide_add_align.
  eapply Zdivide_trans; [| apply (nested_field_rec_divide ids t _ _ H1 H)].
  pose proof (nested_field_rec_nest_pred ids t ofs _ H H1).
  rewrite (no_nested_alignas_type_Tstruct); [| exact H2].
  rewrite fieldlist_app_Fcons.
  apply (alignof_type_divide_whole_fl i0 _ _ HH).
Qed.

Lemma nested_field_offset2_mid: forall i0 t0 i1 t1 ids t i f a f', no_nested_alignas_type t = true -> nested_field_type2 ids t = Tstruct i (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a -> fieldlist_no_replicate (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = true -> nested_field_offset2 (i0 :: ids) t = align (nested_field_offset2 (i1 :: ids) t + sizeof t1) (alignof t0).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hnoalignas H H0.
(* SearchAbout fieldlist_no_replicate. nested_legal_fieldlist *)
  unfold nested_field_offset2. simpl. unfold nested_field_type2 in H.
  destruct (nested_field_rec ids t) as [(pos, t')|] eqn:HH; [subst t' |inversion H].
  assert (HHH: nested_field_type2 ids t = Tstruct i (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) a). unfold nested_field_type2. rewrite HH. reflexivity.
  pose proof nested_field_type2_nest_pred eq_refl ids _ Hnoalignas as HHHH.
  rewrite HHH in HHHH; clear HHH.
  apply nested_field_rec_divide in HH; [|exact Hnoalignas].
  rewrite no_nested_alignas_type_Tstruct in HH; [|exact HHHH]; clear HHHH.
  pose proof field_offset_field_type_match i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) as HH1.
  pose proof field_offset_field_type_match i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) as HH2.
  destruct (field_offset i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H1;
  destruct (field_type i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H2;
  try inversion HH1;
  destruct (field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H3;
  destruct (field_type i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H4;
  try inversion HH2;
  rewrite (field_type_mid _ _ _ _ H0)in H4; inversion H4;
  rewrite fieldlist_app_Fcons in H2, H0; 
  rewrite (field_type_mid _ _ _ _ H0) in H2; inversion H2.
  subst t2 t3.
  rewrite <- fieldlist_app_Fcons in H0.
  unfold field_offset in *.
  remember 0 as pos'; clear Heqpos'.
  revert pos' H1 H3; induction f'; intros; simpl in H0, H1, H3.
  + destruct (Pos.eqb i1 i0) eqn:H; simpl in H0; try inversion H0.
    apply Pos.eqb_neq in H.
    if_tac in H1; try congruence.
    if_tac in H1; try congruence.
    if_tac in H3; try congruence.
    inversion H1.
    inversion H3.
    rewrite <- Zplus_assoc.
    apply divide_add_align.
    eapply Zdivide_trans; [|exact HH].
    eapply Zdivide_trans; [apply alignof_fields_hd_divide | apply alignof_fields_tl_divide].
  + destruct (fieldlist_in i2 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H;
      simpl in H0; try inversion H0.
    simpl fieldlist_in in H.
    rewrite fieldlist_app_in in H.
    destruct (fieldlist_in i2 f'), (fieldlist_in i2 (Fcons i1 t1 (Fcons i0 t0 f))) eqn:HH0; inversion H.
    simpl in HH0.
    destruct (Pos.eqb i2 i1) eqn:HH3; simpl in HH0; [inversion HH0|].
    destruct (Pos.eqb i2 i0) eqn:HH4; simpl in HH0; [inversion HH0|].
    apply Pos.eqb_neq in HH3. apply Pos.eqb_neq in HH4.
    if_tac in H1; try congruence.
    if_tac in H3; try congruence.
    eapply IHf'.
    - assumption.
    - eapply Zdivide_trans; [|exact HH].
      simpl fieldlist_app.
      apply alignof_fields_tl_divide.
    - exact H1.
    - exact H3.
Qed.

Lemma nested_field_offset2_hd: forall i0 t0 ids t i f a, nested_field_type2 ids t = Tstruct i (Fcons i0 t0 f) a -> nested_field_offset2 (i0 :: ids) t = nested_field_offset2 ids t.
Proof.
  intros.
  unfold nested_field_offset2. simpl. unfold nested_field_type2 in H.
  destruct (nested_field_rec ids t) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  omega.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_type2_hd: forall i0 t0 ids t i f a, nested_field_type2 ids t = Tstruct i (Fcons i0 t0 f) a -> nested_field_type2 (i0 :: ids) t = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  destruct (nested_field_rec ids t) as [(pos, t')|]; [subst t' |inversion H].
  replace (field_offset i0 (Fcons i0 t0 f)) with (Errors.OK 0).
  replace (field_type i0 (Fcons i0 t0 f)) with (Errors.OK t0).
  reflexivity.
  simpl. if_tac; [reflexivity|congruence].
  unfold field_offset. simpl. if_tac; [|congruence]. rewrite (align_0 _ (alignof_pos _)). reflexivity.
Qed.

Lemma nested_field_type2_mid: forall i0 t0 ids t i f' f a, nested_field_type2 ids t = Tstruct i (fieldlist_app f' (Fcons i0 t0 f)) a -> fieldlist_no_replicate (fieldlist_app f' (Fcons i0 t0 f)) = true -> nested_field_type2 (i0 :: ids) t = t0.
Proof.
  intros.
  unfold nested_field_type2 in *. simpl.
  valid_nested_field_rec ids t H.
  destruct t1; inversion H; clear H.
  solve_field_offset_type i0 (fieldlist_app f' (Fcons i0 t0 f)).
  + rewrite field_type_mid in H2; [|exact H0].
    inversion H2.
    reflexivity.
  + rewrite field_type_mid in H2; [|exact H0].
    inversion H2.
Qed.
