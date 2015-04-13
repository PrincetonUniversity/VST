Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Import floyd.fieldlist.fieldlist.
Require Import floyd.type_induction.
Open Scope Z.

Definition composite_legal_alignas (env : composite_env) (co : composite) : Prop :=
  (co_alignof co >=? alignof_composite env (co_members co)) = true.

Definition composite_env_legal_alignas env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_alignas env co.

Definition composite_legal_fieldlist (co: composite): Prop :=
  compute_list_norepet (map fst (co_members co)) = true.

Definition composite_env_legal_fieldlist env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_fieldlist co.

Class compspecs_legal (C: compspecs) := mkCompspecsLegal {
  cenv_legal_alignas: composite_env_legal_alignas cenv_cs;
  cenv_legal_fieldlist: composite_env_legal_fieldlist cenv_cs
}.

(************************************************

Definition, lemmas and useful samples of nested_pred

nested_pred only ensure the specific property to be true on nested types with
memory assigned, i.e. inside structure of pointer, function, empty array are
not included.

************************************************)

Lemma fold_right_map: forall {A B C} (f: B -> A -> A) (g: C -> B) (e: A) (l: list C),
  fold_right f e (map g l) = fold_right (fun c a => f (g c) a) e l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    rewrite IHl.
    reflexivity.
Qed.

Section COMPOSITE_ENV.
Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Definition nested_pred (atom_pred: type -> bool): type -> bool :=
  func_type
    (fun _ => bool)
    (fun t => atom_pred t)
    (fun t n a b => (atom_pred (Tarray t n a) && b)%bool)
    (fun id a bl => (atom_pred (Tstruct id a) && fold_right andb true (decay bl))%bool)
    (fun id a bl => (atom_pred (Tunion id a) && fold_right andb true (decay bl))%bool).

Definition nested_fields_pred (atom_pred: type -> bool) (m: members) : bool :=
  fold_right (fun it b => (nested_pred atom_pred (snd it) && b)%bool) true m.

Lemma nested_pred_ind: forall atom_pred t,
  nested_pred atom_pred t = 
  match t with
  | Tarray t0 _ _ => (atom_pred t && nested_pred atom_pred t0)%bool
  | Tstruct id _
  | Tunion id _ => (atom_pred t && nested_fields_pred atom_pred (co_members (get_co id)))%bool
  | _ => atom_pred t
  end.
Proof.
  unfold nested_fields_pred.
  intros.
  unfold nested_pred.
  rewrite func_type_ind with (t0 := t) at 1 by auto.
  destruct t; auto.
  + f_equal.
    rewrite decay_spec.
    rewrite fold_right_map.
    reflexivity.
  + f_equal.
    rewrite decay_spec.
    rewrite fold_right_map.
    reflexivity.
Defined.

Lemma nested_pred_atom_pred: forall (atom_pred: type -> bool) (t: type),
  nested_pred atom_pred t = true -> atom_pred t = true.
Proof.
  intros.
  rewrite nested_pred_ind in H by auto.
  destruct t; simpl in *;
   try (destruct (cenv_cs ! i) eqn:HH; simpl in H; try rewrite HH in H);
   try apply andb_true_iff in H; try tauto.
Defined.

Lemma nested_pred_Tarray: forall (atom_pred: type -> bool) t n a,
  nested_pred atom_pred (Tarray t n a) = true -> nested_pred atom_pred t = true.
Proof.
  intros.
  rewrite nested_pred_ind in H by auto.
  apply andb_true_iff in H.
  tauto.
Defined.

Lemma nested_pred_Tstruct: forall (atom_pred: type -> bool) id a,
  nested_pred atom_pred (Tstruct id a) = true -> nested_fields_pred atom_pred (co_members (get_co id)) = true.
Proof.
  intros.
  rewrite nested_pred_ind in H by auto.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_pred_Tunion: forall (atom_pred: type -> bool) id a,
  nested_pred atom_pred (Tunion id a) = true -> nested_fields_pred atom_pred (co_members (get_co id)) = true.
Proof.
  intros.
  rewrite nested_pred_ind in H by auto.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_fields_pred_hd: forall (atom_pred: type -> bool) i t m,
  nested_fields_pred atom_pred ((i, t) :: m) = true ->
  nested_pred atom_pred t = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Defined.

Lemma nested_fields_pred_tl: forall (atom_pred: type -> bool) i t m,
  nested_fields_pred atom_pred ((i, t) :: m) = true ->
  nested_fields_pred atom_pred m = true.
Proof.
  intros.
  simpl in H.
  apply andb_true_iff in H; tauto.
Defined.

Lemma fold_right_andb: forall bl b, fold_right andb b bl = true -> forall b0, In b0 bl -> b0 = true.
Proof.
  intros.
  induction bl.
  + inversion H0.
  + destruct H0.
    - simpl in H.
      rewrite andb_true_iff in H.
      subst; tauto.
    - simpl in H.
      rewrite andb_true_iff in H.
      tauto.
Qed.

Lemma nested_fields_pred_nested_pred: forall (atom_pred: type -> bool) i m, in_members i m -> nested_fields_pred atom_pred m = true -> nested_pred atom_pred (field_type i m) = true.
Proof.
  intros.
  unfold nested_fields_pred in H0.
  rewrite <- fold_right_map in H0.
  eapply fold_right_andb; [exact H0 |].
  clear - H.
  rewrite <- map_map.
  apply in_map.
  change (field_type i m) with (snd (i, field_type i m)).
  apply in_map.
  apply in_members_field_type.
  auto.
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
  | Tvoid
  | Tfunction _ _ _ => true
  | Tint _ _ a
  | Tlong _ a
  | Tfloat _ a
  | Tpointer _ a 
  | Tarray _ _ a
  | Tstruct _ a
  | Tunion _ a => match attr_alignas a with | Some _ => false | None => true end
  end.

Definition legal_alignas_type := nested_pred local_legal_alignas_type.

Hint Extern 0 (legal_alignas_type _ = true) => reflexivity : cancel.

Lemma power_nat_divide': forall n m: Z,
  (exists N, n = two_power_nat N) ->
  (exists M, m = two_power_nat M) ->
  n >=? m = true ->
  (m | n).
Proof.
  intros.
  destruct H, H0.
  subst.
  apply power_nat_divide.
  pose proof Zge_cases (two_power_nat x) (two_power_nat x0).
  destruct (two_power_nat x >=? two_power_nat x0); try omega.
  inversion H1.
Qed.

Lemma local_legal_alignas_type_Tarray: forall t z a,
  local_legal_alignas_type (Tarray t z a) = true ->
  alignof cenv_cs (Tarray t z a) = alignof cenv_cs t.
Proof.
  intros.
  simpl in H |- *.
  unfold align_attr.
  destruct (attr_alignas a); [inversion H |].
  auto.
Qed.

Lemma local_legal_alignas_type_Tstruct: forall id a,
  local_legal_alignas_type (Tstruct id a) = true ->
  (alignof_composite cenv_cs (co_members (get_co id)) | alignof cenv_cs (Tstruct id a)).
Proof.
  intros.
  unfold local_legal_alignas_type in H.
  unfold alignof, align_attr.
  simpl attr_of_type.
  destruct (attr_alignas a); [inversion H |].
  unfold get_co; destruct (cenv_cs ! id) as [co |] eqn:CO; [| exists 1; auto].
  apply power_nat_divide';
  try apply alignof_composite_two_p;
  try apply co_alignof_two_p.
  exact (cenv_legal_alignas id co CO).
Qed.

Lemma local_legal_alignas_type_Tunion: forall id a,
  local_legal_alignas_type (Tunion id a) = true ->
  (alignof_composite cenv_cs (co_members (get_co id)) | alignof cenv_cs (Tunion id a)).
Proof.
  intros.
  unfold local_legal_alignas_type in H.
  unfold alignof, align_attr.
  simpl attr_of_type.
  destruct (attr_alignas a); [inversion H |].
  unfold get_co; destruct (cenv_cs ! id) as [co |] eqn:CO; [| exists 1; auto].
  apply power_nat_divide';
  try apply alignof_composite_two_p;
  try apply co_alignof_two_p.
  exact (cenv_legal_alignas id co CO).
Qed.

Lemma legal_alignas_type_Tarray: forall t z a,
  legal_alignas_type (Tarray t z a) = true ->
  alignof cenv_cs (Tarray t z a) = alignof cenv_cs t.
Proof.
  intros.
  unfold legal_alignas_type in H.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tarray.
  exact H.
Qed.

Lemma legal_alignas_type_Tstruct: forall id a,
  legal_alignas_type (Tstruct id a) = true ->
  (alignof_composite cenv_cs (co_members (get_co id)) | alignof cenv_cs (Tstruct id a)).
Proof.
  intros.
  unfold legal_alignas_type in H.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tstruct; auto.
Qed.

Lemma legal_alignas_type_Tunion: forall id a,
  legal_alignas_type (Tunion id a) = true ->
  (alignof_composite cenv_cs (co_members (get_co id)) | alignof cenv_cs (Tunion id a)).
Proof.
  intros.
  unfold legal_alignas_type in H.
  apply nested_pred_atom_pred in H.
  apply local_legal_alignas_type_Tunion; auto.
Qed.

Lemma legal_alignas_sizeof_alignof_compat: forall t,
  legal_alignas_type t = true -> (alignof cenv_cs t | sizeof cenv_cs t).
Proof.
  intros.
  revert H.
  type_induction t; intros;
  pose proof @nested_pred_atom_pred local_legal_alignas_type _ H as H0;
  simpl in H, H0 |- *; unfold align_attr in *;
  try (destruct (attr_alignas a); inversion H0).
  - apply Z.divide_refl.
  - destruct i; apply Z.divide_refl.
  - unfold Z.divide. exists 2. reflexivity.
  - destruct f. apply Z.divide_refl.
    unfold Z.divide. exists 2. reflexivity.
  - apply Z.divide_refl.
  - apply (nested_pred_Tarray local_legal_alignas_type) in H.
    apply IH in H.
    apply Z.divide_mul_l.
    exact H.
  - apply Z.divide_refl.
  - destruct (cenv_cs ! id) as [co |] eqn:CO.
    * apply co_sizeof_alignof.
    * exists 0; auto.
  - destruct (cenv_cs ! id) as [co |] eqn:CO.
    * apply co_sizeof_alignof.
    * exists 0; auto.
Qed.

Opaque alignof.

(************************************************

Definition of nested_field_type2, nested_field_offset2

The principle of this part is only exposing nft2 and nfo2 to users 
and hide the implimentation of nf_rec

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
      | Tarray t'' n _, ArraySubsc i => Some(pos + sizeof cenv_cs t'' * i, t'')
      | Tstruct id _, StructField i =>
        if compute_in_members i (co_members (get_co id)) then
          Some (pos + field_offset cenv_cs i (co_members (get_co id)), field_type i (co_members (get_co id)))
        else
          None
      | Tunion id _, UnionField i =>
        if compute_in_members i (co_members (get_co id)) then
          Some (pos, field_type i (co_members (get_co id)))
        else
          None
      | _, _ => None
      end
    | None => None
    end
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

Definition gfield_type t gf :=
  match t, gf with
  | Tarray t0 _ _, ArraySubsc _ => t0
  | Tstruct id _, StructField i
  | Tunion id _, UnionField i => field_type i (co_members (get_co id))
  | _, _ => Tvoid
  end.

Definition gfield_offset t gf :=
  match t, gf with
  | Tarray t0 _ _, ArraySubsc i => sizeof cenv_cs t0 * i
  | Tstruct id _, StructField i => field_offset cenv_cs i (co_members (get_co id))
  | Tunion id _, UnionField i => 0
  | _, _ => 0
  end.

Definition legal_field t gf :=
  match t, gf with
  | Tarray _ n _, ArraySubsc i => 0 <= i < n
  | Tstruct id _, StructField i => co_su (get_co id) = Struct /\ in_members i (co_members (get_co id))
  | Tunion id _, UnionField i => co_su (get_co id) = Union /\ in_members i (co_members (get_co id))
  | _, _ => False
  end.

Fixpoint legal_nested_field (t: type) (gfs: list gfield) : Prop :=
  match gfs with
  | nil => True
  | gf :: gfs0 => legal_nested_field t gfs0 /\ legal_field (nested_field_type2 t gfs0) gf
  end.

Lemma nested_field_type2_ind: forall t gfs,
  nested_field_type2 t gfs =
  match gfs with
  | nil => t
  | gf :: gfs0 => gfield_type (nested_field_type2 t gfs0) gf
  end.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [reflexivity |].
  unfold nested_field_type2.
  simpl.
  destruct (nested_field_rec t gfs) as [[ofs0 t0] |] eqn:NFR; [| reflexivity].
  destruct t0 as [| | | | | | | id ? | id ?]; destruct gf; try reflexivity.
  + destruct_in_members i (co_members (get_co id)).
    - reflexivity.
    - simpl.
      rewrite not_in_members_field_type; auto.
  + destruct_in_members i (co_members (get_co id)).
    - reflexivity.
    - simpl.
      rewrite not_in_members_field_type; auto.
Defined.

Lemma nested_field_offset2_ind: forall t gfs,
  legal_nested_field t gfs ->
  nested_field_offset2 t gfs =
  match gfs with
  | nil => 0
  | gf :: gfs0 => nested_field_offset2 t gfs0 + gfield_offset (nested_field_type2 t gfs0) gf 
  end.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [reflexivity |].
  destruct H.
  unfold nested_field_type2, nested_field_offset2 in *.
  simpl.
  destruct (nested_field_rec t gfs) as [[ofs0 t0] |] eqn:NFR; [| reflexivity].
  destruct t0 as [| | | | | | | id ? | id ?]; destruct gf; try inversion H0; auto.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    reflexivity.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    simpl. omega.
Qed.

(*
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

Lemma nested_field_rec_cons_eq_Some_lemma: forall t gf gfs ofs0 t0, 
  nested_field_rec t (gf :: gfs) = Some (ofs0, t0)
  <->
  match gf, nested_field_rec t gfs with
  | ArraySubsc i0, Some (ofs, Tarray t1 n a) =>
      ofs0 = ofs + sizeof cenv_cs t0 * i0 /\ t0 = t1
  | StructField i, Some (ofs, Tstruct id a) =>
      in_members i (co_members (get_co id)) /\ co_su (get_co id) = Struct /\ t0 = field_type2 i (co_members (get_co id)) /\ ofs0 = ofs + field_offset2 cenv_cs i (co_members (get_co id))
  | UnionField i, Some (ofs, Tunion id a) =>
      in_members i (co_members (get_co id)) /\ co_su (get_co id) = Union /\ t0 = field_type2 i (co_members (get_co id)) /\ ofs0 = ofs
  | _, _ => False
  end.
Proof.
  intros.
  simpl (nested_field_rec t (gf :: gfs)).
  unfold nested_field_type2.
  destruct (nested_field_rec t gfs) as [[? tt]| ]; [destruct tt |]; destruct gf;
  (split; intro H; auto_destruct_above_line);
  try solve[inversion H | inversion H0 | inversion H1 | inversion H2].
  + inversion H; subst.
    auto.
  + subst. auto.
  + unfold destruct (cenv_cs ! i); [| inversion H].
    destruct (co_su c); [| inversion H].
    destruct_in_members i0 (co_members c); [| inversion H].
    inversion H.
    auto.
  + destruct (cenv_cs ! i); [| inversion H].
    auto_destruct_above_line.
    apply compute_in_members_true_iff in H0.
    rewrite H, H0.
    subst; auto.
  + destruct (cenv_cs ! i); [| inversion H].
    destruct (co_su c); [inversion H |].
    destruct_in_members i0 (co_members c); [| inversion H].
    inversion H.
    auto.
  + destruct (cenv_cs ! i); [| inversion H].
    auto_destruct_above_line.
    apply compute_in_members_true_iff in H0.
    rewrite H, H0.
    subst; auto.
Qed.

Ltac solve_legal_nested_field_cons H :=
  let HH := fresh "HH" in
  let Heq := fresh "Heq" in
  let HeqNFT := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  let id := fresh "id" in
  let co := fresh "co" in
  let CO := fresh "CO" in
  match type of H with
  | (legal_nested_field ?T (?A :: ?GFS)) =>
    destruct (legal_nested_field_cons_lemma T A GFS) as [HH _];
    specialize (HH H);
    destruct A eqn:Heq;
    destruct (nested_field_type2 T GFS) as [ | | | | | | | id ? | id ? ] eqn:HeqNFT;
    try solve [destruct HH as [_ HH]; inversion HH]
  end;
  [try solve [inversion Heq]; destruct HH as [H1 H2]
  |try solve [inversion Heq]; destruct HH as [H1 H2];
   destruct (cenv_cs ! id) as [co |] eqn:CO; [| inversion H2];
   destruct H2 as [H2 H3]
  |try solve [inversion Heq]; destruct HH as [H1 H2];
   destruct (cenv_cs ! id) as [co |] eqn:CO; [| inversion H2];
   destruct H2 as [H2 H3]].

Ltac solve_nested_field_rec_cons_eq_Some H :=
  let HH := fresh "HH" in
  let HeqA := fresh "Heq" in
  let HeqNFT := fresh "Heq" in
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  let H4 := fresh "H" in
  let ofs := fresh "ofs" in
  let id := fresh "id" in
  let co := fresh "co" in
  let CO := fresh "CO" in
  match type of H with
  | (nested_field_rec ?T (?A :: ?GFS) = Some (?OFS, ?T0)) => 
    destruct (nested_field_rec_cons_eq_Some_lemma T A GFS OFS T0) as [HH _];
    specialize (HH H);
    destruct A eqn:HeqA;
    destruct (nested_field_rec T GFS) as [[ofs [ | | | | | | | id ? | id ? ]]|] eqn:HeqNFT;
    try solve [inversion HH]
  end;
  [try solve [inversion HeqA]; destruct HH as [H1 H2]
  |try solve [inversion HeqA]; destruct (cenv_cs ! id) as [co |] eqn:CO; [| inversion HH];
   destruct HH as [H1 [H2 [H3 H4]]]
  |try solve [inversion HeqA]; destruct (cenv_cs ! id) as [co |] eqn:CO; [| inversion HH];
   destruct HH as [H1 [H2 [H3 H4]]]].

Ltac solve_legal_nested_field :=
  first [
   solve [apply legal_nested_field_nil_lemma]
  | apply legal_nested_field_cons_lemma; simpl;
    split; [solve_legal_nested_field | auto]].

Global Opaque legal_nested_field.
*)

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
  + left. exact I.
  + simpl.
    apply sumbool_dec_and; [auto |].
    destruct a, (nested_field_type2 t gfs) as [| | | | | | | id ? | id ?]; try solve [right; tauto];
    unfold legal_field.
    - apply sumbool_dec_and; [apply Z_le_dec | apply Z_lt_dec].
    - apply sumbool_dec_and; [destruct (co_su (get_co id)); [left; auto | right; congruence] |].
      apply in_members_dec.
    - apply sumbool_dec_and; [destruct (co_su (get_co id)); [right; congruence | left; auto] |].
      apply in_members_dec.
Qed.

Definition field_compatible t gfs p :=
  isptr p /\
  legal_alignas_type t = true /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field t gfs.

Lemma field_compatible_dec: forall t gfs p,
  {field_compatible t gfs p} + {~ field_compatible t gfs p}.
Proof.
  unfold field_compatible.
  intros.
  repeat apply sumbool_dec_and.
  + destruct p; simpl; try (left; tauto); try (right; tauto).
  + destruct legal_alignas_type; [left | right]; congruence.
  + destruct p; simpl; try solve [left; auto].
    destruct (zle (Int.unsigned i + sizeof cenv_cs t) Int.modulus); [left | right]; omega.
  + destruct p; simpl; try solve [left; auto].
    apply Zdivide_dec.
    apply alignof_pos.
  + apply legal_nested_field_dec.
Qed.

Lemma field_compatible_cons_Tarray:
  forall i t t0 n a gfs p,
  nested_field_type2 t gfs = Tarray t0 n a ->
  field_compatible t gfs p ->
  (0 <= i < n)%Z ->
  field_compatible t (ArraySubsc i :: gfs) p.
Proof.
unfold field_compatible; intros; intuition.
simpl.
rewrite H.
simpl.
auto.
Qed.

Definition field_address t gfs p :=
  if (field_compatible_dec t gfs p)
  then offset_val (Int.repr (nested_field_offset2 t gfs)) p
  else Vundef.

Lemma field_address_isptr:
  forall t path c, isptr c -> field_compatible t path c -> isptr (field_address t path c).
Proof.
  intros.
  unfold field_address. rewrite if_true by auto.
  normalize.
Qed.

Lemma is_pointer_or_null_field_compatible:
  forall t path c, 
     is_pointer_or_null (field_address t path c) ->
      field_compatible t path c.
Proof.
 intros.
 unfold field_address in H.
 if_tac in H; auto. inv H.
Qed.
Hint Resolve field_address_isptr.
Hint Resolve is_pointer_or_null_field_compatible.

Lemma gfield_type_complete_type: forall t gf,
  legal_field t gf ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (gfield_type t gf) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; inversion H; simpl in H0 |- *.
  + auto.
  + eapply complete_member.
    - apply in_members_field_type; auto.
    - apply co_consistent_complete.
      apply get_co_consistent.
  + eapply complete_member.
    - apply in_members_field_type; auto.
    - apply co_consistent_complete.
      apply get_co_consistent.
Qed.

Lemma nested_field_type2_complete_type: forall t gfs,
  legal_nested_field t gfs ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (nested_field_type2 t gfs) = true.
Proof.
  intros.
  induction gfs as [| gf gfs]; rewrite nested_field_type2_ind.
  + exact H0.
  + destruct H.
    apply gfield_type_complete_type; auto.
Qed.

Lemma gfield_type_nested_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (gf: gfield),
  nested_pred atom_pred t = true -> nested_pred atom_pred (gfield_type t gf) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; auto; simpl in H0 |- *; rewrite nested_pred_ind in H0.
  + rewrite andb_true_iff in H0.
    tauto.
  + rewrite andb_true_iff in H0.
    destruct_in_members i (co_members (get_co id)).
    - eapply nested_fields_pred_nested_pred; auto; tauto.
    - rewrite not_in_members_field_type; auto.
  + rewrite andb_true_iff in H0.
    destruct_in_members i (co_members (get_co id)).
    - eapply nested_fields_pred_nested_pred; auto; tauto.
    - rewrite not_in_members_field_type; auto.
Qed.

Lemma nested_field_type2_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (gfs: list gfield),
  nested_pred atom_pred t = true -> nested_pred atom_pred (nested_field_type2 t gfs) = true.
Proof.
  intros.
  induction gfs; rewrite nested_field_type2_ind.
  + auto.
  + apply gfield_type_nested_pred; auto.
Qed.

(*
Lemma nested_field_type2_field_type: forall i f a id t, nested_field_type2 (Tstruct i f a) (StructField id :: nil) = t /\ t <> Tvoid -> field_type id f = Errors.OK t.
Proof.
  unfold nested_field_type2.
  intros.
  simpl in H.
  solve_field_offset_type id f; destruct H.
  - subst; reflexivity.
  - congruence.
Defined.
*)
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

Lemma alignof_gfield_type_divide_alignof: forall gf t,
  legal_alignas_type t = true ->
  (alignof cenv_cs (gfield_type t gf) | alignof cenv_cs t).
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [simpl; apply Z.divide_1_l].
  + simpl.
    rewrite legal_alignas_type_Tarray by auto.
    apply Z.divide_refl.
  + eapply Z.divide_trans; [| apply legal_alignas_type_Tstruct; auto].
    simpl.
    destruct_in_members i (co_members (get_co id)).
    - apply alignof_field_type_divide_alignof; auto.
    - rewrite not_in_members_field_type by auto.
      apply Z.divide_1_l.
  + eapply Z.divide_trans; [| apply legal_alignas_type_Tunion; auto].
    simpl.
    destruct_in_members i (co_members (get_co id)).
    - apply alignof_field_type_divide_alignof; auto.
    - rewrite not_in_members_field_type by auto.
      apply Z.divide_1_l.
Qed.

Lemma alignof_nested_field_type2_divide_alignof: forall t gfs,
  legal_alignas_type t = true ->
  legal_nested_field t gfs ->
  (alignof cenv_cs (nested_field_type2 t gfs) | alignof cenv_cs t).
Proof.
  intros.
  induction gfs; rewrite nested_field_type2_ind.
  + apply Z.divide_refl.
  + specialize (IHgfs (proj1 H0)).
    eapply Z.divide_trans; [| eauto].
    apply alignof_gfield_type_divide_alignof.
    unfold legal_alignas_type; apply nested_field_type2_nest_pred; auto.
Qed.

Lemma gfield_offset_type_divide: forall gf t, legal_alignas_type t = true ->
  (alignof cenv_cs (gfield_type t gf) | gfield_offset t gf).
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [simpl; apply Z.divide_0_r];
  unfold legal_alignas_type in H;
  rewrite nested_pred_ind in H;
  rewrite andb_true_iff in H;
  destruct H.
  + simpl.
    apply Z.divide_mul_l.
    apply legal_alignas_sizeof_alignof_compat; auto.
  + simpl.
    apply field_offset2_aligned.
Qed.

Lemma nested_field_offset2_type2_divide: forall gfs t,
  legal_alignas_type t = true ->
  legal_nested_field t gfs ->
  (alignof cenv_cs (nested_field_type2 t gfs) | nested_field_offset2 t gfs).
Proof.
  intros.
  induction gfs; rewrite nested_field_type2_ind, nested_field_offset2_ind by auto.
  + apply Z.divide_0_r.
  + simpl in H0; spec IHgfs; [tauto |].
    assert (legal_alignas_type (nested_field_type2 t gfs) = true) by
      (unfold legal_alignas_type; apply nested_field_type2_nest_pred; auto).
    apply Z.divide_add_r.
    - eapply Z.divide_trans; [| eauto].
      apply alignof_gfield_type_divide_alignof; auto.
    - apply gfield_offset_type_divide; auto.
Qed.

Lemma gfield_offset_in_range: forall t gf,
  legal_field t gf ->
  0 <= gfield_offset t gf /\ gfield_offset t gf + sizeof cenv_cs (gfield_type t gf) <= sizeof cenv_cs t.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; inversion H.
  + pose proof sizeof_pos cenv_cs t.
    simpl.
    rewrite Z.max_r by omega.
    split.
    - apply Z.mul_nonneg_nonneg; omega.
    - rewrite Zred_factor3.
      apply Zmult_le_compat_l; omega.
  + assert (sizeof_struct cenv_cs 0 (co_members (get_co id)) <= sizeof cenv_cs (Tstruct id a)).
    Focus 1. {
      unfold get_co in *.
      simpl.
      destruct (cenv_cs ! id) as [co |] eqn:CO; [| inversion H1].
      rewrite co_consistent_sizeof with (env := cenv_cs) by exact (cenv_consistent_cs id co CO).
      rewrite H0.
      apply align_le.
      apply co_alignof_pos.
    } Unfocus.
    pose proof field_offset_in_range _ _ H1.
    simpl in *; omega.
  + assert (sizeof_union cenv_cs (co_members (get_co id)) <= sizeof cenv_cs (Tunion id a)).
    Focus 1. {
      unfold get_co in *.
      simpl.
      destruct (cenv_cs ! id) as [co |] eqn:CO; [| inversion H1].
      rewrite co_consistent_sizeof with (env := cenv_cs) by exact (cenv_consistent_cs id co CO).
      rewrite H0.
      apply align_le.
      apply co_alignof_pos.
    } Unfocus.
    pose proof sizeof_union_in_members _ _ H1.
    simpl in *. omega.
Qed.

Lemma nested_field_offset2_in_range: forall t gfs,
  legal_nested_field t gfs ->
  0 <= nested_field_offset2 t gfs /\
  (nested_field_offset2 t gfs) + sizeof cenv_cs (nested_field_type2 t gfs) <= sizeof cenv_cs t.
Proof.
  intros.
  induction gfs as [| gf gfs]; rewrite nested_field_type2_ind, nested_field_offset2_ind by auto.
  + omega.
  + specialize (IHgfs (proj1 H)).
    pose proof gfield_offset_in_range (nested_field_type2 t gfs) gf (proj2 H).
    omega.
Qed.


(*
(************************************************

nested_field_rec_Tarray
nested_field_rec_Tstruct_hd
nested_field_rec_Tstruct_mid
nested_field_rec_Tunion_hd
nested_field_rec_Tunion_mid

************************************************)

Lemma nested_field_rec_Tarray: forall t0 n a gfs t ofs i,
  nested_field_rec t gfs = Some (ofs, Tarray t0 n a) ->
  nested_field_rec t (ArraySubsc i :: gfs) = Some (ofs + sizeof cenv_cs t0 * i, t0).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma nested_field_rec_Tstruct: forall gfs t id i co a ofs,
  nested_field_rec t gfs = Some (ofs, Tstruct id a) ->
  cenv_cs ! id = Some co ->
  co_su co = Struct ->
  in_members i (co_members co) ->
  nested_field_rec t (StructField i :: gfs) =
    Some (ofs + field_offset2 cenv_cs i (co_members co), field_type2 i (co_members co)).
Proof.
  intros.
  simpl.
  rewrite H, H0, H1.
  destruct_in_members i (co_members co); [| tauto].
  reflexivity.
Qed.

Lemma nested_field_rec_Tunion: forall gfs t id i co a ofs,
  nested_field_rec t gfs = Some (ofs, Tunion id a) ->
  cenv_cs ! id = Some co ->
  co_su co = Union ->
  in_members i (co_members co) ->
  nested_field_rec t (UnionField i :: gfs) = Some (ofs, field_type2 i (co_members co)).
Proof.
  intros.
  simpl.
  rewrite H, H0, H1.
  destruct_in_members i (co_members co); [| tauto].
  reflexivity.
Qed.

(*
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
*)
Lemma nested_field_offset2_Tarray: forall t0 n a gfs t i,
  nested_field_type2 t gfs = Tarray t0 n a ->
  nested_field_offset2 t (ArraySubsc i :: gfs) = nested_field_offset2 t gfs + sizeof cenv_cs t0 * i.
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

Lemma nested_field_offset2_Tstruct: forall t gfs id i a co,
  nested_field_type2 t gfs = Tstruct id a ->
  cenv_cs ! id = Some co ->
  co_su co = Struct ->
  in_members i (co_members co) ->
  nested_field_offset2 t (StructField i :: gfs) = nested_field_offset2 t gfs + field_offset2 cenv_cs i (co_members co).
Proof.
  intros.
  unfold nested_field_type2 in H.
  unfold nested_field_offset2.
  valid_nested_field_rec t gfs H.
  subst.
  erewrite nested_field_rec_Tstruct by eauto.
  reflexivity.
Qed.

Lemma nested_field_type2_Tstruct: forall t gfs id i a co,
  nested_field_type2 t gfs = Tstruct id a ->
  cenv_cs ! id = Some co ->
  co_su co = Struct ->
  in_members i (co_members co) ->
  nested_field_type2 t (StructField i :: gfs) = field_type2 i (co_members co).
Proof.
  intros.
  unfold nested_field_type2 in H |- *.
  valid_nested_field_rec t gfs H.
  subst.
  erewrite nested_field_rec_Tstruct by eauto.
  reflexivity.
Qed.

Lemma nested_field_offset2_Tunion: forall t gfs id i a co,
  nested_field_type2 t gfs = Tunion id a ->
  cenv_cs ! id = Some co ->
  co_su co = Union ->
  in_members i (co_members co) ->
  nested_field_offset2 t (UnionField i :: gfs) = nested_field_offset2 t gfs.
Proof.
  intros.
  unfold nested_field_type2 in H.
  unfold nested_field_offset2.
  valid_nested_field_rec t gfs H.
  subst.
  erewrite nested_field_rec_Tunion by eauto.
  reflexivity.
Qed.

Lemma nested_field_type2_Tunion: forall t gfs id i a co,
  nested_field_type2 t gfs = Tunion id a ->
  cenv_cs ! id = Some co ->
  co_su co = Union ->
  in_members i (co_members co) ->
  nested_field_type2 t (UnionField i :: gfs) = field_type2 i (co_members co).
Proof.
  intros.
  unfold nested_field_type2 in H |- *.
  valid_nested_field_rec t gfs H.
  subst.
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
*)
(************************************************

nested_field_offset_app

************************************************)
(*
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
      rewrite CO, H2.
      destruct_in_members i (co_members co); [| tauto].
      f_equal.
      f_equal.
      omega.
    - (* Tunion *)
      subst.
      simpl.
      rewrite (IHgfs1 _ _ eq_refl).
      rewrite CO, H2.
      destruct_in_members i (co_members co); [| tauto].
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
      specialize (IHgfs1 (ofs - ofs0) (Tstruct id a0)).
      replace (ofs0 + (ofs - ofs0)) with ofs in IHgfs1 by omega.
      rewrite (IHgfs1 eq_refl).
      rewrite CO.
      repeat split; auto.
      omega.
    - (* Tunion *)
      specialize (IHgfs1 ofs1 (Tunion id a0)).
      subst ofs.
      rewrite (IHgfs1 eq_refl).
      rewrite CO.
      auto.
Qed.
*)
Lemma legal_nested_field_app: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) -> legal_nested_field t gfs0.
Proof.
  intros.
  induction gfs1.
  + simpl in *; auto.
  + simpl app in H.
    simpl in H.
    tauto.
Qed.

Lemma nested_field_type2_nested_field_type2: forall t gfs0 gfs1,
  nested_field_type2 (nested_field_type2 t gfs0) gfs1 = nested_field_type2 t (gfs1 ++ gfs0).
Proof.
  intros.
  induction gfs1.
  + rewrite nested_field_type2_ind.
    reflexivity.
  + rewrite nested_field_type2_ind.
    simpl app.
    rewrite nested_field_type2_ind with (t := t) (gfs := a :: gfs1 ++ gfs0).
    rewrite IHgfs1.
    reflexivity.
Qed.

Lemma legal_nested_field_app': forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) -> legal_nested_field (nested_field_type2 t gfs0) gfs1.
Proof.
  intros.
  induction gfs1.
  + exact I.
  + simpl in H.
    specialize (IHgfs1 (proj1 H)).
    simpl.
    rewrite nested_field_type2_nested_field_type2.
    tauto.
Qed.

Lemma nested_field_offset2_app: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) ->
  nested_field_offset2 t (gfs1 ++ gfs0) = nested_field_offset2 t gfs0 +
    nested_field_offset2 (nested_field_type2 t gfs0) gfs1.
Proof.
  intros.
  induction gfs1.
  + simpl app.
    rewrite nested_field_offset2_ind with (gfs := nil) by exact I.
    omega.
  + simpl app in *.
    specialize (IHgfs1 (proj1 H)).
    rewrite nested_field_offset2_ind with (gfs := a :: gfs1 ++ gfs0) by auto.
    rewrite nested_field_offset2_ind with (gfs := a :: gfs1) by (apply legal_nested_field_app'; auto).
    rewrite nested_field_type2_nested_field_type2.
    omega.
Qed.

End COMPOSITE_ENV.
(*
Arguments nested_field_offset2 {cs} t gfs /.
Arguments nested_field_type2 {cs} t gfs /.
*)
