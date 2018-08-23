Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.fieldlist.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.align_compatible_dec.
Open Scope Z.

(************************************************

Definition of nested_field_type2, nested_field_offset2

The principle of this part is only exposing nft2 and nfo2 to users
and hide the implimentation of nf_rec

************************************************)

Inductive gfield : Type :=
  | ArraySubsc : forall i: Z, gfield
  | StructField : forall i: ident, gfield
  | UnionField : forall i: ident, gfield.

Delimit Scope gfield_scope with gfield.
Bind Scope gfield_scope with list gfield.
Notation "x 'DOT' y " := (@cons gfield (StructField y) x%gfield) (at level 40, left associativity): gfield_scope.
Notation "x 'UDOT' y " := (@cons gfield (UnionField y) x%gfield) (at level 40, left associativity): gfield_scope.
Notation "x 'SUB' y " := (@cons gfield (ArraySubsc y) x%gfield) (at level 40, left associativity): gfield_scope.
Notation "'DOT' y " := (@cons gfield (StructField y) nil) (at level 40): gfield_scope.
Notation "'UDOT' y " := (@cons gfield (UnionField y) nil) (at level 40): gfield_scope.
Notation "'SUB' y " := (@cons gfield (ArraySubsc y) nil) (at level 40): gfield_scope.

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

Section COMPOSITE_ENV.

Context {cs: compspecs}.
Definition gfield_type t gf :=
  match t, gf with
  | Tarray t0 _ _, ArraySubsc _ => t0
  | Tstruct id _, StructField i
  | Tunion id _, UnionField i => field_type i (co_members (get_co id))
  | _, _ => Tvoid
  end.

Definition gfield_offset t gf :=
  match t, gf with
  | Tarray t0 _ _, ArraySubsc i => sizeof t0 * i
  | Tstruct id _, StructField i => field_offset cenv_cs i (co_members (get_co id))
  | Tunion id _, UnionField i => 0
  | _, _ => 0
  end.

Definition no_alignas_attr (a: attr): attr := mk_attr (attr_volatile a) None.

Lemma no_alignas_attr_spec: forall a d,
  align_attr (no_alignas_attr a) d = d.
Proof.
  intros.
  destruct a; simpl.
  reflexivity.
Qed.

Definition gfield_array_type t lo hi :=
  match t with
  | Tarray t0 _ a => Tarray t0 (hi - lo) (no_alignas_attr a)
  | _ => Tarray Tvoid (hi - lo) (no_alignas_attr (attr_of_type t))
  end.

Fixpoint nested_field_rec (t: type) (gfs: list gfield) : option (prod Z type) :=
  match gfs with
  | nil => Some (0, t)
  | hd :: tl =>
    match nested_field_rec t tl with
    | Some (pos, t') =>
      match t', hd with
      | Tarray t'' n _, ArraySubsc i => Some(pos + sizeof t'' * i, t'')
      | Tstruct id _, StructField i =>
        let m := co_members (get_co id) in
        if compute_in_members i m then
          Some (pos + field_offset cenv_cs i m, field_type i m)
        else
          None
      | Tunion id _, UnionField i =>
        let m := co_members (get_co id) in
        if compute_in_members i m then
          Some (pos, field_type i m)
        else
          None
      | _, _ => None
      end
    | None => None
    end
  end%Z.

(*
Fixpoint nested_field_rec (t: type) (gfs: list gfield) : option (prod Z type) :=
  match gfs with
  | nil => Some (0, t)
  | hd :: tl =>
    match nested_field_rec t tl with
    | Some (pos, t') =>
      match t', hd with
      | Tarray t'' n _, ArraySubsc i => Some(pos + sizeof t'' * i, t'')
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
*)

Definition nested_field_offset (t: type) (gfs: list gfield) : Z :=
  match nested_field_rec t gfs with
  | Some (pos, _) => pos
  | _ => 0
  end.

Definition nested_field_type (t: type) (gfs: list gfield) : type :=
  match nested_field_rec t gfs with
  | Some (_, t0) => t0
  | _ => Tvoid
  end.

Definition nested_field_array_type t gfs lo hi :=
  Tarray (nested_field_type t (ArraySubsc 0 :: gfs)) (hi - lo) (no_alignas_attr (attr_of_type (nested_field_type t gfs))).

Definition legal_field t gf :=
  match t, gf with
  | Tarray _ n _, ArraySubsc i => 0 <= i < n
  | Tstruct id _, StructField i => in_members i (co_members (get_co id))
  | Tunion id _, UnionField i => in_members i (co_members (get_co id))
  | _, _ => False
  end.

Definition legal_field0 t gf :=
  match t, gf with
  | Tarray _ n _, ArraySubsc i => 0 <= i <= n
  | Tstruct id _, StructField i => in_members i (co_members (get_co id))
  | Tunion id _, UnionField i => in_members i (co_members (get_co id))
  | _, _ => False
  end.

Fixpoint legal_nested_field (t: type) (gfs: list gfield) : Prop :=
  match gfs with
  | nil => True
  | gf :: gfs0 => legal_nested_field t gfs0 /\ legal_field (nested_field_type t gfs0) gf
  end.

Definition legal_nested_field0 t gfs :=
  match gfs with
  | nil => True
  | gf :: gfs0 => legal_nested_field t gfs0 /\ legal_field0 (nested_field_type t gfs0) gf
  end.

Fixpoint compute_legal_nested_field (t: type) (gfs: list gfield) : list Prop :=
  match gfs with
  | nil => nil
  | gf :: gfs0 =>
    match (nested_field_type t gfs0), gf with
    | Tarray _ n _, ArraySubsc i =>
       (0 <= i < n) :: compute_legal_nested_field t gfs0
    | Tstruct id _, StructField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs0 else False :: nil
    | Tunion id _, UnionField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs0 else False :: nil
    | _, _ => False :: nil
    end
  end.

Lemma nested_field_type_ind: forall t gfs,
  nested_field_type t gfs =
  match gfs with
  | nil => t
  | gf :: gfs0 => gfield_type (nested_field_type t gfs0) gf
  end.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [reflexivity |].
  unfold nested_field_type.
  simpl.
  destruct (nested_field_rec t gfs) as [[ofs0 t0] |] eqn:NFR; [| reflexivity].
  destruct t0 as [| | | | | | | id ? | id ?]; destruct gf; try reflexivity.
  + destruct_in_members i (co_members (get_co id)).
    - reflexivity.
    - unfold gfield_type.
      rewrite not_in_members_field_type; auto.
  + destruct_in_members i (co_members (get_co id)).
    - reflexivity.
    - unfold gfield_type.
      rewrite not_in_members_field_type; auto.
Defined.

Lemma nested_field_offset_ind: forall t gfs,
  legal_nested_field0 t gfs ->
  nested_field_offset t gfs =
  match gfs with
  | nil => 0
  | gf :: gfs0 => nested_field_offset t gfs0 + gfield_offset (nested_field_type t gfs0) gf
  end.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [reflexivity |].
  destruct H.
  unfold nested_field_type, nested_field_offset in *.
  simpl.
  destruct (nested_field_rec t gfs) as [[ofs0 t0] |] eqn:NFR; [| reflexivity].
  destruct t0 as [| | | | | | | id ? | id ?]; destruct gf; try inversion H0; auto.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    reflexivity.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    simpl. omega.
Qed.

Lemma nested_field_offset_ind': forall t gfs,
  legal_nested_field t gfs ->
  nested_field_offset t gfs =
  match gfs with
  | nil => 0
  | gf :: gfs0 => nested_field_offset t gfs0 + gfield_offset (nested_field_type t gfs0) gf
  end.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [reflexivity |].
  destruct H.
  unfold nested_field_type, nested_field_offset in *.
  simpl.
  destruct (nested_field_rec t gfs) as [[ofs0 t0] |] eqn:NFR; [| reflexivity].
  destruct t0 as [| | | | | | | id ? | id ?]; destruct gf; try inversion H0; auto.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    reflexivity.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    simpl. omega.
Qed.

Lemma offset_val_nested_field_offset_ind: forall t gfs p,
  legal_nested_field0 t gfs ->
  offset_val (nested_field_offset t gfs) p =
  match gfs with
  | nil => force_ptr p
  | gf :: gfs0 => offset_val (gfield_offset (nested_field_type t gfs0) gf)
                    (offset_val (nested_field_offset t gfs0) p)
  end.
Proof.
  intros.
  rewrite nested_field_offset_ind by auto.
  destruct gfs as [| gf gfs].
  + fold Int.zero. rewrite offset_val_force_ptr; auto.
  + rewrite offset_offset_val.
    auto.
Qed.

Lemma nested_field_array_type_ind: forall t gfs lo hi,
  nested_field_array_type t gfs lo hi =
  gfield_array_type (nested_field_type t gfs) lo hi.
Proof.
  intros.
  unfold nested_field_array_type.
  rewrite nested_field_type_ind.
  destruct (nested_field_type t gfs); simpl; auto.
Qed.

Lemma nested_field0_offset_ind: forall t gfs,
  legal_nested_field0 t gfs ->
  nested_field_offset t gfs =
  match gfs with
  | nil => 0
  | gf :: gfs0 => nested_field_offset t gfs0 + gfield_offset (nested_field_type t gfs0) gf
  end.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [reflexivity |].
  destruct H.
  unfold nested_field_type, nested_field_offset in *.
  simpl.
  destruct (nested_field_rec t gfs) as [[ofs0 t0] |] eqn:NFR; [| reflexivity].
  destruct t0 as [| | | | | | | id ? | id ?]; destruct gf; try inversion H0; auto.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    reflexivity.
  + destruct_in_members i (co_members (get_co id)); [| tauto].
    simpl. omega.
Qed.

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
(*
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
      ofs0 = ofs + sizeof t0 * i0 /\ t0 = t1
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

Definition legal_nested_field_dec: forall t gfs,
  {legal_nested_field t gfs} + {~ legal_nested_field t gfs}.
Proof.
  intros.
  induction gfs.
  + left. exact I.
  + simpl.
    apply sumbool_dec_and; [auto |].
    destruct a, (nested_field_type t gfs) as [| | | | | | | id ? | id ?]; try solve [right; tauto];
    unfold legal_field.
    - apply sumbool_dec_and; [apply Z_le_dec | apply Z_lt_dec].
    - destruct_in_members i (co_members (get_co id)); auto.
    - destruct_in_members i (co_members (get_co id)); auto.
Qed.

Definition legal_nested_field0_dec: forall t gfs,
  {legal_nested_field0 t gfs} + {~ legal_nested_field0 t gfs}.
Proof.
  intros.
  destruct gfs as [| gf gfs].
  + left. exact I.
  + simpl.
    apply sumbool_dec_and; [apply legal_nested_field_dec |].
    destruct gf, (nested_field_type t gfs) as [| | | | | | | id ? | id ?]; try solve [right; tauto];
    unfold legal_field0.
    - apply sumbool_dec_and; [apply Z_le_dec | apply Z_le_dec].
    - destruct_in_members i (co_members (get_co id)); auto.
    - destruct_in_members i (co_members (get_co id)); auto.
Qed.

Definition field_compatible t gfs p :=
  isptr p /\
  complete_legal_cosu_type t = true /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field t gfs.

Definition field_compatible0 t gfs p :=
  isptr p /\
  complete_legal_cosu_type t = true /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field0 t gfs.

Lemma field_compatible_dec: forall t gfs p,
  {field_compatible t gfs p} + {~ field_compatible t gfs p}.
Proof.
  unfold field_compatible.
  intros.
  repeat apply sumbool_dec_and.
  + destruct p; simpl; try (left; tauto); try (right; tauto).
  + destruct complete_legal_cosu_type; [left | right]; congruence.
  + destruct p; simpl; try solve [left; auto].
    destruct (zlt (Ptrofs.unsigned i + sizeof t) Ptrofs.modulus); [left | right]; omega.
  + apply align_compatible_dec.
  + apply legal_nested_field_dec.
Qed.

Lemma field_compatible0_dec: forall t gfs p,
  {field_compatible0 t gfs p} + {~ field_compatible0 t gfs p}.
Proof.
  unfold field_compatible0.
  intros.
  repeat apply sumbool_dec_and.
  + destruct p; simpl; try (left; tauto); try (right; tauto).
  + destruct complete_legal_cosu_type; [left | right]; congruence.
  + destruct p; simpl; try solve [left; auto].
    destruct (zlt (Ptrofs.unsigned i + sizeof t) Ptrofs.modulus); [left | right]; omega.
  + apply align_compatible_dec.
  + apply legal_nested_field0_dec.
Qed.

Lemma field_compatible_cons: forall t gf gfs p,
  field_compatible t (gf :: gfs) p <->
  match nested_field_type t gfs, gf with
  | Tstruct id _, StructField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tunion id _, UnionField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tarray _ n _, ArraySubsc i => 0 <= i < n /\ field_compatible t gfs p
  | _, _ => False
  end.
Proof.
  intros.
  unfold field_compatible.
  simpl (legal_nested_field t (gf :: gfs)).
  destruct (nested_field_type t gfs), gf; simpl; tauto.
Qed.

Lemma field_compatible0_cons: forall t gf gfs p,
  field_compatible0 t (gf :: gfs) p <->
  match nested_field_type t gfs, gf with
  | Tstruct id _, StructField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tunion id _, UnionField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tarray _ n _, ArraySubsc i => 0 <= i <= n /\ field_compatible t gfs p
  | _, _ => False
  end.
Proof.
  intros.
  unfold field_compatible, field_compatible0.
  simpl (legal_nested_field0 t (gf :: gfs)).
  destruct (nested_field_type t gfs), gf; simpl; tauto.
Qed.

(* The following two lemmas is covered by the previous two. Delete them some time. *)
Lemma field_compatible_cons_Tarray:
  forall i t t0 n a gfs p,
  nested_field_type t gfs = Tarray t0 n a ->
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

Lemma field_compatible0_cons_Tarray:
  forall k t n a gfs p t',
  nested_field_type t gfs = Tarray t' n a ->
  field_compatible t gfs p ->
  (0 <= k <= n)%Z ->
  field_compatible0 t (ArraySubsc k :: gfs) p.
Proof.
unfold field_compatible, field_compatible0; intros; intuition.
unfold legal_nested_field0.
rewrite H.
simpl.
auto.
Qed.

Definition field_address t gfs p :=
  if (field_compatible_dec t gfs p)
  then offset_val (nested_field_offset t gfs) p
  else Vundef.

Definition field_address0 t gfs p :=
  if (field_compatible0_dec t gfs p)
  then offset_val (nested_field_offset t gfs) p
  else Vundef.

Lemma field_address_isptr:
  forall t path c, field_compatible t path c -> isptr (field_address t path c).
Proof.
  intros.
  unfold field_address. rewrite if_true by auto.
  destruct H as [? _].
  normalize.
Qed.

Lemma field_address0_isptr:
  forall t path c, field_compatible0 t path c -> isptr (field_address0 t path c).
Proof.
  intros.
  unfold field_address0. rewrite if_true by auto.
  destruct H as [? _].
  normalize.
Qed.

Lemma field_address_clarify:
 forall t path c,
   is_pointer_or_null (field_address t path c) ->
   field_address t path c = offset_val (nested_field_offset t path) c.
Proof.
  intros. unfold field_address in *.
  if_tac; try contradiction.
  auto.
Qed.

Lemma field_address0_clarify:
 forall t path c,
   is_pointer_or_null (field_address0 t path c) ->
   field_address0 t path c = offset_val (nested_field_offset t path) c.
Proof.
 intros. unfold field_address0 in *.
  if_tac; try contradiction.
  auto.
Qed.

Lemma field_compatible_field_compatible0:
  forall (t : type) (gfs : list gfield) (p : val),
  field_compatible t gfs p -> field_compatible0 t gfs p.
Proof.
  intros.
  destruct gfs as [| gf gfs]; [auto |].
  rewrite field_compatible0_cons.
  rewrite field_compatible_cons in H.
  destruct (nested_field_type t gfs), gf; try tauto.
  split; [| tauto].
  omega.
Qed.

Lemma field_compatible_field_compatible0':
  forall (t : type) (i : Z) (gfs : list gfield) (p : val),
  field_compatible t (ArraySubsc i :: gfs) p <->
  field_compatible0 t (ArraySubsc i :: gfs) p /\
  field_compatible0 t (ArraySubsc (i + 1) :: gfs) p.
Proof.
  intros.
  rewrite !field_compatible0_cons.
  rewrite field_compatible_cons.
  destruct (nested_field_type t gfs); try tauto.
  assert (0 <= i < z <-> 0 <= i <= z /\ 0 <= i + 1 <= z) by omega.
  tauto.
Qed.

Lemma field_compatible0_range:
 forall i lo hi t gfs p,
   lo <= i <= hi ->
   field_compatible0 t (ArraySubsc lo :: gfs) p ->
   field_compatible0 t (ArraySubsc hi :: gfs) p ->
   field_compatible0 t (ArraySubsc i :: gfs) p.
Proof.
  intros.
  destruct H0 as [? [? [? [? [? ?]]]]].
  destruct H1 as [? [? [? [? [? ?]]]]].
  repeat split; auto.
  hnf in H6, H11|-*.
  destruct (nested_field_type t gfs); auto.
  omega.
Qed.

Lemma field_compatible_range:
 forall i lo hi t gfs p,
   lo <= i < hi ->
   field_compatible0 t (ArraySubsc lo :: gfs) p ->
   field_compatible0 t (ArraySubsc hi :: gfs) p ->
   field_compatible t (ArraySubsc i :: gfs) p.
Proof.
  intros.
  rewrite field_compatible_field_compatible0'.
  split; apply (field_compatible0_range _ lo hi); eauto; omega.
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

Lemma nested_field_type_ArraySubsc: forall t i gfs,
  nested_field_type t (ArraySubsc i :: gfs) = nested_field_type t (ArraySubsc 0 :: gfs).
Proof.
  intros.
  rewrite !nested_field_type_ind with (gfs := _ :: gfs).
  destruct (nested_field_type t gfs); try tauto.
Qed.
(* TODO: not useful any longer *)
(*
Lemma gfield_type_complete_type: forall t gf,
  legal_field t gf ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (gfield_type t gf) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try inversion H; simpl in H0 |- *.
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

Lemma gfield_array_type_complete_type: forall t lo hi,
  legal_field0 t (ArraySubsc lo) ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (gfield_array_type t lo hi) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; try inversion H; simpl in H0 |- *.
  auto.
Qed.

Lemma nested_field_type_complete_type: forall t gfs,
  legal_nested_field t gfs ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (nested_field_type t gfs) = true.
Proof.
  intros.
  induction gfs as [| gf gfs]; rewrite nested_field_type_ind.
  + exact H0.
  + destruct H.
    apply gfield_type_complete_type; auto.
Qed.

Lemma nested_field_array_type_complete_type: forall t gfs lo hi,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (nested_field_array_type t gfs lo hi) = true.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  apply gfield_array_type_complete_type.
  + simpl in H; tauto.
  + apply nested_field_type_complete_type; auto.
    simpl in H; tauto.
Qed.
*)
Lemma gfield_type_nested_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (gf: gfield),
  nested_pred atom_pred t = true -> nested_pred atom_pred (gfield_type t gf) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; auto;
   unfold gfield_type in *; rewrite nested_pred_eq in H0.
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

Lemma gfield_array_type_nested_pred: forall {atom_pred: type -> bool},
  (forall t n m a,
    0 <= m ->
    atom_pred (Tarray t n a) = true ->
    atom_pred (Tarray t m (no_alignas_attr a)) = true) ->
  forall (t: type) lo hi,
  lo <= hi ->
  legal_field0 t (ArraySubsc lo) ->
  nested_pred atom_pred t = true -> nested_pred atom_pred (gfield_array_type t lo hi) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; auto.
  simpl in H2 |- *; rewrite nested_pred_eq in H2 |- *.
  rewrite andb_true_iff in H2 |- *.
  destruct H2; split; auto.
  eapply H; eauto.
  omega.
Qed.

Lemma gfield_type_complete_legal_cosu_type: forall (t: type) (gf: gfield),
  legal_field t gf ->
  complete_legal_cosu_type t = true -> complete_legal_cosu_type (gfield_type t gf) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; auto;
  unfold gfield_type in *; simpl in H, H0; unfold get_co in *.
  + destruct (cenv_cs ! id) eqn:?H; [| inv H0].
    pose proof cenv_legal_su _ _ H1.
    unfold in_members in H.
    induction (co_members c) as [| [i0 t0] ?].
    - inv H.
    - simpl in H2; rewrite andb_true_iff in H2; destruct H2.
      simpl in H |- *.
      if_tac; auto.
      apply IHm; auto.
      destruct H; auto; congruence.
  + destruct (cenv_cs ! id) eqn:?H; [| inv H0].
    pose proof cenv_legal_su _ _ H1.
    unfold in_members in H.
    induction (co_members c) as [| [i0 t0] ?].
    - inv H.
    - simpl in H2; rewrite andb_true_iff in H2; destruct H2.
      simpl in H |- *.
      if_tac; auto.
      apply IHm; auto.
      destruct H; auto; congruence.
Qed.

Lemma gfield_array_type_complete_legal_cosu_type: forall (t: type) lo hi,
  legal_field0 t (ArraySubsc lo) ->
  complete_legal_cosu_type t = true ->
  complete_legal_cosu_type (gfield_array_type t lo hi) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; auto.
Qed.

Lemma nested_field_type_complete_legal_cosu_type: forall (t: type) (gfs: list gfield), complete_legal_cosu_type t = true -> legal_nested_field t gfs -> complete_legal_cosu_type (nested_field_type t gfs) = true.
Proof.
  intros.
  induction gfs; rewrite nested_field_type_ind.
  + auto.
  + destruct H0.
    apply gfield_type_complete_legal_cosu_type; auto.
Qed.

Lemma nested_field_array_type_complete_legal_cosu_type: forall (t: type) (gfs: list gfield) lo hi, complete_legal_cosu_type t = true -> legal_nested_field0 t (ArraySubsc lo :: gfs) -> complete_legal_cosu_type (nested_field_array_type t gfs lo hi) = true.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  simpl in H0; destruct H0.
  apply gfield_array_type_complete_legal_cosu_type; auto.
  apply nested_field_type_complete_legal_cosu_type; auto.
Qed.

Lemma nested_field_type_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (gfs: list gfield),
  nested_pred atom_pred t = true -> nested_pred atom_pred (nested_field_type t gfs) = true.
Proof.
  intros.
  induction gfs; rewrite nested_field_type_ind.
  + auto.
  + apply gfield_type_nested_pred; auto.
Qed.

Lemma nested_field_array_type_nest_pred: forall {atom_pred: type -> bool},
  atom_pred Tvoid = true ->
  (forall t n m a,
     0 <= m ->
     atom_pred (Tarray t n a) = true ->
     atom_pred (Tarray t m (no_alignas_attr a)) = true) ->
  forall (t: type) gfs lo hi,
  lo <= hi ->
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  nested_pred atom_pred t = true ->
  nested_pred atom_pred (nested_field_array_type t gfs lo hi) = true.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  simpl in H2.
  apply gfield_array_type_nested_pred; [auto | auto | tauto |].
  apply nested_field_type_nest_pred; auto.
Qed.
(*
Lemma alignof_gfield_type_divide_alignof: forall t gf,
  legal_alignas_type t = true ->
  (alignof (gfield_type t gf) | alignof t).
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [simpl; apply Z.divide_1_l].
  + simpl.
    apply legal_alignas_type_spec in H.
    exact H.
  + eapply Z.divide_trans; [| apply legal_alignas_type_Tstruct; auto].
    unfold gfield_type.
    destruct_in_members i (co_members (get_co id)).
    - apply alignof_field_type_divide_alignof; auto.
    - rewrite not_in_members_field_type by auto.
      apply Z.divide_1_l.
  + eapply Z.divide_trans; [| apply legal_alignas_type_Tunion; auto].
    unfold gfield_type.
    destruct_in_members i (co_members (get_co id)).
    - apply alignof_field_type_divide_alignof; auto.
    - rewrite not_in_members_field_type by auto.
      apply Z.divide_1_l.
Qed.

Lemma alignof_gfield_array_type_eq: forall t lo hi i,
  legal_alignas_type t = true ->
  legal_field0 t (ArraySubsc lo) ->
  alignof (gfield_array_type t lo hi) = alignof (gfield_type t (ArraySubsc i)).
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; try solve [inversion H0].
  apply legal_alignas_type_spec in H.
Transparent alignof.
  simpl (alignof (gfield_array_type (Tarray t z a) lo hi)).
Opaque alignof.
  unfold plain_alignof in H.
  rewrite no_alignas_attr_spec.
  auto.
Qed.

Lemma alignof_nested_field_type_divide_alignof: forall t gfs,
  legal_alignas_type t = true ->
  legal_nested_field t gfs ->
  (alignof (nested_field_type t gfs) | alignof t).
Proof.
  intros.
  induction gfs; rewrite nested_field_type_ind.
  + apply Z.divide_refl.
  + specialize (IHgfs (proj1 H0)).
    eapply Z.divide_trans; [| eauto].
    apply alignof_gfield_type_divide_alignof.
    unfold legal_alignas_type; apply nested_field_type_nest_pred; auto.
Qed.

Lemma alignof_nested_field_type_divide_alignof': forall t gfs,
  legal_alignas_type t = true ->
  legal_nested_field0 t gfs ->
  (alignof (nested_field_type t gfs) | alignof t).
Proof.
  intros.
  destruct gfs; rewrite nested_field_type_ind.
  + apply Z.divide_refl.
  + simpl in H0.
    pose proof alignof_nested_field_type_divide_alignof t gfs H (proj1 H0).
    eapply Z.divide_trans; [| eauto].
    apply alignof_gfield_type_divide_alignof.
    unfold legal_alignas_type; apply nested_field_type_nest_pred; auto.
Qed.

Lemma alignof_nested_field_array_type_eq: forall t gfs lo hi i,
  legal_alignas_type t = true ->
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  alignof (nested_field_array_type t gfs lo hi) = alignof (nested_field_type t (ArraySubsc i :: gfs)).
Proof.
  intros.
  rewrite nested_field_type_ind.
  rewrite nested_field_array_type_ind.
  simpl in H0.
  apply alignof_gfield_array_type_eq.
  + apply nested_field_type_nest_pred; auto.
  + tauto.
Qed.

Lemma alignof_nested_field_array_type_divide_alignof: forall t gfs lo hi,
  legal_alignas_type t = true ->
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  (alignof (nested_field_array_type t gfs lo hi) | alignof t).
Proof.
  intros.
  rewrite alignof_nested_field_array_type_eq with (i := lo) by auto.
  apply alignof_nested_field_type_divide_alignof'; auto.
Qed.

Lemma gfield_offset_type_divide: forall gf t, legal_alignas_type t = true ->
  (alignof (gfield_type t gf) | gfield_offset t gf).
Proof.
  intros.
  pose proof H.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [simpl; apply Z.divide_0_r];
  unfold legal_alignas_type in H;
  rewrite nested_pred_eq in H;
  rewrite andb_true_iff in H;
  destruct H.
  + simpl.
    apply Z.divide_mul_l.
    apply legal_alignas_type_Tarray in H0; auto.
  + simpl.
    apply field_offset_aligned.
Qed.
*)
Lemma legal_nested_field0_field:
  forall t gfs, legal_nested_field t gfs -> legal_nested_field0 t gfs.
Proof.
intros.
revert t H; induction gfs; intros.
apply I.
destruct H; split; auto.
clear - H0.
destruct (nested_field_type t gfs); simpl in *; auto.
destruct a; auto.
omega.
Qed.

Hint Resolve legal_nested_field0_field.
(*
Lemma nested_field_offset_type_divide: forall gfs t,
  legal_alignas_type t = true ->
  legal_nested_field t gfs ->
  (alignof (nested_field_type t gfs) | nested_field_offset t gfs).
Proof.
  intros.
  induction gfs; rewrite nested_field_type_ind, nested_field_offset_ind by auto.
  + apply Z.divide_0_r.
  + simpl in H0; spec IHgfs; [tauto |].
    assert (legal_alignas_type (nested_field_type t gfs) = true) by
      (unfold legal_alignas_type; apply nested_field_type_nest_pred; auto).
    apply Z.divide_add_r.
    - eapply Z.divide_trans; [| eauto].
      apply alignof_gfield_type_divide_alignof; auto.
    - apply gfield_offset_type_divide; auto.
Qed.

Lemma nested_field_offset_type_divide0: forall gfs t,
  legal_alignas_type t = true ->
  legal_nested_field0 t gfs ->
  (alignof (nested_field_type t gfs) | nested_field_offset t gfs).
Proof.
  intros.
  destruct gfs; rewrite nested_field_type_ind, nested_field_offset_ind by auto.
  + apply Z.divide_0_r.
  + simpl in H0.
    pose proof nested_field_offset_type_divide gfs t H (proj1 H0).
    assert (legal_alignas_type (nested_field_type t gfs) = true) by
      (unfold legal_alignas_type; apply nested_field_type_nest_pred; auto).
    apply Z.divide_add_r.
    - eapply Z.divide_trans; [| eauto].
      apply alignof_gfield_type_divide_alignof; auto.
    - apply gfield_offset_type_divide; auto.
Qed.
*)
Lemma gfield_offset_in_range: forall t gf,
  legal_field t gf ->
  complete_legal_cosu_type t = true ->
  0 <= gfield_offset t gf /\ gfield_offset t gf + sizeof (gfield_type t gf) <= sizeof t.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [inversion H]; simpl in H.
  + simpl. rewrite Z.max_r by omega.
    pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil).
    omega.
  + unfold gfield_type, gfield_offset.
    pose_sizeof_co (Tstruct id a).
    pose proof field_offset_in_range _ _ H.
    omega.
  + unfold gfield_type, gfield_offset.
    pose_sizeof_co (Tunion id a).
    pose proof sizeof_union_in_members _ _ H.
    omega.
Qed.

Lemma gfield_array_offset_in_range: forall t lo hi,
  legal_field0 t (ArraySubsc lo) ->
  legal_field0 t (ArraySubsc hi) ->
  complete_legal_cosu_type t = true ->
  0 <= gfield_offset t (ArraySubsc lo) /\
  gfield_offset t (ArraySubsc lo) + sizeof (gfield_array_type t lo hi) <= sizeof t.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; try solve [inversion H]; simpl in H.
  simpl in *.
  rewrite (Z.max_r 0 z) by omega.
  assert (0 <= Z.max 0 (hi - lo) <= hi) by (apply arith_aux05; omega).
  assert (0 <= lo + Z.max 0 (hi - lo) <= z) by (apply arith_aux06; omega).
  pose_size_mult cenv_cs t (0 :: Z.max 0 (hi - lo) :: hi :: nil).
  pose_size_mult cenv_cs t (0 :: lo :: lo + Z.max 0 (hi - lo) :: z :: nil).
  omega.
Qed.

Lemma gfield0_offset_in_range: forall t gf,
  legal_field0 t gf ->
  complete_legal_cosu_type t = true ->
  0 <= gfield_offset t gf /\ gfield_offset t gf <= sizeof t.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [inversion H]; simpl in H.
  + simpl.
    rewrite Z.max_r by omega.
    pose_size_mult cenv_cs t (0 :: i :: z :: nil).
    omega.
  + unfold gfield_type, gfield_offset.
    pose_sizeof_co (Tstruct id a).
    pose proof field_offset_in_range _ _ H.
    pose proof sizeof_pos (field_type i (co_members (get_co id))).
    omega.
  + unfold gfield_type, gfield_offset.
    pose_sizeof_co (Tunion id a).
    pose proof sizeof_union_in_members _ _ H.
    pose proof sizeof_pos (field_type i (co_members (get_co id))).
    omega.
Qed.

Lemma nested_field_offset_in_range: forall t gfs,
  legal_nested_field t gfs ->
  complete_legal_cosu_type t = true ->
  0 <= nested_field_offset t gfs /\
  (nested_field_offset t gfs) + sizeof (nested_field_type t gfs) <= sizeof t.
Proof.
  intros.
  induction gfs as [| gf gfs]; rewrite nested_field_type_ind, nested_field_offset_ind by auto.
  + omega.
  + specialize (IHgfs (proj1 H)).
    pose proof gfield_offset_in_range (nested_field_type t gfs) gf (proj2 H).
    destruct H.
    spec H1; [apply nested_field_type_complete_legal_cosu_type; auto |].
    omega.
Qed.

Lemma nested_field_array_offset_in_range: forall t gfs lo hi,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  legal_nested_field0 t (ArraySubsc hi :: gfs) ->
  complete_legal_cosu_type t = true ->
  0 <= nested_field_offset t (ArraySubsc lo :: gfs) /\
  nested_field_offset t (ArraySubsc lo :: gfs) + sizeof (nested_field_array_type t gfs lo hi) <= sizeof t.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  rewrite nested_field0_offset_ind by auto.
  pose proof gfield_array_offset_in_range (nested_field_type t gfs) lo hi (proj2 H) (proj2 H0).
  destruct H0.
  spec H2; [apply nested_field_type_complete_legal_cosu_type; auto |].
  pose proof nested_field_offset_in_range t gfs (proj1 H) H1.
  omega.
Qed.

Lemma nested_field0_offset_in_range: forall (t : type) (gfs : list gfield),
  legal_nested_field0 t gfs ->
  complete_legal_cosu_type t = true ->
  0 <= nested_field_offset t gfs <= sizeof t.
Proof.
  intros.
  destruct gfs as [| gf gfs]; rewrite nested_field0_offset_ind by auto.
  + pose proof sizeof_pos t; omega.
  + pose proof gfield0_offset_in_range (nested_field_type t gfs) gf (proj2 H).
    destruct H.
    spec H1; [apply nested_field_type_complete_legal_cosu_type; auto |].
    pose proof nested_field_offset_in_range t gfs.
    spec H3; [auto |].
    spec H3; [auto |].
    omega.
Qed.

(************************************************

nested_field app

************************************************)

Lemma nested_field_type_nested_field_type: forall t gfs0 gfs1,
  nested_field_type (nested_field_type t gfs0) gfs1 = nested_field_type t (gfs1 ++ gfs0).
Proof.
  intros.
  induction gfs1.
  + rewrite nested_field_type_ind.
    reflexivity.
  + rewrite nested_field_type_ind.
    simpl app.
    rewrite nested_field_type_ind with (t := t) (gfs := a :: gfs1 ++ gfs0).
    rewrite IHgfs1.
    reflexivity.
Defined.

Lemma legal_nested_field_shrink: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) -> legal_nested_field t gfs0.
Proof.
  intros.
  induction gfs1.
  + simpl in *; auto.
  + simpl app in H.
    simpl in H.
    tauto.
Qed.

Lemma legal_nested_field0_shrink: forall t gfs0 gfs1,
  legal_nested_field0 t (gfs1 ++ gfs0) -> legal_nested_field0 t gfs0.
Proof.
  intros.
  destruct gfs1.
  + simpl in *; auto.
  + simpl app in H.
    destruct H.
    apply legal_nested_field_shrink in H; auto.
Qed.

Lemma legal_nested_field0_shrink1: forall t gfs0 gfs1,
  gfs1 <> nil ->
  legal_nested_field0 t (gfs1 ++ gfs0) -> legal_nested_field t gfs0.
Proof.
  intros.
  destruct gfs1.
  + congruence.
  + simpl app in H0.
    destruct H0.
    apply legal_nested_field_shrink in H0; auto.
Qed.

Lemma legal_nested_field_app: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) -> legal_nested_field (nested_field_type t gfs0) gfs1.
Proof.
  intros.
  induction gfs1.
  + exact I.
  + simpl in H.
    specialize (IHgfs1 (proj1 H)).
    simpl.
    rewrite nested_field_type_nested_field_type.
    tauto.
Qed.

Lemma legal_nested_field0_app: forall t gfs0 gfs1,
  legal_nested_field0 t (gfs1 ++ gfs0) -> legal_nested_field0 (nested_field_type t gfs0) gfs1.
Proof.
  intros.
  destruct gfs1.
  + exact I.
  + simpl in H.
    pose proof legal_nested_field_app t gfs0 gfs1.
    simpl.
    rewrite nested_field_type_nested_field_type.
    tauto.
Qed.

Lemma legal_nested_field_app_inv: forall t gfs0 gfs1,
  legal_nested_field t gfs0 ->
  legal_nested_field (nested_field_type t gfs0) gfs1 ->
  legal_nested_field t (gfs1 ++ gfs0).
Proof.
  intros.
  induction gfs1.
  + exact H.
  + simpl in *.
    rewrite <- nested_field_type_nested_field_type.
    tauto.
Qed.

Lemma legal_nested_field0_app_inv: forall t gfs0 gfs1,
  legal_nested_field t gfs0 ->
  legal_nested_field0 (nested_field_type t gfs0) gfs1 ->
  legal_nested_field0 t (gfs1 ++ gfs0).
Proof.
  intros.
  destruct gfs1.
  + apply legal_nested_field0_field.
    exact H.
  + simpl in *.
    rewrite <- nested_field_type_nested_field_type.
    destruct H0.
    split; auto.
    apply legal_nested_field_app_inv; auto.
Qed.

Lemma nested_field_offset_app: forall t gfs0 gfs1,
  legal_nested_field t (gfs1 ++ gfs0) ->
  nested_field_offset t (gfs1 ++ gfs0) = nested_field_offset t gfs0 +
    nested_field_offset (nested_field_type t gfs0) gfs1.
Proof.
  intros.
  induction gfs1.
  + simpl app.
    rewrite nested_field_offset_ind with (gfs := nil) by exact I.
    omega.
  + simpl app in *.
    specialize (IHgfs1 (proj1 H)).
    rewrite nested_field_offset_ind with (gfs := a :: gfs1 ++ gfs0) by auto.
    rewrite nested_field_offset_ind with (gfs := a :: gfs1) by (apply legal_nested_field0_field; apply legal_nested_field_app; auto).
    rewrite nested_field_type_nested_field_type.
    omega.
Qed.

Lemma nested_field_offset0_app: forall t gfs0 gfs1,
  legal_nested_field0 t (gfs1 ++ gfs0) ->
  nested_field_offset t (gfs1 ++ gfs0) = nested_field_offset t gfs0 +
    nested_field_offset (nested_field_type t gfs0) gfs1.
Proof.
  intros.
  destruct gfs1.
  + simpl app.
    rewrite nested_field_offset_ind with (gfs := nil) by exact I.
    omega.
  + simpl app in *.
    rewrite nested_field_offset_ind with (gfs := g :: gfs1 ++ gfs0) by auto.
    rewrite nested_field_offset_ind with (gfs := g :: gfs1) by (apply legal_nested_field0_app; auto).
    destruct H.
    pose proof (nested_field_offset_app t gfs0 gfs1 H).
    rewrite nested_field_type_nested_field_type.
    omega.
Qed.
(*
Lemma size_1_compatible: forall t, sizeof t = 1 -> forall p, size_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  destruct (Ptrofs.unsigned_range i).
  omega.
Qed.
*)
Lemma size_0_compatible: forall t, sizeof t = 0 -> forall p, size_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  destruct (Ptrofs.unsigned_range i).
  omega.
Qed.
(*
Lemma align_1_compatible: forall t, alignof t = 1 -> forall p, align_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  apply Z.divide_1_l.
Qed.
*)

Lemma size_compatible_nested_field: forall t gfs p,
  legal_nested_field t gfs ->
  complete_legal_cosu_type t = true ->
  size_compatible t p ->
  size_compatible (nested_field_type t gfs) (offset_val (nested_field_offset t gfs) p).
Proof.
  intros.
  destruct p; simpl; try tauto.
  unfold size_compatible in H1.
  solve_mod_modulus.
  inv_int i.
  pose proof nested_field_offset_in_range t gfs H H0.
  pose proof Zmod_le (ofs + nested_field_offset t gfs) (Ptrofs.modulus).
  spec H4; [pose proof Ptrofs.modulus_pos; omega |].
  spec H4; [omega |].
  pose proof nested_field_offset_in_range t gfs H H0.
  omega.
Qed.

Lemma size_compatible_nested_field_array: forall t gfs lo hi p,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  legal_nested_field0 t (ArraySubsc hi :: gfs) ->
  complete_legal_cosu_type t = true ->
  size_compatible t p ->
  size_compatible (nested_field_array_type t gfs lo hi)
   (offset_val (nested_field_offset t (ArraySubsc lo :: gfs)) p).
Proof.
  intros.
  destruct p; simpl; try tauto.
  unfold size_compatible in H2.
  solve_mod_modulus.
  inv_int i.
  pose proof nested_field_array_offset_in_range t gfs lo hi H H0 H1.
  pose proof Zmod_le (ofs + nested_field_offset t (ArraySubsc lo :: gfs)) (Ptrofs.modulus).
  spec H5; [pose proof Ptrofs.modulus_pos; omega |].
  spec H5; [omega |].
  pose proof nested_field_offset_in_range t gfs (proj1 H) H1.
  simpl in H3.
  omega.
Qed.

Lemma align_compatible_nested_field: forall t gfs p,
  legal_nested_field t gfs ->
  size_compatible t p ->
  align_compatible t p ->
  complete_legal_cosu_type t = true ->
  align_compatible (nested_field_type t gfs) (offset_val (nested_field_offset t gfs) p).
Proof.
  intros. rename H2 into Hcomplete.
  destruct p; simpl in *; try tauto.
  unfold Ptrofs.unsigned; simpl.
  unfold Ptrofs.unsigned at 2; simpl.
  repeat rewrite Ptrofs.Z_mod_modulus_eq.
  rewrite Zplus_mod_idemp_r.
  inv_int i.
  induction gfs as [| gf gfs].
  + rewrite nested_field_type_ind.
    rewrite nested_field_offset_ind by auto.
    rewrite Z.add_0_r.
    rewrite Zmod_small by auto.
    auto.
  + rewrite nested_field_type_ind.
     destruct H.
     specialize (IHgfs H).
     destruct (nested_field_offset_in_range t gfs H Hcomplete).
     destruct gf.
    *
      destruct (nested_field_type t gfs) eqn:?H; try contradiction H2.
      simpl in *.
      rewrite Z.max_r in H5 by omega.
      rewrite nested_field_offset_ind by (split;auto; hnf; rewrite H6; omega).
      rewrite H6. simpl.
     apply align_compatible_rec_Tarray_inv with (i:=i) in IHgfs; auto.
     match goal with H: align_compatible_rec _ t0 ?A |- align_compatible_rec _ t0 ?B => replace B with A; auto end.
     pose proof (sizeof_pos t).  pose proof (sizeof_pos t0).
     rewrite Z.add_assoc.
     assert (Ptrofs.modulus <> 0) by computable.
     rewrite (Z.add_mod (_ + _)) by auto.
     assert (0 <= sizeof t0 * i <= sizeof t0 * z). {
           rewrite <- (Z.mul_0_r (sizeof t0)).
           split; apply Zmult_le_compat_l; omega.
     }
     rewrite (Z.mod_small (sizeof t0 * i))  by omega.
     symmetry. apply Z.mod_small.
     rewrite Z.mod_small; omega.
   *
      assert (H12:= nested_field_type_complete_legal_cosu_type _ _ Hcomplete H).
      destruct (nested_field_type t gfs) eqn:?H; try contradiction H2.
      unfold gfield_type.
      destruct (gfield_offset_in_range (Tstruct i0 a) (StructField i) H2 H12) as [H13 H14].
      simpl in H2.
      eapply align_compatible_rec_Tstruct_inv' in IHgfs; try eassumption.
      match goal with H: align_compatible_rec _ _ ?A |- align_compatible_rec _ _ ?B => replace B with A; auto end.
      clear IHgfs.
      rewrite (nested_field_offset_ind _ (_ DOT _)) by (split; auto; rewrite H6; simpl; auto).
      rewrite H6. unfold gfield_offset.
     pose proof (sizeof_pos t). pose proof (sizeof_pos (Tstruct i0 a)).
     rewrite Z.add_assoc.
     assert (Ptrofs.modulus <> 0) by computable.
     rewrite (Z.add_mod (_ + _)) by auto.
     rewrite (Z.mod_small (ofs + _)) by omega.
     pose (sizeof_pos (field_type i (co_members (get_co i0)))).
     unfold gfield_offset in H13, H14. unfold gfield_type in H14.
     rewrite (Z.mod_small (field_offset _ _ _)) by omega.
     symmetry. apply Z.mod_small.
     omega.
   *
      assert (H12:= nested_field_type_complete_legal_cosu_type _ _ Hcomplete H).
      destruct (nested_field_type t gfs) eqn:?H; try contradiction H2.
      unfold gfield_type.
      destruct (gfield_offset_in_range (Tunion i0 a) (UnionField i) H2 H12) as [H13 H14].
      simpl in H2.
      eapply align_compatible_rec_Tunion_inv' in IHgfs; try eassumption.
      match goal with H: align_compatible_rec _ _ ?A |- align_compatible_rec _ _ ?B => replace B with A; auto end.
      clear IHgfs.
      rewrite (nested_field_offset_ind _ (_ UDOT _)) by (split; auto; rewrite H6; simpl; auto).
      rewrite H6. unfold gfield_offset.
      rewrite Z.add_0_r. auto.
Qed.

Lemma align_compatible_nested_field_array: forall t gfs lo hi p,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  legal_nested_field0 t (ArraySubsc hi :: gfs) ->
  size_compatible t p ->
  align_compatible t p ->
  complete_legal_cosu_type t = true ->
  align_compatible (nested_field_array_type t gfs lo hi)
   (offset_val (nested_field_offset t (ArraySubsc lo :: gfs)) p).
Proof.
  intros.
  intros. rename H3 into Hcomplete.
  rewrite nested_field_offset_ind by auto.
  destruct H.
  destruct H0 as [_ ?].
  assert (H9:= align_compatible_nested_field t gfs p H H1 H2 Hcomplete).
  rewrite nested_field_array_type_ind.
  destruct (nested_field_type t gfs) eqn:?H; inv H3. simpl in H0.
  simpl gfield_array_type.
  destruct p; simpl in *; try tauto.
  unfold Ptrofs.unsigned; simpl.
  unfold Ptrofs.unsigned at 2; simpl.
  apply align_compatible_rec_Tarray.
  intros j ?.
  apply align_compatible_rec_Tarray_inv with (i:= (lo+j)) in H9; [ |omega].
  match goal with H: align_compatible_rec _ _ ?A |- align_compatible_rec _ _ ?B => replace B with A; auto end.
  rewrite !Ptrofs.Z_mod_modulus_eq.
  rewrite Z.mul_add_distr_l.
  rewrite Z.add_assoc.
  f_equal.
  unfold Ptrofs.add.
  destruct (nested_field_offset_in_range t gfs H Hcomplete).
  pose proof (sizeof_pos (nested_field_type t gfs)).
  assert (Ptrofs.max_unsigned = Ptrofs.modulus-1) by computable. (* TODO: This should not be necessary, rep_omega should know it *)
  rewrite (Ptrofs.unsigned_repr (nested_field_offset _ _)) by rep_omega.
  rewrite Ptrofs.unsigned_repr by rep_omega.
  pose proof (sizeof_pos t0).
     assert (0 <= sizeof t0 * lo <= sizeof t0 * z). {
           rewrite <- (Z.mul_0_r (sizeof t0)).
           split; apply Zmult_le_compat_l; omega.
     }
  rewrite H4 in *. simpl in H8. rewrite Z.max_r in H8 by omega.
  rewrite (Z.mod_small (_ + _ * _)) by rep_omega.
  rewrite Z.add_assoc.
  symmetry; apply Z.mod_small.
  rep_omega.
Qed.

Lemma field_compatible_nested_field: forall t gfs p,
  field_compatible t gfs p ->
  field_compatible (nested_field_type t gfs) nil (offset_val (nested_field_offset t gfs) p).
Proof.
  intros.
  unfold field_compatible in *.
  repeat split.
  + rewrite isptr_offset_val; tauto.
  + apply nested_field_type_complete_legal_cosu_type; auto; tauto.
  + apply size_compatible_nested_field; tauto.
  + apply align_compatible_nested_field; tauto.
Qed.

Lemma field_compatible0_nested_field_array: forall t gfs lo hi p,
  field_compatible0 t (ArraySubsc lo :: gfs) p ->
  field_compatible0 t (ArraySubsc hi :: gfs) p ->
  lo <= hi ->
  field_compatible (nested_field_array_type t gfs lo hi) nil (offset_val (nested_field_offset t (ArraySubsc lo :: gfs)) p).
Proof.
  intros.
  unfold field_compatible, field_compatible0 in *.
  repeat split.
  + rewrite isptr_offset_val; tauto.
  + apply nested_field_array_type_complete_legal_cosu_type; try tauto.
  + apply size_compatible_nested_field_array; tauto.
  + apply align_compatible_nested_field_array; tauto.
Qed.

Lemma field_compatible_isptr :
  forall t path p, field_compatible t path p -> isptr p.
Proof. intros. destruct H; auto. Qed.

Lemma field_compatible0_isptr :
  forall t path p, field_compatible0 t path p -> isptr p.
Proof.
intros. destruct H; auto.
Qed.
(*
Lemma field_compatible_complete_type:
  forall t path p, field_compatible t path p -> complete_type cenv_cs t = true.
Proof. intros. destruct H; tauto. Qed.

Lemma field_compatible0_complete_type:
  forall t path p, field_compatible0 t path p -> complete_type cenv_cs t = true.
Proof. intros. destruct H; tauto. Qed.
*)
Lemma field_compatible_legal_nested_field:
  forall (t : type) (path : list gfield) (p : val),
  field_compatible t path p -> legal_nested_field t path.
Proof.
  intros.
  destruct H; tauto.
Qed.

Lemma field_compatible_legal_nested_field0:
  forall (t : type) (path : list gfield) (p : val),
  field_compatible t path p -> legal_nested_field0 t path.
Proof.
  intros.
  apply legal_nested_field0_field.
  destruct H; tauto.
Qed.

Lemma field_compatible0_legal_nested_field0:
  forall (t : type) (path : list gfield) (p : val),
  field_compatible0 t path p -> legal_nested_field0 t path.
Proof.
  intros.
  destruct H; tauto.
Qed.

Lemma field_compatible_field_address: forall t gfs p, field_compatible t gfs p -> field_address t gfs p = offset_val (nested_field_offset t gfs) p.
Proof.
  intros.
  unfold field_address.
  rewrite if_true by auto.
  auto.
Qed.

Lemma field_compatible0_field_address0: forall t gfs p, field_compatible0 t gfs p -> field_address0 t gfs p = offset_val (nested_field_offset t gfs) p.
Proof.
  intros.
  unfold field_address0.
  rewrite if_true by auto.
  auto.
Qed.

Lemma field_compatible_shrink: forall t_root gfsB gfsA a,
  field_compatible t_root (gfsB ++ gfsA) a ->
  field_compatible t_root gfsA a.
Proof.
  intros. unfold field_compatible in *. rename H into A. repeat destruct A as [? A].
  repeat split; try assumption. eapply legal_nested_field_shrink. eassumption.
Qed.

Lemma field_compatible0_shrink: forall t_root gfsB gfsA a,
  field_compatible0 t_root (gfsB ++ gfsA) a ->
  field_compatible0 t_root gfsA a.
Proof.
  intros. unfold field_compatible0 in *. rename H into A. repeat destruct A as [? A].
  repeat split; try assumption. eapply legal_nested_field0_shrink. eassumption.
Qed.

Lemma field_compatible0_shrink1: forall t_root gfsB gfsA a,
  gfsB <> nil ->
  field_compatible0 t_root (gfsB ++ gfsA) a ->
  field_compatible t_root gfsA a.
Proof.
  intros. unfold field_compatible0, field_compatible in *. rename H0 into A. repeat destruct A as [? A].
  repeat split; try assumption. eapply legal_nested_field0_shrink1. eassumption. eassumption.
Qed.

Lemma field_compatible_app: forall gfsB t_root gfsA a,
  field_compatible t_root (gfsB ++ gfsA) a ->
  field_compatible (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a).
Proof.
  intro gfsB. induction gfsB; intros.
  - simpl in H. rewrite field_compatible_field_address by assumption.
    apply field_compatible_nested_field. assumption.
  - rewrite <- app_comm_cons in H.
    apply field_compatible_cons in H.
    destruct (nested_field_type t_root (gfsB ++ gfsA)) eqn: E;
    try solve [exfalso; assumption];
    destruct a; try solve [exfalso; assumption];
    rewrite <- nested_field_type_nested_field_type in E;
    apply field_compatible_cons;
    rewrite E; destruct H; auto.
Qed.

Lemma field_compatible0_app1: forall gfsB t_root gfsA a
  (NEQ: gfsB <> nil),
  field_compatible0 t_root (gfsB ++ gfsA) a ->
  field_compatible0 (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a).
Proof.
  intros.
  destruct gfsB; [congruence | clear NEQ].
  pose proof field_compatible_app gfsB t_root gfsA a.
  rewrite <- app_comm_cons in H.
  apply field_compatible0_cons in H.
  destruct (nested_field_type t_root (gfsB ++ gfsA)) eqn: E;
  try solve [exfalso; assumption];
  destruct g; try solve [exfalso; assumption];
  rewrite <- nested_field_type_nested_field_type in E;
  apply field_compatible0_cons;
  rewrite E; destruct H; auto.
Qed.

Lemma field_compatible_app_inv': forall gfsB t_root gfsA a,
  field_compatible t_root gfsA a ->
  legal_nested_field (nested_field_type t_root gfsA) gfsB ->
  field_compatible t_root (gfsB ++ gfsA) a.
Proof.
  unfold field_compatible.
  intros.
  pose proof legal_nested_field_app_inv t_root gfsA gfsB.
  tauto.
Qed.

Lemma field_compatible0_app_inv': forall gfsB t_root gfsA a,
  field_compatible t_root gfsA a ->
  legal_nested_field0 (nested_field_type t_root gfsA) gfsB ->
  field_compatible0 t_root (gfsB ++ gfsA) a.
Proof.
  unfold field_compatible0, field_compatible.
  intros.
  pose proof legal_nested_field0_app_inv t_root gfsA gfsB.
  tauto.
Qed.

Lemma field_compatible_app_inv: forall gfsB t_root gfsA a,
  field_compatible t_root gfsA a ->
  field_compatible (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a) ->
  field_compatible t_root (gfsB ++ gfsA) a.
Proof.
  intros.
  apply field_compatible_app_inv'; auto.
  destruct H0; tauto.
Qed.

Lemma field_compatible0_app_inv: forall gfsB t_root gfsA a,
  field_compatible t_root gfsA a ->
  field_compatible0 (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a) ->
  field_compatible0 t_root (gfsB ++ gfsA) a.
Proof.
  intros.
  apply field_compatible0_app_inv'; auto.
  destruct H0; tauto.
Qed.

Lemma field_address_app: forall t_root gfsA gfsB a,
  field_address t_root (gfsB ++ gfsA) a =
  field_address (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a).
Proof.
  intros.
  assert (
    ~ field_compatible t_root gfsA a /\ ~ field_compatible t_root (gfsB ++ gfsA) a \/
    ~ field_compatible (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a) /\ ~ field_compatible t_root (gfsB ++ gfsA) a \/
    field_compatible t_root (gfsB ++ gfsA) a).
  {
    pose proof field_compatible_app_inv gfsB t_root gfsA a.
    tauto.
  }
  destruct H as [[? ?] | [[? ?] | ?]].
  + unfold field_address.
    rewrite if_false by auto.
    destruct (field_compatible_dec t_root gfsA a); [tauto |].
    if_tac; reflexivity.
  + unfold field_address.
    rewrite if_false by auto.
    rewrite if_false by auto.
    reflexivity.
  + rewrite field_compatible_field_address.
    rewrite field_compatible_field_address.
    rewrite nested_field_offset_app.
    rewrite field_compatible_field_address.
    rewrite offset_offset_val.
    reflexivity.
    { eapply field_compatible_shrink. eassumption. }
    { eapply field_compatible_legal_nested_field. eassumption. }
    { eapply field_compatible_app. assumption. }
    { assumption. }
Qed.

Lemma field_address0_app: forall t_root gfsA gfsB a
  (NEQ: gfsB <> nil),
  field_address0 t_root (gfsB ++ gfsA) a =
  field_address0 (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a).
Proof.
  intros.
  assert (
    ~ field_compatible t_root gfsA a /\ ~ field_compatible0 t_root (gfsB ++ gfsA) a \/
    ~ field_compatible0 (nested_field_type t_root gfsA) gfsB (field_address t_root gfsA a) /\ ~ field_compatible0 t_root (gfsB ++ gfsA) a \/
    field_compatible0 t_root (gfsB ++ gfsA) a).
  {
    pose proof field_compatible0_app_inv gfsB t_root gfsA a.
    tauto.
  }
  destruct H as [[? ?] | [[? ?] | ?]].
  + unfold field_address0, field_address.
    rewrite if_false by auto.
    destruct (field_compatible_dec t_root gfsA a); [tauto |].
    if_tac; reflexivity.
  + unfold field_address0, field_address.
    rewrite if_false by auto.
    rewrite if_false by auto.
    reflexivity.
  + rewrite field_compatible0_field_address0.
    rewrite field_compatible0_field_address0.
    rewrite nested_field_offset0_app.
    rewrite field_compatible_field_address.
    rewrite offset_offset_val.
    reflexivity.
    { eapply field_compatible0_shrink1; eassumption. }
    { eapply field_compatible0_legal_nested_field0. eassumption. }
    { eapply field_compatible0_app1; assumption. }
    { assumption. }
Qed.

End COMPOSITE_ENV.
(*
Arguments nested_field_offset2 {cs} t gfs /.
Arguments nested_field_type2 {cs} t gfs /.
*)

(* Hint Resolve field_address_isptr. *)
Hint Resolve is_pointer_or_null_field_compatible.
(* Hint Extern 1 (complete_type _ _ = true) => (eapply field_compatible_complete_type; eassumption). *)
Hint Extern 1 (isptr _) => (eapply field_compatible_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_isptr; eassumption).
Hint Extern 1 (legal_nested_field _ _) => (eapply field_compatible_legal_nested_field; eassumption).
Hint Extern 1 (legal_nested_field0 _ _) => (eapply field_compatible_legal_nested_field0; eassumption).
Hint Extern 1 (legal_nested_field0 _ _) => (eapply field_compatible0_legal_nested_field0; eassumption).

Lemma nested_field_type_preserves_change_composite: forall {cs_from cs_to} {CCE: change_composite_env cs_from cs_to} (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  forall gfs, cs_preserve_type cs_from cs_to (coeq cs_from cs_to) (@nested_field_type cs_to t gfs) = true.
Proof.
  intros.
  induction gfs; auto.
  rewrite (@nested_field_type_ind cs_to).
  revert IHgfs; generalize (@nested_field_type cs_to t gfs) as T; clear; intros.
  destruct a.
  + destruct T; auto.
  + destruct T; auto.
    unfold gfield_type.
    apply members_spec_change_composite''; auto.
  + destruct T; auto.
    unfold gfield_type.
    apply members_spec_change_composite''; auto.
Qed.

Lemma nested_field_type_change_composite: forall {cs_from cs_to} {CCE: change_composite_env cs_from cs_to} (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  forall gfs, @nested_field_type cs_from t gfs = @nested_field_type cs_to t gfs.
Proof.
  intros.
  induction gfs; auto.
  rewrite (@nested_field_type_ind cs_from).
  rewrite (@nested_field_type_ind cs_to).
  rewrite IHgfs.
  clear IHgfs.
  generalize (nested_field_type_preserves_change_composite _ H gfs).
  generalize (@nested_field_type cs_to t gfs) as T; clear; intros.
    destruct a.
    - destruct T; auto.
    - destruct T; auto.
      unfold gfield_type.
      rewrite co_members_get_co_change_composite; auto.
    - destruct T; auto.
      unfold gfield_type.
      rewrite co_members_get_co_change_composite; auto.
Qed.

Lemma legal_nested_field_change_composite: forall {cs_from cs_to} {CCE: change_composite_env cs_from cs_to} (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  forall gfs, @legal_nested_field cs_from t gfs <-> @legal_nested_field cs_to t gfs.
Proof.
  intros.
  revert t H; induction gfs; intros.
  + simpl.
    tauto.
  + simpl.
    apply Morphisms_Prop.and_iff_morphism; [apply IHgfs; auto |].
    rewrite nested_field_type_change_composite by auto.
    generalize (nested_field_type_preserves_change_composite _ H gfs).
    generalize (@nested_field_type cs_to t gfs) as T; clear; intros.
    destruct a.
    - destruct T; try tauto.
    - destruct T; try tauto.
      simpl.
      rewrite co_members_get_co_change_composite by auto.
      tauto.
    - destruct T; try tauto.
      simpl.
      rewrite co_members_get_co_change_composite by auto.
      tauto.
Qed.

Lemma field_compatible_change_composite: forall {cs_from cs_to} {CCE: change_composite_env cs_from cs_to} (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  forall gfs p, @field_compatible cs_from t gfs p <-> @field_compatible cs_to t gfs p.
Proof.
  intros.
  unfold field_compatible.
  apply and_iff_compat_l.
  rewrite complete_legal_cosu_type_change_composite by auto.
  apply and_iff_compat_l.
  apply Morphisms_Prop.and_iff_morphism; [| apply Morphisms_Prop.and_iff_morphism].
  + unfold size_compatible.
    rewrite sizeof_change_composite by auto.
    reflexivity.
  + unfold align_compatible.
    destruct p; try reflexivity.
    apply align_compatible_rec_change_composite; auto.
  + apply legal_nested_field_change_composite; auto.
Qed.

Lemma nested_field_offset_change_composite: forall {cs_from cs_to} {CCE: change_composite_env cs_from cs_to} (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  forall gfs,
    @legal_nested_field cs_from t gfs ->
    @legal_nested_field cs_to t gfs ->
    @nested_field_offset cs_from t gfs = @nested_field_offset cs_to t gfs.
Proof.
  intros.
  induction gfs; auto.
  rewrite (@nested_field_offset_ind cs_from) by (apply legal_nested_field0_field; auto).
  rewrite (@nested_field_offset_ind cs_to) by (apply legal_nested_field0_field; auto).
  rewrite IHgfs by (simpl in H0, H1; tauto).
  clear IHgfs.
  f_equal.
  destruct H1 as [_ ?].
  rewrite nested_field_type_change_composite by auto.
  generalize (nested_field_type_preserves_change_composite _ H gfs).
  revert H1.
  generalize (@nested_field_type cs_to t gfs) as T; clear; intros.
  destruct a.
  + destruct T; auto; inv H1.
    simpl.
    f_equal.
    apply sizeof_change_composite; auto.
  + destruct T; try inv H1.
    unfold gfield_offset.
    rewrite co_members_get_co_change_composite by auto.
    apply field_offset_change_composite; auto.
  + destruct T; try inv H1.
    auto.
Qed.

Lemma lvar_size_compatible:
  forall  {cs: compspecs} id t v rho,
  locald_denote (lvar id t v) rho ->
  sizeof t < Ptrofs.modulus ->
  size_compatible t v.
Proof.
intros. hnf in H.
destruct (Map.get (ve_of rho) id) as [[? ?] | ]; try contradiction.
destruct H; subst.
red.
rewrite Ptrofs.unsigned_zero. rewrite Z.add_0_l; auto.
Qed.

Lemma lvar_field_compatible:
  forall {cs: compspecs} id t v rho,
    locald_denote (lvar id t v) rho ->
    complete_legal_cosu_type t = true ->
    is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true ->
    sizeof t < Ptrofs.modulus ->
    field_compatible t nil v.
Proof.
  intros.
  pose proof (lvar_size_compatible _ _ _ _ H).
  hnf in H.
  destruct (Map.get (ve_of rho) id); try contradiction.
  destruct p. destruct H. subst v t0.
  repeat split; auto.
  hnf.
  apply la_env_cs_sound; auto.
Qed.

Lemma compute_in_members_e:
 forall i al, compute_in_members i al = true -> in_members i al.
Proof.
intros.
apply compute_in_members_true_iff. auto.
Qed.

Hint Extern 2 (field_compatible _ (StructField _ :: _) _) =>
  (apply field_compatible_cons; split; [ apply compute_in_members_e; reflexivity | ])
      : field_compatible.

Lemma field_compatible_nullval: forall CS t f P,
  @field_compatible CS t f nullval -> P.
Proof.
intros.
destruct H.
contradiction H.
Qed.

Lemma field_compatible_nullval1:
 forall (CS: compspecs) t fld p,
  @field_compatible CS t fld p -> p <> nullval.
Proof.
 intros. intro; subst p. apply (field_compatible_nullval _ _ _ _ H).
Qed.

Lemma field_compatible_nullval2:
 forall (CS: compspecs) t fld p,
  @field_compatible CS t fld p -> nullval <> p.
Proof.
 intros. intro; subst p. apply (field_compatible_nullval _ _ _ _ H).
Qed.

