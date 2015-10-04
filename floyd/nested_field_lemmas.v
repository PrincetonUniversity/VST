Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require floyd.fieldlist.
Import floyd.fieldlist.fieldlist.
Require Import floyd.type_induction.
Require Import floyd.nested_pred_lemmas.
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
  | Tarray t0 _ _, ArraySubsc i => sizeof cenv_cs t0 * i
  | Tstruct id _, StructField i => field_offset cenv_cs i (co_members (get_co id))
  | Tunion id _, UnionField i => 0
  | _, _ => 0
  end.

Definition gfield_array_type t lo hi :=
  match t with
  | Tarray t0 _ a => Tarray t0 (hi - lo) a
  | _ => Tarray Tvoid (hi - lo) (attr_of_type t)
  end.

Fixpoint nested_field_rec (t: type) (gfs: list gfield) : option (prod Z type) :=
  match gfs with
  | nil => Some (0, t)
  | hd :: tl =>
    match nested_field_rec t tl with
    | Some (pos, t') => 
      match t', hd with
      | Tarray t'' n _, ArraySubsc i => Some(pos + sizeof cenv_cs t'' * i, t'')
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
*)

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

Definition nested_field_array_type t gfs lo hi :=
  Tarray (nested_field_type2 t (ArraySubsc 0 :: gfs)) (hi - lo) (attr_of_type (nested_field_type2 t gfs)).

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
  | gf :: gfs0 => legal_nested_field t gfs0 /\ legal_field (nested_field_type2 t gfs0) gf
  end.

Definition legal_nested_field0 t gfs :=
  match gfs with
  | nil => True
  | gf :: gfs0 => legal_nested_field t gfs0 /\ legal_field0 (nested_field_type2 t gfs0) gf
  end.

Fixpoint compute_legal_nested_field (t: type) (gfs: list gfield) : list Prop :=
  match gfs with
  | nil => nil
  | gf :: gfs0 =>
    match (nested_field_type2 t gfs0), gf with
    | Tarray _ n _, ArraySubsc i =>
       (0 <= i < n) :: compute_legal_nested_field t gfs0
    | Tstruct id _, StructField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs0 else False :: nil
    | Tunion id _, UnionField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs0 else False :: nil
    | _, _ => False :: nil
    end
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

Lemma nested_field_array_type_ind: forall t gfs lo hi,
  nested_field_array_type t gfs lo hi =
  gfield_array_type (nested_field_type2 t gfs) lo hi.
Proof.
  intros.
  unfold nested_field_array_type.
  rewrite nested_field_type2_ind.
  destruct (nested_field_type2 t gfs); simpl; auto.
Qed.

Lemma nested_field0_offset2_ind: forall t gfs,
  legal_nested_field0 t gfs ->
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
    destruct gf, (nested_field_type2 t gfs) as [| | | | | | | id ? | id ?]; try solve [right; tauto];
    unfold legal_field0.
    - apply sumbool_dec_and; [apply Z_le_dec | apply Z_le_dec].
    - destruct_in_members i (co_members (get_co id)); auto.
    - destruct_in_members i (co_members (get_co id)); auto.
Qed.

Definition field_compatible t gfs p :=
  isptr p /\
  legal_alignas_type t = true /\
  legal_cosu_type t = true /\
  complete_type cenv_cs t = true /\
  sizeof cenv_cs t < Int.modulus /\
  size_compatible t p /\
  align_compatible t p /\
  legal_nested_field t gfs.

Definition field_compatible0 t gfs p :=
  isptr p /\
  legal_alignas_type t = true /\
  legal_cosu_type t = true /\
  complete_type cenv_cs t = true /\
  sizeof cenv_cs t < Int.modulus /\
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
  + destruct legal_alignas_type; [left | right]; congruence.
  + destruct legal_cosu_type; [left | right]; congruence.
  + destruct complete_type; [left | right]; congruence.
  + destruct (zlt (sizeof cenv_cs t) Int.modulus); [left | right]; omega.
  + destruct p; simpl; try solve [left; auto].
    destruct (zle (Int.unsigned i + sizeof cenv_cs t) Int.modulus); [left | right]; omega.
  + destruct p; simpl; try solve [left; auto].
    apply Zdivide_dec.
    apply alignof_pos.
  + apply legal_nested_field_dec.
Qed.

Lemma field_compatible0_dec: forall t gfs p,
  {field_compatible0 t gfs p} + {~ field_compatible0 t gfs p}.
Proof.
  unfold field_compatible0.
  intros.
  repeat apply sumbool_dec_and.
  + destruct p; simpl; try (left; tauto); try (right; tauto).
  + destruct legal_alignas_type; [left | right]; congruence.
  + destruct legal_cosu_type; [left | right]; congruence.
  + destruct complete_type; [left | right]; congruence.
  + destruct (zlt (sizeof cenv_cs t) Int.modulus); [left | right]; omega.
  + destruct p; simpl; try solve [left; auto].
    destruct (zle (Int.unsigned i + sizeof cenv_cs t) Int.modulus); [left | right]; omega.
  + destruct p; simpl; try solve [left; auto].
    apply Zdivide_dec.
    apply alignof_pos.
  + apply legal_nested_field0_dec.
Qed.

Lemma field_compatible_cons: forall t gf gfs p,
  field_compatible t (gf :: gfs) p <->
  match nested_field_type2 t gfs, gf with
  | Tstruct id _, StructField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tunion id _, UnionField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tarray _ n _, ArraySubsc i => 0 <= i < n /\ field_compatible t gfs p
  | _, _ => False
  end.
Proof.
  intros.
  unfold field_compatible.
  simpl (legal_nested_field t (gf :: gfs)).
  destruct (nested_field_type2 t gfs), gf; simpl; tauto.
Qed.

Lemma field_compatible0_cons: forall t gf gfs p,
  field_compatible0 t (gf :: gfs) p <->
  match nested_field_type2 t gfs, gf with
  | Tstruct id _, StructField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tunion id _, UnionField i => in_members i (co_members (get_co id)) /\ field_compatible t gfs p
  | Tarray _ n _, ArraySubsc i => 0 <= i <= n /\ field_compatible t gfs p
  | _, _ => False
  end.
Proof.
  intros.
  unfold field_compatible, field_compatible0.
  simpl (legal_nested_field0 t (gf :: gfs)).
  destruct (nested_field_type2 t gfs), gf; simpl; tauto.
Qed.

(* The following two lemmas is covered by the previous two. Delete them some time. *)
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

Lemma field_compatible0_cons_Tarray:
  forall k t n a gfs p t',
  nested_field_type2 t gfs = Tarray t' n a ->
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
  then offset_val (Int.repr (nested_field_offset2 t gfs)) p
  else Vundef.

Definition field_address0 t gfs p :=
  if (field_compatible0_dec t gfs p)
  then offset_val (Int.repr (nested_field_offset2 t gfs)) p
  else Vundef.

Lemma field_address_isptr:
  forall t path c, isptr c -> field_compatible t path c -> isptr (field_address t path c).
Proof.
  intros.
  unfold field_address. rewrite if_true by auto.
  normalize.
Qed.

Lemma field_address0_isptr:
  forall t path c, isptr c -> field_compatible0 t path c -> isptr (field_address0 t path c).
Proof.
 intros.
 unfold field_address0. rewrite if_true by auto.
 normalize.
Qed.

Lemma field_address_clarify:
 forall t path c,
   is_pointer_or_null (field_address t path c) ->
   field_address t path c = offset_val (Int.repr (nested_field_offset2 t path)) c.
Proof.
 intros. unfold field_address in *.
  if_tac; try contradiction.
  auto.
Qed.

Lemma field_address0_clarify:
 forall t path c,
   is_pointer_or_null (field_address0 t path c) ->
   field_address0 t path c = offset_val (Int.repr (nested_field_offset2 t path)) c.
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
  destruct (nested_field_type2 t gfs), gf; try tauto.
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
  destruct (nested_field_type2 t gfs); try tauto.
  assert (0 <= i < z <-> 0 <= i <= z /\ 0 <= i + 1 <= z) by omega.
  tauto.
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

Lemma nested_field_type2_ArraySubsc: forall t i gfs,
  nested_field_type2 t (ArraySubsc i :: gfs) = nested_field_type2 t (ArraySubsc 0 :: gfs).
Proof.
  intros.
  rewrite !nested_field_type2_ind with (gfs := _ :: gfs).
  destruct (nested_field_type2 t gfs); try tauto.
Qed.

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

Lemma nested_field_array_type_complete_type: forall t gfs lo hi,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  complete_type cenv_cs t = true ->
  complete_type cenv_cs (nested_field_array_type t gfs lo hi) = true.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  apply gfield_array_type_complete_type.
  + simpl in H; tauto.
  + apply nested_field_type2_complete_type; auto.
    simpl in H; tauto.
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

Lemma gfield_array_type_nested_pred: forall {atom_pred: type -> bool},
  (forall t n m a, atom_pred (Tarray t n a) = atom_pred (Tarray t m a)) ->
  forall (t: type) lo hi,
  legal_field0 t (ArraySubsc lo) ->
  nested_pred atom_pred t = true -> nested_pred atom_pred (gfield_array_type t lo hi) = true.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; auto.
  simpl in H1 |- *; rewrite nested_pred_ind in H1 |- *.
  erewrite H.
  exact H1.
Qed.

Lemma nested_field_type2_nest_pred: forall {atom_pred: type -> bool}, atom_pred Tvoid = true -> forall (t: type) (gfs: list gfield),
  nested_pred atom_pred t = true -> nested_pred atom_pred (nested_field_type2 t gfs) = true.
Proof.
  intros.
  induction gfs; rewrite nested_field_type2_ind.
  + auto.
  + apply gfield_type_nested_pred; auto.
Qed.

Lemma nested_field_array_type_nest_pred: forall {atom_pred: type -> bool},
  atom_pred Tvoid = true ->
  (forall t n m a, atom_pred (Tarray t n a) = atom_pred (Tarray t m a)) ->
  forall (t: type) gfs lo hi,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  nested_pred atom_pred t = true ->
  nested_pred atom_pred (nested_field_array_type t gfs lo hi) = true.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  simpl in H1.
  apply gfield_array_type_nested_pred; [auto | tauto |].
  apply nested_field_type2_nest_pred; auto.
Qed.

Lemma alignof_gfield_type_divide_alignof: forall t gf,
  legal_alignas_type t = true ->
  (alignof cenv_cs (gfield_type t gf) | alignof cenv_cs t).
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [simpl; apply Z.divide_1_l].
  + simpl.
    apply legal_alignas_type_spec in H.
    exact H.
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

Lemma alignof_gfield_array_type_divide_alignof: forall t lo hi,
  legal_alignas_type t = true ->
  legal_field0 t (ArraySubsc lo) ->
  (alignof cenv_cs (gfield_array_type t lo hi) | alignof cenv_cs t).
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?]; try solve [inversion H0].
  simpl.
  apply Z.divide_refl.
Qed.

(* was called alignof_gfield_type_divide *)
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

Lemma alignof_nested_field_array_type_divide_alignof: forall t gfs lo hi,
  legal_alignas_type t = true ->
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  (alignof cenv_cs (nested_field_array_type t gfs lo hi) | alignof cenv_cs t).
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  simpl in H0.
  eapply Z.divide_trans.
  + apply alignof_gfield_array_type_divide_alignof; [| tauto].
    apply nested_field_type2_nest_pred; auto.
  + apply alignof_nested_field_type2_divide_alignof; auto.
    tauto.
Qed.

Lemma gfield_offset_type_divide: forall gf t, legal_alignas_type t = true ->
  (alignof cenv_cs (gfield_type t gf) | gfield_offset t gf).
Proof.
  intros.
  pose proof H.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [simpl; apply Z.divide_0_r];
  unfold legal_alignas_type in H;
  rewrite nested_pred_ind in H;
  rewrite andb_true_iff in H;
  destruct H.
  + simpl.
    erewrite legal_alignas_type_Tarray by eauto.
    apply Z.divide_mul_l.
    apply legal_alignas_sizeof_alignof_compat; auto.
  + simpl.
    apply field_offset_aligned.
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
  legal_cosu_type t = true ->
  0 <= gfield_offset t gf /\ gfield_offset t gf + sizeof cenv_cs (gfield_type t gf) <= sizeof cenv_cs t.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [inversion H]; simpl in H.
  + simpl.
    rewrite Z.max_r by omega.
    pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil).
    omega.
  + simpl gfield_type; simpl gfield_offset.
    pose_sizeof_co (Tstruct id a).
    pose proof field_offset_in_range _ _ H.
    omega.
  + simpl gfield_type; simpl gfield_offset.
    pose_sizeof_co (Tunion id a).
    pose proof sizeof_union_in_members _ _ H.
    omega.
Qed.

Lemma gfield_array_offset_in_range: forall t lo hi,
  legal_field0 t (ArraySubsc lo) ->
  legal_field0 t (ArraySubsc hi) ->
  legal_cosu_type t = true ->
  0 <= gfield_offset t (ArraySubsc lo) /\
  gfield_offset t (ArraySubsc lo) + sizeof cenv_cs (gfield_array_type t lo hi) <= sizeof cenv_cs t.
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
  legal_cosu_type t = true ->
  0 <= gfield_offset t gf /\ gfield_offset t gf <= sizeof cenv_cs t.
Proof.
  intros.
  destruct t as [| | | | | | | id ? | id ?], gf; try solve [inversion H]; simpl in H.
  + simpl.
    rewrite Z.max_r by omega.
    pose_size_mult cenv_cs t (0 :: i :: z :: nil).
    omega.
  + simpl gfield_type; simpl gfield_offset.
    pose_sizeof_co (Tstruct id a).
    pose proof field_offset_in_range _ _ H.
    pose proof sizeof_pos cenv_cs (field_type i (co_members (get_co id))).
    omega.
  + simpl gfield_type; simpl gfield_offset.
    pose_sizeof_co (Tunion id a).
    pose proof sizeof_union_in_members _ _ H.
    pose proof sizeof_pos cenv_cs (field_type i (co_members (get_co id))).
    omega.
Qed.

Lemma nested_field_offset2_in_range: forall t gfs,
  legal_nested_field t gfs ->
  legal_cosu_type t = true ->
  0 <= nested_field_offset2 t gfs /\
  (nested_field_offset2 t gfs) + sizeof cenv_cs (nested_field_type2 t gfs) <= sizeof cenv_cs t.
Proof.
  intros.
  induction gfs as [| gf gfs]; rewrite nested_field_type2_ind, nested_field_offset2_ind by auto.
  + omega.
  + specialize (IHgfs (proj1 H)).
    pose proof gfield_offset_in_range (nested_field_type2 t gfs) gf (proj2 H).
    spec H1; [apply nested_field_type2_nest_pred; auto |].
    omega.
Qed.

Lemma nested_field_array_offset2_in_range: forall t gfs lo hi,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  legal_nested_field0 t (ArraySubsc hi :: gfs) ->
  legal_cosu_type t = true ->
  0 <= nested_field_offset2 t (ArraySubsc lo :: gfs) /\
  nested_field_offset2 t (ArraySubsc lo :: gfs) + sizeof cenv_cs (nested_field_array_type t gfs lo hi) <= sizeof cenv_cs t.
Proof.
  intros.
  rewrite nested_field_array_type_ind.
  rewrite nested_field0_offset2_ind by auto.
  pose proof gfield_array_offset_in_range (nested_field_type2 t gfs) lo hi (proj2 H) (proj2 H0).
  spec H2; [apply nested_field_type2_nest_pred; auto |].
  pose proof nested_field_offset2_in_range t gfs (proj1 H) H1.
  omega.
Qed.

Lemma nested_field0_offset2_in_range: forall (t : type) (gfs : list gfield),
  legal_nested_field0 t gfs ->
  legal_cosu_type t = true ->
  0 <= nested_field_offset2 t gfs <= sizeof cenv_cs t.
Proof.
  intros.
  destruct gfs as [| gf gfs]; rewrite nested_field0_offset2_ind by auto.
  + pose proof sizeof_pos cenv_cs t; omega.
  + pose proof gfield0_offset_in_range (nested_field_type2 t gfs) gf (proj2 H).
    spec H1; [apply nested_field_type2_nest_pred; auto |].
    pose proof nested_field_offset2_in_range t gfs.
    spec H2; [destruct H; auto |].
    spec H2; [auto |].
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
Defined.

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

Lemma size_1_compatible: forall t, sizeof cenv_cs t = 1 -> forall p, size_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  destruct (Int.unsigned_range i).
  omega.
Qed.

Lemma size_0_compatible: forall t, sizeof cenv_cs t = 0 -> forall p, size_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  destruct (Int.unsigned_range i).
  omega.
Qed.

Lemma align_1_compatible: forall t, alignof cenv_cs t = 1 -> forall p, align_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  apply Z.divide_1_l.
Qed.

Lemma size_compatible_nested_field: forall t gfs p,
  legal_nested_field t gfs ->
  legal_cosu_type t = true ->
  size_compatible t p ->
  size_compatible (nested_field_type2 t gfs) (offset_val (Int.repr (nested_field_offset2 t gfs)) p).
Proof.
  intros.
  destruct p; simpl; try tauto.
  unfold size_compatible in H1.
  solve_mod_modulus.
  inv_int i.
  pose proof nested_field_offset2_in_range t gfs H H0.
  pose proof Zmod_le (ofs + nested_field_offset2 t gfs) (Int.modulus).
  spec H4; [pose proof Int.modulus_pos; omega |].
  spec H4; [omega |].
  pose proof nested_field_offset2_in_range t gfs.
  omega.
Qed.

Lemma size_compatible_nested_field_array: forall t gfs lo hi p,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  legal_nested_field0 t (ArraySubsc hi :: gfs) ->
  legal_cosu_type t = true ->
  size_compatible t p ->
  size_compatible (nested_field_array_type t gfs lo hi)
   (offset_val (Int.repr (nested_field_offset2 t (ArraySubsc lo :: gfs))) p).
Proof.
  intros.
  destruct p; simpl; try tauto.
  unfold size_compatible in H2.
  solve_mod_modulus.
  inv_int i.
  pose proof nested_field_array_offset2_in_range t gfs lo hi H H0 H1.
  pose proof Zmod_le (ofs + nested_field_offset2 t (ArraySubsc lo :: gfs)) (Int.modulus).
  spec H5; [pose proof Int.modulus_pos; omega |].
  spec H5; [omega |].
  pose proof nested_field_offset2_in_range t gfs (proj1 H) H1.
  simpl in H3.
  omega.
Qed.

Lemma align_compatible_nested_field: forall t gfs p,
  legal_nested_field t gfs ->
  legal_alignas_type t = true ->
  align_compatible t p ->
  align_compatible (nested_field_type2 t gfs) (offset_val (Int.repr (nested_field_offset2 t gfs)) p).
Proof.
  intros.
  destruct p; simpl in *; try tauto.
  unfold Int.unsigned; simpl. 
  unfold Int.unsigned; simpl.
  repeat rewrite Int.Z_mod_modulus_eq.
  rewrite Zplus_mod_idemp_r.
  assert (alignof cenv_cs (nested_field_type2 t gfs) | Int.unsigned i + nested_field_offset2 t gfs).
  - apply Z.divide_add_r; auto.
    eapply Z.divide_trans; [| eauto].
    apply alignof_nested_field_type2_divide_alignof; auto.
    apply nested_field_offset2_type2_divide; auto.
  - unfold Int.modulus.
    destruct (alignof_two_p cenv_cs (nested_field_type2 t gfs)).
    rewrite H3 in *.
    destruct H2.
    unfold Int.unsigned in H2; rewrite H2.
    rewrite !two_power_nat_two_p in *.
    apply multiple_divide_mod.
    * apply two_p_gt_ZERO, Zle_0_nat.
    * rewrite <- !two_power_nat_two_p in *. apply power_nat_one_divede_other.
Qed.

Lemma align_compatible_nested_field_array: forall t gfs lo hi p,
  legal_nested_field0 t (ArraySubsc lo :: gfs) ->
  legal_nested_field0 t (ArraySubsc hi :: gfs) ->
  legal_alignas_type t = true ->
  align_compatible t p ->
  align_compatible (nested_field_array_type t gfs lo hi)
   (offset_val (Int.repr (nested_field_offset2 t (ArraySubsc lo :: gfs))) p).
Proof.
  intros.
  destruct p; simpl in *; try tauto.
  inv_int i.
  solve_mod_modulus.
  apply arith_aux04.
  + admit.
  + apply Z.divide_add_r; auto.
admit. admit.
(*
    eapply Z.divide_trans; [| eauto].
    apply alignof_nested_field_type2_divide_alignof; auto.
    apply nested_field_offset2_type2_divide; auto.
*)
Qed.

Lemma field_compatible_nested_field: forall t gfs p,
  field_compatible t gfs p ->
  field_compatible (nested_field_type2 t gfs) nil (offset_val (Int.repr (nested_field_offset2 t gfs)) p).
Proof.
  intros.
  unfold field_compatible in *.
  repeat split.
  + rewrite isptr_offset_val; tauto.
  + apply nested_field_type2_nest_pred; auto. tauto.
  + apply nested_field_type2_nest_pred; auto. tauto.
  + apply nested_field_type2_complete_type; tauto.
  + pose proof nested_field_offset2_in_range t gfs.
    spec H0; [tauto |].
    spec H0; [tauto |].
    omega.
  + apply size_compatible_nested_field; tauto.
  + apply align_compatible_nested_field; tauto.
Qed.

Lemma field_compatible0_nested_field_array: forall t gfs lo hi p,
  field_compatible0 t (ArraySubsc lo :: gfs) p ->
  field_compatible0 t (ArraySubsc hi :: gfs) p ->
  field_compatible (nested_field_array_type t gfs lo hi) nil (offset_val (Int.repr (nested_field_offset2 t (ArraySubsc lo :: gfs))) p).
Proof.
  intros.
  unfold field_compatible, field_compatible0 in *.
  repeat split.
  + rewrite isptr_offset_val; tauto.
  + apply nested_field_array_type_nest_pred; try  tauto.
      admit.  (* Qinxiang  ? *)
  + apply nested_field_array_type_nest_pred; tauto.
  + apply nested_field_array_type_complete_type; tauto.
  + pose proof nested_field_array_offset2_in_range t gfs lo hi.
    spec H1; [tauto |].
    spec H1; [tauto |].
    spec H1; [tauto |].
    omega.
  + apply size_compatible_nested_field_array; tauto.
  + apply align_compatible_nested_field_array; tauto.
Qed.

Lemma field_compatible_isptr :
  forall t path p, field_compatible t path p -> isptr p.
Proof.
intros. destruct H; auto.
Qed.

Lemma field_compatible0_isptr :
  forall t path p, field_compatible0 t path p -> isptr p.
Proof.
intros. destruct H; auto.
Qed.

End COMPOSITE_ENV.
(*
Arguments nested_field_offset2 {cs} t gfs /.
Arguments nested_field_type2 {cs} t gfs /.
*)

(* Hint Resolve field_address_isptr. *)
Hint Resolve is_pointer_or_null_field_compatible.
Hint Extern 1 (isptr _) => (eapply field_compatible_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_isptr; eassumption).

Lemma lvar_size_compatible:
  forall  {cs: compspecs} id t v rho,
  lvar id t v rho -> size_compatible t v.
Proof.
intros. hnf in H. 
destruct (Map.get (ve_of rho) id); try contradiction.
destruct p.
if_tac in H; try contradiction.
destruct H; auto.
Qed.

Lemma lvar_field_compatible:
   forall {cs: compspecs} id t v rho,
    lvar id t v rho ->
    legal_alignas_type t = true ->
    legal_cosu_type t = true ->
    complete_type cenv_cs t = true ->
    sizeof cenv_cs t < Int.modulus ->
 field_compatible t nil v.
Proof.
intros.
pose proof (lvar_size_compatible _ _ _ _ H).
hnf in H.
destruct (Map.get (ve_of rho) id); try contradiction.
destruct p.
if_tac in H; try contradiction.
destruct H.
repeat split; auto.
subst; apply I.
subst; hnf. exists 0. rewrite Z.mul_0_l.
reflexivity.
Qed.



