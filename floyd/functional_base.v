Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Floats.
Require Export compcert.common.Values.
Require Export VST.msl.eq_dec.
Require Export VST.msl.Coqlib2.
Require Export VST.floyd.coqlib3.
Require Export VST.zlist.sublist.
Require Export Lia.
Require Export VST.zlist.list_solver.

Definition Vubyte (c: Byte.int) : val :=
  Vint (Int.repr (Byte.unsigned c)).
Definition Vbyte (c: Byte.int) : val :=
  Vint (Int.repr (Byte.signed c)).
Ltac fold_Vbyte :=
 repeat match goal with |- context [Vint (Int.repr (Byte.signed ?c))] =>
      fold (Vbyte c)
end.
Ltac  customizable_list_solve_preprocess ::= fold_Vbyte.
#[export] Instance Inhabitant_val : Inhabitant val := Vundef.
#[export] Instance Inhabitant_int: Inhabitant int := Int.zero.
#[export] Instance Inhabitant_byte: Inhabitant byte := Byte.zero.
#[export] Instance Inhabitant_int64: Inhabitant Int64.int := Int64.zero.
#[export] Instance Inhabitant_ptrofs: Inhabitant Ptrofs.int := Ptrofs.zero.
#[export] Instance Inhabitant_float : Inhabitant float := Float.zero.
#[export] Instance Inhabitant_float32 : Inhabitant float32 := Float32.zero.

#[export] Hint Rewrite (@Znth_map _ Inhabitant_float) using Zlength_solve : Znth.
#[export] Hint Rewrite (@Znth_map _ Inhabitant_float32) using Zlength_solve : Znth.
#[export] Hint Rewrite (@Znth_map _ Inhabitant_ptrofs) using Zlength_solve : Znth.
#[export] Hint Rewrite (@Znth_map _ Inhabitant_int64) using Zlength_solve : Znth.
#[export] Hint Rewrite (@Znth_map _ Inhabitant_byte) using Zlength_solve : Znth.
#[export] Hint Rewrite (@Znth_map _ Inhabitant_int) using Zlength_solve : Znth.
#[export] Hint Rewrite (@Znth_map _ Inhabitant_val) using Zlength_solve : Znth.

Create HintDb entailer_rewrite discriminated.

Require Import VST.veric.val_lemmas.

Lemma Vlong_inj : forall x y : int64, Vlong x = Vlong y -> x = y.
Proof.
intros.
inv H. auto.
Qed.

Lemma Vint_injective i j (H: Vint i = Vint j): i=j.
Proof. inv H; trivial. Qed. 

Lemma map_Vint_injective: forall l m, map Vint l = map Vint m -> l=m.
Proof. induction l; intros.
+ destruct m; inv H; trivial.
+ destruct m; inv H. f_equal; eauto.
Qed.


Lemma cons_inv {A} (a a':A) l l': a::l = a'::l' -> a=a' /\ l=l'.
Proof. intros. inv H; eauto. Qed.

Lemma unsigned_eq_eq: forall i j, Int.unsigned i = Int.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Int.repr_unsigned i), <- (Int.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

#[export] Hint Rewrite 
   (@Znth_map val _) (@Znth_map int _) (@Znth_map byte _)
   (@Znth_map int64 _) (@Znth_map ptrofs _) (@Znth_map float _)
   (@Znth_map float32 _)
    using (auto; rewrite ?Zlength_map in *; lia) : sublist entailer_rewrite.


Lemma is_long_dec v: {is_long v} + {~ is_long v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial]; left; trivial. Defined.

Lemma is_single_dec v: {is_single v} + {~ is_single v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial]; left; trivial. Defined.

Lemma is_float_dec v: {is_float v} + {~ is_float v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial]; left; trivial. Defined.

Lemma is_pointer_or_integer_dec v: {is_pointer_or_integer v} + {~ is_pointer_or_integer v}.
Proof. 
unfold is_pointer_or_integer.
destruct Archi.ptr64 eqn:Hp;
destruct v; simpl; try solve [right; intros N; trivial]; left; trivial.
Defined.

Lemma is_pointer_or_null_dec v: {is_pointer_or_null v} + {~ is_pointer_or_null v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial]; try solve [left; trivial].
 try apply Int.eq_dec;  (* this line works for CompCert 3.3 *)
 destruct Archi.ptr64; auto; apply Int64.eq_dec.  (* this line needed for newer CompCert *)
Defined.

Lemma isptr_dec v: {isptr v} + {~ isptr v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial]; left; trivial. Defined.

Lemma isptr_offset_val':
 forall i p, isptr p -> isptr (offset_val i p).
Proof. intros. destruct p; try contradiction; apply Coq.Init.Logic.I. Qed.
#[export] Hint Extern 1 (isptr (offset_val _ _)) => apply isptr_offset_val' : core.
#[export] Hint Resolve isptr_offset_val': norm.

Lemma offset_val_force_ptr:
  offset_val 0 = force_ptr.
Proof. extensionality v. destruct v; try reflexivity.
simpl. rewrite Ptrofs.add_zero; auto.
Qed.
#[export] Hint Rewrite <- offset_val_force_ptr : norm.

Lemma offset_offset_val:
  forall v i j, offset_val j (offset_val i v) = offset_val (i + j) v.
Proof. intros; unfold offset_val.
 destruct v; auto.
 f_equal. rewrite Ptrofs.add_assoc. f_equal. apply ptrofs_add_repr.
Qed.
#[export] Hint Rewrite offset_offset_val: norm.

#[export] Hint Rewrite add_repr add64_repr ptrofs_add_repr : norm.
#[export] Hint Rewrite mul_repr mul64_repr ptrofs_mul_repr : norm.
#[export] Hint Rewrite sub_repr sub64_repr ptrofs_sub_repr : norm.
#[export] Hint Rewrite and_repr and64_repr : norm.
#[export] Hint Rewrite or_repr or64_repr : norm.
#[export] Hint Rewrite neg_repr neg64_repr : norm.

Lemma ltu_repr: forall i j,
 (0 <= i <= Int.max_unsigned ->
  0 <= j <= Int.max_unsigned ->
  Int.ltu (Int.repr i) (Int.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma ltu_repr64: forall i j,
 (0 <= i <= Int64.max_unsigned ->
  0 <= j <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr i) (Int64.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int64.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int64.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma ltu_repr_false: forall i j,
 (0 <= i <= Int.max_unsigned ->
  0 <= j <= Int.max_unsigned ->
  Int.ltu (Int.repr i) (Int.repr j) = false -> i>=j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma ltu_repr_false64: forall i j,
 (0 <= i <= Int64.max_unsigned ->
  0 <= j <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr i) (Int64.repr j) = false -> i>=j)%Z.
Proof.
intros. unfold Int64.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int64.unsigned_repr in H2 by assumption.
auto.
Qed.

Lemma ltu_inv:
 forall x y, Int.ltu x y = true -> Int.unsigned x < Int.unsigned y.
Proof.
intros.
apply Int.ltu_inv in H; destruct H; auto.
Qed.

Lemma ltu_inv64:
 forall x y, Int64.ltu x y = true -> Int64.unsigned x < Int64.unsigned y.
Proof.
intros.
apply Int64.ltu_inv in H; destruct H; auto.
Qed.

Lemma ltu_false_inv:
 forall x y, Int.ltu x y = false -> Int.unsigned x >= Int.unsigned y.
Proof.
intros.
unfold Int.ltu in H. if_tac in H; inv H; auto.
Qed.

Lemma ltu_false_inv64:
 forall x y, Int64.ltu x y = false -> Int64.unsigned x >= Int64.unsigned y.
Proof.
intros.
unfold Int64.ltu in H. if_tac in H; inv H; auto.
Qed.

Definition repable_signed (z: Z) :=
  Int.min_signed <= z <= Int.max_signed.

Lemma lt_repr:
     forall i j : Z,
       repable_signed i ->
       repable_signed j ->
       Int.lt (Int.repr i) (Int.repr j) = true -> (i < j)%Z.
Proof.
intros.
unfold Int.lt in H1. if_tac in H1; inv H1.
rewrite !Int.signed_repr in H2 by auto.
auto.
Qed.

Lemma int_add_assoc1:
  forall z i j, Int.add (Int.add z (Int.repr i)) (Int.repr j) = Int.add z (Int.repr (i+j)).
Proof.
intros.
rewrite Int.add_assoc. f_equal. apply add_repr.
Qed.
#[export] Hint Rewrite int_add_assoc1 : norm.

Lemma ptrofs_add_assoc1:
  forall z i j, Ptrofs.add (Ptrofs.add z (Ptrofs.repr i)) (Ptrofs.repr j) = Ptrofs.add z (Ptrofs.repr (i+j)).
Proof.
intros.
rewrite Ptrofs.add_assoc. f_equal. apply ptrofs_add_repr.
Qed.
#[export] Hint Rewrite ptrofs_add_assoc1 : norm.

Lemma divide_add_align: forall a b c, Z.divide b a -> a + (align c b) = align (a + c) b.
Proof.
  intros.
  pose proof zeq b 0.
  destruct H0; unfold Z.divide in H; unfold align.
  + destruct H. subst.
    repeat rewrite Zdiv_0_r.
    simpl.
    lia.
  + destruct H.
    subst.
    replace (x * b + c + b - 1) with (x * b + (c + b - 1)) by lia.
    rewrite Z_div_plus_full_l.
    rewrite Z.mul_add_distr_r.
    reflexivity.
    lia.
Qed.

Lemma force_val_e:
 forall v, force_val (Some v) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite force_val_e: norm.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 =>  Archi.ptr64 = false /\ Int.cmpu Ceq n1 n2 = true  /\ Int.cmpu Ceq n1 (Int.repr 0) = true
      | Vlong n1, Vlong n2 =>  Archi.ptr64 = true /\ Int64.cmpu Ceq n1 n2 = true  /\ Int64.cmpu Ceq n1 (Int64.repr 0) = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Ptrofs.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

Lemma ptr_eq_dec: forall v1 v2, {ptr_eq v1 v2} + {~ptr_eq v1 v2}.
Proof.
  intros; destruct v1, v2; simpl; auto.
  - destruct Archi.ptr64; [intuition discriminate|].
    destruct (Int.eq i i0) eqn: Heq; [|intuition discriminate].
    destruct (Int.eq i (Int.repr 0)); intuition discriminate.
  - destruct Archi.ptr64; [|intuition discriminate].
    destruct (Int64.eq i i0) eqn: Heq; [|intuition discriminate].
    destruct (Int64.eq i (Int64.repr 0)); intuition discriminate.
  - destruct (eq_block b b0); [|intuition discriminate].
    destruct (Ptrofs.eq i i0) eqn: Heq; intuition discriminate.
Qed.

Lemma ptr_eq_e: forall v1 v2, ptr_eq v1 v2 -> v1=v2.
Proof.
intros. destruct v1; destruct v2; simpl in H; try contradiction.
*
pose proof (Int.eq_spec i i0). destruct H as [Hp [? ?]].
rewrite H in H0. subst; auto.
*
pose proof (Int64.eq_spec i i0). destruct H as [Hp [? ?]].
rewrite H in H0. subst; auto.
*
destruct H; subst.
f_equal.
pose proof (Ptrofs.eq_spec i i0). rewrite H0 in H; auto.
Qed.

Lemma ptr_eq_True':
   forall p, isptr p -> ptr_eq p p = True.
Proof. intros.
 apply prop_ext; intuition. destruct p; inv H; simpl; auto.
 rewrite Ptrofs.eq_true. auto.
Qed.
(* #[export] Hint Rewrite ptr_eq_True' using solve[auto] : norm. *)

Lemma ptr_eq_True:
   forall p, is_pointer_or_null p -> ptr_eq p p = True.
Proof. intros.
 apply prop_ext; intuition. destruct p; inv H; simpl; auto.
 rewrite Ptrofs.eq_true. auto.
Qed.
#[export] Hint Rewrite ptr_eq_True using solve[auto] : norm.

Lemma ptr_eq_is_pointer_or_null: forall x y, ptr_eq x y -> is_pointer_or_null x.
Proof.
  intros.
  unfold ptr_eq, is_pointer_or_null in *.
  destruct x; destruct y; try tauto;
  destruct H as [Hp [_ ?]]; rewrite Hp.
  unfold Int.cmpu in H.
  pose proof (Int.eq_spec i (Int.repr 0)). rewrite H in H0. auto.
  unfold Int64.cmpu in H.
  pose proof (Int64.eq_spec i (Int64.repr 0)). rewrite H in H0. auto.
Qed.

Lemma ptr_eq_sym: forall x y, ptr_eq x y -> ptr_eq y x.
Proof.
   intros.
   pose proof ptr_eq_is_pointer_or_null _ _ H.
   apply ptr_eq_e in H.
   rewrite H in *.
   rewrite ptr_eq_True; tauto.
Qed.

Lemma ptr_eq_trans: forall x y z, ptr_eq x y -> ptr_eq y z -> ptr_eq x z.
Proof.
   intros.
   pose proof ptr_eq_is_pointer_or_null _ _ H.
   apply ptr_eq_e in H.
   apply ptr_eq_e in H0.
   subst.
   rewrite ptr_eq_True; tauto.
Qed.

Lemma isptr_offset_val_zero:
  forall v, isptr v -> offset_val 0 v = v.
Proof. intros. destruct v; inv H; subst; simpl.  rewrite Ptrofs.add_zero; reflexivity.
Qed.

#[export] Hint Rewrite isptr_offset_val_zero using solve [auto] : norm.

Lemma isptr_offset_val:
 forall i p, isptr (offset_val i p) = isptr p.
Proof.
intros.
unfold isptr.
destruct p; simpl; auto.
Qed.
#[export] Hint Rewrite isptr_offset_val : norm.

Lemma isptr_force_ptr: forall v, isptr v -> force_ptr v = v.
Proof. intros. destruct v; inv H; auto. Qed.
#[export] Hint Rewrite isptr_force_ptr using solve [auto] : norm.

Lemma isptr_force_ptr' : forall p, isptr (force_ptr p) =  isptr p.
Proof.
intros. destruct p; reflexivity.
Qed.
#[export] Hint Rewrite isptr_force_ptr' : norm.

Ltac no_evars P := (has_evar P; fail 1) || idtac.

Create HintDb computable.
Inductive computable {t:Type} (x:t) : Prop := computable_any.

Ltac putable' x :=
 lazymatch x with
 | O => idtac
 | S ?x => putable x
 | Z.lt ?x ?y => putable x; putable y
 | Z.le ?x ?y => putable x; putable y
 | Z.gt ?x ?y => putable x; putable y
 | Z.ge ?x ?y => putable x; putable y
 | eq?x ?y => putable x; putable y
 | ?x <> ?y => putable x; putable y
 | Zpos ?x => putable x
 | Zneg ?x => putable x
 | Z0 => idtac
 | xH => idtac
 | xI ?x => putable x
 | xO ?x => putable x
 | Z.add ?x ?y => putable x; putable y
 | Z.sub ?x ?y => putable x; putable y
 | Z.mul ?x ?y => putable x; putable y
 | Z.div ?x ?y => putable x; putable y
 | Z.modulo ?x ?y => putable x; putable y
 | Z.max ?x ?y => putable x; putable y
 | Z.opp ?x => putable x
 | Ceq => idtac
 | Cne => idtac
 | Clt => idtac
 | Cle => idtac
 | Cgt => idtac
 | Cge => idtac
 | ?x /\ ?y => putable x; putable y
 | two_power_nat ?x => putable x
 | Int.eq ?x ?y => putable x; putable y
 | Int64.eq ?x ?y => putable x; putable y
 | Ptrofs.eq ?x ?y => putable x; putable y
 | Int.lt ?x ?y => putable x; putable y
 | Int64.lt ?x ?y => putable x; putable y
 | Ptrofs.lt ?x ?y => putable x; putable y
 | Int.ltu ?x ?y => putable x; putable y
 | Int64.ltu ?x ?y => putable x; putable y
 | Ptrofs.ltu ?x ?y => putable x; putable y
 | Int.add ?x ?y => putable x; putable y
 | Int64.add ?x ?y => putable x; putable y
 | Ptrofs.add ?x ?y => putable x; putable y
 | Int.sub ?x ?y => putable x; putable y
 | Int64.sub ?x ?y => putable x; putable y
 | Ptrofs.sub ?x ?y => putable x; putable y
 | Int.mul ?x ?y => putable x; putable y
 | Int64.mul ?x ?y => putable x; putable y
 | Ptrofs.mul ?x ?y => putable x; putable y
 | Int.neg ?x => putable x
 | Int64.neg ?x => putable x
 | Ptrofs.neg ?x => putable x
 | Int.cmp ?op ?x ?y => putable op; putable x; putable y
 | Int64.cmp ?op ?x ?y => putable op; putable x; putable y
 | Ptrofs.cmp ?op ?x ?y => putable op; putable x; putable y
 | Int.cmpu ?op ?x ?y => putable op; putable x; putable y
 | Int64.cmpu ?op ?x ?y => putable op; putable x; putable y
 | Ptrofs.cmpu ?op ?x ?y => putable op; putable x; putable y
 | Int.repr ?x => putable x
 | Int64.repr ?x => putable x
 | Ptrofs.repr ?x => putable x
 | Int.signed ?x => putable x
 | Int64.signed ?x => putable x
 | Ptrofs.signed ?x => putable x
 | Int.unsigned ?x => putable x
 | Int64.unsigned ?x => putable x
 | Ptrofs.unsigned ?x => putable x
 | two_power_nat ?x => putable x
 | Int.max_unsigned => idtac
 | Int64.max_unsigned => idtac
 | Ptrofs.max_unsigned => idtac
 | Int.min_signed => idtac
 | Int64.min_signed => idtac
 | Ptrofs.min_signed => idtac
 | Int.max_signed => idtac
 | Int64.max_signed => idtac
 | Ptrofs.max_signed => idtac
 | Int.modulus => idtac
 | Int64.modulus => idtac
 | Ptrofs.modulus => idtac
 | Int.zwordsize => idtac
 | Int64.zwordsize => idtac
 | Ptrofs.zwordsize => idtac
 | _ => tryif (let b := eval cbv delta [x] in x in putable b) then idtac else fail
end
with putable x := 
  first [putable' x
         | tryif (try (assert (computable x) by (clear; auto 100 with computable); fail 1)) then fail else idtac ].

#[export] Hint Extern 1 (computable ?x) => (putable' x; apply computable_any) : computable.

Ltac computable := match goal with |- ?x =>
 no_evars x;
 putable x;
 compute; clear; repeat split; auto; congruence;
  (match goal with |- context [Archi.ptr64] => idtac end;
    first [change Archi.ptr64 with false | change Archi.ptr64 with true];
    compute; repeat split; auto; congruence)
end.

Lemma sign_ext_range2:
   forall lo n i hi,
      0 < n < Int.zwordsize ->
      lo = - two_p (n-1) ->
      hi = two_p (n-1) - 1 ->
      lo <= Int.signed (Int.sign_ext n i) <= hi.
Proof.
intros.
subst.
pose proof (Int.sign_ext_range n i H).
lia.
Qed.

Lemma zero_ext_range2:
  forall n i lo hi,
      0 <= n < Int.zwordsize ->
      lo = 0 ->
      hi = two_p n - 1 ->
      lo <= Int.unsigned (Int.zero_ext n i) <= hi.
Proof.
intros; subst.
pose proof (Int.zero_ext_range n i H).
lia.
Qed.

#[export] Hint Extern 3 (_ <= Int.signed (Int.sign_ext _ _) <= _) =>
    (apply sign_ext_range2; [computable | reflexivity | reflexivity]) : core.

#[export] Hint Extern 3 (_ <= Int.unsigned (Int.zero_ext _ _) <= _) =>
    (apply zero_ext_range2; [computable | reflexivity | reflexivity]) : core.

#[export] Hint Rewrite sign_ext_inrange using assumption : norm.
#[export] Hint Rewrite zero_ext_inrange using assumption : norm.

Definition repable_signed_dec (z: Z) : {repable_signed z}+{~repable_signed z}.
Proof.
 intros. unfold repable_signed.
 destruct (zlt z Int.min_signed).
 right; intros [? _]; unfold Int.min_signed; lia.
 destruct (zlt Int.max_signed z).
 right; intros [_ ?]; unfold Int.max_signed; lia.
 left; split; lia.
Defined.


Lemma repable_signed_mult2:
  forall i j, i<>0 -> (j <= Int.max_signed \/ i <> -1) ->
   repable_signed (i*j) -> repable_signed j.
Proof.
intros until 1. intro HACK. intros.
assert (MAX: 0 < Int.max_signed) by (compute; auto).
assert (MIN: Int.min_signed < 0) by (compute; auto).
hnf in H0|-*.
assert (0 < i \/ i < 0) by lia; clear H.
destruct H1.
replace i with ((i-1)+1) in H0 by lia.
rewrite Z.mul_add_distr_r in H0.
rewrite Z.mul_1_l in H0.
assert (j < 0 \/ 0 <= j) by lia. destruct H1.
assert ((i-1)*j <= 0) by (apply Z.mul_nonneg_nonpos; lia).
lia.
assert (0 <= (i-1)*j) by (apply Z.mul_nonneg_nonneg; lia).
lia.
replace i with ((i+1)-1) in H0 by lia.
rewrite Z.mul_sub_distr_r in H0.
rewrite Z.mul_1_l in H0.
assert (MINMAX: Int.min_signed = -Int.max_signed - 1) by reflexivity.
assert (j < 0 \/ 0 <= j) by lia. destruct H1.
assert (0 <= (i+1)*j) by (apply Z.mul_nonpos_nonpos; lia).
rewrite MINMAX in H0|-*.
lia.
assert ((i+1)*j <= 0) by (apply Z.mul_nonpos_nonneg; lia).
rewrite MINMAX in H0|-*.
split; try lia.
clear MIN MINMAX.
destruct H0 as [? _].
assert (- Int.max_signed <= 1 + (i+1)*j - j) by lia; clear H0.
assert (-1 - (i + 1) * j + j <= Int.max_signed) by lia; clear H3.
destruct HACK; auto.
assert (i < -1) by lia.
destruct (zlt 0 j); try lia.
assert ((i+1)*j < 0).
rewrite Z.mul_add_distr_r.
replace i with ((i+1)-1) by lia.
rewrite Z.mul_sub_distr_r.
assert ((i+1)*j<0); [ | lia].
apply Z.mul_neg_pos; auto. lia.
lia.
Qed.

Lemma repable_signed_mult1:
  forall i j, j<>0 ->  (i <= Int.max_signed \/ j <> -1) ->
              repable_signed (i*j) -> repable_signed i.
Proof.
intros.
 rewrite Zmult_comm in H1.
 apply repable_signed_mult2 in H0; auto.
Qed.


Lemma force_signed_int_e:
  forall i, force_signed_int (Vint i) = Int.signed i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite force_signed_int_e : norm.

Ltac const_equation x :=
  let y := eval compute in x
   in exact (x = y).

Ltac Zground X :=
  match X with
  | Z0 => idtac
  | Zpos ?y => Zground y
  | Zneg ?y => Zground y 
  | xH => idtac
  | xO ?y => Zground y
  | xI ?y => Zground y
 end.

Ltac natground X :=
  match X with O => idtac | S ?Y => natground Y end.

Ltac compute_Z_of_nat :=
 repeat
  match goal with
  | H: context [Z.of_nat ?n] |- _ => 
          natground n; 
          let z := constr:(Z.of_nat n) in let y := eval hnf in z 
           in change z with y in *
  | |- context [Z.of_nat ?n] => 
          natground n; 
          let z := constr:(Z.of_nat n) in let y := eval hnf in z 
           in change z with y in *
   end.

(*
Ltac pose_const_equation X :=
 match goal with
 | H: X = ?Y |- _ => Zground Y
 | _ => let z := eval compute in X in assert (X = z) by reflexivity
 end.
*)

Ltac pose_const_equation X :=
 match goal with
 | H: X = ?Y |- _ => Zground Y
 | _ => let z := eval compute in X in 
            match z with context C [Archi.ptr64] =>
                       first [
                           unify Archi.ptr64 false; let u := context C [false] in let u := eval compute in u in change X with u in *
                          |unify Archi.ptr64 true; let u := context C [true] in let u := eval compute in u in change X with u in *
                      ]
              | _ => change X with z in *
            end
 end.

Ltac perhaps_post_const_equation X :=
 lazymatch goal with 
 | H: context [X] |- _ => pose_const_equation X
(* | H:= context [X] |- _ => pose_const_equation X *)
 | |- context [X] => pose_const_equation X
 | |- _ => idtac
 end.

Ltac pose_const_equations L :=
 match L with
 | ?X :: ?Y => perhaps_post_const_equation X; pose_const_equations Y
 | nil => idtac
 end.

Import ListNotations.

Ltac pose_standard_const_equations :=
pose_const_equations
  [
  Int.zwordsize; Int.modulus; Int.half_modulus; Int.max_unsigned; Int.max_signed; Int.min_signed;
  Int64.zwordsize; Int64.modulus; Int64.half_modulus; Int64.max_unsigned; Int64.max_signed; Int64.min_signed;
  Ptrofs.zwordsize; Ptrofs.modulus; Ptrofs.half_modulus; Ptrofs.max_unsigned; Ptrofs.max_signed; Ptrofs.min_signed;
  Byte.min_signed; Byte.max_signed; Byte.max_unsigned; Byte.modulus
  ];
 pose_const_equations [Int.wordsize; Int64.wordsize; Ptrofs.wordsize].

Ltac pose_lemma F A L :=
  match type of (L A) with ?T =>
     lazymatch goal with
      | H:  T |- _ => fail
      | H:  T /\ _ |- _ => fail
      | |- _ => pose proof (L A)
     end
  end.

Ltac pose_lemmas F L :=
 repeat
  match goal with
  | |- context [F ?A] => pose_lemma F A L
  | H: context [F ?A] |- _ => pose_lemma F A L
 end.

Ltac rep_lia_setup := 
 repeat match goal with
            | x := _ : ?T |- _ => lazymatch T with Z => fail | nat => fail | _ => clearbody x end
            end;
 zify;
  try autorewrite with rep_lia in *;
  unfold repable_signed in *;
  pose_Zlength_nonneg;
  pose_lemmas Byte.unsigned Byte.unsigned_range;
  pose_lemmas Byte.signed Byte.signed_range;
  pose_lemmas Int.unsigned Int.unsigned_range;
  pose_lemmas Int.signed Int.signed_range;
  pose_lemmas Int64.unsigned Int64.unsigned_range;
  pose_lemmas Int64.signed Int64.signed_range;
  pose_lemmas Ptrofs.unsigned Ptrofs.unsigned_range;
  pose_standard_const_equations.

Ltac rep_lia_setup2 := idtac.

Ltac rep_lia :=
   rep_lia_setup;
   rep_lia_setup2;
   lia.

Ltac repable_signed := 
  idtac "Warning: repable_signed is deprecated;  use rep_lia"; rep_lia.

Lemma Vubyte_injective i j (H: Vubyte i = Vubyte j): i=j.
Proof.
  assert (B: Byte.zwordsize = 8) by reflexivity.
  assert (I: Int.zwordsize = 32) by reflexivity.
  apply Byte.same_bits_eq; intros a A.
  unfold Vubyte in H. remember (Int.repr (Byte.unsigned i)) as z.
  inv H. destruct i; destruct j. unfold Byte.testbit.
  unfold Byte.unsigned in H1. simpl in *.
  rewrite <- 2 Int.testbit_repr, H1; trivial; lia.
Qed. 

Lemma map_Vubyte_injective: forall l m, map Vubyte l = map Vubyte m -> l=m.
Proof. induction l; intros.
+ destruct m; simpl in *; inv H; trivial.
+ destruct m; [ inv H |]. rewrite 2 map_cons in H. apply cons_inv in H.
  destruct H; subst. apply Vubyte_injective in H. f_equal; eauto.
Qed.

Lemma Vbyte_injective a b (H: Vbyte a = Vbyte b): a=b.
Proof. unfold Vbyte in H. apply Vint_injective in H.
  apply Byte.same_bits_eq; intros i I.
  assert (Imin: Int.min_signed = -2147483648) by reflexivity.
  assert (Imax: Int.max_signed = 2147483647) by reflexivity.
  assert (Bmin: Byte.min_signed = -128) by reflexivity.
  assert (Bmax: Byte.max_signed = 127) by reflexivity.
  assert (Byte.signed a = Byte.signed b).
  { rewrite <- (Int.signed_repr (Byte.signed a)). 
    rewrite <- (Int.signed_repr (Byte.signed b)).
    rewrite H; trivial. specialize (Byte.signed_range b); lia.
    specialize (Byte.signed_range a); lia. }
  clear H. unfold Byte.testbit. rewrite 2 Byte.unsigned_signed. 
  unfold Byte.lt. rewrite H0. trivial. 
Qed.

Lemma Znth_map_Vbyte: forall (i : Z) (l : list byte),
  0 <= i < Zlength l -> Znth i (map Vbyte l)  = Vbyte (Znth i l).
Proof.
  intros i l.
  apply Znth_map.
Qed.
#[export] Hint Rewrite Znth_map_Vbyte using old_list_solve : norm entailer_rewrite.

Lemma Znth_map_Vubyte: forall (i : Z) (l : list byte),
  0 <= i < Zlength l -> Znth i (map Vubyte l)  = Vubyte (Znth i l).
Proof.
  intros i l.
  apply Znth_map.
Qed.
#[export] Hint Rewrite Znth_map_Vubyte using old_list_solve : norm entailer_rewrite.

Lemma repr_inj_signed:
  forall i j,
    repable_signed i -> repable_signed j -> Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.signed_repr i) by rep_lia.
rewrite <- (Int.signed_repr j) by rep_lia.
congruence.
Qed.

Lemma repr_inj_signed64:
  forall i j,
    Int64.min_signed <= i <= Int64.max_signed ->
    Int64.min_signed <= j <= Int64.max_signed ->
    Int64.repr i = Int64.repr j -> i=j.
Proof.
intros.
rewrite <- (Int64.signed_repr i) by rep_lia.
rewrite <- (Int64.signed_repr j) by rep_lia.
congruence.
Qed.

Lemma repr_inj_unsigned:
  forall i j,
    0 <= i <= Int.max_unsigned ->
    0 <= j <= Int.max_unsigned ->
    Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.unsigned_repr i) by rep_lia.
rewrite <- (Int.unsigned_repr j) by rep_lia.
congruence.
Qed.

Lemma repr_inj_unsigned64:
  forall i j,
    0 <= i <= Int64.max_unsigned ->
    0 <= j <= Int64.max_unsigned ->
    Int64.repr i = Int64.repr j -> i=j.
Proof.
intros.
rewrite <- (Int64.unsigned_repr i) by rep_lia.
rewrite <- (Int64.unsigned_repr j) by rep_lia.
congruence.
Qed.

Lemma ptrofs_repr_inj_unsigned:
  forall i j,
    0 <= i <= Ptrofs.max_unsigned ->
    0 <= j <= Ptrofs.max_unsigned ->
    Ptrofs.repr i = Ptrofs.repr j -> i=j.
Proof.
intros.
rewrite <- (Ptrofs.unsigned_repr i) by rep_lia.
rewrite <- (Ptrofs.unsigned_repr j) by rep_lia.
congruence.
Qed.

Lemma repr_inj_signed':
  forall i j,
    (* The first two premises are not needed to prove this,
     but are used to limit its applicability *)
    repable_signed i -> repable_signed j ->
    Int.repr i <> Int.repr j -> i<>j.
Proof.
intros.
congruence.
Qed.

Lemma repr_inj_unsigned':
  forall i j,
    0 <= i <= Int.max_unsigned ->
    0 <= j <= Int.max_unsigned ->
    Int.repr i <> Int.repr j -> i<>j.
Proof.
intros.
congruence.
Qed.

Lemma opaque_constant {A: Type} (N: A) : {x: A | x=N}.
Proof. exists N. reflexivity. Qed.

Ltac hint := idtac "Hints are only available when verifying C programs,
that is, when VST.floyd.proofauto has been imported.  But you have
imported only VST.floyd.functional_base, without separation logic.

In VST.floyd.functional_base the following VST tactics are available:
rep_lia, list_solve, if_tac, autorewrite with sublist, computable, ...".

Lemma lt_repr64:
     forall i j : Z,
       repable_signed i ->
       repable_signed j ->
       Int64.lt (Int64.repr i) (Int64.repr j) = true -> (i < j)%Z.
Proof.
intros.
unfold Int64.lt in H1. if_tac in H1; inv H1.
rewrite !Int64.signed_repr in H2 by rep_lia.
auto.
Qed.

Lemma lt_repr_false:
     forall i j : Z,
       repable_signed i ->
       repable_signed j ->
       Int.lt (Int.repr i) (Int.repr j) = false -> (i >= j)%Z.
Proof.
intros.
unfold Int.lt in H1. if_tac in H1; inv H1.
rewrite !Int.signed_repr in H2 by rep_lia.
auto.
Qed.

Lemma lt_repr_false64:
     forall i j : Z,
       repable_signed i ->
       repable_signed j ->
       Int64.lt (Int64.repr i) (Int64.repr j) = false -> (i >= j)%Z.
Proof.
intros.
unfold Int64.lt in H1. if_tac in H1; inv H1.
rewrite !Int64.signed_repr in H2 by rep_lia.
auto.
Qed.

Lemma lt_inv:
 forall i j,
   Int.lt i j = true -> (Int.signed i < Int.signed j)%Z.
Proof.
intros.
unfold Int.lt in H. if_tac in H; inv H. auto.
Qed.

Lemma lt_inv64:
 forall i j,
   Int64.lt i j = true -> (Int64.signed i < Int64.signed j)%Z.
Proof.
intros.
unfold Int64.lt in H. if_tac in H; inv H. auto.
Qed.

Lemma lt_false_inv:
 forall i j,
   Int.lt i j = false -> (Int.signed i >= Int.signed j)%Z.
Proof.
intros.
unfold Int.lt in H. if_tac in H; inv H. auto.
Qed.

Lemma lt_false_inv64:
 forall i j,
   Int64.lt i j = false -> (Int64.signed i >= Int64.signed j)%Z.
Proof.
intros.
unfold Int64.lt in H. if_tac in H; inv H. auto.
Qed.


#[export] Hint Extern 2 (repable_signed ?i) =>
  (putable i; split; computable) : core.

Lemma divu_repr:
 forall i j,
  0 <= i <= Int.max_unsigned ->
  0 <= j <= Int.max_unsigned ->
  Int.divu (Int.repr i) (Int.repr j) = Int.repr (i / j).
Proof.
intros.
unfold Int.divu.
rewrite !Int.unsigned_repr; auto.
Qed.

Lemma divu_repr64:
 forall i j,
  0 <= i <= Int64.max_unsigned ->
  0 <= j <= Int64.max_unsigned ->
  Int64.divu (Int64.repr i) (Int64.repr j) = Int64.repr (i / j).
Proof.
intros.
unfold Int64.divu.
rewrite !Int64.unsigned_repr; auto.
Qed.

Lemma ptrofs_divu_repr:
 forall i j,
  0 <= i <= Ptrofs.max_unsigned ->
  0 <= j <= Ptrofs.max_unsigned ->
  Ptrofs.divu (Ptrofs.repr i) (Ptrofs.repr j) = Ptrofs.repr (i / j).
Proof.
intros.
unfold Ptrofs.divu.
rewrite !Ptrofs.unsigned_repr; auto.
Qed.

#[export] Hint Rewrite divu_repr divu_repr64 ptrofs_divu_repr
          using rep_lia : norm.

