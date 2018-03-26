Require Import VST.floyd.base.
Require Import VST.floyd.sublist.

Lemma is_int_dec i s v: {is_int i s v} + {~ is_int i s v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial].
destruct i.
+ destruct s.
    * destruct (zle Byte.min_signed (Int.signed i0)); [| right; omega].
      destruct (zle (Int.signed i0) Byte.max_signed). left; omega. right; omega.
    * destruct (zle (Int.unsigned i0) Byte.max_unsigned). left; omega. right; omega.
+ destruct s.
    * destruct (zle (-32768) (Int.signed i0)); [| right; omega].
      destruct (zle (Int.signed i0) 32767). left; omega. right; omega.
    * destruct (zle (Int.unsigned i0) 65535). left; omega. right; omega.
+ left; trivial.
+ destruct (Int.eq_dec i0 Int.zero); subst. left; left; trivial.
    destruct (Int.eq_dec i0 Int.one); subst. left; right; trivial.
    right. intros N; destruct N; contradiction.
Defined.

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
  apply Int.eq_dec. 
Defined.

Lemma isptr_dec v: {isptr v} + {~ isptr v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial]; left; trivial. Defined.

Lemma tc_val_dec t v: {tc_val t v} + {~ tc_val t v}.
Proof. destruct t; simpl.
+ right; intros N; trivial.
+ apply is_int_dec.
+ apply is_long_dec.
+ destruct f. apply is_single_dec. apply is_float_dec.
+ destruct ((eqb_type t Tvoid &&
    eqb_attr a
      {| attr_volatile := false; attr_alignas := Some log2_sizeof_pointer |})%bool).
  apply is_pointer_or_integer_dec.
  apply is_pointer_or_null_dec.
+ apply is_pointer_or_null_dec.
+ apply is_pointer_or_null_dec.
+ apply isptr_dec.
+ apply isptr_dec.
Defined.

Lemma isptr_offset_val':
 forall i p, isptr p -> isptr (offset_val i p).
Proof. intros. destruct p; try contradiction; apply Coq.Init.Logic.I. Qed.
Hint Extern 1 (isptr (offset_val _ _)) => apply isptr_offset_val'.
Hint Resolve isptr_offset_val': norm.

Lemma offset_val_force_ptr:
  offset_val 0 = force_ptr.
Proof. extensionality v. destruct v; try reflexivity.
simpl. rewrite Ptrofs.add_zero; auto.
Qed.
Hint Rewrite <- offset_val_force_ptr : norm.

Lemma sem_add_pi_ptr:
   forall {cs: compspecs}  t p i si,
    isptr p ->
    match si with
    | Signed => Int.min_signed <= i <= Int.max_signed
    | Unsigned => 0 <= i <= Int.max_unsigned
    end ->
    Cop.sem_add_ptr_int cenv_cs t si p (Vint (Int.repr i)) = Some (offset_val (sizeof t * i) p).
Proof.
  intros. destruct p; try contradiction.
  unfold offset_val, Cop.sem_add_ptr_int.
  unfold Cop.ptrofs_of_int, Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int.
  f_equal. f_equal. f_equal.
  destruct si; rewrite <- ptrofs_mul_repr;  f_equal.
  rewrite Int.signed_repr by omega; auto.
  rewrite Int.unsigned_repr by omega; auto.
Qed.
Hint Rewrite @sem_add_pi_ptr using (solve [auto with norm]) : norm.

Lemma sem_cast_i2i_correct_range: forall sz s v,
  is_int sz s v -> sem_cast_i2i sz s v = Some v.
Proof.
  intros.
  destruct sz, s, v; try solve [inversion H]; simpl;
  f_equal; f_equal; try apply sign_ext_inrange; try apply zero_ext_inrange; eauto.
  + simpl in H; destruct H; subst; reflexivity.
  + simpl in H; destruct H; subst; reflexivity.
Qed.
Hint Rewrite sem_cast_i2i_correct_range using (solve [auto with norm]) : norm.

Lemma force_val_e:
 forall v, force_val (Some v) = v.
Proof. reflexivity. Qed.
Hint Rewrite force_val_e: norm.

Lemma sem_cast_neutral_ptr:
  forall p, isptr p -> sem_cast_pointer p = Some p.
Proof. intros. destruct p; try contradiction; reflexivity. Qed.
Hint Rewrite sem_cast_neutral_ptr using (solve [auto with norm]): norm.

Lemma sem_cast_neutral_Vint: forall v,
  sem_cast_pointer (Vint v) = Some (Vint v).
Proof.
  intros. reflexivity.
Qed.
Hint Rewrite sem_cast_neutral_Vint : norm.

Definition isVint v := match v with Vint _ => True | _ => False end.

Lemma is_int_is_Vint: forall i s v, is_int i s v -> isVint v.
Proof. intros.
 destruct i,s,v; simpl; intros; auto.
Qed.

Lemma is_int_I32_Vint: forall s v, is_int I32 s (Vint v).
Proof.
intros.
hnf. auto.
Qed.
Hint Resolve is_int_I32_Vint.

Lemma sem_cast_neutral_int: forall v,
  isVint v ->
  sem_cast_pointer v = Some v.
Proof.
destruct v; simpl; intros; try contradiction; auto.
Qed.

Hint Rewrite sem_cast_neutral_int using
  (auto;
   match goal with H: is_int ?i ?s ?v |- isVint ?v => apply (is_int_is_Vint i s v H) end) : norm.

Lemma sizeof_tuchar: forall {cs: compspecs}, sizeof tuchar = 1%Z.
Proof. reflexivity. Qed.
Hint Rewrite @sizeof_tuchar: norm.

Hint Rewrite Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r : norm.

Hint Rewrite eval_id_same : norm.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.
Hint Rewrite Int.sub_idem Int.sub_zero_l  Int.add_neg_zero : norm.
Hint Rewrite Ptrofs.sub_idem Ptrofs.sub_zero_l  Ptrofs.add_neg_zero : norm.

Lemma eval_expr_Etempvar:
  forall {cs: compspecs}  i t, eval_expr (Etempvar i t) = eval_id i.
Proof. reflexivity.
Qed.
Hint Rewrite @eval_expr_Etempvar : eval.

Lemma eval_expr_binop: forall {cs: compspecs}  op a1 a2 t, eval_expr (Ebinop op a1 a2 t) =
          `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2).
Proof. reflexivity. Qed.
Hint Rewrite @eval_expr_binop : eval.

Lemma eval_expr_unop: forall {cs: compspecs} op a1 t, eval_expr (Eunop op a1 t) =
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
Hint Rewrite @eval_expr_unop : eval.

Hint Resolve  eval_expr_Etempvar.

Lemma eval_expr_Etempvar' : forall {cs: compspecs}  i t, eval_id i = eval_expr (Etempvar i t).
Proof. intros. symmetry; auto.
Qed.
Hint Resolve  @eval_expr_Etempvar'.

Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : norm.
Hint Rewrite Ptrofs.add_zero  Ptrofs.add_zero_l Ptrofs.sub_zero_l : norm.

Lemma eval_var_env_set:
  forall i t j v (rho: environ), eval_var i t (env_set rho j v) = eval_var i t rho.
Proof. reflexivity. Qed.
Hint Rewrite eval_var_env_set : norm.

Lemma eval_expropt_Some: forall {cs: compspecs}  e, eval_expropt (Some e) = `Some (eval_expr e).
Proof. reflexivity. Qed.
Lemma eval_expropt_None: forall  {cs: compspecs} , eval_expropt None = `None.
Proof. reflexivity. Qed.
Hint Rewrite @eval_expropt_Some @eval_expropt_None : eval.

Lemma offset_offset_val:
  forall v i j, offset_val j (offset_val i v) = offset_val (i + j) v.
Proof. intros; unfold offset_val.
 destruct v; auto.
 f_equal. rewrite Ptrofs.add_assoc. f_equal. apply ptrofs_add_repr.
Qed.
Hint Rewrite offset_offset_val: norm.

Hint Rewrite add_repr add64_repr ptrofs_add_repr : norm.
Hint Rewrite mul_repr mul64_repr ptrofs_mul_repr : norm.
Hint Rewrite sub_repr sub64_repr ptrofs_sub_repr : norm.
Hint Rewrite and_repr and64_repr : norm.
Hint Rewrite or_repr or64_repr : norm.
Hint Rewrite neg_repr neg64_repr : norm.

Lemma ltu_repr: forall i j,
 (0 <= i <= Int.max_unsigned ->
  0 <= j <= Int.max_unsigned ->
  Int.ltu (Int.repr i) (Int.repr j) = true -> i<j)%Z.
Proof.
intros. unfold Int.ltu in H1. if_tac in H1; inv H1.
repeat rewrite Int.unsigned_repr in H2 by assumption.
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

Lemma int_add_assoc1:
  forall z i j, Int.add (Int.add z (Int.repr i)) (Int.repr j) = Int.add z (Int.repr (i+j)).
Proof.
intros.
rewrite Int.add_assoc. f_equal. apply add_repr.
Qed.
Hint Rewrite int_add_assoc1 : norm.

Lemma ptrofs_add_assoc1:
  forall z i j, Ptrofs.add (Ptrofs.add z (Ptrofs.repr i)) (Ptrofs.repr j) = Ptrofs.add z (Ptrofs.repr (i+j)).
Proof.
intros.
rewrite Ptrofs.add_assoc. f_equal. apply ptrofs_add_repr.
Qed.
Hint Rewrite ptrofs_add_assoc1 : norm.

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

Lemma deref_noload_tarray:
  forall ty n, deref_noload (tarray ty n) = (fun v => v).
Proof.
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_tarray : norm.

Lemma deref_noload_Tarray:
  forall ty n a, deref_noload (Tarray ty n a) = (fun v => v).
Proof.
 intros. extensionality v. reflexivity.
Qed.
Hint Rewrite deref_noload_Tarray : norm.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 =>  Archi.ptr64 = false /\ Int.cmpu Ceq n1 n2 = true  /\ Int.cmpu Ceq n1 (Int.repr 0) = true
      | Vlong n1, Vlong n2 =>  Archi.ptr64 = true /\ Int64.cmpu Ceq n1 n2 = true  /\ Int64.cmpu Ceq n1 (Int64.repr 0) = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Ptrofs.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

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
(* Hint Rewrite ptr_eq_True' using solve[auto] : norm. *)

Lemma ptr_eq_True:
   forall p, is_pointer_or_null p -> ptr_eq p p = True.
Proof. intros.
 apply prop_ext; intuition. destruct p; inv H; simpl; auto.
 rewrite Ptrofs.eq_true. auto.
Qed.
Hint Rewrite ptr_eq_True using solve[auto] : norm.

Lemma ptr_eq_is_pointer_or_null: forall x y, ptr_eq x y -> is_pointer_or_null x.
Proof.
  intros.
  unfold ptr_eq, is_pointer_or_null in *.
  destruct x; destruct y; try tauto;
  destruct H as [Hp [_ ?]]; rewrite Hp.
  unfold Int.cmpu in H.
  exact (binop_lemmas2.int_eq_true _ _ (eq_sym H)).
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

Lemma flip_lifted_eq:
  forall (v1: environ -> val) (v2: val),
    `eq v1 `v2 = `(eq v2) v1.
Proof.
intros. unfold_lift. extensionality rho. apply prop_ext; split; intro; auto.
Qed.
Hint Rewrite flip_lifted_eq : norm.

Lemma isptr_is_pointer_or_null:
  forall v, isptr v -> is_pointer_or_null v.
Proof. intros. destruct v; inv H; simpl; auto.
Qed.
Hint Resolve isptr_is_pointer_or_null.

Definition repable_signed (z: Z) :=
  Int.min_signed <= z <= Int.max_signed.

Definition repable_signed_dec (z: Z) : {repable_signed z}+{~repable_signed z}.
Proof.
 intros. unfold repable_signed.
 destruct (zlt z Int.min_signed).
 right; intros [? _]; unfold Int.min_signed; omega.
 destruct (zlt Int.max_signed z).
 right; intros [_ ?]; unfold Int.max_signed; omega.
 left; split; omega.
Defined.


Definition add_ptr_int  {cs: compspecs}  (ty: type) (v: val) (i: Z) : val :=
           eval_binop Cop.Oadd (tptr ty) tint v (Vint (Int.repr i)).

Lemma repable_signed_mult2:
  forall i j, i<>0 -> (j <= Int.max_signed \/ i <> -1) ->
   repable_signed (i*j) -> repable_signed j.
Proof.
intros until 1. intro HACK. intros.
assert (MAX: 0 < Int.max_signed) by (compute; auto).
assert (MIN: Int.min_signed < 0) by (compute; auto).
hnf in H0|-*.
assert (0 < i \/ i < 0) by omega; clear H.
destruct H1.
replace i with ((i-1)+1) in H0 by omega.
rewrite Z.mul_add_distr_r in H0.
rewrite Z.mul_1_l in H0.
assert (j < 0 \/ 0 <= j) by omega. destruct H1.
assert ((i-1)*j <= 0) by (apply Z.mul_nonneg_nonpos; omega).
omega.
assert (0 <= (i-1)*j) by (apply Z.mul_nonneg_nonneg; omega).
omega.
replace i with ((i+1)-1) in H0 by omega.
rewrite Z.mul_sub_distr_r in H0.
rewrite Z.mul_1_l in H0.
assert (MINMAX: Int.min_signed = -Int.max_signed - 1) by reflexivity.
assert (j < 0 \/ 0 <= j) by omega. destruct H1.
assert (0 <= (i+1)*j) by (apply Z.mul_nonpos_nonpos; omega).
rewrite MINMAX in H0|-*.
omega.
assert ((i+1)*j <= 0) by (apply Z.mul_nonpos_nonneg; omega).
rewrite MINMAX in H0|-*.
split; try omega.
clear MIN MINMAX.
destruct H0 as [? _].
assert (- Int.max_signed <= 1 + (i+1)*j - j) by omega; clear H0.
assert (-1 - (i + 1) * j + j <= Int.max_signed) by omega; clear H3.
destruct HACK; auto.
assert (i < -1) by omega.
destruct (zlt 0 j); try omega.
assert ((i+1)*j < 0).
rewrite Z.mul_add_distr_r.
replace i with ((i+1)-1) by omega.
rewrite Z.mul_sub_distr_r.
assert ((i+1)*j<0); [ | omega].
apply Z.mul_neg_pos; auto. omega.
omega.
Qed.

Lemma repable_signed_mult1:
  forall i j, j<>0 ->  (i <= Int.max_signed \/ j <> -1) ->
              repable_signed (i*j) -> repable_signed i.
Proof.
intros.
 rewrite Zmult_comm in H1.
 apply repable_signed_mult2 in H0; auto.
Qed.

Lemma add_ptr_int_offset:
  forall  {cs: compspecs}  t v n,
  repable_signed (sizeof t) ->
  repable_signed n ->
  add_ptr_int t v n = offset_val (sizeof t * n) v.
Abort. (* broken in CompCert 2.7 *)

Lemma typed_false_cmp:
  forall op i j ,
   typed_false tint (force_val (sem_cmp op tint tint (Vint i) (Vint j))) ->
   Int.cmp (negate_comparison op) i j = true.
Proof.
intros.
unfold sem_cmp in H.
unfold Cop.classify_cmp in H. simpl in H.
rewrite Int.negate_cmp.
unfold both_int, force_val, typed_false, strict_bool_val, sem_cast, classify_cast, tint in H.
destruct Archi.ptr64 eqn:Hp; simpl in H.
destruct (Int.cmp op i j); inv H; auto.
rewrite Hp in H.
destruct (Int.cmp op i j); inv H; auto.
Qed.

Lemma typed_true_cmp:
  forall op i j,
   typed_true tint (force_val (sem_cmp op tint tint (Vint i) (Vint j))) ->
   Int.cmp op i j = true.
Proof.
intros.
unfold sem_cmp in H.
unfold Cop.classify_cmp in H. simpl in H.
unfold both_int, force_val, typed_false, strict_bool_val, sem_cast, classify_cast, tint in H.
destruct Archi.ptr64 eqn:Hp; simpl in H.
destruct (Int.cmp op i j); inv H; auto.
rewrite Hp in H.
destruct (Int.cmp op i j); inv H; auto.
Qed.

Definition Zcmp (op: comparison) : Z -> Z -> Prop :=
 match op with
 | Ceq => eq
 | Cne => (fun i j => i<>j)
 | Clt => Zlt
 | Cle => Zle
 | Cgt => Zgt
 | Cge => Zge
 end.

Lemma int_cmp_repr:
 forall op i j, repable_signed i -> repable_signed j ->
   Int.cmp op (Int.repr i) (Int.repr j) = true ->
   Zcmp op i j.
Proof.
intros.
unfold Int.cmp, Int.eq, Int.lt in H1.
replace (if zeq (Int.unsigned (Int.repr i)) (Int.unsigned (Int.repr j))
             then true else false)
 with (if zeq i j then true else false) in H1.
Focus 2.
destruct (zeq i j); destruct (zeq (Int.unsigned (Int.repr i)) (Int.unsigned (Int.repr j)));
 auto.
subst. contradiction n; auto.
clear - H H0 e n.
apply Int.signed_repr in H. rewrite Int.signed_repr_eq in H.
apply Int.signed_repr in H0; rewrite Int.signed_repr_eq in H0.
contradiction n; clear n.
repeat rewrite Int.unsigned_repr_eq in e.
 match type of H with
           | context [if ?a then _ else _] => destruct a
           end;
 match type of H0 with
           | context [if ?a then _ else _] => destruct a
           end; omega.
unfold Zcmp.
rewrite (Int.signed_repr _ H) in H1; rewrite (Int.signed_repr _ H0) in H1.
repeat match type of H1 with
           | context [if ?a then _ else _] => destruct a
           end; try omegaContradiction;
 destruct op; auto; simpl in *; try discriminate; omega.
Qed.


Lemma typed_false_cmp_repr:
  forall op i j,
   repable_signed i -> repable_signed j ->
   typed_false tint (force_val (sem_cmp op tint tint
                              (Vint (Int.repr i))
                              (Vint (Int.repr j)) )) ->
   Zcmp (negate_comparison op) i j.
Proof.
 intros.
 apply typed_false_cmp in H1.
 apply int_cmp_repr; auto.
Qed.

Lemma typed_true_cmp_repr:
  forall op i j,
   repable_signed i -> repable_signed j ->
   typed_true tint (force_val (sem_cmp op tint tint
                              (Vint (Int.repr i))
                              (Vint (Int.repr j)) )) ->
   Zcmp op i j.
Proof.
 intros.
 apply typed_true_cmp in H1.
 apply int_cmp_repr; auto.
Qed.

Ltac intcompare H :=
 (apply typed_false_cmp_repr in H || apply typed_true_cmp_repr in H);
   [ simpl in H | auto; unfold repable_signed, Int.min_signed, Int.max_signed in *; omega .. ].


Lemma isptr_deref_noload:
 forall t p, access_mode t = By_reference -> isptr (deref_noload t p) = isptr p.
Proof.
intros.
unfold deref_noload. rewrite H. reflexivity.
Qed.
Hint Rewrite isptr_deref_noload using reflexivity : norm.

Lemma isptr_offset_val_zero:
  forall v, isptr v -> offset_val 0 v = v.
Proof. intros. destruct v; inv H; subst; simpl.  rewrite Ptrofs.add_zero; reflexivity.
Qed.

Hint Rewrite isptr_offset_val_zero using solve [auto] : norm.

Lemma isptr_offset_val:
 forall i p, isptr (offset_val i p) = isptr p.
Proof.
intros.
unfold isptr.
destruct p; simpl; auto.
Qed.
Hint Rewrite isptr_offset_val : norm.

Lemma isptr_force_ptr: forall v, isptr v -> force_ptr v = v.
Proof. intros. destruct v; inv H; auto. Qed.
Hint Rewrite isptr_force_ptr using solve [auto] : norm.

Lemma isptr_force_ptr' : forall p, isptr (force_ptr p) =  isptr p.
Proof.
intros. destruct p; reflexivity.
Qed.
Hint Rewrite isptr_force_ptr' : norm.

Ltac no_evars P := (has_evar P; fail 1) || idtac.

Ltac putable x :=
 match x with
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
 | Zmod ?x ?y => putable x; putable y
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
 | Ceq => idtac
 | Cne => idtac
 | Clt => idtac
 | Cle => idtac
 | Cgt => idtac
 | Cge => idtac
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
end.

Ltac computable := match goal with |- ?x =>
 no_evars x;
 putable x;
 compute; clear; repeat split; auto; congruence
end.

Lemma sign_ext_range2:
   forall lo n i hi,
      0 < n < Int.zwordsize ->
      lo = - two_p (n-1) ->
      hi = two_p (n-1) - 1 ->
      lo <= Int.signed (Int.sign_ext n i) <= hi.
Proof.
intros.
subst. apply expr_lemmas3.sign_ext_range'; auto.
Qed.

Lemma zero_ext_range2:
  forall n i lo hi,
      0 <= n < Int.zwordsize ->
      lo = 0 ->
      hi = two_p n - 1 ->
      lo <= Int.unsigned (Int.zero_ext n i) <= hi.
Proof.
intros; subst; apply expr_lemmas3.zero_ext_range'; auto.
Qed.

Hint Extern 3 (_ <= Int.signed (Int.sign_ext _ _) <= _) =>
    (apply sign_ext_range2; [computable | reflexivity | reflexivity]).

Hint Extern 3 (_ <= Int.unsigned (Int.zero_ext _ _) <= _) =>
    (apply zero_ext_range2; [computable | reflexivity | reflexivity]).

Hint Rewrite sign_ext_inrange using assumption : norm.
Hint Rewrite zero_ext_inrange using assumption : norm.

Lemma force_signed_int_e:
  forall i, force_signed_int (Vint i) = Int.signed i.
Proof. reflexivity. Qed.
Hint Rewrite force_signed_int_e : norm.

Definition headptr (v: val): Prop :=
  exists b,  v = Vptr b Ptrofs.zero.

Lemma headptr_isptr: forall v,
  headptr v -> isptr v.
Proof.
  intros.
  destruct H as [b ?].
  subst.
  hnf; auto.
Qed.
Hint Resolve headptr_isptr.

Lemma headptr_offset_zero: forall v,
  headptr (offset_val 0 v) <->
  headptr v.
Proof.
  split; intros.
  + destruct H as [b ?]; subst.
    destruct v; try solve [inv H].
    simpl in H.
    remember (Ptrofs.add i (Ptrofs.repr 0)).
    inversion H; subst.
    rewrite Ptrofs.add_zero in H2; subst.
    hnf; eauto.
  + destruct H as [b ?]; subst.
    exists b.
    reflexivity.
Qed.

(* Equality proofs for all constants from the Compcert Int, Int64, Ptrofs modules: *)

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
                  change X with z in *
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

Ltac pose_lemma F F' A L :=
  match type of (L A) with ?T =>
     lazymatch goal with
      | H:  T |- _ => idtac
      | H:  T /\ _ |- _ => idtac
      | |- _ => pose proof (L A)
     end;  change (F A) with (F' A) in *
  end.

Ltac pose_lemmas F F' L :=
 repeat
  match goal with
  | |- context [F ?A] => pose_lemma F F' A L
  | H: context [F ?A] |- _ => pose_lemma F F' A L
(*  | H:= context [F ?A] |- _ => pose_lemma F F' A L *)
 end;
  unfold F' in *.

Definition byte_unsigned' := Byte.unsigned.
Definition byte_signed' := Byte.signed.
Definition int_unsigned' := Int.unsigned.
Definition int_signed' := Int.signed.
Definition int64_unsigned' := Int64.unsigned.
Definition int64_signed' := Int64.signed.
Definition ptrofs_unsigned' := Ptrofs.unsigned.

Ltac rep_omega_setup := 
 repeat match goal with
            |  x:= _ : Z |- _ => subst x
            |  x:= _ : nat |- _ => subst x
            |  x:= _ |- _ => clearbody x
            end;
  try autorewrite with rep_omega in *;
  unfold repable_signed in *;
  pose_Zlength_nonneg;
  pose_lemmas Byte.unsigned byte_unsigned' Byte.unsigned_range;
  pose_lemmas Byte.signed byte_signed' Byte.signed_range;
  pose_lemmas Int.unsigned int_unsigned' Int.unsigned_range;
  pose_lemmas Int.signed int_signed' Int.signed_range;
  pose_lemmas Int64.unsigned int64_unsigned' Int64.unsigned_range;
  pose_lemmas Int64.signed int64_unsigned' Int64.signed_range;
  pose_lemmas Ptrofs.unsigned ptrofs_unsigned' Ptrofs.unsigned_range;
  pose_standard_const_equations.

Ltac rep_omega2 := 
 repeat  match goal with
  | |- _ /\ _ => match goal with
                        | |- context [Z.of_nat] => split
                        | |- context [Z.to_nat] => split
                        end
            end;
  match goal with
  | |- (_ >= _)%nat => apply <- Nat2Z.inj_ge
  | |- (_ > _)%nat => apply <- Nat2Z.inj_gt
  | |- (_ <= _)%nat => apply <- Nat2Z.inj_le
  | |- (_ < _)%nat => apply <- Nat2Z.inj_lt
  | |- @eq nat _ _ => apply Nat2Z.inj
  | |- _ => idtac
  end;
  repeat rewrite ?Nat2Z.id, ?Nat2Z.inj_add, ?Nat2Z.inj_mul, 
         ?Z2Nat.id, ?Nat2Z.inj_sub, ?Z2Nat.inj_sub,
         ?Z2Nat.inj_add by rep_omega2;
(*    simpl; *)
   omega.

Ltac rep_omega :=
   rep_omega_setup;
   rep_omega2.

Ltac repable_signed := 
  idtac "Warning: repable_signed is deprecated;  use rep_omega"; rep_omega.

Lemma typed_false_ptr:
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct v; try discriminate.
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H.
Qed.

Lemma typed_true_ptr:
  forall {t a v},  typed_true (Tpointer t a) v -> isptr v.
Proof.
unfold typed_true, strict_bool_val; simpl; intros.
destruct v; try discriminate.
if_tac in H; inv H. simpl. auto.
Qed.

Lemma int_cmp_repr':
 forall op i j, repable_signed i -> repable_signed j ->
   Int.cmp op (Int.repr i) (Int.repr j) = false ->
   Zcmp (negate_comparison op) i j.
Proof.
intros.
apply int_cmp_repr; auto.
rewrite Int.negate_cmp.
rewrite H1; reflexivity.
Qed.

Lemma typed_false_of_bool:
 forall x, typed_false tint (Val.of_bool x) -> (x=false).
Proof.
unfold typed_false; simpl.
unfold strict_bool_val, Val.of_bool; simpl.
destruct x; simpl; intros; [inversion H | auto].
Qed.

Lemma typed_true_of_bool:
 forall x, typed_true tint (Val.of_bool x) -> (x=true).
Proof.
unfold typed_true; simpl.
unfold strict_bool_val, Val.of_bool; simpl.
destruct x; simpl; intros; [auto | inversion H].
Qed.

Lemma typed_false_tint:
 forall v, typed_false tint v -> v=nullval.
Proof.
intros.
 hnf in H. destruct v; inv H.
 destruct (Int.eq i Int.zero) eqn:?; inv H1.
 apply int_eq_e in Heqb. subst; reflexivity.
Qed.

Lemma typed_true_tint:
 forall v, typed_true tint v -> v<>nullval.
Proof.
intros.
 hnf in H. destruct v; inv H.
 intro. unfold nullval in H.
 destruct Archi.ptr64; inv H.
 rewrite Int.eq_true in H1. inv H1.
Qed.

Lemma typed_false_tint_Vint:
  forall v, typed_false tint (Vint v) -> v = Int.zero.
Proof.
intros. apply typed_false_tint in H. apply Vint_inj in H; auto.
Qed.

Lemma typed_true_tint_Vint:
  forall v, typed_true tint (Vint v) -> v <> Int.zero.
Proof.
intros. apply typed_true_tint in H.
contradict H. subst; reflexivity.
Qed.

Ltac intro_redundant_prop :=
  (* do it in this complicated way because the proof will come out smaller *)
match goal with |- ?P -> _ =>
  ((assert P by immediate; fail 1) || fail 1) || intros _
end.

Ltac fancy_intro aggressive :=
 match goal with
 | |- ?P -> _ => match type of P with Prop => idtac end
 | |- ~ _ => idtac
 end;
 let H := fresh in
 intro H;
 try simple apply ptr_eq_e in H;
 try simple apply Vint_inj in H;
 try match type of H with
 | tc_val _ _ => unfold tc_val in H; try change (eqb_type _ _) with false in H; cbv iota in H
 end;
 match type of H with
 | ?P => clear H; (((assert (H:P) by immediate; fail 1) || fail 1) || idtac)
                (* do it in this complicated way because the proof will come out smaller *)
 | ?x = ?y => constr_eq aggressive true;
                     first [subst x | subst y
                             | is_var x; rewrite H
                             | is_var y; rewrite <- H
                             | idtac]
 | headptr ?x => let Hx1 := fresh "HP" x in
                 let Hx2 := fresh "P" x in
                   rename H into Hx1;
                   pose proof headptr_isptr _ Hx1 as Hx2
 | isptr ?x => let Hx := fresh "P" x in rename H into Hx
 | is_pointer_or_null ?x => let Hx := fresh "PN" x in rename H into Hx
 | typed_false _ _ =>
        first [simple apply typed_false_of_bool in H
               | apply typed_false_tint_Vint in H
               | apply typed_false_tint in H
               | apply typed_false_ptr in H
               | idtac ]
 | typed_true _ _ =>
        first [simple apply typed_true_of_bool in H
               | apply typed_true_tint_Vint in H
               | apply typed_true_tint in H
               | apply typed_true_ptr in H
               | idtac ]
 (* | locald_denote _ _ => hnf in H *)
 | _ => try solve [discriminate H]
 end.

Ltac fancy_intros aggressive :=
 repeat match goal with
  | |- (_ <= _ < _) -> _ => fancy_intro aggressive
  | |- (_ < _ <= _) -> _ => fancy_intro aggressive
  | |- (_ <= _ <= _) -> _ => fancy_intro aggressive
  | |- (_ < _ < _) -> _ => fancy_intro aggressive
  | |- (?A /\ ?B) -> ?C => apply (@and_ind A B C) (* For some reason "apply and_ind" doesn't work the same *)
  | |- _ -> _ => fancy_intro aggressive
  end.

Ltac fold_types :=
 fold noattr tuint tint tschar tuchar;
 repeat match goal with
 | |- context [Tpointer ?t noattr] =>
      change (Tpointer t noattr) with (tptr t)
 | |- context [Tarray ?t ?n noattr] =>
      change (Tarray t n noattr) with (tarray t n)
 end.

Ltac fold_types1 :=
  match goal with |- _ -> ?A =>
  let a := fresh "H" in set (a:=A); fold_types; subst a
  end.

