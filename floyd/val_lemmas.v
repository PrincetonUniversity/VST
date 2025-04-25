From compcert Require Export Clightdefs.
Require Export VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Export VST.veric.SeparationLogic.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.floyd.functional_base.
Import LiftNotation.

Transparent intsize_eq.

Lemma force_Vint:  forall i, force_int (Vint i) = i.
Proof.  reflexivity. Qed.
#[export] Hint Rewrite force_Vint : norm.

Lemma is_int_dec i s v: {is_int i s v} + {~ is_int i s v}.
Proof. destruct v; simpl; try solve [right; intros N; trivial].
destruct i.
+ destruct s.
    * destruct (zle Byte.min_signed (Int.signed i0)); [| right; lia].
      destruct (zle (Int.signed i0) Byte.max_signed). left; lia. right; lia.
    * destruct (zle (Int.unsigned i0) Byte.max_unsigned). left; lia. right; lia.
+ destruct s.
    * destruct (zle (-two_power_pos 15) (Int.signed i0)); [| right; lia].
      destruct (zle (Int.signed i0) (two_power_pos 15 - 1)). left; lia. right; lia.
    * destruct (zle (Int.unsigned i0) (two_power_pos 16 - 1)). left; lia. right; lia.
+ left; trivial.
+ destruct (Int.eq_dec i0 Int.zero); subst. left; left; trivial.
    destruct (Int.eq_dec i0 Int.one); subst. left; right; trivial.
    right. intros N; destruct N; contradiction.
Defined.

Lemma tc_val_dec t v: {tc_val t v} + {~ tc_val t v}.
Proof. destruct t; simpl.
+ right; intros N; trivial.
+ apply is_int_dec.
+ apply is_long_dec.
+ destruct f. apply is_single_dec. apply is_float_dec.
+ destruct ((eqb_type t Ctypes.Tvoid &&
    eqb_attr a
      {| attr_volatile := false; attr_alignas := Some log2_sizeof_pointer |} )%bool).
  apply is_pointer_or_integer_dec.
  apply is_pointer_or_null_dec.
+ apply is_pointer_or_null_dec.
+ apply is_pointer_or_null_dec.
+ apply isptr_dec.
+ apply isptr_dec.
Defined.

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
  rewrite -> Int.signed_repr by lia; auto.
  rewrite -> Int.unsigned_repr by lia; auto.
Qed.
#[export] Hint Rewrite @sem_add_pi_ptr using (solve [auto with norm]) : norm.

Lemma sem_cast_i2i_correct_range: forall sz s v,
  is_int sz s v -> sem_cast_i2i sz s v = Some v.
Proof.
  intros.
  destruct sz, s, v; try solve [inversion H]; simpl;
  f_equal; f_equal; try apply sign_ext_inrange; try apply zero_ext_inrange; eauto.
  + simpl in H; destruct H; subst; reflexivity.
  + simpl in H; destruct H; subst; reflexivity.
Qed.
#[export] Hint Rewrite sem_cast_i2i_correct_range using (solve [auto with norm]) : norm.

Lemma sem_cast_neutral_ptr:
  forall p, isptr p -> sem_cast_pointer p = Some p.
Proof. intros. destruct p; try contradiction; reflexivity. Qed.
#[export] Hint Rewrite sem_cast_neutral_ptr using (solve [auto with norm]): norm.

Lemma sem_cast_neutral_Vint: forall v,
  sem_cast_pointer (Vint v) = Some (Vint v).
Proof.
  intros. reflexivity.
Qed.
#[export] Hint Rewrite sem_cast_neutral_Vint : norm.

Definition isVint v : Prop := match v with Vint _ => True | _ => False end.

Lemma is_int_is_Vint: forall i s v, is_int i s v -> isVint v.
Proof. intros.
 destruct i,s,v; simpl; intros; auto.
Qed.

Lemma is_int_I32_Vint: forall s v, is_int I32 s (Vint v).
Proof.
intros.
hnf. auto.
Qed.
#[export] Hint Resolve is_int_I32_Vint : core.

Lemma sem_cast_neutral_int: forall v,
  isVint v ->
  sem_cast_pointer v = Some v.
Proof.
destruct v; simpl; intros; try contradiction; auto.
Qed.

#[export] Hint Rewrite sem_cast_neutral_int using
  (auto;
   match goal with H: is_int ?i ?s ?v |- isVint ?v => apply (is_int_is_Vint i s v H) end) : norm.

Lemma sizeof_tuchar: forall {cs: compspecs}, sizeof tuchar = 1%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sizeof_tuchar: norm.

#[export] Hint Rewrite Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r Z.sub_0_r : norm.

#[export] Hint Rewrite eval_id_same : norm.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.
#[export] Hint Rewrite Int.sub_idem Int.sub_zero_l  Int.add_neg_zero : norm.
#[export] Hint Rewrite Ptrofs.sub_idem Ptrofs.sub_zero_l  Ptrofs.add_neg_zero : norm.

Lemma eval_expr_Etempvar:
  forall {cs: compspecs}  i t, eval_expr (Etempvar i t) = eval_id i.
Proof. reflexivity.
Qed.
#[export] Hint Rewrite @eval_expr_Etempvar : eval.

Lemma eval_expr_binop: forall {cs: compspecs}  op a1 a2 t, eval_expr (Ebinop op a1 a2 t) =
          `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @eval_expr_binop : eval.

Lemma eval_expr_unop: forall {cs: compspecs} op a1 t, eval_expr (Eunop op a1 t) =
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @eval_expr_unop : eval.

#[export] Hint Resolve  eval_expr_Etempvar : core.

Lemma eval_expr_Etempvar' : forall {cs: compspecs}  i t, eval_id i = eval_expr (Etempvar i t).
Proof. intros. symmetry; auto.
Qed.
#[export] Hint Resolve  eval_expr_Etempvar' : core.

#[export] Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : norm.
#[export] Hint Rewrite Ptrofs.add_zero  Ptrofs.add_zero_l Ptrofs.sub_zero_l : norm.

Lemma eval_var_env_set:
  forall i t j v (rho: environ), eval_var i t (env_set rho j v) = eval_var i t rho.
Proof. reflexivity. Qed.
#[export] Hint Rewrite eval_var_env_set : norm.

Lemma eval_expropt_Some: forall {cs: compspecs}  e, eval_expropt (Some e) = `Some (eval_expr e).
Proof. reflexivity. Qed.
Lemma eval_expropt_None: forall  {cs: compspecs} , eval_expropt None = `None.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @eval_expropt_Some @eval_expropt_None : eval.

Lemma deref_noload_tarray:
  forall ty n, deref_noload (tarray ty n) = (fun v => v).
Proof.
 intros. extensionality v. reflexivity.
Qed.
#[export] Hint Rewrite deref_noload_tarray : norm.

Lemma deref_noload_Tarray:
  forall ty n a, deref_noload (Tarray ty n a) = (fun v => v).
Proof.
 intros. extensionality v. reflexivity.
Qed.
#[export] Hint Rewrite deref_noload_Tarray : norm.

Lemma flip_lifted_eq:
  forall (v1: environ -> val) (v2: val),
    `eq v1 `(v2) = `(eq v2) v1.
Proof.
intros. unfold_lift. extensionality rho. apply prop_ext; split; intro; auto.
Qed.
#[export] Hint Rewrite flip_lifted_eq : norm.

Lemma isptr_is_pointer_or_null:
  forall v, isptr v -> is_pointer_or_null v.
Proof. intros. destruct v; inv H; simpl; auto.
Qed.
#[export] Hint Resolve isptr_is_pointer_or_null : core.

Definition add_ptr_int  {cs: compspecs}  (ty: type) (v: val) (i: Z) : val :=
           eval_binop Cop.Oadd (tptr ty) tint v (Vint (Int.repr i)).

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
destruct (Int.cmp op i j); inv H; auto.
Qed.

Definition Zcmp (op: comparison) : Z -> Z -> Prop :=
 match op with
 | Ceq => eq
 | Cne => (fun i j => i<>j)
 | Clt => Z.lt
 | Cle => Z.le
 | Cgt => Z.gt
 | Cge => Z.ge
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
2:{
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
           end; lia.
}
unfold Zcmp.
rewrite (Int.signed_repr _ H) in H1; rewrite (Int.signed_repr _ H0) in H1.
repeat match type of H1 with
           | context [if ?a then _ else _] => destruct a
           end; try lia;
 destruct op; auto; simpl in *; try discriminate; lia.
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
   [ simpl in H | auto; unfold repable_signed, Int.min_signed, Int.max_signed in *; lia .. ].


Lemma isptr_deref_noload:
 forall t p, access_mode t = By_reference -> isptr (deref_noload t p) = isptr p.
Proof.
intros.
unfold deref_noload. rewrite H. reflexivity.
Qed.
#[export] Hint Rewrite isptr_deref_noload using reflexivity : norm.

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
#[export] Hint Resolve headptr_isptr : core.

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

Lemma typed_false_ptr:
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct Archi.ptr64 eqn:Hp;
destruct v; try discriminate; f_equal.
first [pose proof (Int64.eq_spec i Int64.zero); 
          destruct (Int64.eq i Int64.zero)
       | pose proof (Int.eq_spec i Int.zero); 
         destruct (Int.eq i Int.zero)]; 
      subst; auto; discriminate.
Qed.

Lemma typed_true_ptr:
  forall {t a v},  typed_true (Tpointer t a) v -> isptr v.
Proof.
unfold typed_true, strict_bool_val; simpl; intros.
destruct v; try discriminate; simpl; auto;
destruct Archi.ptr64; try discriminate;
 revert H; simple_if_tac; intros; discriminate.
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
 forall x, typed_false tint (bool2val x) -> (x=false).
Proof.
destruct x; simpl; intros; [inversion H | auto].
Qed.

Lemma typed_true_of_bool:
 forall x, typed_true tint (bool2val x) -> (x=true).
Proof.
destruct x; simpl; intros; [auto | inversion H].
Qed.

Lemma typed_false_tint:
 Archi.ptr64=false -> 
 forall v, typed_false tint v -> v=nullval.
Proof.
intros.
 hnf in H0. destruct v; inversion H0.
 destruct (Int.eq i Int.zero) eqn:?; inversion H2.
 apply int_eq_e in Heqb. subst.
 inv H; reflexivity.
Qed.

Lemma typed_false_tlong:
 Archi.ptr64=true -> 
 forall v, typed_false tlong v -> v=nullval.
Proof.
intros. unfold nullval. rewrite H.
 hnf in H0. destruct v; inversion H0.
pose proof (Int64.eq_spec i Int64.zero).
 destruct (Int64.eq i Int64.zero); inversion H2; subst.
reflexivity.
Qed.

Lemma typed_true_e:
 forall t v, typed_true t v -> v<>nullval.
Proof.
intros.
 intro Hx. subst.
 hnf in H. unfold nullval, strict_bool_val in H.
 destruct Archi.ptr64, t; discriminate.
Qed.

Lemma typed_false_tint_Vint:
  forall v, typed_false tint (Vint v) -> v = Int.zero.
Proof.
intros.
unfold typed_false, strict_bool_val in H. simpl in H.
pose proof (Int.eq_spec v Int.zero).
destruct (Int.eq v Int.zero); auto. inv H.
Qed.

Lemma typed_true_tint_Vint:
  forall v, typed_true tint (Vint v) -> v <> Int.zero.
Proof.
intros.
unfold typed_true, strict_bool_val in H. simpl in H.
pose proof (Int.eq_spec v Int.zero).
destruct (Int.eq v Int.zero); auto.
Qed.

Lemma typed_true_tlong_Vlong:
  forall v, typed_true tlong (Vlong v) -> v <> Int64.zero.
Proof.
intros.
unfold typed_true, strict_bool_val in H. simpl in H.
pose proof (Int64.eq_spec v Int64.zero).
destruct (Int64.eq v Int64.zero); auto.
Qed.

Lemma typed_false_tlong_Vlong:
  forall v, typed_false tlong (Vlong v) -> v = Int64.zero.
Proof.
intros.
unfold typed_false, strict_bool_val in H. simpl in H.
pose proof (Int64.eq_spec v Int64.zero).
destruct (Int64.eq v Int64.zero); auto. discriminate.
Qed.

Ltac intro_redundant P :=
 match goal with H: P |- _ => idtac end.

Ltac fancy_intro_discriminate H := idtac.

Ltac fancy_intro aggressive :=
 lazymatch goal with |- ~ _ => red | _ => idtac end;
 lazymatch goal with
 | |- ?P -> _ => match type of P with Prop => idtac end
 end;
 tryif
 lazymatch goal with |- ?P -> _ =>
     lazymatch P with
     | ptr_eq ?v1 ?v2 => intro_redundant (v1=v2)
     | Vint ?x = Vint ?y => constr_eq x y + intro_redundant (x=y)
     | tc_val ?ty ?v =>
         lazymatch ty with
         | Tint ?sz ?sg _ => intro_redundant(is_int sz sg v)
         | Tlong _ _ => intro_redundant(is_long v)
         | Tfloat F32 _ => intro_redundant(is_single v)
         | Tfloat F64 _ => intro_redundant(is_float v)
         | Tpointer _ _ =>
           tryif (unify ty int_or_ptr_type) 
           then intro_redundant (is_pointer_or_integer v)
           else intro_redundant (is_pointer_or_null v)
         | Tarray _ _ _ =>  intro_redundant (is_pointer_or_null v)
         | Tfunction _ _ _ =>  intro_redundant (is_pointer_or_null v)
         | _ =>  intro_redundant (isptr v)
         end
     | ?x = ?y => constr_eq x y + intro_redundant P
     | _ => intro_redundant P + unify P True%type
    end
   end
   then intros _
   else 
 let H := fresh in
 intro H;
 try simple apply ptr_eq_e in H;
 try simple apply Vint_inj in H;
 try lazymatch type of H with
 | tc_val _ _ => unfold tc_val in H; try change (eqb_type _ _) with false in H; cbv iota in H
 | ?x = ?y => tryif constr_eq aggressive true
                     then first [subst x | subst y
                                    | is_var x; rewrite H
                                    | is_var y; rewrite <- H
                                    | try fancy_intro_discriminate H]
                     else (try fancy_intro_discriminate H)
 | headptr (_ ?x) => let Hx1 := fresh "HP" x in
                     let Hx2 := fresh "P" x in
                       rename H into Hx1;
                       pose proof headptr_isptr _ Hx1 as Hx2
 | headptr ?x => let Hx1 := fresh "HP" x in
                 let Hx2 := fresh "P" x in
                   rename H into Hx1;
                   pose proof headptr_isptr _ Hx1 as Hx2
 | isptr ?x => let Hx := fresh "P" x in rename H into Hx
 | is_pointer_or_null ?x => let Hx := fresh "PN" x in rename H into Hx
 | typed_false _ _ =>
        first [simple apply typed_false_of_bool in H
               | apply typed_false_tint_Vint in H
               | apply (typed_false_tint (eq_refl _)) in H
               | apply (typed_false_tlong (eq_refl _)) in H
               | apply typed_false_ptr in H
               | idtac ]
 | typed_true _ _ =>
        first [simple apply typed_true_of_bool in H
               | apply typed_true_tint_Vint in H
               | apply typed_true_tlong_Vlong in H
               | apply typed_true_ptr in H
               | idtac ]
 end.

Ltac fancy_intros aggressive :=
 repeat lazymatch goal with
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

Lemma is_int_Vbyte: forall c, is_int I8 Signed (Vbyte c).
Proof.
intros. simpl. rewrite -> Int.signed_repr by rep_lia. rep_lia.
Qed.
#[export] Hint Resolve is_int_Vbyte : core.

