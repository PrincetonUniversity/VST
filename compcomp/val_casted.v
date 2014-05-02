(*TODO: These imports should be pared down*)
Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Errors.
Require Import Ordered.
Require Import AST.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import compcomp.SimplLocals.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.reach.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.

(** Properties of values obtained by casting to a given type. *)

Inductive val_casted: val -> type -> Prop :=
  | val_casted_int: forall sz si attr n,
      cast_int_int sz si n = n ->
      val_casted (Vint n) (Tint sz si attr)
  | val_casted_float: forall sz attr n,
      cast_float_float sz n = n ->
      val_casted (Vfloat n) (Tfloat sz attr)
  | val_casted_long: forall si attr n,
      val_casted (Vlong n) (Tlong si attr)
  | val_casted_ptr_ptr: forall b ofs ty attr,
      val_casted (Vptr b ofs) (Tpointer ty attr)
  | val_casted_int_ptr: forall n ty attr,
      val_casted (Vint n) (Tpointer ty attr)
  | val_casted_ptr_int: forall b ofs si attr,
      val_casted (Vptr b ofs) (Tint I32 si attr)
  | val_casted_ptr_cptr: forall b ofs id attr,
      val_casted (Vptr b ofs) (Tcomp_ptr id attr)
  | val_casted_int_cptr: forall n id attr,
      val_casted (Vint n) (Tcomp_ptr id attr)
  | val_casted_struct: forall id fld attr b ofs,
      val_casted (Vptr b ofs) (Tstruct id fld attr)
  | val_casted_union: forall id fld attr b ofs,
      val_casted (Vptr b ofs) (Tunion id fld attr)
  | val_casted_void: forall v,
      val_casted v Tvoid.

Definition val_casted_func (v : val) (t : type) : bool :=
  match v, t with
    | Vint n, Tint sz si attr => 
      if Int.eq_dec (cast_int_int sz si n) n then true
      else false
    | Vfloat n, Tfloat sz attr => 
      if Float.eq_dec (cast_float_float sz n) n then true
      else false
    | Vlong n, Tlong si attr => true
    | Vptr b ofs, Tpointer ty attr => true
    | Vint n, Tpointer ty attr => true
    | Vptr b ofs, Tint I32 si attr => true
    | Vptr b ofs, Tcomp_ptr id attr => true
    | Vint n, Tcomp_ptr id attr => true
    | Vptr b ofs, Tstruct id flt attr => true
    | Vptr b ofs, Tunion id flt attr => true
    | _, Tvoid => true 
    | _, _ => false
  end.

Lemma val_casted_funcI v t : 
  val_casted v t -> 
  val_casted_func v t=true.
Proof.
destruct 1; simpl; auto.
rewrite H. case_eq (Int.eq_dec n n); auto.
rewrite H. case_eq (Float.eq_dec n n); auto.
destruct v; auto.
Qed.

Lemma val_casted_funcE v t : 
  val_casted_func v t=true ->
  val_casted v t.
Proof.
destruct v; destruct t; simpl; try solve[inversion 1;econstructor; eauto].
case_eq (Int.eq_dec (cast_int_int i0 s i) i). intros e _ _.
constructor; auto. intros n _; inversion 1.
case_eq (Float.eq_dec (cast_float_float f0 f) f). intros e _ _.
constructor; auto. intros n _; inversion 1.
destruct i0; try inversion 1. constructor.
Qed.

Lemma val_casted_funcP v t : 
  val_casted_func v t=true <-> val_casted v t.
Proof.
split; [apply val_casted_funcE|apply val_casted_funcI].
Qed.

Remark cast_int_int_idem:
  forall sz sg i, cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i.
Proof.
  intros. destruct sz; simpl; auto. 
  destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
  destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
  destruct (Int.eq i Int.zero); auto.
Qed.

Remark cast_float_float_idem:
  forall sz f, cast_float_float sz (cast_float_float sz f) = cast_float_float sz f.
Proof.
  intros; destruct sz; simpl.
  apply Float.singleoffloat_idem; auto.
  auto.
Qed.

Lemma cast_val_is_casted:
  forall v ty ty' v', sem_cast v ty ty' = Some v' -> val_casted v' ty'.
Proof.
  unfold sem_cast; intros. destruct ty'; simpl in *.
(* void *)
  constructor.
(* int *)
  destruct i; destruct ty; simpl in H; try discriminate; destruct v; inv H.
  constructor. apply (cast_int_int_idem I8 s).
  constructor. apply (cast_int_int_idem I8 s).
  destruct (cast_float_int s f0); inv H1.   constructor. apply (cast_int_int_idem I8 s). 
  constructor. apply (cast_int_int_idem I16 s).
  constructor. apply (cast_int_int_idem I16 s).
  destruct (cast_float_int s f0); inv H1.   constructor. apply (cast_int_int_idem I16 s). 
  constructor. auto.
  constructor.
  constructor. auto. 
  destruct (cast_float_int s f0); inv H1. constructor. auto.
  constructor. auto.
  constructor.
  constructor; auto.
  constructor.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i0 Int.zero); auto.
  constructor. simpl. destruct (Int64.eq i Int64.zero); auto.
  constructor. simpl. destruct (Float.cmp Ceq f0 Float.zero); auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i0 Int.zero); auto.
  constructor; auto.
(* long *)
  destruct ty; try discriminate.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; try discriminate. destruct (cast_float_long s f0); inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
(* float *)
  destruct ty; simpl in H; try discriminate; destruct v; inv H.
  constructor. unfold cast_float_float, cast_int_float.
  destruct f; destruct s; auto.
  rewrite Float.singleofint_floatofint. apply Float.singleoffloat_idem.
  rewrite Float.singleofintu_floatofintu. apply Float.singleoffloat_idem.
  constructor. unfold cast_float_float, cast_long_float.
  destruct f; destruct s; auto. apply Float.singleoflong_idem. apply Float.singleoflongu_idem.
  constructor. apply cast_float_float_idem.
(* pointer *)
  destruct ty; simpl in H; try discriminate; destruct v; inv H; try constructor.
(* impossible cases *)
  discriminate.
  discriminate.
(* structs *)
  destruct ty; try discriminate; destruct v; try discriminate.
  destruct (ident_eq i0 i && fieldlist_eq f0 f); inv H; constructor.
(* unions *)
  destruct ty; try discriminate; destruct v; try discriminate.
  destruct (ident_eq i0 i && fieldlist_eq f0 f); inv H; constructor.
(* comp_ptr *)
  destruct ty; simpl in H; try discriminate; destruct v; inv H; constructor.
Qed.

Lemma val_casted_load_result:
  forall v ty chunk,
  val_casted v ty -> access_mode ty = By_value chunk ->
  Val.load_result chunk v = v.
Proof.
  intros. inversion H; clear H; subst v ty; simpl in H0.
  destruct sz.
  destruct si; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  destruct si; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  clear H1. inv H0. auto.
  inversion H0; clear H0; subst chunk. simpl in *. 
  destruct (Int.eq n Int.zero); subst n; reflexivity.
  destruct sz; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  inv H0; auto.
  inv H0; auto.
  inv H0; auto.
  inv H0; auto.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

Lemma cast_val_casted:
  forall v ty, val_casted v ty -> sem_cast v ty ty = Some v.
Proof.
  intros. inversion H; clear H; subst v ty; unfold sem_cast; simpl; auto.
  destruct sz; congruence.
  congruence.
  unfold proj_sumbool; repeat rewrite dec_eq_true; auto.
  unfold proj_sumbool; repeat rewrite dec_eq_true; auto.
Qed.

Lemma val_casted_inject:
  forall f v v' ty,
  val_inject f v v' -> val_casted v ty -> val_casted v' ty.
Proof.
  intros. inv H; auto.
  inv H0; constructor.
  inv H0; constructor.
Qed.

Inductive val_casted_list: list val -> typelist -> Prop :=
  | vcl_nil:
      val_casted_list nil Tnil
  | vcl_cons: forall v1 vl ty1 tyl,
      val_casted v1 ty1 -> val_casted_list vl tyl ->
      val_casted_list (v1 :: vl) (Tcons  ty1 tyl).

Lemma val_casted_list_params:
  forall params vl,
  val_casted_list vl (type_of_params params) ->
  list_forall2 val_casted vl (map snd params).
Proof.
  induction params; simpl; intros. 
  inv H. constructor.
  destruct a as [id ty]. inv H. constructor; auto. 
Qed.

Fixpoint val_casted_list_func (vs : list val) (ts : typelist) : bool :=
  match vs, ts with
    | nil, Tnil => true
    | v1 :: vl, Tcons ty1 tyl => 
      val_casted_func v1 ty1 && val_casted_list_func vl tyl
    | _, _ => false
  end.

Lemma val_casted_list_funcP vs ts : 
  val_casted_list_func vs ts=true <-> val_casted_list vs ts.
Proof.
revert ts; induction vs. destruct ts; simpl; auto.
split; auto. intros _. constructor.
split; auto. inversion 1. inversion 1.
split; auto. destruct ts; simpl; auto.
inversion 1. rewrite andb_true_iff. intros [H1 H2]. constructor.
apply val_casted_funcE in H1; auto. rewrite <-IHvs; auto.
inversion 1; subst. simpl. rewrite andb_true_iff; split.
apply val_casted_funcI; auto. rewrite IHvs; auto.
Qed.

Lemma val_casted_inj (j : meminj) v1 v2 tv : 
  val_inject j v1 v2 -> 
  val_casted v1 tv -> 
  val_casted v2 tv.
Proof.
inversion 1; subst; auto.
inversion 1; subst; auto; try solve[constructor; auto].
inversion 1; constructor.
Qed.

Lemma val_casted_list_inj (j : meminj) vs1 vs2 ts :
  val_list_inject j vs1 vs2 ->
  val_casted_list vs1 ts ->
  val_casted_list vs2 ts.
Proof.
intros H1; revert vs1 vs2 H1; induction ts; simpl; intros vs1 vs2 H1 H2.
revert H2 H1; inversion 1; subst. inversion 1; subst. constructor.
revert H2 H1; inversion 1; subst. inversion 1; subst. constructor.
eapply val_casted_inj; eauto.
eapply IHts; eauto.
Qed.
