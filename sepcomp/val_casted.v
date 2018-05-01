Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Export compcert.lib.Axioms.

Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.reach.
Require Import VST.sepcomp.effect_semantics.
Require Import VST.sepcomp.structured_injections.

(** Properties of values obtained by casting to a given type. *)

Inductive val_casted: val -> type -> Prop :=
  | val_casted_int: forall sz si attr n,
      cast_int_int sz si n = n ->
      val_casted (Vint n) (Tint sz si attr)
  | val_casted_float: forall attr n,
      val_casted (Vfloat n) (Tfloat F64 attr)
  | val_casted_single: forall attr n,
      val_casted (Vsingle n) (Tfloat F32 attr)
  | val_casted_long: forall si attr n,
      val_casted (Vlong n) (Tlong si attr)
  | val_casted_ptr_ptr: forall b ofs ty attr,
      val_casted (Vptr b ofs) (Tpointer ty attr)
  | val_casted_int_ptr: forall n ty attr,
      val_casted (Vint n) (Tpointer ty attr)
  | val_casted_ptr_int: forall b ofs si attr,
      val_casted (Vptr b ofs) (Tint I32 si attr)
  | val_casted_struct: forall id attr b ofs,
      val_casted (Vptr b ofs) (Tstruct id attr)
  | val_casted_union: forall id attr b ofs,
      val_casted (Vptr b ofs) (Tunion id attr)
  | val_casted_void: forall v,
      val_casted v Tvoid.

Definition val_casted_func (v : val) (t : type) : bool :=
  match v, t with
    | Vint n, Tint sz si attr =>
      if Int.eq_dec (cast_int_int sz si n) n then true
      else false
    | Vfloat n, Tfloat F64 attr =>  true
    | Vsingle n, Tfloat F32 attr =>  true
    | Vlong n, Tlong si attr => true
    | Vptr b ofs, Tpointer ty attr => true
    | Vint n, Tpointer ty attr => true
    | Vptr b ofs, Tint I32 si attr => true
    | Vptr b ofs, Tstruct id attr => true
    | Vptr b ofs, Tunion id attr => true
    | _, Tvoid => true
    | _, _ => false
  end.

Lemma val_casted_funcI v t :
  val_casted v t ->
  val_casted_func v t=true.
Proof.
destruct 1; simpl; auto.
rewrite H. case_eq (Int.eq_dec n n); auto.
destruct v; auto.
Qed.

Lemma val_casted_funcE v t :
  val_casted_func v t=true ->
  val_casted v t.
Proof.
destruct v; destruct t; simpl; try solve[inversion 1;econstructor; eauto].
case_eq (Int.eq_dec (cast_int_int i0 s i) i). intros e _ _.
constructor; auto. intros n _; inversion 1.
destruct f0; intros; try discriminate; constructor.
destruct f0; intros; try discriminate; constructor.
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

(*
Remark cast_float_float_idem:
  forall sz f, cast_float_float sz (cast_float_float sz f) = cast_float_float sz f.
Proof.
  intros; destruct sz; simpl.
  apply Float.singleoffloat_idem; auto.
  auto.
Qed.
*)

Lemma cast_val_is_casted:
  forall v ty ty' v' m, sem_cast v ty ty' m = Some v' -> val_casted v' ty'.
Proof.
  unfold sem_cast; intros. destruct ty'; simpl in *.
* (* void *)
  constructor.
* (* int *)
  destruct Archi.ptr64 eqn:Hp. 
  inversion Hp. (* Archi.ptr64=false DEPENDENCY *)
  destruct i; destruct ty as [ | | | [ | ] | | | | | ];
   simpl in H; try discriminate; destruct v; inv H;
   try now constructor.
  constructor. apply (cast_int_int_idem I8 s).
  constructor. apply (cast_int_int_idem I8 s).
  destruct (cast_single_int s f); inv H1.   constructor. apply (cast_int_int_idem I8 s).
  destruct (cast_float_int s f); inv H1.   constructor. apply (cast_int_int_idem I8 s).
  constructor. apply (cast_int_int_idem I8 s).
  constructor. apply (cast_int_int_idem I8 s).
  constructor. apply (cast_int_int_idem I8 s).
  constructor. apply (cast_int_int_idem I16 s).
  constructor. apply (cast_int_int_idem I16 s).
  destruct (cast_single_int s f); inv H1.   constructor. apply (cast_int_int_idem I16 s).
  destruct (cast_float_int s f); inv H1.
       constructor. apply (cast_int_int_idem I16 s).
       constructor. apply (cast_int_int_idem I16 s).
       constructor. apply (cast_int_int_idem I16 s).
       constructor. apply (cast_int_int_idem I16 s).
  destruct (cast_single_int s f); inv H1. constructor. auto.
  destruct (cast_float_int s f); inv H1. constructor. auto.
  constructor. simpl. destruct (Int.eq i0 Int.zero); auto.
(*
  constructor. simpl. destruct (Int64.eq i Int64.zero); auto.
  constructor. simpl. destruct (Float32.cmp Ceq f Float32.zero); auto.
  constructor. simpl. destruct (Float.cmp Ceq f Float.zero); auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
*)
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)); inv H1.
    constructor. reflexivity.
  constructor. destruct (Int64.eq i Int64.zero); reflexivity.
  constructor. destruct (Float32.cmp Ceq f Float32.zero); reflexivity.
  constructor. destruct (Float.cmp Ceq f Float.zero); reflexivity.
  constructor. destruct (Int.eq i Int.zero); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H1.
    constructor. reflexivity.
  constructor. destruct (Int.eq i Int.zero); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H1.
    constructor. reflexivity.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H1.
    constructor. reflexivity.
* (* long *)
  destruct ty as [ | | | [ | ] | | | | | ]; try discriminate.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; try discriminate. destruct (cast_single_long s f); inv H. constructor.
  destruct v; try discriminate. destruct (cast_float_long s f); inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
  destruct v; inv H. constructor.
* (* float *)
  destruct f.
  destruct ty as [ | | | [ | ] | | | | | ]; simpl in H; try discriminate; destruct v; inv H;
   try solve [constructor].
  destruct ty as [ | | | [ | ] | | | | | ]; simpl in H; try discriminate; destruct v; inv H;
   try solve [constructor].
* (* pointer *)
  destruct ty; simpl in H; try discriminate; destruct v; inv H; try constructor.
* (* impossible cases *)
  discriminate.
*
  discriminate.
* (* structs *)
  destruct ty; try discriminate; destruct v; try discriminate.
  destruct (ident_eq i0 i ); inv H; constructor.
* (* unions *)
  destruct ty; try discriminate; destruct v; try discriminate.
  destruct (ident_eq i0 i ); inv H; constructor.
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
  inversion H0; clear H0; subst chunk; simpl in *; congruence.
  inversion H0; clear H0; subst chunk; simpl in *; congruence.
  inv H0; auto.
  inv H0; auto.
  inv H0; auto.
  inv H0; auto.
  discriminate.
  discriminate.
  discriminate.
Qed.

Lemma cast_val_casted:
  forall v ty m, val_casted v ty -> sem_cast v ty ty m = Some v.
Proof.
  intros.
  unfold sem_cast, classify_cast.
  destruct Archi.ptr64 eqn:Hp. 
  inversion Hp. (* Archi.ptr64=false DEPENDENCY *)
  inversion H; clear H; subst v ty; unfold sem_cast; simpl; auto.
  destruct sz; simpl; try destruct si; simpl in *; try congruence.
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
  Val.inject_list j vs1 vs2 ->
  val_casted_list vs1 ts ->
  val_casted_list vs2 ts.
Proof.
intros H1; revert vs1 vs2 H1; induction ts; simpl; intros vs1 vs2 H1 H2.
revert H2 H1; inversion 1; subst. inversion 1; subst. constructor.
revert H2 H1; inversion 1; subst. inversion 1; subst. constructor.
eapply val_casted_inj; eauto.
eapply IHts; eauto.
Qed.

Definition val_has_type_func (v : val) (t : typ) : bool :=
  match v with
    | Vundef => true
    | Vint _ => match t with
                  | AST.Tint => true
                  | AST.Tany32 => true
                  | AST.Tany64 => true
                  | _ => false
                end
    | Vlong _ => match t with
                 | AST.Tlong => true
                 | AST.Tany64 => true
                 | _ => false
               end
    | Vfloat f => match t with
                    | AST.Tfloat => true
                    | AST.Tany64 => true
                    | _ => false
                  end
    | Vsingle f => match t with
                    | AST.Tsingle => true
                    | AST.Tany32 => true
                    | AST.Tany64 => true
                    | _ => false
                  end
    | Vptr _ _ => match t with
                    | AST.Tint => true
                    | AST.Tany32 => true
                    | AST.Tany64 => true
                    | _ => false
                  end
  end.

Lemma val_has_type_funcP v t :
  Val.has_type v t <-> (val_has_type_func v t=true).
Proof.
split.
induction v; auto.
simpl. destruct t; auto.
simpl. destruct t; auto.
simpl. destruct t; auto.
simpl. destruct t; auto.
simpl. destruct t; auto.
induction v; simpl; auto.
destruct t; auto; try inversion 1.
destruct t; auto; try inversion 1.
destruct t; auto; try solve[inversion 1].
destruct t; auto. inversion 1. inversion 1. inversion 1.
destruct t; auto. inversion 1. inversion 1.
Qed.

Fixpoint val_has_type_list_func (vl : list val) (tyl : list typ) : bool :=
  match vl, tyl with
    | nil, nil => true
    | v :: vl', ty :: tyl' => val_has_type_func v ty
                              && val_has_type_list_func vl' tyl'
    | nil, _ :: _ => false
    | _ :: _, nil => false
  end.

Lemma val_has_type_list_func_charact vl tyl :
  Val.has_type_list vl tyl <-> (val_has_type_list_func vl tyl=true).
Proof.
revert tyl; induction vl.
destruct tyl. simpl. split; auto. simpl. split; auto. inversion 1.
intros. destruct tyl. simpl; auto. split; auto. inversion 1.
simpl. split. intros [H H2].
+ rewrite andb_true_iff. split.
  rewrite <-val_has_type_funcP; auto.
  rewrite <-IHvl; auto.
+ rewrite andb_true_iff. intros [H H2]. split.
  rewrite val_has_type_funcP; auto.
  rewrite IHvl; auto.
Qed.

Fixpoint tys_nonvoid (tyl : typelist) :=
  match tyl with
    | Tnil => true
    | Tcons Tvoid tyl' => false
    | Tcons _ tyl' => tys_nonvoid tyl'
  end.

Fixpoint vals_defined (vl : list val) :=
  match vl with
    | nil => true
    | Vundef :: _ => false
    | _ :: vl' => vals_defined vl'
  end.

Lemma vals_inject_defined (vl1 vl2 : list val) (j : meminj) :
  Val.inject_list j vl1 vl2 ->
  vals_defined vl1=true ->
  vals_defined vl2=true.
Proof.
revert vl2; induction vl1; simpl. destruct vl2; try solve[inversion 1|auto].
intros vl2; inversion 1; subst. destruct a; try solve[inversion 1].
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
inv H. inv H5. simpl. intros X. rewrite (IHvl1 vl'); auto.
Qed.

Lemma valinject_hastype':
  forall (j : meminj) (v v' : val),
    val_inject j v v' ->
    v <> Vundef ->
    forall T : typ, Val.has_type v T -> Val.has_type v' T.
Proof.
  intros.
  induction H; auto.
  elim H0; auto.
Qed.

Lemma val_list_inject_hastype j vl1 vl2 tys :
  Val.inject_list j vl1 vl2 ->
  vals_defined vl1=true ->
  val_has_type_list_func vl1 tys=true ->
  val_has_type_list_func vl2 tys=true.
Proof.
revert vl2 tys. induction vl1. inversion 1. solve[destruct tys; simpl; auto].
intros H tys H1 H2 H3. inv H1.
assert (def: vals_defined vl1=true).
{ inv H2. revert H0. destruct a; auto. congruence. }
simpl. destruct tys. simpl in H3; congruence.
rewrite andb_true_iff. split.
rewrite <-val_has_type_funcP. eapply valinject_hastype'; eauto.
simpl in H2. intros contra. rewrite contra in H2. congruence.
inv H3. rewrite andb_true_iff in H0.
  destruct H0 as [H0 _]. solve[rewrite val_has_type_funcP; auto].
eapply (IHvl1 vl'); eauto.
inv H3. rewrite H0. rewrite andb_true_iff in H0.
  solve[destruct H0 as [_ ->]; auto].
Qed.

Lemma val_list_inject_defined j vl1 vl2 :
  Val.inject_list j vl1 vl2 ->
  vals_defined vl1=true ->
  vals_defined vl2=true.
Proof.
revert vl2. induction vl1; simpl.
+ intros vl2; inversion 1; auto.
+ intros vl2; inversion 1; subst. inv H.
simpl. intros H8.
assert (def1: vals_defined vl1=true).
{ destruct a; try solve[congruence]. }
revert H2 H8. inversion 1; auto. subst. congruence.
Qed.

(*TODO: put these in Events.v*)
Fixpoint encode_longs (tyl : list typ) (vl : list val) :=
  match tyl with
    | nil => nil
    | AST.Tlong :: tyl' =>
      match vl with
        | nil => nil
        | Vlong n :: vl' => Vint (Int64.hiword n) :: Vint (Int64.loword n)
                            :: encode_longs tyl' vl'
        | Vundef :: vl' => Vundef :: Vundef :: encode_longs tyl' vl'
        | _ :: vl' => Vundef :: Vundef :: encode_longs tyl' vl'
      end
    | t :: tyl' =>
      match vl with
        | nil => nil
        | v :: vl' => v :: encode_longs tyl' vl'
      end
  end.

Fixpoint encode_typs (tyl : list typ) : list typ :=
  match tyl with
    | nil => nil
    | AST.Tlong :: tyl' => AST.Tint :: AST.Tint :: encode_typs tyl'
    | t :: tyl' => t :: encode_typs tyl'
  end.

Lemma encode_longs_has_type tyl vl :
  Val.has_type_list vl tyl ->
  Val.has_type_list (encode_longs tyl vl) (encode_typs tyl).
Proof.
revert vl; induction tyl. simpl; auto.
destruct vl. intros; contradiction. intros [H H2]. simpl.
destruct a; try solve[split; auto].
destruct v; simpl; auto.
Qed.

(* decode_longs copied from CompCert2.6/common/Events.v;
   no longer present in CompCert 2.7; don't know why. -- Andrew *)
Fixpoint decode_longs (tyl: list typ) (vl: list val) : list val :=
  match tyl with
  | nil => nil
  | AST.Tlong :: tys =>
      match vl with
      | v1 :: v2 :: vs => Val.longofwords v1 v2 :: decode_longs tys vs
      | _ => nil
      end
  | ty :: tys =>
      match vl with
      | v1 :: vs => v1 :: decode_longs tys vs
      | _ => nil
      end
  end.


Lemma decode_encode_longs tyl vl :
  Val.has_type_list vl tyl ->
  decode_longs tyl (encode_longs tyl vl) = vl.
Proof.
revert tyl; induction vl.
destruct tyl. simpl; auto.
destruct t; simpl; auto.
destruct tyl. simpl. inversion 1. inversion 1; subst. clear H.
simpl. destruct t; auto; try rewrite IHvl; auto.
destruct a; simpl; try solve[inv H0].
rewrite IHvl; auto.
rewrite IHvl; auto. f_equal.
rewrite Int64.ofwords_recompose; auto.
Qed.

Lemma encode_longs_inject:
  forall (f : meminj) (tyl : list typ) (vl1 vl2 : list val),
  Val.inject_list f vl1 vl2 ->
  Val.inject_list f (encode_longs tyl vl1) (encode_longs tyl vl2).
Proof.
intros until vl2; intros H; revert tyl; induction H; simpl.
destruct tyl; simpl; [solve[constructor]|]. solve[destruct t; auto].
destruct tyl; simpl; [solve[constructor]|]. destruct t.
solve[constructor; auto].
solve[constructor; auto].
inv H. solve[auto]. constructor; auto. solve[auto]. solve[auto]. solve[auto].
destruct v'; solve[auto|constructor; auto].
solve[constructor; auto].
solve[constructor; auto].
solve[constructor; auto].
Qed.

Fixpoint getBlocks' (vl : list val) (b0 : block) :=
  match vl with
    | nil => false
    | Vptr b _ :: vl' => eq_block b b0 || getBlocks' vl' b0
    | _ :: vl' => getBlocks' vl' b0
  end.

Lemma getBlocks_getBlocks' vl b0 : getBlocks vl b0 = getBlocks' vl b0.
Proof.
induction vl; simpl; auto.
destruct a; auto. unfold getBlocks. simpl.
destruct (eq_block b b0); simpl; auto.
rewrite <-IHvl. unfold getBlocks.
destruct (
     in_dec eq_block b0
       (fold_right
          (fun (v : val) (L : list block) =>
           match v with
           | Vundef => L
           | Vint _ => L
           | Vlong _ => L
           | Vfloat _ => L
           | Vsingle _ => L
           | Vptr b' _ => b' :: L
           end) nil vl)
); auto.
Qed.

Lemma getBlocks_encode_longs tys vals b :
  getBlocks (encode_longs tys vals) b=true ->
  getBlocks vals b=true.
Proof.
  rewrite !getBlocks_getBlocks'.
  revert tys; induction vals; simpl; auto. destruct tys. simpl; auto.
  solve[destruct t; simpl; auto].
  destruct tys. simpl; congruence.
  simpl. destruct t; destruct a; simpl; intros; try solve[eapply IHvals; eauto].
  rewrite orb_true_iff in H. destruct H. rewrite H; auto.
    rewrite orb_true_iff. right. solve[eapply IHvals; eauto].
  rewrite orb_true_iff in H. destruct H. rewrite H; auto.
    rewrite orb_true_iff. right. solve[eapply IHvals; eauto].
  rewrite orb_true_iff. right. solve[eapply IHvals; eauto].
  rewrite orb_true_iff in H. destruct H. rewrite H; auto.
    rewrite orb_true_iff. right. solve[eapply IHvals; eauto].
  rewrite orb_true_iff in H. destruct H. rewrite H; auto.
    rewrite orb_true_iff. right. solve[eapply IHvals; eauto].
  rewrite orb_true_iff in H. destruct H. rewrite H; auto.
    rewrite orb_true_iff. right. solve[eapply IHvals; eauto].
Qed.

Lemma val_casted_has_type a t :
  tys_nonvoid (Tcons t Tnil) = true ->
  val_casted_func a t = true ->
  val_has_type_func a (typ_of_type t) = true.
Proof.
intros H0 H.
apply val_casted_funcE in H.
induction H; try solve[auto].
simpl in H0. congruence.
Qed.

Lemma val_casted_has_type_list vals tys :
  tys_nonvoid tys = true ->
  val_casted_list_func vals tys = true ->
  val_has_type_list_func vals (typlist_of_typelist tys) = true.
Proof.
revert vals; induction tys. simpl. intros vals.
destruct vals. simpl; auto. simpl. solve[inversion 2].
simpl; intros vals; revert tys IHtys; induction vals. simpl.
  intros; congruence.
simpl; intros. rewrite andb_true_iff in H0; destruct H0 as [H0 H2].
assert (H3: tys_nonvoid tys = true).
{ destruct t; solve[congruence|auto]. }
rewrite andb_true_iff. split; auto.
apply val_casted_has_type; auto. destruct t; auto.
Qed.
