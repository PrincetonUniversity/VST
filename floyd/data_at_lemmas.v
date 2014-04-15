Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

(******************************************

Lemmas about mapsto and mapsto_

******************************************)

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto_; intros.
  normalize.
  unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); try apply FF_left.
  destruct v; auto.
  apply orp_left.
  apply orp_right2.
  apply andp_left2.
  apply andp_right. apply prop_right; auto.
  apply exp_right with v'; auto.
  normalize.
  apply orp_right2. apply exp_right with v2'.
  normalize.
Qed.
Hint Resolve mapsto_mapsto_ : cancel.

Lemma mapsto_isptr: forall sh t v1 v2, mapsto sh t v1 v2 = !! (isptr v1) && mapsto sh t v1 v2.
Proof.
  intros; apply pred_ext; normalize.
  apply andp_right; auto.
  unfold mapsto.
  destruct (access_mode t); normalize.
  destruct (type_is_volatile t); normalize.
  destruct v1; normalize.
  apply prop_right; apply I.
Qed.

Lemma mapsto__isptr: forall sh t v1, mapsto_ sh t v1 = !! (isptr v1) && mapsto_ sh t v1.
Proof.
  intros.
  unfold mapsto_. apply mapsto_isptr.
Qed.

(******************************************

Lemmas about memory_block

******************************************)

Lemma memory_block_zero: forall sh b z, memory_block sh (Int.repr 0) (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  change (Int.repr 0) with Int.zero.
  rewrite Int.unsigned_zero.
  change (nat_of_Z 0) with (0%nat).
  unfold memory_block'.
  reflexivity.
Qed.
Hint Rewrite memory_block_zero: norm.

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n (offset_val Int.zero v) = memory_block sh n v.
Proof.
  unfold memory_block; intros.
  destruct v; auto.
  simpl offset_val. cbv beta iota.
  rewrite Int.add_zero. auto.
Qed.

Lemma memory_block_local_facts: forall sh n p, memory_block sh n p |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; normalize.
Qed.

Lemma memory_block_isptr: forall sh n p, memory_block sh n p = !!(isptr p) && memory_block sh n p.
Proof.
  intros.
  unfold memory_block.
  destruct p; normalize.
Qed.

Global Opaque memory_block.

(******************************************
******************************************)

Scheme type_mut := Induction for type Sort Prop
with typelist_mut := Induction for typelist Sort Prop
with fieldlist_mut := Induction for fieldlist Sort Prop.

Fixpoint is_Fnil (fld: fieldlist) : bool :=
  match fld with
  | Fnil => true
  | Fcons id ty fld' => false
  end.

Fixpoint reptype (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => val
  | Tlong _ _ => val
  | Tfloat _ _ => val
  | Tpointer t1 a => val
  | Tarray t1 sz a => list (reptype t1)
  | Tfunction t1 t2 => unit
  | Tstruct id fld a => reptype_structlist fld
  | Tunion id fld a => reptype_unionlist fld
  | Tcomp_ptr id a => val
  end
with reptype_structlist (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => 
          if is_Fnil fld' 
                      then reptype ty
                      else prod (reptype ty) (reptype_structlist fld')
  end
with reptype_unionlist (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => sum (reptype ty) (reptype_unionlist fld')
  end.

Fixpoint reptype' (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => int
  | Tlong _ _ => Int64.int
  | Tfloat _ _ => float
  | Tpointer t1 a => val
  | Tarray t1 sz a => list (reptype' t1)
  | Tfunction t1 t2 => unit
  | Tstruct id fld a => reptype'_structlist fld
  | Tunion id fld a => reptype'_unionlist fld
  | Tcomp_ptr id a => val
  end
with reptype'_structlist (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => 
          if is_Fnil fld' 
                      then reptype' ty
                      else prod (reptype' ty) (reptype'_structlist fld')
  end
with reptype'_unionlist (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => sum (reptype' ty) (reptype'_unionlist fld')
  end.

Fixpoint repinj (t: type): reptype' t -> reptype t :=
match t as t0 return (reptype' t0 -> reptype t0) with
| Tvoid => id
| Tint _ _ _ => Vint
| Tlong _ _ => Vlong
| Tfloat _ _ => Vfloat
| Tpointer _ _ => id
| Tarray t0 _ _ => (map (repinj t0))
| Tfunction _ _ => id
| Tstruct _ f _ => (repinj_structlist f)
| Tunion _ f _ => (repinj_unionlist f)
| Tcomp_ptr _ _ => id
end
with repinj_structlist (fld: fieldlist) : reptype'_structlist fld -> reptype_structlist fld :=
match fld as f return (reptype'_structlist f -> reptype_structlist f) with
| Fnil => id
| Fcons _ t fld0 =>
    (if is_Fnil fld0  as b0
      return
        (is_Fnil fld0 = b0 ->
         (if b0
          then reptype' t
          else (reptype' t * reptype'_structlist fld0)%type) ->
         if b0 then reptype t else (reptype t * reptype_structlist fld0)%type)
     then fun _ : is_Fnil fld0 = true => repinj t
     else
      fun (_ : is_Fnil fld0 = false)
        (v : reptype' t * reptype'_structlist fld0) =>
      (repinj t (fst v), repinj_structlist fld0 (snd v))) eq_refl
end
with repinj_unionlist (fld: fieldlist) : reptype'_unionlist fld -> reptype_unionlist fld :=
match fld as f return (reptype'_unionlist f -> reptype_unionlist f) with
| Fnil => id
| Fcons _ t fld0 =>
    fun X : reptype' t + reptype'_unionlist fld0 =>
    match X with
    | inl v1 => inl (repinj t v1)
    | inr v2 => inr (repinj_unionlist fld0 v2)
    end
end.

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Hint Rewrite int_add_repr_0_l int_add_repr_0_r : norm.

(*
Lemma field_at__offset_zero:
  forall sh ty id v, 
   field_at_ sh ty id (offset_val (Int.repr 0) v) =
   field_at_ sh ty id v.
Proof.
 unfold field_at_; intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_at__offset_zero: norm.
*)

Definition at_offset (z: Z) (P: val -> mpred) : val -> mpred :=
 fun v => P (offset_val (Int.repr z) v).

Arguments at_offset z P v : simpl never.

Definition at_offset' (P: val -> mpred) (z: Z)  : val -> mpred :=
 match z with Z0 => P | _ => at_offset z P end.

Definition at_offset2 {T} (f: val -> T -> mpred) pos (v2: T) := 
           at_offset' (fun v => f v v2) pos.

Lemma at_offset'_eq: forall P z v,
  P (offset_val (Int.repr 0) v) = P v ->
  at_offset' P z v = P (offset_val (Int.repr z) v).
Proof.
intros.
unfold at_offset'.
destruct z; auto.
Qed.

Definition spacer (sh: share) (pos: Z) (alignment: Z) : val -> mpred :=
  if Z.eq_dec  (align pos alignment - pos) 0
  then fun _ => emp
  else
   at_offset' (memory_block sh (Int.repr (align pos alignment - pos))) pos.

Arguments spacer sh pos alignment / _ .

Definition withspacer sh (pos: Z) (alignment: Z) : (val -> mpred) -> val -> mpred :=
   match align pos alignment - pos with
   | Z0 => fun P => P
   | _ => fun P => spacer sh pos alignment * P
   end.

Lemma withspacer_spacer: forall sh pos alignment P,
   withspacer sh pos alignment P = spacer sh pos alignment * P.
Proof.
  intros.
 extensionality v.
 unfold withspacer, spacer.
 destruct (align pos alignment - pos); auto.
 rewrite if_true by auto.
 simpl. rewrite emp_sepcon. auto.
Qed.

Fixpoint default_val (t: type) : reptype t :=
  match t as t0 return (reptype t0) with
  | Tvoid => tt
  | Tint _ _ _ => Vundef
  | Tlong _ _ => Vundef
  | Tfloat _ _ => Vundef
  | Tpointer _ _ => Vundef
  | Tarray t0 _ _ => nil
  | Tfunction _ _ => tt
  | Tstruct _ f _ => struct_default_val f
  | Tunion _ f _ =>
      match f as f0 return (reptype_unionlist f0) with
      | Fnil => tt
      | Fcons _ t1 _ => inl (default_val t1)
      end
  | Tcomp_ptr _ _ => Vundef
  end
with struct_default_val flds : reptype_structlist flds :=
  match flds as f return (reptype_structlist f) with
  | Fnil => tt
  | Fcons _ t flds0 =>
     if is_Fnil flds0 as b
      return  (if b then reptype t else (reptype t * reptype_structlist flds0)%type)
     then default_val t
     else (default_val t, struct_default_val flds0)
  end.

(************************************************

reptype is not defined in a quite beautiful way now. However, there seems no
better choice. The situation is explained at the end of this file. When Coq
releases a new version in the future, maybe we can rewrite it in a better way.

************************************************)

(************************************************

Definition of data_at 

************************************************)

(************************************************

Always assume in arguments of data_at', array_at', sfieldlist_at', ufieldlist_
at' has argument pos with alignment criterian. So, spacers are only added after
fields of structs or unions.

A new array_at' is used here. But it worths discussion which version is better.

Personally, I don't know why "function" case looks like this. I just copy it
from previous version.

************************************************)

Definition type_id_env: Type := PTree.t type.
Definition empty_ti: type_id_env := @PTree.empty type.

Definition singleton_si t: type_id_env :=
  match t with
  | Tstruct i _ _ => PTree.set i t empty_ti
  | Tunion i _ _ => PTree.set i t empty_ti
  | _ => empty_ti
  end.

Definition look_up_ident_default (i: ident) (e: type_id_env) : type :=
  match PTree.get i e with
  | Some res => res
  | None => Tvoid
  end.

Fixpoint array_at' (sh: Share.t) (t: type) (length: Z) (P: Z -> reptype t -> val -> mpred) (pos: Z) (v: list (reptype t)) : val -> mpred :=
match v with
| nil => if (Zeq_bool length 0) then fun _ => emp else FF
| hd :: tl => (P pos hd) * (array_at' sh t (length - 1) P (pos + sizeof t) tl)
end.

Definition alignof_hd (fld: fieldlist) : Z :=
  match fld with
  | Fnil => 1
  | Fcons _ t _ => alignof t
  end.

Fixpoint data_at' (sh: Share.t) (e: type_id_env) (t1: type): Z -> reptype t1 -> val -> mpred :=
  match t1 as t return (Z -> reptype t -> val -> mpred) with
  | Tvoid => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tarray t z a => array_at' sh t z (data_at' sh e t)
  | Tfunction t t0 => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tstruct i f a => sfieldlist_at' sh e (alignof t1) f
  | Tunion i f a => ufieldlist_at' sh e (alignof t1) f
  | Tcomp_ptr i a => at_offset2 (mapsto sh (Tpointer (look_up_ident_default i e) a))
  | _ => at_offset2 (mapsto sh t1) (* All these C types are by value types *)
  end
with sfieldlist_at' (sh: Share.t) (e: type_id_env) (alignment: Z) (flds: fieldlist) (pos: Z) : reptype_structlist flds -> val -> mpred :=
match flds as f return reptype_structlist f -> val -> mpred with
| Fnil => fun _ p => !!(isptr p) && emp (* empty struct case *)
| Fcons i t flds0 =>
    fun (v : reptype_structlist (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          (is_Fnil flds0 = b ->
           (if b
            then reptype t
            else (reptype t * reptype_structlist flds0)%type) -> val -> mpred)
       then
        fun (_ : is_Fnil flds0 = true) (v0 : reptype t) =>
          withspacer sh (pos + sizeof t) alignment (data_at' sh e t pos v0)
       else
        fun (_ : is_Fnil flds0 = false) (v0 : reptype t * reptype_structlist flds0) =>
          withspacer sh (pos + sizeof t) (alignof_hd flds0) (data_at' sh e t pos (fst v0)) *
          (sfieldlist_at' sh e alignment flds0 (align (pos + sizeof t) (alignof_hd flds0)) (snd v0)))
   eq_refl v
end
with ufieldlist_at' (sh: Share.t) (e: type_id_env) (alignment: Z) (flds: fieldlist) (pos: Z) {struct flds}: reptype_unionlist flds -> val -> mpred :=
match flds as f return (reptype_unionlist f -> val -> mpred) with
| Fnil => fun _ p => !!(isptr p) && emp (* empty union case *)
| Fcons i t flds0 => fun v : (reptype t) + (reptype_unionlist flds0) =>
  match v with
  | inl v_hd => 
    withspacer sh (pos + sizeof t) alignment (data_at' sh e t pos v_hd)
  | inr v_tl =>
    if is_Fnil flds0
    then fun _ => FF
    else ufieldlist_at' sh e alignment flds0 pos v_tl
  end
end.

Definition data_at (sh: Share.t) (t: type) := data_at' sh empty_ti t 0.

Definition data_at_ (sh: Share.t) (t: type) := data_at sh t (default_val _).

Lemma data_at'_lemma: forall (sh: Share.t) (e1 e2: type_id_env) (t: type), data_at' sh e1 t = data_at' sh e2 t.
Proof.
  intros.
  apply (type_mut (fun t => data_at' sh e1 t = data_at' sh e2 t) (fun _ => True) (fun flds => forall alignment: Z, sfieldlist_at' sh e1 alignment flds = sfieldlist_at' sh e2 alignment flds /\ ufieldlist_at' sh e1 alignment flds = ufieldlist_at' sh e2 alignment flds)); intros; try reflexivity. (* Happily, Tcomp_ptr case is solved by reflexivity automatically. *)
  + simpl. rewrite H. reflexivity. (* About array *)
  + simpl. destruct (H (alignof (Tstruct i f a))). exact H0. (* About struct *)
  + simpl. destruct (H (alignof (Tstruct i f a))). exact H1. (* About union *)
  + simpl. split; reflexivity.  (* Fnil case of fieldlist induction *)
  + destruct (H0 alignment). simpl. split. (* Fcons case of fieldlist induction *)
    rewrite H, H1. reflexivity.
    rewrite H, H2. reflexivity.
Qed.

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

Lemma field_offset_nested_field_offset: forall i f a id ofs, nested_field_offset (id :: nil) (Tstruct i f a) = Some ofs <-> field_offset id f = Errors.OK ofs.
Proof.
  intros.
  unfold nested_field_offset.
  simpl.
  pose proof field_offset_field_type_match id f.
  destruct (field_offset id f), (field_type id f); simpl in *; split; intros.
  - inversion H0; reflexivity.
  - inversion H0; reflexivity.
  - inversion H0.
  - inversion H.
  - inversion H0.
  - inversion H.
  - inversion H0.
  - inversion H0.
Qed.

Lemma field_offset_nested_field_offset2: forall i f a id ofs, field_offset id f = Errors.OK ofs -> nested_field_offset2 (id :: nil) (Tstruct i f a) = ofs.
Proof.
  intros.
  unfold nested_field_offset2.
  simpl.
  pose proof field_offset_field_type_match id f.
  destruct (field_offset id f), (field_type id f); simpl in *.
  - inversion H; reflexivity.
  - inversion H0.
  - inversion H0.
  - inversion H.
Qed.

Lemma nested_field_offset2_field_offset: forall i f a id ofs, nested_field_offset2 (id :: nil) (Tstruct i f a) = ofs /\ ofs <> 0 -> field_offset id f = Errors.OK ofs.
Proof.
  unfold nested_field_offset2.
  intros.
  simpl.
  pose proof field_offset_field_type_match id f. 
  simpl in H. destruct (field_offset id f), (field_type id f); simpl in *; destruct H.
  - subst; reflexivity.
  - inversion H0.
  - inversion H0.
  - congruence.
Qed.

Lemma field_type_nested_field_type2: forall i f a id t, field_type id f = Errors.OK t -> nested_field_type2 (id :: nil) (Tstruct i f a) = t.
Proof.
  intros.
  unfold nested_field_type2.
  simpl.
  pose proof field_offset_field_type_match id f.
  destruct (field_offset id f), (field_type id f); simpl in *.
  - inversion H; reflexivity.
  - inversion H0.
  - inversion H0.
  - inversion H.
Qed.

Lemma nested_field_type2_field_type: forall i f a id t, nested_field_type2 (id :: nil) (Tstruct i f a) = t /\ t <> Tvoid -> field_type id f = Errors.OK t.
Proof.
  unfold nested_field_type2.
  intros.
  simpl.
  pose proof field_offset_field_type_match id f. 
  simpl in H. destruct (field_offset id f), (field_type id f); simpl in *; destruct H.
  - subst; reflexivity.
  - inversion H0.
  - inversion H0.
  - congruence.
Qed.

(************************************************

Definition of fieldlist_no_replicate

************************************************)

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

Lemma fieldlist_app_in: forall f1 f2 x, fieldlist_in x f2 = true -> fieldlist_in x (fieldlist_app f1 f2) = true.
Proof.
  intros.
  induction f1; simpl.
  + exact H.
  + if_tac.
    reflexivity.
    exact IHf1.
Qed.

Lemma fieldlist_no_replicate_fact: forall (f1 f2: fieldlist), fieldlist_no_replicate (fieldlist_app f1 f2) = true -> forall x: ident, fieldlist_in x f2 = true -> fieldlist_in x f1 = false.
Proof.
  intros.
  induction f1; simpl in *.
  + reflexivity.
  + destruct (Pos.eqb x i) eqn:Heq.
    - apply Peqb_true_eq in Heq.
      subst x.
      apply (fieldlist_app_in f1) in H0.
      rewrite H0 in H.
      inversion H.
    - apply eq_sym, andb_true_eq in H; destruct H as [_ ?]. apply eq_sym in H.
      exact (IHf1 H).
Qed.

Lemma field_type_with_witness: forall i t f' f, fieldlist_no_replicate (fieldlist_app f' (Fcons i t f)) = true -> field_type i (fieldlist_app f' (Fcons i t f)) = Errors.OK t.
Proof.
  intros.
  assert (field_type i (Fcons i t f) = Errors.OK t).
    simpl. if_tac; [reflexivity | congruence].
  assert (fieldlist_in i (Fcons i t f) = true). 
    simpl. rewrite (Pos.eqb_refl i). reflexivity.
  remember (Fcons i t f) as f''; clear Heqf'' f.
  pose proof fieldlist_no_replicate_fact f' f'' H i H1.
  induction f'.
  + exact H0.
  + simpl in *.
    destruct (Pos.eqb i i0) eqn:Heq; [inversion H2|].
    apply Pos.eqb_neq in Heq.
    destruct (ident_eq i i0); [congruence| clear n].
    apply eq_sym, andb_true_eq in H; destruct H as [_ ?]. apply eq_sym in H.
    exact (IHf' H H2).
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

(************************************************

Definition of nested_reptype_structlist, nested_data_at, nested_sfieldlist_at

************************************************)

Fixpoint nested_reptype_structlist (ids: list ident) (t: type) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons i _ fld' =>
    if (is_Fnil fld')
    then reptype (nested_field_type2 (i :: ids) t)
    else prod (reptype (nested_field_type2 (i :: ids) t)) (nested_reptype_structlist ids t fld')
  end.

Fixpoint nested_reptype_unionlist (ids: list ident) (t: type) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons i _ fld' => sum (reptype (nested_field_type2 (i :: ids) t)) (nested_reptype_unionlist ids t fld')
  end.

Lemma nested_reptype_lemma: forall ids t t0, nested_field_type ids t = Some t0 -> reptype t0 = reptype (nested_field_type2 ids t).
Proof.
  unfold nested_field_type, nested_field_type2.
  intros.
  destruct (nested_field_rec ids t) as [(ofs', t')|] eqn:HH.
  + inversion H.
    reflexivity.
  + inversion H.
Qed.

Lemma nested_reptype_structlist_lemma: forall ids t i f a, nested_field_type ids t = Some (Tstruct i f a) -> fieldlist_no_replicate f = true -> reptype_structlist f = nested_reptype_structlist ids t f.
Proof.
  unfold nested_field_type.
  intros.
  destruct (nested_field_rec ids t) as [(ofs', t')|] eqn:HH; inversion H; clear H.
  subst t'.
  remember f as f'; rewrite Heqf' in HH, H0.
  assert (Hprefix: exists f'', fieldlist_app f'' f' = f). exists Fnil. subst f'. reflexivity.
  clear Heqf'.
  induction f'.
  + reflexivity.
  + destruct Hprefix as [f'' ?]. rewrite <- H in H0.
    pose proof field_type_with_witness _ _ _ _ H0.
    simpl. destruct f'.
    - simpl. 
      apply nested_reptype_lemma.
      unfold nested_field_type.
      simpl.
      rewrite HH.
      pose proof field_offset_field_type_match i0 f as Hmatch.
      destruct (field_offset i0 f), (field_type i0 f) eqn:Heq; try inversion Hmatch; clear Hmatch; subst f; rewrite H1 in Heq; inversion Heq; reflexivity.
    - destruct (is_Fnil (Fcons i1 t1 f')) eqn:Heq; [simpl in Heq; congruence| clear Heq].
      rewrite (nested_reptype_lemma (i0 :: ids) t t0).
      rewrite IHf'.
      reflexivity.
      * exists (fieldlist_app f'' (Fcons i0 t0 Fnil)).
        rewrite <- fieldlist_app_Fcons.
        exact H.
      * unfold nested_field_type.
        simpl.
        rewrite HH.
      pose proof field_offset_field_type_match i0 f as Hmatch.
      destruct (field_offset i0 f), (field_type i0 f) eqn:Heq; try inversion Hmatch; clear Hmatch; subst f; rewrite H1 in Heq; inversion Heq; reflexivity.
Qed.

Lemma nested_reptype_structlist_lemma2: forall ids t i f a, nested_field_type2 ids t = Tstruct i f a -> fieldlist_no_replicate f = true -> reptype (nested_field_type2 ids t) = nested_reptype_structlist ids t f.
Proof.
  intros.
  rewrite H.
  assert (nested_field_type ids t = Some (Tstruct i f a)).
  unfold nested_field_type, nested_field_type2 in *.
  destruct (nested_field_rec ids t) as [(?, ?)|].
  rewrite H. reflexivity.
  inversion H.
  apply (nested_reptype_structlist_lemma _ _ i f a); assumption.
Qed.

Lemma nested_reptype_unionlist_lemma: forall ids t i f a, nested_field_type ids t = Some (Tunion i f a) -> fieldlist_no_replicate f = true -> reptype_unionlist f = nested_reptype_unionlist ids t f.
Proof.
  unfold nested_field_type.
  intros.
  destruct (nested_field_rec ids t) as [(ofs', t')|] eqn:HH; inversion H; clear H.
  subst t'.
  remember f as f'; rewrite Heqf' in HH, H0.
  assert (Hprefix: exists f'', fieldlist_app f'' f' = f). exists Fnil. subst f'. reflexivity.
  clear Heqf'.
  induction f'.
  + reflexivity.
  + destruct Hprefix as [f'' ?]. rewrite <- H in H0.
    pose proof field_type_with_witness _ _ _ _ H0.
    simpl. destruct f'.
    - simpl. 
      rewrite (nested_reptype_lemma (i0 :: ids) t t0); [reflexivity|].
      unfold nested_field_type.
      simpl.
      rewrite HH.
      pose proof field_offset_field_type_match i0 f as Hmatch.
      destruct (field_offset i0 f), (field_type i0 f) eqn:Heq; try inversion Hmatch; clear Hmatch; subst f; rewrite H1 in Heq; inversion Heq; reflexivity.
    - destruct (is_Fnil (Fcons i1 t1 f')) eqn:Heq; [simpl in Heq; congruence| clear Heq].
      rewrite (nested_reptype_lemma (i0 :: ids) t t0).
      rewrite IHf'.
      reflexivity.
      * exists (fieldlist_app f'' (Fcons i0 t0 Fnil)).
        rewrite <- fieldlist_app_Fcons.
        exact H.
      * unfold nested_field_type.
        simpl.
        rewrite HH.
      pose proof field_offset_field_type_match i0 f as Hmatch.
      destruct (field_offset i0 f), (field_type i0 f) eqn:Heq; try inversion Hmatch; clear Hmatch; subst f; rewrite H1 in Heq; inversion Heq; reflexivity.
Qed.

Lemma nested_reptype_unionlist_lemma2: forall ids t i f a, nested_field_type2 ids t = Tunion i f a -> fieldlist_no_replicate f = true -> reptype (nested_field_type2 ids t) = nested_reptype_unionlist ids t f.
Proof.
  intros.
  rewrite H.
  assert (nested_field_type ids t = Some (Tunion i f a)).
  unfold nested_field_type, nested_field_type2 in *.
  destruct (nested_field_rec ids t) as [(?, ?)|].
  rewrite H. reflexivity.
  inversion H.
  simpl.
  apply (nested_reptype_unionlist_lemma _ _ i f a); assumption.
Qed.

Definition nested_data_at (sh: Share.t) (ids: list ident) (t1: type) (v: reptype (nested_field_type2 ids t1)) : val -> mpred := data_at' sh empty_ti (nested_field_type2 ids t1) (nested_field_offset2 ids t1) v.

Fixpoint nested_sfieldlist_at (sh: Share.t) (ids: list ident) (t1: type) (flds: fieldlist) (v: nested_reptype_structlist ids t1 flds) : val -> mpred := 
  match flds as f return (nested_reptype_structlist ids t1 f -> val -> mpred) with
  | Fnil => fun _ p => (!! isptr p) && emp
  | Fcons i t flds0 =>
    fun (v : nested_reptype_structlist ids t1 (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          (is_Fnil flds0 = b ->
           (if b
            then reptype (nested_field_type2 (i :: ids) t1)
            else ((reptype (nested_field_type2 (i :: ids) t1) *
        nested_reptype_structlist ids t1 flds0)%type)) -> val -> mpred)
       then
        fun (_ : is_Fnil flds0 = true) (v0: reptype (nested_field_type2 (i :: ids) t1)) =>
          withspacer sh (nested_field_offset2 (i :: ids) t1 + sizeof (nested_field_type2 (i :: ids) t1)) (alignof (nested_field_type2 ids t1)) (nested_data_at sh (i :: ids) t1 v0)
       else
        fun (_ : is_Fnil flds0 = false) (v0: ((reptype (nested_field_type2 (i :: ids) t1) *
        nested_reptype_structlist ids t1 flds0)%type)) =>
          withspacer sh (nested_field_offset2 (i :: ids) t1 + sizeof (nested_field_type2 (i :: ids) t1)) (alignof_hd flds0) (nested_data_at sh (i :: ids) t1 (fst v0)) *
          (nested_sfieldlist_at sh ids t1 flds0 (snd v0)))
   eq_refl v
  end v.

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

Lemma nested_data_at_Tstruct: forall sh ids t i f a v1 v2 (H1: nested_field_type2 ids t = Tstruct i f a) (H2: fieldlist_no_replicate f = true), (eq_rect_r (fun x => x) v2 (nested_reptype_structlist_lemma2 _ _ _ _ _ H1 H2)  = v1) -> nested_data_at sh ids t v1 = nested_sfieldlist_at sh ids t f v2.
Proof.
  intros.
  remember (nested_reptype_structlist_lemma2 ids t i f a H1 H2) as Heq; clear HeqHeq.
  unfold nested_data_at.
  revert Heq v1 H; rewrite H1; simpl (reptype (Tstruct i f a)); simpl data_at'; intros.
  destruct f; [reflexivity|].
  remember f as f'.
  rewrite Heqf' in H1, H2. pattern f' at 1. rewrite Heqf'.
  assert (exists f'', fieldlist_app f'' (Fcons i0 t0 f') = (Fcons i0 t0 f)); [exists Fnil; subst; reflexivity|].
  rewrite <- (nested_field_offset2_hd i0 t0 ids t i f a H1).
  pose proof (nested_field_type2_hd i0 t0 ids t i f a H1).  
  clear Heqf'.
  remember (Fcons i0 t0 f) as f0; clear Heqf0 f; rename f0 into f.
  induction f'; destruct H0 as [f'' ?].
  + simpl.
    rewrite H3, H1.
    replace (nested_data_at sh (i0 :: ids) t v2) with (data_at' sh empty_ti t0 (nested_field_offset2 (i0 :: ids) t) v1); [reflexivity|].
    unfold nested_data_at.
    revert Heq v2 H; simpl; rewrite H3; intros.
    unfold eq_rect_r in H; rewrite <- eq_rect_eq in H.
    rewrite H.
    reflexivity.
  + replace (sfieldlist_at' sh empty_ti (alignof (Tstruct i f a))
     (Fcons i0 t0 (Fcons i1 t1 f')) (nested_field_offset2 (i0 :: ids) t) v1) with
     (withspacer sh ((nested_field_offset2 (i0 :: ids) t) + sizeof t0) (alignof_hd (Fcons i1 t1 f')) (data_at' sh empty_ti t0 (nested_field_offset2 (i0 :: ids) t) (fst v1)) *
     sfieldlist_at' sh empty_ti (alignof (Tstruct i f a)) (Fcons i1 t1 f')
     (align (nested_field_offset2 (i0 :: ids) t + sizeof t0) (alignof_hd (Fcons i1 t1 f'))) (snd v1)) by reflexivity.
    replace (nested_sfieldlist_at sh ids t (Fcons i0 t0 (Fcons i1 t1 f')) v2) with
      (withspacer sh (nested_field_offset2 (i0 :: ids) t + sizeof (nested_field_type2 (i0 :: ids) t)) (alignof_hd (Fcons i1 t1 f')) (nested_data_at sh (i0 :: ids) t (fst v2)) *
        nested_sfieldlist_at sh ids t (Fcons i1 t1 f') (snd v2)) by reflexivity.
    pattern (nested_field_type2 (i0 :: ids) t) at 1; rewrite H3.
admit.
Qed.
      
(*
Lemma field_at_offset_zero:
  forall sh ty id v v', 
   field_at sh ty id v' (offset_val (Int.repr 0) v) =
   field_at sh ty id v' v.
Proof.
 intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_at_offset_zero: norm.
*)

Lemma lower_sepcon_val:
  forall (P Q: val->environ->mpred) v, 
  ((P*Q) v) = (P v * Q v).
Proof. reflexivity. Qed.

Definition opaque_sepcon := @sepcon (val->mpred) _ _.
Global Opaque opaque_sepcon.
Definition opaque_emp := @emp (val->mpred) _ _.
Global Opaque opaque_emp.

Lemma distribute_envtrans:
  forall A (P Q: A -> mpred) (J: environ -> A),
   @liftx (Tarrow A (LiftEnviron mpred)) 
   (@sepcon (A -> mpred) _ _ P Q) J = 
   (@liftx (Tarrow A (LiftEnviron mpred)) P J 
    * @liftx (Tarrow A (LiftEnviron mpred)) Q J ).
Proof. reflexivity. Qed.
Hint Rewrite distribute_envtrans: norm.

Lemma distribute_lifted_sepcon:
 forall A F G v,
  (@sepcon (A -> mpred) _ _ F G v) = @sepcon mpred _ _ (F v) (G v).
Proof. reflexivity. Qed.

(**********************************************

Here, we need to think about how to use array in examples.

**********************************************)

(*
Definition array_at (t: type) (sh: Share.t) (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) : mpred :=
           !! isptr v && rangespec lo hi (fun i => data_at sh t  (f i) (add_ptr_int t v i)).

Definition array_at_ t sh lo hi := array_at t sh (fun _ => default_val t) lo hi.
*)

Lemma offset_val_preserve_isptr: forall p pos, !! (isptr (offset_val pos p)) |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; apply derives_refl.
Qed.

Lemma at_offset2_preserve_isptr: forall {A: Type} P pos (v: A), (forall p, P p v |-- !!(isptr p)) -> (forall p, at_offset2 P pos v p |-- !!(isptr p)).
Proof.
  intros.
  unfold at_offset2, at_offset', at_offset.
  destruct pos.
  + exact (H p).
  + eapply derives_trans. exact (H _). apply offset_val_preserve_isptr.
  + eapply derives_trans. exact (H _). apply offset_val_preserve_isptr.
Qed.

Lemma withspacer_preserve_isptr: forall sh pos alignment P, (forall p, P p |-- !! (isptr p)) -> (forall p, withspacer sh pos alignment P p |-- !! (isptr p)).
Proof.
  intros.
  rewrite withspacer_spacer.
  simpl; rewrite sepcon_comm. 
  apply (right_is_prop (!!isptr p) (P p) _); [apply prop_is_prop|].
  apply H.
Qed.

Lemma data_at'_isptr:
  forall sh e t pos v p, data_at' sh e t pos v p = !!(isptr p) && data_at' sh e t pos v p.
Proof.
  intros.
  apply pred_ext; normalize.
  apply andp_right; auto.
  revert p.
  apply (type_mut (fun (t: type) => forall pos v p, (data_at' sh e t pos v p |-- !!(isptr p))) (fun _ => True) (fun flds => (forall alignment pos v p, sfieldlist_at' sh e alignment flds pos v p |-- !!(isptr p)) /\ (forall alignment pos v p, ufieldlist_at' sh e alignment flds pos v p |-- !!(isptr p)))); intros; auto; simpl; 
  try (apply at_offset2_preserve_isptr; intros; apply mapsto_local_facts);
  try (apply at_offset2_preserve_isptr; intros; apply memory_block_local_facts).
  + admit. (* Array case *)
  + destruct H. apply H. (* struct case *)
  + destruct H. apply H0. (* union case *)
  + split; intros. (* Fnil case of fieldlist induction *)
    - normalize.
    - destruct (Zeq_bool alignment 0); normalize.
  + destruct H0. split; intros.
    - destruct (is_Fnil).
      * apply withspacer_preserve_isptr; intros. apply H.
      * apply (right_is_prop (!!isptr p) ( withspacer sh (pos0 + sizeof t0) (alignof_hd f)
     (data_at' sh e t0 pos0 (fst v0)) p)); [apply prop_is_prop|].
        apply withspacer_preserve_isptr; intros. apply H.
    - destruct v0.
      * apply withspacer_preserve_isptr; intros. apply H.
      * if_tac. normalize. apply H1.
Qed.

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = !!(isptr p) && data_at sh t v p.
Proof.
  intros.
  unfold data_at.
  apply data_at'_isptr.
Qed.

Lemma data_at__isptr:
  forall sh t p, data_at_ sh t p = !!(isptr p) && data_at_ sh t p.
Proof.
  intros.
  unfold data_at_.
  apply data_at_isptr.
Qed.

Lemma mapsto_offset_zero:
  forall sh t v1 v2, 
    mapsto sh t (offset_val (Int.repr 0) v1) v2 =
    mapsto sh t v1 v2.
Proof.
  unfold mapsto.
  intros.
  destruct v1; try solve [simpl; auto].
  unfold offset_val.
  rewrite Int.add_zero. auto.
Qed.

Lemma data_at_tint: forall sh v2 v1,
  data_at sh tint v2 v1 = mapsto sh tint v1 v2.
Proof.
  intros. reflexivity. 
Qed.

Lemma spacer_offset_zero:
  forall sh pos n v, spacer sh pos n (offset_val (Int.repr 0) v) = spacer sh pos n v.
Proof.
  intros;
  unfold spacer.
  destruct (Z.eq_dec (align pos n - pos) 0);  auto.
  repeat rewrite at_offset'_eq; 
  try rewrite offset_offset_val; try  rewrite Int.add_zero_l; auto.
  apply memory_block_offset_zero.
Qed.

Fixpoint typecount (t: type) : nat :=
  match t with
  | Tstruct _ f _ => S (typecount_fields f)
  | Tarray t' _ _ => S (typecount t')
  | _ => 1%nat
  end
with typecount_fields (f: fieldlist) : nat :=
  match f with
  | Fnil => 1%nat
  | Fcons _ t f' => (typecount t + typecount_fields f')%nat
  end.

Lemma  typecount_fields_pos: forall f, (typecount_fields f > 0)%nat.
Proof.
  induction f; simpl; intros. auto.
  omega.
Qed.

Lemma typecount_pos: forall t, (typecount t > 0)%nat.
Proof.
  destruct t; simpl; auto; omega.
Qed.

(*
(****** It is not used anywhere else. *********)

Definition fields_mapto_ sh pos t f v :=
  structfieldsof sh t f pos pos (struct_default_val f) v.

Lemma fields_mapto__offset_zero:
  forall sh pos t f v, fields_mapto_ sh pos t f (offset_val (Int.repr 0) v) =
                           fields_mapto_ sh pos t f v.
Proof.
  Admitted.
Qed.
*)

Lemma at_offset'_zero:
  forall P, 
    (forall v, P (offset_val (Int.repr 0) v) = P v) ->
  forall ofs v,
    at_offset' P ofs (offset_val (Int.repr 0) v) = at_offset' P ofs v.
Proof.
  intros.
  repeat rewrite at_offset'_eq. 
  rewrite offset_offset_val. rewrite Int.add_zero_l. auto. auto.
  f_equal.  rewrite offset_offset_val. reflexivity.
Qed.

Lemma FF_orp: forall {A: Type} `{NatDed A} (P: A), FF || P = P.
Proof.
  intros.
  apply pred_ext.
  + apply orp_left.
    apply FF_left.
    apply derives_refl.
  + apply orp_right2.
    apply derives_refl.
Qed.

Definition by_value_no_alignof t :=
  match t with
  | Tint _ _ (mk_attr false None) => True
  | Tlong _ (mk_attr false None) => True
  | Tfloat _ (mk_attr false None) => True
  | Tpointer _ (mk_attr false None) => True
  | _ => False
  end.

Lemma memory_block_mapsto_:
  forall n sh t v, 
  by_value_no_alignof t ->
  n = sizeof t ->
  memory_block sh (Int.repr n) v = mapsto_ sh t v.
Proof.
  Admitted.

(************************************************

Originally, this is proved as follows. It depends on some admitted lemma.
However, I think it is not the correct approach. Memory block is defined upon
mapsto. So, we should resolve the lemma to the level of mapsto but not unfold
mapsto to make things more complicated. Now, I admitted it directly, which is
not worse than before. 

Lemma memory_block_address_mapsto:
  forall n sh ch b i,
  n = Memdata.size_chunk ch ->
  memory_block sh (Int.repr n) (Vptr b i) =
 !!False && address_mapsto ch Vundef (Share.unrel Share.Lsh sh)
  (Share.unrel Share.Rsh sh) (b, Int.unsigned i)
|| !!(Vundef = Vundef) &&
   (EX  v2' : val,
    address_mapsto ch v2' (Share.unrel Share.Lsh sh)
      (Share.unrel Share.Rsh sh) (b, Int.unsigned i)).
Proof.
  intros.
  change (!!False) with FF.
  rewrite FF_andp.
  rewrite FF_orp.
  assert (!!(Vundef = Vundef) = TT); [apply pred_ext; normalize|].
  rewrite H0; clear H0.
  rewrite TT_andp.
Admitted.

Lemma memory_block_mapsto_:
  forall n sh t v, 
   by_value_no_alignof t ->
   n = sizeof t ->
   memory_block sh (Int.repr n) v = mapsto_ sh t v.
Proof.
  intros. subst n.
  pose proof (sizeof_pos t).
  destruct t; try contradiction; (* only by_value type left *)
  destruct a as [[|] [|]]; try contradiction; (* only no_alignof type left *)
  simpl;
 unfold mapsto_, mapsto; simpl;
 try (destruct i,s); try destruct f; 
 rewrite memory_block_isptr by apply H0;
 destruct v; simpl; try  apply FF_andp; 
 rewrite prop_true_andp by auto;
 (apply memory_block_address_mapsto;  try reflexivity).
Qed.

************************************************)

Lemma spacer_memory_block:
  forall sh pos a v, isptr v -> 
 spacer sh pos a v = memory_block sh (Int.repr (align pos a - pos)) (offset_val (Int.repr pos) v).
Proof.
  intros.
  destruct v; inv H.
  unfold spacer.
  destruct (Z.eq_dec (align pos a - pos) 0);
  try solve [rewrite e; simpl offset_val; rewrite memory_block_zero; auto].
  unfold at_offset'.
  destruct pos; auto.
  unfold offset_val; rewrite Int.add_zero; auto.
Qed.

Definition no_attr (a: attr) :=
  andb (negb (attr_volatile a))
  match attr_alignas a with  None => true | _ => false end.

Definition no_attr_e: forall a, no_attr a = true -> a=noattr.
Proof.
  intros. destruct a. destruct attr_volatile; inv H.
  destruct attr_alignas; inv H1.
  reflexivity.
Qed.

Fixpoint no_attr_type (t: type) : bool :=
  match t with 
  | Tint _ _ a => no_attr a
  | Tlong _ a => no_attr a
  | Tfloat _ a => no_attr a
  | Tpointer _ a => no_attr a
  | Tarray t _ a => andb (no_attr_type t) (no_attr a)
  | Tstruct _ flds a => andb (no_attr_fields flds)  (no_attr a)
  | Tunion _ flds a => andb (no_attr_fields flds)  (no_attr a)
  | Tcomp_ptr _ a =>  no_attr a
  | _ => true
  end
with no_attr_fields (f: fieldlist) : bool :=
  match f with 
  | Fnil => true 
  | Fcons _ t f' => andb (no_attr_type t) (no_attr_fields f')
  end.

Lemma no_attr_type_nonvol: forall t, no_attr_type t = true -> type_is_volatile t = false.
Proof.
  intros. destruct t; simpl in *; try apply no_attr_e in H; subst; simpl; try reflexivity.
  destruct i,s; reflexivity. destruct f; reflexivity.
Qed.

Lemma align_1: forall n, align n 1 = n.
Proof.  intros; unfold align. rewrite Z.div_1_r. rewrite Z.mul_1_r. omega.
Qed.

Lemma memory_block_typed': forall sh e pos ty b ofs, 
  no_attr_type ty = true ->
  spacer sh pos (alignof ty) (Vptr b ofs) *
  memory_block sh (Int.repr (sizeof ty)) (offset_val (Int.repr (align pos (alignof ty))) (Vptr b ofs) )
  = data_at' sh e ty pos (default_val ty) (Vptr b ofs).
(*with memory_block_fields: forall sh pos t fld b ofs,
 no_attr_fields fld = true ->
  spacer sh (sizeof_struct fld pos) (alignof_fields fld) (Vptr b ofs) 
  * memory_block sh (Int.repr (sizeof_struct fld pos)) (Vptr b ofs)
  =   memory_block sh (Int.repr pos) (Vptr b ofs) * fields_mapto_ sh pos t fld (Vptr b ofs).
*)
Proof.
  Admitted.

(*
Require Import progs.nest2.

Goal forall a b c, data_at Ews t_struct_b (a, (b,c))= TT.
intros.
extensionality p.
unfold data_at.
simpl data_at'.
Opaque at_offset2.
simpl.
Transparent alignof.
simpl alignof.
simpl align.
simpl.
unfold withspacer.
simpl align.
Opaque spacer.
simpl.
repeat rewrite <- sepcon_assoc.
SearchAbout mapsto FF.
Locate field_at_conflict.
Print res_predicates.address_mapsto.
Locate jam.
Print mapsto.
Print access_mode.
Print compcert.common.Memdata.encode_val.
Locate single_of_bits.
Print compcert.lib.Floats.Float.
Print compcert.common.Memdata.memval.
Print Memdata.proj_bytes.
Print val.
Print res_predicates.spec.
simpl withspacer.
*)

(************************************************

reptype is not defined in a quite beautiful way because of the if operation 
inside it. However, due to the following limitations, the current definition
is the best available choice.

1. We want a compact representation of reptype result and a compact form of
expansion of data_at, i.e. no unit in reptype result of non-empty struct and
no emp clause existing in the expansion of data_at. So, vst does not use the
following simplest approach.

  match fld with
  | Fnil => unit
  | Fcons id ty fld' => prod (reptype ty) (reptype_structlist fld')
  end

2. If using struct recursive definition in reptype like this, in which reptype
recursively is called on 1st level match variable fld' but not any 2nd level 
stuff.

  match fld with
  | Fnil => unit
  | Fcons id ty fld' => 
    match fld' as fld0 return Type with
    | Fnil => reptype ty
    | Fcons id0 ty0 fld0' => prod (reptype ty) (reptype_structlist fld')
    end
  end

or like this

  match fld with
  | Fnil => unit
  | Fcons id ty Fnil => reptype ty
  | Fcons id ty fld' => prod (reptype ty) (reptype_structlist fld')
  end

Then, we would be forced to do type casting when defining data_at. In detail,
match command will destruct a fieldlist into "Fnil", "Fcons _ Fnil _" and
"Fcons _ (Fcons i t f) _", then an equivalence between (Fcons i t f) and fld'
is needed.

3. If reptype is recursively called on (Fcons i t f), we have to use well-found
recursive but not structure recursive. However, Coq does not allow users to use 
well-found recursive on manual recursive functions.

4. If reptype is defined in a well-type recursive style (thus, it has to be non-
manually recursive) (this definition code is long; thus I put it afterwards), 
a match command does not do enough type calculation. As a result, explicit type
casting is needed again, i.e. the following piece of code does not compile. 

  Function test (t: type) (v: reptype t) {measure hry t}: nat :=
    match t as t0 return reptype t0 -> nat with
    | Tvoid => fun (v: unit) => 0%nat
    | Tarray t1 sz a => fun (v: list (reptype t1)) => 2%nat
    | _ => fun _ => 1%nat
    end v.

Though, computation by "Eval compute in" or "simpl" works quite well.

5. Another choice is start induction from the 2nd element but not the 1st
element. However, neither one of the following definition works. The former 
choice requires explicit type casting when defining data_at. The latter choice
does not compile itself.

  Fixpoint reptype (ty: type) : Type :=
    match ty with
    | ...
    | Tstruct id Fnil a => unit
    | Tstruct id (Fcons i t fld) a => reptype_structlist_cons (reptype t) fld
    end
  with reptype_structlist_cons (T: Type) (fld: fieldlist): Type :=
    match fld with
    | Fnil => T
    | Fcons i t fld' => prod T (reptype_structlist_cons (reptype t) fld')
    end.

  Fixpoint reptype (ty: type) : Type :=
    match ty with
    | ...
    | Tstruct id Fnil a => unit
    | Tstruct id (Fcons i t fld) a => reptype_structlist_cons t fld
    end
  with reptype_structlist_cons (t: type) (fld: fieldlist): Type :=
    match fld with
    | Fnil => T
    | Fcons i ty fld' => prod (reptype t) (reptype_structlist_cons ty fld')
    end.


(* (**** Code of Choice 4 ****)
Open Scope nat.

Fixpoint hry (t: type) : nat :=
  match t with
  | Tvoid => 0
  | Tint _ _ _ => 0
  | Tlong _ _ => 0
  | Tfloat _ _ => 0
  | Tpointer t1 a => 0
  | Tarray t1 sz a => (hry t1) + 1
  | Tfunction t1 t2 => 0
  | Tstruct id fld a => (hry_fields fld) + 1
  | Tunion id fld a => (hry_fields fld) + 1
  | Tcomp_ptr id a => 0
  end
with hry_fields (fld: fieldlist): nat :=
  match fld with
  | Fnil => 0
  | Fcons i t fld' => (hry t) + (hry_fields fld') + 1
  end.

Close Scope nat.

Function reptype (ty: type) {measure hry ty}: Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => val
  | Tlong _ _ => val
  | Tfloat _ _ => val
  | Tpointer t1 a => val
  | Tarray t1 sz a => list (reptype t1)
  | Tfunction t1 t2 => unit
  | Tstruct id Fnil a => unit
  | Tstruct id (Fcons i t Fnil) a => reptype t
  | Tstruct id (Fcons i t fld) a => prod (reptype t) (reptype (Tstruct id fld a))
  | Tunion id fld a => unit
  | Tcomp_ptr id a => val
  end
.
Proof.
  + intros. 
    simpl.
    omega.
  + intros.
    simpl.
    omega.
  + intros.
    simpl.
    omega.
  + intros. 
    simpl.
    omega.
Defined.

Eval compute in (reptype (Tstruct 2%positive (Fcons 1%positive Tvoid (Fcons 1%positive Tvoid Fnil)) noattr)).

Lemma foo: (reptype (Tstruct 2%positive (Fcons 1%positive Tvoid (Fcons 1%positive Tvoid Fnil)) noattr)) = (unit * unit)%type.
Proof.
  reflexivity.
Qed.
*)


************************************************)
