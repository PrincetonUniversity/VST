Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Lemma memory_block_zero: forall sh b z, memory_block sh (Int.repr 0) (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  change (Int.repr 0) with Int.zero.
  rewrite Int.unsigned_zero.
  change (nat_of_Z 0) with (0%nat).
  unfold memory_block'.
  reflexivity.
Qed.

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

Hint Rewrite memory_block_zero: norm.

Global Opaque memory_block.

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

Definition str_id_env: Type := PTree.t type.

Definition look_up_ident_default (i: ident) (e: str_id_env) : type :=
  match PTree.get i e with
  | Some res => res
  | None => Tvoid
  end.

(************************************************

reptype is not defined in a quite beautiful way now. However, there seems no
better choice. The situation is explained at the end of this file. When Coq
releases a new version in the future, maybe we can rewrite it in a better way.

************************************************)


(************************************************

Always assume in arguments of data_at', array_at', sfieldlist_at', ufieldlist_
at' has argument pos with alignment criterian. So, spacers are only added after
fields of structs or unions.

A new array_at' is used here. But it worths discussion which version is better.

Personally, I don't know why "function" case looks like this. I just copy it
from previous version.

************************************************)

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

Fixpoint data_at' (sh: Share.t) (e: str_id_env) (t1: type): Z -> reptype t1 -> val -> mpred :=
  match t1 as t return (Z -> reptype t -> val -> mpred) with
  | Tvoid => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tarray t z a => array_at' sh t z (data_at' sh e t)
  | Tfunction t t0 => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tstruct i f a => sfieldlist_at' sh e (alignof t1) f
  | Tunion i f a => ufieldlist_at' sh e (alignof t1) f
  | Tcomp_ptr i a => at_offset2 (mapsto sh (Tpointer (look_up_ident_default i e) a))
  | _ => at_offset2 (mapsto sh t1) (* All these C types are by value types *)
  end
with sfieldlist_at' (sh: Share.t) (e: str_id_env) (alignment: Z) (flds: fieldlist) (pos: Z) : reptype_structlist flds -> val -> mpred :=
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
with ufieldlist_at' (sh: Share.t) (e: str_id_env) (alignment: Z) (flds: fieldlist) (pos: Z) {struct flds}: reptype_unionlist flds -> val -> mpred :=
match flds as f return (reptype_unionlist f -> val -> mpred) with
| Fnil => 
  if (Zeq_bool alignment 0)
  then fun _ p => !!(isptr p) && emp (* empty union case *)
  else fun _ => FF (* this means v in input data is ilegal *)
| Fcons i t flds0 => fun v : (reptype t) + (reptype_unionlist flds0) =>
  match v with
  | inl v_hd => 
    withspacer sh (pos + sizeof t) alignment (data_at' sh e t pos v_hd)
  | inr v_tl =>
    ufieldlist_at' sh e alignment flds0 pos v_tl
  end
end.

Definition data_at (sh: Share.t) (t: type) := data_at' sh (PTree.empty type) t 0.

Definition data_at_ (sh: Share.t) (t: type) := data_at sh t (default_val _).

Lemma data_at'_lemma: forall (sh: Share.t) (e1 e2: str_id_env) (t: type), data_at' sh e1 t = data_at' sh e2 t.
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
      * apply H1.
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
