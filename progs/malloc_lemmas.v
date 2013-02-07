Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Parameter memory_block: share -> int -> val -> mpred.
Lemma memory_block_zero: forall sh v, memory_block sh (Int.repr 0) v = emp.
Admitted.

Lemma offset_val_assoc:
  forall v i j, offset_val (offset_val v i) j = offset_val v (Int.add i j).
Proof.
intros.
unfold offset_val.
destruct v; simpl; auto.
rewrite Int.add_assoc; auto.
Qed.
Hint Rewrite offset_val_assoc: normalize.

Hint Rewrite memory_block_zero: normalize.

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Hint Rewrite int_add_repr_0_l int_add_repr_0_r : normalize.

Lemma field_storable_offset_zero:
  forall sh ty id v, 
   field_storable sh ty id (offset_val v (Int.repr 0)) =
   field_storable sh ty id v.
Proof.
 unfold field_storable; intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_storable_offset_zero: normalize.


Definition spacer (pos: Z) (alignment: Z) (v: val) : mpred :=
   memory_block Share.top (Int.repr (align pos alignment - pos))
                              (offset_val v (Int.repr pos)).

Definition withspacer (pos: Z) (alignment: Z) (v: val) (P: mpred) : mpred :=
   match align pos alignment - pos with
   | Z0 => P
   | n => memory_block Share.top (Int.repr n) (offset_val v (Int.repr pos)) * P
   end.

Lemma withspacer_spacer: forall pos alignment v P,
   withspacer pos alignment v P = spacer pos alignment v * P.
Proof.
  intros.
 unfold withspacer, spacer.
 destruct (align pos alignment - pos); auto.
 rewrite memory_block_zero, emp_sepcon; auto.
Qed.

Fixpoint malloc_assertion (pos: Z) (ty: type)  (v: val) : mpred :=
  match ty with
  | Tstruct id fld a => withspacer pos (alignof ty) v
                          (malloc_assertion_fields 0 ty fld 
                                    (offset_val v (Int.repr (align pos (alignof ty)))))
  | _ => withspacer pos (alignof ty) v
                         (memory_block Share.top (Int.repr (sizeof ty) )
                            (offset_val v (Int.repr (align pos (alignof ty)))))
  end

with malloc_assertion_fields (pos:Z) (t0: type) (flds: fieldlist) (v: val) : mpred :=
 match flds with
 | Fnil => emp
 | Fcons id ty flds' => withspacer pos (alignof ty) v 
                                     (field_storable Share.top t0 id 
                                          (offset_val v (Int.repr (align pos (alignof ty))))) * 
                                   malloc_assertion_fields pos t0 flds' v
  end.


Fixpoint reptype (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => int
  | Tfloat _ _ => float
  | Tpointer t1 a => val
  | Tarray t1 sz a => list (reptype t1)
  | Tfunction t1 t2 => unit
  | Tstruct id fld a => reptype_list prod fld
  | Tunion id fld a => reptype_list sum fld
  | Tcomp_ptr id a => unit
  end

with reptype_list (f: Type -> Type -> Type) (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => f (reptype ty) (reptype_list f fld')
  end.

Fixpoint arrayof (t: Type) (f: forall (v1: val) (v2: t),  mpred)
         (t1: type) (ofs: Z) (v1: val) (v2: list t) : mpred :=
    match v2 with
    | v::rest => f (offset_val v1 (Int.repr ofs)) v * arrayof t f t1 (ofs + sizeof t1) v1 rest
    | nil => emp
   end.

Definition maybe_field_mapsto (t: type) (sh: Share.t) (t_str: type) (id: ident) (pos: Z) (v: val) :
                     (reptype t -> mpred) -> reptype t -> mpred :=
match t as t0 return ((reptype t0 -> mpred) -> reptype t0 -> mpred) with
| Tint i s a =>
    fun (_ : reptype (Tint i s a) -> mpred) (v2'0 : reptype (Tint i s a)) =>
    field_mapsto sh t_str id (offset_val v (Int.repr pos)) (Vint v2'0)
| Tfloat f a =>
    fun (_ : reptype (Tfloat f a) -> mpred) (v2'0 : reptype (Tfloat f a)) =>
    field_mapsto sh t_str id (offset_val v (Int.repr pos)) (Vfloat v2'0)
| Tpointer t0 a =>
    fun _ =>  field_mapsto sh t_str id (offset_val v (Int.repr pos))
| Tcomp_ptr _ _ =>
    fun _ _ => field_storable sh t_str id (offset_val v (Int.repr pos))
| t' => fun (alt1 : reptype t' -> mpred)  => alt1 
end.

Fixpoint typed_mapsto (t1: type) (sh: Share.t) (pos: Z) (v: val) (v2: reptype t1) : mpred :=
match t1 as t return (t1 = t -> mpred) with
| Tvoid => emp
| Tint i s a =>
    fun H : t1 = Tint i s a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tint i s a) =>
                withspacer pos (alignof (Tint i s a)) v
                (mapsto sh (Tint i s a) (offset_val v (Int.repr (align pos (alignof t1)))) (Vint v3))) H in
    H0 v2
| Tfloat f a =>
    fun H : t1 = Tfloat f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tfloat f a) =>
                withspacer pos (alignof (Tfloat f a)) v
                (mapsto sh (Tfloat f a) (offset_val v (Int.repr (align pos (alignof t1)))) (Vfloat v3))) H in
    H0 v2
| Tpointer t a => 
    fun H : t1 = Tpointer t a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tpointer t a) =>
                withspacer pos (alignof (Tpointer t a)) v
                (mapsto sh (Tpointer t a) (offset_val v (Int.repr (align pos (alignof t1)))) v3)) H in
    H0 v2
| Tarray t z a =>
    fun H : t1 = Tarray t z a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tarray t z a) => 
                 withspacer pos (alignof t) v
                 (arrayof _ (typed_mapsto t sh (align pos (alignof t))) t 0 v v3))
        H in
    H0 v2
| Tfunction t t0 => emp
| Tstruct i f a =>
    fun H : t1 = Tstruct i f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tstruct i f a) =>
                 withspacer pos (alignof (Tstruct i f a)) v
                 (structfieldsof (Tstruct i f a) f sh (align pos (alignof t1)) v v3)) H in
    H0 v2
| Tunion i f a =>
    fun H : t1 = Tunion i f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tunion i f a) =>
                 withspacer pos (alignof (Tunion i f a)) v
         (unionfieldsof f sh (align pos (alignof t1)) v v3)) H in
    H0 v2
| Tcomp_ptr i a => 
        fun _ =>
          withspacer pos (alignof (Tcomp_ptr i a)) v
          (memory_block sh (Int.repr (sizeof (Tcomp_ptr i a))) (offset_val v (Int.repr pos)))
end eq_refl
 with
 structfieldsof (t_str: type) (flds: fieldlist) (sh: Share.t) (pos: Z) (v: val) (v2: reptype_list prod flds) : mpred :=
match flds as f0 return (flds = f0 -> mpred) with
| Fnil => fun _ : flds = Fnil => emp
| Fcons i t f0 =>
    fun H : flds = Fcons i t f0 =>
    let H0 :=
      eq_rect_r (fun flds0 : fieldlist => reptype_list prod flds0 -> mpred)
        (fun v3 : reptype_list prod (Fcons i t f0) =>
         let (v2', vr) := v3 in
            withspacer pos (alignof t) v
            (maybe_field_mapsto t sh t_str i (align pos (alignof t)) v (typed_mapsto t sh (align pos (alignof t)) v) v2') *
            structfieldsof t_str f0 sh pos v vr) H in
    H0 v2
end eq_refl
 with
unionfieldsof (flds: fieldlist) (sh: Share.t)  (pos: Z) (v: val) (v2: reptype_list sum flds) : mpred :=
match flds as f0 return (flds = f0 -> mpred) with
| Fnil => fun _ : flds = Fnil => emp
| Fcons i t f0 =>
    fun H : flds = Fcons i t f0 =>
    let H0 :=
      eq_rect_r (fun flds0 : fieldlist => reptype_list sum flds0 -> mpred)
        (fun v3 : reptype_list sum (Fcons i t f0) =>
         match v3 with
         | inl v2' => typed_mapsto t sh pos v v2'
         | inr vr =>  unionfieldsof f0 sh pos v vr 
         end) H
    in H0 v2
end eq_refl.

Lemma field_mapsto_offset_zero:
  forall sh ty id v, 
   field_mapsto sh ty id (offset_val v (Int.repr 0)) =
   field_mapsto sh ty id v.
Proof.
 unfold field_storable; intros. extensionality v2.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto_offset_zero: normalize.

Ltac simpl_malloc_assertion' T H MA :=
       unfold malloc_assertion, typed_mapsto, eq_rect_r, withspacer, align, Zmax in H;
       simpl in H; try fold T in H;
       repeat rewrite emp_sepcon in H; repeat rewrite sepcon_emp in H;
       repeat rewrite field_storable_offset_zero in H;
       repeat rewrite field_mapsto_offset_zero in H;
     subst MA.

Ltac simpl_malloc_assertion :=
    let MA := fresh "MA" in
  match goal with 
  | |- context [malloc_assertion ?N ?T ?V] =>
         remember (malloc_assertion  N T V) as MA;
         match goal with H: MA = _ |- _ => simpl_malloc_assertion' T H MA end
  | |- context [typed_mapsto ?T ?SH ?N ?V ?V'] =>
         remember (typed_mapsto T SH N V V') as MA;
         match goal with H: MA = _ |- _ => simpl_malloc_assertion' T H MA end
  end.

(* TESTING...
Require Import progs.queue.
Parameter sh: Share.t.
Parameter v: val.
Goal forall v2: reptype t_struct_elem, typed_mapsto t_struct_elem sh 0 v v2 =  emp.
intros.
simpl in v2.
destruct v2 as [i [j [[] []]]].
simpl_malloc_assertion.

*)

Lemma malloc_assert: forall ty, 
   memory_block Share.top (Int.repr (sizeof ty)) =
   malloc_assertion 0 ty.
Admitted.

Lemma memory_block_isptr:
  forall sh n v, memory_block sh n v = !! denote_tc_isptr v && memory_block sh n v.
Admitted.


