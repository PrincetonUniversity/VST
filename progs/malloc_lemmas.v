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


Definition spacer (v: val) (pos: Z) (alignment: Z) : mpred :=
   memory_block Share.top (Int.repr (align pos alignment - pos))
                              (offset_val v (Int.repr pos)).

Fixpoint malloc_assertion (v: val) (pos: Z) (ty: type) : mpred :=
  match ty with
  | Tstruct id fld a => spacer v pos (alignof ty) *
                          malloc_assertion_fields 
                                 (offset_val v (Int.repr (align pos (alignof ty)))) 
                                 0 ty fld
  | _ => spacer v pos (alignof ty) *
                         memory_block Share.top (Int.repr (sizeof ty) )
                            (offset_val v (Int.repr (align pos (alignof ty))))
  end

with malloc_assertion_fields (v: val) (pos:Z) (t0: type) (flds: fieldlist) : mpred :=
 match flds with
 | Fnil => emp
 | Fcons id ty flds' => spacer v pos (alignof ty) * 
                                   field_storable Share.top t0 id 
                                        (offset_val v (Int.repr (align pos (alignof ty)))) * 
                                   malloc_assertion_fields v pos t0 flds'
  end.

Require Import progs.queue.

Parameter v: val.

Ltac simpl_malloc_assertion :=
  match goal with |- context [malloc_assertion ?V ?N ?T] =>
    let MA := fresh "MA" in
    remember (malloc_assertion V N T) as MA;
    match goal with H: MA = _ |- _ =>
       simpl in H; try fold T in H;
     unfold Zmax, align, spacer in H; simpl in H;
     normalize in H;
     subst MA
    end
  end.

Goal malloc_assertion v 0 t_struct_fifo = TT.
 simpl_malloc_assertion.
Abort.

Lemma malloc_assert: forall v ty, 
   memory_block Share.top (Int.repr (sizeof ty)) v =
   malloc_assertion v 0 ty.
Admitted.

