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

Fixpoint malloc_assertion (pos: Z) (ty: type)  (v: val) : mpred :=
  match ty with
  | Tstruct id fld a => spacer pos (alignof ty) v *
                          malloc_assertion_fields 0 ty fld 
                                    (offset_val v (Int.repr (align pos (alignof ty)))) 
  | _ => spacer pos (alignof ty) v *
                         memory_block Share.top (Int.repr (sizeof ty) )
                            (offset_val v (Int.repr (align pos (alignof ty))))
  end

with malloc_assertion_fields (pos:Z) (t0: type) (flds: fieldlist) (v: val) : mpred :=
 match flds with
 | Fnil => emp
 | Fcons id ty flds' => spacer pos (alignof ty) v * 
                                   field_storable Share.top t0 id 
                                        (offset_val v (Int.repr (align pos (alignof ty)))) * 
                                   malloc_assertion_fields pos t0 flds' v
  end.

Ltac simpl_malloc_assertion :=
  match goal with |- context [malloc_assertion ?N ?T ?V] =>
    let MA := fresh "MA" in
    remember (malloc_assertion  N T V) as MA;
    match goal with H: MA = _ |- _ =>
       simpl in H; try fold T in H;
     unfold Zmax, align, spacer in H; simpl in H;
     normalize in H;
     subst MA
    end
  end.

Lemma malloc_assert: forall ty, 
   memory_block Share.top (Int.repr (sizeof ty)) =
   malloc_assertion 0 ty.
Admitted.

Lemma memory_block_isptr:
  forall sh n v, memory_block sh n v = !! denote_tc_isptr v && memory_block sh n v.
Admitted.


