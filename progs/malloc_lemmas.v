Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.
Require Import progs.client_lemmas.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Definition memory_byte (sh: share) : val -> mpred :=
       mapsto_ sh (Tint I8 Unsigned noattr).

Lemma memory_byte_offset_zero:
  forall sh v, memory_byte sh (offset_val v Int.zero) = memory_byte sh v.
Proof.
intros.
unfold memory_byte. unfold mapsto_.
f_equal. extensionality v'.
unfold umapsto; destruct v; try solve [simpl; auto].
destruct (access_mode (Tint I8 Unsigned noattr) ); auto.
simpl offset_val. rewrite Int.add_zero. auto.
Qed.

Fixpoint memory_block' (sh: share) (n: nat) (v: val) : mpred :=
  match n with
  | O => emp
  | S n' => memory_byte sh v * memory_block' sh n' (offset_val v Int.one)
 end.

Definition memory_block (sh: share) (n: int) (v: val) : mpred :=
    memory_block' sh (nat_of_Z (Int.unsigned n)) v.

Lemma memory_block_zero: forall sh v, memory_block sh (Int.repr 0) v = emp.
Proof.
 intros. unfold memory_block. rewrite Int.unsigned_repr. simpl. auto.
 pose proof Int.modulus_pos.
 unfold Int.max_unsigned. omega.
Qed.


Lemma offset_val_assoc:
  forall v i j, offset_val (offset_val v i) j = offset_val v (Int.add i j).
Proof.
intros.
unfold offset_val.
destruct v; simpl; auto.
rewrite Int.add_assoc; auto.
Qed.
Hint Rewrite offset_val_assoc: normalize.

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n (offset_val v Int.zero) = memory_block sh n v.
Proof.
unfold memory_block; intros.
revert v; induction (nat_of_Z (Int.unsigned n)); intros.
simpl. auto.
simpl.
f_equal.
apply memory_byte_offset_zero.
rewrite offset_val_assoc.
f_equal.
Qed.

Lemma memory_block_split:
  forall sh v i j,
   0 <= Int.unsigned i <= Int.unsigned j ->
   memory_block sh j v = 
      memory_block sh i v * memory_block sh (Int.sub j i) (offset_val v i).
Proof.
intros.
unfold memory_block.
remember (nat_of_Z (Int.unsigned i)) as n.
assert (Nrange: Z_of_nat n <= Int.max_unsigned).
destruct (Int.unsigned_range_2 i).
subst n. rewrite nat_of_Z_eq by omega. auto.
assert (i = Int.repr (Z_of_nat n)).
clear - Heqn.
admit.  (* tedious Integers proof *)
subst i.
clear Heqn.
revert j v H; induction n; intros.
unfold memory_block' at 2. fold memory_block'. rewrite emp_sepcon.
simpl Z_of_nat. rewrite Int.sub_zero_l.
symmetry.
apply memory_block_offset_zero.
replace (nat_of_Z (Int.unsigned j)) with (S (nat_of_Z (Int.unsigned (Int.sub j Int.one)))).
unfold memory_block' at 1 2; fold memory_block'.
repeat rewrite sepcon_assoc.
f_equal; auto.
rewrite IHn; clear IHn.
f_equal.
rewrite offset_val_assoc.
f_equal.
f_equal.
f_equal.
repeat rewrite Int.sub_add_opp.
rewrite Int.add_assoc.
f_equal.
rewrite <- Int.neg_add_distr.
f_equal.
admit.  (* tedious Integers proof *)
f_equal.
rewrite inj_S.
unfold Zsucc.
rewrite Int.add_unsigned.
f_equal.
rewrite Zplus_comm.
f_equal.
rewrite Int.unsigned_repr; auto.
rewrite inj_S in Nrange. unfold Zsucc in Nrange. split; omega.
rewrite inj_S in Nrange. unfold Zsucc in Nrange. omega.
rewrite inj_S in H. unfold Zsucc in H.
admit.  (* tedious Integers proof *)
admit.  (* tedious Integers proof *)
Qed.

Hint Rewrite memory_block_zero: normalize.

Global Opaque memory_block.

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Hint Rewrite int_add_repr_0_l int_add_repr_0_r : normalize.

Lemma field_mapsto__offset_zero:
  forall sh ty id v, 
   field_mapsto_ sh ty id (offset_val v (Int.repr 0)) =
   field_mapsto_ sh ty id v.
Proof.
 unfold field_mapsto_; intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto__offset_zero: normalize.

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

Definition storable_mode (ty: type) : bool :=
  match ty with
  | Tarray _ _ _ => false
  | Tfunction _ _ => false
  | Tstruct _ _ _ => false
  | Tunion _ _ _ => false
  | Tvoid => false
  | _ => true
end.

Fixpoint typed_mapsto_' (sh: Share.t) (pos: Z) (ty: type)  (v: val) : mpred :=
  match ty with
  | Tstruct id fld a => withspacer pos (alignof ty) v
           match fld with 
           | Fnil => memory_block sh Int.one (offset_val v (Int.repr (align pos (alignof ty))))
           | _ => fields_mapto_ sh 0 ty fld 
                                    (offset_val v (Int.repr (align pos (alignof ty))))
           end
  | _ => withspacer pos (alignof ty) v
                         (memory_block sh (Int.repr (sizeof ty) )
                            (offset_val v (Int.repr (align pos (alignof ty)))))
  end

with fields_mapto_ (sh: Share.t) (pos:Z) (t0: type) (flds: fieldlist) (v: val) : mpred :=
 match flds with
 | Fnil => emp
 | Fcons id ty flds' => 
     (if storable_mode ty 
     then withspacer pos (alignof ty) v (field_mapsto_ sh t0 id v)
     else typed_mapsto_' sh pos ty v)
     * fields_mapto_ sh pos t0 flds' v
  end.

Definition typed_mapsto_ (sh: Share.t) (ty: type) (v: val) : mpred :=
        typed_mapsto_' sh 0 ty v.

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
    fun _ _ => field_mapsto_ sh t_str id (offset_val v (Int.repr pos))
| t' => fun (alt1 : reptype t' -> mpred)  => alt1 
end.

Fixpoint typed_mapsto (t1: type) (sh: Share.t) (pos: Z) (v: val):  reptype t1 -> mpred :=
match t1 as t return (t1 = t -> reptype t1 -> mpred) with
| Tvoid => fun _ => emp
| Tint i s a =>
    fun H : t1 = Tint i s a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tint i s a) =>
                withspacer pos (alignof (Tint i s a)) v
                (mapsto sh (Tint i s a) (offset_val v (Int.repr (align pos (alignof t1)))) (Vint v3))) H in
    H0
| Tfloat f a =>
    fun H : t1 = Tfloat f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tfloat f a) =>
                withspacer pos (alignof (Tfloat f a)) v
                (mapsto sh (Tfloat f a) (offset_val v (Int.repr (align pos (alignof t1)))) (Vfloat v3))) H in
    H0
| Tpointer t a => 
    fun H : t1 = Tpointer t a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tpointer t a) =>
                withspacer pos (alignof (Tpointer t a)) v
                (mapsto sh (Tpointer t a) (offset_val v (Int.repr (align pos (alignof t1)))) v3)) H in
    H0
| Tarray t z a =>
    fun H : t1 = Tarray t z a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tarray t z a) => 
                 withspacer pos (alignof t) v
                 (arrayof _ (typed_mapsto t sh (align pos (alignof t))) t 0 v v3))
        H in
    H0
| Tfunction t t0 => emp
| Tstruct i f a =>
    fun H : t1 = Tstruct i f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tstruct i f a) =>
                 withspacer pos (alignof (Tstruct i f a)) v
                 (structfieldsof (Tstruct i f a) f sh (align pos (alignof t1)) v v3)) H in
    H0
| Tunion i f a =>
    fun H : t1 = Tunion i f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tunion i f a) =>
                 withspacer pos (alignof (Tunion i f a)) v
         (unionfieldsof f sh (align pos (alignof t1)) v v3)) H in
    H0
| Tcomp_ptr i a => 
        fun _ _ =>
          withspacer pos (alignof (Tcomp_ptr i a)) v
          (memory_block sh (Int.repr (sizeof (Tcomp_ptr i a))) (offset_val v (Int.repr pos)))
end eq_refl
 with
 structfieldsof (t_str: type) (flds: fieldlist) (sh: Share.t) (pos: Z) (v: val) :
               reptype_list prod flds -> mpred :=
match flds as f0 return (flds = f0 -> reptype_list prod flds -> mpred) with
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
    H0
end eq_refl
 with
unionfieldsof (flds: fieldlist) (sh: Share.t)  (pos: Z) (v: val):  reptype_list sum flds -> mpred :=
match flds as f0 return (flds = f0 -> reptype_list sum flds -> mpred) with
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
    in H0
end eq_refl.

Lemma field_mapsto_offset_zero:
  forall sh ty id v, 
   field_mapsto sh ty id (offset_val v (Int.repr 0)) =
   field_mapsto sh ty id v.
Proof.
 unfold field_mapsto_; intros. extensionality v2.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto_offset_zero: normalize.

Ltac simpl_typed_mapsto' T H MA :=
       unfold typed_mapsto_', typed_mapsto, eq_rect_r, withspacer, align, Zmax in H;
       simpl in H; try fold T in H;
       repeat rewrite emp_sepcon in H; repeat rewrite sepcon_emp in H;
       repeat rewrite field_mapsto__offset_zero in H;
       repeat rewrite field_mapsto_offset_zero in H;
     subst MA.

Ltac simpl_typed_mapsto :=
    let MA := fresh "MA" in
  match goal with 
  | |- context [typed_mapsto_ ?SH ?T ?V] =>
         remember (typed_mapsto_  SH T V) as MA;
         match goal with H: MA = _ |- _ => 
         unfold typed_mapsto_ in H; simpl_typed_mapsto' T H MA end
  | |- context [typed_mapsto_' ?SH ?N ?T ?V] =>
         remember (typed_mapsto_'  SH N T V) as MA;
         match goal with H: MA = _ |- _ => simpl_typed_mapsto' T H MA end
  | |- context [typed_mapsto ?T ?SH ?N ?V _] =>
         remember (typed_mapsto T SH N V) as MA;
         match goal with H: MA = _ |- _ => simpl_typed_mapsto' T H MA end
  | |- context [typed_mapsto ?T ?SH ?N ?V] =>
         remember (typed_mapsto T SH N V) as MA;
         match goal with H: MA = _ |- _ => simpl_typed_mapsto' T H MA end
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

Lemma spacer_offset_zero:
  forall pos n v, spacer pos n (offset_val v (Int.repr 0)) = spacer pos n v.
Proof.
 intros;
 unfold spacer.
 rewrite offset_val_assoc. rewrite Int.add_commut.
 rewrite <- offset_val_assoc. apply memory_block_offset_zero.
Qed.


Fixpoint typecount (t: type) : nat :=
 match t with
 | Tstruct _ f _ => typecount_fields f
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
 destruct t; simpl; auto.
 apply typecount_fields_pos.
Qed.
 
Lemma mafoz_aux:
  forall n f, (typecount_fields f < n)%nat -> 
     forall sh pos t v,
       fields_mapto_ pos sh t f (offset_val v (Int.repr 0)) =
       fields_mapto_ pos sh t f v.
Proof.
induction n; intros.
 elimtype False. omega.

 destruct f; simpl; auto.
 simpl in H.
 case_eq (storable_mode t0); intros.
 repeat rewrite withspacer_spacer.
 f_equal; [f_equal; [apply spacer_offset_zero |apply field_mapsto__offset_zero ] | ].
 apply IHn.
 pose proof (typecount_pos t0).
 omega.
 f_equal.
 destruct t0; inv H0; simpl;
 repeat rewrite withspacer_spacer;
 try (rewrite offset_val_assoc; rewrite Int.add_commut;
                 rewrite <- offset_val_assoc);
 try (f_equal; [apply spacer_offset_zero |]);
 try  apply memory_block_offset_zero.
 destruct f0.
 apply memory_block_offset_zero.
 apply IHn.
 simpl.
 simpl in H.
 pose proof (typecount_fields_pos f).
 omega.
 apply IHn.
 pose proof (typecount_pos t0).
 omega.
Qed.

Lemma fields_mapto__offset_zero:
  forall sh pos t f v, fields_mapto_ sh pos t f (offset_val v (Int.repr 0)) =
                           fields_mapto_ sh pos t f v.
Proof.
intros.
apply (mafoz_aux (S (typecount_fields f))).
omega.
Qed.

Lemma memory_block_typed': forall sh pos ty v, 
   spacer pos (alignof ty) v *
   memory_block sh (Int.repr (sizeof ty)) (offset_val v (Int.repr (align pos (alignof ty))))
     = typed_mapsto_' sh pos ty v
with memory_block_fields: forall sh pos t fld v,
  spacer (sizeof_struct fld pos) (alignof_fields fld) v 
  * memory_block sh (Int.repr (sizeof_struct fld pos)) v
  =   memory_block sh (Int.repr pos) v * fields_mapto_ sh pos t fld v.
Proof.
 clear memory_block_typed'.
 intros.
 induction ty; try solve [simpl; rewrite withspacer_spacer; auto].
 unfold typed_mapsto_'; fold fields_mapto_.
 rewrite withspacer_spacer.
 f_equal.
 case_eq f; intros. simpl.
 unfold Zmax, align; simpl. auto.
 rewrite <- H.
 assert (Zmax 1 (sizeof_struct f 0) = sizeof_struct f 0).
  subst f. simpl. rewrite align_0 by (apply alignof_pos).
   simpl. pose proof (sizeof_struct_incr f0 (sizeof t)).
   rewrite Zmax_spec. rewrite zlt_false; auto. pose proof (sizeof_pos t). omega.
 simpl sizeof. rewrite H0.
 specialize (memory_block_fields sh 0 (Tstruct i f a) f 
    (offset_val v (Int.repr (align pos (alignof (Tstruct i f a)))))).
 rewrite memory_block_zero in memory_block_fields.
 rewrite emp_sepcon in memory_block_fields.
 rewrite <- memory_block_fields.
 rewrite (memory_block_split sh _ 
                    (Int.repr (sizeof_struct f 0))
                    (Int.repr (align (sizeof_struct f 0) (alignof_fields f)))).
 2:  admit.  (* straightforward *)
 rewrite sepcon_comm. f_equal.
 admit. (* tedious *)
 
 clear memory_block_fields.
 intros. revert pos v; induction fld; simpl; intros.
 rewrite sepcon_comm; f_equal.
 unfold spacer.
 replace (Zminus (align pos (Zpos xH)) pos) with 0.
 apply memory_block_zero.
 unfold align. replace (pos + 1 - 1) with pos by omega.
 rewrite Zdiv_1_r. rewrite Zmult_1_r. omega.
 rewrite withspacer_spacer.
 pull_left (fields_mapto_ sh pos t fld v).
 rewrite <- memory_block_typed'. clear memory_block_typed'.
 replace (if storable_mode t0
  then spacer pos (alignof t0) v * field_mapsto_ sh t i v
  else spacer pos (alignof t0) v *
      memory_block sh (Int.repr (sizeof t0))
          (offset_val v (Int.repr (align pos (alignof t0)))))
 with (spacer  pos (alignof t0) v * 
          if storable_mode t0 then field_mapsto_ sh t i v
               else memory_block sh (Int.repr (sizeof t0))
               (offset_val v (Int.repr (align pos (alignof t0)))))
   by ( destruct (storable_mode t0); auto).
  do 2 rewrite <-sepcon_assoc.
 rewrite <- IHfld. clear IHfld.
 case_eq (storable_mode t0); intros.
 admit. (* might be *)
 admit.  (* might be *)
Admitted.  (* This proof is done here, but Qed takes forever in Coq 8.3pl5.
                         Let's hope it goes faster in 8.4 *)

Lemma memory_block_typed: 
 forall sh ty v, memory_block sh (Int.repr (sizeof ty)) v
               = typed_mapsto_ sh ty v.
Proof.
intros. unfold typed_mapsto_; rewrite <- memory_block_typed'.
unfold spacer.
rewrite align_0 by (apply alignof_pos).
rewrite memory_block_zero.
rewrite memory_block_offset_zero.
rewrite emp_sepcon; auto.
Qed.

Lemma mapsto_offset_zero:
  forall sh t v1 v2, 
    mapsto sh t (offset_val v1 (Int.repr 0)) v2 =
    mapsto sh t v1 v2.
Proof.
 unfold mapsto.
 intros.
 destruct v1; try solve [simpl; auto].
 unfold offset_val.
 rewrite Int.add_zero. auto.
Qed.

Lemma typed_mapsto_tint: forall sh v1 v2,
  (@coerce (val -> reptype tint -> mpred)
                    ((environ -> val) -> (environ -> reptype tint) -> assert)
                    (lift2_C val (reptype tint) mpred)
                    (typed_mapsto tint sh Z0)) 
       v1 v2 =
  (@coerce (val -> val -> mpred) _ (lift2_C val val mpred) (mapsto sh tint)) 
           v1  (`Vint v2).
Proof.
 intros.
 extensionality rho.
 unfold_coerce.
 simpl_typed_mapsto.
 apply mapsto_offset_zero.
Qed.
