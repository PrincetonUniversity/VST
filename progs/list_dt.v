Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Fixpoint reptype (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => int
  | Tfloat _ _ => float
  | Tpointer t1 a => unit
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

Fixpoint arrayof (t: Type) (f: forall (ofs: Z) (v2: t),  mpred)
         (sh: Share.t) (t1: type) (b: block) (ofs: Z) (v2: list t) : mpred :=
    match v2 with
    | v::rest => f ofs v * arrayof t f sh t1 b (ofs+sizeof t1) rest
    | nil => emp
   end.

Fixpoint typed_mapsto' (t1: type) (sh: Share.t) (b: block) (ofs: Z) (v2: reptype t1) : mpred :=
match t1 as t return (t1 = t -> mpred) with
| Tvoid => emp
| Tint i s a =>
    fun H : t1 = Tint i s a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tint i s a) =>
         match i with
         | I8 =>
             match s with
             | Signed =>
                 address_mapsto Mint8signed (Vint v3)
                   (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)
                   (b, ofs)
             | Unsigned =>
                 address_mapsto Mint8unsigned (Vint v3)
                   (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)
                   (b, ofs)
             end
         | I16 =>
             match s with
             | Signed =>
                 address_mapsto Mint16signed (Vint v3)
                   (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)
                   (b, ofs)
             | Unsigned =>
                 address_mapsto Mint16unsigned (Vint v3)
                   (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)
                   (b, ofs)
             end
         | I32 =>
             address_mapsto Mint32 (Vint v3) (Share.unrel Share.Lsh sh)
               (Share.unrel Share.Rsh sh) (b, ofs)
         | IBool =>
             address_mapsto Mint8unsigned (Vint v3)
               (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) 
               (b, ofs)
         end) H in
    H0 v2
| Tfloat f a =>
    fun H : t1 = Tfloat f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tfloat f a) =>
         match f with
         | F32 =>
             address_mapsto Mfloat32 (Vfloat v3) (Share.unrel Share.Lsh sh)
               (Share.unrel Share.Rsh sh) (b, ofs)
         | F64 =>
             address_mapsto Mfloat64 (Vfloat v3) (Share.unrel Share.Lsh sh)
               (Share.unrel Share.Rsh sh) (b, ofs)
         end) H in
    H0 v2
| Tpointer t a => emp
| Tarray t z a =>
    fun H : t1 = Tarray t z a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tarray t z a) => arrayof _ (typed_mapsto' t sh b) sh t b z v3)
        H in
    H0 v2
| Tfunction t t0 => emp
| Tstruct i f a =>
    fun H : t1 = Tstruct i f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tstruct i f a) =>
         structfieldsof f sh b ofs v3) H in
    H0 v2
| Tunion i f a =>
    fun H : t1 = Tunion i f a =>
    let H0 :=
      eq_rect_r (fun t2 : type => reptype t2 -> mpred)
        (fun v3 : reptype (Tunion i f a) =>
         unionfieldsof f sh b ofs v3) H in
    H0 v2
| Tcomp_ptr i a => emp
end eq_refl
 with
 structfieldsof (flds: fieldlist) (sh: Share.t) (b: block) (ofs: Z) (v2: reptype_list prod flds) : mpred :=
match flds as f0 return (flds = f0 -> mpred) with
| Fnil => fun _ : flds = Fnil => emp
| Fcons i t f0 =>
    fun H : flds = Fcons i t f0 =>
    let H0 :=
      eq_rect_r (fun flds0 : fieldlist => reptype_list prod flds0 -> mpred)
        (fun v3 : reptype_list prod (Fcons i t f0) =>
         let (v, vr) := v3 in
         typed_mapsto' t sh b ofs v * structfieldsof f0 sh b (ofs + sizeof t) vr) H in
    H0 v2
end eq_refl
 with
unionfieldsof (flds: fieldlist) (sh: Share.t) (b: block) (ofs: Z) (v2: reptype_list sum flds) : mpred :=
match flds as f0 return (flds = f0 -> mpred) with
| Fnil => fun _ : flds = Fnil => emp
| Fcons i t f0 =>
    fun H : flds = Fcons i t f0 =>
    let H0 :=
      eq_rect_r (fun flds0 : fieldlist => reptype_list sum flds0 -> mpred)
        (fun v3 : reptype_list sum (Fcons i t f0) =>
         match v3 with inl v => typed_mapsto' t sh b ofs v | inr vr =>  unionfieldsof f0 sh b (ofs + sizeof t) vr end) H
    in H0 v2
end eq_refl.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 => Int.cmpu Ceq n1 n2 = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Int.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

Class listspec (list_structid: ident) (list_link: ident) :=
  mk_listspec {  
   list_fields: fieldlist;
   list_struct: type := (Tstruct list_structid list_fields noattr);
   list_link_type: (type_of_field
          (unroll_composite_fields list_structid list_struct list_fields)
          list_link) = tptr list_struct
}.

Definition typed_mapsto (t1: type) (sh: Share.t) (v1: val) (v2: reptype t1) : mpred :=
 match v1 with
 |  Vptr b ofs => typed_mapsto' t1 sh b (Int.unsigned ofs) v2 
 | _ => FF
 end.

Section LIST.
Context  {list_structid} {list_link} (ls: listspec list_structid list_link).

Definition lseg' (sh: share) := 
  HORec (fun (R: (list (reptype list_struct))*(val*val) -> mpred) (lp: (list (reptype list_struct))*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           typed_mapsto list_struct sh first h
                           * field_mapsto sh list_struct list_link first tail
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Definition lseg  (sh: share) (contents: list (reptype list_struct)) (x y: val) : mpred :=
   lseg' sh (contents, (x,y)).

Lemma lseg_unfold: forall sh contents v1 v2,
    lseg sh contents v1 v2 = 
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                       typed_mapsto list_struct sh v1 h 
                      * field_mapsto sh list_struct list_link v1 tail
                      * |> lseg sh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros. unfold lseg.
 unfold lseg' at 1. rewrite HORec_fold_unfold.
  normalize.
 apply prove_HOcontractive; intros.
 destruct x. destruct l. 
 auto 50 with contractive.
 destruct p.
 auto 50 with contractive.
Qed.

Lemma lseg_eq:
  forall sh l v , 
  typecheck_val v (tptr list_struct) = true ->
    lseg sh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold sh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
unfold typecheck_val in H.
destruct v; simpl in H; try discriminate.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
split; auto. 
unfold Int.cmpu.
rewrite Int.eq_true. auto.
normalize.
replace (r :: l = nil) with False by (apply prop_ext; intuition; congruence).
apply pred_ext; normalize.
contradiction H0.
unfold ptr_eq, typecheck_val in H|-*.
destruct v; inv H; auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
Qed.



Definition lseg_cons sh (l: list (reptype list_struct)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(reptype list_struct), EX r:list (reptype list_struct), EX y:val, 
             !!(l=h::r  /\ typecheck_val y (tptr list_struct) = true) && 
                       typed_mapsto list_struct sh x h *
             field_mapsto sh list_struct list_link x y * 
             |> lseg sh r y z.

Lemma lseg_neq:  forall sh l x z , 
  typecheck_val x (tptr list_struct) = true ->
  typecheck_val z (tptr list_struct) = true ->
  ptr_neq x z -> 
    lseg sh l x z = lseg_cons sh l x z.
Proof.
unfold lseg_cons, ptr_neq; intros.
rewrite lseg_unfold at 1; auto.
destruct l.
apply pred_ext; normalize.
intros.
inv H2.
apply pred_ext; normalize.
apply exp_right with r; normalize.
apply exp_right with l; normalize.
apply exp_right with tail; normalize.
apply andp_right; auto.
rewrite (field_mapsto_typecheck_val list_struct list_link sh x tail list_structid list_fields noattr) by auto.
normalize.
rewrite list_link_type in H2.
apply prop_right; auto.
intros.
inv H2.
apply exp_right with x0.
normalize.
Qed.

Lemma lseg_unroll: forall sh l x z , 
    lseg sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons sh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
normalize.
apply orp_right1; auto.
apply orp_right2.
unfold lseg_cons.
normalize.
apply exp_right with r.
normalize.
apply exp_right with l.
normalize.
apply exp_right with tail.
normalize.
apply andp_right.
pattern (field_mapsto sh list_struct list_link x tail) at 1;
 erewrite (field_mapsto_typecheck_val list_struct list_link sh x tail); try reflexivity.
rewrite list_link_type.
normalize.
auto.
apply orp_left; normalize.
unfold lseg_cons.
normalize. inv H0.
apply orp_left.
normalize. inv H0.
unfold lseg_cons.
normalize.
intros. symmetry in H0; inv H0.
apply exp_right with x0.
normalize.
Qed.

Lemma ptr_eq_dec:
  forall x z, {ptr_eq x z}+{~ptr_eq x z}.
Proof.
unfold ptr_eq; intros.
destruct x; simpl; auto. destruct z; simpl; auto. destruct (Int.eq i i0); auto.
destruct z; auto. destruct (eq_dec b b0).
subst. destruct (Int.eq i i0); auto. right; intros [? ?]; auto. inv H0.
right; intros [? ?]. contradiction.
Qed.


Lemma lseg_unroll_nonempty1:
   forall p P sh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    typecheck_val p (tptr list_struct) = true ->
    P |-- typed_mapsto list_struct sh v1 h *
             (field_mapsto sh list_struct list_link v1 p *
               lseg sh tail p v2) ->
    P |-- lseg sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
 apply now_later.
Qed.

Lemma lseg_nonnull:
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg sh s v nullval = lseg_cons sh s v nullval.
Proof.
intros. subst. 
rewrite lseg_unroll.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
apply orp_right2. auto.
Qed.

Lemma lift2_lseg_cons: 
 forall sh s p q, `(lseg_cons sh s)  p q =
    EX hry:(reptype list_struct * list (reptype list_struct) * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (`ptr_neq p q) &&
       (`(typed_mapsto list_struct sh) p (`h) *
        `(field_mapsto sh list_struct list_link) p (`y) *
        |> `(lseg sh r) (`y) q))
     end.
Proof.
 intros.
 unfold lseg_cons, ptr_neq; unfold_coerce. extensionality rho. simpl.
 apply pred_ext; normalize.
 apply exp_right with (h, r, y). normalize.
 destruct h as [[h r] y]. normalize.
 apply exp_right with h. normalize. apply exp_right with r.
 normalize. apply exp_right with y. normalize.
 apply andp_right.
 erewrite (field_mapsto_typecheck_val); [ | reflexivity].
 rewrite list_link_type. normalize. auto.
Qed.

Lemma unfold_lseg_cons:
   forall P Q1 Q R e sh s,
      local Q1 &&
      PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      local Q1 && PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R))) |--
     EX hry: reptype list_struct * list (reptype list_struct) * val,
      match hry with (h,r,y) => 
       !! (s=h::r) &&
      PROPx P (LOCALx Q 
        (SEPx (`(typed_mapsto list_struct sh) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg sh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(local Q1 && PROPx P (LOCALx Q (SEPx (`(lseg_cons sh s) e (`nullval) :: R)))).
apply derives_trans with
(local Q1 && local (`(typed_true (tptr list_struct)) e) &&
 PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R)))).
apply andp_right; auto.
apply andp_right; auto.
apply andp_left1; auto.
apply andp_left2; auto.
clear H.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue; unfold_coerce; simpl.
normalize.
rewrite lseg_nonnull by auto.
auto.
rewrite lift2_lseg_cons.
clear.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
normalize.
apply exp_right with x;
destruct x as [[h r] y].
normalize.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma semax_lseg_nonnull:
  forall Delta P Q sh s e R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e)  ->
  (forall (h: reptype list_struct) (r: list (reptype list_struct)) (y: val), s=h::r ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(typed_mapsto list_struct sh) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg sh r) (`y) (`nullval) ::
                  R)))) c Post) ->
  semax Delta (PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R)))) c Post.
Proof.
intros.
eapply semax_pre;  [apply unfold_lseg_cons | ].
eapply derives_trans; [ | apply H].
normalize.
apply extract_exists_pre; intros [[h r] y].
apply semax_extract_prop; intro; auto.
Qed.

Lemma lseg_nil_eq: 
    forall sh p q, lseg sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left. normalize.
 normalize. unfold lseg_cons. normalize. inv H0.
 apply orp_right1. normalize.
Qed.
End LIST.

Hint Rewrite @lseg_nil_eq : normalize.

Hint Rewrite @lseg_eq using reflexivity: normalize.



