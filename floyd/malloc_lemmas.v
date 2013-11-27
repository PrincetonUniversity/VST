Require Import floyd.base.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Local Open Scope logic.

Lemma memory_block_zero: forall sh b z, memory_block sh (Int.repr 0) (Vptr b z) = emp.
Proof.
 intros. unfold memory_block.
 change (Int.repr 0) with Int.zero.
 rewrite Int.unsigned_zero.
Admitted.  (* pretty straightforward *)

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n (offset_val Int.zero v) = memory_block sh n v.
Proof.
unfold memory_block; intros.
destruct v; auto.
simpl offset_val. cbv beta iota.
rewrite Int.add_zero. auto.
Qed.

Hint Rewrite memory_block_zero: norm.

Global Opaque memory_block.


Fixpoint is_Fnil (fld: fieldlist) : bool :=
match fld with
| Fnil => true
| Fcons id ty fld' => false
end.

Fixpoint reptype (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => option int
  | Tlong _ _ => option Int64.int
  | Tfloat _ _ => option float
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

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Hint Rewrite int_add_repr_0_l int_add_repr_0_r : norm.

Lemma field_mapsto__offset_zero:
  forall sh ty id v, 
   field_mapsto_ sh ty id (offset_val (Int.repr 0) v) =
   field_mapsto_ sh ty id v.
Proof.
 unfold field_mapsto_; intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto__offset_zero: norm.

Definition at_offset (z: Z) (P: val -> mpred) : val -> mpred :=
 fun v => P (offset_val (Int.repr z) v).

Arguments at_offset z P v : simpl never.

Definition at_offset' (P: val -> mpred) (z: Z)  : val -> mpred :=
 match z with Z0 => P | _ => at_offset z P end.

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

Definition storable_mode (ty: type) : bool :=
  match ty with
  | Tarray _ _ _ => false
  | Tfunction _ _ => false
  | Tstruct _ _ _ => false
  | Tunion _ _ _ => false
  | Tvoid => false
  | _ => true
end.


Fixpoint default_val (t: type) : reptype t :=
  match t as t0 return (reptype t0) with
  | Tvoid => tt
  | Tint _ _ _ => None
  | Tlong _ _ => None
  | Tfloat _ _ => None
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

Definition ZnthV t (lis: list (reptype t)) (i: Z) : reptype t := 
       if zlt i 0 then default_val t else nth (Z.to_nat i) lis (default_val t).

Definition cSome {A}(f: Z -> A) i := Some (f i).

Lemma isSome_cSome: 
 forall {B} (f: Z -> B) (i: Z), isSome (cSome f i).
Proof.  intros; apply I. Qed.
Hint Resolve @isSome_cSome.

Fixpoint rangespec' (lo: Z) (n: nat) (P: Z -> mpred): mpred :=
  match n with
  | O => emp
  | S n' => P lo * rangespec' (Zsucc lo) n' P
 end.

Definition rangespec (lo hi: Z) (P: Z -> mpred) : mpred :=
  rangespec' lo (nat_of_Z (hi-lo)) P.

Definition at_offset2 {T} (f: val -> T -> mpred) pos (v2: T) := 
           at_offset' (fun v => f v v2) pos.

Definition force_rep {T} (f: T -> val) (i: option T) :=
  match i with Some i' => f i' | None => Vundef end.

Definition maybe_field_mapsto (sh: Share.t) (t: type) (t_str: type) (id: ident) (pos: Z) :
                     (reptype t -> val -> mpred) -> reptype t -> val -> mpred :=
match t as t0 return ((reptype t0 -> val -> mpred) -> reptype t0 -> val -> mpred) with
| Tint i s a =>
    fun (_ : reptype (Tint i s a) -> val -> mpred) (v2'0 : reptype (Tint i s a)) =>
    at_offset' (field_umapsto sh t_str id (force_rep Vint v2'0)) pos
| Tlong s a =>
    fun (_ : reptype (Tlong s a) -> val -> mpred) (v2'0 : reptype (Tlong s a)) =>
    at_offset' (field_umapsto sh t_str id (force_rep Vlong v2'0)) pos
| Tfloat f a =>
    fun (_ : reptype (Tfloat f a) -> val -> mpred) (v2'0 : reptype (Tfloat f a)) =>
    at_offset' (field_umapsto sh t_str id (force_rep Vfloat v2'0)) pos
| Tpointer t0 a =>
    fun _ v2 =>  at_offset' (field_umapsto sh t_str id v2) pos
| Tcomp_ptr _ _ =>
    fun _ v2 => at_offset' (field_umapsto sh t_str id v2) pos
| t' => fun (alt1 : reptype t' -> val -> mpred)  => alt1 
end.

Definition array_at' (t: type) (sh: Share.t) (tmaps: val -> reptype t -> mpred)
                 (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) : mpred :=
           rangespec lo hi (fun i => tmaps (add_ptr_int t v i) (f i) ).

Fixpoint typed_mapsto' (sh: Share.t) (t1: type) (pos: Z) : reptype t1 -> val -> mpred :=
match t1 as t return (t1 = t -> reptype t1 -> val -> mpred) with
| Tvoid => fun _ _ => withspacer sh pos (alignof Tvoid)
          (at_offset' (memory_block sh (Int.repr (sizeof Tvoid)))pos)
| Tint i s a =>
    fun H : t1 = Tint i s a =>
      eq_rect_r (fun t2 : type => reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tint i s a)) =>
                withspacer sh pos (alignof (Tint i s a))
                (at_offset2 (umapsto sh (Tint i s a)) (align pos (alignof t1)) (force_rep Vint v3))) H
| Tlong s a =>
    fun H : t1 = Tlong s a =>
      eq_rect_r (fun t2 : type => reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tlong s a)) =>
                withspacer sh pos (alignof (Tlong s a))
                (at_offset2 (umapsto sh (Tlong s a)) (align pos (alignof t1)) (force_rep Vlong v3))) H
| Tfloat f a =>
    fun H : t1 = Tfloat f a =>
      eq_rect_r (fun t2 : type =>  reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tfloat f a)) =>
                withspacer sh pos (alignof (Tfloat f a))
                (at_offset' (fun v => umapsto sh (Tfloat f a) v (force_rep Vfloat v3)) (align pos (alignof t1)))) H
| Tpointer t a => 
    fun H : t1 = Tpointer t a =>
      eq_rect_r (fun t2 : type =>  reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tpointer t a)) =>
                withspacer sh pos (alignof (Tpointer t a))
                (at_offset' (fun v => umapsto sh (Tpointer t a) v v3)  (align pos (alignof t1)))) H
| Tarray t z a =>
    fun H : t1 = Tarray t z a =>
      eq_rect_r (fun t2 : type =>  reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tarray t z a)) => 
                 withspacer sh pos (alignof t)
                  (at_offset' (array_at' t sh (fun v7 v6 => typed_mapsto' sh t 0 v6 v7) (ZnthV _ v3) 0 z) (align pos (alignof t))))
        H
| Tfunction t t0 => fun _ _ => withspacer sh pos (alignof (Tfunction t t0))
          (at_offset' (memory_block sh (Int.repr (sizeof (Tfunction t t0))))pos)
| Tstruct i f a =>
    fun H : t1 = Tstruct i f a =>
      eq_rect_r (fun t2 : type =>  reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tstruct i f a)) =>
                 if is_Fnil f then withspacer sh pos (alignof Tvoid)
          (at_offset' (memory_block sh (Int.repr (sizeof Tvoid)))pos)
                  else 
                 withspacer sh pos (alignof (Tstruct i f a))
                 (structfieldsof sh (Tstruct i f a) f (align pos (alignof t1)) (align pos (alignof t1)) v3)) H
| Tunion i f a =>
    fun H : t1 = Tunion i f a =>
      eq_rect_r (fun t2 : type =>  reptype t2 -> val -> mpred)
        (fun (v3 : reptype (Tunion i f a)) =>
                 withspacer sh pos (alignof (Tunion i f a))
         (unionfieldsof sh f (align pos (alignof t1)) v3)) H
| Tcomp_ptr i a => 
     fun _ _ => withspacer sh pos (alignof (Tcomp_ptr i a))
          (at_offset' (memory_block sh (Int.repr (sizeof (Tcomp_ptr i a))))  (align pos (alignof (Tcomp_ptr i a))))
end eq_refl
 with
 structfieldsof (sh: Share.t) (t_str: type) (flds: fieldlist) (pos pos': Z) :
               reptype_structlist flds -> val -> mpred :=
match flds as f return (reptype_structlist f -> val -> mpred) with
| Fnil => fun (_ : reptype_structlist Fnil) _ => emp
| Fcons i t flds0 =>
    fun (X0 : reptype_structlist (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          (is_Fnil flds0 = b ->
           (if b
            then reptype t
            else (reptype t * reptype_structlist flds0)%type) -> val -> mpred)
       then
        fun (_ : is_Fnil flds0 = true) (X1 : reptype t) =>
        withspacer sh pos (alignof t)
          (maybe_field_mapsto sh t t_str i (align pos (alignof t))
             (typed_mapsto' sh t pos') X1)
       else
        fun (_ : is_Fnil flds0 = false)
          (X1 : reptype t * reptype_structlist flds0) =>
        (withspacer sh pos (alignof t)
          (maybe_field_mapsto sh t t_str i (align pos (alignof t))
             (typed_mapsto' sh t pos') (fst X1)) *
        (structfieldsof sh t_str flds0 pos (align pos' (alignof t) + sizeof t) (snd X1))))
   eq_refl X0
end
 with
unionfieldsof  (sh: Share.t) (flds: fieldlist) (pos: Z) :  reptype_unionlist flds -> val -> mpred :=
match flds as f0 return (flds = f0 -> reptype_unionlist flds -> val -> mpred) with
| Fnil => fun (_ : flds = Fnil) _ => emp
| Fcons i t f0 =>
    fun (H : flds = Fcons i t f0) =>
      eq_rect_r (fun flds0 : fieldlist => reptype_unionlist flds0 -> val -> mpred)
        (fun (v3 : reptype_unionlist (Fcons i t f0))=>
         match v3 with
         | inl v2' => typed_mapsto' sh t pos v2'
         | inr vr =>  unionfieldsof sh f0 pos vr 
         end) H
end eq_refl.

Definition typed_mapsto (sh: Share.t) (t1: type) v1 v2 := typed_mapsto' sh t1 0 v2 v1.

Definition typed_mapsto_ (sh: Share.t) (t1: type) := typed_mapsto' sh t1 0 (default_val _).

(* TESTING... 
Require Import progs.queue.
Parameter sh : share.
Goal lift1 (typed_mapsto sh t_struct_elem) = (fun _ _ => emp).

       unfold t_struct_elem, typed_mapsto_, typed_mapsto, typed_mapsto', 
        structfieldsof, eq_rect_r, withspacer, at_offset', align, Zmax.
simpl.
 fold t_struct_elem.


match goal with |- context [lift1 ?P] =>
    match P with (fun _ => _) =>
     let Q := fresh "Q" in let EQ := fresh "EQ" in
      evar (Q: val -> mpred);
      assert (EQ: P = Q); 
      [  let rho := fresh "rho" in
         extensionality rho
     | ]
 end 
end.


Ltac abstract_env T rho P :=
  match P with
   | @emp mpred _ _ => constr:(@emp (T -> mpred) _ _)
   | @sepcon mpred _ _ ?e1 ?e2 => 
      let e1' := abstract_env T rho e1 in let e2' := abstract_env T rho e2
       in constr:(@sepcon (T->mpred) _ _ e1' e2')
   | ?a ?b ?c ?d rho => 
   | _ => constr:(@FF (T -> mpred) _)
   end.

*)


Lemma field_umapsto_offset_zero:
  forall sh ty id v v', 
   field_umapsto sh ty id v' (offset_val (Int.repr 0) v) =
   field_umapsto sh ty id v' v.
Proof.
 intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_umapsto_offset_zero: norm.


Lemma field_mapsto_offset_zero:
  forall sh ty id v, 
   field_mapsto sh ty id (offset_val (Int.repr 0) v) =
   field_mapsto sh ty id v.
Proof.
 unfold field_mapsto_; intros. extensionality v2.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto_offset_zero: norm.

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

Definition array_at (t: type) (sh: Share.t) (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) : mpred :=
           rangespec lo hi (fun i => typed_mapsto sh t (add_ptr_int t v i) (f i)).

Definition array_at_ t sh lo hi := array_at t sh (fun _ => default_val t) lo hi.

Lemma typed_mapsto__isptr:
  forall sh t v, typed_mapsto_ sh t v = !!(isptr v) && typed_mapsto_ sh t v.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold typed_mapsto_.
Admitted. (* straightforward *)

Lemma field_umapsto_Vint:
  forall sh t i x v', field_umapsto sh t i (Vint x) v' = field_mapsto sh t i v' (Vint x).
Proof.
intros.
Transparent field_mapsto.
unfold field_mapsto.
Opaque field_mapsto.
rewrite prop_true_andp by congruence.
auto.
Qed.

Ltac simpl_typed_mapsto' T H MA :=
   try unfold T in H;
   unfold typed_mapsto_, typed_mapsto, typed_mapsto',
    structfieldsof, eq_rect_r, withspacer, at_offset', align, Z.max in H;
   change sepcon with opaque_sepcon in H; 
   change (@emp (val->mpred) _ _) with opaque_emp in H; 
   simpl in H;
   change @opaque_sepcon with (@sepcon (val -> mpred) _ _) in H;
   change @opaque_emp with (@emp (val->mpred) _ _) in H;
   repeat
    match type of H with
    | appcontext [fun (v1 : val) (v4 : option int) =>
               umapsto ?sh ?t v1 (@force_rep int Vint v4)] =>
        change
          (fun (v1 : val) (v4 : option int) =>
           umapsto sh t v1 (@force_rep int Vint v4))
         with (typed_mapsto sh t) in H
    | appcontext [(fun v:val => field_umapsto ?sh ?t ?f Vundef)] =>
          change (fun v :val => field_umapsto sh t f Vundef) with
               (field_mapsto_ sh t f) in H
    | appcontext [(field_umapsto ?sh ?t ?i Vundef)] =>
     change (field_umapsto sh t i Vundef) with (field_mapsto_ sh t i) in H
    end;
    fold tuint in H; fold tint in H;
    try fold T in H;
   repeat rewrite positive_nat_Z in H;
   repeat rewrite sepcon_emp in H || rewrite emp_sepcon in H;
   subst MA;
   repeat rewrite distribute_lifted_sepcon;
   repeat rewrite distribute_envtrans;
   repeat match goal with 
    | |- appcontext [array_at' ?t ?sh (typed_mapsto ?sh ?t')] =>
              unify t t';
              change (array_at' t sh (typed_mapsto sh t')) with (array_at t sh)
      end;
   repeat flatten_sepcon_in_SEP;
   simpl @fst; simpl @snd;  simpl @force_rep;
    repeat rewrite field_umapsto_Vint.


Ltac simpl_typed_mapsto1 :=
    let H := fresh "H" in let MA := fresh "MA" in
  match goal with 
  | |- appcontext [typed_mapsto_ ?SH ?T] =>
         remember (typed_mapsto_  SH T) as MA eqn:H in |-*; simpl_typed_mapsto' T H MA
  | |- appcontext [typed_mapsto' ?SH ?T ?N] =>
         remember (typed_mapsto' SH T N) as MA eqn:H in |-*; simpl_typed_mapsto' T H MA
  | |- appcontext [typed_mapsto ?SH ?T] =>
         remember (typed_mapsto SH T) as MA eqn:H in |-*; simpl_typed_mapsto' T H MA
 | |- appcontext [structfieldsof ?SH ?T ?F ?N ?N'] =>
         remember (structfieldsof SH T F N N') as MA eqn:H in |-*; simpl_typed_mapsto' T H MA
  end. 

Ltac simpl_typed_mapsto := repeat simpl_typed_mapsto1.

Arguments field_umapsto sh t1 fld v2 v1 : simpl never.


(* TESTING

Require Import progs.sha.

Goal typed_mapsto_ Tsh t_struct_SHA256state_st = TT.
simpl_typed_mapsto.
Abort.

Goal forall v,
  typed_mapsto Tsh t_struct_SHA256state_st v 
   (map Some (map Int.repr (1::2::3::4::5::6::7::8::nil)),
       (Some Int.zero, (Some Int.zero, (nil, Some Int.zero)))) |-- FF.
intros.
simpl_typed_mapsto.
Abort.

Goal typed_mapsto Tsh t_struct_SHA256state_st = fun _ _ => TT.
extensionality v w.
simpl_typed_mapsto.
Abort.
*)

(* TESTING
Require Import progs.sha.
Parameter sh : share.
Parameter v: val.

Goal forall r, typed_mapsto sh t_struct_SHA256state_st v r = emp.
intro.
 simpl_typed_mapsto.
Abort.
*)
(* TESTING
Require Import progs.queue.
Parameter sh : share.
Parameter p: environ->val.
Parameter q: environ -> reptype t_struct_elem.
Goal `(typed_mapsto sh t_struct_elem) p q = emp.

(*
    let H := fresh "H" in let MA := fresh "MA" in
  match goal with 
  | |- appcontext [typed_mapsto ?SH ?T] =>
         remember (typed_mapsto SH T) as MA eqn:H in |-*
  end.
elimtype False.
 unfold t_struct_elem in H.
   unfold typed_mapsto_, typed_mapsto, typed_mapsto',
    structfieldsof, eq_rect_r, withspacer, at_offset', align, Z.max in H.
  simpl in H.

Lemma si_ty_ma_aux:
  forall {t} (R P Q: val -> reptype t -> mpred),
              P = Q ->
              (forall v v', Q v v' = R v v') -> P = R.
Proof. intros. subst. extensionality v v'; auto.
Qed.

fold t_struct_elem in H.
evar (Q: val -> reptype t_struct_elem -> mpred).
apply (si_ty_ma_aux Q) in H.
Focus 2.
intros.
Definition stmc {A}{B}{C} (f: B -> C) (g: A -> B) x := f (g x).

repeat match goal with |- ?A = _ =>
  match A with appcontext [(?f (?g v'))] => 
      change (f (g v')) with (stmc f g v') 
end end.
repeat match goal with
   |- appcontext [@sepcon mpred _ _ (?A v' v) (?B v' v)] => 
  replace (@sepcon mpred _ _ (A v' v) (B v' v)) with 
       (@sepcon (reptype t_struct_elem -> val -> mpred) 
          (LiftNatDed _ _) (LiftSepLog _ _) A B v' v)
  by reflexivity
end.
 unfold Q; reflexivity.
 unfold Q in *; clear Q.
match type of H with MA = (fun v v' => ?A v' v) =>
  replace (fun v v' => A v' v) with A in H
end.
*)

simpl_typed_mapsto.
Abort.
*)

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

Lemma typed_mapsto_tint: forall sh (v1: environ -> val) (v2: environ -> option int),
  `(typed_mapsto sh tint) v1 v2 =
  `(umapsto sh tint)  v1  (`(force_rep Vint) v2).
Proof.
 intros.
 extensionality rho. reflexivity. 
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

Lemma umapsto_offset_zero:
  forall sh t v v', umapsto sh t (offset_val (Int.repr 0) v) v' = umapsto sh t v v'.
Proof.
 intros.
 unfold umapsto.
 destruct (access_mode t); auto.
 destruct v; auto.
 unfold offset_val. rewrite Int.add_zero; auto.
Qed. 

Definition fields_mapto_ sh pos t f v :=
 structfieldsof sh t f pos pos (struct_default_val f) v.

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

Lemma mafoz_aux:
  forall n,
  (forall f, (typecount_fields f < n)%nat -> 
     forall sh pos pos' t v v',
       structfieldsof sh t f pos pos' v' (offset_val (Int.repr 0) v) =
       structfieldsof sh t f pos pos' v' v) /\
  (forall t, (typecount t < n)%nat -> 
       forall sh ofs v v', typed_mapsto' sh t ofs v' (offset_val (Int.repr 0) v) =  
                               typed_mapsto' sh t ofs v' v).
Proof.
induction n; [split; intros; omega | ].
 split; intros ? ? ?.
*
 assert (MFM: forall t0 t pos i a v v', (typecount t0 < n)%nat -> 
                       maybe_field_mapsto sh t0 t i a (typed_mapsto' sh t0 pos) v' (offset_val (Int.repr 0) v) =
                       maybe_field_mapsto sh t0 t i a (typed_mapsto' sh t0 pos) v' v).
 { intros. change (Int.repr 0) with Int.zero.
    destruct t0; auto;
    try (apply at_offset'_zero; intros); 
   try apply field_umapsto_offset_zero;
   unfold maybe_field_mapsto;
   apply IHn; omega.
 }
 induction f; intros; simpl; auto.
 simpl in v'.
 destruct (is_Fnil f) eqn:Hf.
 repeat rewrite withspacer_spacer; simpl.
 f_equal; [apply spacer_offset_zero | ].
 apply MFM. simpl in H. pose (typecount_fields_pos f). omega.
 repeat rewrite withspacer_spacer; simpl.
 f_equal.  f_equal; [apply spacer_offset_zero |].
 apply MFM. simpl in H. pose (typecount_fields_pos f). omega.
 apply IHf. simpl  in H; omega.
*
 destruct t; intros; simpl; auto;
 try (unfold eq_rect_r; simpl);
 repeat rewrite withspacer_spacer; simpl;
 try(f_equal; [apply spacer_offset_zero |]);
 try (apply at_offset'_zero; intros); 
 try apply umapsto_offset_zero;
 try apply memory_block_offset_zero.
 + simpl in v'.
    unfold array_at'. unfold rangespec.
    destruct v0; simpl; auto.
    rewrite Int.add_zero. auto.
 + destruct (is_Fnil f) eqn:FN.
    f_equal. apply spacer_offset_zero. 
     apply at_offset'_zero; intros. apply memory_block_offset_zero.
    f_equal. apply spacer_offset_zero. 
   apply IHn. simpl in H; omega.
 + admit. (* union *)
Qed.

Lemma fields_mapto__offset_zero:
  forall sh pos t f v, fields_mapto_ sh pos t f (offset_val (Int.repr 0) v) =
                           fields_mapto_ sh pos t f v.
Proof.
intros.
apply (mafoz_aux (S (typecount_fields f))).
omega.
Qed.

Lemma memory_block_isptr: forall sh i v, 
  i > 0 -> 
  memory_block sh (Int.repr i) v = !!(isptr v) && memory_block sh (Int.repr i) v.
Proof.
intros.
Transparent memory_block.
unfold memory_block.
Opaque memory_block.
destruct v; normalize.
Qed.

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
Admitted. 

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
 intros. subst n.
 pose proof (sizeof_pos t);
destruct t; try contradiction; 
  destruct a as [[|] [|]]; try contradiction; simpl;
 unfold mapsto_, umapsto; simpl;
 try (destruct i,s); try destruct f; 
 rewrite memory_block_isptr by apply H0;
 destruct v; simpl; try  apply FF_andp; 
 rewrite prop_true_andp by auto;
 (apply memory_block_address_mapsto;  try reflexivity).
Qed.
 
Lemma spacer_memory_block:
  forall sh pos a v,
  isptr v -> 
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
 match f with Fnil => true 
    | Fcons _ t f' => andb (no_attr_type t) (no_attr_fields f')
 end.

Lemma no_attr_type_nonvol:
 forall t, no_attr_type t = true -> type_is_volatile t = false.
Proof.
intros. destruct t; simpl in *; try apply no_attr_e in H; subst; simpl; try reflexivity.
destruct i,s; reflexivity. destruct f; reflexivity.
Qed.

Lemma align_1: forall n, align n 1 = n.
Proof.  intros; unfold align. rewrite Z.div_1_r. rewrite Z.mul_1_r. omega.
Qed.

Lemma memory_block_typed': forall sh pos ty b ofs, 
 no_attr_type ty = true ->
   spacer sh pos (alignof ty) (Vptr b ofs) *
   memory_block sh (Int.repr (sizeof ty)) (offset_val (Int.repr (align pos (alignof ty))) (Vptr b ofs) )
     = typed_mapsto' sh ty pos (default_val ty) (Vptr b ofs).
(*with memory_block_fields: forall sh pos t fld b ofs,
 no_attr_fields fld = true ->
  spacer sh (sizeof_struct fld pos) (alignof_fields fld) (Vptr b ofs) 
  * memory_block sh (Int.repr (sizeof_struct fld pos)) (Vptr b ofs)
  =   memory_block sh (Int.repr pos) (Vptr b ofs) * fields_mapto_ sh pos t fld (Vptr b ofs).
*)
Proof.
*
(* clear memory_block_typed'. *)
 intros; rename H into Hno.
 induction ty; intros; simpl; unfold eq_rect_r; simpl;
  repeat rewrite withspacer_spacer; simpl;
 try solve [
     repeat rewrite spacer_memory_block by apply I;
     f_equal; unfold at_offset2;
    rewrite at_offset'_eq by (simpl; rewrite Int.add_zero; auto);
  apply memory_block_mapsto_;
    [rewrite (no_attr_e _ Hno); apply I | reflexivity]].
+ (* Tvoid *)
    repeat rewrite spacer_memory_block by apply I;
   rewrite at_offset'_eq by apply memory_block_offset_zero.
   rewrite align_1; reflexivity.
+ (* Tarray *)
   repeat rewrite spacer_memory_block by apply I;
  f_equal. simpl in Hno;  apply andb_true_iff in Hno; destruct Hno.
  rewrite (no_attr_e _ H0). simpl. auto.
  rewrite at_offset'_eq by (simpl; rewrite Int.add_zero; auto).
  admit.
+ (* Tfunction *)
   repeat rewrite spacer_memory_block by apply I;
   rewrite at_offset'_eq by apply memory_block_offset_zero.
   rewrite align_1; reflexivity.
+ (* Tstruct *)
  unfold fields_mapto_ in *.
  apply andb_true_iff in Hno; destruct Hno.
  fold no_attr_fields in H. rewrite (no_attr_e _ H0). simpl.
  f_equal.
  assert (f=Fnil \/ f<>Fnil) as [?|?] by (clear; destruct f; simpl; [left|right]; congruence).
  subst f.
  simpl. rewrite align_1.  
  f_equal.    rewrite at_offset'_eq by apply memory_block_offset_zero.
 rewrite align_1. reflexivity.
 rewrite Z.max_r
  by (destruct f; try congruence; simpl;
        rewrite align_0 by (pose proof alignof_pos t; omega);
        simpl; rewrite <- (sizeof_struct_incr f);
        pose proof (sizeof_pos t); omega).
 replace (is_Fnil f) with false by (destruct f; try reflexivity; congruence).
 f_equal.
 clear H1. clear a H0.
 set (base := align pos (alignof_fields f)) at 2.
 admit. 
+ (* Tunion *)
  admit.
+ (* Tcomp_ptr *)
 repeat rewrite spacer_memory_block by apply I.
     f_equal; unfold at_offset2.
    rewrite at_offset'_eq by (simpl; rewrite Int.add_zero; auto).
 rewrite (no_attr_e _ Hno) by apply I. simpl.
  auto.
Qed.

Lemma memory_block_typed: 
 forall sh ty, 
  no_attr_type ty = true ->
   memory_block sh (Int.repr (sizeof ty)) = typed_mapsto_ sh ty.
Proof.
intros.
extensionality v.
rewrite memory_block_isptr by (apply sizeof_pos).
rewrite typed_mapsto__isptr.
destruct v; simpl; normalize.
unfold typed_mapsto_; rewrite <- memory_block_typed'; auto.
unfold spacer.
rewrite align_0 by (apply alignof_pos).
simpl. rewrite emp_sepcon.
rewrite Int.add_zero. auto.
Qed.

Lemma var_block_typed_mapsto_:
  forall  sh id t, 
  no_attr_type t = true ->
 var_block sh (id, t) = 
   !!(sizeof t <= Int.max_unsigned) &&
            `(typed_mapsto_ sh t) (eval_var id t).
Proof.
intros; extensionality rho.
unfold_lift.
rewrite <- memory_block_typed by auto.
unfold var_block.
simpl. unfold_lift.
rewrite memory_block_isptr by apply sizeof_pos.
destruct (eval_var id t rho); simpl; normalize.
Qed.

Lemma typed_mapsto_typed_mapsto_ :
  forall sh t v v', typed_mapsto sh t v v' |-- typed_mapsto_ sh t v.
Admitted.
Hint Resolve typed_mapsto_typed_mapsto_.
Hint Resolve field_mapsto_field_mapsto_.

Lemma array_at_local_facts:
 forall t sh f lo hi v,
   lo < hi ->
    array_at t sh f lo hi v |-- !! isptr v.
Proof.
 intros.
 unfold array_at, rangespec.
 destruct (nat_of_Z (hi-lo)) eqn:?H.
 elimtype False.
 assert (hi - lo = 1 +  (hi-lo-1)) by omega.
 rewrite H1 in H0. clear H1.
 rewrite Z2Nat.inj_add in H0 by omega.
 simpl in H0. inv H0.
 simpl.
 eapply derives_trans with (typed_mapsto_ sh t (add_ptr_int t v lo) * TT).
 apply sepcon_derives; auto.
 rewrite typed_mapsto__isptr. normalize.
 destruct v; inv H1. apply prop_right; apply I.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple apply array_at_local_facts; omega : saturate_local.

Lemma array_at__local_facts:
 forall t sh lo hi v,
   lo < hi ->
    array_at_ t sh lo hi v |-- !! isptr v.
Proof.
 intros.
 apply array_at_local_facts; auto.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple apply array_at__local_facts; omega : saturate_local.
