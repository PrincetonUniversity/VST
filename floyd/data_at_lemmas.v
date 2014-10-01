Require Import msl.is_prop_lemma.
Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.type_id_env.
Require Import Coq.Logic.JMeq.
Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

(******************************************

Definition of reptype.

reptype is not defined in a quite beautiful way now. However, there seems no
better choice. The situation is explained at the end of this file. When Coq
releases a new version in the future, maybe we can rewrite it in a better way.

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
  | Tfunction t1 t2 _ => unit
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
  | Fcons id ty fld' => 
    if is_Fnil fld' 
      then reptype ty
      else sum (reptype ty) (reptype_unionlist fld')
  end.

Fixpoint reptype' (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => int
  | Tlong _ _ => Int64.int
  | Tfloat _ _ => float
  | Tpointer t1 a => val
  | Tarray t1 sz a => list (reptype' t1)
  | Tfunction t1 t2 _ => unit
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
  | Fcons id ty fld' => 
    if is_Fnil fld' 
      then reptype' ty
      else sum (reptype' ty) (reptype'_unionlist fld')
  end.

Fixpoint repinj (t: type): reptype' t -> reptype t :=
  match t as t0 return (reptype' t0 -> reptype t0) with
  | Tvoid => id
  | Tint _ _ _ => Vint
  | Tlong _ _ => Vlong
  | Tfloat _ _ => Vfloat
  | Tpointer _ _ => id
  | Tarray t0 _ _ => (map (repinj t0))
  | Tfunction _ _ _ => id
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
    (if is_Fnil fld0  as b0
      return
        (is_Fnil fld0 = b0 ->
         (if b0
          then reptype' t
          else sum (reptype' t) (reptype'_unionlist fld0)) ->
         if b0 then reptype t else sum (reptype t) (reptype_unionlist fld0))
     then fun _ : is_Fnil fld0 = true => repinj t
     else
      fun (_ : is_Fnil fld0 = false) (v : sum (reptype' t) (reptype'_unionlist fld0)) =>
      match v with
      | inl v1 => inl (repinj t v1)
      | inr v2 => inr (repinj_unionlist fld0 v2)
      end) eq_refl
  end.

Fixpoint default_val (t: type) : reptype t :=
  match t as t0 return (reptype t0) with
  | Tvoid => tt
  | Tint _ _ _ => Vundef
  | Tlong _ _ => Vundef
  | Tfloat _ _ => Vundef
  | Tpointer _ _ => Vundef
  | Tarray t0 _ _ => nil
  | Tfunction _ _ _ => tt
  | Tstruct _ f _ => struct_default_val f
  | Tunion _ f _ => union_default_val f
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
  end
with union_default_val flds : reptype_unionlist flds :=
  match flds as f return (reptype_unionlist f) with
  | Fnil => tt
  | Fcons _ t flds0 =>
     if is_Fnil flds0 as b
      return  (if b then reptype t else (reptype t + reptype_unionlist flds0)%type)
     then default_val t
     else inl (default_val t)
  end.

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Hint Rewrite int_add_repr_0_l int_add_repr_0_r : norm.

Definition repinject (t: type) : reptype t -> val :=
  match t as t0 return reptype t0 -> val with
  | Tint _ _ _ => fun v => v
  | Tlong _ _ => fun v => v
  | Tfloat _ _ => fun v => v
  | Tpointer _ _ => fun v => v
  | Tcomp_ptr _ _ => fun v => v
  | _ => fun _ => Vundef
 end.

Definition valinject (t: type) : val -> reptype t :=
  match t as t0 return val -> reptype t0 with
  | Tint _ _ _ => fun v => v
  | Tlong _ _ => fun v => v
  | Tfloat _ _ => fun v => v
  | Tpointer _ _ => fun v => v
  | Tcomp_ptr _ _ => fun v => v
  | t => fun _ => default_val t
 end.

Lemma valinject_JMeq: forall t v, type_is_by_value t -> JMeq (valinject t v) v.
Proof.
  intros.
  destruct t; simpl in *; try tauto.
Qed.

(******************************************

Definition of all at_offsets.

at_offset is the elementary definition. but it is not good for computation. As
a result, users should not unfold at_offset' into at_offset. And all useful 
lemmas about at_offset' will be proved here. 

at_offset2 is defined on at_offset'. Users should unfold at_offset2 and prove
lemmas on the level of at_offset'.

******************************************)

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

Lemma lifted_at_offset'_eq: forall (P: val -> mpred) z v,
  (forall p, P ((offset_val (Int.repr 0)) p) = P p) ->
  `(at_offset' P z) v = `P (`(offset_val (Int.repr z)) v).
Proof.
  intros.
  unfold liftx, lift in *. simpl in *.
  extensionality p.
  apply at_offset'_eq.
  apply H.
Qed.

Lemma at_offset'_eq2: forall pos pos' P, 
  (forall p, P (offset_val (Int.repr 0) p) = P p) -> 
  forall p, at_offset' P (pos + pos') p = at_offset' P pos' (offset_val (Int.repr pos) p).
Proof.
  intros.
  rewrite at_offset'_eq; [| apply H].
  rewrite at_offset'_eq; [| apply H].
  unfold offset_val.
  destruct p; auto.
  rewrite int_add_assoc1.
  reflexivity.
Qed.

Lemma at_offset_derives: forall P Q, P |-- Q -> forall pos, at_offset' P pos |-- at_offset' Q pos.
Proof.
  intros.
  go_lower.
  unfold at_offset', at_offset. destruct pos; apply H.
Qed.

(******************************************

Definitions of spacer and withspacer

Comment: spacer only has offset_zero property but does not have local_facts
and isptr property.

******************************************)

Definition spacer (sh: share) (be: Z) (ed: Z) : val -> mpred :=
  if Z.eq_dec (ed - be) 0
  then fun _ => emp
  else
   at_offset' (memory_block sh (Int.repr (ed - be))) be.

Arguments spacer sh be ed / _ .

Definition withspacer sh (be: Z) (ed: Z) : (val -> mpred) -> val -> mpred :=
   match (ed - be) with
   | Z0 => fun P => P
   | _ => fun P => spacer sh be ed * P
   end.

Lemma withspacer_spacer: forall sh be ed P,
   withspacer sh be ed P = spacer sh be ed * P.
Proof.
  intros.
 extensionality v.
 unfold withspacer, spacer.
 destruct (ed - be); auto.
 rewrite if_true by auto.
 simpl. rewrite emp_sepcon. auto.
Qed.

Lemma spacer_offset_zero:
  forall sh be ed v, spacer sh be ed v = spacer sh be ed (offset_val Int.zero v).
Proof.
  intros;
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);  auto.
  repeat rewrite at_offset'_eq;
  try rewrite offset_offset_val; try  rewrite Int.add_zero_l; auto.
  rewrite <- memory_block_offset_zero.
  reflexivity.
Qed.

Lemma withspacer_add:
  forall sh pos be ed P p,
  withspacer sh (pos + be) (pos + ed) (fun p0 => P (offset_val (Int.repr pos) p)) p = 
  withspacer sh be ed P (offset_val (Int.repr pos) p).
Proof.
  intros.
  rewrite withspacer_spacer.
  rewrite withspacer_spacer.
  simpl.
  replace (pos + ed - (pos + be)) with (ed - be) by omega.
  if_tac; [reflexivity|].
  repeat (rewrite at_offset'_eq; [|rewrite <- memory_block_offset_zero; reflexivity]).
  replace (offset_val (Int.repr (pos + be)) p) with
          (offset_val (Int.repr be) (offset_val (Int.repr pos) p)).
  reflexivity.
  destruct p; simpl; try reflexivity.
  rewrite int_add_assoc1.
  reflexivity.
Qed.

Lemma offset_val_preserve_isptr: forall p pos, !! (isptr (offset_val pos p)) |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; apply derives_refl.
Qed.

Lemma at_offset'_preserve_local_facts: forall {A: Type} P pos, (forall p, P p |-- !!(isptr p)) -> (forall p, at_offset' P pos p |-- !!(isptr p)).
Proof.
  intros.
  unfold at_offset', at_offset.
  destruct pos.
  + exact (H p).
  + eapply derives_trans. exact (H _). apply offset_val_preserve_isptr.
  + eapply derives_trans. exact (H _). apply offset_val_preserve_isptr.
Qed.

Lemma withspacer_preserve_local_facts: forall sh be ed P, (forall p, P p |-- !! (isptr p)) -> (forall p, withspacer sh be ed P p |-- !! (isptr p)).
Proof.
  intros.
  rewrite withspacer_spacer.
  simpl; rewrite sepcon_comm. 
  apply (right_is_prop (!!isptr p) (P p) _); [apply prop_is_prop|].
  apply H.
Qed.

(************************************************

Definition of data_at 

************************************************)

(************************************************

Always assume in arguments of data_at', array_at', sfieldlist_at', ufieldlist_
at' has argument pos with alignment criterian. So, spacers are only added after
fields of structs or unions.

A new array_at' could be used here. But it worths discussion which version is better.

Personally, I don't know why "function" case looks like this. I just copy it
from previous version.

************************************************)

Definition alignof_hd (fld: fieldlist) : Z :=
  match fld with
  | Fnil => 1
  | Fcons _ t _ => alignof t
  end.

Lemma alignof_hd_divide: forall f, (alignof_hd f | alignof_fields f).
Proof.
  intros.
  destruct f.
  + simpl. apply Z.divide_refl.
  + simpl alignof_hd. apply alignof_fields_hd_divide.
Qed.

Lemma alignof_hd_pos: forall f, alignof_hd f > 0.
Proof.
  intros.
  destruct f; simpl.
  omega.
  apply alignof_pos.
Qed.

Lemma divide_align: forall x y: Z, x > 0 -> Zdivide x y -> align y x = y.
Proof.
  intros.
  unfold align.
  destruct H0.
  rewrite H0.
  pose proof Zdiv_unique (x0 * x + x - 1) x x0 (x - 1).
  assert (x0 * x + x - 1 = x0 * x + (x - 1)) by omega.
  assert (0 <= x - 1 < x) by omega.
  rewrite (H1 H2 H3).
  reflexivity.
Qed.

Fixpoint tl_ofs pos alignment fld :=
  match fld with
  | Fnil => align pos alignment
  | Fcons _ t f => 
    if (is_Fnil f)
    then align (pos + sizeof t) alignment
    else tl_ofs (align (pos + sizeof t) (alignof_hd f)) alignment f
  end.

Lemma sizeof_Tstruct_tl_ofs: forall pos i f a, 
  legal_alignas_type (Tstruct i f a) = true ->
  (alignof (Tstruct i f a) | pos) -> 
  pos + sizeof (Tstruct i f a) = tl_ofs pos (alignof (Tstruct i f a)) f.
Proof.
  intros.
  simpl.
  assert (alignof_fields f | alignof (Tstruct i f a)) by apply (legal_alignas_type_Tstruct _ _ _ H).
  assert (alignof_hd f | pos).
    eapply Zdivides_trans; [apply alignof_hd_divide|].
    eapply Zdivides_trans; [exact H1 | exact H0].
  pattern pos at 2; replace pos with (align pos (alignof_hd f)) by
    (apply divide_align; [apply alignof_hd_pos|exact H2]).
  pattern pos at 2; replace pos with (pos + 0) by omega.
  forget 0 as pos'.
  assert (alignof (Tstruct i f a) > 0) by apply alignof_pos.
  forget (alignof (Tstruct i f a)) as alignment.
  destruct f.
  + simpl.
    rewrite (divide_align 1 _); [ | omega | apply Z.divide_1_l].
    apply divide_add_align; exact H0.
  + apply nested_pred_Tstruct in H.
    revert pos' i0 t H H0 H1 H2 H3; induction f; intros.
    - simpl in *. 
      rewrite <- (divide_add_align pos _ pos'); [|exact H2].
      rewrite <- Z.add_assoc.
      apply divide_add_align.
      exact H0.
    - assert (is_Fnil (Fcons i0 t f) = false) by reflexivity.
      pose proof IHf (align pos' (alignof t0) + sizeof t0) i0 t; clear IHf.
      forget (Fcons i0 t f) as ff; clear i0 t.
      simpl; simpl in H5; rewrite H4.
      rewrite <- (divide_add_align pos _ pos'); [|exact H2].
      rewrite <- Z.add_assoc.
      apply H5; try assumption.
      * apply andb_true_iff in H. tauto.
      * eapply Zdivides_trans; [apply alignof_fields_tl_divide | exact H1].
      * eapply Zdivides_trans; [apply alignof_hd_divide|].
        eapply Zdivides_trans; [| exact H0].
        eapply Zdivides_trans; [apply alignof_fields_tl_divide| exact H1].
Qed.

Lemma tl_ofs_le: forall pos alignment f, alignment > 0 -> pos <= tl_ofs pos alignment f.
Proof.
  intros.
  destruct f.
  + simpl.
    apply align_le.
    exact H.
  + revert pos i t; induction f; intros.
    - simpl.
      pose proof sizeof_pos t.
      pose proof align_le (pos + sizeof t) alignment H.
      omega.
    - assert (is_Fnil (Fcons i t f) = false) by reflexivity.
      pose proof IHf (align (pos + sizeof t0) (alignof_hd (Fcons i t f))) i t.
      clear IHf.
      forget (Fcons i t f) as ff.
      simpl.
      rewrite H0.
      pose proof sizeof_pos t0.
      pose proof align_le (pos + sizeof t0) _ (alignof_hd_pos ff).
      omega.
Qed.

Lemma tl_ofs_cons_le: forall pos alignment i t f, alignment > 0 -> 
  pos + sizeof t <= tl_ofs pos alignment (Fcons i t f).
Proof.
  intros.
  simpl.
  if_tac.
  + apply align_le. exact H.
  + pose proof tl_ofs_le (align (pos + sizeof t) (alignof_hd f)) alignment f H.
    pose proof align_le (pos + sizeof t) _ (alignof_hd_pos f).
    omega.
Qed.

Definition ZnthV t (lis: list (reptype t)) (i: Z) : reptype t := 
       if zlt i 0 then default_val t else nth (Z.to_nat i) lis (default_val t).

Fixpoint rangespec' (lo: Z) (n: nat) (P: Z -> mpred): mpred :=
  match n with
  | O => emp
  | S n' => P lo * rangespec' (Zsucc lo) n' P
 end.

Definition rangespec (lo hi: Z) (P: Z -> mpred) : mpred :=
  rangespec' lo (nat_of_Z (hi-lo)) P.

Definition array_at' (t: type) (sh: Share.t) (tmaps: reptype t -> val -> mpred)
                 (f: Z -> reptype t) (lo hi: Z) (v: val) : mpred :=
           !! isptr v && rangespec lo hi (fun i => tmaps (f i) (add_ptr_int t v i)).

(*
Fixpoint array_at' (sh: Share.t) (t: type) (length: Z) (P: Z -> reptype t -> val -> mpred) (pos: Z) (v: list (reptype t)) : val -> mpred :=
match v with
| nil => if (Zeq_bool length 0) then fun _ => emp else FF
| hd :: tl => (P pos hd) * (array_at' sh t (length - 1) P (pos + sizeof t) tl)
end.
*)

Fixpoint data_at' (sh: Share.t) (e: type_id_env) (t1: type): Z -> reptype t1 -> val -> mpred :=
  match t1 as t return (Z -> reptype t -> val -> mpred) with
  | Tvoid => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tarray t z a => at_offset2 (fun p (v: list (reptype t)) => array_at' t sh (data_at' sh e t 0) (ZnthV _ v) 0 z p)
                    (* array_at' sh t z (data_at' sh e t) *)
  | Tfunction t t0 _ => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tstruct i f a => sfieldlist_at' sh e f (alignof t1)
  | Tunion i f a => ufieldlist_at' sh e f (sizeof t1)
  | Tcomp_ptr i a => at_offset2 (mapsto sh (Tpointer (look_up_ident_default i e) a))
  | _ => at_offset2 (mapsto sh t1) (* All these C types are by value types *)
  end
with sfieldlist_at' (sh: Share.t) (e: type_id_env) (flds: fieldlist) (alignment: Z) : Z -> reptype_structlist flds -> val -> mpred :=
  fun (pos: Z) =>
  match flds as f return reptype_structlist f -> val -> mpred with
  | Fnil => fun _ p => !!(isptr p) && emp (* empty struct case *)
  | Fcons i t flds0 =>
    fun v : reptype_structlist (Fcons i t flds0) =>
      (if is_Fnil flds0 as b
        return
          (is_Fnil flds0 = b ->
           (if b
            then reptype t
            else (reptype t * reptype_structlist flds0)%type) -> val -> mpred)
       then
        fun (_ : is_Fnil flds0 = true) (v0 : reptype t) =>
          withspacer sh (pos + sizeof t) (align (pos + sizeof t) alignment) (data_at' sh e t pos v0)
       else
        fun (_ : is_Fnil flds0 = false) (v0 : (reptype t * reptype_structlist flds0)%type) =>
          withspacer sh (pos + sizeof t) (align (pos + sizeof t) (alignof_hd flds0)) (data_at' sh e t pos (fst v0)) *
          (sfieldlist_at' sh e flds0 alignment (align (pos + sizeof t) (alignof_hd flds0)) (snd v0)))
    eq_refl v
  end
with ufieldlist_at' (sh: Share.t) (e: type_id_env) (flds: fieldlist) (size: Z) (pos: Z) {struct flds}: reptype_unionlist flds -> val -> mpred :=
  match flds as f return (reptype_unionlist f -> val -> mpred) with
  | Fnil => fun _ p => !!(isptr p) && emp (* empty union case *)
  | Fcons i t flds0 => 
    fun v : reptype_unionlist (Fcons i t flds0) =>
      (if is_Fnil flds0 as b
        return
          (is_Fnil flds0 = b ->
           (if b
            then reptype t
            else (reptype t + reptype_unionlist flds0)%type) -> val -> mpred)
       then
        fun (_ : is_Fnil flds0 = true) (v0 : reptype t) =>
          withspacer sh (pos + sizeof t) (pos + size) (data_at' sh e t pos v0)
       else
        fun (_ : is_Fnil flds0 = false) (v0 : (reptype t + reptype_unionlist flds0)%type) =>
          match v0 with
          | inl v_hd => 
            withspacer sh (pos + sizeof t) (pos + size) (data_at' sh e t pos v_hd)
          | inr v_tl =>
            ufieldlist_at' sh e flds0 size pos v_tl
          end)
    eq_refl v
  end.

Definition data_at (sh: Share.t) (t: type) :=
  (fun (_:reptype t) p => (!! (size_compatible t p /\ align_compatible t p))) 
  && data_at' sh empty_ti t 0.

Definition data_at_ (sh: Share.t) (t: type) := data_at sh t (default_val _).

Lemma data_at'_mut: forall sh e (bound: Z) 
  (P1: forall {t: type}, (Z -> reptype t -> val -> mpred) -> Z -> Prop) 
  (P3: forall {fld: fieldlist}, (Z -> Z -> reptype_structlist fld -> val -> mpred) -> Z -> Z -> Prop)
  (P4: forall {fld: fieldlist}, (Z -> Z -> reptype_unionlist fld -> val -> mpred) -> Z -> Z -> Prop),
  (forall pos, (legal_alignas_type Tvoid = true) -> 
    (alignof Tvoid | pos) -> 
    (pos + sizeof Tvoid <= bound) -> 
    P1 (data_at' sh e Tvoid) pos) ->
  (forall pos i s a, 
    (legal_alignas_type (Tint i s a) = true) -> 
    (alignof (Tint i s a) | pos) -> 
    (pos + sizeof (Tint i s a) <= bound) -> 
    P1 (data_at' sh e (Tint i s a)) pos) ->
  (forall pos s a,
    (legal_alignas_type (Tlong s a) = true) -> 
    (alignof (Tlong s a) | pos) -> 
    (pos + sizeof (Tlong s a) <= bound) -> 
    P1 (data_at' sh e (Tlong s a)) pos) ->
  (forall pos f a, 
    (legal_alignas_type (Tfloat f a) = true) -> 
    (alignof (Tfloat f a) | pos) -> 
    (pos + sizeof (Tfloat f a) <= bound) -> 
    P1 (data_at' sh e (Tfloat f a)) pos) ->
  (forall pos t a, 
    (legal_alignas_type (Tpointer t a) = true) -> 
    (alignof (Tpointer t a) | pos) -> 
    (pos + sizeof (Tpointer t a) <= bound) -> 
    P1 (data_at' sh e (Tpointer t a)) pos) ->
  (forall pos t z a, 
    (legal_alignas_type (Tarray t z a) = true) -> 
    (alignof (Tarray t z a) | pos) -> 
    (pos + sizeof (Tarray t z a) <= bound) -> 
    (forall n, 0 <= n < z -> P1 (data_at' sh e t) (pos + (sizeof t) * n)) ->
    P1 (data_at' sh e (Tarray t z a)) pos) ->
  (forall pos t t0 c, 
    (legal_alignas_type (Tfunction t t0 c) = true) -> 
    (alignof (Tfunction t t0 c) | pos) -> 
    (pos + sizeof (Tfunction t t0 c) <= bound) -> 
    P1 (data_at' sh e (Tfunction t t0 c)) pos) ->
  (forall pos i f a, 
    (legal_alignas_type (Tstruct i f a) = true) -> 
    (alignof (Tstruct i f a) | pos) -> 
    (pos + sizeof (Tstruct i f a) <= bound) -> 
    P3 (sfieldlist_at' sh e f) (alignof (Tstruct i f a)) pos ->
    P1 (data_at' sh e (Tstruct i f a)) pos) ->
  (forall pos i f a, 
    (legal_alignas_type (Tunion i f a) = true) -> 
    (alignof (Tunion i f a) | pos) -> 
    (pos + sizeof (Tunion i f a) <= bound) -> 
    P4 (ufieldlist_at' sh e f) (sizeof (Tunion i f a)) pos ->
    P1 (data_at' sh e (Tunion i f a)) pos) ->
  (forall pos i a, 
    (legal_alignas_type (Tcomp_ptr i a) = true) -> 
    (alignof (Tcomp_ptr i a) | pos) -> 
    (pos + sizeof (Tcomp_ptr i a) <= bound) -> 
    P1 (data_at' sh e (Tcomp_ptr i a)) pos) ->
  (forall pos alignment, 
    (nested_fields_pred local_legal_alignas_type Fnil = true) -> 
    (alignment > 0) ->
    (alignof_hd Fnil | pos) -> 
    (alignof_fields Fnil | alignment) ->
    (tl_ofs pos alignment Fnil <= bound) -> 
    P3 (sfieldlist_at' sh e Fnil) alignment pos) ->
  (forall pos alignment i t, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t Fnil) = true) -> 
    (alignment > 0) ->
    (alignof_hd (Fcons i t Fnil) | pos) -> 
    (alignof_fields (Fcons i t Fnil) | alignment) -> 
    (tl_ofs pos alignment (Fcons i t Fnil) <= bound) -> 
    P1 (data_at' sh e t) pos ->
    P3 (sfieldlist_at' sh e (Fcons i t Fnil)) alignment pos) ->
  (forall pos alignment i t f, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t f) = true) -> 
    (alignment > 0) ->
    (alignof_hd (Fcons i t f) | pos) -> 
    (alignof_fields (Fcons i t f) | alignment) -> 
    (tl_ofs pos alignment (Fcons i t f) <= bound) -> 
    is_Fnil f = false -> 
    P1 (data_at' sh e t) pos ->
    P3 (sfieldlist_at' sh e f) alignment (align (pos + sizeof t) (alignof_hd f)) ->
    P3 (sfieldlist_at' sh e (Fcons i t f)) alignment pos) ->
  (forall pos size, 
    (nested_fields_pred local_legal_alignas_type Fnil = true) -> 
    (alignof_fields Fnil | pos) ->
    (sizeof_union Fnil <= size) ->
    (pos + size <= bound) -> 
    P4 (ufieldlist_at' sh e Fnil) size pos) ->
  (forall pos size i t, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t Fnil) = true) -> 
    (alignof_fields (Fcons i t Fnil) | pos) ->
    (sizeof_union (Fcons i t Fnil) <= size) ->
    (pos + size <= bound) ->
    P1 (data_at' sh e t) pos ->
    P4 (ufieldlist_at' sh e (Fcons i t Fnil)) size pos) ->
  (forall pos size i t f, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t f) = true) -> 
    (alignof_fields (Fcons i t f) | pos) ->
    (sizeof_union (Fcons i t f) <= size) ->
    (pos + size <= bound) ->
    is_Fnil f = false -> 
    P1 (data_at' sh e t) pos ->
    P4 (ufieldlist_at' sh e f) size pos ->
    P4 (ufieldlist_at' sh e (Fcons i t f)) size pos) ->
  forall pos t, 
    (legal_alignas_type t = true) -> 
    (alignof t | pos) -> 
    (pos + sizeof t <= bound) -> 
    P1 (data_at' sh e t) pos.
Proof.
  intros.
  apply (type_mut (fun t => forall pos, (legal_alignas_type t = true) -> (alignof t | pos) -> 
                  (pos + sizeof t <= bound) -> 
                  @P1 t (data_at' sh e t) pos)
                  (fun _ => True)
                  (fun f => 
                  (forall pos alignment, (nested_fields_pred local_legal_alignas_type f = true) -> 
                  (alignment > 0) ->
                  (alignof_hd f | pos) -> 
                  (alignof_fields f | alignment) -> (tl_ofs pos alignment f <= bound) -> 
                  @P3 f (sfieldlist_at' sh e f) alignment pos) /\
                  (forall pos size,  (nested_fields_pred local_legal_alignas_type f = true) -> 
                  (alignof_fields f | pos) ->
                  (sizeof_union f <= size) -> (pos + size <= bound) ->
                  @P4 f (ufieldlist_at' sh e f) size pos))); intros.
  + apply H; assumption.
  + apply H0; assumption.
  + apply H1; assumption.
  + apply H2; assumption.
  + apply H3; assumption.
  + apply H4; try assumption. (* array case *)
    intros; apply H18.
    - eapply nested_pred_Tarray; [exact H19|destruct H22; omega].
    - apply Z.divide_add_r. 
      * rewrite legal_alignas_type_Tarray in H20; [exact H20 | exact H19].
      * apply Z.divide_mul_l, legal_alignas_sizeof_alignof_compat.
        eapply nested_pred_Tarray; [exact H19|destruct H22; omega].
    - simpl in H21.
      destruct H22.
      replace (Z.max 0 z) with z in H21 by (apply eq_sym; apply Z.max_r; omega).
      assert (sizeof t0 * n <= sizeof t0 * (z - 1)).
        apply Zmult_le_compat_l; [| pose proof sizeof_pos t0; omega].
        omega.
      rewrite Zmult_minus_distr_l in H24.
      rewrite <- Zred_factor0 in H24.
      omega.
  + apply H5; assumption.
  + apply H6; try assumption. (* struct case *)
    assert (alignof_fields f | alignof (Tstruct i f a)) by
      (apply legal_alignas_type_Tstruct; exact H19).
    destruct H18 as [? _]; apply H18.
    - eapply nested_pred_Tstruct. exact H19.
    - apply alignof_pos.
    - eapply Zdivides_trans; [apply alignof_hd_divide |].
      eapply Zdivides_trans; [exact H22 | exact H20].
    - exact H22.
    - rewrite <- sizeof_Tstruct_tl_ofs; [exact H21| exact H19 |exact H20].
  + apply H7; try assumption. (* union case *)
    destruct H18 as [_ ?]; apply H18.
    - eapply nested_pred_Tunion. exact H19.
    - eapply Zdivides_trans; [apply legal_alignas_type_Tunion; exact H19|exact H20].
    - simpl.
      apply align_le.
      apply alignof_pos.
    - exact H21.
  + apply H8; assumption.
  + tauto.
  + tauto.
  + split; intros.
    - apply H9; assumption.
    - apply H12; assumption.
  + split; intros; destruct f.
    - apply H10; try assumption.
      apply H18; [eapply nested_fields_pred_hd; exact H20 | exact H22|].
      pose proof tl_ofs_cons_le pos0 alignment i t0 Fnil H21.
      omega.
    - assert (is_Fnil (Fcons i0 t1 f) = false) by reflexivity.
      forget (Fcons i0 t1 f) as ff.
      apply H11; try assumption.
      * apply H18; [eapply nested_fields_pred_hd; exact H20 | exact H22|].
        pose proof tl_ofs_cons_le pos0 alignment i t0 ff H21.
        omega.
      * destruct H19 as [? _].
        apply H19; [
          eapply nested_fields_pred_tl; exact H20 |
          exact H21 |
          apply align_divides; apply alignof_hd_pos|
          eapply Zdivides_trans; [apply alignof_fields_tl_divide | exact H23] |].
        simpl in H24; rewrite H25 in H24.
        exact H24.
    - apply H13; try assumption.
      apply H18; [
        eapply nested_fields_pred_hd; exact H20 |
        eapply Zdivides_trans; [apply alignof_fields_hd_divide | exact H21]
      |].
      simpl in H22.
      pose proof Z.le_max_l (sizeof t0) 0.
      omega.
    - assert (is_Fnil (Fcons i0 t1 f) = false) by reflexivity.
      forget (Fcons i0 t1 f) as ff.
      apply H14; try assumption.
      * apply H18; [
          eapply nested_fields_pred_hd; exact H20 |
          eapply Zdivides_trans; [apply alignof_fields_hd_divide | exact H21]
        |].
        simpl in H22.
        pose proof Z.le_max_l (sizeof t0) (sizeof_union ff).
        omega.
      * destruct H19 as [_ ?].
        apply H19; [
          eapply nested_fields_pred_tl; exact H20 |
          eapply Zdivides_trans; [apply alignof_fields_tl_divide | exact H21]|
          | exact H23].
        simpl in H22.
        pose proof Z.le_max_r (sizeof t0) (sizeof_union ff).
        omega.
  + assumption.
  + assumption.
  + assumption.
Qed.

Lemma data_at'_env_changable: forall (sh: Share.t) (e1 e2: type_id_env) (t: type), data_at' sh e1 t = data_at' sh e2 t.
Proof.
  intros.
  apply (type_mut (fun t => data_at' sh e1 t = data_at' sh e2 t) (fun _ => True) (fun flds => (forall alignment: Z, sfieldlist_at' sh e1 flds alignment = sfieldlist_at' sh e2 flds alignment) /\ (forall size: Z, ufieldlist_at' sh e1 flds size = ufieldlist_at' sh e2 flds size))); intros; try reflexivity. (* Happily, Tcomp_ptr case is solved by reflexivity automatically. *)
  + simpl. rewrite H. reflexivity. (* About array *)
  + simpl. destruct H as [? _]. apply H. (* About struct *)
  + simpl. destruct H as [_ ?]. apply H. (* About union *)
  + simpl. split; reflexivity.  (* Fnil case of fieldlist induction *)
  + destruct H0. simpl. split; intros. (* Fcons case of fieldlist induction *)
    rewrite H, H0. reflexivity.
    rewrite H, H1. reflexivity.
Qed.

Lemma data_at'_type_changable: forall (sh: Share.t) (e: type_id_env) (t1 t2: type) (pos: Z) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at' sh e t1 pos v1 = data_at' sh e t2 pos v2.
Proof.
  intros.
  subst t2.
  rewrite H0.
  reflexivity.
Qed.

Lemma data_at_type_changable: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at sh t1 v1 = data_at sh t2 v2.
Proof.
  intros.
  unfold data_at.
  simpl. extensionality.
  erewrite data_at'_type_changable; [| exact H| exact H0].
  rewrite H.
  reflexivity.
Qed.

Lemma by_value_default_val: forall t:type, 
  type_is_by_value t -> JMeq (default_val t) Vundef.
Proof.
  intros.
  destruct t; try tauto.
Qed.

(************************************************

local_facts, isptr and offset_zero properties of array_at', data_at', data_at
and data_at_.

************************************************)

Lemma array_at'_local_facts: forall t sh tmap f lo hi p,
  array_at' t sh tmap f lo hi p |-- !! (isptr p).
Proof.
  intros.
  unfold array_at'.
  normalize.
Qed.

Lemma data_at'_local_facts:
  forall sh e t pos v p, data_at' sh e t pos v p |-- !!(isptr p).
Proof.
  intros.
  revert p.
  apply (type_mut (fun (t: type) => forall pos v p, (data_at' sh e t pos v p |-- !!(isptr p))) (fun _ => True) (fun flds => (forall alignment pos v p, sfieldlist_at' sh e flds alignment pos v p |-- !!(isptr p)) /\ (forall alignment pos v p, ufieldlist_at' sh e flds alignment pos v p |-- !!(isptr p)))); intros; auto; simpl; 
  try (unfold at_offset2; apply (@at_offset'_preserve_local_facts val); intros; apply mapsto_local_facts);
  try (unfold at_offset2; apply (@at_offset'_preserve_local_facts val); intros; apply memory_block_local_facts).
  + unfold at_offset2; apply (@at_offset'_preserve_local_facts val). intros. (* Array case *)
    apply array_at'_local_facts.
  + destruct H. apply H. (* struct case *)
  + destruct H. apply H0. (* union case *)
  + split; intros. (* Fnil case of fieldlist induction *)
    - normalize.
    - destruct (Zeq_bool alignment 0); normalize.
  + destruct H0. split; intros.
    - destruct (is_Fnil f).
      * apply withspacer_preserve_local_facts; intros. apply H.
      * change derives with (@predicates_hered.derives compcert_rmaps.RML.R.rmap compcert_rmaps.R.ag_rmap).
        change mpred with (@predicates_hered.pred compcert_rmaps.RML.R.rmap compcert_rmaps.R.ag_rmap).
        eapply (right_is_prop (!!isptr p) _); [apply prop_is_prop|].
        apply withspacer_preserve_local_facts; intros. apply H.
    - destruct (is_Fnil f).
      * apply withspacer_preserve_local_facts; intros. apply H.
      * destruct v0; [apply withspacer_preserve_local_facts; intros; apply H | apply H1].
Qed.

Lemma array_at'_isptr: forall t sh tmap f lo hi p,
  array_at' t sh tmap f lo hi p = !! (isptr p) && array_at' t sh tmap f lo hi p.
Proof. intros. rewrite <- local_facts_isptr. reflexivity. apply array_at'_local_facts. Qed.

Lemma array_at'_offset_zero: forall t sh tmap f lo hi p,
  array_at' t sh tmap f lo hi p = array_at' t sh tmap f lo hi (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity. apply array_at'_local_facts. Qed.

Lemma data_at'_isptr:
  forall sh e t pos v p, data_at' sh e t pos v p = !!(isptr p) && data_at' sh e t pos v p.
Proof. intros. rewrite <- local_facts_isptr. reflexivity. apply data_at'_local_facts. Qed.

Lemma data_at'_offset_zero:
  forall sh e t pos v p, data_at' sh e t pos v p = data_at' sh e t pos v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity. apply data_at'_local_facts. Qed.

Lemma data_at_local_facts: forall sh t v p, data_at sh t v p |-- !!(isptr p).
Proof. intros. unfold data_at. simpl. apply andp_left2. apply data_at'_local_facts. Qed.
Hint Resolve data_at_local_facts : saturate_local.

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = !!(isptr p) && data_at sh t v p.
Proof. intros. rewrite <- local_facts_isptr. reflexivity. apply data_at_local_facts. Qed.

Lemma data_at_offset_zero: forall sh t v p, data_at sh t v p = data_at sh t v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity. apply data_at_local_facts. Qed.

Lemma data_at__local_facts: forall sh t p, data_at_ sh t p |-- !!(isptr p).
Proof. intros. unfold data_at_. apply data_at_local_facts. Qed.
Hint Resolve data_at__local_facts : saturate_local.

Lemma data_at__isptr: forall sh t p, data_at_ sh t p = !!(isptr p) && data_at_ sh t p.
Proof. intros. unfold data_at_. apply data_at_isptr. Qed.

Lemma data_at__offset_zero: forall sh t p, data_at_ sh t p = data_at_ sh t (offset_val Int.zero p).
Proof. intros. unfold data_at_. apply data_at_offset_zero. Qed.

Hint Rewrite <- data_at__offset_zero: norm.
Hint Rewrite <- data_at_offset_zero: norm.
Hint Rewrite <- data_at__offset_zero: cancel.
Hint Rewrite <- data_at_offset_zero: cancel.

(************************************************

Transformation between data_at/data_at_ and mapsto.

************************************************)

Definition uncompomize (e: type_id_env) (t: type) : type :=
  match t with
  | Tcomp_ptr i a => Tpointer (look_up_ident_default i e) a
  | _ => t
  end.

Lemma uncompomize_reptype: forall e t, reptype (uncompomize e t) = reptype t.
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma uncompomize_valinject: forall e t v, JMeq (valinject (uncompomize e t) v) (valinject t v).
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma uncompomize_default_val: forall e t, JMeq (default_val (uncompomize e t)) (default_val t).
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma uncompomize_data_at: forall sh e t v v' p,
  JMeq v v' ->
  data_at sh t v p = data_at sh (uncompomize e t) v' p.
Proof.
  intros.
  destruct t; simpl in *; rewrite H; reflexivity.
Qed.

Lemma by_value_reptype: forall t, type_is_by_value t -> reptype t = val.
Proof.
  intros.
  destruct t; simpl in H; tauto.
Qed.

Lemma by_value_data_at: forall sh t v v' p,
  type_is_by_value t ->
  JMeq v v' ->
  data_at sh t v p = (!! size_compatible t p) && (!! align_compatible t p) && mapsto sh t p v'.
Proof.
  intros.
  destruct t; simpl in H; try tauto; simpl in v;
  try (unfold data_at; simpl; rewrite H0; apply pred_ext; normalize).
Qed.

Lemma uncompomize_by_value_data_at: forall sh e t v v' p,
  type_is_by_value (uncompomize e t) ->
  JMeq v v' ->
  data_at sh t v p = 
  (!! size_compatible (uncompomize e t) p) &&
  (!! align_compatible (uncompomize e t) p) &&
  mapsto sh (uncompomize e t) p v'.
Proof.
  intros.
  remember v as v'' eqn:HH. 
  assert (JMeq v'' v) by (subst; reflexivity); clear HH.
  revert v H1.
  pattern (reptype t) at 1 3. rewrite <- (uncompomize_reptype e t).
  intros.  
  erewrite <- by_value_data_at; [|exact H | rewrite <- H0; rewrite H1; reflexivity].
  apply uncompomize_data_at.
  exact H1.
Qed.

Lemma by_value_data_at_: forall sh t p,
  type_is_by_value t ->
  data_at_ sh t p = (!! size_compatible t p) && (!! align_compatible t p) && mapsto_ sh t p.
Proof.
  intros.
  destruct t; simpl in H; try tauto;
  try (unfold data_at_, data_at; simpl; apply pred_ext; normalize).
Qed.

Lemma uncompomize_by_value_data_at_: forall sh e t p,
  type_is_by_value (uncompomize e t) ->
  data_at_ sh t p = 
  (!! size_compatible (uncompomize e t) p) &&
  (!! align_compatible (uncompomize e t) p) &&
  mapsto_ sh (uncompomize e t) p.
Proof.
  intros.
  unfold data_at_, mapsto_.
  apply uncompomize_by_value_data_at; [exact H|].
  erewrite <- uncompomize_default_val.
  apply by_value_default_val.
  exact H.
Qed.

Lemma lifted_by_value_data_at: forall sh t v p,
  type_is_by_value t ->
  `(data_at sh t) (`(valinject t) v) p =
  `prop (`(size_compatible t) p) &&
  `prop (`(align_compatible t) p) && `(mapsto sh t) p v.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply by_value_data_at; [|apply valinject_JMeq]; assumption.
Qed.

Lemma lifted_uncompomize_by_value_data_at: forall sh e t v p,
  type_is_by_value (uncompomize e t) ->
  `(data_at sh t) (`(valinject t) v) p =
  `prop (`(size_compatible (uncompomize e t)) p) &&
  `prop (`(align_compatible (uncompomize e t)) p) &&
  `(mapsto sh (uncompomize e t)) p v.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply uncompomize_by_value_data_at;
  [|erewrite <- uncompomize_valinject; apply valinject_JMeq]; eassumption.
Qed.

Lemma lifted_by_value_data_at_: forall sh t p,
  type_is_by_value t ->
  `(data_at_ sh t) p =
  `prop (`(size_compatible t) p) &&
  `prop (`(align_compatible t) p) && `(mapsto_ sh t) p.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply by_value_data_at_; assumption.
Qed.

Lemma lifted_uncompomize_by_value_data_at_: forall sh e t p,
  type_is_by_value (uncompomize e t) ->
  `(data_at_ sh t) p =
  `prop (`(size_compatible (uncompomize e t)) p) &&
  `prop (`(align_compatible (uncompomize e t)) p) &&
  `(mapsto_ sh (uncompomize e t)) p.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply uncompomize_by_value_data_at_; assumption.
Qed.

(************************************************

Transformation between data_at and data_at'. This is used in transformation
between field_at and data_at.

************************************************)

Lemma lower_sepcon_val':
  forall (P Q: val->mpred) v, 
  ((P*Q) v) = (P v * Q v).
Proof. reflexivity. Qed.

Lemma data_at'_at_offset': forall sh t v pos,
  (legal_alignas_type t = true) ->
  (alignof t | pos) ->
  data_at' sh empty_ti t pos v = at_offset' (data_at' sh empty_ti t 0 v) pos.
Proof.
  intros.
  extensionality p.
  rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity].
  replace (data_at' sh empty_ti t pos) with (data_at' sh empty_ti t (pos + 0)) by
    (replace (pos + 0) with pos by omega; reflexivity).
  apply (data_at'_mut sh empty_ti (0 + sizeof t) 
        (fun t data_at'_pred pos' => (alignof t | pos) -> forall v p, 
        data_at'_pred (pos + pos') v p = data_at'_pred pos' v (offset_val (Int.repr pos) p))
        (fun f sfieldlist_at'_pred alignment pos' => 
        (alignment | pos) -> forall v p,
        sfieldlist_at'_pred alignment (pos + pos') v p = 
        sfieldlist_at'_pred alignment pos' v (offset_val (Int.repr pos) p))
        (fun f ufieldlist_at'_pred size pos' =>
        (alignof_fields f | pos) -> forall v p,
        ufieldlist_at'_pred size (pos + pos') v p = 
        ufieldlist_at'_pred size pos' v (offset_val (Int.repr pos) p)));
    intros;
    try constructor;
    try omega;
    try (simpl;
         unfold at_offset2;
         rewrite at_offset'_eq2; [reflexivity |];
         try (intros; rewrite <- memory_block_offset_zero; reflexivity);
         try (intros; rewrite <- mapsto_offset_zero; reflexivity)).
  + intros. (* Tarray case *)
    rewrite <- array_at'_offset_zero.
    reflexivity.
  + simpl. (* Tstruct case *)
    apply H4, H5.
  + simpl. (* Tunion case *)
    apply H4.
    eapply Zdivides_trans; [apply legal_alignas_type_Tunion; exact H1 | exact H5].
  + simpl. normalize.
  + simpl.
    rewrite <- withspacer_add.
    repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    rewrite H6; [rewrite divide_add_align; [rewrite Z.add_assoc; reflexivity | exact H7]|].
    eapply Zdivides_trans; [|exact H7].
    eapply Zdivides_trans; [apply alignof_fields_hd_divide |exact H4].
  + revert v0; simpl.
    rewrite H6; intros.
    assert (alignof_hd f | pos) by (
      eapply Zdivides_trans; [|exact H9];
      eapply Zdivides_trans; [|exact H4];
      eapply Zdivides_trans; [apply alignof_hd_divide|apply alignof_fields_tl_divide]).
    rewrite <- withspacer_add.
    repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    rewrite H7; [rewrite <- (H8 H9)|]. Focus 2.
    eapply Zdivides_trans; [|exact H9].
    eapply Zdivides_trans; [apply alignof_fields_hd_divide |exact H4].
    rewrite divide_add_align; [rewrite Z.add_assoc; reflexivity | exact H10].
  + simpl. normalize.
  + simpl.
    rewrite <- withspacer_add.
    repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    rewrite H5; [repeat rewrite Z.add_assoc; reflexivity|].
    eapply Zdivides_trans; [apply alignof_fields_hd_divide | exact H6].
  + revert v0; simpl.
    rewrite H5; intros.
    destruct v0.
    - rewrite <- withspacer_add.
      repeat rewrite withspacer_spacer.
      repeat rewrite lower_sepcon_val'.
      rewrite H6; [repeat rewrite Z.add_assoc; reflexivity |].
      eapply Zdivides_trans; [apply alignof_fields_hd_divide | exact H8].
    - rewrite H7; [reflexivity |].
      eapply Zdivides_trans; [apply alignof_fields_tl_divide | exact H8].
  + assumption.
  + apply Z.divide_0_r.
  + exact H0.
Qed.

Lemma data_at'_data_at: forall sh t v pos,
  (legal_alignas_type t = true) ->
  (alignof t | pos) ->
  (fun p => !! (size_compatible t (offset_val (Int.repr pos) p)
             /\ align_compatible t (offset_val (Int.repr pos) p))) &&
  data_at' sh empty_ti t pos v = at_offset' (data_at sh t v) pos.
Proof.
  intros.
  extensionality p.
  rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
  unfold data_at.
  simpl.
  rewrite data_at'_at_offset'; auto.
  rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity].
  reflexivity.
Qed.

Lemma memory_block_data_at_: forall (sh : share) (t : type),
  legal_alignas_type t = true ->
  nested_non_volatile_type t = true ->
  (fun p => !! (align_compatible t p)) &&
  memory_block sh (Int.repr (sizeof t)) = data_at_ sh t.
Proof.
  intros.
  simpl.
  extensionality p.
  destruct p;
    try (rewrite memory_block_isptr;
     rewrite data_at__isptr;
     apply pred_ext; normalize; reflexivity).
  unfold data_at_, data_at.
  simpl.
  admit.
  (* To prove this lemma, we need non-volatility *)
(*
  apply (data_at'_mut sh empty_ti (Int.modulus - Int.unsigned i)
    (fun t data_at'_pred pos =>
    memory_block sh (Int.repr (sizeof t)) (offset_val (Int.repr pos) (Vptr b i)) =
    data_at'_pred pos (default_val t) (Vptr b i))
    (fun f sfieldlist_at'_pred alignment pos =>
    memory_block sh (Int.repr (tl_ofs pos alignment f - pos)) (offset_val (Int.repr pos) (Vptr b i)) =
    sfieldlist_at'_pred alignment pos (struct_default_val f) (Vptr b i))
    (fun f ufieldlist_at'_pred size pos =>
    memory_block sh (Int.repr size) (offset_val (Int.repr pos) (Vptr b i)) =
    ufieldlist_at'_pred size pos (union_default_val f) (Vptr b i)));
    intros;
    try (unfold data_at', at_offset2; 
         try (rewrite at_offset'_eq; [|apply memory_block_offset_zero]);
         try (rewrite at_offset'_eq; [|apply mapsto_offset_zero]);
         try (rewrite mapsto_mapsto_; rewrite <- memory_block_mapsto_);
          reflexivity).
    unfold data_at', at_offset2.
         try (rewrite at_offset'_eq; [|apply mapsto_offset_zero]).
         simpl default_val. 
         erewrite memory_block_mapsto_; [unfold mapsto_; reflexivity | | exact H0 | simpl;destruct i0;reflexivity | simpl offset_val;unfold size_compatible |].
       *)  
Qed.

Lemma align_1_memory_block_data_at_: forall (sh : share) (t : type),
  legal_alignas_type t = true ->
  nested_non_volatile_type t = true ->
  alignof t = 1 ->
  memory_block sh (Int.repr (sizeof t)) = data_at_ sh t.
Proof.
  intros.
  rewrite <- memory_block_data_at_ by auto.
  rewrite andp_comm.
  apply add_andp.
  go_lower.
  apply prop_right.
  unfold align_compatible.
  rewrite H1.
  destruct rho; auto.
  apply Z.divide_1_l.
Qed.

Lemma data_at_non_volatile: forall sh t v p, 
  data_at sh t v p |-- !! (nested_non_volatile_type t = true).
Proof.
  admit.
Qed.

Lemma data_at'_data_at'_ : forall sh e t v pos b i, 
  legal_alignas_type t = true ->
  Int.unsigned i + pos + sizeof t <= Int.modulus ->
  (alignof t | pos) ->
  (alignof t | Int.unsigned i) ->
  data_at' sh e t pos v (Vptr b i) |-- data_at' sh e t pos (default_val t) (Vptr b i).
Proof.
  intros.
  assert (pos + sizeof t <= Int.modulus - Int.unsigned i) by omega; clear H0.

  apply (data_at'_mut sh e (Int.modulus - Int.unsigned i)
    (fun t data_at'_pred pos => forall v p, data_at'_pred pos v p |-- data_at'_pred pos (default_val t) p)
    (fun f sfieldlist_at'_pred alignment pos => forall v p, sfieldlist_at'_pred alignment pos v p |-- sfieldlist_at'_pred alignment pos (struct_default_val f) p)
    (fun f ufieldlist_at'_pred alignment pos => forall v p, ufieldlist_at'_pred alignment pos v p |-- ufieldlist_at'_pred alignment pos (union_default_val f) p));
  intros; simpl data_at'; simpl sfieldlist_at'; simpl ufieldlist_at';
  try (apply derives_refl; reflexivity);
  try (unfold at_offset2; eapply derives_trans; 
    [apply at_offset_derives; go_lower; apply mapsto_mapsto_; reflexivity |
    unfold mapsto_; apply derives_refl; reflexivity]);
  try tauto.
  + admit. (* Tarray case *)
    (* Need to figure out whether the current definition in default value is correct. *)
  + apply H6. (* Tstruct case *)
  + apply H6. (* Tunion case *)
  + repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    cancel.
  + revert v0; simpl; rewrite H8; intros.
    repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    cancel.
  + repeat rewrite withspacer_spacer.
    repeat rewrite lower_sepcon_val'.
    cancel.
  + revert v0; simpl; rewrite H7; intros.
    destruct v0.
    - repeat rewrite withspacer_spacer.
      repeat rewrite lower_sepcon_val'.
      cancel.
    - admit.
Qed.

Lemma data_at_data_at_ : forall sh t v p, 
  legal_alignas_type t = true ->
  data_at sh t v p |-- data_at_ sh t p.
Proof.
  intros.
  destruct p;
    try (rewrite data_at_isptr;
     rewrite data_at__isptr;
     normalize; reflexivity).
  unfold data_at_, data_at.
  simpl.
  normalize.
  apply data_at'_data_at'_.
  + exact H.
  + omega.
  + apply Z.divide_0_r.
  + exact H1.
Qed.

Hint Resolve data_at_data_at_: cancel.

(**********************************************

Here, we need to think about how to use array in examples.

**********************************************)

Definition offset_in_range ofs p :=
  match p with
  | Vptr b iofs => 0 <= Int.unsigned iofs + ofs <= Int.modulus
  | _ => True
  end.

Definition offset_strict_in_range ofs p :=
  match p with
  | Vptr b iofs => 0 <= Int.unsigned iofs + ofs < Int.modulus
  | _ => True
  end.

Definition array_at (t: type) (sh: Share.t) (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) : mpred :=
  !! isptr v && !! offset_in_range (sizeof t * lo) v && !! offset_in_range (sizeof t * hi) v
  && !! align_compatible t v && rangespec lo hi (fun i => data_at sh t (f i) (add_ptr_int t v i)).

Definition array_at_ t sh lo hi := array_at t sh (fun _ => default_val t) lo hi.

Lemma data_at_tint: forall sh v2 v1,
  data_at sh tint v2 v1 = mapsto sh tint v1 v2.
Proof.
  intros.
  unfold data_at, data_at'.
  simpl.
  apply pred_ext; normalize.
  apply andp_right; [|normalize].
  unfold mapsto. simpl.
  destruct v1; normalize.
  unfold address_mapsto, res_predicates.address_mapsto, size_compatible, align_compatible.
  admit.
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

Lemma spacer_memory_block:
  forall sh be ed v, isptr v -> 
 spacer sh be ed v = memory_block sh (Int.repr (ed - be)) (offset_val (Int.repr be) v).
Proof.
  intros.
  destruct v; inv H.
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);
  try solve [rewrite e; simpl offset_val; rewrite memory_block_zero; auto].
  unfold at_offset'.
  destruct be; auto.
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

(*
Lemma memory_block_typed': forall sh e pos ty b ofs, 
  no_attr_type ty = true ->
  spacer sh pos (align pos (alignof ty)) (Vptr b ofs) *
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

Lemma memory_block_typed: 
 forall sh ty, 
  no_attr_type ty = true ->
   memory_block sh (Int.repr (sizeof ty)) = data_at_ sh ty.
Proof.
intros.
extensionality v.
rewrite memory_block_isptr.
rewrite data_at__isptr.
destruct v; simpl; normalize.
unfold data_at_, data_at; simpl; rewrite <- memory_block_typed'; auto.
unfold spacer.
rewrite align_0 by (apply alignof_pos).
simpl. rewrite emp_sepcon.
rewrite Int.add_zero. auto.
Qed.
*)

Lemma var_block_data_at_:
  forall  sh id t, 
  legal_alignas_type t = true ->
  nested_non_volatile_type t = true ->
  var_block sh (id, t) = 
   !!(sizeof t <= Int.max_unsigned) &&
            `(data_at_ sh t) (eval_var id t).
Proof.
  intros; extensionality rho.
  unfold_lift.
  rewrite <- memory_block_data_at_ by auto.
  unfold var_block.
  simpl. unfold local, lift1. unfold_lift.
  rewrite memory_block_isptr.
  unfold align_compatible.
  destruct (eval_var id t rho); simpl in *; normalize.
  apply pred_ext; normalize.
Qed.

Lemma array_at_local_facts:
 forall t sh f lo hi v,
    array_at t sh f lo hi v |-- !! isptr v.
Proof.
 intros.
 unfold array_at; normalize.
Qed.

Hint Resolve array_at_local_facts : saturate_local.

Lemma array_at_isptr:
  forall t sh f lo hi v, array_at t sh f lo hi v = array_at t sh f lo hi v && !!isptr v.
Proof.
intros.
apply pred_ext; intros.
apply andp_right; auto. apply array_at_local_facts.
normalize.
Qed.

Lemma array_at__local_facts:
 forall t sh lo hi v,
    array_at_ t sh lo hi v |-- !! isptr v.
Proof.
 intros.
 apply array_at_local_facts; auto.
Qed.

Hint Resolve array_at__local_facts : saturate_local.

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

