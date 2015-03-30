Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.rangespec_lemmas.
Require Import Coq.Logic.JMeq.
Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

(******************************************

Definition of reptype.

******************************************)

Section CENV.
Print func_type.

Print type_is_by_value.
Context {cs: compspecs}. 

Definition reptype: type -> Type :=
  func_type (fun _ => Type)
  (fun t =>
     if ((type_is_by_value t) && negb (type_is_volatile t))%bool
     then val
     else unit)
  (fun t n a T => list T)
  (fun id a co T => compact_prod (decay T))
  (fun id a co T => compact_sum (decay T)).

Lemma reptype_ind: forall t,
  reptype t = 
  match t with
  | Tarray t0 _ _ => list (reptype t0)
  | Tstruct id _ =>
      match cenv_cs ! id with
      | Some co => compact_prod (map reptype (map snd (co_members co)))
      | _ => unit
      end
  | Tunion id _ =>
      match cenv_cs ! id with
      | Some co => compact_sum (map reptype (map snd (co_members co)))
      | _ => unit
      end
  | _ => if ((type_is_by_value t) && negb (type_is_volatile t))%bool
      then val
      else unit
  end.
Proof.
  intros.
  unfold reptype.
  rewrite func_type_ind with (t0 := t) at 1 by auto.
  destruct t; auto.
  + destruct (cenv_cs ! i); auto.
    f_equal.
    rewrite decay_spec.
    rewrite map_map.
    rewrite map_map.
    reflexivity.
  + destruct (cenv_cs ! i); auto.
    f_equal.
    rewrite decay_spec.
    rewrite map_map.
    rewrite map_map.
    reflexivity.
Qed.

Definition reptype': type -> Type :=
  func_type (fun _ => Type)
  (fun t =>
     if ((type_is_by_value t) && negb (type_is_volatile t))%bool
     then match t with
          | Tint _ _ _ => int
          | Tlong _ _ => Int64.int
          | Tfloat _ _ => float
          | _ => val
          end
     else unit)
  (fun t n a T => list T)
  (fun id a co T => compact_prod (decay T))
  (fun id a co T => compact_sum (decay T)).

Lemma reptype'_ind: forall t, 
  reptype' t = 
  match t with
  | Tarray t0 _ _ => list (reptype' t0)
  | Tstruct id _ =>
      match cenv_cs ! id with
      | Some co => compact_prod (map reptype' (map snd (co_members co)))
      | _ => unit
      end
  | Tunion id _ =>
      match cenv_cs ! id with
      | Some co => compact_sum (map reptype' (map snd (co_members co)))
      | _ => unit
      end
  | _ => if ((type_is_by_value t) && negb (type_is_volatile t))%bool
      then match t with
           | Tint _ _ _ => int
           | Tlong _ _ => Int64.int
           | Tfloat _ _ => float
           | _ => val
           end
      else unit
  end.
Proof.
  intros.
  unfold reptype'.
  rewrite func_type_ind with (t0 := t) at 1 by auto.
  destruct t; auto.
  + destruct (cenv_cs ! i); auto.
    f_equal.
    rewrite decay_spec.
    rewrite map_map.
    rewrite map_map.
    reflexivity.
  + destruct (cenv_cs ! i); auto.
    f_equal.
    rewrite decay_spec.
    rewrite map_map.
    rewrite map_map.
    reflexivity.
Qed.

Definition repinj: forall t: type, reptype' t -> reptype t :=
  func_type (fun t => reptype' t -> reptype t)
  (fun t => if ((type_is_by_value t) && negb (type_is_volatile t))%bool
      then match t with
            | Tint _ _ _ => Vint
            | Tlong _ _ => Vlong
            | Tfloat _ _ => Vfloat
            | _ => id
            end)
  (fun t n a f v => map f v)
  (fun id a co F

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

Lemma valinject_JMeq: forall t v, type_is_by_value t = true -> JMeq (valinject t v) v.
Proof.
  intros.
  destruct t; simpl in *; try congruence; try tauto.
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
  apply (derives_left_sepcon_right_corable (!!isptr p) (P p) _); [apply corable_prop|].
  apply H.
Qed.

Transparent memory_block.

Lemma spacer_memory_block:
  forall sh be ed v, isptr v -> 
 spacer sh be ed v = memory_block sh (Int.repr (ed - be)) (offset_val (Int.repr be) v).
Proof.
  intros.
  destruct v; inv H.
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);
  try solve [rewrite e; simpl offset_val; rewrite memory_block_zero_Vptr; auto].
  unfold at_offset'.
  destruct be; auto.
  unfold offset_val; rewrite Int.add_zero; auto.
Qed.

Lemma withspacer_memory_block: forall sh be ed p,
  0 <= be <= ed ->
  ed < Int.modulus ->
  offset_in_range ed p ->
  withspacer sh be ed (memory_block sh (Int.repr be)) p = memory_block sh (Int.repr ed) p.
Proof.
  intros.
  rewrite withspacer_spacer; simpl.
  if_tac.
  + assert (ed = be) by omega; subst.
    apply emp_sepcon.
  + rewrite at_offset'_eq by (rewrite <- memory_block_offset_zero; reflexivity).
    destruct p; try solve [(simpl; apply FF_sepcon)].
    unfold offset_val, Int.add.
    pattern i at 2 3;  (* do it this way for compatibility with Coq 8.4pl3 *)
    replace i with (Int.repr (Int.unsigned i)) by apply Int.repr_unsigned.
    rewrite !Int.unsigned_repr by (unfold Int.max_unsigned; omega).
    simpl in H1.
    rewrite sepcon_comm.
    pose proof Int.unsigned_range i.
    rewrite <- memory_block_split by omega.
    f_equal; f_equal; omega.
Qed.
Opaque memory_block.

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

Definition array_at' (sh: Share.t) (t: type) (lo hi: Z) (P: Z -> reptype t -> val -> mpred) (pos: Z) (v: list (reptype t)) (p: val): mpred :=
  !! isptr p && rangespec lo hi (fun i => P (pos + sizeof t * i) (Znth (i - lo) v (default_val _))) p.

Fixpoint data_at' (sh: Share.t) (e: type_id_env) (t1: type): Z -> reptype t1 -> val -> mpred :=
  match t1 as t return (Z -> reptype t -> val -> mpred) with
  | Tvoid => at_offset2 (fun v _ => memory_block sh (Int.repr (sizeof t1)) v)
  | Tarray t z a => array_at' sh t 0 z (data_at' sh e t)
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
  (!! (legal_alignas_type t = true)) && (!! (nested_legal_fieldlist t = true)) &&
  (fun (_:reptype t) p => (!! (size_compatible t p /\ align_compatible t p))) 
  && data_at' sh empty_ti t 0.

Definition data_at_ (sh: Share.t) (t: type) := data_at sh t (default_val _).

Lemma data_at'_mut: forall sh e (bound: Z) 
  (P1: forall {t: type}, (Z -> reptype t -> val -> mpred) -> Z -> Prop) 
  (P3: forall {fld: fieldlist}, (Z -> Z -> reptype_structlist fld -> val -> mpred) -> Z -> Z -> Prop)
  (P4: forall {fld: fieldlist}, (Z -> Z -> reptype_unionlist fld -> val -> mpred) -> Z -> Z -> Prop),
  (forall pos, (legal_alignas_type Tvoid = true) -> 
    (alignof Tvoid | pos) -> 
    (0 <= pos /\ pos + sizeof Tvoid <= bound) -> 
    P1 (data_at' sh e Tvoid) pos) ->
  (forall pos i s a, 
    (legal_alignas_type (Tint i s a) = true) -> 
    (alignof (Tint i s a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tint i s a) <= bound) -> 
    P1 (data_at' sh e (Tint i s a)) pos) ->
  (forall pos s a,
    (legal_alignas_type (Tlong s a) = true) -> 
    (alignof (Tlong s a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tlong s a) <= bound) -> 
    P1 (data_at' sh e (Tlong s a)) pos) ->
  (forall pos f a, 
    (legal_alignas_type (Tfloat f a) = true) -> 
    (alignof (Tfloat f a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tfloat f a) <= bound) -> 
    P1 (data_at' sh e (Tfloat f a)) pos) ->
  (forall pos t a, 
    (legal_alignas_type (Tpointer t a) = true) -> 
    (alignof (Tpointer t a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tpointer t a) <= bound) -> 
    P1 (data_at' sh e (Tpointer t a)) pos) ->
  (forall pos t z a,
    (legal_alignas_type (Tarray t z a) = true) ->
    (alignof (Tarray t z a) | pos) ->
    (0 <= pos /\ pos + sizeof (Tarray t z a) <= bound) -> 
    (forall n, 0 <= n < z -> P1 (data_at' sh e t) (pos + (sizeof t) * n)) ->
    P1 (data_at' sh e (Tarray t z a)) pos) ->
  (forall pos t t0 c, 
    (legal_alignas_type (Tfunction t t0 c) = true) -> 
    (alignof (Tfunction t t0 c) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tfunction t t0 c) <= bound) -> 
    P1 (data_at' sh e (Tfunction t t0 c)) pos) ->
  (forall pos i f a, 
    (legal_alignas_type (Tstruct i f a) = true) -> 
    (alignof (Tstruct i f a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tstruct i f a) <= bound) -> 
    P3 (sfieldlist_at' sh e f) (alignof (Tstruct i f a)) pos ->
    P1 (data_at' sh e (Tstruct i f a)) pos) ->
  (forall pos i f a, 
    (legal_alignas_type (Tunion i f a) = true) -> 
    (alignof (Tunion i f a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tunion i f a) <= bound) -> 
    P4 (ufieldlist_at' sh e f) (sizeof (Tunion i f a)) pos ->
    P1 (data_at' sh e (Tunion i f a)) pos) ->
  (forall pos i a, 
    (legal_alignas_type (Tcomp_ptr i a) = true) -> 
    (alignof (Tcomp_ptr i a) | pos) -> 
    (0 <= pos /\ pos + sizeof (Tcomp_ptr i a) <= bound) -> 
    P1 (data_at' sh e (Tcomp_ptr i a)) pos) ->
  (forall pos alignment, 
    (nested_fields_pred local_legal_alignas_type Fnil = true) -> 
    (alignment > 0) ->
    (alignment | pos) ->
    (0 <= pos /\ pos <= bound) -> 
    P3 (sfieldlist_at' sh e Fnil) alignment pos) ->
  (forall pos alignment i t, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t Fnil) = true) -> 
    (alignment > 0) ->
    (alignof_hd (Fcons i t Fnil) | pos) -> 
    (alignof_fields (Fcons i t Fnil) | alignment) -> 
    (0 <= pos /\ tl_ofs pos alignment (Fcons i t Fnil) <= bound) -> 
    P1 (data_at' sh e t) pos ->
    P3 (sfieldlist_at' sh e (Fcons i t Fnil)) alignment pos) ->
  (forall pos alignment i t f, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t f) = true) -> 
    (alignment > 0) ->
    (alignof_hd (Fcons i t f) | pos) -> 
    (alignof_fields (Fcons i t f) | alignment) -> 
    (0 <= pos /\ tl_ofs pos alignment (Fcons i t f) <= bound) -> 
    is_Fnil f = false -> 
    P1 (data_at' sh e t) pos ->
    P3 (sfieldlist_at' sh e f) alignment (align (pos + sizeof t) (alignof_hd f)) ->
    P3 (sfieldlist_at' sh e (Fcons i t f)) alignment pos) ->
  (forall pos, 
    (nested_fields_pred local_legal_alignas_type Fnil = true) -> 
    (0 <= pos /\ pos <= bound) -> 
    P4 (ufieldlist_at' sh e Fnil) 0 pos) ->
  (forall pos size i t, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t Fnil) = true) -> 
    (alignof_fields (Fcons i t Fnil) | pos) ->
    (sizeof_union (Fcons i t Fnil) <= size) ->
    (0 <= pos /\ pos + size <= bound) ->
    P1 (data_at' sh e t) pos ->
    P4 (ufieldlist_at' sh e (Fcons i t Fnil)) size pos) ->
  (forall pos size i t f, 
    (nested_fields_pred local_legal_alignas_type (Fcons i t f) = true) -> 
    (alignof_fields (Fcons i t f) | pos) ->
    (sizeof_union (Fcons i t f) <= size) ->
    (0 <= pos /\ pos + size <= bound) ->
    is_Fnil f = false -> 
    P1 (data_at' sh e t) pos ->
    P4 (ufieldlist_at' sh e f) size pos ->
    P4 (ufieldlist_at' sh e (Fcons i t f)) size pos) ->
  forall pos t, 
    (legal_alignas_type t = true) -> 
    (alignof t | pos) -> 
    (0 <= pos /\ pos + sizeof t <= bound) -> 
    P1 (data_at' sh e t) pos.
Proof.
  intros.
  apply (type_mut (fun t => forall pos, (legal_alignas_type t = true) -> (alignof t | pos) -> 
                  (0 <= pos /\ pos + sizeof t <= bound) -> 
                  @P1 t (data_at' sh e t) pos)
                  (fun _ => True)
                  (fun f => 
                  (forall pos alignment, (nested_fields_pred local_legal_alignas_type f = true) -> 
                  (f = Fnil -> (alignment | pos)) ->
                  (alignment > 0) ->
                  (alignof_hd f | pos) -> 
                  (alignof_fields f | alignment) ->
                  (0 <= pos /\ tl_ofs pos alignment f <= bound) -> 
                  @P3 f (sfieldlist_at' sh e f) alignment pos) /\
                  (forall pos size,  (nested_fields_pred local_legal_alignas_type f = true) -> 
                  (f = Fnil -> size = 0) ->
                  (alignof_fields f | pos) ->
                  (sizeof_union f <= size) ->
                  (0 <= pos /\ pos + size <= bound) ->
                  @P4 f (ufieldlist_at' sh e f) size pos))); intros.
  + apply H; assumption.
  + apply H0; assumption.
  + apply H1; assumption.
  + apply H2; assumption.
  + apply H3; assumption.
  + apply H4; try assumption. (* array case *)
    intros; apply H18.
    - eapply nested_pred_Tarray; exact H19.
    - apply Z.divide_add_r. 
      * rewrite legal_alignas_type_Tarray in H20; [exact H20 | exact H19].
      * apply Z.divide_mul_l, legal_alignas_sizeof_alignof_compat.
        eapply nested_pred_Tarray; exact H19.
    - simpl in H21.
      destruct H22.
      replace (Z.max 0 z) with z in H21 by (apply eq_sym; apply Z.max_r; omega).
      assert (0 <= sizeof t0 * n <= sizeof t0 * (z - 1)).
      Focus 1. {
        pose proof sizeof_pos t0.
        split.
        + apply Z.mul_nonneg_nonneg; omega.
        + apply Zmult_le_compat_l; omega.
      } Unfocus.
      rewrite Zmult_minus_distr_l in H24.
      rewrite <- Zred_factor0 in H24.
      omega.
  + apply H5; assumption.
  + apply H6; try assumption. (* struct case *)
    assert (alignof_fields f | alignof (Tstruct i f a)) by
      (apply legal_alignas_type_Tstruct; exact H19).
    destruct H18 as [? _]; apply H18.
    - eapply nested_pred_Tstruct. exact H19.
    - intros; auto.
    - apply alignof_pos.
    - eapply Zdivides_trans; [apply alignof_hd_divide |].
      eapply Zdivides_trans; [exact H22 | exact H20].
    - exact H22.
    - rewrite <- sizeof_Tstruct_tl_ofs; [exact H21| exact H19 |exact H20].
  + apply H7; try assumption. (* union case *)
    destruct H18 as [_ ?]; apply H18.
    - eapply nested_pred_Tunion. exact H19.
    - intros; subst; simpl.
      apply align_0, alignof_pos.
    - eapply Zdivides_trans; [apply legal_alignas_type_Tunion; exact H19|exact H20].
    - simpl.
      apply align_le.
      apply alignof_pos.
    - exact H21.
  + apply H8; assumption.
  + tauto.
  + tauto.
  + split; intros.
    - specialize (H19 eq_refl).
      simpl in H23. rewrite divide_align in H23 by assumption.
      apply H9; try assumption.
    - rewrite (H19 eq_refl) in H22 |- *.
      apply H12. assumption. omega.
  + split; intros; destruct f.
    - apply H10; try assumption.
      apply H18; [eapply nested_fields_pred_hd; exact H20 | exact H23|].
      pose proof tl_ofs_cons_le pos0 alignment i t0 Fnil H22.
      omega.
    - assert (is_Fnil (Fcons i0 t1 f) = false) by reflexivity.
      forget (Fcons i0 t1 f) as ff.
      apply H11; try assumption.
      * apply H18; [eapply nested_fields_pred_hd; exact H20 | exact H23|].
        pose proof tl_ofs_cons_le pos0 alignment i t0 ff H22.
        omega.
      * destruct H19 as [? _].
        apply H19; [
          eapply nested_fields_pred_tl; exact H20 |
          intro; rewrite H27 in H26; inversion H26 |
          exact H22 |
          apply align_divides; apply alignof_hd_pos|
          eapply Zdivides_trans; [apply alignof_fields_tl_divide | exact H24] |].
        split; destruct H25. {
          pose proof sizeof_pos t0.
          eapply Z.le_trans; [| apply align_le]; [omega | apply alignof_hd_pos].
        } {
          simpl in H27; rewrite H26 in H27.
          exact H27.
        }
    - apply H13; try assumption.
      apply H18; [
        eapply nested_fields_pred_hd; exact H20 |
        eapply Zdivides_trans; [apply alignof_fields_hd_divide | exact H22]
      |].
      simpl in H23.
      pose proof Z.le_max_l (sizeof t0) 0.
      omega.
    - assert (is_Fnil (Fcons i0 t1 f) = false) by reflexivity.
      forget (Fcons i0 t1 f) as ff.
      apply H14; try assumption.
      * apply H18; [
          eapply nested_fields_pred_hd; exact H20 |
          eapply Zdivides_trans; [apply alignof_fields_hd_divide | exact H22]
        |].
        simpl in H23.
        pose proof Z.le_max_l (sizeof t0) (sizeof_union ff).
        omega.
      * destruct H19 as [_ ?].
        apply H19; [
          eapply nested_fields_pred_tl; exact H20 |
          intro; rewrite H26 in H25; inversion H25 |
          eapply Zdivides_trans; [apply alignof_fields_tl_divide | exact H22]|
          | exact H24].
        simpl in H23.
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
  type_is_by_value t = true -> JMeq (default_val t) Vundef.
Proof.
  intros.
  destruct t; try inversion H; try tauto.
Qed.

(************************************************

local_facts, isptr and offset_zero properties of array_at', data_at', data_at
and data_at_.

************************************************)

Lemma array_at'_local_facts: forall sh t lo hi P pos v p,
  array_at' sh t lo hi P pos v p |-- !! (isptr p).
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
  + apply array_at'_local_facts.
  + destruct H. apply H. (* struct case *)
  + destruct H. apply H0. (* union case *)
  + split; intros. (* Fnil case of fieldlist induction *)
    - normalize.
    - destruct (Zeq_bool alignment 0); normalize.
  + destruct H0. split; intros.
    - destruct (is_Fnil f).
      * apply withspacer_preserve_local_facts; intros. apply H.
      * eapply (derives_left_sepcon_right_corable (!!isptr p) _); [apply corable_prop|].
        apply withspacer_preserve_local_facts; intros. apply H.
    - destruct (is_Fnil f).
      * apply withspacer_preserve_local_facts; intros. apply H.
      * destruct v0; [apply withspacer_preserve_local_facts; intros; apply H | apply H1].
Qed.

Lemma array_at'_isptr: forall sh t lo hi P pos v p,
  array_at' sh t lo hi P pos v p = !! (isptr p) && array_at' sh t lo hi P pos v p.
Proof. intros. rewrite <- local_facts_isptr. reflexivity. apply array_at'_local_facts. Qed.

Lemma array_at'_offset_zero: forall sh t lo hi P pos v p,
  array_at' sh t lo hi P pos v p = array_at' sh t lo hi P pos v (offset_val Int.zero p).
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

Lemma nested_legal_fieldlist_uncompomize: forall e t,
  nested_legal_fieldlist (uncompomize e t) = nested_legal_fieldlist t.
Proof.
  intros.
  destruct t; reflexivity.
Qed.

Lemma legal_alignas_type_uncompomize: forall e t,
  legal_alignas_type (uncompomize e t) = legal_alignas_type t.
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

Lemma by_value_reptype: forall t, type_is_by_value t = true -> reptype t = val.
Proof.
  intros.
  destruct t; simpl in H; try inversion H; tauto.
Qed.

Lemma by_value_data_at: forall sh t v v' p,
  type_is_by_value t = true ->
  JMeq v v' ->
  data_at sh t v p = !! field_compatible t nil p && mapsto sh t p v'.
Proof.
  intros.
  unfold field_compatible.
  pose proof legal_nested_field_nil_lemma t.
  rewrite data_at_isptr.
  destruct t; simpl in H; try inversion H; try tauto; simpl in v;
  try (unfold data_at; simpl; rewrite H0; apply pred_ext; normalize).
Qed.

Lemma uncompomize_by_value_data_at: forall sh e t v v' p,
  type_is_by_value (uncompomize e t) = true ->
  JMeq v v' ->
  data_at sh t v p =
  !! field_compatible (uncompomize e t) nil p && mapsto sh (uncompomize e t) p v'.
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
  type_is_by_value t = true ->
  data_at_ sh t p = !! field_compatible t nil p && mapsto_ sh t p.
Proof.
  intros.
  unfold data_at_, mapsto_.
  destruct t; simpl in H; try inversion H; try tauto; simpl default_val;
  apply by_value_data_at; reflexivity.
Qed.

Lemma uncompomize_by_value_data_at_: forall sh e t p,
  type_is_by_value (uncompomize e t) = true ->
  data_at_ sh t p =
  !! field_compatible (uncompomize e t) nil p && mapsto_ sh (uncompomize e t) p.
Proof.
  intros.
  unfold data_at_, mapsto_.
  apply uncompomize_by_value_data_at; [exact H|].
  erewrite <- uncompomize_default_val.
  apply by_value_default_val.
  exact H.
Qed.

Lemma lifted_by_value_data_at: forall sh t v p,
  type_is_by_value t = true ->
  `(data_at sh t) (`(valinject t) v) p =
  local (`(field_compatible t nil) p) && `(mapsto sh t) p v.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply by_value_data_at; [|apply valinject_JMeq]; assumption.
Qed.

Lemma lifted_uncompomize_by_value_data_at: forall sh e t v p,
  type_is_by_value (uncompomize e t) = true ->
  `(data_at sh t) (`(valinject t) v) p =
  local (`(field_compatible (uncompomize e t) nil) p) &&
  `(mapsto sh (uncompomize e t)) p v.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply uncompomize_by_value_data_at;
  [|erewrite <- uncompomize_valinject; apply valinject_JMeq]; eassumption.
Qed.

Lemma lifted_by_value_data_at_: forall sh t p,
  type_is_by_value t = true ->
  `(data_at_ sh t) p = local (`(field_compatible t nil) p) && `(mapsto_ sh t) p.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply by_value_data_at_; assumption.
Qed.

Lemma lifted_uncompomize_by_value_data_at_: forall sh e t p,
  type_is_by_value (uncompomize e t) = true ->
  `(data_at_ sh t) p =
  local (`(field_compatible (uncompomize e t) nil) p) &&
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

Lemma array_at'_at_offset': forall sh t lo hi P pos pos0 v p,
  lo < hi ->
  (legal_alignas_type t = true) ->
  (alignof t | pos) ->
  (alignof t | pos0) ->
  (forall v n, lo <= n < hi -> 
    P (pos + (pos0 + sizeof t * n)) v p = P (pos0 + sizeof t * n) v (offset_val (Int.repr pos) p)) ->
  (forall v pos, P pos v p = P pos v (offset_val Int.zero p)) ->
  array_at' sh t lo hi P (pos + pos0) v p = array_at' sh t lo hi P pos0 v (offset_val (Int.repr pos) p).
Proof.
  intros.
  unfold array_at'.
  unfold rangespec.
  assert (lo <= hi) by omega; clear H.
  f_equal; [| remember (nat_of_Z (hi - lo)) as n eqn:HH; revert v lo H5 H3 HH; induction n; intros].
  + rewrite isptr_offset_val.
    reflexivity.
  + reflexivity.
  + simpl.
    assert (nat_of_Z (hi - lo) >= 1)%nat by omega.
    destruct (zlt 0 (hi - lo)); [| rewrite nat_of_Z_neg in H; omega].
    f_equal.
    - rewrite <- Z.add_assoc.
      apply H3.
      omega.
    - erewrite rangespec'_ext.
      Focus 2. {
        intros. rewrite Znth_succ by omega.
        instantiate (1 := fun i => P (pos + pos0 + sizeof t * i)
          (Znth (i - Z.succ lo) (skipn 1 v) (default_val t))).
        reflexivity.
      } Unfocus.
      rewrite IHn; [
        | omega
        | intros; apply H3; omega
        | rewrite (juicy_mem_lemmas.nat_of_Z_lem1 _ _ HH);
          f_equal; omega].
      erewrite rangespec'_ext.
      Focus 2. {
        intros. rewrite <- Znth_succ by omega.
        instantiate (1 := fun i => P (pos0 + sizeof t * i) (Znth (i - lo) v (default_val t))).
        reflexivity.
      } Unfocus.
      reflexivity.
Qed.

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
    destruct (zlt 0 z).
    - simpl.
      rewrite legal_alignas_type_Tarray in * by auto.
      apply array_at'_at_offset'; auto.
      * eapply nested_pred_Tarray; eauto.
      * intros. rewrite <- data_at'_offset_zero; reflexivity.
    - simpl.
      unfold array_at', rangespec.
      rewrite nat_of_Z_neg by omega.
      rewrite isptr_offset_val.
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
  (nested_legal_fieldlist t = true) ->
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
  apply pred_ext;
  normalize.
Qed.

Lemma unsigned_add: forall i pos, 0 <= pos -> Int.unsigned (Int.add i (Int.repr pos)) = (Int.unsigned i + pos) mod Int.modulus.
Proof.
  intros.
  unfold Int.add.
  pose proof Int.modulus_pos.
  pose proof Int.unsigned_range i.
  pose proof Int.unsigned_range (Int.repr pos).
  rewrite !Int.unsigned_repr_eq in *.
  rewrite Z.add_mod by omega.
  rewrite Z.mod_mod by omega.
  rewrite <- Z.add_mod by omega.
  reflexivity.
Qed.

Lemma memory_block_data_at__aux1: forall i pos t,
  0 <= pos /\ pos + sizeof t <= Int.modulus - Int.unsigned i ->
  Int.unsigned (Int.add i (Int.repr pos)) + sizeof t <= Int.modulus.
Proof.
  intros.
  destruct H.
  rewrite (unsigned_add i pos H).
  cut ((Int.unsigned i + pos) mod Int.modulus <= Int.unsigned i + pos).
    { intros. omega. }
  pose proof Int.modulus_pos.
  pose proof Int.unsigned_range i.
  apply Z.mod_le; omega.
Qed.

Lemma memory_block_data_at__aux2: forall i pos t,
  0 <= pos /\ pos + sizeof t <= Int.modulus - Int.unsigned i ->
  (alignof t | Int.unsigned i) ->
  (alignof t | pos) ->
  (alignof t | Int.unsigned (Int.add i (Int.repr pos))).
Proof.
  intros.
  destruct H.
  rewrite (unsigned_add i pos H).
  destruct (zlt (Int.unsigned i + pos) Int.modulus).
  + pose proof Int.unsigned_range i.
    rewrite Z.mod_small by omega.
    apply Z.divide_add_r; assumption.
  + pose proof sizeof_pos t.
    assert (Int.unsigned i + pos = Int.modulus) by omega.
    rewrite H4.
    rewrite Z_mod_same_full.
    apply Z.divide_0_r.
Qed.

Lemma memory_block_array_at'_nil: forall sh t b i lo hi pos P,
  lo < hi ->
  0 <= pos + sizeof t * lo /\ pos + sizeof t * hi <= Int.modulus - Int.unsigned i ->
  legal_alignas_type t = true ->
  (alignof t | pos) ->
  (alignof t | Int.unsigned i) ->
  sizeof t * (hi -lo) < Int.modulus ->
  nested_non_volatile_type t = true ->
  (forall n : Z,
       lo <= n < hi ->
       P (pos + sizeof t * n) (default_val t) (Vptr b i) =
       memory_block sh (Int.repr (sizeof t))
         (offset_val (Int.repr (pos + sizeof t * n)) (Vptr b i))) ->
  array_at' sh t lo hi P pos nil (Vptr b i) =
  memory_block sh (Int.repr (sizeof t * (hi - lo)))
    (offset_val (Int.repr (sizeof t * lo)) (offset_val (Int.repr pos) (Vptr b i))).
Proof.
  intros.
  unfold array_at'.
  unfold rangespec.
  assert (lo <= hi) by omega; clear H.
  rewrite memory_block_isptr.
  rewrite !isptr_offset_val.
  f_equal.
  remember (nat_of_Z (hi - lo)) as n eqn:HH; revert lo H0 H4 H6 H7 HH; induction n; intros.
  + simpl.
    destruct (zlt hi (Z.succ lo)).
    - assert (hi - lo = 0) by omega.
      rewrite H, Z.mul_0_r, memory_block_zero_Vptr.
      reflexivity.
    - replace (hi - lo) with ((hi - Z.succ lo) + 1) in HH by omega.
      rewrite nat_of_Z_plus in HH by omega.
      change (nat_of_Z 1) with (1 % nat) in HH.
      rewrite plus_comm in HH.
      simpl in HH.
      inversion HH.
  + simpl.
    assert (nat_of_Z (hi - lo) >= 1)%nat by omega.
    destruct (zlt 0 (hi - lo)); [| rewrite nat_of_Z_neg in H; omega].
    replace (sizeof t * (hi - lo))%Z with (sizeof t + sizeof t * (hi - Z.succ lo)).
    Focus 2. {
      rewrite Zred_factor2.
      f_equal.
      omega.
    } Unfocus.
    rewrite int_add_assoc1.
    unfold Int.add.
    pose proof sizeof_pos t.
    assert (sizeof t * Z.succ lo = sizeof t * lo + sizeof t)%Z.
    {
      rewrite Zred_factor3.
      f_equal; omega.
    }
    rewrite memory_block_split.
    f_equal.
    - rewrite Z.sub_diag.
      unfold Znth.
      if_tac; [omega |].
      change (Z.to_nat 0) with 0%nat.
      simpl nth.
      rewrite H6 by omega.
      reflexivity.
    - erewrite rangespec'_ext.
      Focus 2. {
        intros.
        rewrite Znth_succ by omega.
        instantiate (1 := fun i0 => P (pos + sizeof t * i0)
          (Znth (i0 - Z.succ lo) (skipn 1 nil) (default_val t))).
        reflexivity.
      } Unfocus.
      rewrite IHn.
      {
        destruct (zle (hi - Z.succ lo) 0); [| destruct (zle (sizeof t) 0)].
        + assert (hi - Z.succ lo = 0) by omega.
          unfold offset_val.
          rewrite H10, Z.mul_0_r, !memory_block_zero_Vptr.
          reflexivity.
        + assert (sizeof t = 0) by (pose proof sizeof_pos t; omega).
          unfold offset_val.
          rewrite H10, Z.mul_0_l, !memory_block_zero_Vptr.
          reflexivity.
        + f_equal.
          rewrite offset_offset_val.
          unfold offset_val.
          rewrite <- Int.add_assoc, int_add_assoc1.
          unfold Int.add; f_equal; f_equal.
          assert (0 <= pos + sizeof t * Z.succ lo <= Int.max_unsigned).
          {
            split.
            + rewrite H9; omega.
            + replace (Z.succ lo) with (hi - (hi - Z.succ lo)) by omega.
              rewrite Z.mul_sub_distr_l.
              assert (sizeof t * (hi - Z.succ lo) > 0) by (apply Zmult_gt_0_compat; assumption).
              unfold Int.max_unsigned.
              pose proof Int.unsigned_range i.
              omega.
          }
          rewrite !Int.unsigned_repr; omega.
        }
        * omega.
        * rewrite Z.mul_sub_distr_l, H9.
          rewrite Z.mul_sub_distr_l in H4.
          omega.
        * intros; apply H6; auto; omega.
        * omega.
        * rewrite (juicy_mem_lemmas.nat_of_Z_lem1 _ _ HH).
          f_equal; omega.
      - omega.
      - apply Z.mul_nonneg_nonneg; omega.
      - rewrite Zred_factor2.
        replace (1 + (hi - Z.succ lo)) with (hi - lo) by omega.
        exact H4.
      - split.
        * pose proof Int.unsigned_range i.
          pose proof Int.unsigned_range (Int.repr (pos + sizeof t * lo)).
          omega.
        * assert (Int.unsigned (Int.repr (pos + sizeof t * lo)) <= pos + sizeof t * lo).
            rewrite Int.unsigned_repr_eq.
            pose Int.modulus_pos.
            apply Z.mod_le; omega.
          rewrite Z.mul_sub_distr_l.
          omega.
Qed.

Lemma memory_block_data_at'_default_val: forall sh t b i pos,
  legal_alignas_type t = true ->
  0 <= pos /\ pos + sizeof t <= Int.modulus - Int.unsigned i ->
  nested_non_volatile_type t = true ->
  sizeof t < Int.modulus ->
  Int.unsigned i + sizeof t <= Int.modulus ->
  (alignof t | pos) ->
  (alignof t | Int.unsigned i) ->
  data_at' sh empty_ti t pos (default_val t) (Vptr b i) =
    memory_block sh (Int.repr (sizeof t)) (offset_val (Int.repr pos) (Vptr b i)).
Proof.
  intros.
  apply (data_at'_mut sh empty_ti (Int.modulus - Int.unsigned i)
    (fun t data_at'_pred pos =>
    sizeof t < Int.modulus ->
    (alignof t | Int.unsigned i) ->
    nested_non_volatile_type t = true ->
    data_at'_pred pos (default_val t) (Vptr b i) =
    memory_block sh (Int.repr (sizeof t)) (offset_val (Int.repr pos) (Vptr b i)))
    (fun f sfieldlist_at'_pred alignment pos =>
    tl_ofs pos alignment f - pos < Int.modulus ->
    (alignof_fields f | Int.unsigned i) ->
    nested_fields_pred uncompomize_non_volatile f = true ->
    sfieldlist_at'_pred alignment pos (struct_default_val f) (Vptr b i) =
    memory_block sh (Int.repr (tl_ofs pos alignment f - pos)) (offset_val (Int.repr pos) (Vptr b i)))
    (fun f ufieldlist_at'_pred size pos =>
    sizeof_union f < Int.modulus ->
    (alignof_fields f | Int.unsigned i) ->
    nested_fields_pred uncompomize_non_volatile f = true ->
    ufieldlist_at'_pred size pos (union_default_val f) (Vptr b i) =
    memory_block sh (Int.repr size) (offset_val (Int.repr pos) (Vptr b i))));
    intros;
    try (simpl data_at'; unfold at_offset2; 
         try (rewrite at_offset'_eq; [|rewrite <- memory_block_offset_zero; reflexivity]);
         try (rewrite at_offset'_eq; [|rewrite <- mapsto_offset_zero; reflexivity]);
         try (match goal with
              | |- mapsto _ ?T _ _ = _ => 
                pose proof sizeof_pos T;
                rewrite memory_block_mapsto_ with (t := T); [
                  | simpl; auto
                  | apply (nested_non_volatile_type_fact T); auto
                  | assumption 
                  | apply Int.unsigned_repr; unfold Int.max_unsigned; omega
                  | apply memory_block_data_at__aux1; assumption
                  | apply memory_block_data_at__aux2; assumption]
              end);
         try reflexivity).
  + (* Tarray *)
    destruct (zlt 0 z).
    - assert (sizeof (Tarray t0 z a) = sizeof t0 * z)%Z.
      {
        simpl; f_equal.
        apply Z.max_r_iff.
        omega.
      }
      assert (nested_non_volatile_type t0 = true)
        by (eapply nested_pred_Tarray; eauto; omega).
      rewrite legal_alignas_type_Tarray in * by auto.
      rewrite memory_block_array_at'_nil; auto.
      * rewrite Z.sub_0_r, Z.mul_0_r.
        rewrite <- memory_block_offset_zero.
        f_equal; f_equal.
        apply eq_sym, H13.
      * rewrite Z.mul_0_r. omega.
      * eapply nested_pred_Tarray; eauto.
      * rewrite Z.sub_0_r. omega.
      * intros.
        apply H9; auto.
        rewrite H13 in H10.
        replace z with ((z - 1) + 1) in H10 by omega.
        rewrite Z.mul_add_distr_l in H10.
        pose proof sizeof_pos t0.
        assert (0 <= sizeof t0 * (z - 1))
          by (apply Z.mul_nonneg_nonneg; omega).
        omega.
    - unfold array_at', rangespec.
      rewrite nat_of_Z_neg by omega.
      simpl.
      rewrite Z.max_l, Z.mul_0_r by omega.
      rewrite memory_block_zero.
      reflexivity.
  + (* Tstruct *)
    rewrite H9, <- sizeof_Tstruct_tl_ofs; auto.
    - f_equal; f_equal. omega.
    - assert (sizeof_struct f pos <= align (sizeof_struct f pos) (alignof (Tstruct i0 f a))).
        apply align_le.
        apply alignof_pos.
      rewrite <- sizeof_Tstruct_tl_ofs by auto.
      omega.
    - eapply Z.divide_trans; [apply legal_alignas_type_Tstruct, H6 | exact H11].
  + (* Tunion *)
    simpl in H9; rewrite H9; auto.
    - assert (sizeof_union f <= align (sizeof_union f) (alignof (Tunion i0 f a))).
        apply align_le.
        apply alignof_pos.
      simpl in H10; omega.
    - eapply Z.divide_trans; [apply legal_alignas_type_Tunion, H6 | exact H11].
  + rewrite memory_block_mapsto_ with (t := (Tpointer (look_up_ident_default i0 empty_ti) a)).
    - simpl; auto.
    - simpl; auto.
    - apply (nested_non_volatile_type_fact (Tcomp_ptr i0 a)); auto.
    - unfold legal_alignas_type in *.
      exact H6.
    - apply Int.unsigned_repr; unfold Int.max_unsigned; simpl; omega.
    - apply memory_block_data_at__aux1; assumption.
    - apply memory_block_data_at__aux2; assumption.
  + simpl.
    rewrite divide_align by auto.
    rewrite Z.sub_diag, memory_block_zero.
    reflexivity.
  + simpl.
    assert (pos0 + sizeof t0 <= align (pos0 + sizeof t0) alignment)
      by (apply align_le; omega).
    pose proof sizeof_pos t0.
    rewrite <- withspacer_memory_block
      with (be := sizeof t0) (ed := align (pos0 + sizeof t0) alignment - pos0);
      [| omega | assumption | ].
    Focus 2. {
      unfold offset_in_range, Int.add.
      simpl tl_ofs in H10, H12.
      split.
      + pose proof Int.unsigned_range (Int.repr (Int.unsigned i + Int.unsigned (Int.repr pos0))).
        omega.
      + rewrite !Int.unsigned_repr_eq.
        assert (pos0 mod Int.modulus <= pos0) by (apply Z.mod_le; omega).
        assert (0 <= pos0 mod Int.modulus < Int.modulus) by (apply Z.mod_pos_bound; omega).
        pose proof Int.unsigned_range i.
        assert ((Int.unsigned i + pos0 mod Int.modulus) mod Int.modulus <= 
          Int.unsigned i + pos0 mod Int.modulus)
          by (apply Z.mod_le; omega).
        omega.
    } Unfocus.
Opaque spacer.
    rewrite !withspacer_spacer; simpl.
Transparent spacer.
    rewrite H11. f_equal.
    - admit. (* spacer shifting *)
    - simpl in H12; omega.
    - simpl in H13.
      rewrite Z.max_l in H13 by (pose proof alignof_pos t0; omega).
      exact H13.
    - simpl in H14.
      rewrite andb_comm in H14; simpl in H14.
      exact H14.
  + simpl; rewrite H11; simpl.
    rewrite H13.
    admit.
    admit.
    admit.
    admit.
  + admit.
  + admit.
  + admit.
  + assumption.
  + assumption.
  + assumption.
  + assumption.
  + assumption.
  + assumption.
Qed.

Lemma data_at__memory_block: forall (sh : share) (t : type) (p: val),
  nested_non_volatile_type t = true ->
  sizeof t < Int.modulus ->
  data_at_ sh t p =
  !! (legal_alignas_type t = true) &&
  !! (nested_legal_fieldlist t = true) &&
  !! (align_compatible t p) && memory_block sh (Int.repr (sizeof t)) p.
Proof.
  intros.
  simpl.
  destruct p;
    try (rewrite memory_block_isptr;
     rewrite data_at__isptr;
     apply pred_ext; normalize; reflexivity).
  unfold data_at_, data_at.
  simpl.
  rewrite memory_block_size_compatible by auto.
  unfold size_compatible.
  cut (legal_alignas_type t = true ->
       Int.unsigned i + sizeof t <= Int.modulus ->
      (alignof t | Int.unsigned i) -> 
       data_at' sh empty_ti t 0 (default_val t) (Vptr b i) =
       memory_block sh (Int.repr (sizeof t)) (Vptr b i)).
  Focus 1. {
    intros; apply pred_ext; normalize.
    + rewrite H1 by auto.
      cancel.
    + rewrite H1 by auto.
      cancel.
  } Unfocus.
  intros.
  rewrite memory_block_offset_zero.
  apply memory_block_data_at'_default_val; auto.
  + omega.
  + apply Z.divide_0_r.
Qed.

Lemma memory_block_data_at_:
  forall (sh : share) (t : type) (p : val),
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  align_compatible t p ->
  sizeof t < Int.modulus ->
  memory_block sh (Int.repr (sizeof t)) p = data_at_ sh t p.
Proof.
  intros.
  rewrite data_at__memory_block by eauto.
  normalize.
Qed.

Lemma align_1_memory_block_data_at_: forall (sh : share) (t : type),
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  alignof t = 1%Z ->
  (sizeof t < Int.modulus)%Z ->
  memory_block sh (Int.repr (sizeof t)) = data_at_ sh t.
Proof.
  intros.
  extensionality p.
  rewrite data_at__memory_block by auto.
  rewrite andp_comm.
  apply add_andp.
  normalize.
  apply prop_right.
  unfold align_compatible.
  rewrite H2.
  destruct p; auto.
  split; [| auto].
  apply Z.divide_1_l.
Qed.

Lemma data_at_non_volatile: forall sh t v p, 
  data_at sh t v p |-- !! (nested_non_volatile_type t = true).
Proof.
  admit.
Qed.

Lemma array_at'_array_at'_: forall sh t lo hi P v pos p,
  lo < hi ->
  (legal_alignas_type t = true) ->
  (alignof t | pos) ->
  (forall n : Z,
       lo <= n < hi ->
       forall v p,
       P (pos + sizeof t * n) v p
       |-- P (pos + sizeof t * n) (default_val t) p) ->
  array_at' sh t lo hi P pos v p |-- array_at' sh t lo hi P pos nil p.
Proof.
  intros.
  unfold array_at'.
  unfold rangespec.
  assert (lo <= hi) by omega; clear H.
  apply andp_derives; [apply derives_refl |].
  remember (nat_of_Z (hi - lo)) as n eqn:HH; revert lo v H3 H2 HH; induction n; intros.
  + simpl.
    apply derives_refl.
  + simpl.
    assert (nat_of_Z (hi - lo) >= 1)%nat by omega.
    destruct (zlt 0 (hi - lo)); [| rewrite nat_of_Z_neg in H; omega].
    apply sepcon_derives.
    - unfold Znth. if_tac; [omega | rewrite Z.sub_diag].
      simpl.
      apply H2.
      omega.
    - erewrite rangespec'_ext.
      Focus 2. {
        intros.
        rewrite Znth_succ by omega.
        instantiate (1 := fun i => P (pos + sizeof t * i) (Znth (i - Z.succ lo)
                     (skipn 1 v) (default_val t))).
        reflexivity.
      } Unfocus.
      eapply derives_trans.
      Focus 1. {
        apply IHn; [omega | |].
        + intros. apply H2. omega.
        + rewrite (juicy_mem_lemmas.nat_of_Z_lem1 _ _ HH).
          f_equal; omega.
      } Unfocus.
      erewrite rangespec'_ext.
      Focus 2. {
        intros.
        change (@nil (reptype t)) with (skipn 1 (@nil (reptype t))).
        rewrite <- Znth_succ by omega.
        instantiate (1 := fun i => P (pos + sizeof t * i) (Znth (i - lo) nil (default_val t))).
        reflexivity.
      } Unfocus.
      apply derives_refl.
Qed.

Lemma data_at'_data_at'_ : forall sh e t v pos b i, 
  legal_alignas_type t = true ->
  0 <= pos /\ Int.unsigned i + pos + sizeof t <= Int.modulus ->
  (alignof t | pos) ->
  (alignof t | Int.unsigned i) ->
  data_at' sh e t pos v (Vptr b i) |-- data_at' sh e t pos (default_val t) (Vptr b i).
Proof.
  intros.
  assert (0 <= pos /\ pos + sizeof t <= Int.modulus - Int.unsigned i) by omega; clear H0.

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
  + destruct (zlt 0 z). (* Tarray case *)
    - apply array_at'_array_at'_.
      * omega.
      * eapply nested_pred_Tarray; eauto.
      * rewrite legal_alignas_type_Tarray in * by auto.
        exact H4.
      * intros.
        apply H6, H7.
    - simpl.
      unfold array_at', rangespec.
      rewrite nat_of_Z_neg by omega.
      apply derives_refl.
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
  + exact H1.
  + omega.
  + apply Z.divide_0_r.
  + exact H0.
Qed.

Hint Resolve data_at_data_at_: cancel.

Lemma data_at_Tarray_ext_derives: forall sh t n a v v',
  (forall i, 0 <= i < n ->
     data_at sh t (Znth i v (default_val _)) |-- data_at sh t (Znth i v' (default_val _))) ->
  data_at sh (Tarray t n a) v |-- data_at sh (Tarray t n a) v'.
Proof.
  intros.
  unfold data_at.
  simpl; intro p.
  unfold array_at'.
  normalize.
  apply rangespec_ext_derives.
  intros.
  rewrite !Z.add_0_l.
  rewrite !Z.sub_0_r.
  assert (legal_alignas_type t = true).
  Focus 1. {
    unfold legal_alignas_type in H2.
    simpl in H2.
    rewrite andb_true_iff in H2.
    tauto.
  } Unfocus.
  assert (alignof t | sizeof t * i).
  Focus 1. {
    apply Z.divide_mul_l.
    apply legal_alignas_sizeof_alignof_compat, H5.
  } Unfocus.
  rewrite !data_at'_at_offset' with (pos := (sizeof t * i)%Z) by auto.
  rewrite !at_offset'_eq by (rewrite <- data_at'_offset_zero; reflexivity).
  assert (legal_nested_field (Tarray t n a) (ArraySubsc i :: nil)) by solve_legal_nested_field.
  pose proof size_compatible_nested_field _ (ArraySubsc i :: nil) _ H7 H0.
  unfold nested_field_type2, nested_field_offset2 in H8; simpl in H8.
  pose proof align_compatible_nested_field _ (ArraySubsc i :: nil) _ H7 H2 H1.
  unfold nested_field_type2, nested_field_offset2 in H9; simpl in H9.
  simpl in H8, H9.
  specialize (H i H4 (offset_val (Int.repr (sizeof t * i)) p)).
  unfold data_at in H.
  simpl in H.
  normalize in H.
Qed.

Lemma data_at_Tarray_ext: forall sh t n a v v',
  (forall i, 0 <= i < n ->
    data_at sh t (Znth i v (default_val _)) =
      data_at sh t (Znth i v' (default_val _))) ->
  data_at sh (Tarray t n a) v = data_at sh (Tarray t n a) v'.
Proof.
  intros.
  apply pred_ext; apply data_at_Tarray_ext_derives; auto;
  intros; rewrite H by auto; auto.
Qed.

Lemma data_at_tint: forall sh v2 v1,
  data_at sh tint v2 v1 = mapsto sh tint v1 v2.
Proof.
  intros.
  unfold data_at, data_at'.
  simpl.
  apply pred_ext; normalize.
  apply andp_right; [|normalize].
  rewrite mapsto_isptr.
  unfold mapsto. simpl.
  unfold address_mapsto, res_predicates.address_mapsto, size_compatible, align_compatible.
  assert (legal_alignas_type tint = true) by reflexivity.
  assert (nested_legal_fieldlist tint = true) by reflexivity.
  destruct v1; normalize.
  eapply derives_trans with (!!(Int.unsigned i + sizeof tint <= Int.modulus /\
          (alignof tint | Int.unsigned i))); [| normalize].
  change (@predicates_hered.exp compcert_rmaps.RML.R.rmap
      compcert_rmaps.R.ag_rmap) with (@exp mpred Nveric).
  change (@predicates_hered.andp compcert_rmaps.RML.R.rmap
      compcert_rmaps.R.ag_rmap) with (@andp mpred Nveric).
  change (@predicates_hered.prop compcert_rmaps.RML.R.rmap
      compcert_rmaps.R.ag_rmap) with (@prop mpred Nveric).
  change (sizeof tint) with 4.
  change (alignof tint) with 4.
  change (Memdata.align_chunk Mint32) with 4.
  assert ((4 | Int.unsigned i) -> Int.unsigned i + 4 <= Int.modulus).
  Focus 1. {
    intros.
    destruct H2.
    pose proof Int.unsigned_range i.
    rewrite H2 in *.
    change Int.modulus with (1073741824 * 4)%Z in *.
    destruct H3 as [_ ?].
    rewrite Zmult_succ_l_reverse.
    apply Zmult_le_compat_r; [| omega].
    destruct (zle (Z.succ x) 1073741824); auto.
    assert (1073741824 <= x) by omega.
    apply Zmult_le_compat_r with (p := 4) in H4; [| omega].
    omega.
  } Unfocus.
  eapply orp_left; normalize; apply prop_right.
Qed.

Lemma var_block_data_at_:
  forall  sh id t, 
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  Z.ltb (sizeof t) Int.modulus = true ->
  var_block sh (id, t) = 
   !!(sizeof t <= Int.max_unsigned) &&
            `(data_at_ sh t) (eval_lvar id t).
Proof.
  intros; extensionality rho.
 unfold var_block.
  unfold_lift.
  simpl.
  apply Zlt_is_lt_bool in H2.
  rewrite data_at__memory_block by auto.
  rewrite memory_block_isptr.
  unfold local, lift1; unfold_lift.
  unfold align_compatible.
  destruct (eval_lvar id t rho); simpl in *; normalize.
  apply pred_ext; normalize.
Qed.

(*
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

