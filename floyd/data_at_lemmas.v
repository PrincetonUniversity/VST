Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.aggregate_pred.
Require Import floyd.reptype_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import floyd.fieldlist.
Require Import Coq.Logic.JMeq.
(* Import floyd.fieldlist.fieldlist. *)

Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

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
    at_offset (memory_block sh (Int.repr (ed - be))) be.
(* Arguments spacer sh be ed / _ . *)

Definition withspacer sh (be: Z) (ed: Z) : (val -> mpred) -> val -> mpred :=
   if Z.eq_dec (ed - be) 0
   then fun P => P
   else fun P => P * spacer sh be ed.

Lemma withspacer_spacer: forall sh be ed P,
   withspacer sh be ed P = spacer sh be ed * P.
Proof.
  intros.
  extensionality v.
  unfold withspacer, spacer.
  if_tac.
  + normalize.
  + simpl; apply sepcon_comm.
Qed.

Lemma spacer_offset_zero:
  forall sh be ed v, spacer sh be ed v = spacer sh be ed (offset_val Int.zero v).
Proof.
  intros;
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);  auto.
  repeat rewrite at_offset_eq;
  try rewrite offset_offset_val; try  rewrite Int.add_zero_l; auto.
Qed.

Lemma withspacer_add:
  forall sh pos be ed P p,
  withspacer sh (pos + be) (pos + ed) (fun p0 => P (offset_val (Int.repr pos) p)) p = 
  withspacer sh be ed P (offset_val (Int.repr pos) p).
Proof.
  intros.
  rewrite !withspacer_spacer.
  unfold spacer.
  simpl.
  replace (pos + ed - (pos + be)) with (ed - be) by omega.
  if_tac; [reflexivity|].
  rewrite !at_offset_eq.
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

Lemma at_offset_preserve_local_facts: forall {A: Type} P pos, (forall p, P p |-- !!(isptr p)) -> (forall p, at_offset P pos p |-- !!(isptr p)).
Proof.
  intros.
  rewrite at_offset_eq.
  specialize (H (offset_val (Int.repr pos) p)).
  eapply derives_trans; [exact H |]. 
  apply offset_val_preserve_isptr.
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
  rewrite at_offset_eq.
  destruct be; auto.
Qed.

Lemma withspacer_memory_block: forall sh be ed p,
  0 <= be <= ed ->
  ed < Int.modulus ->
  offset_in_range ed p ->
  withspacer sh be ed (memory_block sh (Int.repr be)) p = memory_block sh (Int.repr ed) p.
Proof.
  intros.
  rewrite withspacer_spacer; unfold spacer; simpl.
  if_tac.
  + assert (ed = be) by omega; subst.
    apply emp_sepcon.
  + rewrite at_offset_eq.
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

Section CENV.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Section WITH_SHARE.

Variable sh: share.

Definition struct_data_at'_aux (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (snd it) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (snd it)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset2 cenv_cs i0 m0 + sizeof cenv_cs t0)
            (field_offset_next cenv_cs i0 m0 sz)
            (at_offset (a v) (field_offset2 cenv_cs i0 m0))).
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset2 cenv_cs i1 m0 + sizeof cenv_cs t1)
            (field_offset_next cenv_cs i1 m0 sz)
            (at_offset (a (fst v)) (field_offset2 cenv_cs i1 m0)) * IHm i0 t0 (snd v) b).
Defined.

Definition union_data_at'_aux (m: members) (sz: Z) (P: ListType (map (fun it => reptype (snd it) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (snd it)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh (sizeof cenv_cs t0) sz (a v)).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (withspacer sh (sizeof cenv_cs t1) sz (a v)).
    - exact (IHm i0 t0 v b).
Defined.

Definition data_at': forall t, reptype t -> val -> mpred :=
  func_type (fun t => reptype t -> val -> mpred)
    (fun t v p =>
       if type_is_volatile t
       then memory_block sh (Int.repr (sizeof cenv_cs t)) p
       else mapsto sh t p (repinject t v))
    (fun t n a P v => array_pred t 0 n P (unfold_reptype v))
    (fun id a P v => struct_data_at'_aux (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_data_at'_aux (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v)).

Lemma struct_data_at'_aux_spec: forall m m0 sz v P,
  struct_data_at'_aux m m0 sz
   (ListTypeGen
     (fun it => reptype (snd it) -> val -> mpred)
     P m) v =
  struct_pred m 
   (fun it v =>
      withspacer sh
       (field_offset2 cenv_cs (fst it) m0 + sizeof cenv_cs (snd it))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset2 cenv_cs (fst it) m0))) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + change
     (struct_data_at'_aux ((i1, t1) :: (i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (snd it) -> val -> mpred)
        P ((i1, t1) :: (i0, t0) :: m)) v) with
     (withspacer sh
       (field_offset2 cenv_cs i1 m0 + sizeof cenv_cs t1)
         (field_offset_next cenv_cs i1 m0 sz)
           (at_offset (P (i1, t1) (fst v)) (field_offset2 cenv_cs i1 m0)) *
      struct_data_at'_aux ((i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (snd it) -> val -> mpred)
        P ((i0, t0) :: m)) (snd v)).
    rewrite IHm.
    reflexivity.
Qed.

Lemma union_data_at'_aux_spec: forall m sz v P,
  union_data_at'_aux m sz
   (ListTypeGen
     (fun it => reptype (snd it) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof cenv_cs (snd it))
       sz
       (P it v)) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - apply IHm.
Qed.

Notation REPTYPE t :=
  match t return Type with
  | Tvoid
  | Tfunction _ _ _ => unit
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tpointer _ _ => val
  | Tarray t0 _ _ => list (reptype t0)
  | Tstruct id _ => reptype_structlist (co_members (get_co id))
  | Tunion id _ => reptype_unionlist (co_members (get_co id))
  end.

Lemma data_at'_ind: forall t v,
  data_at' t v =
  match t return REPTYPE t -> val -> mpred with
  | Tvoid
  | Tfunction _ _ _ => fun _ _ => FF
  | Tint _ _ _
  | Tfloat _ _
  | Tlong _ _
  | Tpointer _ _ => fun v p => 
                      if type_is_volatile t
                      then memory_block sh (Int.repr (sizeof cenv_cs t)) p
                      else mapsto sh t p v
  | Tarray t0 n a => array_pred t0 0 n (data_at' t0)
  | Tstruct id a => struct_pred (co_members (get_co id))
                      (fun it v => withspacer sh
                        (field_offset2 cenv_cs (fst it) (co_members (get_co id)) + sizeof cenv_cs (snd it))
                        (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)))
                        (at_offset (data_at' (snd it) v) (field_offset2 cenv_cs (fst it) (co_members (get_co id)))))
  | Tunion id a => union_pred (co_members (get_co id))
                     (fun it v => withspacer sh
                      (sizeof cenv_cs (snd it))
                      (co_sizeof (get_co id))
                      (data_at' (snd it) v))
  end (unfold_reptype v).
Proof.
  intros.
  unfold data_at' at 1.
  rewrite func_type_ind.
  destruct t; auto;
  try solve [
  match goal with
  | |- appcontext [repinject ?tt] => 
    rewrite (repinject_unfold_reptype tt); auto
  end].
  + rewrite <- struct_data_at'_aux_spec; reflexivity.
  + rewrite <- union_data_at'_aux_spec; reflexivity.
Qed.

(*
Definition data_at (sh: Share.t) (t: type) :=
  (!! (legal_alignas_type t = true)) && (!! (nested_legal_fieldlist t = true)) &&
  (fun (_:reptype t) p => (!! (size_compatible t p /\ align_compatible t p))) 
  && data_at' sh empty_ti t 0.

Definition data_at_ (sh: Share.t) (t: type) := data_at sh t (default_val _).
*)

End WITH_SHARE.

Lemma data_at'_type_changable: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at' sh t1 v1 = data_at' sh t2 v2.
Proof.
  intros.
  subst t2.
  rewrite H0.
  reflexivity.
Qed.
(*
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
*)
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
(*
(* not true now *)
Lemma array_at'_local_facts: forall t lo hi P v p,
  array_at' t lo hi P v p |-- !! (isptr p).
Proof.
  intros.
  unfold array_at'.
  unfold at_offset.
  normalize.
Qed.
*)
(*
Lemma data_at'_local_facts:
  forall sh t v p, data_at' sh t v p |-- !!(isptr p).
Proof.
  intros.
  revert p.
  apply (type_mut (fun (t: type) => forall pos v p, (data_at' sh e t pos v p |-- !!(isptr p))) (fun _ => True) (fun flds => (forall alignment pos v p, sfieldlist_at' sh e flds alignment pos v p |-- !!(isptr p)) /\ (forall alignment pos v p, ufieldlist_at' sh e flds alignment pos v p |-- !!(isptr p)))); intros; auto; simpl; 
  try (unfold at_offset2; apply (@at_offset_preserve_local_facts val); intros; apply mapsto_local_facts);
  try (unfold at_offset2; apply (@at_offset_preserve_local_facts val); intros; apply memory_block_local_facts).
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
*)

(*
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
*)
(************************************************

Transformation between data_at/data_at_ and mapsto.

************************************************)

Lemma by_value_reptype: forall t, type_is_by_value t = true -> reptype t = val.
Proof.
  intros.
  destruct t; simpl in H; try inversion H; tauto.
Qed.

Lemma by_value_data_at': forall sh t v p,
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  data_at' sh t v p = mapsto sh t p (repinject t v).
Proof.
  intros.
  rewrite data_at'_ind; destruct t; try solve [inversion H]; rewrite H0;
  match goal with
  | |- appcontext [repinject ?tt] => 
    rewrite (repinject_unfold_reptype tt); auto
  end.
Qed.

Lemma by_value_data_at'_default_val: forall sh t p,
  type_is_by_value t = true ->
  legal_alignas_type t = true ->
  size_compatible t p ->
  align_compatible t p ->
  data_at' sh t (default_val t) p = memory_block sh (Int.repr (sizeof cenv_cs t)) p.
Proof.
  intros.
  rewrite data_at'_ind; destruct t; try solve [inversion H];
  match goal with
  | |- appcontext [type_is_volatile ?tt] => 
    destruct (type_is_volatile tt) eqn:HH; auto;
    rewrite <- (repinject_unfold_reptype tt); auto
  end;
  symmetry;
  cbv [repinject default_val reptype_gen func_type func_type_rec rank_type type_is_by_value];
  apply memory_block_mapsto_; auto.
  + destruct i; auto.
  + destruct f; auto.
Qed.

(*
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
*)
(************************************************

Transformation between data_at and data_at'. This is used in transformation
between field_at and data_at.

************************************************)

Lemma lower_sepcon_val':
  forall (P Q: val->mpred) v, 
  ((P*Q) v) = (P v * Q v).
Proof. reflexivity. Qed.

(*
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
  0 <= pos /\ pos + sizeof cenv_cs t <= Int.modulus - Int.unsigned i ->
  Int.unsigned (Int.add i (Int.repr pos)) + sizeof cenv_cs t <= Int.modulus.
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
  0 <= pos /\ pos + sizeof cenv_cs t <= Int.modulus - Int.unsigned i ->
  (alignof cenv_cs t | Int.unsigned i) ->
  (alignof cenv_cs t | pos) ->
  (alignof cenv_cs t | Int.unsigned (Int.add i (Int.repr pos))).
Proof.
  intros.
  destruct H.
  rewrite (unsigned_add i pos H).
  destruct (zlt (Int.unsigned i + pos) Int.modulus).
  + pose proof Int.unsigned_range i.
    rewrite Z.mod_small by omega.
    apply Z.divide_add_r; assumption.
  + pose proof sizeof_pos cenv_cs t.
    assert (Int.unsigned i + pos = Int.modulus) by omega.
    rewrite H4.
    rewrite Z_mod_same_full.
    apply Z.divide_0_r.
Qed.
*)
Lemma Znth_nil: forall {A} n (d: A), Znth n nil d = d.
Proof.
  intros.
  unfold Znth.
  if_tac; auto.
  simpl.
  destruct (Z.to_nat n); auto.
Qed.

Lemma offset_val_zero_Vptr: forall b i, offset_val (Int.repr 0) (Vptr b i) = Vptr b i.
Proof.
  intros.
  unfold offset_val, Int.add.
  change (Int.unsigned (Int.repr 0)) with 0.
  rewrite Z.add_0_r.
  rewrite Int.repr_unsigned.
  reflexivity.
Qed.

Ltac AUTO_IND :=
  match goal with
  | H: legal_alignas_type (Tarray ?t ?n ?a) = true |- legal_alignas_type ?t = true =>
    unfold legal_alignas_type in H;
    apply nested_pred_Tarray in H;
    exact H
  | H: complete_type ?env (Tarray ?t ?n ?a) = true |- complete_type ?env ?t = true =>
    simpl in H; auto
  end.

Lemma memory_block_data_at'_default_val_array_aux: forall sh t z a b ofs,
  0 <= ofs /\ ofs + sizeof cenv_cs (Tarray t z a) <= Int.modulus ->
  sizeof cenv_cs (Tarray t z a) < Int.modulus ->
  array_pred t 0 z
    (fun _ : reptype t => memory_block sh (Int.repr (sizeof cenv_cs t))) nil
    (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr (sizeof cenv_cs (Tarray t z a))) (Vptr b (Int.repr ofs)).
Proof.
  intros.
  destruct (zlt z 0).
  + unfold array_pred, rangespec.
    simpl.
    rewrite Z2Nat_neg by omega.
    rewrite Z.max_l by omega.
    rewrite Z.mul_0_r.
    rewrite memory_block_zero.
    simpl; normalize.
  + rewrite memory_block_array_pred.
    - rewrite Z.mul_0_r, Z.sub_0_r, Z.add_0_r.
      f_equal; f_equal.
      simpl.
      f_equal.
      rewrite Z.max_r by omega; auto.
    - rewrite Z.mul_0_r, Z.add_0_r.
      simpl in H.
      rewrite Z.max_r in H by omega; auto.
    - omega.
    - rewrite Z.sub_0_r.
      simpl in H0.
      rewrite Z.max_r in H0 by omega; auto.
Qed.

Lemma memory_block_data_at'_default_val: forall sh t b i,
  legal_alignas_type t = true ->
  complete_type cenv_cs t = true ->
  Int.unsigned i + sizeof cenv_cs t <= Int.modulus ->
  sizeof cenv_cs t < Int.modulus -> (* check why need this *)
  (alignof cenv_cs t | Int.unsigned i) ->
  data_at' sh t (default_val t) (Vptr b i) =
    memory_block sh (Int.repr (sizeof cenv_cs t)) (Vptr b i).
Proof.
  intros sh t.
  type_induction t;intros;
  try solve [inversion H0];
  try solve [apply by_value_data_at'_default_val; auto];
  rewrite data_at'_ind.
  + rewrite default_val_ind.
    rewrite unfold_fold_reptype.
    inv_int i.
    rewrite array_pred_ext with (P1 := fun _ => memory_block sh (Int.repr (sizeof cenv_cs t))) (v1 := nil).
    Focus 2. {
      intros.
      rewrite Znth_nil.
      rewrite !at_offset_eq.
      unfold offset_val.
      simpl sizeof in H1, H2;
      rewrite Z.max_r in H1, H2 by omega.
      apply IH; try AUTO_IND;
      pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil).
      + solve_mod_modulus.
        pose_mod_le (ofs + sizeof cenv_cs t * i).
        omega.
      + omega.
      + solve_mod_modulus.
        apply arith_aux04; [omega |].
        apply Z.divide_add_r.
        - rewrite legal_alignas_type_Tarray in H3 by auto.
          auto.
        - apply Z.divide_mul_l.
          apply legal_alignas_sizeof_alignof_compat.
          AUTO_IND.
    } Unfocus.
    apply memory_block_data_at'_default_val_array_aux; [omega | auto].
  + rewrite struct_pred_ext with
     (P1 := fun it _ => memory_block sh (Int.repr (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)) - field_offset2 cenv_cs (fst it) (co_members (get_co id)))))
     (v1 := unfold_reptype (default_val (Tstruct id a))).
SearchAbout fieldlist.members_no_replicate.
Print compspecs_legal.
Print composite_env_legal_fieldlist.
Print composite_legal_fieldlist.
SearchAbout members_no_replicate.
SearchAbout get_co.


Locate get_co_members_nil_sizeof_0.
Locate get_co.





Lemma memory_block_data_at'_default_val_struct_aux: forall sh b i (P: forall t, reptype t -> val -> mpred) F m m0 sz,
  m = m0 ->
  sizeof_struct cenv_cs 0 m0 <= sz ->
  Forall
   (fun it => forall b i,
      P (snd it) (F it) (Vptr b i) = memory_block sh (Int.repr (sizeof cenv_cs (snd it))) (Vptr b i)) m ->
  struct_pred m (fun it => reptype (snd it))
   (fun it v =>
      withspacer sh
       (field_offset cenv_cs (fst it) m0 + sizeof cenv_cs (snd it))
       (field_offset_next (fst it) m0 sz)
       (at_offset (P (snd it) v) (field_offset cenv_cs (fst it) m0)))
   (compact_prod_gen F m)
   (Vptr b i) = 
  memory_block sh (Int.repr sz) (Vptr b i).
Proof.
  intros.
  

SearchAbout (Int.unsigned (Int.repr _)).
Print at_offset.
Print at_offset.

Print Int.eqm.


 unfold Int.add.
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
         try (rewrite at_offset_eq; [|rewrite <- memory_block_offset_zero; reflexivity]);
         try (rewrite at_offset_eq; [|rewrite <- mapsto_offset_zero; reflexivity]);
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
  rewrite !data_at'_at_offset with (pos := (sizeof t * i)%Z) by auto.
  rewrite !at_offset_eq by (rewrite <- data_at'_offset_zero; reflexivity).
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

