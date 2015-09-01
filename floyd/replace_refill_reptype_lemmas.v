Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import type_induction.
Require floyd.aggregate_type. Import floyd.aggregate_type.aggregate_type.
Require Import floyd.reptype_lemmas.
Require Import floyd.proj_reptype_lemmas.
Require Import Coq.Classes.RelationClasses.
Require Import floyd.sublist.

Section MULTI_HOLES.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Inductive holes : Type :=
  | FullUpdate
  | SemiUpdate: (gfield -> holes) -> holes
  | Stable
  | Invalid.

Fixpoint nested_field_type3 t gfs :=
  match gfs with
  | nil => t
  | gf :: gfs0 => nested_field_type3 (gfield_type t gf) gfs0
  end.

(* reverse gfs order *)
Definition holes_subs t := forall gfs, reptype (nested_field_type3 t gfs).

Lemma nested_field_type2_ind': forall t gf gfs, nested_field_type2 t (gfs ++ gf :: nil) = nested_field_type2 (gfield_type t gf) gfs.
Proof.
  intros.
  rewrite <- nested_field_type2_nested_field_type2.
  rewrite nested_field_type2_ind with (gfs0 := gf :: nil).
  reflexivity.
Defined.

Lemma nested_field_type3_spec: forall t gfs, nested_field_type3 t gfs = nested_field_type2 t (rev gfs).
Proof.
  intros.
  revert t; induction gfs; intros.
  + auto.
  + simpl.
    rewrite nested_field_type2_ind'.
    rewrite IHgfs.
    auto.
Defined.

Lemma nested_field_type3_rev_spec: forall t gfs, nested_field_type3 t (rev gfs) = nested_field_type2 t gfs.
Proof.
  intros.
  rewrite <- (rev_involutive gfs) at 2.
  apply nested_field_type3_spec.
Defined.

Definition gfield_holes (h: holes) (gf: gfield): holes :=
  match h with
  | FullUpdate => Invalid
  | SemiUpdate subl => subl gf
  | Stable => Stable
  | Invalid => Invalid
  end.

Fixpoint nested_field_holes (h: holes) (gfs: list gfield) : holes :=
  match gfs with
  | nil => h
  | gf :: gfs0 => gfield_holes (nested_field_holes h gfs0) gf
  end.

Definition gfield_subs {t} (subs: holes_subs t) (gf: gfield): holes_subs (gfield_type t gf) :=
  fun gfs => subs (gf :: gfs).

Definition holes_subs_equiv {t} h (subs1 subs2: holes_subs t) : Prop :=
  forall gfs, legal_nested_field t gfs -> nested_field_holes h gfs = FullUpdate -> subs1 (rev gfs) = subs2 (rev gfs).

Definition reptype_with_holes (t: type) (h: holes): Type := reptype t.

Definition reptype_with_holes_equiv {t: type} {h: holes} (v0 v1: reptype_with_holes t h): Prop :=
  forall gfs, legal_nested_field t gfs -> nested_field_holes h gfs = Stable -> proj_reptype t gfs v0 = proj_reptype t gfs v1.

Definition proj_except_holes (t: type) (h: holes) (v: reptype t) : reptype_with_holes t h := v.

Definition ListType_map {X: Type} {F F0: X -> Type} {l: list X}
  (f: ListType (map (fun x => F x -> F0 x) l)): ListType (map F l) -> ListType (map F0 l).
Proof.
  intros.
  induction l; simpl in *.
  + exact Nil.
  + inversion f; inversion X0; subst.
    exact (Cons (a0 a1) (IHl b b0)).
Defined.

Lemma ListType_map_ListTypeGen: forall A (F G: A -> Type) (g: forall a, G a) (fg: forall a, G a -> F a) (l: list A),
  ListType_map
   (ListTypeGen (fun a => G a -> F a) (fun a => fg a) l)
   (ListTypeGen G (fun a => g a) l) =
  ListTypeGen F (fun a => fg a (g a)) l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    rewrite IHl.
    reflexivity.
Qed.

Definition legal_holes: forall (t: type) (h: holes), Prop :=
  func_type (fun _ => holes -> Prop)
    (fun t h =>
       match h with
       | FullUpdate | Stable => True
       | SemiUpdate _ | Invalid => False
       end)
    (fun t n a F h => 
       match h with
       | FullUpdate | Stable => True
       | SemiUpdate subl => forall i, 0 <= i < n -> F (subl (ArraySubsc i))
       | Invalid => False
       end)
    (fun id a F h =>
       match h with
       | FullUpdate | Stable => True
       | SemiUpdate subl =>
          fold_right and True 
           (decay (ListType_map F (ListTypeGen (fun _ => holes) (fun it => subl (StructField (fst it))) _)))
       | Invalid => False
       end)
    (fun id a F h =>
       match h with
       | FullUpdate | Stable => True
       | SemiUpdate subl =>
          exists i,
          fold_right and (in_members i (co_members (get_co id)))
           (decay (ListType_map 
             (ListTypeGen
               (fun _ => (holes -> Prop) -> Prop)
               (fun it F => if ident_eq i (fst it)
                            then F (subl (UnionField (fst it)))
                            else subl (UnionField (fst it)) = Invalid) _)
             F))
       | Invalid => False
       end).

Fixpoint get_union_field (subl: gfield -> holes) (m: members) (default: ident): ident :=
  match m with
  | nil => default
  | (i, t) :: m0 => match subl (UnionField i) with | Invalid => get_union_field subl m0 default | _ => i end
  end.

Definition get_union_member subl m :=
  let i := get_union_field subl m 1%positive in
  (i, field_type i m).

Definition reinitiate_compact_sum {A} {F: A -> Type} {l: list A} (v: compact_sum (map F l)) (a: A) (init: forall a, F a) (H: forall a0 a1: A, {a0 = a1} + {a0 <> a1}) :=
  compact_sum_gen
   (fun a0 => if H a a0 then true else false)
   (fun a0 => proj_compact_sum a0 l v (init a0) H)
  l.

Fixpoint map_Znth' {A:Type}  (F: Z -> A -> A) (i: Z) (al: list A) : list A :=
 match al with
 | nil => nil
 | a::al' => F i a :: map_Znth' F (Z.succ i) al'
 end.

Definition map_Znth {A: Type} F (al: list A) := map_Znth' F 0 al.


Definition replace_reptype: forall (t: type) (h: holes) (subs: holes_subs t) (v: reptype t), reptype t :=
  func_type (fun t => holes -> holes_subs t -> reptype t -> reptype t)
    (fun t h subs v =>
       match h with
       | FullUpdate => subs nil
       | _ => v
       end)
    (fun t n a F h subs v =>
       match h with
       | FullUpdate => subs nil
       | SemiUpdate subl =>
         @fold_reptype _ _ (Tarray t n a) 
          (map_Znth
                (fun i => F (subl (ArraySubsc i))
                         (fun gfs => subs (ArraySubsc i :: gfs)))
                (unfold_reptype v))
          (* (zl_gen 0 n
             (fun i => F (subl (ArraySubsc i))
                         (fun gfs => subs (ArraySubsc i :: gfs))
                         (zl_nth i (unfold_reptype v))))
*) 
       | StableOrInvalid => v
       end)
    (fun id a F h subs v =>
       match h with
       | FullUpdate => subs nil
       | SemiUpdate subl =>
         @fold_reptype _ _ (Tstruct id a)
           (compact_prod_map _
             (ListType_map
               (ListType_map F
                 (ListTypeGen (fun _ => holes) (fun it => subl (StructField (fst it))) _))
               (ListTypeGen (fun it => holes_subs (field_type (fst it) (co_members (get_co id))))
                            (fun it gfs => subs (StructField (fst it) :: gfs)) _))
             (unfold_reptype v))
       | StableOrInvalid => v
       end)
    (fun id a F h subs v =>
       match h with
       | FullUpdate => subs nil
       | SemiUpdate subl =>
         @fold_reptype _ _ (Tunion id a)
           (compact_sum_map _
             (ListType_map
               (ListType_map F
                 (ListTypeGen (fun _ => holes) (fun it => subl (UnionField (fst it))) _))
               (ListTypeGen (fun it => holes_subs (field_type (fst it) (co_members (get_co id))))
                            (fun it gfs => subs (UnionField (fst it) :: gfs)) _))
             (reinitiate_compact_sum
               (unfold_reptype v)
               (get_union_member subl (co_members (get_co id)))
               (fun _ => default_val _)
               member_dec
               ))
       | StableOrInvalid => v
       end).

Lemma replace_reptype_ind: forall t h,
  replace_reptype t h =
  match t as t' return holes_subs t' -> reptype t' -> reptype t' with
  | Tarray t0 n a =>
    fun subs v =>
       match h with
       | FullUpdate => subs nil
       | SemiUpdate subl =>
         @fold_reptype _ _ (Tarray t0 n a) 
           (map_Znth (fun i => replace_reptype t0 (subl (ArraySubsc i))
                         (fun gfs => subs (ArraySubsc i :: gfs)))
                (unfold_reptype v))
(*           (zl_gen 0 n
             (fun i => replace_reptype t0 (subl (ArraySubsc i))
                         (fun gfs => subs (ArraySubsc i :: gfs))
                         (zl_nth i (unfold_reptype v))))
*)
       | StableOrInvalid => v
       end
  | Tstruct id a =>
    fun subs v =>
       match h with
       | FullUpdate => subs nil
       | SemiUpdate subl =>
         @fold_reptype _ _ (Tstruct id a)
           (compact_prod_map _
             (ListTypeGen
               (fun it => reptype (field_type (fst it) (co_members (get_co id))) ->
                          reptype (field_type (fst it) (co_members (get_co id))))
               (fun it => replace_reptype
                            (field_type (fst it) (co_members (get_co id)))
                            (subl (StructField (fst it)))
                            (fun gfs => subs (StructField (fst it) :: gfs)))
               _)
             (unfold_reptype v))
       | StableOrInvalid => v
       end
  | Tunion id a => 
    fun subs v =>
       match h with
       | FullUpdate => subs nil
       | SemiUpdate subl =>
         @fold_reptype _ _ (Tunion id a)
           (compact_sum_map _
             (ListTypeGen
               (fun it => reptype (field_type (fst it) (co_members (get_co id))) ->
                          reptype (field_type (fst it) (co_members (get_co id))))
               (fun it => replace_reptype
                            (field_type (fst it) (co_members (get_co id)))
                            (subl (UnionField (fst it)))
                            (fun gfs => subs (UnionField (fst it) :: gfs)))
               _)
             (reinitiate_compact_sum
               (unfold_reptype v)
               (get_union_member subl (co_members (get_co id)))
               (fun _ => default_val _)
               member_dec
               ))
       | StableOrInvalid => v
       end
  | _ => fun subs v =>
       match h with
       | FullUpdate => subs nil
       | _ => v
       end
  end.
Proof.
  intros.
  unfold replace_reptype.
  rewrite func_type_ind.
  destruct t; try auto.
  + (* Tstruct case *)
    destruct h; try auto.
    extensionality subs v.
    rewrite !ListType_map_ListTypeGen.
    reflexivity.
  + destruct h; try auto.
    extensionality subs v.
    rewrite !ListType_map_ListTypeGen.
    reflexivity.
Qed.

Definition refill_reptype {t h} (v: reptype_with_holes t h) (subs: holes_subs t) := replace_reptype t h subs v. 

Lemma replace_stable: forall t h subs v gfs,
  legal_holes t h ->
  legal_nested_field t gfs ->
  nested_field_holes h gfs = Stable ->
  proj_reptype t gfs (replace_reptype t h subs v) = proj_reptype t gfs v.
Admitted.

Lemma replace_change: forall t h subs v gfs,
  legal_holes t h ->
  legal_nested_field t gfs ->
  nested_field_holes h gfs = FullUpdate ->
  proj_reptype t gfs (replace_reptype t h subs v) =
  eq_rect_r reptype (subs (rev gfs)) (eq_sym (nested_field_type3_rev_spec _ _)).
Admitted.

Lemma replace_proj_self: forall t h v gfs,
  legal_holes t h ->
  legal_nested_field t gfs ->
  type_is_by_value (nested_field_type2 t gfs) = true ->
  proj_reptype t gfs (replace_reptype t h (fun rgfs => eq_rect_r reptype (proj_reptype t (rev rgfs) v) (nested_field_type3_spec _ _)) v) = proj_reptype t gfs v \/
  proj_reptype t gfs (replace_reptype t h (fun rgfs => eq_rect_r reptype (proj_reptype t (rev rgfs) v) (nested_field_type3_spec _ _)) v) = default_val _.
Admitted.

Lemma refill_proj_except: forall t h (v: reptype t) (v0: holes_subs t),
  refill_reptype (proj_except_holes t h v) v0 = replace_reptype t h v0 v.
Proof. auto. Qed.

Instance Equiv_reptype_with_holes t h : Equivalence (@reptype_with_holes_equiv t h).
  unfold reptype_with_holes_equiv.
  split.
  + unfold Reflexive.
    intros.
    auto.
  + unfold Symmetric.
    intros.
    symmetry.
    auto.
  + unfold Transitive.
    intros.
    specialize (H gfs H1 H2).
    specialize (H0 gfs H1 H2).
    congruence.
Defined.

Instance Equiv_holes_subs t h: Equivalence (@holes_subs_equiv t h).
  unfold holes_subs_equiv.
  split.
  + unfold Reflexive.
    intros.
    auto.
  + unfold Symmetric.
    intros.
    symmetry.
    auto.
  + unfold Transitive.
    intros.
    specialize (H gfs H1 H2).
    specialize (H0 gfs H1 H2).
    congruence.
Defined.

Require Import Coq.Classes.Morphisms.

Instance Proper_refill_1 t h v0: Proper ((@reptype_with_holes_equiv t h) ==> (@eq (reptype t))) (fun v: reptype_with_holes t h => refill_reptype v v0).
Proof.
  admit.
Defined.

(* (* dont know which version is better. This one is more concise but its correctness is based on function extensionality *)
Instance Proper_refill_1 t h: Proper ((@reptype_with_holes_equiv t h) ==> (@eq (holes_subs t -> reptype t))) (@refill_reptype t h).
Proof.
  admit.
Defined.
*)

Instance Proper_refill_2 t h (v: reptype_with_holes t h) : Proper ((@holes_subs_equiv t h) ==> (@eq (reptype t))) (refill_reptype v).
Proof.
  admit.
Defined.

Instance Proper_replace t h v: Proper ((@holes_subs_equiv t h) ==> (@eq (reptype t))) (fun v0 => replace_reptype t h v0 v).
Proof.
  admit.
Defined.

End MULTI_HOLES.

Section SINGLE_HOLE.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Lemma gfield_dec: forall (gf0 gf1: gfield), {gf0 = gf1} + {gf0 <> gf1}.
Proof.
  intros.
  destruct gf0, gf1; try solve [right; congruence].
  + destruct (zeq i i0); [left | right]; congruence.
  + destruct (Pos.eq_dec i i0); [left | right]; congruence.
  + destruct (Pos.eq_dec i i0); [left | right]; congruence.
Defined.

Fixpoint singleton_hole_rec (rgfs: list gfield) : holes := 
  match rgfs with
  | nil => FullUpdate
  | gf :: rgfs0 => 
    match gf with
    | ArraySubsc _
    | StructField _ => SemiUpdate (fun gf0 => if gfield_dec gf gf0 then singleton_hole_rec rgfs0 else Stable)
    | UnionField _ => SemiUpdate (fun gf0 => if gfield_dec gf gf0 then singleton_hole_rec rgfs0 else Invalid)
    end
  end.

Definition singleton_hole (gfs: list gfield) : holes := singleton_hole_rec (rev gfs).

Lemma rgfs_dec: forall rgfs0 rgfs1: list gfield, {rgfs0 = rgfs1} + {rgfs0 <> rgfs1}.
Proof.
  apply list_eq_dec.
  apply gfield_dec.
Defined.

Definition singleton_subs t gfs (v: reptype (nested_field_type2 t gfs)): holes_subs t.
  rewrite <- nested_field_type3_rev_spec in v.
  intro rgfs.
  destruct (rgfs_dec rgfs (rev gfs)).
  + subst.
    exact v.
  + exact (default_val _).
Defined.

Lemma singleton_subs_self: forall t gfs v,
  JMeq (singleton_subs t gfs v (rev gfs)) v.
Proof.
  intros.
  unfold singleton_subs.
  destruct (rgfs_dec (rev gfs) (rev gfs)); [| congruence].
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    rewrite (eq_rect_r_JMeq A x y F v H)
  end.
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    rewrite (eq_rect_r_JMeq A x y F v H)
  end.
  auto.
Qed.
  
Definition proj_except_holes_1 t gfs v: reptype_with_holes t (singleton_hole gfs) :=
  proj_except_holes t (singleton_hole gfs) v.

Definition refill_reptype_1 t gfs (v: reptype_with_holes t (singleton_hole gfs)) (v0: reptype (nested_field_type2 t gfs)) :=
  refill_reptype v (singleton_subs t gfs v0).

Definition upd_reptype t gfs (v: reptype t) (v0: reptype (nested_field_type2 t gfs)) :=
  replace_reptype t (singleton_hole gfs) (singleton_subs t gfs v0) v.

Definition upd_gfield_reptype t gf (v: reptype t) (v0: reptype (gfield_type t gf)) : reptype t :=
  fold_reptype 
  (match t, gf return (REPTYPE t -> reptype (gfield_type t gf) -> REPTYPE t)
  with
  | Tarray t0 n a, ArraySubsc i =>
      fun v v0 => firstn (Z.to_nat i) v ++ (v0 :: skipn (Z.to_nat (i+1)) v)
(*zl_concat (zl_concat (zl_sublist 0 i v) (zl_singleton i v0)) (zl_sublist (i + 1) n v) *)
  | Tstruct id _, StructField i =>
      fun v v0 => compact_prod_upd _ v (i, field_type i (co_members (get_co id))) v0 member_dec
  | Tunion id _, UnionField i =>
      fun v v0 => compact_sum_upd _ v (i, field_type i (co_members (get_co id))) v0 member_dec
  | _, _ => fun v _ => v
  end (unfold_reptype v) v0).

Fixpoint upd_reptype_rec (t: type) (gfs: list gfield) (v: reptype t) (v0: reptype (nested_field_type2 t gfs)): reptype t :=
  match gfs as gfs'
    return reptype (match gfs' with
                    | nil => t
                    | gf :: gfs0 => gfield_type (nested_field_type2 t gfs0) gf
                    end) -> reptype t
  with
  | nil => fun v0 => v0
  | gf :: gfs0 => fun v0 => upd_reptype_rec t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0)
  end (eq_rect_r reptype v0 (eq_sym (nested_field_type2_ind t gfs))).

Lemma upd_reptype_ind: forall t gfs v v0, upd_reptype t gfs v v0 = upd_reptype_rec t gfs v v0.
Admitted.

Require Import floyd.stronger.

Lemma upd_reptype_rec_data_equal: forall t gfs v v0 v1, data_equal v0 v1 -> data_equal (upd_reptype_rec t gfs v v0) (upd_reptype_rec t gfs v v1).
Proof.
  intros.
  induction gfs as [| gf gfs].
  + exact H.
  + change (upd_reptype_rec t (gf :: gfs) v v0) with
      (upd_reptype_rec t gfs v (upd_gfield_reptype _ gf (proj_reptype t gfs v)
        (eq_rect_r reptype v0 (eq_sym (nested_field_type2_ind t (gf :: gfs)))))).
    change (upd_reptype_rec t (gf :: gfs) v v1) with
      (upd_reptype_rec t gfs v (upd_gfield_reptype _ gf (proj_reptype t gfs v)
        (eq_rect_r reptype v1 (eq_sym (nested_field_type2_ind t (gf :: gfs)))))).
    apply IHgfs.
    assert (data_equal (eq_rect_r reptype v0 (eq_sym (nested_field_type2_ind t (gf :: gfs))))
              (eq_rect_r reptype v1 (eq_sym (nested_field_type2_ind t (gf :: gfs)))))
      by (apply eq_rect_r_data_equal; auto).
    forget (eq_rect_r reptype v0 (eq_sym (nested_field_type2_ind t (gf :: gfs)))) as V0.
    forget (eq_rect_r reptype v1 (eq_sym (nested_field_type2_ind t (gf :: gfs)))) as V1.
    forget (proj_reptype t gfs v) as V.
    clear - H0.
    revert V0 V1 H0 V.
    destruct (nested_field_type2 t gfs), gf; unfold upd_gfield_reptype; intros; try reflexivity.
    - admit.
    - admit.
    - admit.
Qed.

End SINGLE_HOLE.

Module zlist_hint_db.

Lemma Znth_sub_0_r: forall A i l (d: A), Znth (i - 0) l d = Znth i l d.
  intros.
  rewrite Z.sub_0_r by omega.
  auto.
Qed.

Lemma Znth_map_Vint: forall (i : Z) (l : list int),
  0 <= i < Zlength l -> Znth i (map Vint l) Vundef = Vint (Znth i l Int.zero).
Proof.
  intros i l.
  apply Znth_map.
Qed.

End zlist_hint_db.

(*Hint Rewrite @zl_constr_correct using solve [omega] : zl_nth_db.
Hint Rewrite zlist_hint_db.Znth_sub_0_r : zl_nth_db.
Hint Rewrite zlist_hint_db.Znth_map_Vint using solve [omega] : zl_nth_db.
Hint Rewrite (fun A d => @zl_sublist_correct A d _ (list_zlist_correct _ _)) using solve [omega] : zl_nth_db.
Hint Rewrite (fun A d => @zl_concat_correct_l A d _ (list_zlist_correct _ _)) using solve [omega] : zl_nth_db.
Hint Rewrite (fun A d => @zl_concat_correct_r A d _ (list_zlist_correct _ _)) using solve [omega] : zl_nth_db.

Hint Rewrite (fun A d => @zl_sub_concat_l A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_concat_r A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_concat_mid A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_sub A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_self A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_empty A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_concat_empty_l A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_concat_empty_r A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
*)
Section POSE_TAC.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Definition eq_pose {A} x y := @eq A x y.

Definition abs_pose t (v: reptype t) : Prop := True.

Definition concr_pose t (v: reptype t) : Prop := True.

End POSE_TAC.

Ltac abs_or_concr t v :=
  let t' := eval compute in t in
  match t' with
  | Tarray _ _ _ =>
    match v with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: _ => assert (concr_pose t v) by exact I
    | _ => assert (abs_pose t v) by exact I
    end
  | Tstruct ?id _ =>
    let m := eval compute in (co_members (get_co id)) in
    match m with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: @nil _ => assert (concr_pose t v) by exact I
    | _ => match v with
           | (_, _) => assert (concr_pose t v) by exact I
           | _ => assert (abs_pose t v) by exact I
           end
    end
  | Tunion ?id _ =>
    let m := eval compute in (co_members (get_co id)) in
    match m with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: @nil _ => assert (concr_pose t v) by exact I
    | _ => match v with
           | (_, _) => assert (concr_pose t v) by exact I
           | _ => assert (abs_pose t v) by exact I
           end
    end
  end.

Transparent peq.

Ltac cbv_proj_struct H :=
    cbv beta zeta iota delta
    [proj_struct proj_compact_prod list_rect
    member_dec field_type fieldlist.field_type2 Ctypes.field_type
     ident_eq peq Pos.eq_dec BinNums.positive_rec positive_rect
    sumbool_rec sumbool_rect bool_dec bool_rec bool_rect option_rec option_rect
    eq_rect_r eq_rect eq_rec_r eq_rec eq_sym eq_trans f_equal
    type_eq type_rec type_rect typelist_eq typelist_rec typelist_rect
    intsize_rec intsize_rect signedness_rec signedness_rect floatsize_rec floatsize_rect attr_rec attr_rect
    tvoid tschar tuchar tshort tushort tint
    tuint tbool tlong tulong tfloat tdouble tptr tarray noattr
    ] in H; simpl in H.

Ltac pose_proj_reptype_1 CS CSL t gf v H :=
  assert (@proj_gfield_reptype CS CSL t gf v = @proj_gfield_reptype CS CSL t gf v) as H by reflexivity;
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let V := fresh "v" in
  let t' := eval compute in t in
  remember v as V eqn:H0 in H at 2;
  match type of V with
  | ?t_temp => change t_temp with (@reptype CS t) in V
  end;
  change (@proj_gfield_reptype CS CSL t gf V) with (@proj_gfield_reptype CS CSL t' gf V) in H;
  unfold proj_gfield_reptype in H at 2;
  pose proof unfold_reptype_JMeq t' V as H1;
  apply JMeq_eq in H1;
  rewrite H1 in H; clear H1;
  match type of H with
  | _ = proj_struct ?i ?m V ?d =>
    let v_res := fresh "v" in
    let H_eq := fresh "H" in
    remember (proj_struct i m V d) as v_res eqn:H_eq;
    let d' := eval vm_compute in d in change d with d' in H_eq;
    let m' := eval vm_compute in m in change m with m' in H_eq;
    cbv_proj_struct H_eq;
    subst v_res;
    subst V
(*  | _ = zl_nth ?i ?l =>
    subst V;
    autorewrite with zl_nth_db in H
*)
  | _ =>
    subst V
  end
.

Ltac pose_proj_reptype CS CSL t gfs v H :=
  match gfs with
  | nil =>
      assert (eq_pose (@proj_reptype CS CSL t gfs v) v) as H by reflexivity
  | ?gf :: ?gfs0 =>
     pose proof I as H;   (* *0* SEE LINE *1* *)
     let H0 := fresh "H" in
     pose_proj_reptype CS CSL t gfs0 v H0;
     match type of H0 with
     | eq_pose (proj_reptype t gfs0 v) ?v0 =>
         let H1 := fresh "H" in
         match gfs0 with
         | nil => pose_proj_reptype_1 CS CSL t gf v0 H1
         | _ => pose_proj_reptype_1 CS CSL (nested_field_type2 t gfs0) gf v0 H1
         end;
         clear H;         (* *1* SEE LINE *0* *)
         match gfs0 with
         | nil => assert (eq_pose (@proj_reptype CS CSL t gfs v) (@proj_gfield_reptype CS CSL t gf v0)) as H
         | _ => assert (eq_pose (@proj_reptype CS CSL t gfs v)
                   (@proj_gfield_reptype CS CSL (nested_field_type2 t gfs0) gf v0)) as H
         end;
         [unfold eq_pose in *; rewrite <- H0; unfold proj_reptype, eq_rect_r; apply eq_sym, eq_rect_eq |];
         rewrite H1 in H;
         clear H1
     end
  end.

Ltac pose_upd_reptype_1 CS CSL t gf v v0 H :=
  let t' := eval compute in t in
  assert (data_equal (@upd_gfield_reptype CS CSL t gf v v0) (@upd_gfield_reptype CS CSL t' gf v v0)) as H
    by reflexivity;
  unfold upd_gfield_reptype at 2 in H;
  let H0 := fresh "H" in
  pose proof unfold_reptype_JMeq t' v as H0;
  apply JMeq_eq in H0;
  rewrite H0 in H;
  clear H0;
  match t' with
  | Tarray _ _ _ => autorewrite with zl_sub_db in H
  | _ => idtac
  end;
  unfold compact_prod_upd, eq_rect_r in H; simpl in H;
  match type of H with
  | data_equal _ (fold_reptype ?v_res) =>
    pose proof (JMeq_eq (fold_reptype_JMeq t' v_res)) as H0;
    rewrite H0 in H;
    clear H0
  end.

Ltac pose_upd_reptype CS CSL t gfs v v0 H :=
  match gfs with
  | nil => 
      assert (data_equal (@upd_reptype_rec CS CSL t gfs v v0) v0) as H by reflexivity
  | ?gf :: ?gfs0 =>
      pose proof I as H;   (* *2* SEE LINE *3* *)
      match goal with
      | HH : eq_pose (proj_reptype t gfs0 v) ?v1 |- _ =>
          let H_upd1 := fresh "H_upd1" in
          pose_upd_reptype_1 CS CSL (nested_field_type2 t gfs0) gf v1 v0 H_upd1;
          match type of H_upd1 with
          | data_equal _ ?v1' =>
                  let H0 := fresh "H" in
                  pose_upd_reptype CS CSL t gfs0 v v1' H0;
                  match type of H0 with
                  | data_equal _ ?v_res =>
                      clear H;         (* *3* SEE LINE *2* *)
                      assert (H: data_equal (@upd_reptype_rec CS CSL t gfs v v0) v_res);
                          [| clear H_upd1 H0]
                  end;
                 [change (@upd_reptype_rec CS CSL t gfs v v0) with
                   (@upd_reptype_rec CS CSL t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0));
                  unfold eq_pose in HH; rewrite HH;
                  eapply Equivalence.equiv_transitive;
                  [apply upd_reptype_rec_data_equal; exact H_upd1 | exact H0]
                 | clear HH]
          end
      end
  end.

Section Test.

Definition _f1 := 1%positive.
Definition _f2 := 2%positive.
Definition _f3 := 3%positive.
Definition _f4 := 4%positive.
Definition _f5 := 5%positive.
Definition cd1 := Composite 101%positive Struct ((_f1, tint) :: (_f2%positive, tint) :: nil) noattr.
Definition cd2 := Composite 102%positive Struct ((_f3, Tstruct 101%positive noattr) ::
                                 (_f4, Tstruct 101%positive noattr) ::
                                 (_f5, Tpointer (Tstruct 101%positive noattr) noattr) :: nil) noattr.
Definition cenv := match build_composite_env (cd1 :: cd2 :: nil) with Errors.OK env => env | _ => PTree.empty _ end.

Instance cs: compspecs.
  apply (mkcompspecs cenv).
  apply build_composite_env_consistent with (defs := cd1 :: cd2 :: nil).
  reflexivity.
Defined.

Instance csl: compspecs_legal cs.
  split.
  + intros ? ? ?.
    apply PTree.elements_correct in H.
    revert H.
    change co with (snd (id, co)) at 2.
    forget (id, co) as ele.
    revert ele.
    apply Forall_forall.
    assert (8 >= 8) by omega.
    assert (4 >= 4) by omega.
    repeat constructor; unfold composite_legal_alignas; assumption.
  + intros ? ? ?.
    apply PTree.elements_correct in H.
    revert H.
    change co with (snd (id, co)) at 2.
    forget (id, co) as ele.
    revert ele.
    apply Forall_forall.
    repeat constructor; unfold composite_legal_alignas; reflexivity.
Defined.

Definition t1 := Tstruct 101%positive noattr.
Definition t2 := Tstruct 102%positive noattr.
Definition v1: reptype t1 := (Vint Int.zero, Vint Int.one).
Definition v2: reptype t2 := ((Vint Int.zero, Vint Int.one), ((Vint Int.zero, Vint Int.one), Vundef)).

(*
Eval vm_compute in (reptype_gen t2).
Eval vm_compute in (proj_reptype t1 (StructField 1%positive :: nil) v1).
*)
Goal proj_reptype t1 (StructField _f1 :: nil) v1 = Vint Int.zero.
reflexivity.
Qed.

Goal proj_reptype t2 (StructField _f2 :: StructField _f3 :: nil) v2 = Vint Int.one.
unfold v2.
pose_proj_reptype cs csl t2
  (StructField _f2 :: StructField _f3 :: nil) ((Vint Int.zero, Vint Int.one, (Vint Int.zero, Vint Int.one, Vundef)): reptype (Tstruct 102%positive noattr)) HH.
eauto.
Time Qed. (* Cut down from 10 seconds to 4 seconds, magically. *)

Goal forall n l, 0 < n -> proj_reptype (tarray tint n) (ArraySubsc 0 :: nil) l = Znth 0 l Vundef.
intros.
pose_proj_reptype cs csl (tarray tint n) (ArraySubsc 0 :: nil) l HH.
exact HH.
Qed.

Goal data_equal (upd_reptype t2 (StructField 3%positive :: nil) v2 (Vint Int.one, Vint Int.one))
((Vint Int.one, Vint Int.one), ((Vint Int.zero, Vint Int.one), Vundef)).
set (v0 := (Vint Int.one, Vint Int.one)).
change (val * val)%type with (reptype (Tstruct 101%positive noattr)) in v0.
pose_proj_reptype cs csl (Tstruct 102%positive noattr) (StructField 3%positive :: nil) v2 H.
pose_upd_reptype cs csl (Tstruct 102%positive noattr) (StructField 3%positive :: nil) v2 v0 H1.
rewrite upd_reptype_ind.
exact H1.
Qed.

Goal forall n l, 0 < n -> data_equal
    (upd_reptype (tarray tint n) (ArraySubsc 0 :: nil) l Vundef) 
    (Vundef :: skipn (Z.to_nat 1) l).
intros.
pose_proj_reptype cs csl (tarray tint n) (ArraySubsc 0 :: nil) l HH.
pose_upd_reptype cs csl (tarray tint n) (ArraySubsc 0 :: nil) l Vundef HHH.
rewrite upd_reptype_ind.
exact HHH.
Qed.

End Test.

