Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.type_induction.
Require Export VST.floyd.compact_prod_sum.
Require Import VST.floyd.fieldlist.
Require Import VST.zlist.sublist.

Local Unset SsrRewrite.

Definition
map_map: forall {A B C : Type} (f : A -> B) (g : B -> C) (l : list A),
       map g (map f l) = map (fun x : A => g (f x)) l :=
fun {A B C : Type} (f : A -> B) (g : B -> C) (l : list A) =>
list_ind
  (fun l0 : list A => map g (map f l0) = map (fun x : A => g (f x)) l0)
  eq_refl
  (fun (a : A) (l0 : list A)
     (IHl : map g (map f l0) = map (fun x : A => g (f x)) l0) =>
   eq_ind_r
     (fun l1 : list C =>
      g (f a) :: l1 = g (f a) :: map (fun x : A => g (f x)) l0) eq_refl IHl)
  l.

(******************************************

Definition of reptype.

******************************************)

Notation sigTT P := (fun tv => match tv with existT t v => P t end).

Definition compact_prod_sigT_type {A} {P: A -> Type} (l: list (sigT P)): Type :=
  compact_prod (map (sigTT P) l).
Arguments compact_prod_sigT_type {A} {P} l / .

Definition compact_prod_sigT_value: forall {A} {P: A -> Type} (l: list (sigT P)), compact_prod (map (sigTT P) l).
Proof.
  intros.
  destruct l as [| [t0 v0] l]; [exact tt |].
  revert t0 v0; induction l as [| [t v] l]; intros.
  + exact v0.
  + exact (v0, IHl t v).
Defined.

Definition compact_sum_sigT_type {A} {P: A -> Type} (l: list (sigT P)): Type :=
  compact_sum (map (sigTT P) l).

Arguments compact_sum_sigT_type {A} {P} l / .

Definition compact_sum_sigT_value: forall {A} {P: A -> Type} (l: list (sigT P)), compact_sum (map (sigTT P) l).
Proof.
  intros.
  destruct l as [| [t0 v0] l]; [exact tt |].
  revert t0 v0; destruct l as [| [t v] l]; intros.
  + exact v0.
  + exact (@inl (P t0) (compact_sum
  (@map {x : A & P x} Type (fun tv : {x : A & P x} => let (t1, _) := tv in P t1)
     (@existT A P t v :: l))) v0).
Defined.

Definition compact_prod_map {X: Type} {F F0: X -> Type} (l: list X)
  (f: hlist (tmap (fun x => F x -> F0 x) l)): compact_prod (map F l) -> compact_prod (map F0 l).
Proof.
  intros.
  destruct l; [exact tt |].
  revert x f X0; induction l; intros; simpl in *.
  + inversion f; subst.
    exact (X1 X0).
  + remember ((F a -> F0 a) :: map (fun x0 : X => F x0 -> F0 x0) l) as L;
    inversion f; subst.
    exact (X1 (fst X0), IHl a X2 (snd X0)).
Defined.

Lemma compact_prod_map_nil: forall {X: Type} {F F0: X -> Type},
  @compact_prod_map X F F0 nil hnil tt = tt.
Proof.
  intros.
  reflexivity.
Qed.

Lemma compact_prod_map_single: forall {X: Type} {F F0: X -> Type} (x: X)
  (f: F x -> F0 x) (v: F x),
  compact_prod_map (x :: nil) (hcons f hnil) v = f v.
Proof.
  intros.
  reflexivity.
Qed.

Lemma compact_prod_map_cons: forall {X: Type} {F F0: X -> Type} (x x0: X) (l: list X)
  (f: F x -> F0 x) (fl: hlist (tmap (fun x => F x -> F0 x) (x0 :: l)))
  (v: F x) (vl: compact_prod (map F (x0 :: l))),
  compact_prod_map (x :: x0 :: l) (hcons f fl) (v, vl) = (f v, compact_prod_map _ fl vl).
Proof.
  intros.
  reflexivity.
Qed.

Definition compact_sum_map {X: Type} {F F0: X -> Type} (l: list X)
  (f: hlist (tmap (fun x => F x -> F0 x) l)): compact_sum (map F l) -> compact_sum (map F0 l).
Proof.
  intros.
  destruct l; [exact tt |].
  revert x f X0; induction l; intros; simpl in *.
  + inversion f; subst.
    exact (X1 X0).
  + remember ((F a -> F0 a) :: map (fun x0 : X => F x0 -> F0 x0) l) as L;
    inversion f; subst.
    exact match X0 with
          | inl X0_l => inl (X1 X0_l)
          | inr X0_r => inr (IHl a X2 X0_r)
          end.
Defined.

Lemma compact_sum_map_nil: forall {X: Type} {F F0: X -> Type},
  @compact_sum_map X F F0 nil hnil tt = tt.
Proof.
  intros.
  reflexivity.
Qed.

Lemma compact_sum_map_single: forall {X: Type} {F F0: X -> Type} (x: X)
  (f: F x -> F0 x) (v: F x),
  compact_sum_map (x :: nil) (hcons f hnil) v = f v.
Proof.
  intros.
  reflexivity.
Qed.

Lemma compact_sum_map_cons_inl: forall {X: Type} {F F0: X -> Type} (x x0: X) (l: list X)
  (f: F x -> F0 x) (fl: hlist (tmap (fun x => F x -> F0 x) (x0 :: l)))
  (v: F x),
  compact_sum_map (x :: x0 :: l) (hcons f fl) (inl v) = inl (f v).
Proof.
  intros.
  reflexivity.
Qed.

Lemma compact_sum_map_cons_inr: forall {X: Type} {F F0: X -> Type} (x x0: X) (l: list X)
  (f: F x -> F0 x) (fl: hlist (tmap (fun x => F x -> F0 x) (x0 :: l)))
  (vl: compact_sum (map F (x0 :: l))),
  compact_sum_map (x :: x0 :: l) (hcons f fl) (inr vl) = inr (compact_sum_map _ fl vl).
Proof.
  intros.
  reflexivity.
Qed.

Definition reptype_gen {cs: compspecs} : type -> (sigT (fun x => x)) :=
  type_func (fun _ => (sigT (fun x => x)))
  (fun t =>
     if (type_is_by_value t)
     then existT (P := fun x => x) val Vundef
     else existT (P := fun x => x) unit tt)
  (fun t n a TV => existT (P := fun x => x) (list (projT1 TV)) (Zrepeat (projT2 TV) n))
  (fun id a TVs => existT (P := fun x => x) (compact_prod_sigT_type (decay TVs)) (compact_prod_sigT_value (decay TVs)))
  (fun id a TVs => existT (P := fun x => x) (compact_sum_sigT_type (decay TVs)) (compact_sum_sigT_value (decay TVs))).

Definition reptype_gen0 {cs: compspecs} : type -> (sigT (fun x => x)) :=
  type_func (fun _ => (sigT (fun x => x)))
  (fun t =>
     match t with
     | Tint _ _ _ => existT (P := fun x => x) val (Vint Int.zero)
     | Tlong _ _ => existT (P := fun x => x) val (Vlong Int64.zero)
     | Tfloat F32 _ => existT (P := fun x => x) val (Vsingle Float32.zero)
     | Tfloat F64 _ => existT (P := fun x => x) val (Vfloat Float.zero)
     | Tpointer _ _ => existT (P := fun x => x) val (Vptrofs Ptrofs.zero)
     | _ => existT (P := fun x => x) unit tt
     end)
  (fun t n a TV => existT (P := fun x => x) (list (projT1 TV)) (Zrepeat (projT2 TV) n))
  (fun id a TVs => existT (P := fun x => x) (compact_prod_sigT_type (decay TVs)) (compact_prod_sigT_value (decay TVs)))
  (fun id a TVs => existT (P := fun x => x) (compact_sum_sigT_type (decay TVs)) (compact_sum_sigT_value (decay TVs))).

Definition reptype {cs: compspecs} t: Type := match reptype_gen t with existT t _ => t end.

Definition default_val {cs: compspecs} t: reptype t :=
  match reptype_gen t as tv
    return match tv with existT t _ => t end
  with existT t v => v end.

#[export] Instance Inhabitant_reptype {cs: compspecs} (t: type) : Inhabitant (reptype t) := default_val t.

Lemma reptype_gen_eq {cs: compspecs}: forall t,
  reptype_gen t =
  match t with
  | Tarray t0 n _ => existT (P := fun x => x) (list (projT1 (reptype_gen t0))) (Zrepeat (projT2 (reptype_gen t0)) n)
  | Tstruct id _ => existT (P := fun x => x)
                     (compact_prod_sigT_type (map reptype_gen (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
                     (compact_prod_sigT_value (map reptype_gen (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
  | Tunion id _ => existT (P := fun x => x)
                     (compact_sum_sigT_type (map reptype_gen (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
                     (compact_sum_sigT_value (map reptype_gen (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
  | _ => if (type_is_by_value t)
         then existT (P := fun x => x) val Vundef
         else existT (P := fun x => x) unit tt
  end.
Proof.
  intros.
  unfold reptype_gen at 1.
  rewrite type_func_eq.
  destruct t; auto.
  +  unfold FTI_aux; rewrite decay_spec.
    rewrite map_map.
    reflexivity.
  + unfold FTI_aux; rewrite decay_spec.
    rewrite map_map.
    reflexivity.
Defined.


Lemma reptype_gen0_eq {cs: compspecs}: forall t,
  reptype_gen0 t =
  match t with
  | Tarray t0 n _ => existT (P := fun x => x) (list (projT1 (reptype_gen0 t0))) (Zrepeat (projT2 (reptype_gen0 t0)) n)
  | Tstruct id _ => existT (P := fun x => x)
                     (compact_prod_sigT_type (map reptype_gen0 (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
                     (compact_prod_sigT_value (map reptype_gen0 (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
  | Tunion id _ => existT (P := fun x => x)
                     (compact_sum_sigT_type (map reptype_gen0 (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
                     (compact_sum_sigT_value (map reptype_gen0 (map (fun it => field_type (name_member it) (co_members (get_co id))) (co_members (get_co id)))))
  | _ => 
     match t with
     | Tint _ _ _ => existT (P := fun x => x) val (Vint Int.zero)
     | Tlong _ _ => existT (P := fun x => x) val (Vlong Int64.zero)
     | Tfloat F32 _ => existT (P := fun x => x) val (Vsingle Float32.zero)
     | Tfloat F64 _ => existT (P := fun x => x) val (Vfloat Float.zero)
     | Tpointer _ _ => existT (P := fun x => x) val (Vptrofs Ptrofs.zero)
     | _ => existT (P := fun x => x) unit tt
     end
  end.
Proof.
  intros.
  unfold reptype_gen0 at 1.
  rewrite type_func_eq.
  destruct t; auto.
  +  unfold FTI_aux; rewrite decay_spec.
    rewrite map_map.
    reflexivity.
  + unfold FTI_aux; rewrite decay_spec.
    rewrite map_map.
    reflexivity.
Defined.

Definition reptype0 {cs: compspecs} t := match reptype_gen0 t with existT t _ => t end.

Lemma reptype_reptype0' {cs} t: @reptype cs t = @reptype0 cs t.
Proof.
unfold reptype, reptype0.
assert (forall t, projT1 (reptype_gen t) = projT1 (reptype_gen0 t)).
2: specialize (H t); destruct (reptype_gen t), (reptype_gen0 t); apply H.
clear t; intro t.
type_induction t; auto.
- destruct f; auto.
- rewrite reptype_gen_eq, reptype_gen0_eq. simpl; f_equal; auto.
- rewrite reptype_gen_eq, reptype_gen0_eq. simpl.
   forget (co_members (get_co id)) as m. clear id.
   cbv zeta in IH.
   rewrite !map_map.
   apply compact_prod_eq; intros [i t|].
   rewrite Forall_forall in IH.
   intro. apply IH in H. auto.
   rewrite Forall_forall in IH.
   intro. apply IH in H. auto.
- rewrite reptype_gen_eq, reptype_gen0_eq. simpl.
   forget (co_members (get_co id)) as m. clear id.
   cbv zeta in IH.
   rewrite !map_map.
   apply compact_sum_eq; intros [i t|].
   rewrite Forall_forall in IH.
   intro. apply IH in H. auto.
   rewrite Forall_forall in IH.
   intro. apply IH in H. auto.
Qed.


Lemma reptype_reptype0: @reptype = @reptype0.
Proof.
extensionality cs t. apply reptype_reptype0'.
Qed.

Definition zero_val' {cs: compspecs} t: reptype0 t :=
  match reptype_gen0 t as tv
    return match tv with existT t _ => t end
  with existT t v => v end.

Definition zero_val {cs: compspecs} t : reptype t :=
 eq_rect_r (fun T : Type => T) (zero_val' t) (equal_f (equal_f reptype_reptype0 cs) t).

Lemma JMeq_zero_val_zero_val':
  forall {cs} t, JMeq (@zero_val cs t) (@zero_val' cs t).
Proof.
intros.
exists (equal_f (equal_f reptype_reptype0 cs) t).
unfold zero_val.
rewrite rew_opp_r. reflexivity.
Qed.

Section CENV.
Context {cs: compspecs}.

Definition reptype_structlist (m: members) := compact_prod (map (fun it => reptype (field_type (name_member it) m)) m).
Definition reptype_unionlist (m: members) := compact_sum (map (fun it => reptype (field_type (name_member it) m)) m).

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

Lemma reptype_eq: forall t,
  reptype t = REPTYPE t.
Proof.
  intros.
  unfold reptype.
  rewrite reptype_gen_eq.
  destruct t as [| | | | | | | id ? | id ?]; auto.
  + unfold compact_prod_sigT_type.
    pose proof get_co_members_no_replicate id.
    forget (co_members (get_co id)) as m.
    rewrite map_map.
    rewrite map_map.
    unfold reptype_structlist.
    f_equal.
  + unfold compact_sum_sigT_type.
    pose proof get_co_members_no_replicate id.
    forget (co_members (get_co id)) as m.
    rewrite map_map.
    rewrite map_map.
    unfold reptype_unionlist.
    f_equal.
Defined.

Definition unfold_reptype {t} (v: reptype t): REPTYPE t :=
  @eq_rect Type (reptype t) (fun x: Type => x) v (REPTYPE t) (reptype_eq t).

Definition fold_reptype {t} (v: REPTYPE t): reptype t :=
  @eq_rect_r Type (REPTYPE t) (fun x: Type => x) v (reptype t) (reptype_eq t).

Lemma fold_unfold_reptype: forall t (v: reptype t),
  fold_reptype (unfold_reptype v) = v.
Proof.
  intros.
  unfold fold_reptype, unfold_reptype.
  apply JMeq_eq.
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    eapply @JMeq_trans; [apply (eq_rect_r_JMeq A x y F v H) |]
  end.
  match goal with
  | |- JMeq (@eq_rect ?A ?x ?F ?v ?y ?H) _ =>
    apply (eq_rect_JMeq A x y F v H)
  end.
Defined.

Lemma unfold_fold_reptype: forall t (v: REPTYPE t),
  unfold_reptype (fold_reptype v) = v.
Proof.
  intros.
  unfold fold_reptype, unfold_reptype.
  apply JMeq_eq.
  match goal with
  | |- JMeq (@eq_rect ?A ?x ?F ?v ?y ?H) _ =>
    eapply @JMeq_trans; [apply (eq_rect_JMeq A x y F v H) |]
  end.
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    apply (eq_rect_r_JMeq A x y F v H)
  end.
Defined.

Lemma unfold_reptype_JMeq: forall t (v: reptype t),
  JMeq (unfold_reptype v) v.
Proof.
  intros.
  unfold unfold_reptype.
  match goal with
  | |- JMeq (@eq_rect ?A ?x ?F ?v ?y ?H) _ =>
    apply (eq_rect_JMeq A x y F v H)
  end.
Qed.

Lemma fold_reptype_JMeq: forall t v,
  JMeq (fold_reptype v : reptype t) v.
Proof.
  intros.
  unfold fold_reptype.
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    apply (eq_rect_r_JMeq A x y F v H)
  end.
Qed.

Definition union_default_filter m :=
  match m with
  | nil => fun _ => false
  | hd :: _ => fun m => if member_dec hd m then true else false
  end.

Definition is_default_filter {A} f (l: list A) : Prop :=
  match l with
  | nil => True
  | hd :: _ => f hd = true
  end.

Lemma union_default_filter_is_default_filter: forall m, is_default_filter (union_default_filter m) m.
Proof.
  intros.
  destruct m; simpl; auto.
  destruct (member_dec m m); auto.
Qed.

Lemma const_true_is_default_filter: forall m, is_default_filter (fun _: member => true) m.
Proof.
  intros.
  destruct m; simpl; auto.
Qed.

Definition struct_default_val (m : members) := compact_prod_gen (fun it => default_val (field_type (name_member it) m)) m.
Definition union_default_val (m : members) := compact_sum_gen (fun it => true) (fun it => default_val (field_type (name_member it) m)) m.

Definition struct_zero_val (m : members) := compact_prod_gen (fun it => zero_val (field_type (name_member it) m)) m.
Definition union_zero_val (m : members) := compact_sum_gen (fun it => true) (fun it => zero_val (field_type (name_member it) m)) m.

Definition struct_zero_val' (m : members) := compact_prod_gen (fun it => zero_val' (field_type (name_member it) m)) m.
Definition union_zero_val' (m : members) := compact_sum_gen (fun it => true) (fun it => zero_val' (field_type (name_member it) m)) m.

Lemma struct_zero_val_JMeq:
  forall m, JMeq (struct_zero_val m) (struct_zero_val' m).
Proof.
intros.
unfold struct_zero_val, struct_zero_val'.
apply compact_prod_gen_JMeq; intros.
apply JMeq_zero_val_zero_val'.
Qed.

Lemma union_zero_val_JMeq:
  forall m, JMeq (union_zero_val m) (union_zero_val' m).
Proof.
intros.
unfold union_zero_val, union_zero_val'.
apply compact_sum_gen_JMeq; intros.
apply JMeq_zero_val_zero_val'.
Qed.

Lemma compact_prod_sigT_compact_prod_gen:
  forall {A B} {P: A -> Type} (genT: B -> A) (genV: forall b: B, P (genT b)) (gen: B -> sigT P) (l: list B),
    (forall b, gen b = existT (genT b) (genV b)) ->
    JMeq (compact_prod_sigT_value (map gen l)) (compact_prod_gen genV l).
Proof.
  intros.
  assert (gen = fun b => existT (genT b) (genV b)) by (extensionality; apply H).
  rewrite H0; clear H H0 gen.
  destruct l; [apply JMeq_refl |].
  revert b; induction l; intros.
  + apply JMeq_refl.
  + simpl map.
    change (compact_prod_gen genV (b :: a :: l)) with (genV b, compact_prod_gen genV (a :: l)).
    change (compact_prod_sigT_value
        (existT (genT b) (genV b)
         :: existT (genT a) (genV a)
            :: map (fun b0 : B => existT (genT b0) (genV b0)) l)) with
      (genV b, compact_prod_sigT_value (existT (genT a) (genV a) :: map (fun b0 : B => existT (genT b0) (genV b0)) l)).
    apply JMeq_pair; [auto |].
    exact (IHl a).
Qed.

Lemma compact_sum_sigT_compact_sum_gen:
  forall {A B} {P: A -> Type} (genT: B -> A) (genV: forall b: B, P (genT b)) (filter: B -> bool) (gen: B -> sigT P) (l: list B),
    (forall b, gen b = existT (genT b) (genV b)) ->
    is_default_filter filter l ->
    JMeq (compact_sum_sigT_value (map gen l)) (compact_sum_gen filter genV l).
Proof.
  intros.
  assert (gen = fun b => existT (genT b) (genV b)) by (extensionality; apply H).
  rewrite H1; clear H H1 gen.
  destruct l; [apply JMeq_refl |].
  destruct l.
  + apply JMeq_refl.
  + change (compact_sum_sigT_value
        (map (fun b1 : B => existT (genT b1) (genV b1)) (b :: b0 :: l))) with
  (@inl (P (genT b)) (compact_sum (map (fun tv => match tv with existT t _ => P t end) (map (fun b1 : B => @existT A P (genT b1) (genV b1)) (b0 :: l)))) (genV b)).
    change (compact_sum (map (fun tv => match _ with existT t _ => P t end) (map (fun b1 : B => @existT A P (genT b1) (genV b1)) (b :: b0 :: l)))) with
      (P (genT b) + compact_sum (map (fun tv => match tv with existT t _ => P t end) (map (fun b1 : B => @existT A P (genT b1) (genV b1)) (b0 :: l))))%type.
    replace (compact_sum_gen filter genV (b :: b0 :: l)) with
      (@inl (P (genT b)) (compact_sum (map (fun b1 : B => P (genT b1)) (b0 :: l))) (genV b)).
    2:{
      simpl in H0 |- *.
      rewrite H0.
      auto.
    }
    match goal with
    | |- @JMeq _ (@inl _ ?A _) _ (@inl _ ?B _) =>
         replace A with B; [auto |]
    end.
    rewrite map_map; reflexivity.
Qed.

Lemma default_val_eq: forall t,
  default_val t =
  fold_reptype
  match t as t' return REPTYPE t'
  with
  | Tvoid
  | Tfunction _ _ _ => tt
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tpointer _ _ => Vundef
  | Tarray t0 n _ => Zrepeat (default_val t0) n 
  | Tstruct id _ => struct_default_val (co_members (get_co id))
  | Tunion id _ => union_default_val (co_members (get_co id))
  end.
Proof.
  intros.
  unfold fold_reptype.
  apply JMeq_eq.
  match goal with
  | |- JMeq _ (@eq_rect_r ?A ?x ?F ?v ?y ?H) =>
    eapply JMeq_trans; [| apply @JMeq_sym; apply (@eq_rect_r_JMeq A x y F v H)]
  end.
  unfold default_val.
  unfold reptype at 1.
  rewrite reptype_gen_eq.
  destruct t; auto.
  + unfold struct_default_val.
    rewrite map_map.
    apply (compact_prod_sigT_compact_prod_gen
      (fun it => reptype (field_type (name_member it) (co_members (get_co i))))
      (fun it => default_val (field_type (name_member it) (co_members (get_co i))))
      (fun it => reptype_gen (field_type (name_member it) (co_members (get_co i))))); intros.
    unfold reptype, default_val.
    destruct (reptype_gen (field_type (name_member b) (co_members (get_co i)))); reflexivity.
  + unfold union_default_val.
    rewrite map_map.
    apply (compact_sum_sigT_compact_sum_gen
      (fun it => reptype (field_type (name_member it) (co_members (get_co i))))
      (fun it => default_val (field_type (name_member it) (co_members (get_co i))))
      _
      (fun it => reptype_gen (field_type (name_member it) (co_members (get_co i))))); intros.
    unfold reptype, default_val.
    destruct (reptype_gen (field_type (name_member b) (co_members (get_co i)))); reflexivity.
    apply const_true_is_default_filter.
Qed.

Lemma zero_val_eq: forall t,
  zero_val t =
  fold_reptype
  match t as t' return REPTYPE t'
  with
  | Tvoid
  | Tfunction _ _ _ => tt
  | Tint _ _ _ => Vint Int.zero
  | Tlong _ _ => Vlong Int64.zero
  | Tfloat F32 _ => Vsingle Float32.zero
  | Tfloat F64 _ => Vfloat Float.zero
  | Tpointer _ _ => Vptrofs Ptrofs.zero
  | Tarray t0 n _ => Zrepeat (zero_val t0) n
  | Tstruct id _ => struct_zero_val (co_members (get_co id))
  | Tunion id _ => union_zero_val (co_members (get_co id))
  end.
Proof.
  intros.
  unfold fold_reptype.
  apply JMeq_eq.
  match goal with
  | |- JMeq _ (@eq_rect_r ?A ?x ?F ?v ?y ?H) =>
    eapply JMeq_trans; [| apply @JMeq_sym; apply (@eq_rect_r_JMeq A x y F v H)]
  end.
  apply (@JMeq_trans _ _ _ _ (zero_val' t)).
  apply JMeq_zero_val_zero_val'.
  unfold zero_val'.
  unfold reptype0 at 1.
  rewrite reptype_gen0_eq.  
  destruct t; auto.
  + destruct f; auto.
  + apply (@JMeq_trans _ _ _ _  (Zrepeat (zero_val' t) z)).
      apply eq_JMeq. f_equal.
      apply JMeq_func; auto. rewrite reptype_reptype0. auto.
      apply JMeq_func; auto. rewrite reptype_reptype0. auto.
      apply JMeq_sym. apply JMeq_zero_val_zero_val'.
      rewrite reptype_reptype0. apply JMeq_refl.
  + 
    apply (@JMeq_trans _ _ _ _  (struct_zero_val' (co_members (get_co i)))).
    2: apply JMeq_sym; apply struct_zero_val_JMeq.
    unfold struct_zero_val'.
    rewrite map_map.
    apply (compact_prod_sigT_compact_prod_gen
      (fun it => reptype0 (field_type (name_member it) (co_members (get_co i))))
      (fun it => zero_val' (field_type (name_member it) (co_members (get_co i))))
      (fun it => reptype_gen0 (field_type (name_member it) (co_members (get_co i))))); intros.
    unfold reptype0, zero_val'.
    destruct (reptype_gen0 (field_type (name_member b) (co_members (get_co i)))); reflexivity.
  + apply (@JMeq_trans _ _ _ _  (union_zero_val' (co_members (get_co i)))).
    2: apply JMeq_sym; apply union_zero_val_JMeq.
    unfold union_default_val.
    rewrite map_map.
    apply (compact_sum_sigT_compact_sum_gen
      (fun it => reptype0 (field_type (name_member it) (co_members (get_co i))))
      (fun it => zero_val' (field_type (name_member it) (co_members (get_co i))))
      _
      (fun it => reptype_gen0 (field_type (name_member it) (co_members (get_co i))))); intros.
    unfold reptype0, zero_val'.
    destruct (reptype_gen0 (field_type (name_member b) (co_members (get_co i)))); reflexivity.
    apply const_true_is_default_filter.
Qed.

Inductive pointer_val : Type :=
  | ValidPointer: block -> Ptrofs.int -> pointer_val
  | NullPointer.

Lemma PV_eq_dec: forall x y: pointer_val, {x = y} + {x <> y}.
Proof.
  intros; destruct x, y; [| right | right | left]; try congruence.
  destruct (block_eq_dec b b0), (Ptrofs.eq_dec i i0); [left | right | right | right]; congruence.
Qed.

Lemma zero_in_range : (-1 < 0 < Int.modulus)%Z.
compute; split; auto.
Defined.
Definition Int_zero := Int.mkint 0 zero_in_range.

Definition pointer_val_val (pv: pointer_val): val :=
  match pv with
  | ValidPointer b i => Vptr b i
  | NullPointer => nullval
  end.

Definition reptype': type -> Type :=
  type_func (fun _ => Type)
  (fun t =>
     if (type_is_by_value t)
     then match t with
          | Tint _ _ _ => int
          | Tlong _ _ => Int64.int
          | Tfloat _ _ => float
          | Tpointer _ _ => pointer_val
          | _ => val
          end
     else unit)
  (fun t n a T => list T)
  (fun id a T => compact_prod (decay T))
  (fun id a T => compact_sum (decay T)).

Notation REPTYPE' t :=
  match t return Type with
  | Tvoid
  | Tfunction _ _ _ => unit
  | Tint _ _ a => int
  | Tlong _ a => Int64.int
  | Tfloat _ a => float
  | Tpointer _ a => pointer_val
  | Tarray t0 _ _ => list (reptype' t0)
  | Tstruct id _ => compact_prod (map (fun it => reptype' (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id)))
  | Tunion id _ => compact_sum (map (fun it => reptype' (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id)))
  end.

Lemma reptype'_eq: forall t,
  reptype' t = REPTYPE' t.
Proof.
  intros.
 unfold reptype'.
 etransitivity.
 apply (type_func_eq (fun _ => Type) _ _ _ _ t) .
  destruct t; auto.
  + f_equal.
    unfold FTI_aux; rewrite decay_spec.
    reflexivity.
  + f_equal.
    unfold FTI_aux; rewrite decay_spec.
    reflexivity.
Defined.

Definition unfold_reptype' {t} (v: reptype' t): REPTYPE' t :=
  @eq_rect Type (reptype' t) (fun x: Type => x) v (REPTYPE' t) (reptype'_eq t).

Definition fold_reptype' {t} (v: REPTYPE' t): reptype' t :=
  @eq_rect_r Type (REPTYPE' t) (fun x: Type => x) v (reptype' t) (reptype'_eq t).

Lemma fold_unfold_reptype': forall t (v: reptype' t),
  fold_reptype' (unfold_reptype' v) = v.
Proof.
  intros.
  unfold fold_reptype', unfold_reptype'.
  apply JMeq_eq.
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    eapply JMeq_trans; [apply (eq_rect_r_JMeq A x y F v H) |]
  end.
  match goal with
  | |- JMeq (@eq_rect ?A ?x ?F ?v ?y ?H) _ =>
    apply (eq_rect_JMeq A x y F v H)
  end.
Defined.

Lemma unfold_fold_reptype': forall t (v: REPTYPE' t),
  unfold_reptype' (fold_reptype' v) = v.
Proof.
  intros.
  unfold fold_reptype', unfold_reptype'.
  apply JMeq_eq.
  match goal with
  | |- JMeq (@eq_rect ?A ?x ?F ?v ?y ?H) _ =>
    eapply JMeq_trans; [apply (eq_rect_JMeq A x y F v H) |]
  end.
  match goal with
  | |- JMeq (@eq_rect_r ?A ?x ?F ?v ?y ?H) _ =>
    apply (eq_rect_r_JMeq A x y F v H)
  end.
Defined.

Definition repinj_bv (t: type): reptype' t -> reptype t :=
  fun v =>
  fold_reptype
  (match t as t' return (REPTYPE' t' -> REPTYPE t': Type)
   with
   | Tvoid
   | Tfunction _ _ _ => @id unit
   | Tint _ _ a => Vint
   | Tlong _ a => Vlong
   | Tfloat _ a => Vfloat
   | Tpointer _ a => pointer_val_val
   | Tarray t0 n a => fun _ => nil
   | Tstruct id a => fun _ => struct_default_val _
   | Tunion id a => fun _ => union_default_val _
   end (unfold_reptype' v)).

Definition repinj_aux_s (id: ident) (a: attr) (F: hlist (tmap (fun it => reptype' (field_type (name_member it) (co_members (get_co id))) -> reptype (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id)))): reptype' (Tstruct id a) -> reptype (Tstruct id a) :=
  fun v => @fold_reptype (Tstruct id a) (compact_prod_map _ F (unfold_reptype' v)).

Definition repinj_aux_u (id: ident) (a: attr) (F: hlist (tmap (fun it => reptype' (field_type (name_member it) (co_members (get_co id))) -> reptype (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id)))): reptype' (Tunion id a) -> reptype (Tunion id a) :=
  fun v => @fold_reptype (Tunion id a) (compact_sum_map _ F (unfold_reptype' v)).

Definition repinj: forall t: type, reptype' t -> reptype t :=
  type_func (fun t => reptype' t -> reptype t)
  repinj_bv
  (fun t n a f v => @fold_reptype (Tarray t n a) (map f (unfold_reptype' v)))
  repinj_aux_s
  repinj_aux_u.

Lemma repinj_eq: forall t v,
  repinj t v =
  fold_reptype
  (match t as t' return REPTYPE' t' -> REPTYPE t' with
   | Tvoid
   | Tfunction _ _ _ => @id unit
   | Tint _ _ a => Vint
   | Tlong _ a => Vlong
   | Tfloat _ a => Vfloat
   | Tpointer _ a => pointer_val_val
   | Tarray t0 _ _ => map (repinj t0)
   | Tstruct id a => compact_prod_map _ (hmap (fun it => reptype' (field_type (name_member it) (co_members (get_co id))) -> reptype (field_type (name_member it) (co_members (get_co id)))) (fun it => repinj (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id)))
   | Tunion id a => compact_sum_map _ (hmap (fun it => reptype' (field_type (name_member it) (co_members (get_co id))) -> reptype (field_type (name_member it) (co_members (get_co id)))) (fun it => repinj (field_type (name_member it) (co_members (get_co id)))) (co_members (get_co id)))
   end (unfold_reptype' v)).
Proof.
  intros.
  unfold repinj.
  rewrite type_func_eq.
  destruct t; auto.
Defined.

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Local Hint Rewrite int_add_repr_0_l int_add_repr_0_r : norm.

Lemma ptrofs_add_repr_0_l: forall i, Ptrofs.add (Ptrofs.repr 0) i = i.
Proof. intros. apply Ptrofs.add_zero_l. Qed.
Lemma ptrofs_add_repr_0_r: forall i, Ptrofs.add i (Ptrofs.repr 0) = i.
Proof. intros. apply Ptrofs.add_zero. Qed.
Local Hint Rewrite ptrofs_add_repr_0_l ptrofs_add_repr_0_r : norm.

Definition repinject (t: type) : reptype t -> val :=
  match t as t0 return reptype t0 -> val with
  | Tint _ _ _ => fun v => v
  | Tlong _ _ => fun v => v
  | Tfloat _ _ => fun v => v
  | Tpointer _ _ => fun v => v
  | _ => fun _ => Vundef
 end.

Definition valinject (t: type) : val -> reptype t :=
  match t as t0 return val -> reptype t0 with
  | Tint _ _ _ => fun v => v
  | Tlong _ _ => fun v => v
  | Tfloat _ _ => fun v => v
  | Tpointer _ _ => fun v => v
  | t => fun _ => default_val t
 end.

Lemma valinject_JMeq: forall t v, type_is_by_value t = true -> JMeq (valinject t v) v.
Proof.
  intros.
  destruct t; simpl in *; try congruence; try tauto; apply JMeq_refl.
Qed.

Lemma repinject_JMeq: forall t v, type_is_by_value t = true -> JMeq (repinject t v) v.
Proof.
  intros.
  destruct t; simpl in *; try congruence; try tauto; apply JMeq_refl.
Qed.

Lemma repinject_unfold_reptype: forall t v,
  match t as t' return REPTYPE t' -> Prop with
  | Tint _ _ _
  | Tfloat _ _
  | Tlong _ _
  | Tpointer _ _ => fun vv => repinject t v = vv
  | _ => fun _ => True%type
  end (unfold_reptype v).
Proof.
  intros; destruct t; auto;
  unfold repinject;
  unfold unfold_reptype;
  rewrite <- eq_rect_eq; auto.
Qed.

Lemma repinject_valinject:
  forall t v,
    type_is_by_value t = true -> repinject t (valinject t v) = v.
Proof.
  intros.
  destruct t; try inversion H; reflexivity.
Qed.

Lemma valinject_repinject: forall t v,
  type_is_by_value t = true ->
  (valinject t (repinject t v)) = v.
Proof.
  intros.
  destruct t; inversion H; reflexivity.
Qed.

Lemma repinject_default_val:
 forall t, repinject t (default_val t) = Vundef.
Proof.
destruct t; reflexivity.
Qed.

End CENV.

Arguments reptype' {cs} t / .

Global Notation REPTYPE t :=
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

Tactic Notation "unfold_repinj" :=
repeat match goal with |- context [repinj ?T] =>
 let x := fresh "x" in set (x := repinj T);
    lazy beta iota zeta delta in x; subst x; lazy beta
end.

Tactic Notation "unfold_repinj" constr(T) :=
match goal with |- context [repinj T] =>
 let x := fresh "x" in set (x := repinj T);
    lazy beta iota zeta delta in x; subst x; lazy beta
end.

(* Too expensive to do "pattern (repinj T V)", this
  can blow up.
Tactic Notation "unfold_repinj" constr(T) constr(V) :=
   pattern (repinj T V);
  unfold_repinj' T.
*)

Lemma reptype_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @reptype cs_from t = @reptype cs_to t.
Proof.
  intros t.
  type_induction t; intros.
  + rewrite !reptype_eq.
    reflexivity.
  + rewrite !reptype_eq.
    reflexivity.
  + rewrite !reptype_eq.
    reflexivity.
  + rewrite !reptype_eq.
    reflexivity.
  + rewrite !reptype_eq.
    reflexivity.
  + rewrite (@reptype_eq cs_from), (@reptype_eq cs_to).
    rewrite IH; auto.
  + rewrite !reptype_eq.
    reflexivity.
  + rewrite (@reptype_eq cs_from), (@reptype_eq cs_to).
    simpl in H.
    rewrite co_members_get_co_change_composite by auto.
    apply members_spec_change_composite in H.
    cbv zeta in IH.
    revert H IH.
    unfold reptype_structlist.
    generalize (co_members (get_co id)) at 1 3 4 5 7 9; intros.
    f_equal.
    induction IH as [| [i t|] ?].
    - reflexivity.
    - Opaque field_type. simpl. Transparent field_type.
      inv H.
      f_equal; auto.
    - Opaque field_type. simpl. Transparent field_type.
      inv H.
      f_equal; auto.
  + rewrite (@reptype_eq cs_from), (@reptype_eq cs_to).
    simpl in H.
    rewrite co_members_get_co_change_composite by auto.
    apply members_spec_change_composite in H.
    cbv zeta in IH.
    revert H IH.
    unfold reptype_unionlist.
    generalize (co_members (get_co id)) at 1 3 4 5 7 9; intros.
    f_equal.
    induction IH as [| [i t|] ?].
    - reflexivity.
    - Opaque field_type. simpl. Transparent field_type.
      inv H.
      f_equal; auto.
    - Opaque field_type. simpl. Transparent field_type.
      inv H.
      f_equal; auto.
Qed.

Lemma default_val_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  JMeq (@default_val cs_from t) (@default_val cs_to t).
Proof.
  intros t.
  type_induction t; intros.
  + rewrite !default_val_eq.
    apply JMeq_refl.
  + rewrite !default_val_eq.
    apply JMeq_refl.
  + rewrite !default_val_eq.
    apply JMeq_refl.
  + rewrite !default_val_eq.
    apply JMeq_refl.
  + rewrite !default_val_eq.
    apply JMeq_refl.
  + rewrite (@default_val_eq cs_from), (@default_val_eq cs_to).
    eapply JMeq_trans; [| eapply JMeq_trans]; [apply fold_reptype_JMeq | | apply JMeq_sym, fold_reptype_JMeq].
    specialize (IH H).
    revert IH; generalize (@default_val cs_from t), (@default_val cs_to t).
    rewrite reptype_change_composite by auto.
    intros.
    apply JMeq_eq in IH; subst.
    apply JMeq_refl.
  + rewrite !default_val_eq.
    apply JMeq_refl.
  + rewrite (@default_val_eq cs_from), (@default_val_eq cs_to).
    eapply JMeq_trans; [| eapply JMeq_trans]; [apply fold_reptype_JMeq | | apply JMeq_sym, fold_reptype_JMeq].
    simpl in H.
    rewrite co_members_get_co_change_composite by auto.
    apply members_spec_change_composite in H.
    cbv zeta in IH.
    unfold struct_default_val.
    apply compact_prod_gen_JMeq.
    rewrite <- Forall_forall.
    revert H IH.
    generalize (co_members (get_co id)) at 1 3 4 5 6 7 9 10 11 12; intros.
    induction H as [| [i t|] ?].
    - constructor.
    - inv IH.
      constructor; auto.
    - inv IH.
      constructor; auto.
  + rewrite (@default_val_eq cs_from), (@default_val_eq cs_to).
    eapply JMeq_trans; [| eapply JMeq_trans]; [apply fold_reptype_JMeq | | apply JMeq_sym, fold_reptype_JMeq].
    simpl in H.
    rewrite co_members_get_co_change_composite by auto.
    apply members_spec_change_composite in H.
    cbv zeta in IH.
    unfold union_default_val.
    apply compact_sum_gen_JMeq.
    rewrite <- Forall_forall.
    revert H IH.
    generalize (co_members (get_co id)) at 1 3 4 5 6 7 9 10 11 12; intros.
    induction H as [| [i t|] ?].
    - constructor.
    - inv IH.
      constructor; auto.
    - inv IH.
      constructor; auto.
Qed.

Fixpoint force_lengthn {A} n (xs: list A) (default: A) :=
  match n, xs with
  | O, _ => nil
  | S n0, nil => default :: force_lengthn n0 nil default
  | S n0, hd :: tl => hd :: force_lengthn n0 tl default
  end.

Lemma force_lengthn_length_n: forall {A} n (xs : list A) (default: A),
  length (force_lengthn n xs default) = n.
Proof.
  intros.
  revert xs; induction n; intros.
  + reflexivity.
  + simpl.
    destruct xs; simpl; rewrite IHn; reflexivity.
Qed.

Lemma nth_force_lengthn_nil: forall {A} n i (default: A),
  nth i (force_lengthn n nil default) default = default.
Proof.
  intros.
  revert i; induction n; intros.
  + simpl. destruct i; reflexivity.
  + simpl. destruct i.
    - reflexivity.
    - rewrite IHn. reflexivity.
Qed.

Lemma nth_force_lengthn: forall {A} n i (xs : list A) (default: A),
  (0 <= i < n) %nat ->
  nth i (force_lengthn n xs default) default = nth i xs default.
Proof.
  intros.
  revert i H xs; induction n; intros.
  + lia.
  + simpl.
    destruct xs.
    - simpl.
      destruct i; [reflexivity |].
      apply nth_force_lengthn_nil.
    - simpl.
      destruct i; [reflexivity |].
      apply IHn.
      lia.
Qed.

Lemma force_lengthn_id: forall {A} n ct (d: A), length ct = n -> force_lengthn n ct d = ct.
Proof.
  intros.
  revert ct H; induction n; intros.
  + destruct ct; try solve [inversion H].
    reflexivity.
  + destruct ct; try solve [inversion H].
    simpl.
    rewrite IHn by auto.
    reflexivity.
Qed.

(* "replist" is an alternative to zlist, avoids mysterious typeclass *)

Open Scope Z.

Fixpoint replist' {A: Type} {d: Inhabitant A} (lo: Z) (n: nat) (al: list A) :=
 match n with
 | O => nil
 | S n' =>  Znth lo al :: replist' (Z.succ lo) n' al
 end.

Definition replist {cs: compspecs} (t: type)  (lo hi: Z) (al: list (reptype t)) :=
  replist'  lo (Z.to_nat (hi-lo)) al.

(* replist t lo hi al *)

Lemma replist_replist {cs: compspecs}:
 forall t (lo hi lo' hi': Z) al,
   0 <= lo <= hi ->
   0 <= lo' <= hi' ->
   lo'+hi <= hi'  ->
 replist t lo hi (replist t lo' hi' al) =
   replist t (lo+lo') (hi+lo') al.
Proof.
intros.
 unfold replist.
 forget (default_val t) as d.
 replace (hi + lo' - (lo + lo')) with (hi-lo) by lia.
 remember (Z.to_nat (hi-lo)) as n.
 assert (hi = lo + Z.of_nat n).
  subst n. rewrite Z2Nat.id by lia. lia.
 subst hi.
 clear Heqn. destruct H as [? _].
 rewrite Z.add_assoc in H1.
  revert lo lo' H H0 H1; induction n; intros; simpl.
   reflexivity.
 f_equal.
+
  clear - H H0 H1. destruct H0 as [? _].
  remember (Z.to_nat (hi'-lo')) as k.
  rewrite inj_S in H1.
  replace hi' with (lo' + Z.of_nat k) in H1
    by (subst k; rewrite Z2Nat.id by lia; lia).
  clear hi' Heqk.
  assert (lo < Z.of_nat k) by lia. clear H1.
  revert lo lo' H H0 H2; induction k; intros. simpl in H2; lia.
  unfold replist'; fold @replist'.
  rewrite inj_S in H2.
  simpl.
  assert (lo=0 \/ 0<lo) by lia.
  destruct H1. subst lo.
  unfold Znth at 1. rewrite if_false by lia. simpl. auto.
  clear H.
  unfold Znth at 1. rewrite if_false by lia.
  destruct (Z.to_nat lo) eqn:?.
  apply Z2Nat.inj_lt in H1; try lia.
  simpl nth.
  specialize (IHk (Z.of_nat n0) (Z.succ lo')).
  replace (lo+lo') with (Z.of_nat n0 + Z.succ lo').
2:{
  unfold Z.succ.
  transitivity (Z.of_nat n0 + 1 + lo'); [ lia |].
  f_equal. lia.
}
  etransitivity; [ | apply IHk]; try lia.
  unfold Znth. rewrite if_false by lia. rewrite Nat2Z.id. auto.
+
  specialize (IHn (Z.succ lo) lo'). rewrite IHn; try lia.
   f_equal; lia.
Qed.

Lemma replist'_succ:
 forall {A} {d:Inhabitant A} lo n r (al: list A),
   (lo>=0) -> replist' (Z.succ lo) n (r::al) = replist' lo n al.
Proof.
intros.
revert lo al H; induction n; simpl; intros.
auto.
f_equal.
unfold Znth.
 do 2 rewrite if_false by lia.
 replace (Z.to_nat (Z.succ lo)) with (S (Z.to_nat lo)).
 reflexivity. unfold Z.succ. rewrite Z2Nat.inj_add by lia.
 change (Z.to_nat 1) with 1%nat; lia.
 apply IHn. lia.
Qed.

Lemma replist_firstn_skipn {cs: compspecs}:
 forall t lo hi al,
  (lo <= hi <= length al)%nat ->
  replist t (Z.of_nat lo) (Z.of_nat hi) al = firstn (hi-lo) (skipn lo al).
Proof.
intros.
 unfold replist.
 rewrite <- Nat2Z.inj_sub by lia.
 rewrite Nat2Z.id.
 assert (hi-lo <= length al - lo)%nat by lia.
 clear H.
 forget (hi-lo)%nat as n. clear hi.
 revert n al H0; induction lo; intros.
 simpl.
 assert (n <= length al)%nat by lia; clear H0.
 revert al H; induction n; simpl; intros; auto.
 destruct al; simpl in H. lia.
 simpl. f_equal.
 unfold drop in IHn.
 rewrite <- (IHn al) by lia. clear IHn.
 rewrite <- (replist'_succ 0 n r al) by lia.
 reflexivity.
 rewrite inj_S.
  destruct al. simpl length in H0. assert (n=0)%nat by lia.
  subst;   simpl. auto.
  simpl length in H0. simpl in H0. simpl. rewrite <- (IHlo _ _ H0).
  apply replist'_succ. lia.
Qed.

Lemma skipn_0:
 forall A (al: list A) n,
  (n=0)%nat -> skipn n al = al.
Proof.
intros; subst; reflexivity.
Qed.

Lemma replist_elim {cs: compspecs}:
  forall t lo hi al,
    lo = 0 -> hi = Zlength al ->
    replist t lo hi al = al.
Proof.
intros.
subst.
change 0 with (Z.of_nat 0).
rewrite Zlength_correct.
rewrite replist_firstn_skipn by lia.
rewrite skipn_0 by auto.
rewrite Nat.sub_0_r.
apply firstn_exact_length.
Qed.

Lemma replist_Zlength {cs: compspecs}:
  forall t lo hi al,
    lo <= hi ->
   Zlength (replist t lo hi al) = hi-lo.
Proof.
intros.
rewrite <- (Z2Nat.id (hi-lo)) by lia.
unfold replist.
clear H.
forget (Z.to_nat (hi-lo)) as n. clear hi.
revert lo; induction n; intros.
simpl. rewrite Zlength_nil. auto.
rewrite inj_S.
simpl. rewrite Zlength_cons.
rewrite IHn. auto.
Qed.

Lemma replist_length {cs: compspecs}:
  forall t lo hi al,
    lo <= hi ->
   length (replist t lo hi al) = Z.to_nat (hi-lo).
Proof.
intros.
rewrite <- (Nat2Z.id (length _)).
f_equal.
rewrite <- Zlength_correct.
apply replist_Zlength; auto.
Qed.


(* #[export] Hint Rewrite skipn_0 using computable : norm. *)

Lemma unfold_reptype_elim:
  forall cs t v v',
    JMeq v v' ->
   @unfold_reptype cs t v = v'.
Proof.
intros.
unfold unfold_reptype.
match type of v' with ?t => set (t' := t) in * end.
pose proof (eq_rect_JMeq _ (reptype t) t' (fun x : Type => x) v (reptype_eq t)).
apply JMeq_eq.
apply @JMeq_trans with (reptype t) v; auto.
Qed.


Lemma Zlength_default_val_Tarray_tuchar {cs} n a (N:0<=n): Zlength (@default_val cs (Tarray tuchar n a)) = n.
Proof. unfold default_val; simpl. rewrite Zlength_Zrepeat; trivial. Qed.

