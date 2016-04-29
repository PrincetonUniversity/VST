Require Import AggregateType.demo2.expr.
Require Import Coq.Lists.List.

Definition list_prod (T: list Type): Type := fold_right prod unit T.

Fixpoint list_prod_gen {A} {F} (gen: forall a: A, F a) (l: list A): list_prod (map F l) :=
  match l as l_PAT return list_prod (map F l_PAT) with
  | nil => tt
  | t :: l0 => (gen t, list_prod_gen gen l0)
  end.

Notation sigTT P := (fun tv => match tv with existT t v => P t end).

Definition list_prod_sigT_type {A} {P: A -> Type} (l: list (sigT P)): Type :=
  list_prod (map (sigTT P) l).

Fixpoint list_prod_sigT_value {A} {P: A -> Type} (l: list (sigT P)): list_prod_sigT_type l :=
  match l as l_PAT return list_prod_sigT_type l_PAT with
  | nil => tt
  | tv :: l0 => (match tv as tv_PAT return sigTT P tv_PAT with | existT t v => v end, list_prod_sigT_value l0)
  end.

Definition proj_list_prod {A: Type} {F: A -> Type} (a: A) (l: list A) (v: list_prod (map F l)) (default: F a) (H: forall a b: A, {a = b} + {a <> b}) : F a.
Proof.
  induction l; [exact default |].
  destruct (H a a0).
  + subst a0.
    exact (fst v).
  + exact (IHl (snd v)).
Defined.

Definition upd_list_prod {A} {F} (l: list A) (v: list_prod (map F l)) (a: A) (v0: F a) (H: forall a b: A, {a = b} + {a <> b}) : list_prod (map F l).
Proof.
  induction l; [exact v |].
  destruct (H a a0).
  - subst.
    exact (v0, snd v).
  - exact (fst v, IHl (snd v)).
Defined.

Lemma list_prod_sigT_type_list_prod: forall {A: Type} (f: A -> sigT (fun x => x)) (l: list A),
  list_prod_sigT_type (map f l) = list_prod (map (fun i => let (t, _) := f i in t) l).
Proof.
  intros.
  induction l; auto.
  simpl.
  rewrite <- IHl.
  auto.
Defined.

Lemma list_prod_sigT_value_list_prod_gen: forall {A: Type} (f: A -> sigT (fun x => x)) (l: list A)
  (e : list_prod_sigT_type (map f l) = list_prod (map (fun i => let (t, _) := f i in t) l)),
   list_prod_sigT_value (map f l) =
   eq_rect_r (fun x : Type => x)
     (list_prod_gen
        (fun i => let (t, v) as tv return (let (t, _) := tv in t) := f i in v) l) e.
Proof.
  intros.
  induction l.
  + simpl in *.
    unfold eq_rect_r.
    rewrite <- Extensionality.EqdepTh.eq_rect_eq.
    auto.
  + simpl.
    set (vl1 := list_prod_sigT_value (map f l)) in IHl |- *.
    clearbody vl1.
    set (vl2 :=
           list_prod_gen
             (fun i : A =>
              let (t, v) as s return (let (t, _) := s in t) := f i in v) l) in IHl |- *.
    clearbody vl2.
    simpl in e, vl1, vl2.
    change (list_prod_sigT_type (f a :: map f l))
      with ((let (t, _) := f a in t) * list_prod_sigT_type (map f l))%type in *.
    pose proof list_prod_sigT_type_list_prod f l.
    revert vl1 vl2 e IHl.
    set (t1 := list_prod_sigT_type (map f l)) in *.
    set (t2 := list_prod (map (fun i : A => let (t, _) := f i in t) l)) in *.
    clearbody t1 t2.
    subst t2.
    intros.

    unfold eq_rect_r.
    rewrite <- Extensionality.EqdepTh.eq_rect_eq.
    rewrite IHl with eq_refl.
    auto.
Defined.

