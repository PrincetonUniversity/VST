Require Import VST.floyd.jmeq_lemmas.

Definition product_values_reflexivity :=
  VST.floyd.jmeq_lemmas.JMeq_pair nat nat bool bool 0 0 true true
    (VST.floyd.jmeq_lemmas.JMeq_refl _)
    (VST.floyd.jmeq_lemmas.JMeq_refl _).

(* A relation on types lives above the types in the preceding product. *)
Definition product_relations_reflexivity :=
  VST.floyd.jmeq_lemmas.JMeq_pair _ _ _ _
    (@VST.floyd.jmeq_lemmas.JMeq) (@VST.floyd.jmeq_lemmas.JMeq)
    (@VST.floyd.jmeq_lemmas.JMeq) (@VST.floyd.jmeq_lemmas.JMeq)
    (VST.floyd.jmeq_lemmas.JMeq_refl _)
    (VST.floyd.jmeq_lemmas.JMeq_refl _).

Polymorphic Definition product_distinct_levels@{lower higher + | lower < higher +}
    (A: Type@{lower}) (B: Type@{higher}) (a: A) (b: B) :=
  VST.floyd.jmeq_lemmas.JMeq_pair A A B B a a b b
    (VST.floyd.jmeq_lemmas.JMeq_refl _)
    (VST.floyd.jmeq_lemmas.JMeq_refl _).

Polymorphic Definition product_first_distinct_levels@{lower higher + | lower < higher +}
    (A: Type@{lower}) (B: Type@{higher}) (a: A) (b: B) :=
  VST.floyd.jmeq_lemmas.JMeq_fst A B A B (a, b) (a, b)
    eq_refl eq_refl (product_distinct_levels A B a b).

Polymorphic Definition product_second_distinct_levels@{lower higher + | lower < higher +}
    (A: Type@{lower}) (B: Type@{higher}) (a: A) (b: B) :=
  VST.floyd.jmeq_lemmas.JMeq_snd A B A B (a, b) (a, b)
    eq_refl eq_refl (product_distinct_levels A B a b).

Polymorphic Definition list_length_reflexivity@{element +}
    (A: Type@{element}) (values: list A) :=
  VST.floyd.jmeq_lemmas.list_func_JMeq values values
    (fun X (items: list X) => length items) eq_refl
    (VST.floyd.jmeq_lemmas.JMeq_refl _).

Polymorphic Definition list_element_reflexivity@{element +}
    (A: Type@{element}) (values: list A) (value: A) :=
  VST.floyd.jmeq_lemmas.list_func_JMeq' values values value value
    (fun X (_: list X) (item: X) => item)
    (VST.floyd.jmeq_lemmas.JMeq_refl _)
    (VST.floyd.jmeq_lemmas.JMeq_refl _).

Definition list_helper_reflexivity :=
  VST.floyd.jmeq_lemmas.JMeq_refl
    (@VST.floyd.jmeq_lemmas.list_func_JMeq).

Polymorphic Definition transport_reflexivity@{index value + | index < value +}
    (A: Type@{index}) (x y: A) (F: A -> Type@{value})
    (v: F x) (equality: x = y) :=
  VST.floyd.jmeq_lemmas.eq_rect_JMeq A x y F v equality.

Polymorphic Definition reverse_transport_reflexivity@{index value + | value < index +}
    (A: Type@{index}) (x y: A) (F: A -> Type@{value})
    (v: F x) (equality: y = x) :=
  VST.floyd.jmeq_lemmas.eq_rect_r_JMeq A x y F v equality.

Polymorphic Definition equality_elimination@{element predicate + | element < predicate +}
    (A: Type@{element}) (x y: A) (P: A -> Type@{predicate})
    (proof: P x) (equality: VST.floyd.jmeq_lemmas.JMeq x y) :=
  VST.floyd.jmeq_lemmas.JMeq_rect A x P proof y equality.

Polymorphic Lemma reflexivity_hint@{element +}
    (A: Type@{element}) (x: A): VST.floyd.jmeq_lemmas.JMeq x x.
Proof. auto. Qed.

Polymorphic Lemma symmetry_hint@{element +}
    (A: Type@{element}) (x y: A):
    VST.floyd.jmeq_lemmas.JMeq x y -> VST.floyd.jmeq_lemmas.JMeq y x.
Proof. auto. Qed.

Definition reflexivity_hint_on_relation :=
  reflexivity_hint _ (@VST.floyd.jmeq_lemmas.JMeq).

Definition symmetry_hint_on_relation :=
  symmetry_hint _ (@VST.floyd.jmeq_lemmas.JMeq)
    (@VST.floyd.jmeq_lemmas.JMeq).
