Load loadpath.
Require Import Coq.Lists.List Permutation veric.Coqlib2.
Require Import VST.msl.Axioms msl.sepalg VST.msl.predicates_sa msl.base
               veristar.variables veristar.datatypes
               veristar.clauses veristar.basic veristar.compare.

(* listd - interpretation functions folded over sequences *)

Section ListDenote.
Context {A T : Type}.
Variables (f : A -> T) (g : T -> T -> T) (b : T).

Fixpoint list_denote l : T :=
  match l with nil => b | x :: l' => g (f x) (list_denote l')
  end.

Local Notation "'listd'" := (list_denote).

Lemma listd_fold_right l :
  listd l = fold_right (fun x y  => g (f x) y) b l.
Proof. intros; induction l; simpl; intros; auto. Qed.

End ListDenote.

Notation "'listd'" := (list_denote).

Lemma listd_app {A T} f g (b : T) (l l' : list A) :
  listd f g b (l ++ l') =
  listd f g (listd f g b l') l.
Proof.
intros; do 3 rewrite listd_fold_right; apply fold_right_app.
Qed.

(* general listd lemmas *)

Section ListDenoteLems.
Context {A T : Type}.
Variables (f : A -> T) (g : T -> T -> T) (b : T).

Lemma listd_nil : listd f g b nil = b.
Proof. auto. Qed.

Lemma listd_cons a l :
  listd f g b (a :: l) = g (f a) (listd f g b l).
Proof. auto. Qed.

Lemma listd_map h l (Hgh_eq : forall a b', g (f (h a)) b' = g (f a) b') :
  listd f g b (map h l) = listd f g b l.
Proof with auto. induction l; simpl; intros... rewrite IHl, Hgh_eq... Qed.

Lemma listd_filter h l (H : forall a b', false=h a -> g (f a) b' = b') :
  listd f g b (filter h l) = listd f g b l.
Proof with auto.
induction l; simpl...
remember (h a) as b'; destruct b'; simpl. rewrite IHl... rewrite IHl, H...
Qed.

Lemma listd_flat_map h l (H : forall a b', g (f a) b' = listd f g b' (h a)) :
  listd f g b l = listd f g b (flat_map h l).
Proof with auto.
induction l; simpl... rewrite IHl, listd_app; apply H.
Qed.

Lemma listd_compose h1 h2 l
  (Hh1 : forall l, listd f g b l = listd f g b (h1 l))
  (Hh2 : forall l, listd f g b l = listd f g b (h2 l)) :
  listd f g b l = listd f g b ((h1 oo h2) l).
Proof. unfold compose; rewrite <- Hh1, Hh2; auto. Qed.

End ListDenoteLems.

(* listd lemmas that hold when g is symmetric and assoc. *)

Section ListDenoteAS.
Context {A T : Type}.
Variables (f : A -> T) (g : T -> T -> T) (b : T).
Variable (gS : forall x y, g x y = g y x).
Variable (gA : forall x y z, g x (g y z) = g (g x y) z).

Lemma fgAS b' (t t' : T) : g t (g t' b') = g t' (g t b').
Proof with auto. rewrite gA, gS; pattern (g t t'); rewrite gS, gS, gA... Qed.

Lemma listdAS a l : listd f g (g (f a) b) l = g (f a) (listd f g b l).
Proof with auto.
revert a; induction l; simpl; intro a'... rewrite IHl, fgAS...
Qed.

Lemma listd_AS_unit un l (un_unit : forall x, g x un = x) :
  listd f g b l = g b (listd f g un l).
Proof with auto. induction l; simpl... rewrite IHl, fgAS... Qed.

Lemma listd_perm l l' (Hperm : Permutation l l') :
  listd f g b l = listd f g b l'.
Proof with auto.
intros; induction Hperm; simpl... rewrite IHHperm...
do 2 rewrite gA; pattern (g (f y) (f x)); rewrite gS...
transitivity (listd f g b l')...
Qed.

End ListDenoteAS.

Section ListDenoteConj.
Context {A : Type}.
Variables (f : A -> Prop) (g : Prop -> Prop -> Prop) (b : Prop).
Variable (gconj : forall x y, g x y -> y).

Lemma listd_conj a l : listd f g b (a :: l) -> listd f g b l.
Proof. apply gconj. Qed.

Context {B : Type}.
Variables (h : A -> pred B) (k : pred B -> pred B -> pred B) (b0 : pred B).
Variable (hconj : forall x y b, k x y b -> y b).

Lemma listd_conjP a l : forall b, listd h k b0 (a :: l) b -> listd h k b0 l b.
Proof. apply hconj. Qed.

End ListDenoteConj.

(* specializations based on the return type of f *)

(* first, when f : A -> Prop *)

Section ListDenoteProp.
Context {A : Type}.
Variables (f : A -> Prop) (b : Prop).

Lemma andS (x y : Prop) : and x y = and y x.
Proof. apply prop_ext; intuition. Qed.

Lemma andA x y z : and x (and y z) = and (and x y) z.
Proof. apply prop_ext; intuition.  Qed.

Lemma orS (x y : Prop) : or x y = or y x.
Proof. apply prop_ext; apply or_comm. Qed.

Lemma orA x y z : or x (or y z) = or (or x y) z.
Proof. apply prop_ext; rewrite <- or_assoc; split; auto. Qed.

Lemma listd_conj_and a l : listd f and True (a :: l) -> listd f and True l.
Proof. apply listd_conj; auto. intros x y [hx hy]; auto. Qed.

Lemma listd_unfold_and l : listd f and b l = (listd f and True l /\ b).
Proof with auto.
induction l; simpl... apply prop_ext; split; tauto.
apply prop_ext; split; simpl; rewrite IHl; tauto.
Qed.

Lemma listd_unfold_or l : listd f or b l = (listd f or False l \/ b).
Proof with auto.
induction l; simpl... apply prop_ext; split; tauto.
apply prop_ext; split; simpl; rewrite IHl; tauto.
Qed.

Lemma listd_flat_map_and h l
  (H : forall a b', and (f a) b' -> listd f and b' (h a)) :
  listd f and b l -> listd f and b (flat_map h l).
Proof with auto.
induction l; simpl... intros [B C]. specialize (H a _ (conj B (IHl C))).
solve [rewrite listd_app; auto].
Qed.

Lemma listd_In_prop l : (forall a, In a l -> f a) -> listd f and True l.
Proof with simpl; try solve[exfalso; auto]; auto. induction l... Qed.

Lemma listd_In_inv_prop a l : listd f and True l -> In a l -> f a.
Proof with try solve[exfalso; auto]; auto.
revert a; induction l; simpl; intros a' C D...
destruct D as [D|D]; [rewrite <- D|].
solve [destruct C as [C1 C2]; auto]. solve[destruct C; apply IHl; auto].
Qed.

End ListDenoteProp.

Section ListDenoteProp1.
Context {A : Type}.
Variables (f : A -> Prop).

Lemma listd_unfold_app_and b l l' :
  listd f and b (l ++ l') = (listd f and True l /\ listd f and b l').
Proof with auto. rewrite listd_app, listd_unfold_and... Qed.

Lemma listd_unfold_app_or b l l' :
  listd f or b (l ++ l') = (listd f or False l \/ listd f or b l').
Proof with auto. rewrite listd_app, listd_unfold_or... Qed.

End ListDenoteProp1.

(* next - when f : A -> pred B *)

(*these two lemmas should go in predicates_tc, which should maybe be called
   just predicates*)
Lemma union_com {A} : forall (P Q: pred A), ((P || Q) = (Q || P))%pred.
Proof.
intros; extensionality w.
unfold orp; apply prop_ext; intuition.
Qed.

Lemma union_assoc {A} : forall (P Q R: pred A),
  ((P || Q) || R = P || (Q || R))%pred.
Proof.
intros; extensionality w.
unfold orp; apply prop_ext; intuition.
Qed.

Notation "'inter'" := (@andp _).
Notation "'un'" := (@orp _).

Section ListDenotePred.
Context {A B : Type}.
Variables (f : A -> pred B) (b : pred B).

Lemma listd_conj_inter a l :
  forall b', listd f inter TT (a :: l) b' -> listd f inter TT l b'.
Proof. intro b'; apply listd_conjP. intros x y b0 [H1 H2]; auto. Qed.

Lemma listd_unfold_inter l : listd f inter b l = (listd f inter TT l && b)%pred.
Proof with auto.
induction l; simpl... apply extensionality; intro x.
apply prop_ext; split; intro H. split... destruct H...
rewrite IHl, andp_assoc...
Qed.

Lemma listd_unfold_un l : listd f un b l = (listd f un FF l || b)%pred.
Proof with auto.
induction l; simpl... apply extensionality; intro x.
apply prop_ext; split; intro H. right... destruct H... inversion H.
rewrite IHl, union_assoc...
Qed.

Lemma listd_flat_map_inter h l s
  (H : forall a b', inter (f a) b' s -> listd f inter b' (h a) s) :
  listd f inter b l s -> listd f inter b (flat_map h l) s.
Proof with auto.
induction l; simpl... intros [C D].
solve[rewrite listd_app; apply H; split; auto].
Qed.

Lemma listd_In_pred l s :
  (forall a, In a l -> f a s) -> b s -> listd f inter b l s.
Proof with simpl; try solve[exfalso; auto]; auto.
induction l... intro C; split; [ solve [apply (C a); left; auto] | ].
apply IHl...
Qed.

Lemma listd_In_inv_pred a l s : listd f inter TT l s -> In a l -> f a s.
Proof with try solve[exfalso; auto]; auto.
revert a; induction l; simpl; intros a' C D...
destruct D as [D|D]; [rewrite <- D|].
solve [destruct C as [C1 C2]; auto]. solve[destruct C; apply IHl; auto].
Qed.

Lemma listd_In_pred_un l s :
  (exists a, In a l /\ f a s) \/ b s -> listd f un b l s.
Proof with simpl; try solve[exfalso; auto|congruence]; auto.
induction l... intros [[a [C D]]|E]... intros [[a0 [C D]]|E]...
destruct C; subst. left... right; apply IHl; eauto.
right; eapply IHl...
Qed.

Lemma listd_In_inv_pred_un l s :
  listd f un b l s -> (exists a, In a l /\ f a s) \/ b s.
Proof with try solve[exfalso; auto|congruence]; auto.
induction l... destruct 1. left; exists a; split; simpl...
spec IHl H. destruct IHl as [[a0 [C D]]|E].
left; exists a0; split; simpl... right...
Qed.

(* todo: add map/fold_right lems for prop, etc. *)

Lemma listd_map_pred {C : Type} h (g : C -> pred B) l s
  (H : forall a, f a s -> g (h a) s) :
  listd f inter TT l s -> listd g inter TT (map h l) s.
Proof with try solve [exfalso; auto]; auto.
induction l... simpl; intros [? ?]; split...
Qed.

Lemma listd_omapl_pred {C : Type} h (g : C -> pred B) l s
  (H : forall a, f a s -> match h a with Some a' => g a' s | None => True end) :
  listd f inter TT l s -> listd g inter TT (omapl h l) s.
Proof with simpl; try solve [exfalso; auto]; auto.
induction l... simpl; intros [? ?]. spec H a. destruct (h a)... split...
Qed.

Lemma listd_foldr_pred h c0 l s
  (H : forall a x, f a s -> f x s -> f (h a x) s) :
  f c0 s -> listd f inter TT l s -> f (fold_right h c0 l) s.
Proof with try solve [exfalso; auto]; auto.
revert c0 H; induction l... simpl; intros c0 H C [D E]. apply H...
Qed.

Lemma listd_foldl_pred h c0 l s
  (H : forall a x, f a s -> f x s -> f (h x a) s) :
  f c0 s -> listd f inter TT l s -> f (fold_left h l c0) s.
Proof with try solve [exfalso; auto]; auto.
revert c0 H; induction l... simpl; intros c0 H C [D E]; apply IHl...
Qed.

Lemma listd_filter_pred h l s :
  listd f inter TT l s -> listd f inter TT (filter h l) s.
Proof with try solve [exfalso; auto]; auto.
induction l... simpl. intros [H1 H2]. if_tac... simpl... split...
Qed.

Lemma listd_partition_pred h l xs ys s (H : partition h l = (xs, ys)) :
  listd f inter TT l s ->
    listd f inter TT xs s /\ listd f inter TT ys s.
Proof with try solve [exfalso; auto]; auto.
revert xs ys H; induction l... simpl. inversion 1; auto.
intros xs ys; simpl; intros H1 [H2 H3].
remember (partition h l) as c. destruct c. destruct (h a); inversion H1; subst.
spec IHl l0 ys. destruct IHl... split; auto. split; auto.
spec IHl xs l1. destruct IHl... split; auto. split; auto.
Qed.

End ListDenotePred.

Section ListDenotePred1.
Context {A B : Type}.
Variables (f : A -> pred B).

Lemma listd_unfold_app_inter b l l' :
  listd f inter b (l ++ l') = (listd f inter TT l && listd f inter b l')%pred.
Proof with auto. rewrite listd_app, listd_unfold_inter... Qed.

Lemma listd_unfold_app_un b l l' :
  listd f un b (l ++ l') = (listd f un FF l || listd f un b l')%pred.
Proof with auto. rewrite listd_app, listd_unfold_un... Qed.

End ListDenotePred1.

(* insert, insert_uniq, insertion sort *)

Section ListDenoteInsert.
Context {A T : Type}.
Variables (f : A -> T) (g : T -> T -> T) (b : T).
Variable (gS : forall x y, g x y = g y x).
Variable (gA : forall x y z, g x (g y z) = g (g x y) z).

Lemma listd_insert cmp a l :
  listd f g b (insert cmp a l) = g (f a) (listd f g b l).
Proof with auto.
rewrite listd_perm with (l' := (a :: l))... apply perm_insert.
Qed.

Lemma listd_sort cmp l : listd f g b (rsort cmp l) = listd f g b l.
Proof with auto.
(*could prove this w/ perm lemma on rsort*)
induction l... simpl. rewrite <- IHl. apply listd_insert.
Qed.

End ListDenoteInsert.

Section ListDenoteInsertUniq.
Context {A T : Type}.
Variables (f : A -> T) (g : T -> T -> T) (b : T).
Variable (gS : forall x y, g x y = g y x).
Variable (gA : forall x y z, g x (g y z) = g (g x y) z).
Variable (cmp : A -> A -> comparison).
Variable (Hcmp : forall x y, Eq = cmp x y ->
  forall b, g (f x) (g (f y) b) = g (f y) b).

Lemma listd_insert_uniq a l :
  listd f g b (insert_uniq cmp a l) = g (f a) (list_denote f g b l).
Proof with auto.
induction l; simpl...
remember (cmp a a0) as d; destruct d; simpl... rewrite Hcmp...
rewrite IHl... rewrite fgAS...
Qed.

Lemma listd_sort_uniq l : listd f g b (rsort_uniq cmp l) = listd f g b l.
Proof with auto.
induction l... simpl. rewrite <-IHl. rewrite listd_insert_uniq...
Qed.

End ListDenoteInsertUniq.

(* convenience lemmas specializing insert/insert_uniq/sort/sort_uniq to and/or/
   andp/orp *)

Section ListDenoteSortProp.
Context {A : Type}.
Variable (f : A -> Prop) (b : Prop).

Local Hint Resolve andS andA orS orA.

Lemma listd_insert_and cmp a l :
  listd f and b (insert cmp a l) = and (f a) (listd f and b l).
Proof. apply listd_insert; auto. Qed.

Lemma list_sort_and cmp l :
  listd f and b (rsort cmp l) = listd f and b l.
Proof. apply listd_sort; auto. Qed.

Lemma listd_insert_or cmp a l :
  listd f or b (insert cmp a l) = or (f a) (listd f or b l).
Proof. apply listd_insert; auto. Qed.

Lemma listd_sort_or cmp l :
  listd f or b (rsort cmp l) = listd f or b l.
Proof. apply listd_sort; auto. Qed.

End ListDenoteSortProp.

(* sort preds *)

Section ListDenoteInsertPred.

Context {A B : Type}.
Variable (f : A -> pred B) (b : pred B).

(* convenient in the proofs that follow *)
Lemma interS (x y : pred B) : inter x y = inter y x.
Proof. apply andp_comm. Qed.

Lemma interA (x y z : pred B) : inter x (inter y z) = inter (inter x y) z.
Proof. rewrite andp_assoc; auto. Qed.

Lemma unS (x y : pred B) : un x y = un y x.
Proof. apply union_com. Qed.

Lemma unA (x y z : pred B) : un x (un y z) = un (un x y) z.
Proof. rewrite union_assoc; auto. Qed.

Variables (JB: Join B) (PB: Perm_alg B)(SB: Sep_alg B).

Lemma sepconS (x y : pred B) : sepcon x y = sepcon y x.
Proof. apply sepcon_comm. Qed.

Lemma sepconA (x y z : pred B) :
  sepcon x (sepcon y z) = sepcon (sepcon x y) z.
Proof. rewrite sepcon_assoc; auto. Qed.

Local Hint Resolve interS interA unS unA sepconS sepconA.

Lemma listd_insert_inter cmp a l :
  listd f inter b (insert cmp a l) = inter (f a) (listd f inter b l).
Proof. apply listd_insert; auto. Qed.

Lemma listd_sort_inter cmp l :
  listd f inter b (rsort cmp l) = listd f inter b l.
Proof. apply listd_sort; auto. Qed.

Lemma listd_insert_un cmp a l :
  listd f un b (insert cmp a l) = un (f a) (listd f un b l).
Proof. apply listd_insert; auto. Qed.

Lemma listd_sort_un cmp l : listd f un b (rsort cmp l) = listd f un b l.
Proof. apply listd_sort; auto. Qed.

(* todo: add sortuniq lems for sepcon *)

Lemma listd_insert_sepcon cmp a l :
  listd f sepcon b (insert cmp a l) = sepcon (f a) (listd f sepcon b l).
Proof. apply listd_insert; auto. Qed.

Lemma listd_sort_sepcon cmp l :
  listd f sepcon b (rsort cmp l) = listd f sepcon b l.
Proof. apply listd_sort; auto. Qed.

End ListDenoteInsertPred.

(* insert/sort uniq *)

Section ListDenoteSortUniqProp.
Context {A : Type}.
Variables (f : A -> Prop) (b : Prop).
Variable (cmp : A -> A -> comparison).
Variable (Hcmp : forall x y, Eq = cmp x y -> x = y).

Local Hint Resolve andS andA orS orA.

Lemma listd_insert_uniq_and a l :
  listd f and b (insert_uniq cmp a l) = and (f a) (listd f and b l).
Proof.
apply listd_insert_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H); apply prop_ext; split; tauto.
Qed.

Lemma list_sort_uniq_and l :
  listd f and b (rsort_uniq cmp l) = listd f and b l.
Proof.
apply listd_sort_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H); apply prop_ext; split; tauto.
Qed.

Lemma listd_insert_uniq_or a l :
  listd f or b (insert_uniq cmp a l) = or (f a) (listd f or b l).
Proof.
apply listd_insert_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H); apply prop_ext; split; tauto.
Qed.

Lemma listd_sort_uniq_or l :
  listd f or b (rsort_uniq cmp l) = listd f or b l.
Proof.
apply listd_sort_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H); apply prop_ext; split; tauto.
Qed.

End ListDenoteSortUniqProp.

(* insert/sort uniq for preds *)

Section ListDenoteSortUniqPreds.
Context {A B : Type}.
Variables (f : A -> pred B) (b : pred B).
Variable (cmp : A -> A -> comparison).
Variable (Hcmp : forall x y, Eq = cmp x y -> x = y).

Local Hint Resolve (@interS B) (@interA B) (@unS B) (@unA B).

Lemma listd_insert_uniq_inter a l :
  listd f inter b (insert_uniq cmp a l) = inter (f a) (listd f inter b l).
Proof.
apply listd_insert_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H).
apply extensionality; intros ?; apply prop_ext; split;
  unfold andp; tauto.
Qed.

Lemma listd_sort_uniq_inter l :
  listd f inter b (rsort_uniq cmp l) = listd f inter b l.
Proof.
apply listd_sort_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H).
apply extensionality; intros ?; apply prop_ext; split;
  unfold andp; tauto.
Qed.

Lemma listd_insert_uniq_un a l :
  listd f un b (insert_uniq cmp a l) = un (f a) (listd f un b l).
Proof.
apply listd_insert_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H).
apply extensionality; intros ?; apply prop_ext; split; unfold orp; tauto.
Qed.

Lemma listd_sort_uniq_un l :
  listd f un b (rsort_uniq cmp l) = listd f un b l.
Proof.
apply listd_sort_uniq; auto.
intros x y H b'; rewrite (Hcmp _ _ H).
apply extensionality; intros ?; apply prop_ext; split; unfold orp; tauto.
Qed.

End ListDenoteSortUniqPreds.

Section ListDenoteMergePreds.
Context {A B : Type}.
Variables (f : A -> pred B) (b : pred B).
Variable (cmp : A -> A -> comparison).
Variable (Hcmp : forall x y, Eq = cmp x y -> x = y).

Lemma listd_merge_inter l1 l2 s :
  listd f inter TT l1 s -> listd f inter TT l2 s ->
  listd f inter TT (merge cmp l1 l2) s.
Proof with simpl; auto.
revert l2; induction l1... intros l2 _ H1.
assert (forall l, (fix merge_aux (l0 : list A) := l0) l = l)
  as -> by (destruct l; auto)...
intros l2 H1 H2. induction l2... remember (cmp a a0) as b0; destruct b0...
split; auto. rewrite (Hcmp a a0) in Heqb0; subst. destruct H1 as [H1 H3]...
destruct H1, H2... destruct H1, H2... destruct H2; split... destruct H1; split...
Qed.

Lemma merge_nil l : merge cmp l nil = l.
Proof. solve[induction l; simpl; auto]. Qed.

Lemma merge_nil' l : merge cmp nil l = l.
Proof. solve[induction l; simpl; auto]. Qed.

Lemma merge_cons_unfold a1 a2 l1 l2 :
  merge cmp (a1 :: l1) (a2 :: l2) = match cmp a1 a2 with
                                      | Eq => a1 :: merge cmp l1 l2
                                      | Gt => a1 :: merge cmp l1 (a2 :: l2)
                                      | Lt => a2 :: merge cmp (a1 :: l1) l2
                                    end.
Proof. simpl; remember (cmp a1 a2) as c; destruct c; auto. Qed.

Lemma merge_elems a l1 l2 : In a l1 \/ In a l2 <-> In a (merge cmp l1 l2).
Proof with try solve[simpl; auto].
split. intros [H1|H1].
(*-->*)
revert l1 H1; induction l2; induction l1... inversion 1.
intros H2; simpl in H2; destruct H2; subst.
rewrite merge_cons_unfold. remember (cmp a a0) as c; destruct c...
right. apply IHl2...
rewrite merge_cons_unfold. remember (cmp a1 a0) as c; destruct c...
right. apply IHl2. right...
(* In a l2 *)
revert l2 H1; induction l1; induction l2... inversion 1.
intros H2; simpl in H2; destruct H2; subst.
rewrite merge_cons_unfold. remember (cmp a0 a) as c; destruct c...
right. apply IHl1...
rewrite merge_cons_unfold. remember (cmp a0 a1) as c; destruct c...
right. apply IHl1. right...
(*<--*)
revert l1; induction l2; induction l1...
rewrite merge_cons_unfold. remember (cmp a1 a0) as c; destruct c...
simpl. destruct 1; subst... specialize (IHl2 _ H); firstorder.
intros H1. apply in_inv in H1. destruct H1; subst...
specialize (IHl2 _ H). destruct IHl2...
intros H1. apply in_inv in H1. destruct H1; subst...
specialize (IHl1 H). destruct IHl1...
Qed.

Lemma listd_merge_inter' l1 l2 s :
  listd f inter TT (merge cmp l1 l2) s ->
  listd f inter TT l1 s /\ listd f inter TT l2 s.
Proof with auto.
intros H1; split.
apply listd_In_pred. intros a H2.
apply (listd_In_inv_pred _ a) in H1...
rewrite <-merge_elems. left... auto.
apply listd_In_pred. intros a H2.
apply (listd_In_inv_pred _ a) in H1...
rewrite <-merge_elems. right... auto.
Qed.

Lemma listd_merge_un1 l1 l2 s :
  listd f un FF l1 s -> listd f un FF (merge cmp l1 l2) s.
Proof with simpl; auto.
revert l2; induction l1... intros l2; inversion 1. intros l2 H1.
induction l2... remember (cmp a a0) as b0; destruct b0...
apply (Hcmp a a0) in Heqb0; subst.
inversion H1; try solve[left; auto]. right...
right; apply IHl2... inversion H1; try solve[left; auto]. right; auto.
Qed.

Lemma listd_merge_un2 l1 l2 s :
  listd f un FF l2 s -> listd f un FF (merge cmp l1 l2) s.
Proof with simpl; auto.
revert l1; induction l2. intros ?; inversion 1. intros l1 H1.
induction l1; auto. simpl merge. simpl. remember (cmp a0 a) as b0; destruct b0...
apply (Hcmp a0 a) in Heqb0; subst.
inversion H1. left; auto. right; apply IHl2; auto.
inversion H1. left; auto.
spec IHl2 (a0 :: l1). simpl in IHl2. right; auto.
right; apply IHl1.
Qed.

Lemma listd_merge_un' l1 l2 s :
  listd f un FF (merge cmp l1 l2) s ->
  listd f un FF l1 s \/ listd f un FF l2 s.
Proof with auto.
intros H1.
cut (listd f un FF (l1 ++ l2) s).
  intros H2. rewrite listd_app, listd_unfold_un in H2.
  destruct H2; firstorder.
apply listd_In_inv_pred_un in H1. destruct H1 as [[a [C D]]|E].
apply listd_In_pred_un.
left. exists a. rewrite <-merge_elems in C. rewrite Coqlib.in_app. split...
inversion E.
Qed.

End ListDenoteMergePreds.

Section ListDenoteSeparate.
Context {X Y B : Type}.
Variables (f : X -> pred B) (g : Y -> pred B) (b : pred B) (l1 : list X)
          (l2 : list Y).

Lemma listd_separate :
  listd f inter (listd g inter b l2) l1 =
  andp (listd f inter TT l1) (andp (listd g inter TT l2) b).
Proof with auto.
rewrite listd_unfold_inter.
pattern (inter (listd g inter TT l2) b); rewrite <- listd_unfold_inter...
Qed.

Lemma listd_prop:
listd f inter b l1 =
(andp (listd f inter TT l1) b).
Proof.
induction l1; intros; simpl. rewrite TT_and. trivial.
apply extensionality. intros s.
apply prop_ext; split; simpl; intros.
  rewrite IHl in H.
  destruct H; destruct H0.
  split; trivial. split; trivial.

  rewrite IHl.
  destruct H. destruct H.
  split; trivial. split; trivial.
Qed.

End ListDenoteSeparate.

(* interpretation of clausesets *)

Section SetDenote.

Definition setd {T} (f : M.elt -> T) (g : T -> T -> T) (b : T) (s : M.t) :=
  listd f g b (M.elements s).

End SetDenote.

(* general lemmas about clausesets *)

Section SetLems.
Variables (s : M.t) (x y : clause).

Lemma setd_add_In_refl : M.In x (M.add x s).
Proof. rewrite M.add_spec.  auto.  Qed.

Lemma setd_add_In_refl_elems : In x (M.elements (M.add x s)).
Proof.
cut (M.In x (M.add x s)); [ | apply setd_add_In_refl; auto]; intro A.
rewrite <- M.elements_spec1, SetoidList.InA_alt in A; destruct A as [z [A B]].
subst; auto.
Qed.

Lemma setd_add_In : x = y \/ M.In y s -> M.In y (M.add x s).
Proof with auto.
rewrite M.add_spec; intuition.
Qed.

Lemma setd_add_In_inv : M.In y (M.add x s) -> x = y \/ M.In y s.
Proof with auto.
rewrite M.add_spec; intuition.
Qed.

Lemma elements_In {s0} : In y (M.elements s0) = M.In y s0.
Proof with auto.
apply prop_ext; split.
intro A. assert (B : exists z, OrderedClause.eq y z /\ In z (M.elements s0)).
  unfold OrderedClause.eq. eauto.
 rewrite <- SetoidList.InA_alt, M.elements_spec1 in B. auto.
rewrite <- M.elements_spec1, SetoidList.InA_alt; intros [z [A B]].
 subst; auto.
Qed.

Lemma empty_set_elems : M.elements M.empty = nil. (* !!! why not in stdlib *)
Proof with simpl; auto.
case_eq (M.elements M.empty); intros; auto.
destruct (M.elements_spec1 M.empty e) as [? _].
absurd (M.In e M.empty).
apply M.empty_spec.
apply H0.
rewrite H; constructor.
auto.
Qed.

Lemma setd_add_In_inv_elems :
  In y (M.elements (M.add x s)) -> x = y \/ M.In y s.
Proof with auto.
intro A; rewrite elements_In in A.
solve [apply setd_add_In_inv in A; exact A].
Qed.

Lemma setd_rem_In_inv : M.In y (M.remove x s) -> M.In y s.
Proof with auto. rewrite M.remove_spec; intros [A _]... Qed.

Lemma setd_rem_In_inv_elems :
  In y (M.elements (M.remove x s)) -> In y (M.elements s).
Proof.
intro A; rewrite elements_In in A.
solve [apply setd_rem_In_inv in A; rewrite <- elements_In in A; auto].
Qed.

End SetLems.

(* lemmas about interpreting clausesets *)

Section SetDenoteLems.
Context (B : Type). Variables (f : clause -> pred B) (b : pred B).
Variable (h : M.t -> clause -> M.t).
Variable (H : forall c cls s, setd f inter b cls s -> f c s ->
                              setd f inter b (h cls c) s).

Lemma setd_fold_left cls0 l s :
  listd f inter b l s -> setd f inter b cls0 s ->
  setd f inter b (fold_left h l cls0) s.
Proof with simpl; auto.
revert cls0; induction l... intros s0 [A C] D; apply IHl...
Qed.

Lemma setd_fold cls0 l s :
  setd f inter b l s -> setd f inter b cls0 s ->
  setd f inter b (M.fold (Basics.flip h) cls0 l) s.
Proof with simpl; auto.
rewrite M.fold_spec; intros; apply setd_fold_left; auto.
Qed.

Lemma setd_un cls1 cls2 s :
  setd f inter TT cls1 s -> setd f inter TT cls2 s ->
  setd f inter TT (M.union cls1 cls2) s.
Proof with auto.
intros H1 H2. unfold setd.
 apply listd_In_pred; [ | auto]; intros e H3.
assert (H4: M.In e cls1 \/ M.In e cls2) by
  (rewrite elements_In in H3; apply M.union_spec; auto).
do 2 rewrite <-elements_In in H4.
destruct H4 as [H4|H4];
[apply listd_In_inv_pred with (l := M.elements cls1)|
 apply listd_In_inv_pred with (l := M.elements cls2)]...
Qed.

Lemma setd_base_separate:
   forall {A} f (b: pred A) cls,
    setd f inter b cls = andp b (setd f inter (@TT A) cls).
Proof.
 intros. clear H.
 unfold setd in *.
 induction (M.elements cls); simpl.
 rewrite andp_TT. auto.
 rewrite IHl.
 rewrite <- andp_assoc. rewrite (andp_comm (f0 a)).
 rewrite andp_assoc; auto.
Qed.

Lemma setd_add c cls s :
  setd f inter b cls s -> f c s -> setd f inter b (M.add c cls) s.
Proof with auto.
intros A C.
 rewrite setd_base_separate.
 rewrite setd_base_separate in A.
 destruct A as [A' A]. split; auto.
 clear A'.
 apply listd_In_pred; [| auto].
 intros a D.
 generalize (setd_add_In_inv_elems cls _ _ D); intros [E | F].
rewrite <- E... rewrite <- M.elements_spec1, SetoidList.InA_alt in F.
destruct F as [y [F G]]; subst y.
solve [apply (listd_In_inv_pred f _ _ _ A G)].
Qed.

Lemma setd_remove c cls s :
  setd f inter TT cls s -> setd f inter TT (M.remove c cls) s.
Proof with auto.
intro A; apply listd_In_pred; [|auto]; intros a C.
apply listd_In_inv_pred with (l := M.elements cls)...
apply setd_rem_In_inv_elems with (x := c)...
Qed.

Lemma setd_empty_set s : setd f inter TT M.empty s.
Proof.
apply listd_In_pred; [|auto]; intros x A.
rewrite empty_set_elems in A; inversion A.
Qed.

Require Import MSetFacts Logic.

Lemma setd_filter bf cls s :
  setd f inter TT cls s -> setd f inter TT (M.filter bf cls) s.
Proof.
intros.
apply listd_In_pred; [|auto]. intros a H1. unfold setd in H0.
assert (H2: In a (M.elements cls)).
  rewrite elements_In, M.filter_spec in H1; auto.
  destruct H1 as [H1 _]. rewrite <-elements_In in H1; auto.
  unfold Proper, respectful. intros.
  subst x; auto.
apply (listd_In_inv_pred _ _ _ _ H0 H2).
Qed.

End SetDenoteLems.

Section FoldLem.
Context (B : Type). Variables (f : clause -> pred B) (b : pred B).
Variable (h : list clause -> clause -> list clause).

Lemma listd_fold_left cls0 l s
  (H : forall c cls, listd f inter b cls s -> f c s ->
                     listd f inter b (h cls c) s) :
  listd f inter b l s -> listd f inter b cls0 s ->
  listd f inter b (fold_left h l cls0) s.
Proof with simpl; auto.
revert cls0; induction l... intros s0 [A C] D; apply IHl...
Qed.

End FoldLem.

Section FoldLemWeak.
Context (B : Type). Variables (f : clause -> pred B) (b : pred B).
Variable (h : list clause -> clause -> list clause).
Variable (H : forall c cls s, listd f inter b cls s -> (forall s, f c s) ->
                              listd f inter b (h cls c) s).

Lemma listd_fold_left_wk cls0 l s :
  listd (fun c => forall s, f c s) and True l -> listd f inter b cls0 s ->
  listd f inter b (fold_left h l cls0) s.
Proof with simpl; auto.
revert cls0 s; induction l... intros s0 s H1.
assert (H2: forall s, f a s). intros s'. destruct H1 as [H1 H2]. spec H1 s'...
intros D; apply IHl... destruct H1...
Qed.

End FoldLemWeak.

Lemma listd_inter_map: forall {A B C} (l:list A) (f:B -> C -> Prop) h s,
(forall x, In x l -> f (h x) s) ->
inter
  (listd f inter TT (map h l)) TT s.
Proof.
intros A B C l.
induction l; intros; subst; simpl in *.
 split; trivial.
split; trivial.
  split. apply H. left. trivial.
  apply IHl. clear IHl. intros.
    apply H. right. assumption.
Qed.

Lemma listd_inter_rev: forall {A B} (f: A -> B -> Prop) l,
  listd f inter TT (rev  l) = listd f inter TT l.
Proof.
induction l; simpl; auto.
rewrite listd_app.
simpl.
rewrite <- IHl.
rewrite andp_TT.
rewrite andp_comm.
apply listd_unfold_inter.
Qed.

Lemma orp_FF {A} (p : pred A) : orp p FF = p.
Proof.
extensionality s. apply prop_ext. split; firstorder.
Qed.

Lemma listd_un_rev:
  forall {A B} (f: A -> B -> Prop) l, listd f un FF (rev  l) = listd f un FF l.
Proof.
induction l; simpl; auto.
rewrite listd_app; simpl; rewrite <-IHl, orp_FF.
generalize (listd_unfold_un f (f a) (rev l)). intros H1.
rewrite unS in H1; auto.
Qed.

Lemma setd_filter_pred:
  forall {B: Type} (f: M.elt -> pred B) (h: M.elt -> bool) (s: M.t),
     setd f inter TT s |-- setd f inter TT (M.filter h s).
Proof.
intros.
intros st ?.
unfold setd in *.
apply listd_In_pred; intros; auto.
eapply listd_In_inv_pred; eauto.
rewrite Melements_spec1 in *.
rewrite M.filter_spec in H0; intuition.
Qed.




