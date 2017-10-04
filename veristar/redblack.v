(* Implementation and proof of Red-Black Trees,
  matching the Coq Library MSets interface.
  Author:  Andrew W. Appel, 2011.

The design decisions behind this implementation are described here:
Efficient Verified Red-Black Trees, by Andrew W. Appel, September 2011.
http://www.cs.princeton.edu/~appel/papers/redblack.pdf

Additional suggested reading:
Red-Black Trees in a Functional Setting by Chris Okasaki.
Journal of Functional Programming, 9(4):471-477, July 1999.
http://www.eecs.usma.edu/webs/people/okasaki/jfp99redblack.pdf

Red-black trees with types, by Stefan Kahrs.
 Journal of Functional Programming, 11(4), 425-432, 2001.

Functors for Proofs and Programs, by J.-C. Filliatre and P. Letouzey.
ESOP'04: European Symposium on Programming, pp. 370-384, 2004.
http://www.lri.fr/~filliatr/ftp/publis/fpp.ps.gz

*)
Require MSets.
Require Coq.Structures.Orders.
Require Coq.Structures.OrdersFacts.
Require Import Morphisms.
Require Import ProofIrrelevance.
Require Import Sorted.
Require Import SetoidList.
Require Import NArith Lists.List.
Import Pnat.
Require Omega.

Module Type MSetPlus.
 Include MSetInterface.S.
 Parameter delete_min : t -> option (elt * t).
 Axiom delete_min_spec1: forall (s: t) k s',
    delete_min s = Some (k,s') <->
    (min_elt s = Some k /\ remove k s = s').
 Axiom delete_min_spec2: forall s, delete_min s = None <-> Empty s.

 Parameter mem_add: elt -> t -> option t.
 Axiom mem_add_spec:
    forall x s, mem_add x s = if mem x s then None else Some (add x s).

End MSetPlus.

Module Make (K: Orders.OrderedType) : MSetPlus with Module E:=K.
Module OTT := OrdersFacts.OrderedTypeTest K.
Import OTT MO.

Local Notation "'key'" := K.t.

 Module E := K.

 Inductive color := Red | Black.
 Inductive tree  : Type :=
 | EE : tree
 | T: color -> tree -> key -> tree -> tree.

 Fixpoint member (x: key) (t : tree) : bool :=
  match t with
  | EE => false
  | T _ tl k tr => match K.compare x k with
                          | Lt => member x tl
                          | Eq => true
                          | Gt => member x tr
                          end
  end.

Definition balance color t1 k t2 :=
 match color with Red => T Red t1 k t2
 | _ =>
 match t1, t2 with
 | T Red (T Red a x b) y c, d => T Red (T Black a x b) y (T Black c k d)
 | T Red a x (T Red b y c), d => T Red (T Black a x b) y (T Black c k d)
 | a, T Red (T Red b y c) z d => T Red (T Black a k b) y (T Black c z d)
 | a, T Red b y (T Red c z d) => T Red (T Black a k b) y (T Black c z d)
 | _, _ => T Black t1 k t2
  end
 end.

Fixpoint ins x s :=
 match s with
 | EE => T Red EE x EE
 | T c a y b => match K.compare x y with
                       | Lt => balance c (ins x a) y b
                       | Eq => T c a x b
                       | Gt => balance c a y (ins x b)
                       end
 end.

Definition makeBlack t :=
  match t with
  | EE => EE
  | T _ a x b => T Black a x b
  end.

Definition insert x s := makeBlack (ins x s).

Fixpoint ins' x s :=
 match s with
 | EE => Some (T Red EE x EE)
 | T c a y b => match K.compare x y with
                       | Lt => match ins' x a with
                                   | None => None
                                   | Some s' => Some (balance c s' y b)
                                   end
                       | Eq => None
                       | Gt => match ins' x b with
                                   | None => None
                                   | Some s' => Some (balance c a y s')
                                   end
                       end
 end.

Definition mem_add' x s :=
    match ins' x s with
    | None => None
    | Some s' => Some (makeBlack s')
    end.

(* The next several definitions are to handle deletion, which is quite complex! *)

Definition balance' tl k tr :=
    match tl , tr with
    | T Red (T Red a x b) y c, d => T Red (T Black a x b) y (T Black c k d)
    | T Red a x (T Red b y c), d => T Red (T Black a x b) y (T Black c k d)
    | a, T Red b y (T Red c z d) => T Red (T Black a k b) y (T Black c z d)
    | a, T Red (T Red b y c) z d => T Red (T Black a k b) y (T Black c z d)
    | _ , _ => T Black tl k tr
    end.

Definition sub1 t :=
  match t with
  | EE => EE
  | T _ a x b => T Red a x b
  end.

Definition balleft tl k tr :=
  match tl with
  | T Red a x b => T Red (T Black a x b) k tr
  | _ => match tr with
             | T Black a y b => balance' tl k (T Red a y b)
             | T Red (T Black a y b) z c => T Red (T Black tl k a) y (balance' b z (sub1 c))
             | _ => T Red tl k tr (* impossible *)
            end
  end.

Definition balright tl k tr :=
  match tr with
  | T Red b y c => T Red tl k (T Black b y c)
  | _ => match tl with
             | T Black a x b => balance' (T Red a x b) k tr
             | T Red a x (T Black b y c) => T Red (balance' (sub1 a) x b) y (T Black c k tr)
             | _ => T Red tl k tr (* impossible *)
            end
  end.

Fixpoint size t := match t with EE => 0 | T _ tl _ tr => 1 + size tl + size tr end.

Require Recdef Omega.

Function append (tlr: tree*tree) {measure (fun tlr => size (fst tlr) + size (snd tlr)) tlr} : tree :=
 match tlr with
 | (EE, x) => x
 | (x, EE) => x
 | (T Red a x b, T Red c y d) =>
   match append (b,c) with
   | T Red b' z c' => T Red (T Red a x b') z (T Red c' y d)
   | bc => T Red a x (T Red bc y d)
   end
 | (T Black a x b, T Black c y d) =>
   match append (b,c) with
   | T Red b' z c' => T Red (T Black a x b') z (T Black c' y d)
   | bc => balleft a x (T Black bc y d)
   end
 | (a, T Red b x c) => T Red (append(a,b)) x c
 | (T Red a x b, c) => T Red a x (append(b,c))
 end.
Proof.
intros; subst; simpl; omega.
intros; subst; simpl; omega.
intros; subst; simpl; omega.
intros; subst; simpl; omega.
Defined.

Fixpoint del x t :=
 match t with
 | EE => EE
 | T _ a y b =>
   match K.compare x y with
   | Lt => match a with
               | T Black _ _ _ => balleft (del x a) y b
               | _ => T Red (del x a) y b
               end
   | Gt => match b with
               | T Black _ _ _ => balright a y (del x b)
               | _ => T Red a y (del x b)
               end
   | Eq => append(a,b)
   end
  end.

Definition delete x t :=
   match del x t with
   | T _ a y b => T Black a y b
   | EE => EE
   end.


Fixpoint choose' (t : tree) : option key :=
  match t with
  | EE => None
  | T _ EE k tr => Some k
  | T _ tl k tr => choose' tl
  end.

Fixpoint max_elt' (t : tree) : option key :=
  match t with
  | EE => None
  | T _ tl k EE => Some k
  | T _ tl k tr => max_elt' tr
  end.


Fixpoint delmin a y b : (key * tree) :=
   match a with
   | EE => (y,b)
   | T Black aa ya ba =>
              match delmin aa ya ba with
                                 (k, a') => (k,balleft a' y b)
              end
   | T Red aa ya ba =>
              match delmin aa ya ba with
               (k,a') =>  (k, T Red a' y b)
              end
 end.

Definition delete'_min t : option (key * tree) :=
 match t with
 | EE => None
 | T _ a y b =>
  match delmin a y b with
   | (k, T _ a y b) => Some (k, T Black a y b)
   | (k, EE) => Some (k,EE)
   end
 end.


Definition bogus : tree * list key := (EE, nil).

Fixpoint treeify_f (n: positive) (l: list key) : tree * list key:=
 match n with
 | xH => match l with x::l1 => (T Red EE x EE, l1) | _ => bogus end
 | xO n' => match treeify_f n' l with
                   | (t1, x::l2) => let (t2,l3) := treeify_g n' l2 in (T Black t1 x t2, l3)
                   | _ => bogus
                  end
 | xI n' => match treeify_f n' l with
                   | (t1, x::l2) => let (t2,l3) := treeify_f n' l2 in (T Black t1 x t2, l3)
                   | _ => bogus
                  end
 end
 with treeify_g (n: positive) (l: list key) : tree * list key :=
 match n with
 | xH => (EE,l)
 | xO n' => match treeify_g n' l with
                   | (t1, x::l2) => let (t2,l3) := treeify_g n' l2 in (T Black t1 x t2, l3)
                   | _ => bogus
                  end
 | xI n' => match treeify_f n' l with
                   | (t1, x::l2) => let (t2,l3) := treeify_g n' l2 in (T Black t1 x t2, l3)
                   | _ => bogus
                  end
 end.


Fixpoint poslength {A} (l: list A) :=
 match l with nil => 1%positive | _::tl => Psucc (poslength tl) end.

Definition treeify (l: list key) : tree := fst (treeify_g (poslength l) l).

(* Now that the program has been defined, it's time to prove its properties.
   A red-black tree has two kinds of properties:
  [searchtree]: the keys in each left subtree are all less than the node's key,
                      and the keys in each right subtree are greater
  [redblack]:  there is the same number of black nodes on any path from
               the root to each leaf; and there are never two red nodes in a row.
  First, we'll treat the [searchtree] property.
*)

Ltac inv H := inversion H; clear H; subst.

Hint Immediate eq_sym.

Ltac do_compare x y :=  destruct (CompSpec2Type (K.compare_spec x y)).

Ltac do_ins_not_EE :=
  repeat match goal with
    | |- match ?A with Red => _ | Black => _ end  <> _=> destruct A
    | |- match ?A with EE => _ | T _ _ _ _ => _ end  <> _=>destruct A
  end; intro Hx; inversion Hx.

Lemma ins_not_EE: forall x s, ins x s <> EE.
Proof.
intros. induction s; simpl. intro Hx; inversion Hx.
do_compare x t.
congruence.
destruct c; simpl; repeat do_ins_not_EE.
destruct c; simpl; repeat do_ins_not_EE.
Qed.

Definition ltopt (x y : option key) :=
  match x, y with
  | Some x', Some y' => K.lt x' y'
  | _, _ => True
  end.

Inductive searchtree: option key -> option key -> tree -> Prop :=
 | STE: forall lo hi, ltopt lo hi -> searchtree lo hi EE
 | STT: forall c tl k tr lo hi,
                searchtree lo (Some k)  tl ->
                searchtree (Some k) hi tr ->
                searchtree lo hi (T c tl k tr) .

Ltac do_searchtree :=
  assumption ||
  constructor ||
  match goal with
  |  |- searchtree _ _ (match ?C with Red => _ | Black => _ end) => destruct C
  |  |- searchtree _ _ (match ?C with EE => _ | T _ _ _ _ => _ end) => destruct C
  | H: searchtree _ _ EE |- _ => inv H
  | H: searchtree _ _ (T _ _ _ _) |- _ => inv H
  | |- ltopt _ _ => unfold ltopt in *; auto
  | |- match ?A with Some _ => _ | None => _ end => destruct A
  | H: K.lt ?A ?B  |- K.lt ?A ?C  =>
           try solve [apply lt_trans with B; assumption]; clear H
  end.

Lemma searchtree_balance:
 forall c  s1 t s2 lo hi,
   ltopt lo (Some t) -> ltopt (Some t) hi ->
   searchtree lo (Some t)  s1-> searchtree (Some t) hi s2 ->
    searchtree lo hi (balance c s1 t s2).
Proof.
intros.
unfold balance.
repeat do_searchtree.
Qed.

Definition eqopt (a b : option key) :=
 match a, b with
 | Some x, Some y => K.eq x y
 | _ , _ => False
 end.

Lemma searchtree_expand_left:
  forall k t lo hi, searchtree (Some k) hi t ->
     (eqopt lo (Some k) \/ ltopt lo (Some k)) -> searchtree lo hi t.
Proof.
induction t; intros.
constructor.
inv H.
destruct H0; destruct lo, hi; simpl in *; auto. rewrite H; auto.
apply lt_trans with k; auto.
destruct H0.
inv H. constructor; auto.
inv H. constructor; auto.
Qed.

Lemma searchtree_expand_right:
  forall k t lo hi, searchtree lo (Some k) t ->
        (eqopt (Some k) hi \/ ltopt (Some k) hi) -> searchtree lo hi t.
Proof.
induction t; intros.
constructor.
inv H.
destruct H0; destruct lo, hi; simpl in *; auto. rewrite H in H1; auto.
apply lt_trans with k; auto.
destruct H0.
inv H. constructor; auto.
inv H. constructor; auto.
Qed.


Lemma searchtree_None:
  forall s lo hi, searchtree lo hi s -> searchtree None None s.
Proof.
  intros.
   destruct hi.
   apply searchtree_expand_right with t; simpl in *; auto.
   destruct lo; auto.
   apply searchtree_expand_left with t0; simpl in *; auto.
   destruct lo; auto.
   apply searchtree_expand_left with t; simpl in *; auto.
Qed.

Lemma searchtree_mid_congr:
     forall c c' s1 x y s2 lo hi,
        searchtree lo hi (T c s1 x s2) -> K.eq x y -> searchtree lo hi (T c' s1 y s2).
Proof.
intros.
inv H; constructor; auto.
eapply searchtree_expand_right; eauto.
eapply searchtree_expand_left; eauto.
simpl; auto.
Qed.

Lemma searchtree_proper_bounds: forall lo hi t, searchtree lo hi t -> ltopt lo hi.
Proof.
 induction 1; auto.
 destruct lo; simpl in *; auto. destruct hi; simpl in *; auto. apply lt_trans with k; auto.
Qed.

Lemma ins_is_searchtree:
   forall x s lo hi, ltopt lo (Some x) -> ltopt (Some x) hi ->
                    searchtree lo hi s ->
                    searchtree lo hi (ins x s).
Proof.
induction s; simpl; intros.
repeat constructor; auto.
do_compare x t; auto.
eapply searchtree_mid_congr; eauto.
inv H1.
apply searchtree_balance; auto; eapply searchtree_proper_bounds; eauto.
inv H1.
apply searchtree_balance; auto; eapply searchtree_proper_bounds; eauto.
Qed.

Lemma insert_searchtree: forall x s,
    searchtree None None s -> searchtree None None (insert x s).
Proof.
unfold insert; intros.
apply (ins_is_searchtree x) in H; simpl; auto.
destruct (ins x s); simpl in *; auto.
inv H. constructor; auto.
Qed.

Inductive interp: tree -> (key -> Prop) :=
| member_here: forall x y c tl tr, K.eq x y -> interp (T c tl y tr) x
| member_left: forall x y c tl tr, interp tl x -> interp (T c tl y tr) x
| member_right: forall x y c tl tr, interp tr x -> interp (T c tl y tr) x.

Lemma interp_empty: forall x, ~ interp EE x.
Proof.
intros; intro H; inv H.
Qed.

Hint Constructors interp.

Lemma generalize_bounds:
   forall t, searchtree None None t -> exists lo, exists hi, searchtree lo hi t.
Proof.
intros; eauto.
Qed.


Lemma interp_range:
  forall x tr lo hi, searchtree lo hi tr -> interp tr x -> ltopt lo (Some x) /\ ltopt (Some x) hi.
Proof.
induction 1; intros.
inv H0.
inv H1.
split.
 destruct lo; simpl; auto. rewrite H7; apply searchtree_proper_bounds in H; auto.
 destruct hi; simpl; auto. rewrite H7; apply searchtree_proper_bounds in H0; auto.
destruct (IHsearchtree1 H7); split; auto.
destruct hi; simpl; auto.  apply lt_trans with k; auto.
apply searchtree_proper_bounds in H0; auto.
destruct (IHsearchtree2 H7); split; auto.
destruct lo; simpl; auto.
apply lt_trans with k; eauto.
apply searchtree_proper_bounds in H; auto.
Qed.

Ltac etac :=
  match goal with
  | H: interp EE _ |- _ => inv H
  | H: InA _ _ nil |- _ => inv H
  | H: false = true |- _ => inv H
  | H: true = false |- _ => inv H
  | _ => auto
  end.

Lemma interp_member:
    forall x t,
      searchtree None None t ->
      (member x t = true <-> interp t x).
Proof.
intros.
case_eq (member x t); intuition.
clear - H0; induction t; simpl in *. inv H0.
do_compare x t2; [constructor 1 | constructor 2 | constructor 3]; auto.
inv H1.
elimtype False; revert H0 H1; induction H; intros; simpl in *.
inv H1.
inv H2.
rewrite H8 in H1; rewrite compare_refl in H1; inv H1.
destruct (interp_range _ _ _ _ H H8).
simpl in H3; rewrite <- compare_lt_iff in H3; rewrite H3 in H1; auto.
destruct (interp_range _ _ _ _ H0 H8).
simpl in H2; rewrite <- compare_gt_iff in H2; rewrite H2 in H1; auto.
Qed.

Lemma interp_makeBlack:
  forall t x, interp t x <-> interp (makeBlack t) x.
Proof.
destruct t; simpl; intuition;
(inv H;  [ constructor; auto | constructor 2; auto | constructor 3; auto]).
Qed.

Ltac do_interp_balance :=
 match goal with
 | |- interp (match ?A with Red => _ | Black => _ end) _  => destruct A
 | |- interp (match ?A with EE => _ | T _ _ _ _ => _ end) _ => destruct A
 |  H: interp (T _ _ _ _) _ |- _ => inv H
 | H: interp (match ?A with Red => _ | Black => _ end) _ |- _ => destruct A
 | H: interp (match ?A with EE => _ | T _ _ _ _ => _ end) _ |- _ => destruct A
 end; auto.

Lemma interp_balance:
  forall c tl k tr y, interp (balance c tl k tr) y <-> interp (T c tl k tr) y.
Proof.
destruct c, tl, tr; unfold balance;  intuition; repeat do_interp_balance.
Qed.

Lemma ins_ok:
   forall x y t lo hi,
             searchtree lo hi t ->
             ((K.eq x y \/ interp t x) <-> interp (ins y t) x).
Proof.
 induction 1; simpl; intuition;
  [inv H0; auto | ..];
  try solve [do_compare y k; auto; apply interp_balance; auto].
  do_compare y k; auto.
 inv H8; auto. constructor 1; auto. apply eq_trans with k; auto.
  apply interp_balance; auto.
  inv H8; auto.
 apply interp_balance; auto.
  inv H8; auto.
  do_compare y k; auto.
 inv H3; auto.
 apply interp_balance in H3.
  inv H3; auto.
 apply H2 in H13.
 destruct H13; auto.
 apply interp_balance in H3. inv H3; auto.
 apply H4 in H13.
 destruct H13; auto.
Qed.

Lemma interp_insert:
      forall x y s,
             searchtree None None s ->
             ((K.eq x y \/ interp s x) <-> interp (insert y s) x).
Proof.
  unfold insert; intros.
  destruct (ins_ok x y s None None H).
  intuition; try apply -> interp_makeBlack; auto.
  apply <- interp_makeBlack in H0; auto.
Qed.

 Inductive is_redblack : tree -> color -> nat -> Prop :=
 | IsRB_leaf: forall c, is_redblack EE c 0
 | IsRB_r: forall tl k tr n,
          is_redblack tl Red n ->
          is_redblack tr Red n ->
          is_redblack (T Red tl k tr) Black n
 | IsRB_b: forall c tl k tr n,
          is_redblack tl Black n ->
          is_redblack tr Black n ->
          is_redblack (T Black tl k tr) c (S n).

Lemma is_redblack_toblack:
 forall s n, is_redblack s Red n -> is_redblack s Black n.
Proof.
intros; inversion H; clear H; subst; try constructor; auto.
Qed.
Hint Resolve is_redblack_toblack.

Lemma is_redblack_Black_to_Red:
  forall s n, is_redblack s Black n ->
            exists n, is_redblack (makeBlack s) Red n.
Proof.
intros.
inv H; repeat econstructor; eauto.
Qed.

Inductive infrared : tree -> nat -> Prop :=
 (* This predicate expresses, "the tree is a red-black tree, except that
  it is permitted to have two red nodes in a row at the very root (only)."  *)
| infrared_e: infrared EE 0
| infrared_r: forall tl k tr n,
         is_redblack tl Black n ->
         is_redblack tr Black n ->
         infrared (T Red tl k tr) n
| infrared_b: forall tl k tr n,
         is_redblack tl Black n ->
         is_redblack tr Black n ->
         infrared (T Black tl k tr) (S n).

Ltac infrared_tac :=
repeat (
auto ||
constructor ||
match goal with
 | |- infrared (match ?A with
                                  | EE => _
                                  | T _ _ _ _ => _
                                  end)  _ =>
        match goal with
        | H: is_redblack A _ _ |- _ => inv H
         | H: infrared A _ |- _ => inv H
        end
 | |- is_redblack (match ?A with
                                  | EE => _
                                  | T _ _ _ _ => _
                                  end)  _ _ =>
        match goal with
        | H: is_redblack A _ _ |- _ => inv H
         | H: infrared A _ |- _ => inv H
        end
 | |- infrared (match K.compare ?A ?B with Eq => _ | Lt => _ | Gt => _ end)  _ =>
                     do_compare A B
 | |- is_redblack (match K.compare ?A ?B with Eq => _ | Lt => _ | Gt => _ end)  _ _ =>
                     do_compare A B
  end).

Lemma ins_is_redblack:
  forall x s n,
    (is_redblack s Black n -> infrared (ins x s) n) /\
    (is_redblack s Red n -> is_redblack (ins x s) Black n).
(* This one is tedious with proof automation,
   but extremely tedious without proof automation *)
Proof.
induction s; simpl; split; intros; inversion H; clear H; subst.
repeat (constructor; auto).
repeat (constructor; auto).
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H2 H6).
specialize (H0 H5).
clear H H1.
do_compare x t; constructor; auto.
rename n0 into n.
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H H6); specialize (H1 H7).
clear H0 H2.
simpl.
infrared_tac.
rename n0 into n.
destruct (IHs1 n); clear IHs1.
destruct (IHs2 n); clear IHs2.
specialize (H H6).
specialize (H1 H7).
clear H0 H2.
simpl; infrared_tac.
Qed.

Lemma insert_is_redblack:
  forall x s n, is_redblack s Red n ->
                    exists n', is_redblack (insert x s) Red n'.
Proof.
intros.
unfold insert.
destruct (ins_is_redblack x s n).
apply is_redblack_Black_to_Red with n; auto.
Qed.


Definition valid (x: tree) := searchtree None None x /\
                                  (exists n, is_redblack x Red n).

(*  NOW FOR THE HARD PART, DELETION!
   Here we follow the deletion algorithm of Stefan Kahrs (2001),
  and in particular,
  http://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs
*)

Ltac hax :=
  repeat (auto; try solve [repeat constructor; auto];
             match goal with
             | H: is_redblack _ Red _ |- _ => inv H
              | H: is_redblack _ _ 0 |- _ => inv H
             | H: is_redblack _ _ (S _) |- _ => inv H
             | H: infrared _ 0 |- _ => inv H
             | H: infrared _ (S _) |- _ => inv H
             end).

Lemma balance'_shape:
   forall n tl k tr,
     (is_redblack tl Black n /\ infrared tr n \/ infrared tl n /\ is_redblack tr Black n) ->
     is_redblack (balance' tl k tr) Black (S n).
Proof.
induction n; intros; hax.
destruct H as [[? ?] | [? ?]]; hax.
destruct H as [[? ?] | [? ?]]; hax.
Qed.

Lemma searchtree_balance':
 forall s1 t s2 lo hi,
   searchtree lo (Some t) s1 -> searchtree (Some t) hi s2 ->
    searchtree lo hi (balance' s1 t s2).
Proof.
intros.
unfold balance'.
repeat do_searchtree.
Qed.

Lemma searchtree_append_aux:
  forall n tl tr, size tl + size tr < n ->
             forall lo k hi,
               searchtree lo (Some k) tl -> searchtree (Some k) hi tr ->
               searchtree lo hi (append(tl,tr)).
Proof.
induction n; intros.
destruct tl; destruct tr; elimtype False; omega.
rewrite append_equation.
inv H0.
eapply searchtree_expand_left; eauto.
destruct c.
assert (searchtree (Some k0) hi (append(tr0,tr))).
apply IHn with k; auto.
simpl in H; omega.
inv H1.
constructor; auto.
rewrite append_equation in H0.
destruct tr0; try destruct c; auto.
destruct c.
assert (searchtree (Some k0) (Some k1) (append(tr0,tl))).
apply IHn with k; auto.
simpl in H; omega.
inv H1.
repeat constructor; auto.
destruct c; repeat constructor; auto.
constructor; auto.
inv H1.
repeat constructor; auto.
eapply searchtree_expand_right; eauto.
destruct c.
repeat constructor; auto.
apply IHn with k; auto.
simpl in H|-*; omega.
repeat constructor; auto.
assert (searchtree (Some k0) (Some k1) (append(tr0,tl))).
apply IHn with k; auto.
simpl in H|-*; omega.
inv H1.
unfold balleft.
inv H2.
apply searchtree_balance'; auto.
repeat constructor; auto.
repeat constructor; auto.
destruct c.
repeat constructor; auto.
apply searchtree_balance'; auto.
repeat constructor; auto.
repeat constructor; auto.
destruct c.
repeat constructor; auto.
unfold balleft.
inv H2.
apply searchtree_balance'; auto.
constructor; auto.
repeat constructor; auto.
destruct c.
repeat constructor; auto.
apply searchtree_balance'; auto.
repeat constructor; auto.
repeat constructor; auto.
Qed.

Lemma searchtree_append:
    forall tl tr lo k hi,
               searchtree lo (Some k) tl -> searchtree (Some k) hi tr->
               searchtree lo hi (append(tl,tr)).
Proof.
intros.
apply searchtree_append_aux with (S (size tl + size tr)) k; auto.
Qed.

Lemma searchtree_sub1: forall t lo hi, searchtree lo hi t -> searchtree lo hi (sub1 t).
Proof.
destruct t; intros; inv H; repeat constructor; auto.
Qed.

Lemma del_is_searchtree:
  forall x t lo hi,
     searchtree lo hi t -> searchtree lo hi (del x t).
Proof.
induction 1; simpl; intros.
constructor; auto.
do_compare x k.
(* Case 1 *)
apply searchtree_append with k; auto.
(* Case 2*)
inv H.
constructor; auto.
destruct c0.
constructor; auto.
remember (del x (T Black tl0 k0 tr0)) as t.
clear - H1 H2 H0 IHsearchtree1.
unfold balleft.
inv IHsearchtree1.
inv H0.
hax.
destruct c.
inv H3.
hax.
destruct c.
hax.
repeat constructor; auto.
apply searchtree_balance'; auto.
apply searchtree_sub1; auto.
apply searchtree_balance'; auto.
constructor; auto.
repeat constructor; auto.
destruct c.
repeat constructor; auto.
inv H0.
hax.
destruct c.
inv H4.
hax.
destruct c.
hax.
repeat constructor; auto.
apply searchtree_balance'; auto.
apply searchtree_sub1; auto.
apply searchtree_balance'; auto.
repeat constructor; auto.
repeat constructor; auto.
(* Case 3 *)
inv H0.
constructor; auto.
destruct c0.
constructor; auto.
remember (del x (T Black tl0 k0 tr0)) as t.
clear - H1 H2 H IHsearchtree2.
rename H into H0.
unfold balright.
inv IHsearchtree2.
inv H0.
hax.
destruct c.
inv H4.
hax.
destruct c.
hax.
repeat constructor; auto.
apply searchtree_balance'; auto.
apply searchtree_sub1; auto.
apply searchtree_balance'; auto.
repeat constructor; auto.
constructor; auto.
destruct c.
repeat constructor; auto.
inv H0.
hax.
destruct c.
inv H5.
hax.
destruct c.
hax.
repeat constructor; auto.
apply searchtree_balance'; auto.
apply searchtree_sub1; auto.
apply searchtree_balance'; auto.
repeat constructor; auto.
repeat constructor; auto.
Qed.

Definition is_red_or_empty t :=
  match t with T Black _ _ _ => False | _ => True end.

Definition is_black t :=
  match t with T Black _ _ _ => True | _ => False end.

Lemma append_shape_aux:
  forall sz tl tr, size tl + size tr < sz ->
           (forall n, is_redblack tl Black n -> is_redblack tr Black n -> infrared (append (tl,tr)) n) /\
           (forall n, is_redblack tl Red n -> is_redblack tr Red n -> is_redblack (append (tl,tr)) Black n).
Proof.
induction sz; intros.
elimtype False; omega.
split; intros; rewrite append_equation.
inv H0. hax.
inv H2; inv H3.
inv H1. hax.
inv H0; inv H2.
rewrite append_equation; simpl. hax.
inv H1.
inv H2; inv H3.
assert (is_redblack (append (T Black tl0 k1 tr2, T Black tl2 k3 tr)) Black (S n0)).
apply IHsz. simpl in H|-*; omega.
hax. hax.
inv H1.
hax. hax.
constructor; auto. hax.
apply IHsz. simpl in H|-*; omega.
hax. hax.
inv H1.
hax.
constructor; auto.
apply IHsz. simpl in H|-*; omega.
hax. hax. hax.
assert (infrared (append(tr0,tl)) n0).
apply IHsz. simpl in H|-*; omega.
hax. hax.
inv H0.
unfold balleft.
inv H2.
simpl.
inv H7. hax. hax. hax. hax.
inv H2; hax.
inv H0; inv H1.
hax.
assert (infrared (append(tr0,tl)) n0).
apply IHsz; auto. simpl in H|-*; omega.
inv H0.
hax.
hax.
hax.
Qed.

Lemma infrared_append:
   forall tl tr n, is_redblack tl Black n -> is_redblack tr Black n ->
             infrared (append (tl,tr)) n.
Proof.
intros.
apply append_shape_aux with (S (size tl + size tr)); auto.
Qed.

Lemma append_is_redblack:
   forall tl tr n, is_redblack tl Red n -> is_redblack tr Red n ->
             is_redblack (append (tl,tr)) Black n.
Proof.
intros.
apply append_shape_aux with (S (size tl + size tr)); auto.
Qed.

Lemma balance'_shape2:
   forall n tl k tr,
     is_redblack tl Black n -> is_redblack tr Black n ->
     is_redblack (balance' tl k tr) Red (S n).
Proof.
induction n; intros; hax.
Qed.

Lemma del_shape:
  forall x t,
       (forall n, is_redblack t Red (S n) -> is_black t -> infrared (del x t) n) /\
       (forall n, is_redblack t Black n -> is_red_or_empty t -> is_redblack (del x t) Black n).
Proof.
intros x t.
pose (H:=True).
induction t; split.
intros; inv H0.
intros; inv H0.
simpl. constructor.
pose (H0:=True); pose (H1:=True); pose (H2:=True).
intros.
simpl in H4; destruct c; try contradiction; clear H4.
inv H3.
simpl.
rename t2 into k.
do_compare x k.
(* Case 1*)
apply infrared_append; auto.
(* Case 2 *)
destruct IHt1 as [ST1a ST1b]; destruct IHt2 as [ST2a ST2b].
inv H8.
repeat constructor; auto.
assert (is_redblack (del x (T Red tl k0 tr)) Black n).
apply ST1b. constructor; auto. simpl; auto.
remember  (del x (T Red tl k0 tr)) as t.
repeat constructor; auto.
remember  (del x (T Black tl k0 tr)) as t.
assert (infrared t n0).
apply ST1a; repeat constructor; auto.
inv H5.
inv H10.
simpl.
inv H5; repeat constructor; auto.
apply balance'_shape.
left; split; auto.
clear - H7; inv H7; simpl in *; constructor; auto.
simpl.
inv H7.
inv H11.
repeat constructor; auto.
repeat constructor; auto.
inv H11; repeat constructor; auto.
simpl.
repeat constructor; auto.
simpl.
inv H10; repeat constructor; auto.
inv H5; repeat constructor; auto.
apply balance'_shape.
left; split; auto.
clear - H9.
inv H9; simpl; repeat constructor; auto.
inv H9; repeat constructor; auto.
inv H13; repeat constructor; auto.
inv H13; repeat constructor; auto.
(* Case 3 *)
clear H.
inv H10.
repeat constructor; auto.
repeat constructor; auto.
apply IHt2.
repeat constructor; auto.
simpl; auto.
assert (infrared (del x (T Black tl k0 tr)) n0).
apply IHt2.
repeat constructor; auto.
simpl; auto.
remember (del x (T Black tl k0 tr)) as t.
inv H4.
simpl.
inv H8.
inv H6; inv H4.
constructor.
apply balance'_shape.
right; split; auto.
simpl.
repeat constructor; auto.
repeat constructor; auto.
inv H6.
inv H10.
repeat constructor; auto.
inv H4; inv H6.
repeat constructor; auto.
inv H4; inv H7.
repeat constructor; auto.
simpl.
repeat constructor; auto.
simpl.
inv H8.
inv H9.
repeat constructor; auto.
apply balance'_shape.
right; split; auto.
clear - H4; inv H4; simpl; repeat constructor; auto.
inv H9.
repeat constructor; auto.
inv H12.
repeat constructor; auto.
repeat constructor; auto.
(*  END OF PART ONE *)
(* PART TWO *)
intros.
destruct c; simpl in H1; try contradiction; clear H H1.
inv H0.
simpl.
rename t2 into k.
do_compare x k; repeat constructor; auto.
(* Case 1 *)
apply append_is_redblack; auto.
(* Case 2 *)
inv H2; inv H5.
simpl.
repeat constructor; auto.
destruct IHt1 as [ST1 _]. clear IHt2.
assert (infrared (del x (T Black tl k0 tr)) n0).
apply ST1. repeat constructor; auto. simpl; auto. clear ST1.
remember (del x (T Black tl k0 tr)) as t.
clear - H1 H2 H6 l.
assert (is_redblack (T Black tl0 k1 tr0) Black (S n0)) by hax.
unfold balleft.
inv H1.
simpl. inv H2. inv H6. hax. hax. hax.
hax.
simpl.
inv H2. inv H6. hax. hax.
inv H6. hax. hax.
(* Case 3 *)
clear IHt1.
destruct IHt2 as [? _].
inv H5.
hax.
assert (infrared (del x (T Black tl k0 tr)) n0).
apply H; hax.
clear H.
remember (del x (T Black tl k0 tr)) as t.
unfold balright.
inv H3.
inv H2.
apply balance'_shape. right; hax.
hax.
inv H2.
apply balance'_shape.
right; split; hax.
Qed.

Lemma delete_is_redblack:
  forall x t n, is_redblack t Black n ->
          exists n', is_redblack (delete x t) Red n'.
Proof.
intros.
unfold delete.
destruct (del_shape x t).
specialize (H1 _ H).
inv H.
simpl. econstructor; constructor.
specialize ( H1 I).
remember (del x (T Red tl k tr)) as t.
inv H1.
exists 0; constructor.
exists (S n); constructor; apply is_redblack_toblack; auto.
exists (S n0); constructor; auto.
clear H1.
assert (infrared (del x (T Black tl k tr)) n0).
apply H0.
hax. simpl; auto.
remember (del x (T Black tl k tr)) as t.
inv H.
do 2 econstructor.
exists (S n0); hax.
exists (S n); hax.
Qed.

Lemma interp_balance':
  forall tl k tr x, interp (balance' tl k tr) x <-> K.eq x k \/ interp tl x \/ interp tr x.
Proof.
unfold balance'; intros; split; intros.
repeat do_interp_balance.
destruct H as [?|[?|?]]; repeat do_interp_balance.
Qed.

Hint Constructors interp.

Tactic Notation "do_hyp" hyp(H) :=
  match type of H with ?a -> _ =>
    let H1 := fresh in (assert (H1: a); [ |generalize (H H1); clear H H1; intro H]) end.

Ltac jax :=
   repeat
       match goal with
        | H: interp EE _ |- _ => inv H
        | |- interp match ?c with Red => _ | Black => _ end _ => destruct c
        | |- interp match ?t with EE => _ | T _ _ _ _ => _ end _ =>
                  match t with balance' _ _ _ => fail 1 | append _ => fail 1 | _ =>  destruct t end
        | H: interp (balance' _ _ _) _ |- _ =>
                         apply interp_balance' in H; destruct H as [?|[?|?]]
        | |- interp (balance' _ _ _) _ =>
                         apply interp_balance'
        | H: interp match ?c with Red => _ | Black => _ end _ |- _ => destruct c
        | H: interp match ?t with EE => _ | T _ _ _ _ => _ end _ |- _  =>
                match t with balance' _ _ _ => fail 1 | append _ => fail 1 | _ =>  destruct t end
        | H: interp (T _ _ _ _) _ |- _ => inv H
        | H: interp _ _ <-> interp _ _ \/ interp _ _ |- _ =>
                        solve [destruct H  as [H _]; destruct H; auto]
        | |- _ => solve [auto 50]
        | H: interp _ _ -> _ \/ _ |- _ \/ _ => solve [destruct H; auto]
        | H: interp ?JJ  _, IHsz: forall _ _, _ -> _ |- _ =>
          match JJ with context [append(?a,?b)] =>
                 let H99 := fresh in
                    destruct (IHsz a b) as [H99 _];  [simpl in *; omega | ];
                    destruct (append(a,b));
                    try  (destruct (H99 H); [ solve [auto] | | ])
           end
         |  IHsz: forall _ _, _ -> _ |- interp ?JJ _ =>
       match JJ with context [append(?a,?b)] =>
                 let H99 := fresh in
                    destruct (IHsz a b) as [HA HB];  [simpl in *; omega | ];
                    destruct (append(a,b));
                    try (do_hyp HA; [solve [auto] | ]);
                    try (do_hyp HB; [solve [auto] | ])
        end
     end.

Lemma interp_append_aux:
  forall x sz tl tr, size tl + size tr < sz ->
     (interp (append(tl,tr)) x <-> (interp tl x \/ interp tr x)).
Proof.
induction sz; simpl; intros.
elimtype False; omega.
rewrite append_equation.
unfold balleft.
intuition; jax.
Qed.

Lemma interp_append:
  forall tl tr x, interp (append(tl,tr)) x <-> (interp tl x \/ interp tr x).
Proof.
intros.
apply interp_append_aux with (S (size tl + size tr)).
omega.
Qed.

Lemma interp_sub1: forall t x, interp (sub1 t) x <-> interp t x.
Proof.
unfold sub1; destruct t; intuition; inv H; auto.
Qed.

Lemma del_ok:
   forall x y t lo hi,
             searchtree lo hi t ->
             ((~K.eq x y /\ interp t x) <-> interp (del y t) x).
Proof.
induction 1; simpl; split; intros.
destruct H0. inv H1. inv H0.
destruct H1.
inv H2.
(* Forward direction, member_here *)
clear IHsearchtree1 IHsearchtree2.
do_compare y k.
contradiction H1; auto. apply eq_trans with k; auto.
remember (del y tl) as t.
clear - H8.
unfold balleft.
repeat (do_interp_balance; simpl).
unfold balright.
repeat (do_interp_balance; simpl).

(* Forward direction, member_left *)
do_compare y k.
apply interp_append. auto.
remember (del y tl) as t.
assert (interp t x).
apply IHsearchtree1; auto.
clear - H2.
unfold balleft.
repeat (do_interp_balance; simpl).
remember (del y tr) as t.
clear - H8.
unfold balright; repeat (do_interp_balance; simpl).
constructor 2.
apply interp_balance'; auto.
constructor 2; apply interp_balance'; auto.
right; left; apply interp_sub1; auto.
constructor 2; apply interp_balance'; auto.
constructor 2; apply interp_balance'; auto.
constructor 2; apply interp_balance'; auto.
right; left.
apply interp_sub1; auto.
constructor 2; apply interp_balance'; auto.

(* Forward direction, member_right *)
do_compare y k.
apply interp_append. auto.
remember (del y tl) as t.
clear - H8.
unfold balleft.
repeat (do_interp_balance; simpl);
try solve [constructor 3; apply interp_balance'; auto].
constructor 3. apply interp_balance'. right; right.
apply interp_sub1; auto.
constructor 3. apply interp_balance'. right; right.
apply interp_sub1; auto.

assert (interp (del y tr) x) by (apply IHsearchtree2; auto).
remember (del y tr) as t.
clear - H2.
unfold balright.
repeat (do_interp_balance; simpl).

(* Backward direction *)
assert (ST1: interp (del y tl) x -> ~K.eq x y /\ interp tl x).
intro; apply IHsearchtree1; auto.
assert (ST2: interp (del y tr) x -> ~K.eq x y /\ interp tr x).
intro; apply IHsearchtree2; auto.
clear IHsearchtree1 IHsearchtree2.
revert H1 ST1 ST2; set (ytl := del y tl); set (ytr := del y tr); intros.
do_compare y k.
(* Case 1 *)
apply interp_append in H1.
destruct H1.
split.
destruct (interp_range _ _ _ _ H H1).
clear - H3 e.
simpl in *. apply lt_not_eq. apply lt_eq with k; auto.
auto.
split.
destruct (interp_range _ _ _ _ H0 H1).
clear - H2 e.
simpl in *. intro; apply (lt_not_eq H2). apply eq_trans with y; auto.
auto.
(* Case 2 *)
revert H1; inversion H; clear H; intros.
unfold ytl in *; clear ytl; subst.
inv H5.
unfold ytr in *; clear ytr.
split. intro. apply (lt_not_eq l). apply eq_trans with x; auto.
auto.
inv H7.
clear - H0 H7 l.
split.
destruct (interp_range _ _ _ _ H0 H7).
simpl in H.
intro. apply (lt_not_eq (lt_trans l H)); auto.
constructor 3; auto.
assert (interp (T Red ytl k tr) x).
remember ytl as t.
clear - H6.
destruct c0; auto.
unfold balleft in H6.
repeat (do_interp_balance; simpl in *).
apply interp_balance' in H4.
destruct H4 as [?|[?|?]].
auto. auto.
constructor 3.
constructor 3.
apply interp_sub1; auto.
apply interp_balance' in H4.
destruct H4 as [?|[?|?]]. auto. auto.
constructor 3. constructor 3.
apply interp_sub1; auto.
clear H6.
subst lo0 hi0.
inversion H; clear H; subst k tr1 x0 tl1 c1.
split.
clear - l H9.
intro; contradiction (lt_not_eq l); auto. apply eq_trans with x; auto.
auto.
destruct (ST1 H9).
split; auto.
rewrite H5. auto.
rewrite H5.
split.
destruct (interp_range _ _ _ _ H0 H9).
simpl in H.
clear - H l.
intro; apply (lt_not_eq (lt_trans l H)); auto.
auto.
(* Case 3 *)
assert (interp (T Red tl k ytr) x).
clearbody ytr.
clear - H1.
destruct tr; auto. destruct c; auto.
unfold balright in H1.
destruct ytr; repeat (do_interp_balance; simpl); auto.
apply interp_balance' in H5.
constructor 2.
destruct H5 as [?|[?|?]]; auto.
constructor 2. apply interp_sub1; auto.
apply interp_balance' in H1.
destruct H1 as [?|[?|?]]; auto.
constructor 2. apply interp_sub1; auto.
apply interp_balance' in H5.
destruct H5 as [?|[?|?]].
constructor 2. auto.
apply -> interp_sub1 in H. auto.
auto.
apply interp_balance' in H1.
destruct H1 as [?|[?|?]]; auto.
inv H; auto.

clear H1 ST1.
inv H2.
split. intro; apply (lt_not_eq l). apply eq_trans with x; auto.
auto.
destruct (interp_range _ _ _ _ H H7).
simpl in H2.
split.
apply lt_not_eq; eapply lt_trans; eauto.
auto.
apply ST2 in H7.
destruct H7.
split; auto.
Qed.

Lemma interp_delete:
      forall x y s,
             searchtree None None s ->
             ((~K.eq x y /\ interp s x) <-> interp (delete y s) x).
Proof.
intros.
unfold delete.
destruct (del_ok x y s None None H).
split; intros.
apply H0 in H2.
destruct (del y s); auto.
inv H2; auto.
apply H1.
destruct (del y s); auto.
inv H2; auto.
Qed.

Lemma insert_valid: forall x s, valid s -> valid (insert x s).
Proof.
 intros. destruct H; split.
 apply insert_searchtree;  auto.
 destruct H0. simpl.
 eapply insert_is_redblack; eauto.
Qed.

Lemma empty_valid: valid EE.
Proof. split. repeat constructor. do 2 econstructor.
Qed.

Lemma delete_searchtree: forall k s,
  searchtree None None s -> searchtree None None (delete k s).
Proof.
 intros. apply (del_is_searchtree k) in H; unfold delete; simpl. inv H; constructor; auto.
Qed.

Lemma remove_valid: forall k s, valid s -> valid (delete k s).
Proof.
  intros ? ? [? ?]; split.
 apply delete_searchtree; auto.
destruct H0;    eapply delete_is_redblack; simpl; eauto.
Qed.

Lemma singleton_valid: forall k, valid (T Black EE k EE).
Proof. split. repeat constructor; auto. exists 1; repeat constructor; auto.
Qed.

(*  To compare two trees for equality (or less/greater) is the
  classic "samefringe" problem.  I use a solution involving
  the "gopher function",  attributed by Gabriel 1991 to McCarthy 1977,
 but an equivalent solution was published first by Gruessay in 1976.

  Gabriel writes, "this solution is difficult to understand," but in fact
  the Coq proofs about it are quite straightforward, actually simpler
  than the ones involving list-flattening solutions to samefringe.

   Richard Gabriel, The design of parallel programming languages,
   in Artificial intelligence and mathematical theory of computation,
   ed. Vladimir Lifschitz,  pp. 91-108, Academic Press 1991.

  Patrick Gruessay, "An iterative Lisp solution to the Samefringe problem",
  ACM SIGART Bulletin, Issue 59, p. 14, August 1976.

  John McCarthy. Another Samefringe. ACM SIGART Bulletin, No. 61, February 1977.

*)

Fixpoint gopher (s: tree) : tree :=
 match s with
 | EE => EE
 | T _ sl k sr => match gopher sl with
                          | T _ sll j slr => T Red sll j (T Red slr k sr)
                          | EE => s
                          end
  end.

Lemma shape_gopher: forall a,
  match gopher a with
  | T _ (T _ _ _ _) _ _ => False
  | _ => True
  end.
Proof. induction a; simpl; auto.
  destruct a1; simpl in *; try contradiction; auto.
  destruct (gopher a1_1); simpl in *; auto.
Qed.

Lemma size_gopher: forall s, size (gopher s) = size s.
Proof.
 induction s; simpl; auto.
 revert IHs1; case_eq (gopher s1); intros.
 destruct s1; inv IHs1. simpl. auto.
 simpl in *. omega.
 Qed.

Lemma interp_gopher: forall s k, interp (gopher s) k <-> interp s k.
 Proof.
 intros.
  remember (size s) as n.
  assert (size s <= n) by (subst; auto).
  clear - H.
  revert s H; induction n; intros.
  destruct s; simpl in H. simpl; intuition.
  elimtype False; omega.
  destruct s; simpl; intuition.
  destruct (IHn s1). simpl in H; omega.
  revert H0 H1 H2; case_eq (gopher s1); intros.
  destruct s1; inv H0. auto.
  inv H1.
  constructor 1; auto.
  apply H3 in H9. inv H9.
  constructor 3; auto.
  inv H1.
  constructor 2. apply H2. constructor 1; auto.
  constructor 2. apply H2. constructor 2; auto.
  inv H9.
  constructor 1; auto.
  constructor 2. apply H2. constructor 3; auto.
  constructor 3; auto.

  simpl in H.
  case_eq (gopher s1); intros.
  destruct s1; inv H1; auto.
  destruct (IHn s1); try omega.
  rewrite H1 in *.
  clear H1 n IHn H.
  inv H0.
  constructor 3; constructor 1; auto.
  apply H3 in H7.
  inv H7.
  constructor 1; auto.
  constructor 2; auto.
  constructor 3; constructor 2; auto.
  constructor 3; constructor 3; auto.
Qed.

Lemma searchtree_gopher: forall a lo hi,
    searchtree lo hi a <-> searchtree lo hi (gopher a).
 Proof.
  induction a; intros; simpl.
  intuition.
  case_eq (gopher a1); intros.
  intuition.
  rewrite H in IHa1.
  clear - IHa1.
  intuition.
  inv H.
  apply IHa1 in H4. inv H4.
  repeat constructor; auto.
  inv H. inv H7.
  constructor; auto.
  apply IHa1. repeat constructor; auto.
 Qed.


Fixpoint rgopher (s: tree) : tree :=
 match s with
 | EE => EE
 | T _ sl k sr => match rgopher sr with
                          | T _ srl j srr => T Red  (T Red sl k srl) j srr
                          | EE => s
                          end
  end.

Lemma shape_rgopher: forall a,
  match rgopher a with
  | T _ _ _ (T _ _ _ _) => False
  | _ => True
  end.
Proof. induction a; simpl; auto.
  destruct a2; simpl in *; try contradiction; auto.
  destruct (rgopher a2_2); simpl in *; auto.
Qed.

Lemma size_rgopher: forall s, size (rgopher s) = size s.
Proof.
 induction s; simpl; auto.
 revert IHs2; case_eq (rgopher s2); intros.
 destruct s2; inv IHs2. simpl. auto.
 simpl in *. omega.
 Qed.


Lemma searchtree_rgopher: forall a lo hi,
    searchtree lo hi a <-> searchtree lo hi (rgopher a).
 Proof.
  induction a; intros; simpl.
  intuition.
  case_eq (rgopher a2); intros.
  intuition.
  rewrite H in IHa2.
  clear - IHa2.
  intuition.
  inv H.
  apply IHa2 in H7. inv H7.
  repeat constructor; auto.
  inv H. inv H4.
  constructor; auto.
  apply IHa2. repeat constructor; auto.
 Qed.


Lemma interp_rgopher: forall s k, interp (rgopher s) k <-> interp s k.
 Proof.
 intros.
  remember (size s) as n.
  assert (size s <= n) by (subst; auto).
  clear - H.
  revert s H; induction n; intros.
  destruct s; simpl in H. simpl; intuition.
  elimtype False; omega.
  destruct s; simpl; intuition.
  destruct (IHn s2). simpl in H; omega.
  revert H0 H1 H2; case_eq (rgopher s2); intros.
  destruct s2; inv H0. auto.
  inv H1.
  constructor 1; auto.
  constructor 2; auto.
  apply H3 in H9. inv H9.
  inv H1.
  constructor 3. apply H2. constructor 1; auto.
  inv H9.
  constructor 1; auto.
  constructor 2; auto.
  constructor 3; apply H2. constructor 2; auto.
  constructor 3. apply H2. constructor 3; auto.

  simpl in H.
  case_eq (rgopher s2); intros.
  destruct s2; inv H1; auto.
  destruct (IHn s2); try omega.
  rewrite H1 in *.
  clear H1 n IHn H.
  inv H0.
  constructor 2; constructor 1; auto.
  constructor 2; constructor 2; auto.
  apply H3 in H7.
  inv H7.
  constructor 1; auto.
  constructor 2; constructor 3; auto.
  constructor 3; auto.
Qed.

Function compare' (s t : tree) {measure size s} : comparison :=
 match gopher s, gopher t with
 | EE , EE => Eq
 | T _ EE j sr , T _ EE j' tr =>
    match K.compare j j' with
    | Gt => Gt | Lt => Lt | Eq => compare' sr tr
    end
 | T _ _ _ _, T _ _ _ _ => Eq (* impossible *)
 | T _ _ _ _, EE => Gt
 |  EE, T _ _ _ _ => Lt
 end.
 Proof.
  intros. subst.
  rewrite <- (size_gopher s). rewrite teq.
  simpl; omega.
  Defined.

Lemma interp_compare': forall a b,
     compare' a b = Eq -> (forall k, interp a k <-> interp b k).
 Proof.
  intros.
  remember (size a) as n.
  assert (size a <= n) by (subst; auto).
  clear Heqn; revert a b H0 H; induction n; intros.
  destruct a; inv H0. destruct b; inv H. intuition.
  rewrite compare'_equation in H1. simpl in H1.
  destruct (gopher b1); inv H1.

  rewrite compare'_equation in H.
  generalize (interp_gopher a k); intro.
  generalize (interp_gopher b k); intro.
  generalize (size_gopher a); intro.
  generalize (size_gopher b); intro.
  generalize (shape_gopher a); intro SHa.
  generalize (shape_gopher b); intro SHb.
  destruct (gopher a), (gopher b); try discriminate;
  intuition etac.
  destruct t1; try discriminate.
  destruct t1; try contradiction.
  destruct t4; try contradiction.
  do_compare t2 t5; try discriminate.
  simpl in H3, H4.
  apply IHn in H; try omega.
  apply H1. inv H8.  constructor 1. rewrite H13; auto.
  inv H13.
  constructor 3; intuition.
  destruct t1; try contradiction.
  destruct t4; try contradiction.
  do_compare t2 t5; try discriminate.
  simpl in H3,H4.
  apply IHn in H; try omega.
  apply H5.
  inv H8; auto. constructor 1; rewrite e; auto.
  constructor 3; intuition.
 Qed.

Lemma compare'_interp_aux:
  forall a lo hi b lo' hi',
       searchtree lo hi a ->
       searchtree lo' hi' b ->
        (forall k, interp a k <-> interp b k) ->
       compare' a b = Eq.
 Proof.
  intro a.
   remember (size a) as n.
  assert (size a <= n) by (subst; auto).
  clear Heqn; revert a H; induction n; intros; rewrite compare'_equation.
  destruct a; inv H.
  destruct b; simpl; auto.
  destruct (H2 t).
  assert (interp EE t). apply H3. constructor 1; auto. reflexivity. inv H4.
  generalize (shape_gopher a) as SHa.
  case_eq (gopher a); intros.
  destruct a; inv H3.
  replace b with EE. simpl; auto.
  destruct b; auto.
  destruct (H2 t).
  assert (interp EE t). apply H4. constructor 1; auto. reflexivity. inv H5.
  destruct (gopher a1); inv H5.
  destruct t; try contradiction. clear SHa.
  generalize (size_gopher a); rewrite H3 ;intro.
  generalize (interp_gopher a); rewrite H3; intro IGa.
  generalize (searchtree_gopher a lo hi); rewrite H3; intro.
  clear H3.
  generalize (searchtree_gopher b lo' hi'); intro.
  generalize (interp_gopher b); intro.
  generalize (shape_gopher b) as SHb.
  remember (gopher b) as gb; clear Heqgb; intros.
  destruct gb.
  specialize (IGa t0). specialize (H6 t0). specialize (H2 t0).
  rewrite <- H2 in H6.
  rewrite <- H6 in IGa.
  clear - IGa.
  assert (interp EE t0); [| inv H].
  apply IGa. constructor 1; reflexivity.
  destruct gb1; try contradiction.
  do_compare t0 t.
  simpl in H4.
  apply H5 in H0.  inv H0.
  apply H3 in H1. inv H1.
  apply IHn with (lo:=Some t0)(hi:=hi)(lo':=Some t)(hi':=hi'); auto.
  clear - H H4. omega.
  intro; specialize (H6 k); specialize (IGa k). specialize (H2 k).
  intuition.
  assert (interp a k). apply H2. constructor 3; auto.
  apply H0 in H16. apply H13 in H16.
  inv H16.
  elimtype False.
  clear - e H22 H14 H6.
  destruct (interp_range _ _ _ _ H14 H6).
  simpl in H. rewrite H22 in H. rewrite e in H. apply (lt_irrefl H).
  inv H22. auto.
  assert (interp a k).
  apply H1. apply H3. constructor 3; auto.
  apply H7 in H16.
  inv H16.
  elimtype False; clear - H22 H6 H15 e.
  rewrite e in H22.
  destruct (interp_range _ _ _ _ H15 H6).
  simpl in H. rewrite H22 in H. apply (lt_irrefl H).
  inv H22.
  auto.
  rename t into j;   rename t0 into k.
  apply H5 in H0; clear H5; inv H0.
  apply H3 in H1; clear H3; inv H1.
  inv H8; inv H10.
  specialize (H6 k); specialize (IGa k); specialize (H2 k).
  assert (interp a k).
  apply IGa. constructor 1; reflexivity.
  apply H2 in H3. apply H6 in H3.
  inv H3.   rewrite H11 in  l. contradiction (lt_irrefl l). inv H11.
  destruct (interp_range _ _ _ _ H12 H11).
  simpl in H3. contradiction (lt_irrefl (lt_trans  l H3)).
  rename t into j;   rename t0 into k.
  apply H5 in H0; clear H5; inv H0.
  apply H3 in H1; clear H3; inv H1.
  inv H8; inv H10.
  specialize (H6 j); specialize (IGa j); specialize (H2 j).
  assert (interp b j). apply H6. constructor 1; reflexivity.
  apply H2 in H3. apply IGa in H3.
  inv H3. rewrite H11 in l. contradiction (lt_irrefl l). inv H11.
  destruct (interp_range _ _ _ _ H13 H11).
  simpl in H3. contradiction (lt_irrefl (lt_trans  l H3)).
 Qed.

Fixpoint revsize (n: positive) (lr l: list key) : positive * list key :=
 match l with
 | nil => (n, lr)
 | x::xs => revsize (Psucc n) (x::lr) xs
 end.

Function linear_union_aux (st : tree*tree) (nl: positive * list key)
   {measure (fun st => size (fst st) + size (snd st)) st} : positive * list key  :=
 match rgopher (fst st), rgopher (snd st) with
 | EE , EE => nl
 | T _ sl j EE as st1 , T _ tl j' EE as st2 =>
    match K.compare j j' with
    | Lt => linear_union_aux (st1, tl) (Psucc (fst nl), j':: snd nl)
    | Gt => linear_union_aux (sl, st2) (Psucc (fst nl), j:: snd nl)
    | Eq => linear_union_aux (sl,tl) (Psucc (fst nl), j:: snd nl)
    end
 | T _ sl j EE, EE => linear_union_aux (sl,EE) (Psucc (fst nl), j:: snd nl)
 |  EE, T _ tl j' EE => linear_union_aux (EE,tl) (Psucc (fst nl), j':: snd nl)
 | _, _ => nl (* impossible *)
 end.
 Proof.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq0; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
 Defined.

Definition linear_union (s1 s2 : tree) : tree :=
  let (n,l) := linear_union_aux (s1,s2) (1%positive, nil)
   in fst (treeify_g n l).

Function linear_diff_aux (st : tree*tree) (nl: positive * list key)
   {measure (fun st => size (fst st) + size (snd st)) st} : positive * list key  :=
 match rgopher (fst st), rgopher (snd st) with
 | EE , _ => nl
 | T _ sl j EE as st1 , T _ tl j' EE as st2 =>
    match K.compare j j' with
    | Lt => linear_diff_aux (st1, tl) nl
    | Gt => linear_diff_aux (sl, st2) (Psucc (fst nl), j:: snd nl)
    | Eq => linear_diff_aux (sl,tl) nl
    end
 | T _ sl j EE, EE => linear_diff_aux (sl,EE) (Psucc (fst nl), j:: snd nl)
 | _, _ => nl (* impossible *)
 end.
 Proof.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
 Defined.

Definition linear_diff (s1 s2 : tree) : tree :=
  let (n,l) := linear_diff_aux (s1,s2) (1%positive, nil)
   in fst (treeify_g n l).

Fixpoint fold' (A: Type) (f: key -> A -> A) (x: tree) (base: A) : A :=
  match x with
  | EE => base
  | T _ t1 k t2 => fold' A f t2 (f k (fold' A f t1 base))
 end.

Definition skip_red t :=
 match t with
 | T Red t' _ _ => t'
 | _ => t
 end.

Definition skip_black t :=
  match skip_red t with
  | T Black t' _ _ => t'
  | t' => t'
  end.

(* compare_height returns Lt if height(s2) is at least twice height(s1);
  returns Gt if height(s1) is at least twice height (s2);
  returns Eq if heights are approximately equal.
  Warning: this is not an equivalence relation!  but who cares....
*)
Fixpoint compare_height (s1x s1 s2 s2x: tree) : comparison :=
 match skip_red s1x, skip_red s1, skip_red s2, skip_red s2x with
 | T _ s1x' _ _, T _ s1' _ _, T _ s2' _ _, T _ s2x' _ _ =>
        compare_height (skip_black s2x') s1' s2' (skip_black s2x')
 | _, EE, _, T _ _ _ _ => Lt
 | T _ _ _ _, _, EE, _ => Gt
 | T _ s1x' _ _, T _ s1' _ _, T _ s2' _ _, EE =>
        compare_height (skip_black s1x') s1' s2' EE
 | EE, T _ s1' _ _, T _ s2' _ _, T _ s2x' _ _ =>
        compare_height EE s1'  s2'  (skip_black s2x')
 | _, _, _, _ => Eq
 end.


Function linear_inter_aux (st : tree*tree) (nl: positive * list key)
   {measure (fun st => size (fst st) + size (snd st)) st} : positive * list key  :=
 match rgopher (fst st), rgopher (snd st) with
 | T _ sl j EE as st1, T _ tl j' EE as st2 =>
    match K.compare j j' with
    | Lt => linear_inter_aux (st1, tl) nl
    | Gt => linear_inter_aux (sl, st2) nl
    | Eq => linear_inter_aux (sl,tl) (Psucc (fst nl), j:: snd nl)
    end
 | _, _ => nl
 end.
 Proof.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
  simpl; intros; subst;
       rewrite <- (size_rgopher (fst st)); rewrite <- (size_rgopher (snd st));
       rewrite teq; rewrite teq1; simpl; omega.
 Defined.

Definition linear_inter (s1 s2 : tree) : tree :=
  let (n,l) := linear_inter_aux (s1,s2) (1%positive,nil)
   in fst (treeify_g n l).


Functional Scheme treeify_f_ind2 := Induction for treeify_f Sort Prop
   with treeify_g_ind2 := Induction for treeify_g Sort Prop.

Fixpoint plog2 (p: positive) : nat :=
 match p with
 | xH => O
 | xO n => S (plog2 n)
 | xI n => S (plog2 n)
 end.



Lemma nat_of_P_pos: forall n, nat_of_P n > 0.
Proof.
 induction n.
 rewrite nat_of_P_xI. omega.
 rewrite nat_of_P_xO.  omega.
 rewrite nat_of_P_xH; omega.
Qed.

Lemma nat_of_P_pospos: forall n, n<>1%positive -> nat_of_P n > 1.
Proof.
intros.
induction n;
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *;
  simpl in *.
 generalize (nat_of_P_pos n); intro.  omega.
 generalize (nat_of_P_pos n); intro.  omega.
 contradiction H; auto.
Qed.

Lemma treeify_f_length:
  forall n l, length l >= nat_of_P n ->
           length(snd(treeify_f n l))+nat_of_P n = length l.
 Proof.
 pose (fP n (l: list key) (res: tree * list key) :=
                      length l >= nat_of_P n -> length (snd res) + nat_of_P n = length l).
 pose (gP n (l: list key) (res: tree * list key) :=
                      S (length l) >= nat_of_P n -> length (snd res) + nat_of_P n = S(length l)).
 intros.
 apply (treeify_f_ind2 fP gP); unfold fP, gP; clear fP gP; simpl; intros; subst;
  try rewrite e0 in *; try rewrite e2 in *; try clear e0; try clear e2;
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *;
  simpl in *.
 (* 12 cases! *)
 (* case 1 *)
 rewrite <- H0 by omega. omega.
 (* case 2 *)
 rewrite <- H0 by omega. rewrite <- H1 by omega. omega.
 (* case 3 *)
 rewrite <- H0 in H1 by omega. omega.
 (* case 4 *)
 rewrite <- H0 by omega.
 transitivity (S (length l2) + nat_of_P n'); [ | omega].
 rewrite <- H1; try omega.
 (* case 5 *)
 omega.
 (* case 6 *)
 omega.
 (* case 7 *)
 rewrite <- H0 by omega. omega.
 (* case 8 *)
 rewrite <- H0 by omega.
 change (S (length l2 + nat_of_P n')) with (S (length l2) + nat_of_P n').
 rewrite <- H1 by omega. omega.
 (* case 9 *)
 rewrite H0 in H1 by omega. omega.
 (* case 10 *)
 rewrite <- H0 by omega.
 change (S (length l2 + nat_of_P n')) with (S (length l2) + nat_of_P n').
 rewrite <- H1 by omega. omega.
 (* case 11 *)
 omega.
 (* case 12 *)
 auto.
 Qed.

Ltac spec H := match type of H with ?A -> _ =>
                            let H' := fresh in (assert (H' : A); [ | specialize (H H'); clear H']) end.

Lemma treeify_g_length:
  forall n l, S (length l) >= nat_of_P n ->
           length(snd(treeify_g n l))+nat_of_P n = S (length l).
 Proof.
 induction n; simpl; intros;
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *.
 (* case 1 of 3 *)
 generalize (treeify_f_length n l); intros.
 destruct (treeify_f n l); simpl in *.
 destruct l0. simpl in H0.
 spec H0; [omega|]. simpl.
 omega.
 specialize (IHn l0).
 destruct (treeify_g n l0). simpl in *.
 rewrite <- H0 by omega. omega.
 generalize (IHn l); intros.
 destruct (treeify_g n l); simpl in *.
 destruct l0; simpl in *.
 omega.
 specialize (IHn l0). destruct (treeify_g n l0); simpl in *. omega.
 (* case 3 of 3 *)
 omega.
Qed.

Lemma eq1dec: forall n, {n=1%positive}+{n<>1%positive}.
Proof.
 destruct n. right; congruence.  right; congruence. auto.
Qed.

Lemma treeify_g_induc:
        forall fP gP : positive -> list key -> tree * list key -> Prop,
       (forall l n' t1 x l2 t2 l3
         (LEN: length l >= nat_of_P n')
         (LEN2: length l2 >= nat_of_P n'),
         fP n' l (t1, x::l2) ->  treeify_f n' l = (t1, x::l2) -> fP n' l2 (t2, l3) ->
           treeify_f n' l2 = (t2, l3) -> fP (xI n') l (T Black t1 x t2, l3)) ->
       (forall  l n' t1 x l2 t2 l3
         (LEN: length l >= nat_of_P n')
         (LEN2: S (length l2) >= nat_of_P n'),
          fP n' l (t1, x :: l2) -> treeify_f n' l = (t1, x :: l2) -> gP n' l2 (t2, l3) ->
          treeify_g n' l2 = (t2, l3) -> fP (xO n') l (T Black t1 x t2, l3)) ->
       (forall x l1, fP xH (x :: l1) (T Red EE x EE, l1)) ->
       (forall  l n' t1 x l2 t2 l3
           (LEN: length l >= nat_of_P n')
         (LEN2: S (length l2) >= nat_of_P n'),
          fP n' l (t1, x :: l2) -> treeify_f n' l = (t1, x :: l2) -> gP n' l2 (t2, l3) ->
          treeify_g n' l2 = (t2, l3) -> gP (xI n') l (T Black t1 x t2, l3)) ->
       (forall l n' t1 x l2 t2 l3
        (LEN: S (length l) >= nat_of_P n')
         (LEN2: S (length l2) >= nat_of_P n'),
        gP n' l (t1, x :: l2) -> treeify_g n' l = (t1, x :: l2) ->
        gP n' l2 (t2, l3) -> treeify_g n' l2 = (t2, l3) -> gP (xO n') l (T Black t1 x t2, l3)) ->
       (forall l, gP xH l (EE, l)) ->
       forall n l, S (length l) >= nat_of_P n -> gP n l (treeify_g n l).
 Proof.
  intros.
  apply (treeify_g_ind2
     (fun n (l: list key) (res: tree * list key) => length l >= nat_of_P n -> fP n l res)
     (fun n (l: list key) (res: tree * list key) => S (length l) >= nat_of_P n -> gP n l res));
 intros;
 try (rewrite e0 in *); try (rewrite e2 in *);
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *;
  subst; simpl in *.
 (* case 1 of 11 *)
  generalize (treeify_f_length n' l0); rewrite e0; simpl; intro.
  spec H8; [ omega |].
  elimtype False;  omega.
 (* case 2 of 11 *)
  generalize (treeify_f_length n' l0); rewrite e0; simpl; intro.
  spec H9; [omega|].
  spec H7; [ omega |].
  spec H6; [omega|].
  eapply H; eauto. omega. omega.
 (* case 3 of 11 *)
  generalize (treeify_f_length n' l0); rewrite e0; simpl; intro.
   generalize (nat_of_P_pos n'); intro.
  spec H8; [omega|].
  spec H6; [omega|].
  elimtype False. omega.
  (* case 4 of 11 *)
  subst.
   generalize (nat_of_P_pos n'); intro POS.
  generalize (treeify_f_length n' l0); rewrite e0; simpl in *; intro.
  eapply H0; eauto. omega. omega. apply H6. omega.
  apply H7. omega.
  (* case 5 of 11 *)
  elimtype False; omega.
  (* case 6 of 11 *)
  eapply H1; eauto.
  (* case 7 of 11 *)
  generalize (treeify_f_length n' l0); rewrite e0; simpl in *; intro.
  spec H8; [omega|].
  generalize (nat_of_P_pos n'); intro.
  elimtype False.      generalize (nat_of_P_pos n'); intro. omega.
  (* case 8 of 11 *)
  generalize (treeify_f_length n' l0); rewrite e0; simpl in *; intro.
  spec H6; [omega|]. spec H7; [omega|]. spec H9; [omega|].
  eapply H2; eauto; omega.
  (* case 9 of 11 *)
  spec H6; [omega|].
  generalize (treeify_g_length n' l0); rewrite e0; simpl in *; intro.
  spec H8; [omega|].
  elimtype False; omega.
  (* case 10 of 11 *)
  generalize (treeify_g_length n' l0); rewrite e0; simpl in *; intro.
  spec H9; [omega|]. spec H6; [omega|]. spec H7; [omega|].
  eapply H3; eauto. omega. omega.
  (* case 11 of 11 *)
  eapply H4; eauto.
  (* done *)
  auto.
Qed.

Lemma treeify'_g_is_redblack:
   forall n l,
     S (length l) >= nat_of_P n ->
       is_redblack (fst (treeify_g n l)) Red (plog2 n).
 Proof.
  intros.
  apply (treeify_g_induc
              (fun n l res => n<>xH ->  is_redblack (fst res) Red (plog2 n))
              (fun n l res => is_redblack (fst res) Red (plog2 n)));
  auto; clear n l H;
  intros;
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *;
  simpl in *.
 (* case 1 of 6 *)
     destruct (eq1dec n').
     subst n'. clear - H0 H2. simpl in *.
     destruct l; inv H0; try discriminate.
     destruct l2; inv H2; try discriminate.
     repeat constructor; auto.
     repeat constructor; auto.
     repeat constructor; auto.
 (* case 2 of 6 *)
   generalize (nat_of_P_pos n'); intro POS.
  generalize (treeify_f_length n' l); simpl in *; intro.
  constructor.
  destruct (eq1dec n').
  subst n'; simpl in *. destruct l; inv H0. inv H2. repeat constructor; auto.
  apply is_redblack_toblack. apply H; auto; omega.
  apply is_redblack_toblack. apply H1; omega.
  (* case 3 of 6 *)
  contradiction H; auto.
  (* case 4 of 6 *)
  destruct (eq1dec n'). subst n'.
   simpl in *. destruct l; inv H0. inv H2.
   repeat constructor; auto.
  generalize (treeify_f_length n' l); simpl in *; intro.
  constructor.
  apply is_redblack_toblack. apply H; auto; omega.
  apply is_redblack_toblack. apply H1; auto; omega.
  (* case 5 of 6 *)
  generalize (treeify_g_length n' l); simpl in *; intro.
  destruct (eq1dec n'). subst n'. simpl in *. inv H2; inv H0.
  repeat constructor.
  assert (H4 := nat_of_P_pospos _ n).
  constructor; apply is_redblack_toblack.
  apply H; omega.
  auto.
  (* case 6 of 6 *)
  constructor; auto.
Qed.

Lemma nat_of_poslength:
    forall A (l: list A), nat_of_P (poslength l) = S (length l).
Proof.
 induction l. simpl. rewrite nat_of_P_xH; omega.
  simpl.
  rewrite nat_of_P_succ_morphism.
 omega.
Qed.

Lemma treeify_is_redblack:
  forall l, exists n, is_redblack (treeify l) Red n.
Proof.
 intros.
 exists (plog2 (poslength l)).
 apply treeify'_g_is_redblack.
 rewrite nat_of_poslength.
 auto.
Qed.



Definition HdRel' (R: key -> key -> Prop) (lo: option key) (l: list key) :=
   match lo with Some lo' => HdRel R lo' l | None => True end.

Lemma treeify_f_not_EE:
  forall n l, length l >= nat_of_P n -> fst (treeify_f n l) <> EE.
Proof.
 induction n; simpl; intros;
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *.
 generalize (treeify_f_length n l); intro.
 spec H0; [omega|].
  destruct (treeify_f n l).
  simpl in H0. destruct l0.
 simpl in H0; elimtype False; omega.
  destruct (treeify_f n l0); simpl; congruence.
 generalize (treeify_f_length n l); intro.
 spec H0; [omega|].
  destruct (treeify_f n l).
  simpl in H0. destruct l0.
 simpl in H0; elimtype False.
  generalize (nat_of_P_pos n); intro; omega.
  destruct (treeify_g n l0); simpl; congruence.
  destruct l; simpl in H.
  elimtype False; omega.
  simpl; congruence.
Qed.

Lemma treeify'_g_is_searchtree:
   forall n l lo,
    HdRel' K.lt lo l -> Sorted K.lt l ->
     S (length l) >= nat_of_P n ->
       (searchtree lo (hd_error (snd (treeify_g n l))) (fst (treeify_g n l)) /\
        (forall k, interp (fst (treeify_g n l)) k \/ InA K.eq k (snd (treeify_g n l)) <-> InA K.eq k l) /\
            Sorted K.lt (snd (treeify_g n l))).
 Proof.
 intros.
 pose (fP n (l: list key) (res: tree*list key) :=
             forall lo, HdRel' K.lt lo l -> Sorted K.lt l ->
                  searchtree lo (hd_error (snd res)) (fst res) /\
        (forall k, interp (fst (treeify_f n l)) k \/ InA K.eq k (snd (treeify_f n l)) <-> InA K.eq k l) /\
        Sorted K.lt (snd (treeify_f n l))).
 pose (gP n (l: list key) (res: tree*list key) :=
             forall lo, HdRel' K.lt lo l -> Sorted K.lt l ->
          searchtree lo (hd_error (snd res))  (fst res)/\
        (forall k, interp (fst (treeify_g n l)) k \/ InA K.eq k (snd (treeify_g n l)) <-> InA K.eq k l) /\
                   Sorted K.lt (snd (treeify_g n l))).
 eapply (treeify_g_induc fP gP); auto;
  clear l n H H0 H1;
 unfold fP,gP; clear fP gP; intros;
  try rewrite nat_of_P_xH in *;
  try rewrite nat_of_P_xO in *;
  try rewrite nat_of_P_xI in *.
  (* case 1 of 6 *)
  destruct (H _ H3 H4) as [? [? ?]]; clear H.
  rewrite H0 in *; simpl fst in *; simpl snd in *.
  inv H7.
  destruct (H1 (Some x) H10 H9) as [? [? ?]]; clear H1.
  rewrite H2 in *; simpl fst in *; simpl snd in *.
  simpl hd_error in *. unfold value in *.
  rewrite H0. rewrite H2. simpl fst in *; simpl snd in *.
  split; [|split]; auto.
  constructor; auto.
  apply treeify_f_not_EE in LEN; rewrite H0 in LEN. simpl in LEN.
  destruct t1; try solve [contradiction LEN; auto]. inv H5.
    apply treeify_f_not_EE in LEN2; rewrite H2 in LEN2; simpl in LEN2.
  destruct t2; try solve [contradiction LEN2; auto]. inv H.
  clear - H6 H7.
  intro k; specialize (H6 k); specialize (H7 k); intuition. inv H6; intuition.
  inv H0; intuition.
 (* case 2 of 6 *)
  destruct (H _ H3 H4) as [? [? ?]]; clear H.
  simpl fst in *; simpl snd in *.
  rewrite H0 in *; rewrite H2 in *.
  simpl fst in *; simpl snd in *. simpl hd_error in *. unfold value in *.
  inv H7.
  destruct (H1 (Some x) H10 H9) as [? [? ?]]; clear H1.
  split; [|split]; auto.
  constructor; auto.
  clear - H6 H7; intro k; specialize (H6 k); specialize (H7 k); intuition.
  inv H6; intuition. inv H0; intuition.
 (* case 3 of 6 *)
  destruct lo0; simpl in H.
  inv H; inv H0. simpl.
  split; [|split]; auto. repeat constructor; auto.
  destruct l1; simpl; auto. inv H4; auto.
  intro k; intuition.
  inv H0; try solve [inv H8]. constructor 1. auto.
  inv H. left; constructor 1; auto. auto.
  inv H0. simpl.
  split; [|split]; auto. repeat constructor; auto.
  destruct l1; simpl; auto. inv H4; auto.
  intro k; intuition. inv H1; constructor 1; auto. inv H8. inv H8.
  inv H0. left; constructor 1; auto. auto.
 (* case 4 of 6 *)
  simpl in *.
  rewrite H0 in *. rewrite H2 in *.
  simpl in *.
  unfold value in *.
  destruct (H _ H3 H4) as [? [? ?]]; clear H.
  inv H7.
  destruct (H1 (Some x) H10 H9) as [? [? ?]];  clear H1.
  split; [|split]; auto.
  repeat constructor; auto.
  clear - H6 H7; intro k; specialize (H6 k); specialize (H7 k); intuition.
  inv H6; intuition.
  inv H0; intuition.
 (* case 5 of 6 *)
  simpl in *.
  rewrite H0 in *. rewrite H2 in *.
  simpl in *.
  unfold value in *.
  destruct (H _ H3 H4) as [? [? ?]]; clear H.
  inv H7.
  destruct (H1 (Some x) H10 H9) as [? [? ?]];  clear H1.
  split; [|split]; auto.
  repeat constructor; auto.
  clear - H6 H7; intro k; specialize (H6 k); specialize (H7 k); intuition.
  inv H6; intuition.
  inv H0; intuition.
 (* case 6 of 6 *)
  simpl in *.
  split; [|split]; auto.
  constructor.
  destruct lo0; simpl; auto.
 destruct l; simpl in *; try unfold error, ltopt in *; simpl in *; auto.
  inv H; auto.
  intro k; intuition. inv H2.
Qed.

Fixpoint filter_aux (f: key -> bool) (s: tree) (n: positive) (l: list key) : (positive * list key) :=
 match s with
 | T _ sl k sr => let (n,l') := filter_aux f sr n l
                           in if f k then filter_aux f sl (Psucc n) (k::l')
                                        else filter_aux f sl n l'
 | EE => (n,l)
 end.

Definition Kle x y := K.lt x y \/ K.eq x y.

  Lemma HdRel_le_lt:
   forall u v l, K.lt u v -> HdRel Kle v l -> HdRel K.lt u l.
  Proof.
  intros. revert u H; induction H0; intros; constructor.
  destruct H. apply lt_trans with v; auto. rewrite <- H; auto.
 Qed.

  Lemma HdRel_lt_le: forall v l, HdRel K.lt v l -> HdRel Kle v l.
  induction 1; constructor. left; auto.
  Qed.

  Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).


  Lemma filter_aux_lemma:
  forall f s n l lo hi,
           searchtree lo hi s -> filter_aux f s 1%positive nil = (n,l) ->
          HdRel' K.lt lo l /\ Sorted K.lt l /\ S (length l) = nat_of_P n /\
          (compatb f -> forall x, interp s x /\ f x = true <-> InA K.eq x l).
 Proof.
  intros.
  remember 1%positive as n0.
  remember (@nil key) as l0.
  assert (HdRel' Kle hi l0) by (destruct hi; subst; simpl; auto).
  assert (S (length l0) = nat_of_P n0) by (subst; simpl; auto).
  assert (Sorted K.lt l0) by (subst; constructor).
  assert (match hi, l0 with None, _::_ => False | _,_ => True end) by (destruct hi; subst; simpl; auto).
  assert ((forall x, interp s x /\ f x = true <-> InA K.eq x l) <->
             (forall x, interp s x /\ f x =  true \/ InA K.eq x l0 <-> InA K.eq x l)).
  subst l0; simpl. assert (forall x, InA K.eq x nil <-> False) by (clear; intuition; inv H).
  clear - H5; split; intros ? x; specialize (H5 x); specialize (H x); intuition.
  rewrite H5; clear H5.
  clear Heqn0 Heql0.
  revert n0 l0 n l H0 lo hi H H1 H2 H3 H4; induction s; simpl; intros.
  inv H0. split; [|split]; auto.
  destruct lo; simpl; auto.  destruct hi; simpl in *.
  apply  searchtree_proper_bounds in H. simpl in H.
  clear - H H1.
  eapply HdRel_le_lt; eauto.
  destruct l; try contradiction. constructor.
  split; auto.
  intro; intuition etac.
  inv H.
  remember (filter_aux f s2 n0 l0) as nl2; symmetry in Heqnl2.
  destruct nl2 as (n2,l2).
  specialize (IHs2 _ _ _ _ Heqnl2 _ _ H12 H1 H2 H3 H4).
  destruct IHs2 as [? [? [? ?]]].
  remember (f t) as ft; destruct ft.
  specialize (IHs1 _ _ _ _ H0 _ _ H9).
  destruct IHs1 as [? [? [? ?]]].
  simpl. constructor. right. reflexivity.
  rewrite nat_of_P_succ_morphism.
  simpl; omega.
  constructor; auto. auto.
  split; [|split]; auto.
  split; auto.
  intros COMPAT x; rewrite <-(H13 COMPAT x);  clear  H13.
  specialize (H7 COMPAT x); clear - COMPAT Heqft H7; intuition etac. inv H1; auto. inv H3; auto.
  rewrite (COMPAT _ _ H4) in *. auto.
  destruct (H0 H4); auto. destruct H1; auto.

  specialize (IHs1 _ _ _ _ H0 _ _ H9).
  destruct IHs1 as [? [? [? ?]]].
  simpl. simpl in H. clear - H.
  apply HdRel_lt_le; auto.
  omega.
  auto.
  auto.
  split; [|split]; auto.
  split; auto.
  intros COMPAT x; rewrite <- (H13 COMPAT x); clear H13.
  specialize (H7 COMPAT x).
  intuition.
  inv H7; auto.
  rewrite (COMPAT _ _ H22) in *. rewrite <- Heqft in H17; inv H17.
Qed.

Definition filter' (f: key -> bool) (s: tree) : tree :=
  let nl := filter_aux f s 1%positive nil in fst (treeify_g (fst nl) (snd nl)).

Lemma filter_valid: forall f s, valid s -> valid (filter' f s).
Proof.
 unfold filter';  intros.
  simpl.
  case_eq (filter_aux f s 1 nil); intros n l ?.
  destruct H.
  destruct (filter_aux_lemma _ _ _ _ _ _ H H0) as [? [? [? _]]].
  assert (S (length l) >= nat_of_P n) by omega.
  destruct (treeify'_g_is_searchtree n l None); simpl; auto.
  generalize (treeify'_g_is_redblack _ _ H5); intro.
  split; auto.
  destruct (hd_error (snd (treeify_g n l))); auto.
  apply searchtree_expand_right with t; simpl; auto.
  eauto.
Qed.


Lemma linear_inter_aux_lemma:
  forall s1 s2 lo hi,
    searchtree lo hi s1 -> searchtree lo hi s2 ->
   forall n l n0 l0,
    (n,l) = (linear_inter_aux (s1, s2) (n0,l0)) ->
    match hi, l0 with None, _::_ => False | _,_ => True end ->
    HdRel' Kle hi l0 ->
    Sorted K.lt l0 ->
    S (length l0) = nat_of_P n0 ->
    (Sorted K.lt l /\ S (length l) = nat_of_P n
     /\ forall x, InA K.eq x l <-> interp s1 x /\ interp s2 x \/ InA K.eq x l0).
Proof.
intros s1 s2.
assert (exists N, size s1 + size s2 < N).
exists (S (size s1 + size s2)); omega.
destruct H as [N ?].
revert s1 s2 H; induction N; intros.
elimtype False; omega.
rewrite linear_inter_aux_equation in H2.
simpl in H2.
generalize(shape_rgopher s1); intro.
generalize(shape_rgopher s2); intro.
remember (rgopher s1) as s1'.
remember (rgopher s2) as s2'.
destruct s1'.
inv H2.
split; auto.
split; auto.
intuition.
clear - Heqs1' H2.
generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intuition etac.
destruct s1'2; try contradiction.
destruct s2'.
inv H2.
split; auto.
split; auto.
intuition.
clear - Heqs2' H10.
generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intuition etac.
destruct s2'2; try contradiction.
clear H7 H8.
do_compare t t0.
(* case t0=t1 *)
specialize (IHN s1'1 s2'1).
spec IHN.
  generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; intro.
  generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; intro.
  omega.
rewrite searchtree_rgopher in H0,H1.
rewrite <- Heqs1' in H0.  rewrite <- Heqs2' in H1.
generalize (searchtree_mid_congr _ c _ _ _ _ _ _ H0 e); intro.
clear H0.
inv H7; inv H1.
specialize (IHN _ _ H11 H10).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; simpl; auto; clear IHN.
constructor. right; rewrite e; reflexivity.
constructor; auto.
destruct hi; destruct l0; try contradiction; try solve [ constructor].
simpl in H4.
apply searchtree_proper_bounds in H14.
apply HdRel_le_lt with t1; auto.
rewrite e;  auto.
rewrite nat_of_P_succ_morphism.
omega.
split; auto.
split; auto.
intro x; specialize (H7 x).
rewrite H7.
clear - Heqs1' Heqs2' e.
generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
intuition.
inv H4; auto.
left; split. apply H1; constructor 1; auto. apply H; constructor 1; rewrite <- e; auto.
inv H4.
right; constructor 1; auto.
inv H2.
right; constructor 1. rewrite e; auto.
left; auto.
inv H9. inv H10.
(* case t<t0 *)
rewrite Heqs1' in H2.
specialize (IHN (rgopher s1) s2'1).
spec IHN.
rewrite size_rgopher. generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; intros; omega.
specialize (IHN lo (Some t0)).
spec IHN.
  rewrite searchtree_rgopher in H0.
  rewrite <- Heqs1' in H0|-*. inv H0; constructor; auto. constructor. simpl. auto.
spec IHN.
  rewrite searchtree_rgopher in H1.
   rewrite <- Heqs2' in H1. inv H1; auto.
destruct (IHN _ _ _ _ H2) as [? [? ?]]; auto.
 simpl.
 assert (ltopt (Some t0) hi).
   clear - Heqs2' H1. rewrite searchtree_rgopher in H1. rewrite <- Heqs2' in H1.
   inv H1. apply searchtree_proper_bounds in H7; auto.
 clear - H7 H4 H3.
 destruct hi; destruct l0; try contradiction; try solve [constructor].
 simpl in H4.
 apply HdRel_lt_le.
 eapply HdRel_le_lt; eauto.
 split; auto.
 split; auto.
 intro x; specialize (H9 x).
 rewrite H9.
 generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
 generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
 rewrite searchtree_rgopher in H0. rewrite <- Heqs1' in H0.
 rewrite searchtree_rgopher in H1. rewrite <- Heqs2' in H1.
 clear - H10 H11 l1 H0 H1.
 intuition. left.
 split; auto. inv H4; auto. inv H6.
 rewrite <-  H12 in l1; rewrite <- H11 in l1;  contradiction (lt_irrefl l1).
 inv H0. destruct (interp_range _ _ _ _ H9 H11). simpl in H0. rewrite H12 in H0.
 contradiction (lt_irrefl (lt_trans l1 H0)). inv H11. inv H12.
 (* case t0<t *)
rewrite Heqs2' in H2.
specialize (IHN s1'1 (rgopher s2)).
spec IHN.
rewrite size_rgopher. generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; intros; omega.
specialize (IHN lo (Some t)).
spec IHN.
  rewrite searchtree_rgopher in H0.
   rewrite <- Heqs1' in H0. inv H0; auto.
spec IHN.
  rewrite searchtree_rgopher in H1.
  rewrite <- Heqs2' in H1|-*. inv H1; constructor; auto. constructor. simpl. auto.
destruct (IHN _ _ _ _ H2) as [? [? ?]]; auto.
 simpl.
 assert (ltopt (Some t) hi).
   clear - Heqs1' H0. rewrite searchtree_rgopher in H0. rewrite <- Heqs1' in H0.
   inv H0. apply searchtree_proper_bounds in H7; auto.
 clear - H7 H4 H3.
 destruct hi; destruct l0; try contradiction; try solve [constructor].
 simpl in H4.
 apply HdRel_lt_le.
 eapply HdRel_le_lt; eauto.
 split; auto.
 split; auto.
 intro x; specialize (H9 x).
 rewrite H9.
 generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
 generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
 rewrite searchtree_rgopher in H0. rewrite <- Heqs1' in H0.
 rewrite searchtree_rgopher in H1. rewrite <- Heqs2' in H1.
 clear - H10 H11 l1 H0 H1.
 intuition. left.
 split; auto. inv H6; auto. inv H4.
 rewrite <-  H12 in l1; rewrite <- H11 in l1;  contradiction (lt_irrefl l1).
 inv H1. destruct (interp_range _ _ _ _ H9 H11). simpl in H1. rewrite H12 in H1.
 contradiction (lt_irrefl (lt_trans l1 H1)). inv H11. inv H12.
Qed.

Lemma linear_inter_valid: forall s1 s2 : tree,
  valid s1 -> valid s2 -> valid (linear_inter s1 s2).
Proof.
intros s1 s2 [? ?] [? ?].
unfold linear_inter.
remember (linear_inter_aux (s1, s2) (1%positive, nil)) as l.
destruct l as [n l].
  destruct (linear_inter_aux_lemma _ _ _ _ H H1 _ _ _ _ Heql) as [? [? ?]]; simpl; auto.
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  split; auto.
  eapply searchtree_None; eauto.
  econstructor; eapply treeify'_g_is_redblack; auto.
  omega.
Qed.

Lemma linear_union_aux_lemma:
  forall s1 s2 lo hi,
    searchtree lo hi s1 -> searchtree lo hi s2 ->
   forall n l n0 l0,
    (n,l) = (linear_union_aux (s1, s2) (n0,l0)) ->
    match hi, l0 with None, _::_ => False | _,_ => True end ->
    HdRel' Kle hi l0 ->
    Sorted K.lt l0 ->
    S (length l0) = nat_of_P n0 ->
    (Sorted K.lt l /\ S (length l) = nat_of_P n
     /\ forall x, InA K.eq x l <-> interp s1 x \/ interp s2 x \/ InA K.eq x l0).
Proof.
pose (t:=tt).
intros s1 s2.
assert (exists N, size s1 + size s2 < N).
exists (S (size s1 + size s2)); omega.
destruct H as [N ?].
revert s1 s2 H; induction N; intros.
elimtype False; omega.
rewrite linear_union_aux_equation in H2.
simpl in H2.
generalize(shape_rgopher s1); intro.
generalize(shape_rgopher s2); intro.
remember (rgopher s1) as s1'.
remember (rgopher s2) as s2'.
destruct s1'.
assert (s1=EE) by (destruct s1; simpl in Heqs1'; try destruct (rgopher s1_2); inv Heqs1'; auto).
subst s1; clear Heqs1'.
destruct s2'.
assert (s2=EE) by (destruct s2; simpl in Heqs2'; try destruct (rgopher s2_2); inv Heqs2'; auto).
subst s2; clear Heqs2'.
inv H2.
split; auto.
split; auto.
intuition etac.
clear H7.
destruct s2'2; try contradiction; clear H8.
specialize (IHN EE s2'1).
spec IHN.
  generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; omega.
rewrite searchtree_rgopher in H1.
rewrite <- Heqs2' in H1; inv H1.
assert (searchtree lo (Some t0) EE). constructor. eapply searchtree_proper_bounds; eauto.
specialize (IHN _ _ H1 H11).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; clear IHN; simpl; auto.
constructor. right; reflexivity.
constructor; auto.
inv H14. destruct hi; destruct l0; try contradiction; try solve [constructor].
simpl in H4.
eapply HdRel_le_lt; eauto.
rewrite nat_of_P_succ_morphism. omega.
split; auto.
split; auto.
intro x; specialize (H9 x).
rewrite H9; clear H9.
intuition.
right; left. rewrite <- interp_rgopher; rewrite <- Heqs2'.
constructor 2; auto.
right.
inv H9; auto.
left. rewrite <- interp_rgopher; rewrite <- Heqs2'. constructor 1; auto.
right.
rewrite <- interp_rgopher in H9; rewrite <- Heqs2' in H9; inv H9.
right; constructor 1; auto.
left; auto. inv H17.

destruct s1'2; try contradiction; clear H7.
destruct s2'.
clear H8.
assert (s2=EE) by (destruct s2; simpl in Heqs2'; try destruct (rgopher s2_2); inv Heqs2'; auto).
subst s2; clear Heqs2'.
specialize (IHN s1'1 EE).
spec IHN.
  generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; omega.
rewrite searchtree_rgopher in H0.
rewrite <- Heqs1' in H0; inv H0.
assert (searchtree lo (Some t0) EE). constructor. eapply searchtree_proper_bounds; eauto.
specialize (IHN _ _ H11 H0).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; clear IHN; simpl; auto.
constructor. right; reflexivity.
constructor; auto.
inv H14. destruct hi; destruct l0; try contradiction; try solve [constructor].
simpl in H4.
eapply HdRel_le_lt; eauto.
rewrite nat_of_P_succ_morphism. omega.
split; auto.
split; auto.
intro x; specialize (H9 x).
rewrite H9; clear H9.
intuition.
left. rewrite <- interp_rgopher; rewrite <- Heqs1'.
constructor 2; auto.
inv H9; auto.
left.
rewrite <- interp_rgopher; rewrite <- Heqs1'. constructor 1; auto.
rewrite <- interp_rgopher in H10; rewrite <- Heqs1' in H10; inv H10; auto.
destruct s2'2; try contradiction; clear H8.
do_compare t0 t1.
(* t0=t1 case *)
specialize (IHN s1'1 s2'1).
spec IHN.
  generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; intro;
  generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; intro; omega.
rewrite searchtree_rgopher in H0, H1.
rewrite <- Heqs1' in H0; rewrite <- Heqs2' in H1.
eapply searchtree_mid_congr with (c':=c) in H0; try apply e.
inv H0; inv H1.
specialize (IHN _ _ H11 H10).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; clear IHN; simpl; auto.
constructor. right; auto.
constructor; auto.
destruct hi; destruct l0; try contradiction; try solve [constructor].
simpl in H4.
apply HdRel_le_lt with t2; auto.
inv H14.
rewrite e; auto.
rewrite nat_of_P_succ_morphism. omega.
split; auto.
split; auto.
intro x; specialize (H7 x); rewrite H7; clear H7.
generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
clear - e H7 H8; intuition etac.
inv H3; auto.
inv H3; auto; etac. inv H4; auto; etac.
 right; right. constructor 1; rewrite e; auto.
(* t0<t1 case *)
rewrite Heqs1' in H2.
specialize (IHN (rgopher s1) s2'1).
spec IHN.
 rewrite size_rgopher. generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; omega.
rewrite searchtree_rgopher in H0, H1.
rewrite <- Heqs2' in H1.
inv H1.
assert (searchtree lo (Some t1) s1).
rewrite searchtree_rgopher. rewrite <- Heqs1' in H0|-*.
inv H0; constructor; auto.
constructor; auto.
rewrite searchtree_rgopher in H1.
specialize (IHN _ _ H1 H11).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; clear IHN; simpl; auto.
constructor; auto. right; reflexivity.
constructor; auto.
destruct hi; destruct l0; try contradiction; try solve [constructor].
simpl in H4.
apply HdRel_le_lt with t2; auto.
inv H14; auto.
rewrite nat_of_P_succ_morphism. omega.
split; auto.
split; auto.
intro x; rewrite (H9 x); clear H9.
generalize (interp_rgopher s1 x); intro.
generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
clear - l1 H9 H10.
intuition etac; intuition.
inv H3; auto. inv H4; auto; etac.
(* t1<t0 case *)
rewrite Heqs2' in H2.
specialize (IHN s1'1 (rgopher s2)).
spec IHN.
 rewrite size_rgopher. generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; omega.
rewrite searchtree_rgopher in H0, H1.
rewrite <- Heqs1' in H0.
inv H0.
assert (searchtree lo (Some t0) s2).
rewrite searchtree_rgopher. rewrite <- Heqs2' in H1|-*.
inv H1; constructor; auto.
constructor; auto.
rewrite searchtree_rgopher in H0.
specialize (IHN _ _ H11 H0).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; clear IHN; simpl; auto.
constructor; auto. right; reflexivity.
constructor; auto.
destruct hi; destruct l0; try contradiction; try solve [constructor].
simpl in H4.
apply HdRel_le_lt with t2; auto.
inv H14; auto.
rewrite nat_of_P_succ_morphism. omega.
split; auto.
split; auto.
intro x; rewrite (H9 x); clear H9.
generalize (interp_rgopher s2 x); intro.
generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
clear - l1 H9 H10.
intuition etac. inv H3; auto.
inv H3; auto; etac.
Qed.

Lemma linear_union_valid: forall s1 s2 : tree,
  valid s1 -> valid s2 -> valid (linear_union s1 s2).
Proof.
intros s1 s2 [? ?] [? ?].
unfold linear_union.
remember (linear_union_aux (s1, s2) (1%positive, nil)) as l.
destruct l as [n l].
  destruct (linear_union_aux_lemma _ _ _ _ H H1 _ _ _ _ Heql) as [? [? ?]]; simpl; auto.
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  split; auto.
  eapply searchtree_None; eauto.
  econstructor; eapply treeify'_g_is_redblack; auto.
  omega.
Qed.

Lemma linear_diff_aux_lemma:
  forall s1 s2 lo hi,
    searchtree lo hi s1 -> searchtree lo hi s2 ->
   forall n l n0 l0,
    (n,l) = (linear_diff_aux (s1, s2) (n0,l0)) ->
    match hi, l0 with None, _::_ => False | _,_ => True end ->
    HdRel' Kle hi l0 ->
    Sorted K.lt l0 ->
    S (length l0) = nat_of_P n0 ->
    (Sorted K.lt l /\ S (length l) = nat_of_P n
     /\ forall x, InA K.eq x l <-> interp s1 x /\ ~interp s2 x \/ InA K.eq x l0).
Proof.
pose (t:=tt).
intros s1 s2.
assert (exists N, size s1 + size s2 < N).
exists (S (size s1 + size s2)); omega.
destruct H as [N ?].
revert s1 s2 H; induction N; intros.
elimtype False; omega.
rewrite linear_diff_aux_equation in H2.
simpl in H2.
generalize(shape_rgopher s1); intro.
generalize(shape_rgopher s2); intro.
remember (rgopher s1) as s1'.
remember (rgopher s2) as s2'.
destruct s1'.
assert (s1=EE) by (destruct s1; simpl in Heqs1'; try destruct (rgopher s1_2); inv Heqs1'; auto).
subst s1; clear Heqs1'.
inv H2.
split; auto.
split; auto.
intuition etac.
destruct s1'2; try contradiction; clear H7.
destruct s2'.
assert (s2=EE) by (destruct s2; simpl in Heqs2'; try destruct (rgopher s2_2); inv Heqs2'; auto).
subst s2; clear Heqs2'.
clear H8.
specialize (IHN s1'1 EE).
spec IHN.
  generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; intro. omega.
rewrite searchtree_rgopher in H0.
rewrite <- Heqs1' in H0.  inv H0.
assert (searchtree lo (Some t0) EE) by (apply searchtree_proper_bounds in H11; constructor; auto).
specialize (IHN _ _ H11 H0).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; simpl; auto; clear IHN.
constructor; auto. right; reflexivity.
constructor; auto.
destruct hi; destruct l0; try contradiction; try solve [ constructor].
simpl in H4.
apply HdRel_le_lt with t1; auto. inv H14; auto.
rewrite nat_of_P_succ_morphism.
omega.
split; auto.
split; auto.
intro x; rewrite (H9 x); clear H9.
generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
clear - H9. intuition etac. inv H2; auto. left; intuition etac.
inv H2; intuition etac.
destruct s2'2; try contradiction; clear H8.
do_compare t0 t1.
(* case t0=t1 *)
specialize (IHN s1'1 s2'1).
spec IHN.
  generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; intro.
  generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; intro.
  omega.
rewrite searchtree_rgopher in H0,H1.
rewrite <- Heqs1' in H0.  rewrite <- Heqs2' in H1.
generalize (searchtree_mid_congr _ c _ _ _ _ _ _ H0 e); intro.
clear H0.
inv H7; inv H1.
specialize (IHN _ _ H11 H10).
destruct (IHN _ _ _ _ H2) as [? [? ?]]; simpl; auto; clear IHN.
destruct hi; destruct l0; try contradiction; try solve [ constructor].
simpl in H4.
apply HdRel_lt_le. apply HdRel_le_lt with t2; auto. inv H14; auto.
split; auto.
split; auto.
intro x; rewrite (H7 x); clear H7.
clear - Heqs1' Heqs2' e H11 H10.
generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
intuition etac. left; split; auto. intro. apply H3 in H4. inv H4; intuition etac.
destruct (interp_range _ _ _ _ H11 H0). simpl in H6. rewrite H13 in H6. apply (lt_irrefl  H6).
inv H4. elimtype False; apply H5; apply H. constructor 1. rewrite H12; auto.
left; split; auto. inv H12.
(* case t0<t1 *)
rewrite Heqs1' in H2.
specialize (IHN (rgopher s1) s2'1).
spec IHN.
rewrite size_rgopher. generalize (size_rgopher s2); rewrite <- Heqs2'; simpl; intros; omega.
specialize (IHN lo (Some t1)).
spec IHN.
  rewrite searchtree_rgopher in H0.
  rewrite <- Heqs1' in H0|-*. inv H0; constructor; auto. constructor. simpl. auto.
spec IHN.
  rewrite searchtree_rgopher in H1.
   rewrite <- Heqs2' in H1. inv H1; auto.
destruct (IHN _ _ _ _ H2) as [? [? ?]]; simpl; auto; clear IHN.
 destruct hi; destruct l0; try contradiction; try solve [constructor].
simpl in H4.
apply HdRel_lt_le; apply HdRel_le_lt with t2; auto.
rewrite searchtree_rgopher in H1. rewrite <- Heqs2' in H1. inv H1. inv H14; auto.
split; auto.
split; auto.
 intro x; rewrite (H9 x); clear H9.
 generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
 generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
 rewrite searchtree_rgopher in H0. rewrite <- Heqs1' in H0.
 rewrite searchtree_rgopher in H1. rewrite <- Heqs2' in H1.
 clear - H10 H9 l1 H0 H1.
 intuition. clear H5. inv H1. inv H3.
  left; split; auto. intro. apply H2 in H1. inv H1. rewrite <- H11 in l1; rewrite <- H12 in l1; apply (lt_irrefl l1).
  auto. inv H12.
  left; split; auto. intro. apply H2 in H1. inv H1. inv H0.
  destruct (interp_range _ _ _ _ H8 H11). simpl in H1. rewrite H12 in H1.
  apply (lt_irrefl (lt_trans H1 l1)). auto. inv H12. inv H11.
 (* case t1<t0 *)
rewrite Heqs2' in H2.
specialize (IHN s1'1 (rgopher s2)).
spec IHN.
rewrite size_rgopher. generalize (size_rgopher s1); rewrite <- Heqs1'; simpl; intros; omega.
specialize (IHN lo (Some t0)).
spec IHN.
  rewrite searchtree_rgopher in H0.
   rewrite <- Heqs1' in H0. inv H0; auto.
spec IHN.
  rewrite searchtree_rgopher in H1.
  rewrite <- Heqs2' in H1|-*. inv H1; constructor; auto. constructor. simpl. auto.
destruct (IHN _ _ _ _ H2) as [? [? ?]]; simpl; auto; clear IHN.
constructor; auto. right; reflexivity. constructor; auto.
 destruct hi; destruct l0; try contradiction; try solve [constructor].
 simpl in H4. apply HdRel_le_lt with t2; auto.
 rewrite searchtree_rgopher in H0. rewrite <- Heqs1' in H0. inv H0. inv H14; auto.
rewrite nat_of_P_succ_morphism; omega.
 split; auto.
 split; auto.
 intro x; rewrite (H9 x); clear H9.
 generalize (interp_rgopher s2 x); rewrite <- Heqs2'; intro.
 generalize (interp_rgopher s1 x); rewrite <- Heqs1'; intro.
 rewrite searchtree_rgopher in H0. rewrite <- Heqs1' in H0.
 rewrite searchtree_rgopher in H1. rewrite <- Heqs2' in H1.
 clear - H10 H9 l1 H0 H1.
 intuition. inv H6.  left.
 split; auto. intro. apply H2 in H5. inv H5. rewrite <- H7 in l1; rewrite <- H12 in l1; apply (lt_irrefl l1).
 inv H1. destruct (interp_range _ _ _ _ H10 H12). simpl in H5.
 rewrite <- H5 in l1; rewrite <- H7 in l1; apply (lt_irrefl l1). inv H12.
 auto.
 inv H6. right; auto. left; split; auto. inv H12.
Qed.

Lemma linear_diff_valid: forall s1 s2 : tree,
  valid s1 -> valid s2 -> valid (linear_diff s1 s2).
Proof.
intros s1 s2 [? ?] [? ?].
unfold linear_diff.
remember (linear_diff_aux (s1, s2) (1%positive, nil)) as l.
destruct l as [n l].
  destruct (linear_diff_aux_lemma _ _ _ _ H H1 _ _ _ _ Heql) as [? [? ?]]; simpl; auto.
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  split; auto.
  eapply searchtree_None; eauto.
  econstructor; eapply treeify'_g_is_redblack; auto.
  omega.
Qed.

Fixpoint partition_aux (f: key -> bool) (s: tree)
   (nl1 nl2: positive *  list key) :  (positive * list key) * (positive * list key) :=
 match s with
 | T _ sl k sr => match partition_aux f sr nl1 nl2
    with (nl1', nl2') =>
                    if f k then partition_aux f sl (Psucc (fst nl1'), k:: snd nl1') nl2'
                            else partition_aux f sl nl1' (Psucc (fst nl2'), k:: snd nl2')
    end
 | EE => (nl1,nl2)
 end.

Lemma partition_aux_lemma1:
   forall f s lo hi, searchtree lo hi s ->
     forall nl1' nl2' nl1 nl2,
           (nl1',nl2') = partition_aux f s nl1 nl2 ->
      (hi=None -> snd nl1 = nil /\ snd nl2 = nil) ->
     HdRel' Kle hi (snd nl1) ->
     HdRel' Kle hi (snd nl2) ->
     Sorted K.lt (snd nl1) ->
     Sorted K.lt (snd nl2) ->
     S (length (snd nl1)) = nat_of_P (fst nl1) ->
     S (length (snd nl2)) = nat_of_P (fst nl2) ->
     HdRel' K.lt lo (snd nl1') /\  HdRel' K.lt lo (snd nl2') /\
     Sorted K.lt (snd nl1') /\ Sorted K.lt (snd nl2') /\
     S (length (snd nl1')) = nat_of_P (fst nl1') /\
     S (length (snd nl2')) = nat_of_P (fst nl2').
Proof.
induction 1; intros.
simpl in H0. inv H0. intuition.
destruct lo; simpl; auto. destruct hi. apply HdRel_le_lt with t0; auto. destruct H1; auto. rewrite H0; simpl; auto.
 destruct lo; simpl; auto. destruct hi. apply HdRel_le_lt with t0; auto. destruct H1; auto. rewrite H1; simpl; auto.
simpl in H1.
remember (partition_aux f tr nl1 nl2) as zz; destruct zz as [nl1'' nl2''].
destruct (IHsearchtree2 _ _ _ _ Heqzz) as [? [? [? [? [? ?]]]]]; simpl; auto; clear IHsearchtree2.
remember (f k) as b; destruct b;
destruct (IHsearchtree1 _ _ _ _ H1) as [? [? [? [? [? ?]]]]]; simpl; auto; clear IHsearchtree1.
intro Hx; inv Hx.
constructor; auto. right; reflexivity.
apply HdRel_lt_le; auto.
rewrite nat_of_P_succ_morphism; omega.
split; auto.
intro Hx; inv Hx.
simpl in *.
apply HdRel_lt_le. auto.
constructor; auto. right; reflexivity.
rewrite nat_of_P_succ_morphism; omega.
split; auto.
Qed.

Definition partition'  (f: key -> bool) (s: tree) : (tree*tree) :=
  match partition_aux f s (1%positive, nil) (1%positive,  nil)
   with ((n1,l1),(n2,l2)) => (fst (treeify_g n1 l1), fst (treeify_g n2 l2))
  end.

Lemma partition_valid1: forall f s, valid s -> valid (fst (partition' f s)).
Proof.
  unfold partition'.
  intros f s [?H ?H].
  remember (partition_aux f s (1%positive, nil) (1%positive, nil)) as p.
  destruct p as [[n1 l1] [n2 l2]].
  simpl in *.
  destruct (partition_aux_lemma1 f _ _ _ H _ _ _ _ Heqp)
  as [? [? [? [? [? ?]]]]]; simpl; auto.
  simpl in *.
  destruct (treeify'_g_is_searchtree n1 l1 None) as [? [? ?]]; simpl; auto.
  omega.
  split; auto.
  eapply searchtree_None; eauto.
  econstructor; eapply treeify'_g_is_redblack; auto.
  omega.
Qed.

Lemma partition_valid2: forall f s, valid s -> valid (snd (partition' f s)).
Proof.
  unfold partition'.
  intros f s [?H ?H].
  remember (partition_aux f s (1%positive, nil) (1%positive, nil)) as p.
  destruct p as [[n1 l1] [n2 l2]].
  simpl in *.
  destruct (partition_aux_lemma1 f _ _ _ H _ _ _ _ Heqp)
  as [? [? [? [? [? ?]]]]]; simpl; auto.
  simpl in *.
  destruct (treeify'_g_is_searchtree n2 l2 None) as [? [? ?]]; simpl; auto.
  omega.
  split; auto.
  eapply searchtree_None; eauto.
  econstructor; eapply treeify'_g_is_redblack; auto.
  omega.
 Qed.


  Lemma fold'_app: forall s d ar,
                  fold' (list key) (@cons key) s (app d ar) =
                      app (fold' (list key) (@cons key) s d) ar.
 induction s; intros; auto.
  simpl fold'.
  remember (fold' (list key) (@cons key)) as g.
  rewrite <- Heqg.
  rewrite <- IHs2.
  f_equal. simpl.
  f_equal.
  apply IHs1.
  Qed.

  Lemma fold'_spec:  forall s (A : Type) (i : A) (f : key -> A -> A),
      fold' _ f s i = List.fold_left (fun a e => f e a) (List.rev (fold' _ (@cons _) s nil)) i.
 Proof.
  induction s; intros; auto.
  simpl. rewrite IHs2. rewrite IHs1.
 remember (fold' (list key) (@cons key) s1 (@nil key)) as l1.
  change (cons t l1) with (app nil (cons t l1)).
  rewrite fold'_app.
 remember (fold' (list key) (@cons key) s2 (@nil key)) as l2.
  rewrite List.rev_app_distr.
 rewrite List.fold_left_app.
   repeat rewrite <- IHs2.
  f_equal.
  simpl.
 rewrite List.fold_left_app.
 rewrite <- IHs1.
  simpl. auto.
 Qed.


Lemma mem_add_valid:
   forall x s, valid s -> forall s', Some s' = mem_add' x s -> valid s'.
Proof.
 intros x s V s' H.
 symmetry in H.
  unfold mem_add' in H.
  revert H; case_eq (ins' x s); intros; inv H0.
  assert (ins x s = t).
  clear V.
  revert t H; induction s; simpl; intros. inv H; auto.
  destruct (K.compare x t); try inv H.
  revert H1; case_eq (ins' x s1); intros; inv H1.
  apply IHs1 in H. rewrite H. auto.
  revert H1; case_eq (ins' x s2); intros; inv H1.
  apply IHs2 in H. rewrite H. auto.
  subst.  apply insert_valid; auto.
 Qed.


  Lemma InA_rev_fold'_range:
     forall k s lo hi,
      searchtree lo hi s ->
       SetoidList.InA E.eq k (List.rev (fold' (list key) (@cons _) s nil)) ->
       (ltopt lo (Some k) /\ ltopt (Some k) hi).
    Proof.
    induction 1; simpl; intros. inv H0.
    change
     (SetoidList.InA E.eq k
       (List.rev
          (fold' (list key) (@cons _) tr (nil++(k0 ::nil)++ fold' (list key) (@cons _) tl nil)%list)))
   in H1.
   repeat rewrite fold'_app in H1.
   repeat rewrite List.rev_app_distr in H1.
  repeat  rewrite -> SetoidList.InA_app_iff in H1 by apply E.eq_equiv.
  apply searchtree_proper_bounds in H.
  apply searchtree_proper_bounds in H0.
  destruct H1 as [[?|?]|?].
  destruct (IHsearchtree1 H1).
  clear - H H0 H2 H3; destruct lo, hi; simpl in *; intuition.
  apply lt_trans with k0; auto.
  apply lt_trans with k0; auto.
  inv H1.
  clear - H H0 H3; destruct lo, hi; simpl in *; intuition; rewrite H3; auto.
  inv H3.
  destruct (IHsearchtree2 H1).
  clear - H H0 H2 H3; destruct lo, hi; simpl in *; intuition.
  apply lt_trans with k0; auto.
  apply lt_trans with k0; auto.
  Qed.


Lemma tree_similar_lemma':
       forall c c' k k' s s' lo hi lo' hi',
          searchtree lo hi (T c EE k s) ->
          searchtree lo' hi' (T c' EE k' s') ->
          (forall x : key,
            interp (T c EE k s) x <-> interp (T c' EE k' s') x) ->
          K.eq k k' /\ (forall x, interp s x -> interp s' x).
     Proof.
      intros.
      inv H.
      rename H6 into H8; generalize (searchtree_proper_bounds _ _ _ H8); intro H10.
      generalize (searchtree_proper_bounds _ _ _ H9); intro H11.
      inv H0.
      rename H5 into H7.
      generalize (searchtree_proper_bounds _ _ _ H7); intro H13.
      generalize (searchtree_proper_bounds _ _ _ H12); intro H14.
      destruct (H1 k).
      assert (interp (T c' EE k' s') k)  by (apply H; constructor 1; reflexivity).
      inv H2. split; auto.
      intros x H20; destruct (H1 x).
      do_compare k x.
      destruct (interp_range _ _ _ _ H9 H20). simpl in H4. rewrite e in H4; contradiction (lt_irrefl H4).
      assert (interp (T c' EE k' s') x). apply H2; constructor 3; auto.
        inv H4. rewrite <- H16 in H19; rewrite H19 in l; contradiction (lt_irrefl l).
         inv H19. auto.
      destruct (interp_range _ _ _ _ H9 H20). simpl in H4.
          contradiction (lt_irrefl (lt_trans H4 l)).
       inv H16.
       destruct (interp_range _ _ _ _ H12 H16). simpl in H2.
       elimtype False.
       destruct (H1 k') as [_ ?].
       absurd (interp (T c EE k s) k').
        intro Hx; inv Hx.  rewrite H19 in H2. contradiction (lt_irrefl  H2). inv H19.
       destruct (interp_range _ _ _ _ H9 H19). simpl in H7.
          contradiction (lt_irrefl (lt_trans H5 H2)).
        apply H4.
       constructor 1; reflexivity.
      Qed.

Lemma tree_similar_lemma:
       forall c c' k k' s s' lo hi lo' hi',
          searchtree lo hi (T c EE k s) ->
          searchtree lo' hi' (T c' EE k' s') ->
          (forall x : key,
            interp (T c EE k s) x <-> interp (T c' EE k' s') x) ->
          K.eq k k' /\ (forall x, interp s x <-> interp s' x).
 Proof.
   intros.
   destruct (tree_similar_lemma' _ _ _ _ _ _ _ _ _ _ H H0 H1).
   destruct (tree_similar_lemma' _ _ _ _ _ _ _ _ _ _ H0 H).
   intuition; destruct (H1 x); auto.
   split; auto; intuition.
 Qed.

Definition union' (s1 s2: tree) : tree :=
   match compare_height s1 s1 s2 s2 with
      | Lt => fold' _ insert s1 s2
      | Gt => fold' _ insert s2 s1
      | Eq => linear_union s1 s2
    end.


Lemma fold'_searchtree:
  forall (f: key -> tree -> tree)
      (Hf: forall k s, searchtree None None s -> searchtree None None (f k s))
      s1 s2,
      searchtree None None s1 -> searchtree None None s2 ->
      searchtree None None (fold' _ f s1 s2).
Proof.
 induction s1; simpl; intros; auto.
  inv H.
  apply IHs1_2; auto.
  eapply searchtree_None; eauto.
  apply Hf; auto.
  apply IHs1_1; auto.
  eapply searchtree_None; eauto.
Qed.


Lemma fold'_valid: forall (f: key -> tree -> tree)
                  (f_valid: forall k s, valid s -> valid (f k s))
                  s1 s2,
           valid s1 -> valid s2 -> valid (fold' _ f s1 s2).
Proof.
intros.
destruct H.
remember Red as c. clear Heqc.
revert c H H1 s2 H0; induction s1; simpl; intros; auto.
inv H. destruct H1 as [n ?].
inv H.
eapply IHs1_2; eauto.
eapply searchtree_None; eauto.
apply f_valid.
eapply IHs1_1; eauto.
eapply searchtree_None; eauto.
eapply IHs1_2; eauto.
eapply searchtree_None; eauto.
apply f_valid.
eapply IHs1_1; eauto.
eapply searchtree_None; eauto.
Qed.

Lemma union_valid: forall s1 s2, valid s1 -> valid s2 -> valid (union' s1 s2).
Proof.
unfold union'; intros.
destruct (compare_height s1 s1 s2 s2).
apply linear_union_valid; auto.
apply fold'_valid; auto; apply insert_valid.
apply fold'_valid; auto; apply insert_valid.
Qed.

Definition diff' (s1 s2: tree) : tree :=
   match compare_height s1 s1 s2 s2 with
      | Lt => filter' (fun k => negb (member k s2)) s1
      | Gt => fold' _ delete s2 s1
      | Eq => linear_diff s1 s2
    end.

Lemma diff_valid:  forall s1 s2, valid s1 -> valid s2 -> valid (diff' s1 s2).
Proof.
unfold diff'; intros.
destruct (compare_height s1 s1 s2 s2).
apply linear_diff_valid; auto.
apply filter_valid; auto.
apply fold'_valid; auto; apply remove_valid.
Qed.

Definition inter' (s1 s2: tree) : tree :=
   match compare_height s1 s1 s2 s2 with
      | Lt => filter' (fun k => member k s2) s1
      | Gt => filter' (fun k => member k s1) s2
      | Eq => linear_inter s1 s2
    end.

Lemma inter_valid:  forall s1 s2, valid s1 -> valid s2 -> valid (inter' s1 s2).
Proof.
unfold inter'; intros.
destruct (compare_height s1 s1 s2 s2).
apply linear_inter_valid; auto.
apply filter_valid; auto.
apply filter_valid; auto.
Qed.


Fixpoint elements' (x: tree) (base: list key) : list key :=
  match x with
  | EE => base
  | T _ t1 k t2 => elements' t1 (cons k (elements' t2 base))
 end.

Lemma elements'_interp : forall s x l,
     SetoidList.InA E.eq x (elements' s l) <-> interp s x \/ InA E.eq x l.
  Proof.
    intros.
    revert l; induction s; simpl; intros; intuition etac.
    rewrite IHs1 in H.
    destruct H. left; constructor 2; auto.
    inv H. left; constructor 1; auto. rewrite IHs2 in H1. destruct H1.
    left; constructor 3; auto. right; auto.
    rewrite IHs1.
    inv H0. right; constructor 1; auto. left; auto.
    right; constructor 2. rewrite IHs2; auto.
    rewrite IHs1; right. constructor 2. rewrite IHs2; right; auto.
Qed.

Lemma union'_spec : forall s s' x, valid s -> valid s' ->
   (interp (union' s s') x <-> interp s x \/ interp s' x).
  Proof.
  intros s s' x V V';  unfold union'.
  destruct (compare_height s s s' s').
 (* case 1 *)
  unfold linear_union; simpl.
  destruct V as [?H _]; destruct V' as [?H _].
  remember (linear_union_aux (s,s') (1%positive,nil)).
  destruct p as (n,l).
  destruct (linear_union_aux_lemma _ _ _ _ H H0 _ _ _ _ Heqp) as [? [? ?]]; simpl; auto.
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  specialize (H3 x); specialize (H5 x).
  rewrite H3 in H5.
  generalize (treeify_g_length n l); intro.
  spec H7. rewrite H2; auto.
  rewrite H2 in H7.
  assert (length (snd (treeify_g n l)) = 0) by (clear - H7; omega).
  destruct (snd (treeify_g n l)); inv H8.
  remember (fst(treeify_g n l)) as u.
  assert (InA K.eq x nil <-> False) by (split; intro Hx; try contradiction; inv Hx).
  clear - H5 H8; intuition.
 (* case 2 *)
  destruct V as [?H _]; destruct V' as [?H _].
  revert H s' H0; induction s; simpl; intros.
  intuition etac.
  inv H.
  rewrite IHs2; auto.
  rewrite <- interp_insert.
  rewrite IHs1; auto.
  intuition. inv H1; intuition.
  eapply searchtree_None; eauto.
  apply fold'_searchtree.
  apply insert_searchtree; auto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
  apply insert_searchtree; auto.
  apply fold'_searchtree.
  apply insert_searchtree; auto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
 (* case 3 *)
  destruct V as [?H _]; destruct V' as [?H _].
  revert H0 s H; induction s'; simpl; intros.
  intuition etac.
  inv H0.
  rewrite IHs'2; auto.
  rewrite <- interp_insert.
  rewrite IHs'1; auto.
  intuition. inv H1; intuition.
  eapply searchtree_None; eauto.
  apply fold'_searchtree.
  apply insert_searchtree; auto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
  apply insert_searchtree; auto.
  apply fold'_searchtree.
  apply insert_searchtree; auto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
Qed.


Lemma filter'_spec : forall s x f,
   compatb f ->
    valid s ->
    (interp (filter' f s) x <-> interp s x /\ f x = true).
  Proof.
  intros s x f ? [? _].
  unfold filter'.
 remember (filter_aux f s 1 nil) as nl.
  destruct nl as [n l].
  destruct (filter_aux_lemma _ _ _ _ _ _ H0 (Logic.eq_sym Heqnl)) as [? [? [? ?]]].
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  rewrite (H4 H x).
  rewrite <- (H6 x).
  generalize (treeify_g_length n l); intro.
  spec H8; [omega|].
  rewrite H3 in H8.
  destruct (snd (treeify_g n l)); [ | elimtype False; simpl in H8; clear - H8; omega].
  clear; intuition etac.
Qed.

  Lemma choose'_spec1 : forall s x, searchtree None None s ->
            choose' s = Some x -> interp s x.
  Proof.
    intros s x v;
    induction v; simpl in *; intros.  inv H0.
   clear o.
    destruct tl. inv H. constructor. reflexivity.
    specialize (IHv1 H).
    constructor 2; auto.
  Qed.


   Lemma choose'_spec2 : forall s, choose' s = None -> s=EE.
   Proof.
     induction s; simpl; intros; auto.
     elimtype False. destruct s1. inv H.
     apply IHs1 in H. inv H.
   Qed.

Lemma delmin_eq:
  forall s x (v: searchtree None None s),
      choose' s = Some x ->
      delete'_min s = Some (x, delete x s).
Proof.
 intros.
 assert (IN: interp s x) by (apply choose'_spec1; auto).
 assert (ST: exists lo, exists hi, searchtree lo hi s) by eauto.
  clear v; destruct ST as [lo [hi ST]].
 unfold delete'_min, delete.
 destruct s. simpl in H. inv H.
 assert (fst (delmin s1 t s2) = x).
 clear - H.
 revert t s2 H; induction s1; simpl; intros.
 inv H; auto.
 destruct s1_1. inv H.
 specialize (IHs1_1 x s1_2 (refl_equal _)).
  destruct (delmin EE x s1_2); auto. destruct c0; auto.
  specialize (IHs1_1 t s1_2 H).
  destruct (delmin (T c1 s1_1_1 t1 s1_1_2) t s1_2); subst.
  destruct c0; auto.
  assert (snd (delmin s1 t s2) = del x (T c s1 t s2)).
  clear - H ST.
  revert t s2 c H lo hi ST.
  induction s1;  intros. inv H. simpl. rewrite compare_refl.
  rewrite append_equation; auto.
  destruct s1_1.
  inv H.  simpl.
  pattern (append(EE,s1_2)); rewrite append_equation.
  rewrite compare_refl.
  inv ST.
  replace (K.compare x t0) with Lt.
  destruct c; auto.
  inv H3. clear - H8. apply searchtree_proper_bounds in H8; simpl in H8.
  symmetry; rewrite compare_lt_iff; auto.
  inv ST.
  specialize (IHs1_1 t s1_2 c H _ _ H4).
  revert IHs1_1; case_eq (delmin (T c1 s1_1_1 t1 s1_1_2) t s1_2); intros.
  remember (T c1 s1_1_1 t1 s1_1_2) as B.
  simpl snd in IHs1_1.
  assert (K.compare x t = Lt).
  subst B; clear - H4 H7 H.
    simpl in H.
   rewrite compare_lt_iff.
   inv H4. inv H5.
   destruct (s1_1_1). inv H. apply searchtree_proper_bounds in H10;  auto.
   apply choose'_spec1 in H.
  destruct (interp_range _ _ _ _ H4 H).
  apply searchtree_proper_bounds in H10.
  apply lt_trans with t1; auto.
  eapply searchtree_None; eauto.
  assert (K.compare x t0 = Lt).
  clear - H4 H H7.
   assert (choose' (T c B t s1_2) = Some x).
   simpl in H. destruct B; auto.
   apply choose'_spec1 in H0.
  destruct (interp_range _ _ _ _ H4 H0).
   rewrite compare_lt_iff. apply H2.
  eapply searchtree_None; eauto.
  unfold del in IHs1_1. fold del in IHs1_1. rewrite H1 in IHs1_1.
  unfold delmin; fold delmin. rewrite H0.
  unfold del; fold del.
  rewrite H1. rewrite H2.
  destruct c; subst t3; auto.
  rewrite <- H1. destruct (delmin s1 t s2); subst; auto.
  destruct t1; auto.
 Qed.

Lemma delete_min_valid:
       forall s, valid s ->
                    match delete'_min s with
                        | Some (_, s0) => valid s0
                        | None => True
                       end.
 Proof.
  intros s [? ?].
 case_eq (delete'_min s); intros; auto.
 destruct p as [k s'].
  case_eq (choose' s); intros.
  rewrite (delmin_eq s t) in H1; auto.
  inv H1.
  split.
  apply (del_is_searchtree k) in H.
  unfold delete. destruct (del k s); simpl; auto. inv H; repeat constructor; auto.
  destruct H0 as [n ?]; apply delete_is_redblack with n; auto.
  apply choose'_spec2 in H2. subst s. simpl in *. discriminate.
Qed.


Lemma member_compat:
  forall s, valid s -> Proper (E.eq ==> Logic.eq) (fun k : key => member k s).
Proof.
  repeat intro.
  clear H.
  induction s; simpl; auto.
  rewrite H0. rewrite IHs1. rewrite IHs2. auto.
Qed.

Lemma inter'_spec : forall s s' x,
  valid s -> valid s' -> (interp (inter' s s') x <-> interp s x /\ interp s' x).
  Proof.
  intros s s' x V V'.
  unfold inter'; simpl.
  destruct (compare_height s s s' s' ).
 (* case 1 *)
  unfold linear_inter; simpl.
  destruct V as [?H _]; destruct V' as [?H _].
  remember (linear_inter_aux (s,s') (1%positive,nil)).
  destruct p as (n,l).
  destruct (linear_inter_aux_lemma _ _ _ _ H H0 _ _ _ _ Heqp) as [? [? ?]]; simpl; auto.
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  specialize (H3 x); specialize (H5 x).
  rewrite H3 in H5.
  generalize (treeify_g_length n l); intro.
  spec H7. rewrite H2; auto.
  rewrite H2 in H7.
  assert (length (snd (treeify_g n l)) = 0) by (clear - H7; omega).
  destruct (snd (treeify_g n l)); inv H8.
  remember (fst(treeify_g n l)) as u.
  assert (InA K.eq x nil <-> False) by (split; intro Hx; try contradiction; inv Hx).
  clear - H5 H8; intuition.
 (* case 2 *)
  rewrite filter'_spec; auto. rewrite interp_member. intuition.
  destruct V'; auto.
  apply member_compat; auto.
 (* case 3 *)
  rewrite filter'_spec; auto. rewrite interp_member. intuition.
  destruct V; auto.
  apply member_compat; auto.
Qed.

 Lemma diff'_spec : forall s s' x,
   valid s -> valid s' -> (interp (diff' s s') x <-> interp s x /\ ~ interp s' x).
  Proof.
  intros s s' x V V'.
  unfold diff'; simpl.
  destruct (compare_height s s s' s' ).
 (* case 1 *)
  destruct V as [?H _]; destruct V' as [?H _].
  unfold linear_diff; simpl.
  remember (linear_diff_aux (s,s') (1%positive,nil)).
  destruct p as (n,l).
  destruct (linear_diff_aux_lemma _ _ _ _ H H0 _ _ _ _ Heqp) as [? [? ?]]; simpl; auto.
  destruct (treeify'_g_is_searchtree n l None) as [? [? ?]]; simpl; auto.
  omega.
  specialize (H3 x); specialize (H5 x).
  rewrite H3 in H5.
  generalize (treeify_g_length n l); intro.
  spec H7. rewrite H2; auto.
  rewrite H2 in H7.
  assert (length (snd (treeify_g n l)) = 0) by (clear - H7; omega).
  destruct (snd (treeify_g n l)); inv H8.
  remember (fst(treeify_g n l)) as u.
  assert (InA K.eq x nil <-> False) by (split; intro Hx; try contradiction; inv Hx).
  clear - H5 H8; intuition.
 (* case 2 *)
  rewrite filter'_spec; auto.
  rewrite <- (interp_member x s').
  destruct (member x s'); intuition.
  destruct V'; auto.
  repeat intro. f_equal. eapply member_compat; eauto.
 (* case 3 *)
  destruct V as [?H _]; destruct V' as [?H _].
  revert H0 s H; induction s'; simpl; intros.
  intuition etac.
  inv H0.
  rewrite IHs'2; auto.
  rewrite <- interp_delete; auto.
  rewrite IHs'1; auto.
  intuition etac.
  inv H3; intuition.
  eapply searchtree_None; eauto.
  apply fold'_searchtree; auto.
  apply delete_searchtree; auto.
  eapply searchtree_None; eauto.
  eapply searchtree_None; eauto.
  apply delete_searchtree; auto.
  apply fold'_searchtree; auto.
  apply delete_searchtree; auto.
  eapply searchtree_None; eauto.
Qed.

Lemma interp_dec: forall s x, {interp s x}+{~interp s x}.
Proof.
intros.
induction s. right; intro; inv H.
destruct IHs1.
left; constructor 2; auto.
destruct IHs2.
left; constructor 3; auto.
destruct (K.eq_dec x t).
left; constructor 1; auto.
right; intro; inv H; intuition.
Qed.


Definition lt' (s s': tree):  Prop :=  compare' s s' = Lt.

Lemma lt'_strorder : StrictOrder lt'.
 Proof.
  constructor.
 (* Irreflexive *)
  intros s ?.
  unfold lt' in H.
  clear - H.
  revert H.
  remember (size s); intro.
  assert (size s <= n) by omega. clear Heqn.
  revert s H0 H; induction n; intros.
  destruct s; inv H0.
 rewrite compare'_equation in H; simpl in H; inv H.
 rewrite compare'_equation in H; simpl in H.
  generalize (size_gopher s); intro.
  remember (gopher s) as s'.
  destruct s'. inv H.
  destruct s'1. rewrite compare_refl in H.
  apply IHn in H; auto. simpl in H1; omega.
  inv H.
 (* Transitive *)
  intros a b c ? ?. unfold lt' in *.
  clear - H H0.
  remember (size c).
  assert (size c <= n) by omega. clear Heqn.
  revert a b c H1 H H0; induction n; intros.
  destruct c; inv H1.
  rewrite compare'_equation in H0. simpl in H0.
  destruct (gopher b); inv H0. destruct t1; inv H2.
  rewrite compare'_equation in H, H0 |- *.
  remember (gopher a) as a'. remember (gopher b) as b'. remember (gopher c) as c'.
  destruct c'.
  elimtype False; clear - H0; destruct b'; inv H0. destruct b'1; inv H1.
  destruct a'; auto.
  destruct a'1.
  2: clear - H; destruct b'; inv H.
  destruct b'. inv H.
  destruct b'1; [ | inv H].
  destruct c'1; [ | inv H0].
  generalize (size_gopher c); intro.
  do_compare t0 t1; try solve [inv H].
  rewrite e.
  do_compare t1 t; auto.
  apply (IHn a'2 b'2 c'2); auto.
  rewrite <-  Heqc' in H2; simpl in H2; omega.
   do_compare t1 t; auto.
  rewrite e in l. rewrite <- compare_lt_iff in l. rewrite l. auto.
  replace (K.compare t0 t) with Lt; auto.
  symmetry. rewrite compare_lt_iff. apply lt_trans with t1; auto.
  inv H0.
Qed.

Lemma lt'_compat: Proper (eq ==> eq ==> iff) lt'.
 Proof.
 constructor;  intros.
 subst; auto. subst; auto.
Qed.


Lemma min_elt'_spec2:
     forall s (x : key) (y : key),
     choose' s = Some x ->
     interp s y ->
    forall (lo hi : option key)
      (ST: searchtree lo hi s), ~ E.lt y x.
 Proof.
  induction s; simpl; intros. inv H.
  inv ST.
  destruct s1. inv H.
  inv H0. rewrite H6.  apply lt_irrefl. inv H6.
  destruct (interp_range _ _ _ _ H8 H6). simpl in H.
  intro. apply (lt_irrefl (lt_trans H H1)).
  inv H0.
  apply choose'_spec1 in H.
  2: eapply searchtree_None; eauto.
  destruct (interp_range _ _ _ _ H5 H). simpl in H1.
  rewrite <- H7 in H1.
  intro. apply (lt_irrefl (lt_trans H1 H2)).
  eapply IHs1; eauto.
  destruct (interp_range _ _ _ _ H8 H7). simpl in H0.
  apply choose'_spec1 in H.
  destruct (interp_range _ _ _ _ H5 H). simpl in H3.
  intro.
 apply (lt_irrefl (lt_trans H4 (lt_trans H3 H0))).
  eapply searchtree_None; eauto.
Qed.

Lemma Klt_strictorder: StrictOrder K.lt.
 Proof.  constructor. repeat intro. apply (lt_irrefl H).
  repeat intro; eapply lt_trans; eauto.
 Qed.

Lemma elements'_spec2 : forall s, valid s -> Sorted.sort E.lt (elements' s nil).
 Proof.
  intros s [?v _].
  remember (@nil key) as rest.
  assert (exists lo, exists hi, searchtree lo hi s) by eauto.
  clear v; destruct H as [lo [hi H]].
  assert (forall x,
             SetoidList.InA K.eq x rest ->
             exists hi', hi = Some hi' /\ (K.eq x hi' \/ K.lt hi' x)).
  subst rest; intros; simpl in *. inv H0.
  assert (Sorted.Sorted K.lt rest). subst rest; constructor.
 clear Heqrest.

  revert lo hi H rest H0 H1;
      induction s; simpl; intros.
  apply H1.
  inv H.
  eapply IHs1; eauto.
  intros. inv H.
  exists t; split; auto.
  exists t; split; auto.
  rewrite elements'_interp in H3.
  destruct H3.
  destruct (interp_range _ _ _ _ H9 H).
  simpl in H2. auto.
  destruct (H0 _ H) as [hi' [? ?]].
  subst.
  apply searchtree_proper_bounds in H9.
  simpl in H9.
  destruct H3. rewrite H2 in *; auto. right; apply lt_trans with hi'; auto.
  constructor; eauto.
  apply InA_InfA with K.eq.
  apply K.eq_equiv.
  intros. rewrite elements'_interp in H.
  destruct H.
  destruct (interp_range _ _ _ _ H9 H).
  auto.
  destruct (H0 _ H) as [hi' [? ?]].
  subst.
  apply searchtree_proper_bounds in H9. simpl in H9.
  clear - H3 H9.
  destruct H3. rewrite H in *; auto. apply lt_trans with hi'; auto.
Qed.

Definition Equal' s s' := forall a, interp s a <-> interp s' a.
Definition Subset' s s' := forall a, interp s a -> interp s' a.
Definition Empty' s := forall a, ~ interp s a.
Definition For_all' (P : key -> Prop) s := forall x, interp s x -> P x.
Definition Exists' (P : key -> Prop) s := exists x, interp s x /\ P x.

(* Now, some definitions to match the Module Type *)

Definition t : Type := sig valid.
Definition elt := key.

Definition empty : t := exist valid EE empty_valid.

Definition is_empty (x: t) : bool :=
   match proj1_sig x with EE => true | _ => false end.

Definition mem (k: elt) (x: t) : bool := member k (proj1_sig x).

Definition add (k: elt) (x: t) : t :=
      exist valid (insert k (proj1_sig x)) (insert_valid _ _ (proj2_sig x)).

Definition singleton (k: elt) : t := exist valid _ (singleton_valid k).

Definition remove (k: elt) (x: t) : t :=
  exist valid _ (remove_valid k _ (proj2_sig x)).

Definition fold (A: Type) (f: elt -> A -> A) (x: t) (base: A) : A :=
  fold' A f (proj1_sig x) base.

Definition for_all (f: elt -> bool) (x: t) : bool :=
   fold bool (fun k y => andb (f k) y) x true.

Definition exists_ (f: elt -> bool) (x: t) : bool :=
   fold bool (fun k y => orb (f k) y) x false.

Definition cardinal (x: t) := fold nat (fun _ => S) x O.

Definition filter (f: elt -> bool) (s: t) : t := exist valid _ (filter_valid f _ (proj2_sig s)).

 Definition partition (f: elt -> bool) (s: t) : t*t :=
   let s' := partition' f (proj1_sig s)
    in (exist valid _ (partition_valid1 f _ (proj2_sig s)),
         exist valid _ (partition_valid2 f _ (proj2_sig s))).

Definition union (t1 t2: t) : t := exist valid _ (union_valid _ _ (proj2_sig t1) (proj2_sig t2)).

Definition diff (t1 t2: t) : t := exist valid _ (diff_valid _ _ (proj2_sig t1) (proj2_sig t2)).

Definition inter (t1 t2: t) : t := exist valid _ (inter_valid _ _ (proj2_sig t1) (proj2_sig t2)).

Definition elements (x: t) : list elt := elements' (proj1_sig x) nil.

Definition choose (x: t) : option elt := choose' (proj1_sig x).
Definition max_elt (x: t) : option elt := max_elt' (proj1_sig x).


Definition equal' (s1 s2 : tree) : bool :=
  match compare' s1 s2 with Eq => true | _ => false end.

Definition equal (t1 t2 : t) : bool := equal' (proj1_sig t1) (proj1_sig t2).

Definition subset (t1 t2: t) : bool := is_empty (diff t1 t2).

Definition In (k: key) (x: t) := interp (proj1_sig x) k.

Lemma In_compat : Proper (E.eq==>eq==>iff) In.
Proof.
repeat intro.
subst; auto.
assert (forall x y, E.eq x y -> forall u, In x u -> In y u).
clear.
intros.
destruct u as [u [? ?]].
unfold In in *.
simpl in *.
clear e s.
induction H0.
constructor 1.
transitivity x; auto.
constructor 2.
apply IHinterp; auto.
constructor 3.
apply IHinterp; auto.
split; intros; eapply H0; eauto.
Qed.

Definition Equal (s s': t)  := Equal' (proj1_sig s) (proj1_sig s').
  Definition Subset (s s': t) := Subset' (proj1_sig s) (proj1_sig s').
  Definition Empty (s: t) := Empty' (proj1_sig s).
  Definition For_all (P : elt -> Prop) (s: t) := For_all' P (proj1_sig s).
  Definition Exists (P : elt -> Prop) (s: t) := Exists' P  (proj1_sig s).

  Definition eq : t -> t -> Prop := Equal.

Lemma eq_equiv: Equivalence eq.
Proof.
 constructor;  repeat intro. split; auto.
 specialize (H a); symmetry; auto.
 specialize (H a); specialize (H0 a).
 transitivity (In a y); auto.
Qed.

  Lemma mem_spec : forall s x, mem x s = true <-> In x s.
  Proof.
   intros.
   unfold In, mem.
   destruct s as [? [? ?]].
   simpl; rewrite interp_member; auto. intuition.
 Qed.

  Lemma empty_spec : Empty empty.
  Proof. unfold Empty, Empty', empty, In, mem. intros. intro.  simpl in H.
   inv H.
  Qed.

  Lemma is_empty_spec : forall s, is_empty s = true <-> Empty s.
  Proof.
   unfold is_empty, Empty, Empty', In, mem.
  intro; destruct (proj1_sig s);
  simpl; intuition.
  inv H0.
  contradiction (H t0).
  constructor. reflexivity.
 Qed.

  Lemma add_spec : forall s x y, In y (add x s) <-> E.eq y x \/ In y s.
  Proof.
   intros.
   destruct s as [s [? ?]].
    unfold add, In, E.eq, mem; simpl.
   intuition.
   apply interp_insert in H; auto.
   apply interp_insert; auto.
   apply interp_insert; auto.
 Qed.

Definition mem_add (x: elt) (s: t) : option t :=
   match mem_add' x (proj1_sig s) as b return (b = mem_add' x (proj1_sig s) -> option t)with
     | None => fun _ => None
     | Some s' => fun p => Some (exist valid s' (mem_add_valid x _ (proj2_sig s) s' p))
     end (Logic.eq_refl _).

Lemma mem_add_spec:
    forall (x: elt) (s: t), mem_add x s = if mem x s then None else Some (add x s).
 Proof.
 intros.
  destruct s as [s V].
  unfold mem_add, mem in * ; simpl in *.
  remember (Logic.eq_refl (mem_add' x s)) as z. clear Heqz.
  revert z.
  remember (mem_add_valid x s V) as y.
  unfold add.  simpl.
  remember (insert_valid x s V) as u.
  clear Heqy Hequ V.
  case_eq (member x s); intros ?.
  assert (mem_add' x s = None); [ |  destruct (mem_add' x s);  inv H0; auto].
  clear - H.
  unfold mem_add'.
  induction s; simpl in *; try discriminate.
  destruct (K.compare x t0); auto.
   apply IHs1 in H.  destruct (ins' x s1); inv H; auto.
   apply IHs2 in H.  destruct (ins' x s2); inv H; auto.
  assert (mem_add' x s = Some (insert x s)).
Focus 2.
  destruct (mem_add' x s); inv H0.
  intros. f_equal. f_equal.
  apply PI.proof_irrelevance.
  clear - H.
  unfold mem_add', insert.
  replace (ins' x s) with (Some (ins x s)); auto.
  symmetry.
  induction s; simpl in *; auto.
  destruct (K.compare x t0); auto; try discriminate.
  rewrite (IHs1 H); auto.
  rewrite (IHs2 H); auto.
Qed.

  Lemma remove_spec : forall s x y,
                      In y (remove x s) <-> In y s /\ ~E.eq y x.
  Proof.
   intros.
   destruct s as [s [v ?]].
    unfold remove, In, E.eq, mem; simpl.
    destruct (interp_delete y x s v).
    split; intros.
    destruct (H0 H1); intuition. intuition.
 Qed.

  Lemma singleton_spec : forall x y, In y (singleton x) <-> E.eq y x.
  Proof. intros. unfold In, singleton; simpl.
    do_compare y x; intuition; try inv H; auto. inv H5. inv H5. inv H5. inv H5.
   Qed.

  Lemma fold_spec : forall s (A : Type) (i : A) (f : elt -> A -> A),
      fold _ f s i = List.fold_left (fun a e => f e a) (elements s) i.
  Proof. intros. unfold elements.
  destruct s as [s [? ?]].
  unfold fold; simpl. clear.
  rewrite fold'_spec.
  f_equal.
  clear.
  symmetry.
  change (rev (fold' (list key) (@cons _) s nil)) with (rev (nil ++ fold' (list key) (@cons _) s nil)).
  remember (@nil key) as l.
  rewrite Heql at  3.
  pattern l at 2; replace l with (rev l) by (subst; simpl; auto).
  clear.
  revert l; induction s; simpl; intros; auto.
  rewrite <- app_nil_end. symmetry; apply rev_involutive.
  rewrite IHs2. rewrite IHs1.
  clear.
  remember ( fold' (list key) (@cons _) s1 nil) as B.
  f_equal.
  clear.
   change (t0::B) with (nil ++ (t0::nil)++B).
   rewrite fold'_app.
  remember ( fold' (list key) (@cons _) s2 nil) as A.
  clear.
  simpl.
  rewrite rev_involutive.
  repeat rewrite app_ass.
  simpl; auto.
Qed.

  Lemma elements_spec1 : forall s x,
     SetoidList.InA E.eq x (elements s) <-> In x s.
  Proof.
    intros.
    unfold elements.
    rewrite elements'_interp. intuition etac.
Qed.

Lemma add_commute:
  forall x i j s, In x (add i (add j s)) <-> In x (add j (add i s)).
Proof.
  intros.
  repeat rewrite add_spec; intuition.
Qed.

Lemma union_spec : forall s s' x, In x (union s s') <-> In x s \/ In x s'.
  Proof.
  intros; unfold union, In.
  destruct s as [s V]; destruct s' as [s' V']; simpl.
  apply union'_spec; auto.
Qed.

 Lemma filter_spec : forall s x f,
   compatb f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
  intros [s V] ? ? ?.
  unfold In, filter. simpl.
  apply filter'_spec; auto.
Qed.

Lemma inter_spec : forall s s' x, In x (inter s s') <-> In x s /\ In x s'.
  Proof.
  intros; unfold inter, In.
  destruct s as [s V]; destruct s' as [s' V']; simpl.
  apply inter'_spec; auto.
Qed.

Lemma remove_commute:
  forall x i j s, In x (remove i (remove j s)) <-> In x (remove j (remove i s)).
Proof.
  intros.
  repeat rewrite remove_spec; intuition.
Qed.

 Lemma diff_spec : forall s s' x, In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
  destruct s as [s V]; destruct s' as [s' V'].
  intros; unfold diff, In; simpl.
  apply diff'_spec; auto.
 Qed.

Lemma In_dec: forall x s, {In x s}+{~In x s}.
Proof.
intros.
apply interp_dec.
Qed.


  Lemma subset_spec : forall s s', subset s s' = true <-> Subset s s'.
  Proof. intros.
  unfold subset.
  generalize (diff_spec s s'); intro.
  rewrite (is_empty_spec (diff s s')).
  unfold Empty, Empty', Subset, Subset', In, diff in *.
  simpl in *.
  split; intros.
  specialize (H a); specialize (H0 a). rewrite H in H0.
  destruct (In_dec a s'); auto. intuition.
  rewrite H.
  intros [? ?].
  apply H0 in H1. intuition.
 Qed.


 Lemma equal'_spec : forall s s', valid s -> valid s' ->
               (equal' s s' = true <-> Equal' s s').
 Proof.
 unfold equal', Equal'.
 intros s s' [v e] [v' e'].
 generalize (interp_compare' s s'); intro.
 generalize (compare'_interp_aux _ _ _ _ _ _ v v'); intro.
 destruct (compare' s s'); intuition discriminate.
 Qed.

 Lemma equal_spec : forall s s', equal s s' = true <-> Equal s s'.
 Proof.
 intros [s v] [s' v']; apply equal'_spec; auto.
 Qed.

Lemma eq_dec : forall (s s':t), { eq s s' }+{ ~eq s s' }.
Proof.
 intros. unfold eq, Equal.
  case_eq (equal s s'); intros.
  apply equal_spec in H. left; auto.
  right; intro.
  apply equal_spec in H0.
  rewrite H in H0; inv H0.
 Qed.

  Lemma cardinal_spec : forall s, cardinal s = length (elements s).
  Proof.
   unfold cardinal.
    intros; rewrite fold_spec.
   rewrite <- List.fold_left_rev_right.
   rewrite <- List.rev_length.
    unfold elt.
    remember (@rev K.t (elements s)) as  l; clear.
    clear; induction l; simpl; auto.
  Qed.

  Lemma for_all_spec : forall s f,
  compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
 Proof.
 intros.
 unfold for_all, For_all.
  rewrite fold_spec.
  generalize (elements_spec1 s); intro.
  transitivity (forall x, InA E.eq x (elements s) -> f x = true).
  2: split; intros ? x; specialize (H0 x); intuition.
  clear H0.
  remember (elements s) as el; clear s Heqel.
  induction el; simpl. intuition etac.
  split; intros. inv H1.
  rewrite (H _ _ H3).
  clear - H0.
  destruct (f a); auto. simpl in H0.
  revert H0;   induction el; simpl in *; intros; auto.
  destruct (f a0); simpl in *; auto.
  apply IHel; auto.
  destruct (f a); simpl in H0; auto.
  elimtype False; clear - H0. revert H0; induction el; simpl; intros; try discriminate.
  destruct (f a); simpl in H0; auto.
  case_eq (f a); simpl; intros.
  apply IHel; intros. eapply H0; eauto.
  rewrite (H0 a) in H1. inv H1. constructor 1; reflexivity.
 Qed.

  Lemma exists_spec : forall s f,
   compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
 Proof.

  intros.
  unfold exists_, Exists.
  rewrite fold_spec.
  generalize (elements_spec1 s); intro.
  transitivity (exists x, InA E.eq x (elements s) /\ f x = true).
  2:  split; intros [x ?]; exists x; rewrite (H0 x) in *; auto.
  remember (elements s) as el; clear - H.
  induction el; simpl.
  intuition etac. destruct H0 as [? [? ?]]. inv H0.
  case_eq (f a); intros.
  simpl.
  transitivity True.
  2: intuition; exists a; split; auto; constructor 1; reflexivity.
  clear.
  induction el; intuition. simpl. destruct (f a); simpl; auto.
  simpl. rewrite IHel.
  split; (intros [x ?]; exists x; intuition).
  inv H2; auto. rewrite (H _ _ H6) in H3; rewrite H0 in H3; inv H3.
Qed.


Lemma partition_aux_filter:
  forall f s n1 l1 n2 l2, partition_aux f s  (n1,l1) (n2,l2) =
                 (filter_aux f s n1 l1, filter_aux (compose negb f) s n2 l2).
 Proof.
  induction s; simpl; intros; auto.
  rewrite IHs2.
  unfold compose at 5.
  case_eq (f t0); simpl; intros.
  case_eq (filter_aux (compose negb f) s2 n2 l2); intros.
  rewrite IHs1.
  destruct (filter_aux f s2 n1 l1); simpl. auto.
  destruct (filter_aux f s2 n1 l1); simpl.
  rewrite IHs1.
  destruct (filter_aux (compose negb f) s2 n2 l2).
  simpl. auto.
 Qed.

  Lemma partition_spec1 : forall s f,
      compatb f -> Equal (fst (partition f s)) (filter f s).
  Proof.
  intros [s H] f H1 a.
  unfold In, filter, filter', partition, partition'; simpl.
    remember (partition_valid1 f s H) as H3.
  clear HeqH3.
  remember (partition_valid2 f s H) as H4.
  clear HeqH4.
 assert (H2: filter_aux f s 1 nil = fst ( partition_aux f s (1%positive, nil) (1%positive, nil)))
   by (rewrite partition_aux_filter; simpl; auto).
  rewrite H2. simpl in *.
  clear.
  destruct (partition_aux f s (1%positive, nil) (1%positive, nil)).
  destruct p as [n1 l1]. destruct p0 as [n2 l2]. simpl.
  intuition.
 Qed.

  Lemma partition_spec2 : forall s f,
    compatb f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
 Proof.
  intros [s H] f H1 a.
  unfold In, filter, filter', partition, partition'; simpl.
  remember (partition_valid1 f s H) as H3.
  clear HeqH3.
  remember (partition_valid2 f s H) as H4.
  clear HeqH4.
 assert (H2: filter_aux (compose negb f) s 1 nil = snd ( partition_aux f s (1%positive, nil) (1%positive, nil)))
   by (rewrite partition_aux_filter; simpl; auto).
  destruct (partition_aux f s (1%positive, nil) (1%positive, nil)).
  simpl in *. destruct p;   subst p0; simpl.
  unfold compose.
  unfold elt.
  destruct (filter_aux (fun x : key => negb (f x)) s 1 nil).
  simpl. intuition.
 Qed.


  Lemma choose_spec1 : forall s x, choose s = Some x -> In x s.
  Proof.
    intros. unfold choose, In in *.
    destruct s as [s [? ?]]; simpl in *.
     apply choose'_spec1; auto.
   Qed.

   Lemma choose_spec2 : forall s, choose s = None -> Empty s.
   Proof.
     intros.
    destruct s as [s [? ?]]; unfold choose, Empty, Empty', In in *;
     simpl in *.
     apply choose'_spec2 in H. subst.
     intros. intro Hx; inv Hx.
   Qed.

Definition compare (s s':  t) : comparison :=
 compare' (proj1_sig s) (proj1_sig s').

Definition lt (s s': t):  Prop :=
    compare s s' = Lt.

Lemma lt_strorder : StrictOrder lt.
 Proof.
  constructor.
 (* Irreflexive *)
  intros ? ?.
  unfold lt in H. unfold compare in H.
  apply lt'_strorder in H; auto.
 (* Transitive *)
  intros ? ? ? ? ?. unfold lt, compare in *.
  eapply lt'_strorder; eauto.
Qed.

Lemma lt_compat: Proper (eq ==> eq ==> iff) lt.
 Proof.
 constructor;  intros.
 (*  PART 1 *)
  destruct x as [a [?v ?]]; destruct y as [b [?v ?]];
  destruct x0 as [a' [?v ?]]; destruct y0 as [b' [?v ?]].
  unfold eq, Equal, Equal', lt, lt', In, compare, mem in *.
  simpl in *. clear e1 e2 e e0.
  rename H into EQab; rename H0 into EQa'b'.
  assert (STa: exists lo, exists hi, searchtree lo hi a) by eauto;
   destruct STa as [loa [hia STa]].
  assert (STa': exists lo, exists hi, searchtree lo hi a') by eauto;
   destruct STa' as [loa' [hia' STa']].
  assert (STb: exists lo, exists hi, searchtree lo hi b) by eauto;
   destruct STb as [lob [hib STb]].
  assert (STb': exists lo, exists hi, searchtree lo hi b') by eauto;
   destruct STb' as [lob' [hib' STb']].
  clear v v0 v1 v2.
  remember (S (size a')) as n.
  assert (size a' < n) by (subst; auto).
  clear Heqn.
  revert a' H loa' hia' STa' a loa hia STa
            b' lob' hib' STb' b lob hib STb
            EQab EQa'b' H1;
   induction n; simpl; intros.
   elimtype False; omega.
   rewrite compare'_equation in H1; rewrite compare'_equation.
   rewrite <- (size_gopher a') in H.
   rewrite (searchtree_gopher a') in STa'.
   rewrite (searchtree_gopher a) in STa.
   rewrite (searchtree_gopher b') in STb'.
   rewrite (searchtree_gopher b) in STb.
   generalize (shape_gopher a'); intro SHa'.
   generalize (shape_gopher a); intro SHa.
   generalize (shape_gopher b'); intro SHb'.
   generalize (shape_gopher b); intro SHb.
   assert (Gab: forall x : key, interp (gopher a) x <-> interp (gopher b) x)
     by (intro; rewrite (interp_gopher a); rewrite (interp_gopher b); auto).
   assert (Ga'b': forall x : key, interp (gopher a') x <-> interp (gopher b') x)
     by (intro; rewrite (interp_gopher a'); rewrite (interp_gopher b'); auto).
    clear EQab EQa'b'.
   destruct (gopher a); try discriminate.
   destruct (gopher a'); try discriminate.
   destruct t0_1; try contradiction.
   destruct (gopher b).
   2: elimtype False; clear - Gab; destruct (Gab t1);
        absurd (interp EE t1); [intro Hx; inv Hx
                                     | apply H0; constructor 1; reflexivity].
   destruct (gopher b'); auto.
    absurd (interp EE t0); [intro Hx; inv Hx
                                     | apply Ga'b'; constructor 1; reflexivity].
   destruct t0_1; try contradiction.
   destruct (gopher a'); try discriminate.
    destruct t1_1; try discriminate.
    destruct (gopher b).
    absurd (interp EE t0); [intro Hx; inv Hx
                                     | apply Gab; constructor 1; reflexivity].
    destruct (gopher b').
    absurd (interp EE t1); [intro Hx; inv Hx
                                     | apply Ga'b'; constructor 1; reflexivity].
    destruct (t3_1); try contradiction.
    destruct (t2_1); try contradiction.
    destruct (tree_similar_lemma _ _ _ _ _ _ _ _ _ _ STa STb Gab).
    destruct (tree_similar_lemma _ _ _ _ _ _ _ _ _ _ STa' STb' Ga'b').
     rewrite <- H0. rewrite <- H3.
     do_compare t0 t1; auto.
     clear SHa' SHa SHb' SHb.
     inv STa'; inv STa; inv STb'; inv STb.
     eapply (IHn t1_2); try ( simpl in H; omega);
         try apply H2;  auto; eassumption.
  (* PART 2:  similar *)
  destruct x as [a [?v ?]]; destruct y as [b [?v ?]];
  destruct x0 as [a' [?v ?]]; destruct y0 as [b' [?v ?]].
  unfold eq, Equal, Equal', lt, lt', In, compare, mem in *.
  simpl in *. clear e1 e2 e e0.
  rename H into EQab; rename H0 into EQa'b'.
  assert (STa: exists lo, exists hi, searchtree lo hi a) by eauto;
   destruct STa as [loa [hia STa]].
  assert (STa': exists lo, exists hi, searchtree lo hi a') by eauto;
   destruct STa' as [loa' [hia' STa']].
  assert (STb: exists lo, exists hi, searchtree lo hi b) by eauto;
   destruct STb as [lob [hib STb]].
  assert (STb': exists lo, exists hi, searchtree lo hi b') by eauto;
   destruct STb' as [lob' [hib' STb']].
  clear v v0 v1 v2.
  remember (S (size a')) as n.
  assert (size a' < n) by (subst; auto).
  clear Heqn.
  revert a' H loa' hia' STa' a loa hia STa
            b' lob' hib' STb' b lob hib STb
            EQab EQa'b' H1;
   induction n; simpl; intros.
   elimtype False; omega.
   rewrite compare'_equation in H1; rewrite compare'_equation.
   rewrite <- (size_gopher a') in H.
   rewrite (searchtree_gopher a') in STa'.
   rewrite (searchtree_gopher a) in STa.
   rewrite (searchtree_gopher b') in STb'.
   rewrite (searchtree_gopher b) in STb.
   generalize (shape_gopher a'); intro SHa'.
   generalize (shape_gopher a); intro SHa.
   generalize (shape_gopher b'); intro SHb'.
   generalize (shape_gopher b); intro SHb.
   assert (Gab: forall x : key, interp (gopher a) x <-> interp (gopher b) x)
     by (intro; rewrite (interp_gopher a); rewrite (interp_gopher b); auto).
   assert (Ga'b': forall x : key, interp (gopher a') x <-> interp (gopher b') x)
     by (intro; rewrite (interp_gopher a'); rewrite (interp_gopher b'); auto).
    clear EQab EQa'b'.
   destruct (gopher b); try discriminate.
   destruct (gopher b'); try discriminate.
   destruct t0_1; try contradiction.
   destruct (gopher a).
   2: elimtype False; clear - Gab; destruct (Gab t1);
        absurd (interp EE t1); [intro Hx; inv Hx
                                     | apply H; constructor 1; reflexivity].
   destruct (gopher a'); auto.
    absurd (interp EE t0); [intro Hx; inv Hx
                                     | apply Ga'b'; constructor 1; reflexivity].
   destruct t0_1; try contradiction.
   destruct (gopher b'); try discriminate.
    destruct t1_1; try discriminate.
    destruct (gopher a).
    absurd (interp EE t0); [intro Hx; inv Hx
                                     | apply Gab; constructor 1; reflexivity].
    destruct (t2_1); try contradiction.
    destruct (gopher a').
    absurd (interp EE t1); [intro Hx; inv Hx
                                     | apply Ga'b'; constructor 1; reflexivity].
    destruct (t3_1); try contradiction.
    destruct (tree_similar_lemma _ _ _ _ _ _ _ _ _ _ STa STb Gab).
    destruct (tree_similar_lemma _ _ _ _ _ _ _ _ _ _ STa' STb' Ga'b').
     rewrite  H0. rewrite H3.
     do_compare t0 t1; auto.
     clear SHa' SHa SHb' SHb.
     inv STa'; inv STa; inv STb'; inv STb.
     eapply (IHn t3_2); try ( simpl in H; omega);
         try apply H2;  auto; eassumption.
Qed.

Lemma compare_spec
     : forall s s' : t, CompSpec eq lt s s' (compare s s').
 Proof.
   intros [s [? ?]] [s' [? ?]]; unfold compare; simpl.
   case_eq (compare' s s'); intros;
     [constructor 1 | constructor 2 | constructor 3].
   unfold eq, Equal, Equal', In, mem; simpl.
   intro k. repeat rewrite interp_member; auto.
   apply interp_compare'; auto.
   unfold lt, compare; simpl. auto.
   unfold lt, compare; simpl.
   clear - H.
   remember (size s') as n.
   assert (size s' <= n) by omega.
   clear Heqn.
   revert s s' H0 H; induction n; intros.
   destruct s'; inv H0. rewrite compare'_equation in H. simpl in H.
   rewrite compare'_equation. simpl.
   destruct (gopher s); auto. inv H.
   rewrite compare'_equation in H|-*.
   remember (gopher s') as gs'.
   remember (gopher s) as gs.
   destruct gs. destruct gs'; inv H.
   destruct gs'; auto.
   destruct gs1; [| inv H].
   destruct gs'1; [| inv H].
   do_compare t0 t1.
   rewrite e. rewrite compare_refl.
   eapply IHn; eauto.
   generalize (size_gopher s'); intro. rewrite <- Heqgs' in H1; simpl in H1; omega.
   inv H.
   rewrite <- compare_lt_iff in l. rewrite l. auto.
 Qed.

Definition min_elt: t -> option elt := choose.

Lemma elements_spec2 : forall s, Sorted.sort E.lt (elements s).
 Proof.  intros [s v]; apply elements'_spec2; simpl; auto.
 Qed.

  Lemma elements_spec2w : forall s, SetoidList.NoDupA E.eq (elements s).
  Proof.
   intros.
   generalize (elements_spec2 s); intros.
   remember (elements s) as l; clear - H; induction H.
  constructor.
   constructor; auto.
   intro.
   apply (@lt_irrefl a).
   eapply SortA_InfA_InA; eauto.
   apply K.eq_equiv.
   apply Klt_strictorder.
   apply K.lt_compat.
Qed.

Lemma min_elt_spec1
     : forall (s : t) (x : elt), min_elt s = Some x -> In x s.
 Proof. intros. apply choose_spec1. auto. Qed.

Lemma min_elt_spec2 : forall s x y,
         min_elt s = Some x -> In y s -> ~ E.lt y x.
Proof.
  unfold min_elt, choose, In, mem.  intros [s [v ?]]; simpl; intros.
  eapply min_elt'_spec2; eauto.
Qed.

 Lemma min_elt_spec3 : forall s, min_elt s = None -> Empty s.
 Proof.  exact choose_spec2. Qed.

  Lemma max_elt'_spec1 : forall s x, searchtree None None s ->
            max_elt' s = Some x -> interp s x.
  Proof.
    intros s x v;
    induction v; simpl in *; intros.  inv H0.
    destruct tr. inv H. constructor. reflexivity.
    specialize (IHv2 H).
    constructor 3; auto.
  Qed.

 Lemma max_elt_spec1 : forall s x, max_elt s = Some x -> In x s.
  Proof.
   unfold In, max_elt; intros [s [? ?]] x ?; simpl in *.
  eapply max_elt'_spec1; eauto.
  Qed.

 Lemma max_elt_spec2 : forall s x y, max_elt s = Some x -> In y s -> ~ E.lt x y.
 Proof.
 unfold max_elt, In.  intros [s [v ?]]; simpl; intros.
  clear e.
  assert (ST: exists lo, exists hi, searchtree lo hi s) by eauto.
  clear v; destruct ST as [lo [hi ST]].
  revert H H0; induction ST; intros. inv H1.
  simpl in H. destruct tr. inv H.
  inv H0. rewrite H5. apply lt_irrefl.
  destruct (interp_range _ _ _ _ ST1 H5).
  simpl in H0.
  intro Hx. apply (lt_irrefl (lt_trans H0 Hx)).
  inv H5.
  remember (T c0 tr1 t0 tr2) as tr.
  clear tr1 t0 tr2 Heqtr.
  specialize (IHST2 H).
  apply max_elt'_spec1 in H.
  destruct (interp_range _ _ _ _ ST2 H). simpl in H1.
  inv H0. rewrite <- H8 in H1.
  intro Hx. apply (lt_irrefl (lt_trans H1 Hx)).
 destruct (interp_range _ _ _ _ ST1 H8). simpl in H3.
  intro. apply (lt_irrefl (lt_trans H4 (lt_trans H3 H1))).
  auto.
  eapply searchtree_None; eauto.
 Qed.

Lemma max_elt_spec3 : forall s, max_elt s = None -> Empty s.
Proof.
 unfold max_elt, In; intros [s [? ?]] ?; simpl in *.
 rewrite <- is_empty_spec. unfold is_empty; simpl. destruct s; auto.
 clear s0 e.
 simpl in H.
 elimtype False; revert t0 H; induction s2; intros. inv H.
 simpl in H. eapply IHs2_2; eauto.
Qed.

Lemma choose_spec3 : forall s s' x y,
   choose s = Some x -> choose s' = Some y ->
    Equal s s' -> E.eq x y.
Proof.
 intros.
  unfold E.eq.
 unfold Equal in H1.
 generalize (min_elt_spec2 _ _ y H); intro.
 generalize (min_elt_spec2 _ _ x H0); intro.
 apply choose_spec1 in H.
 apply choose_spec1 in H0.
 destruct (H1 y); destruct (H1 x).
 do_compare x y; auto.
 contradiction (H3 (H6 H)); auto.
 contradiction (H2 (H5 H0)); auto.
Qed.


Definition opt_t_aux (x: option (elt * tree))
    (P: match x with Some (_,s) => valid s | None => True end) : option (elt * t) :=
match
  x as o
  return
    (match o with
     | Some (_, s) => valid s
     | None => True
     end -> option (elt * t))
with
| Some (k,s') => fun P0 : valid s' => Some (k, exist valid s' P0)
| None => fun _ : True => None
end P.

Definition delete_min (s: t) : option (elt * t) :=
  opt_t_aux (delete'_min (proj1_sig s)) (delete_min_valid _ (proj2_sig s)).

 Lemma delete_min_spec1: forall (s: t) k s',
    delete_min s = Some (k,s') <->
    (min_elt s = Some k /\ remove k s = s').
 Proof.
  intros.
  destruct s as [s ?]. destruct s' as [s' ?].
  unfold delete_min, min_elt, choose, remove in *. simpl in *.
  remember (delete_min_valid s v) as P.
  clear HeqP.
  split; intro.
  case_eq (choose' s); intros.
   generalize (delmin_eq _ _ (proj1 v) H0); intro.
   destruct (delete'_min s); inv H1.
   simpl in H. inv H. split; simpl; auto.
   rewrite (proof_irrelevance _ v0 (remove_valid k s v)).
   auto.
   apply choose'_spec2 in H0. subst s.
   simpl in *. inv H.
   destruct H.
   inv H0.
   generalize (delmin_eq _ _ (proj1 v) H); intro.
   revert P; rewrite H0; simpl; intros.
   rewrite (proof_irrelevance _ P v0); auto.
 Qed.

Lemma delete_min_spec2: forall s, delete_min s = None <-> Empty s.
 Proof.
  intros [s ?].
   unfold delete_min in *.
  simpl.
  split; intro.
  unfold Empty, Empty'; simpl.
  case_eq (choose' s); intros.
  generalize (delmin_eq _ _ (proj1 v) H0); intro.
  remember (delete_min_valid s v) as P.
  clear HeqP.
  remember (delete'_min s) as x; clear Heqx; subst x.
  inv H.
  clear H.
   apply choose'_spec2 in H0. subst s.
   unfold In. simpl. intro Hx; inv Hx.
   rewrite <- is_empty_spec in H. unfold is_empty in H.
   simpl in H. destruct s; inv H. reflexivity.
 Qed.

End Make.
