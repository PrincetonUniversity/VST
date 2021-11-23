Require Import ZArith.
Require Import VST.msl.Extensionality.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.coqlib4.
Require Import compcert.lib.Maps.
Import PTree.

Fixpoint PTree_samedom' {A B} (m1: tree' A) (m2: tree' B) :=
 match m1, m2 with
 | Node001 r1, Node001 r2 => PTree_samedom' r1 r2
 | Node010 _, Node010 _ => True
 | Node011 _ r1, Node011 _ r2 => PTree_samedom' r1 r2
 | Node100 l1, Node100 l2 => PTree_samedom' l1 l2
 | Node101 l1 r1, Node101 l2 r2 => PTree_samedom' l1 l2 /\ PTree_samedom' r1 r2
 | Node110 l1 _, Node110 l2 _ => PTree_samedom' l1 l2
 | Node111 l1 _ r1, Node111 l2 _ r2 => PTree_samedom' l1 l2 /\ PTree_samedom' r1 r2
 | _, _ => False
 end.

Definition PTree_samedom {A B} (m1: PTree.t A) (m2: PTree.t B) :=
 match m1, m2 with 
 | Empty, Empty => True
 | Nodes m1', Nodes m2' => PTree_samedom' m1' m2'
 | _, _ => False
 end.

Fixpoint PTree_map3' {A1 A2 A3 B}
       (f: A1 -> A2 -> A3 -> B) (d: B)
       (m1: tree' A1) (m2: tree' A2) (m3: tree' A3) : tree' B :=
match m1, m2, m3 with
| Node001 r1, Node001 r2, Node001 r3 => Node001 (PTree_map3' f d r1 r2 r3)
| Node010 x1, Node010 x2, Node010 x3 => Node010 (f x1 x2 x3)
| Node011 x1 r1, Node011 x2 r2, Node011 x3 r3 => 
       Node011 (f x1 x2 x3) (PTree_map3' f d r1 r2 r3)
| Node100 l1, Node100 l2, Node100 l3 => Node100 (PTree_map3' f d l1 l2 l3)
| Node101 l1 r1, Node101 l2 r2, Node101 l3 r3 =>
     Node101 (PTree_map3' f d l1 l2 l3) (PTree_map3' f d r1 r2 r3)
| Node110 l1 x1, Node110 l2 x2, Node110 l3 x3 =>
     Node110 (PTree_map3' f d l1 l2 l3) (f x1 x2 x3)
| Node111 l1 x1 r1, Node111 l2 x2 r2, Node111 l3 x3 r3 =>
     Node111 (PTree_map3' f d l1 l2 l3) (f x1 x2 x3) (PTree_map3' f d r1 r2 r3)
| _, _, _ => Node010 d
end.

Definition PTree_map3  {A1 A2 A3 B}
       (f: A1 -> A2 -> A3 -> B) (d: B)
       (m1: tree A1) (m2: tree A2) (m3: tree A3) : tree B :=
 match m1, m2, m3 with
 | Empty, Empty, Empty => Empty
 | Nodes m1', Nodes m2', Nodes m3' => Nodes (PTree_map3' f d m1' m2' m3')
 | _, _, _ => Empty
 end.

Lemma PTree_gmap3:
  forall {A1 A2 A3 B} (f:  A1 -> A2 -> A3 -> B) d i m1 m2 m3,
  PTree_samedom m1 m2 -> PTree_samedom m1 m3 ->
  ((PTree_map3 f d m1 m2 m3) ! i) = 
  match (m1 ! i), (m2 ! i), (m3 ! i) with
  | Some x1, Some x2, Some x3 => Some (f x1 x2 x3)
  | None, None, None => None
  | _, _, _ => None
  end.
Proof.
intros until m3. intros S1 S2.
destruct m1 as [|m1], m2 as [|m2]; try contradiction S1;
destruct m3 as [|m3]; try contradiction S2.
reflexivity.
unfold PTree_samedom, PTree_map3, PTree.get in *.
revert m1 m2 S1 m3 S2;
induction i; destruct m1, m2; simpl; intro S1;
 try destruct S1;
 destruct m3; simpl; intro S2;
 try destruct S2;
 auto.
Qed.

Fixpoint PTree_Forall' {A: Type} (F: A -> Prop) (m: tree' A): Prop :=
match m with
| Node001 r => PTree_Forall' F r
| Node010 x => F x
| Node011 x r => F x /\ PTree_Forall' F r
| Node100 l => PTree_Forall' F l
| Node101 l r => PTree_Forall' F l /\ PTree_Forall' F r
| Node110 l x => PTree_Forall' F l /\ F x
| Node111 l x r => PTree_Forall' F l /\ F x /\ PTree_Forall' F r
end.

Definition PTree_Forall {A: Type} (F: A -> Prop) (m: PTree.t A): Prop :=
match m with Empty => True | Nodes m' => PTree_Forall' F m' end.

Definition PTree_Forall_get {A: Type} (F: A -> Prop) (m: PTree.t A): Prop :=
  forall i, match PTree.get i m with Some c => F c | None => True end.

Lemma PTree_Forall_get_eq: @PTree_Forall_get = @PTree_Forall.
Proof.
extensionality A F m.
unfold PTree_Forall_get, PTree_Forall.
apply prop_ext.
destruct m as [|m]; simpl.
tauto.
split; intro.
-
induction m.
+ apply IHm. intro i; apply (H (xI i)).
+ apply (H xH).
+ split. apply (H xH). apply IHm. intro i; apply (H (xI i)).
+ apply IHm. intro i; apply (H (xO i)).
+ split. apply IHm1. intro i; apply (H (xO i)). apply IHm2. intro i; apply (H (xI i)).
+ split. apply IHm. intro i; apply (H (xO i)). apply (H xH).
+ split3.  apply IHm1. intro i; apply (H (xO i)). apply (H xH).  apply IHm2. intro i; apply (H (xI i)).
-
 induction m; intro i; destruct i; simpl; auto;
 try destruct H as [? [? ?]]; try destruct H;
  auto;
  try apply IHm; try apply IHm1; try apply IHm2; auto.
Qed.

Lemma PTree_domain_eq_e {A B} {m1: PTree.t A} {m2: PTree.t B}:
   PTree_samedom m1 m2 -> 
  forall i, (exists x, m1 ! i = Some x) <-> (exists y, m2 ! i = Some y).
Proof.
assert (H8: (exists x:A, None = Some x) <-> (exists y:B, None = Some y))
 by (split; intros [x H0]; inv H0).
destruct m1 as [|m1], m2 as [|m2]; intro H; try contradiction H; auto.
intro i.
unfold get, PTree_samedom in *.
revert m1 m2 H; induction i; destruct m1, m2; simpl; intro H; try contradiction H; try destruct H;
auto;
(split; intros [x H7]; eauto).
Qed.

Lemma PTree_Forall_elements:
 forall A (F: A -> Prop) (m: PTree.t A),
  PTree_Forall F m <-> Forall (fun ix => F (snd ix)) (PTree.elements m).
Proof.
intros.
rewrite <- PTree_Forall_get_eq.
split; intros.
-
red in H.
apply Forall_forall.
intros (i,y) ?.
simpl.
specialize (H i).
apply PTree.elements_complete in H0.
rewrite H0 in H.
auto.
-
intro i.
rewrite -> Forall_forall in H.
destruct (m ! i) eqn:?H; auto.
specialize (H (i,a)).
apply H.
apply PTree.elements_correct.
auto.
Qed.

Lemma PTree_elements_map1:
  forall {A B} (f: A -> B)  e, PTree.elements (PTree.map1 f e) =
                  List.map (fun ix => (fst ix, f (snd ix))) (PTree.elements e).
Proof.
intros.
unfold PTree.elements.
set (g := (fun ix : positive * A => (fst ix, f (snd ix)))).
change (@nil (positive * B)) with (List.map g (@nil (positive * A))).
forget (@nil (positive * A)) as r.
forget 1%positive as n.
revert r n.
destruct e as [|m]; simpl; auto.
induction m; intros; simpl; auto.
- f_equal; auto.
- rewrite <- IHm1. rewrite <- IHm2. reflexivity.
- rewrite <- IHm.  reflexivity.
- rewrite <- IHm1. simpl. rewrite <- IHm2. reflexivity.
Qed.

(*
Definition Some_e {A} (default: A) (o: option A) : A :=
 match o with Some x => x | None => default end.

Lemma xelements_empty:
  forall {A} (m: PTree.t A) n al, 
   (forall i, (m ! i) = None) ->
   PTree.xelements m n al = al.
Proof.
induction m; intros.
reflexivity.
simpl.
destruct o.
specialize (H 1%positive); inv H.
rewrite IHm1.
rewrite IHm2.
auto.
intro i; specialize (H (xI i)); inv H; auto.
intro i; specialize (H (xO i)); inv H; auto.
Qed.
*)

Fixpoint map3 {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) 
  (al1: list A1) 
  (al2: list A2) 
  (al3: list A3) :  list B :=
match al1, al2, al3 with
| a1::al1', a2::al2', a3::al3' => f a1 a2 a3 :: map3 f al1' al2' al3'
| _, _, _ => nil
end.

(*
Lemma PTree_domain_eq_Leaf:
 forall {A B} a,
    @PTree_domain_eq A B a PTree.Leaf <->
    (forall i, a ! i = None).
Proof.
induction a; simpl; intros; split; intro.
apply PTree.gempty.
split; intro; hnf; rewrite PTree.gempty; auto.
hnf in H0; rewrite PTree.gempty in H0; auto.
hnf in H0; rewrite PTree.gempty in H0; auto.
destruct i; simpl.
specialize (proj1 (H (xI i))); simpl in *; destruct (a2!i); intro; auto. contradiction H0. apply I.
specialize (proj1 (H (xO i))); simpl in *; destruct (a1!i); intro; auto. contradiction H0. apply I.
specialize (proj1 (H xH)); simpl. destruct o; intro; auto. contradiction H0; hnf; auto.
split; rewrite PTree.gempty; intro; hnf in H0.
rewrite H in H0; auto.
contradiction.
Qed.

Lemma PTree_domain_empty_Node:
 forall {A} (a: PTree.t A) o b,
  (forall i, (PTree.Node a o b) ! i = None) ->
  (forall i, a ! i = None) /\ o = None /\ (forall i, b ! i = None).
Proof.
intros.
split3.
intro i. apply (H (xO i)).
apply (H xH).
intro i. apply (H (xI i)).
Qed.

Lemma PTree_domain_eq_Node_Node:
  forall {A1 A2} (a1: PTree.t A1) o1 b1 (a2: PTree.t A2) o2 b2,
  PTree_domain_eq (PTree.Node a1 o1 b1) (PTree.Node a2 o2 b2) <->
  (PTree_domain_eq a1 a2 /\ (isSome o1 <-> isSome o2) 
    /\ PTree_domain_eq b1 b2).
Proof.
intros.
split; intro.
split3; try intro.
apply (H (xO i)).
apply (H xH).
apply (H (xI i)).
destruct H as [? [? ?]].
intro i. destruct i; simpl.
apply H1.
apply H.
apply H0.
Qed.

*)

Lemma PTree_elements_map3:
  forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) d e1 e2 e3, 
         PTree_samedom e1 e2 ->
         PTree_samedom e1 e3 ->
         PTree.elements (PTree_map3 f d e1 e2 e3) =
             map3 (fun ix iy iz => (fst ix, f (snd ix) (snd iy) (snd iz)))
                  (PTree.elements e1) (PTree.elements e2) (PTree.elements e3).
Proof.
intros.
match goal with |- _ = map3 ?A _ _ _ => set (g := A) end.
unfold PTree.elements.
change (@nil (positive * B)) with (map3 g nil nil nil).
forget (@nil (positive * A1)) as r1.
forget (@nil (positive * A2)) as r2.
forget (@nil (positive * A3)) as r3.
forget 1%positive as n.
destruct e1 as [|m1], e2 as [|m2]; try contradiction H;
 destruct e3 as [|m3]; try contradiction H0.
reflexivity.
unfold PTree_samedom, PTree_map3 in *.
revert r1 r2 r3 n.
revert m2 H m3 H0; induction m1; destruct m2; intro H;
 simpl in H; try destruct H;
 destruct m3; simpl; intro H1; try destruct H1;
intros; auto.
- f_equal; auto.
- rewrite IHm1_2 by auto. apply IHm1_1; auto.
- rewrite <- IHm1 by auto. auto.
- rewrite IHm1_2 by auto. rewrite <- IHm1_1; auto.
Qed.

Lemma PTree_samedom_sym:
  forall {A B}  (ma: PTree.t A) (mb: PTree.t B),
  PTree_samedom ma mb -> PTree_samedom mb ma.
Proof.
intros ? ? ma mb.
destruct ma as [|ma], mb as [|mb]; simpl; try tauto.
revert mb; induction ma; destruct mb; simpl in *; try tauto;
 auto; intros [? ?]; split; auto.
Qed.

Lemma xelements_append':
    forall {A} (m: tree' A) i k,
    xelements' m i k = xelements' m i nil ++ k.
  Proof.
    intros.
    rewrite <- (app_nil_l k).
    rewrite xelements'_append. auto.
  Qed.


Lemma xelements_cons:
    forall {A} (m: tree' A) i y k,
    xelements' m i (y::k) = xelements' m i (y::nil) ++ k.
  Proof.
    intros.
    change (y::k) with ((y::nil)++k). apply xelements'_append.
  Qed.

Lemma PTree_domain_eq_elements:
 forall {A B} (ma: PTree.t A) (mb: PTree.t B),
  PTree_samedom ma mb ->
  List.map fst (PTree.elements ma) = List.map fst (PTree.elements mb).
Proof.
intros.
unfold PTree.elements.
forget 1%positive as n.
destruct ma as [|ma], mb as [|mb]; try contradiction H.
auto.
red in H.
revert mb H n; induction ma; destruct mb; intros; auto;
simpl in *; try destruct H; auto; f_equal; auto.
rewrite !(xelements_append'  _ _ (xelements' _ _ _)), !List.map_app.
f_equal; auto.
rewrite !(xelements_append' _ _ (_ ::_)), !List.map_app. f_equal; auto.
rewrite !(xelements_cons _ _ _ (xelements' _ _ _)), !List.map_app.
f_equal; auto.
rewrite !(xelements_append' _ _ (_::_)),  !List.map_app. f_equal; auto.
Qed.

Require compcert.common.Errors.

Local Notation "'OK'" := (Errors.OK).

Fixpoint merge_PTrees' {X} (merge: X -> X -> Errors.res X) (a b: tree' X) : Errors.res (tree' X) :=
 let gt (m1 m2: tree' X) (f: tree' X -> tree' X) :=  
       match merge_PTrees' merge m1 m2 with Errors.OK m => Errors.OK (f m) | e => e end in
 let gt' (m1 m2: tree' X) (f: tree' X -> Errors.res (tree' X)) :=  
       match merge_PTrees' merge m1 m2 with Errors.OK m => f m | e => e end in
 let gx (x1 x2: X) (f: X -> tree' X) :=
       match merge x1 x2 with Errors.OK x => Errors.OK (f x) | Errors.Error msg => Errors.Error msg end in
 let gx' (x1 x2: X) (f: X -> Errors.res (tree' X)) :=
       match merge x1 x2 with Errors.OK x => f x | Errors.Error msg => Errors.Error msg end in
 match a, b with
 | Node001 r1, Node001 r2 => gt r1 r2 Node001
 | Node001 r1, Node010 x2 => OK (Node011 x2 r1)
 | Node001 r1, Node011 x2 r2 => gt r1 r2 (fun r => Node011 x2 r)
 | Node001 r1, Node100 l2 => OK (Node101 l2 r1)
 | Node001 r1, Node101 l2 r2 => gt r1 r2 (fun r => Node101 l2 r)
 | Node001 r1, Node110 l2 x2 => OK (Node111 l2 x2 r1)
 | Node001 r1, Node111 l2 x2 r2 => gt r1 r2 (fun r => Node111 l2 x2 r)
 | Node010 x1, Node001 r2 => OK (Node011 x1 r2)
 | Node010 x1, Node010 x2 => gx x1 x2 (fun x => Node010 x)
 | Node010 x1, Node011 x2 r2 => gx x1 x2 (fun x => Node011 x r2)
 | Node010 x1, Node100 l2 => OK (Node110 l2 x1)
 | Node010 x1, Node101 l2 r2 => OK (Node111 l2 x1 r2)
 | Node010 x1, Node110 l2 x2 =>  gx x1 x2  (fun x => Node110 l2 x)
 | Node010 x1, Node111 l2 x2 r2 =>  gx x1 x2 (fun x => Node111 l2 x r2)
 | Node011 x1 r1, Node001 r2 => gt r1 r2 (fun r => Node011 x1 r)
 | Node011 x1 r1, Node010 x2 =>  gx x1 x2 (fun x => Node011 x r1)
 | Node011 x1 r1, Node011 x2 r2 => gx' x1 x2 (fun x => gt r1 r2 (fun r => Node011 x r))
 | Node011 x1 r1, Node100 l2 => OK (Node111 l2 x1 r1)
 | Node011 x1 r1, Node101 l2 r2 => gt r1 r2 (fun r => Node111 l2 x1 r)
 | Node011 x1 r1, Node110 l2 x2 =>gx x1 x2 (fun x => Node111 l2 x r1)
 | Node011 x1 r1, Node111 l2 x2 r2 => gx' x1 x2 (fun x => gt r1 r2 (fun r => Node111 l2 x r))
 | Node100 l1, Node001 r2 => OK (Node101 l1 r2)
 | Node100 l1, Node010 x2 => OK (Node110 l1 x2)
 | Node100 l1, Node011 x2 r2 => OK (Node111 l1 x2 r2)  
 | Node100 l1, Node100 l2 => gt l1 l2 (fun l => Node100 l)
 | Node100 l1, Node101 l2 r2 => gt l1 l2 (fun l => Node101 l r2)
 | Node100 l1, Node110 l2 x2 => gt l1 l2 (fun l => Node110 l x2)
 | Node100 l1, Node111 l2 x2 r2 => gt l1 l2 (fun l => Node111 l x2 r2)
 | Node101 l1 r1, Node001 r2 => gt r1 r2 (fun r => Node101 l1 r)
 | Node101 l1 r1, Node010 x2 => OK (Node111 l1 x2 r1)
 | Node101 l1 r1, Node011 x2 r2 => gt r1 r2 (fun r => Node111 l1 x2 r)
 | Node101 l1 r1, Node100 l2 => gt l1 l2 (fun l => Node101 l r1)
 | Node101 l1 r1, Node101 l2 r2 => gt' l1 l2 (fun l => gt r1 r2 (fun r => Node101 l r))
 | Node101 l1 r1, Node110 l2 x2 => gt l1 l2 (fun l => Node111 l x2 r1)
 | Node101 l1 r1, Node111 l2 x2 r2 => gt' l1 l2 (fun l => gt r1 r2 (fun r => Node111 l x2 r))
 | Node110 l1 x1, Node001 r1 => OK (Node111 l1 x1 r1)
 | Node110 l1 x1, Node010 x2 => gx x1 x2 (fun x => Node110 l1 x)
 | Node110 l1 x1, Node011 x2 r2 => gx x1 x2 (fun x => Node111 l1 x r2)
 | Node110 l1 x1, Node100 l2 => gt l1 l2 (fun l => Node110 l x1)
 | Node110 l1 x1, Node101 l2 r2 =>  gt l1 l2 (fun l => Node111 l x1 r2)
 | Node110 l1 x1, Node110 l2 x2 => gt' l1 l2 (fun l => gx x1 x2 (fun x => Node110 l x))
 | Node110 l1 x1, Node111 l2 x2 r2 => gt' l1 l2 (fun l => gx x1 x2 (fun x => Node111 l x r2))
 | Node111 l1 x1 r1, Node001 r2 => gt r1 r2 (fun r => Node111 l1 x1 r)
 | Node111 l1 x1 r1, Node010 x2 => gx x1 x2 (fun x => Node111 l1 x r1)
 | Node111 l1 x1 r1, Node011 x2 r2 => gt' r1 r2 (fun r => gx x1 x2 (fun x => Node111 l1 x r))
 | Node111 l1 x1 r1, Node100 l2 => gt l1 l2 (fun l => Node111 l x1 r1)
 | Node111 l1 x1 r1, Node101 l2 r2 => gt' l1 l2 (fun l => gt r1 r2 (fun r => Node111 l x1 r))
 | Node111 l1 x1 r1, Node110 l2 x2 => gt' l1 l2 (fun l => gx x1 x2 (fun x => Node111 l x r1))
 | Node111 l1 x1 r1, Node111 l2 x2 r2 => gt' l1 l2 (fun l => gx' x1 x2 (fun x => gt r1 r2 (fun r => Node111 l x r)))
 end.

Definition merge_PTrees {X} (merge: X -> X -> Errors.res X) (a b: PTree.t X) : Errors.res (PTree.t X) :=
 match a with
 | Empty => OK b 
 | Nodes a' => match b with
                        | Empty => OK a
                        | Nodes b' => Errors.bind (merge_PTrees' merge a' b') (fun m => OK (Nodes m)) 
 end                 end.

Import ListNotations.

Definition merge_consistent_PTrees {X} (eqb: X -> X -> bool) (a b: PTree.t X) 
      : Errors.res (PTree.t X) :=
  merge_PTrees (fun x y => if eqb x y then Errors.OK x else Errors.Error [Errors.MSG "inconsistent PTrees"]) a b.

Lemma merge_PTrees_e:
 forall i {A} (p1 p2 p : PTree.t A) merge,
  merge_PTrees merge p1 p2 = Errors.OK p ->
  match PTree.get i p1, PTree.get i p2 with
  | None, None =>  PTree.get i p = None
  | Some x1, None => PTree.get i p = Some x1
  | None, Some x2 => PTree.get i p = Some x2
  | Some x1, Some x2 => exists x, merge x1 x2 = Errors.OK x
                                         /\ PTree.get i p = Some x
   end.
Proof.
intros i A.
revert i.
assert (H99: forall a: option A, match a with Some x => a = Some x | None => a = None end).
destruct a; auto.
intros.
destruct p1 as [|m1]; simpl.
inv H. destruct (p ! i); auto.
destruct p2 as [|m2]; simpl in *.
inv H; unfold get; simpl.
destruct (get' i m1); auto.
unfold get.
Errors.monadInv H.
revert m2 x EQ i.
induction m1; destruct m2; intros; simpl in EQ;
repeat match goal with H: match ?A with _ => _ end = _ |- _ => destruct A eqn:?H; inv H end;
repeat match goal with H: OK _ = OK _ |- _ => inv H end;
repeat match goal with H: _, H': _ = OK _ |- _ => specialize (H _ _ H'); clear H' end;
destruct i; simpl; auto; try match goal with H: _ |- _ => apply H end;
eauto.
Qed.


Lemma merge_consistent_PTrees_e: forall {X} (eqX: X -> X -> bool)
  (eqX_prop: forall x y, eqX x y = true -> x=y)
  (eqX_refl: forall x, eqX x x = true)
  (m1 m2 m: PTree.t X),
  merge_consistent_PTrees eqX m1 m2 = Errors.OK m ->
  forall i, 
              match PTree.get i m1, PTree.get i m2 with
              | None, a => PTree.get i m = a
              | a, None => PTree.get i m = a
              | Some x, Some y => eqX x y = true /\ PTree.get i m = Some x
              end.
Proof.
intros.
apply (merge_PTrees_e i) in H.
destruct (m1 ! i).
destruct (m2 ! i).
destruct H as [x1 [? ?]].
destruct (eqX x x0) eqn:?H.
inv H; auto.
inv H.
auto.
destruct (m2 ! i); auto.
Qed.

Lemma merge_consistent_PTrees_e': forall {X} (eqX: X -> X -> bool)
  (eqX_prop: forall x y, eqX x y = true -> x=y)
  (eqX_refl: forall x, eqX x x = true)
  (m1 m2 m: PTree.t X),
  merge_consistent_PTrees eqX m1 m2 = Errors.OK m ->
  forall (i : positive) (x: X),
  m ! i = Some x <-> m1 ! i = Some x \/ m2 ! i = Some x.
Proof.
 intros. 
 apply @merge_consistent_PTrees_e with (i:=i) in H; auto.
 destruct (m1 ! i) eqn:?H.
 destruct (m2 ! i) eqn:?H.
 destruct H. apply eqX_prop in H; subst x1.
 rewrite H2. split; intro. inv H ;auto. destruct H; inv H; auto.
 rewrite H.  split; intro.  inv H2; auto. destruct H2; inv H2; auto.
 rewrite H.  split; intro.  inv H1; auto. destruct H1; inv H1; auto.
Qed.

Lemma merge_PTrees_map1:
 forall {A} (f: A -> A -> Errors.res A) m1 m2 m, 
     merge_PTrees f m1 m2 = Errors.OK m ->
   forall {B} (g: A -> B) (h: B -> B -> Errors.res B),
     (forall x y z, f x y = Errors.OK z -> h (g x) (g y) = Errors.OK (g z)) ->
    merge_PTrees h (PTree.map1 g m1) (PTree.map1 g m2) = 
      Errors.OK (PTree.map1 g m).
Proof.
intros.
revert m2 m H.
rename H0 into FGH.
destruct m1 as [|m1], m2 as [|m2]; simpl.
1,2,3: intros; inv H; reflexivity.
unfold Errors.bind.
intros.
destruct (merge_PTrees' f m1 m2) eqn:E; inv H.
rename t0 into m.
revert m2 m E; induction m1; destruct m2; simpl; intros;
repeat match goal with
           | H: OK _ = OK _ |- _ => inv H
           | H: match ?A with _ => _ end = _ |- _ => destruct A eqn:?H; inv H
           | H: _, H': _ = OK _ |- _ => specialize (H _ _ H'); clear H' 
           | H': _ = OK _ |- _ => specialize (FGH _ _ _ H'); clear H' 
           end;
  rewrite ?FGH;
  try reflexivity.
Qed.

Lemma merge_PTrees_empty1:
  forall {X: Type} (merge: X -> X -> Errors.res X) m, merge_PTrees merge (PTree.empty _) m = Errors.OK m.
Proof.
intros. destruct m; simpl; auto.
Qed.

Lemma merge_PTrees_empty2:
  forall {X: Type} (merge: X -> X -> Errors.res X) m, merge_PTrees merge m (PTree.empty _) = Errors.OK m.
Proof.
intros. destruct m; simpl; auto.
Qed.

Fixpoint PTree_filter' {A} (f: positive * A -> bool) (i: positive) (m: tree' A) : PTree.t A  :=
  match m with
  | Node001 r => Node Empty None (PTree_filter' f (xI i) r)
  | Node010 x => if f (i,x) then Nodes m else Empty
  | Node011 x r => Node Empty (if f (i,x) then (Some x) else None) (PTree_filter' f (xI i) r)
  | Node100 l => Node (PTree_filter' f (xO i) l) None Empty
  | Node101 l r => Node (PTree_filter' f (xO i) l) None (PTree_filter' f (xI i) r)
  | Node110 l x => Node (PTree_filter' f (xO i) l) (if f (i,x) then (Some x) else None) Empty
  | Node111 l x r=> Node (PTree_filter' f (xO i) l) (if f (i,x) then (Some x) else None) (PTree_filter' f (xI i) r)
  end.

Definition PTree_filter {A} (f: positive * A -> bool) (m: PTree.t A) := 
 match m with Empty => Empty | Nodes m' => PTree_filter' f xH m' end.

Lemma PTree_map1_map3:
 forall {A B C D E}  (g: D -> E) (f: A -> B -> C -> D) d e
(m1: PTree.t A) (m2: PTree.t B) (m3: PTree.t C),
  PTree_samedom m1 m2 -> PTree_samedom m1 m3 ->
  PTree.map1 g (PTree_map3 f d m1 m2 m3) = 
  PTree_map3 (fun x1 x2 x3 => g (f x1 x2 x3)) e m1 m2 m3.
Proof.
intros.
destruct m1 as [|m1], m2 as [|m2]; try contradiction; destruct m3 as [|m3]; try contradiction.
reflexivity.
red in H, H0.
unfold PTree_map3.
simpl. f_equal.
revert m2 H m3 H0.
induction m1; destruct m2; intro H; try destruct H; destruct m3; intro H2; try destruct H2;
simpl in *;
repeat match goal with H:_, H1: PTree_samedom' _ _ |- _ => specialize (H _ H1); clear H1 end;
congruence.
Qed.

Lemma PTree_map3_2:
 forall {A B C} d
(m1: PTree.t A) (m2: PTree.t B) (m3: PTree.t C),
  PTree_samedom m1 m2 ->
  PTree_samedom m1 m3 ->
  PTree_map3 (fun x1 x2 x3 => x2) d m1 m2 m3 = m2.
Proof.
destruct m1 as [|m1], m2 as [|m2]; try contradiction; destruct m3 as [|m3]; try contradiction.
reflexivity.
simpl. intros. f_equal.
revert m2 H m3 H0.
induction m1; destruct m2; intro H; try destruct H; destruct m3; intro H2; try destruct H2;
simpl in *;
repeat match goal with H:_, H1: PTree_samedom' _ _ |- _ => specialize (H _ H1); clear H1 end;
congruence.
Qed.

Lemma PTree_map3_1:
 forall {A B C} d
(m1: PTree.t A) (m2: PTree.t B) (m3: PTree.t C),
  PTree_samedom m1 m2 ->
  PTree_samedom m1 m3 ->
  PTree_map3 (fun x1 x2 x3 => x1) d m1 m2 m3 = m1.
Proof.
destruct m1 as [|m1], m2 as [|m2]; try contradiction; destruct m3 as [|m3]; try contradiction.
reflexivity.
simpl. intros. f_equal.
revert m2 H m3 H0.
induction m1; destruct m2; intro H; try destruct H; destruct m3; intro H2; try destruct H2;
simpl in *;
repeat match goal with H:_, H1: PTree_samedom' _ _ |- _ => specialize (H _ H1); clear H1 end;
congruence.
Qed.

Lemma PTree_map3_3:
 forall {A B C} d
(m1: PTree.t A) (m2: PTree.t B) (m3: PTree.t C),
  PTree_samedom m1 m2 ->
  PTree_samedom m1 m3 ->
  PTree_map3 (fun x1 x2 x3 => x3) d m1 m2 m3 = m3.
Proof.
destruct m1 as [|m1], m2 as [|m2]; try contradiction; destruct m3 as [|m3]; try contradiction.
reflexivity.
simpl. intros. f_equal.
revert m2 H m3 H0.
induction m1; destruct m2; intro H; try destruct H; destruct m3; intro H2; try destruct H2;
simpl in *;
repeat match goal with H:_, H1: PTree_samedom' _ _ |- _ => specialize (H _ H1); clear H1 end;
congruence.
Qed.

Definition sub_option {A} (x y : option A) :=
match x with
| Some x' => y = Some x'
| None => True
end.

Definition PTree_sub {A} (m1 m2 : PTree.t A) :=
  forall id, sub_option (m1 ! id) (m2 ! id).


Lemma PTree_Equal_e:
 forall {A} (a b: PTree.t A),
  PTree_Properties.Equal (Eqsth _) a b ->
  forall i, a ! i = b ! i.
Proof.
intros.
specialize (H i).
destruct (a ! i), (b ! i); try contradiction; auto.
Qed.

Definition and_option_Prop (a b: option Prop) : option Prop :=
match a, b with
| None, _ => b
| _, None => a
| Some x, Some y => Some (x /\ y)
end.

Definition interpret_option_Prop (a: option Prop) : Prop :=
 match a with Some x => x | None => True end.

Fixpoint PTree_Foralln' {A: Type} (F: positive -> A -> option Prop) 
  (i: positive) (m: tree' A): option Prop :=
match m with
| Node001 r => PTree_Foralln' F (xI i) r
| Node010 x => F (prev i) x
| Node011 x r => and_option_Prop (F (prev i) x) (PTree_Foralln' F (xI i) r)
| Node100 l => PTree_Foralln' F (xO i) l
| Node101 l r => and_option_Prop (PTree_Foralln' F (xO i) l) (PTree_Foralln' F (xI i) r)
| Node110 l x =>and_option_Prop (PTree_Foralln' F (xO i) l) (F (prev i) x)
| Node111 l x r => and_option_Prop (PTree_Foralln' F (xO i) l) 
                                 (and_option_Prop (F (prev i) x) (PTree_Foralln' F (xI i) r))
end.

Definition PTree_Foralln {A: Type} (F: positive -> A -> option Prop) 
      (m: PTree.t A): Prop :=
 match m with
 | Empty => True
 | Nodes m' =>interpret_option_Prop (PTree_Foralln' F xH m')
 end.

Lemma interpret_option_Prop_and:
 forall a b, interpret_option_Prop (and_option_Prop a b) -> 
       interpret_option_Prop a /\ interpret_option_Prop b.
Proof.
destruct a,b; simpl; auto.
Qed.

Lemma PTree_Foralln_e:
  forall A (F: positive -> A -> option Prop) m, 
  PTree_Foralln F m ->
  forall i x, (m ! i) = Some x -> interpret_option_Prop (F i x).
Proof.
intros.
destruct m as [|m].
inv H0.
unfold get in H0. red in H.
change i with (PTree.prev_append 1 i).
forget 1%positive as j.
revert i H0 j H; induction m; destruct i; simpl in *; intros;
try apply (IHm _ H0 _ H);
try discriminate;
try inv H0; auto;
repeat match goal with H: interpret_option_Prop (and_option_Prop _ _) |- _ =>
 apply interpret_option_Prop_and in H; destruct H
end;
auto;
try (eapply IHm in H0; try eassumption; auto).
eapply IHm2 in H0; try eassumption; auto.
eapply IHm1 in H; try eassumption; auto.
eapply IHm in H; eauto.
eapply IHm2 in H1; eauto.
eapply IHm1 in H; eauto.
Qed.

Lemma PTree_samedom_trans {A B C}:
 forall  (m1: PTree.t A) (m2: PTree.t B) (m3: PTree.t C),
  PTree_samedom m1 m2 -> PTree_samedom m2 m3 -> PTree_samedom m1 m3.
Proof.
destruct m1 as [|m1], m2 as [|m2], m3 as [|m3]; intros;
try contradiction; auto.
red in H,H0|-*.
revert m2 H m3 H0; induction m1; destruct m2; intro H; try destruct H;
 destruct m3; intro H1; try destruct H1; simpl in *; eauto.
Qed.

Lemma PTree_samedom_map1: forall {A B} (f: A -> B),
 forall m,  PTree_samedom (PTree.map1 f m) m.
Proof.
destruct m as [|m]; simpl; auto.
induction m; simpl; intros; auto.
Qed.

