Require Import VST.floyd.base.

Ltac make_ground_PTree a :=
 let a := eval hnf in a in
 match a with
 | PTree.Leaf => constr:(a)
 | PTree.Node ?l ?o ?r => 
    let l := make_ground_PTree l in
    let r := make_ground_PTree r in
    let o := eval hnf in o in 
    constr:(PTree.Node l o r)
 end.

Ltac simpl_PTree_get_old :=
  repeat match goal with
         | |- context [PTree.get ?i' ?t] =>
           let i'' := eval hnf in i' in
               change (PTree.get i' t) with
               ((fix get (A : Type) (i : positive) (m : PTree.t A) {struct i} : option A :=
                 match m with
                 | PTree.Leaf => None
                 | PTree.Node l o r =>
                     match i with
                     | (ii~1)%positive => get A ii r
                     | (ii~0)%positive => get A ii l
                     | 1%positive => o
                     end
                 end) _ i'' t)
         end;
  cbv iota zeta beta.

Ltac simpl_PTree_get :=
  repeat match goal with
         | |- context [PTree.get ?i' ?t] =>
           let g := constr:(PTree.get i' t) in 
           let g := eval hnf in g in
           change (PTree.get i' t) with g
         end;
  cbv iota zeta beta.

Ltac simpl_eqb_type :=
  repeat
  match goal with
  | |- context [eqb_type ?t1 ?t2] =>
    let b := eval hnf in (eqb_type t1 t2) in
    change (eqb_type t1 t2) with b;
    cbv beta iota zeta
  end.

Ltac simpl_temp_types_get :=
  repeat
  match goal with
  | |- context [(temp_types ?Delta) ! ?i] =>
          let ret := eval hnf in ((temp_types Delta) ! i) in
          change ((temp_types Delta) ! i) with ret
  end.

Ltac pos_eqb_tac :=
  let H := fresh "H" in
  match goal with
  | |- context [Pos.eqb ?i ?j] => destruct (Pos.eqb i j) eqn:H; [apply Pos.eqb_eq in H | apply Pos.eqb_neq in H]
  end.


Definition VST_floyd_map {A B : Type} (f: A -> B): list A -> list B :=
  fix map (l : list A) : list B := match l with
                                   | nil => nil
                                   | a :: t => f a :: map t
                                   end.

Definition VST_floyd_app {A: Type}: list A -> list A -> list A :=
  fix app (l m : list A) {struct l} : list A :=
  match l with
  | nil => m
  | a :: l1 => a :: app l1 m
  end.

Definition VST_floyd_concat {A: Type}: list (list A) -> list A :=
  fix concat (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | x :: l0 => VST_floyd_app x (concat l0)
  end.

