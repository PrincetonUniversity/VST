Inductive reptype_skeleton : Type :=
  | RepDefault: reptype_skeleton
  | RepVar: reptype_skeleton
  | RepPair: reptype_skeleton -> reptype_skeleton -> reptype_skeleton
(*  | RepNil: reptype_skeleton *)
(*  | RepCons: reptype_skeleton -> reptype_skeleton -> reptype_skeleton *)
  | RepInl: reptype_skeleton -> reptype_skeleton
  | RepInr: reptype_skeleton -> reptype_skeleton.

Ltac simple_reify v :=
  match v with
  | pair ?v1 ?v2 =>
    let e1 := simple_reify v1 in
    let e2 := simple_reify v2 in
    constr:(RepPair e1 e2)
  | @inl _ _ ?v0 =>
    let e0 := simple_reify v0 in
    constr:(RepInl e0)
  | @inr _ _ ?v0 =>
    let e0 := simple_reify v0 in
    constr:(RepInr e0)
  | _ =>
    constr:(RepVar)
  end.

Goal 0 = 0.
let e := simple_reify ((1, 1), (1, (1, 1))) in pose e.
reflexivity.
Qed.
