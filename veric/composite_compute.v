Require Import Coq.Sorting.Permutation.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.

Fixpoint relative_defined_type {A: Type} (l: list (ident * A)) (t: type): Prop :=
  match t with
  | Tarray t' _ _ => relative_defined_type l t'
  | Tstruct id _ => In id (map fst l)
  | Tunion id _ => In id (map fst l)
  | _ => True
  end.

Module type_func.
Section type_func.

Context {A: Type}
        (f_default: type -> A)
        (f_array: A -> Z -> attr -> A)
        (f_struct: A -> attr -> A)
        (f_union: A -> attr -> A)
        (f_member: struct_or_union -> list (ident * A) -> A).

Fixpoint F (env: PTree.t A) (t: type): A :=
  match t with
  | Tarray t n a => f_array (F env t) n a
  | Tstruct id a =>
      match env ! id with
      | Some v => f_struct v a
      | None => f_default t
      end
  | Tunion id a =>
      match env ! id with
      | Some v => f_union v a
      | None => f_default t
      end
  | _ => f_default t
  end.

Fixpoint Env (l: list (positive * composite)): PTree.t A :=
  fold_right
    (fun (ic: positive * composite) env =>
       let (i, co) := ic in
       PTree.set i
                 (f_member (co_su co)
                           (map
                              (fun it0: positive * type =>
                                 let (i0, t0) := it0 in (i0, F env t0))
                              (co_members co)))
                 env)
    (PTree.empty A)
    l.

Lemma Consistent: forall env l,
  Permutation l (PTree.elements env) ->
  (forall l1 i co l2,
      l = l1 ++ (i, co) :: l2 ->
      Forall (relative_defined_type l1) (map snd (co_members co))) ->
  forall i co a,
    PTree.get i env = Some co ->
    PTree.get i (Env (PTree.elements env)) = Some a ->
    a = f_member (co_su co) (map
                              (fun it0: positive * type =>
                                 let (i0, t0) := it0 in
                                 (i0, F (Env l) t0))
                              (co_members co)).
                 .