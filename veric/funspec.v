From iris.algebra Require Import ofe list.
From VST.veric Require Import compspecs res_predicates.
(* funspecs are effectively dependent pairs of an algebra and a pair of assertions on that algebra.
   This means we have to take some care to define them in a way that avoids universe inconsistencies. *)

(* Reify the type of the funspec's WITH clause. *)
Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | CompspecsType: TypeTree
  | Mpred: TypeTree
(*  | DependentType: nat -> TypeTree *)
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
(*  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree*)
  | ListType: TypeTree -> TypeTree.

Fixpoint dependent_type_functor_rec (T : TypeTree) : oFunctor :=
  match T with
  | ConstType t => constOF (leibnizO t)
  | CompspecsType => constOF (leibnizO compspecs)
  | Mpred => idOF
  | ProdType a b => dependent_type_functor_rec a * dependent_type_functor_rec b
  | ArrowType a b => dependent_type_functor_rec a -n> dependent_type_functor_rec b
  | SigType _ f => sigTOF (fun i => dependent_type_functor_rec (f i))
  | ListType t => listOF (dependent_type_functor_rec t)
  end.

Definition ArgsTT A := ArrowType A (ArrowType (ConstType argsEnviron) Mpred).
Definition AssertTT A := ArrowType A (ArrowType (ConstType environ) Mpred).

Inductive funspec {Σ} :=
   mk_funspec (sig : typesig) (cc : calling_convention) (A: TypeTree)
     (P: dependent_type_functor_rec (ArgsTT A) mpred)
     (Q: dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.
