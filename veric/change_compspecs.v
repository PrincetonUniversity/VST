Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.type_induction.
Require Import VST.veric.composite_compute.
Require Import VST.veric.tycontext.

Section cs_preserve.

Context (cs_from cs_to: compspecs).
SearchAbout type_eq.
SearchAbout type_eq.
Locate type_eq.
SearchAbout (@eq attr). sumbool.
Definition eqb_ident: ident -> ident -> bool := Pos.eqb.

Definition 

Definition eqb_member (it1 it2: ident * type): bool :=
  Pos.eqb (fst it1) (fst it2) && eqb_type (snd it1) (snd it2).

Definition test_aux (b: bool) (i: ident): bool :=
  b && match cs_from, cs_to with
       | Some co_from, Some co_to => list_eq co_members (

Fixpoint cs_preserve_type (coeq: PTree.t bool) (t: type): bool :=
  match t with
  | Tarray t0 _ _ => cs_preserve_type coeq t0
  | Tstruct id _ => match coeq ! id with | Some true => true | _ => false end
  | Tunion id _ => match coeq ! id with | Some true => true | _ => false end
  | _ => true
  end.

Fixpoint cs_preserve_members (coeq: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | ((_, t) :: m) => andb (cs_preserve_type coeq t) (cs_preserve_members coeq m)
  end.

Class change_composite_env (): Type := {
  coeq: PTree.t bool;
  coeq_consistent:
    forall i co b,
      cenv ! i = Some co ->
      coeq ! i = Some b ->
      b = cs_preserve_members coeq (co_members co)
      }.

  Definition legal_alignas_env_complete (cenv: composite_env) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall i,
      (exists co, cenv ! i = Some co) <->
      (exists la, la_env ! i = Some la).