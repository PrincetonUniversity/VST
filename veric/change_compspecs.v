Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.type_induction.
Require Import VST.veric.composite_compute.
Require Import VST.veric.tycontext.
Require Import VST.veric.Cop2.

Section cs_preserve.

Context (cs_from cs_to: compspecs).

Definition eqb_member (it1 it2: ident * type): bool :=
  Pos.eqb (fst it1) (fst it2) && eqb_type (snd it1) (snd it2).

Definition test_aux (b: bool) (i: ident): bool :=
  b && match (@cenv_cs cs_from) ! i, (@cenv_cs cs_to) ! i with
       | Some co_from, Some co_to => eqb_list eqb_member (co_members co_from) (co_members co_to)
       | _, _ => false
       end.

Fixpoint cs_preserve_type (coeq: PTree.t bool) (t: type): bool :=
  match t with
  | Tarray t0 _ _ => cs_preserve_type coeq t0
  | Tstruct id _ => match coeq ! id with | Some b => test_aux b id | _ => true end
  | Tunion id _ => match coeq ! id with | Some b => test_aux b id | _ => true end
  | _ => true
  end.

Fixpoint cs_preserve_members (coeq: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | ((_, t) :: m) => andb (cs_preserve_type coeq t) (cs_preserve_members coeq m)
  end.

Class change_composite_env: Type := {
  coeq: PTree.t bool;
  coeq_consistent:
    forall i co b,
      (@cenv_cs cs_to) ! i = Some co ->
      coeq ! i = Some b ->
      b = cs_preserve_members coeq (co_members co);
  coeq_complete:
    forall i,
      (exists co, (@cenv_cs cs_to) ! i = Some co) <->
      (exists b, coeq ! i = Some b)
}.

Definition cs_preserve_env: PTree.t bool :=
  let l := composite_reorder.rebuild_composite_elements (@cenv_cs cs_to) in
  fold_right (fun (ic: positive * composite) (T0: PTree.t bool) => let (i, co) := ic in let T := T0 in PTree.set i (cs_preserve_members T (co_members co)) T) (PTree.empty _) l.

Lemma aux1: forall T co,
  (fix fm (l : list (ident * type * bool)) : bool :=
   match l with
   | nil => true
   | (_, _, b) :: l' => b && fm l'
   end)
  (map
     (fun it0 : positive * type =>
      let (i0, t0) := it0 in
      (i0, t0,
      type_func.F (fun _ : type => true) (fun (b : bool) (_ : type) (_ : Z) (_ : attr) => b)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id) T t0)) (co_members co)) =
  cs_preserve_members T (co_members co).
Proof.
  intros; unfold cs_preserve_members, cs_preserve_type.
  induction (co_members co) as [| [i t] ?].
  + auto.
  + simpl.
    f_equal; auto.
Qed.

Lemma aux2:
  type_func.Env (fun _ : type => true) (fun (b : bool) (_ : type) (_ : Z) (_ : attr) => b)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id)
        (fun _ : struct_or_union =>
         fix fm (l : list (ident * type * bool)) : bool :=
           match l with
           | nil => true
           | (_, _, b) :: l' => b && fm l'
           end) (composite_reorder.rebuild_composite_elements cenv_cs) =
  cs_preserve_env.
Proof.
  intros.
  unfold type_func.Env, type_func.env_rec, cs_preserve_env.
  f_equal.
  extensionality ic.
  destruct ic as [i co].
  extensionality T.
  f_equal.
  apply aux1.
Qed.

Lemma cs_preserve_env_consisent: forall (coeq: PTree.t bool),
  coeq = cs_preserve_env ->
  forall i co b,
    (@cenv_cs cs_to) ! i = Some co ->
    coeq ! i = Some b ->
    b = cs_preserve_members coeq (co_members co).
Proof.
  intros.
  pose proof @composite_reorder_consistent bool (@cenv_cs cs_to)
             (fun t => true)
             (fun b _ _ _ => b)
             (fun b id _ => test_aux b id)
             (fun b id _ => test_aux b id)
             (fun _ =>
                fix fm (l: list (ident * type * bool)): bool :=
                match l with
                | nil => true
                | (_, _, b) :: l' => b && (fm l')
                end)
             (@cenv_consistent cs_to)
    as HH.
  hnf in HH.
  subst coeq0.
  rewrite aux2 in HH.
  specialize (HH _ _ b H0 H1).
  rewrite HH, aux1; auto.
Qed.

Lemma cs_preserve_completeness: forall (coeq: PTree.t bool),
  coeq = cs_preserve_env ->
  forall i,
    (exists co, (@cenv_cs cs_to) ! i = Some co) <->
    (exists b, coeq ! i = Some b).
Proof.
  intros.
  pose proof @composite_reorder_complete bool (@cenv_cs cs_to)
             (fun t => true)
             (fun b _ _ _ => b)
             (fun b id _ => test_aux b id)
             (fun b id _ => test_aux b id)
             (fun _ =>
                fix fm (l: list (ident * type * bool)): bool :=
                match l with
                | nil => true
                | (_, _, b) :: l' => b && (fm l')
                end)
    as HH.
  hnf in HH.
  subst.
  rewrite aux2 in HH.
  auto.
Qed.

End cs_preserve.

Ltac make_cs_preserve cs_from cs_to :=
  let coeq0 := eval cbv in (cs_preserve_env cs_from cs_to) in
  let Hcoeq0 := constr: (eq_refl: coeq0 = cs_preserve_env cs_from cs_to) in
  let coeq0_consistent := constr: (cs_preserve_env_consisent cs_from cs_to coeq0 Hcoeq0) in
  let coeq0_complete := constr: (cs_preserve_completeness cs_from cs_to coeq0 Hcoeq0) in
  refine (  {| coeq := coeq0 ;
               coeq_consistent := coeq0_consistent;
               coeq_complete := coeq0_complete |}).
