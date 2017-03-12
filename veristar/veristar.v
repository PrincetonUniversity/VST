(** The main VeriStar procedures.
Entailments are of the form [Pi /\ Sigma ==> Pi' /\ Sigma'].  Here,
-[Pi] and [Pi'] are sets of equalities between program variables.
-[Sigma] and [Sigma'] are spatial atoms in a limited subset of separation logic.
*)

Load loadpath.
Require Import ZArith Znumtheory Coq.Lists.List.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.heapresolve.

(* To build the model-based saturation system, replace the following line with

       Require Import veristar.superpose_modelsat. *)

(*Require Import veristar.superpose. *)
Require Import veristar.superpose_modelsat.

Import Superposition. Import HeapResolve.
Require Recdef.

(** The VeriStar interface *)

Inductive veristar_result :=
| Valid : veristar_result
| C_example : model -> veristar_result
| Aborted : list clause -> clause -> veristar_result.

Module Type VERISTAR.

Parameter check_entailment : entailment -> veristar_result.

End VERISTAR.

(** The VeriStar implementation *)

Module VeriStar.

Inductive veristar_result :=
| Valid : veristar_result
| C_example : model -> veristar_result
| Aborted : list clause -> clause -> veristar_result.

Definition pureb c := match c with PureClause _ _ _ _ => true | _ => false end.

Definition pure_clauses := filter pureb.

Definition is_empty_clause (c : clause) :=
  match c with PureClause nil nil _ _ => true | _ => false end.

Definition pures := M.filter pureb.

Lemma Ppred_decrease n :
  (n<>1)%positive -> (nat_of_P (Ppred n)<nat_of_P n)%nat.
Proof.
intros; destruct (Psucc_pred n) as [Hpred | Hpred]; try contradiction;
  pattern n at 2; rewrite <- Hpred; rewrite nat_of_P_succ_morphism; omega.
Qed.

(** Top-level redundancy elimination *)

Section RedundancyElim.
Context {A: Type}.
Variable (cmp: A -> A->comparison).
(*begin hide*)
Definition naive_sublist (l1 l2: list A) :=
  forallb (fun a => existsb (fun b => isEq (cmp a b)) l2) l1.
(*end hide*)

(** Linear time sublist for sorted lists *)

Fixpoint sublistg (l1 l2: list A) :=
  match l1, l2 with
  | a::l1', b::l2' => andb (isEq (cmp a b)) (sublistg l1' l2')
  | nil, _ => true
  | _::_, nil => false
  end.

Fixpoint sublist (l1 l2: list A) :=
  match l1, l2 with
  | a::l1', b::l2' =>
    if isEq (cmp a b) then sublistg l1' l2' else sublist l1 l2'
  | nil, _ => true
  | _::_, nil => false
  end.

End RedundancyElim.

Definition impl_pure_clause (c d: clause) :=
  match c, d with PureClause gamma delta _ _, PureClause gamma' delta' _ _ =>
    andb (sublist pure_atom_cmp gamma gamma')
             (sublist pure_atom_cmp delta delta')
  | _, _ => false
  end.

Definition relim1 (c: clause) (s: M.t) :=
  M.filter (fun d => negb (impl_pure_clause c d)) s.

Definition incorp (s t : M.t) :=
  M.union s (M.fold (fun c t0 => relim1 c t0) s t).

(** The main loop of the prover *)

(* begin show *)

Function the_loop
  (n: positive) (sigma: list space_atom) (nc: clause)
  (s: M.t) (cl: clause) {measure nat_of_P n} : veristar_result :=
  if Coqlib.peq n 1 then Aborted (M.elements s) cl
  else match check_clauseset s with
  | (Superposition.Valid, units, _, _) => Valid
  | (Superposition.C_example R selected, units, s_star, _) =>
         let sigma' := simplify_atoms units sigma in
         let nc' := simplify units nc in
         let c := print_spatial_model (norm (print_wf_set selected)
                      (PosSpaceClause nil nil sigma')) R in
         let nu_s := incorp (print_wf_set (do_wellformed c)) s_star in
         if isEq (M.compare nu_s s_star)
         then if is_model_of_PI (List.rev R) (print_spatial_model nc' R)
              then let c' := print_spatial_model2 c (norm selected nc') R in
                   let pcns_u := pures (unfolding c c') in
                   let s_star' := incorp (print_unfold_set pcns_u) nu_s in
                   if isEq (M.compare nu_s s_star') then C_example R
                   else the_loop (Ppred n) sigma' nc' s_star' c
              else C_example R
         else the_loop (Ppred n) sigma' nc' nu_s c
  | (Superposition.Aborted l, units, _, _) => Aborted l cl
  end.
Proof.
intros; apply Ppred_decrease; auto.
intros; apply Ppred_decrease; auto.
Defined.

(* end show *)
(* Required to work around Coq bug #2613 *)
Implicit Arguments eq_sym.

Definition check_entailment (ent: entailment) : veristar_result :=
  let s := clause_list2set (pure_clauses (map order_eqv_clause (cnf ent)))
  in match ent with
     | Entailment (Assertion pi sigma) (Assertion pi' sigma') =>
       match mk_pureR pi, mk_pureR pi' with
       | (piplus, piminus), (pi'plus, pi'minus) =>
           the_loop 1000000 sigma (NegSpaceClause pi'plus sigma' pi'minus)
             (print_new_pures_set s) empty_clause
       end
     end.

End VeriStar.

