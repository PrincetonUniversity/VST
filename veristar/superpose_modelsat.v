Load loadpath.
Require Import ZArith List Bool Recdef.
Require Import Coqlib.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.cclosure veristar.basic veristar.compare.

(** * Superposition:
a superposition-based theorem prover for ground clauses, with a new,
counterexample-guided saturation strategy
*)

Module Type SUPERPOSITION.

Definition model := list (var * expr).

Inductive superposition_result : Type :=
| Valid : superposition_result
| C_example : model -> M.t -> superposition_result
| Aborted : list clause -> superposition_result.

(** check:
-Check a pure entailment of the form [Pi ==> Pi']
-Returns, when a [C_example] is found, the model exhibiting the [C_example] and
 the final clause set (i.e., the set of clauses derived during proof search)
*)

Parameter check : entailment -> superposition_result * list clause * M.t*M.t.

(** check_clauseset:
Just like check, except we operate instead on an initial _set_ of clauses.
This function is the one called by the main theorem prover, veristar.v. *)

Parameter check_clauseset : M.t -> superposition_result * list clause * M.t*M.t.

(** is_model_of_PI:
Check whether R is a model of Pi+ /\ Pi-; used in the Veristar main loop *)

Parameter is_model_of_PI : model -> clause -> bool.

Parameter rewrite_by : expr -> expr -> pure_atom -> pure_atom.

Parameter demodulate : clause -> clause -> clause.

Parameter simplify : list clause -> clause -> clause.

Parameter simplify_atoms : list clause -> list space_atom -> list space_atom.

End SUPERPOSITION.

(** Module Superposition:
 *)

Module Superposition <: SUPERPOSITION.

Definition model := list (var * expr).

Inductive superposition_result : Type :=
| Valid : superposition_result
| C_example : model -> M.t -> superposition_result
| Aborted : list clause -> superposition_result.

(* side condition used in superposition rules below *)
(* begin hide *)
Definition pure_atom_gt1 a (l: list pure_atom) :=
  match l with b :: _ => pure_atom_gt a b | _ => true end.
(* end hide *)

(** ef:
Equality factoring *)

Fixpoint ef_aux neg u0 u v pos0 pos l0 : list clause :=
  match pos with
  | (Eqv s t as a2) :: pos' =>
    if expr_eq s u && greater_than_all u0 neg
    then mkPureClause
           (insu_atm (norm_pure_atom (Eqv v t)) neg)
           (insu_atm (norm_pure_atom (Eqv u t))
                 (merge pure_atom_cmp (List.rev pos0) pos)) ::
             ef_aux neg u0 u v (insu_atm a2 pos0) pos' l0
    else l0
  | nil => l0
  end.

Definition ef (cty : ce_type) (c : clause) l0 : list clause :=
  match cty, c with
  | CexpEf, PureClause neg (Eqv (Var u0 as u) v :: pos) _ _ =>
    if greater_than_all u0 neg then ef_aux neg u0 u v nil pos l0
    else l0
  | _, _ => l0
  end.

(** sp:
left and right superposition *)

Definition sp (cty : ce_type) (c d : clause) l0 : list clause :=
  match cty, c, d with
  (* negative (left) superposition *)
  | CexpL, PureClause (Eqv s' v :: neg') pos' _ _,
           PureClause neg (Eqv (Var s0 as s) t :: pos) _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && greater_than_all s0 neg
    then mkPureClause
      (insu_atm (norm_pure_atom (Eqv t v)) (merge pure_atom_cmp neg neg'))
      (merge pure_atom_cmp pos pos') :: l0
    else l0
  (* positive (right) superposition *)
  | CexpR, PureClause neg (Eqv (Var s0 as s) t :: pos) _ _,
           PureClause neg' (Eqv (Var s'0 as s') v :: pos') _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && pure_atom_gt1 (Eqv s' v) pos' &&
       pure_atom_gt (Eqv s t) (Eqv s' v) &&
       greater_than_all s0 neg && greater_than_all s'0 neg'
    then mkPureClause
      (merge pure_atom_cmp neg neg')
      (insu_atm (norm_pure_atom (Eqv t v)) (merge pure_atom_cmp pos pos')) :: l0
    else l0
  | _, _, _ => l0
  end.

(** Retractive rules:
    -demodulation (simplification by positive unit clauses),
    -equality resolution *)

(* u[s->t] *)
Definition rewrite_expr s t u := if expr_eq s u then t else u.

Definition rewrite_by s t atm :=
  match atm with Eqv u v =>
    if expr_eq s u then if expr_eq s v then norm_pure_atom (Eqv t t)
                        else norm_pure_atom (Eqv t v)
    else if expr_eq s v then norm_pure_atom (Eqv u t)
         else atm
  end.

Definition rewrite_in_space s t atm :=
  match atm with
  | Next u v => Next (rewrite_expr s t u) (rewrite_expr s t v)
  | Lseg u v => Lseg (rewrite_expr s t u) (rewrite_expr s t v)
  end.

Definition rewrite_clause_in_space c atm :=
  match c with
  | PureClause nil [Eqv s t] _ _ => rewrite_in_space s t atm
  | _ => atm
  end.

(** Rewrite by a positive unit clause *)

Definition demodulate (c d : clause) : clause :=
  match c, d with
  | PureClause nil [Eqv s t] _ _, PureClause neg pos _ _ =>
      mkPureClause (map (rewrite_by s t) neg) (map (rewrite_by s t) pos)
  | PureClause nil [Eqv s t] _ _, PosSpaceClause neg pos space =>
      PosSpaceClause (map (rewrite_by s t) neg) (map (rewrite_by s t) pos)
          (map (rewrite_in_space s t) space)
  | PureClause nil [Eqv s t] _ _, NegSpaceClause neg space pos =>
      NegSpaceClause (map (rewrite_by s t) neg) (map (rewrite_in_space s t) space)
          (map (rewrite_by s t) pos)
  | _, _ => d
  end.

(** Delete resolved negative atoms, i.e., atoms of the form [Eqv x x]
    lying in negative positions.  This is called equality resolution by some. *)

Definition delete_resolved (c : clause) : clause :=
  match c with
  | PureClause neg pos _ _ =>
     mkPureClause (sortu_atms (remove_trivial_atoms neg)) (sortu_atms pos)
  | _ => c
(*  | _ => mkPureClause nil [Eqv Nil Nil] (* impossible *)*)
  end.

(** Filter tautological clauses *)

Definition not_taut (c: clause) :=
  negb (match c with
        | PureClause neg pos _ _ =>
          existsb (fun a => existsb (fun b =>
                     pure_atom_eq a b) pos) neg ||
          existsb (fun a =>
            match a with Eqv e1 e2 => expr_eq e1 e2 end) pos
        | _ => false end).

(** Rewrite [c] by positive unit clauses in [l]. Delete resolved atoms
    from the resulting clause. Argument [l] is already sorted so no need to
    re-sort. *)

Definition simplify (l : list clause) (c : clause) : clause :=
  delete_resolved (fold_left (fun d c => demodulate c d) l c).

Definition simplify_atoms (l : list clause) (atms : list space_atom)
  : list space_atom :=
  fold_left (fun atms d => map (rewrite_clause_in_space d) atms) l atms.

(** Derive clauses from clause [c] and clauses [l] using [cty] inferences alone.
    Forward-simplify any resulting clauses using facts in [l] (note: we do no
    backward simplification here since this would greatly complicate the termination
    proof). *)

Definition infer (cty : ce_type) (c : clause) (l : list clause) : list clause :=
  print_inferred_list (rsort_uniq compare_clause
    (filter not_taut (map (simplify nil)
      (ef cty c (fold_left (fun l0 d => sp cty c d l0) l nil))))).

(** Model generation: build a candidate model for clauses [l] *)

Definition apply_model (R : model) (cl : clause) : clause :=
  fold_right (fun ve => subst_clause (fst ve) (snd ve)) cl R.

Definition is_model_of (R : model) (gamma delta : list pure_atom) : bool :=
  match fold_right (fun ve => subst_pures_delete (fst ve) (snd ve))
               (remove_trivial_atoms gamma) R,
          fold_right (fun ve => subst_pures (fst ve) (snd ve)) delta R with
  | _::_, _ => true
  | nil , delta' => negb (forallb nonreflex_atom delta')
  end.

(** Check whether R is a model of [Pi+ /\ Pi-]; used in the Veristar main loop *)

Definition is_model_of_PI (R: model) (nc : (*negative spatial*) clause) : bool :=
 match nc with NegSpaceClause pi_plus _ pi_minus =>
  match fold_right (fun ve =>
          subst_pures_delete (fst ve) (snd ve)) (remove_trivial_atoms pi_plus) R,
        fold_right (fun ve =>
          subst_pures (fst ve) (snd ve)) pi_minus R with
  | nil , pi_minus' => forallb nonreflex_atom pi_minus'
  | _ :: _ , _ => false
  end
 | _ => false
 end.

(** Is there a rewrite rule [v'->r] in [R] s.t. [v==v']? *)

Definition reduces (R: model) (v : var) :=
  existsb (fun ve' => if Ident.eq_dec v (fst ve') then true else false) R.

(** Does clause [cl] generate a new rewrite rule that must be added to the
    candidate model [R]? If so, return the rewrite rule paired with [cl]. Otherwise
    [cl] is a c-example for the current candidate model (invariant: [clause_generate
    R cl] is only called when [R] is [not] already a model for [cl]) so determine which
    type of c-example [cl] is, and return that as a value of [ce_type]. *)

Definition clause_generate (R : model) (cl : clause)
  : (var * expr * clause) + ce_type :=
  match cl with
  | PureClause gamma (Eqv (Var l' as l) r :: delta) _ _ as c' =>
      if greater_than_expr l' r && greater_than_all l' gamma &&
         greater_than_atoms (Eqv l r) delta
      then if reduces R l' then inr _ CexpR
           else if is_model_of (List.rev R) nil (map (rewrite_by l r) delta)
                then inr _ CexpEf else inl _ (l', r, cl)
      else inr _ CexpL
  | _ => inr _ CexpL
  end.

(** Construct a candidate model for [l] or fail with (1) the partial model built
    so far (for debugging); (2) the clause that failed; and (3) its [ce_type]. *)

Fixpoint partial_mod (R : model) (acc l : list clause)
  : (model * list clause) + (model * clause * ce_type) :=
  match l with
  | nil => inl _ (R, acc)
  | (PureClause gamma delta _ _) as cl :: l' =>
      if is_model_of (List.rev R) gamma delta then partial_mod R acc l'
      else match clause_generate R cl with
           | (inl (v, exp, cl')) => partial_mod ((v, exp) :: R) (cl' :: acc) l'
           | (inr cty) => inr _ (print_ce_clause R cl cty)
           end
  | _ => inl _ (R, acc)
  end.

Definition is_empty_clause (cl : clause) :=
  match cl with PureClause nil nil _ _ => true | _ => false end.

Definition is_unit_clause (cl : clause) :=
  match cl with PureClause nil (a :: nil) _ _ => true | _ => false end.

Lemma Ppred_decrease n : (n<>1)%positive -> (nat_of_P (Ppred n)<nat_of_P n)%nat.
Proof.
intros; destruct (Psucc_pred n) as [Hpred | Hpred]; try contradiction;
pattern n at 2; rewrite <- Hpred; rewrite nat_of_P_succ_morphism; omega.
Defined.

Require Import Recdef.

(* begin show *)

(** The Superpose main loop *)

Function main (n : positive) (units l : list clause) {measure nat_of_P n}
  : superposition_result * list clause * M.t*M.t :=
  if Coqlib.peq n 1 then (Aborted l, units, M.empty, M.empty)
  else if existsb is_empty_clause (map delete_resolved l)
       then (Valid, units, M.empty, M.empty)
       else match partition is_unit_clause l with (us, rs) =>
              let us' := cclose us in
              let l' := filter not_taut (map (simplify
                                (print_eqs_list us')) rs) in
                match partial_mod nil nil l' with
                | inl (R, selected) =>
                  (C_example R (clause_list2set selected), cclose (us'++units),
                      clause_list2set l', M.empty)
                | inr (R, cl, cty) =>
                  let r := infer cty cl l' in
                    main (Ppred n) (cclose (us'++units))
                         (print_pures_list
                           (rsort (rev_cmp compare_clause2) (r ++ l')))
                end
            end.
Proof. intros; apply Ppred_decrease; auto. Defined.

(* end show *)

(** Convert a pure entailment to clausal-nf *)

Definition purecnf (en: entailment) : M.t :=
  match en with
    Entailment (Assertion pureL spaceL) (Assertion pureR spaceR) =>
    match mk_pureR pureL, mk_pureR pureR with (p, n), (p', n') =>
      let pureplus :=
        map (fun a => mkPureClause nil (norm_pure_atom a::nil)) p in
      let pureminus :=
        map (fun a => mkPureClause (norm_pure_atom a::nil) nil) n in
      let pureplus' := rsort_uniq pure_atom_cmp (map norm_pure_atom p') in
      let pureminus' := rsort_uniq pure_atom_cmp (map norm_pure_atom n') in
      let cl := mkPureClause pureplus' pureminus' in
        clause_list2set (cl :: pureplus ++ pureminus)
    end
  end.

Definition check (ent : entailment)
  : superposition_result * list clause * M.t*M.t :=
  main 1000000 nil (print_pures_list
    (rsort (rev_cmp compare_clause2) (M.elements (purecnf ent)))).

Definition check_clauseset (s : M.t)
  : superposition_result * list clause * M.t*M.t :=
  main 1000000 nil (print_pures_list
    (rsort (rev_cmp compare_clause2) (M.elements (M.filter not_taut s)))).

End Superposition.
