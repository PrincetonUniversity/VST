(*This program implements Bachmair and Ganzinger's superposition calculus S
(superposition with selection).  System S differs from Nieuwenhuis and Rubio's
system I by limiting positive superposition inferences to clauses without
negative literals.  Given a term ordering on literals, such clauses correspond
to unconditional rewrite rules. To get a flavor for the system, consider the
following (unsatisfiable) set of pure clauses under the term ordering d > c > b
> a.  Our goal is to prove that the empty clause --> is derivable from clauses
0-3.

c = d -->         [0]
a = b --> c = d   [1]
      --> a = c   [2]
a = c --> a = b   [3]

In system S, only unconditional clauses, such as clause 2, can participate
positively in superposition inferences.  This rules out positive superposition
between clauses 2 and 3 since clause 3 is conditional.  We can derive a new
clause, however, by rewriting clause 2 into the negative literal of clause 3
(negative superposition).

a = a --> a = b   [4]

Clause 4 can further be simplified by reflexivity resolution, which removes
trivial atoms such as a = a from negative positions.  We thus derive the new
unconditional clause

      --> a = b   [5]

which can drive a further rewrite into the negative literal of clause 1, giving

      --> c = d   [6]

after reflexivity resolution.  But now we derive a contradiction by rewriting
clause 6 into clause 0 and simplifying using reflexivity resolution, giving the
empty clause.

c = c -->         [7]
      -->         [8]

The original set of clauses 0-3 is therefore unsatisfiable.

For more information about system S, see the following tutorial paper:

"Equational Reasoning in Saturation-Based Theorem Proving." Leo Bachmair and
Harald Ganzinger.  February 19, 1998.  *)

(** Given-clause style implementation of the superposition subsystem; this module
    has been superceded by veristar.superpose_modelsat. *)

Load loadpath.
Require Import ZArith List Bool.
Require Import veristar.datatypes veristar.clauses.
Require Import veristar.wellfounded.
Require Import Image.
Require Import veristar.basic.
Require Import veristar.clause_universe.
Require Import veristar.compare.
Require Import VST.veric.Coqlib2.

Module Type SUPERPOSITION.

Definition model := list (var * expr).

Inductive superposition_result : Type :=
| Valid : superposition_result
| C_example : model -> M.t -> superposition_result
| Aborted : list clause -> superposition_result.

(* check a pure entailment of the form Pi ==> Pi';
   returns a superposition_result and the final clause set (i.e., the set of
   clauses derived during proof search) *)
Parameter check : entailment -> superposition_result * M.t * M.t.

(* just like check, except we start out with a set of clauses instead of an
   entailment.  this function is the one called by the main theorem prover,
   veristarulate.v. *)
Parameter check_clauseset : M.t -> superposition_result * M.t * M.t.

Parameter clause_generate : model -> clause -> option (var * expr * clause).

Parameter clauses_generate : model -> list clause -> model * M.t.

End SUPERPOSITION.

Module Superposition <: SUPERPOSITION.

(* side conditions *)
Definition pure_atom_gt1 a (l: list pure_atom) :=
  match l with b :: _ => pure_atom_gt a b | _ => true end.

Definition pure_atom_geq1 a (l: list pure_atom) :=
  match l with b :: _ => pure_atom_geq a b | _ => true end.

(* clauseset expansion -- the following resolution proof rules, collected in
   function "sp", may generate fresh clauses to be added to the prover's clause
   database. *)

Definition sp (c d : clause) l0 : list clause :=
  match c, d with
  (* negative superposition *)
  | PureClause nil (Eqv s t :: pos) _ _ ,
        PureClause (Eqv s' v :: neg') pos' _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s'
    then mkPureClause (insu_atm (norm_pure_atom (Eqv t v)) neg')
                      (merge pure_atom_cmp pos pos') :: l0
    else l0
  | PureClause nil (Eqv s t :: pos) _ _,
        PureClause nil (Eqv s' v :: pos') _ _ =>
    let ef := match c with
      (* equality factoring *)
      | PureClause nil (Eqv u v :: Eqv s t :: pos) _ _ =>
        if expr_eq s u && pure_atom_gt (Eqv u v) (Eqv s t)
        then mkPureClause [norm_pure_atom (Eqv v t)]
               (insu_atm (norm_pure_atom (Eqv u t)) pos) :: l0
        else l0
      | _ => l0 end in
    (* positive superposition *)
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && pure_atom_gt1 (Eqv s' v) pos' &&
       pure_atom_gt (Eqv s' v) (Eqv s t)
    then mkPureClause nil (insu_atm (norm_pure_atom (Eqv t v))
                          (merge pure_atom_cmp pos pos')) :: ef
    else ef
  | _ , _ => l0
  end.

(* "superpose" applies "sp" from L-R and R-L, thus returning all new
   clauses derivable from clauses "c" and "d" under the proof rules *)
Definition superpose (c d : clause) l0 : list clause := sp c d (sp d c l0).

(* clause simplification -- the following proof rules simplify clauses
   "in place".  that is, either a newly generated clause is simplified before
   entering the clause database for the first time or an existing clause is
   replaced by its simplified form, e.g., when it is rewritten by a newly
   derived positive unit clause (demodulation). *)
Definition rewrite_by s t atm :=
  match atm with Eqv u v =>
    if expr_eq s u then if expr_eq s v then norm_pure_atom (Eqv t t)
                        else norm_pure_atom (Eqv t v)
    else if expr_eq s v then norm_pure_atom (Eqv u t)
         else atm
  end.

(** rewrite by a positive unit clause *)

Definition demodulate (c d : clause) : clause :=
  match c, d with
  | PureClause nil [Eqv s t] _ _, PureClause neg pos _ _ =>
      mkPureClause (map (rewrite_by s t) neg) (map (rewrite_by s t) pos)
  | _, _ => d
  end.

(** Delete resolved negative atoms, i.e., atoms of the form "Eqv x x"
    lying in negative positions *)

Definition delete_resolved (c : clause) : clause :=
  match c with
  | PureClause neg pos _ _ =>
     mkPureClause (sortu_atms (remove_trivial_atoms neg))
                            (sortu_atms pos)
  | _ => mkPureClause nil [Eqv Nil Nil] (* impossible *)
  end.

(*begin hide*)
(* filter tautological clauses *)

(* Function taut_aux (n p : pure_atom) (arg: list pure_atom * list pure_atom) *)
(*    {measure (fun arg => length (fst arg) + length (snd arg)) arg} : bool := *)
(*  match pure_atom_cmp n p with *)
(*  | Lt => match arg with *)
(*              | (n'::nl', pl) => taut_aux n' p (nl',pl) *)
(*              | _ => false *)
(*              end *)
(*  | Eq => true *)
(*  | Gt => match arg with  *)
(*               | (nl, p'::pl') => taut_aux n p' (nl,pl') *)
(*               | _ => false *)
(*               end *)
(*  end. *)
(*  Proof.  *)
(*    intros; subst; simpl; omega. *)
(*    intros; subst; simpl; omega. *)
(*  Defined. *)

(* Definition not_taut (c: clause) := *)
(*   match c with *)
(*   | PureClause (n::neg) (p::pos) _ _ => negb (taut_aux n p (neg,pos)) *)
(*   | _ => true *)
(*   end. *)
(*end hide*)

(* for some reason, this version of not_taut when extracted runs faster
   than the one above *)
Definition not_taut (c: clause) :=
  negb (match c with
        | PureClause neg pos _ _ =>
          existsb (fun a => existsb (fun b =>
                     pure_atom_eq a b) pos) neg ||
          existsb (fun a =>
            match a with Eqv e1 e2 => expr_eq e1 e2 end) pos
        | _ => false end).


(* rewrite "c" by any positive unit clauses in "l". delete resolved atoms
   from the resulting clause. Argument l is sorted so no need to sort here.
 *)
Definition simplify (l : list clause) (c : clause) : clause :=
  delete_resolved (fold_left (fun d c => demodulate c d) l c).

(* derive all possible inferences from clause "c" and clauses "l", simplifying
   any resulting clauses using facts in "l" *)
Definition infer_list (c : clause) (l : list clause) : list clause :=
  print_inferred_list (filter not_taut (map (simplify l)
    (fold_left (fun l0 d => superpose c d l0) l nil))).

(*begin hide*)
(* VERSION 0:
Definition mem_add (x: M.elt) (s: M.t) : option M.t :=
 if M.mem x s then None else Some (M.add x s).
Lemma mem_add_spec:
    forall x s, mem_add x s = if M.mem x s then None else Some (M.add x s).
Proof. auto. Qed.
Opaque mem_add.
 END VERSION 0 *)
(*end hide*)
(* VERSION 1: *)
Definition mem_add := M.mem_add.
Lemma mem_add_spec:
    forall x s, mem_add x s = if M.mem x s then None else Some (M.add x s).
Proof. apply M.mem_add_spec. Qed.
(* END VERSION 1 *)

Definition mem_add_nonempty x s :=
  if isEq (compare_clause x (mkPureClause nil nil)) then None else
    mem_add x s.

Definition add_list_to_set_simple (l: list M.elt) (s: M.t) : M.t :=
  fold_left (Basics.flip M.add) l s.

Fixpoint add_list_to_set (l: list M.elt) (s: M.t) : option M.t :=
 match l with
 | x::xs => match mem_add x s with
                  | None => add_list_to_set xs s
                  | Some s' => Some (add_list_to_set_simple xs s')
                  end
 | nil => None
 end.

(** Perform one inference step.  G(=given) is the set of previously selected
   clauses (the given clause set). U is the set of unselected clauses.

   The clause ordering, which is lexicographic first in the size of the clauses,
   then in the clauses themselves, ensures that the smallest clause in the
   unselected set is always returned.  this strategy is called best-first by
   McCune, "33 Basic Test Problems: A Practical Evaluation of Some
   Paramodulation Strategies", and performs reasonably well in practice.

   Algorithm:
   - Pick an unselected clause c \in U using the best-first (ie., small first)
      heuristic.
   - c <- simpflify(c, wrt. G)
   - G <- G \cup {c}
   - I <- infer(c, G) //all inferences between c and clauses in G
   - U <- (U \cup (I - G)) //add any clauses not yet in G and U to U
   - ret(U, G) *)

Definition is_pure_clause (c : clause) : bool :=
 match c with PureClause _ _ _ _ => true | _ => false end.

Definition is_unit_cls (c: clause) :=
  match c with
  | PureClause nil [Eqv _ _] _ _ => true | _ => false end.

Definition one_inference_step (given_unselected: M.t*M.t)
  : (M.t * M.t) :=
  let (given, unselected) := given_unselected in
  match M.delete_min unselected with
  | Some (given_clause, unselected') =>
    if is_pure_clause given_clause &&
       not_taut given_clause
    then let s := M.elements given in
      let c := simplify s given_clause in
      match mem_add c given with
      | None => (given, unselected')
      | Some new_given =>
        let inferred_clauses := infer_list c s in
        let new_unselected :=
          fold_left (fun s0 c =>
            if M.mem c new_given then s0
            else M.add c s0) inferred_clauses unselected'
          in (new_given, new_unselected)
      end
    else (given, unselected')
  | None => (given, unselected)
  end.

Definition model := list (var * expr).

Inductive superposition_result : Type :=
| Valid : superposition_result
| C_example : model -> M.t -> superposition_result
| Aborted : list clause -> superposition_result.

(******** Model Generation ********)
Definition apply_model (R: model) (cl: clause) : clause :=
  fold_right (fun ve => subst_clause (fst ve) (snd ve)) cl R.

Definition is_model_of (R: model) (gamma delta : list pure_atom) : bool :=
  match fold_right (fun ve => subst_pures_delete (fst ve) (snd ve)) gamma R,
          fold_right (fun ve => subst_pures (fst ve) (snd ve)) delta R with
  | _::_, _ => true
  | nil , delta' => negb (forallb nonreflex_atom delta')
  end.

Definition is_model_of_PI (R: model) (nc : (*negative spatial*) clause) : bool :=
 match nc with NegSpaceClause pi_plus _ pi_minus =>
  match remove_trivial_atoms (fold_right (fun ve =>
          subst_pures_delete (fst ve) (snd ve)) pi_plus R),
        fold_right (fun ve =>
          subst_pures (fst ve) (snd ve)) pi_minus R with
  | nil , pi_minus' => forallb nonreflex_atom pi_minus'
  | _ :: _ , _ => false
  end
 | _ => false
 end.

Definition clause_generate (R: model) (cl: clause) : option (var * expr * clause) :=
  match apply_model R cl with
  | PureClause gamma (Eqv (Var l' as l) r :: delta) _ _ as c' =>
    if (andb (greater_than_expr l' r)
         (andb (greater_than_all l' gamma)
           (andb (greater_than_atoms (Eqv l r) delta)
             (negb (is_model_of R gamma delta))))) then Some (l', r, cl)
    else None
  | _ => None
  end.

Fixpoint clauses_generate (R: model) (cl: list clause) : model * M.t :=
  match cl with
  | nil => (R, M.empty)
  | c::cs => match clause_generate R c with
             | Some (i,e,c') => match clauses_generate ((i,e)::R) cs with
                                | (R', cs') => (R', M.add c cs')
                                end
             | None => clauses_generate R cs
             end
  end.

(* main_loop(n, G, U):
   if n<=0: return Abort
   else:
       if empty_clause \in U: return Valid
       else:
           (G, U) <- one_inference_step(G, U)
           if is_empty U: return counter-example //G is saturated
           else: loop(n-1, G', U') *)
Definition arg := (M.t * M.t)%type.

Require Import veristar.variables.
Require Import veristar.fresh.

Definition varbound (ss: arg) : vset := var_upto (freshmax_list freshmax_clause (M.elements (M.union (fst ss) (snd ss)))).

Definition effective_cardinal (vb : vset) (s: M.t) (n: nat) :=
  cardinal _ (Intersection _ (Basics.flip M.In s) (clause_bound vb) ) n.

Definition headroom (vb: vset) (s: M.t) (h: nat) :=
 exists n, effective_cardinal vb s n /\ cardinal _ (clause_bound vb) (n+h).

Definition clause_set_increases vb (s s':  M.t) : Prop :=
  exists n, exists n',  headroom vb s n /\ headroom vb s' n' /\ n < n'.

Lemma effective_cardinal_fun: forall vb s n n',
   effective_cardinal vb s n -> effective_cardinal vb s n' -> n=n'.
Proof.
intros. unfold effective_cardinal in *.
 eapply cardinal_is_functional; eauto.
Qed.

Definition unselected_set_decreases (s s' : M.t) := M.cardinal s < M.cardinal s'.

Lemma well_founded_unselected_set_decreases: well_founded unselected_set_decreases.
Proof.
 intros.
 apply (well_founded_inv_lt_rel_compat _ _ (fun x n => M.cardinal x = n)).
 unfold inv_lt_rel; intros. eexists; eauto.
 unfold unselected_set_decreases in H.
 intros; subst; auto. omega.
Qed.

Lemma well_founded_clause_set_increases:
 forall vb, well_founded (clause_set_increases vb).
Proof.
 intro vb.
  apply (well_founded_inv_lt_rel_compat _ _ (headroom vb)).
  intros. unfold inv_lt_rel.
  destruct H as [n [n' [? [? ?]]]].
  exists n; auto.
  intros.
  destruct H0 as [h' [? ?]].
  destruct H2 as [h'' [? ?]].
  assert (h'=h'') by (eapply effective_cardinal_fun; eauto).
  subst h''.
  assert (h'+m = h' + n').
  eapply cardinal_is_functional; eauto.
  omega.
Qed.

Definition superpose_loop_order (s s': arg)  : Prop :=
   (Included _ (varbound s) (varbound s') /\
     (clause_set_increases (varbound s) (fst s) (fst s') \/
      fst s = fst s' /\ unselected_set_decreases (snd s) (snd s'))).

Definition Strict_Included_Fin (U: Type) (x y: Ensemble U) :=
  Strict_Included _ x y /\ Finite _ y.

Lemma well_founded_Strict_Included_Fin:
  forall U, well_founded (Strict_Included_Fin U).
Proof.
 intros.
 apply (well_founded_inv_lt_rel_compat _ _ (cardinal _)); intros.
 unfold inv_lt_rel.
 destruct H.
 assert (Finite U x).
   apply Finite_downward_closed with y; auto.
  destruct (Strict_Included_inv _ _ _ H); auto.
 destruct (finite_cardinal _ _ H1) as [n ?].
 exists n; auto.
 intros.
 eapply incl_st_card_lt; eauto.
Qed.

Import ClauseUniverseFinite.

Lemma well_founded_superpose_loop_order: well_founded superpose_loop_order.
Proof.
  apply well_founded_incl
     with  (lexprodx varbound (Strict_Included_Fin _)
                   (fun vb => lex_pair (clause_set_increases vb) unselected_set_decreases)).
 (* inclusion *)
 intros ? ? ?.
 destruct H.
 apply Included_Strict_Included in H.
 destruct H; [left | right]; auto.
 split; auto.
 apply Finite_var_upto.
  (* well-foundedness *)
 apply well_founded_lexprodx.
 apply well_founded_Strict_Included_Fin.
 intro vb.
 apply well_founded_lex_pair.
 apply well_founded_clause_set_increases.
 apply well_founded_unselected_set_decreases.
Qed.

Lemma pures_bound_empty n : pures_bound n [].
Proof. split; [apply Forall_nil|apply NoDup_nil]. Qed.

Lemma pures_bound_nil_nil n : pures_bound n [Eqv Nil Nil].
Proof.
split; [solve[apply Forall_cons; simpl; auto]|].
apply NoDup_cons; simpl; auto. apply NoDup_nil.
Qed.

Hint Resolve pures_bound_empty pures_bound_nil_nil.

Lemma clause_bound_delete_resolved:
  forall n cl, clause_bound' n cl -> clause_bound n (delete_resolved cl).
Proof.
 unfold delete_resolved; destruct cl; simpl; intros; auto;
 try solve [repeat split; simpl; auto; constructor].
 destruct H; unfold pures_bound' in *.
 split; split; try apply NoDup_rsort_uniq; auto.
 apply Forall_sortu.
 clear - H; induction H; simpl; try constructor.
 destruct x; auto. destruct (expr_cmp e e0); try constructor; auto.
 apply Forall_sortu. auto.
Qed.

Lemma pure_bound_norm:
  forall n e1 e2, expr_bound n e1 -> expr_bound n  e2 ->
           pure_bound n (norm_pure_atom (Eqv e1 e2)).
Proof.
 intros. simpl.
 destruct (expr_lt e1 e2); simpl; auto.
Qed.

Lemma pure_bound_rewrite:
  forall n e1 e2 a, expr_bound n e1 -> expr_bound n e2 -> pure_bound n a ->
                pure_bound n (rewrite_by e1 e2 a).
Proof.
unfold rewrite_by; intros.
destruct a; auto.
simpl in H1; destruct H1.
destruct (expr_eq e1 e); destruct (expr_eq e1 e0); try apply pure_bound_norm; auto.
simpl; auto.
Qed.

Lemma pures_bound_sortu_rewrite:
  forall n e1 e2 pi,
        pures_bound' n [Eqv e1 e2] ->
        pures_bound' n pi ->
        pures_bound' n (map (rewrite_by e1 e2) pi).
Proof.
unfold pures_bound'; intros.
(* all bounded *)
inversion H; clear H; subst.
clear H4.
destruct H3.
induction H0; constructor; auto.
apply pure_bound_rewrite; auto.
Qed.

Lemma clause_bound_demodulate:
  forall n c d, clause_bound' n c  -> clause_bound' n d ->
    clause_bound' n (demodulate c d).
Proof.
unfold demodulate; intros.
destruct c; auto.
destruct gamma; auto. destruct delta; auto.
destruct p; auto. destruct delta; auto. destruct d; auto.
simpl in *.
destruct H as [_ ?].
destruct H0.
split; apply pures_bound_sortu_rewrite; auto.
Qed.


Lemma clause_bound'_in:
 forall ss c,
  M.In c (M.union (fst ss) (snd ss)) ->
  clause_bound' (varbound ss) c.
Proof.
  unfold varbound;  simpl; intros. destruct ss; simpl in *.
  remember (M.union t t0) as s; clear t t0 Heqs.
  rewrite <- Melements_spec1  in H.
  revert H; induction (M.elements s); intros.
  inversion H.
  simpl in H. destruct H.
  subst.
  simpl.
  clear.
  apply clause_bound'_more with (var_upto (freshmax_clause c)).
 apply included_var_upto;  apply Ile_var_max1.
  apply clause_bound'_freshmax.
  simpl.
  eapply clause_bound'_more; try apply IHl; auto.
 apply included_var_upto;  apply Ile_var_max2.
Qed.

Lemma remove_trivial_atoms_in:
 forall a pi, List.In a (remove_trivial_atoms pi) -> List.In a pi.
Proof.
 induction pi; simpl; intros; auto.
 destruct a0. destruct (expr_cmp e e0); auto.
 destruct H; auto.
 destruct H; auto.
Qed.

Lemma freshmax_norm:
  forall a, freshmax_pure_atom (norm_pure_atom a) = freshmax_pure_atom a.
Proof. destruct a; simpl. destruct (expr_lt e e0); simpl; auto. apply var_max_com.
Qed.

Ltac fresh_tac :=
   solve [auto]
 || rewrite freshmax_norm in *
 || match goal with
  | H : List.In _ (match ?D with | PureClause _ _ _ _ => _
          | PosSpaceClause _ _ _ => _ | NegSpaceClause _ _ _ => _ end)
     |- _  => destruct D
  | H : List.In _ (match ?D with nil => _ | _ :: _ => _ end) |- _  => destruct D
  | H : List.In _ (match ?D with Eqv _ _ => _ end) |- _  => destruct D
  | H : List.In _ (if ?D then _ else _) |- _ =>
      let H' := fresh in revert H; case_eq D; intros H' H;
           repeat rewrite <- andb_assoc in H';
           try (rewrite andb_true_iff in H'; destruct H' as [H' _])
  | H : expr_eq _ ?e1 = true |- _ => symmetry in H; apply expr_eq_eq' in H;
                                        subst e1
  | H : Ile _ _ |- _ => apply var_max_split' in H; destruct H
  | H : List.In ?c (_ :: _) |- _ => destruct H; [ subst c | ]
  | |- Ile (freshmax_pure_atom (norm_pure_atom _)) _ => unfold norm_pure_atom
  | |- Ile (freshmax_pure_atom (if ?D then _ else _)) _ => destruct D
  end
 || apply freshmax_list_merge
 || simpl freshmax_clause
 || apply Ile_minid
 || apply var_max_intro'
 || (rewrite comp_refl in *; auto)
 || (rewrite freshmax_list_sort; [auto | apply pure_atom_cmp_eq])
 || apply freshmax_insu.

Lemma freshmax_delete_resolved:
  forall c m, Ile (freshmax_clause c) m -> Ile (freshmax_clause (delete_resolved c)) m.
Proof.
 unfold delete_resolved; intros.
 destruct c; repeat fresh_tac; auto.
 clear - H; rewrite  Ile_freshmax_list in *; intros.
 apply H. apply remove_trivial_atoms_in. auto.
Qed.


Lemma freshmax_rewrite_by:
  forall m e e' a, Ile (freshmax_expr e) m -> Ile (freshmax_expr e') m ->
      Ile (freshmax_pure_atom a) m ->
      Ile (freshmax_pure_atom (rewrite_by e e' a)) m.
Proof.
 intros.
 unfold rewrite_by.
 destruct a; auto.
 repeat fresh_tac.
Qed.

Lemma freshmax_demodulate:
  forall a c m, Ile (freshmax_clause a) m -> Ile (freshmax_clause c) m ->
             Ile (freshmax_clause (demodulate a c)) m.
Proof.
 unfold demodulate; intros.
 destruct a; auto. destruct gamma; auto. destruct delta; auto. destruct p; auto.
 destruct delta; auto. destruct c; auto.
 repeat fresh_tac.
 rewrite Ile_freshmax_list in *.
 intros.
  apply Coqlib.list_in_map_inv in H5.
 destruct H5 as [a [? ?]]; subst x.
  apply freshmax_rewrite_by; auto.
 rewrite Ile_freshmax_list in *.
 intros.
  apply Coqlib.list_in_map_inv in H5.
 destruct H5 as [a [? ?]]; subst x.
  apply freshmax_rewrite_by; auto.
Qed.

Lemma varbound_remove:
  forall s x s', Included _ (varbound (s, M.remove x s')) (varbound (s, s')).
Proof.
 unfold varbound; intros.
 simpl.
 intros ? ?; unfold In, var_upto in *.
 remember (freshmax_list freshmax_clause (M.elements (M.union s s')))  as m.
 assert (forall c, M.In c (M.union s s') -> Ile (freshmax_clause c) m).
  subst; clear; intros.
  rewrite <- Melements_spec1 in H.
  revert H; induction (M.elements (M.union s s')); intros.
  inversion H.
  simpl in H. destruct H. subst.
  simpl.
  apply Ile_var_max1.
  simpl. eapply Ile_trans; try apply IHl; auto.
  apply Ile_var_max2.
  eapply Ile_trans; try apply H.
  clear - H0.
  apply Ile_freshmax_i3; intros.
  apply H0; clear H0.
  rewrite M.union_spec in *.
  intuition.
  right. rewrite M.remove_spec in H0; intuition.
Qed.

Lemma freshmax_simplify:
  forall m l g, (forall c : M.elt, List.In c l -> Ile (freshmax_clause c) m) ->
    Ile (freshmax_clause g) m ->
   Ile (freshmax_clause (simplify l g)) m.
Proof.
 intros.
 unfold simplify.
 apply freshmax_delete_resolved.
 revert H g H H0; induction l; simpl; intros; auto.
 apply IHl; auto.
 apply freshmax_demodulate; auto.
Qed.

Require Import VST.msl.Coqlib2.

Lemma freshmax_sp:
  forall m d a l,
    Ile (freshmax_clause d) m ->
    Ile (freshmax_clause a) m ->
    (forall c, List.In c l -> Ile (freshmax_clause c) m) ->
    forall c, List.In c (sp d a l) -> Ile (freshmax_clause c) m.
Proof.
  intros.
  unfold sp in H2.
  repeat fresh_tac.
  destruct delta; auto; destruct p; auto.
  if_tac in H2; auto.
  destruct H2; auto. rewrite <-H2.
  repeat fresh_tac; auto.
Qed.

Lemma freshmax_superpose:
  forall m d a l,
    Ile (freshmax_clause d) m ->
    Ile (freshmax_clause a) m ->
    (forall c, List.In c l -> Ile (freshmax_clause c) m) ->
    forall c, List.In c (superpose d a l) -> Ile (freshmax_clause c) m.
Proof.
 intros.
 unfold superpose in H2.
 eapply freshmax_sp; try apply H2; eauto.
 intros.
 eapply freshmax_sp; try apply H3; eauto.
Qed.

Lemma freshmax_infer_list:
  forall d l m,
        Ile (freshmax_clause d) m ->
        (forall c, List.In c l -> Ile (freshmax_clause c) m) ->
        forall c, List.In c (infer_list d l) -> Ile (freshmax_clause c) m.
Proof.
 intros.
 unfold infer_list in H1.  autounfold with DEBUG_UNFOLD in *.
 rewrite filter_In in H1. destruct H1 as [H1 _].
 apply Coqlib.list_in_map_inv in H1.
 destruct H1 as [c' [? ?]].
 subst c. apply freshmax_simplify; auto.
 remember (@nil clause) as b.
 assert (forall c, List.In c b -> Ile (freshmax_clause c) m).
 subst b; intros. inversion H1.
 clear Heqb.
 revert b H0 H1 H2; induction l; simpl; intros; auto.
 apply (IHl (superpose d a b)); auto.
 apply freshmax_superpose; auto.
Qed.

Lemma varbound_nonincreasing: forall given unselected giv,
  M.In giv unselected ->
 Included _ (varbound
  (M.add (simplify (M.elements given) giv) given,
  fold_left
    (fun (s0 : M.t) (c : M.elt) =>
     if M.mem c (M.add (simplify (M.elements given) giv) given)
     then s0
     else M.add c s0)
    (infer_list (simplify (M.elements given) giv)
       (simplify (M.elements given) giv :: M.elements given))
    (M.remove giv unselected)))
    (varbound (given, unselected)).
Proof.
  intros.
  unfold varbound.
  simpl.
  apply included_var_upto.
  remember (freshmax_list freshmax_clause (M.elements (M.union given unselected)))
    as m.
  assert (forall c, M.In c (M.union given unselected) -> Ile (freshmax_clause c) m).
  subst; clear; intros.
  rewrite <- Melements_spec1 in H.
  revert H; induction (M.elements (M.union given unselected)); intros.
  inversion H.
  simpl in H. destruct H. subst.
  simpl.
  apply Ile_var_max1.
  simpl. eapply Ile_trans; try apply IHl; auto.
  apply Ile_var_max2.
  clear - H H0.
  apply Ile_freshmax_i3; intros.
  rewrite M.union_spec in H1.
  assert (forall c, List.In c (M.elements given) -> Ile (freshmax_clause c) m).
  intros. apply H0. rewrite M.union_spec; left. rewrite Melements_spec1 in H2; auto.
  destruct H1.
  rewrite M.add_spec in H1.
  destruct H1. subst.
  assert (Ile (freshmax_clause giv) m).
  apply H0. rewrite M.union_spec; auto.
  remember (M.elements given) as l;
  clear - H1 H2.
  apply freshmax_simplify; auto.
  apply H0. rewrite M.union_spec; auto.
  assert (forall c, M.In c (M.remove giv unselected) -> Ile (freshmax_clause c) m).
  intros; apply H0. rewrite M.union_spec; right. rewrite M.remove_spec in H3; intuition.
  remember (M.remove giv unselected) as J.
  assert (Ile (freshmax_clause giv) m).
  apply H0. rewrite M.union_spec; right; auto.
  remember (M.elements given) as givl.
  remember (M.add (simplify givl giv) given) as foo.
  clear - H1 H2 H3 H4.
  assert (Ile (freshmax_clause (simplify givl giv)) m).
  clear - H4 H2.
  apply freshmax_simplify; auto.
  remember (simplify givl giv) as d; clear - H H1 H2 H3.
  assert (forall c, List.In c (infer_list d (d :: givl)) -> Ile (freshmax_clause c) m).
  apply freshmax_infer_list; auto.
  intros. destruct H0; auto. subst; auto.
  remember (infer_list d (d :: givl)) as dl; clear givl Heqdl H2 d H.
  revert J H1 H3 H0; induction dl; simpl; intros; auto.
  destruct (M.mem a foo).
  eapply IHdl; eauto.
  eapply IHdl; eauto.
  intros.
  rewrite M.add_spec in H.
  destruct H.
  subst c. auto.
  apply H3; auto.
Qed.

Lemma varbound_nonincreasing': forall given unselected giv,
  M.In giv unselected ->
  Included _ (varbound
  (M.add (simplify (M.elements given) giv) given,
  fold_left
    (fun (s0 : M.t) (c : M.elt) =>
     if M.mem c (M.add (simplify (M.elements given) giv) given)
     then s0
     else M.add c s0)
    (infer_list (simplify (M.elements given) giv)
       (M.elements given))
    (M.remove giv unselected)))
   (varbound (given, unselected)).
Proof.
  intros.
  unfold varbound.
  simpl.
  apply included_var_upto.
  remember (freshmax_list freshmax_clause (M.elements (M.union given unselected)))
    as m.
  assert (forall c, M.In c (M.union given unselected) -> Ile (freshmax_clause c) m).
  subst; clear; intros.
  rewrite <- Melements_spec1 in H.
  revert H; induction (M.elements (M.union given unselected)); intros.
  inversion H.
  simpl in H. destruct H. subst.
  simpl.
  apply Ile_var_max1.
  simpl. eapply Ile_trans; try apply IHl; auto.
  apply Ile_var_max2.
  clear - H H0.
  apply Ile_freshmax_i3; intros.
  rewrite M.union_spec in H1.
  assert (forall c, List.In c (M.elements given) -> Ile (freshmax_clause c) m).
  intros. apply H0. rewrite M.union_spec; left. rewrite Melements_spec1 in H2; auto.
  destruct H1.
  rewrite M.add_spec in H1.
  destruct H1. subst.
  assert (Ile (freshmax_clause giv) m).
  apply H0. rewrite M.union_spec; auto.
  remember (M.elements given) as l;
  clear - H1 H2.
  apply freshmax_simplify; auto.
  apply H0. rewrite M.union_spec; auto.
  assert (forall c, M.In c (M.remove giv unselected) -> Ile (freshmax_clause c) m).
  intros; apply H0. rewrite M.union_spec; right. rewrite M.remove_spec in H3; intuition.
  remember (M.remove giv unselected) as J.
  assert (Ile (freshmax_clause giv) m).
  apply H0. rewrite M.union_spec; right; auto.
  remember (M.elements given) as givl.
  remember (M.add (simplify givl giv) given) as foo.
  clear - H1 H2 H3 H4.
  assert (Ile (freshmax_clause (simplify givl giv)) m).
  clear - H4 H2.
  apply freshmax_simplify; auto.
  remember (simplify givl giv) as d; clear - H H1 H2 H3.
  assert (forall c, List.In c (infer_list d (givl)) -> Ile (freshmax_clause c) m).
  apply freshmax_infer_list; auto.
  remember (infer_list d (givl)) as dl; clear d givl Heqdl H2 H.
  revert J H1 H3 H0; induction dl; simpl; intros; auto.
  destruct (M.mem a foo).
  eapply IHdl; eauto.
  eapply IHdl; eauto.
  intros.
  rewrite M.add_spec in H.
  destruct H.
  subst c. auto.
  apply H3; auto.
Qed.

Lemma simplify_nodup:
   forall n l c,
     clause_bound' n (simplify l c) ->
     clause_bound n (simplify l c).
Proof.
 unfold simplify, delete_resolved; simpl; intros.
 destruct (fold_left  (fun d c : clause => demodulate c d) l c);
 unfold clause_bound; simpl in *.
 destruct H.
 split; split; auto;  apply NoDup_rsort_uniq; auto.
 destruct H; split; split; auto; constructor; auto. apply NoDup_nil.
 destruct H; split; split; auto; constructor; auto. apply NoDup_nil.
Qed.

Lemma one_inference_step_order:
       forall given unselected new_given  new_unselected,
       M.mem empty_clause unselected = false ->
       M.is_empty new_unselected = false ->
       one_inference_step (given, unselected) = (new_given, new_unselected) ->
       superpose_loop_order (new_given, new_unselected) (given, unselected).
 Proof.
  unfold one_inference_step; intros.
  rewrite mem_spec' in H. rewrite is_empty_spec' in H0.
  revert H1; case_eq (M.delete_min unselected); intros.
Focus 2.
  rewrite M.delete_min_spec2 in H1.
  symmetry in H2;   inversion H2; clear H2; subst.
  contradiction.
 (* End Focus 2 *)
  destruct p as [giv uns].
  rewrite M.delete_min_spec1 in H1.
  destruct H1.   subst uns.
  apply M.min_elt_spec1 in H1.
  autounfold with DEBUG_UNFOLD in *.
  destruct (is_pure_clause giv).
 Focus 2.
  symmetry in H2; inversion H2; clear H2; subst.
  split. apply varbound_remove.
  simpl. right; split; auto.
  apply remove_decreases; auto.
  rewrite mem_add_spec in H2.
  destruct (not_taut giv); simpl in H2.
  revert H2; case_eq (M.mem  (simplify (M.elements given) giv) given); intros.
  symmetry in H3; inversion H3; clear H3; subst.
  split. apply varbound_remove.
  right; simpl; split; auto.
  apply remove_decreases; auto.
  inversion H3; clear H3; subst.
  clear H0.
  match goal with |- superpose_loop_order ?SS _ => remember SS as ss end.
  split.
  subst ss; clear - H1.
 apply varbound_nonincreasing'; auto.
  left.
  unfold clause_set_increases.
  destruct (finite_cardinal _ _ ( Intersection_preserves_finite _
                      _ (clause_bound_finite (varbound ss) (Finite_var_upto _))
         (Basics.flip M.In (M.add (simplify (M.elements given) giv) given)))) as [n ?].
  destruct (finite_cardinal _ _ ( Intersection_preserves_finite _
                      _ (clause_bound_finite (varbound ss) (Finite_var_upto _))
         (Basics.flip M.In given))) as [n' ?].
  destruct (finite_cardinal _ _ (clause_bound_finite (varbound ss) (Finite_var_upto _)))
     as [N ?].
  assert (N>=n) by (eapply incl_card_le; eauto;  intros ? [? ?]; auto).
  assert (N>=n') by (eapply incl_card_le; eauto;  intros ? [? ?]; auto).
  exists (N-n); exists (N-n').
  assert (clause_bound (varbound ss) (simplify (M.elements given) giv)).
  apply simplify_nodup.
  apply clause_bound'_in.
  rewrite M.union_spec. left. rewrite Heqss. simpl.
  rewrite M.add_spec. left. auto.
  split; [|split]; auto.
  rewrite Heqss at 2; simpl.
  unfold headroom.
  exists n. split; auto.
  replace (n+(N-n)) with N by omega. auto.
  exists n'; split; auto.
  replace (n'+(N-n')) with N by omega. auto.
  assert (n>n'); [ | omega].
   eapply (incl_st_card_lt); eauto.
  split.
   intros ? [? ?]. unfold In in *.
   split; auto.
    unfold In, Basics.flip in *. rewrite M.add_spec. auto.
   remember  (simplify (M.elements given) giv) as c.
   rewrite mem_spec' in H2.
   clear - H7 H2.
   intro H.
   match type of H with ?A = ?B => assert (A c) end.
   rewrite H.
   split; auto.
    unfold In, Basics.flip; rewrite M.add_spec. left.
    auto.
   destruct H0. unfold In, Basics.flip in H0; contradiction.
 (* tautology case *)
 inversion H2; subst. split; auto. apply varbound_remove.
 right; simpl; split; auto. apply remove_decreases; auto.
Qed.

(*begin show*)
(* NOTE: it may occur that empty_clause \in given if the clause selected from
   unselected is simplified to empty_clause. We need to check both. *)
Function loop (given_unselected : M.t*M.t)
  {wf superpose_loop_order given_unselected}
  : superposition_result * M.t*M.t :=
  let (given, unselected) := given_unselected in
    if M.mem empty_clause given || M.mem empty_clause unselected
    then (Valid, given, unselected)
    else match one_inference_step (given, unselected) with
         | (new_given, new_unselected) =>
           if M.is_empty new_unselected
             then let (R, selected) := clauses_generate nil
                 (rsort_uniq (rev_cmp compare_clause) (M.elements new_given)) in
               (C_example R selected, new_given, new_unselected)
             else loop (new_given, new_unselected)
         end.
Proof.
  intros.
  subst. eapply one_inference_step_order; eauto.
  rewrite orb_false_iff in teq0; destruct teq0 as [_ H]; auto.
  apply well_founded_superpose_loop_order.
Defined.
(*end show*)

(* convert a pure entailment to clausal-nf *)
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

Definition check (ent : entailment) : superposition_result * M.t*M.t :=
  loop (M.empty, purecnf ent).

Definition check_clauseset (s : M.t) : superposition_result * M.t*M.t :=
  loop (M.empty, M.filter not_taut s).

End Superposition.
