Load loadpath.
Require Import ZArith List Recdef Coq.MSets.MSetInterface Coq.Sorting.Mergesort
               Permutation Coq.MSets.MSetAVL.
Require Import veristar.basic veristar.tactics veristar.variables veristar.datatypes
               veristar.compare veristar.redblack.

(** The clause datatype and related definitions and lemmas *)

(** pure_atom:
pure atoms *)

Inductive pure_atom := Eqv : expr -> expr -> pure_atom.

Let var1 : var := Z2id 1.
Let var0 : var := Z2id 0.
Let var2 : var := Z2id 2.

Fixpoint list_prio {A} (weight: var) (l: list A) (p: var) : var :=
  match l with
  | nil => p
  | _::l' => list_prio weight l' (add_id weight p)
  end.

(** Weight the positive atoms 1 each, and the negative atoms 2 each.
    Then the highest-priority terms will be the positive unit clauses *)

Definition prio (gamma delta: list pure_atom) : var :=
    list_prio var2 gamma (list_prio var1 delta var0).

(** clause:
clauses are either pure (no spatial atoms), negative spatial (spatial atom on the left)
or positive spatial. *)

Inductive clause : Type :=
| PureClause : forall (gamma : list pure_atom) (delta : list pure_atom)
                         (priority : var)
                         (prio_ok: prio gamma delta = priority), clause
| PosSpaceClause : forall (gamma : list pure_atom) (delta : list pure_atom)
  (sigma : list space_atom), clause
| NegSpaceClause : forall (gamma : list pure_atom) (sigma : list space_atom)
  (delta : list pure_atom), clause.

Definition expr_cmp e e' :=
 match e, e' with
   | Nil , Nil => Eq
   | Nil, _ => Lt
   | _, Nil => Gt
   | Var v, Var v' => Ident.compare v v'
 end.

Lemma var_cspec : StrictCompSpec (@Logic.eq var) Ident.lt Ident.compare.
Proof. split; [apply Ident.lt_strorder|apply Ident.compare_spec]. Qed.

Hint Resolve var_cspec.

Lemma expr_cspec: CompSpec' expr_cmp.
Proof.
 repeat constructor; repeat intro.
 destruct x; simpl in *; try discriminate.
 rewrite <- (lt_comp _ _ var_cspec) in H.
 contradiction (Ilt_irrefl H).
 repeat intro.
 destruct x; destruct y; simpl in *; try discriminate;
   destruct z; simpl in *; try discriminate; auto.
 rewrite <- (lt_comp _ _ var_cspec) in *.
  eapply Ilt_trans; eauto.
 destruct x; destruct y; simpl; try econstructor; auto.
 do_comp var_cspec v v0; subst; econstructor; simpl; eauto.
 rewrite <- lt_comp; eauto.
 rewrite <- lt_comp; eauto.
Qed.

Hint Resolve expr_cspec.

Definition pure_atom_cmp (a a': pure_atom) : comparison :=
 match a, a' with
   | Eqv e1 e2, Eqv e1' e2' =>
     match expr_cmp e1 e1' with
       Eq => expr_cmp e2 e2' | c => c
     end
 end.

Hint Rewrite @comp_refl using solve[auto] : comp.

Ltac comp_tac :=
    progress (autorewrite with comp in *; auto)
  || discriminate
  || solve [eapply comp_trans;  eauto]
  || subst
 || match goal with
  | H: Lt = ?A |- context [?A] => rewrite <- H
  | H: Gt = ?A |- context [?A] => rewrite <- H
  | H: Eq = ?A |- context [?A] => rewrite <- H
 end.

Lemma pure_atom_cspec: CompSpec' pure_atom_cmp.
Proof with repeat comp_tac.
 repeat split; repeat intro.
 destruct x; simpl in H...
 destruct x; destruct y; destruct z; simpl in *...
 do_comp expr_cspec e e1...
 do_comp expr_cspec e1 e3...
 do_comp expr_cspec e1 e3...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e5 e6)...
 destruct x; destruct y.
 simpl.
 do_comp expr_cspec e e1...
 do_comp expr_cspec e0 e2; econstructor; eauto; simpl...
 econstructor; simpl...
 econstructor; simpl...
Qed.

Hint Resolve pure_atom_cspec.

Lemma pure_atom_cmp_eq a b : a = b <-> Eq = pure_atom_cmp a b.
Proof. intuition. subst; rewrite comp_refl; auto.
  do_comp pure_atom_cspec a b; auto; congruence.
Qed.
Hint Resolve pure_atom_cmp_eq.

(** ordering expressions, atoms and clauses *)

Definition expr_order (t t': expr) := isGe (expr_cmp t t').

Inductive max_expr (t : expr) : pure_atom -> Prop :=
| mexpr_left : forall t', expr_order t t' -> max_expr t (Eqv t t')
| mexpr_right : forall t', expr_order t t' -> max_expr t (Eqv t' t).

Definition order_eqv_pure_atom (a: pure_atom) :=
  match a with
    | Eqv i j => match expr_cmp i j with Lt => Eqv j i | _ => Eqv i j end
  end.

Definition nonreflex_atom a :=
  match a with Eqv i j => match expr_cmp i j with Eq => false | _ => true end
  end.

Definition normalize_atoms pa :=
  rsort_uniq pure_atom_cmp (map order_eqv_pure_atom pa).

Definition mkPureClause (gamma delta: list pure_atom) : clause :=
  PureClause gamma delta _ (eq_refl _).

Definition order_eqv_clause (c: clause) :=
  match c with
  | PureClause pa pa' _ _ =>
        mkPureClause (normalize_atoms (filter nonreflex_atom pa)) (normalize_atoms pa')
  | PosSpaceClause pa pa' sa' =>
    PosSpaceClause (normalize_atoms (filter nonreflex_atom pa))
                   (normalize_atoms pa') sa'
  | NegSpaceClause pa sa pa' =>
    NegSpaceClause (normalize_atoms (filter nonreflex_atom pa)) sa
                   (normalize_atoms pa')
  end.

Definition mk_pureL (a: pn_atom) : clause :=
 match a with
 | Equ x y => mkPureClause nil (order_eqv_pure_atom(Eqv x y)::nil)
 | Nequ x y => mkPureClause (order_eqv_pure_atom(Eqv x y)::nil) nil
 end.

Fixpoint mk_pureR (al: list pn_atom) : list pure_atom * list pure_atom :=
 match al with
 | nil => (nil,nil)
 | Equ x y :: l' => match mk_pureR l' with (p,n) =>
                      (order_eqv_pure_atom(Eqv x y)::p, n) end
 | Nequ x y :: l' => match mk_pureR l' with (p,n) =>
                       (p, order_eqv_pure_atom(Eqv x y)::n) end
 end.

(** cnf:
clausal normal form *)

Definition cnf (en: entailment) : list clause :=
 match en with
  Entailment (Assertion pureL spaceL) (Assertion pureR spaceR) =>
   match mk_pureR pureR with (p,n) =>
     map mk_pureL pureL ++ (PosSpaceClause nil nil spaceL :: nil) ++
       match spaceL, spaceR with
       | nil, nil => mkPureClause p n :: nil
       | _, _ => NegSpaceClause p spaceR n :: nil
       end
   end
  end.

(** various comparison functions *)

Definition pure_atom_geq a b := isGeq (pure_atom_cmp a b).
Definition pure_atom_gt a b := match pure_atom_cmp a b with Gt => true | _ => false end.
Definition pure_atom_eq a b := match pure_atom_cmp a b with Eq => true | _ => false end.
Definition expr_lt a b := match expr_cmp a b with Lt => true | _ => false end.
Definition expr_eq a b := match expr_cmp a b with Eq => true | _ => false end.
Definition expr_geq a b := match expr_cmp a b with Lt => false | _ => true end.

Definition norm_pure_atom (a : pure_atom) :=
  match a with
    | Eqv i j => if expr_lt i j then Eqv j i else Eqv i j
  end.

Definition subst_pure (i: var) (t: expr) (a: pure_atom) :=
 match a with
   | Eqv t1 t2 => Eqv (subst_expr i t t1) (subst_expr i t t2)
 end.

Definition subst_pures (i: var) (t: expr) (pa: list pure_atom)
  : list pure_atom := map (subst_pure i t) pa.

Definition compare_space_atom (a b : space_atom) : comparison :=
 match a , b with
  | Next i j , Next i' j' => match expr_cmp i i' with Eq => expr_cmp j j' | c => c end
  | Next i j, Lseg i' j' =>
    match expr_cmp i i' with
    | Lt => Lt
    | Eq => Lt
    | Gt => Gt
    end
  | Lseg i j, Next i' j' =>
    match expr_cmp i i' with
    | Lt => Lt
    | Eq => Gt
    | Gt => Gt
    end
  | Lseg i j , Lseg i' j' => match expr_cmp i i' with Eq => expr_cmp j j' | c => c end
  end.

Lemma space_atom_cspec: CompSpec' compare_space_atom.
Proof with (repeat (comp_tac || solve [econstructor; simpl; repeat comp_tac])).
 repeat constructor; repeat intro.
 destruct x; simpl in *...
 destruct x; destruct y; simpl in *...
 do_comp expr_cspec e e1...
 destruct z; simpl in *...
 do_comp expr_cspec e1 e...
 destruct z; simpl in *...
 do_comp expr_cspec e1 e4...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e3 e6)...
 do_comp expr_cspec e1 e4...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e3 e6)...
 do_comp expr_cspec e e1...
 destruct z; simpl in *.
 do_comp expr_cspec e1 e...
 do_comp expr_cspec e1 e...
 destruct z; simpl in *.
 do_comp expr_cspec e1 e4...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e3 e6)...
 do_comp expr_cspec e1 e4...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e3 e6)...
 destruct z; simpl in *.
 do_comp expr_cspec e e1...
 do_comp expr_cspec e1 e3...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e5 e6)...
 do_comp expr_cspec e e1...
 do_comp expr_cspec e1 e3...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e5 e6)...
 do_comp expr_cspec e e1...
 destruct z; simpl in *.
 do_comp expr_cspec e1 e...
 do_comp expr_cspec e1 e...
 destruct z; simpl in *.
 do_comp expr_cspec e1 e4...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e3 e6)...
 do_comp expr_cspec e1 e4...
 rewrite <- (comp_trans _ expr_cspec _ _ _ e3 e6)...
 destruct x; destruct y; simpl...
 do_comp expr_cspec e e1; simpl...
 do_comp expr_cspec e0 e2...
 do_comp expr_cspec e e1...
 do_comp expr_cspec e e1...
 do_comp expr_cspec e e1...
 do_comp expr_cspec e0 e2...
Qed.

Hint Resolve space_atom_cspec.

Definition compare_clause (cl1 cl2 : clause) : comparison :=
  match cl1 , cl2 with
  | PureClause neg pos _ _ , PureClause neg' pos' _ _ =>
    match compare_list pure_atom_cmp neg neg' with
    | Eq => compare_list pure_atom_cmp pos pos'
    | c => c
    end
  | PureClause _ _ _ _ , _ => Lt
  | _ , PureClause _ _ _ _ => Gt
  | PosSpaceClause gamma delta sigma , PosSpaceClause gamma' delta' sigma'
  | NegSpaceClause gamma sigma delta , NegSpaceClause gamma' sigma' delta' =>
    match compare_list pure_atom_cmp gamma gamma' with
    | Eq => match compare_list pure_atom_cmp delta delta' with
                 | Eq => compare_list compare_space_atom sigma sigma'
                 | c => c
                 end
    | c => c
    end
  | PosSpaceClause _ _ _ , NegSpaceClause _ _ _ => Lt
  | NegSpaceClause _ _ _ , PosSpaceClause _ _ _ => Gt
  end.

Lemma clause_cspec: CompSpec' compare_clause.
Proof with (repeat (comp_tac || solve [econstructor; simpl; repeat comp_tac])).
 repeat constructor; repeat intro.
 (* irreflexive *)
 destruct x; simpl in *...
 (* transitive *)
 destruct x; destruct y; destruct z; simpl in *...
 do_comp (list_cspec _ pure_atom_cspec) gamma gamma0...
 do_comp (list_cspec _ pure_atom_cspec) gamma0 gamma1...
 do_comp (list_cspec _ pure_atom_cspec) gamma0 gamma1...
 replace (compare_list pure_atom_cmp gamma gamma1)  with Lt by (eapply comp_trans; eauto)...
 do_comp (list_cspec _ pure_atom_cspec) gamma gamma0...
 do_comp (list_cspec _ pure_atom_cspec) gamma0 gamma1...
 do_comp (list_cspec _ pure_atom_cspec) delta delta0...
 do_comp (list_cspec _ pure_atom_cspec) delta0 delta1...
 do_comp (list_cspec _ pure_atom_cspec) delta0 delta1...
 replace (compare_list pure_atom_cmp delta delta1)  with Lt by (eapply comp_trans; eauto)...
 do_comp (list_cspec _ pure_atom_cspec) gamma0 gamma1...
 replace (compare_list pure_atom_cmp gamma gamma1)  with Lt by (eapply comp_trans; eauto)...
 do_comp (list_cspec _ pure_atom_cspec) gamma gamma0...
 do_comp (list_cspec _ pure_atom_cspec) gamma0 gamma1...
 do_comp (list_cspec _ pure_atom_cspec) delta delta0...
 do_comp (list_cspec _ pure_atom_cspec) delta0 delta1...
 do_comp (list_cspec _ pure_atom_cspec) delta0 delta1...
 replace (compare_list pure_atom_cmp delta delta1)  with Lt by (eapply comp_trans; eauto)...
 do_comp (list_cspec _ pure_atom_cspec) gamma0 gamma1...
 replace (compare_list pure_atom_cmp gamma gamma1)  with Lt by (eapply comp_trans; eauto)...
 (* CompSpec *)
 destruct x; destruct y; simpl in *...
 do_comp (list_cspec _ pure_atom_cspec) gamma gamma0...
 do_comp (list_cspec _ pure_atom_cspec) delta delta0...
 do_comp (list_cspec _ pure_atom_cspec) gamma gamma0...
 do_comp (list_cspec _ pure_atom_cspec) delta delta0...
 do_comp (list_cspec _ space_atom_cspec) sigma sigma0...
 do_comp (list_cspec _ pure_atom_cspec) gamma gamma0...
 do_comp (list_cspec _ pure_atom_cspec) delta delta0...
 do_comp (list_cspec _ space_atom_cspec) sigma sigma0...
Qed.

Hint Resolve clause_cspec.

Definition rev_cmp {A : Type} (cmp : A -> A -> comparison) :=
  fun a b => match cmp a b with Eq => Eq | Lt => Gt | Gt => Lt end.

Lemma rev_cmp_cspec {A} (c: A -> A -> comparison) :
  CompSpec' c -> CompSpec' (rev_cmp c).
Proof with try solve[congruence].
intro H; unfold rev_cmp; repeat constructor; repeat intro.
apply comp_refl with (x := x) in H... rewrite H in H0...
do_comp H x y... do_comp H y z...
assert (Lt = c z x) by (eapply comp_trans; eauto).
rewrite comp_antisym in H2; auto. rewrite <-H2; auto.
do_comp H x y. subst; constructor; auto.
constructor; rewrite comp_antisym in e; auto; rewrite <-e; auto.
constructor. rewrite comp_antisym in e; auto. rewrite <-e; auto.
Qed.

Lemma rev_cmp_eq : forall {A : Type} (cmp : A -> A -> comparison) (x y : A),
  (forall x0 y0 : A, Eq = cmp x0 y0 -> x0 = y0) ->
  Eq = rev_cmp cmp x y -> x = y.
Proof.
intros until y; intros H H1.
unfold rev_cmp in H1. remember (cmp x y) as b. destruct b;try solve[congruence].
apply H; auto.
Qed.

Definition prio1000 := Z2id 1000.
Definition prio1001 := Z2id 1001.

Definition clause_prio (cl : clause) : var :=
  match cl with
  | PureClause gamma delta prio _ => prio
  | PosSpaceClause _ _ _ => prio1000
  | NegSpaceClause gamma sigma delta => prio1001
  end%Z.


Definition compare_clause' (cl1 cl2 : clause) : comparison :=
  match Ident.compare (clause_prio cl1) (clause_prio cl2) with
  | Eq => compare_clause cl1 cl2
  | c => c
  end.

Lemma clause_cspec': CompSpec' compare_clause'.
Proof with (repeat (comp_tac || solve [econstructor; simpl; repeat comp_tac])).
 unfold compare_clause';
  repeat constructor; repeat intro.
 (* irrefl *)
  id_compare (clause_prio x) (clause_prio x)...
  apply (Ilt_irrefl l).
 (* trans *)
  id_compare (clause_prio x) (clause_prio y). rewrite e.
  id_compare (clause_prio y) (clause_prio z)...
  id_compare (clause_prio y) (clause_prio z)...
  rewrite e in l.
  id_compare (clause_prio x) (clause_prio z)...
  rewrite e0 in l.   contradiction (Ilt_irrefl l).
  contradiction (Ilt_irrefl (Ilt_trans l l0)).
  id_compare (clause_prio x) (clause_prio z)...
  rewrite e in *.   contradiction (Ilt_irrefl (Ilt_trans l l0)).
  contradiction (Ilt_irrefl (Ilt_trans l1 (Ilt_trans l l0))).
  id_compare (clause_prio y) (clause_prio z)...
  (* CompSpec *)
  id_compare (clause_prio x) (clause_prio y).
  do_comp clause_cspec x y...
  econstructor. rewrite e.
  id_compare (clause_prio y) (clause_prio y)...
  contradiction (Ilt_irrefl l).
  constructor... rewrite e.
  id_compare (clause_prio y) (clause_prio y)...
  contradiction (Ilt_irrefl l).
  constructor...
  id_compare (clause_prio x) (clause_prio y)...
  rewrite e in l.
  contradiction (Ilt_irrefl l).
  contradiction (Ilt_irrefl (Ilt_trans l l0)).
  constructor...
  id_compare (clause_prio y) (clause_prio x)...
  rewrite e in l.
  contradiction (Ilt_irrefl l).
  contradiction (Ilt_irrefl (Ilt_trans l l0)).
Qed.

Hint Resolve clause_cspec'.



Definition clause_length (cl : clause) : Z :=
  match cl with
  | PureClause gamma delta _ _ => Zlength gamma + Zlength delta
  | PosSpaceClause gamma delta sigma =>
      Zlength gamma + Zlength delta + Zlength sigma
  | NegSpaceClause gamma sigma delta =>
      Zlength gamma + Zlength sigma + Zlength delta
  end%Z.

Definition compare_clause_length (cl1 cl2 : clause) :=
   Zcompare (clause_length cl1) (clause_length cl2).

Definition compare_clause'1 (cl1 cl2 : clause) : comparison :=
  match compare_clause_length cl1 cl2 with
  | Eq => compare_clause cl1 cl2
  | c => c
  end.

Lemma clause_cspec'1: CompSpec' compare_clause'1.
Proof with (repeat (comp_tac || solve [econstructor; simpl; repeat comp_tac])).
 unfold compare_clause'1;
  repeat constructor; repeat intro.
 (* irrefl *)
  rewrite (comp_refl _ clause_cspec) in H;   unfold compare_clause_length in *;
  destruct x; simpl in *;
  rewrite Zcompare_refl in H; repeat (rewrite comp_refl in H; auto); congruence.
 (* trans *)
  remember (compare_clause_length x y) as j; destruct j.
  remember (compare_clause_length y z) as j; destruct j.
  replace (compare_clause_length x z) with Eq...
  symmetry in Heqj,Heqj0|-*.
  clear - Heqj Heqj0.
  apply Zcompare_Eq_iff_eq.
  apply Zcompare_Eq_eq in Heqj.
  apply Zcompare_Eq_eq in Heqj0.
  congruence.
  unfold compare_clause_length in *.
  symmetry in Heqj; apply Zcompare_Eq_eq in Heqj. rewrite Heqj. rewrite <- Heqj0; auto.
  unfold compare_clause_length in *.
  symmetry in Heqj; apply Zcompare_Eq_eq in Heqj. rewrite Heqj. rewrite <- Heqj0; auto.
  remember (compare_clause_length y z) as j; destruct j.
  unfold compare_clause_length in *.
  symmetry in Heqj0; apply Zcompare_Eq_eq in Heqj0. rewrite <- Heqj0. rewrite <- Heqj; auto.
  replace (compare_clause_length x z) with Lt; auto.
  unfold compare_clause_length in *.
  symmetry in Heqj,Heqj0|-*.
  eapply Zcompare_Lt_trans; eauto.
  inversion H0.
  inversion H.
  (* CompSpec *)
  remember (compare_clause_length x y) as j; destruct j.
  do_comp clause_cspec x y...
  econstructor.
  unfold compare_clause_length in *.
  symmetry in Heqj.
  apply Zcompare_Eq_eq in Heqj. rewrite Heqj.
  rewrite Zcompare_refl. auto.
  constructor; auto. rewrite <- Heqj; auto.
  constructor; auto.
  replace (compare_clause_length y x) with Lt; auto.
  symmetry in Heqj|-*; apply Zcompare_Gt_Lt_antisym; auto.
Qed.

Hint Resolve clause_cspec'1.

Module OrderedClause <: OrderedType
  with Definition t:=clause
  with Definition compare:=compare_clause'.

Definition t := clause.

Definition eq : clause -> clause -> Prop := Logic.eq.

Lemma eq_equiv : Equivalence eq.
Proof.  apply eq_equivalence. Qed.

Definition lt (c1 c2 : clause) := Lt = compare_clause' c1 c2.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
intros. constructor; unfold eq in H,H0; subst; auto.
Qed.

Definition compare := compare_clause'.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.  destruct clause_cspec'; auto. Qed.

Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.
Proof.
intros; unfold eq.
remember (compare x y) as j; destruct j.
destruct (CompSpec2Type (compare_spec x y)); try discriminate. left; auto.
right; intro; subst.
unfold compare in Heqj; rewrite comp_refl in Heqj; auto.
inversion Heqj.
do_comp clause_cspec' x y; subst; auto.
right; intro; subst. rewrite comp_refl in e; auto. inversion e.
right; intro; subst. rewrite comp_refl in e; auto. inversion e.
Qed.

Lemma lt_strorder : StrictOrder lt.
Proof. destruct clause_cspec'; auto. Qed.

End OrderedClause.

(* The clause database.  There are two alternate implementations.
  The first uses MSetAVL from the Coq library, the second uses red-black trees.
  Since red-black trees match an enhanced interface MSetPlus,
  in the first implementation we define the additional operator(s) in terms
  of what's available in MSetAVL.
*)

(* First implementation *)

Module M1 : redblack.MSetPlus
   with Definition E.t := OrderedClause.t
   with Definition E.compare := OrderedClause.compare
   with Definition E.eq := OrderedClause.eq
   with Definition E.lt := OrderedClause.lt
   with Definition E.compare := OrderedClause.compare.
 Include MSetAVL.Make(OrderedClause).
 Definition delete_min (s: t) : option (elt * t) :=
   match min_elt s with
   | Some x => Some (x, remove x s)
   | None => None
  end.
 Lemma delete_min_spec1: forall (s: t) k s',
    delete_min s = Some (k,s') <->
    (min_elt s = Some k /\ remove k s = s').
  Proof.
   intros. unfold delete_min.
   case_eq (min_elt s); intros.
   intuition. inversion H0; clear H0; subst; auto.
     inversion H0; clear H0; subst; auto. inversion H1; clear H1; subst; auto.
     intuition; discriminate.
  Qed.
 Lemma delete_min_spec2: forall s, delete_min s = None <-> Empty s.
 Proof. unfold delete_min; intros.
   case_eq (min_elt s); intros.
  intuition; try discriminate.
  apply min_elt_spec1 in H.
  apply H0 in H; contradiction.
  apply min_elt_spec3 in H.
  intuition.
  Qed.
Definition mem_add (x: elt) (s: t) : option t :=
 if mem x s then None else Some (add x s).

Lemma mem_add_spec:
    forall x s, mem_add x s = if mem x s then None else Some (add x s).
Proof. auto. Qed.
End M1.

(* Second implementation *)
Module M := redblack.Make(OrderedClause).

Definition clause_list2set (l : list clause) : M.t :=
  fold_left (fun s0 c => M.add c s0) l M.empty.

Definition empty_clause : clause := mkPureClause nil nil.

Definition remove_trivial_atoms := filter (fun a =>
  match a with
  | Eqv e1 e2 => match expr_cmp e1 e2 with
                 | Eq => false
                 | _ => true
                 end
  end).

Definition subst_pures_delete (i: var) (e: expr)
  : list pure_atom -> list pure_atom :=
  remove_trivial_atoms oo subst_pures i e.

Definition isEq cc := match cc with Eq => true | _ => false end.

Definition eq_space_atom (a b : space_atom) : bool :=
  isEq (compare_space_atom a b).

Definition eq_space_atomlist (a b : list space_atom) : bool :=
  isEq (compare_list compare_space_atom a b).

Definition eq_var i j : bool := isEq (Ident.compare i j).

Definition drop_reflex_lseg : list space_atom -> list space_atom :=
  filter (fun sa =>
                    match sa with
                    | Lseg (Var x) (Var y) => negb (eq_var x y)
                    | Lseg Nil Nil => false
                    | _ => true
                    end).

Definition order_eqv_pure_atoms := map order_eqv_pure_atom.

Definition greater_than_expr (i: var) (e: expr) :=
  match e with Var j => match Ident.compare i j with Gt => true | _ => false end
                        | Nil => true
  end.

Definition greatereq_than_expr (i: var) (e: expr) :=
  match e with
  | Var j => match Ident.compare i j with Gt => true | Eq => true | Lt => false
             end
  | Nil => true
  end.

Definition greater_than_atom (s u : pure_atom) :=
  match s , u with
  | Eqv s t , Eqv u v =>
    ((expr_lt u s && (expr_geq s v || expr_geq t v)) ||
      (expr_lt v s && (expr_geq s u || expr_geq t u))) ||
    ((expr_lt u t && (expr_geq s v || expr_geq t v)) ||
      (expr_lt v t && (expr_geq s u || expr_geq t u)))
  end.

Definition greater_than_atoms (s : pure_atom) (delta : list pure_atom) :=
  forallb (fun u => greater_than_atom s u) delta.

Definition greater_than_all (i: var) : list pure_atom -> bool :=
  forallb (fun a => match a with Eqv x y =>
             andb (greater_than_expr i x) (greater_than_expr i y) end).

Definition subst_clause i e cl : clause :=
  match cl with
  | PureClause pa pa' _ _ =>
      mkPureClause (subst_pures_delete i e pa) (subst_pures i e pa')
  | NegSpaceClause pa sa pa' =>
      NegSpaceClause (subst_pures_delete i e pa) (subst_spaces i e sa)
                     (subst_pures i e pa')
  | PosSpaceClause pa pa' sa' =>
      PosSpaceClause (subst_pures_delete i e pa) (subst_pures i e pa')
                     (subst_spaces i e sa')
  end.

(* fix this *)

Definition var_eqZ v v' := Ident.eq v v'.

Lemma eq_pos_var_eqZ v v' : true = eq_var v v' -> var_eqZ v v'.
Proof.
unfold eq_var, var_eqZ.
intros; id_compare v v'; auto; discriminate.
Qed.

(* general functions that should be moved elsewhere *)

Definition ocons {A : Type} (o : option A) l :=
  match o with Some a => a :: l | None => l end.

Fixpoint omapl {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | a :: l' => ocons (f a) (omapl f l')
  | nil => nil
  end.

Fixpoint merge {A: Type} (cmp : A -> A -> comparison) l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      match cmp a1 a2 with
      | Eq => a1 :: merge cmp l1' l2'
      | Gt => a1 :: merge cmp l1' l2
      | _ => a2 :: merge_aux l2' end
  end
  in merge_aux l2.

Notation sortu_atms := (rsort_uniq pure_atom_cmp).
Notation insu_atm := (insert_uniq pure_atom_cmp).
Notation sortu_clauses := (rsort_uniq compare_clause).


Lemma compare_clause_eq_equivalence:
     RelationClasses.Equivalence (fun c1 c2 => Eq = compare_clause c1 c2).
Proof.
constructor; repeat intro.
rewrite comp_refl; auto.
do_comp clause_cspec x y; try congruence. subst; rewrite comp_refl; auto.
do_comp clause_cspec x y; try congruence.
Qed.

Lemma pure_clause_ext:
  forall gamma delta p Pp p' Pp',
     PureClause gamma delta p Pp = PureClause gamma delta p' Pp'.
Proof.
  intros. subst. auto.
Qed.


Lemma expr_eq_eq' : forall e1 e2, true = expr_eq e1 e2 -> e1=e2.
Proof.
unfold expr_eq; intros; do_comp expr_cspec e1 e2; subst; auto; congruence.
Qed.

Lemma mem_spec': forall s x, M.mem x s = false <-> ~M.In x s.
Proof.
 intros. rewrite <- M.mem_spec. destruct (M.mem x s); intuition discriminate.
Qed.

Lemma is_empty_spec': forall s, M.is_empty s = false <-> ~M.Empty s.
Proof.
 intros. rewrite <- M.is_empty_spec. destruct (M.is_empty s); intuition discriminate.
Qed.

Lemma empty_set_elems':
  forall s, M.Empty s <-> M.elements s = nil.
Proof.
intros.
generalize (M.elements_spec1 s); intro.
destruct (M.elements s); intuition.
intros ? ?.
rewrite <- H in H1.
inversion H1.
contradiction (H0 e).
rewrite <- H. left; auto.
inversion H0.
Qed.

Lemma Melements_spec1: forall (s: M.t) x, List.In x (M.elements s) <-> M.In x s.
Proof.
intros.
rewrite <- M.elements_spec1.
induction (M.elements s); intuition;
try solve [inversion H].
simpl in H1. destruct H1; subst.
constructor; auto.
constructor 2; auto.
inversion H1; clear H1; subst; simpl; auto.
Qed.

Require Import Finite_sets_facts.
Require Import VST.msl.Axioms.

Lemma Mcardinal_spec': forall s,   cardinal _ (Basics.flip M.In s) (M.cardinal s).
Proof.
 intros.
 rewrite (M.cardinal_spec s).
 generalize (M.elements_spec1 s); intro.
 replace (Basics.flip M.In s) with (Basics.flip (@List.In _) (M.elements s)).
Focus 2.
unfold Basics.flip; apply extensionality; intro x;
apply prop_ext; rewrite <- (H x).
clear; intuition.
apply SetoidList.In_InA; auto.
apply eq_equivalence.
rewrite SetoidList.InA_alt in H.
destruct H as [? [? ?]].
subst; auto.
(* End Focus 2 *)
 clear H.
 generalize (M.elements_spec2w s); intro.
 remember (M.elements s) as l.
 clear s Heql.
 induction H.
 replace (Basics.flip (@List.In M.elt) (@nil clause)) with (@Empty_set M.elt).
 constructor 1.
 apply Axioms.extensionality; intro; apply Axioms.prop_ext; intuition; inversion H.
 simpl.
 replace (Basics.flip (@List.In M.elt) (@cons clause x l))
   with (Add M.elt (Basics.flip (@List.In _) l) x).
 constructor 2; auto.
 contradict H.
 simpl.
 apply SetoidList.In_InA; auto.
 apply eq_equivalence.
 clear.
 apply Axioms.extensionality; intro; apply Axioms.prop_ext; intuition.
 unfold Basics.flip; simpl.
 unfold Add in H. destruct H; auto.
 apply Singleton_inv in H. auto.
 simpl in H; destruct H; [right | left].
 apply Singleton_intro. auto.
 apply H.
Qed.

Lemma remove_decreases:
  forall giv unselected,
  M.In giv unselected ->
  M.cardinal  (M.remove giv unselected)  < M.cardinal  unselected.
Proof.
 intros.
 generalize (Mcardinal_spec' (M.remove giv unselected)); intro.
 generalize (Mcardinal_spec' unselected); intro.
 generalize (card_soustr_1 _ _ _ H1 _ H); intro.
 rewrite (cardinal_is_functional _ _ _ H0 _ _ H2).
 assert (M.cardinal unselected > 0).
 generalize (Mcardinal_spec' unselected); intro.
 inversion H3; clear H3; subst.
 assert (Empty_set M.elt giv). rewrite H5. unfold Basics.flip. auto.
 inversion H3.
 omega.
 omega.
 clear - H.
 apply Axioms.extensionality;  intro x.
 unfold Basics.flip at 1.
 apply Axioms.prop_ext; intuition.
rewrite M.remove_spec in H0.
destruct H0.
split.
unfold In, Basics.flip. auto.
intro.
apply Singleton_inv in H2.
subst. contradiction H1; auto.
destruct H0.
rewrite M.remove_spec.
split; auto.
intro.
subst.
apply H1; apply Singleton_intro.
auto.
Qed.

(** a second comparison function on clauses that meets the requirements
   of model generation *)

Definition pure_atom2pn_atom (b : bool) (a : pure_atom) :=
  match a with
  | Eqv e1 e2 => if b then Equ e1 e2 else Nequ e1 e2
  end.

Definition pn_atom_cmp (a1 a2 : pn_atom) : comparison :=
  match a1, a2 with
  | Equ e1 e2, Equ e1' e2' => pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  | Nequ e1 e2, Equ e1' e2' =>
    if expr_eq e1 e1' then Gt else pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  | Equ e1 e2, Nequ e1' e2' =>
    if expr_eq e1 e1' then Lt else pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  | Nequ e1 e2, Nequ e1' e2' => pure_atom_cmp (Eqv e1 e2) (Eqv e1' e2')
  end.

Definition pure_clause2pn_list (c : clause) :=
  match c with
  | PureClause gamma delta _ _ =>
    rsort pn_atom_cmp
      (map (pure_atom2pn_atom false) gamma ++ map (pure_atom2pn_atom true) delta)
  | _ => nil
  end.

Definition compare_clause2 (cl1 cl2 : clause) :=
  match cl1, cl2 with
  | PureClause _ _ _ _, PureClause _ _ _ _ =>
    compare_list pn_atom_cmp (pure_clause2pn_list cl1) (pure_clause2pn_list cl2)
  | _, _ => compare_clause cl1 cl2
  end.

Lemma compare_clause_eq cl1 cl2 : Eq = compare_clause cl1 cl2 -> cl1 = cl2.
Proof. intros; do_comp clause_cspec cl1 cl2; auto; congruence. Qed.

Inductive ce_type := CexpL | CexpR | CexpEf.

(** Patch until Coq extraction of sharing constraints is fixed *)

Module DebuggingHooks.

(* To add a new debugging hook, do the following:
   -define a new function equal to the identity on the type of whatever
   value you want to report
   -define a corresponding ML function with the same name in extract/debugging.ml
   to do the actual reporting
*)
Definition print_new_pures_set (s: M.t) := s.

Definition print_wf_set (s: M.t) := s.

Definition print_unfold_set (s: M.t) := s.

Definition print_inferred_list (l: list clause) := l.

Definition print_pures_list (l: list clause) := l.

Definition print_eqs_list (l: list clause) := l.

Definition print_spatial_model (c: clause) (R: list (var * expr)) := c.

Definition print_spatial_model2 (c c': clause) (R: list (var * expr)) := c'.

Definition print_ce_clause (R: list (var * expr)) (cl : clause) (ct : ce_type)
  := (R, cl, ct).

End DebuggingHooks.

Export DebuggingHooks.

Hint Unfold print_new_pures_set print_wf_set print_inferred_list print_spatial_model
            print_pures_list print_eqs_list
  : DEBUG_UNFOLD.

