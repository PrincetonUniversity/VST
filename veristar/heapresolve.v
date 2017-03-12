Load loadpath.
Require Import ZArith Znumtheory Coq.Lists.List.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.superpose veristar.basic veristar.compare.
Import Superposition.
Require Recdef.

Module HeapResolve.

(** Normalization Rules *)

Definition normalize1_3 (pc sc : clause) : clause :=
  match pc , sc with
  | PureClause gamma (Eqv (Var x) y :: delta) _ _,
    PosSpaceClause gamma' delta' sigma =>
        PosSpaceClause (rsort_uniq pure_atom_cmp (gamma++gamma'))
                       (rsort_uniq pure_atom_cmp (delta++delta'))
                       (subst_spaces x y sigma)
  | PureClause gamma (Eqv (Var x) y :: delta) _ _,
    NegSpaceClause gamma' sigma delta' =>
         NegSpaceClause (rsort_uniq pure_atom_cmp (gamma++gamma'))
                        (subst_spaces x y sigma)
                        (rsort_uniq pure_atom_cmp (delta++delta'))
  | _ , _  => sc
  end.

Definition normalize2_4 (sc : clause) : clause :=
  match sc with
  | PosSpaceClause gamma delta sigma =>
        PosSpaceClause gamma delta (drop_reflex_lseg sigma)
  | NegSpaceClause gamma sigma delta =>
        NegSpaceClause gamma (drop_reflex_lseg sigma) delta
  | _ => sc
  end.

Definition norm (s:  M.t) (sc: clause) : clause :=
  normalize2_4 (List.fold_right normalize1_3 sc
    (rsort (rev_cmp compare_clause2) (M.elements s))).

(** Wellformedness Rules *)

Fixpoint do_well1_2 (sc: list space_atom) : list (list pure_atom) :=
  match sc with
  | Next Nil _ :: sc' => nil :: do_well1_2 sc'
  | Lseg Nil y :: sc' => [Eqv y Nil] :: do_well1_2 sc'
  | _ :: sc' => do_well1_2 sc'
  | nil => nil
  end.

(** Next x ? \in sc *)
Fixpoint next_in_dom (x : Ident.t) (sc : list space_atom) : bool :=
  match sc with
  | nil => false
  | Next (Var x') y :: sc' =>
    if Ident.eq_dec x x' then true
    else next_in_dom x sc'
  | _ :: sc' => next_in_dom x sc'
  end.

(** Next x ? \in sc, ?=y *)
Fixpoint next_in_dom1 (x : Ident.t) (y : expr) (sc : list space_atom) : bool :=
  match sc with
  | nil => false
  | Next (Var x') y' :: sc' =>
    if Ident.eq_dec x x' then if expr_eq y y' then true
    else next_in_dom1 x y sc' else next_in_dom1 x y sc'
  | _ :: sc' => next_in_dom1 x y sc'
  end.

(** Next x ? \in sc, ?<>y *)

Fixpoint next_in_dom2 (x : Ident.t) (y : expr) (sc : list space_atom)
  : option expr :=
  match sc with
  | nil => None
  | Next (Var x') y' :: sc' =>
    if Ident.eq_dec x x' then if expr_eq y y' then next_in_dom2 x y sc'
                                 else Some y'
    else next_in_dom2 x y sc'
  | _ :: sc' => next_in_dom2 x y sc'
  end.

Fixpoint do_well3 (sc: list space_atom) : list (list pure_atom) :=
  match sc with
  | Next (Var x) y :: sc' =>
    if next_in_dom x sc'
      then nil :: do_well3 sc'
      else do_well3 sc'
  | _ :: sc' => do_well3 sc'
  | nil => nil
  end.

(** Lseg x ?, ?<>y *)

Fixpoint lseg_in_dom2 (x : Ident.t) (y : expr) (sc : list space_atom)
  : option expr :=
  match sc with
  | Lseg (Var x' as x0) y0 :: sc' =>
    if Ident.eq_dec x x'
      then if negb (expr_eq y0 y) then Some y0 else lseg_in_dom2 x y sc'
      else lseg_in_dom2 x y sc'
  | _ :: sc' => lseg_in_dom2 x y sc'
  | nil => None
  end.

Fixpoint lseg_in_dom_atoms (x : Ident.t) (sc : list space_atom)
  : list pure_atom :=
  match sc with
  | Lseg (Var x' as x0) y0 :: sc' =>
    if Ident.eq_dec x x'
      then order_eqv_pure_atom (Eqv x0 y0) :: lseg_in_dom_atoms x sc'
      else lseg_in_dom_atoms x sc'
  | _ :: sc' => lseg_in_dom_atoms x sc'
  | nil => nil
  end.

Fixpoint do_well4_5 (sc : list space_atom) : list (list pure_atom) :=
  match sc with
  | Next (Var x') y :: sc' =>
    let atms := map (fun a => [a]) (lseg_in_dom_atoms x' sc') in
      atms ++ do_well4_5 sc'
  | Lseg (Var x' as x0) y :: sc' =>
    let l0 := lseg_in_dom_atoms x' sc' in
      match l0 with
      | nil => do_well4_5 sc'
      | _ :: _ =>
        let atms := map (fun a => normalize_atoms [Eqv x0 y, a]) l0 in
          atms ++ do_well4_5 sc'
      end
  | _ as a :: sc' => do_well4_5 sc'
  | nil => nil
  end.

Definition do_well (sc : list space_atom) : list (list pure_atom) :=
  do_well1_2 sc ++ do_well3 sc ++ do_well4_5 sc.

Definition do_wellformed (sc: clause) : M.t :=
 match sc with
 | PosSpaceClause gamma delta sigma =>
   let sigma' := rsort (rev_cmp compare_space_atom) sigma in
     clause_list2set
       (map (fun ats => mkPureClause gamma (normalize_atoms (ats++delta)))
         (do_well sigma'))
 | _ => M.empty
 end.

(** Unfolding Rules *)

Definition spatial_resolution (pc nc : clause) : M.t :=
  match pc , nc with
  | PosSpaceClause gamma' delta' sigma' , NegSpaceClause gamma sigma delta =>
    match eq_space_atomlist (rsort compare_space_atom sigma)
                            (rsort compare_space_atom sigma') with
    | true => M.singleton (order_eqv_clause (mkPureClause (gamma++gamma') (delta++delta')))
    | false => M.empty
      end
  | _ , _ => M.empty
  end.

Fixpoint unfolding1' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) z :: sigma2' =>
    if next_in_dom1 x' z sigma1
    (*need to reinsert since replacing lseg with next doesn't always preserve
    sorted order*)
      then
        (Eqv x z,
          insert (rev_cmp compare_space_atom) (Next x z) (rev sigma0 ++ sigma2'))
        :: unfolding1' (Lseg x z :: sigma0) sigma1 sigma2'
      else unfolding1' (Lseg x z :: sigma0) sigma1 sigma2'
  | a :: sigma2' => unfolding1' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding1 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding1' nil sigma1 sigma2 in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause gamma' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

Fixpoint unfolding2' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) z :: sigma2' =>
    match next_in_dom2 x' z sigma1 with
    | Some y =>
      (Eqv x z,
          insert (rev_cmp compare_space_atom) (Next x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z) (rev sigma0 ++ sigma2')))
        :: unfolding2' (Lseg x z :: sigma0) sigma1 sigma2'
    | None => unfolding2' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding2' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding2 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding2' nil sigma1 sigma2 in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause gamma' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

Fixpoint unfolding3' (sigma0 sigma1 sigma2 : list space_atom) :
  list (list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) Nil :: sigma2' =>
    match lseg_in_dom2 x' Nil sigma1 with
    | Some y =>
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y Nil) (rev sigma0 ++ sigma2'))
        :: unfolding3' (Lseg x Nil :: sigma0) sigma1 sigma2'
    | None => unfolding3' (Lseg x Nil :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding3' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding3 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding3' nil sigma1 sigma2 in
    let build_clause sigma2' := NegSpaceClause gamma' sigma2' delta' in
      map build_clause l0
  | _ , _ => nil
  end.

(** NPR's rule given in the paper. Confirmed unsound by NP.*)

Fixpoint unfolding4NPR' (sigma0 sigma1 sigma2 : list space_atom)
  : list (list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    match lseg_in_dom2 x' z sigma1 with
    | Some y =>
      if next_in_dom z' sigma1 then
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z) (rev sigma0 ++ sigma2'))
        :: unfolding4NPR' (Lseg x z :: sigma0) sigma1 sigma2'
      else unfolding4NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None => unfolding4NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding4NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfoldingNPR4 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding4NPR' nil sigma1 sigma2 in
    let build_clause sigma2' := NegSpaceClause gamma' sigma2' delta' in
      map build_clause l0
  | _ , _ => nil
  end.

(** Our rule; also suggested by NP. *)

Definition unfolding4 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding4NPR' nil sigma1 sigma2 in
    let GG' := rsort_uniq pure_atom_cmp (gamma ++ gamma') in
    let DD' := rsort_uniq pure_atom_cmp (delta ++ delta') in
    let build_clause sigma2' := NegSpaceClause GG' sigma2' DD' in
      map build_clause l0
  | _ , _ => nil
  end.


(** Unsound rule as given in NPR's paper *)

Fixpoint unfolding5NPR' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    match lseg_in_dom2 x' z sigma1 with
    | Some y =>
      let atms := lseg_in_dom_atoms z' sigma1 in
      let build_res atm :=
        (atm,
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z)
              (rev sigma0 ++ sigma2'))) in
        map build_res atms ++ unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None => unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding5NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding5NPR (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding5NPR' nil sigma1 sigma2 in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause gamma' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) delta')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

(** Rule as given in NPR's paper, corrected variable uses *)

Fixpoint unfolding5NPRALT' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    match lseg_in_dom2 x' z sigma1, lseg_in_dom2 x' z sigma1 with
    | Some y, _ =>
      let atms := lseg_in_dom_atoms z' sigma1 in
      let build_res atm :=
        (atm,
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z)
              (rev sigma0 ++ sigma2'))) in
        map build_res atms ++ unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None, _ => unfolding5NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding5NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

(** Our version - also suggested by NP in his reply. *)

Definition unfolding5 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding5NPR' nil sigma1 sigma2 in
    let GG' := rsort_uniq pure_atom_cmp (gamma ++ gamma') in
    let DD' := rsort_uniq pure_atom_cmp (delta ++ delta') in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause GG' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) DD')
      end in
      map build_clause l0
  | _ , _ => nil
  end.

(** Same as unfolding5NPR', but with added side-condition *)

Fixpoint unfolding6NPR' (sigma0 sigma1 sigma2 : list space_atom)
  : list (pure_atom * list space_atom) :=
  match sigma2 with
  | Lseg (Var x' as x) (Var z' as z) :: sigma2' =>
    if Ident.eq_dec x' z' then unfolding6NPR' sigma0 sigma1 sigma2' else
    match lseg_in_dom2 x' z sigma1 with
    | Some y =>
      let atms := lseg_in_dom_atoms z' sigma1 in
      let build_res atm :=
        (atm,
          insert (rev_cmp compare_space_atom) (Lseg x y)
            (insert (rev_cmp compare_space_atom) (Lseg y z)
              (rev sigma0 ++ sigma2'))) in
        map build_res atms ++ unfolding6NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    | None =>
       unfolding6NPR' (Lseg x z :: sigma0) sigma1 sigma2'
    end
  | a :: sigma2' => unfolding6NPR' (a :: sigma0) sigma1 sigma2'
  | nil => nil
  end.

Definition unfolding6 (sc1 sc2 : clause) : list clause :=
  match sc1 , sc2 with
  | PosSpaceClause gamma delta sigma1 , NegSpaceClause gamma' sigma2 delta' =>
    let l0 := unfolding6NPR' nil sigma1 sigma2 in
    let GG' := rsort_uniq pure_atom_cmp (gamma ++ gamma') in
    let DD' := rsort_uniq pure_atom_cmp (delta ++ delta') in
    let build_clause p :=
      match p with (atm, sigma2') =>
        NegSpaceClause GG' sigma2'
          (insert_uniq pure_atom_cmp (order_eqv_pure_atom atm) DD')
      end in
      (map build_clause l0)
  | _ , _ => nil
  end.

Definition mem_add (x: M.elt) (s: M.t) : option M.t :=
 if M.mem x s then None else Some (M.add x s).

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

Definition do_unfold' pc nc l :=
  unfolding1 pc nc ++
  unfolding2 pc nc ++ unfolding3 pc nc ++
  unfolding4 pc nc ++ unfolding6 pc nc ++ l.

Fixpoint do_unfold (n: nat) (pc : clause) (s : M.t) : M.t :=
  match n with
  | O => s
  | S n' =>
   match add_list_to_set  (M.fold (do_unfold' pc) s nil)  s with
   | Some s'' => do_unfold n' pc s''
   | None => s
   end
  end.

Definition unfolding (pc nc : clause) : M.t :=
  M.fold (fun c => M.union (spatial_resolution pc c))
            (do_unfold 500 pc (M.add nc M.empty)) M.empty.

End HeapResolve.
