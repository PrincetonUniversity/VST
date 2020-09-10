Require Import VST.floyd.base2.
Import ListNotations.

Module PosOrder <: Orders.TotalLeBool.
  Definition t := positive.
  Definition leb := Pos.leb.
  Theorem leb_total : forall a1 a2, Pos.leb a1 a2 = true \/ Pos.leb a2 a1 = true.
  Proof.  intros. 
    pose proof (Pos.leb_spec a1 a2).
    pose proof (Pos.leb_spec a2 a1).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End PosOrder.
Module SortPos := Mergesort.Sort(PosOrder).

Module CompOrder <: Orders.TotalLeBool.
  Definition t := composite_definition.
  Definition leb := fun x y => Pos.leb (name_composite_def x) (name_composite_def y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.  intros. unfold leb. 
    pose proof (Pos.leb_spec (name_composite_def a1) (name_composite_def a2)).
    pose proof (Pos.leb_spec (name_composite_def a2) (name_composite_def a1)).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End CompOrder.
Module SortComp := Mergesort.Sort(CompOrder).

Module GlobdefOrder <: Orders.TotalLeBool.
  Definition t := (ident * globdef (fundef function) type)%type.
  Definition leb := fun x y : (ident * globdef (fundef function) type)=> Pos.leb (fst x) (fst y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.  intros. unfold leb. 
    pose proof (Pos.leb_spec (fst a1) (fst a2)).
    pose proof (Pos.leb_spec (fst a2) (fst a1)).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End GlobdefOrder.
Module SortGlobdef := Mergesort.Sort(GlobdefOrder).

Definition isnil {A} (al: list A) := 
   match al with nil => true | _ => false end.

Lemma prod_eq_dec {A B} (Ha: forall (a1 a2:A), {a1 = a2} + {a1<>a2})
      (Hb: forall (b1 b2:B), {b1 = b2} + {b1<>b2}):
      forall (x y : A * B), {x=y} + {x<>y}.
Proof. intros. destruct x as [a1 b1]. destruct y as [a2 b2].
destruct (Ha a1 a2); [ subst | right; congruence].
destruct (Hb b1 b2); [ subst; left; trivial | right; congruence].
Defined. 

Lemma function_eq_dec (f g: function): { f=g } + { f <> g }.
Proof.
destruct f as [rtF ccF paramsF varsF tempsF bodyF].
destruct g as [rtG ccG paramsG varsG tempsG bodyG].
destruct (type_eq rtF rtG); [ subst | right; congruence].
destruct (calling_convention_eq ccF ccG); [ subst | right; congruence].
destruct (list_eq_dec (prod_eq_dec ident_eq type_eq) paramsF paramsG); [ subst | right; congruence].
destruct (list_eq_dec (prod_eq_dec ident_eq type_eq) varsF varsG); [ subst | right; congruence].
destruct (list_eq_dec (prod_eq_dec ident_eq type_eq) tempsF tempsG); [ subst | right; congruence].
destruct (semax_lemmas.eq_dec_statement bodyF bodyG); [ subst; left; trivial | right; congruence].
Defined.

Definition merge_globdef (g1 g2: globdef (fundef function) type) :=
 match g1, g2 with
 | Gfun (External _ _ _ _), Gfun (External _ _ _ _) => 
     Errors.OK g1  (* SHOULD CHECK g1=g2 *)
 | Gfun (External _ _ _ _), Gfun (Internal f2) => 
     Errors.OK g2  (* SHOULD CHECK TYPES MATCH *)
 | Gfun (Internal f1), Gfun (External _ _ _ _) =>
    Errors.OK g1  (* SHOULD CHECK TYPES MATCH *)
 | Gfun (Internal f), Gfun (Internal g) => Errors.OK g1 (*this is OK 
      since VSU.ComponentJoin contains hypothesis Fundefs_match*) 
    (*Errors.Error [Errors.MSG "internal function clash"]*)
   (* if function_eq_dec f g then Errors.OK g1
    else Errors.Error [Errors.MSG "internal function clash"]*)
 | Gvar {| gvar_info := i1; gvar_init := l1; gvar_readonly := r1; gvar_volatile := v1 |},
   Gvar {| gvar_info := i2; gvar_init := l2; gvar_readonly := r2; gvar_volatile := v2 |} =>
   if (eqb_type i1 i2 &&
      bool_eq r1 r2 &&
      bool_eq v1 v2)%bool
   then if isnil l1 
           then Errors.OK g2 
           else if isnil l2 then Errors.OK g1 
           else Errors.Error [Errors.MSG "Gvars both initialized"]
   else Errors.Error [Errors.MSG "Gvar type/readonly/volatile clash"]
  | _, _ => Errors.Error [Errors.MSG "Gvar versus Gfun"]
 end.

Function merge_global_definitions'
    (d1 d2: list (ident * globdef (fundef function) type))
    (fuel: nat) :=
 match fuel with
 | O => Errors.Error [Errors.MSG "out of fuel"]
 | S fuel' => 
  match d1, d2 with
  | nil, _ => Errors.OK d2
  | _, nil => Errors.OK d1
  | (i1,g1)::d1', (i2,g2)::d2' => 
     if Pos.ltb i1 i2 
     then match merge_global_definitions' d1' d2 fuel' with
            | Errors.OK dl => Errors.OK ((i1,g1)::dl)
            | err => err
            end
     else if Pos.ltb i2 i1
     then match merge_global_definitions' d1 d2' fuel' with
            | Errors.OK dl => Errors.OK ((i2,g2)::dl)
            | err => err
            end
    else match merge_globdef g1 g2 with
           | Errors.OK g => match merge_global_definitions' d1' d2' fuel' with
                     | Errors.OK dl => Errors.OK ((i1,g)::dl)
                     | Errors.Error el => Errors.Error el
                    end
            | Errors.Error err => Errors.Error (Errors.POS i1 :: err)
            end
 end end.

Definition merge_global_definitions
    (d1 d2: list (ident * globdef (fundef function) type)) :=
 merge_global_definitions' d1 d2 (length d1 + length d2).

Fixpoint merge_prog_types' (e1 e2: list composite_definition)
                 (fuel: nat) 
              : Errors.res (list composite_definition) :=
 match fuel with
 | O => Errors.Error [Errors.MSG "ran out of fuel in composites"]
 | S fuel' => 
 match e1, e2 with
 | nil, _ => Errors.OK e2
 | _, nil => Errors.OK e1
 | (Composite i1 su1 m1 a1 as c1) :: e1', 
   (Composite i2 su2 m2 a2 as c2) :: e2' =>
   if Pos.ltb i1 i2 
   then Errors.bind (merge_prog_types' e1' e2 fuel')
          (fun e => Errors.OK (c1::e))
   else if Pos.ltb i2 i1 
   then Errors.bind (merge_prog_types' e1 e2' fuel')
          (fun e => Errors.OK (c2::e))
   else if (eqb_su su1 su2 &&
              eqb_list eqb_member m1 m2 &&
              eqb_attr a1 a2)%bool
   then Errors.bind (merge_prog_types' e1' e2' fuel')
          (fun e => Errors.OK (c1::e))
   else Errors.Error [Errors.MSG "struct/union does not match:"; Errors.POS i1]
 end
end.

Definition merge_prog_types e1 e2 :=
 merge_prog_types' e1 e2 (S(length e1 + length e2)).
 
Definition link_progs (prog1 prog2 : Clight.program) : 
  Errors.res Clight.program :=
 match prog1, prog2 with
  {|prog_defs := d1;
    prog_public := p1;
    prog_main := m1;
    prog_types := t1;
    prog_comp_env := e1;
    prog_comp_env_eq := q1|},
  {|prog_defs := d2;
    prog_public := p2;
    prog_main := m2;
    prog_types := t2;
    prog_comp_env := e2;
    prog_comp_env_eq := q2|}  =>
 Errors.bind (merge_global_definitions 
               (SortGlobdef.sort d1) (SortGlobdef.sort d2)) (fun d =>
 Errors.bind (merge_prog_types (SortComp.sort t1) (SortComp.sort t2)) (fun t =>
 match build_composite_env t as e 
       return (build_composite_env t = e -> Errors.res Clight.program) with
 | Errors.Error err => fun _ => Errors.Error err
 | Errors.OK e =>  fun q => 
 if negb (eqb_ident m1 m2) 
   then Errors.Error [Errors.MSG "main identifiers differ"]
   else
    Errors.OK {| prog_defs := d;
    prog_public := SortPos.merge (SortPos.sort p1) (SortPos.sort p2);
    prog_main := m2;
    prog_types := t;
    prog_comp_env := e;
    prog_comp_env_eq := q|} 
   end eq_refl ))
end.

Definition link_progs_list (pl: list Clight.program) : 
  Errors.res Clight.program :=
 match pl with
 | nil => Errors.Error [Errors.MSG "no programs to link"]
 | p::pl' => List.fold_left (fun q p =>
                  match q with
                  | Errors.Error e => q
                  | Errors.OK q' => link_progs q' p
                  end) pl' (Errors.OK p)
  end.

Ltac link_progs_list pl :=
 let q := constr:(linking.link_progs_list pl) in
 let q := eval hnf in q in
 let q := eval cbv beta iota delta [linking.SortComp.sort] in q in
 let q := eval simpl in q in
 match q with
 | Errors.Error ?e => fail 1 e
 | Errors.OK ?q' => exact q'
 end.

(*duplicate of lemma in globals_lemas*)
Lemma prog_defs_Clight_mkprogram:
 forall c g p m w,
 prog_defs (Clightdefs.mkprogram c g p m w) = g.
Proof.
intros. unfold Clightdefs.mkprogram.
destruct ( build_composite_env' c w).
reflexivity.
Qed.

Lemma prog_types_Clight_mkprogram:
  forall (c : list composite_definition) (g : list (ident * globdef Clight.fundef type)) (p : list ident) 
    (m : ident) (w : wf_composites c), prog_types (Clightdefs.mkprogram c g p m w) = c.
Proof. intros. unfold prog_types. unfold Clightdefs.mkprogram.
destruct (build_composite_env' c w ); trivial.
Qed. 

Module NEW_LINK_PROGS.  (* Everything in this Module should perhaps be moved to floyd/linking.v *)

(* All of this complexity is because the naturally computed proof whose type is
     build_composite_env t12 = Errors.OK e12
  blows up:  the nested environments explode exponentially.
 And that's a pity, because after all we have  proof irrelevance.  But I could not
 think of a better way than this to exploit proof irrelevance.  -- Andrew, 7/24/2020
*)
Definition carefully_link_progs (prog1 prog2 : Clight.program) 
  (MAIN: prog_main prog1 = prog_main prog2)
  (d12: list (ident * globdef (fundef function) type))
  (Hd12: merge_global_definitions 
               (SortGlobdef.sort (prog_defs prog1)) (SortGlobdef.sort (prog_defs prog2)) = Errors.OK d12)
  (t12: list composite_definition) 
  (Ht12: merge_prog_types (SortComp.sort (prog_types prog1)) (SortComp.sort (prog_types prog2)) = Errors.OK t12)
  (e12: composite_env)
  (He12: build_composite_env t12 = Errors.OK e12)
  : Clight.program := 
 {| prog_defs := d12;
    prog_public := SortPos.merge (SortPos.sort (prog_public prog1)) (SortPos.sort (prog_public prog2));
    prog_main := prog_main prog2;
    prog_types := t12;
    prog_comp_env := e12;
    prog_comp_env_eq := He12|} .

Lemma Gt_neq_Lt: Gt = Lt -> False.
Proof. congruence. Qed.

Lemma prove_exists_align_attr:
  forall d, two_power_nat (Z.to_nat (Z.log2 d)) = d ->
    exists n, align_attr noattr d = two_power_nat n.
Proof.
intros.
exists (Z.to_nat (Z.log2 d)).
rewrite H. reflexivity.
Qed.

Lemma prove_align_attr:
  forall i j,  (j/i)*i=j -> (align_attr noattr i | j).
Proof. intros. exists (j/i). symmetry. apply H. Qed. 

Ltac process_composite_definitions_step := 
repeat
match goal with
|- Errors.bind match ?z with _ => _ end  _  = _ => 
  set (j := z); hnf in j; simpl in j; subst j; cbv beta iota
end;
 match goal with |- context [Ctypes.composite_of_def_obligation_1 _ _ _ _] =>
   set (x := Ctypes.composite_of_def_obligation_1 _ _ _ _);
  simpl in x;
  match type of x with ?t => 
    replace x with (Gt_neq_Lt : t) by apply proof_irr
 end; 
  clear x
end;
 match goal with |- context [Ctypes.composite_of_def_obligation_2 _ _ _] =>
   set (x := Ctypes.composite_of_def_obligation_2 _ _ _);
  simpl in x;
  match type of x with (exists i, align_attr noattr ?d = two_power_nat i) => 
    replace x with (prove_exists_align_attr d (eq_refl _)) by apply proof_irr
 end; 
  clear x
end;
repeat
  match goal with |- context [Ctypes.composite_of_def_obligation_3 _ _ _ _] =>
   set (x := Ctypes.composite_of_def_obligation_3 _ _ _ _);
  simpl in x;
  match type of x with (align_attr noattr ?i | ?j)  => 
    replace x with (prove_align_attr i j (eq_refl _)) by apply proof_irr
 end; 
  clear x
end;
change (Errors.bind (Errors.OK ?x) ?f) with (f x); cbv beta iota.

Ltac process_composite_definitions :=
 simpl;
 unfold build_composite_env; 
 unfold add_composite_definitions, composite_of_def; 
 simpl align; simpl align_attr; simpl rank_members;
 simpl PTree.set;
 repeat process_composite_definitions_step;
 reflexivity.

Ltac do_merge_global_definitions := 
match goal with |- context [SortGlobdef.sort ?x] =>
 set (j :=SortGlobdef.sort x); hnf in j; simpl in j; subst j
end;
match goal with |- context [SortGlobdef.sort ?x] =>
 set (j :=SortGlobdef.sort x); hnf in j; simpl in j; subst j
end;
match goal with |- ?A = _ =>
 set (j :=A); hnf in j; simpl in j; subst j
end; reflexivity.

Ltac do_merge_prog_types := 
match goal with |- context [SortComp.sort ?x] =>
 set (j :=SortComp.sort x); hnf in j; simpl in j; subst j
end;
match goal with |- context [SortComp.sort ?x] =>
 set (j :=SortComp.sort x); hnf in j; simpl in j; subst j
end;
match goal with |- ?A = _ =>
 set (j :=A); hnf in j; simpl in j; subst j
end; reflexivity.  

Ltac do_link_progs_step1 p1 p2 := 
  eapply (carefully_link_progs p1 p2 (eq_refl _));
  [time "merge_global" do_merge_global_definitions
  |time "merge_types" do_merge_prog_types
  |time "process_composites" process_composite_definitions].

Ltac do_merge_global_definitions_unfold p1 p2 :=
  unfold p1; try rewrite prog_defs_Clight_mkprogram;
  unfold p2; try rewrite prog_defs_Clight_mkprogram;
  do_merge_global_definitions.

Ltac do_merge_prog_types_unfold p1 p2 :=
 unfold p1; try rewrite prog_types_Clight_mkprogram;
 unfold p2; try rewrite prog_types_Clight_mkprogram;
  do_merge_prog_types.

Ltac do_link_progs_step1_unfold p1 p2 := 
  eapply (carefully_link_progs p1 p2 (eq_refl _));
  [time "merge_global" do_merge_global_definitions_unfold p1 p2
  |time "merge_types" do_merge_prog_types_unfold p1 p2
  |time "process_composites" process_composite_definitions].

Ltac do_link_progs_step2 p := 
let x := eval hnf in p in
match x with
 {| prog_defs := ?d;
    prog_public := ?p;
    prog_main := ?m;
    prog_types := ?t;
    prog_comp_env := ?e;
    prog_comp_env_eq := _ |} =>
refine  {| prog_defs := d;
    prog_public := p;
    prog_main := m;
    prog_types := t;
    prog_comp_env := e;
    prog_comp_env_eq := _ |} 
end;
abstract (exact (prog_comp_env_eq p)).

End NEW_LINK_PROGS.
(* Now, to use NEW_LINK_PROGS, it is unfortunately necessary to do this in two steps*)
