Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Module FunspecOrder <: Orders.TotalLeBool.
  Definition t := (ident * funspec)%type.
  Definition leb := fun x y : (ident * funspec)=> Pos.leb (fst x) (fst y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.  intros. unfold leb. 
    pose proof (Pos.leb_spec (fst a1) (fst a2)).
    pose proof (Pos.leb_spec (fst a2) (fst a1)).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End FunspecOrder.
Module SortFunspec := Mergesort.Sort(FunspecOrder).

Record SortedComponent {Espec V cs} Externs Imports p Exports G:= {
  SC_component :> @Component Espec V cs Externs Imports p Exports G;
  SC_sorted: (*G = SortFunspec.sort G*) Sorted.LocallySorted
         (fun x x0 : ident * funspec =>
          Datatypes.is_true
            ((fun x1 y : ident * funspec => (fst x1 <=? fst y)%positive) x x0))  G
}.
Require Import VST.veric.initial_world.

Lemma perm_In_map_fst {A}: forall {G:list (ident*A)} {G'} (P: Permutation G G') i,
      In i (map fst G') -> In i (map fst G).
Proof. intros G G' P. induction P; simpl; intros; trivial.
+ destruct x; simpl in *; intros.
  destruct H; [ left; trivial | right; auto].
+ destruct H as [? | [? | ?]]. right; left; trivial. left; trivial. right; right; trivial.
+ apply IHP1. apply IHP2; trivial.
Qed.
 
Lemma perm_LNR {A}: forall {G:list (ident * A)} {G'} (P: Permutation G G')
      (LNR: list_norepet (map fst G)),
      list_norepet (map fst G').
Proof. intros G G' P. induction P; simpl; intros; trivial; auto.
+ destruct x. inv LNR. constructor; eauto. simpl.
  intros N. apply H1. apply (perm_In_map_fst P); trivial.
+ inv LNR. inv H2. constructor.
  - intros N. destruct N; auto. rewrite H in *; apply H1; left; trivial.
  - constructor; trivial. intros N. apply H1. right; trivial.
Qed.

Lemma perm_find_id {A}: forall (G:list (ident * A)) G' (P: Permutation G G')
      (LNR: list_norepet (map fst G)) i,
      find_id i G = find_id i G'.
Proof. intros G G' P. induction P; simpl; intros; trivial.
+ destruct x. inv LNR. rewrite IHP; trivial.
+ destruct y. destruct x; simpl in *. inv LNR. inv H2.
  destruct (Memory.EqDec_ident i i0); subst; trivial.
  rewrite if_false; trivial. intros N; subst. apply H1; left; trivial.
+ rewrite IHP1; trivial. apply IHP2.
  apply (perm_LNR P1); trivial.
Qed.

Lemma sort_In_map_fst {G i}:
      In i (map fst G) <-> In i (map fst (SortFunspec.sort G)).
Proof.
split; intros; eapply perm_In_map_fst; try eassumption.
apply Permutation_sym. apply SortFunspec.Permuted_sort.
apply SortFunspec.Permuted_sort.
Qed.

Lemma sort_LNR {G}: list_norepet (map fst G) <->
      list_norepet (map fst (SortFunspec.sort G)).
Proof.
split; intros; eapply perm_LNR; try eassumption.
apply SortFunspec.Permuted_sort.
apply Permutation_sym. apply SortFunspec.Permuted_sort.
Qed.

Lemma sort_find_id {G i} (LNR: list_norepet (map fst G)) :
      find_id i G = find_id i (SortFunspec.sort G).
Proof.
apply perm_find_id; trivial.
apply SortFunspec.Permuted_sort.
Qed.

Definition SortComponent {Espec V cs Externs Imports p Exports G} 
           (C:@Component Espec V cs Externs Imports p Exports G):
           @SortedComponent Espec V cs Externs Imports p Exports (SortFunspec.sort G).
constructor; [ | apply SortFunspec.Sorted_sort].
specialize (Comp_ctx_LNR C); intros DISJ.
destruct C; unfold Comp_G in DISJ.
constructor; trivial.
+ clear - Comp_G_dom Comp_G_LNR. intros. destruct (Comp_G_dom i); clear Comp_G_dom.
  split; intros.
  - apply H in H1. clear - Comp_G_LNR H1.
    destruct (assoclists.In_map_fst_find_id H1 Comp_G_LNR) as [x Hx].
    apply (@sort_In_map_fst G); trivial. 
  - apply H0. clear - Comp_G_LNR H1.
    apply sort_In_map_fst; trivial.
+ clear - Comp_G_LNR. apply (@sort_LNR G); trivial.
+ intros. rewrite (Comp_G_E _ H). clear - Comp_G_LNR.
  apply sort_find_id; trivial.
+ intros. eapply SF_ctx_extensional.
  - apply (Comp_G_justified i phi fd). trivial. clear - H0 Comp_G_LNR.
     rewrite (sort_find_id Comp_G_LNR); trivial.
  - apply DISJ.
  - clear - DISJ Comp_G_LNR. intros. rewrite 2 assoclists.find_id_app_char. 
    rewrite (sort_find_id Comp_G_LNR). trivial.
+ intros. destruct (Comp_G_Exports _ _ E) as [phi' [? ?]].
  exists phi'; split; trivial. clear - H Comp_G_LNR.
  rewrite <- (sort_find_id Comp_G_LNR). trivial.
Qed.

Ltac prove_cspecs_sub := split3; intros ?i; apply sub_option_get;
     repeat (constructor; [ reflexivity |]); constructor.

Ltac solve_entry H H0:=
     inv H; inv H0; first [ solve [ trivial ] | split; [ reflexivity | eexists; reflexivity] ].

Ltac LNR_tac := apply compute_list_norepet_e; reflexivity.

Ltac list_disjoint_tac := (*red; simpl; intros; contradiction.*)
     apply list_norepet_append_inv; LNR_tac.

Ltac ExternsHyp_tac := first [ reflexivity | idtac ].
Ltac SC_tac := simpl; intros ? ? X H;
  repeat (destruct H; [ subst; simpl; simpl in X; try discriminate | ]);
  inv X; first [ eexists; split; [reflexivity | apply funspec_sub_refl] | idtac]; try contradiction.

Ltac HImports_tac := simpl; intros ? ? ? H1 H2;
  repeat (if_tac in H1; subst; simpl in *; try discriminate).

Ltac ImportsDef_tac := first [ reflexivity | idtac ].
Ltac ExportsDef_tac := first [ reflexivity | idtac ].
Ltac domV_tac := cbv; intros; auto.

Ltac FunctionsPreserved_tac :=
  eapply FP_entries_sound;
  [ cbv; reflexivity
  | solve [repeat (constructor; [ reflexivity | ]); constructor]
  | cbv; reflexivity
  | repeat (constructor; [ reflexivity | ]); constructor
  | cbv; reflexivity ].
Ltac FDM_tac := eapply FDM; [ cbv; reflexivity | repeat (constructor; [ cbv; reflexivity | ]); constructor].

Ltac find_id_subset_tac := simpl; intros ? ? H;
  repeat (if_tac in H; [ inv H; simpl; try reflexivity | ]); discriminate.

Ltac ComponentMerge C1 C2 :=
  eapply (ComponentJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 C2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
| FDM_tac
| FunctionsPreserved_tac
| list_disjoint_tac
| list_disjoint_tac
| ExternsHyp_tac
| SC_tac
| SC_tac
| HImports_tac
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
| ImportsDef_tac
| ExportsDef_tac
| LNR_tac
| LNR_tac
| domV_tac
].

Ltac VSUMerge VSU1 VSU2 :=
  eapply (VSUJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ VSU1 VSU2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
| FDM_tac
| FunctionsPreserved_tac
| list_disjoint_tac
| list_disjoint_tac
| ExternsHyp_tac
| SC_tac
| SC_tac
| HImports_tac
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
| ImportsDef_tac
| ExportsDef_tac
| LNR_tac
| LNR_tac
| domV_tac
].

Require Import VST.floyd.linking.
Require Import VST.veric.initial_world.
(*
Definition mergeTwoGdefs (g1: globdef (fundef function) type) (d2: option (globdef (fundef function) type)):=
match d2 with
  Some g2 => match merge_globdef g1 g2 with 
              Errors.OK g => g
            | Errors.Error el => g1
             end
| None => g1
end.

Definition merge_Gdefs_aux (l1 l2 : list (ident * globdef (fundef function) type)) : list (ident * globdef (fundef function) type):=
  map (fun x => match x with (i,phi1) =>
                    (i, mergeTwoGdefs phi1 (find_id i l2))
                   end) l1.

Definition merge_Gdefs l1 l2 :=
  merge_Gdefs_aux l1 l2 ++ 
  filter (fun x => match x with (i,a) => match find_id i l1 with 
                                                 Some phi => false | None => true end end) l2.

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
 let d := merge_Gdefs d1 d2 in 
 Errors.bind (merge_prog_types (*(SortComp.sort t1) (SortComp.sort t2)*)t1 t2) (fun t =>
 match build_composite_env t as e 
       return (build_composite_env t = e -> Errors.res Clight.program) with
 | Errors.Error err => fun _ => Errors.Error err
 | Errors.OK e =>  fun q => 
 if negb (eqb_ident m1 m2) 
   then Errors.Error [Errors.MSG "main identifiers differ"]
   else
    Errors.OK {| prog_defs := d;
    prog_public := SortPos.merge (*(SortPos.sort p1) (SortPos.sort p2)*)p1 p2;
    prog_main := m2;
    prog_types := t;
    prog_comp_env := e;
    prog_comp_env_eq := q|} 
   end eq_refl )
end.*)

Require Import verif_stdlib. (*M is a parameter of that module, so we're getting access to it now*)
Require Import spec_fastpile_private.

Require Import verif_fastpile.
Definition PILE := (*verif_pile.*)FASTPILEPRIV M.

Require Import verif_fastonepile.
Definition ONEPILE := verif_fastonepile.ONEPILE PILE.

Definition onepile_pile_prog: Clight.program := 
  match link_progs fastpile.prog onepile.prog with
    Errors.OK p => p
  | _ => fastpile.prog (*arbitrary*)
  end.
Definition mrg_prog1 := ltac:
  (let x := eval hnf in onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).
Instance mrg_cs1 : compspecs. make_compspecs mrg_prog1. Defined.

Definition mrg_Vprog1:varspecs. mk_varspecs mrg_prog1. Defined.

(*unresolved imports*)
Definition mrg_Imports1:funspecs := MM_ASI.

Definition mrg_Exports1:funspecs := 
G_merge (spec_fastpile.PileASI M PILE) (spec_fastonepile.OnepileASI M ONEPILE).

Definition Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1
   (G_merge (Comp_G (FastpileComponent M))
            (Comp_G (OnepileComponent M PILE))).
Proof.
  ComponentMerge (FastpileComponent M) (OnepileComponent M PILE).
Qed.

Definition Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1.
Proof.
  VSUMerge (FastpilePrivateVSU M) (OnepileVSU M PILE).
Qed.
Eval compute in (map fst (Comp_G Onepile_Pile_Component)).
Definition Onepile_Pile_SortedComponent:= SortComponent Onepile_Pile_Component.
Check Onepile_Pile_SortedComponent.
Eval compute in (map fst (Comp_G Onepile_Pile_SortedComponent)).

Definition Onepile_Pile_CanonicalComponent: @CanonicalComponent  NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1
   (G_merge (Comp_G (FastpileComponent M))
            (Comp_G (OnepileComponent M PILE))).
apply (Build_CanonicalComponent _ _ _ _ _ _ _ _ Onepile_Pile_Component).
cbv; reflexivity.
Qed.

Require Import verif_fastapile.
Definition APILE := verif_fastapile.APILE (FASTPILEPRIV M).

Definition apile_onepile_pile_prog: Clight.program := 
  match link_progs mrg_prog1 fastapile.prog with
    Errors.OK p => p
  | _ => apile.prog (*arbitrary*)
  end.
Definition mrg_prog2 := ltac:
  (let x := eval hnf in apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs2 : compspecs. make_compspecs mrg_prog2. Defined.

Definition mrg_Vprog2:varspecs. mk_varspecs mrg_prog2. Defined.

(*unresolved imports*)
Definition mrg_Imports2:funspecs := MM_ASI.

Definition mrg_Exports2:funspecs := G_merge  mrg_Exports1 (Apile_ASI M PILE).

Definition Apile_Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2
   (G_merge (Comp_G (Onepile_Pile_Component))
            (Comp_G (ApileComponent M (FASTPILEPRIV M)))).
Proof.
  ComponentMerge (Onepile_Pile_Component) (ApileComponent M (FASTPILEPRIV M)).
  intuition.
Qed.

Eval compute in (map fst (Comp_G Apile_Onepile_Pile_Component)).
(*[65%positive; 66%positive; 67%positive; 70%positive; 72%positive; 77%positive;
       78%positive; 79%positive; 74%positive; 75%positive]*)

Definition Apile_Onepile_Pile_SortedComponent:= SortComponent Apile_Onepile_Pile_Component.
Eval compute in (map fst (Comp_G Apile_Onepile_Pile_SortedComponent)).
(*[65%positive; 66%positive; 67%positive; 70%positive; 72%positive; 74%positive;
       75%positive; 77%positive; 78%positive; 79%positive]*)

Definition Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2.
Proof.
  VSUMerge (Onepile_Pile_VSU) (ApileVSU M PILE).
  intuition.
Qed.

Program Definition Apile_Onepile_Pile_CanonicalComponent:=
 Build_CanonicalComponent _ _ _ _ _ _ _ _ Apile_Onepile_Pile_SortedComponent _.
Next Obligation.
cbv; reflexivity.
Qed.
(*
Definition Apile_Onepile_Pile_CanonicalComponent: @CanonicalComponent  NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2
   (G_merge (Comp_G (Onepile_Pile_Component))
            (Comp_G (ApileComponent M PILE))).
apply (Build_CanonicalComponent _ _ _ _ _ _ _ _ Apile_Onepile_Pile_Component).
cbv. reflexivity.
Qed.*)

Require Import verif_fasttriang.

Definition triang_apile_onepile_pile_prog: Clight.program := 
  match link_progs mrg_prog2 triang.prog with
    Errors.OK p => p
  | _ => triang.prog (*arbitrary*)
  end.
Definition mrg_prog3 := ltac:
  (let x := eval hnf in triang_apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs3 : compspecs. make_compspecs mrg_prog3. Defined.

Definition mrg_Vprog3:varspecs. mk_varspecs mrg_prog3. Defined.

(*unresolved imports*)
Definition mrg_Imports3:funspecs := MM_ASI.

Definition mrg_Exports3:funspecs := G_merge mrg_Exports2 (spec_fasttriang.TriangASI M).

Definition Triang_Apile_Onepile_Pile_Component:
@Component NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3
   (G_merge (Comp_G (Apile_Onepile_Pile_Component))
            (Comp_G (TriangComponent M PILE))).
Proof.
  ComponentMerge (Apile_Onepile_Pile_Component) (TriangComponent M PILE).
Qed.

Definition Triang_Apile_Onepile_Pile_SortedComponent:= SortComponent Triang_Apile_Onepile_Pile_Component.

Definition Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3.
Proof.
  VSUMerge (Apile_Onepile_Pile_VSU) (TriangVSU M PILE).
Qed.

Program Definition Triang_Apile_Onepile_Pile_CanonicalComponent:=
 Build_CanonicalComponent _ _ _ _ _ _ _ _ Triang_Apile_Onepile_Pile_SortedComponent _.
Next Obligation.
cbv; reflexivity.
Qed.

Definition mm_triang_apile_onepile_pile_prog: Clight.program := 
  match link_progs stdlib.prog mrg_prog3 with
    Errors.OK p => p
  | _ => triang.prog (*arbitrary*)
  end.
Definition coreprog := ltac:
  (let x := eval hnf in mm_triang_apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance coreCS : compspecs. make_compspecs coreprog. Defined.

Definition coreVprog:varspecs. mk_varspecs coreprog. Defined.

(*unresolved imports*)
Definition coreImports:funspecs := nil.

Definition coreExports:funspecs := G_merge MM_ASI mrg_Exports3.

Definition MM_Triang_Apile_Onepile_Pile_Component:
@Component NullExtension.Espec
   coreVprog coreCS MM_E coreImports coreprog coreExports
   (G_merge (Comp_G MMComponent)(Comp_G (Triang_Apile_Onepile_Pile_Component))
            ).
Proof.
  ComponentMerge MMComponent (Triang_Apile_Onepile_Pile_Component). congruence.
Qed.

Definition MM_Triang_Apile_Onepile_Pile_SortedComponent:= SortComponent MM_Triang_Apile_Onepile_Pile_Component.

Definition MM_Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec coreVprog coreCS MM_E coreImports coreprog coreExports.
Proof.
  VSUMerge MMVSU (Triang_Apile_Onepile_Pile_VSU). congruence.
Qed.

Definition CoreG := SortFunspec.sort
            (G_merge (Comp_G MMComponent) (Comp_G Triang_Apile_Onepile_Pile_Component)).

Program Definition CoreComponent: 
       CanonicalComponent MM_E coreImports coreprog coreExports CoreG :=
 Build_CanonicalComponent _ _ _ _ _ _ _ _ MM_Triang_Apile_Onepile_Pile_SortedComponent _.
Next Obligation.
cbv; reflexivity.
Qed.

Definition Applic_semaxfunc (*:
   semaxfunc mrg_Vprog4 (Comp_G CoreComponent)
         (Genv.globalenv mrg_prog4)
         (filter
            (fun x : positive * fundef function =>
             in_dec ident_eq (fst x) (IntIDs mrg_prog4 ++ map fst MM_E)) 
            (prog_funct mrg_prog4))
         (SortFunspec.sort
            (G_merge (Comp_G MMComponent) (Comp_G Triang_Apile_Onepile_Pile_Component)))*)
   :=@Canonical_semaxfunc _ _ _ _ _ _ _  CoreComponent.