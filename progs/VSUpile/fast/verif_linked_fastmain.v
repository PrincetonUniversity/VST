Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import PileModel. (*needed for decreasing etc*)
Require Import spec_stdlib.
Require Import spec_onepile.
Require Import fastpile.
Require Import fastapile.
Require Import spec_apile.
Require Import spec_triang.
Require Import main.
Require Import spec_main.

Section MainInstASI.
  Variable M: MallocFreeAPD.
  Variable G: list (globals -> mpred).

(*Specification of "module-instantiated main" - we permit an arbitrary G here
 (eventually, we'll roll M (or better: memmrg M gv) into G, too.*)
Definition main_inst_spec:=
 DECLARE _main
 WITH gv: globals
 PRE [ ] (*(main_preinst tt G gv)*)
    PROP ()
    PARAMS () GLOBALS (gv)
    SEP (fold_right (fun g p => g gv * p) emp G; has_ext tt)
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(mem_mgr M gv; has_ext tt; TT).
End MainInstASI.

Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [
   stdlib.prog; fastpile.prog; onepile.prog; fastapile.prog;
   triang.prog; main.prog]).

Instance LinkedCompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition LinkedVprog : varspecs. mk_varspecs linked_prog. Defined.

(*Instantiating main_spec with linked_prog rather than main.prog ensures that all 
  gv's are present after we do start_function in body_main*)
Definition mainspec (*M*) := (main_spec (*M*) linked_prog).

Section MainVSU. 
  Variable M: MallocFreeAPD.
  Variable ONEPILE:OnePileAPD.
  Variable APILE:APileAPD.

  Definition MainImports: funspecs := OnepileASI M ONEPILE ++ ApileASI M APILE ++ TriangASI M.

  Definition MyInitPred := [(*mem_mgr M; *)onepile ONEPILE None; apile APILE nil].
  Definition maininstspec (*M*) := (main_inst_spec M MyInitPred).
  
  Definition main_internal_specs: funspecs := [main_spec linked_prog].

  Definition MainVprog : varspecs. mk_varspecs main.prog. Defined.

  Definition MainGprog:funspecs := MainImports ++ main_internal_specs.

  (* Instance MainCompSpecs : compspecs. make_compspecs main.prog. Defined.
     Definition MainVprog : varspecs. mk_varspecs main.prog. Defined.*)

 (* Again, to ensure that start_function succeeds, we use LinkedCompSpecs and
    LinkedVprog*)
  Lemma body_main: semax_body LinkedVprog MainGprog f_main maininstspec.
Proof.
start_function.
sep_apply (make_mem_mgr M gv).
simpl; Intros.

forward_call gv.
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (onepile ONEPILE (Some (decreasing (Z.to_nat i))) gv;
          apile APILE (decreasing (Z.to_nat i)) gv;
          mem_mgr M gv; has_ext tt)).
- 
 entailer!.
-
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_lia.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_lia. rewrite decreasing_inc by lia.
entailer!.
-
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
lia.
forward.
cancel.
Qed.

End MainVSU.

Require Import verif_fastcore.
Require Import VST.veric.initial_world.

(*Finally, we assert existence of a mallocfree library.*)
Parameter M: MallocFreeAPD.

Lemma tc_VG: tycontext_subVG LinkedVprog (MainGprog M (ONEPILE M) (APILE M))
                             LinkedVprog (mainspec :: coreExports M).
Proof. split.
* intros i. red. rewrite 2 semax_prog.make_context_g_char, 2 make_tycontext_s_find_id by LNR_tac.
  remember (find_id i (MainGprog M (ONEPILE M) (APILE M))) as w.
  destruct w; [symmetry in Heqw | simpl; trivial].
  +  simpl in Heqw.
     repeat (if_tac in Heqw; [ subst i; inv Heqw; reflexivity |]).
     congruence.
  + repeat (if_tac; [subst i; simpl; trivial |]); trivial.
* intros i; red. rewrite 2 make_tycontext_s_find_id.
  remember (find_id i (MainGprog M (ONEPILE M) (APILE M))) as w.
  destruct w; [symmetry in Heqw | trivial]. simpl in Heqw.
  repeat (if_tac in Heqw; [ subst i; inv Heqw;
                            eexists; split; [ reflexivity | apply funspec_sub_si_refl]
                          | ]).
  congruence.
Qed.

Definition ExtIDtable : PTree.t unit :=
  ltac:(let x := constr:(fold_right (fun i t => PTree.set i tt t) (PTree.empty _) (ExtIDs linked_prog))
           in let x := eval compute in x
           in exact x).

Definition in_ExtIDs (ia: ident*funspec) : bool :=
 match PTree.get (fst ia) ExtIDtable with Some _ => true | None => false end.

Definition LinkedSYS_pre:funspecs :=
   filter in_ExtIDs (augment_funspecs linked_prog (MallocFreeASI M)).

Definition LinkedSYS:funspecs := 
  ltac: 
    (let x := eval hnf in LinkedSYS_pre in
     let x := eval simpl in x in 
     (*let x := eval compute in x in leaving this in leads Coq to timeout/crash*)
       exact x).

Lemma ApplibSys_in_LinkedSys: forall i phi, find_id i (coreBuiltins M) = Some phi -> find_id i LinkedSYS = Some phi.
  Proof.
    intros. specialize (find_id_In_map_fst _ _ _ H); intros.
    simpl in H0. repeat (destruct H0 as [HO | H0]; [ subst i; inv H; reflexivity |]). contradiction.
  Qed. 

Lemma LinkedSYS_External: forall i, In i (map fst LinkedSYS) ->
      exists ef ts t cc, find_id i (prog_defs linked_prog) = Some (Gfun (External ef ts t cc)).
  Proof.
    intros. cbv in H. 
    repeat (destruct H as [H | H];
      [ subst; try solve [do 4 eexists; split; reflexivity ]
      | ]).
    contradiction.
  Qed.

Lemma LinkedSYS_vacuous i phi: find_id i LinkedSYS = Some phi -> find_id i (coreBuiltins M) = None ->
        exists ef argsig retsig cc, 
           phi = vacuous_funspec (External ef argsig retsig cc) /\ 
           find_id i (prog_funct coreprog) = Some (External ef argsig retsig cc) /\
           ef_sig ef = {| sig_args := typlist_of_typelist argsig;
                          sig_res := rettype_of_type retsig;
                          sig_cc := cc_of_fundef (External ef argsig retsig cc) |}.
  Proof.
    intros. specialize (find_id_In_map_fst _ _ _ H); intros.
    cbv in H1.
    Time repeat (destruct H1 as [H1 | H1]; 
      [ subst; inv H; try solve [do 4 eexists; split3; reflexivity]
      | ]); try inv H0; try contradiction. (*3s*)
  Qed.

Lemma disjoint_Vprog_linkedfuncts: 
      list_disjoint (map fst LinkedVprog) (map fst (prog_funct linked_prog)).
Proof.
  intros x y X Y ?; subst x; cbv in X; apply assoclists.find_id_None_iff in Y; [ trivial | clear H Y];
  repeat (destruct X as [X | X]; [ subst y; cbv; reflexivity |]); contradiction.
Qed.

Lemma main_sub: funspec_sub (snd (main_inst_spec M (MyInitPred (ONEPILE M) (APILE M))))
                             (snd mainspec).
Proof. do_funspec_sub. unfold main_pre; simpl; Intros; subst. clear. 
  Exists (initialize.genviron2globals g) emp. unfold globvars2pred; simpl.
  unfold globvars2pred, lift2; Intros. simpl. entailer!.
  + intros. entailer!.
  + rewrite sepcon_comm; apply sepcon_derives.
    - eapply derives_trans. 2: apply verif_fastonepile.onepile_Init with (PILE:= (PILE M)).
      unfold InitGPred. simpl. unfold globvar2pred; simpl. rewrite ! sepcon_emp.
      apply andp_right.
      * eapply derives_trans. apply mapsto_zeros_memory_block.
        apply writable_readable. apply writable_Ews.
        rewrite memory_block_isptr; Intros.
        apply prop_right.
        unfold initialize.genviron2globals in *.
        destruct (Map.get g onepile._the_pile); try contradiction; auto.
        eexists; reflexivity.
      * auto.
    - unfold globvar2pred; simpl. rewrite mapsto_isptr; Intros.
       assert (headptr (initialize.genviron2globals g fastapile._a_pile)).
        unfold initialize.genviron2globals in *.
        destruct (Map.get g fastapile._a_pile); try contradiction; auto.
        eexists; reflexivity.    
      rewrite sepcon_emp by trivial. 
      eapply derives_trans. 2: apply verif_fastapile.make_apile; trivial.
      erewrite <- (mapsto_data_at''); trivial. apply derives_refl.
Qed.


Definition Imports:funspecs:=nil.
(*
Lemma CSSUB: cspecs_sub MainCompSpecs LinkedCompSpecs.
Proof.
  split3.
+ intros i; red; remember ((@cenv_cs MainCompSpecs) ! i) as w; destruct w; 
   [symmetry in Heqw; simpl in Heqw; rewrite PTree.gleaf in Heqw; congruence | trivial].
+ intros i. red. remember ((@ha_env_cs MainCompSpecs) ! i) as w. destruct w; [symmetry in Heqw | trivial].
  simpl in Heqw. rewrite PTree.gleaf in Heqw. congruence.
+ intros i. red. remember ((@la_env_cs MainCompSpecs) ! i) as w. destruct w; [symmetry in Heqw | trivial].
  simpl in Heqw. rewrite PTree.gleaf in Heqw. congruence.
Qed.*)

Require Import VST.floyd.VSU_addmain.

Definition SO_VSU: @LinkedProgVSU NullExtension.Espec LinkedVprog LinkedCompSpecs
      LinkedSYS Imports linked_prog [mainspec (*M*)]
      (fun gv => onepile (ONEPILE M) None gv * apile (APILE M)  [] gv)%logic.
Proof.
 VSUAddMain_tac (Core_CanVSU M).
   + apply disjoint_Vprog_linkedfuncts.
   + apply LinkedSYS_External.
   + eapply semax_body_subsumption.
       * eapply semax_body_funspec_sub. 
         - apply (body_main M (ONEPILE M) (APILE M)).
         - apply main_sub.
         - LNR_tac.
       * apply tycontext_sub_i99. apply tc_VG.
   + apply LinkedSYS_vacuous.
Qed.

Lemma prog_correct:
  exists G, 
 @semax_prog NullExtension.Espec LinkedCompSpecs linked_prog tt LinkedVprog G.
Proof.
  destruct SO_VSU as [G Comp MAIN]. exists G. 
  assert (DomG: map fst G = map fst (prog_funct linked_prog)).
  { destruct Comp. unfold Comp_G in *. rewrite CC_canonical.
    cbv; reflexivity. }
  prove_linked_semax_prog.
  all: rewrite augment_funspecs_eq by trivial.
  apply (@Canonical_semax_func _ _ _ _ _ _ _ _ Comp); cbv; reflexivity.
  destruct MAIN as [post [MainG MainExp]]. inv MainExp. rewrite MainG; eexists; reflexivity.
Qed.

(* Print Assumptions prog_correct. *)
