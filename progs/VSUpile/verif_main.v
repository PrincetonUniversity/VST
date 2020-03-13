Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import verif_core.
Require Import main.
Require Import VST.veric.initial_world.

  Lemma decreasing_inc i (I:0 <= i):
  i + 1 :: spec_triang.decreasing (Z.to_nat i) = spec_triang.decreasing (Z.to_nat (i + 1)).
  Proof. 
    replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    unfold spec_triang.decreasing; fold spec_triang.decreasing.
    + f_equal. rewrite inj_S. rewrite Z2Nat.id by omega. omega.
    + rewrite <- Z2Nat.inj_succ by omega. f_equal; omega.
  Qed.

Notation M := verif_stdlib.M.


Section MainASI.
Variable p: Clight.program. (*linked_prog, or fullprog, 
or "cons main.prog component.prog", where
  component.prog = mrg_prog4 from link_pile.v*)

Definition main_spec :=
 DECLARE _main
 WITH gv: globals
 PRE [ ] main_pre p tt gv
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr 0)))
    SEP(TT).

Definition MainASI:funspecs := [ main_spec ].
End MainASI.

Definition linked_prog: Clight.program :=
 ltac: (linking.link_progs_list [ main.prog; coreprog]).

Instance LinkedCompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition ExtIDs (p: Ctypes.program function): list ident := 
  map fst ((filter (fun x => negb (isInternal (snd x)))) (prog_defs p)).

Module MainComponent_with_ExtsInE.

  Definition main_imported_specs:funspecs := nil(*verif_stdlib.MM_ASI*).
  (*placeholder:57, main:58; surely:65*)
  Eval compute in (map fst (MainASI linked_prog)). (*58, ie main*)
  Eval compute in (map fst (verif_stdlib.MM_ASI)). (*[54%positive; 55%positive; 56%positive], ie malloc, free, exit*)
  Eval compute in (map fst CoreG). 
    (*[54%positive; 55%positive; 56%positive; 57%positive; 65%positive; 66%positive; 67%positive;
       70%positive; 72%positive; 74%positive; 75%positive; 77%positive; 78%positive; 79%positive;
       81%positive], ie malloc free exit placeholder surelymalloc, Pile_new... BUT NOT MAIN OR BUILTINS*)

  Eval compute in (map fst coreExports). (*[54%positive; 55%positive; 56%positive; 66%positive; 67%positive; 70%positive; 72%positive;
       77%positive; 78%positive; 79%positive; 74%positive; 75%positive; 81%positive]*)
    (*malloc, free, exit, PileNew, ..., BUT not main, surely, place*)

  Eval compute in (IntIDs linked_prog).
    (*[57%positive; 58%positive; 65%positive; 66%positive; 67%positive; 70%positive; 72%positive;
       74%positive; 75%positive; 77%positive; 78%positive; 79%positive; 81%positive]
     ie, place, main, surely, Pile_new...*)

  Eval compute in (ExtIDs linked_prog). (*Builtins, malloc, free, exit, plus globalvars*)
 
  Eval compute in (IntIDs main.prog). (*58, main*)
  Eval compute in (ExtIDs main.prog).
    (*Builtins, Apileadd, Apilecount, onepileinit, onepileadd, onepilecount,thriang_nth,
      ie builtins plus the explicitly called funcitons -- OK*)

  Definition linked_internal_specs: funspecs := SortFunspec.sort
         (filter (fun a => in_dec ident_eq (fst a) (IntIDs linked_prog)) (main_spec linked_prog :: CoreG)).

  Goal (map fst linked_internal_specs) = (IntIDs linked_prog). cbv; trivial. Qed.

  Definition MainE_pre:funspecs := (*verif_stdlib.MM_ASI.*)
   filter (fun x => in_dec ident_eq (fst x) (ExtIDs linked_prog)) (augment_funspecs linked_prog verif_stdlib.MM_ASI).

Definition MainE:funspecs := ltac:
  (let x := eval hnf in MainE_pre in
   let x := eval simpl in x in 
   (*let x := eval compute in x in *)
       exact x). (*Takes 30s to compute...*)
Eval compute in (map fst MainE). (*Malloc, free, exit, Builtins*)

  Definition Imports: funspecs := nil.
  Definition Exports:funspecs := nil.

  Definition G := MainE ++ linked_internal_specs.

  Eval compute in (map fst CoreG).

  Definition Vprog: varspecs. mk_varspecs linked_prog. Defined. 
(*using main_prog means that the gvars from apile and onlpile won't be in Delta, 
  so start_function in body_main will fail during process_idstar. 
  (in expand_main_pre_old, ie start_function2)*)

Lemma subG1: forall i : positive,
sub_option (make_tycontext_g coreVprog CoreG) ! i
           (make_tycontext_g Vprog G) ! i.
Proof. intros. rewrite 2 semax_prog.make_context_g_char by LNR_tac.
rewrite 2 make_tycontext_s_find_id.
red. remember (find_id i CoreG). destruct o; symmetry in Heqo.
+ assert (Hi:=find_id_In_map_fst _ _ _ Heqo).
  cbv in Hi.
  repeat (destruct Hi as [X | Hi]; [ subst i; simpl in Heqo; inv Heqo; reflexivity |]).
  contradiction.
+ remember (find_id i coreVprog) as q; destruct q; symmetry in Heqq; trivial.
  assert (Hi:=find_id_In_map_fst _ _ _ Heqq).
  cbv in Hi.
  repeat (destruct Hi as [X | Hi]; [ subst i; simpl in Heqo; inv Heqq; reflexivity |]).
  contradiction.
Qed.

Lemma subG2: forall i : ident, subsumespec (find_id i CoreG) (find_id i G).
Proof. intros. red. remember (find_id i CoreG). destruct o; symmetry in Heqo; trivial.
assert (Hi:=find_id_In_map_fst _ _ _ Heqo).
cbv in Hi.
repeat (destruct Hi as [X | Hi]; 
  [ subst i; simpl in Heqo; inv Heqo;
    eexists; split; [ reflexivity | apply funspec_sub_si_refl]
  | ]). (*9.6s*)
contradiction.
Qed.

  Definition Gprog := ltac:
  (let x := eval hnf in G in
   let x := eval simpl in x in 
   (*let x := eval compute in x in *)
       exact x).

Lemma subGprog1: forall i : positive,
sub_option (make_tycontext_g coreVprog CoreG) ! i
  (make_tycontext_g Vprog Gprog) ! i.
Proof. intros. rewrite 2 semax_prog.make_context_g_char by LNR_tac.
rewrite 2 make_tycontext_s_find_id.
red. remember (find_id i CoreG). destruct o; symmetry in Heqo.
+ assert (Hi:=find_id_In_map_fst _ _ _ Heqo).
  cbv in Hi.
  repeat (destruct Hi as [X | Hi]; [ subst i; simpl in Heqo; inv Heqo; reflexivity |]).
  contradiction.
+ remember (find_id i coreVprog) as q; destruct q; symmetry in Heqq; trivial.
  assert (Hi:=find_id_In_map_fst _ _ _ Heqq).
  cbv in Hi.
  repeat (destruct Hi as [X | Hi]; [ subst i; simpl in Heqo; inv Heqq; reflexivity |]).
  contradiction.
Qed.

Lemma subGprog2: forall i : ident,
subsumespec (find_id i CoreG) (find_id i Gprog).
Proof. intros. red. remember (find_id i CoreG). destruct o; symmetry in Heqo; trivial.
assert (Hi:=find_id_In_map_fst _ _ _ Heqo).
cbv in Hi.
repeat (destruct Hi as [X | Hi]; 
  [ subst i; simpl in Heqo; inv Heqo;
    eexists; split; [ reflexivity | apply funspec_sub_si_refl]
  | ]). (*2.2s*)
contradiction.
Qed.

(*In fact, provable from (much less than) Gprog, but we add Imports here to simplify
  the component construction below*)
Lemma body_main: semax_body Vprog Gprog
  f_main (main_spec linked_prog).
(*i.e.  (_main,
  WITH gv : globals PRE [ ] main_pre linked_prog tt gv
  POST [tint] PROP ( )
              LOCAL (temp ret_temp (Vint (Int.repr 0)))  SEP (TT)).*)
Proof.
start_function.
sep_apply (spec_stdlib.make_mem_mgr M gv).
sep_apply (spec_apile.make_apile APILE gv). (* yields spec_apile.apile APILE gv []; *)
(*sep_apply (make_apile PILE gv). yields apile PILE gv []; *)
generalize (spec_onepile.make_onepile ONEPILE gv).
(*generalize (make_onepile PILE gv).*)

assert (change_composite_env (spec_onepile.OnePileCompSpecs ONEPILE) LinkedCompSpecs).
make_cs_preserve (spec_onepile.OnePileCompSpecs ONEPILE) LinkedCompSpecs.
change_compspecs LinkedCompSpecs.
(*now necessary *)unfold onepile._pile, onepile._the_pile.
intro Hx; sep_apply Hx; clear Hx.
forward_call gv.
{ simpl. cancel. }
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (spec_onepile.onepile ONEPILE gv (Some (spec_triang.decreasing (Z.to_nat i)));
          spec_apile.apile APILE gv (spec_triang.decreasing (Z.to_nat i));
          spec_stdlib.mem_mgr M gv; has_ext tt)).
- 
 entailer!.  simpl; cancel.
-
unfold APILE.
forward_call (i+1, spec_triang.decreasing(Z.to_nat i), gv).
{ simpl; cancel. }
rep_omega.
forward_call (i+1, spec_triang.decreasing(Z.to_nat i), gv).
rep_omega. rewrite decreasing_inc by omega.
entailer!. simpl; cancel. (*unfold APILE. trivial.*)
-
unfold APILE.
forward_call (spec_triang.decreasing (Z.to_nat 10), gv).
{ simpl; cancel. }
compute; split; congruence.
forward_call (spec_triang.decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
omega.
forward.
Qed.

Ltac solve_SF_sub J :=
       specialize (J _ _ (eq_refl _) (eq_refl _)); simpl; simpl in J;
       eapply (@InternalInfo_envs_sub LinkedCompSpecs) in J;
       [ eapply InternalInfo_subsumption; [ | | | apply J]; clear J;
           [ apply subGprog1 | apply subGprog2 | LNR_tac ]
       | apply cspecs_sub_refl 
       | eexists; split; [ LookupID | LookupB ] ].

Lemma SF_ext_vacuous {Espec cs V ge G i ef types tp cc} phi:
      find_id i MainE = Some phi ->
      find_id i verif_stdlib.MM_ASI = None ->
      ef_sig ef = {| sig_args := typlist_of_typelist types;
                     sig_res := opttyp_of_type tp;
                     sig_cc := cc |} ->
      genv_find_func ge i (External ef types tp cc) ->
      @SF Espec cs V ge G i (External ef types tp cc) (vacuous_funspec (External ef types tp cc)).
Proof. intros. repeat split; trivial.
simpl. apply typelist2list_arglist.
right. red. simpl; intros ? HI. inv HI.
intros. apply andp_left1. unfold FF; simpl. apply FF_left.
apply semax_external_FF.
Qed.

     Opaque semaxfunc_ExternalInfo.

Ltac do_SF_ext_vacuous := 
     eapply SF_ext_vacuous;
           [ cbv; reflexivity
           | cbv; reflexivity
           | reflexivity
           | eexists; split; cbv; reflexivity].
Ltac do_extinfo_envsub J :=
     eapply ExternalInfo_envs_sub;
          [ apply (J _ _ (eq_refl _) (eq_refl _))
          |  eexists; split; cbv; reflexivity].
Ltac do_internal_lookups J :=
          specialize (J _ _ (eq_refl _) (eq_refl _)); simpl; simpl in J;
          eapply (@InternalInfo_envs_sub LinkedCompSpecs) in J;
          [ eapply InternalInfo_subsumption; [ | | | apply J]; clear J;
              [ apply subGprog1 | apply subGprog2 | LNR_tac ]
          | apply cspecs_sub_refl 
          | eexists; split; [ LookupID | LookupB ] ].
       
  Definition LinkComponent: @Component NullExtension.Espec Vprog _ 
      MainE Imports linked_prog (main_spec linked_prog::nil(*Exports*)) Gprog.
  Proof.
  eapply Build_Component.
   - intros i H; 
     first [ repeat (destruct H; [subst; do 4 eexists; findentry; reflexivity  |]); contradiction
          | (*fail 99 "SC1"*)idtac ].
   - apply compute_list_norepet_e; reflexivity.
   - apply compute_list_norepet_e; reflexivity.
   - apply compute_list_norepet_e; reflexivity.
   - intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; do 4 eexists; reflexivity |]); try contradiction.
   - intros; simpl; split; intros.
     + repeat (destruct H; [ subst; repeat (first [ solve [left; trivial] | right]) |]).
       contradiction.
     + repeat (destruct H; [ subst; repeat (first [ solve [left; trivial] | right]) |]).
       contradiction.
   - apply compute_list_norepet_e; reflexivity.
   - intros i H; first [ solve contradiction | simpl in H];
     repeat (destruct H; [ subst; reflexivity |]); try contradiction.
   - intros i phi fd H H0. replace (Imports ++ Gprog) with Gprog by trivial.
     assert (Hi:=find_id_In_map_fst _ _ _ H0).
     specialize (Comp_G_justified CoreComponent i); intros J.
     cbv in Hi.
     repeat (destruct Hi as [X | Hi];
        [ subst i; simpl in H0; inv H0; simpl in H; inv H;
          first [ do_SF_ext_vacuous | do_extinfo_envsub J | do_internal_lookups J | idtac ]
        | ]).
     (*main; *) solve_SF_internal body_main.
     contradiction.
   - finishComponent.
Qed.
Definition Link_SortedComponent:= SortComponent LinkComponent.

Program Definition CheckSortedComponent {Espec V cs Externs Imports p Exports G} 
           (C:@Component Espec V cs Externs Imports p Exports G)
           (SRT: SortFunspec.sort G = G)(*:
          @SortedComponent Espec V cs Externs Imports p Exports G*) :=
    Build_SortedComponent _ _ _ _ _ _ _ _ C _.
Next Obligation.
intros. rewrite <- SRT. apply SortFunspec.Sorted_sort.
Qed.

Definition Link_SortedComponent1:= CheckSortedComponent LinkComponent (eq_refl _).

Program Definition LinkCanonicalComponent:=
 Build_CanonicalComponent _ _ _ _ _ _ _ _ Link_SortedComponent _.
Next Obligation.
cbv; reflexivity.
Qed.
  
Program Definition LinkCanonicalComponent1:=
 Build_CanonicalComponent _ _ _ _ _ _ _ _ Link_SortedComponent1 _.
Next Obligation.
cbv; reflexivity.
Qed.
(*Print Link_SortedComponent. *)
(*Print Link_SortedComponent1. (avoids double sorting, so lket's use that one in the APPLIC definition*) 


Program Definition PileVSU:@LinkedProgVSU NullExtension.Espec Vprog LinkedCompSpecs
      MainE Imports linked_prog (main_spec linked_prog::nil(*Exports*)).
eexists. split. apply LinkCanonicalComponent1. simpl. eexists; eexists; reflexivity.
Qed.

End MainComponent_with_ExtsInE.