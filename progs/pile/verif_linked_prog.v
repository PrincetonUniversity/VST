Require Import VST.floyd.proofauto.

Require Import spec_stdlib.
Require Import spec_onepile.
Require Import spec_apile.
Require Import spec_triang.
Require Import spec_main.

Require Import verif_pile.
Require Import verif_onepile.
Require Import verif_apile.
Require Import verif_triang.
Require Import verif_main.
(*Require Import VST.floyd.forward. To have access to lower level tactics*)

Lemma semax_func_split n Espec V G cs ge funs specs:
  @semax_func Espec V G cs ge (firstn n funs) (firstn n specs) ->
  @semax_func Espec V G cs ge (skipn n funs) (skipn n specs) ->
  length funs = length specs ->
  @semax_func Espec V G cs ge funs specs.
Proof. intros.  
 rewrite <- (firstn_skipn n funs).
 rewrite <- (firstn_skipn n specs).
 apply semax_func_app. trivial. trivial. rewrite 2 firstn_length, H1; trivial.
Qed.
Lemma semax_func_firstn' n Espec V G cs ge funs specs:
  @semax_func Espec V G cs ge funs specs ->
  @semax_func Espec V G cs ge (firstn n funs) (firstn n specs).
Proof. intros. apply semax_func_firstn; trivial. Qed.

Lemma semax_body_subsumption' cs V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (TS: tycontext_sub (nofunc_tycontext V F) (nofunc_tycontext V F'))
      (HV: forall id, sub_option (make_tycontext_g V F) ! id (make_tycontext_g V' F') ! id):
  @semax_body V' F' cs f spec.
Proof.
  intros. eapply semax_body_subsumption. apply SF.
  hnf. destruct TS as [TS1 [TS2 [TS3 [TS4 [TS5 TS6]]]]]. intuition. simpl in *.
  destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id ); trivial. 
Qed.

Lemma temp_types_of_make_tycontext a b c t V G x: temp_types (make_tycontext a b c t V G x) = make_tycontext_t a b.
Proof. reflexivity. Qed.
Lemma glob_types_of_make_tycontext a b c t V G x: glob_types (make_tycontext a b c t V G x) = make_tycontext_g V G.
Proof. reflexivity. Qed.
Lemma glob_specs_of_make_tycontext a b c t V G x: glob_specs (make_tycontext a b c t V G x) = make_tycontext_s G.
Proof. reflexivity. Qed.

Lemma glob_types_of_nofunc_tycontext V G: glob_types (nofunc_tycontext V G) = make_tycontext_g V G.
Proof. reflexivity. Qed.
Lemma glob_specs_of_nofunc_tycontext V G: glob_specs (nofunc_tycontext V G) = make_tycontext_s G.
Proof. reflexivity. Qed.

Lemma func_sub cs (Espec : OracleKind) (ge ge': Genv.t Clight.fundef type)
       (cs': compspecs) (V V' : varspecs) (F F' : funspecs) (funs : list (ident * Clight.fundef)) (G : funspecs):
  @semax_func Espec V F cs ge funs G -> 
  tycontext_sub (nofunc_tycontext V F) (nofunc_tycontext V F') ->
  (forall id : positive, @sub_option type (make_tycontext_g V F) ! id (make_tycontext_g V' F') ! id) ->
  (forall i : ident, sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i)) ->
  (forall b : block, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b)) ->
  cspecs_sub cs cs' ->
  @semax_func Espec V' F' cs' ge' funs G.
Proof.
  intros. eapply semax_func_subsumption; try eassumption.
  eapply (@semax_func_mono Espec cs); try eassumption.
Qed.

   
Existing Instance NullExtension.Espec.
Locate Gprog. (*top one is in verif_main*)
Locate Vprog. (*top one is in spec_main*)
Locate specs. (*top one is in spec_main*)

Definition exportedfuns := verif_main.exported_funs ++
                         verif_pile.exported_funs ++
                         verif_onepile.exported_funs ++
                         verif_apile.exported_funs ++
                         verif_triang.exported_funs.

Definition exportedspecs := verif_main.exported_specs ++(*Gprog ++*)
                          verif_pile.exported_specs ++
                          verif_onepile.exported_specs ++
                          verif_apile.exported_specs ++
                          verif_triang.exported_specs.

Lemma semax_exportmodule: semax_func Vprog Gprog (Genv.globalenv linked_prog) exportedfuns exportedspecs.
Proof.
  semax_func_cons body_main.
  
  apply (semax_func_split 4).
  { simpl. eapply func_sub.
    + apply verif_pile.semax_exportmodule.
    + red; intros. intuition.
      - simpl. destruct ((PTree.empty type) ! id); trivial.
      - rewrite 2 glob_types_of_nofunc_tycontext.
        apply semax_prog.suboption_make_tycontext_s_g. 2: apply compute_list_norepet_e; reflexivity. 2: apply compute_list_norepet_e; reflexivity.
        intros. rewrite 2 initial_world.make_tycontext_s_find_id. simpl. red. simpl.
        if_tac; subst; simpl. reflexivity.  admit.
      - admit. - admit.
    + admit. + admit. + admit. + apply cspecs_sub_refl. }
  
  apply (semax_func_split 3).
  { simpl. eapply (func_sub spec_onepile.CompSpecs). 
    apply verif_onepile.semax_exportmodule.
    admit. admit. admit. admit. admit. }

  apply (semax_func_split 2).
  { simpl. eapply (func_sub spec_apile.CompSpecs). 
    apply verif_apile.semax_exportmodule.
    admit. admit. admit. admit. admit. }

  simpl. eapply (func_sub spec_triang.CompSpecs). 
    apply verif_triang.semax_exportmodule.
    admit. admit. admit. admit. admit.

  simpl. trivial. simpl. trivial. simpl. trivial.
Admitted.

Lemma prog_correct:
  semax_prog linked_prog Vprog linkedspecs.
Proof.
  prove_semax_prog.
  repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB | ]).
  apply (semax_func_split 1). simpl.
  
Lemma prog_correct:
  semax_prog linked_prog Vprog Gprog.
Proof.
  prove_semax_prog.
(*  repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB | ]).*)
simpl.  apply (semax_func_split 5).
  { simpl.
    (*semax_func_cons body_surely_malloc.*)
    (*relevant part of the tactic is:
eapply semax_func_cons;
           [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
           | unfold var_sizes_ok; repeat constructor; try (simpl; rep_omega)
           | reflexivity | LookupID | LookupB | precondition_closed | apply L
           | ]*)
    eapply semax_func_cons. (*leaves 9 goals*)
    + cbv; reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity.
    + unfold var_sizes_ok; repeat constructor; try (simpl; rep_omega).
    + reflexivity.
    + LookupID.
    + LookupB.
    + precondition_closed. admit. (*!!!*) admit. (*!!*)
    + assert (X: forall i, sub_option (make_tycontext_g spec_pile.Vprog verif_pile.Gprog) ! i (make_tycontext_g Vprog Gprog) ! i ).
      admit.
      (*apply L*) eapply semax_body_subsumption'; [ | | apply X].
      - eapply semax_body_subs.
        apply body_surely_malloc. admit. (*fails*)
      - unfold nofunc_tycontext.
        split; intuition.
        * (* rewrite 2 temp_types_of_make_tycontext.*) simpl. destruct ((PTree.empty type) ! id); trivial.
        * rewrite 2 glob_types_of_make_tycontext.  hnf. admit. (*rewrite 2 semax_prog.make_context_g_char.
          remember  (make_tycontext_s verif_pile.Gprog) as s1. simpl in Heqs1.
          simpl. Search make_tycontext_g. temp_types make_tycontext.*)
        * rewrite 2 glob_specs_of_make_tycontext. admit.
        * simpl. apply Annotation_sub_refl.
    +
    +
      }
  + solve [ reflexivity || fail "match_globvars failed" ].
  + (*match goal with
     |- match initial_world.find_id (prog_main ?prog) ?Gprog with _ => _ end =>
     unfold prog at 1; rewrite extract_prog_main;
     ((eexists; reflexivity) || 
        fail "Funspec of _main is not in the proper form")
    end.  fails*) admit.
3:{ 
                  solve_cenvcs_goal. solve_cenvs_goal. solve [solve_cenvcs_goal || fail "comp_specs not equal"].
   (*compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"*)
 |
 | reflexivity || fail "match_globvars failed"
 | match goal with
     |- match initial_world.find_id (prog_main ?prog) ?Gprog with _ => _ end =>
     unfold prog at 1; rewrite extract_prog_main;
     ((eexists; reflexivity) || 
        fail "Funspec of _main is not in the proper form")
    end
 ]; tac.
Qed.