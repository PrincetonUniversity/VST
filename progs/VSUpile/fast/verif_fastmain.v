Require Import VST.floyd.proofauto.
Require Import VST.veric.initial_world.
Require Import VST.floyd.VSU.
Require Import VST.floyd.VSU_addmain.

Require Import PileModel.
Require Import verif_fastcore.
Require Import main.
Require Import spec_main.

Notation M := verif_stdlib.M.

Definition linked_prog : Clight.program :=
 ltac: (linking.link_progs_list [
   stdlib.prog; fastpile.prog; onepile.prog; fastapile.prog;
   triang.prog; main.prog]).

Notation mainspec:= (main_spec linked_prog).

Instance LinkedCompSpecs : compspecs. make_compspecs linked_prog. Defined.

Definition Vprog: varspecs. mk_varspecs linked_prog. Defined. 

Lemma body_main: semax_body Vprog (mainspec ::coreExports) f_main mainspec.
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
(*{ simpl. cancel. }*)
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (spec_onepile.onepile ONEPILE gv (Some (decreasing (Z.to_nat i)));
          spec_apile.apile APILE gv (decreasing (Z.to_nat i));
          spec_stdlib.mem_mgr M gv; has_ext tt)).
- 
 entailer!. (*  simpl; cancel.*)
-
unfold APILE.
forward_call (i+1, decreasing(Z.to_nat i), gv).
(*{ simpl; cancel. }*)
rep_omega.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_omega. rewrite decreasing_inc by omega.
entailer!. simpl; cancel. (*unfold APILE. trivial.*)
-
unfold APILE.
forward_call (decreasing (Z.to_nat 10), gv).
(*{ simpl; cancel. }*)
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
omega.
forward.
Qed.

Definition MainE_pre:funspecs :=
   filter (fun x => in_dec ident_eq (fst x) (ExtIDs linked_prog)) (augment_funspecs linked_prog verif_stdlib.MF_ASI).
  (* Holds
  Lemma coreE_in_MainE: forall i phi, find_id i verif_stdlib.MM_E = Some phi -> find_id i MainE_pre = Some phi.
  Proof. intros. specialize (find_id_In_map_fst _ _ _ H); intros.
    simpl in H0. repeat (destruct H0 as [HO | H0]; [ subst i; inv H; reflexivity |]). contradiction.
  Qed. *)

Definition MainE:funspecs := ltac:
    (let x := eval hnf in MainE_pre in
     let x := eval simpl in x in 
(*     let x := eval compute in x in *)
       exact x). (*Takes 30s to compute...*)

Lemma HypME1 : forall i : ident,
         In i (map fst MainE) ->
         exists (ef : external_function) (ts : typelist) (t : type) (cc : calling_convention),
           find_id i (prog_defs linked_prog) = Some (Gfun (External ef ts t cc)) (*/\
           ef_sig ef = {| sig_args := typlist_of_typelist ts;
                          sig_res := opttyp_of_type t;
                          sig_cc := cc_of_fundef (External ef ts t cc) |} /\
           genv_find_func (Genv.globalenv linked_prog) i (External ef ts t cc)*).
  Proof. intros.
    cbv in H. 
    repeat (destruct H as [H | H];
      [ subst; try solve [do 4 eexists; split; reflexivity ]
      | ]).
   (*
    repeat (destruct H as [H | H];
      [ subst; try solve [do 4 eexists; split3; 
                                    [ reflexivity | reflexivity 
                                    | eexists; split; cbv; reflexivity]]
      | ]).*)
    contradiction.
  Qed.

Lemma MainE_vacuous i phi: find_id i MainE = Some phi -> find_id i verif_stdlib.MF_E = None ->
        exists ef argsig retsig cc, 
           phi = vacuous_funspec (External ef argsig retsig cc) /\ 
           find_id i (prog_funct coreprog) = Some (External ef argsig retsig cc) /\
           ef_sig ef = {| sig_args := typlist_of_typelist argsig;
                          sig_res := opttyp_of_type retsig;
                          sig_cc := cc_of_fundef (External ef argsig retsig cc) |}.
  Proof. intros. specialize (find_id_In_map_fst _ _ _ H); intros.
    cbv in H1.
    Time repeat (destruct H1 as [H1 | H1]; 
      [ subst; inv H; try solve [do 4 eexists; split3; reflexivity]
      | ]). (*3s*)
    inv H0. inv H0. inv H0. contradiction.
  Qed.

Lemma disjoint_Vprog_linkedfuncts: list_disjoint (map fst Vprog) (map fst (prog_funct linked_prog)).
Proof.
  intros x y X Y ?; subst x; cbv in X; apply assoclists.find_id_None_iff in Y; [ trivial | clear H Y];
  repeat (destruct X as [X | X]; [ subst y; cbv; reflexivity |]); contradiction.
Qed.

Definition Imports:funspecs:=nil.

Definition PILE_VSU: @LinkedProgVSU NullExtension.Espec Vprog LinkedCompSpecs
      MainE Imports linked_prog [mainspec].
Proof.
 AddMainProgProgVSU_tac CoreVSU.
   + apply disjoint_Vprog_linkedfuncts.
   + apply HypME1. 
   + apply body_main.
   + apply MainE_vacuous.
Qed.