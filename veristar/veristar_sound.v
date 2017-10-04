Load loadpath.
Require Import veristar.compare.

(** Soundness proof of the SL theorem prover. Imports are organized
    into groups below, defining the main components of the system. *)

(** 1- Coq stdlibs *)

Require Import ZArith Coq.Lists.List Permutation Classical.

(** 2- msl axioms and basic SL predicates *)

Require Import VST.msl.Axioms VST.msl.predicates_sa VST.veric.Coqlib2.

(** 3- defns. of datatypes and clauses *)

Require Import veristar.datatypes veristar.clauses.

(** 4- implementations of superposition and heap systems. *)

Require Import veristar.heapresolve veristar.veristar.
(*begin hide*)
(* To build the soundness proof for the model-based saturation system, replace
    the following line with

       Require Import veristar.superpose_modelsat. *)
(*Require Import veristar.superpose.*)
(*end hide*)
Require Import veristar.superpose_modelsat.

(** 5- a model of generic SLs *)

Require Import veristar.model_type veristar.model.

(** 6- soundness proof of (4) wrt. model defined in (5) is split into the
    following major components:

     -clausify_sound:   soundness of clausal embedding of entailments
     -superpose_sound:  soundness of the superposition system for proof
                        search in the pure fragment
     -norm_sound:       soundness of normalization rules N1-N4
     -wellformed_sound: soundness of wellformedness rules W1-W5
     -unfold_sound:     soundness of unfolding rules U1-U5 and spatial
                        resolution (rule SR) *)

Require Import veristar.clausify_sound veristar.norm_sound
               veristar.wellformed_sound veristar.unfold_sound.
(*begin hide*)
(* To build the soundness proof for the model-based saturation system, replace
   the following line with

       Require Import veristar.superpose_modelsat_sound. *)
(*end hide*)
Require Import veristar.superpose_modelsat_sound.

(** 7- misc. lemmas

   lemma library for reasoning about denotations folded over sequences;
   misc. lemmas about clauses *)

Require Import veristar.list_denote veristar.clause_lemmas.

(** Signature of soundness proof *)

Module Type VERISTAR_SOUND.
Declare Module VSM : VERISTAR_MODEL.
Import VSM.

Axiom check_entailment_sound: forall (e: entailment),
  VeriStar.check_entailment e = VeriStar.Valid -> entailment_denote e.

End VERISTAR_SOUND.

Module VeriStarSound (VSM: VERISTAR_MODEL) : VERISTAR_SOUND
  with Module VSM := VSM.

Module VSM := VSM.  Import VSM. Import VeriStarLogic.
Module CS  := Clausify_Sound VSM. Import CS.
Module SPS := SP_Sound VSM.       Import SPS.
Module NS  := Norm_Sound VSM.     Import NS.
Module WFS := WF_Sound VSM.       Import WFS.
Module UFS := UF_Sound VSM.       Import UFS.
Module CL  := CL_Sound VSM.       Import CL.

(* import theorem prover *)

Import HeapResolve.
Import VeriStar.

(* begin hide *)
(* redundancy elimination --- should go elsewhere *)
Lemma relim1_sound c s st :
  clause_denote c st -> setd clause_denote inter TT s st ->
  setd clause_denote inter TT (relim1 c s) st.
Proof. intros; apply setd_filter_pred; auto. Qed.

Lemma incorp_sound s t st :
  setd clause_denote inter TT s st -> setd clause_denote inter TT t st ->
  setd clause_denote inter TT (incorp s t) st.
Proof.
intros; apply setd_un; auto. apply setd_fold; auto.
intros. apply relim1_sound; auto.
Qed.
(* end hide *)
(* proof of soundness of the main loop *)
Local Open Scope nat_scope.

Lemma positive_base_case : forall n: positive,
  O = nat_of_P n - 1 -> n=1%positive.
Proof. intros. generalize (lt_O_nat_of_P n); intro.
 assert (nat_of_P n = 1) by omega.
 assert (nat_of_P 1%positive = 1) by reflexivity.
 rewrite <- H2 in H1.
 generalize (nat_of_P_inj n 1 H1); intro; subst n; auto.
Qed.

Local Coercion bool2Prop (b: bool) := b = true.
(*begin hide*)
(* NOTE: obsolete stuff related to proving the invariant the clauses fed into
   unfolding contain no reflexive spatial atoms of the form Lseg x x. *)

(*Lemma pure_nlsegrefl c : is_pure_clause c -> no_refl_Lseg_clause c.
Proof with simpl; auto; try solve[congruence]. destruct c... Qed.*)

(*Lemma drop_reflex_lseg_nlsegreflatms sigma :
  no_refl_Lseg_spaceatom (drop_reflex_lseg sigma).
Proof with simpl; auto; try congruence.
unfold no_refl_Lseg_spaceatom. intros x H1. induction sigma...
simpl in H1. destruct a. inversion H1...
destruct e... destruct e0... inversion H1...
destruct e0. inversion H1... remember (negb (eq_var v v0)) as b.
if_tac in H1... inversion H1... inversion H. inversion H3. subst.
unfold eq_var in Heqb. rewrite fresh.var_compare_refl in Heqb; simpl in Heqb...
Qed.
*)
(*Local Hint Resolve drop_reflex_lseg_nlsegreflatms.*)

(*Lemma norm_nlsegrefl sel nc : no_refl_Lseg_clause (norm sel nc).
Proof with simpl; auto; try congruence.
destruct nc as [gamma delta|gamma delta sigma|gamma sigma delta].
apply pure_nlsegrefl; apply norm_pure_pure...
unfold norm. unfold normalize2_4. remember
  (fold_right normalize1_3 (PosSpaceClause gamma delta sigma)
         (rsort_uniq (rev_cmp compare_clause) (M.elements sel))) as c.
destruct c...
unfold norm. unfold normalize2_4. remember
 (fold_right normalize1_3 (NegSpaceClause gamma sigma delta)
         (rsort_uniq (rev_cmp compare_clause) (M.elements sel))) as c.
destruct c...
Qed.
*)
(*end hide*)

Lemma loop_sound n sigma nc s cl st :
  clause_denote nc st -> space_denote sigma st ->
  setd clause_denote inter TT s st -> the_loop n sigma nc s cl = Valid ->
  clause_denote empty_clause st.
Proof with simpl in *; auto; try solve[congruence].
remember (nat_of_P n - 1)%nat as nn.
revert n Heqnn sigma nc s cl; induction nn; intros ? ?.
(* base case *)
apply positive_base_case in Heqnn; subst.
intros; rewrite the_loop_equation in H2; rewrite Coqlib.peq_true in H2.
inversion H2.
(* inductive case *)
assert (Hnnx: nn = nat_of_P (Ppred n) - 1).
 rewrite Ppred_minus;
   rewrite nat_of_P_minus_morphism by
    (clear - Heqnn; destruct n; simpl in *; auto; discriminate);
   unfold nat_of_P at 2; simpl; omega.
specialize (IHnn _ Hnnx). clear Hnnx.
intros sigma nc s cl H0 H1 H2; rewrite the_loop_equation.
rewrite if_false by (clear - Heqnn; intro H; subst;  inversion Heqnn).
clear nn Heqnn.
remember (Superposition.check_clauseset s) as S.
  destruct S as [res s']; symmetry in HeqS.
destruct res... destruct p... destruct s0... intros H3 _.
apply (check_clauseset_Valid_sound _ _ _ _ HeqS)...
assert (H3: setd clause_denote inter TT t st).
  apply (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS st)...
remember (M.mem empty_clause t) as E; destruct E as [E|E].
assert (H4: In empty_clause (M.elements t)).
  clear - HeqE H3. symmetry in HeqE.
rewrite M.mem_spec in HeqE. rewrite <- Melements_spec1 in HeqE. auto.
unfold setd in H3; apply listd_In_inv_pred with (a := empty_clause) in H3...
if_tac... if_tac... if_tac... apply IHnn...
 assert (H4: listd clause_denote inter TT
   (rsort_uniq (rev_cmp compare_clause) (M.elements t)) st).
   rewrite (@listd_sort_uniq_inter _ state)...
   intros x y H4; rewrite rev_cmp_eq in H4...
   apply comp_eq in H4; auto.
   apply simplify_sound...
   edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS); eauto.
   apply simplify_atoms_sound...
   edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS); eauto.
 apply setd_un.
   apply setd_filter_pred.
   apply unfolding_sound.
   apply norm_sound. intro; auto.
   apply check_clauseset_Cexample_sound in HeqS.
   specialize (HeqS st H2). destruct HeqS...
   apply simplify_atoms_sound...
   edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS); eauto.
   autounfold with DEBUG_UNFOLD.
   destruct H...
   apply norm_sound...
   apply check_clauseset_Cexample_sound in HeqS.
   specialize (HeqS st H2). destruct HeqS...
   apply simplify_sound...
   edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS)
     as [[H4 H5]]; eauto.
 apply setd_fold.
   intros. apply relim1_sound; auto.
   apply incorp_sound... apply do_wellformed_sound... apply norm_sound...
   apply check_clauseset_Cexample_sound in HeqS.
   specialize (HeqS st H2). destruct HeqS...
   intros; apply simplify_atoms_sound...
   edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS)
     as [[H4 H5]]; eauto.
   apply setd_filter_pred... apply unfolding_sound...
   apply norm_sound...
   apply check_clauseset_Cexample_sound in HeqS.
   specialize (HeqS st H2). destruct HeqS...
   intros; apply simplify_atoms_sound...
   edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS)
     as [[H4 H5]]; eauto.
   apply check_clauseset_Cexample_sound in HeqS.
   specialize (HeqS st H2). destruct HeqS...
   apply norm_sound...
   apply simplify_sound... destruct H...
apply IHnn...
  assert (H4: listd clause_denote inter TT
    (rsort_uniq (rev_cmp compare_clause) (M.elements t)) st).
    rewrite (@listd_sort_uniq_inter _ state)...
    intros x y H4; rewrite rev_cmp_eq in H4...  apply comp_eq in H4; auto.
  apply simplify_sound...
  edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS); eauto.
  apply simplify_atoms_sound...
  edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS); eauto.
  apply setd_un.
  apply do_wellformed_sound... apply norm_sound...
  apply check_clauseset_Cexample_sound in HeqS.
  specialize (HeqS st H2). destruct HeqS...
  intros; apply simplify_atoms_sound...
  edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS)
    as [[H4 H5]]; eauto.
  apply setd_fold... intros; apply relim1_sound...
  apply do_wellformed_sound... apply norm_sound...
  apply check_clauseset_Cexample_sound in HeqS.
  specialize (HeqS st H2). destruct HeqS...
  intros; apply simplify_atoms_sound...
  edestruct (check_clauseset_Cexample_sound _ _ _ _ _ _ HeqS)
    as [[H4 H5]]; eauto.
Qed.

(** VeriStar main soundness theorem:
    veristarulate e = "Valid" ==> entailment semantically valid.*)

Theorem check_entailment_sound: forall (e: entailment),
  VeriStar.check_entailment e = VeriStar.Valid -> entailment_denote e.
Proof with simpl; auto.
intros e H1. rewrite cnf_correct. intros st H2.
destruct e as [[pi sigma] [pi' sigma']].
  unfold check_entailment in H1. simpl in H2.
destruct sigma, sigma'.
(*TODO: streamline case explosion*)
(*nil,nil*)
remember (mk_pureR pi') as PI'; destruct PI' as [pi'plus pi'minus].
destruct (mk_pureR pi).
cut (clause_denote empty_clause st). simpl; intros H3. spec H3...
apply loop_sound with (st:=st) in H1; auto.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... intros H5. simpl in H3, H4.
apply H4. clear -H5. induction pi'plus...
solve[destruct H5; split; auto].
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl in H3...
unfold pure_clauses.
apply clause_setd_listd.
 apply listd_filter_pred.
apply listd_map_pred with (f := fun c => clause_denote c)...
intros a; rewrite order_eqv_clause_sound...
remember (mk_pureR pi') as b; destruct b... inversion HeqPI'; subst.
rewrite listd_app, (@listd_unfold_inter _ state); split.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl; split... split...
(*nil,cons*)
remember (s :: sigma') as sigma'0.
remember (mk_pureR pi') as PI'; destruct PI' as [pi'plus pi'minus].
destruct (mk_pureR pi).
cut (clause_denote empty_clause st). simpl; intros H3. spec H3...
apply loop_sound with (st:=st) in H1; auto.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl in H3...
unfold pure_clauses.
apply clause_setd_listd.
 apply listd_filter_pred.
apply listd_map_pred with (f := fun c => clause_denote c)...
intros a; rewrite order_eqv_clause_sound...
remember (mk_pureR pi') as b; destruct b... inversion HeqPI'; subst.
rewrite listd_app, (@listd_unfold_inter _ state); split.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl; split... split...
(*cons,nil*)
remember (s :: sigma) as sigma0.
remember (mk_pureR pi') as PI'; destruct PI' as [pi'plus pi'minus].
destruct (mk_pureR pi).
cut (clause_denote empty_clause st). simpl; intros H3. spec H3...
apply loop_sound with (st:=st) in H1; auto.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl in H3...
unfold pure_clauses.
apply clause_setd_listd.
 apply listd_filter_pred.
apply listd_map_pred with (f := fun c => clause_denote c)...
intros a; rewrite order_eqv_clause_sound...
remember (mk_pureR pi') as b; destruct b... inversion HeqPI'; subst.
rewrite listd_app, (@listd_unfold_inter _ state); split.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl; split... split...
(*cons,cons*)
remember (mk_pureR pi') as PI'; destruct PI' as [pi'plus pi'minus].
destruct (mk_pureR pi).
cut (clause_denote empty_clause st). simpl; intros H3. spec H3...
apply loop_sound with (st:=st) in H1; auto.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl in H3...
unfold pure_clauses.
apply clause_setd_listd.
 apply listd_filter_pred.
apply listd_map_pred with (f := fun c => clause_denote c)...
intros a; rewrite order_eqv_clause_sound...
remember (mk_pureR pi') as b; destruct b... inversion HeqPI'; subst.
rewrite listd_app, (@listd_unfold_inter _ state); split.
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]...
rewrite listd_app, (@listd_unfold_inter _ state) in H2.
destruct H2 as [H2 [H3 [H4 _]]]... simpl; split... split...
Qed.

End VeriStarSound.


