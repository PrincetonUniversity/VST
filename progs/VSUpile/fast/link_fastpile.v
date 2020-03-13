Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.veric.initial_world.
Require Import verif_fastmain.
Import main.

Notation LinkCanonicalComponent1 := MainComponent_with_ExtsInE.LinkCanonicalComponent1.
Notation Gprog:= MainComponent_with_ExtsInE.Gprog.
Notation Vprog:= MainComponent_with_ExtsInE.Vprog.
Notation Imports:= MainComponent_with_ExtsInE.Imports.
Notation G:= MainComponent_with_ExtsInE.G.

(*Succeeds as imports are now empty*)
Definition APPLIC:= @Canonical_semaxfunc _ _ _ _ _ _ _ LinkCanonicalComponent1.

Definition AGG_pre := augment_funspecs linked_prog Gprog.

  Definition AGG := ltac:
  (let x := eval hnf in AGG_pre in
   let x := eval simpl in x in 
   (*let x := eval compute in x in *)
       exact x).

Lemma AGG_char i: find_id i (augment_funspecs linked_prog Gprog) = find_id i AGG.
Proof.
remember (find_id i AGG) as d; symmetry in Heqd. destruct d.
+ assert (X:= find_id_In_map_fst _ _ _ Heqd). cbv in X.
  repeat (destruct X as [Hi | X]; [ subst i; apply Heqd |]).
  contradiction.
+ remember (find_id i (augment_funspecs linked_prog Gprog)) as e; symmetry in Heqe; destruct e; trivial.
  assert (X:= find_id_In_map_fst _ _ _ Heqe). cbv in X.
  repeat (destruct X as [Hi | X]; [ subst i; inv Heqd |]).
  contradiction.
Qed.
(*
Axiom ExternalInfo_funspec_sub: forall {Espec ge i e ts t c phi}
(SFE: semaxfunc_ExternalInfo Espec ge i e ts t c phi)
(phi' : funspec)
(Fsub : funspec_sub phi phi'),
semaxfunc_ExternalInfo Espec ge i e ts t c phi'.
(*NOT provable currently -- see VSU*)

Lemma semaxfunc_funspec_sub {Espec cs V G ge}: forall funs G1 G2,
@semaxfunc Espec cs V G ge funs G1 ->
Forall2 (fun fs1 fs2 => fst fs1 = fst fs2 /\ funspec_sub (snd fs1) (snd fs2)) G1 G2 ->
@semaxfunc Espec cs V G ge funs G2.
Proof. induction funs; intros; inv H; inv H0. constructor.
+ destruct y as [i psi]. simpl in H2. destruct H2; subst.
  constructor; trivial.
  eapply InternalInfo_funspec_sub; eassumption.
  eauto.
+ destruct y as [i psi]. simpl in H2. destruct H2; subst.
  constructor; trivial.
  eapply ExternalInfo_funspec_sub; eassumption.
  eauto.
Qed.
*)
Lemma prog_correct: 
 @semax_prog NullExtension.Espec LinkedCompSpecs linked_prog tt Vprog Gprog.
Proof.
(*  prove_semax_prog.*)
(*Ltac prove_semax_prog_aux tac :=*)
  (*match goal with
    | |- semax_prog ?prog ?z ?Vprog ?Gprog =>
     let x := constr:(ltac:(old_with_library prog Gprog))
     in change ( SeparationLogicAsLogicSoundness.MainTheorem.CSHL_MinimumLogic.CSHL_Defs.semax_prog
                    prog z Vprog x)
  end.*)
 split3; [ | | split3; [ | | split]];
 [ reflexivity || fail "duplicate identifier in prog_defs"
 | reflexivity || fail "unaligned initializer"
 | solve [solve_cenvcs_goal || fail "comp_specs not equal"]
   (*compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"*)
 |
 | reflexivity || fail "match_globvars failed"
 | (*match goal with
     |- match find_id (prog_main ?prog) ?Gprog with _ => _ end =>
     unfold prog at 1; (rewrite extract_prog_main || rewrite extract_prog_main');
     ((eexists; try (unfold NDmk_funspec'; rewrite_old_main_pre); reflexivity) || 
        fail "Funspec of _main is not in the proper form")
    end*)
 ].
  all: rewrite augment_funspecs_eq by reflexivity.
  2:{ assert (prog_main linked_prog = _main) by reflexivity. rewrite H.
      (*rewrite AGG_char.*)
      simpl. eexists; try (unfold NDmk_funspec'; rewrite_old_main_pre); reflexivity. }
 (*
 match goal with |- semax_func ?V ?G ?g ?D ?G' =>
   let Gprog := fresh "Gprog" in 
   pose (Gprog := @abbreviate _ G); 
  change (semax_func V Gprog g D G')
 end.
 tac.*)
(*finish_semax_prog. *)
specialize APPLIC; intros APP.
(*eapply (semaxfunc_funspec_sub _ _ (augment_funspecs linked_prog Gprog)) in APP.*)
+ apply semaxfunc_sound in APP.
  assert (HG: Comp_G LinkCanonicalComponent1 = Gprog) by reflexivity. unfold Imports in HG.
  rewrite filter_true in APP. 
  - eapply semax_func_subsumption. 3: apply APP.
    * clear APP. rewrite HG; clear HG.
      assert (HH: nofunc_tycontext Vprog Gprog = nofunc_tycontext Vprog G) by trivial.
      rewrite HH; trivial.
      apply tycontext_sub_refl.
    * clear APP. rewrite HG; clear HG.
      assert (HH: make_tycontext_g Vprog Gprog = make_tycontext_g Vprog G) by trivial.
      rewrite HH. intros. apply sub_option_refl.
  - clear APP; intros [i fd] Hi. cbv in Hi.
    repeat ( destruct Hi as [X | Hi]; [ inv X; reflexivity |] ).
    contradiction.
Qed.