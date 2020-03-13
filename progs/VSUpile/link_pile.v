Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.veric.initial_world.
Require Import verif_main.
Import main.

Notation LinkCanonicalComponent1 := MainComponent_with_ExtsInE.LinkCanonicalComponent1.
Notation Gprog:= MainComponent_with_ExtsInE.Gprog.
Notation Vprog:= MainComponent_with_ExtsInE.Vprog.

Definition Exports := [main_spec linked_prog].

(*Succeeds as imports are now empty*)
Definition APPLIC:= @Canonical_semaxfunc _ _ _ _ _ _ _ LinkCanonicalComponent1.
(*Definition is dead, but the reminder Imports empty is important*)

Notation PileMainVSU := MainComponent_with_ExtsInE.PileVSU.

Lemma prog_correct:
  exists G, 
 @semax_prog NullExtension.Espec LinkedCompSpecs linked_prog tt Vprog G(*prog*).
Proof.
  destruct PileMainVSU as [G [Comp MAIN]]. exists G.
  assert (DomG: map fst G = map fst (prog_funct linked_prog)).
  { destruct Comp. unfold Comp_G in *. rewrite CC_canonical.
    cbv; reflexivity. }
(*  specialize (Comp_G_Exports Comp _main _ (eq_refl _)); intros.*)
(*  prove_semax_prog. failes*)
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
  all: rewrite augment_funspecs_eq by trivial.
  2:{ destruct MAIN as [post [ora MAIN]]. rewrite MAIN. exists post. destruct ora. trivial.  }
 (*
 match goal with |- semax_func ?V ?G ?g ?D ?G' =>
   let Gprog := fresh "Gprog" in 
   pose (Gprog := @abbreviate _ G); 
  change (semax_func V Gprog g D G')
 end.
 tac.*)
(*finish_semax_prog. *)
apply (@Canonical_semax_func _ _ _ _ _ _ _ Comp). cbv; reflexivity.
(*OLD PROOF
specialize (@Canonical_semaxfunc _ _ _ _ _ _ _ LinkCanonicalComponent1); intros APP.
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
    contradiction.*)
Qed.
