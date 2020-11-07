Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.VSU_addmain.
Require Import verif_fastmain.

Lemma prog_correct:
  exists G, 
 @semax_prog NullExtension.Espec LinkedCompSpecs linked_prog tt Vprog G.
Proof.
  destruct PILE_VSU as [G [Comp MAIN]]. exists G. 
  assert (DomG: map fst G = map fst (prog_funct linked_prog)).
  { destruct Comp. unfold Comp_G in *. rewrite CC_canonical.
    cbv; reflexivity. }
  prove_linked_semax_prog.
  all: rewrite augment_funspecs_eq by trivial.
  apply (@Canonical_semax_func _ _ _ _ _ _ _ Comp); cbv; reflexivity.
  destruct MAIN as [post [MainG MainExp]]. inv MainExp. rewrite MainG; eexists; reflexivity.
Qed.