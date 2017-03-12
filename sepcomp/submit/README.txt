README
======

This directory includes files accompanying the ESOP'14 submission:

    Verified Compilation for Shared-Memory C

BUILDING
--------

The files in this directory are excerpted from a larger proof development,
the VST, or Princeton Verified Software Toolchain.

To build, and to get a sense of the larger context of the proof development,
please download VST revision 5785, which is linked at

    http://vst.cs.princeton.edu/download

and follow the attached build/installation instructions.  Most of the files
relating to this paper are in directory [vst/sepcomp], with the
exception of [Clight_new.v], which is located in [vst/veric].


FILES
-----

Section 3:
----------

- core_semantics.v
   definition of core_semantics, cooperative core_semantics,
   and lemmas on multistep relations

- mem_lemmas.v
   auxiliary definitions and lemmas used throughout the developent,
   including definitions for mem_forward and mem_wd ("closed"),

Section 4:
----------

- forward_simulations.v
   Definition of the logical simulations on cores, with cases according
   to the three kinds of memory transformations. Definition 4.1 in the
   paper corresponds to Module Forward_simulation_inj (starting at line 299).
   Full simulations combining the three cases are given at the end of
   the file, for coresemantics and coopsemantics.

- forward_simulations_lemmas.v
  lemmas on the definitions

- compiler_correctness.v
  lifts the simulations to programs

- compcert_compiler_correctness.v
  relates compiler_correctness.v to CompCert 2.0's memory-oblivious
  whole-program simulations.

Files required for proof of transitivity:
- FiniteMaps.v (auxilary data structure; used in constructing
  interpolating memories)

- mem_interpol*.v: files for the interpolation lemmas
   (4 cases: extend-extend (EE), extend-inject (EI),etc),
  with appropriate constructions of the memories, injections, etc,
  and proofs that they satify the diagrams.
  All interpolation lemmas are collected together in mem-interpolants.v

- forward_simulations_trans.v
  the proof of transitivity, using the interpolations.
  All admits here are all on global environments, and due to the fact
  that CompCert's definition is not yet adapted to mutiple modules.

- compiler_correctness_trans.v
  lifts transitivity of core forward simulations to programs.

Section 5:
----------

- safety_preservation.v
  Safety and semantics preservation, in addition to a restricted
  version of program safety for closed whole programs.  General
  program safety is defined in step_lemmas.v.

Section 6:
----------

- Files from CompCert 2.0 (appropriate license applies here!):
  Switch.v, Ordered.v Cminor.v Csharpminor.v Cminorgen.v Cminorgenproof.v

- CminorgenproofRestructured.v: restructuring of Cminorgenproof.v to
  isolate the cases on the various istructions better.

- Cminor_coop.v, Csharpminor_coop.v
  Cores semantics and cooperative core semantics formulations of the
  two languages

- CminorgenproofSIM.v: the adapted proof of CompCert's Cminorgen phase

Relevant, but not discussed in the paper due to lack of space:
--------------------------------------------------------------

- linking.v:
    extensional model of core semantics linking

- linking_simulations.v:
    states a linking simulation theorem

- linking_proof.v:
    proves the linking simulation theorem of linking_simulation.v

- fs_linking.v:
    develops a model of a simple file system;
    proves the linking simulation theorem of linking_simulations.v
    for the file system model


