README
======

This directory includes files accompanying the POPL'14 submission:

    Verified Compilation for Shared-Memory C

BUILDING
--------

The files in this directory are excerpted from a larger proof development,
the VST, or Princeton Verified Software Toolchain.  

To build, please download revision XXXX of the VST from the SVN repository
linked at

    http://vst.cs.princeton.edu/download

and follow the attached build/installation instructions.


FILES
-----

Section 3:
----------

- mem_lemmas.v:
   auxiliary definitions and lemmas used throughout the developent,
   including definitions for mem_forward and mem_wd ("closed"), 
   
- core_semantics.v
   definition of core_semantics, cooperative core_semantics,
   and lemmas on multietep relations

Section 4:
----------

- forward_simulations.v
   Definition of the logical simulations on cores, with cases according 
   to the three kinds of memory transformations. Definition 4.1 in the 
   paper corresponds to Module Forward_simulation_inj (starting at line 299).
   Full simulations combining the three cases are given at the end of 
   the file, for coresemantics and coopsemantics. 

- forward_simulations_lemmas.v
  lemmas on the definitions...

- compiler_correctness.v
  lifts the simulations to programs

- compcert_compiler_correctness.v
  relates compiler_correctness.v to CompCert 2.0's memory-oblivious
  whole-program simulations. (admits in this file are on mem_wd etc 
  are ok, since some of our invariants are simply not satisfied in
  CompCert2.0)

Files required for proof of transitivity:

- mem_interpol*.v: files for the interpolation lemmas
   (4 cases: extend-extend (EE), extend-inject (EI),etc).
  All interpolation lemmas are collected together in mem-interpolants.v

- forward_simulations_trans.v
  the proof of transitivity, using the interpolations.
  All admits here are all on global environments, and due to the fact
  that CompCert's definition is not yet adapted to mutiple modules.

- compiler_correctness_trans.v
  lifts transitivity of core forward simulations to programs.

Section 6:
----------

- linking.v: 
    extensional model of core semantics linking

- linking_simulations.v:
    states the linking simulation theorem of Sec. 6

- linking_proof.v:
    proves the linking simulation theorem of Sec. 6

- fs_linking.v:
    develops the file system model described in Sec. 6
    proves the linking simulation theorem of linking_simulations.v
      

