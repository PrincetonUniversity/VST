README
======

This directory includes files accompanying the LICS/CSL'14 submission:

             "To see ourselves as others see us"
    Structured logical simulation relations for blunderless
                   separate compilation

BUILDING
--------

The files in this directory are excerpted from a larger proof development,
the VST, or Princeton Verified Software Toolchain.

To build, and to get a sense of the larger context of the proof development,
please download VST revision 5992, which is linked at

    http://vst.cs.princeton.edu/download

and follow the attached build/installation instructions.  Most of the files
relating to this paper are in directory [vst/sepcomp], with the
exception of [Clight_coop.v], which is located in [vst/veric].


FILES
=====

Section 2:
----------

- mem_lemmas.v
   auxiliary definitions and lemmas used throughout the developent,
   including definitions for mem_forward and lemmas about
   CompCert's memory model

- core_semantics.v
   definition of core_semantics, cooperative core_semantics,
   and lemmas on multistep relations

Section 4:
----------

- StructuredInjections.v
   definition of structured injections and associated constructions/lemmas

- effect_semantics.v
   definition and lemmas about single- and multi-step execution
   decorated with memory effects

- Lemma 1(item one) is lemma [inject_restrict] in file effect_simulations.v

- Lemma 1(item two) is lemma [REACH_inject] in file effect_simulations.v

Section 5:
----------

- effect_simulations.v
   Definition of Structured Logical Simulation Relations (SLSRs).
   The definition of SLSRs is at the very end of the file.
   The notions leakOut/leakIn as used in the paper correspond
   to the definitions [replace_locals/replace_externs] in this file.
   Axiom REACHAX is provable constructively in CompCert's memory
   using the constructions in FiniteMaps.v [finiteness of
   CompCert memories].  The axiom states that whenever a block b
   is reachable from root set B in memory m, there exists a path
   L witnessing this reachability.

- effect_simulations_lemmas.v
   definition of SLSR composition and multistep simulation diagrams

Section 6:
----------

  Section 6.A:
  ------------

  - rg_lemmas.v
     proofs of rely-guarantee propositions 1 and 2 (Section VI.A)

  Section 6.B (SLSR Transitivity):
  --------------------------------

  - effect_simulations_trans.v
     main transitivity proof.  Contains in particular
     Theorem 1 [Theorem eff_sim_trans].

  - effect_corediagram_trans.v
     Transitivity of the core diagram of SLSRs. In addition to
     proving transitivity of the core diagram clause of Figure 6,
     proof of which is illustrated in Figure 7, this file also
     proves transitivity of a simplified core diagram rule that
     omits the effect annotations.

  - effect_interpolants.v
     Statement of the interpolation lemma illustrated in Figure 8
     as a Coq module type.  For the transitivity of the [initCore]
     clause, an interpolation lemma on unstructured injections is
     needed.  The proof of this lemma is given in mem_interpolation_II.v.

  - effect_interpolation_II.v
     construction of interpolating memory and proof of interpolation
     lemma, as stated in effect_interpolants.v

  - effect_interpolation_proofs.v
     formal instantiation, with proofs, of the Coq module type
     given in effect_interpolants.v

Section 7:
----------

  The files associated with this section of the paper are in
  directory ./compcert_adapt, and based on files from CompCert's trunk
  at INRIA.

  - Clight_coop.v, Csharpminor_coop.v, Cminor_coop.v,
  CminorSel_coop.v, RTL_coop.v

      Adaptations of the semantics of CompCert Clight, Csharpminor,
      Cminor, CminorSel, and RTL to our Core Semantics interface

  - Clight_eff.v, Csharpminor_eff.v, Cminor_eff.v,
  CminorSel_eff.v, RTL_eff.v

      Adaptations of the above files to support effect annotations

  - CshmgenproofEFF.v, CminorgenproofEFF.v, SelectionproofEFF.v,
  RTLgenproofEFF.v

      Adaptations of CompCert's simulation proofs to SLSRs. The
      "admit"s in these proofs are related to the following two
      limitations mentioned in the paper:
        a) Lack of support for builtins, largely due to the fact
	that CompCert inlines builtins such as memcpy in order
	to eliminate certain external function calls in compiled
	code.  This violates the principle that external calls
	are preserved by compilation.
        b) 64-bit operations: to support 64-bit operations,
        CompCert introduces further builtins.
      We are in active discussion with Leroy, the creator and
      maintainer of CompCert, about how CompCert might best be adapted
      to solve these two issues.

  - Lemma 2 (preservation of reach-closure under storing) is proved
    in file effect_properties.v [Lemma REACH_Store] so that it can
    be used in the proof of all translation phases

Section 8:
----------

  - extspec.v
     axiomatic specifications of external functions

  - trace_semantics.v
     Definition of memory-instrumented events, extending CompCert's
     event model. Definition of trace semantics for arbitrary
     core semantics.

  - closed_safety.v
     definition of safety for trace semantics

  - open_semantics_preservation.v
     Proof of Theorem 2 (called [trace_refinement] in the file) and
     proof of Corollary 1 (called [corollary])

