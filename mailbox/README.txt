The extension of VST with SC and RA atomics consists of:
general_atomics.v - invariants, SC atomics, and logical atomicity (Section 4.2 of the POPL submission)
acq_rel_atomics.v, acq_rel_SW.v - axiomatic specifications of release-acquire atomics (Section 4.3)
gen_atomics.h, gen_atomics.h - C interface for our atomics
The following files for each concurrent data structure <D> in {kvnode_atomic (6.2.1), hashtable_atomic (6.2.2), kvnode_atomic_ra (6.3.1), hashtable_atomic_ra (6.3.2)}:
<D>.c - C code for the data structure
<D>.v - Coq representation of the C code generated via CompCert clightgen
verif_<D>.v - specifications and proofs of correctness for the data structure
