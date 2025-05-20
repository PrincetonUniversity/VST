# Catalog of multilevel verified programs
To prove your program correct, prove that the low-level program (such as a C program) correctly implements a functional model, then (separately) prove that the functional model correctly satisfies a high-level specification.

Ideally, many of the following requirements should be satisfied.  Henceforth we will refer to the low-level program as a "C program" but the concept generalizes to Rust, Java, etc.
- **Multilevel:**  The C program must not only be proved to implement a functional model, the functional model must be proved to actually do the desired thing.
Or at least, *High-level:** a high-level correctness property is proved about the C program, without an intermediate functional-model layer.
- **Unified:**  The C-program proof and high-level proof should be done in the same logical framework so that they can be composed into a single, machine-checkable, end-to-end theorem.
- **Composable:** Even if they are not in the same logical framework, the _specification_ of the C-program proof should be able to mention operators from the functional model (function names and other abstractions) so that the low-level and high-level theorems can be composed "on paper".
- **Low-expressive:** The proof system for C-program proofs should be expressive enough to verify "dusty deck" programs that do all-too-clever things with data representations.
- **High-expressive:** The proof system for high-level proofs should be expressive enough to verify high-level specifications with entirely nontrivial application-specific mathematics.
- **Modular or Semimodular:**  The verification should be in a style of "modular verification of modular programs with data abstraction".  In VST (for example) the verification
should be in the form of a [Verified Software Unit (VSU)](https://softwarefoundations.cis.upenn.edu/vc-current/VSU_intro.html).
If not *modular,* then at least,
*semimodular,* meaning that each function is verified w.r.t. its
own function-spec, and the verification of the caller depends only
on the *specification* of the callee, and not on its function-body.
- **Open-source:** The C program and its proofs (low-level and high-level) should be open-source so that people can examine and compare them.
- **Documented:** The verification should be (if possible) documented in a paper so people can understand what it's about.
- **32/64-bit:**  The C program and its proofs are portable to C implementations
with 32-bit pointers or 64-bit pointers.  But not all C programs are portable
in that way, and even where the program is portable, the proof might not be.
Programs/proofs that are not portable are marked here as 32-bit or 64-bit.

Here we provide a catalog of such verifications.  So far, all of these are done with the Verified Software Toolchain, but we welcome examples done with other verifiers
(contribute to this list by pull request).

**If you use a different C program verifier**, these examples provide C program test cases along with specifications and invariants that you may find useful.

### General framework

For each benchmark, we give a brief summary, followed by URLs for,

Where to find it:
- The paper: either a published paper or unpublished documentation explaining the main point.
- C program: link to a .c program in an open-source repository (see the rest of the repo for context).
- Functional model: usually in the form of a functional program in Coq (Gallina), but could in principle be an inductive relation or some other mathematical structure.
- Low-level spec:  Separation logic (or other program logic) specification of how the
variables and data structures of the C program encode the values of the functional model.
- Low-level proof:  Proof in the program logic that the C program correctly implements the functional model.
- High-level spec: Proposition in Coq giving the claimed high-level property of the functional model.
- High-level proof: Proof in Coq that the functional model satisfies the high-level specification.

-----------------------------------------------------

### SHA-256
- Yes:  Low-expressive, Open-source, Documented, 32-bit
- Not: Multilevel or High-level, hence not Unified or High-Expressive

Secure Hash Algorithm from an early release of OpenSSL.
We include this here because it is an important component of HMAC and HMAC-DRBG.
Even though nobody knows how to do the high-level proof (whether in a proof assistant or in just "mathematics") that SHA-256 is collision-resistant, everybody assumes that's true, and based on that assumption one can do high-level proofs (in math or in Coq) of the properties of HMAC and HMAC-DRBG; see below.

*Warning: These proofs are very old (dating originally from 2013), and
therefore clumsy and cumbersome, because they often do not take
advantage of more modern VST-Floyd proof automation.*

Where to find it:
- The paper: [Second Edition: Verification of a Cryptographic Primitive: SHA-256](https://www.cs.princeton.edu/~appel/papers/verif-sha-2.pdf). This is a very minor revision of Verification of a Cryptographic Primitive: SHA-256, by Andrew W. Appel, *ACM Transactions on Programming Languages and Systems* 37(2) 7:1-7:31, April 2015.
- [C program: sha.c](https://github.com/PrincetonUniversity/VST/blob/master/sha/sha.c)
- [Functional model: SHA256.v](https://github.com/PrincetonUniversity/VST/blob/master/sha/SHA256.v)
- [Low-level spec: spec_sha.v](https://github.com/PrincetonUniversity/VST/blob/master/sha/spec_sha.v)
- [Low-level proof: verif_SHA256.v](https://github.com/PrincetonUniversity/VST/blob/master/sha/verif_SHA256.v)
- High-level spec: N/A
- High-level proof: N/A

### HMAC
- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 32-bit

Hash-based Message Authentication Code, a keyed cryptographic hash function, from OpenSSL.

**Theorem.** The assembly-language program, resulting
from compiling OpenSSL 0.9.1c using CompCert, correctly implements the FIPS standards for HMAC and
SHA, and implements a cryptographically secure PRF (pseudorandom function)
subject to the usual assumptions about SHA.

*Warning: These proofs are very old (dating originally from 2014), and
therefore clumsy and cumbersome, because they often do not take
advantage of more modern VST-Floyd proof automation.*

Where to find it:
- The paper: [Verified Correctness and Security of OpenSSL HMAC](https://www.cs.princeton.edu/~appel/papers/verified-hmac.pdf), by Lennart Beringer, Adam Petcher, Katherine Q. Ye, and Andrew W. Appel. *24th USENIX Security Symposium,* pages 207-221, August 2015.
- [C program: hmac.c](https://github.com/PrincetonUniversity/VST/blob/master/sha/hmac.c)
- [Functional model: HMAC_functional_prog.v](https://github.com/PrincetonUniversity/VST/blob/master/sha/HMAC_functional_prog.v)
- [Low-level spec: spec_hmac.v](https://github.com/PrincetonUniversity/VST/blob/master/sha/spec_hmac.v)
- [Low-level proof: verif_hmac_simple.v](https://github.com/PrincetonUniversity/VST/blob/master/sha/verif_hmac_simple.v)
- [High-level spec: in HMAC_PRF.v](https://github.com/PrincetonUniversity/VST/blob/master/hmacfcf/HMAC_PRF.v)
- [High-level proof: HMAC_PRF.v](https://github.com/PrincetonUniversity/VST/blob/master/hmacfcf/HMAC_PRF.v)

### HMAC-DRBG
- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 32-bit

Widely used cryptographic random number generator standardized by NIST and implemented in mbedTLS open-source library: takes a small sequence of truly random bits and expands to a much longer sequence of hard-to-predict bits.

*Warning: These proofs are very old (dating originally from 2016),
done by a novice VST user, 
 and are therefore clumsy and cumbersome, because they often do not take
advantage of more modern VST-Floyd proof automation.*

**Theorem.**
1.  Verson 2.1.1 of the mbedTLS
HMAC-DRBG correctly implements the NIST 800-90A standard, and
2. HMAC-DRBG Generate and Update as described in that same NIST
800-90A standard *indeed produces pseudorandom output,* subject to
the standard assumptions about SHA-2, as well as certain assumptions about the adversary and the HMAC-DRBG instantiation that
we state formally and explicitly.
3. An adversary with a thousand million terabytes (< 2^78 bits), 
and a million 1-gigahertz processors running for a year (< 2^78 cycles) has a 
0.5+2^(−52) chance of predicting the next bit.

Where to find it:
- The paper: [Verified Correctness and Security of mbedTLS HMAC-DRBG](https://www.cs.princeton.edu/~appel/papers/verified-hmac-drbg.pdf)
by Katherine Q. Ye, Matthew Green, Naphat Sanguansin, Lennart Beringer, Adam Petcher, and Andrew W. Appel. *CCS'17: ACM Conference on Computer and Communications Security,* October 2017.
- [C program: hmac_drbg.c](https://github.com/PrincetonUniversity/VST/blob/master/hmacdrbg/hmac_drbg.c)
- [Functional model: HMAC_DRBG_algorithms.v](https://github.com/PrincetonUniversity/VST/blob/master/hmacdrbg/HMAC_DRBG_algorithms.v)
- [Low-level spec](https://github.com/PrincetonUniversity/VST/blob/master/hmacdrbg/spec_hmac_drbg.v)
- [Low-level proof: verif_hmac_drbg_update.v](https://github.com/PrincetonUniversity/VST/blob/master/hmacdrbg/verif_hmac_drbg_update.v) and also other files in the same directory of the form `verif_hmac_drbg_*.v`
- [High-level spec: HMAC_DRBG_nonadaptive_result.v](https://github.com/PrincetonUniversity/VST/blob/catalog/hmacdrbg/HMAC_DRBG_nonadaptive_result.v)  (should update link to master after merge)
- [High-level proof: HMAC_DRBG_nonadaptive_result.v](https://github.com/PrincetonUniversity/VST/blob/catalog/hmacdrbg/HMAC_DRBG_nonadaptive_result.v)  (should update link to master after merge)

### Forward Erasure Correction
- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 64-bit

Reconstruct missing network packets (or RAID disks) by using Reed-Solomon coding expressed in the form of linear algebra.  A 1990s algorithm implemented in a 1997 C program.

Where to find it:
- The paper: [Verified Erasure Correction in Coq with MathComp and VST](https://www.cs.princeton.edu/~appel/papers/FECVerification.pdf), by Joshua M. Cohen, Qinshi Wang, and Andrew W. Appel, in *CAV'22: 34th International Conference on Computer Aided Verification,* August 2022.
- The second paper: [Specifying and Verifying a Real-World Packet Error-Correction System](https://doi.org/10.1007/978-3-031-66064-1_4) [(author's copy)](https://www.cs.princeton.edu/~appel/papers/SpecPaper.pdf), by Joshua M. Cohen and Andrew W. Appel, in VSTTE'23, 15th International Conference on Verified Software: Theories, Tools, and Experiments, October 23, 2023. Springer LNCS vol 14095, July 2024.
- [C program for first paper: fec.c](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/src/fecActuator/fec.c)
- [C program for second paper: fecActuator/*.c](https://github.com/verified-network-toolchain/Verified-FEC/tree/end-to-end/src/modified/mini_prod3/fecActuator)
- [Functional model 1: ReedSolomonList.v](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/proofs/RS/ReedSolomonList.v)
- [Low-level spec 1: Specs.v](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/proofs/VST/Specs.v)
- [Low-level proof 1: Verif_encode.v](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/proofs/VST/Verif_encode.v) and other `Verif_*.v` in the same directory.
- [High-level spec 1: in ReedSolomon.v](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/proofs/RS/ReedSolomon.v)
- [High-level proof1 : ReedSolomon.v](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/proofs/RS/ReedSolomon.v)
- See the [README](https://github.com/verified-network-toolchain/Verified-FEC/blob/master/README.md) for more information

### Quicksort
- Yes:  Low-expressive, Open-source, Documented, High-level, Unified, High-Expressive, 64-bit

These are three different versions of quicksort, of increasing generality and modularity, 
from [Freek Wiedijk's benchmark suite](https://github.com/cverified/cbench).
A single-layer proof directly proves that the C program sorts correctly, there is no functional model in between.


- The paper: [A benchmark for C program verification](https://arxiv.org/abs/1904.01009), by Eekelen and 8 others and Wiedijk.
- C programs: [qsort1.c](https://github.com/cverified/cbench-vst/blob/master/qsort/qsort1.c),
[qsort3.c](https://github.com/cverified/cbench-vst/blob/master/qsort/qsort3.c),
[qsort4.c](https://github.com/cverified/cbench-vst/blob/master/qsort/qsort4.c)
- Functional models: N/A
- Low+High-level spec: [qsort1](https://github.com/cverified/cbench-vst/blob/master/qsort/verif_qsort1.v),
[qsort3](https://github.com/cverified/cbench-vst/blob/master/qsort/spec_qsort3.v),
[qsort4](https://github.com/cverified/cbench-vst/blob/master/qsort/spec_qsort4.v)
- Low+High-level proof:
[qsort1](https://github.com/cverified/cbench-vst/blob/master/qsort/verif_qsort1.v),
[qsort3](https://github.com/cverified/cbench-vst/blob/master/qsort/verif_qsort3.v),
[qsort4](https://github.com/cverified/cbench-vst/blob/master/qsort/verif_qsort4.v)

### Newton's method square root

- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 64-bit

Compute floating-point square roots using Newton's method, with a proof of termination and accuracy.

The C program is from [Freek Wiedijk's benchmark suite](https://github.com/cverified/cbench).

- The paper: [C-language floating-point proofs layered with VST and Flocq](https://doi.org/10.6092/issn.1972-5787/11442), by Andrew W. Appel and Yves Bertot, Journal of Formalized Reasoning 13(1), December 2020.
- [C program: sqrt1.c](https://github.com/cverified/cbench-vst/blob/master/sqrt/sqrt1.c)
- [Functional model: sqrt1_f.v](https://github.com/cverified/cbench-vst/blob/master/sqrt/sqrt1_f.v)
- [Low-level spec: verif_sqrt1.v](https://github.com/cverified/cbench-vst/blob/master/sqrt/verif_sqrt1.v)
- [Low-level proof: verif_sqrt1.v](https://github.com/cverified/cbench-vst/blob/master/sqrt/verif_sqrt1.v)
- [High-level spec: sqrt1_f_correct.v](https://github.com/cverified/cbench-vst/blob/master/sqrt/sqrt1_f_correct.v)
- [High-level proof: sqrt1_f_correct.v](https://github.com/cverified/cbench-vst/blob/master/sqrt/sqrt1_f_correct.v)

### Ordinary Differential Equation by Leapfrog integration
- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 64-bit

Numerical-method Stoermer-Verlet integration of the differential equation for a harmonic oscillator, proved to produce a correct solution within a specified accuracy bound, including both discretization error and floating-point round-off error.

- The paper: [Verified Numerical Methods for Ordinary Differential Equations](https://www.cs.princeton.edu/~appel/papers/VerifiedODE.pdf), by Ariel E. Kellison and Andrew W. Appel, in *NSV'22: 15th International Workshop on Numerical Software Verification,* August 2022.
- [C program: lfharm.c](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/leapfrog_project/lfharm.c)
- [Functional model: float_model.v](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/leapfrog_project/float_model.v)
- [Low-level spec: verif_lfharm.v](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/leapfrog_project/verif_lfharm.v)
- [Low-level proof: verif_lfharm.v](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/leapfrog_project/verif_lfharm.v)
- [High-level spec: total_error.v](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/leapfrog_project/total_error.v)
- [High-level proof: total_error.v](https://github.com/VeriNum/VerifiedLeapfrog/blob/main/leapfrog_project/total_error.v)

### Jacobi iteration for solution of sparse linear systems
- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 64-bit

Numerical-method Jacobi iteration to solve a sparse linear system Ax=b, proved to converge within a bounded number of iterations to an accurate result in floating point, provided that the matrix A satisfies certain (testable) conditions.

- The paper: [Verified correctness, accuracy, and convergence of a stationary iterative linear solver: Jacobi method](https://www.cs.princeton.edu/~appel/papers/jacobi.pdf), by Mohit Tekriwal, Andrew W. Appel, Ariel E. Kellison, David Bindel, and Jean-Baptiste Jeannin, In *16th Conference on Intelligent Computer Mathematics*, pp. 206-221, September 2023.
- [C program: *.c](https://github.com/VeriNum/iterative_methods/tree/main/sparse)
- [Functional model: jacob_list_fun_model.v](https://github.com/VeriNum/iterative_methods/blob/main/jacob_list_fun_model.v)
- Low-level spec, High-level spec, proofs, etc.:  See the [README](https://github.com/VeriNum/iterative_methods/blob/main/README.md) for an explanation of which files are which.

### Binary Search Trees

- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, 32/64-bit

- The papers:
  - [Proof pearl: Magic wand as frame](https://www.cs.princeton.edu/~appel/papers/wand-frame.pdf), by Qinxiang Cao, Shengyi Wang, Aquinas Hobor, and Andrew W. Appel, February 2018.
  - [Binary Search Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html), by Andrew W. Appel, in *Verified Functional Algorithms*, Volume 3 of Software Foundations, softwarefoundations.org, 2017.
- [C program: bst.c](https://github.com/PrincetonUniversity/VST/blob/master/progs64/bst.c)
- [Functional model: verif_bst.v](https://github.com/PrincetonUniversity/VST/blob/master/progs64/verif_bst.v)
- [Low-level spec: verif_bst.v](https://github.com/PrincetonUniversity/VST/blob/master/progs64/verif_bst.v)
- [Low-level proof: verif_bst.v](https://github.com/PrincetonUniversity/VST/blob/master/progs64/verif_bst.v)
- [High-level spec: SearchTree.v](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)
- [High-level proof: SearchTree.v](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)

### Concurrent messaging system

- Yes:  Low-expressive, Open-source, Documented, High-level, Unified, High-Expressive, 32-bit

*Warning: These proofs are moderately old (dating originally from 2015), and
therefore clumsy and cumbersome, because they often do not take
advantage of more modern VST-Floyd proof automation.*

- The paper: [A verified messaging system](https://dl.acm.org/doi/10.1145/3133911), by William Mansky, Andrew W. Appel, and Aleksey Nogin. *Proceedings of the ACM on Programming Languages (PACM/PL)* volume 1, issue OOPSLA, paper 87, 2017.
- [C program: mailbox.c](https://github.com/PrincetonUniversity/VST/blob/master/mailbox/mailbox.c)
- [Low+High-level spec: verif_mailbox_specs.v](https://github.com/PrincetonUniversity/VST/blob/master/mailbox/verif_mailbox_specs.v)
- [Low+High-level proofs: verif_mailbox_all.v](https://github.com/PrincetonUniversity/VST/blob/master/mailbox/verif_mailbox_all.v)

### Generational garbage collector
- Yes:  Low-expressive, Open-source, Documented, High-level, Unified, High-Expressive, 32/64-bit

- The paper: [Certifying Graph-Manipulating C Programs via Localizations within Data Structures](https://dl.acm.org/doi/abs/10.1145/3360597), by Shengyi Wang, Qinxiang Cao, Anshuman Mohan, Aquinas Hobor. *Proceedings of the ACM on Programming Languages* volume 3, issue OOPSLA, October 2019, Article 171, pp 1–30.
- [C program: gc.c](https://github.com/CertiGraph/CertiGraph/blob/live/CertiGC/GC%20Source/gc.c)
- Functional model expressed using the [CertiGraph](https://github.com/CertiGraph/CertiGraph/) abstraction (not as a functional program *per se*)
- [Low+High-level spec: gc_spec.v](https://github.com/CertiGraph/CertiGraph/blob/live/CertiGC/gc_spec.v)
- [Low+High-level proof: gc_correct.v](https://github.com/CertiGraph/CertiGraph/blob/live/CertiGC/gc_correct.v)

### Malloc-free system with size classes
- Yes:  Low-expressive, Open-source, Documented, High-level, Unified, High-Expressive, Modular, 32-bit

A size-class-array implementation of the C malloc/free library.

- The paper: [Verified sequential malloc/free](https://www.cs.princeton.edu/~appel/papers/memmgr.pdf), by Andrew W. Appel and David A. Naumann, in *2020 ACM SIGPLAN International Symposium on Memory Management,* June 2020.
- [C program: malloc.c](https://github.com/PrincetonUniversity/VST/blob/master/progs/memmgr/malloc.c)
- [Low+High-level spec: ASI_malloc.v](https://github.com/PrincetonUniversity/VST/blob/master/progs/memmgr/ASI_malloc.v)
- [Low+High-level proof: VSU_malloc.v](https://github.com/PrincetonUniversity/VST/blob/master/progs/memmgr/VSU_malloc.v)

### Abstract and concrete data types
- Yes:  Low-expressive, Open-source, Documented, Multilevel, Unified, High-Expressive, Modular, 32-bit

The "pile" program that is the running example in the
Abstraction and Subsumption paper, but
verified in the style of Verified Software Units.

- The papers: [Abstraction and Subsumption in Modular Verification of C Programs](https://www.cs.princeton.edu/~appel/papers/abstraction-subsumption-full.pdf), by A. W. Appel and L. Beringer; 
[Verified Software Units](https://link.springer.com/content/pdf/10.1007/978-3-030-72019-3_5.pdf), by Lennart Beringer, in *ESOP 2021: European Symposium on Programming*, LNCS 12648.
- [C program](https://github.com/PrincetonUniversity/VST/tree/master/progs/VSUpile): pile.c, onepile.c, apile.c, stdlib.c, triang.c, main.c.
- [Low-level spec, High-level spec](https://github.com/PrincetonUniversity/VST/tree/master/progs/VSUpile):  In a VSU-style verification,
 these are done on a per-module basis.  These specs are all in
 the same directory;  the paper explains the structure of specification
 and proof.

### Many small program examples

- Yes: Low-expressive, Open-source, Semimodular, 32-bit or 32/64-bit
- No: not documented or very well organized.

These are small C programs of just one or two functions each,
that serve as primitive test cases for VST verifications.

*Warning: Some of these proofs are very old (from 2013), and
therefore clumsy and cumbersome, because they often do not take
advantage of more modern VST-Floyd proof automation.*

- [32/64-bit portable C programs](https://github.com/PrincetonUniversity/VST/tree/master/progs64): reverse.c revarray.c sumarray.c append.c bin_search.c 
    bst.c field_loadstore.c float.c object.c global.c min.c min64.c nest2.c
    nest3.c logical_compare.c strlib.c switch.c union.c message.c incr.c
- [32-bit-only C programs](https://github.com/PrincetonUniversity/VST/tree/master/progs) incr.c io.c io_mem.c printf.c ptr_cmp.c queue.c
- [Specifications and verifications](https://github.com/PrincetonUniversity/VST/tree/master/progs): in the various `verif_*.v` files in these directories.
