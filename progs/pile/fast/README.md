DEMONSTRATION OF FUNSPEC_SUB AND SUBSUMPTION

  from the paper,

   Abstraction and Subsumption in Modular Verification of C Programs
    by Lennart Beringer and Andrew W. Appel,
    in FM 2019: 3rd World Congress on Formal Methods, October 2019.

see the files in the parent directory, and these files in this directory:

THE FOLLOWING FILES SHOWN IN FIGURE 3 OF THE PAPER
fastpile_private.h
fastpile.c
spec_fastpile.v

THESE FILES COMPLETE THE VERIFICATION OF THE fastpile PROGRAM
verif_fastpile.v (different proof than verif_pile.v, because a different program)
spec_fastapile.v

THE FOLLOWING FILES ARE IDENTICAL TO THEIR NON-fast COUNTERPARTS,
EXCEPT FOR THE NAMES OF CORRESPONDING FILES THAT THEY IMPORT:
spec_fastonepile.v
spec_fasttriang.v
spec_fastmain.v
verif_fastonepile.v
verif_fastapile.v
verif_fasttriang.v
verif_fastmain.v
link_fastpile.v

THE FOLLOWING FILES ARE DISCUSSED IN SECTION 3 OF THE PAPER
spec_fastpile_concrete.v
subsume_fastpile.v
