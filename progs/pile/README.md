DEMONSTRATION OF MODULAR VERIFICATION OF MODULAR PROGRAMS

 * If you just want to learn how module linking works in VST proofs,
   read _only_ section 2 of this paper:

   Abstraction and Subsumption in Modular Verification of C Programs
    by Lennart Beringer and Andrew W. Appel,
    in FM 2019: 3rd World Congress on Formal Methods, October 2019.

   and then look at the files (and Makefile) in this directory.

 * If you want to see how subsumption works, as described
   in the rest of that paper, you'll also want to look in the
   fast/   and  incr/ directories (and their own README files).
  
This directory contains files constituting the verification examples
shown in the above-named paper.

CONTENTS OF THIS DIRECTORY:
linking.v  (Support for module linking of VST proofs)

FILES FROM THE PAPER:
(See the diagram at the beginning of section 2 of the paper for a roadmap)

stdlib.h  (extern declarations of the malloc/free functions)

THE FOLLOWING FILES SHOWN IN FIGURE 1 OF THE PAPER
pile.h
onepile.h
apile.h
triang.h
triang.c
onepile.c
pile_private.h
pile.c
apile.c

THE FOLLOWING FILE MENTIONED BUT NOT SHOWN IN THE PAPER:
main.c

THE FOLLOWING FILES CREATED BY RUNNING clightgen ON THE .c files:
triang.v
onepile.v
pile.v
apile.v
main.v

THE FOLLOWING FILES SHOWN IN FIGURE 2 OF THE PAPER
spec_pile.v  (VST funspecs for pile.c)

THESE FILES COMPLETE THE VERIFICATION OF THE pile PROGRAM:
verif_pile.v (VST verification of pile.c)
spec_onepile.v (VST funspecs for onepile.c)
verif_onepile.v (VST verification of onepile.c)
spec_apile.v (VST funspecs for apile.c)
verif_apile.v (VST verification of apile.c)
spec_triang.v (VST funspecs for triang.c)
verif_triang.v (VST verification of triang.c)
spec_main.v (VST funspecs for main.c)
verif_main.v (VST verification of main.c)
link_pile.v (VST verification of the linked program, all .c files linked)

BUILD INSTRUCTIONS:
1.  From the VST root installation directory,
make -jN     (where N is the number of threads to run in parallel)

2.  From this directory (progs/pile)
make -jN link_pile.vo

IF YOU WANT TO BUILD THE FASTPILE EXAMPLE:
make -jN fast/link_fastpile.vo

IF YOU WANT TO BUILD THIS OUTSIDE VST:
  You can move this VST/progs/pile directory to some location outside
  VST, in which case you'll need to create a CONFIGURE file
  with the following contents:
VST_LOC= path/to/VST
COMPCERT_LOC= path/to/CompCert

Then "make".

