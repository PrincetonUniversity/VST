# Using VST

## On your own machine

See the INSTALL.md file for installing it.  You may want to add to your $PATH the path to CompCert's clightgen to convert .c files into .v files.

You can use [proofgeneral](http://proofgeneral.inf.ed.ac.uk/) or CoqIde.  With proofgeneral, it's good to set up a script e.g. called `pg` that loads VST and CompCert as libraries:

    #!/bin/bash

    emacs \
      --eval "(setq coq-prog-name \"coqtop\")" \
      --eval "(setq coq-prog-args \
        '(\"-I\" \"/PATHTOVST/VST\"
          \"-R\" \"/PATHTOCOMPCERT/CompCert-2.5\" \"-as\" \"compcert\"
         )
       )" $@

Similarly for Coqide:

    coqide -I /PATHTOVST/VST -R /PATHTOCOMPCERT/CompCert-2.5 -as compcert YOURFILE.v

And similarly in your typical Makefile

    FLAGS=-I /PATHTOVST/VST -R /PATHTOCOMPCERT/CompCert-2.5 -as compcert

    all:myprogram.vo

    %.vo:%.v Makefile
    	coqc $(FLAGS) $<

and then the usual routine is to convert your .c file into a .v file, compile it with coq through make, and run proofgeneral or coqide on it:

    clightgen myprogram.c
    make myprogram.vo
    pg verif_myprogram.v #or coqide

You can use the following files to get started
[Makefile](https://madiot.fr/vst/Makefile),
[myprogram.c](https://madiot.fr/vst/myprogram.c) and
[verif_myprogram.v](https://madiot.fr/vst/verif_myprogram.v) (this example is the list reversal program and its proof, taken from [here](https://raw.githubusercontent.com/PrincetonUniversity/VST/new_compcert/progs/verif_reverse.v)).


## On cs.princeton.edu machines

With a CS account at princeton, [you can ssh to the following machines](https://csguide.cs.princeton.edu/remote/ssh) with the `-X` option to enable X11 forwarding to be able to open windows:

    ssh -X username@cycles.cs.princeton.edu

You'll need to run Proof General instead of CoqIDE, because there's currently no CoqIDE installed on the cycles.cs machines.

You should add this to your .bash_profile (or profile for whatever shell you use):

    export PATH=/n/fs/sml/sharedvst/bin:$PATH

and this to your .emacs

    (load "/n/fs/sml/sharedvst/proofgeneral/generic/proof-site.el")

Then you'll get two commands:

* "clightgen"  (for translating .c files into .v files) and
* "pg" for proofgeneral (which loads Compcert (as "compcert") and VST (as an empty dirpath)).

Next step is use this as a starting Makefile:

    FLAGS=-I /n/fs/sml/sharedvst/VST -R /n/fs/sml/sharedvst/CompCert-2.5 -as compcert

    all:myprogram.vo

    %.vo:%.v Makefile
    	coqc $(FLAGS) $<

and then the usual routine is to convert your .c file into a .v file, compile it with coq through make, and run proofgeneral on it:

    clightgen myprogram.c
    make myprogram.vo
    pg verif_myprogram.v

You can use the following files to get started
[Makefile](https://madiot.fr/vst/Makefile),
[myprogram.c](https://madiot.fr/vst/myprogram.c) and
[verif_myprogram.v](https://madiot.fr/vst/verif_myprogram.v) (this example is the list reversal program and its proof, taken from [here](https://raw.githubusercontent.com/PrincetonUniversity/VST/new_compcert/progs/verif_reverse.v)).

Signal problems to Jean-Marie Madiot (jmadiot at cs dot princeton ...).
