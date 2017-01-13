# Installing [VST](https://github.com/PrincetonUniversity/VST/)

1. [Instructions for Linux](#instructions-for-linux)
2. [Instructions for OS X](#instructions-for-os-x)
3. [Instructions for Windows / Cygwin](#instructions-for-windows)

## Instructions for Linux

Branch [new_compcert](https://github.com/PrincetonUniversity/VST/tree/new_compcert) with CompCert 2.5.

If you have already Coq 8.4pl6 (or 8.4pl5) or menhir >= 20140422, skip the corresponding sections.

Building times correspond to some 2015 laptop with 8 threads and 16 of RAM, which was still slower than the "cycles" machines at the Princeton CS department.  Building was roughly 3 times slower with a 2008 laptop with 2 threads and 4 G of RAM.

## Get opam (~5 minutes)

Opam is a package manager for ocaml programs.

You might not need opam! But if you do, try installing it from the standard repositories, then run `opam init`.  If `opam init` fails, uninstall it and then install it manually:

    wget https://github.com/ocaml/opam/releases/download/1.2.2/opam-full-1.2.2.tar.gz
    tar xf opam-full-1.2.2.tar.gz
    cd opam-full-1.2.2
    ./configure
    make lib-ext
    make -j
    sudo make install
    opam init

Say yes to modify your favorite .bashrc/.bash_profile file change if it's not the one you use).  Then the best is to open a new console to have opam ready.

Alternatively, run:

    eval `opam config env`

each time you want to use opam-installed packages.

### Get Coq 8.4pl6 (~5 minutes)
[Coq 8.4pl5 will suffice, if you already have that]

You'll need camlp5.  If you don't have it, you can use opam:

    opam install camlp5

Then standard installation process:

    wget https://coq.inria.fr/distrib/8.4pl5/files/coq-8.4pl5.tar.gz
    tar xf coq-8.4pl6.tar.gz
    cd coq-8.4pl6/
    ./configure
    make -j
    sudo make install

Build time is 15 minutes, 3 minutes with many cores.

### Get menhir version 20140422 (~1 minute)

With opam:

    opam install menhir -y

### Get and compile CompCert 2.5 (~10 minutes)

Go to some directory that will be your main VST directory

    wget http://compcert.inria.fr/release/compcert-2.5.tgz
    tar xf compcert-2.5.tgz
    cd CompCert-2.5
    ./configure ia32-linux

Now, we need clightgen, and for it we need a patch:

    mv exportclight/ExportClight.ml{,_bak}
    wget https://raw.githubusercontent.com/PrincetonUniversity/VST/new_compcert/compcert/exportclight/ExportClight.ml -O exportclight/ExportClight.ml

and another patch for Ctypes.v:

    mv cfrontend/Ctypes.v{,_bak}
    wget https://raw.githubusercontent.com/AbsInt/CompCert/db0a62a01bbf90617701b68917319767159bf039/cfrontend/Ctypes.v -O cfrontend/Ctypes.v

We can finally build CompCert:

    make -j
    make -j clightgen

Build time is 30 minutes, 7 minutes with many cores.

### Get and compile VST (~1 or 2 hours)

Go to your main VST directory where there is already CompCert.  This will create a VST directory next to "CompCert-2.5", that should be renamed to "compcert".

    mv CompCert-2.5 compcert
    git clone https://github.com/PrincetonUniversity/VST.git
    cd VST
    git checkout new_compcert
    make -j -k

If the Makefile rejects your version of Coq because it's too recent, you can try for example if you have 8.4pl7:

    sed -i 's/or-else 8.4pl6/or-else 8.4pl6 or-else 8.4pl7/' Makefile

Build time is 120 minutes, 50 minutes with many cores.

### Open proofgeneral/coqide

Both CoqIDE and Emacs (with proofgeneral) automatically recognize _CoqProject files.  This means that when you open a .v file that is located inside the VST repository, you should have the correct, up-to-date loadpath.

If it does not work for CoqIDE, go to Edit > Preferences > Project and select the option "appended to arguments" instead of "ignored".  If it still does not work, try using something a command of the form:

    coqide -I msl -as msl -I sepcomp -as sepcomp -I veric -as veric -I floyd -as floyd -I progs -as progs -I sha -as sha -I concurrency -as concurrency -R compcert -as compcert YOURFILE.v

If it does not work for emacs, try updating proofgeneral and/or emacs and try again.  If it still does not work, try to open a terminal in the directory "VST" inside your main VST directory, and run:

    ./pg

Then open your files from inside emacs.  Start with 'progs/verif_reverse.v' for an introduction.


## Instructions for OS X

Branch [new_compcert](https://github.com/PrincetonUniversity/VST/tree/new_compcert) with CompCert 2.5.

If you have already Coq 8.4pl6 or menhir >= 20140422, skip the corresponding sections.
[Coq 8.4pl5 will suffice, if you already have that]

## Get [Homebrew](http://http://brew.sh/) (~5 minutes)

Run the following on your Terminal:

`ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"`

Now you have Homebrew, this is a big day for you.

### Get wget (~1 minute)

I use wget to download the packages that are not in Homebrew. If you don't have it, you can use hombrew:

    brew install wget

### Get Coq 8.4pl6 (~5 minutes)
[Coq 8.4pl5 will suffice, if you already have that]

You'll need camlp5.  If you don't have it, you can use hombrew:

    brew install camlp5

Then brew Coq:

    brew install coq


### Get menhir version 20140422 (~1 minute)

With homebrew:

    brew install menhir

### Get and compile CompCert 2.5 (~10 minutes)

Go to some directory that will be your main VST directory

    wget http://compcert.inria.fr/release/compcert-2.5.tgz
    tar xf compcert-2.5.tgz
    cd CompCert-2.5
    ./configure ia32-macosx

Now, we need clightgen, and for it we need a patch:

    mv exportclight/ExportClight.ml{,_bak}
    wget https://raw.githubusercontent.com/PrincetonUniversity/VST/new_compcert/compcert/exportclight/ExportClight.ml -O exportclight/ExportClight.ml

And another patch for Ctypes.v:

    mv cfrontend/Ctypes.v{,_bak}
    wget https://raw.githubusercontent.com/AbsInt/CompCert/db0a62a01bbf90617701b68917319767159bf039/cfrontend/Ctypes.v -O cfrontend/Ctypes.v

We can finally build CompCert:

    make -j
    make -j clightgen

Build time is 30 minutes, 7 minutes with many cores.

### Get and compile VST (~1 or 2 hours)

Go to your main VST directory where there is already CompCert.  This will create a VST directory next to "CompCert-2.5", that should be renamed to "compcert".

    mv CompCert-2.5 compcert
    git clone https://github.com/PrincetonUniversity/VST.git
    cd VST
    git checkout new_compcert
    make -j -k

### Set the coqpath

Both CoqIDE and Emacs (with proofgeneral) automatically recognize _CoqProject files.  This means that when you open a .v file that is located inside the VST repository, you should have the correct, up-to-date loadpath.

If it does not work for CoqIDE, go to Edit > Preferences > Project and select the option "appended to arguments" instead of "ignored".  If it still does not work, try using something a command of the form:

    coqide -I msl -as msl -I sepcomp -as sepcomp -I veric -as veric -I floyd -as floyd -I progs -as progs -I sha -as sha -I concurrency -as concurrency -R compcert -as compcert YOURFILE.v

If it does not work for emacs, try updating proofgeneral and/or emacs and try again.  If it still does not work, try to open a terminal in the directory "VST" inside your main VST directory, and run:

    ./pg

Then open your files from inside emacs.

If it still does not work, add the following lines to your .emacs file:

    ;VST coqpaths
    (custom-set-variables '(coq-prog-args '(
    "-R" "/Users/scuellar/Projects/compcert-2.5" "-as" "compcert"
    "-R" "/Users/scuellar/Projects/VST/msl" "-as" "msl"
    "-R" "/Users/scuellar/Projects/VST/veric" "-as" "veric"
    "-R" "/Users/scuellar/Projects/VST/floyd" "-as" "floyd"
    "-R" "/Users/scuellar/Projects/VST/progs" "-as" "progs"
    "-R" "/Users/scuellar/Projects/VST/sepcomp" "-as" "sepcomp"
    )))

    (setq coq-load-path '(("/Users/scuellar/Projects/compcert-2.5" "compcert")
                      ("/Users/scuellar/Projects/VST/msl" "msl")
                      ("/Users/scuellar/Projects/VST/veric" "veric")
                      ("/Users/scuellar/Projects/VST/floyd" "floyd")
                      ("/Users/scuellar/Projects/VST/progs" "progs")
                      ("/Users/scuellar/Projects/VST/sepcomp" "sepcomp") ))`


### Open a file

Open your files from inside emacs.  Start with 'progs/verif_reverse.v' for an introduction. Another good example is 'progs/verif_nest2.v'.

## Instructions for Windows

Branch [new_compcert](https://github.com/PrincetonUniversity/VST/tree/new_compcert) with CompCert 2.5.

If you have already Coq 8.4pl6 (or 8.4pl5) or menhir >= 20140422, skip the corresponding sections.

## Install cygwin

In some directory (name immaterial, for example, "root"),
download CompCert as one subdirectory (compcert-2.5)
and VST as another subdirectory (VST).

## Download CompCert 2.5 from compcert.inria.fr

Don't build it yet!  It will need a patch, see below.

## Download the Verified Software Toolchain, new_compcert branch

    git clone https://github.com/PrincetonUniversity/VST.git
    cd VST
    git checkout new_compcert

(To download, it's probably best to use git to clone the repository)

https://github.com/PrincetonUniversity/VST/tree/new_compcert

## Patch CompCert

cd root
cp VST/compcert/exportclight/ExportClight.ml compcert-2.5/exportclight/ExportClight.ml

## Build CompCert
cd root/compcert-2.5
./configure ia32-cygwin
make -j clightgen

## Build VST
cd root/vst/compcert
./make -j
cd root/vst
make depend
make -j

## Run VST

To run a file inside Coqide, for example VST/progs/verif_reverse.v,
do this:

    cd VST
    coqide `cat .loadpath` progs/verif_reverse.v &

However, both CoqIDE and Emacs (with proofgeneral) should automatically recognize _CoqProject files. If it does not work for CoqIDE, go to Edit > Preferences > Project and select the option "appended to arguments" instead of "ignored".  You might have to `cd` to VST before opening your file.
