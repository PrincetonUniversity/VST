# HOW TO BUILD:

## Check compatibility

If you install VST via opam, opam will take care of dependency versions.

Otherwise, run `opam pin add builddep/` to install the required dependencies.

## Install Method 1: use the Rocq Platform

The recommended way to install any library for Rocq (including VST) is via
the [Rocq  Platform](https://github.com/rocq-prover/platform), which is a set of 
scripts that will do an appropriate opam install for your operating 
system (Linux, MacOS, Windows). Follow the instructions there
(that is, in README.md under Usage) to download the Rocq Platform scripts
and then follow the OS-specific instructions. After you install via the
Rocq Platform, you can still use opam commands to adjust your configuration,
add more packages, et cetera.

## Install Method 2: use opam directly

If you install VST via opam, opam will try to install a
suitable version of CompCert, Flocq and other dependencies.
```
opam install rocq-vst
```

## Install Method 3: manual make with opam-supplied CompCert

Download the VST sources (by cloning the repo, or by unzipping
a release .zip or .tar.gz file).

Then follow this procedure:

1. Make sure CompCert and Flocq `.vo` files are installed in
   ```
   <opam-root>/lib/coq/user-contrib/Flocq
   <opam-root>/lib/coq/user-contrib/compcert
   ```
  This will happen automatically if you use the Rocq Platform
  (or opam directly) to install CompCert.

2. Make sure CompCert clightgen is installed in
   ```
   <opam-root>/bin
   ```

3. In the VST root source directory (the directory containing the file
   you are reading), execute this command:
   ```
   make
   ```  
   (or, if you have a multi-core computer,  `make -j 16`). You may add the
   target `floyd` to just build VST's core without examples and tests.

Please note that if you give options via the make command line, you should
*not* have a file `CONFIGURE` in the VST root folder.

## Install Method 4: advanced manual make, e.g. with bundled CompCert

Download the VST sources (by cloning the repo, or by unzipping
a release .zip or .tar.gz file).

All options described in this section can be given in 3 ways:
- on the command line of make via `<option>=<value>`
- as an environment variable
- as an assignment in a file `CONFIGURE` in the VST root folder
Please be sure that you don't mix these methods in unintended ways.

VST make supports the below options to control which CompCert is used:
- `COMPCERT=platform`: (default) choose 32 or 64 bit platform supplied x86 variant, dependent on BITSIZE, ARCH can be left empty or must be x86
- `COMPCERT=bundled`: build and use bundled 32 or 64 x86 variant, dependent on BITSIZE, ARCH can be left empty or must be x86
- `COMPCERT=bundled_new`: build and use bundled compcert_new 32 or 64 x86 variant, dependent on BITSIZE, ARCH can be left empty or must be x86
- `COMPCERT=src_dir`: build and use in source folder COMPCERT_SRC_DIR the variant specified by ARCH and BITSIZE
- `COMPCERT=inst_dir`: use prebuilt CompCert in COMPCERT_INST_DIR.  BITSIZE and ARCH can be left empty or must match

The above settings for COMPCERT are keywords and not placeholders.
If required additional information is given with these variables:
- `COMPCERT_SRC_DIR`: absolute or relative CompCert source path
- `COMPCERT_INST_DIR`: usually absolute CompCert installation path or source path with in-place build

If CompCert is built from sources, make sure to give at least one of
the following options to CompCert's ./configure script: -clightgen, or
-install-coqdev, or -coqdevdir, so that CompCert's compcert.config
file is produced for VST to read.

The below options can be given in addition in order to chose the architecture.
If CompCert is built from sources, this configures CompCert accordingly.
If `COMPCERT=inst_dir` is chosen, the below options must match the specified
installation if they are given.
If `COMPCERT=platform` is chosen, `BITSIZE` can be specified, but the architecture
is ignored.
- `BITSIZE=32` (default)
- `BITSIZE=64`
- `ARCH=x86`: (default) Intel x86, 32 and 64 bit
- `ARCH=aarch64`: 64 bit ARM architecture
- `ARCH=powerpc`: 32 bit power PC architecture

In case you want to regenerate the clightgen Rocq files for the examples, you need to
specify an absolute path to a clightgen executable. This is useful in case you want
to check the examples for non x86 architectures. Please take care that this matches
the given architecture (this is not checked).
- `CLIGHTGEN=<absolute path for given architecture>/clightgen`

--------------------------------------------------------------------------------

# ORGANIZATION:

The Verified Software Toolchain is organized into separate sub-projects,
each in a separate directory:

- `msl` -   Mechanized Software Library (currently just definitions of tree shares)
- `compcert` -   front end of the CompCert compiler, specification of C light
- `zlist` - theory of concatenable sublists, and list theory solver
- `sepcomp` - the theory and practice of how to specify shared-memory interaction
- `shared` -  basic constructs for VST's separation logic
- `veric` -  program logic (and soundness proof) for Verifiable C
- `floyd` -  tactics for applying the separation logic
- `progs` -  sample programs, with their verifications

The dependencies are:

- `msl`:   _no dependency on other directories_
- `compcert`: _no dependency on other directories_
- `zlist` - _no dependency on other directories_
- `sepcomp`: compcert
- `shared` -  _no dependency on other directories_
- `veric`:  msl shared compcert sepcomp
- `floyd`: msl shared sepcomp compcert veric
- `progs`: msl shared sepcomp compcert veric floyd

In general, we Import using `-Q` (qualified) instead of `-R`
(recursive).  This means modules need to be named using qualified names.
Thus, in `veric/expr.v` we write `Require Import VST.veric.Clight_base.`
instead of `Require Import Clight_base`.  To make this work, the loadpaths
need to be set up properly; the file `_CoqProject` (built by `make _CoqProject`)
shows what -I includes to use.

## USING VST:

To use either of these interactive development environments you will
need to have the right load path.  This can be done by generating
a `_CoqProject` file; "make" produces the following files:

- `_CoqProject-export`: For VST users, running the IDE outside the VST directory
- `_CoqProject` : For VST developers, running the IDE in the VST directory

## NEW DIRECTORIES:

If you add a new directory, you will probably want to augment the loadpath
so that qualified names work right.  Edit the `OTHERDIRS` or `VSTDIRS` lines of
the `Makefile`.

## EXTERNAL COMPCERT:

The VST imports from the CompCert verified C compiler, the definition
of C light syntax and operational semantics.  For the convenience of
VST users, the `VST/compcert` directory is a copy (with permission) of
the front-end portions of compcert.  
You may choose to ignore the `VST/compcert` directory and have
the VST import from a build of compcert that you have installed in
another directory, for example,  `../CompCert`.

**This has not been tested recently, as of August 2017.**  
To do this, create a file `CONFIGURE` containing a definition such as,
  `COMPCERT=../CompCert`  
Make sure that you have the right version of CompCert!  Check
the file `VST/compcert/VERSION` to be sure.

## COMPCERT_NEW:
There is an experimental alternate CompCert basis in compcert_new, for use in the concurrent soundness proofs circa 2020.
To use this, define a CONFIGURE file containing  COMPCERT=compcert_new,
and make sure to do a "make depend" and "make clean" before (re)building.
WARNING:  When using compcert_new, the file veric/Clight_core.v
is not active; instead concurrency/shim/Clight_core.v is bound to the
module path VST.veric.Clight_core.
