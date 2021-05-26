# HOW TO BUILD:

## Check compatibility

If you install VST via opam, opam will take care of dependency versions.

Otherwise please check:

1. Make sure you have the right version of Coq.  
   ```sh
   grep ^COQVERSION Makefile
   ```
   will tell you which versions are compatible.

2. Make sure you have the right version of CompCert.
   VST 2.6 uses CompCert 3.7 for Coq 8.11 or Coq 8.12

## Install Method 1: use the Coq Platform

The recommended way to install any library for Coq (including VST) is via
the [Coq Platform](https://github.com/coq/platform), which is a set of 
scripts that will do an appropriate opam install for your operating 
system (Linux, MacOS, Windows). Follow the instructions there
(that is, in README.md under Usage) to download the Coq Platform scripts
and then follow the OS-specific instructions. After you install via the
Coq Platform, you can still use opam commands to adjust your configuration,
add more packages, et cetera.

## Install Method 2: use opam directly

If you install VST via opam, opam will try to install a
suitable version of CompCert, Flocq and other dependencies.
```
opam install coq-vst
AND/OR
opam install coq-vst-64
```
You can install both the 32 bit and the 64 bit versions of VST and
CompCert in parallel. They will be installed in different folders.
Please note that the 64 bit variants will be installed in non standard
locations and must be included explicitly with -Q or -R options:
```
<opam-root>/lib/coq-variants/vst64/vst/
<opam-root>/lib/coq-variants/compcert64/compcert/
<opam-root>/variants/compcert64/bin/
<opam-root>/variants/compcert64/lib/
```
Please also note that some opam supplied versions of CompCert use a version of
Flocq distributed with CompCert. This is problematic if you want to verify
numerical code which uses tools like CoqInterval or Gappa which also use
Flocq. The proofs these tools do might then not be compatible with VST
and CompCert. For CompCert 3.7 there is an opam version called
```
coq-compcert.3.7~coq-platform
coq-compcert-64.3.7~coq-platform
```
which uses the opam supplied version of Flocq. There is also a version
```
coq-compcert.3.7~coq-platform~open-source
coq-compcert-64.3.7~coq-platform~open-source
```
which only contains the dual licensed open source part of CompCert. This
is sufficient for learning VST using the example C programs provided. If you
want to use VST for your own C code, you need at least clightgen, which is
*not* free software. Please clarify the CompCert license conditions if you
want to use clightgen. In case you want to use clightgen, please use this
install command:
```
opam install coq-compcert.3.7~coq-platform coq-vst
AND/OR
opam install coq-compcert-64.3.7~coq-platform coq-vst-64
```
VST can work with various installations of CompCert and this sequence ensures
you get the version you want. If you are an industrial user and want to
learn CompCert and ensure you only install open source software, please
use this install command:
```
opam install coq-compcert.3.7~coq-platform~open-source coq-vst
AND/OR
opam install coq-compcert-64.3.7~coq-platform~open-source coq-vst-64
```

## Install Method 3: manual make with opam-supplied CompCert

Download the VST sources (by cloning the repo, or by unzipping
a release .zip or .tar.gz file).

Then follow this procedure:

1. Make sure CompCert and Flocq Coq `.vo` files are installed in
   ```
   <opam-root>/lib/coq/user-contrib/Flocq
   <opam-root>/lib/coq/user-contrib/compcert
   AND/OR
   <root>/lib/coq-variants/compcert64/compcert
   ```
  This will happen automatically if you use the Coq Platform
  (or opam directly) to install CompCert.

2. Make sure CompCert clightgen is installed in
   ```
   <opam-root>/bin
   AND/OR
   <opam-root>/variants/compcert64/bin
   ```

3. In the VST root source directory (the directory containing the file
   you are reading), execute this command:
   ```
   make
   OR
   make BITSIZE=64
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

In case you want to regenerate the clightgen Coq files for the examples, you need to
specify an absolute path to a clightgen executable. This is useful in case you want
to check the examples for non x86 architectures. Please take care that this matches
the given architecture (this is not checked).
- `CLIGHTGEN=<absolute path for given architecture>/clightgen`

--------------------------------------------------------------------------------

# ORGANIZATION:

The Verified Software Tool-chain is organized into separate sub-projects,
each in a separate directory:

- `msl` -   Mechanized Software Library
- `examples` - examples of how to use the msl (not ported to Coq 8.6)
- `compcert` -   front end of the CompCert compiler, specification of C light
- `sepcomp` - the theory and practice of how to specify shared-memory interaction
- `veric` -  program logic (and soundness proof) for Verifiable C
- `floyd` -  tactics for applying the separation logic
- `progs` -  sample programs, with their verifications

The dependencies are:

- `msl`:   _no dependency on other directories_
- `examples`: msl
- `compcert`: _no dependency on other directories_
- `sepcomp`: compcert
- `veric`:  msl compcert sepcomp
- `floyd`: msl sepcomp compcert veric
- `progs`: msl sepcomp compcert veric floyd

In general, we Import using `-Q` (qualified) instead of `-R`
(recursive).  This means modules need to be named using qualified names.
Thus, in `veric/expr.v` we write `Require Import msl.msl_standard`
instead of `Require Import msl_standard`.  To make this work, the loadpaths
need to be set up properly; the file `_CoqProject` (built by `make _CoqProject`)
shows what -I includes to use.

## USING VST:

To use either of these interactive development environments you will
need to have the right load path.  This can be done by command-line
arguments to coqide or coqtop.  The precise command-line arguments
to use when running CoqIDE or coqc are constructed automatically when
when you do "make", in the following files:

- `_CoqProject-export`: For VST users, running the IDE outside the VST directory
- `_CoqProject` : For VST developers, running the IDE in the VST directory

#### WITH COQIDE

From the VST root directory, run `./coqide` to run coqide with recommended options.
(Read the script for more info.)

#### WITH PROOF GENERAL

Use the `_CoqProject` file generated by the Makefile
   (Yes, we know, normally it's the other way 'round, normally one generates
    a Makefile from the `_CoqProject`.)

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
Starting in July 2018, for a limited period of (we hope) only a few months,
there is an experimental alternate CompCert basis in compcert_new.
To use this, define a CONFIGURE file containing  COMPCERT=compcert_new,
and make sure to do a "make depend" and "make clean" before (re)building.
WARNING:  When using compcert_new, the file veric/Clight_core.v
is not active; instead concurrency/shim/Clight_core.v is bound to the
module path VST.veric.Clight_core.
