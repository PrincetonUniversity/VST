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
   VST 2.6 uses CompCert 3.7 for Coq 8.11

## Install Methods

### Install via opam

If you install VST via opam, opam will automatically install a
suitable version of CompCert, Flocq and other dependencies.
```
opam install coq-vst
AND/OR
opam install coq-vst-64
```
You can install both the 32 bit and the 64 bit versions of VST and
CompCert in parallel. They will be installed in different folders.

Please note that some opam supplied versions of CompCert use a version of
Flocq distributed with CompCert. This is problematic if you want to verify
numerical code which uses tools like CoqInterval or Gappa which also use
Flocq. The proofs these tools do might then not be compatible with VST
and CompCert. For CompCert 3.7 there is an opam version called
```
coq-compcert.3.7~platform-flocq
coq-compcert-64.3.7~platform-flocq
```
which uses the opam supplied version of Flocq. There is also a version
```
coq-compcert.3.7~platform-flocq~open-source
coq-compcert-64.3.7~platform-flocq~open-source
```
which only contains the dual licensed open source part of CompCert. This
is sufficient for learning VST using the example C programs provided and it
is the *default* dependency of VST. If you want to use VST for your own C code,
you need at least clightgen, which is *not* free software. Please clarify the
CompCert license conditions if you want to use clightgen. In case you want to
use clightgen, please use this install command:
```
opam install coq-compcert.3.7~platform-flocq coq-vst
AND/OR
opam install coq-compcert-64.3.7~platform-flocq coq-vst-64
```
VST can work with various installations of CompCert and this sequence ensures
you get the version you want. If you are an industrial user and want to
learn CompCert and ensure you only install open source software, please
use this install command:
```
opam install coq-compcert.3.7~platform-flocq~open-source coq-vst
AND/OR
opam install coq-compcert-64.3.7~platform-flocq~open-source coq-vst
```

### Manual make with opam / coq-platform supplied CompCert

For a manual make please follow this procedure:

1. Make sure CompCert and Flocq Coq `.vo` files are installed in
   ```
   <root>/lib/coq/user-contrib/Flocq
   <root>/lib/coq/user-contrib/compcert
   AND/OR
   <root>/lib/coq/user-contrib/compcert64
   ```

2. Make sure CompCert clightgen is installed in
   ```
   <root>/bin
   ```

3. Execute this command:
   ```
   make
   OR
   make BITSIZE=64
   ```  
   (or, if you have a multicore computer,  `make -j`)

Please note that in this case you should *not* have a file `CONFIGURE` in
the VST root folder as you might for the next method.

### Manual make with bundled CompCert

VST includes two bundled variants of CompCert, which in some releases of
VST might include changes to support new features of VST. The bundled
variants are in the VST root folder under
```
<vst-root>/compcert
<vst-root>/compcert_new
```
Please note that by default VST uses a platform supplied CompCert and
not the bundled CompCert. In case you want to use one of the bundled
CompCert variants, please use these options:
```
COMPCERT_INST_PATH=<vst-root>/compcert
```
OR
```
COMPCERT_INST_PATH=<vst-root>/compcert_new
COMPCERT_NEW
```
The COMPCERT_NEW flag sets a few additional makefile options required to
build the variant in `<vst-root>/compcert_new` and must be set if this
folder is specified for `COMPCERT_INST_PATH`.

You can set the additional options `BITSIZE` and `ARCH`. The supported
variants are:
```
ARCH=x86 BITSIZE=32 (default)
ARCH=x86 BITSIZE=64
ARCH=aarch64 BITSIZE=64
ARCH=powerpc BITSIZE=32
```
Both variables can be set either on the make command line or in a file named
`CONFIGURE` in the VST source root folder which is read by the VST makefile.

### Manual make with private build of CompCert and/or advanced options

If you want to use a different CompCert than the default opam supplied
CompCert, you can configure the CompCert path by setting:
```
COMPCERT=mycompcert
OR
COMPCERT_INST_PATH=/home/me/mycompcert
```
`COMPCERT` names a Coq module path under `lib/coq/user-contrib`.
`COMPCERT_INST_PATH` names an arbitrary CompCert path, e.g. a local GIT build.

Both variables can be set either on the make command line or in a file named
`CONFIGURE` in the VST source root folder which is read by the VST makefile.

In addition you can define the variables `BITSIZE` and `ARCH`. If neither
`COMPCERT` nor `COMPCERT_INST_PATH` are set, `BITSIZE` can be used to
choose between `COMPCERT=compcert` and `COMPCERT=compcert64`. In any case
it is checked if `BITSIZE` and `ARCH` match the configurazion information
found in `compcert-config` in the specified CompCert folder.

--------------------------------------------------------------------------------

# ORGANIZATION:

The Verified Software Toolchain is organized into separate subprojects,
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
