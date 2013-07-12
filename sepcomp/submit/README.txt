README
======

This directory includes files accompanying the POPL'14 submission:

    Verified Compilation for Shared-Memory C

BUILDING
--------

The files in this directory are excerpted from a larger proof development,
the VST, or Princeton Verified Software Toolchain.  

To build, please download revision XXXX of the VST from the SVN repository
linked at

    http://vst.cs.princeton.edu/download

and follow the attached build/installation instructions.


FILES
-----

Section 6:
----------

- linking.v: 
    extensional model of core semantics linking

- linking_simulations.v:
    states the linking simulation theorem of Sec. 6

- linking_proof.v:
    proves the linking simulation theorem of Sec. 6

- fs_linking.v:
    develops the file system model described in Sec. 6
    proves the linking simulation theorem of linking_simulations.v
      

