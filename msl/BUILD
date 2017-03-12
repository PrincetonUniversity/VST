
HOW TO BUILD  [A. Appel, March 2010]

This library is set up so that clients can import all or part of it
without worrying about file name clashes between the MSL and the
client.  This is not the most idiomatic way to use Coq, but it does
work.

To compile the MSL, just do "make".  If you change the pattern of
Require statements, do "make depend" to rebuild the .depend file.

To edit the MSL in CoqIde or Proof General, upon startup of the IDE
you must visit the file "0path.v" in a buffer and "run" it to the end.
This globally sets up path visibility for all the other buffers!

To import the MSL into client programs, you have two choices.

METHOD 1.  Import only by qualified path names.  The client can do,

Require Import msl.msl_standard.

or can import individual components selectively, via

Require Import msl.sepalg.
Require Import msl.shares.

Note: some components are not exported by msl_standard,
so the client would still have to do (for example),

Require Import msl.cjoins.

For all this to work, the Coq include path for the client must contain
the PARENT directory containing the msl directory; suppose msl is
located at PATH="/lib/coq/msl" or PATH="../msl", then the coqc command
for use by the *client* is,

coqc -I . -I $(PATH)

and the client's "0path.v" file must contain something like
Add LoadPath "/lib/coq".    or,
Add LoadPath ".."           (whichever is the value of PATH)

To use CoqIde or Proof General to edit client code that imports
MSL, you must load the client's 0path.v in a buffer first, before
opening the client file in question.

METHOD 2.  Import more conventionally.

For this, one would use -R instead of -I for coqc. Then the client
would get all the filenames unqualified, i.e. as "Require Import cjoins"
instead of "Require Import msl.cjoins".
I haven't debugged this version yet.

