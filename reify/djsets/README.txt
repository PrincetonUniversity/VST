
                ATBR
                ====

Thomas Braibant & Damien Pous

Laboratoire d'Informatique de Grenoble (UMR 5217), INRIA, CNRS, France

Webpage of the project: http://proton.inrialpes.fr/~braibant/atbr/

This library is distributed under the terms of the GNU Lesser General
Public License version 3. See files LICENSE and COPYING. 
 


INSTALLATION.
=============

	Run 'make' to compile the library (please note that it takes
	quite a long time -- about six minutes with a recent computer).

	The bugfix version of Coq v8.3 might be required (it is known
	to compile with Coq v8.3 revisions pl2, 13766, 13769, and 14149).


DOCUMENTATION. 
==============

        Here is a succinct description of each file. 
	The user can also refer to files Examples.v and ChurchRosser.v.

0- Library files
ATBR			Export all relevant modules, except those related to matrices
ATBR_Matrices		Export all relevant modules, including those related to matrices


1- Algebraic hierarchy
Classes   	       	Definitions of algebraic classes of the development	
Graph 			Lemmas and hints about the base class (carrier with equality)
Monoid			Monoids, free monoids, finite iterations over a monoid, various tactics
SemiLattice		Semilattices, tactics: normalise, reflexivity, rewrite 
SemiRing		Idempotent semirings, tactics: normalise, reflexivity, rewrite 
KleeneAlgebra 		Kleene algebras, basic properties
Converse 		Structures with converse (semirings and Kleene Algebras)
Functors		Functors between the various algebraic structures
StrictKleeneAlgebra	Class of Strict Kleene algebras (without 0), and extension of the decision procedure

2- Models
Model_Relations		Kleene Algebra of (heterogeneous) binary relations
Model_StdRelations	Kleene Algebra of standard (homogeneous) binary relations
Model_Languages		Kleene Algebra of languages
Model_RegExp		Kleene Algebra of regular expressions (syntactic free model), typed reification
Model_MinMax		(min,+) Kleene Algebra (matrices on this algebra give weighted graphs)


3- Matrices
MxGraph			Matrices without operations; blocks definitions
MxSemiLattice		Semilattices of matrices
MxSemiRing		Semiring of matrices
MxKleeneAlgebra	        Kleene algebra of matrices (definition of the star operation)
MxFunctors		Extension of functors to matrices


4- Decision procedure for KA
DKA_Definitions		Base definitions for the decision procedure for KA (automata types, notations, ...)
DKA_StateSetSets        Properties about sets of sets
DKA_CheckLabels		Algorithm to check whether two regex have the same set of labels
DKA_Construction	Construction algorithm, and proof of correctness
DKA_Epsilon		Removal of epsilon transitions, proof of correctness
DKA_Determinisation	Determinisation algorithm, proof of correctness
DKA_Merge 		Union of DFAs, proof of correctness
DKA_DFA_Language	Language recognised by a DFA, equivalence with the evaluation of the DFA
DKA_DFA_Equiv 		Equivalence check for DFAs, proof of correctness
DecideKleeneAlgebra     Kozen's initiality proof, kleene_reflexivity tactic


5- Other tools
StrictStarForm	        Conversion of regular expressions into strict star form, kleene_ssf tactic
Equivalence	        Tactic for solving equivalences by transitivity



5- Examples
Examples 	  	Small tutorial file, that goes through our set of tactics
ChurchRosser 	  	Simple usages of kleene_reflexivity to prove commutation properties
ChurchRosser_Points  	Comparison between a standard CR proof and algebraic ones


6- Misc.
Common			Shared simple tactics and definitions
BoolView		View mechanism for Boolean computations 
Numbers			NUM interface, to abstract over the representation of numbers, sets, and maps 
Utils_WF		Utilities about well-founded relations; partial fixpoint operators (powerfix) 
DisjointSets		Efficient implementation of a disjoint sets data structure 
Force			Functional memoisation (in case one needs efficient matrix computations)
Reification		Reified syntax for the various algebraic structures


7- Finite sets and maps
MyFSets 		Efficient ordered datatypes constructions (for FSets functors)
MyFSetProperties	Handler for FSet properties
MyFMapProperties	Handler for FMap properties


9- OCaml modules
reification.ml		reification for the reflexive tactics



TACTICS.
========

1- Reflexive tactics:

[semiring_reflexivity]	solve an (in)equation on the idempotent semiring (*,+,1,0)
[semiring_normalize]	simplify an (in)equation on the idempotent semiring (*,+,1,0)
[semiring_clean]	simplify 0 and 1
[semiring_cleanassoc]	simplify 0 and 1, normalize the parentheses

[kleene_reflexivity]	solve an (in)equation in Kleene Algebras
[ckleene_reflexivity]	solve an (in)equation in Kleene Algebras with converse
[skleene_reflexivity]	solve an (in)equation in Strict Kleene Algebras (without 0)
[kleene_clean_zero]	remove zeros in a KA expression
[kleene_ssf]		put KA expressions into strict star form

2- Rewriting tactics:

[ac_rewrite H]		rewrite a closed equality modulo (AC) of (+)
[monoid_rewrite H]   	rewrite a closed equality modulo (A) of (*)

3- Other tactics:

[converse_down]		push converses down to terms leaves
[switch]		add converses to the goal and push them down to terms leaves





ACKNOWLEDGEMENTS.
=================

We would like to thank Guilhem Moulin and Sebastien Briais, 
who participated to a preliminary version of this project.

We are also grateful to Assia Mahboubi, Matthieu Sozeau, Bruno Barras,
and Hugo Herbelin for highly stimulating discussions, as well as
numerous hints for solving various problems.
