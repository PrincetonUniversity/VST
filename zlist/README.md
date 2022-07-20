This is a library of list operations using Z as index, and a simple yet powerful solver.

## Installation
This is a component of VST but can also be installed separately.  When used within VST does not need a separate opam install, but when used independently of vst then:
```
opam pin coq-vst-zlist https://github.com/PrincetonUniversity/VST.git
```
This is compatible with VST of the same version.

## Definitions
`Zlength`: length of a list.
`Znth`: nth element of a list; returns default when out of bounds.
`sublist`: a slice of a list in the range [lo, hi).
`upd_Znth`: update the nth element of a list.

## Tactics
`list_solve`: Use the list solver to solve the goal. If it fails, you may try `list_simplify` to see the subgoal that cannot be solved.
`list_simplify`: Reduce the goal using the list solver. It is safe that it does not turn a provable goal into any unprovable goals.

## Credit
Qinshi Wang and Andrew W. Appel
