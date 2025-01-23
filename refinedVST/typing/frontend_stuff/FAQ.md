The type system gets stuck on a sidecondition which contains an existential quantifier, what should I do? 
--------------------------------------------------------------------------------------------------------------

See `tutorial/t02_evars.c` for an explanation how to RefinedC's
mechanism for instantiating existential quantifiers works. This file
also explains different strategies for guiding RefinedC towards the
right instantiation of existential quantifiers.

How do I add additional simplification rules?
---------------------------------------------

The simplification rules can be extended by the user through special
typeclasses such as `SimplBoth`, `SimplAnd` and `SimplImpl`. See the
file
[theories/lithium/simpl_instances.v](theories/lithium/simpl_instances.v)
for the definition and many instances. Keep in mind the simplification
rules should in general be bi-implications to avoid accidentally
turning a provable goal into an unprovable.


How do I debug the simplification mechanism?
--------------------------------------------
When adding such simplification rules, the system may still get stuck and it
may be useful to understand why. To this aim, you can step through the proof
manually until it gets stuck
```
repeat liRStep; liShow.
```
and then enable typeclass debugging.
```
Set Typeclasses Debug.
(*Set Typeclasses Debug Verbosity 2.*)
try liRStep.
```

Why does `ContainsEx` contain an evar?
----------------------------------------------

Simplification rules will sometimes have an argument of the following form:
```
`{!ContainsEx (some coq term)}
```
Do not forget the `!` here. Otherwise weird things happen.

Why don't I get as an hypothesis that an integer parameter is in range?
-----------------------------------------------------------------------

The hypotheses that the integer parameters are in range are only added to the
context on the first time the parameter is accessed. If such an hypothesis is
required prior to a first access, you can use the following macro to make it
available.
```c
rc_unfold_int(i);
```
