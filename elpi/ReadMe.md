# Elpi code for VST

Elpi is a (relatively) new tactic language for Coq based on Prolog.

Currently we use it only for one purpose:

## Simplification by "Call By Value" computation with specially crafted delta symbol lists

VST needs in many places to do e.g. computations on PTress with symbol lists. These can contain user provided terms (values assigned to variables).
Using simpl for this task usually works but has two drawbacks:

- it is quite slow because simpl employs rather involved heuristics to decide if a term will get simpler if reductions are done
- running simpl on unknown user terms can explode in case the terms contain variables

This problem is solved by using the `cbv` tactic with a specially crafted delta symbol list, which only contains those symbols required e.g.
for the PTree reduction. As long as the user terms don't contain PTree logic, they are unmodified by this.

The issue with this is that the symbol lists are long (many 100) and it might be a lot of work to maintain them. For this reason we use Elpi
to create symbol lists from high level descriptions like "all transparent definitions in module X.Y".

This works, but requires a version of Elpi which has not yet been released (at least not in Coq Platform), so we do this in a two step process:

- a symbol list generator which creates .v files which are checked into git - only this requires the edge version of Elpi
- a tactic which uses the generated symbol list .v files - this is (currently) written in Ltac2

Adding make rules for the generator leads to circular make dependencies. So no explicit rules are provided.
The symbol lists can be regenerated with a usual call to make (with whatever parameters you usually use) and the target

`elpi/cbv_symbol_lists_generator.vo`

This regenerates `elpi/cbv_symbol_lists_generated.v` and `ltac2/cbv_symbol_lists_generated.v`
