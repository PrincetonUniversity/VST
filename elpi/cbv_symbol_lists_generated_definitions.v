Require Import elpi.elpi.

(** * ELPI based cbv reduction in parts of terms with hand crafted delta symbol lists: Common definitions *)

(** ** Elpi Database containing some helper databases for CBV symbol list generation + helper predicates *)

Elpi Db cbv_symbol_generated.db lp:{{
  % A database mapping reduction names (ids) to reduction flags (usually with lengthy delta expansion lists)
  pred cbv-reduction i:string o:coq.redflags.
  :name "cbv-reduction.fail"
  cbv-reduction N _ :- coq.error "cbv-reduction: entry with name" N "not found!".
}}.

Elpi Command cbv_expanded_reduction_definition.
Elpi Accumulate Db cbv_symbol_generated.db.
Elpi Accumulate lp:{{
  % Convert a symbol name to a redflag
  pred argument->redflag i:argument, o:coq.redflag.
  argument->redflag (str N) (coq.redflags.const C) :- coq.locate N (const C), !.
  argument->redflag (str N) _ :- coq.error "cbv_expanded_reduction_definition: the given name" N "is not a constant!".
  argument->redflag A _ :- coq.error "cbv_expanded_reduction_definition: the given argument" A "is not a string".

  main [str NAME|ARGUMENTS] :-
    std.map ARGUMENTS argument->redflag LR,
    coq.redflags.add coq.redflags.betaiotazeta LR RF,
    coq.elpi.accumulate _ "cbv_symbol_generated.db" (clause _ (before "cbv-reduction.fail") (cbv-reduction NAME RF))
  .
}}.
Elpi Typecheck.
