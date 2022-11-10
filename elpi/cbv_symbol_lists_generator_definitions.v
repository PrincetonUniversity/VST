Require Import elpi.elpi.

(** * ELPI based cbv reduction in parts of terms with hand crafted delta symbol lists: Common definitions *)

(** ** Elpi Database containing some helper databases for CBV symbol list generation + helper predicates *)

Elpi Db cbv_symbol_generator.db lp:{{
  % A database mapping reduction names (ids) to a list of constants.
  % Note: all parameters are "output" because this predicate is enumerated with "forall".
  pred cbv-reduction-definition o:string, o:list constant.
  :name "cbv-reduction-definition.fail"
  cbv-reduction-definition _ _ :- fail.

  % A database mapping module paths to file level module paths which can be used for Require.
  % That is path components refering to modules defined with Module are stripped away.
  % The default is that both are the same.
  pred module-path->require-path i:string, o:string.
  :name "module-path->require-path.default"
  module-path->require-path MP MP.

  % Remove duplicates from a list
  pred remove-duplicates i:list A, o:list A.
  remove-duplicates [] [].
  remove-duplicates [H|T] L :- std.mem! T H, remove-duplicates T L, !.
  remove-duplicates [H|T] [H|L] :- remove-duplicates T L.

  % Convert a contant to a fully qualified name
  pred constant->name i:constant, o:string.
  constant->name C N :-
    coq.gref->string (const C) N.
  
  % Extract the module part of the fully qualified name of a constant
  pred constant->module-path i:constant o:string.
  constant->module-path C MP :- 
    coq.gref->string (const C) CS,
    rex.replace "\.[^.]+$" "" CS MP.

  % Get the list of require modules from a cbv-reduction-definition entry
  pred cbv-reduction-definition->require-list i:prop, o:list string.
  cbv-reduction-definition->require-list (cbv-reduction-definition _NAME CONSTANTS) REQUIRES :-
    std.map CONSTANTS constant->module-path LM,
    std.map LM module-path->require-path LR,
    remove-duplicates LR REQUIRES.
  
  % output a "Require Import" command
  pred output-require i:out_stream, i:string.
  output-require OS RP :-
    output OS "Require Import ",
    output OS RP,
    output OS ".\n".
}}.

(** ** Elpi Command to add an entry into the module path -> require path database *)

Elpi Command cbv_add_module_mapping.
Elpi Accumulate Db cbv_symbol_generator.db.
Elpi Accumulate lp:{{
  main [str MP, str RP] :-
    coq.elpi.accumulate _ "cbv_symbol_generator.db" (clause _ (before "module-path->require-path.default") (module-path->require-path MP RP)),
    coq.say "Added module path mapping" MP "->" RP.
}}.
Elpi Typecheck.

(** ** Elpi Command to add a new reduction definition *)

Elpi Command cbv_add_reduction_definition.
Elpi Accumulate Db cbv_symbol_generator.db.
Elpi Accumulate lp:{{
  % Filter transparnt constants from module-items 
  pred module-item-filter-transparent-const-gref i:module-item, o:constant.
  module-item-filter-transparent-const-gref (gref (const X)) X :- not (coq.env.opaque? X).

  % Get a list of transparent definitions from a module
  pred module-get-transparent-definitions i:string, o:list constant.
  module-get-transparent-definitions MN LR :-
    coq.locate-module MN MP,
    coq.env.module MP L,
    std.map-filter L module-item-filter-transparent-const-gref LR.

  % Convert a - preferably fully qualified - name to a constant
  pred name->constant i:string, o:constant.
  name->constant N C :- coq.locate N (const C).
  name->constant N _ :- coq.error "name->constant: the given name" N "is not a constant!".

  % Append symbols from an argument string (either module or individual symbol prefixed with "ADD.") to a list of constants
  pred filter-items i:argument, i:list constant, o:list constant.
  % Individual symbols are prefixed with "ADD."
  filter-items (str NAME) LCI LCO :-
    rex.match "^ADD\\." NAME,
    rex.replace "^ADD\\." "" NAME NAMES,
    name->constant NAMES C,
    LCO = [C|LCI], !.
  % Removals (exclusions on the already constructed list) are prefixed with "REMOVE."
  filter-items (str NAME) LCI LCO :-
    rex.match "^REMOVE\\." NAME,
    rex.replace "^REMOVE\\." "" NAME NAMES,
    name->constant NAMES C,
    std.filter LCI (x\ not (x = C)) LCO, !.
  % Otherwise we habe a module
  filter-items (str NAME) LCI LCO :-
    module-get-transparent-definitions NAME LC,
    std.append LC LCI LCO.
  % In case this is not a string -> fail
  filter-items I _ _ :- coq.error "cbv_add_reduction_definition: illegal command line item (should all be strings)" I.

  main [str NAME|ENTRIES] :-
    std.fold ENTRIES [] filter-items CONSTANTS,
    coq.elpi.accumulate _ "cbv_symbol_generator.db" (clause _ (before "cbv-reduction-definition.fail") (cbv-reduction-definition NAME CONSTANTS)),
    coq.say "Added reduction definition" NAME "containing" {std.length CONSTANTS} "definitions."
    .
}}.
Elpi Typecheck.

(** ** Elpi Command to add write *all* defined reductions to a file in Elpi format *)

Elpi Command cbv_write_reduction_definitions.
Elpi Accumulate Db cbv_symbol_generator.db.
Elpi Accumulate lp:{{
  % output a constant
  pred output-constant i:out_stream, i:constant.
  output-constant OS C :-
    constant->name C N,
    output OS "  ",
    output OS N,
    output OS "\n".
  
  % Output a cbv-reduction-definition as cbv_expanded_reduction_definition
  pred output-cbv-reduction-definition i:out_stream, i:prop.
  output-cbv-reduction-definition OS (cbv-reduction-definition NAME CONSTANTS) :-
    output OS "\n",
    output OS "Elpi cbv_expanded_reduction_definition \"",
    output OS NAME,
    output OS "\"\n",
    std.forall CONSTANTS (output-constant OS),
    output OS ".\n".
  
  % Main function of command
  main [str FILEPATH] :-
    % Get list of reduction definitions
    std.findall (cbv-reduction-definition _ _) LRD,

    % Get list of Require commands from reduction definitions
    std.map LRD cbv-reduction-definition->require-list LLRP,
    std.flatten LLRP LRPD,
    remove-duplicates LRPD LRP,

    % Write Coq file
    open_out FILEPATH OSTREAM,
    output OSTREAM "(* This file has been auto-generated by elpi/cbv_symbol_lists_generator.v - DO NOT MODIFY! *)\n",
    output OSTREAM "Require Import elpi.elpi.\n",
    output OSTREAM "Require Import VST.elpi.cbv_symbol_lists_generated_definitions.\n",
    output OSTREAM "\n",
    std.forall LRP (output-require OSTREAM),
    std.forall LRD (output-cbv-reduction-definition OSTREAM),
    close_out OSTREAM
  .
}}.
Elpi Typecheck.

(** ** Elpi Command to add write *all* defined reductions to a file in Ltac2 format *)

Elpi Command cbv_write_reduction_definitions_ltac2.
Elpi Accumulate Db cbv_symbol_generator.db.
Elpi Accumulate lp:{{
  % output a constant
  pred output-constant i:out_stream, i:constant.
  output-constant OS C :-
    constant->name C N,
    output OS "  reference:(",
    output OS N,
    output OS ")".

  % Like std.forall but calls a second function without arguments between any two list elements
  pred forall-sep i:list A, i:(A -> prop), i:prop.
  forall-sep [] _ _.
  forall-sep [X] P _ :- P X, !.
  forall-sep [X|L] P S :- P X, S, forall-sep L P S.

  % Output a cbv-reduction-definition as cbv_expanded_reduction_definition
  pred output-cbv-reduction-definition i:out_stream, i:prop.
  output-cbv-reduction-definition OS (cbv-reduction-definition NAME CONSTANTS) :-
    output OS "\n",
    output OS "Ltac2 reduction_symbol_list_",
    output OS NAME,
    output OS "() : Std.reference list := [\n",
    forall-sep CONSTANTS (output-constant OS) (output OS ";\n"),
    output OS "\n].\n".

  % Main function of command
  main [str FILEPATH] :-
    % Get list of reduction definitions
    std.findall (cbv-reduction-definition _ _) LRD,

    % Get list of Require commands from reduction definitions
    std.map LRD cbv-reduction-definition->require-list LLRP,
    std.flatten LLRP LRPD,
    remove-duplicates LRPD LRP,

    % Write Coq file
    open_out FILEPATH OSTREAM,
    output OSTREAM "(* This file has been auto-generated by elpi/cbv_symbol_lists_generator.v - DO NOT MODIFY! *)\n",
    output OSTREAM "Require Import Ltac2.Ltac2.\n",
    output OSTREAM "\n",
    std.forall LRP (output-require OSTREAM),
    std.forall LRD (output-cbv-reduction-definition OSTREAM),
    close_out OSTREAM
  .
}}.
Elpi Typecheck.
