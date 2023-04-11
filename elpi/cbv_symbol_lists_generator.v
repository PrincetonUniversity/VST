(** * Create file with hand craftes symbol lists *)

(** ATTENTION: running the generator require coq-elpi >= 1.16.0. *)
(** For this reason we currently generate a checked in file with symbol lists. *)

Require Import elpi.elpi.
Require Import VST.elpi.cbv_symbol_lists_generator_definitions.

(** ** Require all modules, for which we want to create symbol lists below *)

From VST Require floyd.proofauto floyd.library.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.

(** ** Map modules which are not file level modules to the corresponding file level module *)

Elpi cbv_add_module_mapping compcert.lib.Maps.PTree  compcert.lib.Maps.
Elpi cbv_add_module_mapping VST.veric.mpred.Map      VST.veric.mpred.
Elpi cbv_add_module_mapping Coq.ZArith.BinInt.Z      ZArith.BinInt.
Elpi cbv_add_module_mapping Coq.PArith.BinPos.Pos    PArith.BinPos.

(** ** Add definitions of reduction symbol lists *)

(**
The first entry in the list is the name of the generated delta reduction symbol list (used with "cbv_nr" tactic).
Further entries are intepreted as follows:
- if prefixed with "ADD." the entry adds a single (preferably fully ualified) symbol to the delta reduction symbol list
- if prefixed with "REMOVE." the entry removes a single (preferably fully ualified) symbol from the (so far constructed) delta reduction symbol listt
- otherwise the entry is intepreted as module path and all transparanet definitions from the module (not recursive) are added to the delta reduction symbol list
- if the module path of a module or an individual symbol is not a file level module (one which can be loaded with "Require") a name mapping must be given with cbv_add_module_mapping (see above).
*)

Elpi cbv_add_reduction_definition
  "msubst_denote_tc_assert"
  compcert.cfrontend.Clight
  compcert.cfrontend.Cop
  compcert.cfrontend.Ctypes
  compcert.export.Ctypesdefs
  compcert.lib.Maps.PTree
  compcert.aarch64.Archi
  VST.floyd.local2ptree_eval
  VST.floyd.local2ptree_typecheck
  VST.veric.Clight_Cop2
  VST.veric.expr
  VST.veric.lift
  VST.veric.mpred
  REMOVE.VST.veric.mpred.mpred
  VST.veric.mpred.Map
  VST.veric.SeparationLogic
  VST.veric.val_lemmas
  .

Elpi cbv_add_reduction_definition
  "zarith"
  ZArith.BinInt.Z
  PArith.BinPos.Pos
  .

(** ** Generate file with expaned reduction definitions *)

Elpi cbv_write_reduction_definitions "elpi/cbv_symbol_lists_generated.v".
Elpi cbv_write_reduction_definitions_ltac2 "ltac2/cbv_symbol_lists_generated.v".
