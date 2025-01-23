(* export some of the same files as SeparationLogic.v, without going through all of VeriC *)
From compcert.cfrontend Require Export Ctypes.
From VST.sepcomp Require Export extspec.
From VST.veric Require Export Clight_base Cop2 Clight_Cop2 val_lemmas res_predicates mpred seplog tycontext lifting_expr lifting mapsto_memory_block.
From VST.floyd Require Export functional_base canon client_lemmas nested_field_lemmas.
Export Address.
