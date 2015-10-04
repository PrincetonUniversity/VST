Module CompcertLibraries.
Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Maps.
Require Export compcert.lib.Integers.
End CompcertLibraries.

Module CompcertCommon.
Require Export compcert.common.Events.
Require Export compcert.common.Memory.
Require Export compcert.common.Values.
Require Export compcert.common.AST.
Require Export compcert.common.Globalenvs.
End CompcertCommon.

Module CompcertAll.
Export CompcertLibraries.
Export CompcertCommon.
End CompcertAll.