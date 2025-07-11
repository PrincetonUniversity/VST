From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/test_f_temps.c]. *)
Section code.
  Definition file_0 : string := "examples/test_f_temps.c".
  Definition loc_4 : location_info := LocationInfo file_0 14 4 14 14.
  Definition loc_5 : location_info := LocationInfo file_0 15 4 15 18.
  Definition loc_6 : location_info := LocationInfo file_0 15 11 15 17.
  Definition loc_7 : location_info := LocationInfo file_0 15 11 15 12.
  Definition loc_8 : location_info := LocationInfo file_0 15 11 15 12.
  Definition loc_9 : location_info := LocationInfo file_0 15 15 15 17.
  Definition loc_10 : location_info := LocationInfo file_0 14 12 14 13.

  (* Definition of function [main]. *)
  Definition impl_main : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        Return (i2v 0 i32)
      ]> $∅
    )%E
  |}.

  (* Definition of function [f_temps]. *)
  Definition impl_f_temps : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("a", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "a" <-{ IntOp i32 } LocInfoE loc_10 (i2v 1 i32) ;
        locinfo: loc_5 ;
        Return (LocInfoE loc_6 ((LocInfoE loc_7 (use{IntOp i32} (LocInfoE loc_8 ("a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_9 (i2v 41 i32))))
      ]> $∅
    )%E
  |}.
End code.
