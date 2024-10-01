From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/test_f_temps.c]. *)
Section code.
  Definition file_0 : string := "examples/test_f_temps.c".
  Definition loc_4 : location_info := LocationInfo file_0 10 4 10 14.
  Definition loc_5 : location_info := LocationInfo file_0 11 4 11 15.
  Definition loc_6 : location_info := LocationInfo file_0 12 4 12 17.
  Definition loc_7 : location_info := LocationInfo file_0 12 11 12 16.
  Definition loc_8 : location_info := LocationInfo file_0 12 11 12 12.
  Definition loc_9 : location_info := LocationInfo file_0 12 11 12 12.
  Definition loc_10 : location_info := LocationInfo file_0 12 15 12 16.
  Definition loc_11 : location_info := LocationInfo file_0 12 15 12 16.
  Definition loc_12 : location_info := LocationInfo file_0 11 12 11 14.
  Definition loc_15 : location_info := LocationInfo file_0 10 12 10 13.

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
      ("b", it_layout i32);
      ("a", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "a" <-{ IntOp i32 } LocInfoE loc_15 (i2v 1 i32) ;
        "b" <-{ IntOp i32 } LocInfoE loc_12 (i2v 41 i32) ;
        locinfo: loc_6 ;
        Return (LocInfoE loc_7 ((LocInfoE loc_8 (use{IntOp i32} (LocInfoE loc_9 ("a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_10 (use{IntOp i32} (LocInfoE loc_11 ("b"))))))
      ]> $∅
    )%E
  |}.
End code.
