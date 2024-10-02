From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/test.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/test.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_13 : location_info := LocationInfo file_1 12 4 12 14.
  Definition loc_14 : location_info := LocationInfo file_1 13 4 13 15.
  Definition loc_15 : location_info := LocationInfo file_1 14 4 14 17.
  Definition loc_16 : location_info := LocationInfo file_1 14 11 14 16.
  Definition loc_17 : location_info := LocationInfo file_1 14 11 14 12.
  Definition loc_18 : location_info := LocationInfo file_1 14 11 14 12.
  Definition loc_19 : location_info := LocationInfo file_1 14 15 14 16.
  Definition loc_20 : location_info := LocationInfo file_1 14 15 14 16.
  Definition loc_21 : location_info := LocationInfo file_1 13 12 13 14.
  Definition loc_24 : location_info := LocationInfo file_1 12 12 12 13.

  (* Definition of function [copy_alloc_id]. *)
  Definition impl_copy_alloc_id : function := {|
    f_args := [
      ("to", it_layout uintptr_t);
      ("from", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{IntOp uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{PtrOp} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

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
        "a" <-{ IntOp i32 } LocInfoE loc_24 (i2v 1 i32) ;
        "b" <-{ IntOp i32 } LocInfoE loc_21 (i2v 41 i32) ;
        locinfo: loc_15 ;
        Return (LocInfoE loc_16 ((LocInfoE loc_17 (use{IntOp i32} (LocInfoE loc_18 ("a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_19 (use{IntOp i32} (LocInfoE loc_20 ("b"))))))
      ]> $∅
    )%E
  |}.
End code.
