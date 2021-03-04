Require Import VST.floyd.base2.
Require Import VST.floyd.canon.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.entailer.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.call_lemmas.
Require Import VST.floyd.globals_lemmas.
Require Import VST.floyd.forward.
Import ListNotations.
Import LiftNotation.
Local Open Scope logic.

Declare Scope old_funspec_scope.
Delimit Scope old_funspec_scope with old_funspec.

Declare Scope formals.
Notation " a 'OF' ta " := (a%positive,ta%type) (at level 100, only parsing): formals.
Delimit Scope formals with formals.

Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default tx (fun x => P%assert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH' x : tx 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default tx (fun x => P%assert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%assert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%assert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%assert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%assert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0, x21 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0, x21 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 , x22 : t22 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21*t22)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0, x21 at level 0, x22 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 , x22 : t22 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec' ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21*t22)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0, x21 at level 0, x22 at level 0,
             P at level 100, Q at level 100) : old_funspec_scope.

Definition main_pre {Z: Type} (prog: Clight.program) (ora: Z) : globals -> environ -> mpred :=
 fun gv rho => !! (gv = globals_of_env rho) && (globvars2pred gv (prog_vars prog) * has_ext ora).

Lemma old_main_pre_eq:
 forall prog,  convertPre (nil,tint) globals (main_pre prog tt) = SeparationLogic.main_pre prog tt.
Proof.
intros.
unfold convertPre.
extensionality gv.
unfold SeparationLogic.main_pre, main_pre.
extensionality ae.
destruct ae as [g args].
simpl.
apply pred_ext; normalize.
-
destruct args; inv H.
simpl. normalize.
apply derives_refl'.
f_equal.
simpl.
unfold globvars2pred.
unfold lift2.
simpl.
rewrite prop_true_andp; auto.
-
simpl.
unfold globvars2pred.
unfold lift2.
normalize.
simpl.
rewrite prop_true_andp by (split; auto).
auto.
Qed.

Ltac rewrite_old_main_pre ::= rewrite ?old_main_pre_eq; unfold convertPre.

(*Notation "'main_pre'" := (old_main_pre) : old_funspec_scope. *)
(*
Definition main_pre := @SeparationLogic.main_pre.
Arguments main_pre {Z} _ _ _.
*)

Lemma convertPre_helper1:
  forall P1 P Q R x,
   !! P1 && PROPx P (LOCALx Q (SEPx R)) x = 
   PROPx P ((!!P1 && (local (fold_right (liftx and) (liftx True) (map locald_denote Q)))) && SEPx R) x.
Proof.
intros.
unfold PROPx, LOCALx; simpl; normalize.
f_equal; auto.
f_equal; auto.
apply prop_ext; intuition.
Qed.

Definition all_defined P R vals :=
andp (!! fold_right and True P) (fold_right_sepcon R) |-- 
  !! (fold_right and True (map (fun v => v<>Vundef) vals)).

Lemma Forall_fold_right:
 forall {A} (f: A -> Prop) al, Forall f al = fold_right and True (map f al).
Proof.
induction al; simpl; intros; apply prop_ext; split; intros ?; auto.
inv H; split; auto.
rewrite <- IHal; auto.
destruct H; constructor; auto.
rewrite IHal; auto.
Qed.


Lemma convertPre_helper2:
  forall P1 P Q R G L x y,
  (Forall (fun v : val => v <> Vundef) L ->
   !!P1 && (local (fold_right (liftx and) (liftx True) (map locald_denote Q)) x) =
      !! (snd y = L) &&
         local (fold_right (liftx and) (liftx True) (map locald_denote (map gvars G)))
                   (Clight_seplog.mkEnv (fst y) [] [])) ->
   all_defined P R L ->
   !! P1 && PROPx P (LOCALx Q (SEPx R)) x 
   = PROPx P (LAMBDAx G L (SEPx R)) y.
Proof.
intros.
unfold PROPx,PARAMSx, GLOBALSx, LOCALx, SEPx.
red in H0.
unfold local, lift1.
simpl.
unfold_lift.
apply pred_ext; normalize;
rewrite prop_true_andp in H0 by auto.
-
clear P H2.
rewrite prop_true_andp in H by auto.
clear P1 H1.
eapply derives_trans.
apply andp_right; [apply H0 | apply derives_refl].
clear H0.
Intros.
rewrite <- Forall_fold_right in H0.
specialize (H H0); clear H0.
unfold local, lift1 in H.
normalize in H.
apply derives_trans with (fold_right_sepcon R && TT).
normalize.
rewrite H; clear H.
normalize.
apply andp_right; [ | apply derives_refl].
apply prop_right; split; auto.
-
unfold argsassert2assert.
apply andp_right; [ | apply derives_refl].
eapply derives_trans.
apply andp_right; [apply H0 | apply derives_refl].
clear H0.
Intros.
rewrite <- Forall_fold_right in H0.
specialize (H H0); clear H0.
unfold local, lift1 in H.
normalize in H.
apply derives_trans with (fold_right_sepcon R && TT).
normalize.
rewrite <- H; clear H.
normalize.
apply prop_right; split; auto.
Qed.


Fixpoint findPARAM i D :=
 match D with
 | temp j v :: D' => if ident_eq i j then v else findPARAM i D'
 | _ :: D' => findPARAM i D'
 | nil => Vundef
 end.

Fixpoint makePARAMS (L: list (ident * type)) D :=
 match L with
 | (i,_)::L' => findPARAM i D :: makePARAMS L' D
 | nil => nil
 end.

Fixpoint temps_of_localdef (dl: list localdef) : list ident :=
 match dl with
 | temp i _ :: dl' => i :: temps_of_localdef dl'
 | _ :: dl' => temps_of_localdef dl'
 | nil => nil
 end.

Definition no_locals_localdefs : list localdef -> Prop :=
 Forall (fun d => match d with lvar _ _ _ => False | _ => True end).
Definition no_globals_localdefs : list localdef -> Prop :=
 Forall (fun d => match d with gvars _ => False | _ => True end).

Fixpoint globals_localdefs (lds: list localdef) : list globals :=
 match lds with
 | gvars gv :: lds' => gv :: globals_localdefs lds'
 | _ :: lds' => globals_localdefs lds'
 | nil => nil
 end.

Lemma field_compatible_Vundef : forall {cs: compspecs} t gfs, 
   field_compatible t gfs Vundef -> False.
Proof.
intros.
destruct H.
contradiction H.
Qed.

Lemma Vptrofs_neq_Vundef: forall x, Vptrofs x <> Vundef.
Proof.
intros.
unfold Vptrofs.
destruct Archi.ptr64; congruence.
Qed.

Lemma Vbyte_neq_Vundef: forall x, Vbyte x <> Vundef.
Proof.
intros.
unfold Vbyte. congruence.
Qed.

Lemma nullval_neq_Vundef: nullval <> Vundef.
Proof.
intro; inv H.
Qed.

Ltac prove_all_defined := 
 red; simpl makePARAMS;
lazymatch goal with |- !! ?A _ _ _ && _ |-- !! ?B=>
 let a := fresh "a" in let b := fresh "b" in 
  set (b:=B); set (a:=A); 
  unfold fold_right in a;
 simpl in b;
  unfold fold_right_sepcon;
  subst a b; cbv beta iota zeta
end;
pull_out_props;
saturate_local;
apply prop_right; repeat split;
let H := fresh in 
try congruence; 
try apply Vptrofs_neq_Vundef;
try apply Vbyte_neq_Vundef;
try apply nullval_neq_Vundef;
try (intro H; rewrite H in *;
      (contradiction || eapply field_compatible_Vundef; eassumption));
match goal with  |- ?A <> Vundef =>
  fail 100 "From assumptions above the line and PROP and SEP clauses in precondition, cannot prove LOCAL variable" A "<>Vundef"
end.

Ltac convertPreElim' := 
unfold convertPre;
let ae := fresh "ae" in extensionality ae;
let g := fresh "g" in let args := fresh "args" in destruct ae as [g args];
lazymatch goal with |-
  andp _ (PROPx _ (LOCALx ?Q _) _)  =  PROPx _ (LAMBDAx ?G _ _) _ =>
 unify G (globals_localdefs Q)
end;
apply convertPre_helper2;
 [intro;
  simpl fst; simpl snd;
  match goal with |- !! (_ = Datatypes.length ?L) && local (fold_right _ _ (map _ ?D)) _=
                              !! (args = ?A) && local (fold_right _ _ (map _ (map _ ?G))) _ => 
  let p := constr:(makePARAMS L D) in
  let p := eval simpl in p in 
    unify A p
   end
  | ];  
  [ | prove_all_defined ];
unfold local, lift1; unfold_lift; rewrite <- !prop_and; apply f_equal;
let H0 := fresh in let H1 := fresh  in 
apply prop_ext; split; intros [H0 H1];
[ simpl in H0;
  repeat (destruct args as [ | ? args]; [discriminate H0 | ]);
  destruct args; [clear H0 | inv H0];
  simpl in H1; unfold_lift in H1;
  unfold eval_id, env_set in H1;
  simpl in H1; 
  decompose [and] H1; clear H1; subst;
  simpl;
  repeat split; auto
| subst args; 
  simpl in H1; unfold_lift in H1;
  unfold eval_id, env_set in H1;
  simpl in H1; 
  decompose [and] H1; clear H1; subst;
  simpl; unfold_lift; unfold eval_id, env_set; simpl;
  repeat match goal with H: Forall _ _ |- _ => inv H end;
  repeat split; auto
].

Ltac convertPreElim := 
  match goal with |- convertPre _ _ _ _ = _ => idtac end;
  convertPreElim' || fail 100 "Could not convert old-style precondition to new-style".

Ltac try_convertPreElim ::= 
  lazymatch goal with
  | |- convertPre _ _ _ _ = _ =>  convertPreElim
  | |- _ => reflexivity
  end.

Lemma convertPre_helper3:
  forall (fsig: funsig) P Q R vals gvs,
  makePARAMS (fst fsig) Q = vals ->
  list_norepet (temps_of_localdef Q) ->
  list_norepet (map fst (fst fsig)) ->
  (forall i, In i (temps_of_localdef Q) <-> In i (map fst (fst fsig))) ->
  no_locals_localdefs Q ->
  globals_localdefs Q = gvs ->
  all_defined P R vals ->
  (fun ae : argsEnviron => !! (Datatypes.length (snd ae) = Datatypes.length (fst fsig)) &&
      (PROPx P (LOCALx Q (SEPx R)))
        (make_args
           (map fst (fst fsig))
           (snd ae)
           (mkEnviron (fst ae) (Map.empty (block * type))
              (Map.empty val)))) =
  PROPx P (PARAMSx vals (GLOBALSx gvs (SEPx R))).
Proof.
intros. 
rename H3 into Hloc. rename H4 into Hglob. rename H5 into Hdef.
extensionality ae.
apply convertPre_helper2; auto.
clear Hdef; intros Hdef.
unfold local, lift1.
unfold_lift.
simpl.
normalize.
f_equal.
apply prop_ext.
destruct ae as [g args].
simpl snd.
simpl fst.
(*

split.
-
clear Hloc Hglob Hdef.
intros [? ?].
simpl in *.
subst vals.
revert H1 args H3 Q H0 H2 H4;
induction (fst fsig) as [|[??]];
simpl; intros.
destruct args; inv H3; auto.
split; auto.
admit.  (* plausible *)
destruct args as [ | a1 args]. inv H3.
simpl in H3. injection H3 as H3.
pose (Q' := remove_localdef_temp i Q).
inv H1.
specialize (IHl H7 args H3 Q').
spec IHl.  admit.  (* easy *)
spec IHl.
{ clear IHl H4. intros.
  destruct (ident_eq i0 i). subst.
 split; intros; try contradiction.
 elimtype False; clear - H. subst Q'.
 admit. (* easy *)
 specialize (H2 i0). 
 assert (In i0 (temps_of_localdef Q) <-> In i0 (temps_of_localdef Q'))
   by admit. (* easy *)
rewrite <- H.
rewrite H2.
split; intros; auto. destruct H1; auto. subst; contradiction.
}
f_equal.
+
assert (In i (temps_of_localdef Q)).
rewrite (H2 i); auto.
clear - H4 H.
induction Q; simpl in *; auto; try contradiction.
destruct a.
*
destruct H4.
split.
--
if_tac.
subst i0.
hnf in H0.
unfold_lift in H0.
destruct H0.
 unfold eval_id, env_set in H0. simpl in H0.
rewrite Map.gss in H0. simpl in H0. auto.
apply IHQ; auto.
destruct H; subst; try contradiction; auto.
*
apply IHQ; auto.
destruct H4; auto.
*
apply IHQ; auto.
destruct H4; auto.
+
replace (makePARAMS l Q) with (makePARAMS l Q').
apply IHl.
{
clear - H4.
induction Q; simpl in *; auto.
destruct a; simpl in *; auto.
-
destruct (ident_eq i i0).
subst i0.
apply IHQ.
unfold_lift in H4;
destruct H4.
apply H0.
unfold_lift in H4.
destruct H4.
destruct H.
unfold eval_id, env_set in H. simpl in H.
rewrite Map.gso in H by auto.
subst Q'; simpl.
split.
unfold_lift.
split; auto.
auto.
-
destruct H4.
split; auto.
-
destruct H4.
split; auto.
}
clear - H6 H7.
revert i Q' H6.
induction l; simpl; intros; auto.
inv H7.
apply Decidable.not_or in H6.
destruct H6.
destruct a.
simpl in H,H1.
f_equal; auto.
clear - H.
induction Q; simpl; auto.
destruct a; auto.
if_tac; subst.
rewrite if_false by auto. auto.
if_tac; subst; auto.
simpl. rewrite if_true by auto; auto.
simpl.
rewrite if_false by auto; auto.
-
intros.
subst vals args.
split; [clear; induction (fst fsig) as [|[??]]; simpl; auto | ].
revert Q Hloc Hglob Hdef H0 H2; 
induction (fst fsig) as [|[??]]; simpl; intros.
+
clear - Hloc Hglob Hdef H2.
assert (temps_of_localdef Q = nil).
admit. (* easy. *)
clear - Hloc Hglob H.
induction Q; simpl; auto.
destruct a; simpl in *; unfold_lift; auto; try congruence.
inv Hloc; contradiction.
inv Hglob; contradiction.
+
simpl in H1.
inv H1.
inv Hdef.
rename H3 into Hdef1; rename H6 into Hdef.
spec IHl; auto.
specialize (IHl (remove_localdef_temp i Q)).
spec IHl.  admit. (* easy *)
spec IHl.  admit. (* easy *)
spec IHl.  admit. (* easy *)
spec IHl.  admit. (* easy *)
spec IHl.
{ intros. specialize (H2 i0). 
  destruct (ident_eq i i0). subst.
  split; intros; try contradiction.
  elimtype False; clear - H. admit. (* easy *)
  clear - H2 n.
  split; intros. 
  assert (In i0 (temps_of_localdef Q)) by admit. (* easy *)
  intuition.
 destruct H2. spec H1; auto.
  clear - H1 n. 
  admit. (* easy *)
}
assert (In i (temps_of_localdef Q)).
  clear - H2; pose proof (H2 i); intuition.
clear - IHl H Hloc Hglob Hdef Hdef1 H0.
assert (fold_right
  (fun (x x0 : environ -> Prop) (x1 : environ) => x x1 /\ x0 x1)
  (fun _ : environ => True)
  (map locald_denote (temp i (findPARAM i Q) :: remove_localdef_temp i Q))
  (env_set
     (make_args (map fst l) (makePARAMS l Q)
        (mkEnviron g (Map.empty (block * type)) (Map.empty val)))
     i (findPARAM i Q))).
*
split.
hnf. unfold_lift; simpl.
unfold eval_id, env_set. simpl. rewrite Map.gss. split; auto.
assert (~ In i (temps_of_localdef (remove_localdef_temp i Q))) by admit. (* easy *)
assert (Hloc': no_locals_localdefs (remove_localdef_temp i Q)) by admit. (* easy *)
assert (Hglob': no_globals_localdefs (remove_localdef_temp i Q)) by admit. (* easy *)
assert (list_norepet (temps_of_localdef (remove_localdef_temp i Q))) by admit. (* easy *)

clear - IHl H1 Hloc' Hglob' Hdef H2.
assert 
replace (makePARAMS l Q) with (makeParams l ((

induction (remove_localdef_temp i Q).
simpl. auto.
inv Hloc'. inv Hglob'.
destruct a; try contradiction.
fold (no_locals_localdefs l0) in H4.
fold (no_globals_localdefs l0) in H6.
clear H3 H5.
inv H2.
simpl in H1.
apply Decidable.not_or in H1.
destruct H1.
destruct IHl.
spec IHl0. {
  clear - H2 H3.
  admit.  (* looks fine *)
}
spec IHl0; auto.
spec IHl0; auto.
spec IHl0; auto.
spec IHl0; auto.
split.
--
hnf. unfold_lift.
hnf in H1.
unfold_lift in H1.
destruct H1; split; auto.
unfold eval_id, env_set. simpl. rewrite Map.gso by auto.
rewrite H1; clear H1.
*)
Admitted. (* might be true *)


Ltac prove_norepet := 
   clear; repeat constructor; simpl; intros ?H;
     repeat match goal with H: _ \/ _ |- _ => destruct H end;
      repeat match goal with H: _ = _ |- _ => inv H end; auto.


Ltac start_func_convert_precondition ::=
erewrite convertPre_helper3;
 [ 
 | reflexivity || fail 100 "makePARAMS filed in start_func_convert_precondition"
 | prove_norepet || fail 100 "repeated temp-identifier in LOCAL clause"
 | prove_norepet || fail 100 "repeated formal parameter in funsig"
 | intros; compute; tauto || fail 100 "temp-ids of LOCAL not the same as temp-ids of funsig formal parameters"
 | repeat constructor; auto || fail 100 "unexpected lvar in LOCAL"
 | reflexivity || fail 100 "unexpected problem with gvars in old-style LOCAL"
 | prove_all_defined
 ];
 simpl makePARAMS.
