Require Import reify.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import reverse_defs.

Local Open Scope logic.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Goal True.
reify_typ (Values.val -> Values.val).

Goal forall (sh : share) (contents : list val),
  writable_share sh ->
  forall (cts1 cts2 : list val) (w v : val),
    isptr v ->
   exists (a : Share.t) (b : val),
     PROP  (contents = (*rev*) cts1 ++ cts2)
     LOCAL  (tc_environ Delta2; `(eq w) (eval_id _w); 
     `(eq v) (eval_id _v))
     SEP  (`(lseg LS sh cts1 w nullval); `(lseg LS sh cts2 v nullval))
     |-- local (tc_expr Delta2 (Etempvar _v (tptr t_struct_list))) &&
         (`(field_at a t_struct_list (_tail::nil) b)
            (eval_expr (Etempvar _v (tptr t_struct_list))) * TT).
Proof.
intros. eexists. eexists. go_lower0.
reify_expr_tac.
Abort.

Goal forall n v, `(eq v) (eval_id _v) = n.
 intros.
Abort.
(* reify_expr_tac.*)
Definition lift_eq_val2  (a b : environ -> val) := (`eq a b : environ -> Prop).
Definition lift_eq_val a (b : environ -> val) := (`(eq a) b : environ -> Prop).
Definition sp (s : mpred):= `s.

Ltac replace_lift :=
repeat
match goal with
| [ |- context [`eq ?A ?B]] => change (`eq A B) with (lift_eq_val2 A B)
| [ |- context [`(eq ?A) ?B]] => change (`(eq A) B) with (lift_eq_val A B)
end;
repeat
match goal with
| [ |- context [`?S]] => change (`S) with (sp S)
end.

Existing Instance NullExtension.Espec.

Goal forall p contents sh,
semax Delta2
     (PROP  ()
      LOCAL  (`(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))
     (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        Sskip) 
(normal_ret_assert (PROP  ()
      LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _w); 
      `(eq p) (eval_id _p))  SEP  (`(lseg LS sh contents p nullval)))).
intros.
replace_lift.
reify_expr_tac.
Abort.

Goal
  forall (sh : share) (contents : list int),
  PROP  ()
  LOCAL  (tc_environ Delta;
         `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list)));
         `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
  SEP  (`(lseg LS sh (map Vint contents)) (eval_id _p) `nullval)
          |-- EX  cts : list int,
  PROP  ()
  LOCAL 
        (`(eq (Vint (Int.sub (sum_int contents) (sum_int cts)))) (eval_id _s))
  SEP  (TT; `(lseg LS sh (map Vint cts)) (eval_id _t) `nullval).
Proof.
intros. 
replace_lift.
reify_expr_tac.
go_lower0.
reify_expr_tac.
Abort.


Goal
 forall (i : int) (cts : list int) (t0 y : val) (sh : share)
     (contents : list int),
   exists a, exists b,
   PROP  ()
   LOCAL  (tc_environ Delta; `(eq t0) (eval_id _t);
   `(eq (Vint (Int.sub (sum_int contents) (sum_int (i :: cts)))))
     (eval_id _s))
   SEP 
   (`(field_at sh t_struct_list _head (Vint i))
      (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(field_at sh t_struct_list _tail y)
     (fun _ : lift_S (LiftEnviron mpred) => t0);
   `(lseg LS sh (map Vint cts)) `y `nullval; TT)
   |-- local (tc_expr Delta (Etempvar _t (tptr t_struct_list))) &&
       (`(field_at a t_struct_list _head b)
          (eval_expr (Etempvar _t (tptr t_struct_list))) * TT).
Proof.
intros. 
eexists. eexists.
go_lower0.