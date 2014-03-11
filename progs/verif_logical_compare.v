Require Import floyd.proofauto.
Require Import progs.logical_compare.

Local Open Scope logic.

Definition do_or_spec :=
 DECLARE _do_or
  WITH a: int, b : int
  PRE [ _a OF tbool, _b OF tbool ]
         PROP () LOCAL (`(eq (Vint a)) (eval_id _a); `(eq (Vint b)) (eval_id _b)) SEP (TT)
  POST [ tbool ]  
        local(`eq retval `(logical_or_result tbool (Vint a) tbool (Vint b))).

Definition do_and_spec :=
 DECLARE _do_and
  WITH a: int, b : int
  PRE [ _a OF tbool, _b OF tbool ]
         PROP () LOCAL (`(eq (Vint a)) (eval_id _a); `(eq (Vint b)) (eval_id _b)) SEP (TT)
  POST [ tbool ]  
        local(`eq retval `(logical_and_result tbool (Vint a) tbool (Vint b))).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := 
    do_or_spec :: do_and_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma or_one_zero :
forall r a b, 
Vint r = logical_or_result tbool (Vint a) tbool (Vint b) ->
Vint (if Int.eq r Int.zero then Int.zero else Int.one) = Vint r.
Proof.
intros. unfold logical_or_result in *. simpl in *.
if_tac in H. inv H. auto.
if_tac in H. inv H; auto.
inv H. auto.
Qed.

Lemma and_one_zero :
forall r a b, 
Vint r = logical_and_result tbool (Vint a) tbool (Vint b) ->
Vint (if Int.eq r Int.zero then Int.zero else Int.one) = Vint r.
Proof.
intros. unfold logical_and_result in *. simpl in *.
repeat if_tac in H; inv H; auto.
Qed.

Lemma body_do_or: semax_body Vprog Gtot f_do_or do_or_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
forward.
entailer!.
apply orp_right2. auto.
forward. rewrite <- H. 
eapply or_one_zero; eauto.
Qed.

Lemma body_do_and: semax_body Vprog Gtot f_do_and do_and_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
forward.
entailer!.
apply orp_right2. auto.
forward. rewrite <- H. 
eapply and_one_zero; eauto.
Qed.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
forward.
unfold main_post.
unfold TT. 
simpl.
apply prop_right.
auto.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons; [ reflexivity | apply body_do_or | ].
apply semax_func_cons; [ reflexivity | apply body_do_and | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

