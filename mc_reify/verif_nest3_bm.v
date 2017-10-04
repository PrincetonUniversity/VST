Require Import VST.floyd.proofauto.
Require Import VST.progs.nest3.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_c, p: val
  PRE  []
        PROP  ()
        LOCAL (var _p t_struct_c p)
        SEP   (`(data_at Ews t_struct_c (repinj _ v) p))
  POST [ tint ]
        PROP  ()
        LOCAL (var _p t_struct_c p; temp 1%positive (Vint (snd (snd (snd v)))))
        SEP   (`(data_at Ews t_struct_c (repinj _ v) p)).

Definition update222 (i: int) (v: reptype' t_struct_c) : reptype' t_struct_c :=
   (fst v, (fst (snd v), (fst (snd (snd v)), i))).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_c, p : val
  PRE  [ _i OF tint ]
        PROP ()
        LOCAL(temp _i (Vint i); var _p t_struct_c p)
        SEP(`(data_at Ews t_struct_c (repinj _ v) p))
  POST [ tvoid ]
        `(data_at Ews t_struct_c (repinj _ (update222 i v)) p).

Definition multi_command_spec :=
 DECLARE _multi_command
  WITH i111: int,
       i112: int,
       i121: int,
       i122: int,
       i211: int,
       i212: int,
       i221: int,
       i222: int,
       p: val
  PRE  []
        PROP ()
        LOCAL(var _p t_struct_c p)
        SEP(`(data_at Ews t_struct_c
               (repinj t_struct_c (((i111, i112), (i121, i122)), ((i211, i212), (i221, i222)))) p))
  POST [ tvoid ]
            `(data_at Ews t_struct_c
               (repinj t_struct_c (((i111, i112), (i121, i122)),
                          ((Int.add i122 (Int.repr 4), Int.add i121 (Int.repr 3)),
                           (Int.add i112 (Int.repr 2), Int.add i111 (Int.repr 1))))) p).

Definition multi_command_spec' :=
 DECLARE _multi_command
  WITH i111: int,
       i112: int,
       i121: int,
       i122: int,
       i211: int,
       i212: int,
       i221: int,
       i222: int,
       p: val,
       q: val
  PRE  []
        PROP ()
        LOCAL(var _p t_struct_c p)
        SEP(`(data_at Ews t_struct_c (default_val _) q);
            `(data_at Ews t_struct_c
               (repinj t_struct_c (((i111, i112), (i121, i122)), ((i211, i212), (i221, i222)))) p))
  POST [ tvoid ]
            `(data_at Ews t_struct_c (default_val _) q) *
            `(data_at Ews t_struct_c
               (repinj t_struct_c (((i111, i112), (i121, i122)),
                          ((Int.add i122 (Int.repr 4), Int.add i121 (Int.repr 3)),
                           (Int.add i112 (Int.repr 2), Int.add i111 (Int.repr 1))))) p).

Definition multi_command_s_spec :=
 DECLARE _multi_command_s
  WITH p0: val,
       p1: val,
       p2: val,
       p3: val,
       p4: val,
       p5: val,
       p6: val,
       p7: val
  PRE  []
        PROP ()
        LOCAL(var _p0 tint p0;
              var _p1 tint p1;
              var _p2 tint p2;
              var _p3 tint p3;
              var _p4 tint p4;
              var _p5 tint p5;
              var _p6 tint p6;
              var _p7 tint p7)
        SEP(`(data_at Ews tint (Vint (Int.repr 0)) p0);
            `(data_at Ews tint (Vint (Int.repr 0)) p1);
            `(data_at Ews tint (Vint (Int.repr 0)) p2);
            `(data_at Ews tint (Vint (Int.repr 0)) p3);
            `(data_at Ews tint (Vint (Int.repr 0)) p4);
            `(data_at Ews tint (Vint (Int.repr 0)) p5);
            `(data_at Ews tint (Vint (Int.repr 0)) p6);
            `(data_at Ews tint (Vint (Int.repr 0)) p7))
  POST [ tvoid ]
        PROP ()
        LOCAL(var _p0 tint p0;
              var _p1 tint p1;
              var _p2 tint p2;
              var _p3 tint p3;
              var _p4 tint p4;
              var _p5 tint p5;
              var _p6 tint p6;
              var _p7 tint p7)
        SEP(`(data_at Ews tint (Vint (Int.repr 0)) p0);
            `(data_at Ews tint (Vint (Int.repr 0)) p1);
            `(data_at Ews tint (Vint (Int.repr 0)) p2);
            `(data_at Ews tint (Vint (Int.repr 0)) p3);
            `(data_at Ews tint (Vint (Int.repr 4)) p4);
            `(data_at Ews tint (Vint (Int.repr 3)) p5);
            `(data_at Ews tint (Vint (Int.repr 2)) p6);
            `(data_at Ews tint (Vint (Int.repr 1)) p7)).

Definition Vprog : varspecs := (_p, t_struct_c)::
                               (_p0, tint)::
                               (_p1, tint)::
                               (_p2, tint)::
                               (_p3, tint)::
                               (_p4, tint)::
                               (_p5, tint)::
                               (_p6, tint)::
                               (_p7, tint)::
                               nil.

Definition Gprog : funspecs :=
    multi_command_s_spec::multi_command_spec::nil.

Require Import Timing.
(*
Ltac lforward :=
start_timer "Forward";
forward.forward;
stop_timer "Forward".

Clear Timing Profile.

Lemma body_multi_command: semax_body Vprog Gprog f_multi_command multi_command_spec.
Proof.
  start_function.
start_timer "T08a Folded Ltac".
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' x|].
  simpl upd_reptype.
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
stop_timer "T08a Folded Ltac".
  forward.forward. (* return *)
Qed.

Print Timing Profile.
*)

(*
Lemma body_multi_command2: semax_body Vprog Gprog f_multi_command multi_command_spec.
Proof.
  start_function.
  unfold_data_at 1%nat.
  unfold_field_at 1%nat.
  unfold_field_at 3%nat.
  unfold_field_at 1%nat.
  unfold_field_at 3%nat.
  unfold_field_at 5%nat.
  unfold_field_at 7%nat.
start_timer "T08a Unfolded Ltac".
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
stop_timer "T08a Unfolded Ltac".
  forward.forward. (* return *)
  unfold_data_at 1%nat.
  unfold_field_at 9%nat.
  unfold_field_at 11%nat.
  unfold_field_at 9%nat.
  unfold_field_at 11%nat.
  unfold_field_at 13%nat.
  unfold_field_at 15%nat.
  entailer!.
Qed.

Lemma body_multi_command3: semax_body Vprog Gprog f_multi_command multi_command_spec'.
Proof.
  start_function.
  unfold_data_at 1%nat.
  unfold_data_at 1%nat.
  unfold_field_at 1%nat.
  unfold_field_at 3%nat.
  unfold_field_at 5%nat.
  unfold_field_at 7%nat.
  unfold_field_at 1%nat.
  unfold_field_at 3%nat.
  unfold_field_at 5%nat.
  unfold_field_at 7%nat.
  unfold_field_at 9%nat.
  unfold_field_at 11%nat.
  unfold_field_at 13%nat.
  unfold_field_at 15%nat.
start_timer "T16 Unfolded Ltac".
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  forward.forward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
stop_timer "T16 Unfolded Ltac".
  forward.forward. (* return *)
  unfold_data_at 1%nat.
  unfold_data_at 1%nat.
  unfold_field_at 17%nat.
  unfold_field_at 19%nat.
  unfold_field_at 21%nat.
  unfold_field_at 23%nat.
  unfold_field_at 17%nat.
  unfold_field_at 19%nat.
  unfold_field_at 21%nat.
  unfold_field_at 23%nat.
  unfold_field_at 25%nat.
  unfold_field_at 27%nat.
  unfold_field_at 29%nat.
  unfold_field_at 31%nat.
  cancel.
Qed.
*)
(*
Clear Timing Profile.
Lemma body_multi_command_s: semax_body Vprog Gprog f_multi_command_s multi_command_s_spec.
Proof.
  start_function.
start_timer "T08b Unfolded Ltac".
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  lforward; [entailer! | solve_legal_nested_field_in_entailment' |].
  simpl upd_reptype.
stop_timer "T08b Unfolded Ltac".
  forward.forward. (* return *)
  cancel.
Qed.
*)
Print Timing Profile.

Require Export mc_reify.symexe_soundness.

Require Import MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.RTac.Try.
Require Import MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.RTac.RTac.
Require Import mc_reify.types.
Require Import mc_reify.funcs.
Require Import mc_reify.func_defs.
Require Import mc_reify.app_lemmas.
Require Import MirrorCore.LemmaApply.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Import mc_reify.rtac_base.
Require Import mc_reify.reified_ltac_lemmas.
Require Import mc_reify.hoist_later_in_pre.
Require Import mc_reify.set_load_store.
Require Import mc_reify.symexe.

(*
Lemma body_multi_command_s2: semax_body Vprog nil f_multi_command_s multi_command_s_spec.
Proof.
  start_function.

start_timer "T08b Unfolded Rtac".

unfold abbreviate in Delta, (*MORE_COMMANDS,*) POSTCONDITION.
subst Delta (*MORE_COMMANDS*) POSTCONDITION.
ensure_normal_ret_assert.
match goal with
| |- semax _ _ _ (normal_ret_assert ?M) => set (POSTCONDITION := M)
end.

prepare_reify.
unfold PTree.set, PTree.prev, tarray, tint; simpl.

rforward.

repeat split.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+
stop_timer "T08b Unfolded Rtac".
admit.
Qed.
Print Timing Profile.
*)
Lemma body_multi_command4: semax_body Vprog nil f_multi_command multi_command_spec.
Proof.
  start_function.
start_timer "T08a Folded Rtac".

unfold abbreviate in Delta, MORE_COMMANDS, POSTCONDITION.
subst Delta MORE_COMMANDS POSTCONDITION.
ensure_normal_ret_assert.
match goal with
| |- semax _ _ _ (normal_ret_assert ?M) => set (POSTCONDITION := M)
end.

prepare_reify.
unfold t_struct_c, t_struct_b, t_struct_a in *; simpl.
unfold PTree.set, PTree.prev, tarray, tint; simpl.

(*
match goal with
| |- semax ?Delta ?Pre (Ssequence (Ssequence ?A1 (Ssequence ?A2 (Ssequence ?A3 _))) _)  _ =>
   assert (semax Delta Pre (Ssequence A1 Sskip)
   (normal_ret_assert Pre)); [| admit]
end.
(*
 08 reduce:	(total:0.057167, mean:0.057167, runs:1, sigma2:0.000000)
   09 cut1:	(total:0.118262, mean:0.118262, runs:1, sigma2:0.000000)
 10 change:	(total:0.000002, mean:0.000002, runs:1, sigma2:0.000000)
   11 cut2:	(total:0.184445, mean:0.184445, runs:1, sigma2:0.000000)
*)
*)

(*
match goal with
| |- semax ?Delta ?Pre (Ssequence (Ssequence ?A1 (Ssequence ?A2 (Ssequence ?A3 _))) _)  _ =>
   assert (semax Delta Pre (Ssequence A1 (Ssequence A2 Sskip))
   (normal_ret_assert Pre)); [| admit]
end.
(*
 08 reduce:	(total:0.079519, mean:0.079519, runs:1, sigma2:0.000000)
   09 cut1:	(total:0.284411, mean:0.284411, runs:1, sigma2:0.000000)
 10 change:	(total:0.000001, mean:0.000001, runs:1, sigma2:0.000000)
   11 cut2:	(total:0.307770, mean:0.307770, runs:1, sigma2:0.000000)
*)
*)

(*
match goal with
| |- semax ?Delta ?Pre (Ssequence (Ssequence ?A1 (Ssequence ?A2 (Ssequence ?A3 _))) _)  _ =>
   assert (semax Delta Pre (Ssequence A1 (Ssequence A2 (Ssequence A3 Sskip)))
   (normal_ret_assert Pre)); [| admit]
end.
(*
05 vm_compute:	(total:0.093451, mean:0.093451, runs:1, sigma2:0.000000)
 08 reduce:	(total:0.223416, mean:0.223416, runs:1, sigma2:0.000000)
   09 cut1:	(total:1.312236, mean:1.312236, runs:1, sigma2:0.000000)
 10 change:	(total:0.000002, mean:0.000002, runs:1, sigma2:0.000000)
   11 cut2:	(total:1.057662, mean:1.057662, runs:1, sigma2:0.000000)
*)
*)

(*
match goal with
| |- semax ?Delta ?Pre (Ssequence (Ssequence ?A1 (Ssequence ?A2 (Ssequence ?A3 (Ssequence ?A4 _)))) _)  _ =>
   assert (semax Delta Pre (Ssequence A1 (Ssequence A2 (Ssequence A3 (Ssequence A4 Sskip))))
   (normal_ret_assert Pre)); [| admit]
end.
(*
 05 vm_compute:	(total:0.154376, mean:0.154376, runs:1, sigma2:0.000000)
 08 reduce:	(total:0.784162, mean:0.784162, runs:1, sigma2:0.000000)
   09 cut1:	(total:6.706352, mean:6.706352, runs:1, sigma2:0.000000)
 10 change:	(total:0.000002, mean:0.000002, runs:1, sigma2:0.000000)
   11 cut2:	(total:5.556991, mean:5.556991, runs:1, sigma2:0.000000)
*)
*)
(*
match goal with
| |- semax ?Delta ?Pre (Ssequence (Ssequence ?A1 (Ssequence ?A2 (Ssequence ?A3 (Ssequence ?A4
         (Ssequence ?A5 (Ssequence ?A6 (Ssequence ?A7 ?A8))))))) _)  _ =>
   assert (semax Delta Pre (Ssequence A1 (Ssequence A3 (Ssequence A5 (Ssequence A7
                             (Ssequence A1 (Ssequence A3 (Ssequence A5 (Ssequence A7 Sskip))))))))
   (normal_ret_assert Pre)); [| admit]
end.
*)
Set Printing Depth 4.
Clear Timing Profile.
rforward.
Print Timing Profile.

repeat split.
+ Set Printing Depth 50.
  intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply andp_right.
  entailer!.
  apply prop_right. solve_legal_nested_field.
+ intros.
  apply prop_right. solve_legal_nested_field.
+
stop_timer "T08a Folded Rtac".
admit.

Qed.
