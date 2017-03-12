Require Import language.
Require Import msl.base.
Require Import msl.seplog.
Require Import msl.alg_seplog.
Require Import seplogic.
Require Import lseg.
Require Import msl.Coqlib2.
Require Import msl.log_normalize.
Require Import client_lemmas.

Local Open Scope logic.

Import Semax.

Section PROG.

Let a : var := 0.
Let s : var := 1.
Let p : var := 2.
Let r : var := 3.
Let START : adr := 0.
Let LOOP : adr := 1.
Let DONE : adr := 2.

Definition STARTbody := (a::nil,
                  Do Mem a := a .+ 1; Do Mem (a .+ 1) := a .+ 2; Do Mem (a .+ 2) := Const 0;
                  Go LOOP ((a.+3)::(Var a)::(Var a)::(Const DONE)::nil)).

Definition LOOPbody := (a::s::p::r::nil,
                If p Then (Do p := Mem p; Go LOOP (Var a::Var s::Var p::Var r::nil))
                      Else Go r (Var a::Var s::nil)).

Definition DONEbody := (a::s::nil,  Go DONE (Var a::Var s::nil)).

Definition myprog : program :=
   (START, STARTbody):: (LOOP,  LOOPbody) :: (DONE,   DONEbody) :: nil.

Definition STARTspec : funspec := (a::nil,
               fun s => allocpool (eval (Var a) s)).
Definition DONEspec: funspec := (a::s::nil,
               fun s' => lseg (eval (Var s) s') (eval (Const 0) s') * allocpool (eval (Var a) s')).
Definition LOOPspec: funspec :=  (a::s::p::r::nil,
              fun s' => lseg (eval (Var s) s') (eval (Var p) s')
               * lseg (eval (Var p) s') (eval (Const 0) s')
               * allocpool (eval (Var a) s')
               && cont DONEspec (eval (Var r) s')).

Definition myspec := (START, STARTspec):: ((LOOP, LOOPspec) :: (DONE, DONEspec) :: nil).


Lemma prove_START: semax_body myspec STARTspec STARTbody.
 eapply semax_pre; [intro ; call_tac; apply derives_refl |  simpl ].
 rewrite' alloc.
 apply semax_prop; auto; intros _.
 forward.
 rewrite' alloc. rewrite' @sepcon_comm.  rewrite' @sepcon_assoc.
 forward.
 rewrite' alloc. rewrite' @sepcon_comm. do 2  rewrite' @sepcon_assoc.
 forward.
 forward.
 rewrite lseg_eq. normalize.
 apply andp_derives;  [ | apply funassert_e; reflexivity].
 rewrite (sepcon_comm (allocpool _)). repeat rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (next (S (S (s0 a))) _)).
 apply sepcon_derives; auto.
 repeat rewrite sepcon_assoc. rewrite (next_gt_0 (s0 a)).
 normalize.
 eapply derives_trans;  [ |  eapply lseg_cons; try omega].
 eapply sepcon_derives; [ apply derives_refl |].
 rewrite sepcon_comm.
 eapply derives_trans;  [ |  eapply lseg_cons; try omega].
 eapply sepcon_derives; [ apply derives_refl |].
 apply next_lseg;  omega.
Qed.

Lemma prove_LOOP: semax_body myspec LOOPspec LOOPbody.
  eapply semax_pre; [intro ; call_tac; apply derives_refl | simpl ].
 forward.
 apply semax_pre
   with  (fun s' => EX x: adr, (next (s' p) x * |>lseg x 0 * lseg (s' s) (s' p) * allocpool (s' a)) &&
     cont DONEspec (s' r)).
 intro s'. normalize.
 rewrite (lseg_neq (s' p)) by auto. normalize. apply exp_right with y.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 rewrite sepcon_comm. auto.
 apply (@semax_exp' _ 0). intro tail.
 do 2 rewrite' @sepcon_assoc.
 apply semax_pre with (fun s0 => next (eval (Var p) s0) tail * TT &&
      |> subst p tail (fun s1 =>
                               lseg (eval (Var p) s1) 0 * lseg (eval (Var s) s1) (eval (Var p) s1)
                             * allocpool (eval (Var a) s1)
                             && cont DONEspec (s1 r)) s0);
  [ | apply semax_load_next; auto 50].
 intro.
 unfold subst. simpl. rewrite env_gss.
 rewrite env_gso by (intro Hx; inv Hx).
 rewrite env_gso by (intro Hx; inv Hx).
 rewrite env_gso by (intro Hx; inv Hx).
 apply andp_right.
 apply andp_left1. apply sepcon_derives; auto.
 normalize.
 rewrite later_andp.
 apply andp_derives.
 rewrite sepcon_comm.
 rewrite sepcon_assoc. rewrite sepcon_comm.
 eapply derives_trans. apply sepcon_derives; [ apply now_later | apply derives_refl].
 rewrite <- later_sepcon.
 apply later_derives.
 rewrite sepcon_comm.
 rewrite (sepcon_assoc _ (allocpool _)).
 repeat rewrite <- sepcon_assoc.
 rewrite sepcon_comm.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives; auto.
 rewrite sepcon_comm. rewrite (sepcon_comm (lseg tail 0)).
 rewrite <- sepcon_assoc.
 apply lseg_cons_in_list_context.
 apply now_later.

 forward. normalize.
 apply andp_left1.
 rewrite (sepcon_comm (lseg (s0 s) _)). auto.
 forward.
 normalize.
 apply andp_left1. apply andp_left2. apply derives_refl.
 simpl. normalize.
 autorewrite with args. rewrite H. rewrite lseg_eq. normalize.
 apply andp_left1.
 apply andp_left1. auto.
Qed.

Lemma prove_DONE: semax_body myspec DONEspec DONEbody.
  eapply semax_pre; [intro ; call_tac; apply derives_refl | simpl ].
 forward.
 apply andp_left1.
 apply derives_refl.
Qed.

Lemma prove_myspec:   semax_func myspec myprog myspec.
Proof.
 func_tac; [apply prove_START | ].
 func_tac; [apply prove_LOOP | ].
 func_tac; [apply prove_DONE | ].
 apply semax_func_nil.
Qed.

 Lemma myprog_safe:  forall n, run myprog n <> None.
 Proof. intros. apply semax_sound. exists myspec.
   split. apply prove_myspec. reflexivity.
 Qed.

Definition run' (p: program) (n: nat) : bool :=
 match
    stepN p (nil, initial_heap p, Go (Const 0) (Const (boundary p) :: nil)) n
  with None => false | _ => true
 end.

Compute run' myprog 100.

End PROG.
