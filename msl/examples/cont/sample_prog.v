Require Import msl.examples.cont.language.
Require Import msl.examples.cont.sep_base.
Require Import msl.msl_standard.
Require Import msl.examples.cont.seplog.
Require Import msl.examples.cont.lseg.
Require Import msl.Coqlib2.

Local Open Scope pred.

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

Lemma semax_store_next: forall x y v c vars G (Q P: assert),
    expcheck vars x = true ->
    expcheck vars y = true ->
    Q = (fun s => next (eval x s) v  * P s) ->
    semax vars G (fun s => next (eval x s) (eval y s) * P s) c ->
    semax vars G Q  (Do Mem x  := y ; c).
Proof. intros; subst. 
    apply semax_pre with (fun s => mapsto (eval x s) v * (!! (eval x s > 0) && P s)).
    intros. unfold next. rewrite sepcon_andp_prop. 
    rewrite sepcon_comm. rewrite sepcon_andp_prop. rewrite sepcon_comm; auto.
    apply semax_store; auto.
    eapply semax_pre; try apply H2.
    intros; unfold next.
    rewrite sepcon_andp_prop. 
    rewrite (sepcon_comm (andp _ _)). rewrite sepcon_andp_prop.
   rewrite sepcon_comm; auto.
 Qed.

Lemma semax_load_next: forall x y z c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c -> 
    semax vars G (fun s => (next (eval y s) z * TT) && |> subst x z P s)
               (Do x := Mem y ; c).
Proof.
 intros.
  apply semax_pre with (fun s => mapsto (eval y s) z * TT && |> subst x z P s).
 intros. apply andp_derives; auto. apply sepcon_derives; auto. apply andp_left2; auto.
 apply semax_load; auto.
Qed.

Lemma prove_START: semax_body myspec STARTspec STARTbody. 
 eapply semax_pre; [intro ; call_tac; apply derives_refl |  simpl ].
 rewrite' alloc.
 apply semax_prop; auto; intros _.
 eapply semax_store_next; [ compute ; reflexivity | compute; reflexivity | reflexivity | ].
 rewrite' alloc. rewrite' sepcon_comm.  rewrite' sepcon_assoc.
 simpl.
 eapply semax_store_next; [ compute ; reflexivity | compute; reflexivity | reflexivity | ].
 rewrite' alloc. rewrite' sepcon_comm. do 2  rewrite' sepcon_assoc.
 eapply semax_store_next; [ compute ; reflexivity | compute; reflexivity | reflexivity | ].
 forward.
 rewrite lseg_eq. rewrite emp_sepcon.
 apply andp_right. apply prop_right. auto.
 apply andp_derives;  [ | apply funassert_e; reflexivity].
 rewrite (sepcon_comm (allocpool _)). repeat rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (next (S (S (s0 a))) _)).
 apply sepcon_derives; auto.
 repeat rewrite sepcon_assoc.
 rewrite (next_gt_0 (s0 a)).
 rewrite sepcon_andp_prop1.
 apply prop_andp_left; intro.
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
 eapply semax_pre. intro s'.
 apply prop_andp_left; intro.
 rewrite (sepcon_comm (lseg (s' s) _)).
 apply prop_andp_left; intros _.
 simpl in H.
 apply andp_derives.
 eapply derives_trans.
 rewrite sepcon_assoc.
 rewrite lseg_neq by auto. apply derives_refl.
 rewrite <- sepcon_assoc.
 do 2 rewrite exp_sepcon1.
 apply derives_refl.
 apply derives_refl.
 rewrite' ex_and.
 apply (@semax_exp' _ 0). intro tail.
 do 2 rewrite' sepcon_assoc.
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
 rewrite later_andp.
 apply andp_derives; auto.
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

 forward.
 apply andp_left1.
 apply andp_right; auto. apply prop_right; auto.
 rewrite (sepcon_comm (lseg (s0 s) _)). auto.
 forward. 
 apply andp_left1. apply andp_left2.
 apply andp_left2. apply andp_left2. apply derives_refl.
 simpl. apply prop_andp_right; auto.
 apply andp_left1.
 apply prop_andp_left; intro.
 apply andp_left2. rewrite H. apply andp_left1.
 autorewrite with args. rewrite lseg_eq. rewrite sepcon_emp.
 auto.
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
