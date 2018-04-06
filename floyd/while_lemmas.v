Require Import VST.floyd.base2.
Require Import VST.floyd.expr_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.forward_lemmas.
Require Import VST.floyd.entailer.

Local Open Scope logic.

Definition loop_ram_ret_assert (Pcn Pb: environ -> mpred) (R: ret_assert): ret_assert :=
  fun ek vl =>
    match ek with
    | EK_normal => Pcn
    | EK_break => Pb
    | EK_continue => Pcn
    | EK_return => R EK_return vl
    end.

Lemma semax_loop_ramify :
 forall Espec {cs: compspecs} Delta body
           (A: Type) (Pre Post: A -> environ -> mpred) (R: ret_assert) (a: A),
   (forall vl, R EK_normal vl = Post a) ->
   (forall a: A,
      @semax cs Espec Delta
        (Pre a)
        body
        (loop_ram_ret_assert (EX b:A, Pre b * (Post b -* Post a)) (Post a) R)) ->
  @semax cs Espec Delta (Pre a) (Sloop body Sskip) R.
Proof.
  intros.
  pose proof semax_loop Delta
    (EX b: A, Pre b * (Post b -* Post a))
    (EX b: A, Pre b * (Post b -* Post a))
    Sskip body R.
  eapply semax_pre; [| apply H1; clear H1].
  + Exists a.
    apply andp_left2.
    intro; apply cancel_emp_wand; auto.
  + Intros a0.
    admit.
  + 
    SearchAbout (_ |-- _ * (_ -* _)).
