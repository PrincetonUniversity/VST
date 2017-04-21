Require Import progs.ghost.
Require Import mailbox.verif_ptr_atomics.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.oplistset.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(*Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.*)

Definition tnode := Tstruct _node noattr.

(* Holding the other half of the ghost var gives permission to write to next/know that it won't change. *)
Definition node_fun sh gsh1 gsh2 (R : val * val -> mpred) a := let '(g, p) := a in
  EX e : Z, EX next : val, EX lock : val, data_at sh tnode (vint e, (next, lock)) p * ghost_var gsh1 p g *
  EX g' : val, lock_inv sh lock (EX p : val, ghost_var gsh2 p g') *
  if eq_dec next (vint 0) then emp else atomic_loc sh next (|>fun v => R (g', v)).

Definition node sh gsh1 gsh2 := HORec (node_fun sh gsh1 gsh2).

Lemma A_inv_nonexpansive : forall p l P1 P2, ALL x : val, |> P1 x <=> |> P2 x |--
  A_inv p l (|> P1) <=> A_inv p l (|> P2).
Proof.
  intros; rewrite fash_andp; apply andp_right; unfold A_inv.
  - apply subp_exp; intro v.
    apply allp_left with v.
    repeat apply subp_sepcon; try apply subp_andp; try apply subp_refl.
    + apply fash_derives, andp_left1; auto.
    + eapply derives_trans; [apply precise_mpred_nonexpansive|].
      simpl; apply subtypes.fash_derives, predicates_hered.andp_left1; auto.
  - apply subp_exp; intro v.
    apply allp_left with v.
    repeat apply subp_sepcon; try apply subp_andp; try apply subp_refl.
    + apply fash_derives, andp_left2; auto.
    + eapply derives_trans; [apply precise_mpred_nonexpansive|].
      simpl; apply subtypes.fash_derives, predicates_hered.andp_left2; auto.
Qed.

Lemma node_eq' : forall sh gsh1 gsh2, node sh gsh1 gsh2 = node_fun sh gsh1 gsh2 (node sh gsh1 gsh2).
Proof.
  intros; apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 (g, p).
  apply subp_exp; intro e.
  apply subp_exp; intro next.
  apply subp_exp; intro lock.
  apply subp_sepcon; [apply subp_refl|].
  apply subp_exp; intro g'.
  apply subp_sepcon; [apply subp_refl|].
  if_tac; [apply subp_refl|].
  apply subp_andp; [apply subp_refl|].
  apply subp_exp; intro l.
  apply subp_sepcon; [apply subp_refl|].
  eapply derives_trans; [|simpl; apply subtypes.fash_derives, predicates_hered.andp_left1; auto].
  eapply derives_trans; [|apply (nonexpansive_lock_inv sh l)].
  eapply derives_trans; [|simpl; apply (A_inv_nonexpansive next l)].
  apply allp_right; intro v.
  apply allp_left with (g', v); auto.
Qed.

Corollary node_eq : forall sh gsh1 gsh2 g p, node sh gsh1 gsh2 (g, p) =
  EX e : Z, EX next : val, EX lock : val, data_at sh tnode (vint e, (next, lock)) p * ghost_var gsh1 p g *
    EX g' : val, lock_inv sh lock (EX p : val, ghost_var gsh2 p g') *
    if eq_dec next (vint 0) then emp else atomic_loc sh next (|>fun v => node sh gsh1 gsh2 (g', v)).
Proof.
  intros.
  transitivity (node_fun sh gsh1 gsh2 (node sh gsh1 gsh2) (g, p)); [|reflexivity].
  rewrite <- node_eq'; auto.
Qed.

Lemma node_isptr : forall sh gsh1 gsh2 g p, node sh gsh1 gsh2 (g, p) = !!isptr p && node sh gsh1 gsh2 (g, p).
Proof.
  intros; eapply local_facts_isptr with (P := fun p => node sh gsh1 gsh2 (g, p)); eauto.
  rewrite node_eq.
  Intros e next lock.
  rewrite data_at_isptr; entailer!.
Qed.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100).

Definition validate_spec := DECLARE _validate
  WITH hp : val, head : val, e : Z, pred : val, curr : val, sh : share, gsh1 : share, gsh2 : share,
    gh : val, ep : Z, nextp : val, lockp : val, gp : val, gp' : val, pn : val, gc : val
  PRE [ _e OF tint, _pred OF tptr tnode, _curr OF tptr tnode ]
    PROP (readable_share sh; sepalg.join gsh1 gsh2 Tsh)
    LOCAL (gvar _head hp; temp _e (vint e); temp _pred pred; temp _curr curr)
    SEP (data_at sh (tptr tnode) head hp; node sh gsh1 gsh2 (gh, head);
         data_at sh tnode (vint ep, (nextp, lockp)) pred; ghost_var gsh1 pred gp;
         lock_inv sh lockp (EX p : val, ghost_var gsh2 p gp'); ghost_var gsh2 pn gp';
         atomic_loc sh nextp (|>fun v => node sh gsh1 gsh2 (gp', v));
         node sh gsh1 gsh2 (gc, curr))
  POST [ tint ]
   EX b : bool,
    PROP (b = true -> gp' = gc /\ pn = curr)
    LOCAL (temp ret_temp (Val.of_bool b))
    SEP (data_at sh (tptr tnode) head hp; node sh gsh1 gsh2 (gh, head);
         data_at sh tnode (vint ep, (nextp, lockp)) pred; ghost_var gsh1 pred gp;
         lock_inv sh lockp (EX p : val, ghost_var gsh2 p gp'); ghost_var gsh2 pn gp';
         atomic_loc sh nextp (|>fun v => node sh gsh1 gsh2 (gp', v));
         node sh gsh1 gsh2 (gc, curr)).

Definition Gprog : funspecs := ltac:(with_library prog [load_SC_spec; validate_spec]).

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Lemma body_validate : semax_body Vprog Gprog f_validate validate_spec.
Proof.
  start_function.
  rewrite node_isptr; Intros.
  forward.
  rewrite node_eq; Intros eh nexth lockh gh'.
  forward.
  unfold Swhile.
  eapply semax_seq'.
  eapply semax_pre, semax_loop.
  
  
  
  