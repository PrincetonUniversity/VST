(** * verif_conc_stack.c: Correctness proof of conc_stack.c *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.conclib.
Require Import VST.progs.conc_stack.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).

Fixpoint listrep (il: list Z) (p: val) : mpred :=
 match il with
 | i::il' => EX y: val, 
        malloc_token Tsh (Tstruct _cons noattr) p *
        data_at Tsh (Tstruct _cons noattr) (Vint (Int.repr i),y) p * listrep il' y
 | nil => !! (p = nullval) && emp
 end.

Lemma listrep_local_prop: forall il p, listrep il p |--
        !! (is_pointer_or_null p  /\ (p=nullval <-> il=nil)).
Proof.
induction il; intro; simpl.
entailer!. intuition.
Intros y.
entailer!.
split; intros. subst.
eapply field_compatible_nullval; eauto.
inversion H3.
Qed.
Hint Resolve listrep_local_prop : saturate_local.

Lemma listrep_valid_pointer:
  forall il p,
   listrep il p |-- valid_pointer p.
Proof.
(* ADMITTED *)
 destruct il; unfold listrep; fold listrep; intros.
 entailer!.
 Intros y.
 auto with valid_pointer.
Qed.
(* /ADMITTED *)
Hint Resolve listrep_valid_pointer : valid_pointer.


Definition stack (il: list Z) (p: val) :=
 EX q: val,
  data_at Tsh (Tstruct _stack noattr) q p * listrep il q.

Lemma stack_local_prop: forall il p, stack il p |--  !! (isptr p).
Proof.
(* ADMITTED *)
intros.
unfold stack.
Intros y.
entailer!.
Qed.
(* /ADMITTED *)
Hint Resolve stack_local_prop : saturate_local.

Lemma stack_valid_pointer:
  forall il p,
   stack il p |-- valid_pointer p.
Proof.
(* ADMITTED *)
intros.
unfold stack.
Intros y.
auto with valid_pointer.
Qed.
(* /ADMITTED *)
Hint Resolve stack_valid_pointer : valid_pointer.

(* new material *)
Definition tlstack := Tstruct _lstack noattr.

Definition stack_inv p := EX il : _, stack il p.

Definition lstack sh p := !! (field_compatible tlstack [] p) &&
  malloc_token sh tlstack p * EX l : val, malloc_token sh tlock l *
    field_at sh tlstack [StructField _lock] l p *
    lock_inv sh l (stack_inv p).

Definition newstack_spec : ident * funspec :=
 DECLARE _newstack
 WITH tt: unit
 PRE [ ] 
    PROP () LOCAL () SEP ()
 POST [ tptr (Tstruct _stack noattr) ] 
    EX p: val, PROP ( ) LOCAL (temp ret_temp p) SEP (lstack Tsh p).

Definition push_spec : ident * funspec :=
 DECLARE _push
 WITH p: val, i: Z, sh: share
 PRE [ _p OF tptr (Tstruct _stack noattr), _i OF tint ] 
    PROP (Int.min_signed <= i <= Int.max_signed; readable_share sh) 
    LOCAL (temp _p p; temp _i (Vint (Int.repr i))) 
    SEP (lstack sh p)
 POST [ tvoid ] 
    PROP ( ) LOCAL () SEP (lstack sh p).

Definition pop_spec : ident * funspec :=
 DECLARE _pop
 WITH p: val, i: Z, sh: share
 PRE [ _p OF tptr (Tstruct _stack noattr) ] 
    PROP (readable_share sh) 
    LOCAL (temp _p p) 
    SEP (lstack sh p)
 POST [ tint ] 
  EX i : _, PROP ( ) LOCAL (temp ret_temp (Vint (Int.repr i))) SEP (lstack sh p).

(*  PUTTING ALL THE FUNSPECS TOGETHER *)

Definition Gprog : funspecs :=
        ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
                   newstack_spec; push_spec; pop_spec
 ]).

Lemma stack_inv_exclusive : forall p, exclusive_mpred (stack_inv p).
Proof.
  intro; unfold stack_inv, stack.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX il : list Z, EX q : val, listrep il q),
    data_at__exclusive with (sh := Tsh)(t := Tstruct _stack noattr); auto; simpl; try omega.
  Intros il q; apply sepcon_derives; [cancel|].
  Exists il q; apply derives_refl.
Qed.
Hint Resolve stack_inv_exclusive.

Lemma body_pop: semax_body Vprog Gprog f_pop pop_spec.
Proof.
start_function.
(* ADMITTED *)
forward_loop (PROP () LOCAL (temp _p p) SEP (lstack sh p)).
{ entailer!. }
forward.
unfold lstack.
Intros l.
rewrite lock_inv_isptr.
forward.
forward_call (l, sh, stack_inv p).
unfold stack_inv at 2.
unfold stack.
Intros il q.
forward.
forward.
forward_if.
{ forward.
  forward_call (l, sh, stack_inv p).
  { lock_props.
    unfold stack_inv, stack.
    Exists il q; cancel. }
  eapply semax_pre; [|eapply semax_seq; [apply semax_continue|]].
  simpl RA_continue.
  unfold lstack.
  Exists l; entailer!.
  forward. }
forward.
destruct il; simpl.
{ Intros; contradiction. }
Intros y.
forward.
forward.
forward.
forward_call (l, sh, stack_inv p).
{ lock_props.
  unfold stack_inv, stack.
  Exists il y; entailer!. }
forward.
forward_call (Tstruct _cons noattr, q).
forward.
unfold lstack.
Exists z l.
entailer!.
Qed.
(* /ADMITTED *)

Lemma body_push: semax_body Vprog Gprog f_push push_spec.
Proof.
start_function.
forward_call (Tstruct _cons noattr).
{ simpl; split3; auto.
  rep_omega. }
(* ADMITTED *)
Intros q.
if_tac.
{ subst.
  forward_if False.
  forward_call tt.
  contradiction.
  inversion H0. }
forward_if True.
{ contradiction. }
forward.
{ entailer!. }
Intros.
forward.
simpl.
unfold lstack.
Intros l.
rewrite lock_inv_isptr.
forward.
forward_call (l, sh, stack_inv p).
unfold stack_inv at 2.
unfold stack.
Intros il q'.
forward.
forward.
forward.
forward.
forward.
forward_call (l, sh, stack_inv p).
{ lock_props.
  unfold stack_inv, stack.
  Exists (i :: il) q; simpl listrep.
  Exists q'.
  entailer!. }
forward.
unfold lstack.
Exists l.
entailer!.
Qed.
(* /ADMITTED *)

Lemma lstack_field_stack : forall sh q p,
  field_at sh tlstack [StructField _d] q p |-- data_at sh (Tstruct _stack noattr) q p.
Proof.
  intros.
  unfold_data_at 1%nat.
  unfold_field_at 1%nat.
  unfold field_at; entailer!.
  rewrite field_compatible_cons in *; simpl in *.
  destruct H as [_ H].
  apply field_compatible_nested_field in H; simpl in H.
  rewrite isptr_offset_val_zero in H by auto.
  split; hnf; auto.
Qed.

Lemma body_newstack: semax_body Vprog Gprog f_newstack newstack_spec.
Proof.
start_function.
(* ADMITTED *)
forward_call (tlstack).
{ simpl; split; auto. rep_omega. }
Intros p.
forward_if (p <> nullval).
{ if_tac.
  entailer!.
  entailer!. }
{ subst.
  rewrite if_true by auto.
  forward_call tt.
  contradiction. }
{ rewrite if_false by auto.
  forward.
  rewrite if_false by auto.
  entailer!. }
Intros.
rewrite if_false by auto.
Intros.
forward.
forward_call (tlock).
{ simpl; split; auto. rep_omega. }
Intros l.
forward_if (l <> nullval).
{ if_tac.
  entailer!.
  entailer!. }
{ subst.
  rewrite if_true by auto.
  forward_call tt.
  contradiction. }
{ rewrite if_false by auto.
  forward.
  rewrite if_false by auto.
  entailer!. }
Intros.
rewrite if_false by auto.
Intros.
forward_call (l, Tsh, stack_inv p).
forward.
forward_call (l, Tsh, stack_inv p).
{ lock_props.
  unfold stack_inv, stack.
  Exists (@nil Z) nullval.
  simpl listrep; entailer!.
  unfold_data_at 1%nat.
  rewrite sepcon_comm, !sepcon_assoc.
  apply sepcon_derives; [apply lstack_field_stack | cancel]. }
forward.
unfold lstack.
Exists p l.
entailer!.
Qed.
(* /ADMITTED *)
