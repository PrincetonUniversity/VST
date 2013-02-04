Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.list_dt.
Require Import progs.malloc_lemmas.

Require Import progs.queue.

Local Open Scope logic.

Instance QS: listspec _struct_elem _next.
Proof.
apply mk_listspec with  (Fcons _a tint
       (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil))).
simpl. reflexivity.
Defined.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]  (!! (4 <= Int.signed n) &&
                             local (`(eq (Vint n)) (eval_id 1%positive))) && emp
  POST [ tptr tvoid ]  `(memory_block Share.top n) retval.

Definition freeN_spec :=
 DECLARE _freeN
  WITH u: unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
         `(memory_block Share.top) (`force_int (eval_id 1%positive)) (eval_id 2%positive) 
  POST [ tvoid ]  emp.

Definition elemtype := (int*(int*(unit*unit)))%type.

Definition fifo (contents: list elemtype) (p: val) : mpred:=
  EX ht: (val*val), EX last : val, 
      mapsto Share.top (tptr t_struct_elem) (snd ht) last *
      (mapsto Share.top (tptr t_struct_elem) (snd ht) last -*
      (field_mapsto Share.top t_struct_fifo _head p (fst ht) *
       field_mapsto Share.top t_struct_fifo _tail p (snd ht) *
       lseg QS Share.top contents (fst ht) last)).

Definition elemrep (rep: elemtype) (p: val) : mpred :=
  field_mapsto Share.top (tptr t_struct_elem) _a p (Vint (fst rep)) * 
  (field_mapsto Share.top (tptr t_struct_elem) _b p (Vint (fst (snd rep))) *
   (EX x:val, field_mapsto Share.top (tptr t_struct_elem) _next p x)).

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH u : unit
  PRE  [  ] emp
  POST [ (tptr t_struct_fifo) ] `(fifo nil) retval.

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list elemtype, elem: elemtype
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
            local (`(eq q) (eval_id _Q)) && 
           `(fifo contents q) * `(elemrep elem) (eval_id _p)
  POST [ tvoid ] `(fifo (contents++(elem :: nil)) q).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, contents: list elemtype, elem: elemtype
  PRE  [ _Q OF (tptr t_struct_fifo) ]
            local (`(eq q) (eval_id _Q)) && `(fifo (elem :: contents) q) 
  POST [ (tptr t_struct_elem) ] `(fifo contents q) * `(elemrep elem) retval.

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int
  PRE  [ _a OF tint, _b OF tint ] 
            local (`(eq (Vint a)) (eval_id _a))
       && local (`(eq (Vint b)) (eval_id _b))
       && emp
  POST [ (tptr t_struct_elem) ] `(elemrep (a,(b,(tt,tt)))) retval.

Definition main_spec := 
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := 
    mallocN_spec :: freeN_spec :: fifo_new_spec :: fifo_put_spec :: fifo_get_spec 
         :: make_elem_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.


Lemma andp_prop_gather {A}{NA: NatDed A}:
  forall P Q: Prop, andp (prop P) (prop Q) = prop (P /\ Q).
Proof.
intros. apply pred_ext; normalize.
Qed.

Lemma memory_block_isptr:
  forall sh n v, memory_block sh n v = !! denote_tc_isptr v && memory_block sh n v.
Admitted.

Lemma memory_block_fifo:
 forall e, 
   `(memory_block Share.top (Int.repr 8)) e =
  `(field_storable Share.top t_struct_fifo queue._head) e *
  `(field_storable Share.top t_struct_fifo queue._tail) e.
Proof.
 intros.
 extensionality rho.
 unfold coerce at 1; unfold lift1_C, lift1.
 change 8 with (sizeof t_struct_fifo).
 rewrite (malloc_assert (e rho) t_struct_fifo).
 simpl_malloc_assertion.
Qed.

Lemma lift1_lift1_retval {A}: forall i (P: val -> A),
lift1 (lift1 P retval) (get_result1 i) = lift1 P (eval_id i).
Proof. intros.  extensionality rho. 
  unfold lift1.  f_equal. 
Qed.

Lemma lift1_lift1_retvalC {A}: forall i (P: val -> A),
`(`P retval) (get_result1 i) = @coerce _ _ (lift1_C _ _) P (eval_id i).
Proof. intros.  extensionality rho.
  unfold coerce, lift1_C, lift1. 
  f_equal.  
Qed.

Hint Resolve writable_share_top.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name _Q _Q.
name _q 21%positive.
forward. (* q = mallocN(sizeof ( *Q)); *) 
instantiate (1:= Int.repr 8) in (Value of witness).
go_lower. rewrite andp_prop_gather. normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence.
compute; congruence.
cancel.
normalize.
unfold assert.
rewrite lift1_lift1_retvalC.
forward. (* Q = (struct fifo * )q; *)  
apply semax_pre_PQR with
   (PROP  ()
   LOCAL ()
   SEP  (`(memory_block Share.top (Int.repr 8)) (eval_id queue._Q))).
go_lower. subst. destruct _q; inv TC; simpl; normalize.
clear _q.
rewrite memory_block_fifo.
flatten_sepcon_in_SEP.
forward. (* Q->head = NULL; *)
go_lower. apply andp_right; auto. apply prop_right; hnf; auto.
forward.  (*  Q->tail = &(Q->head); *)
go_lower. apply andp_right; auto.
  rewrite field_mapsto_nonnull at 1. normalize.
  apply prop_right. destruct _Q; inv H; inv TC.
    rewrite H0 in H1; inv H1. 
  hnf; reflexivity.
forward. (* return Q; *)
go_lower.
apply andp_right.
  rewrite field_mapsto_nonnull; normalize.
  apply prop_right; destruct _Q; inv H; inv TC; hnf; simpl; auto.
  rewrite H0 in H1; inv H1.
  unfold fifo. apply exp_right with (nullval,_Q).
  simpl.  apply exp_right with nullval.
  rewrite field_mapsto_nonnull.  normalize.
  destruct _Q; inv H; inv TC; simpl; auto.
  rewrite H0 in H1; inv H1. unfold eval_cast; simpl. normalize.

replace (mapsto Share.top (tptr t_struct_elem) (Vptr b i) nullval) 
  with (field_mapsto Share.top t_struct_fifo _head (Vptr b i) nullval).
Focus 2. symmetry. 
eapply mapsto_field_mapsto; simpl; try reflexivity.
unfold field_offset; simpl; reflexivity.
rewrite align_0 by (compute; auto).
rewrite Int.add_zero. auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
apply wand_sepcon_adjoint.
rewrite sepcon_comm; auto.
Qed.

Lemma body_fifo_put: semax_body Vprog Gtot f_fifo_put fifo_put_spec.
Proof.
start_function.
name _Q _Q.
name _p _p.


(* forward. *) (* *(Q->tail) = p;  *) 

Admitted.


Lemma body_fifo_get: semax_body Vprog Gtot f_fifo_get fifo_get_spec.
Proof.
start_function.
name _Q _Q.
name _p _p.

(* forward. *) (* if (Q->tail== &(Q->head))  *) 

Admitted.


Lemma body_make_elem: semax_body Vprog Gtot f_make_elem make_elem_spec.
Proof.
start_function.
name _a _a.
name _b _b.
name _p _p.

(* forward. *) (*  p = mallocN(sizeof ( *p));  *) 

Admitted.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name _i _i.
name _Q _Q.
name _p _p.
forward. (* Q = fifo_new(); *)
instantiate (1:= tt) in (Value of witness).
go_lower. cancel.
auto with closed.
Admitted.

Parameter body_mallocN:
 semax_external

  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint |}) int
  (fun n : int =>
   !!(4 <= Int.signed n) && local (`(eq (Vint n)) (eval_id 1%positive)) &&
   emp) (fun n : int => `(memory_block Share.top n) retval).

Parameter body_freeN:
semax_external
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None |}) unit
  (fun _ : unit =>
   `(memory_block Share.top) (`force_int (eval_id 1%positive))
     (eval_id 2%positive)) (fun _ : unit => emp).

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons_ext; [ reflexivity | apply body_mallocN | ].
apply semax_func_cons_ext; [ reflexivity | apply body_freeN | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_new | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_put | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_get | ].
apply semax_func_cons; [ reflexivity | apply body_make_elem | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.


