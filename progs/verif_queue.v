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
Require Import progs.listc.

Require Import progs.queue.

Local Open Scope logic.

Instance QS: listspec _struct_elem _next.
Proof.
apply mk_listspec with  (Fcons _a tint
       (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil))).
simpl. rewrite if_false by  (intro Hx; inv Hx). rewrite if_false by  (intro Hx; inv Hx).
 rewrite if_true by auto.  rewrite if_true by auto.  
reflexivity.
Defined.

Parameter memory_block: share -> int -> val -> mpred.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]  !! (4 <= Int.signed n) &&
                             local (`(eq (Vint n)) (eval_id 1%positive)) && emp
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
      (field_mapsto Share.top (tptr t_struct_elem) _head p (fst ht) *
       field_mapsto Share.top (tptr (tptr t_struct_elem)) _tail p (snd ht) *
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
  WITH q: val, ss : (list elemtype * elemtype)
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
            local (`(eq q) (eval_id _Q)) && 
           `(fifo (fst ss) q) * `(elemrep (snd ss)) (eval_id _p)
  POST [ tvoid ] `(fifo (fst ss++(snd ss :: nil)) q).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, ss : (list elemtype * elemtype)
  PRE  [ _Q OF (tptr t_struct_fifo) ]
            local (`(eq q) (eval_id _Q)) && `(fifo (snd ss :: fst ss) q) 
  POST [ (tptr t_struct_elem) ] `(fifo (fst ss) q) * `(elemrep (snd ss)) retval.

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

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name _Q _Q.
(* forward. *) (* Q = (struct fifo * )mallocN(sizeof ( *Q)); *) 

Admitted.

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


