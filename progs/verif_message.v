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
Require Import progs.malloc_lemmas.
Require Import progs.message.

Local Open Scope logic.

(* f : message_format t
    f sh buf n data  := the [data] is formatted into a message of length [n]
          stored starting at address [buf] with share [sh] *)
Definition message_format (t: type) : Type :=
   forall (sh: share) (buf: val) (length:  Z) (data: reptype t), mpred.

Definition intpair_message: message_format t_struct_intpair :=
  fun sh buf n data => 
   !!(n= sizeof t_struct_intpair) && typed_mapsto t_struct_intpair sh buf data.

Definition serialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ _p OF (tptr t), _buf OF (tptr tuchar) ] 
          PROP (writable_share sh')
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf))
          SEP (`(typed_mapsto t sh p data); 
                 `(memory_block sh' (Int.repr (sizeof t)) buf))
  POST [ tint ] 
         `(typed_mapsto t sh p data) 
           * `(format sh' buf) (`Int.unsigned (`force_int retval)) `data.

Definition deserialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ _p OF (tptr t), _buf OF (tptr tuchar), _length OF tint ] 
          PROP (writable_share sh)
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf))
          SEP (`(format sh' buf) (`Int.unsigned (`force_int (eval_id _length))) `data;
                 `(memory_block sh' (Int.repr (sizeof t)) p))
  POST [ tint ]
            `(format sh' buf) (`Int.unsigned (`force_int (eval_id _length))) `data *
            `(typed_mapsto t sh p data).

Definition intpair_serialize_spec :=
 DECLARE _intpair_serialize (serialize_spec intpair_message).

Definition intpair_deserialize_spec :=
 DECLARE _intpair_deserialize (deserialize_spec intpair_message).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_intpair_message, t_struct_message)::nil.

Definition func_at (spec: funspec) (v: val) : mpred := 
  match v with Vptr b z => veric.seplog.func_at spec (b, Int.unsigned z)
   | _ => FF
  end.

Definition message {t: type} (format: message_format t) (sh: share) (m: val) : mpred :=
  EX fg: val*val,
          func_at (serialize_spec format) (fst fg) &&
          func_at (deserialize_spec format) (snd fg) &&
       typed_mapsto t_struct_message sh m (Int.repr (sizeof t), (fst fg, snd fg)).

Definition Gprog : funspecs := 
    intpair_serialize_spec :: intpair_deserialize_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma body_intpair_serialize: semax_body Vprog Gtot f_intpair_serialize intpair_serialize_spec.
Proof.
unfold intpair_serialize_spec.
unfold serialize_spec.
start_function.
name p0 _p.
name buf0 _buf.
name x _x.
name y _y.
rewrite memory_block_typed.
do 2 simpl_typed_mapsto.
destruct data as (x1,y1); simpl in *.
apply semax_pre_PQR with
 (PROP  (isptr buf)
   LOCAL  (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf))
   SEP 
   (`(field_mapsto sh t_struct_intpair _x) (eval_id _p) `(Vint x1);
    `(field_mapsto sh t_struct_intpair _y) (eval_id _p) `(Vint y1);
   `(mapsto_ sh' tint) (`(add_ptr_int tint) (`(eval_cast (tptr tuchar) (tptr tint)) (eval_id _buf)) `0);
   `(mapsto_ sh' tint) (`(add_ptr_int tint) (`(eval_cast (tptr tuchar) (tptr tint)) (eval_id _buf)) `1))).
go_lower; subst;  rewrite (field_mapsto__isptr). normalize. 
 cancel.
apply sepcon_derives; apply derives_refl''; 
 eapply mapsto_field_mapsto_; unfold field_offset; try (simpl; reflexivity);
 apply add_ptr_int_offset;
 simpl; compute; intuition congruence.
forward. (* x = p->x; *)
forward. (* y = p->y; *)
forward. (*  ((int * )buf)[0]=x; *)
go_lower. subst. apply andp_right; auto. apply prop_right; intuition.
forward. (*  ((int * )buf)[1]=y; *)
go_lower. subst. apply andp_right; auto. apply prop_right; intuition.
forward. (* return 8; *)
go_lower. subst. apply andp_right; try apply prop_right; auto.
unfold intpair_message.
normalize.
cancel.
simpl_typed_mapsto.
simpl.
rewrite sepcon_comm.
apply sepcon_derives; apply derives_refl';
 eapply mapsto_field_mapsto; unfold field_offset; try (simpl; reflexivity);
destruct buf0; inv H0; reflexivity.
Qed.

















