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
  WITH data: reptype t, p: val, buf: val, shs: share*share, len: Z
  PRE [ _p OF (tptr t), _buf OF (tptr tuchar), _length OF tint ] 
          PROP (writable_share (fst shs))
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf);
                        `(eq (Vint (Int.repr len))) (eval_id _length))
          SEP (`(format (snd shs) buf len) `data;
                 `(memory_block (fst shs) (Int.repr (sizeof t)) p))
  POST [ tint ]
            `(format (snd shs) buf len data) *
            `(typed_mapsto t (fst shs) p data).

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
destruct buf0; inv H0; unfold eval_binop; simpl; f_equal; rewrite Int.add_assoc; f_equal.
Qed.

Lemma body_intpair_deserialize: semax_body Vprog Gtot f_intpair_deserialize intpair_deserialize_spec.
Proof.
unfold intpair_deserialize_spec, deserialize_spec.
start_function. destruct shs as (sh,sh'). simpl @fst; simpl @snd.
name p0 _p.
name buf0 _buf.
name x _x.
name y _y.
name len0 _length.
rewrite memory_block_typed.
do 2 simpl_typed_mapsto.
destruct data as (x1,y1); simpl in *.
apply semax_pre_PQR with
 (PROP  (isptr buf; len=8)
   LOCAL  (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf); `(eq (Vint (Int.repr len))) (eval_id _length))
   SEP 
   (`(field_mapsto_ sh t_struct_intpair _x) (eval_id _p);
    `(field_mapsto_ sh t_struct_intpair _y) (eval_id _p);
   `(mapsto sh' tint)
        (`(add_ptr_int tint) (`(eval_cast (tptr tuchar) (tptr tint)) (eval_id _buf)) `0)
      `(Vint x1);
   `(mapsto sh' tint)
        (`(add_ptr_int tint) (`(eval_cast (tptr tuchar) (tptr tint)) (eval_id _buf)) `1)
        `(Vint y1))).
go_lower; subst. unfold intpair_message.
 simpl_typed_mapsto.  simpl. rewrite (field_mapsto_isptr). normalize.
 repeat apply andp_right; try apply prop_right; auto.
 destruct buf0; inv H0; auto.
 cancel.
apply sepcon_derives; apply derives_refl'';
 eapply mapsto_field_mapsto; unfold field_offset; try (simpl; reflexivity);
 apply add_ptr_int_offset;
 simpl; compute; intuition congruence.
normalizex.
forward. (* x = ((int * )buf)[0]; *)
go_lower. subst buf0 p0. apply prop_right; auto. 
forward. (* y = ((int * )buf)[1]; *)
go_lower. subst buf0 p0. apply prop_right; auto. 
forward. (* p->x = x; *)
forward. (*  p->y = y; *)
forward.  (* return; *)
go_lower. subst. unfold intpair_message. normalize.
simpl_typed_mapsto.
cancel.
simpl. rewrite sepcon_comm.
apply sepcon_derives;
apply derives_refl'; eapply mapsto_field_mapsto;  unfold field_offset; try (simpl; reflexivity);
 destruct buf0; inv H0; unfold eval_binop; simpl; reflexivity.
Qed.

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_typed_mapsto__top. 

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function. simpl_stackframe_of.
repeat simpl_typed_mapsto.












