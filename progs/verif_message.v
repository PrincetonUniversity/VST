Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.message.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* This program, and its verification, are described in Chapter 29
   of _Program Logics for Certified Compilers_, by Appel et al., 2014 *)

Local Open Scope Z.

(*   mf_assert msgfmt sh buf len data  := the [data] is formatted into a message
         at most [len] bytes,  stored starting at address [buf] with share [sh] *)

Record message_format (t: type) : Type :=
mf_build {
   mf_size: Z;
   mf_data_assert: forall (data: reptype t), Prop;
   mf_assert: forall (sh: share) (buf: val) (len: Z) (data: reptype t), mpred;
   mf_size_range:  0 <= mf_size <= Int.max_signed;
   mf_bufprop: forall sh buf len data,
           mf_assert sh buf len data |--
                 !!(0 <= len <= mf_size) && memory_block sh len buf;
   mf_restbuf := fun (sh: share) (buf: val) (len: Z) =>
          memory_block sh (mf_size-len) (offset_val len buf)
}.

Arguments mf_build {t}.
Arguments mf_size {t}.
Arguments mf_data_assert {t}.
Arguments mf_assert {t}.
Arguments mf_bufprop {t}.
Arguments mf_size_range {t}.
Arguments mf_restbuf {t}.

Lemma mf_assert_local_facts: forall t (mf: message_format t) sh buf len (data: reptype t),
   mf_assert mf sh buf len data |-- 
    !! (0 <= len <= mf_size mf /\ isptr buf).
Proof.
intros.
eapply derives_trans;[ apply mf_bufprop | ].
entailer!.
Qed.

#[export] Hint Resolve mf_assert_local_facts : saturate_local.


Definition t_struct_intpair := Tstruct _intpair noattr.
Definition t_struct_message := Tstruct _message noattr.

Program Definition intpair_message: message_format t_struct_intpair :=
  mf_build 8 (fun data => is_int I32 Signed (fst data) /\ is_int I32 Signed (snd data))
             (fun sh buf len data => !!(len=8/\ is_int I32 Signed (fst data) /\ is_int I32 Signed (snd data))
                           && data_at sh (tarray tint 2) [fst data; snd data] buf)
      _ _.
Next Obligation.
compute; split; congruence.
Qed.
Next Obligation.
  entailer!.
  change 8 with (sizeof (tarray tint 2)).
  apply data_at_memory_block.
Qed.

Definition serialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ tptr tvoid, tptr tuchar ]
          PROP (readable_share sh; writable_share sh';
                mf_data_assert format data;
                align_compatible tint buf)
          PARAMS (p; buf)
          SEP (data_at sh t data p;
                 memory_block sh' (mf_size format) buf)
  POST [ tint ]
         EX len: Z,
          PROP() RETURN (Vint (Int.repr len))
          SEP( data_at sh t data p;
                 mf_assert format sh' buf len data;
                 mf_restbuf format sh' buf len).

Definition deserialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share, len: Z
  PRE [ tptr tvoid, tptr tuchar, tint ]
          PROP (readable_share sh'; writable_share sh;
                0 <= len <= mf_size format)
          PARAMS (p; buf; Vint (Int.repr len))
          SEP (mf_assert format sh' buf len data;
                 data_at_ sh t p)
  POST [ tvoid ]
          PROP (mf_data_assert format data)  RETURN ()
          SEP (mf_assert format sh' buf len data;
                 data_at sh t data p).

Definition intpair_serialize_spec :=
 DECLARE _intpair_serialize (serialize_spec intpair_message).

Definition intpair_deserialize_spec :=
 DECLARE _intpair_deserialize (deserialize_spec intpair_message).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition message (sh: share) {t: type} (format: message_format t) (m: val) : mpred :=
  EX fg: val*val,
          func_ptr (serialize_spec format) (fst fg) *
          func_ptr (deserialize_spec format) (snd fg) *
       data_at sh t_struct_message (Vint (Int.repr (mf_size format)), (fst fg, snd fg)) m.

Definition Gprog : funspecs :=   ltac:(with_library prog [
    intpair_serialize_spec; intpair_deserialize_spec; main_spec]).

Lemma body_intpair_serialize: semax_body Vprog Gprog f_intpair_serialize intpair_serialize_spec.
Proof.
unfold intpair_serialize_spec.
unfold serialize_spec.
start_function.
destruct H as [Dx Dy].
destruct data as [[|x1 | | | | ] [|y1 | | | | ]]; try contradiction. clear Dx Dy.

change (mf_size intpair_message) with (sizeof (tarray tint 2)).
assert_PROP (field_compatible (tarray tint 2) [] buf).
  entailer!.
  hnf in H; decompose[and] H; repeat split; auto.
  (* TODO: abstract the following proof. *)  
  unfold align_compatible in H0 |- *.
  destruct buf; auto.
  constructor.
  intros.
  eapply align_compatible_rec_by_value_inv in H0; [| reflexivity].
  econstructor; [reflexivity |].
  apply Z.divide_add_r; auto.
  exists i0; rewrite Z.mul_comm; auto.
rewrite memory_block_data_at_; auto.
change (data_at_ sh' (tarray tint 2) buf) with
   (data_at sh' (tarray tint 2) [Vundef;Vundef] buf).
forward. (* x = p->x; *)
forward. (* y = p->y; *)
forward. (*  ((int * )buf)[0]=x; *)
forward. (*  ((int * )buf)[1]=y; *)
forward. (* return 8; *)
Exists 8.
unfold mf_restbuf. simpl.
rewrite memory_block_zero.
entailer!!.
Qed.

Lemma body_intpair_deserialize: semax_body Vprog Gprog f_intpair_deserialize intpair_deserialize_spec.
Proof.
unfold intpair_deserialize_spec, deserialize_spec.
start_function.
hnf in data; simpl in data. (* This speeds things up dramatically *)
simpl. Intros. subst len.
destruct data as [[|x1 | | | | ] [|y1 | | | | ]]; try contradiction.
clear H H1 H2.
forward. (* x = ((int * )buf)[0]; *)
forward. (* y = ((int * )buf)[1]; *)
forward. (* p->x = x; *)
forward. (* p->y = y; *)
entailer!.
simpl; auto.
unfold mf_assert.
simpl.
entailer!!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
function_pointers.
start_function.
set (ipm := gv _intpair_message).
fold cc_default noattr.
make_func_ptr _intpair_deserialize.
make_func_ptr _intpair_serialize.
set (des := gv _intpair_deserialize).
set (ser := gv _intpair_serialize).
match goal with 
 |- context [mapsto_zeros 4 Ews _] =>
  (* 64-bit mode *)
  sep_apply mapsto_zeros_memory_block; auto;
  gather_SEP (mapsto _ _ _ (offset_val 0 des))
      (mapsto _ _ _ (offset_val 0 ser))
      (memory_block Ews 4 _)
      (data_at _ _ _ ipm)
 | _ => (*32-bit mode *)
  gather_SEP (mapsto _ _ _ (offset_val 0 des))
      (mapsto _ _ _ (offset_val 0 ser))
      (data_at _ _ _ ipm)
end.
replace_SEP 0 
    (data_at Ews t_struct_message
      (Vint (Int.repr (mf_size intpair_message)), (ser, des)) ipm). {
 entailer!.
 unfold_data_at (data_at _ t_struct_message _ ipm).
 rewrite (field_at_data_at _ _ _ _ ipm).
rewrite data_at_tuint_tint.
(* rewrite <- (mapsto_field_at _ _ [StructField _bufsize] (Vint (Int.repr 8))) by auto with field_compatible. *)
 rewrite <- (mapsto_field_at _ _ [StructField _deserialize] des) by auto with field_compatible.
 rewrite <- (mapsto_field_at _ _ [StructField _serialize] ser) by auto with field_compatible.
 rewrite !field_compatible_field_address by auto with field_compatible.
 simpl.
 normalize.
 unfold spacer, at_offset; simpl.
 cancel.
}
forward. (* p.x = 1; *)
forward. (* p.y = 2; *)
forward. (* ser = intpair_message.serialize; *)

rewrite <- memory_block_data_at__tarray_tuchar_eq by computable.
change (memory_block Tsh 8 v_buf)
with (memory_block Tsh (mf_size intpair_message) v_buf).

assert_PROP (align_compatible tint v_buf).
  entailer!.
  destruct HPv_buf; subst; simpl.
  econstructor; [reflexivity | apply Z.divide_0_r].
forward_call (* len = ser(&p, buf); *)
      ((Vint (Int.repr 1), Vint (Int.repr 2)), v_p, v_buf, Tsh, Tsh).
{ simpl; auto. }
Intros rest.
simpl.
Intros. subst rest.

forward. (* des = intpair_message.deserialize; *)
forward_call (* des(&q, buf, 8); *)
        ((Vint (Int.repr 1), Vint (Int.repr 2)), v_q, v_buf, Tsh, Tsh, 8).
  simpl. fold t_struct_intpair. entailer!.
  simpl; computable.
(* after the call *)
forward. (* x = q.x; *)
forward. (* y = q.y; *)
forward. (* return x+y; *)
simpl.
entailer!.
sep_apply (data_at_memory_block Tsh (tarray tint 2) [Vint (Int.repr 1); Vint (Int.repr 2)] v_buf).
unfold sizeof; simpl Ctypes.sizeof.
sep_apply (memory_block_data_at__tarray_tuchar Tsh v_buf 8).
   computable.
entailer!!.
Qed.
