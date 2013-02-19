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

(* message_format t = (length, f)
   where 
    f sh buf data  := the [data] is formatted into a message 
         at most [length] bytes, 
          stored starting at address [buf] with share [sh] *)
Definition message_format (t: type) : Type :=
   (Z * (forall (sh: share) (buf: val) (data: reptype t), mpred))%type.

Definition intpair_message: message_format t_struct_intpair :=
  (8, typed_mapsto t_struct_intpair).

Definition serialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ _p OF (tptr t), _buf OF (tptr tuchar) ] 
          PROP (writable_share sh')
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf))
          SEP (`(typed_mapsto t sh p data); 
                 `(memory_block sh' (Int.repr (fst format)) buf))
  POST [ tint ]  
          local (`(fun len => 0 <= Int.signed (force_int len) <= fst format) retval) &&
         `(typed_mapsto t sh p data)  * `(snd format sh' buf) `data.

Definition deserialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, shs: share*share, len: Z
  PRE [ _p OF (tptr t), _buf OF (tptr tuchar), _length OF tint ] 
          PROP (writable_share (fst shs); 0 <= len <= fst format)
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf);
                        `(eq (Vint (Int.repr len))) (eval_id _length))
          SEP (`(snd format (snd shs) buf) `data;
                 `(memory_block (fst shs) (Int.repr (fst format)) p))
  POST [ tint ]
            `(snd format (snd shs) buf data) *
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

Definition message {t: type} (format: message_format t) (sh: share) (m: val) : mpred :=
  EX fg: val*val,
          func_ptr (serialize_spec format) (fst fg) &&
          func_ptr (deserialize_spec format) (snd fg) &&
       typed_mapsto t_struct_message sh m (Int.repr (fst format), (fst fg, snd fg)).

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
change (fst intpair_message) with (sizeof t_struct_intpair).
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
normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence.
compute; congruence.
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
change 8 with (sizeof t_struct_intpair).
rewrite memory_block_typed.
do 2 simpl_typed_mapsto.
destruct data as (x1,y1); simpl in *.
apply semax_pre_PQR with
 (PROP  (isptr buf)
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
go_lower; subst. rewrite field_mapsto_isptr. normalize.
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
simpl.
cancel.
rewrite sepcon_comm.
apply sepcon_derives;
apply derives_refl'; eapply mapsto_field_mapsto;  unfold field_offset; try (simpl; reflexivity);
 destruct buf0; inv H0; unfold eval_binop; simpl; reflexivity.
Qed.

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_typed_mapsto__top. 

Ltac get_global_function id :=
  eapply (semax_fun_id' id); [ reflexivity | simpl; reflexivity | ].

Lemma slide_func_ptr:
  forall f e R1 R, 
  SEPx (`(func_ptr' f) e :: R1 :: R) = SEPx ((`(func_ptr f) e && R1)::R).
Proof.
 intros. change SEPx with SEPx'; unfold SEPx'; unfold_coerce.
extensionality rho.
simpl. 
rewrite <- sepcon_assoc.
 f_equal.
unfold func_ptr'.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon; auto.
Qed.

Ltac get_global_function' id :=
  eapply (semax_fun_id' id); [ reflexivity | simpl; reflexivity | rewrite slide_func_ptr ].


Lemma globfun_eval_var:
  forall Delta rho id f,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  (Global_func f) ->
     exists b, exists z,  eval_var id (type_of_funspec f) rho = Vptr b z /\
             ge_of rho id = Some (Vptr b z, type_of_funspec f).
Proof.
intros.
unfold tc_environ, typecheck_environ in H.
repeat rewrite andb_true_iff in H. destruct H as [[[Ha Hb] Hc] Hd].
apply environ_lemmas.typecheck_ge_eqv in Hc. 
hnf in Hc.
specialize (Hc _ _ H1). destruct Hc as [b [i [Hc Hc']]].
exists b; exists i.
unfold eval_var; simpl.
apply environ_lemmas.typecheck_mode_eqv in Hd.
apply Hd in H1. 
destruct H1 as [? | [? ?]]; [ | congruence].
unfold Map.get; rewrite H. rewrite Hc.
rewrite eqb_type_refl; auto.
Qed.

Lemma  setup_globals:
  forall u XX, 
        local (tc_environ (func_tycontext f_main Vprog Gtot)) &&
PROP  ()
LOCAL ()
(SEPx
   (`(func_ptr (serialize_spec intpair_message))
      (eval_var _intpair_serialize
         (globtype (Global_func (serialize_spec intpair_message)))) &&
    (`(func_ptr (deserialize_spec intpair_message))
       (eval_var _intpair_deserialize
          (globtype (Global_func (deserialize_spec intpair_message)))) &&
     main_pre prog u) :: XX)) |-- PROP  ()  LOCAL ()  
                                                   (SEPx (`(message intpair_message Ews)  (eval_var _intpair_message t_struct_message)
                :: XX)).
Proof.
intros.
apply go_lower_lem9.
unfold PROPx; apply andp_derives; auto.
change SEPx with SEPx'; unfold LOCALx, SEPx', local; unfold_coerce; intro rho; normalize.
apply sepcon_derives; auto.
clear XX.
unfold main_pre.
 unfold message.
 apply exp_right with
   (eval_var _intpair_serialize (type_of_funspec (snd intpair_serialize_spec)) rho,
    eval_var _intpair_deserialize (type_of_funspec (snd intpair_deserialize_spec)) rho).
simpl @fst; simpl @snd.
 rewrite andp_assoc.
apply andp_derives; auto.
apply andp_derives; auto.
 destruct (globvar_eval_var _ _ _intpair_message _ H (eq_refl _) (eq_refl _))
  as [b [z [H97 H99]]].
 unfold globvars2pred,globvar2pred. simpl. rewrite H99.
 simpl gvar_volatile. cbv iota.
 simpl gvar_init. simpl readonly2share.
 destruct (globfun_eval_var _ _ _intpair_serialize _ H (eq_refl _) (eq_refl _))
  as [b1 [z1 [EV1 GE1]]].
 destruct (globfun_eval_var _ _ _intpair_deserialize _ H (eq_refl _) (eq_refl _))
  as [b2 [z2 [EV2 GE2]]].
 simpl in H97.
 simpl. rewrite H97, GE1, GE2. simpl.
 simpl in EV1; rewrite EV1.
 simpl in EV2; rewrite EV2. 
 simpl_typed_mapsto.
 simpl.
repeat rewrite Int.add_zero.
 rewrite Int.add_assoc.
 repeat rewrite sepcon_emp.
 repeat apply sepcon_derives; umapsto_field_mapsto_tac.
Qed.

Lemma subst_eval_var:
  forall id v id' t, subst id v (eval_var id' t) = eval_var id' t.
Proof.
intros. unfold subst, eval_var. extensionality rho.
simpl. auto.
Qed.
Hint Rewrite subst_eval_var : normalize.
Hint Rewrite subst_eval_var : subst.


Lemma semax_frame_PQR:
  forall Delta R1 R2 P Q P' Q' R1' c,
     closed_wrt_modvars c (SEPx R2) ->
     semax Delta (PROPx P (LOCALx Q (SEPx R1))) c 
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     semax Delta (PROPx P (LOCALx Q (SEPx (R1++R2)))) c 
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx (R1'++R2))))).
Proof.
intros.
replace (PROPx P (LOCALx Q (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * SEPx R2).
eapply semax_post0; [ | apply semax_frame; eassumption].
normalize.
apply derives_refl'. f_equal.
change SEPx with SEPx'. extensionality rho; unfold PROPx,LOCALx,SEPx'.
normalize.
f_equal. f_equal.
clear; induction R1'; simpl. apply emp_sepcon.
rewrite sepcon_assoc. f_equal. auto.
change SEPx with SEPx'. extensionality rho; unfold PROPx,LOCALx,SEPx'.
normalize.
f_equal. f_equal.
clear; induction R1; simpl. apply emp_sepcon.
rewrite sepcon_assoc. f_equal. auto.
Qed.

Lemma drop_local: forall  P Q1 Q R,
    (PROPx P (LOCALx (Q1::Q) R)) |-- (PROPx P (LOCALx Q R)).
Admitted.  (* temporary? *)

Lemma closed_wrt_eval_var:
  forall S id t, closed_wrt_vars S (eval_var id t).
Proof.
unfold closed_wrt_vars, eval_var; intros.
simpl.
auto.
Qed.
Hint Resolve closed_wrt_eval_var : closed.

Ltac frame_upto N :=
 match goal with |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                                 (Ssequence _ _) ?Post =>
  rewrite <- (firstn_skipn N R); simpl firstn; simpl skipn;
  eapply semax_seq'; 
  [apply semax_frame_PQR ; 
      [ unfold closed_wrt_modvars;  auto 50 with closed | ]
  | ]
end.

Lemma gather_SEP:
  forall R1 R2, 
    SEPx (R1 ++ R2) = SEPx (fold_right sepcon emp R1 :: R2).
Proof. 
intros. change SEPx with SEPx'.
unfold SEPx'.
extensionality rho.
induction R1; simpl. rewrite emp_sepcon; auto.
rewrite sepcon_assoc; f_equal; auto.
Qed.

Ltac gather_SEP N :=
 match goal with |- context [SEPx ?R] => 
   rewrite <- (firstn_skipn N R); simpl firstn; simpl skipn; rewrite gather_SEP;
   unfold fold_right; try  rewrite sepcon_emp
 end.

Ltac replace_SEP R :=
match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (?R1::_)))) _ _ =>
 let H := fresh in assert (H: R1 = R); [ | rewrite H; clear H]
end.


Lemma call_serialize:
 forall (Delta: tycontext) P Q R (ser id x: ident)
           (sh_obj : share) (e_obj: expr) (d_obj: environ -> val)
           (sh_p: share) (e_p: expr) (d_p: environ -> val)
           (sh_buf: share) (e_buf: expr) (d_buf: environ -> val)
           (t: type) (msg: message_format t)
             (v: reptype t),
 eval_lvalue e_obj = d_obj ->
 eval_expr e_p = d_p ->
 eval_lvalue e_buf = d_buf ->
 writable_share sh_buf ->
 closed_wrt_vars (modified2 (modified1 ser) (modified1 x)) 
             (PROPx P (LOCALx Q
     (SEPx (`(message msg sh_obj) d_obj :: 
               `(typed_mapsto t sh_p) d_p `v::
               `(typed_mapsto_ sh_buf (tarray tuchar (fst msg))) d_buf ::
                R)))) ->
 semax Delta
   (PROPx P (LOCALx Q
     (SEPx (`(message msg sh_obj) d_obj :: 
               `(typed_mapsto t sh_p) d_p `v::
               `(typed_mapsto_ sh_buf (tarray tuchar (fst msg))) d_buf ::
                R))))
   (Ssequence 
    (Sset ser 
     (Efield e_obj _serialize 
        (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint))))
      (Ssequence
           (Scall (Some x)
              (Etempvar _ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint)))
              (e_p :: e_buf :: nil))
           (Sset id (Etempvar x tint))))
    (normal_ret_assert (PROPx P (LOCALx Q
     (SEPx (`(message msg sh_obj) d_obj :: 
               `(typed_mapsto t Share.top) d_p `v::
               `(snd msg sh_buf) d_buf `v::
                R))))).
Admitted.
(* need to add a proof to message_format, that the
     representation of a  buf implies the typed_mapsto_ of the bufsize array *)

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function. simpl_stackframe_of.
name len _len.
name x _x.
name y _y.
name ser _ser.
name des _des.
repeat flatten_sepcon_in_SEP.
focus_SEP 1%nat.
focus_SEP 3%nat.
get_global_function' _intpair_deserialize.
get_global_function' _intpair_serialize.
eapply semax_pre.
apply setup_globals.
focus_SEP 3%nat.
rewrite -> seq_assoc.

frame_upto 1%nat.
simpl_typed_mapsto.
forward. (*  p.x = 1; *)
forward. (* p.y = 2; *)
apply drop_local.  (* tempory, should fix store_field_tac *)
simpl app.
simpl update_tycon. (* should forward do this? *)
gather_SEP 2%nat.
replace_SEP  (`(typed_mapsto t_struct_intpair Share.top)
                      (eval_var _p t_struct_intpair) `((Int.repr 1, Int.repr 2)) : assert).
simpl_typed_mapsto.
extensionality rho; unfold_coerce; simpl; rewrite sepcon_comm; reflexivity.

rewrite -> seq_assoc.
eapply semax_seq'.
focus_SEP 1%nat.
apply call_serialize; auto 50 with closed.
simpl update_tycon.
forward. (* ser = intpair_message.serialize; *)
redefine_Delta.
simpl eval_lvalue.
autorewrite with subst.

















