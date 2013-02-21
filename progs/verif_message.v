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


Lemma typed_mapsto_typed_mapsto_ :
  forall sh t v v', typed_mapsto sh t v v' |-- typed_mapsto_ sh t v.
Admitted.
Hint Resolve typed_mapsto_typed_mapsto_.
Hint Resolve field_mapsto_field_mapsto_.


(* message_format t = (length, f)
   where 
    f sh buf data  := the [data] is formatted into a message 
         at most [length] bytes, 
          stored starting at address [buf] with share [sh] *)

Record message_format (t: type) : Type :=
mf_build {
   mf_size: Z;
   mf_assert: forall (sh: share) (buf: val) (len: Z) (data: reptype t), mpred;
   mf_size_range:  0 <= mf_size <= Int.max_signed;
   mf_bufprop: forall sh buf len data, 
           mf_assert sh buf len data |-- 
                 !!(0 <= len <= mf_size) && memory_block sh (Int.repr len) buf;
   mf_restbuf := fun (sh: share) (buf: val) (len: Z) => 
                              memory_block sh (Int.repr (mf_size-len)) (offset_val buf (Int.repr len))
}.

Implicit Arguments mf_build [[t]].
Implicit Arguments mf_size [[t]].
Implicit Arguments mf_assert [[t]].
Implicit Arguments mf_bufprop [[t]].
Implicit Arguments mf_size_range [[t]].
Implicit Arguments mf_restbuf [[t]].
(* need to add a proof to message_format, that the
     representation of a  buf implies the typed_mapsto_ of the bufsize array *)

 
Program Definition intpair_message: message_format t_struct_intpair :=
  mf_build 8 (fun sh buf len data => !!(len=8) && typed_mapsto sh t_struct_intpair buf data) _ _.
Next Obligation.
compute; split; congruence.
Qed.
Next Obligation.
 normalize. repeat apply andp_right; try (apply prop_right; compute; congruence).
 change 8 with (sizeof t_struct_intpair). rewrite memory_block_typed. auto.
Qed.

Definition serialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ _p OF (tptr tvoid), _buf OF (tptr tuchar) ] 
          PROP (writable_share sh')
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf))
          SEP (`(typed_mapsto sh t p data); 
                 `(memory_block sh' (Int.repr (mf_size format)) buf))
  POST [ tint ]  
         EX len: Z, 
          local (`(eq (Vint (Int.repr len))) retval) &&
         `(typed_mapsto sh t p data)  
            * `(mf_assert format sh' buf len data) * `(mf_restbuf format sh' buf len).

Definition deserialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, shs: share*share, len: Z
  PRE [ _p OF (tptr tvoid), _buf OF (tptr tuchar), _length OF tint ] 
          PROP (writable_share (fst shs); 0 <= len <= mf_size format)
          LOCAL (`(eq p) (eval_id _p); `(eq buf) (eval_id _buf);
                        `(eq (Vint (Int.repr len))) (eval_id _length))
          SEP (`(mf_assert format (snd shs) buf len data);
                 `(memory_block (fst shs) (Int.repr (mf_size format)) p))
  POST [ tint ]
            `(mf_assert format (snd shs) buf len data) *
            `(typed_mapsto (fst shs) t p data).

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

Definition message (sh: share) {t: type} (format: message_format t) (m: val) : mpred :=
  EX fg: val*val,
          func_ptr (serialize_spec format) (fst fg) &&
          func_ptr (deserialize_spec format) (snd fg) &&
       typed_mapsto sh t_struct_message m (Int.repr (mf_size format), (fst fg, snd fg)).

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
change (mf_size intpair_message) with (sizeof t_struct_intpair).
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
apply exp_right with 8.
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
change (mf_size intpair_message) with (sizeof t_struct_intpair).
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
go_lower; subst.
simpl_typed_mapsto. simpl.
 rewrite field_mapsto_isptr. normalize.
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
 destruct buf0; inv H1; unfold eval_binop; simpl; reflexivity.
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
                                                   (SEPx (`(message Ews intpair_message)  (eval_var _intpair_message t_struct_message)
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

Definition serialize_A {t}  (msg: message_format t) : Type := 
  match serialize_spec msg with mk_funspec _ A _ _ => A  end.

Definition serialize_pre {t} (msg: message_format t)  :=
match serialize_spec msg as f 
     return match f with mk_funspec _ A _ _ => A -> assert end
with mk_funspec f A P Q => P end.

Definition serialize_post {t} (msg: message_format t)  :=
match serialize_spec msg as f 
     return match f with mk_funspec _ A _ _ => A -> assert end
with mk_funspec f A P Q => Q end.

Definition serialize_fsig {t} (msg: message_format t)  : funsig :=
match serialize_spec msg with mk_funspec f A P Q => f end.

Definition included {U} (S S': U -> Prop) := forall x, S x -> S' x.

Lemma closed_wrt_subset:
  forall (S S': ident -> Prop) (H: included S' S) B (f: environ -> B),
       closed_wrt_vars S f -> closed_wrt_vars S' f.
Proof.
intros. hnf. intros. specialize (H0 rho te').
apply H0.
intro i; destruct (H1 i); auto.
Qed.
Hint Resolve closed_wrt_subset : closed.

Lemma closed_wrt_Forall_subset:
  forall S S' (H: included S' S) B (f: list (environ -> B)),
 Forall (closed_wrt_vars S) f ->
 Forall (closed_wrt_vars S') f.
Proof.
induction f; simpl; auto.
intro.
inv H0.
constructor.
apply (closed_wrt_subset _ _ H). auto.
auto.
Qed.

Lemma forward_setx_closed_now':
  forall Delta P (Q: list (environ -> Prop)) (R: list assert) id e,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx P (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx P (LOCALx Q (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) (Sset id e) 
        (normal_ret_assert (PROPx P (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R)))).
Proof.
intros.
eapply semax_pre; [ | apply semax_set].
eapply derives_trans; [ | apply now_later].
apply andp_left2.
apply andp_right; auto.
apply andp_right; auto.
autorewrite with subst.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local,lift1; simpl.
apply prop_derives; simpl; intro; split; auto.
hnf; auto.
Qed.

Fixpoint list2ensemble  (l: list ident) : (ident -> Prop) :=
 match l with nil => modified0 | x::l' => modified2 (eq x) (list2ensemble l') end.

Definition temp_type_is (Delta: tycontext) (id: ident) (t: type) :=
   match (temp_types Delta) ! id with 
    Some (t',_) => t' = t
   | _ => False
  end.


(*
Lemma subst_make_args':
  forall id v (P: assert) fsig tl el,
  subst id v (`P (make_args' fsig (eval_exprlist tl el))) =  (`P (make_args' fsig (eval_exprlist tl el))).
Proof.
intros. unfold_coerce. extensionality rho; unfold subst.
f_equal. unfold make_args'.

induction (fst fsig); simpl; intros.
destruct tl; simpl.
unfold globals_only; unfold env_set; simpl; auto.
destruct el; simpl. reflexivity.


Admitted.
Hint Rewrite subst_make_args': normalize.
Hint Rewrite subst_make_args': subst.
*)

Lemma subst_make_args':
  forall id v (P: assert) fsig tl el,
  length tl = length el ->
  length (fst fsig) = length el ->
  subst id v (`P (make_args' fsig (eval_exprlist tl el))) = 
           (`P (make_args' fsig (subst id v (eval_exprlist tl el)))).
Proof.
intros. unfold_coerce. extensionality rho; unfold subst.
f_equal. unfold make_args'.
revert tl el H H0; induction (fst fsig); destruct tl,el; simpl; intros; inv H; inv H0.
reflexivity.
specialize (IHl _ _ H2 H1).
rewrite IHl. auto.
Qed.
Hint Rewrite subst_make_args' using (solve[reflexivity]) : subst.

Lemma closed_wrt_lvalue: forall S e,
  access_mode (typeof e) = By_reference ->
  closed_wrt_vars S (eval_expr e) -> closed_wrt_vars S (eval_lvalue e).
Proof.
intros.
destruct e; simpl in *; auto with closed;
unfold closed_wrt_vars in *;
intros; specialize (H0 _ _ H1); clear H1; unfold_coerce;
unfold deref_noload in *; rewrite H in H0; auto.
Qed.
Hint Resolve closed_wrt_lvalue : closed.

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
 typeof e_obj = t_struct_message ->
 (temp_type_is Delta ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint)) /\
  temp_type_is Delta x tint /\ temp_type_is Delta id tint ) ->
 writable_share sh_buf ->
 x <> ser /\ x <> id /\ id <> ser ->
 forall
  (AM_buf: access_mode (typeof e_buf) = By_reference)
  (CL_R: Forall (closed_wrt_vars (list2ensemble(ser::x::id::nil))) Q)
  (CL_R: Forall (closed_wrt_vars (list2ensemble(ser::x::id::nil))) R)
  (CL_obj: closed_wrt_vars (list2ensemble(ser::x::id::nil)) (eval_lvalue e_obj))
  (CL_p: closed_wrt_vars (list2ensemble(ser::x::id::nil)) (eval_expr e_p))
  (CL_buf: closed_wrt_vars (list2ensemble(ser::x::id::nil)) (eval_expr e_buf))
  (H6: PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- local (tc_lvalue Delta e_obj)),
 semax Delta
   (PROPx P (LOCALx (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil) :: Q)
     (SEPx (`(message sh_obj msg) d_obj :: 
               `(typed_mapsto sh_p t) d_p `v::
               `(typed_mapsto_ sh_buf (tarray tuchar (mf_size msg))) d_buf ::
                R))))
   (Ssequence 
    (Sset ser 
     (Efield e_obj _serialize 
        (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint))))
      (Ssequence
           (Scall (Some x)
              (Etempvar ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint)))
              (e_p :: e_buf :: nil))
           (Sset id (Etempvar x tint))))
    (normal_ret_assert (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj :: 
               `(typed_mapsto sh_p t) d_p `v::
               `(mf_assert msg sh_buf) d_buf (`Int.signed (`force_int (eval_id id))) `v::
               `(mf_restbuf msg sh_buf) d_buf (`Int.signed (`force_int (eval_id id))) ::
                R))))).
Proof.
intros.
destruct H5 as [H5a [H5b H5c]].
subst.
assert (CLser: included (eq ser) (list2ensemble(ser::x::id::nil))) by (intros ? ?; left; auto).
assert (CLx: included (eq x) (list2ensemble(ser::x::id::nil))) by (intros ? ?; right; left; auto).
assert (CLid: included (eq id) (list2ensemble(ser::x::id::nil))) by (intros ? ?; do 2 right; left; auto).
eapply semax_pre with
 (PROPx P
  (LOCALx (tc_lvalue Delta e_obj :: (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil) :: Q))
     (SEPx
        (`(message sh_obj msg) (eval_lvalue e_obj)
         :: `(typed_mapsto sh_p t) (eval_expr e_p) `v
            :: `(typed_mapsto_ sh_buf (tarray tuchar (mf_size msg)))
                 (eval_lvalue e_buf) :: R))) ).
change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local; unfold_coerce; intro rho; simpl.
normalize.
rewrite andp_assoc.
apply andp_right.
eapply derives_trans; [ |  apply H6].
change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local; unfold_coerce; simpl.
normalize.
normalize.
clear H6.
unfold message at 1.
normalize.
change (`(fun m : val =>
               EX  fg : val * val,
               func_ptr (serialize_spec msg) (fst fg) &&
               func_ptr (deserialize_spec msg) (snd fg) &&
               typed_mapsto sh_obj t_struct_message m
                 (Int.repr (mf_size msg), (fst fg, snd fg)))
              (eval_lvalue e_obj))
 with (EX fg: val*val,
            `(func_ptr (serialize_spec msg) (fst fg)) &&
            `(func_ptr (deserialize_spec msg) (snd fg)) &&
            `(typed_mapsto sh_obj t_struct_message)
                  (eval_lvalue e_obj)
                 `((Int.repr (mf_size msg), (fst fg, snd fg))) : assert).
extract_exists_in_SEP. intros [f g].
simpl @fst; simpl @ snd.
simpl_typed_mapsto.
apply semax_pre with
  (EX p:val, EX buf:val, |>(PROPx P
     (LOCALx (tc_lvalue Delta e_obj :: `(eq p) (eval_expr e_p)
                          :: `(eq buf) (eval_lvalue e_buf)  
                        :: (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil) :: Q))
        (SEPx
  (`(field_mapsto sh_obj t_struct_message _serialize) (eval_lvalue e_obj) `f ::
      `(func_ptr' (serialize_spec msg)) `f ::
    `(field_mapsto sh_obj t_struct_message _bufsize) (eval_lvalue e_obj)
                        `(Vint (Int.repr (mf_size msg))) :: 
     `(serialize_pre msg (v,p,buf,sh_p,sh_buf))
       (make_args' (serialize_fsig msg)
         (eval_exprlist (snd (split (fst (serialize_fsig msg)))) (e_p :: e_buf :: nil))) ::
      `(field_mapsto sh_obj t_struct_message _deserialize) (eval_lvalue e_obj) `g ::
    (*  `(func_ptr' (deserialize_spec msg)) `g :: *)
         R))))).
admit.  (* might work *)
apply extract_exists_pre; intro p.
apply extract_exists_pre; intro buf.
destruct H3 as [H3 [H3x H3id]]; unfold temp_type_is in H3;
revert H3; case_eq ((temp_types Delta) ! ser); intros; try contradiction.
destruct p0.
subst t0.
eapply semax_seq'.
eapply semax_load_field'; try reflexivity. auto.
apply H.
apply extract_exists_pre; intro old.

assert (CL_TC: closed_wrt_vars (list2ensemble(ser::x::id::nil))
  (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil))).
 admit.  (* should be fine *)
assert (C1:=closed_wrt_subset _ _ CLser).
assert (C2:=closed_wrt_Forall_subset _ _ CLser).
autorewrite with subst.
simpl eval_exprlist.
autorewrite with subst.
clear C1 C2.

focus_SEP 3 1.
 simpl.
   apply semax_pre_PQR with 
     (P':=PROPx P (LOCALx (tc_expr (initialized ser Delta)
                (Etempvar ser
                   (tptr
                      (Tfunction
                         (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint)))
              :: tc_exprlist  (initialized ser Delta) (snd (split (fst (serialize_fsig msg))))   (e_p :: e_buf :: nil) 
              :: `eq (eval_id ser) `f
         :: `(eq p) (eval_expr e_p) :: `(eq buf) (eval_lvalue e_buf) :: Q) 
       (SEPx (`(serialize_pre msg (v, p, buf, sh_p, sh_buf))
              (make_args'  (fst (serialize_fsig msg), snd (serialize_fsig msg))
                 (eval_exprlist (snd (split (fst (serialize_fsig msg))))
                    (e_p :: e_buf :: nil)))
            :: `(func_ptr' (serialize_spec msg))
                      (eval_expr
                         (Etempvar ser
                            (tptr
                               (Tfunction
                                  (Tcons (tptr tvoid)
                                     (Tcons (tptr tuchar) Tnil)) tint))))
                 :: `(field_mapsto sh_obj t_struct_message _serialize)
                            (eval_lvalue e_obj)  (eval_id ser) 
                  :: `(field_mapsto sh_obj t_struct_message _bufsize)
                       (eval_lvalue e_obj) `(Vint (Int.repr (mf_size msg)))
                 :: `(field_mapsto sh_obj t_struct_message _deserialize)
                            (eval_lvalue e_obj)  `g
                     :: R)))).

change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local; unfold_coerce; intro rho.
simpl. apply andp_derives; auto.
apply derives_extract_prop; intros [? [? [? [? [? ?]]]]].
apply andp_right. apply prop_right; repeat split; auto.
clear - H0 H.
admit.  (* should be fine *)
clear - H0 H6 CL_p CL_buf.
admit.  (* looks OK *)
subst f.  simpl. apply derives_refl.
simpl update_tycon.
eapply semax_seq'.
apply (semax_call' (initialized ser Delta) (serialize_A msg) (serialize_pre msg) (serialize_post msg)
   (v,p,buf,sh_p,sh_buf)  (Some x) (fst (serialize_fsig msg)) (snd (serialize_fsig msg))
   (Etempvar ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint)))
   (e_p :: e_buf :: nil) P).
reflexivity. simpl. auto.
apply extract_exists_pre; intro old'.
change (@substopt Prop (Some x)) with (@subst Prop x).
change (@substopt mpred (Some x)) with (@subst mpred x).
assert (C1:=closed_wrt_subset _ _ CLx).
assert (C2:=closed_wrt_Forall_subset _ _ CLx).
autorewrite with subst.
clear C1 C2.
simpl update_tycon.
eapply semax_post_flipped.
apply forward_setx.
apply andp_right; intro rho; apply prop_right.
hnf.
clear - H3x.
admit. (* straightforward *)
clear - H3id.
admit. (* straightforward *)
intros.
unfold normal_ret_assert.
normalize. intro old''.
assert (C1:=closed_wrt_subset _ _ CLid).
assert (C2:=closed_wrt_Forall_subset _ _ CLid).
unfold assert;
autorewrite with subst.
change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local; unfold_coerce; intro rho; simpl.
apply derives_extract_prop; intro; unfold normal_ret_assert; simpl.
repeat (apply derives_extract_prop; intro).
subst.
decompose [and] H1; clear H1.
apply andp_right; try apply prop_right; auto.
apply andp_right; try apply prop_right; auto.
unfold serialize_post, serialize_spec.
normalize. intro len.
intro.
subst.
rewrite H6;
rewrite <- H1.
simpl force_int.
cancel.
apply derives_trans with
((!!(0 <= len <= mf_size msg) && 
  mf_assert msg sh_buf (eval_lvalue e_buf rho) len v ) *
mf_restbuf msg sh_buf (eval_lvalue e_buf rho) len *
field_mapsto sh_obj t_struct_message _serialize (eval_lvalue e_obj rho)
  (eval_id ser rho) *
field_mapsto sh_obj t_struct_message _bufsize (eval_lvalue e_obj rho)
  (Vint (Int.repr (mf_size msg))) *
field_mapsto sh_obj t_struct_message _deserialize (eval_lvalue e_obj rho) g).
repeat apply sepcon_derives; auto.
apply andp_right; auto.
eapply derives_trans; [ apply mf_bufprop | ].
apply andp_left1; auto.
repeat rewrite sepcon_assoc.
rewrite sepcon_andp_prop'.
apply derives_extract_prop; intro.
assert (MMM: mf_size msg <= Int.max_signed).
apply mf_size_range.
rewrite Int.signed_repr by (unfold Int.min_signed; simpl; omega).
cancel.
unfold message.
apply exp_right with (eval_id ser rho, g).
apply andp_right.
admit.  (* need to preserve these from above *)
simpl_typed_mapsto.
simpl.
cancel.
Qed.


Lemma call_deserialize:
 forall (Delta: tycontext) P Q R (ser: ident)
           (sh_obj : share) (e_obj: expr) (d_obj: environ -> val)
           (sh_p: share) (e_p: expr) (d_p: environ -> val)
           (sh_buf: share) (e_buf: expr) (d_buf: environ -> val)
           (e_len: expr)  (d_len: environ -> Z) (t: type) (msg: message_format t)   (v: reptype t),
 eval_lvalue e_obj = d_obj ->
 eval_expr e_p = d_p ->
 eval_expr e_buf = d_buf ->
 writable_share sh_p ->
  (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj :: 
               `(typed_mapsto_ sh_p t) d_p::
               `(mf_assert msg sh_buf) d_buf d_len `v ::
                R)))) |-- local (`(fun n => 0 <= n <= mf_size msg) d_len) &&
                             local (`eq d_len (`Int.signed (`force_int (eval_expr e_len)))) ->
 closed_wrt_vars (modified1 ser)
             (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj :: 
               `(typed_mapsto_ sh_p t) d_p::
               `(mf_assert msg sh_buf) d_buf d_len `v ::
                R)))) ->
 semax Delta
   (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj :: 
               `(typed_mapsto_ sh_p t) d_p::
               `(mf_assert msg sh_buf) d_buf d_len`v ::
                R))))
   (Ssequence 
    (Sset ser 
     (Efield e_obj _deserialize 
        (tptr  (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid))))
      (Scall None
        (Etempvar ser (tptr  (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid)))
          (e_p :: e_buf :: e_len :: nil)))
    (normal_ret_assert (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj :: 
               `(typed_mapsto sh_p t) d_p `v::
               `(mf_assert msg sh_buf) d_buf d_len`v::
                R))))).
Admitted.

Lemma intpair_message_length:
  forall sh p (len: environ -> Z) v P Q R,
    (PROPx P (LOCALx Q (SEPx
       (`(mf_assert intpair_message sh) p len v :: R)))) |--
   (PROPx P 
        (LOCALx (`(eq (mf_size intpair_message)) len :: Q)
         (SEPx (`(mf_assert intpair_message sh) p len v :: R)))).
Proof.
intros.
change SEPx with SEPx'; 
unfold PROPx, LOCALx, SEPx', local; intro rho; simpl.
apply andp_derives; auto.
unfold_coerce.
normalize.
Qed.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function. simpl_stackframe_of.
name len _len.
name x _x.
name y _y.
name ser _ser.
name des _des.
repeat flatten_sepcon_in_SEP.
focus_SEP 3 1.
get_global_function' _intpair_deserialize.
get_global_function' _intpair_serialize.
eapply semax_pre.
apply setup_globals.
focus_SEP 3.
rewrite -> seq_assoc.

frame_upto 1%nat.
simpl_typed_mapsto.
forward. (*  p.x = 1; *)
forward. (* p.y = 2; *)
apply drop_local.  (* tempory, should fix store_field_tac *)
simpl app.
simpl update_tycon. (* should forward do this? *)
gather_SEP 2%nat.
replace_SEP  (`(typed_mapsto Share.top t_struct_intpair)
                      (eval_var _p t_struct_intpair) `((Int.repr 1, Int.repr 2)) : assert).
simpl_typed_mapsto.
extensionality rho; unfold_coerce; simpl; rewrite sepcon_comm; reflexivity.

rewrite -> seq_assoc.
eapply semax_seq'.
focus_SEP 1.
replace_in_pre (nil: list (environ -> Prop)) (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil)
          ((Eaddrof (Evar _p t_struct_intpair) (tptr t_struct_intpair)
            :: Evar _buf (tarray tuchar 8) ::  nil))::nil).
apply go_lower_lem9.
go_lower.
apply andp_right; try apply prop_right; auto.
apply call_serialize; repeat split; simpl; auto 50 with closed; auto.
intro rho. apply prop_right. hnf. auto.
simpl update_tycon.
redefine_Delta.
focus_SEP 2.
eapply semax_pre0; [apply intpair_message_length | ].
focus_SEP 1 4.
rewrite -> seq_assoc.
eapply semax_seq'.
apply call_deserialize; auto 50 with closed.
go_lower. apply andp_right; apply prop_right.
simpl in H. omega. simpl in *. rewrite <- H.  reflexivity. 
focus_SEP 1.
replace_SEP 
  ((`(field_mapsto Share.top t_struct_intpair _x) (eval_var _q t_struct_intpair) `(Vint (Int.repr 1)) *
   `(field_mapsto Share.top t_struct_intpair _y) (eval_var _q t_struct_intpair) `(Vint (Int.repr 2)))
    : assert).
reflexivity.
flatten_sepcon_in_SEP.
forward. (* x = q.x; *)
forward. (* y = q.y; *)
forward. (* return x+y; *)
go_lower. subst. simpl. normalize. unfold main_post.
 simpl in H2. rewrite <- H2.
 unfold mf_restbuf; simpl. rewrite memory_block_zero. rewrite sepcon_emp.

repeat rewrite <- sepcon_assoc.
apply derives_trans with
( typed_mapsto_ Share.top t_struct_intpair
      (eval_var _q t_struct_intpair rho) 
 * TT 
 * typed_mapsto_ Share.top (tarray tuchar 8)
      (eval_var _buf (tarray tuchar 8) rho)
 *  typed_mapsto_ Share.top t_struct_intpair
      (eval_var _p t_struct_intpair rho)).
repeat apply sepcon_derives; auto.
simpl_typed_mapsto; simpl. rewrite sepcon_comm; apply sepcon_derives; auto.
rewrite <- memory_block_typed.
change (sizeof (tarray tuchar 8)) with (sizeof t_struct_intpair).
rewrite memory_block_typed. auto.
cancel.
Qed.











