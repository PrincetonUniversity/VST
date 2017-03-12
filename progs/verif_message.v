Require Import floyd.proofauto.
Require Import progs.message.

Local Open Scope Z.
Local Open Scope logic.

(*   mf_assert msgfmt sh buf len data  := the [data] is formatted into a message
         at most [len] bytes,  stored starting at address [buf] with share [sh] *)


Definition natural_alignment := 8.

Lemma natural_alignment_enough: forall t, type_is_by_value t = true -> legal_alignas_type t = true -> (alignof t | 8).
Proof.
  intros.
  assert (1 | 8). exists 8. reflexivity.
  assert (2 | 8). exists 4. reflexivity.
  assert (4 | 8). exists 2. reflexivity.
  assert (8 | 8). exists 1. reflexivity.
  destruct t; try inversion H; simpl;
  unfold legal_alignas_type in H0; simpl in H0;
  destruct (attr_alignas a); inversion H0; [destruct i| | destruct f|]; assumption.
Qed.

Definition natural_align_compatible p :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs)
  | _ => True
  end.

Record message_format (t: type) : Type :=
mf_build {
   mf_size: Z;
   mf_data_assert: forall (data: reptype t), Prop;
   mf_assert: forall (sh: share) (buf: val) (len: Z) (data: reptype t), mpred;
   mf_size_range:  0 <= mf_size <= Int.max_signed;
   mf_bufprop: forall sh buf len data,
           mf_assert sh buf len data |--
                 !!(0 <= len <= mf_size) && memory_block sh (Int.repr len) buf;
   mf_restbuf := fun (sh: share) (buf: val) (len: Z) =>
          memory_block sh (Int.repr (mf_size-len)) (offset_val (Int.repr len) buf)
}.

Implicit Arguments mf_build [[t]].
Implicit Arguments mf_size [[t]].
Implicit Arguments mf_data_assert [[t]].
Implicit Arguments mf_assert [[t]].
Implicit Arguments mf_bufprop [[t]].
Implicit Arguments mf_size_range [[t]].
Implicit Arguments mf_restbuf [[t]].
(* need to add a proof to message_format, that the
     representation of a  buf implies the data_at_ of the bufsize array *)

Program Definition intpair_message: message_format t_struct_intpair :=
  mf_build 8 (fun data => is_int I32 Signed (fst data) /\ is_int I32 Signed (snd data))
             (fun sh buf len data => !!(len=8/\ is_int I32 Signed (fst data) /\ is_int I32 Signed (snd data))
                           && data_at sh (tarray tint 2) [fst data; snd data] buf)
      _ _.
Next Obligation.
compute; split; congruence.
Qed.
Next Obligation.
  normalize.
  eapply derives_trans; [apply data_at_data_at_; reflexivity|].
  rewrite data_at__memory_block by reflexivity.
  apply andp_right; [apply prop_right; omega|].
  simpl.
  apply andp_left2.
  apply derives_refl.
Qed.

(* align_compatible requirement is neccesary in precondition *)
Definition serialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ _p OF (tptr tvoid), _buf OF (tptr tuchar) ]
          PROP (writable_share sh';
                mf_data_assert format data;
                natural_align_compatible buf)
          LOCAL (temp _p p; temp _buf buf)
          SEP (`(data_at sh t data p);
               `(memory_block sh' (Int.repr (mf_size format)) buf))
  POST [ tint ]
         EX len: Z,
          local (`(eq (Vint (Int.repr len))) retval) &&
         `(data_at sh t data p)
            * `(mf_assert format sh' buf len data) * `(mf_restbuf format sh' buf len).

Definition deserialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, shs: share*share, len: Z
  PRE [ _p OF (tptr tvoid), _buf OF (tptr tuchar), _length OF tint ]
          PROP (writable_share (fst shs);
                0 <= len <= mf_size format)
          LOCAL (temp _p p;
                 temp _buf buf;
                 temp _length (Vint (Int.repr len)))
          SEP (`(mf_assert format (snd shs) buf len data);
               `(data_at_ (fst shs) t p))
  POST [ tvoid ]
          PROP (mf_data_assert format data)  LOCAL ()
          SEP (`(mf_assert format (snd shs) buf len data);
                 `(data_at (fst shs) t data p)).

Definition intpair_serialize_spec :=
 DECLARE _intpair_serialize (serialize_spec intpair_message).

Definition intpair_deserialize_spec :=
 DECLARE _intpair_deserialize (deserialize_spec intpair_message).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Vprog : varspecs := (_intpair_message, t_struct_message)::nil.

Definition message (sh: share) {t: type} (format: message_format t) (m: val) : mpred :=
  EX fg: val*val,
          func_ptr (serialize_spec format) (fst fg) &&
          func_ptr (deserialize_spec format) (snd fg) &&
       data_at sh t_struct_message (Vint (Int.repr (mf_size format)), (fst fg, snd fg)) m.

Definition Gprog : funspecs :=   ltac:(with_library prog [
    intpair_serialize_spec; intpair_deserialize_spec; main_spec]).

Lemma body_intpair_serialize: semax_body Vprog Gprog f_intpair_serialize intpair_serialize_spec.
Proof.
unfold intpair_serialize_spec.
unfold serialize_spec.
start_function.
name p0 _p.
name buf0 _buf.
name x _x.
name y _y.
destruct H0 as [Dx Dy].
destruct data as [[|x1 | | | | ] [|y1 | | | | ]]; try contradiction. clear Dx Dy.

unfold_data_at 1%nat.
change (mf_size intpair_message) with (sizeof (tarray tint 2)).
rewrite memory_block_data_at_; try reflexivity.
Focus 2. {
  unfold natural_align_compatible in H1.
  unfold align_compatible.
  destruct buf; auto.
  eapply Z.divide_trans; [| exact H1].
  exists 2.
  cbv.
  reflexivity.
} Unfocus.

forward. (* x = p->x; *)
forward. (* y = p->y; *)
forward. (*  ((int * )buf)[0]=x; *)
forward. (*  ((int * )buf)[1]=y; *)
forward. (* return 8; *)
apply exp_right with 8.
entailer.

unfold_data_at 2%nat.
cancel.
unfold mf_restbuf. simpl.
destruct buf0; inv Pbuf0.
simpl. rewrite memory_block_zero.
entailer!.
Qed.

Lemma body_intpair_deserialize: semax_body Vprog Gprog f_intpair_deserialize intpair_deserialize_spec.
Proof.
unfold intpair_deserialize_spec, deserialize_spec.
start_function. destruct shs as (sh,sh'). simpl @fst; simpl @snd.
name p0 _p.
name buf0 _buf.
name x _x.
name y _y.
name len0 _length.
destruct data as (x1,y1); simpl in *.
normalize.
destruct x1 as [|x1| | | |]; try contradiction.
destruct y1 as [|y1| | | |]; try contradiction.
clear H2 H3.

forward. (* x = ((int * )buf)[0]; *)
forward. (* y = ((int * )buf)[1]; *)
forward. (* p->x = x; *)
forward. (*  p->y = y; *)
forward.  (* return; *)
Qed.

Ltac simpl_stackframe_of :=
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_data_at_ by reflexivity.

Ltac get_global_function id :=
  eapply (call_lemmas.semax_fun_id' id); [ reflexivity | simpl; reflexivity | ].

Lemma slide_func_ptr:
  forall f e R1 R,
  SEPx (`(func_ptr' f) e :: R1 :: R) = SEPx ((`(func_ptr f) e && R1)::R).
Proof.
 intros. unfold SEPx; unfold_lift.
extensionality rho.
simpl.
rewrite <- sepcon_assoc.
 f_equal.
unfold func_ptr'.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon; auto.
Qed.

Ltac get_global_function' id :=
  eapply (call_lemmas.semax_fun_id' id); [ reflexivity | reflexivity | simpl; reflexivity | rewrite slide_func_ptr ].

Lemma  create_message_object:
 forall t (msg: message_format t) objid serid desid
 (Vobj: (var_types (func_tycontext f_main Vprog Gprog)) ! objid = None)
 (Gobj: (glob_types (func_tycontext f_main Vprog Gprog)) ! objid = Some (t_struct_message))
 (Vser: (var_types (func_tycontext f_main Vprog Gprog)) ! serid = None)
 (Gser: (glob_types (func_tycontext f_main Vprog Gprog)) ! serid =
                                   Some (type_of_funspec (serialize_spec msg)))
 (Vdes: (var_types (func_tycontext f_main Vprog Gprog)) ! desid = None)
 (Gdes: (glob_types (func_tycontext f_main Vprog Gprog)) ! desid =
                                   Some (type_of_funspec (deserialize_spec msg))),
PROP  ()
LOCAL (tc_environ (func_tycontext f_main Vprog Gprog))
SEP
   (`(func_ptr (serialize_spec msg))
      (eval_var serid
         (type_of_funspec (serialize_spec msg))) &&
    (`(func_ptr (deserialize_spec msg))
       (eval_var desid
          (type_of_funspec  (deserialize_spec msg))) &&
  (id2pred_star (func_tycontext f_main Vprog Gprog) Ews t_struct_message
    (eval_var objid t_struct_message) 0
    (Init_int32 (Int.repr (mf_size msg))
     :: Init_addrof serid (Int.repr 0)
        :: Init_addrof desid (Int.repr 0) :: nil))))
  |-- PROP()  LOCAL() SEP (`(message Ews msg)  (eval_var objid t_struct_message)).
Proof.
intros.
unfold id2pred_star, init_data2pred'.
 rewrite Vser,Vdes. rewrite Gser,Gdes.
go_lower.
normalize.
 unfold message.
 apply exp_right with
 (eval_var serid
     (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint cc_default) rho,
 eval_var desid
      (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tint Tnil)))
         tvoid cc_default) rho).
rewrite andp_assoc.
apply andp_derives; auto.
apply andp_derives; auto.
 simpl_data_at.
 simpl.
 normalize.
    rewrite mapsto_tuint_tint.
 destruct (globvar_eval_var _ _ objid _ H Vobj Gobj) as [b1 [Eobj _]].
 simpl in Eobj; rewrite Eobj. clear dependent objid.
 destruct (globvar_eval_var _ _ serid _ H Vser Gser) as [b2 [Eser _]].
 simpl in Eser; rewrite Eser; clear dependent serid.
 destruct (globvar_eval_var _ _ desid _ H Vdes Gdes) as [b3 [Edes _]].
 simpl in Edes; rewrite Edes; clear dependent desid.
 apply andp_right.
 + apply prop_right.
   unfold size_compatible, align_compatible.
   split; simpl.
   cbv; intros; inversion H0.
   change (Int.unsigned Int.zero) with 0.
   split3.
   apply Z.divide_0_r.  reflexivity. reflexivity.
 + repeat apply sepcon_derives.
   normalize.
   simpl offset_val.
   rewrite  int_add_repr_0_r.
   normalize.
   simpl offset_val.
   rewrite int_add_repr_0_r.
   normalize.
Qed.

Definition serialize_A {t}  (msg: message_format t) : Type :=
  match serialize_spec msg with mk_funspec _ A _ _ => A  end.

Definition serialize_pre {t} (msg: message_format t)  :=
match serialize_spec msg as f
     return match f with mk_funspec _ A _ _ => A -> environ->mpred end
with mk_funspec f A P Q => P end.

Definition serialize_post {t} (msg: message_format t)  :=
match serialize_spec msg as f
     return match f with mk_funspec _ A _ _ => A -> environ->mpred end
with mk_funspec f A P Q => Q end.

Definition serialize_fsig {t} (msg: message_format t)  : funsig :=
match serialize_spec msg with mk_funspec f A P Q => f end.

Fixpoint list2idset'  (l: list ident) : idset :=
 match l with nil => idset0  | x::l' => insert_idset x (list2idset' l') end.

Definition list2idset  (l: list ident) (id: ident)  :=
  isSome ((list2idset' l) ! id).

Definition temp_type_is (Delta: tycontext) (id: ident) (t: type) :=
   match (temp_types Delta) ! id with
    Some (t',_) => t' = t
   | _ => False
  end.

Lemma subst_make_args'x
     : forall (id : ident) (v : environ -> val)
         (fsig : list (ident * type) * type) (tl : list type)
         (el : list expr),
       length tl = length el ->
       length (fst fsig) = length el ->
       subst id v (make_args' fsig (eval_exprlist tl el)) =
        make_args' fsig (subst id v (eval_exprlist tl el)).
Proof.
intros. unfold_lift. extensionality rho; unfold subst.
unfold make_args'.
revert tl el H H0; induction (fst fsig); destruct tl,el; simpl; unfold lift; intros; inv H; inv H0.
reflexivity.
specialize (IHl _ _ H2 H1).
unfold_lift; rewrite IHl. auto.
Qed.
Hint Rewrite subst_make_args'x using (solve[reflexivity]) : subst.

Lemma func_ptr_isptr:
 forall spec f, func_ptr spec f |-- !! isptr f.
Proof.
Admitted.  (* needs to go in veric *)
Hint Resolve func_ptr_isptr: saturate_local.

Section HINTS.
Hint Resolve closed_wrt_eval_expr : closed.
Hint Resolve closed_wrt_lvalue : closed.

Lemma call_serialize:
 forall Espec (Delta: tycontext) (ser id x: ident)
           (sh_obj : share) (e_obj: expr) (d_obj: environ -> val)
           (sh_p: share) (e_p: expr) (d_p: environ -> val)
           (sh_buf: share) (e_buf: expr) (d_buf: environ -> val)
           (t: type) (msg: message_format t)
             (v: reptype t),
 eval_lvalue e_obj = d_obj ->
 eval_expr e_p = d_p ->
 eval_lvalue e_buf = d_buf ->
 typeof e_obj = t_struct_message ->
 (temp_type_is Delta ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint cc_default)) /\
  temp_type_is Delta x tint /\ temp_type_is Delta id tint ) ->
 writable_share sh_buf ->
 x <> ser /\ x <> id /\ id <> ser ->
 forall
  (AM_buf: access_mode (typeof e_buf) = By_reference)
  (CL_obj: closed_wrt_vars (list2idset(ser::x::id::nil)) (eval_lvalue e_obj))
  (CL_p: closed_wrt_vars (list2idset(ser::x::id::nil)) (eval_expr e_p))
  (CL_buf: closed_wrt_vars (list2idset(ser::x::id::nil)) (eval_expr e_buf))
  (H6: local (tc_environ Delta) |-- local (tc_lvalue Delta e_obj)),
 @semax Espec Delta
   (PROP ()
    (LOCAL (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil))
     SEP (`(message sh_obj msg) d_obj ;
               `(data_at sh_p t v) d_p;
               `(data_at_ sh_buf (tarray tuchar (mf_size msg))) d_buf)))
   (Ssequence
    (Sset ser
     (Efield e_obj _serialize
        (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint cc_default))))
      (Ssequence
           (Scall (Some x)
              (Etempvar ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint cc_default)))
              (e_p :: e_buf :: nil))
           (Sset id (Etempvar x tint))))
    (normal_ret_assert (PROP () LOCAL()
      SEP (`(message sh_obj msg) d_obj;
               `(data_at sh_p t v) d_p;
               `(mf_assert msg sh_buf) d_buf (`Int.signed (`force_int (eval_id id))) `v;
               `(mf_restbuf msg sh_buf) d_buf (`Int.signed (`force_int (eval_id id)))))).
Proof.
intros.
destruct H5 as [H5a [H5b H5c]].
subst.
assert (CLser: included (eq ser) (list2idset(ser::x::id::nil))) by admit.
assert (CLx: included (eq x) (list2idset(ser::x::id::nil))) by admit.
assert (CLid: included (eq id) (list2idset(ser::x::id::nil))) by admit.
eapply semax_pre with
 (PROP()
  LOCAL (tc_lvalue Delta e_obj ; tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil))
  SEP (`(message sh_obj msg) (eval_lvalue e_obj);
        `(data_at sh_p t v) (eval_expr e_p);
        `(data_at_ sh_buf (tarray tuchar (mf_size msg))) (eval_lvalue e_buf))).
go_lowerx.
normalize. rewrite prop_and.
repeat apply andp_right; auto.
eapply derives_trans; [ |  apply H6].
apply prop_right; auto.
apply prop_right; auto.
clear H6.
unfold message at 1.
replace_SEP 0%Z (EX fg: val*val,
            `(func_ptr (serialize_spec msg) (fst fg)) &&
            `(func_ptr (deserialize_spec msg) (snd fg)) &&
            `(data_at sh_obj t_struct_message ((Vint (Int.repr (mf_size msg)), (fst fg, snd fg))))
                  (eval_lvalue e_obj)).
entailer. apply exp_right with x0. entailer.
extract_exists_in_SEP. intros [f g].
simpl @fst; simpl @ snd.
match goal with |- semax _ (PROPx nil ?QR) _ _ =>
 apply semax_pre with (PROP (isptr f) QR)
end.
go_lowerx. entailer.
repeat rewrite sepcon_assoc.
eapply derives_trans. apply sepcon_derives.
apply andp_left1. apply func_ptr_isptr.
apply TT_right.
rewrite sepcon_prop_prop. apply prop_derives; intuition.
normalize.
apply semax_pre with
  (EX p:val, EX buf:val, |>(PROP()
     LOCAL(tc_lvalue Delta e_obj; `(eq p) (eval_expr e_p);
                     `(eq buf) (eval_lvalue e_buf);
                     (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil) (e_p :: e_buf :: nil)))
      SEP
  (`(field_at sh_obj t_struct_message [StructField _serialize] f) (eval_lvalue e_obj);
      `(func_ptr' (serialize_spec msg)) `f;
    `(field_at sh_obj t_struct_message [StructField _bufsize] (Vint (Int.repr (mf_size msg))))
                            (eval_lvalue e_obj);
     `(serialize_pre msg (v,p,buf,sh_p,sh_buf))
       (make_args' (serialize_fsig msg)
         (eval_exprlist (snd (split (fst (serialize_fsig msg)))) (e_p :: e_buf :: nil)));
      `(field_at sh_obj t_struct_message [StructField _deserialize] g) (eval_lvalue e_obj)))).
admit.  (* might work *)
apply extract_exists_pre; intro p.
apply extract_exists_pre; intro buf.
destruct H3 as [H3 [H3x H3id]]; unfold temp_type_is in H3;
revert H3; case_eq ((temp_types Delta) ! ser); intros; try contradiction.
destruct p0.
subst t0.


eapply semax_seq'.
{
  change (Efield e_obj _serialize
           (tptr
              (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint
                 cc_default))) with
  (nested_efield e_obj (eStructField _serialize :: nil) ((tptr
              (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint
                 cc_default)) :: nil)).
Admitted.
(*
  apply semax_max_path_field_load_37'
   with (t0 := (tptr
          (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint
             cc_default)))
     (e:= PTree.empty _)(sh := sh_obj) (v':= valinject (nested_field_type (typeof e_obj) (StructField _serialize :: @nil gfield)) f) (*t:= t_struct_message*);
    try assumption; try rewrite H2; try reflexivity.
  admit.  (* closed...  should be fine *)
   admit.  (* closed...  should be fine *)
 unfold typeof_temp; rewrite H0. reflexivity.
 go_lowerx; entailer.
 simpl. cancel.
 entailer!.
 hnf. simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
 rewrite H2. simpl. hnf; auto.
}
rename H into H'.
focus_SEP 3 1.
   apply semax_pre with
     (P':=PROP () LOCAL (tc_expr (initialized ser Delta)
                (Etempvar ser
                   (tptr
                      (Tfunction
                         (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint cc_default)));
              tc_exprlist  (initialized ser Delta) (snd (split (fst (serialize_fsig msg))))   (e_p :: e_buf :: nil);
              `eq (eval_id ser) `f;
              `(eq p) (eval_expr e_p);  `(eq buf) (eval_lvalue e_buf))
       (SEP (`(serialize_pre msg (v, p, buf, sh_p, sh_buf))
              (make_args'  (fst (serialize_fsig msg), snd (serialize_fsig msg))
                 (eval_exprlist (snd (split (fst (serialize_fsig msg))))
                    (e_p :: e_buf :: nil)));
            `(func_ptr' (serialize_spec msg))
                      (eval_expr
                         (Etempvar ser
                            (tptr
                               (Tfunction
                                  (Tcons (tptr tvoid)
                                     (Tcons (tptr tuchar) Tnil)) tint cc_default))));
             `(field_at sh_obj t_struct_message [_serialize])  (eval_id ser)
                            (eval_lvalue e_obj);
              `(field_at sh_obj t_struct_message [_bufsize] (Vint (Int.repr (mf_size msg))))
                       (eval_lvalue e_obj);
               `(field_at sh_obj t_struct_message [_deserialize] g)
                            (eval_lvalue e_obj)))).
go_lowerx. subst.
apply andp_right; auto.
apply prop_right.
repeat split; auto.
hnf. unfold typecheck_expr.
simpl negb. cbv iota.
rewrite (temp_types_init_same _ _ _ _ H0).
apply I.
hnf in H8|-*.
unfold typecheck_exprlist in H8|-*.
repeat rewrite denote_tc_assert_andp in H8|-*.
destruct H8 as [? [? _]]; repeat split; auto.
apply tc_expr_init; auto.
apply tc_expr_init; auto.
eapply semax_seq'.
apply (call_lemmas.semax_call' Espec (initialized ser Delta) (serialize_A msg) (serialize_pre msg) (serialize_post msg)
   (v,p,buf,sh_p,sh_buf)  (Some x) (fst (serialize_fsig msg)) (snd (serialize_fsig msg))
   (Etempvar ser (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint cc_default)))
   (e_p :: e_buf :: nil)).
reflexivity. simpl. auto.
hnf.
rewrite <- (expr_lemmas.initialized_ne Delta x ser)
 by auto.
hnf in H3x. destruct ((temp_types Delta) ! x); try contradiction.
destruct p0; subst. reflexivity.
apply extract_exists_pre; intro old'.
change (@substopt Prop (Some x)) with (@subst Prop x).
change (@substopt mpred (Some x)) with (@subst mpred x).
assert (C1:=closed_wrt_subset _ _ CLx).
assert (C2:=closed_wrt_Forall_subset _ _ CLx).
autorewrite with subst.
clear C1 C2.
simpl update_tycon.
eapply semax_post_flipped.
apply forward_lemmas.forward_setx.
apply andp_right; intro rho; apply prop_right.
hnf.
clear - H3x.
admit. (* straightforward *)
clear - H3id.
admit. (* straightforward *)
intros.
unfold normal_ret_assert.
repeat rewrite exp_andp2. apply exp_left; intro old''.
assert (C1:=closed_wrt_subset _ _ CLid).
assert (C2:=closed_wrt_Forall_subset _ _ CLid).
autorewrite with subst.
normalize.
unfold SeparationLogic.maybe_retval.
change (fun rho : environ =>
    serialize_post msg (v, p, buf, sh_p, sh_buf) (get_result1 x rho))
 with (`(serialize_post msg (v, p, buf, sh_p, sh_buf)) (get_result1 x)).
simpl @snd.
change(maybe_retval (serialize_post msg (v, p, buf, sh_p, sh_buf)) tint (Some x))
  with (`(serialize_post msg (v, p, buf, sh_p, sh_buf)) (get_result1 x)).
autorewrite with subst.
go_lowerx. normalize.
unfold serialize_post, serialize_spec.
normalize. rename x0 into len.
subst.

rewrite H3;
rewrite <- H9.
simpl force_int.
cancel.
apply derives_trans with
((!!(0 <= len <= mf_size msg) &&
  mf_assert msg sh_buf (eval_lvalue e_buf rho) len v ) *
mf_restbuf msg sh_buf (eval_lvalue e_buf rho) len *
field_at sh_obj t_struct_message [_serialize]
    (eval_id ser rho) (eval_lvalue e_obj rho)
  *
field_at sh_obj t_struct_message [_bufsize]
    (Vint (Int.repr (mf_size msg))) (eval_lvalue e_obj rho)
  *
field_at sh_obj t_struct_message [_deserialize] g (eval_lvalue e_obj rho)).
repeat apply sepcon_derives; auto.
apply andp_right; auto.
eapply derives_trans; [ apply mf_bufprop | ].
apply andp_left1; auto.
repeat rewrite sepcon_assoc.
rewrite sepcon_andp_prop'.
apply derives_extract_prop; intro.
assert (MMM: mf_size msg <= Int.max_signed).
apply mf_size_range.
rewrite Int.signed_repr by repable_signed.
cancel.
unfold message.
apply exp_right with (eval_id ser rho, g).
apply andp_right.
admit.  (* need to preserve these from above *)
rename H into HYP. (*remove when simpl_data_at is fixed (explanation in verif_queue)*)
simpl_data_at; try reflexivity.
simpl.
normalize.
unfold at_offset.
normalize.
cancel.
Qed.
*)

Lemma call_deserialize:
 forall Espec (Delta: tycontext) P Q R (ser: ident)
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
               `(data_at_ sh_p t) d_p::
               `(mf_assert msg sh_buf) d_buf d_len `v ::
                R)))) |-- local (`((fun n => 0 <= n <= mf_size msg) : Z->Prop) d_len) &&
                             local (`eq d_len (`Int.signed (`force_int (eval_expr e_len)))) ->
 closed_wrt_vars (eq ser)
             (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj ::
               `(data_at_ sh_p t) d_p::
               `(mf_assert msg sh_buf) d_buf d_len `v ::
                R)))) ->
 @semax Espec Delta
   (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj ::
               `(data_at_ sh_p t) d_p::
               `(mf_assert msg sh_buf) d_buf d_len`v ::
                R))))
   (Ssequence
    (Sset ser
     (Efield e_obj _deserialize
        (tptr  (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid cc_default))))
      (Scall None
        (Etempvar ser (tptr  (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid cc_default)))
          (e_p :: e_buf :: e_len :: nil)))
    (normal_ret_assert (PROPx P (LOCALx Q
     (SEPx (`(message sh_obj msg) d_obj ::
               `(data_at sh_p t v) d_p::
               `(mf_assert msg sh_buf) d_buf d_len`v::
                R))))).
Admitted.

End HINTS.

Lemma intpair_message_length:
  forall sh p (len: environ -> Z) v P Q R,
    (PROPx P (LOCALx Q (SEPx
       (`(mf_assert intpair_message sh) p len v :: R)))) |--
   (PROPx P
        (LOCALx (`(eq (mf_size intpair_message)) len :: Q)
         (SEPx (`(mf_assert intpair_message sh) p len v :: R)))).
Proof.
intros.
unfold PROPx, LOCALx, SEPx, local; intro rho; simpl.
apply andp_derives; auto.
unfold_lift.
normalize.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function. unfold MORE_COMMANDS, abbreviate.
simpl_stackframe_of.
name len _len.
name x _x.
name y _y.
name ser _ser.
name des _des.
normalize.
repeat flatten_sepcon_in_SEP.
focus_SEP 3 1.
get_global_function' _intpair_deserialize.
get_global_function' _intpair_serialize.
eapply semax_pre.
frame_SEP' (0::nil).
unfold main_pre, globvars2pred, prog_vars. simpl map.
apply create_message_object; reflexivity.
unfold app.

apply (remember_value (eval_var _p t_struct_intpair)); intros p.
apply (remember_value (eval_var _q t_struct_intpair)); intros q.
apply (remember_value (eval_var _intpair_message t_struct_message)); intros ipm.
apply (remember_value (eval_var _buf (tarray tuchar 8))); intros buf.
eapply semax_pre with
(P' := (PROP  ()
      LOCAL  (`(eq buf) (eval_var _buf (tarray tuchar 8));
      `(eq ipm) (eval_var _intpair_message t_struct_message);
      `(eq q) (eval_var _q t_struct_intpair);
      `(eq p) (eval_var _p t_struct_intpair))
      SEP
      (`(message Ews intpair_message ipm);
      `(data_at_ Tsh (tarray tuchar 8) buf);
      `(data_at_ Tsh t_struct_intpair q);
      `(data_at_ Tsh t_struct_intpair p)))); [entailer! |].

forward. (*  p.x = 1; *)
forward. (* p.y = 2; *)
(*
entailer!.
unfold replace_nth.
simpl update_tycon.
apply derives_refl.  (* SHOULD NOT NEED THIS LINE *)

Ltac gather_SEP' L :=
   grab_indexes_SEP L; (*handles lifting better than the one in client_lemmas *)
 match goal with |- context [SEPx ?R] =>
   rewrite <- (firstn_skipn (length L) R);
   unfold firstn, skipn; simpl length; cbv beta iota; rewrite gather_SEP;
   unfold app, fold_right; try  rewrite sepcon_emp
 end.

gather_SEP' (0::1::nil).
replace_SEP 0 (`(data_at Tsh t_struct_intpair (Vint (Int.repr 1), Vint (Int.repr 2)))
                      (eval_var _p t_struct_intpair) ).
unfold_data_at 1%nat.
entailer.
rewrite -> seq_assoc. simpl.
eapply semax_seq'.
frame_SEP 1 0 2.
replace_in_pre (nil: list (environ -> Prop)) (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil)
          ((Eaddrof (Evar _p t_struct_intpair) (tptr t_struct_intpair)
            :: Evar _buf (tarray tuchar 8) ::  nil))::nil).
entailer.
try (apply prop_right; apply I). (* temporary, should soon not be needed *)
simpl update_tycon.
unfold_abbrev.
abbreviate_semax.
unfold POSTCONDITION, MORE_COMMANDS, abbreviate.
simpl update_tycon.
replace_in_pre (tc_environ Delta ::
   tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil)
     (Eaddrof (Evar _p t_struct_intpair) (tptr t_struct_intpair)
      :: Evar _buf (tarray tuchar 8) :: nil) :: nil)
  (tc_exprlist Delta (tptr tvoid :: tptr tuchar :: nil)
     (Eaddrof (Evar _p t_struct_intpair) (tptr t_struct_intpair)
      :: Evar _buf (tarray tuchar 8) :: nil) :: nil).
rewrite <- insert_local.
apply andp_left2.
rewrite <- insert_local.
apply andp_left2.
 apply derives_refl.
*)
Abort.
(*
apply call_serialize; repeat split; simpl; auto 50 with closed; auto.
intro rho. apply prop_right. hnf. auto.
simpl update_tycon. unfold app.
focus_SEP 2.
eapply semax_pre0; [apply intpair_message_length | ].
focus_SEP 1 4.
rewrite -> seq_assoc.
eapply semax_seq'.
apply call_deserialize; try reflexivity; auto.
entailer.
apply closed_wrt_PROPx.
apply closed_wrt_LOCALx; [ auto 50 with closed | ].
apply closed_wrt_SEPx.
assert (CLX: closed_wrt_vars (eq _des)
  (`(mf_assert intpair_message Tsh) (eval_var _buf (tarray tuchar 8))
     (`Int.signed (`force_int (eval_id _len))) `((Vint (Int.repr 1), Vint (Int.repr 2)))))
  by admit.
assert (CLY: closed_wrt_vars (eq _des)
  (`(data_at Tsh t_struct_intpair (Vint (Int.repr 1), Vint (Int.repr 2)))
     (eval_var _p t_struct_intpair)))
 by admit.
auto 50 with closed.
focus_SEP 1.
replace_SEP 0
  ((`( field_at Tsh t_struct_intpair [_x] (Vint (Int.repr 1))) (eval_var _q t_struct_intpair) *
   `( field_at Tsh t_struct_intpair [_y] (Vint (Int.repr 2))) (eval_var _q t_struct_intpair))
    ).
unfold_data_at 1%nat.
entailer!.
normalize.
forward. (* x = q.x; *)
forward. (* y = q.y; *)
forward. (* return x+y; *)
 unfold frame_ret_assert; simpl.  (* shouldn't need this *)
 unfold main_post.
 entailer.
 unfold mf_restbuf.
 change (mf_size intpair_message) with 8.
 assert (isptr (eval_var _buf(tarray tuchar 8) rho)).
 apply eval_var_isptr with Delta; auto.
 rewrite <- H1; clear len H1.
 simpl.
 replace (memory_block Tsh (Int.repr 0)
      (offset_val (Int.repr 8) (eval_var _buf (tarray tuchar 8) rho)))
  with (@emp mpred _ _).
 rewrite sepcon_emp.
2: symmetry; destruct (eval_var _buf (tarray tuchar 8) rho); inv H3;
 apply memory_block_zero.
unfold stackframe_of.
simpl.
repeat rewrite var_block_data_at_ by reflexivity.
unfold id.
entailer.

assert (data_at_ Tsh t_struct_intpair (eval_var _buf (tarray tuchar 8) rho) |--
   data_at_ Tsh (tarray tuchar 8) (eval_var _buf (tarray tuchar 8) rho)).
  rewrite <- !memory_block_data_at_ by reflexivity.
  unfold align_compatible; simpl.
  destruct (eval_var _buf (tarray tuchar 8) rho); entailer!.
  eapply Zdivides_trans; [exists 4; reflexivity | exact H1].
rename H into HYP. (*remove when simpl_data_at is fixed (explanation in verif_queue)*)
unfold data_at_ at 2.
unfold_data_at 3%nat.
change (field_at Tsh t_struct_intpair [_x] Vundef
          (eval_var _q t_struct_intpair rho)) with
  (field_at_ Tsh t_struct_intpair [_x]
          (eval_var _q t_struct_intpair rho)).
change (field_at Tsh t_struct_intpair [_y] Vundef
          (eval_var _q t_struct_intpair rho)) with
  (field_at_ Tsh t_struct_intpair [_y]
          (eval_var _q t_struct_intpair rho)).
cancel.
apply sepcon_derives; [cancel |].
eapply derives_trans; [apply data_at_data_at_; reflexivity | exact H1].
Qed.
*)

