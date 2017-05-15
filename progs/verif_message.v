Require Import floyd.proofauto.
Require Import progs.message.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Local Open Scope Z.
Local Open Scope logic.

(*   mf_assert msgfmt sh buf len data  := the [data] is formatted into a message
         at most [len] bytes,  stored starting at address [buf] with share [sh] *)


Definition natural_alignment := 8.

Lemma natural_alignment_enough: 
   forall t, 
    type_is_by_value t = true -> 
    attr_of_type t = noattr ->
    (alignof t | 8).
Proof.
  intros.
  assert (1 | 8). exists 8. reflexivity.
  assert (2 | 8). exists 4. reflexivity.
  assert (4 | 8). exists 2. reflexivity.
  assert (8 | 8). exists 1. reflexivity.
  destruct t; simpl in *; try subst a;
 try inversion H; simpl;
  try destruct i; try destruct f; try assumption.
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
                 !!(0 <= len <= mf_size) && memory_block sh len buf;
   mf_restbuf := fun (sh: share) (buf: val) (len: Z) =>
          memory_block sh (mf_size-len) (offset_val len buf)
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
  normalize.
  eapply derives_trans; [apply data_at_data_at_; reflexivity|].
  rewrite data_at__memory_block by reflexivity.
  apply andp_right; [apply prop_right; omega|].
  simpl.
  apply andp_left2.
  apply derives_refl.
Qed.

(* align_compatible requirement is necessary in precondition *)
Definition serialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, sh: share, sh': share
  PRE [ _p OF (tptr tvoid), _buf OF (tptr tuchar) ]
          PROP (readable_share sh; writable_share sh';
                mf_data_assert format data;
                natural_align_compatible buf)
          LOCAL (temp _p p; temp _buf buf)
          SEP (data_at sh t data p;
                 memory_block sh' (mf_size format) buf)
  POST [ tint ]
         EX len: Z,
          PROP() LOCAL (temp ret_temp (Vint (Int.repr len)))
          SEP( data_at sh t data p;
                 mf_assert format sh' buf len data;
                 mf_restbuf format sh' buf len).

Definition deserialize_spec {t: type} (format: message_format t) :=
  WITH data: reptype t, p: val, buf: val, shs: share*share, len: Z
  PRE [ _p OF (tptr tvoid), _buf OF (tptr tuchar), _length OF tint ]
          PROP (readable_share (snd shs); writable_share (fst shs);
                0 <= len <= mf_size format)
          LOCAL (temp _p p;
                 temp _buf buf;
                 temp _length (Vint (Int.repr len)))
          SEP (mf_assert format (snd shs) buf len data;
                 data_at_ (fst shs) t p)
  POST [ tvoid ]
          PROP (mf_data_assert format data)  LOCAL ()
          SEP (mf_assert format (snd shs) buf len data;
                 data_at (fst shs) t data p).

Definition intpair_serialize_spec :=
 DECLARE _intpair_serialize (serialize_spec intpair_message).

Definition intpair_deserialize_spec :=
 DECLARE _intpair_deserialize (deserialize_spec intpair_message).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition message (sh: share) {t: type} (format: message_format t) (m: val) : mpred :=
  EX fg: val*val,
          func_ptr' (serialize_spec format) (fst fg) *
          func_ptr' (deserialize_spec format) (snd fg) *
       data_at sh t_struct_message (Vint (Int.repr (mf_size format)), (fst fg, snd fg)) m.

Definition Gprog : funspecs :=   ltac:(with_library prog [
    intpair_serialize_spec; intpair_deserialize_spec; main_spec]).

Lemma memory_block_field_compatible_tarray_tint:
  forall sh n buf, 
   0 <= n -> 4*n < Int.modulus ->
   natural_align_compatible buf ->
   memory_block sh (sizeof (tarray tint n)) buf =
   !! field_compatible (tarray tint n) [] buf && memory_block sh (sizeof (tarray tint n)) buf.
Proof.
intros.
apply pred_ext; [ apply andp_right; auto | apply andp_left2; auto].
rewrite memory_block_size_compatible.
Intros.
entailer!.
destruct buf; try contradiction.
repeat split; auto; simpl; auto; try computable.
destruct n; try reflexivity.
hnf in H. simpl in H. elimtype False; auto.
unfold size_compatible in H2. simpl in H2.
rewrite Z.max_r by omega. auto.
destruct H1 as [z H1]; exists (z*2)%Z. rewrite <- Z.mul_assoc. apply H1.
Qed.

Lemma body_intpair_serialize: semax_body Vprog Gprog f_intpair_serialize intpair_serialize_spec.
Proof.
unfold intpair_serialize_spec.
unfold serialize_spec.
start_function.
destruct H as [Dx Dy].
destruct data as [[|x1 | | | | ] [|y1 | | | | ]]; try contradiction. clear Dx Dy.

change (mf_size intpair_message) with (sizeof (tarray tint 2)).
rewrite memory_block_field_compatible_tarray_tint; try computable; auto.
Intros.
rewrite memory_block_data_at_; auto.
change (data_at_ sh' (tarray tint 2) buf) with
   (data_at sh' (tarray tint 2) [Vundef;Vundef] buf).
forward. (* x = p->x; *)
forward. (* y = p->y; *)
(* TODO: fix bug-- without the assert_PROP, wrong error message from store_tac *)
(* TODO: fix bug2: the assert_PROP shouldn't even be necessary... *)
assert_PROP (force_val (sem_cast_neutral buf) = field_address (tarray tint 2) nil buf).
entailer!; rewrite field_compatible_field_address by auto; simpl; normalize.
forward. (*  ((int * )buf)[0]=x; *)
forward. (*  ((int * )buf)[1]=y; *)
forward. (* return 8; *)
apply exp_right with 8.
entailer!.
unfold mf_restbuf. simpl.
rewrite memory_block_zero. entailer!.
Qed.

Lemma body_intpair_deserialize: semax_body Vprog Gprog f_intpair_deserialize intpair_deserialize_spec.
Proof.
unfold intpair_deserialize_spec, deserialize_spec.
start_function. destruct shs as (sh,sh'). simpl @fst in *; simpl @snd in *.
unfold mf_assert. simpl. Intros. subst len.
destruct data as [[|x1 | | | | ] [|y1 | | | | ]]; try contradiction.
clear H H1 H2.

(* TODO: fix bug-- without the assert_PROP, wrong error message from store_tac *)
(* TODO: fix bug2: the assert_PROP shouldn't even be necessary... *)
assert_PROP (force_val (sem_cast_neutral buf) = field_address (tarray tint 2) nil buf).
entailer!; rewrite field_compatible_field_address by auto; simpl; normalize.
forward. (* x = ((int * )buf)[0]; *)
forward. (* y = ((int * )buf)[1]; *)
forward. (* p->x = x; *)
forward. (*  p->y = y; *)
forward.  (* return; *)
Qed.

Ltac get_global_function id :=
  eapply (call_lemmas.semax_fun_id' id); [ reflexivity | simpl; reflexivity | ].

Lemma slide_func_ptr:
  forall f e R1 R,
  SEPx (func_ptr' f e :: R1 :: R) = SEPx ((func_ptr f e && R1)::R).
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

Definition serialize_A {t}  (msg: message_format t) : Type :=
  match serialize_spec msg with
  |  mk_funspec _ _ (rmaps.ConstType A) _ _ _ _ => A  
  | _ =>  unit
  end.

Definition serialize_pre {t} (msg: message_format t)  :=
match serialize_spec msg as f
     return match f with
       | mk_funspec _ _ (rmaps.ConstType A) _ _ _ _ => A -> environ->mpred 
       | _ => unit
     end
with mk_funspec f _ (rmaps.ConstType A) P Q _ _ => P nil 
     | _ => tt
 end.

Definition serialize_post {t} (msg: message_format t)  :=
match serialize_spec msg as f
     return match f with
       | mk_funspec _ _ (rmaps.ConstType A) _ _ _ _ => A -> environ->mpred 
       | _ => unit
     end
with mk_funspec f _ (rmaps.ConstType A) P Q _ _ => Q nil
     | _ => tt
 end.

Definition serialize_fsig {t} (msg: message_format t)  : funsig :=
match serialize_spec msg with
     | mk_funspec f _ _ _ _ _ _ => f
 end.

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

Lemma make_func_ptr:  (* this is not quite right, needs to be on a semax *)
 forall id Delta P Q R fs p,
   (var_types Delta) ! id = None ->
   (glob_specs Delta) ! id = Some fs ->
   (glob_types Delta) ! id = Some (type_of_funspec fs) ->
    PTree.get id (snd (fst ((fst (local2ptree Q))))) = Some (vardesc_visible_global p) ->
 ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- 
   PROPx P (LOCALx Q (SEPx (func_ptr' fs p :: R))).
Admitted.

Ltac make_func_ptr id :=
 first [eapply semax_pre | eapply ENTAIL_trans];
 [eapply (make_func_ptr id); reflexivity  | ].

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
name buf _buf.
name q _q.
name p _p.
name ipm _intpair_message.
start_function.
(* TODO:   "name" tactic doesn't work for function-pointer gvars? *)
rename gvar1 into des.
rename gvar0 into ser.
assert_PROP (natural_align_compatible buf).
  entailer!. clear - H.
  admit. 
rename H into ALIGN.
make_func_ptr _intpair_deserialize.
make_func_ptr _intpair_serialize.
assert_PROP (
  field_compatible t_struct_message [StructField _deserialize] ipm /\
  field_compatible t_struct_message [StructField _serialize] ipm /\ 
field_compatible t_struct_message [StructField _bufsize] ipm).
entailer!.
split3; auto;
solve [
split3; auto; [split3; auto]; [ split3; [ simpl; computable | auto | ]];
  split; auto; [ split; [apply I | ]]; simpl; clear; compute; auto].
destruct H as [? [? ?]].
eapply semax_pre with
  (PROP ( )
   LOCAL (lvar _buf (tarray tuchar 8) buf;
   lvar _q (Tstruct _intpair noattr) q; lvar _p (Tstruct _intpair noattr) p;
   gvar _intpair_deserialize des; gvar _intpair_serialize ser;
   gvar _intpair_message ipm)
   SEP (func_ptr' (serialize_spec intpair_message) ser;
          func_ptr' (deserialize_spec intpair_message) des;
          data_at Ews t_struct_message
                 (@fold_reptype CompSpecs t_struct_message (Vint (Int.repr (mf_size intpair_message)), (ser, des))) ipm;
          data_at_ Tsh (tarray tuchar 8) buf;
          data_at_ Tsh (Tstruct _intpair noattr) q;
          data_at_ Tsh (Tstruct _intpair noattr) p)).  {
 entailer!.
 unfold_data_at 1%nat.
 rewrite <- !sepcon_assoc.
 match goal with |- _ |-- ?B * ?S * ?D =>
  apply derives_trans with (D * S * B); [ | solve [cancel]] end.
 rewrite <- mapsto_field_at with (v:=des) by auto.
 rewrite field_compatible_field_address by auto.
 rewrite <- mapsto_field_at with (v:=ser) by auto.
 rewrite field_compatible_field_address by auto.
 rewrite <- mapsto_field_at with (v:=Vint (Int.repr 8)) by auto.
 rewrite field_compatible_field_address by auto.
 normalize.
}
forward. (*  p.x = 1; *)
forward. (* p.y = 2; *)
forward. (* ser = intpair_message.serialize; *)

rewrite <- memory_block_data_at__tarray_tuchar_eq by computable.
change (memory_block Tsh 8 buf)
with (memory_block Tsh (mf_size intpair_message) buf).

forward_call ((Vint (Int.repr 1), Vint (Int.repr 2)), p, buf, Tsh, Tsh).
  split3; auto.
  split; auto. split; apply I.
Intros rest.
simpl.
Intros. subst rest.

forward.
forward_call ((Vint (Int.repr 1), Vint (Int.repr 2)), q, buf, (Tsh,Tsh), 8).
simpl.
entailer!.
fold t_struct_intpair.
cancel.
simpl.
split3; auto. computable.
(* after the call *)
forward. (* x = q.x; *)
forward. (* y = q.y; *)
forward. (* return x+y; *)
Exists buf q p.
entailer!.
sep_apply (data_at_memory_block Tsh (tarray tint 2) [Vint (Int.repr 1); Vint (Int.repr 2)] buf).
simpl sizeof.
sep_apply (memory_block_data_at__tarray_tuchar Tsh buf 8).
computable.
cancel.
Admitted.