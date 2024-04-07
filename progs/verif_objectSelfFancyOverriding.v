Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.objectSelfFancyOverriding.

(*Version 1 -- leave specs of foo methods unchanged, and require neither funcspec_sub nor 
anything else. Just replicate the spec/proof structure of foo in fancy foo and see whether
the client has enough knowledge to call the correct function*)

(*Require Import VST.floyd.Funspec_old_Notation.*)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section mpred.

Context `{!default_VSTGS Σ}.

Section FOO.

(*Andrew's definition
Definition object_invariant := list Z -> val -> mpred.*)

(*But the uncurried version is easier for the fixpoint construction*)
Definition ObjInv : Type:= (list Z * val).
Definition object_invariant := ObjInv -d> mpred.

Definition tobject := tptr (Tstruct _object noattr).

Definition reset_spec (instance: object_invariant) :=
  WITH hs:ObjInv (*modified*)
  PRE [ (*_self OF*) tobject]
          PROP (isptr (snd hs) (*NEW*))
          PARAMS (snd hs) GLOBALS ()
          SEP (instance hs)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance (nil, snd hs)).

Definition twiddle_spec (instance: object_invariant) :=
  WITH hs: ObjInv, i: Z (*modified*)
  PRE [ (*_self OF*) tobject, (*_i OF*) tint]
          PROP (0 < i <= Int.max_signed / 4;
                0 <= fold_right Z.add 0 (fst hs) <= Int.max_signed / 4; 
               isptr (snd hs) (*NEW*))
          PARAMS (snd hs; Vint (Int.repr i)) GLOBALS ()
          SEP (instance hs)
  POST [ tint ]
      ∃ v: Z,
          PROP(2* fold_right Z.add 0 (fst hs) < v <= 2* fold_right Z.add 0 (i::(fst hs)))
          LOCAL (temp ret_temp (Vint (Int.repr v)))
          SEP(instance (i::(fst hs), snd hs)).

Definition object_methods (instance: object_invariant) (mtable: val) : mpred :=
  ∃ sh: share, ∃ reset: val, ∃ twiddle: val, ∃ twiddleR:val,
  ⌜readable_share sh⌝ ∧
  func_ptr (reset_spec instance) reset ∗
  func_ptr (twiddle_spec instance) twiddle ∗
  func_ptr (twiddle_spec instance) twiddleR ∗
  data_at sh (Tstruct _methods noattr) (reset,(twiddle, twiddleR)) mtable.
Typeclasses Opaque object_methods.

Global Instance reset_spec_ne : NonExpansive reset_spec.
Proof.
  intros ????.
  unfold reset_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance twiddle_spec_ne : NonExpansive twiddle_spec.
Proof.
  intros ????.
  unfold twiddle_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance object_methods_ne n : Proper (dist n ==> eq ==> dist n) object_methods.
Proof. solve_proper. Qed.

Lemma object_methods_local_facts: forall instance p,
  object_methods instance p ⊢ ⌜isptr p⌝.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle twiddleR.
entailer!.
Qed.
Local Hint Resolve object_methods_local_facts : saturate_local.

(*Moved here from further below, and added twiddleR*)
Lemma make_object_methods:
  forall sh instance reset twiddle twiddleR mtable,
  readable_share sh ->
  func_ptr (reset_spec instance) reset ∗
  func_ptr (twiddle_spec instance) twiddle ∗
  func_ptr (twiddle_spec instance) twiddleR ∗
  data_at sh (Tstruct _methods noattr) (reset, (twiddle, twiddleR)) mtable
  ⊢ object_methods instance mtable.
Proof.
  intros.
  unfold object_methods.
  Exists sh reset twiddle twiddleR.
  entailer!!.
Qed.

Lemma make_object_methods_later:
  forall sh instance reset twiddle twiddleR mtable,
  readable_share sh ->
  func_ptr (reset_spec instance) reset ∗
  func_ptr (twiddle_spec instance) twiddle ∗
  func_ptr (twiddle_spec instance) twiddleR ∗
  data_at sh (Tstruct _methods noattr) (reset, (twiddle, twiddleR)) mtable
  ⊢ ▷ object_methods instance mtable.
Proof.
intros. eapply derives_trans. apply make_object_methods; trivial. apply bi.later_intro.
Qed.

(*Andrew's definition
Definition object_mpred (history: list Z) (self: val) : mpred :=
  ∃ instance: object_invariant, ∃ mtable: val, 
       (object_methods instance mtable *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable self*
     instance history self).*)

Section ObjMpred.
Variable instance: object_invariant.

Definition F (X: ObjInv -d> mpred) : ObjInv -d> mpred := fun hs =>
   ((∃ mtable: val, ⌜isptr mtable⌝ (*This has to hold NOW, not just LATER*)∧
     (▷ object_methods X mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   instance hs).

Local Instance F_contractive : Contractive F.
Proof.
  intros ?????.
  unfold F.
  do 5 f_equiv.
  f_contractive.
  rewrite H //.
Qed.

Definition obj_mpred:ObjInv -> mpred := fixpoint F.

Lemma ObjMpred_fold_unfold:
forall hs, obj_mpred hs ⊣⊢
  ((∃ mtable: val,⌜isptr mtable⌝ ∧
     (▷ object_methods obj_mpred mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   instance hs).
Proof.
  intros; unfold obj_mpred at 1.
  by rewrite (fixpoint_unfold F _).
Qed.
Lemma ObjMpred_fold_unfold' hs:
obj_mpred hs ⊣⊢
  ((∃ mtable: val, ⌜isptr mtable⌝ ∧
     (▷ object_methods obj_mpred mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   instance hs).
Proof.
  intros. rewrite ObjMpred_fold_unfold -ObjMpred_fold_unfold; trivial.
Qed.

Lemma ObjMpred_isptr hs: obj_mpred hs ⊢ ⌜isptr (snd hs)⌝.
Proof. rewrite -> ObjMpred_fold_unfold' by trivial; Intros m. entailer!. Qed.

End ObjMpred.

Definition object_mpred: object_invariant := fun hs =>
  ∃ instance, obj_mpred instance hs.
(*This now plays the role of Andrew's obj_mpred*)

Lemma object_mpred_isptr hs: object_mpred hs ⊢ ⌜isptr (snd hs)⌝.
Proof. unfold object_mpred; Intros inst. apply ObjMpred_isptr; trivial. Qed.

Lemma obj_mpred_entails_object_mpred inst hs:
  obj_mpred inst hs ⊢ object_mpred hs.
Proof. unfold object_mpred. Exists inst. entailer!. Qed.

(*Andrew's specs 
Definition foo_invariant : object_invariant :=
  (fun (history: list Z) p => 
    withspacer Ews (sizeof size_t + sizeof tint) (2 * sizeof size_t) (field_at Ews (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 history)))) p
      *  malloc_token Ews (Tstruct _foo_object noattr) p)
Definition foo_reset_spec :=
 DECLARE _foo_reset (reset_spec foo_invariant).

Definition foo_twiddle_spec :=
 DECLARE _foo_twiddle  (twiddle_spec foo_invariant).

Definition foo_twiddleR_spec :=
 DECLARE _foo_twiddleR  (twiddle_spec foo_invariant).

Definition make_foo_spec :=
 DECLARE _make_foo
 WITH gv: globals
 PRE [ ]
    PROP () LOCAL (gvars gv) 
    SEP (mem_mgr gv; object_methods foo_invariant (gv _foo_methods))
 POST [ tobject ]
    ∃ p: val, PROP () LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; object_mpred (*nil p*)(nil, p); object_methods foo_invariant (gv _foo_methods)).

*)

Section NewSpecs.
Definition foo_data : object_invariant :=
  (fun (x:ObjInv) => 
    withspacer Ews (sizeof size_t + sizeof tint) (2 * sizeof size_t) (field_at Ews (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 (fst x))))) (snd x)
      ∗ malloc_token Ews (Tstruct _foo_object noattr) (snd x)).

Definition foo_obj_invariant : object_invariant := obj_mpred foo_data.

(*New lemma!*)
Lemma foo_obj_invariant_fold_unfold: foo_obj_invariant ≡
 fun hs =>
  ((∃ mtable: val, ⌜isptr mtable⌝ ∧
     (▷object_methods foo_obj_invariant  mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   foo_data hs).
Proof.
  unfold foo_obj_invariant; intros ?.
  rewrite <- ObjMpred_fold_unfold. trivial.
Qed.

(*Sometimes this variant is preferable, sometimes the one above*)
Lemma foo_obj_invariant_fold_unfold' hs: foo_obj_invariant hs ⊣⊢
  ((∃ mtable: val, ⌜isptr mtable⌝ ∧
     (▷object_methods foo_obj_invariant  mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   foo_data hs).
Proof. apply (foo_obj_invariant_fold_unfold hs). Qed.

Lemma foo_data_isptr hs: foo_data hs ⊣⊢ ⌜isptr (snd hs)⌝ ∧ foo_data hs.
Proof.
  iSplit.
  - iIntros; iSplit; last done.
    unfold foo_data; iStopProof.
    destruct (hs.2); entailer!.
  - iIntros "(_ & $)".
Qed.


Definition foo_reset_spec :=
 DECLARE _foo_reset (reset_spec foo_obj_invariant).

Definition foo_twiddle_spec :=
 DECLARE _foo_twiddle  (twiddle_spec foo_obj_invariant).

Definition foo_twiddleR_spec :=
 DECLARE _foo_twiddleR  (twiddle_spec foo_obj_invariant).

Definition make_foo_spec :=
 DECLARE _make_foo
 WITH gv: globals
 PRE [ ]
    PROP () PARAMS () GLOBALS (gv) 
    SEP (mem_mgr gv; object_methods foo_obj_invariant (gv _foo_methods))
 POST [ tobject ]
    ∃ p: val, PROP () LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; object_mpred (nil,p); object_methods foo_obj_invariant (gv _foo_methods)).
End NewSpecs.

Definition FooGprog : funspecs :=   ltac:(with_library prog [
    foo_reset_spec; foo_twiddle_spec; foo_twiddleR_spec; make_foo_spec(*; main_spec*)]).

Lemma body_foo_reset: semax_body Vprog FooGprog f_foo_reset foo_reset_spec.
Proof.
start_function.
(*New:*) rewrite foo_obj_invariant_fold_unfold'. Intros m; unfold foo_data.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
entailer!!.
(*New:*) rewrite foo_obj_invariant_fold_unfold'. Exists m; unfold foo_data.
all: unfold withspacer; simpl; entailer!.  (* needed if Archi.ptr64=true *)
Qed.

(*Lemma body_foo_reset_alternativeproof: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
(*New*) unfold foo_reset_spec. rewrite foo_obj_invariant_fold_unfold'; unfold reset_spec.
start_function. 
(*New:*) Intros m; unfold foo_data.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
entailer!!.
(*New:*) Exists m; unfold foo_data.
all: unfold withspacer; simpl; entailer!!.  (* needed if Archi.ptr64=true *)
Qed.*)

Lemma body_foo_twiddle: semax_body Vprog FooGprog f_foo_twiddle foo_twiddle_spec.
Proof.
(*New*) unfold foo_twiddle_spec. unfold twiddle_spec.
start_function.
rewrite foo_obj_invariant_fold_unfold'.
(*New:*) Intros m; unfold foo_data.
unfold withspacer; simpl.
Intros.
forward.  (* d = self->data; *)
forward.  (* self -> data = d+2*i; *) 
{ set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  entailer!!. }
forward.  (* return d+i; *)
{ simpl.
  set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  entailer!!. }
Exists (2 * fold_right Z.add 0 (*history*)(fst hs) + i).
rewrite foo_obj_invariant_fold_unfold'.
(*New:*) Exists m; unfold foo_data.
simpl;
entailer!!.
rewrite Z.mul_add_distr_l Z.add_comm.
unfold withspacer; simpl.
entailer!!.
Qed.

Lemma body_foo_twiddleR: semax_body Vprog FooGprog f_foo_twiddleR foo_twiddleR_spec.
Proof.
(*New*) unfold foo_twiddleR_spec. unfold twiddle_spec.
start_function.
rewrite foo_obj_invariant_fold_unfold'.
(*New:*) Intros m; unfold foo_data.
unfold withspacer; simpl.
Intros.
forward.  (* d = self->data; *)

(*The new function call*)
forward.
unfold object_methods. Intros sh r t tR.
forward. (*_s_reset = (_mtable -> _reset);*)
forward_call hs.
{ rewrite foo_obj_invariant_fold_unfold'.
  Exists m. unfold foo_data, withspacer; simpl. entailer!!.
  rewrite -make_object_methods_later //. ecancel. }
(*The spec has folded the object, so need to unfold again*)
deadvars!. clear - H H0.
rewrite foo_obj_invariant_fold_unfold'. Intros m. unfold foo_data, withspacer; Intros; simpl.

forward.  (* self -> data = d+2*i; *) 
{ set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  rewrite field_at_isptr; Intros.
  entailer!!. }
forward.  (* return d+i; *)
{ simpl.
  set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  entailer!!. }
Exists (2 * fold_right Z.add 0 (*history*)(fst hs) + i).
rewrite foo_obj_invariant_fold_unfold'.
(*New:*) Exists m; unfold foo_data.
simpl;
entailer!.
rewrite Z.mul_add_distr_l Z.add_comm.
unfold withspacer; simpl.
entailer!!.
Qed.

Lemma split_object_methods:
  forall instance m,
    object_methods instance m ⊢ object_methods instance m ∗ object_methods instance m.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle twiddleR.

Exists (fst (slice.cleave sh)) reset twiddle twiddleR.
Exists (snd (slice.cleave sh)) reset twiddle twiddleR.
iIntros "(#$ & #$ & #$ & H)".
rewrite -(data_at_share_join (fst (slice.cleave sh)) (snd (slice.cleave sh)) sh); last apply slice.cleave_join.
iDestruct "H" as "($ & $)".
iPureIntro; repeat split; auto; apply slice.cleave_readable1 || apply slice.cleave_readable2; auto.
Qed.

(* Isolate a lemma from Andrew's proof of body_make_foo; TODO: simplify the following proof. *)
Lemma MC_FC p (H: malloc_compatible (sizeof (Tstruct _foo_object noattr)) p):
      field_compatible (Tstruct _object noattr) [StructField _mtable] p.
Proof.
destruct p; try contradiction.
destruct H as [AL SZ].
repeat split; auto.
simpl in *.  unfold sizeof in *; simpl in *; lia.
eapply align_compatible_rec_Tstruct; [reflexivity.. |].
simpl co_members; intros.
simpl in H.
if_tac in H; [| inv H].
inv H. inv H0.
eapply align_compatible_rec_by_value.
reflexivity.
rewrite Z.add_0_r.
simpl.
unfold natural_alignment in AL.
eapply Z.divide_trans; [ | apply AL].
apply prove_Zdivide.
reflexivity.
left; auto.
Qed.

Lemma body_make_foo: semax_body Vprog FooGprog f_make_foo make_foo_spec.
Proof.
unfold make_foo_spec.
start_function.
rename a into gv.
forward_call (Tstruct _foo_object noattr, gv).
Intros p.
forward_if
  (PROP ( )
   LOCAL (temp _p p; gvars gv)
   SEP (mem_mgr gv;
          malloc_token Ews (Tstruct _foo_object noattr) p;
          data_at_ Ews (Tstruct _foo_object noattr) p;
          object_methods foo_obj_invariant (gv _foo_methods))).
*
change (EqDec_val p nullval) with (eq_dec p nullval).
if_tac; entailer!!.
*
forward_call 1.
contradiction.
*
rewrite -> if_false by auto.
Intros.
forward.  (*  /*skip*/;  *)
entailer!!.
*
unfold data_at_, field_at_, default_val; simpl.
forward. (* p->mtable = &foo_methods; *)
forward. (* p->data = 0; *)
forward. (* return (struct object * ) p; *)
Exists p.
sep_apply (split_object_methods foo_obj_invariant (gv _foo_methods)).
entailer!!.
unfold obj_mpred.

(*slight variation of Andrew's proof from here on*)
Exists foo_data. entailer!!.
rewrite -> ObjMpred_fold_unfold by (apply foo_data_HOcontr).
Exists (gv _foo_methods). simpl. normalize.
unfold foo_data; simpl. unfold withspacer; simpl.
cancel.
apply bi.sep_mono; first apply bi.later_intro.
unfold_data_at (field_at _ _ nil _ p).
cancel.
clear -H.
rewrite !field_at_data_at.
simpl.
f_equiv.
rewrite !field_compatible_field_address; auto with field_compatible.
apply MC_FC; trivial.
Qed.
End FOO.

Section FancyFoo.

Definition fObjInv : Type:= ((list Z * Z) * val).
Definition fobject_invariant := fObjInv -d> mpred.

(*not replicated: Definition tobject := tptr (Tstruct _object noattr).*)

(*A new spec, not just the adpatation of reset_spec to fancy invariants*)
Definition freset_spec (instance: fobject_invariant) :=
  WITH hs:fObjInv (*modified*)
  PRE [ (*_self OF*) tobject]
          PROP (isptr (snd hs) (*NEW*))
          PARAMS (snd hs) GLOBALS ()
          SEP (instance hs)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance ((nil, 0), snd hs)).

Definition ftwiddle_spec (instance: fobject_invariant) :=
  WITH hs: fObjInv, i: Z
  PRE [ (*_self OF*) tobject, (*_i OF*) tint]
          PROP (0 < i <= Int.max_signed / 4;
                0 <= fold_right Z.add 0 (fst (fst hs)) <= Int.max_signed / 4; 
               isptr (snd hs) (*NEW*))
          PARAMS (snd hs; Vint (Int.repr i)) GLOBALS ()
          SEP (instance hs)
  POST [ tint ]
      ∃ v: Z,
          PROP(2* fold_right Z.add 0 (fst (fst hs)) < v <= 2* fold_right Z.add 0 (i::(fst (fst hs))))
          LOCAL (temp ret_temp (Vint (Int.repr v)))
          SEP(instance ((i::(fst (fst hs)), snd(fst hs)), snd hs)).

(*A separate spec, since this method is affected by the overrising of reset*)
Definition ftwiddleR_spec (instance: fobject_invariant) :=
  WITH hs: fObjInv, i: Z
  PRE [ (*_self OF*) tobject, (*_i OF*) tint]
          PROP (0 < i <= Int.max_signed / 4;
                0 <= fold_right Z.add 0 (fst (fst hs)) <= Int.max_signed / 4; 
               isptr (snd hs) (*NEW*))
          PARAMS (snd hs; Vint (Int.repr i)) GLOBALS ()
          SEP (instance hs)
  POST [ tint ]
      ∃ v: Z, 
          PROP(2* fold_right Z.add 0 (fst (fst hs)) < v <= 2* fold_right Z.add 0 (i::(fst (fst hs))))
          LOCAL (temp ret_temp (Vint (Int.repr v))) 
          SEP(instance ((i::(fst (fst hs)), 0), snd hs)).

Definition fsetcolor_spec (instance: fobject_invariant) :=
  WITH hs:fObjInv, c:Z
  PRE [ (*_self OF*) tobject, (*_c OF*) tint]
          PROP (isptr (snd hs) (*NEW*))
          PARAMS (snd hs; Vint(Int.repr c)) GLOBALS ()
          SEP (instance hs)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance ((fst(fst hs), c), snd hs)).

Definition fgetcolor_spec (instance: fobject_invariant) :=
  WITH hs: fObjInv
  PRE [ (*_self OF*) tobject]
          PROP (isptr (snd hs) (*NEW*))
          PARAMS (snd hs) GLOBALS ()
          SEP (instance hs)
  POST [ tint ]
          PROP()
          LOCAL (temp ret_temp (Vint (Int.repr (snd(fst hs))))) 
          SEP(instance hs).

Definition fobject_methods (instance: fobject_invariant) (mtable: val) : mpred :=
  ∃ sh: share, ∃ reset: val, ∃ twiddle: val, ∃ twiddleR:val, ∃ setcol: val, ∃ getcol:val,
  ⌜readable_share sh⌝ ∧ 
  func_ptr (freset_spec instance) reset ∗
  func_ptr (ftwiddle_spec instance) twiddle ∗
  func_ptr (ftwiddleR_spec instance) twiddleR ∗
  func_ptr (fsetcolor_spec instance) setcol ∗
  func_ptr (fgetcolor_spec instance) getcol ∗
  data_at sh (Tstruct _fancymethods noattr) (reset,(twiddle, (twiddleR, (setcol, getcol)))) mtable.

Global Instance freset_spec_ne : NonExpansive freset_spec.
Proof.
  intros ????.
  unfold freset_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance ftwiddle_spec_ne : NonExpansive ftwiddle_spec.
Proof.
  intros ????.
  unfold ftwiddle_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance ftwiddleR_spec_ne : NonExpansive ftwiddleR_spec.
Proof.
  intros ????.
  unfold ftwiddleR_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance fsetcolor_spec_ne : NonExpansive fsetcolor_spec.
Proof.
  intros ????.
  unfold fsetcolor_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance fgetcolor_spec_ne : NonExpansive fgetcolor_spec.
Proof.
  intros ????.
  unfold fgetcolor_spec, NDmk_funspec.
  f_equiv; intros ??; simpl; by repeat f_equiv.
Qed.

Global Instance fobject_methods_ne n : Proper (dist n ==> eq ==> dist n) fobject_methods.
Proof. solve_proper. Qed.

Lemma fobject_methods_local_facts: forall instance p,
  fobject_methods instance p ⊢ ⌜isptr p⌝.
Proof.
intros.
unfold fobject_methods.
Intros sh reset twiddle twiddleR setcol getcol.
entailer!.
Qed.
Local Hint Resolve fobject_methods_local_facts : saturate_local.

Lemma make_fobject_methods:
  forall sh instance reset twiddle twiddleR setcol getcol mtable,
  readable_share sh ->
  func_ptr (freset_spec instance) reset ∗
  func_ptr (ftwiddle_spec instance) twiddle ∗
  func_ptr (ftwiddleR_spec instance) twiddleR ∗
  func_ptr (fsetcolor_spec instance) setcol ∗
  func_ptr (fgetcolor_spec instance) getcol ∗
  data_at sh (Tstruct _fancymethods noattr) (reset,(twiddle, (twiddleR, (setcol, getcol)))) mtable
  ⊢ fobject_methods instance mtable.
Proof.
  intros.
  unfold fobject_methods.
  Exists sh reset twiddle twiddleR setcol getcol.
  entailer!!.
Qed.

Lemma make_fobject_methods_later:
  forall sh instance reset twiddle twiddleR setcol getcol mtable,
  readable_share sh ->
  func_ptr (freset_spec instance) reset ∗
  func_ptr (ftwiddle_spec instance) twiddle ∗
  func_ptr (ftwiddleR_spec instance) twiddleR ∗
  func_ptr (fsetcolor_spec instance) setcol ∗
  func_ptr (fgetcolor_spec instance) getcol ∗
  data_at sh (Tstruct _fancymethods noattr) (reset,(twiddle, (twiddleR, (setcol, getcol)))) mtable
  ⊢ ▷ fobject_methods instance mtable.
Proof.
intros. eapply derives_trans. apply make_fobject_methods; trivial. apply bi.later_intro.
Qed.

Section FObjMpred.
Variable instance: fobject_invariant.

Definition G (X: fObjInv -d> mpred) : fObjInv -d> mpred := fun hs =>
   ((∃ mtable: val, ⌜isptr mtable⌝ (*This has to hold NOW, not ust LATER*)∧
     (▷ fobject_methods X mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   instance hs).

Local Instance G_contractive : Contractive G.
Proof.
  intros ?????.
  unfold G.
  do 5 f_equiv.
  f_contractive.
  rewrite H //.
Qed.

Definition fobj_mpred:fObjInv -> mpred := fixpoint G.

Lemma fObjMpred_fold_unfold:
forall hs, fobj_mpred hs ⊣⊢
  ((∃ mtable: val,⌜isptr mtable⌝ ∧
     (▷ fobject_methods fobj_mpred mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   instance hs).
Proof.
  intros; unfold fobj_mpred at 1.
  by rewrite (fixpoint_unfold G _).
Qed.
Lemma fObjMpred_fold_unfold' hs:
fobj_mpred hs ⊣⊢
  ((∃ mtable: val, ⌜isptr mtable⌝ ∧
     (▷ fobject_methods fobj_mpred mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   instance hs).
Proof.
  intros. rewrite fObjMpred_fold_unfold -fObjMpred_fold_unfold; trivial.
Qed.

Lemma fObjMpred_isptr hs: fobj_mpred hs ⊢ ⌜isptr (snd hs)⌝.
Proof. rewrite -> fObjMpred_fold_unfold' by trivial; Intros m. entailer!. Qed.

End FObjMpred.

Definition fobject_mpred: fobject_invariant := fun hs =>
  ∃ instance, fobj_mpred instance hs.
(*This now plays the role of Andrew's obj_mpred*)

Lemma fobject_mpred_isptr hs: fobject_mpred hs ⊢ ⌜isptr (snd hs)⌝.
Proof. unfold fobject_mpred; Intros inst. apply fObjMpred_isptr; trivial. Qed.

Lemma fobj_mpred_entails_object_mpred inst hs:
  fobj_mpred inst hs ⊢ fobject_mpred hs.
Proof. unfold fobject_mpred. Exists inst. entailer!!. Qed.

Section FancySpecs.

(*We use (Tstruct _foo_object noattr) (superclass) for the field_at for _data
  and (Tstruct _fancyfoo_object noattr) for the field_at for _color*)
Definition fancyfoo_data : fobject_invariant :=
  (fun (x:fObjInv) => 
    withspacer Ews (sizeof size_t + sizeof tint) (2 * sizeof size_t) (field_at Ews (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 (fst (fst x)))))) (snd x) 
   ∗ withspacer Ews (sizeof size_t + 2*sizeof tint) (3 * sizeof size_t) (field_at Ews (Tstruct _fancyfoo_object noattr)
            [StructField _color] (Vint (Int.repr (snd(fst x))))) (snd x)
      ∗ malloc_token Ews (Tstruct _fancyfoo_object noattr) (snd x)).

Definition fancyfoo_obj_invariant :fobject_invariant := fobj_mpred fancyfoo_data.

(*New lemma!*)
Lemma fancyfoo_obj_invariant_fold_unfold: fancyfoo_obj_invariant ≡
 fun hs =>
  ((∃ mtable: val, ⌜isptr mtable⌝ ∧
     (▷fobject_methods fancyfoo_obj_invariant  mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   fancyfoo_data hs).
Proof.
  unfold fancyfoo_obj_invariant; intros ?.
  rewrite <- fObjMpred_fold_unfold. trivial.
Qed.

(*Sometimes this variant is preferable, sometimes the one above*)
Lemma fancyfoo_obj_invariant_fold_unfold' hs: fancyfoo_obj_invariant hs ⊣⊢
  ((∃ mtable: val, ⌜isptr mtable⌝ ∧
     (▷fobject_methods fancyfoo_obj_invariant  mtable) ∗
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) ∗
   fancyfoo_data hs).
Proof. apply (fancyfoo_obj_invariant_fold_unfold hs). Qed.

Lemma fancyfoo_data_isptr hs: fancyfoo_data hs ⊣⊢ ⌜isptr (snd hs)⌝ ∧ fancyfoo_data hs.
Proof.
  iSplit.
  - iIntros; iSplit; last done.
    unfold fancyfoo_data; iStopProof.
    destruct (hs.2); entailer!.
  - iIntros "(_ & $)".
Qed.


(*The inherited function is equipped with a fancy specs*)
Definition ffoo_twiddle_spec :=
 DECLARE _foo_twiddle  (ftwiddle_spec fancyfoo_obj_invariant).

(*THe overridden function and the one affected by it are equipped with new specs*)
Definition ffoo_reset_spec :=
 DECLARE _fancy_reset (freset_spec fancyfoo_obj_invariant).

Definition ffoo_twiddleR_spec :=
 DECLARE _foo_twiddleR  (ftwiddleR_spec fancyfoo_obj_invariant).

(*The two new functions are given fancy specs*)
Definition ffoo_setcolor_spec :=
 DECLARE _setcolor  (fsetcolor_spec fancyfoo_obj_invariant).

Definition ffoo_getcolor_spec :=
 DECLARE _getcolor  (fgetcolor_spec fancyfoo_obj_invariant).

Definition make_fancyfoo_spec :=
 DECLARE _make_fancyfoo
 WITH gv: globals, c:Z
 PRE [(*_c OF*) tint ]
    PROP () PARAMS (Vint(Int.repr c)) GLOBALS (gv) 
    SEP (mem_mgr gv; fobject_methods fancyfoo_obj_invariant (gv _fancyfoo_methods))
 POST [ tobject ]
    ∃ p: val, PROP () LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; fobject_mpred ((nil,c),p); fobject_methods fancyfoo_obj_invariant (gv _fancyfoo_methods)).

Definition make_fancyfooTyped_spec :=
 DECLARE _make_fancyfooTyped
 WITH gv: globals, c:Z
 PRE [ (*_c OF*) tint ]
    PROP () PARAMS (Vint(Int.repr c)) GLOBALS (gv) 
    SEP (mem_mgr gv; fobject_methods fancyfoo_obj_invariant (gv _fancyfoo_methods))
 POST [ tptr (Tstruct _fancyfoo_object noattr) ]
    ∃ p: val, PROP () LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; fobject_mpred ((nil,c),p); fobject_methods fancyfoo_obj_invariant (gv _fancyfoo_methods)).

End FancySpecs.

Definition FancyGprog : funspecs :=   ltac:(with_library prog [
    ffoo_reset_spec; ffoo_twiddle_spec; ffoo_twiddleR_spec;
    ffoo_setcolor_spec; ffoo_getcolor_spec;
    make_fancyfoo_spec; make_fancyfooTyped_spec(*; main_spec*)]).

(*Now concerns the function f_fancy_reset*)
Lemma body_fancyfoo_reset: semax_body Vprog FancyGprog f_fancy_reset ffoo_reset_spec.
Proof.
start_function.
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Intros m; unfold fancyfoo_data.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
forward.  (* self->color=0; *)
entailer!!.
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Exists m; unfold fancyfoo_data.
all: unfold withspacer; simpl; entailer!!.  (* needed if Archi.ptr64=true *)
Qed.

Lemma body_fancyfoo_twiddle: semax_body Vprog FancyGprog f_foo_twiddle ffoo_twiddle_spec.
Proof.
start_function.
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Intros m; unfold fancyfoo_data.
unfold withspacer; simpl.
Intros.
forward.  (* d = self->data; *)
forward.  (* self -> data = d+2*i; *) 
{ set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*(fst hs)*)(fst(fst hs))) as h.
  entailer!!. }
forward.  (* return d+i; *)
{ simpl.
  set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*(fst hs)*) (fst(fst hs))) as h.
  entailer!!. }
Exists (2 * fold_right Z.add 0 (*(fst hs)*) (fst(fst hs)) + i).
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'.
Exists m; unfold fancyfoo_data.
simpl;
entailer!!.
rewrite Z.mul_add_distr_l Z.add_comm.
unfold withspacer; simpl.
entailer!!.
Qed.

(*A key lemma relating the two classes*)
Lemma FC_fancymethods f m (L: legal_field (nested_field_type (Tstruct _methods noattr) []) (StructField f))
        (FC: field_compatible (Tstruct _fancymethods noattr) [StructField f] m):
        field_compatible (Tstruct _methods noattr) [StructField f] m.
Proof. 
  destruct FC as [X1 [X2 [SZ [AL [X5 X6]]]]].
  destruct m; try inv X1. clear - L SZ AL.
  repeat split; auto.
  + simpl in *.  unfold sizeof in *; simpl in *; lia.
  + inv AL. inv H1.
    eapply align_compatible_rec_Tstruct; [reflexivity.. |].
    simpl co_members in *; intros. specialize (H4 i0 t0).
    simpl in H.
    if_tac in H.
    { inv H. specialize (H4 _ (eq_refl _) (eq_refl _)).
      inv H4. inv H0. inv H. simpl in H1.
      eapply align_compatible_rec_by_value.
      reflexivity. apply H1. }
    clear H1.
    if_tac in H.
    { inv H. specialize (H4 _ (eq_refl _) (eq_refl _)).
      inv H4. inv H0. inv H. simpl in H1.
      eapply align_compatible_rec_by_value.
      reflexivity. apply H1. }
    clear H1.
    if_tac in H.
    { inv H. specialize (H4 _ (eq_refl _) (eq_refl _)).
      inv H4. inv H0. inv H. simpl in H1.
      eapply align_compatible_rec_by_value.
      reflexivity. apply H1. }
    inv H.
Qed.

(*Verification wrt new spec, BUT NO CHANGE IN PROOF SCRIPT OR LEMMA STATEMENT!!*)
Lemma body_fancyfoo_twiddleR: semax_body Vprog FancyGprog f_foo_twiddleR ffoo_twiddleR_spec.
Proof.
start_function.
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Intros m; unfold fancyfoo_data.
unfold withspacer; simpl.
Intros.
forward.  (* d = self->data; *)

(*The new function call*)
forward.
unfold fobject_methods. Intros sh r t tR g s.

(*New HERE*)
unfold_data_at (data_at sh (Tstruct _fancymethods noattr) _ _).
rewrite (field_at_compatible' sh (Tstruct _fancymethods noattr) [StructField _reset]); Intros. rename H3 into FCmethod.
replace_SEP 5 (field_at sh (Tstruct _methods noattr) [StructField _reset] r m).
{ clear - FCmethod. entailer!!. clear - FCmethod. unfold field_at; simpl; entailer!. 
  apply FC_fancymethods; trivial. left; auto. }

forward. (*_s_reset = (_mtable -> _reset);*)
forward_call hs.
{ (*NEW side condition - again a property of subclasses*)
  rewrite fancyfoo_obj_invariant_fold_unfold'.
  Exists m. unfold fancyfoo_data, withspacer; simpl. entailer!!.
  rewrite -make_fobject_methods_later; last done.
  ecancel.
  unfold_data_at (data_at sh (Tstruct _fancymethods noattr) _ _).
  cancel. unfold field_at; simpl; entailer!!. }
(*The spec has folded the object, so need to unfold again*)
deadvars!. clear - H H0.
rewrite fancyfoo_obj_invariant_fold_unfold'. Intros m. unfold fancyfoo_data, withspacer; Intros; simpl.

forward.  (* self -> data = d+2*i; *) 
{ set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*(fst hs)*)(fst(fst hs))) as h.
  rewrite field_at_isptr; Intros.
  entailer!!. }
forward.  (* return d+i; *)
{ simpl.
  set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*(fst hs)*)(fst(fst hs))) as h.
  entailer!!. }
Exists (2 * fold_right Z.add 0 (*(fst hs)*)(fst(fst hs)) + i).
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'.
Exists m; unfold fancyfoo_data.
simpl;
entailer!.
rewrite Z.mul_add_distr_l Z.add_comm.
unfold withspacer; simpl.
entailer!!.
Qed.

Lemma body_ffoo_setcolor: semax_body Vprog FancyGprog f_setcolor ffoo_setcolor_spec.
Proof.
start_function. 
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Intros m; unfold fancyfoo_data.
unfold withspacer; simpl; Intros.
forward.  (* self->color=0; *)
entailer!!.
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Exists m; unfold fancyfoo_data.
all: unfold withspacer; simpl; entailer!!.  (* needed if Archi.ptr64=true *)
Qed.

Lemma body_ffoo_getcolor: semax_body Vprog FancyGprog f_getcolor ffoo_getcolor_spec.
Proof.
start_function. 
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Intros m; unfold fancyfoo_data.
unfold withspacer; simpl; Intros.
forward.  (* _t'1 = ((tptr (Tstruct _fancyfoo_object noattr)) _self -> _color); *)
forward.
entailer!!.
(*New:*) rewrite fancyfoo_obj_invariant_fold_unfold'. Exists m; unfold fancyfoo_data.
all: unfold withspacer; simpl; entailer!!.  (* needed if Archi.ptr64=true *)
Qed.

(*TINY ADAPTATION IN PROOF*)
Lemma split_fobject_methods:
  forall instance m,
    fobject_methods instance m ⊢ fobject_methods instance m ∗ fobject_methods instance m.
Proof.
intros.
unfold fobject_methods.
Intros sh reset twiddle twiddleR setC getC.

Exists (fst (slice.cleave sh)) reset twiddle twiddleR setC getC.
Exists (snd (slice.cleave sh)) reset twiddle twiddleR setC getC.
iIntros "(#$ & #$ & #$ & #$ & #$ & H)".
rewrite -(data_at_share_join (fst (slice.cleave sh)) (snd (slice.cleave sh)) sh); last apply slice.cleave_join.
iDestruct "H" as "($ & $)".
iPureIntro; repeat split; auto; apply slice.cleave_readable1 || apply slice.cleave_readable2; auto.
Qed.

Lemma body_make_fancyfoo: semax_body Vprog FancyGprog f_make_fancyfoo make_fancyfoo_spec.
Proof.
unfold make_fancyfoo_spec.
start_function.
forward_call (Tstruct _fancyfoo_object noattr, gv).
Intros p.
forward_if
  (PROP ( )
   LOCAL (temp _p p; temp _c (Vint (Int.repr c)); gvars gv)
   SEP (mem_mgr gv;
          malloc_token Ews (Tstruct _fancyfoo_object noattr) p;
          data_at_ Ews (Tstruct _fancyfoo_object noattr) p;
          fobject_methods fancyfoo_obj_invariant (gv _fancyfoo_methods))).
*
change (EqDec_val p nullval) with (eq_dec p nullval).
if_tac; entailer!!.
*
forward_call 1.
contradiction.
*
rewrite -> if_false by auto.
Intros.
forward.  (*  /*skip*/;  *)
entailer!!.
*
unfold data_at_, field_at_, default_val; simpl.
forward. (* p->mtable = &fancyfoo_methods; *)
forward. (* p->data = 0; *)
forward. (* p->color = c;*)
forward. (* return (struct object * ) p; *)
Exists p.
match goal with |- _ ⊢ ?C => set (D := C); rewrite split_fobject_methods; subst D end.
entailer!!.
unfold fobject_mpred.

(*slight variation of Andrew's proof from here on*)
Exists fancyfoo_data. entailer!!.
rewrite fObjMpred_fold_unfold.
Exists (gv _fancyfoo_methods).
rewrite -bi.later_intro /fancyfoo_obj_invariant. entailer!.
unfold fancyfoo_data; simpl. unfold withspacer; simpl.
cancel.
unfold_data_at (field_at _ _ nil _ p).
cancel.
assert_PROP (isptr p) by entailer!. destruct p; inv H2. entailer!.
apply bi.sep_mono.
+ clear - H2. unfold field_at; simpl; entailer!!.
  - unfold field_compatible. destruct H2 as [_ [_ [SZ [AL _]]]].
    repeat split; trivial.
    ++ red. red in SZ. simpl sizeof in *. lia.
    ++ clear SZ. inv AL.
       eapply align_compatible_rec_Tstruct; [reflexivity.. | intros]. specialize (H4 i0).
       simpl co_members in *; intros. inv H.
       if_tac in H5; inv H5.
       inv H0. inv H1. specialize (H4 _ 0 (eq_refl _) (eq_refl _)).
       inv H4. inv H. econstructor. reflexivity. trivial.
    ++ simpl. left; auto.
  - unfold at_offset. entailer!.
+ clear - H4. unfold field_at; simpl; entailer!!.
  - unfold field_compatible. destruct H4 as [_ [_ [SZ [AL _]]]].
    repeat split; trivial.
    ++ red. red in SZ. simpl sizeof in *. lia.
    ++ clear SZ; inv AL.
       eapply align_compatible_rec_Tstruct; [reflexivity.. | intros]. specialize (H4 i0).
       simpl co_members in *; intros. inv H. 
       if_tac in H5; inv H5.
       { inv H0. inv H1. specialize (H4 _ 0 (eq_refl _) (eq_refl _)).
          inv H4. inv H. econstructor. reflexivity. trivial. }
       clear H.
       if_tac in H6; inv H6.
       { inv H0. inv H1. specialize (H4 _ 4 (eq_refl _) (eq_refl _)).
          inv H4. inv H. econstructor. reflexivity. trivial. }
    ++ simpl. right; left; auto.
Qed.

(*EXACT SAME PROOF SCRIPT AS Lemma body_make_fancyfoo*)
Lemma body_make_fancyfooTyped: semax_body Vprog FancyGprog f_make_fancyfooTyped make_fancyfooTyped_spec.
Proof.
unfold make_fancyfooTyped_spec.
start_function.
forward_call (Tstruct _fancyfoo_object noattr, gv).
Intros p.
forward_if
  (PROP ( )
   LOCAL (temp _p p; temp _c (Vint (Int.repr c)); gvars gv)
   SEP (mem_mgr gv;
          malloc_token Ews (Tstruct _fancyfoo_object noattr) p;
          data_at_ Ews (Tstruct _fancyfoo_object noattr) p;
          fobject_methods fancyfoo_obj_invariant (gv _fancyfoo_methods))).
*
change (EqDec_val p nullval) with (eq_dec p nullval).
if_tac; entailer!!.
*
forward_call 1.
contradiction.
*
rewrite -> if_false by auto.
Intros.
forward.  (*  /*skip*/;  *)
entailer!!.
*
unfold data_at_, field_at_, default_val; simpl.
forward. (* p->mtable = &fancyfoo_methods; *)
forward. (* p->data = 0; *)
forward. (* p->color = c;*)
forward. (* return (struct object * ) p; *)
Exists p.
match goal with |- _ ⊢ ?C => set (D := C); rewrite split_fobject_methods; subst D end.
entailer!!.
unfold fobject_mpred.

(*slight variation of Andrew's proof from here on*)
Exists fancyfoo_data. entailer!!.
rewrite fObjMpred_fold_unfold.
Exists (gv _fancyfoo_methods).
rewrite -bi.later_intro /fancyfoo_obj_invariant; entailer!.
unfold fancyfoo_data; simpl. unfold withspacer; simpl.
cancel.
unfold_data_at (field_at _ _ nil _ p).
cancel.
assert_PROP (isptr p) by entailer!. destruct p; inv H2. entailer!.
apply bi.sep_mono.
+ clear - H2. unfold field_at; simpl; entailer!!.
  - unfold field_compatible. destruct H2 as [_ [_ [SZ [AL _]]]].
    repeat split; trivial.
    ++ red. red in SZ. simpl sizeof in *. lia.
    ++ clear SZ. inv AL.
       eapply align_compatible_rec_Tstruct; [reflexivity.. | intros]. specialize (H4 i0).
       simpl co_members in *; intros. inv H.
       if_tac in H5; inv H5.
       inv H0. inv H1. specialize (H4 _ 0 (eq_refl _) (eq_refl _)).
       inv H4. inv H. econstructor. reflexivity. trivial.
    ++ simpl. left; auto.
  - unfold at_offset. entailer!.
+ clear - H4. unfold field_at; simpl; entailer!!.
  - unfold field_compatible. destruct H4 as [_ [_ [SZ [AL _]]]].
    repeat split; trivial.
    ++ red. red in SZ. simpl sizeof in *. lia.
    ++ clear SZ; inv AL.
       eapply align_compatible_rec_Tstruct; [reflexivity.. | intros]. specialize (H4 i0).
       simpl co_members in *; intros. inv H. 
       if_tac in H5; inv H5.
       { inv H0. inv H1. specialize (H4 _ 0 (eq_refl _) (eq_refl _)).
          inv H4. inv H. econstructor. reflexivity. trivial. }
       clear H.
       if_tac in H6; inv H6.
       { inv H0. inv H1. specialize (H4 _ 4 (eq_refl _) (eq_refl _)).
          inv H4. inv H. econstructor. reflexivity. trivial. }
    ++ simpl. right; left; auto.
Qed.

End FancyFoo.

Section Putting_It_All_Together.

Notation funspec := (@funspec Σ).

(*Since the code calls reset on q and u before acessing their color, the result value is just 0*)
Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
     ∃ i:Z, PROP(0<=i<=6) LOCAL (temp ret_temp (Vint (Int.repr (i)))) SEP(True).
(*
Definition reset_intersection: funspec.
Proof.
eapply (binary_intersection' (reset_spec foo_obj_invariant) (freset_spec fancyfoo_obj_invariant)); reflexivity.
Defined.*)
Definition twiddle_intersection: funspec.
Proof.
eapply (binary_intersection'(A1 := ConstType _)(A2 := ConstType _) (twiddle_spec foo_obj_invariant) (ftwiddle_spec fancyfoo_obj_invariant)); reflexivity.
Defined.

(*New: for twiddleR, take intersection of twiidle_spec and ftwiddleR_spec*)
Definition twiddleR_intersection: funspec.
Proof.
eapply (binary_intersection'(A1 := ConstType _)(A2 := ConstType _) (twiddle_spec foo_obj_invariant) (ftwiddleR_spec fancyfoo_obj_invariant)); reflexivity.
Defined.
(*
Lemma reset_sub_foo: funspec_sub reset_intersection (reset_spec foo_obj_invariant).
Proof. 
apply (binaryintersection_sub (reset_spec foo_obj_invariant) (freset_spec fancyfoo_obj_invariant)).
apply binary_intersection'_sound.
Qed.
Lemma reset_sub_fancy: funspec_sub reset_intersection (freset_spec fancyfoo_obj_invariant).
Proof. 
apply (binaryintersection_sub (reset_spec foo_obj_invariant) (freset_spec fancyfoo_obj_invariant)).
apply binary_intersection'_sound.
Qed.*)

Lemma twiddle_sub_foo: funspec_sub twiddle_intersection (twiddle_spec foo_obj_invariant).
Proof.
apply (binaryintersection_sub (twiddle_spec foo_obj_invariant) (ftwiddle_spec fancyfoo_obj_invariant)).
apply binary_intersection'_sound.
Qed.
Lemma twiddle_sub_fancy: funspec_sub twiddle_intersection (ftwiddle_spec fancyfoo_obj_invariant).
Proof.
apply (binaryintersection_sub (twiddle_spec foo_obj_invariant) (ftwiddle_spec fancyfoo_obj_invariant)).
apply binary_intersection'_sound.
Qed.

(*2 new lemmas for twiddleR*)
Lemma twiddleR_sub_foo: funspec_sub twiddleR_intersection (twiddle_spec foo_obj_invariant).
Proof.
apply (binaryintersection_sub (twiddle_spec foo_obj_invariant) (ftwiddleR_spec fancyfoo_obj_invariant)).
apply binary_intersection'_sound.
Qed.
Lemma twiddleR_sub_fancy: funspec_sub twiddleR_intersection (ftwiddleR_spec fancyfoo_obj_invariant).
Proof. 
apply (binaryintersection_sub (twiddle_spec foo_obj_invariant) (ftwiddleR_spec fancyfoo_obj_invariant)).
apply binary_intersection'_sound.
Qed.

(*We associate twiddle, and twiddleR with their intersection specs, reset with its foospec, and ffoo_reset with the fancyspec*)
Definition Gprog : funspecs :=   ltac:(with_library prog [
    (_foo_reset, reset_spec foo_obj_invariant); (_foo_twiddle, twiddle_intersection); (_foo_twiddleR, twiddleR_intersection);
    (*foo_reset_spec; foo_twiddle_spec; foo_twiddleR_spec; *)make_foo_spec; 
    ffoo_reset_spec; (*ffoo_twiddle_spec; ffoo_twiddleR_spec; *)
    ffoo_setcolor_spec; ffoo_getcolor_spec;
    make_fancyfoo_spec; make_fancyfooTyped_spec; main_spec]).

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
rename a into gv.
sep_apply (create_mem_mgr gv).
(* assert_gvar _foo_methods. (* TODO: this is needed for a field_compatible later on *) *)
fold noattr cc_default.

(* 0. This part should be handled automatically by start_function *) simpl.
gather_SEP (mapsto _ _ (offset_val 8 (gv _foo_methods)) _) 
           (mapsto _ _ (offset_val 4 (gv _foo_methods)) _)
           (data_at _ _ _ (gv _foo_methods));
replace_SEP 0 (data_at Ews (Tstruct _methods noattr) 
   (gv _foo_reset, (gv _foo_twiddle, gv _foo_twiddleR)) (gv _foo_methods)). {
  entailer!.
  unfold_data_at (data_at _ (Tstruct _methods _) _ (gv _foo_methods)).
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddle]) (v:= (gv _foo_twiddle))
  by  auto with field_compatible. 
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddleR]) (v:= (gv _foo_twiddleR))
  by  auto with field_compatible.
  rewrite field_at_data_at. rewrite -> !field_compatible_field_address by auto with field_compatible.
  rewrite -> !isptr_offset_val_zero by auto.
  cancel.
} 
gather_SEP (mapsto _ _ (offset_val 16 (gv _fancyfoo_methods)) _) 
           (mapsto _ _ (offset_val 12 (gv _fancyfoo_methods)) _)
           (mapsto _ _ (offset_val 8 (gv _fancyfoo_methods)) _) 
           (mapsto _ _ (offset_val 4 (gv _fancyfoo_methods)) _) 
           (data_at _ _ _ (gv _fancyfoo_methods));
replace_SEP 0 (data_at Ews (Tstruct _fancymethods noattr) 
   (gv _fancy_reset, (gv _foo_twiddle, (gv _foo_twiddleR, (gv _setcolor, gv _getcolor)))) (gv _fancyfoo_methods)). {
  entailer!.
  unfold_data_at (data_at _ (Tstruct _fancymethods _) _ (gv _fancyfoo_methods)).
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddle]) (v:= (gv _foo_twiddle))
  by  auto with field_compatible. 
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddleR]) (v:= (gv _foo_twiddleR))
  by  auto with field_compatible.
  rewrite <- mapsto_field_at with (gfs := [StructField _setcolor]) (v:= (gv _setcolor))
  by  auto with field_compatible. 
  rewrite <- mapsto_field_at with (gfs := [StructField _getcolor]) (v:= (gv _getcolor))
  by  auto with field_compatible.
  rewrite field_at_data_at. rewrite -> !field_compatible_field_address by auto with field_compatible.
  rewrite -> !isptr_offset_val_zero by auto.
  cancel.
}

(* 1a. Prove that [methods] is a proper method table for foo-objects, and that
        fancymethods is a proper method table for fancyfoo-objects *)

make_func_ptr _foo_reset. (*
replace_SEP 0 (func_ptr (reset_spec foo_obj_invariant) (gv _foo_reset)(* *
               func_ptr (freset_spec fancyfoo_obj_invariant) (gv _foo_reset)*)).
{ entailer!. (*rewrite split_func_ptr. apply sepcon_derives; *)apply func_ptr_mono.
  apply reset_sub_foo. (* apply reset_sub_fancy.*) }*)
make_func_ptr _foo_twiddle.
replace_SEP 0 (func_ptr (twiddle_spec foo_obj_invariant) (gv _foo_twiddle) ∗
               func_ptr (ftwiddle_spec fancyfoo_obj_invariant) (gv _foo_twiddle)).
{ entailer!. iIntros "#?"; iSplit; iApply (func_ptr_mono with "[$]").
  apply twiddle_sub_foo. apply twiddle_sub_fancy. }
make_func_ptr _foo_twiddleR.
replace_SEP 0 (func_ptr (twiddle_spec foo_obj_invariant) (gv _foo_twiddleR) ∗
               func_ptr (ftwiddleR_spec fancyfoo_obj_invariant) (gv _foo_twiddleR)).
{ entailer!. iIntros "#?"; iSplit; iApply (func_ptr_mono with "[$]").
  apply twiddleR_sub_foo. apply twiddleR_sub_fancy. }
sep_apply (make_object_methods Ews foo_obj_invariant (gv _foo_reset) (gv _foo_twiddle) (gv _foo_twiddleR) (gv _foo_methods)); auto.

make_func_ptr _fancy_reset.
make_func_ptr _setcolor.
make_func_ptr _getcolor.
sep_apply (make_fobject_methods Ews fancyfoo_obj_invariant (gv _fancy_reset) (gv _foo_twiddle) (gv _foo_twiddleR) (gv _setcolor) (gv _getcolor) (gv _fancyfoo_methods)); auto.

(* 2. Build an instance of class [foo], called [p] *)
forward_call (* p = make_foo(); *)
        gv.
Intros p.

(* 4. Build an instance of class [fancyfoo], called [q] *)
forward_call (* q = make_fancyfoo(); *)
        (gv,4).
Intros q.
(*New*) freeze [0; 2; 4; 5] FR1. (*Hide the global method tables, memmgr, and the has_ext *)

assert_PROP (p<>Vundef) as pNotVundef by entailer!.
(* Illustration of an alternate method to prove the method calls.
   Method 1:  comment out lines AA and BB and the entire range CC-DD.
   Method 2:  comment out lines AA-BB, inclusive.
*)
(*TODO: Adapt
(* AA *) try (tryif 
  (method_call (p, @nil Z) (@nil Z) whatever;
   method_call (p, 3, @nil Z) [3%Z] i;
     [simpl; computable | ])
(* BB *)  then fail else fail 99)
  .*)

(* CC *)
(* 4. first method-call, p.reset *)
(*NEW*) assert_PROP (isptr p) as isptrP by (sep_apply object_mpred_isptr; entailer!).
unfold object_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rewrite ObjMpred_fold_unfold. Intros mtable0; simpl.

forward. (*  mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0 tR0.
forward. (* p_reset = mtable->reset; *)
forward_call (* p_reset(p); *)
      (@nil Z,p).
{ (*NEW subgoal*)
   sep_apply make_object_methods_later.
   rewrite ObjMpred_fold_unfold.
   Exists mtable0. entailer!!. }
(* WAS (*Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).*)

(*Now: folding partially done by forward_call (and the preceding new subgoal*)
sep_apply obj_mpred_entails_object_mpred; simpl.

deadvars!. clear.

(* 5. second method-call, q.reset *)
(*NEW*) assert_PROP (isptr q) as isptrQ by (sep_apply fobject_mpred_isptr; entailer!).
unfold fobject_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rewrite fObjMpred_fold_unfold. Intros mtable0; simpl.

forward. (*_t'9 = (_q -> _mtable);*)
forward. (*_mtable = (tptr (Tstruct _fancymethods noattr)) _t'9;*)

unfold fobject_methods at 1.
Intros sh r0 t0 tR0 sC gC.
forward. (* q_reset = qmtable->reset; *)
forward_call (* q_reset(q); *)
      ((@nil Z,4),q).
{ (*NEW subgoal*)
   sep_apply make_fobject_methods_later.
   rewrite fObjMpred_fold_unfold.
   Exists mtable0. entailer!. }
(* WAS (*Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).*)

(*Now: folding partially done by forward_call (and the preceding new subgoal*)
sep_apply fobj_mpred_entails_object_mpred; simpl.

(*NEW : object q has now color 0, not 4*)
deadvars!. clear.

(* 6. second method-call on q, q->getcolor *)
(*NEW*) assert_PROP (isptr q) as isptrQ by (sep_apply fobject_mpred_isptr; entailer!).
unfold fobject_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rewrite fObjMpred_fold_unfold. Intros mtable0; simpl.

forward. (*_t'8 = (_q -> _mtable);*)
forward. (*_mtable = (tptr (Tstruct _fancymethods noattr)) _t'8;*)

unfold fobject_methods at 1.
Intros sh r0 t0 tR0 sC gC.
forward. (* q_getcolor = qmtable->getcolor; *)
forward_call (* q_reset(q); *)
      ((@nil Z,(*4*)0),q).
{ (*NEW subgoal*)
   sep_apply make_fobject_methods_later.
   rewrite fObjMpred_fold_unfold.
   Exists mtable0. entailer!!. }
(* WAS (*Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).*)

(*Now: folding partially done by forward_call (and the preceding new subgoal*)
sep_apply fobj_mpred_entails_object_mpred; simpl.

deadvars!. clear.

(* 7. second method-call on p, p->twiddleR*)
(*NEW*) assert_PROP (isptr p) as isptrP by (sep_apply object_mpred_isptr; entailer!).
unfold object_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rewrite ObjMpred_fold_unfold. Intros mtable0; simpl.

forward.  (* pmtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0 tR0.
forward.   (* p_twiddle = pmtable->twiddleR; *)
(*Now redundant: assert_PROP (p<>Vundef) by entailer!.*)
forward_call (* i = p_twiddle(p,3); *)
      ((@nil Z,p), 3).
{ (*NEW subgoal*)
   sep_apply make_object_methods_later.
   rewrite ObjMpred_fold_unfold.
   Exists mtable0. entailer!!. }
{ simpl; computable. }
Intros i.
simpl in H0. (*
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [3] p instance mtable0).*)
sep_apply obj_mpred_entails_object_mpred; simpl.
deadvars!. rename H0 into Hi. clear - Hi.

(* 8. Build an typed instance of class [fancyfoo], called [u] *)
thaw FR1.
forward_call (*t'5 = _make_fancyfooTyped([((9)*)
        (gv, 9).
Intros u. freeze [0; 2; 5;6] FR1. (*Hide the global method tables, the memmgr, and and the has_ext *)
freeze [2;3] PQ. (*Hide the other objects p and q*)

(* 9. first method-call on u, u->reset *)
(*NEW*) assert_PROP (isptr u) as isptrU by (sep_apply fobject_mpred_isptr; entailer!).
unfold fobject_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rewrite fObjMpred_fold_unfold. Intros mtable0; simpl.

forward. (*_t'7 = ((tptr (Tstruct _object noattr)) _u -> _mtable);*)
forward. (* _umtable = (tptr (Tstruct _fancymethods noattr)) _t'7;*)

unfold fobject_methods at 1.
Intros sh r0 t0 tR0 sC gC.
forward. (* u_reset = (_umtable -> _reset); *)
forward_call (* u_reset(u); *)
      ((@nil Z,9),u).
{ (*NEW subgoal*)
   sep_apply make_fobject_methods_later.
   rewrite fObjMpred_fold_unfold.
   Exists mtable0. entailer!!. }
(* WAS (*Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).*)

(*Now: folding partially done by forward_call (and the preceding new subgoal*)
sep_apply fobj_mpred_entails_object_mpred; simpl.

(*Indeed, u has now color 0 not 9*)

deadvars!. clear -Hi.

(* 10. second method-call on u, u->getcolor *)
(*NEW*) assert_PROP (isptr u) as isptrU by (sep_apply fobject_mpred_isptr; entailer!).
unfold fobject_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rewrite fObjMpred_fold_unfold. Intros mtable0; simpl.

forward. (*_t'7 = ((tptr (Tstruct _object noattr)) _u -> _mtable);*)
forward. (* _umtable = (tptr (Tstruct _fancymethods noattr)) _t'7;*)

unfold fobject_methods at 1.
Intros sh r0 t0 tR0 sC gC.
forward. (* u_getcolor = (_umtable -> _getcolor); *)
forward_call (* u_getcolor(u); *)
      ((@nil Z,(*9*)0),u).
{ (*NEW subgoal*)
   sep_apply make_fobject_methods_later.
   rewrite fObjMpred_fold_unfold.
   Exists mtable0. entailer!. }
(* WAS (*Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).*)

(*Now: folding partially done by forward_call (and the preceding new subgoal*)
sep_apply fobj_mpred_entails_object_mpred; simpl.

deadvars!. clear -Hi.

(* 11. return *)
forward.  (* return i; *)
Exists i; entailer!.
Qed.

End Putting_It_All_Together.
(*
Lemma funspec_sub_reset_foo_fancy: funspec_sub (reset_spec foo_obj_invariant) (freset_spec fancyfoo_obj_invariant).
Proof. do_funspec_sub. simpl in H. inv H. inv H6.
  destruct w as [[hs c] q]. 
  rewrite fancyfoo_obj_invariant_fold_unfold' at 1. (*foo_obj_invariant_fold_unfold;*) Intros m.
  simpl in H0, H4.
  Exists (hs, q). entailer.
  unfold fancyfoo_data, foo_data, withspacer; simpl. entailer!.
  unfold fobject_methods. 
  rewrite later_exp'; normalize. rename x into sh.
  rewrite later_exp'; normalize. rename x into r.
  rewrite later_exp'; normalize. rename x into t.
  rewrite later_exp'; normalize. rename x into tR.
  rewrite later_exp'; normalize. rename x into sC.
  rewrite later_exp'; normalize. rename x into gC.
  Exists ((
     field_at Ews (Tstruct _fancyfoo_object noattr) [StructField _color] (Vint (Int.repr c)) q *
     (|> (func_ptr (fsetcolor_spec fancyfoo_obj_invariant) sC *
          func_ptr (fgetcolor_spec fancyfoo_obj_invariant) gC))) * 
     ((malloc_token Ews (Tstruct _foo_object noattr) q) -* malloc_token Ews (Tstruct _fancyfoo_object noattr) q)).
  rewrite later_andp. rewrite ! later_sepcon. Intros.
  entailer. apply andp_right.
  + entailer!. intros. rewrite fancyfoo_obj_invariant_fold_unfold'; simpl.
    Exists m. entailer!.
    sep_apply wand_frame_elim''. cancel.
(*    eapply derives_trans. apply sepcon_derives. apply bi.later_intro. apply derives_refl.*)
    rewrite  <- ! later_sepcon. 
    apply later_derives. Exists sh r t tR sC gC. entailer!. admit. (*readable_share*)
    unfold object_methods. admit.
  + entailer!. cancel. normalize.
Abort.*)

End mpred.
