Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.objectSelf.

Require Import VST.floyd.Funspec_old_Notation.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope Z.
Local Open Scope logic.

(*Andrew's definition
Definition object_invariant := list Z -> val -> mpred.*)

(*But the uncurried version is easier for the HOrec construction*)
Definition ObjInv : Type:= (list Z * val).
Definition object_invariant := ObjInv -> mpred.

Definition tobject := tptr (Tstruct _object noattr).

Definition reset_spec (instance: object_invariant) :=
  WITH hs:ObjInv (*modified*)
  PRE [ _self OF tobject]
          PROP (isptr (snd hs) (*NEW*))
          LOCAL (temp _self (snd hs))
          SEP (instance hs)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance (nil, snd hs)).

Definition twiddle_spec (instance: object_invariant) :=
  WITH hs: ObjInv, i: Z (*modified*)
  PRE [ _self OF tobject, _i OF tint]
          PROP (0 < i <= Int.max_signed / 4;
                0 <= fold_right Z.add 0 (fst hs) <= Int.max_signed / 4; 
               isptr (snd hs) (*NEW*))
          LOCAL (temp _self (snd hs); temp _i (Vint (Int.repr i)))
          SEP (instance hs)
  POST [ tint ]
      EX v: Z, 
          PROP(2* fold_right Z.add 0 (fst hs) < v <= 2* fold_right Z.add 0 (i::(fst hs)))
          LOCAL (temp ret_temp (Vint (Int.repr v))) 
          SEP(instance (i::(fst hs), snd hs)).
(*
Require Import VST.progs.conclib.
Require Import VST.concurrency.semax_conc.
Require Import VST.msl.seplog.
Require Import VST.msl.predicates_hered.
Lemma Contractive: forall Q R v, 
  predicates_hered.allp (fun x : ObjInv => |> R x <=> |> Q x)
  |-- func_ptr (reset_spec R) v <=> func_ptr (reset_spec Q) v.
Proof. intros. rewrite fash_andp. apply andp_right. 
+ red. intros n N. unfold func_ptr, func_ptr_si. apply subp_exp.
Search seplog.imp fash. exp.
 red. intros r. simpl. apply subp_i1. Search fash seplog.imp. unfold func_ptr, func_ptr_si.
apply eqp_exp. p_right. red.
   *)
Definition object_methods (instance: object_invariant) (mtable: val) : mpred :=
  EX sh: share, EX reset: val, EX twiddle: val, EX twiddleR:val,
  !! readable_share sh && 
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  func_ptr' (twiddle_spec instance) twiddleR *
  data_at sh (Tstruct _methods noattr) (reset,(twiddle, twiddleR)) mtable.

Lemma object_methods_local_facts: forall instance p,
  object_methods instance p |-- !! isptr p.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle twiddleR.
entailer!.
Qed.
#[export] Hint Resolve object_methods_local_facts : saturate_local.

(*Andrew's definition
Definition object_mpred (history: list Z) (self: val) : mpred :=
  EX instance: object_invariant, EX mtable: val, 
       (object_methods instance mtable *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable self*
     instance history self).*)

Section ObjMpred.
Variable instance: object_invariant.

Definition F (X: ObjInv -> mpred) (hs: ObjInv): mpred :=
   ((EX mtable: val, !!(isptr mtable) (*This has to hold NOW, not ust LATER*)&&
     (|> object_methods X mtable) *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) *
   instance hs)%logic.

Definition HOcontractive1 {A: Type}{NA: NatDed A}{IA: Indir A}{RI: RecIndir A}{X: Type}
     (f: (X -> A) -> (X -> A)) := 
 forall P Q : X -> A,
 ALL x : X, |> fash (P x <--> Q x)
 |-- ALL x : X, fash (f P x --> f Q x).

Lemma HOcontractive_i1:
 forall  (A: Type)(NA: NatDed A){IA: Indir A}{RI: RecIndir A}{X: Type}
     (f: (X -> A) -> (X -> A)),
  HOcontractive1 f -> HOcontractive f.
Proof.
intros.
red in H|-*.
intros.
eapply derives_trans.
apply andp_right.
apply H.
specialize (H Q P).
eapply derives_trans.
2: apply H.
apply allp_derives; intros.
apply later_derives.
apply fash_derives.
rewrite andp_comm.
auto.
apply allp_right; intro.
rewrite fash_andp.
apply andp_right.
apply andp_left1.
apply allp_left with v; auto.
apply andp_left2.
apply allp_left with v; auto.
Qed.

Lemma HOcontrF
     (*Need sth like this (HI: HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => instance x))*):
      HOcontractive F.
Proof.
unfold F.
apply HOcontractive_i1.
red; intros.
apply allp_right; intro oi.
apply subp_sepcon_mpred; [ | apply subp_refl].
apply subp_exp; intro v.
apply subp_sepcon_mpred; [ | apply subp_refl].
clear oi.
apply subp_andp; [ apply subp_refl | ].
rewrite <- subp_later.
rewrite <- later_allp.
apply later_derives.
unfold object_methods.
apply subp_exp; intro sh.
apply subp_exp; intro reset.
apply subp_exp; intro twiddle.
apply subp_exp; intro twiddleR.
apply subp_sepcon_mpred; [ | apply subp_refl].
repeat simple apply subp_sepcon_mpred;
try (simple apply subp_andp; [simple apply subp_refl | ]).
+
unfold func_ptr'.
apply subp_andp; [ | apply subp_refl].
clear - instance.
eapply derives_trans; [ | apply fash_func_ptr_ND].
apply allp_right; intro oi.
apply andp_right.
*
apply allp_right; intro rho.
apply subp_i1.
rewrite unfash_allp.
set (zz := allp _).
unfold convertPre.
unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
unfold_lift.
normalize.
rewrite prop_true_andp by tauto.
subst zz.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply allp_left with oi.
apply unfash_fash.
eapply derives_trans.
apply andp_derives.
apply andp_left2. apply derives_refl. apply derives_refl.
rewrite andp_comm. apply modus_ponens.
*
apply allp_right; intro rho.
apply subp_i1.
rewrite unfash_allp.
set (zz := allp _).
unfold convertPre.
unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
unfold_lift.
normalize.
subst zz.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply allp_left with ([], snd oi).
apply unfash_fash.
eapply derives_trans.
apply andp_derives.
apply andp_left1. apply derives_refl. apply derives_refl.
rewrite andp_comm. apply modus_ponens.
+
unfold func_ptr'.
apply subp_andp; [ | apply subp_refl].
clear - instance.
eapply derives_trans; [ | apply fash_func_ptr_ND].
apply allp_right; intros [hs i].
apply andp_right.
*
apply allp_right; intro rho.
apply subp_i1.
rewrite unfash_allp.
set (zz := allp _).
unfold convertPre.
unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
unfold_lift.
normalize.
rewrite prop_true_andp by tauto.
subst zz.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply allp_left with hs.
apply unfash_fash.
eapply derives_trans.
apply andp_derives.
apply andp_left2. apply derives_refl. apply derives_refl.
rewrite andp_comm. apply modus_ponens.
*
apply allp_right; intro rho.
apply subp_i1.
rewrite unfash_allp.
set (zz := allp _).
unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
unfold_lift.
normalize.
subst zz.
apply exp_right with x.
normalize.
rewrite prop_true_andp by tauto.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply allp_left with (i::fst hs, snd hs).
apply unfash_fash.
eapply derives_trans.
apply andp_derives.
apply andp_left1. apply derives_refl. apply derives_refl.
rewrite andp_comm. apply modus_ponens.
+
unfold func_ptr'.
apply subp_andp; [ | apply subp_refl].
clear - instance.
eapply derives_trans; [ | apply fash_func_ptr_ND].
apply allp_right; intros [hs i].
apply andp_right.
*
apply allp_right; intro rho.
apply subp_i1.
rewrite unfash_allp.
set (zz := allp _).
unfold convertPre.
unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
unfold_lift.
normalize.
rewrite prop_true_andp by tauto.
subst zz.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply allp_left with hs.
apply unfash_fash.
eapply derives_trans.
apply andp_derives.
apply andp_left2. apply derives_refl. apply derives_refl.
rewrite andp_comm. apply modus_ponens.
*
apply allp_right; intro rho.
apply subp_i1.
rewrite unfash_allp.
set (zz := allp _).
unfold PROPx, LOCALx, SEPx, local, lift1; simpl.
unfold_lift.
normalize.
subst zz.
apply exp_right with x.
normalize.
rewrite prop_true_andp by tauto.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply allp_left with (i::fst hs, snd hs).
apply unfash_fash.
eapply derives_trans.
apply andp_derives.
apply andp_left1. apply derives_refl. apply derives_refl.
rewrite andp_comm. apply modus_ponens.
Qed.

Definition obj_mpred:ObjInv -> mpred := (HORec F). (*ie same type as Andrew's object_mpred.*)

Lemma ObjMpred_fold_unfold: 
HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => instance x) ->
obj_mpred = 
fun hs => 
  ((EX mtable: val,!!(isptr mtable) &&
     (|> object_methods obj_mpred mtable) *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) *
   instance hs)%logic.
Proof.
  intros; unfold obj_mpred at 1.
  rewrite HORec_fold_unfold; [ reflexivity | apply HOcontrF]; trivial.
Qed.
Lemma ObjMpred_fold_unfold' hs: 
HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => instance x) ->
obj_mpred hs = 
  ((EX mtable: val, !!(isptr mtable) &&
     (|> object_methods obj_mpred mtable) *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) *
   instance hs)%logic.
Proof.
  intros. rewrite ObjMpred_fold_unfold, <- ObjMpred_fold_unfold; trivial. 
Qed.

Lemma ObjMpred_isptr
   (H: HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => instance x))
    hs: obj_mpred hs |-- !!(isptr (snd hs)).
Proof. rewrite ObjMpred_fold_unfold' by trivial; Intros m. entailer!. Qed.

End ObjMpred.

Definition object_mpred: object_invariant := fun hs =>
  EX instance, !!(HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => instance x)) &&
               obj_mpred instance hs.
(*This now plays the role of Andrew's obj_mpred*)

Lemma object_mpred_isptr hs: object_mpred hs |-- !!(isptr (snd hs)).
Proof. unfold object_mpred; Intros inst. apply ObjMpred_isptr; trivial. Qed.

Lemma obj_mpred_entails_object_mpred inst hs
  (H: HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => inst x)):
  obj_mpred inst hs |-- object_mpred hs.
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
    EX p: val, PROP () LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; object_mpred (*nil p*)(nil, p); object_methods foo_invariant (gv _foo_methods)).

*)

Section NewSpecs.
Definition foo_data : object_invariant :=
  (fun (x:ObjInv) => 
    withspacer Ews (sizeof size_t + sizeof tint) (2 * sizeof size_t) (field_at Ews (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 (fst x))))) (snd x)
      *  malloc_token Ews (Tstruct _foo_object noattr) (snd x)).
Lemma foo_data_HOcontr: HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => foo_data x).
Proof.
  assert (predicates_rec.HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => foo_data x)). 2: apply H.
  unfold foo_data.
  unfold withspacer; simpl.
  apply Trashcan.sepcon_HOcontractive.
  apply Trashcan.const_HOcontractive.
  apply Trashcan.const_HOcontractive.
Qed.

Definition foo_obj_invariant :object_invariant := obj_mpred foo_data.

(*New lemma!*)
Lemma foo_obj_invariant_fold_unfold: foo_obj_invariant =
 fun hs =>
  ((EX mtable: val, !!(isptr mtable) &&
     (|>object_methods foo_obj_invariant  mtable) *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) *
   foo_data hs)%logic.
Proof.
  unfold foo_obj_invariant.
  rewrite <- ObjMpred_fold_unfold. trivial. apply foo_data_HOcontr.
Qed.

(*Sometimes this variant is preferable, sometimes the one above*)
Lemma foo_obj_invariant_fold_unfold' hs: foo_obj_invariant hs =
  ((EX mtable: val, !!(isptr mtable) &&
     (|>object_methods foo_obj_invariant  mtable) *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd hs)) *
   foo_data hs)%logic.
Proof. rewrite foo_obj_invariant_fold_unfold. rewrite <- foo_obj_invariant_fold_unfold; trivial. Qed.

Lemma foo_data_isptr hs: foo_data hs = !!(isptr (snd hs)) && foo_data hs.
apply pred_ext; entailer.
unfold foo_data. entailer!. destruct (snd hs); simpl in *; trivial;  contradiction.
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
    PROP () LOCAL (gvars gv) 
    SEP (mem_mgr gv; object_methods foo_obj_invariant (gv _foo_methods))
 POST [ tobject ]
    EX p: val, PROP () LOCAL (temp ret_temp p)
     SEP (mem_mgr gv; object_mpred (nil,p); object_methods foo_obj_invariant (gv _foo_methods)).
End NewSpecs.

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
     EX i:Z, PROP(0<=i<=6) LOCAL (temp ret_temp (Vint (Int.repr i))) SEP(TT).

Definition Gprog : funspecs :=   ltac:(with_library prog [
    foo_reset_spec; foo_twiddle_spec; foo_twiddleR_spec; make_foo_spec; main_spec]).

(*Redundant given obj_mpred_entails_object_mpred and the fact that our funspecs yield a folded  obj_mpred.
Lemma object_mpred_i:
  forall (*(history: list Z) (self: val)*)(x:ObjInv) (instance: object_invariant) (mtable: val)
  ((*NEW*)CONTR: HOcontractive (fun (_ : ObjInv -> mpred) (x : ObjInv) => instance x)),
  match x with (history, self) => !!(isptr mtable) &&
     (|>object_methods instance mtable) *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable self *
     instance (*history self*)x 
    |-- object_mpred (*history self*)x
  end.
Proof.
(*intros. unfold object_mpred. Exists instance mtable; auto.*)
intros. destruct x as [history self]. unfold object_mpred. Exists instance. entailer!.
rewrite ObjMpred_fold_unfold by trivial.
Exists mtable. simpl. entailer!.
unfold object_methods. apply later_derives.
apply exp_derives; intros sh.
apply exp_derives; intros r.
apply exp_derives; intros t.
apply exp_derives; intros tR. entailer!.
apply sepcon_derives. admit.
apply func_ptr'_mono. clear - CONTR. do_funspec_sub.
 rewrite ObjMpred_fold_unfold by trivial.
Exists w; destruct w; entailer!. unfold convertPre. Intros.
Exists (EX mtable : val,
 !! isptr mtable && |> object_methods (obj_mpred instance) mtable *
 field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable (snd o)).
entailer!.
intros. Exists mtable x0. entailer!. destruct w.
 Exists w (EX mtable : val,
      !! isptr mtable &&
      |> object_methods (obj_mpred instance) mtable *
      field_at Ews (Tstruct _object noattr) [
        StructField _mtable] mtable (snd hs)). entailer!.
  intros. destruct w as [hist i]. 
  rewrite ObjMpred_fold_unfold. <- ObjMpred_fold_unfold. by trivial.
 cancel. apply now_later. auto.
*)

(*Andrew's proof
Lemma body_foo_reset: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
unfold foo_reset_spec, foo_invariant, reset_spec.
start_function.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
entailer!.
all: unfold withspacer; simpl; entailer!.  (* needed if Archi.ptr64=true *)
Qed.*)
Lemma body_foo_reset: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
start_function. 
(*New:*) rewrite foo_obj_invariant_fold_unfold. Intros m; unfold foo_data.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
entailer!.
(*New:*) rewrite foo_obj_invariant_fold_unfold, <- foo_obj_invariant_fold_unfold. Exists m; unfold foo_data.
all: unfold withspacer; simpl; entailer!.  (* needed if Archi.ptr64=true *)
Qed.

Lemma body_foo_reset_alternativeproof: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
(*New*) unfold foo_reset_spec. rewrite foo_obj_invariant_fold_unfold; unfold reset_spec.
start_function. 
(*New:*) Intros m; unfold foo_data.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
entailer!.
(*New:*) Exists m; unfold foo_data.
all: unfold withspacer; simpl; entailer!.  (* needed if Archi.ptr64=true *)
Qed.

Lemma body_foo_twiddle: semax_body Vprog Gprog f_foo_twiddle foo_twiddle_spec.
Proof.
(*New*) unfold foo_twiddle_spec. rewrite foo_obj_invariant_fold_unfold; unfold twiddle_spec.
start_function.
(*New:*) Intros m; unfold foo_data.
unfold withspacer; simpl.
Intros.
forward.  (* d = self->data; *)
forward.  (* self -> data = d+2*i; *) 
{ set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  entailer!. }
forward.  (* return d+i; *)
{ simpl.
  set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  entailer!. }
Exists (2 * fold_right Z.add 0 (*history*)(fst hs) + i).
(*New:*) Exists m; unfold foo_data.
simpl;
entailer!.
rewrite Z.mul_add_distr_l, Z.add_comm.
unfold withspacer; simpl.
entailer!.
Qed.

(*Moved here from further below, and added twiddleR*)
Lemma make_object_methods:
  forall sh instance reset twiddle twiddleR mtable,
  readable_share sh ->
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  func_ptr' (twiddle_spec instance) twiddleR * 
  data_at sh (Tstruct _methods noattr) (reset, (twiddle, twiddleR)) mtable
  |-- object_methods instance mtable.
Proof.
  intros.
  unfold object_methods.
  Exists sh reset twiddle twiddleR.
  entailer!.
Qed.

Lemma make_object_methods_later:
  forall sh instance reset twiddle twiddleR mtable,
  readable_share sh ->
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  func_ptr' (twiddle_spec instance) twiddleR * 
  data_at sh (Tstruct _methods noattr) (reset, (twiddle, twiddleR)) mtable
  |-- |> object_methods instance mtable.
Proof.
intros. eapply derives_trans. apply make_object_methods; trivial. apply now_later.
Qed.

Lemma body_foo_twiddleR: semax_body Vprog Gprog f_foo_twiddleR foo_twiddleR_spec.
Proof.
(*New*) unfold foo_twiddleR_spec. rewrite foo_obj_invariant_fold_unfold; unfold twiddle_spec.
start_function.
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
  Exists m. unfold foo_data, withspacer; simpl. entailer!.
  sep_apply make_object_methods_later. cancel. }
(*The spec has folded the object, so need to unfold again*)
deadvars!. clear - H H0.
rewrite foo_obj_invariant_fold_unfold. Intros m. unfold foo_data, withspacer; Intros; simpl.

forward.  (* self -> data = d+2*i; *) 
{ set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  rewrite field_at_isptr; Intros.
  entailer!. }
forward.  (* return d+i; *)
{ simpl.
  set (j:= Int.max_signed / 4) in *; compute in j; subst j.
  forget (fold_right Z.add 0 (*history*)(fst hs)) as h.
  entailer!. }
Exists (2 * fold_right Z.add 0 (*history*)(fst hs) + i).
(*New:*) Exists m; unfold foo_data.
simpl;
entailer!.
rewrite Z.mul_add_distr_l, Z.add_comm.
unfold withspacer; simpl.
entailer!.
Qed.

Lemma split_object_methods:
  forall instance m, 
    object_methods instance m |-- object_methods instance m * object_methods instance m.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle twiddleR.

Exists (fst (slice.cleave sh)) reset twiddle twiddleR.
Exists (snd (slice.cleave sh)) reset twiddle twiddleR.
rewrite (split_func_ptr' (reset_spec instance) reset) at 1.
rewrite (split_func_ptr' (twiddle_spec instance) twiddle) at 1.
rewrite (split_func_ptr' (twiddle_spec instance) twiddleR) at 1.
entailer!.
split.
apply slice.cleave_readable1; auto.
apply slice.cleave_readable2; auto.
rewrite (data_at_share_join (fst (slice.cleave sh)) (snd (slice.cleave sh)) sh).
auto.
apply slice.cleave_join.
Qed.

(* Isolate a lemma from Andrew's proof of body_make_foo; TODO: simplify the following proof. *)
Lemma MC_FC p (H: malloc_compatible (sizeof (Tstruct _foo_object noattr)) p):
      field_compatible (Tstruct _object noattr) [StructField _mtable] p.
Proof.
destruct p; try contradiction.
destruct H as [AL SZ].
repeat split; auto.
simpl in *.  unfold sizeof in *; simpl in *; lia.
eapply align_compatible_rec_Tstruct; [reflexivity |].
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

Lemma body_make_foo: semax_body Vprog Gprog f_make_foo make_foo_spec.
Proof.
unfold make_foo_spec.
start_function.
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
change (Memory.EqDec_val p nullval) with (eq_dec p nullval).
if_tac; entailer!.
*
forward_call 1.
contradiction.
*
rewrite if_false by auto.
Intros.
forward.  (*  /*skip*/;  *)
entailer!.
*
unfold data_at_, field_at_, default_val; simpl.
forward. (* p->mtable = &foo_methods; *)
forward. (* p->data = 0; *)
forward. (* return (struct object * ) p; *)
Exists p.
sep_apply (split_object_methods foo_obj_invariant (gv _foo_methods)).
entailer!.
unfold object_mpred.

(*slight variation of Andrew's proof from here on*)
Exists foo_data. entailer!. 1: solve [apply foo_data_HOcontr].
rewrite ObjMpred_fold_unfold by (apply foo_data_HOcontr).
Exists (gv _foo_methods). simpl. normalize.
rewrite ! sepcon_assoc. apply sepcon_derives. apply now_later.
unfold foo_data; simpl. unfold withspacer; simpl.
cancel.
unfold_data_at (field_at _ _ nil _ p).
cancel.
clear -H.
rewrite !field_at_data_at.
simpl.
apply derives_refl'.
rewrite <- ?sepcon_assoc. (* needed if Archi.ptr64=true *)
rewrite !field_compatible_field_address; auto with field_compatible.
apply MC_FC; trivial.
Qed.
(*
Ltac method_call witness hist' result :=
repeat apply seq_assoc1;
match goal with 
   |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) 
            (Ssequence (Sset ?mt (Efield (Ederef (Etempvar ?x _)  _) _ _))
                 _) _  =>
    match Q with context [temp ?x ?x'] =>
     match R with context [object_mpred _ x'] =>
          let instance := fresh "instance" in let mtable := fresh "mtable" in
          unfold object_mpred; Intros instance mtable;
          forward;
          unfold object_methods at 1; 
          let sh := fresh "sh" in let r := fresh "r" in let t := fresh "t" in
          Intros sh r t;
          forward;
          forward_call witness;
          [ .. | try Intros result;
                  sep_apply (make_object_methods sh instance r t mtable); [ auto .. | ];
                  sep_apply (object_mpred_i hist' x' instance mtable);
                  deadvars; try clear dependent sh; try clear r; try clear t
           ]
    end end
end.*)

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
(* assert_gvar _foo_methods. (* TODO: this is needed for a field_compatible later on *) *)
fold noattr cc_default.
(* 0. This part should be handled automatically by start_function *) simpl.
gather_SEP (mapsto _ _ (offset_val 8 (gv _foo_methods)) _) 
           (mapsto _ _ (offset_val 4 (gv _foo_methods)) _ ) (data_at _ _ _ _);
replace_SEP 0 (data_at Ews (Tstruct _methods noattr) 
   (gv _foo_reset, (gv _foo_twiddle, gv _foo_twiddleR)) (gv _foo_methods)). {
  entailer!.
  unfold_data_at (data_at _ (Tstruct _methods _) _ (gv _foo_methods)).
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddle]) (v:= (gv _foo_twiddle))
  by  auto with field_compatible. 
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddleR]) (v:= (gv _foo_twiddleR))
  by  auto with field_compatible.
  rewrite field_at_data_at. rewrite !field_compatible_field_address by auto with field_compatible.
  rewrite !isptr_offset_val_zero by auto.
  cancel.
}

(* 1. Prove that [mtable] is a proper method-table for foo-objects *)

make_func_ptr _foo_twiddle.
make_func_ptr _foo_reset.
make_func_ptr _foo_twiddleR.
sep_apply (make_object_methods Ews foo_obj_invariant (gv _foo_reset) (gv _foo_twiddle) (gv _foo_twiddleR) (gv _foo_methods)); auto.

(* 2. Build an instance of class [foo], called [p] *)
forward_call (* p = make_foo(); *)
        gv.
Intros p.
(*New*) freeze [2; 3] FR1. (*Hide the global method table and the has_ext *)

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
(* 4. first method-call *)
(*NEW*) assert_PROP (isptr p) as isptrP by (sep_apply object_mpred_isptr; entailer!).
unfold object_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rename H into HOC. rewrite ObjMpred_fold_unfold by trivial. Intros mtable0; simpl.

forward. (*  mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0 tR0.
forward. (* p_reset = mtable->reset; *)
forward_call (* p_reset(p); *)
      (@nil Z,p).
{ (*NEW subgoal*)
   sep_apply make_object_methods_later.
   rewrite ObjMpred_fold_unfold, <- ObjMpred_fold_unfold by trivial.
   Exists mtable0. entailer!. } 
(* WAS (*Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).*)

(*Now: folding partially done by forward_call (and the preceding new subgoal*)
sep_apply obj_mpred_entails_object_mpred; simpl.

deadvars!. clear.

(* 5. second method-call *)
(*NEW*) assert_PROP (isptr p) as isptrP by (sep_apply object_mpred_isptr; entailer!).
unfold object_mpred.

(*WAS:Intros instance mtable0.*)
(*Now*) Intros instance. rename H into HOC. rewrite ObjMpred_fold_unfold by trivial. Intros mtable0; simpl.

forward.  (* mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0 tR0.
forward.   (* p_twiddle = mtable->twiddle; *)
(*Now redundant: assert_PROP (p<>Vundef) by entailer!.*)
forward_call (* i = p_twiddle(p,3); *)
      ((@nil Z,p), 3).
{ (*NEW subgoal*)
   sep_apply make_object_methods_later.
   rewrite ObjMpred_fold_unfold, <- ObjMpred_fold_unfold by trivial.
   Exists mtable0. entailer!. }
{ simpl. repeat split; try trivial; computable. }
Intros i.
simpl in H0. (*
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [3] p instance mtable0).*)
sep_apply obj_mpred_entails_object_mpred; simpl.
deadvars!.
(*simpl in H1.*)

(* DD *)

(* 6. return *)
forward.  (* return i; *)
Exists i; entailer!.
Qed.





