Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.object.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope Z.
Local Open Scope logic.

Definition object_invariant := list Z -> val -> mpred.

Definition tobject := tptr (Tstruct _object noattr).

Definition reset_spec (instance: object_invariant) :=
  WITH self: val, history: list Z
  PRE [ _self OF tobject]
          PROP ()
          LOCAL (temp _self self)
          SEP (instance history self)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance nil self).

Definition twiddle_spec (instance: object_invariant) :=
  WITH self: val, i: Z, history: list Z
  PRE [ _self OF tobject, _i OF tint]
          PROP (0 < i <= Int.max_signed / 4;
                0 <= fold_right Z.add 0 history <= Int.max_signed / 4)
          LOCAL (temp _self self; temp _i (Vint (Int.repr i)))
          SEP (instance history self)
  POST [ tint ]
      EX v: Z, 
          PROP(2* fold_right Z.add 0 history < v <= 2* fold_right Z.add 0 (i::history))
          LOCAL (temp ret_temp (Vint (Int.repr v))) 
          SEP(instance (i::history) self).

Definition object_methods (instance: object_invariant) (mtable: val) : mpred :=
  EX sh: share, EX reset: val, EX twiddle: val,
  !! readable_share sh && 
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  data_at sh (Tstruct _methods noattr) (reset,twiddle) mtable.

Lemma object_methods_local_facts: forall instance p,
  object_methods instance p |-- !! isptr p.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle.
entailer!.
Qed.
Hint Resolve object_methods_local_facts : saturate_local.

Definition object_mpred (history: list Z) (self: val) : mpred :=
  EX instance: object_invariant, EX mtable: val, 
       (object_methods instance mtable *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable self*
     instance history self).

Definition foo_invariant : object_invariant :=
  (fun (history: list Z) p =>
    withspacer Ews (sizeof size_t + sizeof tint) (2 * sizeof size_t) (field_at Ews (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 history)))) p
      *  malloc_token Ews (Tstruct _foo_object noattr) p).

Definition foo_reset_spec :=
 DECLARE _foo_reset (reset_spec foo_invariant).

Definition foo_twiddle_spec :=
 DECLARE _foo_twiddle  (twiddle_spec foo_invariant).

Definition make_foo_spec :=
 DECLARE _make_foo
 WITH gv: globals
 PRE [ ]
    PROP () LOCAL (gvars gv) 
    SEP (object_methods foo_invariant (gv _foo_methods))
 POST [ tobject ]
    EX p: val, PROP () LOCAL (temp ret_temp p)
     SEP (object_mpred nil p; object_methods foo_invariant (gv _foo_methods)).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]
     EX i:Z, PROP(0<=i<=6) LOCAL (temp ret_temp (Vint (Int.repr i))) SEP(TT).

Definition Gprog : funspecs :=   ltac:(with_library prog [
    foo_reset_spec; foo_twiddle_spec; make_foo_spec; main_spec]).

Lemma object_mpred_i:
  forall (history: list Z) (self: val) (instance: object_invariant) (mtable: val),
    object_methods instance mtable *
     field_at Ews (Tstruct _object noattr) [StructField _mtable] mtable self *
     instance history self 
    |-- object_mpred history self.
Proof.
intros. unfold object_mpred. Exists instance mtable; auto.
Qed.

Lemma body_foo_reset: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
unfold foo_reset_spec, foo_invariant, reset_spec.
start_function.
unfold withspacer; simpl; Intros.
forward.  (* self->data=0; *)
forward.  (* return; *)
all: unfold withspacer; simpl; entailer!.  (* needed if Archi.ptr64=true *)
Qed.

Lemma body_foo_twiddle: semax_body Vprog Gprog f_foo_twiddle foo_twiddle_spec.
Proof.
unfold foo_twiddle_spec, foo_invariant, twiddle_spec.
start_function.
unfold withspacer; simpl.
Intros.
forward.  (* d = self->data; *)
forward.  (* self -> data = d+2*i; *) 
 set (j:= Int.max_signed / 4) in *; compute in j; subst j.
 forget (fold_right Z.add 0 history) as h.
 entailer!.
forward.  (* return d+i; *)
 set (j:= Int.max_signed / 4) in *; compute in j; subst j.
 forget (fold_right Z.add 0 history) as h.
 entailer!.
Exists (2 * fold_right Z.add 0 history + i).
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
Intros sh reset twiddle.

Exists (fst (slice.cleave sh)) reset twiddle.
Exists (snd (slice.cleave sh)) reset twiddle.
rewrite (split_func_ptr' (reset_spec instance) reset) at 1.
rewrite (split_func_ptr' (twiddle_spec instance) twiddle) at 1.
entailer!.
split.
apply slice.cleave_readable1; auto.
apply slice.cleave_readable2; auto.
rewrite (data_at_share_join (fst (slice.cleave sh)) (snd (slice.cleave sh)) sh).
auto.
apply slice.cleave_join.
Qed.

Lemma body_make_foo: semax_body Vprog Gprog f_make_foo make_foo_spec.
Proof.
unfold make_foo_spec.
start_function.
forward_call (Tstruct _foo_object noattr).
   split3; simpl; auto; computable.
Intros p.
forward_if
  (PROP ( )
   LOCAL (temp _p p; gvars gv)
   SEP (malloc_token Ews (Tstruct _foo_object noattr) p;
          data_at_ Ews (Tstruct _foo_object noattr) p;
          object_methods foo_invariant (gv _foo_methods))).
*
change (Memory.EqDec_val p nullval) with (eq_dec p nullval).
if_tac; entailer!.
*
forward_call tt.
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
unfold object_mpred.
Exists foo_invariant (gv _foo_methods).
sep_apply (split_object_methods foo_invariant (gv _foo_methods)).
unfold foo_invariant at 4.
entailer!.
simpl.
unfold_field_at 1%nat.
cancel.
unfold withspacer; simpl.
rewrite !field_at_data_at.
simpl.
apply derives_refl'.
rewrite <- ?sepcon_assoc. (* needed if Archi.ptr64=true *)
rewrite !field_compatible_field_address; auto with field_compatible.
clear - H.
(* TODO: simplify the following proof. *)
destruct p; try contradiction.
destruct H as [AL SZ].
repeat split; auto.
simpl in *; omega.
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


Lemma make_object_methods:
  forall sh instance reset twiddle mtable,
  readable_share sh ->
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  data_at sh (Tstruct _methods noattr) (reset, twiddle) mtable
  |-- object_methods instance mtable.
Proof.
  intros.
  unfold object_methods.
  Exists sh reset twiddle.
  entailer!.
Qed.

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
end.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
(* assert_gvar _foo_methods. (* TODO: this is needed for a field_compatible later on *) *)
fold noattr cc_default.

(* 0. This part should be handled automatically by start_function *)
gather_SEP 0 1; 
replace_SEP 0 (data_at Ews (Tstruct _methods noattr) 
   (gv _foo_reset, gv _foo_twiddle) (gv _foo_methods)). {
  entailer!.
  unfold_data_at 2%nat.
  rewrite <- mapsto_field_at with (gfs := [StructField _twiddle]) (v:= (gv _foo_twiddle))
  by  auto with field_compatible.
  rewrite field_at_data_at.  rewrite !field_compatible_field_address by auto with field_compatible.
  rewrite !isptr_offset_val_zero by auto.
  rewrite sepcon_comm.
  apply derives_refl.
}

(* 1. Prove that [mtable] is a proper method-table for foo-objects *)

make_func_ptr _foo_twiddle.
make_func_ptr _foo_reset.
sep_apply (make_object_methods Ews foo_invariant(gv _foo_reset) (gv _foo_twiddle) (gv _foo_methods)); auto.

(* 2. Build an instance of class [foo], called [p] *)
forward_call (* p = make_foo(); *)
        gv.
Intros p.

(* 3. Done with object_methods for the foreseeable future *)
freeze [1]  MT. gather_SEP 1.

(* Illustration of an alternate method to prove the method calls.
   Method 1:  comment out lines AA and BB and the entire range CC-DD.
   Method 2:  comment out lines AA-BB, inclusive.
*)

(* AA *) try (tryif 
  (method_call (p, @nil Z) (@nil Z) whatever;
   method_call (p, 3, @nil Z) [3%Z] i;
     [simpl; computable | ])
(* BB *)  then fail else fail 99)
  .

(* CC *)
(* 4. first method-call *)
unfold object_mpred.
Intros instance mtable0.
forward. (*  mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0.
forward. (* p_reset = mtable->reset; *)
forward_call (* p_reset(p); *)
      (p, @nil Z).
(* Finish the method-call by regathering the object p back together *)
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [] p instance mtable0).
deadvars!. clear.

(* 5. second method-call *)
unfold object_mpred.
Intros instance mtable0.
forward.  (* mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0.
forward.   (* p_twiddle = mtable->twiddle; *)
forward_call (* i = p_twiddle(p,3); *)
      (p, 3, @nil Z).
  simpl. computable.
Intros i.
simpl in H0.
sep_apply (make_object_methods sh instance r0 t0 mtable0); auto.
sep_apply (object_mpred_i [3] p instance mtable0).
deadvars!. clear - H0.

(* DD *)

(* 6. return *)
forward.  (* return i; *)
Exists i; entailer!.
Qed.





