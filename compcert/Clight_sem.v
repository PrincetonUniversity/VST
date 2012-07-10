(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Csem.
Require Import Clight.

Section SEMANTICS.

Variable ge: genv.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

(** [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. *)

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation op v1 (typeof a1) v2 (typeof a2) (Mem.valid_pointer m) = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Econdition: forall a1 a2 a3 ty v1 b v' v,
      eval_expr a1 v1 ->
      bool_val v1 (typeof a1) = Some b ->
      eval_expr (if b then a2 else a3) v' ->
      sem_cast v' (typeof (if b then a2 else a3)) ty = Some v ->
      eval_expr (Econdition a1 a2 a3 ty) v
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs -> type_is_volatile (typeof a) = false ->
      deref_loc ge (typeof a) m loc ofs E0 v ->
      eval_expr a v

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

with eval_lvalue: expr -> block -> int -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Int.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      type_of_global ge l = Some ty ->
      eval_lvalue (Evar id ty) l Int.zero
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs
 | eval_Efield_struct:   forall a i ty l ofs id fList att delta,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tstruct id fList att ->
      field_offset i fList = OK delta ->
      eval_lvalue (Efield a i ty) l (Int.add ofs (Int.repr delta))
 | eval_Efield_union:   forall a i ty l ofs id fList att,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tunion id fList att ->
      eval_lvalue (Efield a i ty) l ofs.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

(** [eval_exprlist ge e m al tyl vl] evaluates a list of r-value
  expressions [al], cast their values to the types given in [tyl],
  and produces the list of cast values [vl].  It is used to
  evaluate the arguments of function calls. *)

Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty = Some v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.


(** ** Transition semantics for statements and functions *)

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kwhile: expr -> statement -> cont -> cont       (**r [Kwhile e s k] = after [s] in [while (e) s] *)
  | Kdowhile: expr -> statement -> cont -> cont       (**r [Kdowhile e s k] = after [s] in [do s while (e)] *)
  | Kfor2: expr -> statement -> statement -> cont -> cont       (**r [Kfor2 e2 e3 s k] = after [s] in [for'(e2;e3) s] *)
  | Kfor3: expr -> statement -> statement -> cont -> cont       (**r [Kfor3 e2 e3 s k] = after [e3] in [for'(e2;e3) s] *)
  | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kcall: option ident ->                  (**r where to store result *)
           function ->                      (**r calling function *)
           env ->                           (**r local env of calling function *)
           temp_env ->                      (**r temporary env of calling function *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kwhile e s k => call_cont k
  | Kdowhile e s k => call_cont k
  | Kfor2 e2 e3 s k => call_cont k
  | Kfor3 e2 e3 s k => call_cont k
  | Kswitch k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** States *)

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) : state.
                 
(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont) 
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 =>
      find_label lbl s1 (Kwhile a s1 k)
  | Sdowhile a s1 =>
      find_label lbl s1 (Kdowhile a s1 k)
  | Sfor' a2 a3 s1 =>
      match find_label lbl s1 (Kfor2 a2 a3 s1 k) with
      | Some sk => Some sk
      | None => find_label lbl a3 (Kfor3 a2 a3 s1 k)
      end
  | Sswitch e sl =>
      find_label_ls lbl sl (Kswitch k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont) 
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Transition relation *)

Inductive step: state -> trace -> state -> Prop :=

  | step_assign:   forall f a1 a2 k e le m loc ofs v2 v t m',
      eval_lvalue e le m a1 loc ofs ->
      eval_expr e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      assign_loc ge (typeof a1) m loc ofs v t m' ->
      step (State f (Sassign a1 a2) k e le m)
         t (State f Sskip k e le m')

  | step_set:   forall f id a k e le m v,
      eval_expr e le m a v ->
      step (State f (Sset id a) k e le m)
        E0 (State f Sskip k e (PTree.set id v le) m)

  | step_vol_read:   forall f id a k e le m loc ofs t v,
      eval_lvalue e le m a loc ofs ->
      deref_loc ge (typeof a) m loc ofs t v ->
      type_is_volatile (typeof a) = true ->
      step (State f (Svolread id a) k e le m)
         t (State f Sskip k e (PTree.set id v le) m)

  | step_call:   forall f optid a al k e le m tyargs tyres vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres ->
      step (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)

  | step_seq:  forall f s1 s2 k e le m,
      step (State f (Ssequence s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)
  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
  | step_continue_seq: forall f s k e le m,
      step (State f Scontinue (Kseq s k) e le m)
        E0 (State f Scontinue k e le m)
  | step_break_seq: forall f s k e le m,
      step (State f Sbreak (Kseq s k) e le m)
        E0 (State f Sbreak k e le m)

  | step_ifthenelse:  forall f a s1 s2 k e le m v1 b,
      eval_expr e le m a v1 ->
      bool_val v1 (typeof a) = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f (if b then s1 else s2) k e le m)

  | step_while_false: forall f a s k e le m v,
      eval_expr e le m a v ->
      bool_val v (typeof a) = Some false ->
      step (State f (Swhile a s) k e le m)
        E0 (State f Sskip k e le m)
  | step_while_true: forall f a s k e le m v,
      eval_expr e le m a v ->
      bool_val v (typeof a) = Some true ->
      step (State f (Swhile a s) k e le m)
        E0 (State f s (Kwhile a s k) e le m)
  | step_skip_or_continue_while: forall f x a s k e le m,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kwhile a s k) e le m)
        E0 (State f (Swhile a s) k e le m)
  | step_break_while: forall f a s k e le m,
      step (State f Sbreak (Kwhile a s k) e le m)
        E0 (State f Sskip k e le m)

  | step_dowhile: forall f a s k e le m,
      step (State f (Sdowhile a s) k e le m)
        E0 (State f s (Kdowhile a s k) e le m)
  | step_skip_or_continue_dowhile_false: forall f x a s k e le m v,
      x = Sskip \/ x = Scontinue ->
      eval_expr e le m a v ->
      bool_val v (typeof a) = Some false ->
      step (State f x (Kdowhile a s k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_or_continue_dowhile_true: forall f x a s k e le m v,
      x = Sskip \/ x = Scontinue ->
      eval_expr e le m a v ->
      bool_val v (typeof a) = Some true ->
      step (State f x (Kdowhile a s k) e le m)
        E0 (State f (Sdowhile a s) k e le m)
  | step_break_dowhile: forall f a s k e le m,
      step (State f Sbreak (Kdowhile a s k) e le m)
        E0 (State f Sskip k e le m)

  | step_for_false: forall f a2 a3 s k e le m v,
      eval_expr e le m a2 v ->
      bool_val v (typeof a2) = Some false ->
      step (State f (Sfor' a2 a3 s) k e le m)
        E0 (State f Sskip k e le m)
  | step_for_true: forall f a2 a3 s k e le m v,
      eval_expr e le m a2 v ->
      bool_val v (typeof a2) = Some true ->
      step (State f (Sfor' a2 a3 s) k e le m)
        E0 (State f s (Kfor2 a2 a3 s k) e le m)
  | step_skip_or_continue_for2: forall f x a2 a3 s k e le m,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kfor2 a2 a3 s k) e le m)
        E0 (State f a3 (Kfor3 a2 a3 s k) e le m)
  | step_break_for2: forall f a2 a3 s k e le m,
      step (State f Sbreak (Kfor2 a2 a3 s k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_for3: forall f a2 a3 s k e le m,
      step (State f Sskip (Kfor3 a2 a3 s k) e le m)
        E0 (State f (Sfor' a2 a3 s) k e le m)
  | step_break_for3: forall f a2 a3 s k e le m,
      step (State f Sbreak (Kfor3 a2 a3 s k) e le m)
        E0 (State f Sskip k e le m)

  | step_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k e le m v v' m',
      eval_expr e le m a v -> 
      sem_cast v (typeof a) f.(fn_return) = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m)
        E0 (Returnstate v' (call_cont k) m')
  | step_skip_call: forall f k e le m m',
      is_call_cont k ->
      f.(fn_return) = Tvoid ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')

  | step_switch: forall f a sl k e le m n,
      eval_expr e le m a (Vint n) ->
      step (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
  | step_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m)
        E0 (State f Sskip k e le m)
  | step_continue_switch: forall f k e le m,
      step (State f Scontinue (Kswitch k) e le m)
        E0 (State f Scontinue k e le m)

  | step_label: forall f lbl s k e le m,
      step (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)

  | step_internal_function: forall f vargs k m e le m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_temps)) ->
      alloc_variables empty_env m (f.(fn_vars)) e m1 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) =
                        Some le ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1) 

  | step_external_function: forall ef targs tres vargs k m vres t m',
      external_call ef  ge vargs m t vres m' ->
      step (Callstate (External ef targs tres) vargs k m)
         t (Returnstate vres k m')

  | step_returnstate_none: forall v f e le k m,
      step (Returnstate v (Kcall None f e le k) m)
        E0 (State f Sskip k e le m)
  | step_returnstate_some: forall v id f e le k m,
      step (Returnstate v (Kcall (Some id) f e le k) m)
        E0 (State f Sskip k e (PTree.set id v le) m).


End SEMANTICS.

(** * Whole-program semantics *)

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s ->
      initial_state p (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

(** Wrapping up these definitions in a small-step semantics. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  (* assign *)
  inv H5; auto. exploit volatile_store_receptive; eauto. intros EQ. subst t2; econstructor; eauto.
  (* volatile read *)
  inv H3; auto. exploit volatile_load_receptive; eauto. intros [v2 LD]. 
  econstructor. eapply step_vol_read; eauto. eapply deref_loc_volatile; eauto. 
  (* external *)
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; intros. inv H; simpl; try omega.
  inv H3; simpl; try omega. inv H5; simpl; omega.
  inv H1; simpl; try omega. inv H4; simpl; omega.
  eapply external_call_trace_length; eauto.
Qed.

