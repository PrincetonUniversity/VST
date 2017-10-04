Require Import List.
Require Import Arith.
Require Import Relations.

Require Import msl.msl_standard.

(* Identifiers and addresses are just drawn from the naturals.*)
Definition ident := nat.
Definition addr  := nat.

(* Values are either integers or pointers (addresses) *)
Inductive val : Set :=
  | int_val : nat -> val
  | ptr_val : addr -> val.

Definition locals := ShareMap.map ident val.
Instance Join_locals: Join locals := ShareMap.Join_map _ _ (Join_equiv _).
Instance locals_sa : Sep_alg locals := ShareMap.sa_map _ _ _.

(* We characterize expressions as functions from local variable
   environments whcih are monotone with respect to increasing the
   environment.
*)
Definition expr :=
  { f: locals -> option val |
    forall l l' v, join_sub l l' -> f l = Some v -> f l' = Some v }.

Definition mem := ShareMap.map addr val.
Instance Join_mem: Join mem := ShareMap.Join_map _ _ (Join_equiv _).
Instance mem_sa : Sep_alg mem := ShareMap.sa_map _ _ _.

(* The syntax of commands.  These are pretty basic
   imperative language constructs.
*)
Inductive cmd :=
  | skip
  | seq : cmd -> cmd -> cmd
  | call : ident -> ident -> list expr -> cmd
  | ret : expr -> cmd
  | load : ident -> expr -> cmd
  | store : expr -> expr -> cmd
  | assign : ident -> expr -> cmd
  | cif : expr -> cmd -> cmd -> cmd
  | while : expr -> cmd -> cmd.

(* A function declaration consists of a list of formal arguments
   (local identifiers which will receive the actual arguments),
   a list of local variables together with their initial values,
   and a command implementing the function body.

   Finally we include a syntactic validity fact -- the formals
   and declared locals are disjoint.
*)
Inductive fun_decl :=
  { fnd_formals : list ident
  ; fnd_locals  : list (ident * val)
  ; fnd_cmd     : cmd
  ; fnd_valid   : NoDup (fnd_formals ++ map (@fst _ _) fnd_locals)
  }.

(* A program is a mapping from function identifiers to function declarations. *)
Definition program_unit := nat -> option fun_decl.


(** Operational semantics **)

(* Controls capture the control stack of imperative languages.

    kseq c k       means "execute c, then run k"
    kcall i rho k  means "when a return is executed, unwind to this point,
                         restore local varibles rho, and update i with the
                         return value"
    kext i f vs k  means "I tried to call funcion f with arguments vs,
                          but f isn't defined"
    knil           means "safely halted"
 *)
Inductive ctl :=
  | kseq : cmd -> ctl -> ctl
  | kcall : ident -> locals -> ctl -> ctl
  | kext  : ident -> ident -> list val -> ctl -> ctl
  | knil : ctl.

(* We define a small step semantics which manipulate states of this form.*)
Definition state := (ctl * locals * mem)%type.

(* In local environment rho, the list of expressions es have values vs *)
Fixpoint evaluate_exprs (rho:locals) (es:list expr) (vs:list val) : Prop :=
  match es, vs with
  | e::es', v::vs' => proj1_sig e rho = Some v /\ evaluate_exprs rho es' vs'
  | nil, nil => True
  | _, _ => False
  end.

(* the funtion make_locals builds the initial local variable
   environment at function entry
*)
Section function_entry_locals.
  Variable vals:list val.
  Variable fd:fun_decl.

  Let actuals := combine (fnd_formals fd) vals.

  Definition make_locals := ShareMap.build_map _ _ _ (actuals ++ fnd_locals fd).
End function_entry_locals.

(* unwind_return drops all the leading kseq constructions to finde
   the correct function return position
*)
Fixpoint unwind_return (k:ctl) : option (ident * locals * ctl):=
   match k with
   | kseq _ k' => unwind_return k'
   | kcall i rho k => Some (i,rho,k)
   | kext _ _ _ _ => None
   | knil => None
   end.

(* Main small step semantics definition.
   We send state (k,rho,m) to state (k',rho',m')
   when we execute command c (in program p).
*)
Inductive step (pu:program_unit) :
  forall (k:ctl) (rho:locals) (m:mem)
         (c:cmd)
         (k':ctl) (rho':locals) (m':mem), Prop :=

 | step_skip : forall k rho m,
       step pu  k rho m
                skip
                k rho m

 | step_seq : forall k rho m c1 c2,
       step pu k rho m
               (seq c1 c2)
               (kseq c1 (kseq c2 k)) rho m

 | step_if_false : forall k rho m e c1 c2,
       proj1_sig e rho = Some (int_val 0) ->

       step pu k rho m
               (cif e c1 c2)
               (kseq c2 k) rho m

 | step_if_true : forall k rho m x e c1 c2,
       x <> 0 ->
       proj1_sig e rho = Some (int_val x) ->

       step pu k rho m
               (cif e c1 c2)
               (kseq c1 k) rho m

 | step_while_false : forall k rho m e c,
       proj1_sig e rho = Some (int_val 0) ->

       step pu k rho m
               (while e c)
               k rho m

 | step_while_true : forall k rho m e c x,
       x <> 0 ->
       proj1_sig e rho = Some (int_val x) ->

       step pu k rho m
               (while e c)
               (kseq c (kseq (while e c) k)) rho m

 | step_ret : forall k rho m e v i rho' k' rho'',
       proj1_sig e rho = Some v ->
       unwind_return k = (Some (i,rho',k')) ->
       ShareMap.map_upd _ _ _ i v rho' = Some rho'' ->
       step pu k rho m
               (ret e)
               k' rho''  m

 | step_call_internal : forall k rho m x f exps vals fd,
       evaluate_exprs rho exps vals ->
       pu f = Some fd ->
       step pu k rho m
               (call x f exps)
               (kseq (fnd_cmd fd) (kcall x rho k))
                  (make_locals vals fd) m

 | step_call_external : forall k rho m x f exps vals,
       pu f = None ->
       evaluate_exprs rho exps vals ->
       step pu k rho m
               (call x f exps)
               (kext x f vals k) rho m

 | step_assign : forall k rho rho' m i e v,
       proj1_sig e rho = Some v ->
       ShareMap.map_upd _ _ _ i v rho = Some rho' ->
       step pu k rho m
               (assign i e)
               k rho' m

 | step_load : forall k rho rho' m i e a v,
       proj1_sig e rho = Some (ptr_val a) ->
       ShareMap.map_val _ _ a m = Some v ->
       ShareMap.map_upd _ _ _ i v rho = Some rho' ->
       step pu k rho m
               (load i e)
               k rho' m

 | step_store : forall k rho m e1 a e2 v m',
       proj1_sig e1 rho = Some (ptr_val a) ->
       proj1_sig e2 rho = Some v ->

       ShareMap.map_upd _ _ _ a v m = Some m' ->

       step pu k rho m
               (store e1 e2)
               k rho m'.

(* Pull off the outermost command and execute it *)
Inductive step' (pu:program_unit) :
  forall (st st':state), Prop :=

  | step'_step : forall c k rho m k' rho' m',
      step  pu k rho m c k' rho' m' ->
      step' pu (kseq c k,rho,m) (k',rho',m').

(* Evaluating a list of expressions is functional. *)
Lemma evaluate_exprs_fun : forall rho exps vals1 vals2,
  evaluate_exprs rho exps vals1 ->
  evaluate_exprs rho exps vals2 ->
  vals1 = vals2.
Proof.
  intros rho exps. induction exps; simpl; intros.
  destruct vals1. destruct vals2. auto. elim H0. elim H.
  destruct vals1. elim H. destruct vals2. elim H0.
  intuition. f_equal. congruence. auto.
Qed.

(* The small step semantics is functional (deterministic) *)
Lemma step_fun : forall pu k rho m c k1 rho1 m1 k2 rho2 m2,
  step pu k rho m c k1 rho1 m1 ->
  step pu k rho m c k2 rho2 m2 ->
  (k1,rho1,m1) = (k2,rho2,m2).
Proof.
  intros; inv H; inv H0; try congruence.
  assert (vals = vals0).
  eapply evaluate_exprs_fun; eauto.
  congruence.
  assert (vals = vals0).
  eapply evaluate_exprs_fun; eauto.
  congruence.
Qed.
