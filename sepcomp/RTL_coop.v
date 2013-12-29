Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.

Require Import RTL.

Inductive RTL_core : Type :=
  | RTL_State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset),             (**r register state *)
      RTL_core
  | RTL_Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val),         (**r arguments to the call *)
      RTL_core
  | RTL_Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val),                 (**r return value for the call *)
      RTL_core.

(* Transformations between the new and the old definitions of state *)
Definition core2state (q:RTL_core)(m:mem): state:=
  match q with
      RTL_State stack f sp pc rs => State stack f sp pc rs m
    | RTL_Callstate stack f args => Callstate stack f args m
    | RTL_Returnstate stack v => Returnstate stack v m
  end.

Definition state2core (s:state): RTL_core * mem :=
  match s with
      State stack f sp pc rs m => (RTL_State stack f sp pc rs, m)
    | Callstate stack f args m => (RTL_Callstate stack f args, m)
    | Returnstate stack v m => (RTL_Returnstate stack v, m)
  end.

Section RELSEM.

Inductive RTL_corestep (ge:genv): RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | rtl_corestep_exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_corestep_exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' (rs#res <- v)) m
  | rtl_corestep_exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' (rs#dst <- v)) m
  | rtl_corestep_exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m'
  | rtl_corestep_exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_Callstate (Stackframe res f sp pc' rs :: s) fd rs##args) m
  | rtl_corestep_exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      RTL_corestep ge (RTL_State s f (Vptr stk Int.zero) pc rs) m
        (RTL_Callstate s fd rs##args) m'
  | rtl_corestep_exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' t v m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      external_call ef ge rs##args m t v m' ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
         (RTL_State s f sp pc' (rs#res <- v)) m'
  | rtl_corestep_exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_corestep_exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_corestep_exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      RTL_corestep ge (RTL_State s f (Vptr stk Int.zero) pc rs) m
        (RTL_Returnstate s (regmap_optget or Vundef rs)) m'
  | rtl_corestep_exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      RTL_corestep ge (RTL_Callstate s (Internal f) args) m
        (RTL_State s
                  f
                  (Vptr stk Int.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params)))
        m'
(*no external calls
  | rtl_corestep_exec_function_external:
      forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      RTL_corestep ge (Callstate s (External ef) args) m
         t (Returnstate s res m')*)
  | rtl_corestep_exec_return:
      forall res f sp pc rs s vres m,
      RTL_corestep ge (RTL_Returnstate (Stackframe res f sp pc rs :: s) vres) m
        (RTL_State s f sp pc (rs#res <- vres)) m.

(* IMO this should be redefined from scratch. *)
Definition RTL_corestepX (ge:genv) (p: RTL_core) (m: mem) (q: RTL_core) (m0: mem): Prop.
  destruct p; destruct q.
  apply (exists t, step ge (State stack f sp pc rs m) t (State stack0 f0 sp0 pc0 rs0 m0)).
  apply (exists t, step ge (State stack f sp pc rs m) t (Callstate stack0 f0 args m0)).
  apply (exists t, step ge (State stack f sp pc rs m) t (Returnstate stack0 v m0)).
  apply (match f with
             Internal f' =>
             exists t, step ge (Callstate stack f args m) t (State stack0 f0 sp pc rs m0)
           | External _ => False 
         end).
  apply False.
  apply False.
  apply (exists t, step ge (Returnstate stack v m) t (State stack0 f sp pc rs m0)).
  apply False.
  apply False.
Defined.

Goal forall ge p m q m0,
     RTL_corestep ge p m q m0 -> RTL_corestepX ge p m q m0.
Proof. intros.
  inv H; simpl in *.
  eexists; eapply exec_Inop; eauto.
  eexists; eapply exec_Iop; eauto.
  eexists; eapply exec_Iload; eauto.
  eexists; eapply exec_Istore; eauto.
  eexists; eapply exec_Icall; eauto.
  eexists; eapply exec_Itailcall; eauto.
  eexists; eapply exec_Ibuiltin; eauto.
  eexists; eapply exec_Icond; eauto.
  eexists; eapply exec_Ijumptable; eauto.
  eexists; eapply exec_Ireturn; eauto.
  eexists; eapply exec_function_internal; eauto.
  eexists; eapply exec_return; eauto.
Qed.
Goal forall ge p m q m0,
     RTL_corestepX ge p m q m0 -> RTL_corestep ge p m q m0.
Proof. intros.
  destruct p; destruct q; simpl in *; try contradiction.
  destruct H.
    inv H.
     eapply rtl_corestep_exec_Inop; eauto.
     eapply rtl_corestep_exec_Iop; eauto.
     eapply rtl_corestep_exec_Iload; eauto.
     eapply rtl_corestep_exec_Istore; eauto.
     eapply rtl_corestep_exec_Ibuiltin; eauto.
     eapply rtl_corestep_exec_Icond; eauto.
     eapply rtl_corestep_exec_Ijumptable; eauto.
  destruct H.
    inv H.
     eapply rtl_corestep_exec_Icall; eauto.
     eapply rtl_corestep_exec_Itailcall; eauto.
  destruct H.
    inv H.
     eapply rtl_corestep_exec_Ireturn; eauto.
  destruct f; try contradiction.
  destruct H.
    inv H.
      eapply rtl_corestep_exec_function_internal; eauto.
  destruct H.
    inv H.
      eapply rtl_corestep_exec_return; eauto.
Qed.
End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Require Import sepcomp.core_semantics.

(* New initial state *)
Definition RTL_initial_core (ge: genv) (v:val)(args: list val): option RTL_core:=
  match v with
      Vptr b i =>
      if Int.eq_dec i Int.zero
      then match Genv.find_funct_ptr ge b with
               None => None
             | Some f => Some (RTL_Callstate nil f args)
           end
      else None
    | _ => None
  end.

(** A final state is a [Returnstate] with an empty call stack. *)

(*LENB: in shared-memory compcert, we should allow arbitrary 
  return values, not just integers*)
Definition RTL_halted (c: RTL_core ): option val :=
  match c with
(*      RTL_Returnstate nil (Vint i) => Some (Vint i)*)
      RTL_Returnstate nil v => Some v
    | _ => None
  end.


(* New definition of semantics *)
Definition RTL_at_external (c: RTL_core): option (external_function * signature * list val) :=
  match c with
    | RTL_State stack f sp pc rs => None
    | RTL_Callstate stack f args =>  match f with
                                        Internal _ => None
                                      | External f' => Some( f', ef_sig f', args)
                                    end
    | RTL_Returnstate stack v => None
  end.

Definition RTL_after_external (vret: option val)(c: RTL_core): option RTL_core :=
  match c with
    | RTL_State stack f sp pc rs => None
    | RTL_Callstate stack f args => 
      match f with
          Internal _ => None
        | External f' => match vret with
                             None => Some (RTL_Returnstate stack Vundef)
                           | Some v => Some (RTL_Returnstate stack v)
                         end
      end
    | RTL_Returnstate stack v => None
  end.           

Lemma corestep_not_external: forall (ge : genv) (m : mem) (q : RTL_core) (m' : mem) (q' : RTL_core),
                               RTL_corestep ge q m q' m' -> RTL_at_external q = None.
  intros. inv H; reflexivity. 
Qed.

Lemma corestep_not_halted: forall (ge : genv) (m : mem) (q : RTL_core) (m' : mem) (q' : RTL_core),
                             RTL_corestep ge q m q' m' -> RTL_halted q = None.
Proof. intros. inv H; try reflexivity. Qed.
(*Old proof:
Lemma corestep_not_halted: forall (ge : genv) (m : mem) (q : RTL_core) (m' : mem) (q' : RTL_core),
                             RTL_corestep ge q m q' m' -> RTL_halted q = None.
Proof. intros.
  destruct q; destruct q'; simpl in *; try reflexivity; try contradiction.
  intros. inv H. inversion H.
  Lemma list_false: forall A s (a:A) , s = a::s -> False.  
    induction s.
    discriminate.
    inversion 1.
    apply IHs in H2; trivial.
  Qed.
  apply list_false in H5. contradiction.
Qed. 
*)

Lemma external_xor_halted: forall q : RTL_core, RTL_at_external q = None \/ RTL_halted q = None.
  destruct q; simpl; try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma after_xor_at_external: forall (retv : option val) (q q' : RTL_core),
                               RTL_after_external retv q = Some q' -> RTL_at_external q' = None.
  intros. destruct q; destruct q'; try destruct f; destruct retv; simpl in *; try discriminate; try reflexivity.
Qed.

Definition RTL_core_sem : CoreSemantics genv RTL_core mem.
  eapply @Build_CoreSemantics with (at_external:= RTL_at_external) (after_external:= RTL_after_external)(corestep:=RTL_corestep)(halted:= RTL_halted).
  apply RTL_initial_core.
  eapply corestep_not_external.
  eapply corestep_not_halted.
  eapply external_xor_halted.
  eapply after_xor_at_external.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Require Import sepcomp.mem_lemmas. (*for mem_forward*)

Lemma rtl_coop_forward : forall g c m c' m' (CS: RTL_corestep g c m c' m'), 
      mem_forward m m'.
Proof. intros.
       inv CS; try apply mem_forward_refl.
         (*Storev*)
          destruct a; simpl in H1; inv H1. 
          eapply store_forward. eassumption. 
         eapply free_forward; eassumption.
         (*builtin*) 
          eapply external_call_mem_forward; eassumption.
         eapply free_forward; eassumption.
         eapply alloc_forward; eassumption.
Qed.

Program Definition rtl_coop_sem : 
  CoopCoreSem genv RTL_core.
apply Build_CoopCoreSem with (coopsem := RTL_core_sem).
  apply rtl_coop_forward.
Defined.
