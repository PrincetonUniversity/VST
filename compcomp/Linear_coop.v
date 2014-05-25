Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.

Require Import Linear.

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import core_semantics.

Require Import compcomp.val_casted.

(** Linear execution states. *)

Inductive Linear_core: Type :=
  | Linear_State:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (f: Linear.function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (c: Linear.code)                (**r current program point *)
             (rs: Linear.locset),             (**r location state *)
      Linear_core
  | Linear_Callstate:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (f: Linear.fundef)              (**r function to call *)
             (rs: Linear.locset),             (**r location state at point of call *)
      Linear_core
  | Linear_Returnstate:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (retty: option typ)      (**r optional return register int-floatness *)
             (rs: Linear.locset),             (**r location state at point of return *)
      Linear_core.

Section RELSEM.

Variable ge: genv.

Inductive Linear_step: Linear_core -> mem -> Linear_core -> mem -> Prop :=
  | lin_exec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      Linear_step (Linear_State s f sp (Lgetstack sl ofs ty dst :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_exec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      Linear_step (Linear_State s f sp (Lsetstack src sl ofs ty :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_exec_Lop:
      forall s f sp op args res b rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      Linear_step (Linear_State s f sp (Lop op args res :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_exec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      Linear_step (Linear_State s f sp (Lload chunk addr args dst :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      Linear_step (Linear_State s f sp (Lstore chunk addr args src :: b) rs) m
        (Linear_State s f sp b rs') m'
  | lin_exec_Lcall:
      forall s f sp sig ros b rs m f',
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      Linear_step (Linear_State s f sp (Lcall sig ros :: b) rs) m
        (Linear_Callstate (Stackframe f sp rs b:: s) f' rs) m
  | lin_exec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m',
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some f' ->
      (*Lenb: Mach's at/after external treatment, and absence of m and ge in atExternal
           may need this:
           only internal calls can be tailcalls 
            (exists f'', f' = Internal f'') ->*)
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Linear_step (Linear_State s f (Vptr stk Int.zero) (Ltailcall sig ros :: b) rs) m
        (Linear_Callstate s f' rs') m'
  | lin_exec_Lbuiltin:
      forall s f sp rs m ef args res b t vl rs' m',
      external_call' ef ge (reglist rs args) m t vl m' ->
      rs' = Locmap.setlist (map R res) vl (undef_regs (destroyed_by_builtin ef) rs) ->
      Linear_step (Linear_State s f sp (Lbuiltin ef args res :: b) rs) m
         (Linear_State s f sp b rs') m'
(*NO ANNOTS YET
  | lin_exec_Lannot:
      forall s f sp rs m ef args b t v m',
      external_call' ef ge (map rs args) m t v m' ->
      Linear_step (Linear_State s f sp (Lannot ef args :: b) rs) m
         (Linear_State s f sp b rs) m'*)
  | lin_exec_Llabel:
      forall s f sp lbl b rs m,
      Linear_step (Linear_State s f sp (Llabel lbl :: b) rs) m
        (Linear_State s f sp b rs) m
  | lin_exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      Linear_step (Linear_State s f sp (Lgoto lbl :: b) rs) m
        (Linear_State s f sp b' rs) m
  | lin_exec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b',
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      Linear_step (Linear_State s f sp (Lcond cond args lbl :: b) rs) m
        (Linear_State s f sp b' rs') m
  | lin_exec_Lcond_false:
      forall s f sp cond args lbl b rs m rs',
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      Linear_step (Linear_State s f sp (Lcond cond args lbl :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      Linear_step (Linear_State s f sp (Ljumptable arg tbl :: b) rs) m
        (Linear_State s f sp b' rs') m
  | lin_exec_Lreturn:
      forall s f stk b rs m m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Linear_step (Linear_State s f (Vptr stk Int.zero) (Lreturn :: b) rs) m
        (Linear_Returnstate s (sig_res (fn_sig f)) (return_regs (parent_locset s) rs)) m'
  | lin_exec_function_internal:
      forall s f rs m rs' m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      Linear_step (Linear_Callstate s (Internal f) rs) m
        (Linear_State s f (Vptr stk Int.zero) f.(fn_code) rs') m'
(*NO RULE FOR EXTERNAL CALLS
  | lin_exec_function_external:
      forall s ef args res rs1 rs2 m t m',
      args = map rs1 (loc_arguments (ef_sig ef)) ->
      external_call' ef ge args m t res m' ->
      rs2 = Locmap.setlist (map R (loc_result (ef_sig ef))) res rs1 ->
      Linear_step (Linear_Callstate s (External ef) rs1) m
          (Linear_Returnstate s rs2) m'*)
  | lin_exec_return:
      forall s f sp rs0 c rs retty m,
      Linear_step (Linear_Returnstate (Stackframe f sp rs0 c :: s) retty rs) m
         (Linear_State s f sp c rs) m.

End RELSEM.

Definition Linear_initial_core (ge:genv) (v: val) (args:list val): 
           option Linear_core :=match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                     let tyl := sig_args (funsig f) in
                     if val_has_type_list_func args (sig_args (funsig f))
                        && vals_defined args
                     then Some (Linear_Callstate
                                      nil
                                      f 
                                      (Locmap.setlist
                                          (loc_arguments (funsig f)) 
                                          (encode_longs tyl args)
                                          (Locmap.init Vundef)))
                     else None
                    | External _ => None
                     end
               end
          else None
     | _ => None
    end.
(*Compcert's original definition is for initial PROGRAM states
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f (Locmap.init Vundef) m0).
*)

(*Maybe generalize to other types?*)
Definition Linear_halted (q : Linear_core): option val :=
    match q with 
      (*Return Tlong, which must be decoded*)
      | Linear_Returnstate nil (Some Tlong) rs => 
           match loc_result (mksignature nil (Some Tlong)) with
             | nil => None
             | r1 :: r2 :: nil => 
                 match decode_longs (Tlong::nil) (rs (R r1)::rs (R r2)::nil) with
                   | v :: nil => Some v
                   | _ => None
                 end
             | _ => None
           end

      (*Return a value of any other typ*)
      | Linear_Returnstate nil (Some retty) rs => 
           match loc_result (mksignature nil (Some retty)) with
            | nil => None
            | r :: TL => match TL with 
                           | nil => Some (rs (R r))
                           | _ :: _ => None
                         end
           end

      (*Return Tvoid - modeled as integer return*)
      | Linear_Returnstate nil None rs => Some (rs (R AX))

      | _ => None
    end.

(*Original had this:
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result (mksignature nil (Some Tint)) = r :: nil ->
      rs (R r) = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.
*)

Definition Linear_at_external (c: Linear_core) : option (external_function * signature * list val) :=
  match c with
  | Linear_State _ _ _ _ _ => None
  | Linear_Callstate s f rs => 
      match f with
        | Internal f => None
        | External ef => 
          Some (ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) 
                                 (map rs (loc_arguments (ef_sig ef))))
      end
  | Linear_Returnstate _ _ _ => None
 end.

Definition Linear_after_external (vret: option val) (c: Linear_core) : option Linear_core :=
  match c with 
    | Linear_Callstate s f rs => 
      match f with
        | Internal f => None
        | External ef => 
          match vret with
            | None => Some (Linear_Returnstate s (sig_res (ef_sig ef))
                             (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                               (encode_long (sig_res (ef_sig ef)) Vundef) rs))
            | Some v => Some (Linear_Returnstate s (sig_res (ef_sig ef))
                               (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                                 (encode_long (sig_res (ef_sig ef)) v) rs))
          end
      end
    | _ => None
  end.

Lemma Linear_corestep_not_at_external:
       forall ge m q m' q', Linear_step ge q m q' m' -> Linear_at_external q = None.
  Proof. intros. inv H; try reflexivity. Qed.

Lemma Linear_corestep_not_halted : forall ge m q m' q', 
       Linear_step ge q m q' m' -> Linear_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.
    
Lemma Linear_at_external_halted_excl :
       forall q, Linear_at_external q = None \/ Linear_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma Linear_after_at_external_excl : forall retv q q',
      Linear_after_external retv q = Some q' -> Linear_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl.
         destruct retv; inv H0; simpl; trivial.
  Qed.

Definition Linear_core_sem : CoreSemantics genv Linear_core mem.
  eapply (@Build_CoreSemantics _ _ _ 
           Linear_initial_core
           Linear_at_external
           Linear_after_external
           Linear_halted
           Linear_step).
    apply Linear_corestep_not_at_external.
    apply Linear_corestep_not_halted.
    apply Linear_at_external_halted_excl.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma Linear_forward : forall g c m c' m' (CS: Linear_step g c m c' m'), 
                    mem_forward m m'.
  Proof. intros.
   inv CS; try apply mem_forward_refl.
         (*Storev*)
          destruct a; simpl in H0; inv H0. 
          eapply store_forward. eassumption. 
         (*Ltailcall*)
           eapply free_forward; eassumption.
         (*Lbuiltin*) 
           inv H. 
           eapply external_call_mem_forward; eassumption.
         (*Lannot
           inv H. 
           eapply external_call_mem_forward; eassumption.*)
         (*free*)
           eapply free_forward; eassumption.
         (*internal function*)
           eapply alloc_forward; eassumption.
Qed.

Program Definition Linear_coop_sem : 
  CoopCoreSem genv Linear_core.
apply Build_CoopCoreSem with (coopsem := Linear_core_sem).
  apply Linear_forward.
Defined.

