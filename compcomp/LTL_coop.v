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
Require Import Locations.
Require Import Conventions.

Require Import LTL. 

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.

Require Import compcomp.val_casted.

Inductive LTL_core : Type :=
  | LTL_State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point *)
             (ls: locset),            (**r location state *)
      LTL_core
  | LTL_Block:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (bb: bblock)             (**r current basic block *)
             (ls: locset),            (**r location state *)
      LTL_core
  | LTL_Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (ls: locset),            (**r location state of caller *)
      LTL_core
  | LTL_Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (retty: option typ)      (**r optional return register int-floatness *)
             (ls: locset),            (**r location state of callee *)
      LTL_core.

Definition LTL_at_external (c: LTL_core) : option (external_function * signature * list val) :=
  match c with
    | LTL_State _ _ _ _ _ => None
    | LTL_Block _ _ _ _ _ => None
    | LTL_Callstate s f rs => 
      match f with
        | Internal f => None
        | External ef => 
          Some (ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) 
                                 (map rs (loc_arguments (ef_sig ef))))
      end
    | LTL_Returnstate _ _ _ => None
 end.

Definition LTL_after_external (vret: option val) (c: LTL_core) : option LTL_core :=
  match c with 
    | LTL_Callstate s f rs => 
      match f with
        | Internal f => None
        | External ef => 
          match vret with
            | None => Some (LTL_Returnstate s (sig_res (ef_sig ef))
                (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                  (encode_long (sig_res (ef_sig ef)) Vundef) rs))
            | Some v => Some (LTL_Returnstate s (sig_res (ef_sig ef))
                (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                  (encode_long (sig_res (ef_sig ef)) v) rs))
          end
      end
    | _ => None
  end.

Section RELSEM.

Variable ge: genv.

Inductive ltl_corestep: LTL_core -> mem -> LTL_core -> mem -> Prop :=
  | ltl_exec_start_block: forall s f sp pc rs m bb,
      (fn_code f)!pc = Some bb ->
      ltl_corestep (LTL_State s f sp pc rs) m
        (LTL_Block s f sp bb rs) m
  | ltl_exec_Lop: forall s f sp op args res bb rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      ltl_corestep (LTL_Block s f sp (Lop op args res :: bb) rs) m
        (LTL_Block s f sp bb rs') m
  | ltl_exec_Lload: forall s f sp chunk addr args dst bb rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      ltl_corestep (LTL_Block s f sp (Lload chunk addr args dst :: bb) rs) m
        (LTL_Block s f sp bb rs') m
  | ltl_exec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      ltl_corestep (LTL_Block s f sp (Lgetstack sl ofs ty dst :: bb) rs) m
        (LTL_Block s f sp bb rs') m
  | ltl_exec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      ltl_corestep (LTL_Block s f sp (Lsetstack src sl ofs ty :: bb) rs) m
        (LTL_Block s f sp bb rs') m
  | ltl_exec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      ltl_corestep (LTL_Block s f sp (Lstore chunk addr args src :: bb) rs) m
        (LTL_Block s f sp bb rs') m'
  | ltl_exec_Lcall: forall s f sp sig ros bb rs m fd,
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      ltl_corestep (LTL_Block s f sp (Lcall sig ros :: bb) rs) m
        (LTL_Callstate (Stackframe f sp rs bb :: s) fd rs) m
  | ltl_exec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m',
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      ltl_corestep (LTL_Block s f (Vptr sp Int.zero) (Ltailcall sig ros :: bb) rs) m
        (LTL_Callstate s fd rs') m'
  | ltl_exec_Lbuiltin: forall s f sp ef args res bb rs m t vl rs' m',
      external_call' ef ge (reglist rs args) m t vl m' ->
      rs' = Locmap.setlist (map R res) vl (undef_regs (destroyed_by_builtin ef) rs) ->
      ltl_corestep (LTL_Block s f sp (Lbuiltin ef args res :: bb) rs) m
         (LTL_Block s f sp bb rs') m'
(* WE DON'T SUPPORT ANNOT YET
  | ltl_exec_Lannot: forall s f sp ef args bb rs m t vl m',
      external_call' ef ge (map rs args) m t vl m' ->
      ltl_corestep (LTL_Block s f sp (Lannot ef args :: bb) rs) m
         (LTL_Block s f sp bb rs) m' *)
  | ltl_exec_Lbranch: forall s f sp pc bb rs m,
      ltl_corestep (LTL_Block s f sp (Lbranch pc :: bb) rs) m
        (LTL_State s f sp pc rs) m
  | ltl_exec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m,
      eval_condition cond (reglist rs args) m = Some b ->
      pc = (if b then pc1 else pc2) ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      ltl_corestep (LTL_Block s f sp (Lcond cond args pc1 pc2 :: bb) rs) m
        (LTL_State s f sp pc rs') m
  | ltl_exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      ltl_corestep (LTL_Block s f sp (Ljumptable arg tbl :: bb) rs) m
        (LTL_State s f sp pc rs') m
  | ltl_exec_Lreturn: forall s f sp bb rs m m',
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      ltl_corestep (LTL_Block s f (Vptr sp Int.zero) (Lreturn :: bb) rs) m
        (LTL_Returnstate s (sig_res (fn_sig f)) (return_regs (parent_locset s) rs)) m'
  | ltl_exec_function_internal: forall s f rs m m' sp rs',
      Mem.alloc m 0 f.(fn_stacksize) = (m', sp) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      ltl_corestep (LTL_Callstate s (Internal f) rs) m
        (LTL_State s f (Vptr sp Int.zero) f.(fn_entrypoint) rs') m'
(*no external call
  | exec_function_external: forall s ef t args res rs m rs' m',
      args = map rs (loc_arguments (ef_sig ef)) ->
      external_call' ef ge args m t res m' ->
      rs' = Locmap.setlist (map R (loc_result (ef_sig ef))) res rs ->
      ltl_corestep (LTL_Callstate s (External ef) rs m)
         t (LTL_Returnstate s rs' m')*)
  | ltl_exec_return: forall f sp rs1 bb s retty rs m,
      ltl_corestep (LTL_Returnstate (Stackframe f sp rs1 bb :: s) retty rs) m
        (LTL_Block s f sp bb rs) m.

End RELSEM.

Lemma LTL_corestep_not_at_external:
       forall ge m q m' q', ltl_corestep ge q m q' m' -> LTL_at_external q = None.
  Proof. intros. inv H; try reflexivity. Qed.

Definition LTL_halted (q : LTL_core): option val :=
    match q with 
      (*Return Tlong, which must be decoded*)
      | LTL_Returnstate nil (Some Tlong) rs => 
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
      | LTL_Returnstate nil (Some retty) rs => 
           match loc_result (mksignature nil (Some retty)) with
            | nil => None
            | r :: TL => match TL with 
                           | nil => Some (rs (R r))
                           | _ :: _ => None
                         end
           end

      (*Return Tvoid - modeled as integer return*)
      | LTL_Returnstate nil None rs => Some (rs (R AX))

      | _ => None
    end.

(*Original CompCert has this:
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result (mksignature nil (Some Tint)) = r :: nil ->
      rs (R r) = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.
*)

Lemma LTL_corestep_not_halted : forall ge m q m' q', 
       ltl_corestep ge q m q' m' -> LTL_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.
    
Lemma LTL_at_external_halted_excl :
       forall q, LTL_at_external q = None \/ LTL_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma LTL_after_at_external_excl : forall retv q q',
      LTL_after_external retv q = Some q' -> LTL_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl.
         destruct retv; inv H0; simpl; trivial.
  Qed.

Definition check_signature (sig: signature): bool :=
  match sig_args sig, sig_res sig with
     nil, Some ty => match ty with Tint => true | _ => false end
   | _, _ => false
  end.

(*LENB: we do not require argtype=nil and res_type =vint, and
instead create an loc-list containing all agruments*) 
Definition LTL_initial_core (ge:genv) (v: val) (args:list val): option LTL_core :=
   match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                     let tyl := sig_args (funsig f) in
                     if val_has_type_list_func args (sig_args (funsig f))
                        && vals_defined args
                     then Some (LTL_Callstate
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

(*original CompCert has this - do we really need the 
  Int.eq_dec i Int.zero in the above definition (we've got it in Cminor etc)?
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f (Locmap.init Vundef) m0).
*)

Definition LTL_core_sem : CoreSemantics genv LTL_core mem.
  eapply (@Build_CoreSemantics _ _ _ 
       LTL_initial_core
       LTL_at_external
       LTL_after_external
       LTL_halted
       ltl_corestep).
    apply LTL_corestep_not_at_external.
    apply LTL_corestep_not_halted.
    apply LTL_at_external_halted_excl.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma LTL_forward : forall g c m c' m' (CS: ltl_corestep g c m c' m'), 
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

Program Definition LTL_coop_sem : 
  CoopCoreSem genv LTL_core.
apply Build_CoopCoreSem with (coopsem := LTL_core_sem).
  apply LTL_forward.
Defined.

