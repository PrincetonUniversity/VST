Require Import sepcomp.semantics.
(* Require Import sepcomp.simulations. *)
Require Import ZArith List.
Import ListNotations.
(*Require Import veric.base. *)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.common.Events.
Require Import compcert.ia32.Asm.
Require Import Values.
Import AST.

(*To prove memsem*)
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.mem_lemmas.

Definition cl_halted (c: regset) : option val := None.

Definition empty_function : function := 
  mkfunction (mksignature nil None cc_default) nil.
Check Locations.Outgoing.

Definition get_extcall_arg (inout: Locations.slot) (rs: regset) (m: mem) (l: Locations.loc) : option val :=
 match l with
  | Locations.R r => Some (rs (preg_of r))
  | Locations.S inout ofs ty => 
      let bofs := (Stacklayout.fe_ofs_arg + 4 * ofs)%Z  in
      Mem.loadv (chunk_of_type ty) m
                (Val.add (rs (IR ESP)) (Vint (Int.repr bofs)))
  end.

Fixpoint get_extcall_arguments
    (inout: Locations.slot) (rs: regset) (m: mem) (al: list (rpair Locations.loc)) : option (list val) :=
  match al with
  | One l :: al' => 
     match get_extcall_arg inout rs m l with
     | Some v => match get_extcall_arguments inout rs m al' with
                         | Some vl => Some (v::vl)
                         | None => None
                        end
     | None => None
    end
  | Twolong hi lo :: al' =>
     match get_extcall_arg inout rs m hi with
     | Some vhi => 
       match get_extcall_arg inout rs m lo with
       | Some vlo => 
        match get_extcall_arguments inout rs m al' with
                         | Some vl => Some (Val.longofwords vhi vlo :: vl)
                         | None => None
        end
        | None => None
      end
     | None => None
    end
  | nil => Some nil
 end.

Definition funsig (fd: Asm.fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Fixpoint store_arguments (tys: list typ) (args: list val) (loc: val) (m: mem): option mem :=
 match tys, args with
 | Tlong::tys', a::args' => None
 | ty::tys', a::args' =>
    match Mem.storev (chunk_of_type ty) m loc a with
    | Some m' => store_arguments tys' args' (Val.add loc (Vint (Int.repr (typesize ty)))) m'
    | None => None
    end
 | nil, nil => Some m
 | _, _ => None
 end.

Definition cl_initial_core (ge: genv) (m: mem) (v: val) (args: list val) : option (regset * option mem) :=
  match v with
  | Vptr b i =>  if Int.eq_dec i Int.zero then
    match  Genv.find_funct_ptr ge b with
    | Some f =>
       let fsig := funsig f in
       let (m', stk) := Mem.alloc m 0 (Conventions1.size_arguments fsig) in
       match store_arguments fsig.(sig_args) args (Vptr stk Int.zero) m with
        | Some m'' => 
           Some ( (Pregmap.init Vundef)
                      # PC <- v
                      # ESP <- (Vptr stk Int.zero)
                      # RA <- Vzero,
                      Some m'')
        | _ => None
       end
     | _ => None
   end else None
   | _ => None
  end.


Definition cl_at_external  (ge: genv) (rs: regset) (m: mem) : option (external_function * list val) :=
  match rs PC with
(*  | CC_core_Callstate (External ef _ _ _) args _ => Some (ef, args)*)
  | Vptr b i => if Int.eq_dec i Int.zero then
    match  Genv.find_funct_ptr ge b with
    | Some (External ef) =>
     match get_extcall_arguments Locations.Outgoing rs m
                 (Conventions1.loc_arguments (ef_sig ef)) with
     | Some args => Some (ef, args)
     | None => None
    end
   | _ => None
   end
   else None
  | _ => None
end.

Definition cl_after_external  (ge: genv) (vret: option val) (rs: regset) : option regset :=
  match rs PC with
  | Vptr b i => if Int.eq_dec i Int.zero then
    match  Genv.find_funct_ptr ge b with
    | Some (External ef) =>
      match vret with
      | Some res => 
          Some ((set_pair (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA))
      | None => 
          Some ( rs #PC <- (rs RA))
     end
    | _ => None
   end
   else None
 | _ => None
 end.

Definition cl_step ge (q: regset) (m: mem) (q': regset) (m': mem) : Prop :=
    cl_at_external ge q m = None /\ 
     Asm.step ge (State q m) Events.E0 (State q' m').

Lemma cl_corestep_not_at_external:
  forall ge m q m' q', 
          cl_step ge q m q' m' -> cl_at_external ge q m = None.
Proof.
  intros.
  unfold cl_step in H. destruct H; auto.  
Qed.

Lemma cl_corestep_not_halted :
  forall ge m q m' q', cl_step ge q m q' m' -> cl_halted q = None.
Proof.
  intros.
  simpl; auto.
Qed.

Program Definition cl_core_sem :
  @CoreSemantics genv regset mem :=
  @Build_CoreSemantics _ _ _
    (*deprecated cl_init_mem*)
    (fun _ => cl_initial_core)
    cl_at_external
    cl_after_external
    cl_halted
    cl_step
    cl_corestep_not_at_external
    cl_corestep_not_halted _.
