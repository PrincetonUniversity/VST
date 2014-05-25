Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.

Require Import Asm. 

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.
Require Import compcomp.val_casted.

Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Section RELSEM.
Variable ge: genv.

Inductive state: Type :=
  | State: regset -> state
  | ExtCallState: external_function -> list val -> regset -> state.

Inductive asm_step: state -> mem -> state -> mem -> Prop :=
  | asm_exec_step_internal:
      forall b ofs c i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some i ->
      exec_instr ge c i rs m = Next rs' m' ->
      asm_step (State rs) m (State rs') m'
  | asm_exec_step_builtin:
      forall b ofs c ef args res rs m t vl rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pbuiltin ef args res) ->
      external_call' ef ge (map rs args) m t vl m' ->
      rs' = nextinstr_nf 
             (set_regs res vl
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_step (State rs) m (State rs') m'
(*WE DON'T SUPPORT  ANNOTS YET
  | asm_exec_step_annot:
      forall b ofs c ef args rs m vargs t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pannot ef args) ->
      annot_arguments rs m args vargs ->
      external_call' ef ge vargs m t v m' ->
      asm_step (State rs) m (State (nextinstr rs)) m'*)
  | asm_exec_step_external:
      forall b ef args rs m,
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_step (State rs) m (ExtCallState ef args rs) m
(*NO REEAL EXTERNAL STEPS
  | asm_exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      external_call' ef ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig ef)) res rs) #PC <- (rs RA) ->
      asm_step (State rs) m (State rs') m'*).

End RELSEM.

Definition Asm_at_external (c: state):
          option (external_function * signature * list val) :=
  match c with
    ExtCallState ef args rs => Some(ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) args)
  | _ => None
  end.

Definition Asm_after_external (vret: option val)(c: state) : option state :=
  match c with 
    ExtCallState ef args rs => 
      match vret with
         None => Some (State ((set_regs (loc_external_result (ef_sig ef)) 
                               (encode_long (sig_res (ef_sig ef)) Vundef) rs) #PC <- (rs RA)))
       | Some res => Some (State ((set_regs (loc_external_result (ef_sig ef)) 
                               (encode_long (sig_res (ef_sig ef)) res) rs) #PC <- (rs RA))) 
      end
  | _ => None
  end.

Definition Asm_initial_core (ge:genv) (v: val) (args:list val): 
           option state :=
  match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                     if (*Lenb: which signature should we take here?
                          val_has_type_list_func args (sig_args fi))
                        &&*)  vals_defined args
                     then Some (State 
                               ((Pregmap.init Vundef)
                                    # PC <- (Vptr b Int.zero) (*lenb: is this use of f correct here?*)
                                    # RA <- Vzero
                                    # ESP <- Vzero))
                     else None
                   | External _ => None
                   end
               end
          else None
     | _ => None
    end.
(*COMPCERT:
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (symbol_offset ge p.(prog_main) Int.zero)
        # RA <- Vzero
        # ESP <- Vzero in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vzero ->
      rs#EAX = Vint r ->
      final_state (State rs m) r.
*)

Definition Asm_halted (q : state): option val :=
    (*What fundef should we use here to check whether return type is long???*)
    match q with
      State rs => if Val.cmp_bool Ceq (rs#PC) Vzero 
                  then Some(rs#EAX) (*no check for integer return value*)
                  else None
    | _ => None
    end.

Section ASM_CORESEM.
Lemma Asm_at_external_halted_excl :
       forall q, Asm_at_external q = None \/ Asm_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma Asm_after_at_external_excl : forall retv q q',
      Asm_after_external retv q = Some q' -> Asm_at_external q' = None.
  Proof. intros.
    destruct q; simpl in *; try inv H.
    destruct retv; inv H1; simpl; trivial.
  Qed.

Lemma Asm_corestep_not_at_external:
       forall ge m q m' q', asm_step ge q m q' m' -> 
              Asm_at_external q = None.
  Proof. intros. inv H; try reflexivity. Qed.

Lemma Asm_corestep_not_halted : forall ge m q m' q', 
       asm_step ge q m q' m' -> 
       Asm_halted q = None.
  Proof. intros. inv H; simpl in *.
    rewrite H0; simpl. trivial. 
    rewrite H0; simpl. trivial.
    rewrite H0; simpl. trivial.
  Qed.
 
Definition Asm_core_sem : CoreSemantics genv state mem.
  eapply (@Build_CoreSemantics _ _ _ 
            Asm_initial_core
            Asm_at_external
            Asm_after_external
            Asm_halted
            asm_step).
    apply Asm_corestep_not_at_external.
    apply Asm_corestep_not_halted.
    apply Asm_at_external_halted_excl.
Defined.
End ASM_CORESEM.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Section ASM_COOPSEM.

Lemma exec_load_forward: forall g chunk m a rs rd rs' m',
   exec_load g chunk m a rs rd = Next rs' m' ->
   mem_forward m m'.
Proof. intros. unfold exec_load in H.
  remember (Mem.loadv chunk m (eval_addrmode g a rs)) as d.
  destruct d; inv H. apply  mem_forward_refl.
Qed.

Lemma exec_store_forward: forall g chunk m a rs rs1 pregs rs' m',
  exec_store g chunk m a rs rs1 pregs = Next rs' m' ->
  mem_forward m m'.
Proof. intros. unfold exec_store in H.
  remember (Mem.storev chunk m (eval_addrmode g a rs) (rs rs1)) as d.
  destruct d; inv H.
  remember (eval_addrmode g a rs) as addr.
  destruct addr; simpl in *; inv Heqd.
  apply eq_sym in H0. eapply store_forward; eassumption.
Qed.

Lemma goto_label_forward: forall c0 l rs m rs' m',
      goto_label c0 l rs m = Next rs' m' -> mem_forward m m'.
Proof. intros.
   unfold goto_label in H. 
   destruct (label_pos l 0 c0); inv H.
   destruct (rs PC); inv H1. 
   apply mem_forward_refl.
Qed.

Lemma exec_instr_forward g c i rs m rs' m': forall 
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_forward m m'.
Proof. intros.
   destruct i; simpl in *; inv EI; try apply mem_forward_refl;
   try (eapply exec_load_forward; eassumption);
   try (eapply exec_store_forward; eassumption).

   destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply mem_forward_refl.

   destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply mem_forward_refl.

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1; apply mem_forward_refl.
   apply mem_forward_refl.

   eapply goto_label_forward; eassumption. 

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1.
   eapply goto_label_forward; eassumption. 
   apply mem_forward_refl.

   destruct (eval_testcond c1 rs); inv H0.
   destruct b. 
     destruct (eval_testcond c2 rs); inv H1.
     destruct b; inv H0. 
     eapply goto_label_forward; eassumption.
     apply mem_forward_refl.

     destruct (eval_testcond c2 rs); inv H1.
     apply mem_forward_refl.
     destruct (rs r); inv H0.
     destruct (list_nth_z tbl (Int.unsigned i)); inv H1. 
     eapply goto_label_forward; eassumption.
  remember (Mem.alloc m 0 sz) as d; apply eq_sym in Heqd.
    destruct d; inv H0.
    remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as q.
    apply eq_sym in Heqq; destruct q; inv H1.
    remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply mem_forward_trans.
      eapply alloc_forward; eassumption. 
    eapply mem_forward_trans.
      eapply store_forward; eassumption. 
      eapply store_forward; eassumption.
  destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))); inv H0.  
    destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))); inv H1.  
    destruct (rs ESP); inv H0.
    remember (Mem.free m b 0 sz) as t.
    destruct t; inv H1; apply eq_sym in Heqt. 
    eapply free_forward; eassumption. 
Qed.

Lemma Asm_forward : forall g c m c' m'
         (CS: asm_step g c m c' m'), 
         mem_forward m m'.
  Proof. intros.
   inv CS; try apply mem_forward_refl. clear - H2.
   eapply exec_instr_forward; eassumption.
   inv H2. eapply external_call_mem_forward; eassumption.
Qed.
   
Program Definition Asm_coop_sem : 
  CoopCoreSem genv state.
apply Build_CoopCoreSem with (coopsem := Asm_core_sem).
  apply Asm_forward.
Defined.

End ASM_COOPSEM.

