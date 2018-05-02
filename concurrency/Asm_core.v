Require Import VST.sepcomp.semantics.
Require Import compcert.lib.Coqlib.
(* Require Import VST.sepcomp.simulations. *)
Require Import ZArith List.
Import ListNotations.
(*Require Import veric.base. *)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.common.Events.
Require Import compcert.x86.Asm.
Require Import Values.
Import AST.

(*To prove memsem*)
Require Import VST.concurrency.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.I64Helpers.
Require Import VST.concurrency.BuiltinEffects.

Definition cl_halted (c: regset) : option val := None.

Definition empty_function : function := 
  mkfunction (mksignature nil None cc_default) nil.

Definition get_extcall_arg (inout: Locations.slot) (rs: regset) (m: mem) (l: Locations.loc) : option val :=
 match l with
  | Locations.R r => Some (rs (preg_of r))
  | Locations.S inout ofs ty => 
      let bofs := (Stacklayout.fe_ofs_arg + 4 * ofs)%Z  in
      Mem.loadv (chunk_of_type ty) m
                (Val.add (rs (IR RSP)) (Vint (Int.repr bofs)))
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

Inductive builtin_event: external_function -> mem -> list val -> list mem_event -> Prop :=
  BE_malloc: forall m n m'' b m'
         (ALLOC: Mem.alloc m (-size_chunk Mptr) (Ptrofs.unsigned n) = (m'', b))
         (ALGN : (align_chunk Mptr | (-size_chunk Mptr)))
         (ST: Mem.storebytes m'' b (-size_chunk Mptr) (encode_val Mptr (Vptrofs n)) = Some m'),
         builtin_event EF_malloc m [Vptrofs n]
               [Alloc b (-size_chunk Mptr) (Ptrofs.unsigned n);
                Write b (-size_chunk Mptr) (encode_val Mptr (Vptrofs n))]
| BE_free: forall m b lo bytes sz m'
        (POS: Ptrofs.unsigned sz > 0)
        (LB : Mem.loadbytes m b (Ptrofs.unsigned lo - size_chunk Mptr) (size_chunk Mptr) = Some bytes)
        (FR: Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m')
        (ALGN : (align_chunk Mptr | Ptrofs.unsigned lo - size_chunk Mptr))
        (SZ : Vptrofs sz = decode_val Mptr bytes),
        builtin_event EF_free m [Vptr b lo]
              [Read b (Ptrofs.unsigned lo - size_chunk Mptr) (size_chunk Mptr) bytes;
               Free [(b,Ptrofs.unsigned lo - size_chunk Mptr, Ptrofs.unsigned lo + Ptrofs.unsigned sz)]]
| BE_memcpy: forall m al bsrc bdst sz bytes osrc odst m'
        (AL: al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
        (POS : sz >= 0)
        (DIV : (al | sz))
        (OSRC : sz > 0 -> (al | Ptrofs.unsigned osrc))
        (ODST: sz > 0 -> (al | Ptrofs.unsigned odst))
        (RNG: bsrc <> bdst \/
                Ptrofs.unsigned osrc = Ptrofs.unsigned odst \/
                Ptrofs.unsigned osrc + sz <= Ptrofs.unsigned odst \/ Ptrofs.unsigned odst + sz <= Ptrofs.unsigned osrc)
        (LB: Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m'),
        builtin_event (EF_memcpy sz al) m [Vptr bdst odst; Vptr bsrc osrc]
              [Read bsrc (Ptrofs.unsigned osrc) sz bytes;
               Write bdst (Ptrofs.unsigned odst) bytes]
| BE_EFexternal: forall name sg m vargs,
        I64Helpers.is_I64_helperS name sg ->
         builtin_event (EF_external name sg) m vargs []
| BE_EFbuiltin: forall name sg m vargs, is_I64_builtinS name sg ->
         builtin_event (EF_builtin name sg) m vargs [].

Lemma Vptrofs_inj : forall o1 o2, Vptrofs o1 = Vptrofs o2 ->
  Ptrofs.unsigned o1 = Ptrofs.unsigned o2.
Proof.
  unfold Vptrofs; intros.
  pose proof (Ptrofs.unsigned_range o1); pose proof (Ptrofs.unsigned_range o2).
  destruct Archi.ptr64 eqn: H64.
  - assert (Int64.unsigned (Ptrofs.to_int64 o1) = Int64.unsigned (Ptrofs.to_int64 o2)) by congruence.
    unfold Ptrofs.to_int64 in *.
    rewrite Ptrofs.modulus_eq64 in * by auto.
    rewrite !Int64.unsigned_repr in * by (unfold Int64.max_unsigned; omega); auto.
  - assert (Int.unsigned (Ptrofs.to_int o1) = Int.unsigned (Ptrofs.to_int o2)) by congruence.
    unfold Ptrofs.to_int in *.
    rewrite Ptrofs.modulus_eq32 in * by auto.
    rewrite !Int.unsigned_repr in * by (unfold Int.max_unsigned; omega); auto.
Qed.

Lemma builtin_event_determ ef m vargs T1 (BE1: builtin_event ef m vargs T1) T2 (BE2: builtin_event ef m vargs T2): T1=T2.
inversion BE1; inv BE2; try discriminate; simpl in *; trivial.
+ assert (Vptrofs n0 = Vptrofs n) as H by congruence.
  rewrite H; rewrite (Vptrofs_inj _ _ H) in *.
  rewrite ALLOC0 in ALLOC; inv ALLOC; trivial.
+ inv H5.
  rewrite LB0 in LB; inv LB. rewrite <- SZ in SZ0. rewrite (Vptrofs_inj _ _ SZ0); trivial.
+ inv H3; inv H5.
  rewrite LB0 in LB; inv LB; trivial.
Qed.

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

Inductive cl_initial_core (ge: genv) (m: mem) (rs0: regset) (v: val) (args: list val) : Prop :=
 INIT_CORE : forall f b,
      v = Vptr b (Ptrofs.zero) ->
      rs0 = (Pregmap.init Vundef)
            # PC <- (Vptr b Ptrofs.zero) 
            # RA <- Vzero
            # RSP <- Vnullptr ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      extcall_arguments rs0 m (fn_sig f) args ->
      cl_initial_core ge m rs0 v args.

Definition cl_at_external  (ge: genv) (rs: regset) (m: mem) : option (external_function * signature * list val) :=
  match rs PC with
  | Vptr b i => if Ptrofs.eq_dec i Ptrofs.zero then
    match  Genv.find_funct_ptr ge b with
    | Some (External ef) =>
     match ef with
     | EF_external _ _ => 
      match get_extcall_arguments Locations.Outgoing rs m
                 (Conventions1.loc_arguments (ef_sig ef)) with
      | Some args => Some (ef, ef_sig ef, args)
      | None => None
     end
    | _ => None
   end
   | _ => None
   end
   else None
  | _ => None
end.

Definition cl_after_external  (ge: genv) (vret: option val) (rs: regset) : option regset :=
  match rs PC with
  | Vptr b i => if Ptrofs.eq_dec i Ptrofs.zero then
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

Inductive cl_step ge: regset -> mem -> regset -> mem -> Prop :=
  | cl_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      cl_step ge rs m rs' m'
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      builtin_event ef m vargs t ->
      ev_elim m t m' ->
      external_call ef ge vargs m nil vres m' ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs)) ->
      cl_step ge rs m rs' m'.

Lemma cl_corestep_not_at_external:
  forall ge m q m' q', 
          cl_step ge q m q' m' -> cl_at_external ge q m = None.
Proof.
  intros.
  unfold cl_at_external. 
  inv H.
 *
   rewrite H0.
  destruct (Ptrofs.eq_dec ofs Ptrofs.zero); auto.
  unfold Asm.fundef. rewrite H1. auto.
 *
  rewrite H0.
  destruct (Ptrofs.eq_dec ofs Ptrofs.zero); auto.
  unfold Asm.fundef. rewrite H1. auto.
Qed.

Lemma cl_corestep_not_halted :
  forall ge m q m' q', cl_step ge q m q' m' -> cl_halted q = None.
Proof.
  intros.
  simpl; auto.
Qed.

Program Definition cl_core_sem (ge : genv) :
  @CoreSemantics genv regset mem :=
  @Build_CoreSemantics _ _ _
    (fun _ => cl_initial_core ge)
    (cl_at_external ge)
    (fun v q m => cl_after_external ge v q)
    (fun _ _ => False)
    cl_step
    _
    cl_corestep_not_at_external.
Next Obligation.
Proof.
Admitted.

Section ASM_MEMSEM.

Lemma exec_load_mem_step ge ch m a rs rd rs' m': forall
      (EI: exec_load ge ch m a rs rd = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_load in EI.
  remember (Mem.loadv ch m (eval_addrmode ge a rs) ).
  symmetry in Heqo; destruct o; inversion EI; clear EI; subst. apply mem_step_refl.
Qed.

Lemma exec_store_mem_step ge ch m a rs rs0 vals rs' m': forall
      (ES: exec_store ge ch m a rs rs0 vals = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_store in ES.
  remember (Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)).
  symmetry in Heqo; destruct o; inversion ES; clear ES; subst.
  remember (eval_addrmode ge a rs). destruct v; inversion Heqo; clear Heqo; subst.
  eapply mem_step_store; eassumption.
Qed.

Lemma goto_label_mem_same c0 l rs m rs' m': forall
      (G: goto_label c0 l rs m = Next rs' m'), m=m'.
Proof. intros.
   unfold goto_label in G.
   destruct (label_pos l 0 (fn_code c0)); inversion G; clear G; subst.
   destruct (rs PC); inversion H0; clear H0; subst. auto.
Qed.

Lemma goto_label_mem_step c0 l rs m rs' m': forall
      (G: goto_label c0 l rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
  apply goto_label_mem_same in G. subst; apply mem_step_refl.
Qed.

Lemma exec_instr_mem_step ge c i rs m rs' m': forall
      (EI: exec_instr ge c i rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
   destruct i; simpl in *; inversion EI; clear EI; subst; try apply mem_step_refl;
   try (eapply exec_load_mem_step; eassumption);
   try (eapply exec_store_mem_step; eassumption).

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int.divmodu2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int64.divmodu2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int.divmods2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int64.divmods2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (eval_testcond c0 rs); inversion H0; clear H0; subst.
   destruct b; inversion H1; clear H1; subst; apply mem_step_refl.
   apply mem_step_refl.

   eapply goto_label_mem_step; eassumption.

   destruct (eval_testcond c0 rs); inversion H0; clear H0; subst.
   destruct b; inversion H1; clear H1; subst.
   eapply goto_label_mem_step; eassumption.
   apply mem_step_refl.

   destruct (eval_testcond c1 rs); inversion H0; clear H0; subst.
   destruct b.
     destruct (eval_testcond c2 rs); inversion H1; clear H1; subst.
     destruct b; inversion H0; clear H0; subst.
     eapply goto_label_mem_step; eassumption.
   apply mem_step_refl.

     destruct (eval_testcond c2 rs); inversion H1; clear H1; subst.
     apply mem_step_refl.
     destruct (rs r); inversion H0; clear H0; subst.
     destruct (list_nth_z tbl (Int.unsigned i)); inversion H1; clear H1; subst.
     eapply goto_label_mem_step; eassumption.
  remember (Mem.alloc m 0 sz) as d; apply eq_sym in Heqd.
    destruct d; inv H0.
    remember (Mem.store Mptr m0 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_link))
         (rs RSP)) as q.
    apply eq_sym in Heqq; destruct q; inversion H1; clear H1; subst.
    remember (Mem.store Mptr m1 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_ra))
         (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply mem_step_trans.
      eapply mem_step_alloc; eassumption.
    eapply mem_step_trans.
      eapply mem_step_store; eassumption.
      eapply mem_step_store; eassumption.
  destruct (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_ra)); inv H0.
    destruct (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_link)); inv H1.
    destruct (rs RSP); inv H0.
    remember (Mem.free m b 0 sz) as t.
    destruct t; inv H1; apply eq_sym in Heqt.
    eapply mem_step_free; eassumption.
Qed.

Lemma ev_elim_mem_step: forall t m m', ev_elim m t m' -> mem_step m m'.
Proof.
induction t; simpl; intros.
subst. apply mem_step_refl.
destruct a.
destruct H as [m'' [? ?]].
eapply mem_step_trans; [ | eauto].
eapply mem_step_storebytes; eauto.
destruct H as [? ?].
eapply mem_step_trans; [ | eauto].
apply mem_step_refl.
destruct H as [m'' [? ?]].
eapply mem_step_trans; [ | eauto].
eapply mem_step_alloc; eauto.
destruct H as [m'' [? ?]].
eapply mem_step_trans; [ | eauto].
eapply mem_step_freelist; eauto.
Qed.

Lemma asm_mem_step : forall ge c m c' m' (CS: corestep (cl_core_sem ge) ge c m c' m'), mem_step m m'.
Proof. intros.
  inv CS; simpl in *; try apply mem_step_refl; try contradiction.
 inv H0.
 + eapply exec_instr_mem_step; try eassumption.
 + eapply ev_elim_mem_step; eauto.
Qed.

Lemma ple_exec_load:
    forall g ch m a rs rd rs' m'
       m1 (PLE: perm_lesseq m m1),
       exec_load g ch m a rs rd = Next rs' m' ->
       m'=m /\ exec_load g ch m1 a rs rd = Next rs' m1.
Proof.
  intros.
  unfold exec_load in *.
  destruct (Mem.loadv ch m (eval_addrmode g a rs)) eqn:?; inv H.
  split; auto.
  eapply ple_load in Heqo; eauto. rewrite Heqo. auto.
Qed.

Lemma ple_exec_store:
  forall g ch m a rs rs0 rsx rs' m' m1
   (PLE: perm_lesseq m m1),
   exec_store g ch m a rs rs0 rsx = Next rs' m' ->
  exists m1',
    perm_lesseq m' m1' /\ exec_store g ch m1 a rs rs0 rsx = Next rs' m1'.
Proof.
intros.
 unfold exec_store in *.
 destruct (Mem.storev ch m (eval_addrmode g a rs) (rs rs0)) eqn:?; inv H.
 destruct (ple_store _ _ _ _ _ _ PLE Heqo) as [m1' [? ?]].
 exists m1'; split; auto.
 rewrite H0. auto.
Qed.

Lemma asm_inc_perm: forall (g : genv) c m c' m'
      (CS:corestep (cl_core_sem g) g c m c' m')
      m1 (PLE: perm_lesseq m m1),
      exists m1', corestep (cl_core_sem g) g c m1 c' m1' /\ perm_lesseq m' m1'.
Proof.
intros; inv CS; simpl in *; try contradiction.
inv H0.
 destruct i; simpl in *; inv H2;
     try solve [
      exists m1; split; trivial; econstructor; try eassumption; reflexivity
     | destruct (ple_exec_load _ _ _ _ _ _ _ _ _ PLE H3); subst m';
        exists m1; split;  simpl; auto; econstructor; eassumption
     | destruct (ple_exec_store _ _ _ _ _ _ _ _ _ _ PLE H3) as [m1' [? ?]];
        exists m1'; split; auto; econstructor; eassumption
    |  exists m1; split; auto; [ econstructor; try eassumption; simpl | ];
       repeat match type of H3 with match ?A with Some _ => _ | None => _ end = _ =>
         destruct A; try now inv H3 end;
       eassumption
    ].
 - (* Pcmp_rr case fails! *)
(*+ exists m1; split; trivial. econstructor; try eassumption. ad_it.
+ ad_it.
*)
Abort.

Program Definition Asm_mem_sem (ge : genv) : @MemSem genv regset.
Proof.
apply Build_MemSem with (csem := cl_core_sem ge).
  apply (asm_mem_step).
Defined.

Lemma exec_instr_forward g c i rs m rs' m': forall
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_forward m m'.
Proof. intros.
    apply mem_forward_preserve.
    eapply exec_instr_mem_step; eassumption.
Qed.

End ASM_MEMSEM.

(*Require Import VST.concurrency.load_frame.
Lemma load_frame_store_args_rec_nextblock:
  forall args m m2 stk ofs tys
    (Hload_frame: store_args_rec m stk ofs args tys = Some m2),
    Mem.nextblock m2 = Mem.nextblock m.
Proof.
  intro args.
  induction args; intros; simpl in *.
  destruct tys; inv Hload_frame; auto.
  destruct tys; try discriminate;
  destruct t;
  repeat match goal with
         | [H: match ?Expr with _ => _ end = _ |- _] =>
           destruct Expr eqn:?; try discriminate;
             unfold load_frame.store_stack in *
         | [H: Mem.storev _ _ _ _ = _ |- _] =>
           eapply nextblock_storev in H
         | [H: ?Expr = ?Expr2 |- context[?Expr2]] =>
           rewrite <- H
         end;
  eauto.
Qed.

Lemma load_frame_store_nextblock:
  forall m m2 stk args tys
    (Hload_frame: store_args m stk args tys = Some m2),
    Mem.nextblock m2 = Mem.nextblock m.
Proof.
  intros.
  unfold load_frame.store_args in *.
  eapply load_frame_store_args_rec_nextblock; eauto.
Qed.*)

