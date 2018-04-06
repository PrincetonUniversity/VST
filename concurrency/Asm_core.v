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
Require Import compcert.ia32.Asm.
Require Import Values.
Import AST.

(*To prove memsem*)
Require Import VST.sepcomp.semantics.
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

Inductive builtin_event: external_function -> mem -> list val -> list mem_event -> Prop :=
  BE_malloc: forall m n m'' b m'
         (ALLOC: Mem.alloc m (-4) (Int.unsigned n) = (m'', b))
         (ALGN : (align_chunk Mint32 | (-4)))
         (ST: Mem.storebytes m'' b (-4) (encode_val Mint32 (Vint n)) = Some m'),
         builtin_event EF_malloc m [Vint n]
               [Alloc b (-4) (Int.unsigned n); Write b (-4) (encode_val Mint32 (Vint n))]
| BE_free: forall m b lo bytes sz m'
        (POS: Int.unsigned sz > 0)
        (LB : Mem.loadbytes m b (Int.unsigned lo - 4) (size_chunk Mint32) = Some bytes)
        (FR: Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) = Some m')
        (ALGN : (align_chunk Mint32 | Int.unsigned lo - 4))
        (SZ : Vint sz = decode_val Mint32 bytes),
        builtin_event EF_free m [Vptr b lo]
              [Read b (Int.unsigned lo - 4) (size_chunk Mint32) bytes;
               Free [(b,Int.unsigned lo - 4, Int.unsigned lo + Int.unsigned sz)]]
| BE_memcpy: forall m al bsrc bdst sz bytes osrc odst m'
        (AL: al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
        (POS : sz >= 0)
        (DIV : (al | sz))
        (OSRC : sz > 0 -> (al | Int.unsigned osrc))
        (ODST: sz > 0 -> (al | Int.unsigned odst))
        (RNG: bsrc <> bdst \/
                Int.unsigned osrc = Int.unsigned odst \/
                Int.unsigned osrc + sz <= Int.unsigned odst \/ Int.unsigned odst + sz <= Int.unsigned osrc)
        (LB: Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m'),
        builtin_event (EF_memcpy sz al) m [Vptr bdst odst; Vptr bsrc osrc]
              [Read bsrc (Int.unsigned osrc) sz bytes;
               Write bdst (Int.unsigned odst) bytes]
| BE_EFexternal: forall name sg m vargs,
        I64Helpers.is_I64_helperS name sg ->
         builtin_event (EF_external name sg) m vargs []
| BE_EFbuiltin: forall name sg m vargs, is_I64_builtinS name sg ->
         builtin_event (EF_builtin name sg) m vargs [].

Lemma builtin_event_determ ef m vargs T1 (BE1: builtin_event ef m vargs T1) T2 (BE2: builtin_event ef m vargs T2): T1=T2.
inv BE1; inv BE2; simpl in *; trivial.
+ rewrite ALLOC0 in ALLOC; inv ALLOC; trivial.
+ rewrite LB0 in LB; inv LB. rewrite <- SZ in SZ0; inv SZ0. trivial.
+ rewrite LB0 in LB; inv LB; trivial.
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

Definition cl_initial_core (ge: genv) (m: mem) (v: val) (args: list val) : option (regset * option mem) :=
  match v with
  | Vptr b i =>  if Int.eq_dec i Int.zero then
    match  Genv.find_funct_ptr ge b with
    | Some f =>
       let fsig := funsig f in
       let (m', stk) := Mem.alloc m 0 (Conventions1.size_arguments fsig) in
       match store_arguments fsig.(sig_args) args (Vptr stk Int.zero) m' with
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
  | Vptr b i => if Int.eq_dec i Int.zero then
    match  Genv.find_funct_ptr ge b with
    | Some (External ef) =>
     match ef with
     | EF_external _ _ => 
      match get_extcall_arguments Locations.Outgoing rs m
                 (Conventions1.loc_arguments (ef_sig ef)) with
      | Some args => Some (ef, args)
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

Inductive cl_step ge: regset -> mem -> regset -> mem -> Prop :=
  | cl_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      cl_step ge rs m rs' m'
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      builtin_event ef m vargs t ->
      ev_elim m t m' ->
      external_call ef ge vargs m nil vres m' ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (backend.Machregs.destroyed_by_builtin ef)) rs)) ->
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
  destruct (Int.eq_dec ofs Int.zero); auto.
  unfold Asm.fundef. rewrite H1. auto.
 *
  rewrite H0.
  destruct (Int.eq_dec ofs Int.zero); auto.
  unfold Asm.fundef. rewrite H1. auto.
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

   destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inversion H0; clear H0; subst.
   destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inversion H1; clear H1; subst.
   apply mem_step_refl.

   destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inversion H0; clear H0; subst.
   destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inversion H1; clear H1; subst.
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
    remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link))
         (rs ESP)) as q.
    apply eq_sym in Heqq; destruct q; inversion H1; clear H1; subst.
    remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply mem_step_trans.
      eapply mem_step_alloc; eassumption.
    eapply mem_step_trans.
      eapply mem_step_store; eassumption.
      eapply mem_step_store; eassumption.
  destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))); inv H0.
    destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))); inv H1.
    destruct (rs ESP); inv H0.
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

Lemma asm_mem_step : forall ge c m c' m' (CS: corestep cl_core_sem ge c m c' m'), mem_step m m'.
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
      (CS:corestep cl_core_sem g c m c' m')
      m1 (PLE: perm_lesseq m m1),
      exists m1', corestep cl_core_sem g c m1 c' m1' /\ perm_lesseq m' m1'.
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

Program Definition Asm_mem_sem : @MemSem genv regset.
Proof.
apply Build_MemSem with (csem := cl_core_sem).
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

Require Import VST.concurrency.load_frame.
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
Qed.

