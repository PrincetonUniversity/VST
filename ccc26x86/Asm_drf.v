Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import ccc26x86.Locations.
(*Require Import Stacklayout.*)
Require Import ccc26x86.Conventions.

Require Import ccc26x86.Asm.
(*LENB: In CompComp, we used a modified Asm.v, called Asm.comp.v*)

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.val_casted.
Require Import ccc26x86.BuiltinEffects.
Require Import ccc26x86.load_frame.
Require Import sepcomp.drf_semantics.
Require Import ccc26x86.Asm_coop.

Require Import List. Import ListNotations.
(*
Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
    load_frame.
*)

Section ASM_EV.
Variable hf : I64Helpers.helper_functions.

Definition drf_instr (ge:genv) (c: code) (i: instruction) (rs: regset) (m: mem) 
           : option (list mem_event)  :=
  match i with
  | Pfstps_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat32 (rs ST0))]
                  | _ => None
                 end
  | Pfstpl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat64 (rs ST0))]
                  | _ => None
                 end
  | Pmovss_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat32 (rs r1))]
                  | _ => None
                 end
  | Pmov_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mint32 (rs r1))]
                  | _ => None
                 end
  | Pmov_mr_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Many32 (rs r1))]
                  | _ => None
                 end
  | Pmovsd_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat64 (rs r1))]
                  | _ => None
                 end
  | Pmovsd_mf_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs)  (encode_val Many64 (rs r1))]
                  | _ => None
                 end
  | Pmovb_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mint8unsigned (rs r1))]
                  | _ => None
                 end
  | Pmovw_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mint16unsigned (rs r1))]
                  | _ => None
                 end

  | Pmov_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint32) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovsd_fm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat64) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat64) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovss_fm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pfldl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat64) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat64) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pflds_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovzb_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint8unsigned) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint8unsigned) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsb_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint8signed) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint8signed) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovzw_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint16unsigned) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint16unsigned) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsw_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint16signed) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint16signed) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmov_rm_a rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Many32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Many32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsd_fm_a rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Many64) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Many64) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Int.zero in
      match Mem.storev Mint32 m1 (Val.add sp (Vint ofs_link)) rs#ESP with
      | None => None
      | Some m2 =>
          match Mem.storev Mint32 m2 (Val.add sp (Vint ofs_ra)) rs#RA with
          | None => None
          | Some m3 => Some [Alloc stk 0 sz; 
                             Write stk (Int.unsigned ofs_link) (encode_val Mint32 (rs ESP));
                             Write stk (Int.unsigned ofs_ra) (encode_val Mint32 (rs RA))] 
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with
      | None => None
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with
          | None => None
          | Some sp =>
              match rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => None
                  | Some m' => match (Val.add rs#ESP (Vint ofs_ra)), (Val.add rs#ESP (Vint ofs_link)) with
                                Vptr b1 ofs1, Vptr b2 ofs2 =>
                                  match Mem.loadbytes m b1 (Int.unsigned ofs1) (size_chunk Mint32), Mem.loadbytes m b2 (Int.unsigned ofs2) (size_chunk Mint32) 
                                  with Some bytes1, Some bytes2=>
                                     Some [Read b1 (Int.unsigned ofs1) (size_chunk Mint32) bytes1;
                                           Read b2 (Int.unsigned ofs2) (size_chunk Mint32) bytes2;
                                           Free [(stk, 0, sz)]]
                                   | _, _ => None
                                  end
                              | _, _ => None
                              end
                  end
              | _ => None
              end
          end
      end
(*  | Pbuiltin ef args res => EmptyEffect
(*     (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)*)
(*  | Pannot ef args =>
      EmptyEffect *)*)
  | _ => Some [Free nil]
  end. 

Lemma store_stack_ev_elim m sp ty ofs v m' (SS: store_stack m sp ty ofs v = Some m'):
  exists b z, sp =Vptr b z /\
  ev_elim m [Write b (Int.unsigned (Int.add z ofs)) (encode_val (chunk_of_type ty) v)] m'.
Proof. 
  destruct sp; try discriminate. unfold store_stack in SS.
  exists b, i; split; trivial.
  apply Mem.store_storebytes in SS.
  econstructor. split. eassumption. constructor.
Qed.

Fixpoint store_args_ev_rec sp ofs args tys : option (list mem_event) :=
  match tys, args with
    | nil, nil => Some nil
    | ty'::tys',a'::args' => 
      match ty', a' with 
        | Tlong, Vlong n => 
           match store_args_ev_rec sp (ofs+2) args' tys' with
             None => None
           | Some tailEvents =>
               Some ((Write sp (Int.unsigned (Int.repr(Stacklayout.fe_ofs_arg + 4*(ofs+1))))
                              (encode_val (chunk_of_type Tint) (Vint (Int64.hiword n)))) ::
                     (Write sp (Int.unsigned (Int.repr(Stacklayout.fe_ofs_arg + 4*ofs)))
                            (encode_val (chunk_of_type Tint) (Vint (Int64.loword n)))) ::
                     tailEvents)
           end
        | Tlong, _ => None
        | _,_ => 
           match store_args_ev_rec sp (ofs+typesize ty') args' tys' with
             None => None
           | Some tailEvents =>
               Some ((Write sp (Int.unsigned (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs))) (encode_val (chunk_of_type ty') a'))
                      :: tailEvents)
           end 
      end
    | _, _ => None
  end.

Lemma store_args_ev_elim sp: forall args tys ofs m m' (SA: store_args_rec m sp ofs args tys = Some m'),
  exists T, store_args_ev_rec sp ofs args tys = Some T /\ ev_elim m T m'.
Proof.
induction args; intros tys; destruct tys; simpl; intros; try discriminate.
+ inv SA. exists nil. split. trivial. constructor.
+ destruct t.
  - remember (store_stack m (Vptr sp Int.zero) Tint
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA. 
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b [z [B EV]]]; inv B.
    rewrite Int.add_zero_l in EV.
    simpl in EV. destruct EV as [mm [SB MM]]; subst m0.
    eexists; split. reflexivity.
    econstructor. split; eassumption.
  - remember (store_stack m (Vptr sp Int.zero) Tfloat
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA. 
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b [z [B EV]]]; inv B.
    rewrite Int.add_zero_l in EV.
    simpl in EV. destruct EV as [mm [SB MM]]; subst m0.
    eexists; split. reflexivity.
    econstructor. split; eassumption.
  - destruct a; try discriminate.
    remember (store_stack m (Vptr sp Int.zero) Tint
         (Int.repr
            match ofs + 1 with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) (Vint (Int64.hiword i))) as p.
    destruct p; inv SA.
    remember (store_stack m0 (Vptr sp Int.zero) Tint
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) (Vint (Int64.loword i))) as q. 
    destruct q; inv H0.
    destruct (IHargs _ _ _ _ H1) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    symmetry in Heqq. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqq) as [b2 [z2 [B2 EV2]]]; inv B2.
    rewrite Int.add_zero_l in EV2.
    simpl in EV2. destruct EV2 as [mm2 [SB2 MM2]]. subst m1. clear - SB1 SB2 EVT.
    eexists; split. reflexivity.
    econstructor. split. apply SB1.  
    econstructor. split. apply SB2. assumption.
  - remember (store_stack m (Vptr sp Int.zero) Tsingle
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    eexists; split. reflexivity.
    econstructor. split. apply SB1. assumption.
  - remember (store_stack m (Vptr sp Int.zero) Tany32
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    eexists; split. reflexivity.
    econstructor. split. apply SB1. assumption.
  - remember (store_stack m (Vptr sp Int.zero) Tany64
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    eexists; split. reflexivity.
    econstructor. split. apply SB1. assumption.
Qed.

Definition store_args_events sp args tys := store_args_ev_rec sp 0 args tys.

Parameter ExtEvent : external_function-> mem -> list val -> option (list mem_event).
(*Parameter builtin_args_events: val -> mem -> list (builtin_arg preg) -> list val -> option (list mem_event).*)
Parameter call_args_events: (preg -> val) -> mem -> list val -> option (list mem_event).

Section EVAL_BUILTIN_ARG_EV.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_builtin_arg_ev: builtin_arg A -> val -> list mem_event -> Prop :=
  | eval_BA_ev: forall x,
      eval_builtin_arg_ev (BA x) (e x) nil
  | eval_BA_ev_int: forall n,
      eval_builtin_arg_ev (BA_int n) (Vint n) nil
  | eval_BA_ev_long: forall n,
      eval_builtin_arg_ev (BA_long n) (Vlong n) nil
  | eval_BA_ev_float: forall n,
      eval_builtin_arg_ev (BA_float n) (Vfloat n) nil
  | eval_BA_ev_single: forall n,
      eval_builtin_arg_ev (BA_single n) (Vsingle n) nil
  | eval_BA_ev_loadstack: forall chunk ofs v b z,
      Mem.loadv chunk m (Val.add sp (Vint ofs)) = Some v ->
      Val.add sp (Vint ofs) = Vptr b z ->
      eval_builtin_arg_ev (BA_loadstack chunk ofs) v [Read b (Int.unsigned z) (size_chunk chunk) (encode_val chunk v)]
  | eval_BA_ev_addrstack: forall ofs,
      eval_builtin_arg_ev (BA_addrstack ofs) (Val.add sp (Vint ofs)) nil
  | eval_BA_ev_loadglobal: forall chunk id ofs v b z,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      Senv.symbol_address ge id ofs = Vptr b z ->
      eval_builtin_arg_ev (BA_loadglobal chunk id ofs) v [Read b (Int.unsigned z) (size_chunk chunk) (encode_val chunk v)]
  | eval_BA_ev_addrglobal: forall id ofs,
      eval_builtin_arg_ev (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs) nil
  | eval_BA_ev_splitlong: forall hi lo vhi vlo Thi Tlo,
      eval_builtin_arg_ev hi vhi Thi -> eval_builtin_arg_ev lo vlo Tlo->
      eval_builtin_arg_ev (BA_splitlong hi lo) (Val.longofwords vhi vlo) (Thi++Tlo).

Lemma eval_builtin_arg_ev_determ: forall a v1 T1 (HT1:eval_builtin_arg_ev a v1 T1)
      v2 T2 (HT2:eval_builtin_arg_ev a v2 T2), v1=v2 /\ T1=T2.
Proof.
induction a; intros; inv HT1; inv HT2; try solve [split; trivial].
+ rewrite H6 in H4; inv H4. rewrite H2 in H1; inv H1. split; trivial.
+ rewrite H7 in H5; inv H5. rewrite H6 in H4; inv H4. split; trivial.
+ destruct (IHa1 _ _ H2 _ _ H1); subst.
  destruct (IHa2 _ _ H6 _ _ H4); subst. split; trivial.
Qed.

Lemma eval_builtin_arg_event: forall a v, eval_builtin_arg ge e sp m a v -> exists T, eval_builtin_arg_ev a v T.
Proof.
  induction 1; intros; try solve [eexists; econstructor; try eassumption].
+ assert (B: exists b z, sp = Vptr b z). destruct sp; inv H. exists b, i; trivial.
  destruct B as [b [i SP]]. 
  eexists. econstructor. eassumption. subst sp. reflexivity.
+ assert (B: exists b z, (Senv.symbol_address ge id ofs) = Vptr b z). destruct (Senv.symbol_address ge id ofs); inv H. exists b, i; trivial.
  destruct B as [b [i SA]]. 
  eexists. econstructor; eassumption.
+ destruct IHeval_builtin_arg1 as [Thi HThi]. destruct IHeval_builtin_arg2 as [Tlo HTlo].
  eexists. econstructor; eassumption.
Qed.

Inductive eval_builtin_args_ev: list (builtin_arg A) -> list val -> list mem_event -> Prop :=
  eval_builtin_args_ev_nil: eval_builtin_args_ev nil nil nil
| eval_builtin_args_ev_cons: forall a v T1 al vl T2 ,
                         eval_builtin_arg_ev a v T1 ->
                         eval_builtin_args_ev al vl T2 -> 
                         eval_builtin_args_ev (a::al) (v::vl) (T1++T2).

Lemma eval_builtin_args_ev_determ: forall al vl1 T1 (HA1: eval_builtin_args_ev al vl1 T1)
      vl2 T2 (HA2: eval_builtin_args_ev al vl2 T2), vl1=vl2 /\ T1=T2.
Proof.
induction al; intros; inv HA1; inv HA2.
+ split; trivial.
+ destruct (IHal _ _ H6 _ _ H4); subst.
  destruct (eval_builtin_arg_ev_determ  _ _ _ H2 _ _ H1); subst.
  split; trivial.
Qed.

Lemma eval_builtin_args_eval_builtin_args_ev: forall al vl, eval_builtin_args ge e sp m al vl ->
  exists T, eval_builtin_args_ev al vl T.
Proof.
  induction 1.
+ eexists; econstructor.
+ destruct IHlist_forall2 as [T2 HT2].
  destruct (eval_builtin_arg_event _ _ H) as [T1 HT1].
  eexists; econstructor; eassumption.
Qed. 

End EVAL_BUILTIN_ARG_EV.

Inductive asm_ev_step ge : state -> mem -> list mem_event -> state -> mem -> Prop :=
  | asm_ev_step_internal:
      forall b ofs f i rs m rs' m' lf T,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      drf_instr ge (fn_code f) i rs m = Some T ->
      asm_ev_step ge (State rs lf) m T (State rs' lf) m'
  | asm_ev_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' lf T
        (HFD: helper_functions_declared ge hf)
         (NASS: ~ isInlinedAssembly ef)  (*NEW; we don't support inlined assembly yet*),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      eval_builtin_args_ev _ ge rs (rs ESP) m args vargs T ->
      asm_ev_step ge (State rs lf) m T (State rs' lf) m' 
  | asm_ev_step_to_external:
      forall b ef args rs m lf T
      (HFD: helper_functions_declared ge hf),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      call_args_events rs m args = Some T -> 
      asm_ev_step ge (State rs lf) m T (Asm_CallstateOut ef args rs lf) m
  | asm_ev_step_external:
      forall b callee args res rs m t rs' m' lf T
      (HFD: helper_functions_declared ge hf)
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      ExtEvent callee m args = Some T ->
      asm_ev_step ge (Asm_CallstateOut callee args rs lf) m T (State rs' lf) m'
  (*NOTE [loader]*)
  | asm_ev_initialize_call: 
      forall m args tys retty m1 stk m2 fb z T
      (HFD: helper_functions_declared ge hf),
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 ->
      store_args_events stk args tys = Some T -> 
      let rs0 := (Pregmap.init Vundef) 
                  #PC <- (Vptr fb Int.zero)
                  #RA <- Vzero 
                  # ESP <- (Vptr stk Int.zero) in
      asm_ev_step ge (Asm_CallstateIn fb args tys retty) m (Alloc stk 0 (4*z) :: T)
               (State rs0 (mk_load_frame stk retty)) m2.

Lemma asm_ev_ax1 g (HFD: helper_functions_declared g hf): 
  forall c m T c' m' (EStep:asm_ev_step g c m T c' m'), corestep (Asm_mem_sem hf) g c m c' m'.
Proof.
 induction 1.
+ destruct i; inv H2;
  try solve[eapply asm_exec_step_internal; try eassumption; reflexivity].
+ (*builtin*) eapply asm_exec_step_builtin; eassumption.
+ (*step-to_callstateOut*) eapply asm_exec_step_to_external; eassumption. 
+ (*step_from-callstateOut*) eapply asm_exec_step_external; try eassumption.
+ (*loadframe*) eapply asm_exec_initialize_call; try eassumption. 
Qed.

Lemma asm_ev_ax2 g: forall c m c' m' (CS:corestep (Asm_mem_sem hf) g c m c' m'),
   exists T, asm_ev_step g c m T c' m'.
Proof. induction 1.
+ destruct i; inv H2;
  try solve [eexists; eapply asm_ev_step_internal; try eassumption; reflexivity].
  - unfold exec_load in H4.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Many32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - unfold exec_load in H4.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity. 
  - unfold exec_store in H4.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity. 
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as alloc; destruct alloc as [m1 stk]. 
    remember (Mem.store Mint32 m1 stk (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as p; destruct p; try discriminate.
    remember (Mem.store Mint32 m0 stk (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as q; destruct q; try discriminate.
    inv H4.
    eexists.
    eapply asm_ev_step_internal; try eassumption; simpl.
    * rewrite <- Heqalloc, <- Heqp, <- Heqq. reflexivity.
    * rewrite <- Heqalloc, <- Heqp, <- Heqq. reflexivity.
  - (*Pfreeframe*)
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as p; destruct p; try discriminate.
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q; destruct q; try discriminate.
    remember (rs ESP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as r; destruct r; try discriminate. inv H4.
    symmetry in Heqp, Heqq. simpl in *.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqq) as [bytes2 [Bytes2 LD2]].
    eexists.
    eapply asm_ev_step_internal; try eassumption; simpl.
    * rewrite <- Heqw in *. simpl.
      rewrite Heqp, Heqq, <- Heqr. trivial. 
    * rewrite <- Heqw in *. simpl in *.
      rewrite Heqp, Heqq, <- Heqr, Bytes1, Bytes2. reflexivity.
+ (*builtin*) 
  exploit eval_builtin_args_eval_builtin_args_ev. eassumption. intros [T HT].
  exists T. eapply asm_ev_step_builtin; try eassumption.
+ (*step-to_callstateOut*) admit. (*needs call args eexists. eapply asm_ev_step_to_external; eassumption. *)
+ (*step_from-callstateOut*) admit. (*needs args stuff eexists. eapply asm_ev_step_external; try eassumption.*)
+ (*loadframe*)
  unfold store_args in H1.
  destruct (store_args_ev_elim _ _ _ _ _ _ H1) as [T [HT EV]].
  eexists. eapply asm_ev_initialize_call; eassumption. 
Admitted.

Lemma asm_ev_fun g: forall c m T' c' m' T'' c'' m''
    (Estep': asm_ev_step g c m T' c' m') (Estep'': asm_ev_step g c m T'' c'' m''), T' = T''.
Proof. intros.
inv Estep'; inv Estep''; trivial.
+ rewrite H in H6; inv H6. rewrite H0 in H7; inv H7.
  rewrite H1 in H8; inv H8. rewrite H2 in H9; inv H9.
  rewrite H3 in H14; inv H14. trivial.
+ rewrite H in H6; inv H6. rewrite H0 in H7; inv H7.
  rewrite H1 in H8; inv H8. simpl in *; discriminate. 
+ rewrite H in H6; inv H6. rewrite H0 in H7; inv H7.
+ rewrite H in H8; inv H8. rewrite H0 in H9; inv H9.
  rewrite H1 in H10; inv H10. simpl in *; discriminate. 
+ rewrite H in H8; inv H8. rewrite H0 in H9; inv H9.
  rewrite H1 in H10; inv H10.
  exploit eval_builtin_args_determ. apply H11. apply H2. intros; subst vargs0.
  exploit eval_builtin_args_ev_determ. apply H6. apply H19. intros [_ X]; trivial.
+ rewrite H in H8; inv H8. rewrite H0 in H9; inv H9.
+ rewrite H in H5; inv H5. rewrite H0 in H6; inv H6.
+ rewrite H in H5; inv H5. rewrite H0 in H6; inv H6.
+ rewrite H in H5; inv H5. rewrite H0 in H6; inv H6.
  exploit extcall_arguments_determ. apply H7. apply H1. intros; subst args0.
  admit. (*needs determinsm of call_args_events*)
+ rewrite H in H7; inv H7. simpl in *.  admit. (*TODO: needs determinism of ExtEvent*) 
+ (*loadframe*)
  rewrite H in H7; inv H7. rewrite H0 in H12; inv H12.
  rewrite H1 in H13; inv H13. rewrite H2 in H14; inv H14. reflexivity. 
Admitted.

Lemma asm_ev_elim g: forall c m T c' m' (Estep: asm_ev_step g c m T c' m'), ev_elim m T m'.
Proof.
induction 1; intros.
+ destruct i; inv H2; inv H3;
  try solve [eexists; split; reflexivity]. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_store in H5.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_store in H5.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H5.
    destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H3.
    eexists; simpl; split; reflexivity.
  - destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H5.
    destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H3.
    eexists; simpl; split; reflexivity.
  - destruct (eval_testcond c rs); inv H5.
    * destruct b0; inv H3; eexists; simpl; split; reflexivity.
    * eexists; simpl; split; reflexivity.
  - unfold goto_label in H5. rewrite H in *.
    destruct (label_pos l 0 (fn_code f)); inv H5. 
    eexists; simpl; split; reflexivity.
  - destruct (eval_testcond c rs); inv H5.
    destruct b0; inv H3; try solve [eexists; simpl; split; reflexivity].
    unfold goto_label in H4. rewrite H in *.
    destruct (label_pos l 0 (fn_code f)); inv H4.
    eexists; simpl; split; reflexivity.
  - destruct (eval_testcond c1 rs); inv H5.
    destruct b0; inv H3.
    * destruct (eval_testcond c2 rs); inv H4.
      destruct b0; inv H3; try solve [eexists; simpl; split; reflexivity].
      unfold goto_label in H4. rewrite H in *.
      destruct (label_pos l 0 (fn_code f)); inv H4.
      eexists; simpl; split; reflexivity.
    * destruct (eval_testcond c2 rs); inv H4; try solve [eexists; simpl; split; reflexivity].
  - destruct (rs r); inv H5.
    destruct (list_nth_z tbl (Int.unsigned i)); inv H3. 
    unfold goto_label in H4. rewrite H in *.
    destruct (label_pos l 0 (fn_code f)); inv H4.
    eexists; simpl; split; reflexivity.
  - unfold exec_load in H5.
    remember (Mem.loadv Many32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as a; symmetry in Heqa; destruct a as [m1 stk].
    remember (Mem.store Mint32 m1 stk
         (Int.unsigned (Int.add Int.zero ofs_link)) 
         (rs ESP)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (Mem.store Mint32 m0 stk (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as q.
    destruct q; try discriminate; symmetry in Heqq. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    apply Mem.store_storebytes in Heqq.
    rewrite Int.add_zero_l in *.
    econstructor. split. eassumption.
    econstructor. split. eassumption.
    econstructor. split. eassumption.
    econstructor. 
  - (*Pfreeframe*)
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q.
    destruct q; try discriminate; symmetry in Heqq.
    remember (rs ESP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as t; destruct t; try discriminate. 
    inv H5; inv H4; simpl in *.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqq) as [bytes2 [Bytes2 LD2]].
    simpl in *. rewrite Bytes1, Bytes2 in *. inv H3.
    econstructor. trivial.
    econstructor. trivial.
    econstructor. split. simpl. rewrite <- Heqt; trivial.
    econstructor. 
+ (*builtin*) admit. (*TODO*)
 (* induction H6. admit. (*needs fact that builtins don't change memory*)*) 
+ admit. (*needs facts about call_args*)
+ admit. (*extcall*)
+ (*loadframe*)
    eexists. split. eassumption.
    destruct (store_args_ev_elim _ _ _ _ _ _ H1) as [TT [HTT EV]].
    unfold store_args_events in H2. rewrite H2 in HTT. inv HTT. trivial.
Admitted. (*due to extcall and builtins*)

Lemma AR n: match n with
                  | 0 => 0
                  | Z.pos y' => Z.pos y'~0~0
                  | Z.neg y' => Z.neg y'~0~0
                  end = 4*n.
destruct n; simpl; trivial. Qed. 

Lemma store_args_rec_transfer stk m2 mm': forall args tys m1 n
 (STARGS: store_args_rec m1 stk n args tys = Some m2) TT
 (STARGSEV: store_args_ev_rec stk n args tys = Some TT) x
 (EV: ev_elim x TT mm'), store_args_rec x stk n args tys = Some mm'.
Proof.
 induction args; simpl; intros; destruct tys; try discriminate.
+ inv STARGS. inv STARGSEV. inv EV.  trivial.
+ rewrite AR in *. Opaque Z.mul. 
  destruct t. 
  - remember (store_args_ev_rec stk (n + typesize Tint) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tint (Int.repr (4*n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp. 
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - remember ( store_args_ev_rec stk (n + typesize Tfloat) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tfloat 
             (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp. 
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - destruct a; try discriminate.
    remember (store_args_ev_rec stk (n + 2) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV]. inv EV. destruct H.
    remember (store_stack m1 (Vptr stk Int.zero) Tint
             (Int.repr
                match n + 1 with
                | 0 => 0
                | Z.pos y' => Z.pos y'~0~0
                | Z.neg y' => Z.neg y'~0~0
                end) (Vint (Int64.hiword i))) as q. destruct q; inv STARGS.
    remember (store_stack m (Vptr stk Int.zero) Tint (Int.repr (4 * n))
         (Vint (Int64.loword i))) as w; destruct w; inv H2.
    symmetry in Heqq, Heqp, Heqw. 
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGNhi].
    unfold store_stack in Heqw; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqw) as [_ ALGNlo].
    specialize (IHargs _ _ _ H3 _ Heqp _ H0).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *; simpl in *.
    erewrite Mem.storebytes_store; try eassumption.
    erewrite Mem.storebytes_store; try eassumption.
    rewrite Int.add_zero_l; assumption. rewrite Int.add_zero_l; assumption.
  - remember (store_args_ev_rec stk (n + typesize Tsingle) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tsingle (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp. 
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - remember (store_args_ev_rec stk (n + typesize Tany32) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tany32 (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp. 
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - remember (store_args_ev_rec stk (n + typesize Tany64) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tany64 (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp. 
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
Qed.

Lemma asm_ev_elim_strong g: forall c m T c' m' (Estep: asm_ev_step g c m T c' m'), 
      ev_elim m T m' /\ (forall mm mm', ev_elim mm T mm' -> exists cc', asm_ev_step g c mm T cc' mm').
Proof.
induction 1; intros.
+ destruct i; inv H2; inv H3;
  try solve [split; 
        first [eexists; split; reflexivity |
               intros mm mm' EV'; inv EV'; destruct H2 as [FL EV']; inv EV'; inv FL;
                 eexists; econstructor; try eassumption; reflexivity]]. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl. erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_store in H5.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_load in H5.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.   
  - unfold exec_load in H5.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity. 
  - remember (Val.divu (rs EAX) (rs # EDX <- Vundef r1)) as p; destruct p; inv H5.
    remember (Val.modu (rs EAX) (rs # EDX <- Vundef r1)) as q; destruct q; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqp, <- Heqq; reflexivity. 
  - remember (Val.divs (rs EAX) (rs # EDX <- Vundef r1)) as p; destruct p; inv H5.
    remember ( Val.mods (rs EAX) (rs # EDX <- Vundef r1)) as q; destruct q; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqp, <- Heqq; reflexivity. 
  - remember (eval_testcond c rs) as p; destruct p; inv H5.
    * destruct b0; inv H3.
      ++ split. econstructor. split. reflexivity. constructor.
         intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
      ++ split. econstructor. split. reflexivity. constructor.
         intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
    * split. econstructor. split. reflexivity. constructor.
      intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
  - unfold goto_label in H5. rewrite H in *.
    remember (label_pos l 0 (fn_code f)) as p; destruct p; inv H5. 
    split. 
    * econstructor. split. reflexivity. constructor.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; trivial.
      unfold goto_label. rewrite <- Heqp, H. reflexivity.
  - remember (eval_testcond c rs) as p;destruct p; inv H5.
    destruct b0; inv H3. 
    * unfold goto_label in H4. rewrite H in *.
      remember (label_pos l 0 (fn_code f)) as q; destruct q; inv H4.
      split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
         unfold goto_label. rewrite <- Heqq, H; reflexivity.
    * split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
  - remember (eval_testcond c1 rs) as p; destruct p; inv H5.
    destruct b0; inv H3.
    * remember (eval_testcond c2 rs) as q; destruct q; inv H4.
      destruct b0; inv H3.
      ++ unfold goto_label in H4. rewrite H in *.
         remember (label_pos l 0 (fn_code f)) as w; destruct w; inv H4.
         split.
         -- econstructor. split. reflexivity. constructor.
         -- intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
            eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
            unfold goto_label. rewrite <- Heqw, H; reflexivity.
      ++ split.
         -- econstructor. split. reflexivity. constructor.
         -- intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
            eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
    * remember (eval_testcond c2 rs) as q; destruct q; inv H4.
      split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
  - remember (rs r) as p; destruct p; inv H5.
    remember (list_nth_z tbl (Int.unsigned i)) as q; destruct q; inv H3. 
    unfold goto_label in H4. rewrite H in *.
    remember (label_pos l 0 (fn_code f)) as w; destruct w; inv H4.
    split.
      * econstructor. split. reflexivity. constructor.
      * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
        eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
        unfold goto_label. rewrite <- Heqw, H; reflexivity.
  - unfold exec_load in H5.
    remember (Mem.loadv Many32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - unfold exec_store in H5.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity. 
  - unfold exec_load in H5.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - unfold exec_store in H5.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity. 
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as a; symmetry in Heqa; destruct a as [m1 stk].
    remember (Mem.store Mint32 m1 stk
         (Int.unsigned (Int.add Int.zero ofs_link)) 
         (rs ESP)) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (Mem.store Mint32 m0 stk (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as q.
    destruct q; try discriminate; symmetry in Heqq. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGNp].
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALIGNq].
    apply Mem.store_storebytes in Heqp.
    apply Mem.store_storebytes in Heqq.
    rewrite Int.add_zero_l in *.
    split.
    * econstructor. split. eassumption.
      econstructor. split. eassumption.
      econstructor. split. eassumption.
      econstructor.
    * intros mm mm' EV'; inv EV'. destruct H2 as [ALLOC EV]. inv EV. inv H2. inv H4. destruct H2. inv H4.
      eexists; econstructor; try eassumption; simpl; repeat rewrite Int.add_zero_l; rewrite ALLOC;
      repeat erewrite Mem.storebytes_store; try eassumption; reflexivity. 
  - (*Pfreeframe*)
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as p.
    destruct p; try discriminate; symmetry in Heqp.  
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q.
    destruct q; try discriminate; symmetry in Heqq.
    remember (rs ESP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as t; destruct t; try discriminate.
    inv H5; inv H4.
    destruct (Mem.load_loadbytes _ _ _ _ _  Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _  Heqq) as [bytes2 [Bytes2 LD2]].
    simpl in *; rewrite Bytes1, Bytes2 in *. inv H3.
    destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN1].
    destruct (Mem.load_valid_access _ _ _ _ _ Heqq) as [_ ALIGN2].
    split.
    * econstructor; trivial. econstructor; trivial.  econstructor.
      split. simpl. rewrite <- Heqt; trivial. econstructor. 
    * intros mm mm' EV'. inv EV'. inv H3. inv H5. destruct H3. inv H5. simpl in H3.
      remember (Mem.free mm b0 0 sz) as d; destruct d; try discriminate. inv H3.
      exploit (Mem.loadbytes_load Mint32). apply H2. assumption.
      exploit (Mem.loadbytes_load Mint32). apply H4. assumption.
      eexists; econstructor; try eassumption. 
      ++ simpl. rewrite <- Heqw; simpl. rewrite H3, H5, <- Heqd. reflexivity.
      ++ simpl. rewrite <- Heqw; simpl. rewrite H3, H5, <- Heqd. rewrite H2, H4. reflexivity.
+ (*builtin*) admit.
+ split.
  - admit.  (*extcallargs*)
  - intros mm mm' EV'. admit. (*inv EV'.
    eexists. eapply asm_ev_step_to_external; try eassumption. econstructor. eassumption. eassumption.  simpl.*)
+ admit. (*extcall*)
+ (*loadframe*)
   destruct (store_args_ev_elim _ _ _ _ _ _ H1) as [TT [HTT EV]].
   unfold store_args_events in H2. rewrite H2 in HTT. inv HTT. 
   split.
   * econstructor. split; eassumption.
   * intros mm mm' EV'. inv EV'. destruct H3.
     exploit store_args_rec_transfer. eassumption. eassumption. eassumption. intros SAR. 
     eexists. econstructor; try eassumption.
Admitted. (*due to extcall and builtins*)

Program Definition Asm_EvSem : @EvSem genv state.
Proof.
eapply Build_EvSem with (msem := Asm_mem_sem hf) (ev_step:=asm_ev_step).
+ intros. eapply asm_ev_ax1; try eassumption. admit. (*helper_functions declared*)
+ eapply asm_ev_ax2; eassumption.
+ eapply asm_ev_fun; eassumption.
+ eapply asm_ev_elim; eassumption.
Admitted. (*helper_functions declared*)

End ASM_EV.
