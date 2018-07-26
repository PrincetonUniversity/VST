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
Require Import compcert.backend.Locations.
Require Import compcert.backend.Conventions.
Require Import compcert.x86.Asm.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.common.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.common.Asm_core.

Require Import List. Import ListNotations.
(*
Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).
*)

Section ASM_EV.
(*Variable hf : I64Helpers.helper_functions.*)

Definition drf_instr (ge:genv) (c: code) (i: instruction) (rs: regset) (m: mem)
           : option (list mem_event)  :=
  match i with
  | Pfstps_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mfloat32 (rs ST0))]
                  | _ => None
                 end
  | Pfstpl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mfloat64 (rs ST0))]
                  | _ => None
                 end
  | Pmovss_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mfloat32 (rs r1))]
                  | _ => None
                 end
  | Pmovl_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mint32 (rs r1))]
                  | _ => None
                 end
  | Pmovq_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mint64 (rs r1))]
                  | _ => None
                 end
  | Pmov_mr_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Many32 (rs r1))]
                  | _ => None
                 end
  | Pmovsd_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mfloat64 (rs r1))]
                  | _ => None
                 end
  | Pmovsd_mf_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs)  (encode_val Many64 (rs r1))]
                  | _ => None
                 end
  | Pmovb_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mint8unsigned (rs r1))]
                  | _ => None
                 end
  | Pmovw_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Ptrofs.unsigned ofs) (encode_val Mint16unsigned (rs r1))]
                  | _ => None
                 end

  | Pmovl_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mint32) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mint32) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovq_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mint64) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mint64) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovsd_fm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mfloat64) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mfloat64) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovss_fm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mfloat32) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mfloat32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pfldl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mfloat64) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mfloat64) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pflds_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mfloat32) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mfloat32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovzb_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mint8unsigned) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mint8unsigned) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsb_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mint8signed) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mint8signed) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovzw_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mint16unsigned) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mint16unsigned) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsw_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Mint16signed) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Mint16signed) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmov_rm_a rd a =>
    match eval_addrmode ge a rs with
      Vptr b ofs =>
      match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk (if Archi.ptr64 then Many64 else Many32)) with
        Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk (if Archi.ptr64 then Many64 else Many32)) bytes]
      | None => None
      end
    | _ => None
    end
  | Pmovsd_fm_a rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk Many64) with
                                    Some bytes => Some [Read b (Ptrofs.unsigned ofs) (size_chunk Many64) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_link) rs#RSP with
      | None => None
      | Some m2 =>
          match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
          | None => None
          | Some m3 => Some [Alloc stk 0 sz;
                             Write stk (Ptrofs.unsigned ofs_link) (encode_val Mptr (rs RSP));
                             Write stk (Ptrofs.unsigned ofs_ra) (encode_val Mptr (rs RA))]
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => None
      | Some ra =>
          match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
          | None => None
          | Some sp =>
              match rs#RSP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => None
                  | Some m' => match (Val.offset_ptr rs#RSP ofs_ra), (Val.offset_ptr rs#RSP ofs_link) with
                                Vptr b1 ofs1, Vptr b2 ofs2 =>
                                  match Mem.loadbytes m b1 (Ptrofs.unsigned ofs1) (size_chunk Mptr), Mem.loadbytes m b2 (Ptrofs.unsigned ofs2) (size_chunk Mptr)
                                  with Some bytes1, Some bytes2=>
                                     Some [Read b1 (Ptrofs.unsigned ofs1) (size_chunk Mptr) bytes1;
                                           Read b2 (Ptrofs.unsigned ofs2) (size_chunk Mptr) bytes2;
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
  | eval_BA_ev_loadstack: forall chunk ofs v b z bytes,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      (align_chunk chunk | (Ptrofs.unsigned z)) ->
      Mem.loadbytes m b (Ptrofs.unsigned z) (size_chunk chunk) = Some bytes ->
      v= decode_val chunk bytes ->
      Val.offset_ptr sp ofs = Vptr b z ->
      eval_builtin_arg_ev (BA_loadstack chunk ofs) v [Read b (Ptrofs.unsigned z) (size_chunk chunk) bytes]
  | eval_BA_ev_addrstack: forall ofs,
      eval_builtin_arg_ev (BA_addrstack ofs) (Val.offset_ptr sp ofs) nil
  | eval_BA_ev_loadglobal: forall chunk id ofs v b z bytes,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      (align_chunk chunk | (Ptrofs.unsigned z)) ->
      Mem.loadbytes m b (Ptrofs.unsigned z) (size_chunk chunk) = Some bytes ->
      v= decode_val chunk bytes ->
      Senv.symbol_address ge id ofs = Vptr b z ->
      eval_builtin_arg_ev (BA_loadglobal chunk id ofs) v [Read b (Ptrofs.unsigned z) (size_chunk chunk) bytes]
  | eval_BA_ev_addrglobal: forall id ofs,
      eval_builtin_arg_ev (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs) nil
  | eval_BA_ev_splitlong: forall hi lo vhi vlo Thi Tlo,
      eval_builtin_arg_ev hi vhi Thi -> eval_builtin_arg_ev lo vlo Tlo->
      eval_builtin_arg_ev (BA_splitlong hi lo) (Val.longofwords vhi vlo) (Thi++Tlo)
  | eval_BA_ev_addptr: forall a1 a2 v1 v2 T1 T2,
      eval_builtin_arg_ev a1 v1 T1 -> eval_builtin_arg_ev a2 v2 T2->
      eval_builtin_arg_ev (BA_addptr a1 a2) (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2) (T1++T2).

Lemma eval_builtin_arg_ev_determ: forall a v1 T1 (HT1:eval_builtin_arg_ev a v1 T1)
      v2 T2 (HT2:eval_builtin_arg_ev a v2 T2), v1=v2 /\ T1=T2.
Proof.
induction a; intros; inv HT1; inv HT2; try solve [split; trivial].
+ rewrite H11 in H7; inv H7. rewrite H6 in H3; inv H3. split; trivial.
+ rewrite H12 in H8; inv H8. rewrite H7 in H4; inv H4. split; trivial.
+ destruct (IHa1 _ _ H2 _ _ H1); subst.
  destruct (IHa2 _ _ H6 _ _ H4); subst. split; trivial.
+ destruct (IHa1 _ _ H2 _ _ H1); subst.
  destruct (IHa2 _ _ H6 _ _ H4); subst. split; trivial.
Qed.

Lemma eval_builtin_arg_event: forall a v, eval_builtin_arg ge e sp m a v -> exists T, eval_builtin_arg_ev a v T.
Proof.
  induction 1; intros; try solve [eexists; econstructor; try eassumption].
+ assert (B: exists b z, sp = Vptr b z). destruct sp; inv H. exists b, i; trivial.
  destruct B as [b [i SP]]. subst sp. simpl in H.
  destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALIGN].
  destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes [LD V]].
  eexists. econstructor. subst sp; simpl; eassumption. eassumption. eassumption. trivial. subst sp. reflexivity.
+ assert (B: exists b z, (Senv.symbol_address ge id ofs) = Vptr b z). destruct (Senv.symbol_address ge id ofs); inv H. exists b, i; trivial.
  destruct B as [b [i SA]]. rewrite SA in *.
  destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes [LB V]].
  destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
  eexists. econstructor; try eassumption; trivial. rewrite SA; trivial.
+ destruct IHeval_builtin_arg1 as [Thi HThi]. destruct IHeval_builtin_arg2 as [Tlo HTlo].
  eexists. econstructor; eassumption.
+ destruct IHeval_builtin_arg1 as [T1 HT1]. destruct IHeval_builtin_arg2 as [T2 HT2].
  eexists. econstructor; eassumption.
Qed.

Lemma eval_builtin_arg_event_inv: forall a v T, eval_builtin_arg_ev a v T -> eval_builtin_arg ge e sp m a v.
Proof. induction 1; intros; solve [econstructor; try eassumption]. Qed.

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

Lemma eval_builtin_args_ev_eval_builtin_args: forall al vl T, eval_builtin_args_ev al vl T ->
  eval_builtin_args ge e sp m al vl.
Proof.
  induction 1.
+ econstructor.
+ apply eval_builtin_arg_event_inv in H. econstructor; eassumption.
Qed.

End EVAL_BUILTIN_ARG_EV.

Lemma eval_builtin_arg_ev_elim_strong {A} ge (rs: A -> val) sp m a v T (EV: eval_builtin_arg_ev A ge rs sp m a v T):
  ev_elim m T m /\
  (forall mm mm', ev_elim mm T mm' -> mm'=mm /\ eval_builtin_arg_ev A ge rs sp mm a v T).
Proof.
  induction EV.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split.
  - constructor; trivial. constructor.
  - intros mm mm' MM; inv MM; split.
    * inv H5; trivial.
    * inv H5. rewrite H3 in *.
      destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes2 [LB2 V2]]. rewrite LB2 in H1; inv H1.
      destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
      constructor; try eassumption; trivial.
      rewrite H3; simpl. erewrite Mem.loadbytes_load; trivial.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split.
  - constructor; trivial. constructor.
  - intros mm mm' MM; inv MM; split.
    * inv H5; trivial.
    * inv H5. rewrite H3 in *.
      destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes2 [LB2 V2]]. rewrite LB2 in H1; inv H1.
      destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
      constructor; try eassumption; trivial.
      rewrite H3; simpl. erewrite Mem.loadbytes_load; trivial.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ destruct IHEV1 as [EL1 EStrong1]. destruct IHEV2 as [EL2 EStrong2].
  split. eapply ev_elim_app; eassumption.
  intros. apply ev_elim_split in H; destruct H as [m' [E1 E2]].
  destruct (EStrong1 _ _ E1) as [MT EHi]; subst mm.
  destruct (EStrong2 _ _ E2) as [ML ELo]; subst mm'.
  split; trivial.
  constructor; eassumption.
+ destruct IHEV1 as [EL1 EStrong1]. destruct IHEV2 as [EL2 EStrong2].
  split. eapply ev_elim_app; eassumption.
  intros. apply ev_elim_split in H; destruct H as [m' [E1 E2]].
  destruct (EStrong1 _ _ E1) as [MT EHi]; subst mm.
  destruct (EStrong2 _ _ E2) as [ML ELo]; subst mm'.
  split; trivial.
  constructor; eassumption.
Qed.

Lemma eval_builtin_args_ev_elim_strong {A} ge (rs: A -> val) sp m al vl T (EV: eval_builtin_args_ev A ge rs sp m al vl T):
  ev_elim m T m /\
  (forall mm mm', ev_elim mm T mm' -> mm'=mm /\ eval_builtin_args_ev A ge rs sp mm al vl T).
Proof.
  induction EV.
+ split. constructor.
  intros mm mm' MM; inv MM; split; trivial. constructor.
+ destruct IHEV as [EV2 HEV2].
  apply eval_builtin_arg_ev_elim_strong in H. destruct H as [EV1 HEV1].
  split. eapply ev_elim_app; eassumption.
  intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [m' [EV1' EV2']].
  destruct (HEV1 _ _ EV1') as [? HE1]; subst.
  destruct (HEV2 _ _ EV2') as [? HE2]; subst.
  split; trivial.
  constructor; trivial.
Qed.

Definition option_list_to_list {A} (x: option (list A)) : list A :=
 match x with Some al => al | None => nil end.

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
(*| BE_EFexternal: forall name sg m vargs,
(*        I64Helpers.is_I64_helperS name sg ->*)
         builtin_event (EF_external name sg) m vargs []
| BE_EFbuiltin: forall name sg m vargs, (*is_I64_builtinS name sg ->*)
         builtin_event (EF_builtin name sg) m vargs []*)
| BE_other: forall ef m vargs,
  match ef with EF_malloc | EF_free | EF_memcpy _ _ => False | _ => True end ->
  builtin_event ef m vargs [].

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
inversion BE1; inv BE2; try discriminate; try contradiction; simpl in *; trivial.
+ assert (Vptrofs n0 = Vptrofs n) as H by congruence.
  rewrite H; rewrite (Vptrofs_inj _ _ H) in *.
  rewrite ALLOC0 in ALLOC; inv ALLOC; trivial.
+ inv H5.
  rewrite LB0 in LB; inv LB. rewrite <- SZ in SZ0. rewrite (Vptrofs_inj _ _ SZ0); trivial.
+ inv H3; inv H5.
  rewrite LB0 in LB; inv LB; trivial.
Qed.

Inductive asm_ev_step ge: state -> mem -> list mem_event -> state -> mem -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m1 m rs' m' T,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      drf_instr ge (fn_code f) i rs m = Some T ->
      asm_ev_step ge (State rs m1) m T (State rs' m') m'
  | exec_step_builtin:
      forall b ofs f ef args res rs m1 m vargs t T1 T2 vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args_ev _ ge rs (rs RSP) m args vargs T1 ->
      builtin_event ef m vargs T2 ->
(*      ev_elim m (T1++T2) m' ->*)
  (* Must it be the case that builtins don't produce trace events? *)
      external_call ef ge vargs m (*nil*) t vres m' ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_ev_step ge (State rs m1) m (T1++T2) (State rs' m') m'.

Lemma asm_ev_ax1 g (Hsafe : safe_genv g) (*(HFD: helper_functions_declared g hf)*):
  forall c m T c' m' (EStep:asm_ev_step g c m T c' m'), 
      corestep (Asm_mem_sem g Hsafe (*hf*)) c m c' m'.
Proof.
 induction 1.
 - econstructor; [econstructor; eauto | simpl].
   rewrite H.
   destruct (Ptrofs.eq_dec _ _); auto.
   unfold fundef; rewrite H0; auto.
 - econstructor; [econstructor 2; eauto | simpl].
   + eapply eval_builtin_args_ev_eval_builtin_args; eauto.
   + rewrite H.
     destruct (Ptrofs.eq_dec _ _); auto.
     unfold fundef; rewrite H0; auto.
Qed.

Lemma asm_ev_ax2 g (Hsafe : safe_genv g) :
  forall c m c' m' (CS:corestep (Asm_mem_sem g Hsafe (*hf*)) c m c' m'),
   exists T, asm_ev_step g c m T c' m'.
Proof.
  inversion 1; subst.
  destruct c, c'; simpl in *.
  inv H.
  - remember (drf_instr g (fn_code f) i r m) eqn:Hdrf.
    pose proof Hdrf as Hdrf'.
    symmetry in Hdrf'. 
    unfold drf_instr in Hdrf.
    unfold exec_instr in *.
    assert (exists T, drf_instr g (fn_code f) i r m = Some T).
    { clear H0.
      assert (Archi.ptr64 = false) by auto.
      destruct i; subst; 
        repeat match goal with
               |[H: exec_load _ _ _ _ _ _ = _ |- _] =>
                unfold exec_load in H
               |[H: exec_store _ _ _ _ _ _ _ = _ |- _] =>
                unfold exec_store in H
               |[H:context[Mem.loadv _ _ (eval_addrmode ?E1 ?E2 ?E3)] |- _] =>
                destruct (eval_addrmode E1 E2 E3); simpl in H; try discriminate
               |[H:context[Mem.storev _ _ (eval_addrmode ?E1 ?E2 ?E3) _] |- _] =>
                destruct (eval_addrmode E1 E2 E3); simpl in H; try discriminate
               |[H: match Mem.load ?E1 ?E2 ?E3 ?E4 with _ => _ end = _ |- _] =>
                destruct (Mem.load E1 E2 E3 E4) eqn:?; try discriminate
               |[H: match Mem.store ?E1 ?E2 ?E3 ?E4 ?E5 with _ => _ end = _ |- _] =>
                destruct (Mem.store E1 E2 E3 E4 E5) eqn:?; try discriminate
               |[H: Mem.load _ _ _ _ = _  |- _] =>
                eapply Mem.load_loadbytes in H;
                  destruct H as [? [? ?]]
               |[H: Mem.store _ _ _ _ _ = _  |- _] =>
                eapply Mem.store_storebytes in H
               |[H: Mem.loadbytes _ _ _ _ = _, H1: _ = match Mem.loadbytes _ _ _ _ with _ => _ end |- _] =>
                rewrite H in H1
               |[H: Mem.storebytes _ _ _ _ _ = _, H1: _ = match Mem.storebytes _ _ _ _ _ with _ => _ end |- _] =>
                rewrite H in H1
               |[H: context[if Archi.ptr64 then _ else _] |- _] =>
                destruct (Archi.ptr64)
               |[H: context[Mem.alloc ?E1 ?E2 ?E3] |- _] =>
                destruct (Mem.alloc E1 E2 E3)
               |[H: match Mem.storev ?E1 ?E2 ?E3 ?E4 with _ => _ end = _ |- _] =>
                destruct (Mem.storev E1 E2 E3 E4); try discriminate
               |[H: match ?Expr with _ => _ end = _ |- _] =>
                destruct Expr eqn:?; try discriminate
               end;
        try (eexists; now eauto).
      destruct ((Val.offset_ptr (Vptr b0 i) ofs_ra)); simpl in Heqo; try discriminate.
      destruct ((Val.offset_ptr (Vptr b0 i) ofs_link)); simpl in Heqo0; try discriminate.
      eapply Mem.load_loadbytes in Heqo; eauto.
      eapply Mem.load_loadbytes in Heqo0.
      destruct Heqo as [? [Hload ?]].
      destruct Heqo0 as [? [Hload0 ?]].
      rewrite Hload, Hload0 in Hdrf'.
      now eauto.
    }
    destruct H.
    eexists; econstructor; now eauto.
- exploit Hsafe; eauto.
  apply eval_builtin_args_eval_builtin_args_ev in H9 as [T H9].
  destruct ef; try solve [intros []; subst; exists (T ++ nil); econstructor 2; eauto; constructor; auto]; intros _.
  + inv H10. destruct (Mem.store_valid_access_3 _ _ _ _ _ _ H1) as [_ ALGN].
    pose proof (Mem.store_storebytes _ _ _ _ _ _ H1).
    eexists; econstructor 2; eauto; econstructor; eauto.
  + inv H10. destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
    pose proof (Mem.load_loadbytes _ _ _ _ _ H) as (? & ? & ?).
    eexists; econstructor 2; eauto; econstructor; eauto.
  + inv H10.
    eexists; econstructor 2; eauto; econstructor; eauto.
- simpl in *.
  rewrite H5 in H0.
  destruct (Ptrofs.eq_dec _ _); [|contradiction].
  rewrite H6 in H0.
  apply get_extcall_arguments_spec in H8; rewrite H8 in H0; discriminate.
Qed.

Lemma asm_ev_fun g: forall c m T' c' m' T'' c'' m''
    (Estep': asm_ev_step g c m T' c' m') (Estep'': asm_ev_step g c m T'' c'' m''), T' = T''.
Proof. intros.
inv Estep'; inv Estep''; trivial; try contradiction; try congruence;
  repeat match goal with H1 : ?a = _, H2 : ?a = _ |- _ => rewrite H1 in H2; inv H2 end.
inv H2.
inv H10.
pose proof (eval_builtin_args_ev_determ _ _ _ _ _ _ _ _ H2 _ _ H10) as []. subst.
clear - H3 H11.
f_equal; eapply builtin_event_determ; eauto.
Qed.

Lemma asm_ev_elim g (Hsafe : safe_genv g): forall c m T c' m' 
     (Estep: asm_ev_step g c m T c' m'), ev_elim m T m'.
Proof.
intros.
inv Estep; try contradiction.
clear - H2 H3.
(* assert (Harchi: Archi.ptr64 = false) by auto. *)
destruct i; inv H2; simpl in *; inv H3; simpl; eauto;
  unfold exec_load, exec_store in *;
  simpl in *;
try match goal with
    | H0 : match ?L with Some _ => _ | None => _ end = _ |- _ =>
        destruct L eqn:H; inv H0
    end;
   repeat match goal with
          | [H: context [eval_addrmode ?G ?A ?C] |- _]  => 
            destruct (eval_addrmode G A C) eqn:H2; try discriminate; simpl in H
          | [H: Mem.load _ _ _ _ = _, H1: match Mem.loadbytes _ _ _ _ with _ => _ end = _ |- _] =>
            eapply Mem.load_loadbytes in H;
              destruct H as [bytes [LB LV]]; simpl in LB; rewrite LB in H1; inv H1
          | [H: Some _ = Some _ |- _] =>
            inv H
          | [H: Mem.storev _ _ _ _ = _ |- _] =>
            eapply Mem.store_storebytes in H; try (simpl; eexists; split; now eauto)
          end; try (simpl; split; auto);
   try (repeat match goal with
   | H: match ?X with Vundef => _ | Vint _ => _ | Vlong _ => _ | Vfloat _ => _ | Vsingle _ => _ | Vptr _ _ => _ end = _ |- _ => destruct X; inv H
   | H: match ?X with Some _ => _ | None => _ end = _ |- _ => first [destruct X as [[]|] | destruct X]; inv H
   (* | H: context[if Archi.ptr64 then _ else _] |- _ => rewrite Harchi in H *)
   | H: context[if ?B then _ else _] |- _ => destruct B; try discriminate
   | H: goto_label _ _ _ _ = Next _ _ |- _ => apply goto_label_mem_same in H; subst
   | H: Next _ _ = Next _ _ |- _ => inv H 
   end;
        eexists; split; now eauto).
  - (*Pallocframe*)
    destruct (Mem.alloc m 0 sz) eqn:?H.
    destruct (Mem.store Mptr m0 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_link)) (rs RSP)) eqn:?H;
      try discriminate.
    destruct (Mem.store Mptr m1 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_ra)) (rs RA)) eqn:?H;
      try discriminate.
    inv H0.
    apply Mem.store_storebytes in H2.
    apply Mem.store_storebytes in H3.
    rewrite Ptrofs.add_zero_l in *.
    inv H1.
    simpl.
    eexists; split;
      now eauto.
  - (*Pfreeframe*)
    destruct (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_link)) eqn:?H; try discriminate.
    destruct (rs RSP); try discriminate.
    destruct (Mem.free m b 0 sz) eqn:Hfree. inv H0.
    destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _ H1) as [bytes2 [Bytes2 LD2]].
    subst.
    destruct (Val.offset_ptr (Vptr b i) ofs_ra); try discriminate.
    destruct (Val.offset_ptr (Vptr b i) ofs_link); try discriminate.
    destruct (Mem.loadbytes m b0 (Ptrofs.unsigned i0) (size_chunk Mptr)) eqn:?,
    (Mem.loadbytes m b1 (Ptrofs.unsigned i1) (size_chunk Mptr)) eqn:?; try discriminate.
    inv H3.
    simpl.
    split; auto. split; auto.
    eexists. rewrite Hfree; split; eauto.
    discriminate.
- destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H2).
  eapply ev_elim_app; eauto.
  exploit Hsafe; eauto.
  { eapply eval_builtin_args_ev_eval_builtin_args; eauto. }
  inversion H3; subst ef; [.. | destruct ef0; try contradiction; intros []; simpl; auto]; intros _.
  + (*malloc*)
    inv H4.
    rewrite Vptrofs_inj with (o2 := n) in H7 by congruence.
    rewrite H7 in ALLOC. inv ALLOC.
    apply Mem.store_storebytes in H11.
    replace (Vptrofs sz) with (Vptrofs n) in H11 by congruence.
    econstructor. split. eassumption.
    econstructor. split. eassumption. constructor.
  + (*free*)
    inv H4.
    inv H13.
    destruct (Mem.load_loadbytes _ _ _ _ _ H7) as [bytes1 [LB1 SZ1]].
    rewrite LB1 in LB; inv LB. rewrite <- SZ1 in SZ.
    rewrite (Vptrofs_inj _ _ SZ) in *.
    rewrite H12 in FR; inv FR.
    econstructor. eassumption.
    econstructor. split. simpl. rewrite H12. reflexivity. constructor.
  + (*memcpy*)
    inv H4. inv H18. rewrite LB in H16; inv H16. rewrite ST in H17; inv H17.
    econstructor. eassumption.
    econstructor. split. eassumption. constructor.
Qed.

Lemma ev_elim_determ:
   forall t m m1 m2, ev_elim m t m1 -> ev_elim m t m2 -> m1=m2.
Proof.
 induction t; intros.
 inv H; inv H0. auto.
 simpl in *.
 destruct a.
 destruct H as [m1' [? ?]].
 destruct H0 as [m2' [? ?]].
 assert (m1'=m2') by congruence. subst m2'. eauto.
 destruct H, H0. eauto.
 destruct H as [m1' [? ?]].
 destruct H0 as [m2' [? ?]].
 assert (m1'=m2') by congruence. subst m2'. eauto.
 destruct H as [m1' [? ?]].
 destruct H0 as [m2' [? ?]].
 assert (m1'=m2') by congruence. subst m2'. eauto.
Qed.

(*Lemma asm_ev_elim_strong g (Hsafe : safe_genv g): forall c m T c' m' (Estep: asm_ev_step g c m T c' m'),
      ev_elim m T m' /\ (forall mm mm', ev_elim mm T mm' -> exists cc', asm_ev_step g c mm T cc' mm').
Proof.
  induction 1; intros; try contradiction.
  destruct i; inv H2;
  simpl in H3; inv H3;
  try solve [split; simpl;
        first [eexists; split; reflexivity |
               intros mm mm' EV'; inv EV'; destruct H2 as [FL EV']; inv EV'; inv FL;
                 eexists (State _ m1); econstructor; try eassumption; reflexivity]];
  simpl.
  - (*Pmovl_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4. inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl. erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovq_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl. erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovl_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovq_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint64 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovsd_fm*)
    unfold exec_load in H5.
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
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsd_mf*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovss_fm*)
    unfold exec_load in H5.
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
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovss_mf*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pfldl_m*)
    unfold exec_load in H5.
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
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pfstpl_m*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pflds_m*)unfold exec_load in H5.
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
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pfstps_m*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovb_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    inv H4.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovw_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    inv H4.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovzb_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4. inv H5. inv H4.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsb_rm*)unfold exec_load in H5.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4. inv H5. inv H4.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovzw_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4. inv H5. inv H4.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsw_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4. inv H5. inv H4.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pdivl*)
    remember (rs RDX) as d; destruct d; inv H5.
    remember (rs RAX) as a; destruct a; inv H3.
    remember (rs r1) as r; destruct r; inv H4.
    remember (Int.divmodu2 _ _ _) as v; destruct v as [[]|]; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      change [Free[]] with (option_list_to_list (Some [Free[]])).
      eexists (State _ m1); econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqd, <- Heqa, <- Heqr, <- Heqv; reflexivity.
  - (*Pdivq*)
    remember (rs RDX) as d; destruct d; inv H5.
    remember (rs RAX) as a; destruct a; inv H3.
    remember (rs r1) as r; destruct r; inv H4.
    remember (Int64.divmodu2 _ _ _) as v; destruct v as [[]|]; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      change [Free[]] with (option_list_to_list (Some [Free[]])).
      eexists (State _ m1); econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqd, <- Heqa, <- Heqr, <- Heqv; reflexivity.
  - (*Pidivl*)
    remember (rs RDX) as d; destruct d; inv H5.
    remember (rs RAX) as a; destruct a; inv H3.
    remember (rs r1) as r; destruct r; inv H4.
    remember (Int.divmods2 _ _ _) as v; destruct v as [[]|]; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      change [Free[]] with (option_list_to_list (Some [Free[]])).
      eexists (State _ m1); econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqd, <- Heqa, <- Heqr, <- Heqv; reflexivity.
  - (*Pidivq*)
    remember (rs RDX) as d; destruct d; inv H5.
    remember (rs RAX) as a; destruct a; inv H3.
    remember (rs r1) as r; destruct r; inv H4.
    remember (Int64.divmods2 _ _ _) as v; destruct v as [[]|]; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      change [Free[]] with (option_list_to_list (Some [Free[]])).
      eexists (State _ m1); econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqd, <- Heqa, <- Heqr, <- Heqv; reflexivity.
  - (*Pcmov*)
    remember (eval_testcond c rs) as p; destruct p; inv H5.
    * destruct b0; inv H3.
      ++ split. econstructor. split. reflexivity. constructor.
         intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
         eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
      ++ split. econstructor. split. reflexivity. constructor.
         intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
         eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
    * split. econstructor. split. reflexivity. constructor.
      intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
      eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
  - (*Pjmp_l*)
    unfold goto_label in H5. rewrite H in *.
    remember (label_pos l 0 (fn_code f)) as p; destruct p; inv H5.
    split.
    * econstructor. split. reflexivity. constructor.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
      eexists (State _ m1); econstructor; try eassumption; simpl; trivial.
      unfold goto_label. rewrite <- Heqp, H. reflexivity.
  - (*Pjcc*)
    remember (eval_testcond c rs) as p;destruct p; inv H5.
    destruct b0; inv H3.
    * unfold goto_label in H4. rewrite H in *.
      remember (label_pos l 0 (fn_code f)) as q; destruct q; inv H4.
      split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
         eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
         unfold goto_label. rewrite <- Heqq, H; reflexivity.
    * split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
         eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
  - (*Pjcc2*)
    remember (eval_testcond c1 rs) as p; destruct p; inv H5.
    destruct b0; inv H3.
    * remember (eval_testcond c2 rs) as q; destruct q; inv H4.
      destruct b0; inv H3.
      ++ unfold goto_label in H4. rewrite H in *.
         remember (label_pos l 0 (fn_code f)) as w; destruct w; inv H4.
         split.
         -- econstructor. split. reflexivity. constructor.
         -- intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
            eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
            unfold goto_label. rewrite <- Heqw, H; reflexivity.
      ++ split.
         -- econstructor. split. reflexivity. constructor.
         -- intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
            eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
    * remember (eval_testcond c2 rs) as q; destruct q; inv H4.
      split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
         eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
  - (*Pjmptbl*)
    remember (rs r) as p; destruct p; inv H5.
    remember (list_nth_z tbl (Int.unsigned i)) as q; destruct q; inv H3.
    unfold goto_label in H4. rewrite !Pregmap.gso, H in * by discriminate.
    remember (label_pos l 0 (fn_code f)) as w; destruct w; inv H4.
    split.
      * econstructor. split. reflexivity. constructor.
      * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         change [Free[]] with (option_list_to_list (Some [Free[]])).
        eexists (State _ m1); econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
        unfold goto_label. rewrite <- Heqw, !Pregmap.gso, H by discriminate; reflexivity.
  - (*Pmov_rm_a*)
    unfold exec_load in H5.
    remember (Mem.loadv _ m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    remember (if Archi.ptr64 then Many64 else Many32) as mchunk.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB;
    rewrite LB in H4; inv H5. inv H4.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmov_mr_a*)
    unfold exec_store in H5.
    remember (Mem.storev _ m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5.
    remember (if Archi.ptr64 then Many64 else Many32) as mchunk.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp. inv H4.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovsd_fm_a*)
    unfold exec_load in H5.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4. inv H5. inv H4.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsd_mf_a*)
    unfold exec_store in H5.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp. inv H4.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists (State _ m1); econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as a; symmetry in Heqa; destruct a as [ma stk].
    remember (Mem.store Mptr ma stk
         (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_link))
         (rs RSP)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (Mem.store Mptr m0 stk (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_ra))
         (rs RA)) as q.
    destruct q; try discriminate; symmetry in Heqq. inv H5.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGNp].
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALIGNq].
    apply Mem.store_storebytes in Heqp.
    apply Mem.store_storebytes in Heqq.
    rewrite Ptrofs.add_zero_l in *. inv H4.
    split.
    * econstructor. split. eassumption.
      econstructor. split. eassumption.
      econstructor. split. eassumption.
      econstructor.
    * intros mm mm' EV'; inv EV'. destruct H2 as [ALLOC EV]. inv EV. inv H2. inv H4. destruct H2. inv H4.
      eexists (State _ m1); econstructor; try eassumption; simpl; repeat rewrite Ptrofs.add_zero_l; rewrite ALLOC;
      repeat erewrite Mem.storebytes_store; try eassumption; reflexivity.
  - (*Pfreeframe*)
    remember (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_ra)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_link)) as q.
    destruct q; try discriminate; symmetry in Heqq.
    remember (rs RSP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as t; destruct t; try discriminate.
    inv H5.
    destruct (Mem.load_loadbytes _ _ _ _ _  Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _  Heqq) as [bytes2 [Bytes2 LD2]].
    simpl in *; rewrite Bytes1, Bytes2 in *. inv H4.
    destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN1].
    destruct (Mem.load_valid_access _ _ _ _ _ Heqq) as [_ ALIGN2].
    split.
    * econstructor; trivial. econstructor; trivial.  econstructor.
      split. simpl. rewrite <- Heqt; trivial. econstructor.
    * intros mm mm' EV'. inv EV'. inv H3. inv H5. destruct H3. inv H5. simpl in H3.
      remember (Mem.free mm b0 0 sz) as d; destruct d; try discriminate. inv H3.
      exploit (Mem.loadbytes_load Mptr). apply H2. assumption.
      exploit (Mem.loadbytes_load Mptr). apply H4. assumption.
      eexists (State _ m1); econstructor; try eassumption.
      ++ simpl. rewrite <- Heqw; simpl. rewrite H3, H5, <- Heqd. reflexivity.
      ++ simpl. rewrite <- Heqw; simpl. rewrite H3, H5, <- Heqd. rewrite H2, H4. reflexivity.
- (*builtin*)
  destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H2) as [EV EVS].
  exploit Hsafe; eauto.
  { eapply eval_builtin_args_ev_eval_builtin_args; eauto. }
  inversion H3; subst ef.
  + (*malloc*)
    intros _.
    inv H4. rewrite Vptrofs_inj with (o2 := n) in H6 by congruence.
    rewrite H6 in ALLOC. inv ALLOC.
    replace (Vptrofs sz) with (Vptrofs n) in H10 by congruence.
    apply Mem.store_storebytes in H10.
    split.
    * eapply ev_elim_app. eassumption.
      econstructor. split. eassumption.
      econstructor. split. eassumption. constructor.
    * intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [mm1 [EV1 EV2]].
      inv EV2. destruct H4. inv H5. destruct H7. inv H7.
      specialize (EVS _ _ EV1); destruct EVS; subst mm1.
      eexists (State _ m1). econstructor 2; try eassumption; simpl; trivial.
      ++ econstructor; try eassumption.
      ++ econstructor. eassumption. erewrite Mem.storebytes_store; auto.
  + (*free*)
    intros _.
    inv H4. inv H12.
    destruct (Mem.load_loadbytes _ _ _ _ _ H6) as [bytes1 [LB1 SZ1]].
    rewrite LB1 in LB; inv LB. rewrite <- SZ1 in SZ. rewrite (Vptrofs_inj _ _ SZ) in *.
    rewrite H11 in FR; inv FR.
    split.
    * eapply ev_elim_app. eassumption.
      econstructor. eassumption.
      econstructor. split. simpl. rewrite H11. reflexivity. constructor.
    * intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [mm1 [EV1 EV2]].
      inv EV2. inv H5. destruct H7. inv H7.
      specialize (EVS _ _ EV1); destruct EVS; subst mm1.
      simpl in H5.
      remember (Mem.free mm b0 (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz0)) as d.
      destruct d; inv H5; symmetry in Heqd.
      eexists (State _ m1). econstructor 2; try eassumption; simpl; trivial.
      ++ econstructor; eassumption.
      ++ econstructor; try eassumption.
         rewrite SZ1. apply Mem.loadbytes_load; assumption.
  + (*memcpy*)
    intros _.
    inv H4. inv H17. rewrite LB in H15; inv H15. rewrite ST in H16; inv H16.
    split.
    * eapply ev_elim_app. eassumption.
      econstructor. eassumption.
      econstructor. split. eassumption. constructor.
    * intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [mm1 [EV1 EV2]].
      inv EV2. inv H5. destruct H7. inv H7.
      specialize (EVS _ _ EV1); destruct EVS; subst mm1.
      eexists (State _ m1). econstructor 2; try eassumption; simpl; trivial.
      ++ econstructor; eassumption.
      ++ econstructor; try eassumption.
  + intro; assert (m' = m /\ (forall mm, external_call ef0 g vargs mm t vres mm) /\ False) as [? []]
      by (destruct ef0; auto; contradiction); subst.
    split; [rewrite app_nil_r; auto|].
    intros ?? Hmm; rewrite app_nil_r in Hmm.
    destruct (EVS _ _ Hmm); subst.
    eexists (State _ m1); econstructor 2; try eassumption; [constructor; auto | ..]; eauto.
Qed.*)

Program Definition Asm_EvSem (ge : genv) (Hsafe : safe_genv ge) : @EvSem state.
Proof.
eapply Build_EvSem with (msem := Asm_mem_sem ge Hsafe (*hf*)) (ev_step:=asm_ev_step ge).
+ intros. eapply asm_ev_ax1; try eassumption. (*helper_functions declared*)
+ eapply asm_ev_ax2; eassumption.
+ eapply asm_ev_fun; eassumption.
+ eapply asm_ev_elim; eassumption.
Defined.

End ASM_EV.
